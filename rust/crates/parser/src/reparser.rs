// Ported from tsc/internal/parser/reparser.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Go `*ast.Node` values are `NodeId`s resolved through `self.nodes`; Go nil is
// `Option<NodeId>`.

use tsc_ast::ast_generated::*;
use tsc_ast::utilities::{
    JsDeclarationKind, get_assignment_declaration_kind, get_right_most_assigned_expression,
    has_same_property_access_name, is_function_like, is_this_identifier,
};
use tsc_ast::{Kind, ModifierList, Node, NodeFlags, NodeId, NodeList, TokenFlags};
use tsc_core::text::TextRange;
use tsc_diagnostics as diagnostics;
use tsc_scanner::scanner;

use crate::parser::{JSDocInfo, Parser, parsing_context::PC_OBJECT_LITERAL_MEMBERS};

impl<'a> Parser<'a> {
    /// `func (p *Parser) finishReparsedNode(node *ast.Node, locationNode *ast.Node)`
    pub(crate) fn finish_reparsed_node(&mut self, node: NodeId, location_node: NodeId) {
        self.nodes[node].flags = self.context_flags | NodeFlags::REPARSED;
        self.nodes[node].loc = self.nodes[location_node].loc;
        self.override_parent_in_immediate_children(node);
    }

    /// `func (p *Parser) finishMutatedNode(node *ast.Node)`
    pub(crate) fn finish_mutated_node(&mut self, node: NodeId) {
        self.override_parent_in_immediate_children(node);
    }

    /// `func (p *Parser) addDeepCloneReparse(node *ast.Node) *ast.Node`
    ///
    /// Deep-clone the given node and add the clone to the reparsed clone list.
    /// The list is used by `ast.GetReparsedNodeForNode` to locate reparsed
    /// clones of JSDoc nodes. Since the binder attaches symbols to reparsed
    /// nodes and not to JSDoc nodes, we need the mapping when obtaining symbols
    /// and types from JSDoc nodes.
    pub(crate) fn add_deep_clone_reparse(&mut self, node: Option<NodeId>) -> Option<NodeId> {
        let clone = self.factory.deep_clone_reparse(&mut self.nodes, node);
        if let Some(clone) = clone {
            self.reparsed_clones.push(clone);
        }
        clone
    }

    /// `func (p *Parser) addTransformedReparse(newNode *ast.Node, old *ast.Node) *ast.Node`
    pub(crate) fn add_transformed_reparse(&mut self, new_node: NodeId, old: NodeId) -> NodeId {
        self.finish_reparsed_node(new_node, old);
        self.nodes[new_node].flags |= NodeFlags::REPARSER_TRANSFORMED_LITERAL;
        self.reparsed_clones.push(new_node);
        new_node
    }

    /// `func (p *Parser) checkNonIdentifierName(name *ast.Node) *ast.Node`
    pub(crate) fn check_non_identifier_name(&mut self, name: Option<NodeId>) -> Option<NodeId> {
        // Handles the case of anonymous functions
        let name = name?;
        if is_identifier(&self.nodes[name])
            && !scanner::is_valid_identifier(&self.nodes[name].as_identifier().text)
        {
            let mut err_loc = self.nodes[name].loc;
            if err_loc.len() == 0 {
                // missing name, emit error on the character before the missing name node
                err_loc =
                    TextRange::new(self.nodes[name].loc.pos() - 1, self.nodes[name].loc.pos());
            }
            self.parse_error_at_range(err_loc, &diagnostics::Identifier_expected, &[]);
        }
        Some(name)
    }

    /// `func (p *Parser) reparseTags(parent *ast.Node, jsDoc []*ast.Node)`
    ///
    /// Hosted tags find a host and add their children to the correct location
    /// under the host. Unhosted tags add synthetic nodes to the reparse list.
    pub fn reparse_tags(&mut self, parent: NodeId, js_doc: &[NodeId]) {
        let last = js_doc.last().copied();
        for &j in js_doc {
            let is_last = Some(j) == last;
            let tags: Vec<NodeId> = match &self.nodes[j].as_js_doc().tags {
                Some(tags) => tags.nodes.to_vec(),
                None => continue,
            };
            for tag in tags {
                self.reparse_unhosted(tag, parent, j);
                if is_last {
                    self.reparse_hosted(tag, parent, j);
                }
            }
        }
    }

    /// `func (p *Parser) reparseUnhosted(tag *ast.Node, parent *ast.Node, jsDoc *ast.Node)`
    fn reparse_unhosted(&mut self, tag: NodeId, parent: NodeId, js_doc: NodeId) {
        match self.nodes[tag].kind {
            Kind::JSDocTypedefTag => {
                let Some(type_expression) = self.nodes[tag].type_expression() else {
                    return;
                };
                let full_name = self.nodes[tag].name();
                let is_namespace = full_name.is_some_and(|n| is_module_declaration(&self.nodes[n]));
                let mut modifiers = None;
                if is_namespace {
                    modifiers = Some(self.create_export_modifier(tag));
                }
                let name = self.get_innermost_name_of_jsdoc_namespace(full_name);
                let name = self.check_non_identifier_name(name);
                let name = self.add_deep_clone_reparse(name);
                let type_alias = self.factory.new_js_type_alias_declaration(
                    &mut self.nodes,
                    modifiers,
                    name,
                    None,
                    None,
                );
                let type_parameters =
                    self.gather_type_parameters(js_doc, true /*typedefOrCallback*/);
                self.nodes[type_alias]
                    .as_type_alias_declaration_mut()
                    .type_parameters = type_parameters;
                let t = match self.nodes[type_expression].kind {
                    Kind::JSDocTypeExpression => {
                        self.add_deep_clone_reparse(self.nodes[type_expression].type_())
                    }
                    Kind::JSDocTypeLiteral => {
                        self.reparse_jsdoc_type_literal(Some(type_expression))
                    }
                    kind => panic!(
                        "typedef tag type expression should be a name reference or a type expression {:?}",
                        kind
                    ),
                };
                self.nodes[type_alias].as_type_alias_declaration_mut().type_ = t;
                self.finish_reparsed_node(type_alias, tag);
                self.jsdoc_infos.push(JSDocInfo {
                    parent: Some(type_alias),
                    js_docs: vec![js_doc],
                });
                self.nodes[type_alias].flags |= NodeFlags::HAS_JSDOC;
                let result =
                    self.wrap_in_jsdoc_namespace(full_name, type_alias, false /*nested*/);
                self.reparse_list.push(result);
            }
            Kind::JSDocCallbackTag => {
                let Some(type_expression) = self.nodes[tag].type_expression() else {
                    return;
                };
                let full_name = self.nodes[tag].name();
                let is_namespace = full_name.is_some_and(|n| is_module_declaration(&self.nodes[n]));
                let mut modifiers = None;
                if is_namespace {
                    modifiers = Some(self.create_export_modifier(tag));
                }
                let function_type =
                    self.reparse_jsdoc_signature(type_expression, tag, js_doc, tag, None);
                let name = self.get_innermost_name_of_jsdoc_namespace(full_name);
                let name = self.add_deep_clone_reparse(name);
                let type_alias = self.factory.new_js_type_alias_declaration(
                    &mut self.nodes,
                    modifiers,
                    name,
                    None,
                    Some(function_type),
                );
                let type_parameters =
                    self.gather_type_parameters(js_doc, true /*typedefOrCallback*/);
                self.nodes[type_alias]
                    .as_type_alias_declaration_mut()
                    .type_parameters = type_parameters;
                self.finish_reparsed_node(type_alias, tag);
                self.jsdoc_infos.push(JSDocInfo {
                    parent: Some(type_alias),
                    js_docs: vec![js_doc],
                });
                self.nodes[type_alias].flags |= NodeFlags::HAS_JSDOC;
                let result =
                    self.wrap_in_jsdoc_namespace(full_name, type_alias, false /*nested*/);
                self.reparse_list.push(result);
            }
            Kind::JSDocImportTag => {
                let (import_clause_id, module_specifier, attributes) = {
                    let import_tag = self.nodes[tag].as_js_doc_import_tag();
                    (
                        import_tag.import_clause,
                        import_tag.module_specifier,
                        import_tag.attributes,
                    )
                };
                if import_clause_id.is_none() {
                    return;
                }
                let import_clause = self.add_deep_clone_reparse(import_clause_id);
                if let Some(import_clause) = import_clause {
                    self.nodes[import_clause]
                        .as_import_clause_mut()
                        .phase_modifier = Kind::TypeKeyword;
                }
                let tag_modifiers = self.nodes[tag].modifiers().cloned();
                let modifiers = self
                    .factory
                    .deep_clone_reparse_modifiers(&mut self.nodes, tag_modifiers);
                let module_specifier = self.add_deep_clone_reparse(module_specifier);
                let attributes = self.add_deep_clone_reparse(attributes);
                let import_declaration = self.factory.new_js_import_declaration(
                    &mut self.nodes,
                    modifiers,
                    import_clause,
                    module_specifier,
                    attributes,
                );
                self.finish_reparsed_node(import_declaration, tag);
                self.reparse_list.push(import_declaration);
            }
            Kind::JSDocOverloadTag => {
                // Create overload signatures only for function, method, and constructor declarations outside object literals
                if (is_function_declaration(&self.nodes[parent])
                    || is_method_declaration(&self.nodes[parent])
                    || is_constructor_declaration(&self.nodes[parent]))
                    && self.parsing_contexts & (1 << PC_OBJECT_LITERAL_MEMBERS) == 0
                {
                    let type_expression = self.nodes[tag].as_js_doc_overload_tag().type_expression;
                    let modifiers = self.nodes[parent].modifiers().cloned();
                    if let Some(type_expression) = type_expression {
                        let signature = self.reparse_jsdoc_signature(
                            type_expression,
                            parent,
                            js_doc,
                            tag,
                            modifiers,
                        );
                        self.reparse_list.push(signature);
                    }
                }
            }
            _ => {}
        }
    }

    /// `func (p *Parser) reparseJSDocSignature(jsSignature *ast.Node, fun *ast.Node, jsDoc *ast.Node, tag *ast.Node, modifiers *ast.ModifierList) *ast.Node`
    fn reparse_jsdoc_signature(
        &mut self,
        js_signature: NodeId,
        fun: NodeId,
        js_doc: NodeId,
        tag: NodeId,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let cloned_modifiers = self
            .factory
            .deep_clone_reparse_modifiers(&mut self.nodes, modifiers);
        let signature = match self.nodes[fun].kind {
            Kind::FunctionDeclaration => {
                let name = self.check_non_identifier_name(self.nodes[fun].name());
                let name = self.factory.deep_clone_reparse(&mut self.nodes, name);
                self.factory.new_function_declaration(
                    &mut self.nodes,
                    cloned_modifiers,
                    None,
                    name,
                    None,
                    None,
                    None,
                    None,
                    None,
                )
            }
            Kind::MethodDeclaration => {
                let name = self.check_non_identifier_name(self.nodes[fun].name());
                let name = self.factory.deep_clone_reparse(&mut self.nodes, name);
                self.factory.new_method_declaration(
                    &mut self.nodes,
                    cloned_modifiers,
                    None,
                    name,
                    None,
                    None,
                    None,
                    None,
                    None,
                    None,
                )
            }
            Kind::Constructor => self.factory.new_constructor_declaration(
                &mut self.nodes,
                cloned_modifiers,
                None,
                None,
                None,
                None,
                None,
            ),
            Kind::JSDocCallbackTag => {
                let any_type = self
                    .factory
                    .new_keyword_type_node(&mut self.nodes, Kind::AnyKeyword);
                self.factory
                    .new_function_type_node(&mut self.nodes, None, None, Some(any_type))
            }
            kind => panic!("Unexpected kind {:?}", kind),
        };

        if self.nodes[tag].kind != Kind::JSDocCallbackTag {
            let type_parameters =
                self.gather_type_parameters(js_doc, false /*typedefOrCallback*/);
            if let Some(data) = self.nodes[signature].data.function_like_data_mut() {
                data.type_parameters = type_parameters;
            }
        }
        let mut parameters: Vec<NodeId> = Vec::new();
        let js_parameters: Vec<NodeId> = self.nodes[js_signature]
            .parameters()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        for (pi, param) in js_parameters.iter().copied().enumerate() {
            let parameter: NodeId;
            if self.nodes[param].kind == Kind::JSDocThisTag {
                let this_tag_loc = self.nodes[param].loc;
                let this_ident = self.factory.new_identifier(&mut self.nodes, "this");
                self.nodes[this_ident].loc = this_tag_loc;
                self.nodes[this_ident].flags = self.context_flags | NodeFlags::REPARSED;
                parameter = self.factory.new_parameter_declaration(
                    &mut self.nodes,
                    None,
                    None,
                    Some(this_ident),
                    None,
                    None,
                    None,
                );
                let this_type_expression = self.nodes[param].as_js_doc_this_tag().type_expression;
                if let Some(this_type_expression) = this_type_expression {
                    let t = self.add_deep_clone_reparse(self.nodes[this_type_expression].type_());
                    self.nodes[parameter].as_parameter_declaration_mut().type_ = t;
                }
            } else if self.nodes[param].kind == Kind::JSDocParameterTag
                || self.nodes[param].kind == Kind::JSDocPropertyTag
            {
                let param_name = self.nodes[param].name();
                // Skip sub-property parameters (e.g., @param x.y) - these have QualifiedNames
                // and describe properties of a parent parameter, not standalone parameters.
                if param_name.is_some_and(|n| is_qualified_name(&self.nodes[n])) {
                    continue;
                }
                let is_bracketed = self.nodes[param]
                    .as_js_doc_parameter_or_property_tag()
                    .is_bracketed;
                let type_expression = self.nodes[param]
                    .as_js_doc_parameter_or_property_tag()
                    .type_expression;
                let mut dot_dot_dot_token = None;
                let mut param_type = None;

                if let Some(type_expression) = type_expression {
                    let te_type = self.nodes[type_expression].type_();
                    if te_type.is_some_and(|t| self.nodes[t].kind == Kind::JSDocVariadicType) {
                        let tok = self
                            .factory
                            .new_token(&mut self.nodes, Kind::DotDotDotToken);
                        self.nodes[tok].loc = self.nodes[param].loc;
                        self.nodes[tok].flags = self.context_flags | NodeFlags::REPARSED;
                        dot_dot_dot_token = Some(tok);

                        let variadic_type =
                            self.nodes[te_type.unwrap()].as_js_doc_variadic_type().type_;
                        param_type = self.reparse_jsdoc_type_literal(variadic_type);
                    } else {
                        param_type = self.reparse_jsdoc_type_literal(te_type);
                    }
                }
                let mut name = param_name;
                let name_is_invalid_identifier = name.is_some_and(|n| {
                    is_identifier(&self.nodes[n])
                        && !scanner::is_valid_identifier(&self.nodes[n].as_identifier().text)
                });
                if name_is_invalid_identifier {
                    // drop invalid chars for _, if empty, write _0, etc., so we have a valid param name to emit later
                    let text = self.nodes[name.unwrap()].as_identifier().text.clone();
                    let mut result = String::new();
                    for (i, ch) in text.char_indices() {
                        if i == 0 {
                            if !scanner::is_identifier_start(ch as i32) {
                                result.push('_');
                            } else {
                                result.push(ch);
                            }
                            continue;
                        } else if !scanner::is_identifier_part(ch as i32) {
                            result.push('_');
                        } else {
                            result.push(ch);
                        }
                    }
                    if result.is_empty() {
                        result.push('_');
                        result.push_str(&pi.to_string());
                    }
                    let new_name = self.factory.new_identifier(&mut self.nodes, &result);
                    name = Some(self.add_transformed_reparse(new_name, name.unwrap()));
                } else {
                    name = self.add_deep_clone_reparse(name);
                }
                let question_token = self.make_question_if_optional(
                    is_bracketed,
                    type_expression,
                    self.nodes[param].loc,
                );
                parameter = self.factory.new_parameter_declaration(
                    &mut self.nodes,
                    None,
                    dot_dot_dot_token,
                    name,
                    question_token,
                    param_type,
                    None,
                );
            } else {
                // PORT: Go leaves `parameter` nil here (e.g. unexpected kinds);
                // mirror by finishing a clone of the param itself.
                parameter = param;
            }
            self.finish_reparsed_node(parameter, param);
            parameters.push(parameter);
            self.reparse_jsdoc_comment_node(parameter, param);
        }
        let parameters_loc = self.nodes[js_signature]
            .as_js_doc_signature()
            .function_like_base
            .parameters
            .as_ref()
            .map(|p| p.loc)
            .unwrap_or_default();
        let parameters_list = self.new_node_list(parameters_loc, parameters);
        if let Some(data) = self.nodes[signature].data.function_like_data_mut() {
            data.parameters = Some(parameters_list);
        }

        let sig_type = self.nodes[js_signature].type_();
        if let Some(sig_type) = sig_type
            && let Some(type_expression) = self.nodes[sig_type].type_expression()
        {
            let t = self.add_deep_clone_reparse(self.nodes[type_expression].type_());
            if let Some(data) = self.nodes[signature].data.function_like_data_mut() {
                data.type_ = t;
            }
        }
        let mut loc = js_signature;
        if self.nodes[tag].kind == Kind::JSDocOverloadTag
            && let Some(tag_name) = self.nodes[tag].tag_name()
        {
            loc = tag_name;
        }
        self.finish_reparsed_node(signature, loc);
        signature
    }

    /// `func (p *Parser) reparseJSDocTypeLiteral(t *ast.TypeNode) *ast.Node`
    fn reparse_jsdoc_type_literal(&mut self, t: Option<NodeId>) -> Option<NodeId> {
        let t = t?;
        if self.nodes[t].kind == Kind::JSDocTypeLiteral {
            let is_array_type = self.nodes[t].as_js_doc_type_literal().is_array_type;
            let property_tags: Vec<NodeId> = self.nodes[t]
                .as_js_doc_type_literal()
                .js_doc_property_tags
                .to_vec();
            let literal_loc = self.nodes[t].loc;
            let mut properties: Vec<NodeId> = Vec::new();
            for prop in property_tags {
                if self.nodes[prop].kind != Kind::JSDocPropertyTag
                    && self.nodes[prop].kind != Kind::JSDocParameterTag
                {
                    continue;
                }
                let js_prop_type_expression = self.nodes[prop]
                    .as_js_doc_parameter_or_property_tag()
                    .type_expression;
                let is_bracketed = self.nodes[prop]
                    .as_js_doc_parameter_or_property_tag()
                    .is_bracketed;
                let mut name = self.nodes[prop].name();
                if let Some(n) = name
                    && self.nodes[n].kind == Kind::QualifiedName
                {
                    name = self.nodes[n].as_qualified_name().right;
                }
                let name_is_invalid_identifier = name.is_some_and(|n| {
                    is_identifier(&self.nodes[n])
                        && !scanner::is_valid_identifier(&self.nodes[n].as_identifier().text)
                });
                if name_is_invalid_identifier {
                    let text = self.nodes[name.unwrap()].as_identifier().text.clone();
                    let new_name =
                        self.factory
                            .new_string_literal(&mut self.nodes, &text, TokenFlags::NONE);
                    name = Some(self.add_transformed_reparse(new_name, name.unwrap()));
                } else {
                    name = self.add_deep_clone_reparse(name);
                }
                let question_token = self.make_question_if_optional(
                    is_bracketed,
                    js_prop_type_expression,
                    self.nodes[prop].loc,
                );
                let property = self.factory.new_property_signature_declaration(
                    &mut self.nodes,
                    None,
                    name,
                    question_token,
                    None,
                    None,
                );
                if let Some(type_expression) = js_prop_type_expression {
                    let t2 = self.reparse_jsdoc_type_literal(self.nodes[type_expression].type_());
                    self.nodes[property]
                        .as_property_signature_declaration_mut()
                        .type_ = t2;
                }
                self.finish_reparsed_node(property, prop);
                properties.push(property);
                self.reparse_jsdoc_comment_node(property, prop);
            }
            let js_type_literal = t;
            let properties_list = self.new_node_list(literal_loc, properties);
            let mut t = self
                .factory
                .new_type_literal_node(&mut self.nodes, Some(properties_list));
            if is_array_type {
                self.finish_reparsed_node(t, js_type_literal);
                t = self.factory.new_array_type_node(&mut self.nodes, Some(t));
            }
            self.finish_reparsed_node(t, js_type_literal);
            return Some(t);
        }
        self.add_deep_clone_reparse(Some(t))
    }

    /// `func (p *Parser) reparseJSDocComment(node *ast.Node, tag *ast.Node)`
    fn reparse_jsdoc_comment_node(&mut self, node: NodeId, tag: NodeId) {
        let comment = self.nodes[tag].comment_list().cloned();
        if let Some(comment) = comment {
            let new_nodes: Vec<NodeId> = comment
                .nodes
                .iter()
                .map(|&n| self.factory.deep_clone_reparse(&mut self.nodes, Some(n)))
                .collect::<Option<Vec<_>>>()
                .unwrap_or_default();
            let mut new_comment = self.factory.new_node_list(new_nodes);
            new_comment.loc = comment.loc;
            let prop_jsdoc = self
                .factory
                .new_js_doc(&mut self.nodes, Some(new_comment), None);
            self.finish_reparsed_node(prop_jsdoc, tag);
            self.nodes[prop_jsdoc].parent = Some(node);
            self.jsdoc_infos.push(JSDocInfo {
                parent: Some(node),
                js_docs: vec![prop_jsdoc],
            });
            self.nodes[node].flags |= NodeFlags::HAS_JSDOC;
        }
    }

    /// `func (p *Parser) gatherTypeParameters(j *ast.Node, typedefOrCallback bool) *ast.NodeList`
    fn gather_type_parameters(&mut self, j: NodeId, typedef_or_callback: bool) -> Option<NodeList> {
        let mut type_parameters: Vec<NodeId> = Vec::new();
        let mut pos = -1;
        let mut end_pos = -1;
        let mut first_template = true;
        let tags: Vec<NodeId> = self.nodes[j]
            .as_js_doc()
            .tags
            .as_ref()
            .map(|t| t.nodes.to_vec())
            .unwrap_or_default();
        for tag in tags {
            // When a JSDoc comment contains an `@typedef` or `@callback` tag, `@template` type parameter
            // declarations apply to the type being defined.
            if !typedef_or_callback
                && (self.nodes[tag].kind == Kind::JSDocTypedefTag
                    || self.nodes[tag].kind == Kind::JSDocCallbackTag)
            {
                return None;
            }
            if self.nodes[tag].kind != Kind::JSDocTemplateTag {
                continue;
            }
            if first_template {
                pos = self.nodes[tag].pos();
                first_template = false;
            }
            end_pos = self.nodes[tag].end();
            let constraint = self.nodes[tag].as_js_doc_template_tag().constraint;
            let mut first_type_parameter = true;
            let tps: Vec<NodeId> = self.nodes[tag]
                .type_parameters()
                .map(|t| t.to_vec())
                .unwrap_or_default();
            for tp in tps {
                let reparse;
                if constraint.is_some() && first_type_parameter {
                    let tp_modifiers = self.nodes[tp].modifiers().cloned();
                    let modifiers = self
                        .factory
                        .deep_clone_reparse_modifiers(&mut self.nodes, tp_modifiers);
                    let name = self.check_non_identifier_name(self.nodes[tp].name());
                    let name = self.add_deep_clone_reparse(name);
                    let constraint_type =
                        self.add_deep_clone_reparse(self.nodes[constraint.unwrap()].type_());
                    let default_type = self.add_deep_clone_reparse(
                        self.nodes[tp].as_type_parameter_declaration().default_type,
                    );
                    reparse = self.factory.new_type_parameter_declaration(
                        &mut self.nodes,
                        modifiers,
                        name,
                        constraint_type,
                        None, // expression
                        default_type,
                    );
                    self.finish_reparsed_node(reparse, tp);
                } else {
                    reparse = self.add_deep_clone_reparse(Some(tp)).unwrap();
                }
                type_parameters.push(reparse);
                first_type_parameter = false;
            }
        }
        if type_parameters.is_empty() {
            None
        } else {
            Some(self.new_node_list(TextRange::new(pos, end_pos), type_parameters))
        }
    }

    /// `func (p *Parser) reparseHosted(tag *ast.Node, parent *ast.Node, jsDoc *ast.Node)`
    fn reparse_hosted(&mut self, tag: NodeId, parent: NodeId, js_doc: NodeId) {
        match self.nodes[tag].kind {
            Kind::JSDocTypeTag => {
                match self.nodes[parent].kind {
                    Kind::VariableStatement => {
                        if let Some(declaration_list) =
                            self.nodes[parent].as_variable_statement().declaration_list
                        {
                            let declarations: Vec<NodeId> = self.nodes[declaration_list]
                                .as_variable_declaration_list()
                                .declarations
                                .as_ref()
                                .map(|d| d.nodes.to_vec())
                                .unwrap_or_default();
                            for declaration in declarations {
                                if self.nodes[declaration].type_().is_none()
                                    && self.nodes[tag].type_expression().is_some()
                                {
                                    let t = self.add_deep_clone_reparse(
                                        self.nodes[self.nodes[tag].type_expression().unwrap()]
                                            .type_(),
                                    );
                                    self.nodes[declaration].set_type(t);
                                    self.finish_mutated_node(declaration);
                                    return;
                                }
                            }
                        }
                    }
                    Kind::VariableDeclaration
                    | Kind::ExportAssignment
                    | Kind::PropertyDeclaration
                    | Kind::PropertyAssignment
                    | Kind::ShorthandPropertyAssignment
                    | Kind::GetAccessor => {
                        if self.nodes[parent].type_().is_none()
                            && self.nodes[tag].type_expression().is_some()
                        {
                            let t = self.add_deep_clone_reparse(
                                self.nodes[self.nodes[tag].type_expression().unwrap()].type_(),
                            );
                            self.nodes[parent].set_type(t);
                            self.finish_mutated_node(parent);
                            return;
                        }
                    }
                    Kind::Parameter => {
                        if self.nodes[parent].type_().is_none()
                            && self.nodes[tag].type_expression().is_some()
                        {
                            let te = self.nodes[tag].type_expression();
                            let t =
                                self.reparse_jsdoc_type_literal(self.nodes[te.unwrap()].type_());
                            self.nodes[parent].set_type(t);
                            self.finish_mutated_node(parent);
                            return;
                        }
                    }
                    Kind::ExpressionStatement => {
                        let expression = self.nodes[parent].expression();
                        if expression.is_some_and(|e| self.nodes[e].kind == Kind::BinaryExpression)
                        {
                            let bin = expression.unwrap();
                            let kind = get_assignment_declaration_kind(bin, &self.nodes);
                            if kind != JsDeclarationKind::None
                                && self.nodes[tag].type_expression().is_some()
                            {
                                let t = self.add_deep_clone_reparse(
                                    self.nodes[self.nodes[tag].type_expression().unwrap()].type_(),
                                );
                                self.nodes[bin].set_type(t);
                                self.finish_mutated_node(bin);
                                return;
                            }
                        }
                    }
                    Kind::ReturnStatement | Kind::ParenthesizedExpression => {
                        if self.nodes[parent].expression().is_some()
                            && self.nodes[tag].type_expression().is_some()
                        {
                            let t = self.add_deep_clone_reparse(
                                self.nodes[self.nodes[tag].type_expression().unwrap()].type_(),
                            );
                            let e = self.nodes[parent].expression();
                            let cast = self.make_new_cast(t, e, true /*isAssertion*/);
                            self.nodes[parent].set_expression(cast);
                            self.finish_mutated_node(parent);
                            return;
                        }
                    }
                    _ => {}
                }
                if let Some(fun) = get_function_like_host(&self.nodes, parent) {
                    let no_typed_params = self.nodes[fun]
                        .parameters()
                        .map(|params| {
                            params
                                .iter()
                                .all(|&param| self.nodes[param].type_().is_none())
                        })
                        .unwrap_or(true);
                    if self.nodes[fun].type_parameter_list().is_none()
                        && self.nodes[fun].type_().is_none()
                        && no_typed_params
                        && self.nodes[tag].type_expression().is_some()
                    {
                        let t = self.add_deep_clone_reparse(
                            self.nodes[self.nodes[tag].type_expression().unwrap()].type_(),
                        );
                        if let Some(data) = self.nodes[fun].data.function_like_data_mut() {
                            data.full_signature = t;
                        }
                        self.finish_mutated_node(fun);
                    }
                }
            }
            Kind::JSDocSatisfiesTag => {
                match self.nodes[parent].kind {
                    Kind::VariableStatement => {
                        if let Some(declaration_list) =
                            self.nodes[parent].as_variable_statement().declaration_list
                        {
                            let declarations: Vec<NodeId> = self.nodes[declaration_list]
                                .as_variable_declaration_list()
                                .declarations
                                .as_ref()
                                .map(|d| d.nodes.to_vec())
                                .unwrap_or_default();
                            for declaration in declarations {
                                if self.nodes[declaration].initializer().is_some()
                                    && self.nodes[tag].type_expression().is_some()
                                {
                                    let t = self.add_deep_clone_reparse(
                                        self.nodes[self.nodes[tag].type_expression().unwrap()]
                                            .type_(),
                                    );
                                    let init = self.nodes[declaration].initializer();
                                    let cast =
                                        self.make_new_cast(t, init, false /*isAssertion*/);
                                    self.nodes[declaration].set_initializer(cast);
                                    self.finish_mutated_node(declaration);
                                    break;
                                }
                            }
                        }
                    }
                    Kind::VariableDeclaration
                    | Kind::PropertyDeclaration
                    | Kind::PropertyAssignment => {
                        if self.nodes[parent].initializer().is_some()
                            && self.nodes[tag].type_expression().is_some()
                        {
                            let t = self.add_deep_clone_reparse(
                                self.nodes[self.nodes[tag].type_expression().unwrap()].type_(),
                            );
                            let init = self.nodes[parent].initializer();
                            let cast = self.make_new_cast(t, init, false /*isAssertion*/);
                            self.nodes[parent].set_initializer(cast);
                            self.finish_mutated_node(parent);
                        }
                    }
                    Kind::ShorthandPropertyAssignment => {
                        let object_assignment_initializer = self.nodes[parent]
                            .as_shorthand_property_assignment()
                            .object_assignment_initializer;
                        let type_expression =
                            self.nodes[tag].as_js_doc_satisfies_tag().type_expression;
                        if object_assignment_initializer.is_some() && type_expression.is_some() {
                            let t = self.add_deep_clone_reparse(
                                self.nodes[type_expression.unwrap()].type_(),
                            );
                            let cast = self.make_new_cast(
                                t,
                                object_assignment_initializer,
                                false, /*isAssertion*/
                            );
                            self.nodes[parent]
                                .as_shorthand_property_assignment_mut()
                                .object_assignment_initializer = cast;
                            self.finish_mutated_node(parent);
                        }
                    }
                    Kind::ReturnStatement
                    | Kind::ParenthesizedExpression
                    | Kind::ExportAssignment => {
                        if self.nodes[parent].expression().is_some()
                            && self.nodes[tag].type_expression().is_some()
                        {
                            let t = self.add_deep_clone_reparse(
                                self.nodes[self.nodes[tag].type_expression().unwrap()].type_(),
                            );
                            let e = self.nodes[parent].expression();
                            let cast = self.make_new_cast(t, e, false /*isAssertion*/);
                            self.nodes[parent].set_expression(cast);
                            self.finish_mutated_node(parent);
                        }
                    }
                    Kind::ExpressionStatement => {
                        let expression = self.nodes[parent].expression();
                        if expression.is_some_and(|e| self.nodes[e].kind == Kind::BinaryExpression)
                        {
                            let bin = expression.unwrap();
                            let kind = get_assignment_declaration_kind(bin, &self.nodes);
                            if kind != JsDeclarationKind::None
                                && self.nodes[tag].type_expression().is_some()
                            {
                                let t = self.add_deep_clone_reparse(
                                    self.nodes[self.nodes[tag].type_expression().unwrap()].type_(),
                                );
                                let right = self.nodes[bin].as_binary_expression().right;
                                let cast = self.make_new_cast(t, right, false /*isAssertion*/);
                                self.nodes[bin].as_binary_expression_mut().right = cast;
                                self.finish_mutated_node(bin);
                            }
                        }
                    }
                    _ => {}
                }
            }
            Kind::JSDocTemplateTag => {
                if let Some(fun) = get_function_like_host(&self.nodes, parent) {
                    if self.nodes[fun].type_parameters().is_none()
                        && self.nodes[fun]
                            .function_like_data()
                            .is_some_and(|d| d.full_signature.is_none())
                    {
                        let tps =
                            self.gather_type_parameters(js_doc, false /*typedefOrCallback*/);
                        if let Some(data) = self.nodes[fun].data.function_like_data_mut() {
                            data.type_parameters = tps;
                        }
                        self.finish_mutated_node(fun);
                    }
                } else if self.nodes[parent].kind == Kind::ClassDeclaration {
                    if self.nodes[parent]
                        .as_class_declaration()
                        .class_like_base
                        .type_parameters
                        .is_none()
                    {
                        let tps =
                            self.gather_type_parameters(js_doc, false /*typedefOrCallback*/);
                        self.nodes[parent]
                            .as_class_declaration_mut()
                            .class_like_base
                            .type_parameters = tps;
                        self.finish_mutated_node(parent);
                    }
                } else if self.nodes[parent].kind == Kind::ClassExpression {
                    if self.nodes[parent]
                        .as_class_expression()
                        .class_like_base
                        .type_parameters
                        .is_none()
                    {
                        let tps =
                            self.gather_type_parameters(js_doc, false /*typedefOrCallback*/);
                        self.nodes[parent]
                            .as_class_expression_mut()
                            .class_like_base
                            .type_parameters = tps;
                        self.finish_mutated_node(parent);
                    }
                }
            }
            Kind::JSDocParameterTag => {
                if let Some(fun) = get_function_like_host(&self.nodes, parent)
                    && self.nodes[fun]
                        .function_like_data()
                        .is_some_and(|d| d.full_signature.is_none())
                {
                    if let Some(param) = find_matching_parameter(&self.nodes, fun, tag, js_doc) {
                        let param_tag_type_expression = self.nodes[tag]
                            .as_js_doc_parameter_or_property_tag()
                            .type_expression;
                        if self.nodes[param].as_parameter_declaration().type_.is_none()
                            && param_tag_type_expression.is_some()
                        {
                            let t = self.reparse_jsdoc_type_literal(
                                self.nodes[param_tag_type_expression.unwrap()].type_(),
                            );
                            self.nodes[param].as_parameter_declaration_mut().type_ = t;
                        }
                        if self.nodes[param]
                            .as_parameter_declaration()
                            .question_token
                            .is_none()
                        {
                            let is_bracketed = self.nodes[tag]
                                .as_js_doc_parameter_or_property_tag()
                                .is_bracketed;
                            let question = self.make_question_if_optional(
                                is_bracketed,
                                param_tag_type_expression,
                                self.nodes[tag].loc,
                            );
                            if question.is_some() {
                                self.nodes[param]
                                    .as_parameter_declaration_mut()
                                    .question_token = question;
                            }
                        }
                        self.finish_mutated_node(param);
                    }
                }
            }
            Kind::JSDocThisTag => {
                if let Some(fun) = get_function_like_host(&self.nodes, parent) {
                    let params: Vec<NodeId> = self.nodes[fun]
                        .parameters()
                        .map(|p| p.to_vec())
                        .unwrap_or_default();
                    let first_is_this = params.first().is_some_and(|&p| {
                        self.nodes[p].name().is_some_and(|n| {
                            self.nodes[n].kind == Kind::ThisKeyword
                                || is_this_identifier(&self.nodes[n])
                        })
                    });
                    if params.is_empty() || !first_is_this {
                        let this_ident = self.factory.new_identifier(&mut self.nodes, "this");
                        let this_param = self.factory.new_parameter_declaration(
                            &mut self.nodes,
                            None, /* decorators */
                            None, /* modifiers */
                            Some(this_ident),
                            None, /* questionToken */
                            None, /* type */
                            None, /* initializer */
                        );
                        let type_expression = self.nodes[tag].as_js_doc_this_tag().type_expression;
                        if let Some(type_expression) = type_expression {
                            let t =
                                self.add_deep_clone_reparse(self.nodes[type_expression].type_());
                            self.nodes[this_param].as_parameter_declaration_mut().type_ = t;
                        }
                        let loc_node = self.nodes[tag].tag_name().unwrap_or(this_param);
                        self.finish_reparsed_node(this_param, loc_node);

                        let mut new_params = Vec::with_capacity(params.len() + 1);
                        new_params.push(this_param);
                        new_params.extend(params);

                        let params_loc = self.nodes[fun]
                            .parameter_list()
                            .map(|p| p.loc)
                            .unwrap_or_default();
                        let params_list = self.new_node_list(params_loc, new_params);
                        if let Some(data) = self.nodes[fun].data.function_like_data_mut() {
                            data.parameters = Some(params_list);
                        }
                        self.finish_mutated_node(fun);
                    }
                }
            }
            Kind::JSDocReturnTag => {
                if let Some(fun) = get_function_like_host(&self.nodes, parent)
                    && self.nodes[fun]
                        .function_like_data()
                        .is_some_and(|d| d.full_signature.is_none())
                {
                    if self.nodes[fun].type_().is_none()
                        && self.nodes[tag].type_expression().is_some()
                    {
                        let t = self.add_deep_clone_reparse(
                            self.nodes[self.nodes[tag].type_expression().unwrap()].type_(),
                        );
                        if let Some(data) = self.nodes[fun].data.function_like_data_mut() {
                            data.type_ = t;
                        }
                        self.finish_mutated_node(fun);
                    }
                }
            }
            Kind::JSDocReadonlyTag
            | Kind::JSDocPrivateTag
            | Kind::JSDocPublicTag
            | Kind::JSDocProtectedTag
            | Kind::JSDocOverrideTag => {
                let mut parent = parent;
                if self.nodes[parent].kind == Kind::ExpressionStatement {
                    if let Some(e) = self.nodes[parent].expression() {
                        parent = e;
                    }
                }
                match self.nodes[parent].kind {
                    Kind::MethodDeclaration | Kind::GetAccessor | Kind::SetAccessor => {
                        // In object literals these aren't class-like members, so JSDoc modifiers like @override
                        // or @readonly aren't real modifiers there; reparsing them produces spurious grammar errors (#4437).
                        if self.parsing_contexts & (1 << PC_OBJECT_LITERAL_MEMBERS) != 0 {
                            return;
                        }
                        self.reparse_add_modifier(tag, parent);
                    }
                    Kind::PropertyDeclaration | Kind::Constructor | Kind::BinaryExpression => {
                        self.reparse_add_modifier(tag, parent);
                    }
                    _ => {}
                }
            }
            Kind::JSDocImplementsTag => {
                if get_class_like_data(&self.nodes, parent).is_some() {
                    let class_name = self.nodes[tag].as_js_doc_implements_tag().class_name;
                    let Some(class_name) = class_name else { return };

                    let heritage_clauses = self.nodes[parent]
                        .class_like_data()
                        .and_then(|c| c.heritage_clauses.clone());
                    if let Some(ref clauses) = heritage_clauses {
                        let implements_clause = clauses.nodes.iter().copied().find(|&n| {
                            self.nodes[n].as_heritage_clause().token == Kind::ImplementsKeyword
                        });
                        if let Some(implements_clause) = implements_clause {
                            let cloned = self.add_deep_clone_reparse(Some(class_name));
                            if let Some(cloned) = cloned {
                                let mut types = self.nodes[implements_clause]
                                    .as_heritage_clause()
                                    .types
                                    .clone()
                                    .unwrap_or_default();
                                let mut ids = types.nodes.to_vec();
                                ids.push(cloned);
                                types.nodes = ids.into();
                                self.nodes[implements_clause].as_heritage_clause_mut().types =
                                    Some(types);
                            }
                            self.finish_mutated_node(implements_clause);
                            return;
                        }
                    }
                    let cloned = self.add_deep_clone_reparse(Some(class_name));
                    let types_list = self
                        .new_node_list(self.nodes[class_name].loc, cloned.into_iter().collect());

                    let heritage_clause = self.factory.new_heritage_clause(
                        &mut self.nodes,
                        Kind::ImplementsKeyword,
                        Some(types_list),
                    );
                    self.finish_reparsed_node(heritage_clause, class_name);

                    let has_clauses = self.nodes[parent]
                        .class_like_data()
                        .is_some_and(|c| c.heritage_clauses.is_some());
                    if !has_clauses {
                        let heritage_clauses =
                            self.new_node_list(self.nodes[class_name].loc, vec![heritage_clause]);
                        if let Some(data) = self.nodes[parent].data.class_like_data_mut() {
                            data.heritage_clauses = Some(heritage_clauses);
                        }
                    } else if let Some(data) = self.nodes[parent].data.class_like_data_mut()
                        && let Some(clauses) = data.heritage_clauses.as_mut()
                    {
                        let mut ids = clauses.nodes.to_vec();
                        ids.push(heritage_clause);
                        clauses.nodes = ids.into();
                    }
                    self.finish_mutated_node(parent);
                }
            }
            Kind::JSDocAugmentsTag => {
                if get_class_like_data(&self.nodes, parent).is_some() {
                    let heritage_clauses = self.nodes[parent]
                        .class_like_data()
                        .and_then(|c| c.heritage_clauses.clone());
                    if let Some(clauses) = heritage_clauses {
                        let extends_clause = clauses.nodes.iter().copied().find(|&n| {
                            self.nodes[n].as_heritage_clause().token == Kind::ExtendsKeyword
                        });
                        if let Some(extends_clause) = extends_clause {
                            let types = self.nodes[extends_clause]
                                .as_heritage_clause()
                                .types
                                .clone();
                            if let Some(types) = types
                                && types.nodes.len() == 1
                            {
                                let target = types.nodes[0];
                                // `tag.ClassName().AsExpressionWithTypeArguments()`
                                let Some(source) = self.nodes[tag].class_name() else {
                                    return;
                                };
                                let target_expr = self.nodes[target]
                                    .as_expression_with_type_arguments()
                                    .expression;
                                let source_expr = self.nodes[source]
                                    .as_expression_with_type_arguments()
                                    .expression;
                                if self.nodes[source].kind == Kind::ExpressionWithTypeArguments
                                    && let (Some(target_expr), Some(source_expr)) =
                                        (target_expr, source_expr)
                                    && has_same_property_access_name(
                                        &self.nodes[target_expr],
                                        &self.nodes[source_expr],
                                        &self.nodes,
                                    )
                                {
                                    let target_has_no_args = self.nodes[target]
                                        .as_expression_with_type_arguments()
                                        .type_arguments
                                        .is_none();
                                    let source_args = self.nodes[source]
                                        .as_expression_with_type_arguments()
                                        .type_arguments
                                        .clone();
                                    if target_has_no_args && let Some(source_args) = source_args {
                                        let args_loc = source_args.loc;
                                        let mut new_arguments =
                                            Vec::with_capacity(source_args.nodes.len());
                                        for &arg in source_args.nodes.iter() {
                                            if let Some(c) = self.add_deep_clone_reparse(Some(arg))
                                            {
                                                new_arguments.push(c);
                                            }
                                        }
                                        let list = self.new_node_list(args_loc, new_arguments);
                                        self.nodes[target]
                                            .as_expression_with_type_arguments_mut()
                                            .type_arguments = Some(list);
                                        self.finish_mutated_node(target);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    /// Shared tail of the readonly/private/public/protected/override case in
    /// `reparseHosted` — Go expresses this with `fallthrough`.
    fn reparse_add_modifier(&mut self, tag: NodeId, parent: NodeId) {
        let keyword = match self.nodes[tag].kind {
            Kind::JSDocReadonlyTag => Kind::ReadonlyKeyword,
            Kind::JSDocPrivateTag => Kind::PrivateKeyword,
            Kind::JSDocPublicTag => Kind::PublicKeyword,
            Kind::JSDocProtectedTag => Kind::ProtectedKeyword,
            Kind::JSDocOverrideTag => Kind::OverrideKeyword,
            _ => return,
        };
        let modifier = self.factory.new_token(&mut self.nodes, keyword);
        self.nodes[modifier].loc = self.nodes[tag].loc;
        self.nodes[modifier].flags = self.context_flags | NodeFlags::REPARSED;
        let (nodes, loc) = if self.nodes[parent].modifiers().is_none() {
            (vec![modifier], self.nodes[tag].loc)
        } else {
            let mut nodes = self.nodes[parent]
                .modifier_nodes()
                .map(|m| m.to_vec())
                .unwrap_or_default();
            nodes.push(modifier);
            let loc = self.nodes[parent]
                .modifiers()
                .map(|m| m.loc)
                .unwrap_or_default();
            (nodes, loc)
        };
        let list = self.new_modifier_list(loc, nodes);
        self.nodes[parent].set_modifiers(Some(list));
        self.finish_mutated_node(parent);
    }

    /// `func (p *Parser) makeQuestionIfOptional(parameter *ast.JSDocParameterOrPropertyTag) *ast.Node`
    ///
    /// PORT: takes the tag's fields by value since the tag's `NodeId` may be
    /// mutably borrowed elsewhere.
    fn make_question_if_optional(
        &mut self,
        is_bracketed: bool,
        type_expression: Option<NodeId>,
        loc: TextRange,
    ) -> Option<NodeId> {
        if is_bracketed
            || type_expression.is_some_and(|te| {
                self.nodes[te]
                    .type_()
                    .is_some_and(|t| self.nodes[t].kind == Kind::JSDocOptionalType)
            })
        {
            let question_token = self.factory.new_token(&mut self.nodes, Kind::QuestionToken);
            self.nodes[question_token].loc = loc;
            self.nodes[question_token].flags = self.context_flags | NodeFlags::REPARSED;
            return Some(question_token);
        }
        None
    }

    /// `func (p *Parser) makeNewCast(t *ast.TypeNode, e *ast.Node, isAssertion bool) *ast.Node`
    fn make_new_cast(
        &mut self,
        t: Option<NodeId>,
        e: Option<NodeId>,
        is_assertion: bool,
    ) -> Option<NodeId> {
        let e = e?;
        let assert = if is_assertion {
            self.factory.new_as_expression(&mut self.nodes, Some(e), t)
        } else {
            self.factory
                .new_satisfies_expression(&mut self.nodes, Some(e), t)
        };
        let pos = self.nodes[e].pos();
        let end = self.nodes[e].end();
        Some(self.finish_node_with_end(assert, pos, end))
    }

    /// `func (p *Parser) createExportModifier(locationNode *ast.Node) *ast.ModifierList`
    fn create_export_modifier(&mut self, location_node: NodeId) -> ModifierList {
        let export_modifier = self.factory.new_token(&mut self.nodes, Kind::ExportKeyword);
        self.nodes[export_modifier].loc = self.nodes[location_node].loc;
        self.nodes[export_modifier].flags = self.context_flags | NodeFlags::REPARSED;
        self.new_modifier_list(self.nodes[location_node].loc, vec![export_modifier])
    }

    /// `func (p *Parser) getInnermostNameOfJSDocNamespace(fullName *ast.Node) *ast.Node`
    ///
    /// Returns the innermost identifier from a JSDoc namespace chain
    /// (ModuleDeclaration). For a simple identifier, it returns the identifier
    /// itself. For "A.B.C", it returns the identifier "C".
    fn get_innermost_name_of_jsdoc_namespace(&self, full_name: Option<NodeId>) -> Option<NodeId> {
        let mut full_name = full_name?;
        while self.nodes[full_name].kind == Kind::ModuleDeclaration {
            let body = self.nodes[full_name].body();
            match body {
                None => return self.nodes[full_name].name(),
                Some(body) => full_name = body,
            }
        }
        Some(full_name)
    }

    /// `func (p *Parser) wrapInJSDocNamespace(fullName *ast.Node, statement *ast.Node, nested bool) *ast.Node`
    ///
    /// Wraps a statement (typically a type alias) in namespace declarations
    /// corresponding to a JSDoc dotted name. For example, given name "A.B.C"
    /// and a type alias for C, this produces:
    ///
    /// ```text
    /// namespace A { namespace B { type C = ... } }
    /// ```
    ///
    /// If the name is a simple identifier (not a ModuleDeclaration), it returns
    /// the statement as-is.
    fn wrap_in_jsdoc_namespace(
        &mut self,
        full_name: Option<NodeId>,
        statement: NodeId,
        nested: bool,
    ) -> NodeId {
        let Some(full_name) = full_name else {
            return statement;
        };
        if !is_module_declaration(&self.nodes[full_name]) {
            return statement;
        }
        // Recursively wrap from outermost to innermost. Inner namespaces always get an export modifier
        // so members are accessible via dotted access from outside. The outermost namespace is treated as
        // exported only in module files via IsImplicitlyExportedJSDocDeclaration (in the binder), so it
        // does not get an explicit export modifier here.
        let body = self.nodes[full_name].body();
        let wrapped = self.wrap_in_jsdoc_namespace(body, statement, true /*nested*/);
        let wrapped_list = self.new_node_list(self.nodes[full_name].loc, vec![wrapped]);
        let block = self
            .factory
            .new_module_block(&mut self.nodes, Some(wrapped_list));
        self.finish_reparsed_node(block, full_name);
        let mut modifiers = None;
        if nested {
            modifiers = Some(self.create_export_modifier(full_name));
        }
        let name = self.add_deep_clone_reparse(self.nodes[full_name].name());
        let result = self.factory.new_module_declaration(
            &mut self.nodes,
            modifiers,
            Kind::NamespaceKeyword,
            name,
            None,
            Some(block),
        );
        self.finish_reparsed_node(result, full_name);
        self.reparsed_clones.push(result);
        result
    }
}

/// `func findMatchingParameter(fun *ast.Node, parameterTag *ast.JSDocParameterOrPropertyTag, jsDoc *ast.Node) (*ast.ParameterDeclaration, bool)`
///
/// PORT: `parameterTag` is passed as the tag's `NodeId` (Go compares struct
/// pointers); `fun` and `jsDoc` are `NodeId`s resolved through `nodes`.
fn find_matching_parameter(
    nodes: &[Node],
    fun: NodeId,
    parameter_tag: NodeId,
    js_doc: NodeId,
) -> Option<NodeId> {
    let mut tag_index: i64 = -1;
    let mut param_count: i64 = -1;
    let tags: &[NodeId] = match &nodes[js_doc].as_js_doc().tags {
        Some(t) => &t.nodes,
        None => &[],
    };
    for &tag in tags {
        if nodes[tag].kind == Kind::JSDocParameterTag {
            param_count += 1;
            if tag == parameter_tag {
                tag_index = param_count;
                break;
            }
        }
    }
    let parameters = nodes[fun].parameters().unwrap_or(&[]);
    let parameter_tag_name = nodes[parameter_tag].name();
    for (parameter_index, &parameter) in parameters.iter().enumerate() {
        let param_name = nodes[parameter].name();
        if param_name.is_some_and(|n| nodes[n].kind == Kind::Identifier) {
            let name = param_name.unwrap();
            if parameter_tag_name.is_some_and(|n| nodes[n].kind == Kind::Identifier)
                && (nodes[name].text(nodes) == nodes[parameter_tag_name.unwrap()].text(nodes)
                    || (parameter_index as i64 == tag_index
                        && nodes[parameter_tag_name.unwrap()].text(nodes).is_empty()))
            {
                return Some(parameter);
            }
        } else if parameter_index as i64 == tag_index {
            return Some(parameter);
        }
    }
    None
}

/// `func skipSatisfiesExpressions(node *ast.Node) *ast.Node`
fn skip_satisfies_expressions(nodes: &[Node], node: Option<NodeId>) -> Option<NodeId> {
    let mut node = node;
    while let Some(n) = node {
        if nodes[n].kind != Kind::SatisfiesExpression {
            break;
        }
        node = nodes[n].expression();
    }
    node
}

/// `func getFunctionLikeHost(host *ast.Node) *ast.Node`
fn get_function_like_host(nodes: &[Node], host: NodeId) -> Option<NodeId> {
    let mut fun = Some(host);
    match nodes[host].kind {
        Kind::VariableStatement => {
            if let Some(declaration_list) = nodes[host].as_variable_statement().declaration_list {
                if let Some(declarations) = &nodes[declaration_list]
                    .as_variable_declaration_list()
                    .declarations
                    && !declarations.nodes.is_empty()
                {
                    fun = nodes[declarations.nodes[0]].initializer();
                }
            }
        }
        Kind::PropertyAssignment | Kind::PropertyDeclaration => {
            fun = nodes[host].initializer();
        }
        Kind::ExportAssignment | Kind::ReturnStatement => {
            fun = nodes[host].expression();
        }
        Kind::ExpressionStatement => {
            fun = nodes[host]
                .expression()
                .map(|e| get_right_most_assigned_expression(e, nodes));
        }
        _ => {}
    }
    let fun = skip_satisfies_expressions(nodes, fun);
    if is_function_like(fun, nodes) {
        return fun;
    }
    None
}

/// `func getClassLikeData(parent *ast.Node) *ast.ClassLikeBase`
///
/// PORT: returns whether `parent` is a class-like declaration; callers resolve
/// the data through `Node::class_like_data`.
fn get_class_like_data(nodes: &[Node], parent: NodeId) -> Option<NodeId> {
    match nodes[parent].kind {
        Kind::ClassDeclaration | Kind::ClassExpression => Some(parent),
        _ => None,
    }
}
