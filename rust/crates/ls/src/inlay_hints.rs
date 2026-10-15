// Ported from tsc/internal/ls/inlay_hints.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*ast.Node` → `NodeId`; `*ast.Symbol` → `SymbolId`; `*checker.Type` →
//   `TypeId`; `*checker.Signature` → `SignatureId`; `*checker.Checker` →
//   `Rc<RefCell<Checker>>`; `map[*ast.IdentifierNode]*ast.Symbol` →
//   `FxHashMap<NodeId, SymbolId>`.
// - Go's `node.ForEachChild(s.visit)` borrows the arena while `visit` may
//   mint token nodes (`astnav.GetStartOfNode`/`FindChildOfKind`), so
//   children are collected before recursing (same pattern as
//   `semantictokens.rs`/`symbols.rs`).
// - `nodes_mut` guards are held only in short scopes and are never live
//   across `type_to_type_node`/`type_predicate_to_type_predicate_node`,
//   which mint into a checked-out arena.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, Kind, Node, NodeFlags, NodeId, SymbolFlags, SymbolId};
use tsc_checker::checker_core::Checker;
use tsc_checker::types::{ElementFlags, TypeFlags, TypeId, TypePredicate};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::{TextPos, TextRange};
use tsc_debug as debug;
use tsc_evaluator as evaluator;
use tsc_lsconv::converters::{Converters, file_name_to_document_uri, source_file_script};
use tsc_lsproto::{self as lsproto};
use tsc_lsutil::userpreferences::{IncludeInlayParameterNameHints, QuotePreference};
use tsc_lsutil::userpreferences_generated::InlayHintsPreferences;
use tsc_lsutil::utilities::get_quote_preference;
use tsc_nodebuilder as nodebuilder;
use tsc_printer::{QuoteChar, escape_string};
use tsc_scanner::scanner::token_to_string;
use tsc_scanner::utilities::is_identifier_text;
use tsc_spanmap::Feature;
use tsc_stringutil::equate_string_case_insensitive;

use crate::api::Error;
use crate::languageservice::LanguageService;
use crate::utilities::get_leading_comment_ranges_of_node;

impl<'h> LanguageService<'h> {
    /// `ProvideInlayHint`.
    pub fn provide_inlay_hint(
        &self,
        ctx: &Context,
        params: &lsproto::InlayHintParams,
    ) -> Result<lsproto::InlayHintResponse, Error> {
        let user_preferences = self.user_preferences();
        let inlay_hint_preferences = &user_preferences.inlay_hints_preferences;
        if !is_any_inlay_hint_enabled(inlay_hint_preferences) {
            return Ok(lsproto::InlayHintsOrNull { inlay_hints: None });
        }

        let (program, file) = self.get_program_and_file(&params.text_document.uri);
        let nodes = program.nodes(file.file_index());
        let quote_preference = get_quote_preference(&nodes, file, user_preferences);

        let mapped_ranges = self.converters.from_lsp_range_intersecting_for_source_file(
            file,
            &nodes,
            params.range.clone(),
            Feature::InlayHints,
        );
        let mut result: Vec<lsproto::InlayHint> = Vec::with_capacity(mapped_ranges.len());
        for mapped in mapped_ranges {
            let projection = mapped.script.file;
            let (checker, done) = program.get_type_checker_for_file(ctx.clone(), projection);
            let mut inlay_hint_state = InlayHintState {
                ctx,
                span: mapped.span,
                preferences: inlay_hint_preferences,
                quote_preference: quote_preference.clone(),
                file: projection,
                checker: &checker,
                converters: &self.converters,
                program: &program,
                result: Vec::new(),
            };
            inlay_hint_state.visit(projection);
            result.extend(inlay_hint_state.result);
            done();
        }
        Ok(lsproto::InlayHintsOrNull {
            inlay_hints: Some(result),
        })
    }
}

/// `type inlayHintState struct`.
struct InlayHintState<'a, 'h> {
    /// `ctx`.
    ctx: &'a Context,
    /// `span`.
    span: TextRange,
    /// `preferences`.
    preferences: &'a InlayHintsPreferences,
    /// `quotePreference`.
    quote_preference: QuotePreference,
    /// `file`.
    file: NodeId,
    /// `checker`.
    checker: &'a Rc<RefCell<Checker>>,
    /// `converters`.
    converters: &'a Converters<'h>,
    /// `program` — for arena access beyond `file` (declaration names in
    /// `idToSymbol` and labeled tuple elements may live in other files).
    program: &'a Rc<Program>,
    /// `result`.
    result: Vec<lsproto::InlayHint>,
}

impl<'a, 'h> InlayHintState<'a, 'h> {
    /// `nodes` snapshot of `self.file`'s arena.
    fn nodes(&self) -> Rc<tsc_ast::NodeArenaBuf> {
        self.program.nodes(self.file.file_index())
    }

    /// `visit`.
    fn visit(&mut self, node: NodeId) -> bool {
        let nodes = self.nodes();
        if nodes[node].end() - nodes[node].pos() == 0
            || nodes[node].flags.intersects(NodeFlags::REPARSED)
        {
            return false;
        }

        match nodes[node].kind {
            Kind::ModuleDeclaration
            | Kind::ClassDeclaration
            | Kind::InterfaceDeclaration
            | Kind::FunctionDeclaration
            | Kind::ClassExpression
            | Kind::FunctionExpression
            | Kind::MethodDeclaration
            | Kind::ArrowFunction => {
                if self.ctx.is_cancelled() {
                    return true;
                }
            }
            _ => {}
        }

        if !self.span.intersects(&nodes[node].loc) {
            return false;
        }

        if ast::is_type_node(&nodes[node])
            && !ast::is_expression_with_type_arguments(&nodes[node])
        {
            return false;
        }

        if self.preferences.include_inlay_variable_type_hints.is_true()
            && ast::is_variable_declaration(&nodes[node])
        {
            self.visit_variable_like_declaration(node);
        } else if self
            .preferences
            .include_inlay_property_declaration_type_hints
            .is_true()
            && ast::is_property_declaration(&nodes[node])
        {
            self.visit_variable_like_declaration(node);
        } else if self
            .preferences
            .include_inlay_enum_member_value_hints
            .is_true()
            && ast::is_enum_member(&nodes[node])
        {
            self.visit_enum_member(node);
        } else if should_show_parameter_name_hints(self.preferences)
            && (ast::is_call_expression(&nodes[node]) || ast::is_new_expression(&nodes[node]))
        {
            self.visit_call_or_new_expression(node);
        } else {
            if self
                .preferences
                .include_inlay_function_parameter_type_hints
                .is_true()
                && ast::is_function_like_declaration(Some(node), &nodes)
                && ast::has_context_sensitive_parameters(&nodes[node], &nodes)
            {
                self.visit_function_like_for_parameter_type(node);
            }
            if self
                .preferences
                .include_inlay_function_like_return_type_hints
                .is_true()
                && is_signature_supporting_return_annotation(&nodes[node])
            {
                self.visit_function_declaration_like_for_return_type(node);
            }
        }
        // `n.ForEachChild(s.visit)` — collect the children first because the
        // recursion may mutably borrow the arena for token minting.
        let mut children: Vec<NodeId> = Vec::new();
        nodes[node].for_each_child(&nodes, &mut |child| {
            children.push(child);
            false
        });
        for child in children {
            if self.visit(child) {
                return true;
            }
        }
        false
    }

    /// `visitFunctionDeclarationLikeForReturnType` — `decl` is
    /// FunctionDeclaration | MethodDeclaration | GetAccessor |
    /// FunctionExpression | ArrowFunction.
    fn visit_function_declaration_like_for_return_type(&mut self, decl: NodeId) {
        let nodes = self.nodes();
        if ast::is_arrow_function(&nodes[decl]) {
            let open_paren = {
                let mut nodes_mut = self.program.nodes_mut(self.file.file_index());
                tsc_astnav::tokens::find_child_of_kind(
                    &mut nodes_mut,
                    self.file,
                    decl,
                    Kind::OpenParenToken,
                )
            };
            if open_paren.is_none() {
                return;
            }
        }

        if nodes[decl].type_().is_some() || nodes[decl].body().is_none() {
            return;
        }

        let signature = self.checker.borrow_mut().get_signature_from_declaration(decl);
        if signature.is_none() {
            return;
        }

        let type_predicate = self
            .checker
            .borrow_mut()
            .get_type_predicate_of_signature(signature);

        if let Some(type_predicate) = &type_predicate
            && type_predicate.t().is_some()
        {
            let hint_parts = self.type_predicate_to_inlay_hint_parts(type_predicate);
            let position = self.get_type_annotation_position(&nodes, decl);
            self.add_type_hints(&nodes, hint_parts, position);
            return;
        }

        let return_type = self
            .checker
            .borrow_mut()
            .get_return_type_of_signature(signature);
        if is_module_reference_type(&self.checker.borrow(), return_type) {
            return;
        }

        let hint_parts = self.type_to_inlay_hint_parts(return_type);
        let position = self.get_type_annotation_position(&nodes, decl);
        self.add_type_hints(&nodes, hint_parts, position);
    }

    /// `visitCallOrNewExpression`.
    fn visit_call_or_new_expression(&mut self, expr: NodeId) {
        let nodes = self.nodes();
        let Some(args) = nodes[expr].arguments() else {
            return;
        };
        let args: Vec<NodeId> = args.to_vec();
        if args.is_empty() {
            return;
        }

        let Some(signature) = self.checker.borrow_mut().get_resolved_signature_api(expr) else {
            return;
        };

        let mut signature_param_pos = 0usize;
        for original_arg in args {
            let arg = ast::skip_parentheses(original_arg, &nodes);
            if should_show_literal_parameter_name_hints_only(self.preferences)
                && !is_hintable_literal(&nodes[arg], &nodes)
            {
                signature_param_pos += 1;
                continue;
            }

            let mut spread_args = 0usize;
            if ast::is_spread_element(&nodes[arg]) {
                let spread_type = self
                    .checker
                    .borrow_mut()
                    .get_type_at_location(nodes[arg].expression().expect("spread expression"));
                if tsc_checker::checker_core::is_tuple_type(&self.checker.borrow().types, spread_type)
                {
                    let cb = self.checker.borrow();
                    let target = cb.types.target_tuple_type(spread_type).expect("tuple target");
                    let tuple = cb.types.get_ref(target).as_tuple_type();
                    let element_flags = tuple.element_flags();
                    let fixed_length = tuple.fixed_length();
                    if fixed_length == 0 {
                        continue;
                    }
                    let first_optional_index = element_flags
                        .iter()
                        .position(|f| !f.intersects(ElementFlags::REQUIRED));
                    let required_args = first_optional_index.unwrap_or(fixed_length);
                    if required_args > 0 {
                        spread_args = required_args;
                    }
                }
            }

            let identifier_info =
                self.get_parameter_identifier_info_at_position(signature, signature_param_pos);
            signature_param_pos += if spread_args > 0 { spread_args } else { 1 };
            let Some(identifier_info) = identifier_info else {
                return;
            };

            let parameter = identifier_info.parameter;
            let parameter_name = identifier_info.name;
            let is_first_variadic_argument = identifier_info.is_rest_parameter;
            let parameter_name_not_same_as_argument = self
                .preferences
                .include_inlay_parameter_name_hints_when_argument_matches_name
                .is_true()
                || !identifier_or_access_expression_postfix_matches_parameter_name(
                    &nodes,
                    arg,
                    &parameter_name,
                );
            if !parameter_name_not_same_as_argument && !is_first_variadic_argument {
                continue;
            }

            if self.leading_comments_contains_parameter_name(arg, &parameter_name) {
                continue;
            }

            let position = {
                let mut nodes_mut = self.program.nodes_mut(self.file.file_index());
                tsc_astnav::tokens::get_start_of_node(
                    &mut nodes_mut,
                    self.file,
                    original_arg,
                    false, /*includeJSDoc*/
                )
            };
            self.add_parameter_hints(
                &nodes,
                &parameter_name,
                parameter,
                position,
                is_first_variadic_argument,
            );
        }
    }

    /// `visitEnumMember`.
    fn visit_enum_member(&mut self, member: NodeId) {
        let nodes = self.nodes();
        if nodes[member].initializer().is_some() {
            return;
        }

        let enum_value = self.checker.borrow_mut().get_constant_value(member);
        if let Some(enum_value) = enum_value {
            self.add_enum_member_value_hints(
                &nodes,
                evaluator::any_to_string(&enum_value),
                nodes[member].end(),
            );
        }
    }

    /// `visitVariableLikeDeclaration`.
    fn visit_variable_like_declaration(&mut self, decl: NodeId) {
        let nodes = self.nodes();
        if (nodes[decl].initializer().is_none()
            && !(ast::is_property_declaration(&nodes[decl]) && {
                let t = self.checker.borrow_mut().get_type_at_location(decl);
                !self
                    .checker
                    .borrow()
                    .types
                    .get_ref(t)
                    .flags()
                    .intersects(TypeFlags::ANY)
            }))
            || nodes[decl]
                .name()
                .is_some_and(|n| ast::is_binding_pattern(&nodes[n]))
            || (ast::is_variable_declaration(&nodes[decl])
                && !is_hintable_declaration(&nodes, decl))
        {
            return;
        }

        if nodes[decl].type_().is_some() {
            return;
        }

        let declaration_type = self.checker.borrow_mut().get_type_at_location(decl);
        if is_module_reference_type(&self.checker.borrow(), declaration_type) {
            return;
        }

        let hint_parts = self.type_to_inlay_hint_parts(declaration_type);
        let mut hint_text = String::new();
        if let Some(s) = &hint_parts.string {
            hint_text = s.clone();
        } else if let Some(parts) = &hint_parts.inlay_hint_label_parts {
            for part in parts {
                hint_text.push_str(&part.value);
            }
        }
        let name = nodes[decl].name();
        if !self
            .preferences
            .include_inlay_variable_type_hints_when_type_matches_name
            .is_true()
            && !name.is_some_and(|n| ast::is_computed_property_name(&nodes[n]))
            && name.is_some_and(|n| {
                equate_string_case_insensitive(
                    nodes[n].text(&nodes).as_bytes(),
                    hint_text.as_bytes(),
                )
            })
        {
            return;
        }
        self.add_type_hints(&nodes, hint_parts, nodes[name.expect("name")].end());
    }

    /// `visitFunctionLikeForParameterType`.
    fn visit_function_like_for_parameter_type(&mut self, node: NodeId) {
        let signature = self.checker.borrow_mut().get_signature_from_declaration(node);
        if signature.is_none() {
            return;
        }

        let nodes = self.nodes();
        let parameters = nodes[node]
            .parameters()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        let mut pos = 0usize;
        for param in parameters {
            if is_hintable_declaration(&nodes, param) {
                let symbol = if ast::is_this_parameter(&nodes[param], &nodes) {
                    self.checker
                        .borrow()
                        .signature_arena
                        .get(signature)
                        .this_parameter
                } else {
                    Some(
                        self.checker
                            .borrow()
                            .signature_arena
                            .get(signature)
                            .parameters[pos],
                    )
                };
                self.add_parameter_type_hint(&nodes, param, symbol);
            }
            if ast::is_this_parameter(&nodes[param], &nodes) {
                continue;
            }
            pos += 1;
        }
    }

    /// `addParameterTypeHint`.
    fn add_parameter_type_hint(
        &mut self,
        nodes: &[Node],
        node: NodeId,
        symbol: Option<SymbolId>,
    ) {
        if nodes[node].type_().is_some() {
            return;
        }
        let Some(symbol) = symbol else {
            return;
        };
        let Some(type_hints) = self.get_parameter_declaration_type_hints(symbol) else {
            return;
        };
        let pos = if let Some(question_token) = nodes[node].question_token(nodes) {
            nodes[question_token].end()
        } else {
            nodes[nodes[node].name().expect("parameter name")].end()
        };
        self.add_type_hints(nodes, type_hints, pos);
    }

    /// `getParameterDeclarationTypeHints`.
    fn get_parameter_declaration_type_hints(
        &mut self,
        symbol: SymbolId,
    ) -> Option<lsproto::StringOrInlayHintLabelParts> {
        let value_declaration = self
            .checker
            .borrow()
            .symbol_arena
            .get_ref(symbol)
            .value_declaration;
        let Some(value_declaration) = value_declaration else {
            return None;
        };
        {
            let decl_nodes = self.program.arena_of(value_declaration);
            if !ast::is_parameter_declaration(&decl_nodes[value_declaration]) {
                return None;
            }
        }

        let signature_param_type = self
            .checker
            .borrow_mut()
            .get_type_of_symbol_at_location(symbol, Some(value_declaration));
        if is_module_reference_type(&self.checker.borrow(), signature_param_type) {
            return None;
        }

        Some(self.type_to_inlay_hint_parts(signature_param_type))
    }

    /// `typeToInlayHintParts`.
    fn type_to_inlay_hint_parts(
        &mut self,
        t: TypeId,
    ) -> lsproto::StringOrInlayHintLabelParts {
        let flags = nodebuilder::Flags::IGNORE_ERRORS
            | nodebuilder::Flags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
            | nodebuilder::Flags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE;
        // !!! Avoid type node reuse so we collect identifier symbols.
        let (type_node, id_to_symbol) = self
            .checker
            .borrow_mut()
            .type_to_type_node_with_id_map(t, None, flags);
        debug::assert_!(type_node.is_some(), "should always get typenode");
        lsproto::StringOrInlayHintLabelParts {
            inlay_hint_label_parts: Some(
                self.get_inlay_hint_label_parts(type_node.unwrap(), &id_to_symbol),
            ),
            ..Default::default()
        }
    }

    /// `typePredicateToInlayHintParts`.
    fn type_predicate_to_inlay_hint_parts(
        &mut self,
        type_predicate: &TypePredicate,
    ) -> lsproto::StringOrInlayHintLabelParts {
        let flags = nodebuilder::Flags::IGNORE_ERRORS
            | nodebuilder::Flags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
            | nodebuilder::Flags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE;
        // !!! Avoid type node reuse so we collect identifier symbols.
        let (type_node, id_to_symbol) = type_predicate_to_type_predicate_node_with_map(
            &mut self.checker.borrow_mut(),
            Some(type_predicate),
            None,
            flags,
        );
        debug::assert_!(type_node.is_some(), "should always get typePredicateNode");
        lsproto::StringOrInlayHintLabelParts {
            inlay_hint_label_parts: Some(
                self.get_inlay_hint_label_parts(type_node.unwrap(), &id_to_symbol),
            ),
            ..Default::default()
        }
    }

    /// `addTypeHints`.
    fn add_type_hints(
        &mut self,
        nodes: &[Node],
        mut hint: lsproto::StringOrInlayHintLabelParts,
        position: TextPos,
    ) {
        let (lsp_position, fidelity) = self.converters.to_lsp_position_for_feature(
            &source_file_script(self.file, nodes),
            position,
            Feature::InlayHints,
        );
        if fidelity.is_none() {
            return;
        }
        if let Some(s) = hint.string {
            hint.string = Some(format!(": {s}"));
        } else if let Some(parts) = hint.inlay_hint_label_parts {
            let mut prefixed = Vec::with_capacity(parts.len() + 1);
            prefixed.push(lsproto::InlayHintLabelPart {
                value: ": ".to_string(),
                ..Default::default()
            });
            prefixed.extend(parts);
            hint.inlay_hint_label_parts = Some(prefixed);
        }
        self.result.push(lsproto::InlayHint {
            label: hint,
            position: lsp_position,
            kind: Some(lsproto::InlayHintKind::Type),
            padding_left: Some(true),
            ..Default::default()
        });
    }

    /// `addEnumMemberValueHints`.
    fn add_enum_member_value_hints(
        &mut self,
        nodes: &[Node],
        text: String,
        position: TextPos,
    ) {
        let (lsp_position, fidelity) = self.converters.to_lsp_position_for_feature(
            &source_file_script(self.file, nodes),
            position,
            Feature::InlayHints,
        );
        if fidelity.is_none() {
            return;
        }
        self.result.push(lsproto::InlayHint {
            label: lsproto::StringOrInlayHintLabelParts {
                string: Some(format!("= {text}")),
                ..Default::default()
            },
            position: lsp_position,
            padding_left: Some(true),
            ..Default::default()
        });
    }

    /// `addParameterHints`.
    fn add_parameter_hints(
        &mut self,
        nodes: &[Node],
        text: &str,
        parameter: NodeId,
        position: TextPos,
        is_first_variadic_argument: bool,
    ) {
        let (lsp_position, fidelity) = self.converters.to_lsp_position_for_feature(
            &source_file_script(self.file, nodes),
            position,
            Feature::InlayHints,
        );
        if fidelity.is_none() {
            return;
        }
        let hint_text = format!("{}{text}", if is_first_variadic_argument { "..." } else { "" });
        let display_parts = vec![
            self.get_node_display_part(&hint_text, parameter),
            lsproto::InlayHintLabelPart {
                value: ":".to_string(),
                ..Default::default()
            },
        ];
        let label_parts = lsproto::StringOrInlayHintLabelParts {
            inlay_hint_label_parts: Some(display_parts),
            ..Default::default()
        };

        self.result.push(lsproto::InlayHint {
            label: label_parts,
            position: lsp_position,
            kind: Some(lsproto::InlayHintKind::Parameter),
            padding_right: Some(true),
            ..Default::default()
        });
    }

    /// `getInlayHintLabelParts`.
    fn get_inlay_hint_label_parts(
        &self,
        node: NodeId,
        id_to_symbol: &FxHashMap<NodeId, SymbolId>,
    ) -> Vec<lsproto::InlayHintLabelPart> {
        let tnodes = self.program.arena_of(node);
        let mut parts: Vec<lsproto::InlayHintLabelPart> = Vec::new();
        self.visit_for_display_parts(&tnodes, node, id_to_symbol, &mut parts);
        parts
    }

    /// `visitForDisplayParts` — `tnodes` is the arena containing `node`
    /// (the node builder's output arena).
    fn visit_for_display_parts(
        &self,
        tnodes: &[Node],
        node: NodeId,
        id_to_symbol: &FxHashMap<NodeId, SymbolId>,
        parts: &mut Vec<lsproto::InlayHintLabelPart>,
    ) {
        let token_string = token_to_string(tnodes[node].kind);
        if !token_string.is_empty() {
            parts.push(lsproto::InlayHintLabelPart {
                value: token_string.to_string(),
                ..Default::default()
            });
            return;
        }

        if ast::is_literal_expression(&tnodes[node]) {
            parts.push(lsproto::InlayHintLabelPart {
                value: self.get_literal_text(tnodes, node),
                ..Default::default()
            });
            return;
        }

        match tnodes[node].kind {
            Kind::Identifier => {
                let identifier_text = tnodes[node].text(tnodes).into_owned();
                let mut name = None;
                if let Some(&symbol) = id_to_symbol.get(&node) {
                    let declarations = self
                        .checker
                        .borrow()
                        .symbol_arena
                        .get_ref(symbol)
                        .declarations
                        .clone();
                    if let Some(&decl) = declarations.first() {
                        let decl_nodes = self.program.arena_of(decl);
                        name = ast::get_name_of_declaration(Some(decl), &decl_nodes);
                    }
                }
                if let Some(name) = name {
                    parts.push(self.get_node_display_part(&identifier_text, name));
                } else {
                    parts.push(lsproto::InlayHintLabelPart {
                        value: identifier_text,
                        ..Default::default()
                    });
                }
            }
            Kind::QualifiedName => {
                let d = tnodes[node].as_qualified_name();
                let (left, right) = (d.left, d.right);
                if let Some(left) = left {
                    self.visit_for_display_parts(tnodes, left, id_to_symbol, parts);
                }
                parts.push(label_part("."));
                if let Some(right) = right {
                    self.visit_for_display_parts(tnodes, right, id_to_symbol, parts);
                }
            }
            Kind::TypePredicate => {
                let d = tnodes[node].as_type_predicate_node();
                let (asserts_modifier, parameter_name) = (d.asserts_modifier, d.parameter_name);
                if asserts_modifier.is_some() {
                    parts.push(label_part("asserts "));
                }
                if let Some(parameter_name) = parameter_name {
                    self.visit_for_display_parts(tnodes, parameter_name, id_to_symbol, parts);
                }
                if let Some(t) = tnodes[node].type_() {
                    parts.push(label_part(" is "));
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::TypeReference => {
                let type_name = tnodes[node].as_type_reference_node().type_name;
                if let Some(type_name) = type_name {
                    self.visit_for_display_parts(tnodes, type_name, id_to_symbol, parts);
                }
                let type_args: Vec<NodeId> = tnodes[node]
                    .type_arguments()
                    .map(|t| t.to_vec())
                    .unwrap_or_default();
                if !type_args.is_empty() {
                    parts.push(label_part("<"));
                    self.visit_display_part_list(tnodes, &type_args, ",", id_to_symbol, parts);
                    parts.push(label_part(">"));
                }
            }
            Kind::TypeParameter => {
                let d = tnodes[node].as_type_parameter_declaration();
                let modifiers: Vec<NodeId> = tnodes[node]
                    .modifier_nodes()
                    .map(|m| m.to_vec())
                    .unwrap_or_default();
                if !modifiers.is_empty() {
                    self.visit_display_part_list(tnodes, &modifiers, "", id_to_symbol, parts);
                }
                if let Some(name) = tnodes[node].name() {
                    self.visit_for_display_parts(tnodes, name, id_to_symbol, parts);
                }
                if let Some(constraint) = d.constraint {
                    parts.push(label_part(" extends "));
                    self.visit_for_display_parts(tnodes, constraint, id_to_symbol, parts);
                }
                if let Some(default_type) = d.default_type {
                    parts.push(label_part(" = "));
                    self.visit_for_display_parts(tnodes, default_type, id_to_symbol, parts);
                }
            }
            Kind::Parameter => {
                let d = tnodes[node].as_parameter_declaration();
                let modifiers: Vec<NodeId> = tnodes[node]
                    .modifier_nodes()
                    .map(|m| m.to_vec())
                    .unwrap_or_default();
                if !modifiers.is_empty() {
                    self.visit_display_part_list(tnodes, &modifiers, " ", id_to_symbol, parts);
                }
                if d.dot_dot_dot_token.is_some() {
                    parts.push(label_part("..."));
                }
                if let Some(name) = tnodes[node].name() {
                    self.visit_for_display_parts(tnodes, name, id_to_symbol, parts);
                }
                if tnodes[node].question_token(tnodes).is_some() {
                    parts.push(label_part("?"));
                }
                if let Some(t) = tnodes[node].type_() {
                    parts.push(label_part(": "));
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::ConstructorType => {
                parts.push(label_part("new "));
                self.visit_parameters_and_type_parameters(tnodes, node, id_to_symbol, parts);
                parts.push(label_part(" => "));
                if let Some(t) = tnodes[node].type_() {
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::TypeQuery => {
                parts.push(label_part("typeof "));
                let expr_name = tnodes[node].as_type_query_node().expr_name;
                if let Some(expr_name) = expr_name {
                    self.visit_for_display_parts(tnodes, expr_name, id_to_symbol, parts);
                }
                let type_args: Vec<NodeId> = tnodes[node]
                    .type_arguments()
                    .map(|t| t.to_vec())
                    .unwrap_or_default();
                if !type_args.is_empty() {
                    parts.push(label_part("<"));
                    self.visit_display_part_list(tnodes, &type_args, ", ", id_to_symbol, parts);
                    parts.push(label_part(">"));
                }
            }
            Kind::TypeLiteral => {
                parts.push(label_part("{"));
                let members: Vec<NodeId> = tnodes[node]
                    .members()
                    .map(|m| m.to_vec())
                    .unwrap_or_default();
                if !members.is_empty() {
                    parts.push(label_part(" "));
                    self.visit_display_part_list(tnodes, &members, "; ", id_to_symbol, parts);
                    parts.push(label_part(" "));
                }
                parts.push(label_part("}"));
            }
            Kind::ArrayType => {
                let element_type = tnodes[node].as_array_type_node().element_type;
                if let Some(element_type) = element_type {
                    self.visit_for_display_parts(tnodes, element_type, id_to_symbol, parts);
                }
                parts.push(label_part("[]"));
            }
            Kind::TupleType => {
                parts.push(label_part("["));
                let elements: Vec<NodeId> = tnodes[node]
                    .elements()
                    .map(|e| e.to_vec())
                    .unwrap_or_default();
                self.visit_display_part_list(tnodes, &elements, ", ", id_to_symbol, parts);
                parts.push(label_part("]"));
            }
            Kind::NamedTupleMember => {
                let d = tnodes[node].as_named_tuple_member();
                if d.dot_dot_dot_token.is_some() {
                    parts.push(label_part("..."));
                }
                if let Some(name) = tnodes[node].name() {
                    self.visit_for_display_parts(tnodes, name, id_to_symbol, parts);
                }
                if tnodes[node].question_token(tnodes).is_some() {
                    parts.push(label_part("?"));
                }
                parts.push(label_part(": "));
                if let Some(t) = tnodes[node].type_() {
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::OptionalType => {
                if let Some(t) = tnodes[node].type_() {
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
                parts.push(label_part("?"));
            }
            Kind::RestType => {
                parts.push(label_part("..."));
                if let Some(t) = tnodes[node].type_() {
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::UnionType => {
                if let Some(types) = &tnodes[node]
                    .as_union_type_node()
                    .union_or_intersection_type_node_base
                    .types
                {
                    let list: Vec<NodeId> = types.nodes().to_vec();
                    self.visit_display_part_list(tnodes, &list, " | ", id_to_symbol, parts);
                }
            }
            Kind::IntersectionType => {
                if let Some(types) = &tnodes[node]
                    .as_intersection_type_node()
                    .union_or_intersection_type_node_base
                    .types
                {
                    let list: Vec<NodeId> = types.nodes().to_vec();
                    self.visit_display_part_list(tnodes, &list, " & ", id_to_symbol, parts);
                }
            }
            Kind::ConditionalType => {
                let d = tnodes[node].as_conditional_type_node();
                let (check_type, extends_type, true_type, false_type) =
                    (d.check_type, d.extends_type, d.true_type, d.false_type);
                if let Some(check_type) = check_type {
                    self.visit_for_display_parts(tnodes, check_type, id_to_symbol, parts);
                }
                parts.push(label_part(" extends "));
                if let Some(extends_type) = extends_type {
                    self.visit_for_display_parts(tnodes, extends_type, id_to_symbol, parts);
                }
                parts.push(label_part(" ? "));
                if let Some(true_type) = true_type {
                    self.visit_for_display_parts(tnodes, true_type, id_to_symbol, parts);
                }
                parts.push(label_part(" : "));
                if let Some(false_type) = false_type {
                    self.visit_for_display_parts(tnodes, false_type, id_to_symbol, parts);
                }
            }
            Kind::InferType => {
                parts.push(label_part("infer "));
                let type_parameter = tnodes[node].as_infer_type_node().type_parameter;
                if let Some(type_parameter) = type_parameter {
                    self.visit_for_display_parts(tnodes, type_parameter, id_to_symbol, parts);
                }
            }
            Kind::ParenthesizedType => {
                parts.push(label_part("("));
                if let Some(t) = tnodes[node].type_() {
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
                parts.push(label_part(")"));
            }
            Kind::TypeOperator => {
                let operator = tnodes[node].as_type_operator_node().operator;
                parts.push(label_part(token_to_string(operator)));
                if let Some(t) = tnodes[node].type_() {
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::IndexedAccessType => {
                let d = tnodes[node].as_indexed_access_type_node();
                let (object_type, index_type) = (d.object_type, d.index_type);
                if let Some(object_type) = object_type {
                    self.visit_for_display_parts(tnodes, object_type, id_to_symbol, parts);
                }
                parts.push(label_part("["));
                if let Some(index_type) = index_type {
                    self.visit_for_display_parts(tnodes, index_type, id_to_symbol, parts);
                }
                parts.push(label_part("]"));
            }
            Kind::MappedType => {
                parts.push(label_part("{ "));
                let d = tnodes[node].as_mapped_type_node();
                let (readonly_token, type_parameter, name_type) =
                    (d.readonly_token, d.type_parameter, d.name_type);
                if let Some(readonly_token) = readonly_token {
                    if tnodes[readonly_token].kind == Kind::PlusToken {
                        parts.push(label_part("+"));
                    } else if tnodes[readonly_token].kind == Kind::MinusToken {
                        parts.push(label_part("-"));
                    }
                    parts.push(label_part("readonly "));
                }
                parts.push(label_part("["));
                if let Some(type_parameter) = type_parameter {
                    self.visit_for_display_parts(tnodes, type_parameter, id_to_symbol, parts);
                }
                if let Some(name_type) = name_type {
                    parts.push(label_part(" as "));
                    self.visit_for_display_parts(tnodes, name_type, id_to_symbol, parts);
                }
                parts.push(label_part("]"));
                if let Some(question_token) = tnodes[node].question_token(tnodes) {
                    if tnodes[question_token].kind == Kind::PlusToken {
                        parts.push(label_part("+"));
                    } else if tnodes[question_token].kind == Kind::MinusToken {
                        parts.push(label_part("-"));
                    }
                    parts.push(label_part("?"));
                }
                parts.push(label_part(": "));
                if let Some(t) = tnodes[node].type_() {
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
                parts.push(label_part("; }"));
            }
            Kind::LiteralType => {
                let literal = tnodes[node].as_literal_type_node().literal;
                if let Some(literal) = literal {
                    self.visit_for_display_parts(tnodes, literal, id_to_symbol, parts);
                }
            }
            Kind::FunctionType => {
                self.visit_parameters_and_type_parameters(tnodes, node, id_to_symbol, parts);
                parts.push(label_part(" => "));
                if let Some(t) = tnodes[node].type_() {
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::ImportType => {
                let d = tnodes[node].as_import_type_node();
                let (is_type_of, argument, qualifier) = (d.is_type_of, d.argument, d.qualifier);
                if is_type_of {
                    parts.push(label_part("typeof "));
                }
                parts.push(label_part("import("));
                if let Some(argument) = argument {
                    self.visit_for_display_parts(tnodes, argument, id_to_symbol, parts);
                }
                parts.push(label_part(")"));
                if let Some(qualifier) = qualifier {
                    parts.push(label_part("."));
                    self.visit_for_display_parts(tnodes, qualifier, id_to_symbol, parts);
                }
                let type_args: Vec<NodeId> = tnodes[node]
                    .type_arguments()
                    .map(|t| t.to_vec())
                    .unwrap_or_default();
                if !type_args.is_empty() {
                    parts.push(label_part("<"));
                    self.visit_display_part_list(tnodes, &type_args, ", ", id_to_symbol, parts);
                    parts.push(label_part(">"));
                }
            }
            Kind::PropertySignature => {
                let modifiers: Vec<NodeId> = tnodes[node]
                    .modifier_nodes()
                    .map(|m| m.to_vec())
                    .unwrap_or_default();
                if !modifiers.is_empty() {
                    self.visit_display_part_list(tnodes, &modifiers, " ", id_to_symbol, parts);
                    parts.push(label_part(" "));
                }
                if let Some(name) = tnodes[node].name() {
                    self.visit_for_display_parts(tnodes, name, id_to_symbol, parts);
                }
                if let Some(postfix_token) = tnodes[node].postfix_token() {
                    parts.push(label_part(token_to_string(tnodes[postfix_token].kind)));
                }
                if let Some(t) = tnodes[node].type_() {
                    parts.push(label_part(": "));
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::IndexSignature => {
                parts.push(label_part("["));
                let parameters: Vec<NodeId> = tnodes[node]
                    .parameters()
                    .map(|p| p.to_vec())
                    .unwrap_or_default();
                self.visit_display_part_list(tnodes, &parameters, ", ", id_to_symbol, parts);
                parts.push(label_part("]"));
                if let Some(t) = tnodes[node].type_() {
                    parts.push(label_part(": "));
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::MethodSignature => {
                let modifiers: Vec<NodeId> = tnodes[node]
                    .modifier_nodes()
                    .map(|m| m.to_vec())
                    .unwrap_or_default();
                if !modifiers.is_empty() {
                    self.visit_display_part_list(tnodes, &modifiers, " ", id_to_symbol, parts);
                    parts.push(label_part(" "));
                }
                if let Some(name) = tnodes[node].name() {
                    self.visit_for_display_parts(tnodes, name, id_to_symbol, parts);
                }
                if let Some(postfix_token) = tnodes[node].postfix_token() {
                    parts.push(label_part(token_to_string(tnodes[postfix_token].kind)));
                }
                self.visit_parameters_and_type_parameters(tnodes, node, id_to_symbol, parts);
                if let Some(t) = tnodes[node].type_() {
                    parts.push(label_part(": "));
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::CallSignature => {
                self.visit_parameters_and_type_parameters(tnodes, node, id_to_symbol, parts);
                if let Some(t) = tnodes[node].type_() {
                    parts.push(label_part(": "));
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::ConstructSignature => {
                parts.push(label_part("new "));
                self.visit_parameters_and_type_parameters(tnodes, node, id_to_symbol, parts);
                if let Some(t) = tnodes[node].type_() {
                    parts.push(label_part(": "));
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
            }
            Kind::ArrayBindingPattern => {
                parts.push(label_part("["));
                let elements: Vec<NodeId> = tnodes[node]
                    .elements()
                    .map(|e| e.to_vec())
                    .unwrap_or_default();
                self.visit_display_part_list(tnodes, &elements, ", ", id_to_symbol, parts);
                parts.push(label_part("]"));
            }
            Kind::ObjectBindingPattern => {
                parts.push(label_part("{"));
                let elements: Vec<NodeId> = tnodes[node]
                    .elements()
                    .map(|e| e.to_vec())
                    .unwrap_or_default();
                if !elements.is_empty() {
                    parts.push(label_part(" "));
                    self.visit_display_part_list(tnodes, &elements, ", ", id_to_symbol, parts);
                    parts.push(label_part(" "));
                }
                parts.push(label_part("}"));
            }
            Kind::BindingElement => {
                if let Some(name) = tnodes[node].name() {
                    self.visit_for_display_parts(tnodes, name, id_to_symbol, parts);
                }
            }
            Kind::PrefixUnaryExpression => {
                let d = tnodes[node].as_prefix_unary_expression();
                let (operator, operand) = (d.operator, d.operand);
                parts.push(label_part(token_to_string(operator)));
                if let Some(operand) = operand {
                    self.visit_for_display_parts(tnodes, operand, id_to_symbol, parts);
                }
            }
            Kind::TemplateLiteralType => {
                let d = tnodes[node].as_template_literal_type_node();
                let head = d.head;
                let spans: Vec<NodeId> = d
                    .template_spans
                    .as_ref()
                    .map(|s| s.nodes().to_vec())
                    .unwrap_or_default();
                if let Some(head) = head {
                    self.visit_for_display_parts(tnodes, head, id_to_symbol, parts);
                }
                for span in spans {
                    self.visit_for_display_parts(tnodes, span, id_to_symbol, parts);
                }
            }
            Kind::TemplateHead => {
                parts.push(label_part(&self.get_literal_text(tnodes, node)));
            }
            Kind::TemplateLiteralTypeSpan => {
                if let Some(t) = tnodes[node].type_() {
                    self.visit_for_display_parts(tnodes, t, id_to_symbol, parts);
                }
                let literal = tnodes[node].as_template_literal_type_span().literal;
                if let Some(literal) = literal {
                    self.visit_for_display_parts(tnodes, literal, id_to_symbol, parts);
                }
            }
            Kind::TemplateMiddle | Kind::TemplateTail => {
                parts.push(label_part(&self.get_literal_text(tnodes, node)));
            }
            Kind::ThisType => {
                parts.push(label_part("this"));
            }
            Kind::ComputedPropertyName => {
                parts.push(label_part("["));
                if let Some(expression) = tnodes[node].expression() {
                    self.visit_for_display_parts(tnodes, expression, id_to_symbol, parts);
                }
                parts.push(label_part("]"));
            }
            Kind::PropertyAccessExpression => {
                if let Some(expression) = tnodes[node].expression() {
                    self.visit_for_display_parts(tnodes, expression, id_to_symbol, parts);
                }
                parts.push(label_part("."));
                if let Some(name) = tnodes[node].name() {
                    self.visit_for_display_parts(tnodes, name, id_to_symbol, parts);
                }
            }
            Kind::ElementAccessExpression => {
                if let Some(expression) = tnodes[node].expression() {
                    self.visit_for_display_parts(tnodes, expression, id_to_symbol, parts);
                }
                parts.push(label_part("["));
                let argument_expression =
                    tnodes[node].as_element_access_expression().argument_expression;
                if let Some(argument_expression) = argument_expression {
                    self.visit_for_display_parts(tnodes, argument_expression, id_to_symbol, parts);
                }
                parts.push(label_part("]"));
            }
            _ => debug::fail_bad_syntax_kind!(tnodes[node]),
        }
    }

    /// `visitDisplayPartList`.
    fn visit_display_part_list(
        &self,
        tnodes: &[Node],
        nodes_list: &[NodeId],
        separator: &str,
        id_to_symbol: &FxHashMap<NodeId, SymbolId>,
        parts: &mut Vec<lsproto::InlayHintLabelPart>,
    ) {
        for (i, &n) in nodes_list.iter().enumerate() {
            if i > 0 {
                parts.push(label_part(separator));
            }
            self.visit_for_display_parts(tnodes, n, id_to_symbol, parts);
        }
    }

    /// `visitParametersAndTypeParameters`.
    fn visit_parameters_and_type_parameters(
        &self,
        tnodes: &[Node],
        node: NodeId,
        id_to_symbol: &FxHashMap<NodeId, SymbolId>,
        parts: &mut Vec<lsproto::InlayHintLabelPart>,
    ) {
        let type_parameters: Vec<NodeId> = tnodes[node]
            .type_parameters()
            .map(|t| t.to_vec())
            .unwrap_or_default();
        if !type_parameters.is_empty() {
            parts.push(label_part("<"));
            self.visit_display_part_list(tnodes, &type_parameters, ", ", id_to_symbol, parts);
            parts.push(label_part(">"));
        }
        parts.push(label_part("("));
        let parameters: Vec<NodeId> = tnodes[node]
            .parameters()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        self.visit_display_part_list(tnodes, &parameters, ", ", id_to_symbol, parts);
        parts.push(label_part(")"));
    }

    /// `getNodeDisplayPart`.
    fn get_node_display_part(&self, text: &str, node: NodeId) -> lsproto::InlayHintLabelPart {
        let (file, pos, end) = {
            let nodes = self.program.arena_of(node);
            let file = ast::get_source_file_of_node(Some(node), &nodes).expect("source file");
            drop(nodes);
            let mut nodes_mut = self.program.nodes_mut(file.file_index());
            let pos = tsc_astnav::tokens::get_start_of_node(
                &mut nodes_mut,
                file,
                node,
                false, /*includeJSDoc*/
            );
            let end = nodes_mut[node].end();
            (file, pos, end)
        };
        let mut part = lsproto::InlayHintLabelPart {
            value: text.to_string(),
            ..Default::default()
        };
        // The location is an optional go-to target for the name. Only attach it when the name maps back to a
        // single concrete span in the original text; an approximate or synthesized mapping would point the
        // user somewhere wrong, so it is better to omit the target than to fabricate one.
        let nodes = self.program.nodes(file.file_index());
        let (lsp_range, fidelity) = self.converters.to_lsp_range_for_feature(
            &source_file_script(file, &nodes),
            TextRange::new(pos, end),
            Feature::InlayHints,
        );
        if fidelity.is_single_segment() {
            part.location = Some(lsproto::Location {
                uri: file_name_to_document_uri(
                    nodes[file].as_source_file().original_file_name(&nodes),
                ),
                range: lsp_range,
            });
        }
        part
    }

    /// `getLiteralText`.
    fn get_literal_text(&self, tnodes: &[Node], node: NodeId) -> String {
        match tnodes[node].kind {
            Kind::StringLiteral => {
                if self.quote_preference == QuotePreference::SINGLE {
                    return format!(
                        "'{}'",
                        escape_string(&tnodes[node].text(tnodes), QuoteChar::SingleQuote)
                    );
                }
                return format!(
                    "\"{}\"",
                    escape_string(&tnodes[node].text(tnodes), QuoteChar::DoubleQuote)
                );
            }
            Kind::TemplateHead | Kind::TemplateMiddle | Kind::TemplateTail => {
                let mut raw_text = tnodes[node].raw_text().to_string();
                if raw_text.is_empty() {
                    raw_text = escape_string(&tnodes[node].text(tnodes), QuoteChar::Backtick);
                }
                match tnodes[node].kind {
                    Kind::TemplateHead => return format!("`{raw_text}${{"),
                    Kind::TemplateMiddle => return format!("}}{raw_text}${{"),
                    Kind::TemplateTail => return format!("}}{raw_text}`"),
                    _ => {}
                }
            }
            _ => {}
        }
        tnodes[node].text(tnodes).into_owned()
    }

    /// `getParameterIdentifierInfoAtPosition`.
    fn get_parameter_identifier_info_at_position(
        &mut self,
        signature: tsc_checker::types::SignatureId,
        pos: usize,
    ) -> Option<ParameterInfo> {
        let (parameters, has_rest_parameter) = {
            let cb = self.checker.borrow();
            let sig = cb.signature_arena.get(signature);
            (sig.parameters.clone(), sig.has_rest_parameter())
        };
        let param_count = parameters.len() - if has_rest_parameter { 1 } else { 0 };
        if pos < param_count {
            let param = parameters[pos];
            let param_id = get_parameter_declaration_identifier(self.checker, param)?;
            let name = {
                let param_nodes = self.program.arena_of(param_id);
                param_nodes[param_id].text(&param_nodes).into_owned()
            };
            return Some(ParameterInfo {
                parameter: param_id,
                name,
                is_rest_parameter: false,
            });
        }

        let mut rest_parameter = None;
        let mut rest_id = None;
        if param_count < parameters.len() {
            rest_parameter = Some(parameters[param_count]);
            rest_id = get_parameter_declaration_identifier(self.checker, parameters[param_count]);
        }
        let rest_id = rest_id?;

        let rest_type = self
            .checker
            .borrow_mut()
            .get_type_of_symbol(rest_parameter.expect("rest parameter"));
        if tsc_checker::checker_core::is_tuple_type(&self.checker.borrow().types, rest_type) {
            let cb = self.checker.borrow();
            let target = cb.types.target_tuple_type(rest_type).expect("tuple target");
            let element_infos = cb.types.get_ref(target).as_tuple_type().element_infos.clone();
            drop(cb);
            let mut associated_names: Vec<Option<NodeId>> =
                Vec::with_capacity(element_infos.len());
            for element_info in &element_infos {
                associated_names.push(element_info.labeled_declaration());
            }
            let index = pos - param_count;
            if index < associated_names.len() {
                let associated_name = associated_names[index];
                if let Some(associated_name) = associated_name {
                    let name = {
                        let decl_nodes = self.program.arena_of(associated_name);
                        let name = decl_nodes[associated_name]
                            .name()
                            .expect("associated name");
                        debug::assert_!(
                            ast::is_identifier(&decl_nodes[name]),
                            "associatedName name should be identifier"
                        );
                        let is_rest_tuple_element = if ast::is_named_tuple_member(
                            &decl_nodes[associated_name],
                        ) {
                            decl_nodes[associated_name]
                                .as_named_tuple_member()
                                .dot_dot_dot_token
                                .is_some()
                        } else {
                            decl_nodes[associated_name]
                                .as_parameter_declaration()
                                .dot_dot_dot_token
                                .is_some()
                        };
                        (
                            name,
                            decl_nodes[name].text(&decl_nodes).into_owned(),
                            is_rest_tuple_element,
                        )
                    };
                    return Some(ParameterInfo {
                        parameter: name.0,
                        name: name.1,
                        is_rest_parameter: name.2,
                    });
                }
            }

            return None;
        }

        if pos == param_count {
            let name = self
                .checker
                .borrow()
                .symbol_arena
                .get_ref(rest_parameter.expect("rest parameter"))
                .name
                .to_string();
            return Some(ParameterInfo {
                parameter: rest_id,
                name,
                is_rest_parameter: true,
            });
        }
        None
    }

    /// `leadingCommentsContainsParameterName`.
    fn leading_comments_contains_parameter_name(&self, node: NodeId, name: &str) -> bool {
        let nodes = self.nodes();
        if !is_identifier_text(name, nodes[self.file].as_source_file().language_variant) {
            return false;
        }

        let ranges = {
            let mut nodes_mut = self.program.nodes_mut(self.file.file_index());
            get_leading_comment_ranges_of_node(&mut nodes_mut, node, self.file)
        };
        let file_text = nodes[self.file].as_source_file().text().to_string();
        for r in ranges {
            let comment_text = file_text[r.text_range.pos() as usize..r.text_range.end() as usize]
                .trim_matches(|c: char| c.is_whitespace() || c == '/' || c == '*');
            if comment_text == name {
                return true;
            }
        }

        false
    }

    /// `getTypeAnnotationPosition`.
    fn get_type_annotation_position(&self, nodes: &[Node], decl: NodeId) -> TextPos {
        let close_paren_token = {
            let mut nodes_mut = self.program.nodes_mut(self.file.file_index());
            tsc_astnav::tokens::find_child_of_kind(
                &mut nodes_mut,
                self.file,
                decl,
                Kind::CloseParenToken,
            )
        };
        if let Some(close_paren_token) = close_paren_token {
            return nodes[close_paren_token].end();
        }
        nodes[decl].parameter_list().expect("parameter list").end()
    }
}

/// `label_part` — `&lsproto.InlayHintLabelPart{Value: text}`.
fn label_part(text: &str) -> lsproto::InlayHintLabelPart {
    lsproto::InlayHintLabelPart {
        value: text.to_string(),
        ..Default::default()
    }
}

/// `shouldShowParameterNameHints`.
fn should_show_parameter_name_hints(preferences: &InlayHintsPreferences) -> bool {
    preferences.include_inlay_parameter_name_hints == IncludeInlayParameterNameHints::LITERALS
        || preferences.include_inlay_parameter_name_hints == IncludeInlayParameterNameHints::ALL
}

/// `shouldShowLiteralParameterNameHintsOnly`.
fn should_show_literal_parameter_name_hints_only(preferences: &InlayHintsPreferences) -> bool {
    preferences.include_inlay_parameter_name_hints == IncludeInlayParameterNameHints::LITERALS
}

/// `isSignatureSupportingReturnAnnotation` — node is FunctionDeclaration |
/// ArrowFunction | FunctionExpression | MethodDeclaration | GetAccessor.
fn is_signature_supporting_return_annotation(node: &Node) -> bool {
    ast::is_arrow_function(node)
        || ast::is_function_expression(node)
        || ast::is_function_declaration(node)
        || ast::is_method_declaration(node)
        || ast::is_get_accessor_declaration(node)
}

/// `isHintableDeclaration`.
fn is_hintable_declaration(nodes: &[Node], node: NodeId) -> bool {
    if (ast::is_part_of_parameter_declaration(node, nodes)
        || ast::is_variable_declaration(&nodes[node]) && ast::is_var_const(node, nodes))
        && nodes[node].initializer().is_some()
    {
        let initializer = ast::skip_parentheses(nodes[node].initializer().unwrap(), nodes);
        return !(is_hintable_literal(&nodes[initializer], nodes)
            || ast::is_new_expression(&nodes[initializer])
            || ast::is_object_literal_expression(&nodes[initializer])
            || ast::is_assertion_expression(&nodes[initializer]));
    }
    true
}

/// `isHintableLiteral`.
fn is_hintable_literal(node: &Node, nodes: &[Node]) -> bool {
    match node.kind {
        Kind::PrefixUnaryExpression => {
            let operand = node
                .as_prefix_unary_expression()
                .operand
                .expect("prefix unary operand");
            ast::is_literal_expression(&nodes[operand])
                || ast::is_identifier(&nodes[operand])
                    && ast::is_infinity_or_na_n_string(&nodes[operand].text(nodes))
        }
        Kind::TrueKeyword
        | Kind::FalseKeyword
        | Kind::NullKeyword
        | Kind::NoSubstitutionTemplateLiteral
        | Kind::TemplateExpression => true,
        Kind::Identifier => {
            let name = node.text(nodes);
            name.as_ref() == "undefined" || ast::is_infinity_or_na_n_string(&name)
        }
        _ => ast::is_literal_expression(node),
    }
}

/// `isModuleReferenceType`.
fn is_module_reference_type(c: &Checker, t: TypeId) -> bool {
    c.types
        .get_ref(t)
        .symbol()
        .is_some_and(|s| c.symbol_arena.get_ref(s).flags.intersects(SymbolFlags::MODULE))
}

/// `parameterInfo`.
struct ParameterInfo {
    /// `parameter` — `*ast.IdentifierNode`.
    parameter: NodeId,
    /// `name`.
    name: String,
    /// `isRestParameter`.
    is_rest_parameter: bool,
}

/// `getParameterDeclarationIdentifier`.
fn get_parameter_declaration_identifier(
    checker: &Rc<RefCell<Checker>>,
    symbol: SymbolId,
) -> Option<NodeId> {
    let cb = checker.borrow();
    let value_declaration = cb.symbol_arena.get_ref(symbol).value_declaration;
    let Some(value_declaration) = value_declaration else {
        return None;
    };
    let program = cb.program.clone().expect("program");
    let decl_nodes = program.nodes(value_declaration.file_index());
    if !ast::is_parameter_declaration(&decl_nodes[value_declaration]) {
        return None;
    }
    let name = decl_nodes[value_declaration].name();
    name.filter(|&n| ast::is_identifier(&decl_nodes[n]))
}

/// `identifierOrAccessExpressionPostfixMatchesParameterName`.
fn identifier_or_access_expression_postfix_matches_parameter_name(
    nodes: &[Node],
    expr: NodeId,
    parameter_name: &str,
) -> bool {
    if ast::is_identifier(&nodes[expr]) {
        return nodes[expr].text(nodes).as_ref() == parameter_name;
    }
    if ast::is_property_access_expression(&nodes[expr]) {
        return nodes[expr]
            .name()
            .is_some_and(|n| nodes[n].text(nodes).as_ref() == parameter_name);
    }
    false
}

/// `typePredicateToTypePredicateNode` variant that also returns the filled
/// `id_to_symbol` map — mirrors `printer_util.rs::type_to_type_node_with_id_map`
/// (the public checker method consumes the map).
fn type_predicate_to_type_predicate_node_with_map(
    c: &mut Checker,
    t: Option<&TypePredicate>,
    enclosing_declaration: Option<NodeId>,
    flags: nodebuilder::Flags,
) -> (Option<NodeId>, FxHashMap<NodeId, SymbolId>) {
    let mut node_builder = c.get_node_builder_ex(FxHashMap::default());
    let file_index = enclosing_declaration
        .map(|d| d.file_index())
        .unwrap_or_else(|| {
            node_builder
                .impl_
                .as_ref()
                .expect("NodeBuilder without impl")
                .f
                .file_index()
        });
    let program = c.program.clone().expect("program");
    let (file_index, arena_cell) = program.nodes_handle_or_fallback(file_index);
    node_builder
        .impl_
        .as_mut()
        .expect("NodeBuilder without impl")
        .f
        .set_file_index(file_index);
    let mut nodes = tsc_ast::ast::ArenaAccess::new(&arena_cell);
    let type_node = node_builder.type_predicate_to_type_predicate_node(
        c,
        &mut nodes,
        t,
        enclosing_declaration,
        flags,
        nodebuilder::InternalFlags::NONE,
        None,
    );
    let id_to_symbol = node_builder
        .impl_
        .as_mut()
        .map(|i| std::mem::take(&mut i.id_to_symbol))
        .unwrap_or_default();
    (type_node, id_to_symbol)
}

/// `isAnyInlayHintEnabled`.
fn is_any_inlay_hint_enabled(preferences: &InlayHintsPreferences) -> bool {
    preferences.include_inlay_parameter_name_hints != IncludeInlayParameterNameHints::NONE
        || preferences.include_inlay_function_parameter_type_hints.is_true()
        || preferences.include_inlay_variable_type_hints.is_true()
        || preferences
            .include_inlay_property_declaration_type_hints
            .is_true()
        || preferences
            .include_inlay_function_like_return_type_hints
            .is_true()
        || preferences.include_inlay_enum_member_value_hints.is_true()
}
