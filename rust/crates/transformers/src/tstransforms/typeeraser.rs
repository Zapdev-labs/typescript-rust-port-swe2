// Ported from tsc/internal/transformers/tstransforms/typeeraser.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The type eraser — strips TypeScript-only syntax (type annotations, type
// parameters, accessibility/readonly modifiers, `implements` clauses, type
// assertions, etc.) so the ES transforms see plain JavaScript.
//
// PORT: `parentNode`/`currentNode` (the manual ancestor stack maintained by
// `pushNode`/`popNode`) live in `Cell`s on the shared state. `nil` compiler
// options map to `EMPTY_COMPILER_OPTIONS` (Go would nil-pointer panic; the
// empty options carry the same field values).

use std::cell::Cell;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{self as ast, Kind, ModifierList, NodeId, SubtreeFacts};
use tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::TS_TRUE;

use super::runtimesyntax::get_innermost_module_declaration_from_dotted_module;
use crate::chain::TransformOptions;
use crate::estransforms::{Ec, make_transformer, visit_each_child};
use crate::modifier_visitor::extract_modifiers;
use crate::transformer::Transformer;

/// `type TypeEraserTransformer struct`.
pub struct TypeEraserTransformer<'a> {
    /// `compilerOptions *core.CompilerOptions`
    compiler_options: &'a CompilerOptions,
    /// `parentNode *ast.Node`
    parent_node: Cell<Option<NodeId>>,
    /// `currentNode *ast.Node`
    current_node: Cell<Option<NodeId>>,
}

impl<'a> TypeEraserTransformer<'a> {
    /// `pushNode` — pushes a new child node onto the ancestor tracking stack,
    /// returning the grandparent node to be restored later via `pop_node`.
    fn push_node(&self, node: NodeId) -> Option<NodeId> {
        let grandparent_node = self.parent_node.get();
        self.parent_node.set(self.current_node.get());
        self.current_node.set(Some(node));
        grandparent_node
    }

    /// `popNode` — pops the last child node off the ancestor tracking stack,
    /// restoring the grandparent node.
    fn pop_node(&self, grandparent_node: Option<NodeId>) {
        self.current_node.set(self.parent_node.get());
        self.parent_node.set(grandparent_node);
    }

    /// `tx.elide` — replaces a statement with a NotEmittedStatement so its
    /// comments can still be emitted.
    fn elide(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        Some(ec.borrow_mut().new_not_emitted_statement(cx.nodes, node))
    }

    /// `tx.visit`
    fn visit<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].subtree_facts(cx.nodes) & SubtreeFacts::CONTAINS_TYPE_SCRIPT
            == SubtreeFacts::NONE
        {
            return Some(node);
        }

        if ast::is_statement(&cx.nodes[node], cx.nodes)
            && ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::AMBIENT)
        {
            return self.elide(ec, cx, node);
        }

        let grandparent_node = self.push_node(node);
        let result = self.visit_inner(ec, v, cx, node);
        self.pop_node(grandparent_node);
        result
    }

    /// The `switch node.Kind` body of `tx.visit` (split out so `pop_node`
    /// always runs — Go uses `defer`).
    fn visit_inner<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            // TypeScript accessibility and readonly modifiers are elided;
            // TypeScript type nodes are elided; TypeScript index signatures
            // are elided.
            Kind::PublicKeyword
            | Kind::PrivateKeyword
            | Kind::ProtectedKeyword
            | Kind::AbstractKeyword
            | Kind::OverrideKeyword
            | Kind::ConstKeyword
            | Kind::DeclareKeyword
            | Kind::ReadonlyKeyword
            | Kind::ArrayType
            | Kind::TupleType
            | Kind::OptionalType
            | Kind::RestType
            | Kind::TypeLiteral
            | Kind::TypePredicate
            | Kind::TypeParameter
            | Kind::AnyKeyword
            | Kind::UnknownKeyword
            | Kind::BooleanKeyword
            | Kind::StringKeyword
            | Kind::NumberKeyword
            | Kind::NeverKeyword
            | Kind::VoidKeyword
            | Kind::SymbolKeyword
            | Kind::ConstructorType
            | Kind::FunctionType
            | Kind::TypeQuery
            | Kind::TypeReference
            | Kind::UnionType
            | Kind::IntersectionType
            | Kind::ConditionalType
            | Kind::ParenthesizedType
            | Kind::ThisType
            | Kind::TypeOperator
            | Kind::IndexedAccessType
            | Kind::MappedType
            | Kind::LiteralType
            | Kind::IndexSignature => None,

            Kind::InKeyword | Kind::OutKeyword => {
                // TypeScript `in`/`out` variance modifiers are elided. These
                // keywords are only meaningful as modifiers on type
                // parameters (which are themselves elided), but they may
                // appear as a grammar error on other declarations and must
                // not leak into the emitted JS. The `in` binary operator
                // shares this token kind, so only elide when used as a
                // modifier.
                if !self
                    .parent_node
                    .get()
                    .is_some_and(|p| ast::is_binary_expression(&cx.nodes[p]))
                {
                    return None;
                }
                Some(visit_each_child(v, cx, node))
            }

            // Reparsed commonjs imports are elided.
            Kind::JSImportDeclaration => None,

            // TypeScript type-only declarations are elided.
            Kind::TypeAliasDeclaration
            | Kind::JSTypeAliasDeclaration
            | Kind::InterfaceDeclaration => self.elide(ec, cx, node),

            // TypeScript namespace export declarations are elided.
            Kind::NamespaceExportDeclaration => None,

            Kind::ModuleDeclaration => {
                // TypeScript module declarations are elided if they are not
                // instantiated or have no body.
                let name = cx.nodes[node].name();
                let name_is_identifier =
                    name.is_some_and(|name| ast::is_identifier(&cx.nodes[name]));
                let body_missing =
                    get_innermost_module_declaration_from_dotted_module(node, cx.nodes)
                        .and_then(|d| cx.nodes[d].as_module_declaration().body_base.body)
                        .is_none();
                if !name_is_identifier
                    || !ast::is_instantiated_module(
                        node,
                        self.compiler_options.should_preserve_const_enums(),
                        cx.nodes,
                    )
                    || body_missing
                {
                    return self.elide(ec, cx, node);
                }
                Some(visit_each_child(v, cx, node))
            }

            Kind::ExpressionWithTypeArguments => {
                let expression_in = cx.nodes[node]
                    .as_expression_with_type_arguments()
                    .expression;
                let expression = v.visit_node(cx, expression_in);
                ec.borrow_mut()
                    .factory
                    .update_expression_with_type_arguments(cx.nodes, node, expression, None)
                    .unwrap_or(node)
                    .into()
            }

            Kind::PropertyDeclaration => {
                if self.compiler_options.experimental_decorators == TS_TRUE
                    && ast::has_syntactic_modifier(
                        &cx.nodes[node],
                        ast::ModifierFlags::AMBIENT | ast::ModifierFlags::ABSTRACT,
                    )
                    && ast::has_decorators(&cx.nodes[node])
                {
                    // declare/abstract props with decorators must be preserved
                    // until the decorator transform can process them and
                    // remove them.
                    return Some(self.visit_property_declaration(ec, v, cx, node));
                }
                if ast::has_syntactic_modifier(
                    &cx.nodes[node],
                    ast::ModifierFlags::AMBIENT | ast::ModifierFlags::ABSTRACT,
                ) {
                    // TypeScript `declare` fields are elided.
                    return None;
                }
                Some(self.visit_property_declaration(ec, v, cx, node))
            }

            Kind::Constructor => {
                let d = cx.nodes[node].as_constructor_declaration();
                let (parameters, body) = (
                    d.function_like_with_body_base
                        .function_like_base
                        .parameters
                        .clone(),
                    d.function_like_with_body_base.body_base.body,
                );
                if ast::node_is_missing(body, cx.nodes) {
                    // TypeScript overloads are elided.
                    return None;
                }
                let parameters = v.visit_nodes(cx, parameters);
                let body = v.visit_node(cx, body);
                ec.borrow_mut()
                    .factory
                    .update_constructor_declaration(
                        cx.nodes, node, None, None, parameters, None, None, body,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::MethodDeclaration => {
                let d = cx.nodes[node].as_method_declaration();
                let (modifiers, asterisk_token, name, parameters, body) = (
                    d.named_member_base.modifiers_base.modifiers.clone(),
                    d.function_like_with_body_base.body_base.asterisk_token,
                    d.named_member_base.name,
                    d.function_like_with_body_base
                        .function_like_base
                        .parameters
                        .clone(),
                    d.function_like_with_body_base.body_base.body,
                );
                if ast::node_is_missing(body, cx.nodes) {
                    // TypeScript overloads are elided.
                    return None;
                }
                let modifiers = v.visit_modifiers(cx, modifiers);
                let name = v.visit_node(cx, name);
                let parameters = v.visit_nodes(cx, parameters);
                let body = v.visit_node(cx, body);
                ec.borrow_mut()
                    .factory
                    .update_method_declaration(
                        cx.nodes,
                        node,
                        modifiers,
                        asterisk_token,
                        name,
                        None,
                        None,
                        parameters,
                        None,
                        None,
                        body,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::GetAccessor => {
                let d = cx.nodes[node].as_get_accessor_declaration();
                let (modifiers, name, parameters, body) = (
                    d.accessor_declaration_base
                        .named_member_base
                        .modifiers_base
                        .modifiers
                        .clone(),
                    d.accessor_declaration_base.named_member_base.name,
                    d.accessor_declaration_base
                        .function_like_with_body_base
                        .function_like_base
                        .parameters
                        .clone(),
                    d.accessor_declaration_base
                        .function_like_with_body_base
                        .body_base
                        .body,
                );
                if ast::node_is_missing(body, cx.nodes)
                    && ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::ABSTRACT)
                {
                    // Abstract accessors are elided.
                    return None;
                }
                let mut body = v.visit_node(cx, body);
                if body.is_none() {
                    let statements = ec.borrow_mut().factory.new_node_list([]);
                    body = Some(ec.borrow_mut().factory.new_block(
                        cx.nodes,
                        Some(statements),
                        false,
                    ));
                }
                let modifiers = v.visit_modifiers(cx, modifiers);
                let name = v.visit_node(cx, name);
                let parameters = v.visit_nodes(cx, parameters);
                ec.borrow_mut()
                    .factory
                    .update_get_accessor_declaration(
                        cx.nodes, node, modifiers, name, None, parameters, None, None, body,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::SetAccessor => {
                let d = cx.nodes[node].as_set_accessor_declaration();
                let (modifiers, name, parameters, body) = (
                    d.accessor_declaration_base
                        .named_member_base
                        .modifiers_base
                        .modifiers
                        .clone(),
                    d.accessor_declaration_base.named_member_base.name,
                    d.accessor_declaration_base
                        .function_like_with_body_base
                        .function_like_base
                        .parameters
                        .clone(),
                    d.accessor_declaration_base
                        .function_like_with_body_base
                        .body_base
                        .body,
                );
                if ast::node_is_missing(body, cx.nodes)
                    && ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::ABSTRACT)
                {
                    // Abstract accessors are elided.
                    return None;
                }
                let mut body = v.visit_node(cx, body);
                if body.is_none() {
                    let statements = ec.borrow_mut().factory.new_node_list([]);
                    body = Some(ec.borrow_mut().factory.new_block(
                        cx.nodes,
                        Some(statements),
                        false,
                    ));
                }
                let modifiers = v.visit_modifiers(cx, modifiers);
                let name = v.visit_node(cx, name);
                let parameters = v.visit_nodes(cx, parameters);
                ec.borrow_mut()
                    .factory
                    .update_set_accessor_declaration(
                        cx.nodes, node, modifiers, name, None, parameters, None, None, body,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::VariableDeclaration => {
                let d = cx.nodes[node].as_variable_declaration();
                let (name_in, type_node_in, initializer_in) = (d.name, d.type_, d.initializer);
                let name = v.visit_node(cx, name_in);
                let initializer = v.visit_node(cx, initializer_in);
                let updated = ec
                    .borrow_mut()
                    .factory
                    .update_variable_declaration(cx.nodes, node, name, None, None, initializer)
                    .unwrap_or(node);
                if let Some(type_node) = type_node_in {
                    if let Some(updated_name) = cx.nodes[updated].as_variable_declaration().name {
                        ec.borrow().set_type_node(updated_name, type_node);
                    }
                }
                Some(updated)
            }

            Kind::HeritageClause => {
                let d = cx.nodes[node].as_heritage_clause();
                let (token, types) = (d.token, d.types.clone());
                if token == Kind::ImplementsKeyword {
                    // TypeScript `implements` clauses are elided.
                    return None;
                }
                let types = v.visit_nodes(cx, types);
                ec.borrow_mut()
                    .factory
                    .update_heritage_clause(cx.nodes, node, token, types)
                    .unwrap_or(node)
                    .into()
            }

            Kind::ClassDeclaration => {
                let d = cx.nodes[node].as_class_declaration();
                let (modifiers, name, heritage_clauses, members) = (
                    d.class_like_base.modifiers_base.modifiers.clone(),
                    d.class_like_base.name,
                    d.class_like_base.heritage_clauses.clone(),
                    d.class_like_base.members.clone(),
                );
                let modifiers = v.visit_modifiers(cx, modifiers);
                let name = v.visit_node(cx, name);
                let heritage_clauses = v.visit_nodes(cx, heritage_clauses);
                let members = v.visit_nodes(cx, members);
                ec.borrow_mut()
                    .factory
                    .update_class_declaration(
                        cx.nodes,
                        node,
                        modifiers,
                        name,
                        None,
                        heritage_clauses,
                        members,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::ClassExpression => {
                let d = cx.nodes[node].as_class_expression();
                let (modifiers, name, heritage_clauses, members) = (
                    d.class_like_base.modifiers_base.modifiers.clone(),
                    d.class_like_base.name,
                    d.class_like_base.heritage_clauses.clone(),
                    d.class_like_base.members.clone(),
                );
                let modifiers = v.visit_modifiers(cx, modifiers);
                let name = v.visit_node(cx, name);
                let heritage_clauses = v.visit_nodes(cx, heritage_clauses);
                let members = v.visit_nodes(cx, members);
                ec.borrow_mut()
                    .factory
                    .update_class_expression(
                        cx.nodes,
                        node,
                        modifiers,
                        name,
                        None,
                        heritage_clauses,
                        members,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::FunctionDeclaration => {
                let d = cx.nodes[node].as_function_declaration();
                let (modifiers, asterisk_token, name, parameters, body) = (
                    d.modifiers_base.modifiers.clone(),
                    d.function_like_with_body_base.body_base.asterisk_token,
                    d.name,
                    d.function_like_with_body_base
                        .function_like_base
                        .parameters
                        .clone(),
                    d.function_like_with_body_base.body_base.body,
                );
                if ast::node_is_missing(body, cx.nodes) {
                    // TypeScript overloads are elided.
                    return self.elide(ec, cx, node);
                }
                let modifiers = v.visit_modifiers(cx, modifiers);
                let name = v.visit_node(cx, name);
                let parameters = v.visit_nodes(cx, parameters);
                let body = v.visit_node(cx, body);
                ec.borrow_mut()
                    .factory
                    .update_function_declaration(
                        cx.nodes,
                        node,
                        modifiers,
                        asterisk_token,
                        name,
                        None,
                        parameters,
                        None,
                        None,
                        body,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::FunctionExpression => {
                let d = cx.nodes[node].as_function_expression();
                let (modifiers, asterisk_token, name, parameters, body) = (
                    d.modifiers_base.modifiers.clone(),
                    d.function_like_with_body_base.body_base.asterisk_token,
                    d.name,
                    d.function_like_with_body_base
                        .function_like_base
                        .parameters
                        .clone(),
                    d.function_like_with_body_base.body_base.body,
                );
                let modifiers = v.visit_modifiers(cx, modifiers);
                let name = v.visit_node(cx, name);
                let parameters = v.visit_nodes(cx, parameters);
                let body = v.visit_node(cx, body);
                ec.borrow_mut()
                    .factory
                    .update_function_expression(
                        cx.nodes,
                        node,
                        modifiers,
                        asterisk_token,
                        name,
                        None,
                        parameters,
                        None,
                        None,
                        body,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::ArrowFunction => {
                let d = cx.nodes[node].as_arrow_function();
                let (modifiers, parameters, equals_greater_than_token, body) = (
                    d.modifiers_base.modifiers.clone(),
                    d.function_like_with_body_base
                        .function_like_base
                        .parameters
                        .clone(),
                    d.equals_greater_than_token,
                    d.function_like_with_body_base.body_base.body,
                );
                let modifiers = v.visit_modifiers(cx, modifiers);
                let parameters = v.visit_nodes(cx, parameters);
                let body = v.visit_node(cx, body);
                ec.borrow_mut()
                    .factory
                    .update_arrow_function(
                        cx.nodes,
                        node,
                        modifiers,
                        None,
                        parameters,
                        None,
                        None,
                        equals_greater_than_token,
                        body,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::Parameter => {
                if ast::is_this_parameter(&cx.nodes[node], cx.nodes) {
                    // TypeScript `this` parameters are elided.
                    return None;
                }
                let d = cx.nodes[node].as_parameter_declaration();
                let (modifiers_in, dot_dot_dot_token, name, initializer) = (
                    d.modifiers_base.modifiers.clone(),
                    d.dot_dot_dot_token,
                    d.name,
                    d.initializer,
                );
                // preserve parameter property modifiers to be handled by the
                // runtime transformer.
                let mut modifiers: Option<ModifierList> = None;
                if self.parent_node.get().is_some_and(|p| {
                    ast::is_parameter_property_declaration(&cx.nodes[node], &cx.nodes[p])
                }) {
                    modifiers = extract_modifiers(
                        Some(ec),
                        cx.nodes,
                        modifiers_in,
                        ast::ModifierFlags::PARAMETER_PROPERTY_MODIFIER,
                    );
                }
                // preserve decorators for the decorator transforms.
                if ast::has_decorators(&cx.nodes[node]) {
                    let decorator_ids: Vec<NodeId> = cx.nodes[node]
                        .decorators(cx.nodes)
                        .iter()
                        .map(|d| d.id)
                        .collect();
                    // Go's `VisitSlice` returns the input slice unchanged when
                    // no element changed; ours returns `None` in that case.
                    let visited = v
                        .visit_slice(cx, &decorator_ids)
                        .unwrap_or(decorator_ids);
                    modifiers = Some(match modifiers {
                        None => ec.borrow_mut().factory.new_modifier_list(cx.nodes, visited),
                        Some(m) => {
                            let mut all = m.nodes.to_vec();
                            all.extend_from_slice(&visited);
                            ec.borrow_mut().factory.new_modifier_list(cx.nodes, all)
                        }
                    });
                }
                let name = v.visit_node(cx, name);
                let initializer = v.visit_node(cx, initializer);
                ec.borrow_mut()
                    .factory
                    .update_parameter_declaration(
                        cx.nodes,
                        node,
                        modifiers,
                        dot_dot_dot_token,
                        name,
                        None,
                        None,
                        initializer,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::CallExpression => {
                let d = cx.nodes[node].as_call_expression();
                let (expression, question_dot_token, arguments) =
                    (d.expression, d.question_dot_token, d.arguments.clone());
                let flags = cx.nodes[node].flags;
                let expression = v.visit_node(cx, expression);
                let arguments = v.visit_nodes(cx, arguments);
                ec.borrow_mut()
                    .factory
                    .update_call_expression(
                        cx.nodes,
                        node,
                        expression,
                        question_dot_token,
                        None,
                        arguments,
                        flags,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::NewExpression => {
                let d = cx.nodes[node].as_new_expression();
                let (expression, arguments) = (d.expression, d.arguments.clone());
                let expression = v.visit_node(cx, expression);
                let arguments = v.visit_nodes(cx, arguments);
                ec.borrow_mut()
                    .factory
                    .update_new_expression(cx.nodes, node, expression, None, arguments)
                    .unwrap_or(node)
                    .into()
            }

            Kind::TaggedTemplateExpression => {
                let d = cx.nodes[node].as_tagged_template_expression();
                let (tag, question_dot_token, template) = (d.tag, d.question_dot_token, d.template);
                let flags = cx.nodes[node].flags;
                let tag = v.visit_node(cx, tag);
                let template = v.visit_node(cx, template);
                ec.borrow_mut()
                    .factory
                    .update_tagged_template_expression(
                        cx.nodes,
                        node,
                        tag,
                        question_dot_token,
                        None,
                        template,
                        flags,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::NonNullExpression
            | Kind::TypeAssertionExpression
            | Kind::AsExpression
            | Kind::SatisfiesExpression => {
                let expression_in = cx.nodes[node].expression();
                let expression = v.visit_node(cx, expression_in);
                let partial = ec
                    .borrow_mut()
                    .factory
                    .new_partially_emitted_expression(cx.nodes, expression);
                ec.borrow().set_original(partial, node);
                cx.nodes[partial].loc = cx.nodes[node].loc;
                Some(partial)
            }

            Kind::ParenthesizedExpression => {
                if !ast::is_js_doc_type_assertion(Some(node), cx.nodes) {
                    let expression_in = cx.nodes[node].as_parenthesized_expression().expression;
                    if let Some(expression_in) = expression_in {
                        // Go's
                        // `OEKAllExceptAssertionsOrExpressionsWithTypeArguments`
                        // = `OEKAll &^ OEKAssertions &^
                        // OEKExpressionsWithTypeArguments`
                        // = `OEKParentheses | OEKPartiallyEmittedExpressions`.
                        let expression = ast::skip_outer_expressions(
                            expression_in,
                            ast::outer_expression_kinds::PARENTHESES
                                | ast::outer_expression_kinds::PARTIALLY_EMITTED_EXPRESSIONS,
                            cx.nodes,
                        );
                        if ast::is_assertion_expression(&cx.nodes[expression])
                            || ast::is_satisfies_expression(&cx.nodes[expression])
                        {
                            let visited = v.visit_node(cx, Some(expression_in));
                            let partial = ec
                                .borrow_mut()
                                .factory
                                .new_partially_emitted_expression(cx.nodes, visited);
                            ec.borrow().set_original(partial, node);
                            cx.nodes[partial].loc = cx.nodes[node].loc;
                            return Some(partial);
                        }
                    }
                }
                Some(visit_each_child(v, cx, node))
            }

            Kind::JsxSelfClosingElement => {
                let d = cx.nodes[node].as_jsx_self_closing_element();
                let (tag_name, attributes) = (d.tag_name, d.attributes);
                let tag_name = v.visit_node(cx, tag_name);
                let attributes = v.visit_node(cx, attributes);
                ec.borrow_mut()
                    .factory
                    .update_jsx_self_closing_element(cx.nodes, node, tag_name, None, attributes)
                    .unwrap_or(node)
                    .into()
            }

            Kind::JsxOpeningElement => {
                let d = cx.nodes[node].as_jsx_opening_element();
                let (tag_name, attributes) = (d.tag_name, d.attributes);
                let tag_name = v.visit_node(cx, tag_name);
                let attributes = v.visit_node(cx, attributes);
                ec.borrow_mut()
                    .factory
                    .update_jsx_opening_element(cx.nodes, node, tag_name, None, attributes)
                    .unwrap_or(node)
                    .into()
            }

            Kind::ImportEqualsDeclaration => {
                if cx.nodes[node].as_import_equals_declaration().is_type_only {
                    // elide type-only imports
                    return None;
                }
                Some(visit_each_child(v, cx, node))
            }

            Kind::ImportDeclaration => {
                let d = cx.nodes[node].as_import_declaration();
                let (modifiers, import_clause, module_specifier, attributes) = (
                    d.modifiers_base.modifiers.clone(),
                    d.import_clause,
                    d.module_specifier,
                    d.attributes,
                );
                if import_clause.is_none() {
                    // Do not elide a side-effect only import declaration.
                    //  import "foo";
                    return Some(node);
                }
                let import_clause = v.visit_node(cx, import_clause);
                if import_clause.is_none() {
                    return None;
                }
                ec.borrow_mut()
                    .factory
                    .update_import_declaration(
                        cx.nodes,
                        node,
                        modifiers,
                        import_clause,
                        module_specifier,
                        attributes,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::ImportClause => {
                let d = cx.nodes[node].as_import_clause();
                let (phase_modifier, name, named_bindings_in) =
                    (d.phase_modifier, d.name, d.named_bindings);
                if cx.nodes[node].is_type_only() {
                    // Always elide type-only imports.
                    return None;
                }
                let mut named_bindings = v.visit_node(cx, named_bindings_in);
                // Empty {} due to type-only import erasure can be skipped if
                // there is also a default import.
                if name.is_some()
                    && named_bindings.is_some_and(|nb| {
                        ast::is_named_imports(&cx.nodes[nb])
                            && cx.nodes[nb]
                                .as_named_imports()
                                .elements
                                .as_ref()
                                .is_some_and(|e| e.nodes.is_empty())
                    })
                    && named_bindings_in.is_some_and(|nb| {
                        cx.nodes[nb]
                            .as_named_imports()
                            .elements
                            .as_ref()
                            .is_some_and(|e| !e.nodes.is_empty())
                    })
                {
                    // the default binding keeps the import; a source-written {}
                    // is left as is.
                    named_bindings = None;
                }
                if name.is_none() && named_bindings.is_none() {
                    // all import bindings were elided
                    return None;
                }
                ec.borrow_mut()
                    .factory
                    .update_import_clause(cx.nodes, node, phase_modifier, name, named_bindings)
                    .unwrap_or(node)
                    .into()
            }

            Kind::NamedImports => {
                let elements_in = cx.nodes[node].as_named_imports().elements.clone();
                if elements_in.as_ref().is_none_or(|e| e.nodes.is_empty()) {
                    // Do not elide a side-effect only import declaration.
                    return Some(node);
                }
                let elements = v.visit_nodes(cx, elements_in);
                if self.compiler_options.verbatim_module_syntax != TS_TRUE
                    && elements.as_ref().is_none_or(|e| e.nodes.is_empty())
                {
                    // all import specifiers were elided
                    return None;
                }
                ec.borrow_mut()
                    .factory
                    .update_named_imports(cx.nodes, node, elements)
                    .unwrap_or(node)
                    .into()
            }

            Kind::ImportSpecifier => {
                if cx.nodes[node].as_import_specifier().is_type_only {
                    // elide type-only or unused imports
                    return None;
                }
                Some(node)
            }

            Kind::ExportDeclaration => {
                let d = cx.nodes[node].as_export_declaration();
                let (is_type_only, export_clause_in, module_specifier_in, attributes_in) = (
                    d.is_type_only,
                    d.export_clause,
                    d.module_specifier,
                    d.attributes,
                );
                if is_type_only {
                    // elide type-only exports
                    return None;
                }
                let mut export_clause = None;
                if export_clause_in.is_some() {
                    export_clause = v.visit_node(cx, export_clause_in);
                    if export_clause.is_none() {
                        // all export bindings were elided
                        return None;
                    }
                }
                let module_specifier = v.visit_node(cx, module_specifier_in);
                let attributes = v.visit_node(cx, attributes_in);
                ec.borrow_mut()
                    .factory
                    .update_export_declaration(
                        cx.nodes,
                        node,
                        None,
                        false,
                        export_clause,
                        module_specifier,
                        attributes,
                    )
                    .unwrap_or(node)
                    .into()
            }

            Kind::NamedExports => {
                let elements_in = cx.nodes[node].as_named_exports().elements.clone();
                if elements_in.as_ref().is_none_or(|e| e.nodes.is_empty()) {
                    // Do not elide an empty export declaration.
                    return Some(node);
                }
                let elements = v.visit_nodes(cx, elements_in);
                if self.compiler_options.verbatim_module_syntax != TS_TRUE
                    && elements.as_ref().is_none_or(|e| e.nodes.is_empty())
                {
                    // all export specifiers were elided
                    return None;
                }
                ec.borrow_mut()
                    .factory
                    .update_named_exports(cx.nodes, node, elements)
                    .unwrap_or(node)
                    .into()
            }

            Kind::ExportSpecifier => {
                if cx.nodes[node].as_export_specifier().is_type_only {
                    // elide unused export
                    return None;
                }
                Some(node)
            }

            Kind::EnumDeclaration => {
                if ast::is_enum_const(node, cx.nodes) {
                    return Some(node);
                }
                Some(visit_each_child(v, cx, node))
            }

            _ => Some(visit_each_child(v, cx, node)),
        }
    }

    /// The shared `case ast.KindPropertyDeclaration` tail of `tx.visit` —
    /// both branches rebuild the declaration identically.
    fn visit_property_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let d = cx.nodes[node].as_property_declaration();
        let (modifiers, name, initializer) = (
            d.named_member_base.modifiers_base.modifiers.clone(),
            d.named_member_base.name,
            d.initializer,
        );
        let modifiers = v.visit_modifiers(cx, modifiers);
        let name = v.visit_node(cx, name);
        let initializer = v.visit_node(cx, initializer);
        ec.borrow_mut()
            .factory
            .update_property_declaration(cx.nodes, node, modifiers, name, None, None, initializer)
            .unwrap_or(node)
    }
}

/// `NewTypeEraserTransformer`.
pub fn new_type_eraser_transformer<'a>(opts: &TransformOptions<'a>) -> Option<Transformer<'a>> {
    make_transformer(opts, |ec| {
        let state = Rc::new(TypeEraserTransformer {
            compiler_options: opts.compiler_options.unwrap_or(&EMPTY_COMPILER_OPTIONS),
            parent_node: Cell::new(None),
            current_node: Cell::new(None),
        });
        let visit: Box<VisitFn<'a>> = Box::new(
            move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, v, cx, node)
            },
        );
        visit
    })
}
