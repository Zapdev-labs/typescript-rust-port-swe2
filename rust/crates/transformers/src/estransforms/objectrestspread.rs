// Ported from tsc/internal/transformers/estransforms/objectrestspread.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Downlevels object rest properties in binding/assignment patterns
// (`var { a, ...rest } = o`) and spread elements in object literals
// (`{ a, ...o }` → `__assign(__assign({a}, o))`).

use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId, NodeList, SubtreeFacts};
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::TextRange;
use tsc_printer::EmitFlags;

use super::{Ec, make_transformer, subtree_facts, tx_adapter, visit_each_child, visit_node};
use crate::chain::TransformOptions;
use crate::destructuring::{
    FlattenLevel, flatten_destructuring_assignment, flatten_destructuring_binding,
};
use crate::transformer::Transformer;

/// `type objectRestSpreadTransformer struct`.
struct ObjectRestSpreadTransformer<'a> {
    compiler_options: Option<&'a CompilerOptions>,

    in_exported_variable_statement: Cell<bool>,
    expression_result_is_unused: Cell<bool>,

    parameters_with_preceding_object_rest_or_spread: RefCell<Option<HashSet<NodeId>>>,
}

/// `newObjectRestSpreadTransformer`.
pub(crate) fn new_object_rest_spread_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    let compiler_options = opts.compiler_options;
    make_transformer(opts, |ec| {
        let tx = Rc::new(ObjectRestSpreadTransformer {
            compiler_options,
            in_exported_variable_statement: Cell::new(false),
            expression_result_is_unused: Cell::new(false),
            parameters_with_preceding_object_rest_or_spread: RefCell::new(None),
        });
        Box::new(move |v, cx, node| tx.visit(&ec, v, cx, node))
    })
}

impl<'a> ObjectRestSpreadTransformer<'a> {
    /// `(ch *objectRestSpreadTransformer) visit`.
    fn visit(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if subtree_facts(cx, node) & SubtreeFacts::CONTAINS_ES_OBJECT_REST_OR_SPREAD
            == SubtreeFacts::NONE
            && self
                .parameters_with_preceding_object_rest_or_spread
                .borrow()
                .is_none()
        {
            return Some(node);
        }
        // Save the expressionResultIsUnused flag set by the parent for this
        // node, then reset to false for children (the default). Specific
        // cases below override as needed.
        let expression_result_is_unused = self.expression_result_is_unused.replace(false);
        let result = self.visit_inner(ec, v, cx, node, expression_result_is_unused);
        // `defer func() { ch.expressionResultIsUnused = expressionResultIsUnused }()`
        self.expression_result_is_unused
            .set(expression_result_is_unused);
        result
    }

    /// The `switch node.Kind` dispatch of `(ch *objectRestSpreadTransformer)
    /// visit` — split out so the `defer`-equivalent restore runs over every
    /// return path.
    fn visit_inner(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        expression_result_is_unused: bool,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::SourceFile => Some(self.visit_source_file(ec, v, cx, node)),
            Kind::ObjectLiteralExpression => {
                Some(self.visit_object_literal_expression(ec, v, cx, node))
            }
            Kind::BinaryExpression => {
                self.visit_binary_expression(ec, v, cx, node, expression_result_is_unused)
            }
            Kind::ExpressionStatement => {
                self.expression_result_is_unused.set(true);
                Some(visit_each_child(v, cx, node))
            }
            Kind::ParenthesizedExpression => {
                self.expression_result_is_unused
                    .set(expression_result_is_unused);
                Some(visit_each_child(v, cx, node))
            }
            Kind::ForOfStatement => Some(self.visit_for_of_statement(ec, v, cx, node)),
            Kind::VariableStatement => Some(self.visit_variable_statement(ec, v, cx, node)),
            Kind::VariableDeclaration => self.visit_variable_declaration(ec, v, cx, node),
            Kind::CatchClause => Some(self.visit_catch_clause(ec, v, cx, node)),
            Kind::Parameter => Some(self.visit_parameter(ec, v, cx, node)),
            Kind::Constructor => Some(self.visit_constructor_declaration(ec, v, cx, node)),
            Kind::GetAccessor => Some(self.visit_get_accessor_declaration(ec, v, cx, node)),
            Kind::SetAccessor => Some(self.visit_set_accessor_declaration(ec, v, cx, node)),
            Kind::MethodDeclaration => Some(self.visit_method_declaration(ec, v, cx, node)),
            Kind::FunctionDeclaration => Some(self.visit_function_declaration(ec, v, cx, node)),
            Kind::ArrowFunction => Some(self.visit_arrow_function(ec, v, cx, node)),
            Kind::FunctionExpression => Some(self.visit_function_expression(ec, v, cx, node)),
            _ => Some(visit_each_child(v, cx, node)),
        }
    }

    /// `(ch *objectRestSpreadTransformer) visitSourceFile` — `node` must be a
    /// `SourceFile`.
    fn visit_source_file(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let visited = visit_each_child(v, cx, node);
        let helpers = ec.borrow_mut().read_emit_helpers();
        ec.borrow().add_emit_helper(visited, &helpers);
        visited
    }

    /// `(ch *objectRestSpreadTransformer) visitParameter` — `node` must be a
    /// `ParameterDeclaration`.
    fn visit_parameter(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if let Some(set) = self
            .parameters_with_preceding_object_rest_or_spread
            .borrow()
            .as_ref()
            .map(|s| s.contains(&node))
        {
            if set {
                let mut name = cx.nodes[node].name();
                if name.is_some_and(|n| ast::is_binding_pattern(&cx.nodes[n])) {
                    name = Some(
                        ec.borrow_mut()
                            .factory
                            .new_generated_name_for_node(cx.nodes, node),
                    );
                }
                let dot_dot_dot_token = cx.nodes[node].as_parameter_declaration().dot_dot_dot_token;
                return ec
                    .borrow_mut()
                    .factory
                    .update_parameter_declaration(
                        cx.nodes,
                        node,
                        None,
                        dot_dot_dot_token,
                        name,
                        None,
                        None,
                        None,
                    )
                    .unwrap_or(node);
            }
        }
        if subtree_facts(cx, node) & SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
            != SubtreeFacts::NONE
        {
            // Binding patterns are converted into a generated name and are
            // evaluated inside the function body.
            let dot_dot_dot_token = cx.nodes[node].as_parameter_declaration().dot_dot_dot_token;
            let name = ec
                .borrow_mut()
                .factory
                .new_generated_name_for_node(cx.nodes, node);
            let initializer = cx.nodes[node].initializer();
            let visited = v.visit_node(cx, initializer);
            return ec
                .borrow_mut()
                .factory
                .update_parameter_declaration(
                    cx.nodes,
                    node,
                    None,
                    dot_dot_dot_token,
                    Some(name),
                    None,
                    None,
                    visited,
                )
                .unwrap_or(node);
        }
        visit_each_child(v, cx, node)
    }

    /// `(ch *objectRestSpreadTransformer)
    /// collectParametersWithPrecedingObjectRestOrSpread` — `node` is a
    /// function-like node.
    fn collect_parameters_with_preceding_object_rest_or_spread(
        &self,
        cx: &VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<HashSet<NodeId>> {
        let mut result: Option<HashSet<NodeId>> = None;
        let parameters: &[NodeId] = cx.nodes[node].parameters().unwrap_or(&[]);
        for &parameter in parameters {
            if let Some(set) = result.as_mut() {
                set.insert(parameter);
            } else if subtree_facts(cx, parameter) & SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
                != SubtreeFacts::NONE
            {
                result = Some(HashSet::new());
            }
        }
        result
    }

    /// `(ch *objectRestSpreadTransformer) enterParameterListContext` —
    /// returns the previous scope (`oldParamScope`).
    fn enter_parameter_list_context(
        &self,
        cx: &VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<HashSet<NodeId>> {
        let old = self
            .parameters_with_preceding_object_rest_or_spread
            .replace(self.collect_parameters_with_preceding_object_rest_or_spread(cx, node));
        old
    }

    /// `(ch *objectRestSpreadTransformer) exitParameterListContext`.
    fn exit_parameter_list_context(&self, scope: Option<HashSet<NodeId>>) {
        *self
            .parameters_with_preceding_object_rest_or_spread
            .borrow_mut() = scope;
    }

    /// `(ch *objectRestSpreadTransformer) visitContructorDeclaration` —
    /// `node` must be a `ConstructorDeclaration`.
    fn visit_constructor_declaration(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let old = self.enter_parameter_list_context(cx, node);
        let result = self.visit_constructor_declaration_inner(ec, v, cx, node);
        self.exit_parameter_list_context(old);
        result
    }

    fn visit_constructor_declaration_inner(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = cx.nodes[node].modifiers().cloned();
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_params = v.visit_nodes(cx, parameters);
        let body = self.transform_function_body(ec, v, cx, node);
        ec.borrow_mut()
            .factory
            .update_constructor_declaration(
                cx.nodes,
                node,
                modifiers,
                None,
                visited_params,
                None,
                None,
                body,
            )
            .unwrap_or(node)
    }

    /// `(ch *objectRestSpreadTransformer) visitGetAccessorDeclaration` —
    /// `node` must be a `GetAccessorDeclaration`.
    fn visit_get_accessor_declaration(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let old = self.enter_parameter_list_context(cx, node);
        let result = self.visit_get_accessor_declaration_inner(ec, v, cx, node);
        self.exit_parameter_list_context(old);
        result
    }

    fn visit_get_accessor_declaration_inner(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = cx.nodes[node].modifiers().cloned();
        let name = cx.nodes[node].name();
        let visited_name = v.visit_node(cx, name);
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_params = v.visit_nodes(cx, parameters);
        let body = self.transform_function_body(ec, v, cx, node);
        ec.borrow_mut()
            .factory
            .update_get_accessor_declaration(
                cx.nodes,
                node,
                modifiers,
                visited_name,
                None,
                visited_params,
                None,
                None,
                body,
            )
            .unwrap_or(node)
    }

    /// `(ch *objectRestSpreadTransformer) visitSetAccessorDeclaration` —
    /// `node` must be a `SetAccessorDeclaration`.
    fn visit_set_accessor_declaration(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let old = self.enter_parameter_list_context(cx, node);
        let result = self.visit_set_accessor_declaration_inner(ec, v, cx, node);
        self.exit_parameter_list_context(old);
        result
    }

    fn visit_set_accessor_declaration_inner(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = cx.nodes[node].modifiers().cloned();
        let name = cx.nodes[node].name();
        let visited_name = v.visit_node(cx, name);
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_params = v.visit_nodes(cx, parameters);
        let body = self.transform_function_body(ec, v, cx, node);
        ec.borrow_mut()
            .factory
            .update_set_accessor_declaration(
                cx.nodes,
                node,
                modifiers,
                visited_name,
                None,
                visited_params,
                None,
                None,
                body,
            )
            .unwrap_or(node)
    }

    /// `(ch *objectRestSpreadTransformer) visitMethodDeclaration` — `node`
    /// must be a `MethodDeclaration`.
    fn visit_method_declaration(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let old = self.enter_parameter_list_context(cx, node);
        let result = self.visit_method_declaration_inner(ec, v, cx, node);
        self.exit_parameter_list_context(old);
        result
    }

    fn visit_method_declaration_inner(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let d = cx.nodes[node].as_method_declaration();
        let modifiers = d.named_member_base.modifiers_base.modifiers.clone();
        let asterisk_token = d.function_like_with_body_base.body_base.asterisk_token;
        let name = d.named_member_base.name;
        let postfix_token = d.named_member_base.postfix_token;
        let parameters = d
            .function_like_with_body_base
            .function_like_base
            .parameters
            .clone();
        let visited_name = v.visit_node(cx, name);
        let visited_params = v.visit_nodes(cx, parameters);
        let body = self.transform_function_body(ec, v, cx, node);
        ec.borrow_mut()
            .factory
            .update_method_declaration(
                cx.nodes,
                node,
                modifiers,
                asterisk_token,
                visited_name,
                postfix_token,
                None,
                visited_params,
                None,
                None,
                body,
            )
            .unwrap_or(node)
    }

    /// `(ch *objectRestSpreadTransformer) visitFunctionDeclaration` — `node`
    /// must be a `FunctionDeclaration`.
    fn visit_function_declaration(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let old = self.enter_parameter_list_context(cx, node);
        let result = self.visit_function_declaration_inner(ec, v, cx, node);
        self.exit_parameter_list_context(old);
        result
    }

    fn visit_function_declaration_inner(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = cx.nodes[node].modifiers().cloned();
        let asterisk_token = cx.nodes[node]
            .as_function_declaration()
            .function_like_with_body_base
            .body_base
            .asterisk_token;
        let name = cx.nodes[node].name();
        let visited_name = v.visit_node(cx, name);
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_params = v.visit_nodes(cx, parameters);
        let body = self.transform_function_body(ec, v, cx, node);
        ec.borrow_mut()
            .factory
            .update_function_declaration(
                cx.nodes,
                node,
                modifiers,
                asterisk_token,
                visited_name,
                None,
                visited_params,
                None,
                None,
                body,
            )
            .unwrap_or(node)
    }

    /// `(ch *objectRestSpreadTransformer) visitArrowFunction` — `node` must
    /// be an `ArrowFunction`.
    fn visit_arrow_function(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let old = self.enter_parameter_list_context(cx, node);
        let result = self.visit_arrow_function_inner(ec, v, cx, node);
        self.exit_parameter_list_context(old);
        result
    }

    fn visit_arrow_function_inner(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = cx.nodes[node].modifiers().cloned();
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_params = v.visit_nodes(cx, parameters);
        let equals_greater_than_token =
            cx.nodes[node].as_arrow_function().equals_greater_than_token;
        let body = self.transform_function_body(ec, v, cx, node);
        ec.borrow_mut()
            .factory
            .update_arrow_function(
                cx.nodes,
                node,
                modifiers,
                None,
                visited_params,
                None,
                None,
                equals_greater_than_token,
                body,
            )
            .unwrap_or(node)
    }

    /// `(ch *objectRestSpreadTransformer) visitFunctionExpression` — `node`
    /// must be a `FunctionExpression`.
    fn visit_function_expression(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let old = self.enter_parameter_list_context(cx, node);
        let result = self.visit_function_expression_inner(ec, v, cx, node);
        self.exit_parameter_list_context(old);
        result
    }

    fn visit_function_expression_inner(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = cx.nodes[node].modifiers().cloned();
        let asterisk_token = cx.nodes[node]
            .as_function_expression()
            .function_like_with_body_base
            .body_base
            .asterisk_token;
        let name = cx.nodes[node].name();
        let visited_name = v.visit_node(cx, name);
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_params = v.visit_nodes(cx, parameters);
        let body = self.transform_function_body(ec, v, cx, node);
        ec.borrow_mut()
            .factory
            .update_function_expression(
                cx.nodes,
                node,
                modifiers,
                asterisk_token,
                visited_name,
                None,
                visited_params,
                None,
                None,
                body,
            )
            .unwrap_or(node)
    }

    /// `(ch *objectRestSpreadTransformer) transformFunctionBody` — `node` is
    /// a function-like node.
    fn transform_function_body(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // EmitContext().VisitFunctionBody is not used here because this
        // transformer needs to inject object rest assignments between
        // visiting the body and merging the variable environment.
        ec.borrow_mut().start_variable_environment();
        let body = v.visit_node(cx, cx.nodes[node].body());
        let mut extras = ec.borrow_mut().end_variable_environment(cx.nodes);
        ec.borrow_mut().start_variable_environment();
        let new_statements = self.collect_object_rest_assignments(ec, v, cx, node);
        extras = ec
            .borrow_mut()
            .end_and_merge_variable_environment(cx.nodes, &extras);
        if new_statements.is_empty() && extras.is_empty() {
            return body;
        }

        let mut body = match body {
            Some(b) => b,
            None => {
                let empty = ec.borrow_mut().factory.new_node_list(vec![]);
                ec.borrow_mut()
                    .factory
                    .new_block(cx.nodes, Some(empty), true)
            }
        };
        let mut prefix: Vec<NodeId> = Vec::new();
        let mut suffix: Vec<NodeId> = Vec::new();
        if ast::is_block(&cx.nodes[body]) {
            let mut custom = false;
            let body_statements: Vec<NodeId> = cx.nodes[body]
                .statements()
                .map(<[_]>::to_vec)
                .unwrap_or_default();
            for (i, &statement) in body_statements.iter().enumerate() {
                if !custom && ast::is_prologue_directive(&cx.nodes[statement], cx.nodes) {
                    prefix.push(statement);
                } else if ec.borrow().emit_flags(statement) & EmitFlags::CUSTOM_PROLOGUE
                    != EmitFlags::NONE
                {
                    custom = true;
                    prefix.push(statement);
                } else {
                    suffix = body_statements[i..].to_vec();
                    break;
                }
            }
        } else {
            let ret = ec
                .borrow_mut()
                .factory
                .new_return_statement(cx.nodes, Some(body));
            cx.nodes[ret].loc = cx.nodes[body].loc;
            let mut list = ec.borrow_mut().factory.new_node_list(vec![]);
            list.loc = cx.nodes[body].loc;
            body = ec
                .borrow_mut()
                .factory
                .new_block(cx.nodes, Some(list), true);
            suffix.push(ret);
        }

        let mut all_statements = prefix;
        all_statements.extend(extras);
        all_statements.extend(new_statements);
        all_statements.extend(suffix);
        let mut new_statement_list = ec.borrow_mut().factory.new_node_list(all_statements);
        new_statement_list.loc = cx.nodes[body]
            .statement_list()
            .map(|l| l.loc)
            .unwrap_or_else(TextRange::default);
        let multi_line = cx.nodes[body].as_block().multi_line;
        Some(
            ec.borrow_mut()
                .factory
                .update_block(cx.nodes, body, Some(new_statement_list), multi_line)
                .unwrap_or(body),
        )
    }

    /// `(ch *objectRestSpreadTransformer) collectObjectRestAssignments` —
    /// `node` is a function-like node.
    fn collect_object_rest_assignments(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Vec<NodeId> {
        let mut contains_preceding_object_rest_or_spread = false;
        let mut results: Vec<NodeId> = Vec::new();
        let parameters: Vec<NodeId> = cx.nodes[node]
            .parameters()
            .map(<[_]>::to_vec)
            .unwrap_or_default();
        for parameter in parameters {
            if contains_preceding_object_rest_or_spread {
                let parameter_name = cx.nodes[parameter].name();
                if parameter_name.is_some_and(|n| ast::is_binding_pattern(&cx.nodes[n])) {
                    // In cases where a binding pattern is simply '[]' or '{}',
                    // we usually don't want to emit a var declaration;
                    // however, in the presence of an initializer, we must
                    // emit that expression to preserve side effects.
                    let name = parameter_name.unwrap();
                    let element_count = cx.nodes[name]
                        .as_binding_pattern()
                        .elements
                        .as_ref()
                        .map(|e| e.nodes.len())
                        .unwrap_or(0);
                    if element_count > 0 {
                        let rval = ec
                            .borrow_mut()
                            .factory
                            .new_generated_name_for_node(cx.nodes, parameter);
                        let adapter = tx_adapter(v, ec);
                        let declarations = flatten_destructuring_binding(
                            &adapter,
                            cx,
                            parameter,
                            Some(rval),
                            FlattenLevel::All,
                            false,
                            false,
                        );
                        if let Some(declarations) = declarations {
                            results.push(self.make_destructuring_var_statement(
                                ec,
                                cx,
                                declarations,
                            ));
                        }
                    } else if cx.nodes[parameter].initializer().is_some() {
                        let name = ec
                            .borrow_mut()
                            .factory
                            .new_generated_name_for_node(cx.nodes, parameter);
                        let initializer = cx.nodes[parameter].initializer();
                        let initializer =
                            visit_node(v, cx, initializer.expect("parameter has no initializer"));
                        let assignment = ec.borrow_mut().factory.new_assignment_expression(
                            cx.nodes,
                            name,
                            initializer.expect("VisitNode returned no node"),
                        );
                        let statement = ec
                            .borrow_mut()
                            .factory
                            .new_expression_statement(cx.nodes, Some(assignment));
                        ec.borrow()
                            .add_emit_flags(statement, EmitFlags::CUSTOM_PROLOGUE);
                        results.push(statement);
                    }
                } else if cx.nodes[parameter].initializer().is_some() {
                    // Converts a parameter initializer into a function body
                    // statement, i.e.:
                    //
                    //  function f(x = 1) { }
                    //
                    // becomes
                    //
                    //  function f(x) {
                    //    if (typeof x === "undefined") { x = 1; }
                    //  }
                    let name_id = cx.nodes[parameter].name().unwrap();
                    let name = ec.borrow_mut().factory.clone_node(cx.nodes, name_id);
                    cx.nodes[name].loc = cx.nodes[name_id].loc;
                    ec.borrow().add_emit_flags(name, EmitFlags::NO_SOURCE_MAP);

                    let initializer = cx.nodes[parameter].initializer();
                    let initializer =
                        visit_node(v, cx, initializer.expect("parameter has no initializer"))
                            .expect("VisitNode returned no node");
                    ec.borrow().add_emit_flags(
                        initializer,
                        EmitFlags::NO_SOURCE_MAP | EmitFlags::NO_COMMENTS,
                    );

                    let assignment = ec.borrow_mut().factory.new_assignment_expression(
                        cx.nodes,
                        name,
                        initializer,
                    );
                    cx.nodes[assignment].loc = cx.nodes[parameter].loc;
                    ec.borrow()
                        .add_emit_flags(assignment, EmitFlags::NO_COMMENTS);

                    let block = {
                        let mut e = ec.borrow_mut();
                        let f = &mut e.factory;
                        let expr_stmt = f.new_expression_statement(cx.nodes, Some(assignment));
                        let stmt_list = f.new_node_list(vec![expr_stmt]);
                        f.new_block(cx.nodes, Some(stmt_list), false)
                    };
                    cx.nodes[block].loc = cx.nodes[parameter].loc;
                    ec.borrow().add_emit_flags(
                        block,
                        EmitFlags::SINGLE_LINE
                            | EmitFlags::NO_TRAILING_SOURCE_MAP
                            | EmitFlags::NO_TOKEN_SOURCE_MAPS
                            | EmitFlags::NO_COMMENTS,
                    );

                    let type_check = {
                        let name_clone = ec.borrow_mut().factory.clone_node(cx.nodes, name);
                        ec.borrow_mut()
                            .factory
                            .new_type_check(cx.nodes, name_clone, "undefined")
                    };
                    let statement = ec.borrow_mut().factory.new_if_statement(
                        cx.nodes,
                        Some(type_check),
                        Some(block),
                        None,
                    );
                    cx.nodes[statement].loc = cx.nodes[parameter].loc;
                    ec.borrow().add_emit_flags(
                        statement,
                        EmitFlags::NO_TOKEN_SOURCE_MAPS
                            | EmitFlags::NO_TRAILING_SOURCE_MAP
                            | EmitFlags::CUSTOM_PROLOGUE
                            | EmitFlags::NO_COMMENTS
                            | EmitFlags::START_ON_NEW_LINE,
                    );
                    results.push(statement);
                }
            } else if subtree_facts(cx, parameter) & SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
                != SubtreeFacts::NONE
            {
                contains_preceding_object_rest_or_spread = true;
                let rval = ec
                    .borrow_mut()
                    .factory
                    .new_generated_name_for_node(cx.nodes, parameter);
                let adapter = tx_adapter(v, ec);
                let declarations = flatten_destructuring_binding(
                    &adapter,
                    cx,
                    parameter,
                    Some(rval),
                    FlattenLevel::ObjectRest,
                    false,
                    true,
                );
                if let Some(declarations) = declarations {
                    results.push(self.make_destructuring_var_statement(ec, cx, declarations));
                }
            }
        }

        results
    }

    /// Shared tail of `collectObjectRestAssignments` — wraps a flatten
    /// result (declaration or SyntaxList of declarations) in a
    /// `VariableStatement` flagged `EFCustomPrologue`.
    fn make_destructuring_var_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        declarations: NodeId,
    ) -> NodeId {
        let decls: Vec<NodeId> = if cx.nodes[declarations].kind == Kind::SyntaxList {
            cx.nodes[declarations].as_syntax_list().children.to_vec()
        } else {
            vec![declarations]
        };
        let statement = {
            let mut e = ec.borrow_mut();
            let f = &mut e.factory;
            let empty = f.new_node_list(vec![]);
            let declaration_list =
                f.new_variable_declaration_list(cx.nodes, Some(empty), ast::NodeFlags::NONE);
            cx.nodes[declaration_list]
                .as_variable_declaration_list_mut()
                .declarations
                .as_mut()
                .unwrap()
                .nodes = decls.into_boxed_slice().into();
            f.new_variable_statement(cx.nodes, None, Some(declaration_list))
        };
        ec.borrow()
            .add_emit_flags(statement, EmitFlags::CUSTOM_PROLOGUE);
        statement
    }

    /// `(ch *objectRestSpreadTransformer) visitCatchClause` — `node` must be
    /// a `CatchClause`.
    fn visit_catch_clause(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let variable_declaration = cx.nodes[node].as_catch_clause().variable_declaration;
        let needs_flatten = variable_declaration.is_some_and(|decl| {
            cx.nodes[decl]
                .name()
                .is_some_and(|n| ast::is_binding_pattern(&cx.nodes[n]))
                && cx.nodes[decl].name().is_some_and(|n| {
                    cx.nodes[n].subtree_facts(cx.nodes)
                        & SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
                        != SubtreeFacts::NONE
                })
        });
        if needs_flatten {
            let decl = variable_declaration.unwrap();
            let decl_name = cx.nodes[decl].name().unwrap();
            let name = ec
                .borrow_mut()
                .factory
                .new_generated_name_for_node(cx.nodes, decl_name);
            let updated_decl = ec
                .borrow_mut()
                .factory
                .update_variable_declaration(
                    cx.nodes,
                    decl,
                    Some(decl_name),
                    None,
                    None,
                    Some(name),
                )
                .unwrap_or(decl);
            let adapter = tx_adapter(v, ec);
            let visited_bindings = flatten_destructuring_binding(
                &adapter,
                cx,
                updated_decl,
                None,
                FlattenLevel::ObjectRest,
                false,
                false,
            );
            let block_id = cx.nodes[node].as_catch_clause().block.unwrap();
            let mut block = visit_node(v, cx, block_id).expect("VisitNode returned no node");
            if let Some(visited_bindings) = visited_bindings {
                let decls: Vec<NodeId> = if cx.nodes[visited_bindings].kind == Kind::SyntaxList {
                    cx.nodes[visited_bindings]
                        .as_syntax_list()
                        .children
                        .to_vec()
                } else {
                    vec![visited_bindings]
                };
                let new_statement = {
                    let mut e = ec.borrow_mut();
                    let f = &mut e.factory;
                    let decl_list_nodes = f.new_node_list(decls);
                    let decl_list = f.new_variable_declaration_list(
                        cx.nodes,
                        Some(decl_list_nodes),
                        ast::NodeFlags::NONE,
                    );
                    f.new_variable_statement(cx.nodes, None, Some(decl_list))
                };
                let mut statements: Vec<NodeId> = vec![new_statement];
                statements.extend(
                    cx.nodes[block]
                        .statements()
                        .map(<[_]>::to_vec)
                        .unwrap_or_default(),
                );
                let mut statement_list = ec.borrow_mut().factory.new_node_list(statements);
                statement_list.loc = cx.nodes[block]
                    .statement_list()
                    .map(|l| l.loc)
                    .unwrap_or_else(TextRange::default);
                let multi_line = cx.nodes[block].as_block().multi_line;
                block = ec
                    .borrow_mut()
                    .factory
                    .update_block(cx.nodes, block, Some(statement_list), multi_line)
                    .unwrap_or(block);
            }
            let updated_variable_declaration = ec
                .borrow_mut()
                .factory
                .update_variable_declaration(cx.nodes, decl, Some(name), None, None, None)
                .unwrap_or(decl);
            return ec
                .borrow_mut()
                .factory
                .update_catch_clause(
                    cx.nodes,
                    node,
                    Some(updated_variable_declaration),
                    Some(block),
                )
                .unwrap_or(node);
        }
        visit_each_child(v, cx, node)
    }

    /// `(ch *objectRestSpreadTransformer) visitVariableStatement` — `node`
    /// must be a `VariableStatement`.
    fn visit_variable_statement(
        &self,
        _ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::EXPORT) {
            let old_in_exported_variable_statement =
                self.in_exported_variable_statement.replace(true);
            let result = visit_each_child(v, cx, node);
            self.in_exported_variable_statement
                .set(old_in_exported_variable_statement);
            return result;
        }
        visit_each_child(v, cx, node)
    }

    /// `(ch *objectRestSpreadTransformer) visitVariableDeclaration` — `node`
    /// must be a `VariableDeclaration`.
    fn visit_variable_declaration(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if self.in_exported_variable_statement.get() {
            self.in_exported_variable_statement.set(false);
            let result = self.visit_variable_declaration_worker(ec, v, cx, node, true);
            self.in_exported_variable_statement.set(true);
            return result;
        }
        self.visit_variable_declaration_worker(ec, v, cx, node, false)
    }

    /// `(ch *objectRestSpreadTransformer) visitVariableDeclarationWorker` —
    /// `node` must be a `VariableDeclaration`.
    fn visit_variable_declaration_worker(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        exported: bool,
    ) -> Option<NodeId> {
        // If we are here it is because the name contains a binding pattern
        // with a rest somewhere in it.
        if cx.nodes[node]
            .name()
            .is_some_and(|n| ast::is_binding_pattern(&cx.nodes[n]))
            && subtree_facts(cx, node) & SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
                != SubtreeFacts::NONE
        {
            let adapter = tx_adapter(v, ec);
            return flatten_destructuring_binding(
                &adapter,
                cx,
                node,
                None,
                FlattenLevel::ObjectRest,
                exported,
                false,
            );
        }
        Some(visit_each_child(v, cx, node))
    }

    /// `(ch *objectRestSpreadTransformer) visitForOftatement` — `node` must
    /// be a `ForInOrOfStatement`.
    fn visit_for_of_statement(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let initializer = cx.nodes[node]
            .as_for_in_or_of_statement()
            .initializer
            .expect("for-of statement has no initializer");
        if subtree_facts(cx, initializer) & SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
            != SubtreeFacts::NONE
            || (ast::is_assignment_pattern(&cx.nodes[initializer])
                && ast::contains_object_rest_or_spread(&cx.nodes[initializer], cx.nodes))
        {
            let initializer_without_parens = ast::skip_parentheses(initializer, cx.nodes);
            if ast::is_variable_declaration_list(&cx.nodes[initializer_without_parens])
                || ast::is_assignment_pattern(&cx.nodes[initializer_without_parens])
            {
                let mut body_location = TextRange::default();
                let mut statements_location = TextRange::default();
                let temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                let binding_statement = ec.borrow_mut().factory.create_for_of_binding_statement(
                    cx.nodes,
                    initializer_without_parens,
                    temp,
                );
                let res = v.visit_node(cx, Some(binding_statement));
                let mut statements: Vec<NodeId> = Vec::with_capacity(1);
                if let Some(res) = res {
                    statements.push(res);
                }
                let statement = cx.nodes[node].as_for_in_or_of_statement().statement;
                if let Some(statement_id) = statement {
                    if ast::is_block(&cx.nodes[statement_id]) {
                        let block_statements: Vec<NodeId> = cx.nodes[statement_id]
                            .statements()
                            .map(<[_]>::to_vec)
                            .unwrap_or_default();
                        for stmt in block_statements {
                            let visited = v.visit_each_child(cx, stmt).unwrap_or(stmt);
                            statements.push(visited);
                        }
                        body_location = cx.nodes[statement_id].loc;
                        statements_location = cx.nodes[statement_id]
                            .statement_list()
                            .map(|l| l.loc)
                            .unwrap_or_else(TextRange::default);
                    } else {
                        let visited = v.visit_each_child(cx, statement_id).unwrap_or(statement_id);
                        statements.push(visited);
                        body_location = cx.nodes[statement_id].loc;
                        statements_location = cx.nodes[statement_id].loc;
                    }
                }

                let initializer_loc = cx.nodes[initializer].loc;
                let list = {
                    let mut e = ec.borrow_mut();
                    let f = &mut e.factory;
                    let decl = f.new_variable_declaration(cx.nodes, Some(temp), None, None, None);
                    let decls = f.new_node_list(vec![decl]);
                    f.new_variable_declaration_list(cx.nodes, Some(decls), ast::NodeFlags::LET)
                };
                cx.nodes[list].loc = initializer_loc;

                let expression = cx.nodes[node]
                    .as_for_in_or_of_statement()
                    .expression
                    .expect("for-of statement has no expression");
                let expr = v.visit_each_child(cx, expression).unwrap_or(expression);

                let mut statements_list = ec.borrow_mut().factory.new_node_list(statements);
                statements_list.loc = statements_location;

                let block =
                    ec.borrow_mut()
                        .factory
                        .new_block(cx.nodes, Some(statements_list), true);
                cx.nodes[block].loc = body_location;

                let await_modifier = cx.nodes[node].as_for_in_or_of_statement().await_modifier;
                return ec
                    .borrow_mut()
                    .factory
                    .update_for_in_or_of_statement(
                        cx.nodes,
                        node,
                        await_modifier,
                        Some(list),
                        Some(expr),
                        Some(block),
                    )
                    .unwrap_or(node);
            }
        }
        visit_each_child(v, cx, node)
    }

    /// `(ch *objectRestSpreadTransformer) visitBinaryExpression` — `node`
    /// must be a `BinaryExpression`.
    fn visit_binary_expression(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        expression_result_is_unused: bool,
    ) -> Option<NodeId> {
        if ast::is_destructuring_assignment(&cx.nodes[node], cx.nodes)
            && cx.nodes[node]
                .as_binary_expression()
                .left
                .is_some_and(|l| ast::contains_object_rest_or_spread(&cx.nodes[l], cx.nodes))
        {
            let adapter = tx_adapter(v, ec);
            return flatten_destructuring_assignment(
                &adapter,
                cx,
                node,
                !expression_result_is_unused,
                FlattenLevel::ObjectRest,
                None,
            );
        }
        let (left_in, operator_token, right_in) = {
            let d = cx.nodes[node].as_binary_expression();
            (d.left, d.operator_token, d.right)
        };
        if operator_token.is_some_and(|t| cx.nodes[t].kind == Kind::CommaToken) {
            self.expression_result_is_unused.set(true);
            let left = v.visit_node(cx, left_in);
            self.expression_result_is_unused
                .set(expression_result_is_unused);
            let right = v.visit_node(cx, right_in);
            return Some(
                ec.borrow_mut()
                    .factory
                    .update_binary_expression(
                        cx.nodes,
                        node,
                        None,
                        left,
                        None,
                        operator_token,
                        right,
                    )
                    .unwrap_or(node),
            );
        }
        Some(visit_each_child(v, cx, node))
    }

    /// `(ch *objectRestSpreadTransformer) visitObjectLiteralExpression` —
    /// `node` must be an `ObjectLiteralExpression`.
    fn visit_object_literal_expression(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if subtree_facts(cx, node) & SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
            == SubtreeFacts::NONE
        {
            return visit_each_child(v, cx, node);
        }
        // spread elements emit like so:
        // non-spread elements are chunked together into object literals, and
        // then all are passed to __assign:
        //     { a, ...o, b } => __assign(__assign({a}, o), {b});
        // If the first element is a spread element, then the first argument
        // to __assign is {}:
        //     { ...o, a, b, ...o2 } => __assign(__assign(__assign({}, o), {a, b}), o2)
        //
        // We cannot call __assign with more than two elements, since any
        // element could cause side effects. For example:
        //      var k = { a: 1, b: 2 };
        //      var o = { a: 3, ...k, b: k.a++ };
        //      // expected: { a: 1, b: 1 }
        // If we translate the above to `__assign({ a: 3 }, k, { b: k.a++ })`,
        // the `k.a++` will evaluate before `k` is spread and we end up with
        // `{ a: 2, b: 1 }`.
        //
        // This also occurs for spread elements, not just property
        // assignments:
        //      var k = { a: 1, get b() { l = { z: 9 }; return 2; } };
        //      var l = { c: 3 };
        //      var o = { ...k, ...l };
        //      // expected: { a: 1, b: 2, z: 9 }
        // If we translate the above to `__assign({}, k, l)`, the `l` will
        // evaluate before `k` is spread and we end up with `{ a: 1, b: 2,
        // c: 3 }`

        let properties = cx.nodes[node]
            .as_object_literal_expression()
            .properties
            .clone();
        let mut objects = self.chunk_object_literal_elements(ec, v, cx, properties);
        if !objects.is_empty() && cx.nodes[objects[0]].kind != Kind::ObjectLiteralExpression {
            let empty_literal = {
                let mut e = ec.borrow_mut();
                let empty = e.factory.new_node_list(vec![]);
                e.factory
                    .new_object_literal_expression(cx.nodes, Some(empty), false)
            };
            objects.insert(0, empty_literal);
        }
        let mut expression = objects[0];
        if objects.len() > 1 {
            let script_target = self
                .compiler_options
                .expect("objectRestSpreadTransformer requires compiler options")
                .get_emit_script_target();
            for (i, &obj) in objects.iter().enumerate() {
                if i == 0 {
                    continue;
                }
                expression = ec.borrow_mut().factory.new_assign_helper(
                    cx.nodes,
                    vec![expression, obj],
                    script_target,
                );
            }
            return expression;
        }
        let script_target = self
            .compiler_options
            .expect("objectRestSpreadTransformer requires compiler options")
            .get_emit_script_target();
        ec.borrow_mut()
            .factory
            .new_assign_helper(cx.nodes, objects, script_target)
    }

    /// `(ch *objectRestSpreadTransformer) chunkObjectLiteralElements` —
    /// `list` is the properties `NodeList` of an `ObjectLiteralExpression`
    /// (`None` mirrors Go nil).
    fn chunk_object_literal_elements(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        list: Option<NodeList>,
    ) -> Vec<NodeId> {
        let Some(list) = list else {
            return Vec::new();
        };
        if list.nodes.is_empty() {
            return Vec::new();
        }
        let elements = list.nodes;
        let mut chunk_object: Vec<NodeId> = Vec::new();
        let mut objects: Vec<NodeId> = Vec::with_capacity(1);
        for e in elements.iter() {
            if cx.nodes[*e].kind == Kind::SpreadAssignment {
                if !chunk_object.is_empty() {
                    let lit = {
                        let mut ecg = ec.borrow_mut();
                        let props = ecg.factory.new_node_list(std::mem::take(&mut chunk_object));
                        ecg.factory
                            .new_object_literal_expression(cx.nodes, Some(props), false)
                    };
                    objects.push(lit);
                }
                let target = cx.nodes[*e].expression();
                let visited = v
                    .visit_node(cx, target)
                    .expect("VisitNode returned no node");
                objects.push(visited);
            } else {
                let elem = if cx.nodes[*e].kind == Kind::PropertyAssignment {
                    let name = cx.nodes[*e].name();
                    let initializer = cx.nodes[*e].initializer();
                    let visited = v.visit_node(cx, initializer);
                    ec.borrow_mut()
                        .factory
                        .new_property_assignment(cx.nodes, None, name, None, None, visited)
                } else {
                    v.visit_node(cx, Some(*e))
                        .expect("VisitNode returned no node")
                };
                chunk_object.push(elem);
            }
        }
        if !chunk_object.is_empty() {
            let lit = {
                let mut ecg = ec.borrow_mut();
                let props = ecg.factory.new_node_list(chunk_object);
                ecg.factory
                    .new_object_literal_expression(cx.nodes, Some(props), false)
            };
            objects.push(lit);
        }
        objects
    }
}
