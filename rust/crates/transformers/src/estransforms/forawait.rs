// Ported from tsc/internal/transformers/estransforms/forawait.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `newforawaitTransformer` — downlevels `for await..of` and async
// generators (`async function*`) for ES2017 and earlier.
//
// PORT notes: see `mod.rs` and `async.rs` — same `Rc<State>` + `txv`
// (synthesized `tx.Visitor()` equivalent) + `ec_visit_*` hook conventions.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::functionflags::{FunctionFlags, get_function_flags};
use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId, NodeList, SubtreeFacts};
use tsc_collections::OrderedSet;
use tsc_core::options_generated::CompilerOptions;
use tsc_printer::{
    AutoGenerateOptions, EmitFlags, GeneratedIdentifierFlags, advanced_async_super_helper,
    async_super_helper,
};

use super::utilities::SuperAccessState;
use super::{Ec, ec_visit_function_body, ec_visit_parameters, make_transformer, subtree_facts};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;

// Facts we track as we traverse the tree
// `type forAwaitHierarchyFacts int`
//
// Ancestor facts
const HAS_LEXICAL_THIS: u32 = 1;
const ITERATION_CONTAINER: u32 = 1 << 1;

// Ancestor masks
const ANCESTOR_FACTS_MASK: u32 = (1 << 2) - 1;

const SOURCE_FILE_EXCLUDES: u32 = ITERATION_CONTAINER;
const STRICT_MODE_SOURCE_FILE_INCLUDES: u32 = 0;

const CLASS_OR_FUNCTION_INCLUDES: u32 = HAS_LEXICAL_THIS;
const CLASS_OR_FUNCTION_EXCLUDES: u32 = ITERATION_CONTAINER;

const ARROW_FUNCTION_INCLUDES: u32 = 0;
const ARROW_FUNCTION_EXCLUDES: u32 = CLASS_OR_FUNCTION_EXCLUDES;

const ITERATION_STATEMENT_INCLUDES: u32 = ITERATION_CONTAINER;
const ITERATION_STATEMENT_EXCLUDES: u32 = 0;

/// `type forawaitTransformer struct`.
pub(crate) struct ForAwaitTransformer<'a> {
    pub super_access: Rc<SuperAccessState<'a>>,
    /// `compilerOptions *core.CompilerOptions` — stored but never read (as
    /// in Go).
    #[allow(dead_code)]
    compiler_options: Option<&'a CompilerOptions>,

    enclosing_function_flags: Cell<FunctionFlags>,
    for_await_hierarchy_facts: Cell<u32>,
    exported_variable_statement: Cell<bool>,

    fallback_node_visitor: RefCell<Option<NodeVisitor<'a>>>,
    no_async_modifier_visitor: RefCell<Option<NodeVisitor<'a>>>,
}

impl<'a> ForAwaitTransformer<'a> {
    /// `affectsSubtree`.
    fn affects_subtree(&self, exclude_facts: u32, include_facts: u32) -> bool {
        let facts = self.for_await_hierarchy_facts.get();
        facts != (facts & !exclude_facts | include_facts)
    }

    /// `enterSubtree` sets the HierarchyFacts for this node prior to visiting
    /// this node's subtree, returning the facts set prior to modification.
    fn enter_subtree(&self, exclude_facts: u32, include_facts: u32) -> u32 {
        let ancestor_facts = self.for_await_hierarchy_facts.get();
        self.for_await_hierarchy_facts.set(
            (self.for_await_hierarchy_facts.get() & !exclude_facts | include_facts)
                & ANCESTOR_FACTS_MASK,
        );
        ancestor_facts
    }

    /// `exitSubtree` restores the HierarchyFacts for this node's ancestor
    /// after visiting this node's subtree.
    fn exit_subtree(&self, ancestor_facts: u32) {
        self.for_await_hierarchy_facts.set(ancestor_facts);
    }

    /// `visitModifiersNoAsync`.
    fn visit_modifiers_no_async(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        modifiers: Option<tsc_ast::ModifierList>,
    ) -> Option<tsc_ast::ModifierList> {
        self.no_async_modifier_visitor
            .borrow()
            .as_ref()
            .expect("no-async-modifier visitor not initialized")
            .visit_modifiers(cx, modifiers)
    }

    /// `doWithHierarchyFacts`.
    fn do_with_hierarchy_facts(
        self: &Rc<Self>,
        cb: impl FnOnce(&Rc<Self>, &mut VisitorCx<'_, '_>, NodeId) -> Option<NodeId>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        exclude_facts: u32,
        include_facts: u32,
    ) -> Option<NodeId> {
        if self.affects_subtree(exclude_facts, include_facts) {
            let ancestor_facts = self.enter_subtree(exclude_facts, include_facts);
            let result = cb(self, cx, node);
            self.exit_subtree(ancestor_facts);
            return result;
        }
        cb(self, cx, node)
    }

    /// A `NodeVisitor` equivalent to `tx.Visitor()` (see `async.rs` PORT note).
    fn txv(self: &Rc<Self>, ec: &Ec) -> NodeVisitor<'a> {
        let state = self.clone();
        let ec2 = ec.clone();
        ec.borrow().new_node_visitor(Box::new(
            move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec2, _v, cx, node)
            },
        ))
    }

    /// `visitDefault`.
    fn visit_default(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        self.txv(ec).visit_each_child(cx, node).or(Some(node))
    }

    /// `fallbackVisitor`.
    fn fallback_visitor(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        if self
            .super_access
            .captured_super_properties
            .borrow()
            .is_none()
        {
            return Some(node);
        }
        match cx.nodes[node].kind {
            Kind::FunctionExpression
            | Kind::FunctionDeclaration
            | Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::Constructor => return Some(node),
            _ => {}
        }
        self.super_access.track_super_access(cx, node);
        self.fallback_node_visitor
            .borrow()
            .as_ref()
            .expect("fallback visitor not initialized")
            .visit_each_child(cx, node)
            .or(Some(node))
    }

    /// `(tx *forawaitTransformer) visit` — the main visit callback.
    pub(crate) fn visit(
        self: &Rc<Self>,
        ec: &Ec,
        _v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if subtree_facts(cx, node) & SubtreeFacts::CONTAINS_FOR_AWAIT_OR_ASYNC_GENERATOR
            == SubtreeFacts::NONE
        {
            return self.fallback_visitor(cx, node);
        }
        self.super_access.track_super_access(cx, node);
        match cx.nodes[node].kind {
            Kind::SourceFile => Some(self.visit_source_file(ec, cx, node)),
            Kind::AwaitExpression => Some(self.visit_await_expression(ec, cx, node)),
            Kind::YieldExpression => Some(self.visit_yield_expression(ec, cx, node)),
            Kind::ReturnStatement => Some(self.visit_return_statement(ec, cx, node)),
            Kind::LabeledStatement => Some(self.visit_labeled_statement(ec, cx, node)),
            Kind::DoStatement | Kind::WhileStatement | Kind::ForInStatement => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_default(&ec, c, n),
                    cx,
                    node,
                    ITERATION_STATEMENT_EXCLUDES,
                    ITERATION_STATEMENT_INCLUDES,
                )
            }
            Kind::ForOfStatement => Some(self.visit_for_of_statement(ec, cx, node, None)),
            Kind::ForStatement => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_default(&ec, c, n),
                    cx,
                    node,
                    ITERATION_STATEMENT_EXCLUDES,
                    ITERATION_STATEMENT_INCLUDES,
                )
            }
            Kind::Constructor => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_constructor_declaration(&ec, c, n),
                    cx,
                    node,
                    CLASS_OR_FUNCTION_EXCLUDES,
                    CLASS_OR_FUNCTION_INCLUDES,
                )
            }
            Kind::MethodDeclaration => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_method_declaration(&ec, c, n),
                    cx,
                    node,
                    CLASS_OR_FUNCTION_EXCLUDES,
                    CLASS_OR_FUNCTION_INCLUDES,
                )
            }
            Kind::GetAccessor => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_get_accessor_declaration(&ec, c, n),
                    cx,
                    node,
                    CLASS_OR_FUNCTION_EXCLUDES,
                    CLASS_OR_FUNCTION_INCLUDES,
                )
            }
            Kind::SetAccessor => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_set_accessor_declaration(&ec, c, n),
                    cx,
                    node,
                    CLASS_OR_FUNCTION_EXCLUDES,
                    CLASS_OR_FUNCTION_INCLUDES,
                )
            }
            Kind::FunctionDeclaration => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_function_declaration(&ec, c, n),
                    cx,
                    node,
                    CLASS_OR_FUNCTION_EXCLUDES,
                    CLASS_OR_FUNCTION_INCLUDES,
                )
            }
            Kind::FunctionExpression => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_function_expression(&ec, c, n),
                    cx,
                    node,
                    CLASS_OR_FUNCTION_EXCLUDES,
                    CLASS_OR_FUNCTION_INCLUDES,
                )
            }
            Kind::ArrowFunction => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_arrow_function(&ec, c, n),
                    cx,
                    node,
                    ARROW_FUNCTION_EXCLUDES,
                    ARROW_FUNCTION_INCLUDES,
                )
            }
            Kind::ClassDeclaration | Kind::ClassExpression => {
                let ec = ec.clone();
                self.do_with_hierarchy_facts(
                    move |s, c, n| s.visit_default(&ec, c, n),
                    cx,
                    node,
                    CLASS_OR_FUNCTION_EXCLUDES,
                    CLASS_OR_FUNCTION_INCLUDES,
                )
            }
            _ => self.txv(ec).visit_each_child(cx, node).or(Some(node)),
        }
    }

    /// `(tx *forawaitTransformer) visitAwaitExpression`.
    fn visit_await_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let flags = self.enclosing_function_flags.get();
        if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL
            && flags & FunctionFlags::GENERATOR != FunctionFlags::NORMAL
        {
            let expression = cx.nodes[node].as_await_expression().expression;
            let visited = self.txv(ec).visit_node(cx, expression);
            let awaited = ec
                .borrow_mut()
                .factory
                .new_await_helper(cx.nodes, visited.expect("await expression operand"));
            let result = ec.borrow_mut().factory.new_yield_expression(
                cx.nodes,
                None, /*asterisk_token*/
                Some(awaited),
            );
            cx.nodes[result].loc = cx.nodes[node].loc;
            ec.borrow().set_original(result, node);
            return result;
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `(tx *forawaitTransformer) visitYieldExpression`.
    fn visit_yield_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let flags = self.enclosing_function_flags.get();
        if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL
            && flags & FunctionFlags::GENERATOR != FunctionFlags::NORMAL
        {
            let (asterisk_token, expression) = {
                let d = cx.nodes[node].as_yield_expression();
                (d.asterisk_token, d.expression)
            };
            if asterisk_token.is_some() {
                let expression = self.txv(ec).visit_node(cx, expression);

                let async_values_result = ec
                    .borrow_mut()
                    .factory
                    .new_async_values_helper(cx.nodes, expression.expect("yield* operand"));
                cx.nodes[async_values_result].loc =
                    expression.map(|e| cx.nodes[e].loc).unwrap_or_default();

                let async_delegator_result = ec
                    .borrow_mut()
                    .factory
                    .new_async_delegator_helper(cx.nodes, async_values_result);
                cx.nodes[async_delegator_result].loc =
                    expression.map(|e| cx.nodes[e].loc).unwrap_or_default();

                let inner_yield = ec
                    .borrow_mut()
                    .factory
                    .update_yield_expression(
                        cx.nodes,
                        node,
                        asterisk_token,
                        Some(async_delegator_result),
                    )
                    .unwrap_or(node);

                let awaited_yield = ec
                    .borrow_mut()
                    .factory
                    .new_await_helper(cx.nodes, inner_yield);

                let result = ec.borrow_mut().factory.new_yield_expression(
                    cx.nodes,
                    None, /*asterisk_token*/
                    Some(awaited_yield),
                );
                cx.nodes[result].loc = cx.nodes[node].loc;
                ec.borrow().set_original(result, node);
                return result;
            }

            let inner_expression = if let Some(expression) = expression {
                self.txv(ec)
                    .visit_node(cx, Some(expression))
                    .unwrap_or(expression)
            } else {
                ec.borrow_mut().factory.new_void_zero_expression(cx.nodes)
            };

            let awaited = self.create_downlevel_await(ec, cx, inner_expression);
            let result = ec.borrow_mut().factory.new_yield_expression(
                cx.nodes,
                None, /*asterisk_token*/
                Some(awaited),
            );
            cx.nodes[result].loc = cx.nodes[node].loc;
            ec.borrow().set_original(result, node);
            return result;
        }

        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `(tx *forawaitTransformer) visitReturnStatement`.
    fn visit_return_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let flags = self.enclosing_function_flags.get();
        if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL
            && flags & FunctionFlags::GENERATOR != FunctionFlags::NORMAL
        {
            let expression = cx.nodes[node].as_return_statement().expression;
            let expression = if let Some(expression) = expression {
                self.txv(ec)
                    .visit_node(cx, Some(expression))
                    .unwrap_or(expression)
            } else {
                ec.borrow_mut().factory.new_void_zero_expression(cx.nodes)
            };
            let awaited = self.create_downlevel_await(ec, cx, expression);
            return ec
                .borrow_mut()
                .factory
                .update_return_statement(cx.nodes, node, Some(awaited))
                .unwrap_or(node);
        }

        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `(tx *forawaitTransformer) visitLabeledStatement`.
    fn visit_labeled_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let flags = self.enclosing_function_flags.get();
        if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL {
            let statement = unwrap_innermost_statement_of_label(cx, node);
            if cx.nodes[statement].kind == Kind::ForOfStatement
                && cx.nodes[statement]
                    .as_for_in_or_of_statement()
                    .await_modifier
                    .is_some()
            {
                return self.visit_for_of_statement(ec, cx, statement, Some(node));
            }
            let visited = self
                .txv(ec)
                .visit_node(cx, Some(statement))
                .unwrap_or(statement);
            return ec
                .borrow_mut()
                .factory
                .restore_enclosing_label(cx.nodes, visited, node);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `(tx *forawaitTransformer) visitSourceFile`.
    fn visit_source_file(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let ancestor_facts =
            self.enter_subtree(SOURCE_FILE_EXCLUDES, STRICT_MODE_SOURCE_FILE_INCLUDES);
        self.exported_variable_statement.set(false);
        let visited = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
        let helpers = ec.borrow_mut().read_emit_helpers();
        ec.borrow().add_emit_helper(visited, &helpers);
        self.exit_subtree(ancestor_facts);
        visited
    }

    /// `visitForOfStatement` visits a ForOfStatement and converts it into a
    /// ES2015-compatible ForOfStatement.
    fn visit_for_of_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        outermost_labeled_statement: Option<NodeId>,
    ) -> NodeId {
        let ancestor_facts =
            self.enter_subtree(ITERATION_STATEMENT_EXCLUDES, ITERATION_STATEMENT_INCLUDES);
        let result = if cx.nodes[node]
            .as_for_in_or_of_statement()
            .await_modifier
            .is_some()
        {
            self.transform_for_await_of_statement(
                ec,
                cx,
                node,
                outermost_labeled_statement,
                ancestor_facts,
            )
        } else {
            let visited = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
            match outermost_labeled_statement {
                Some(label) => ec
                    .borrow_mut()
                    .factory
                    .restore_enclosing_label(cx.nodes, visited, label),
                None => visited,
            }
        };
        self.exit_subtree(ancestor_facts);
        result
    }

    /// `(tx *forawaitTransformer) convertForOfStatementHead`.
    fn convert_for_of_statement_head(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        bound_value: NodeId,
        non_user_code: NodeId,
    ) -> NodeId {
        let (initializer, expression, statement) = {
            let d = cx.nodes[node].as_for_in_or_of_statement();
            (d.initializer, d.expression, d.statement)
        };
        let expression_loc = expression.map(|e| cx.nodes[e].loc).unwrap_or_default();

        let value = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
        ec.borrow_mut().add_variable_declaration(cx.nodes, value);
        let iterator_value_expression =
            ec.borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, value, bound_value);
        let iterator_value_statement = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(iterator_value_expression));
        ec.borrow()
            .set_source_map_range(iterator_value_statement, expression_loc);

        let false_keyword = ec
            .borrow_mut()
            .factory
            .new_keyword_expression(cx.nodes, Kind::FalseKeyword);
        let exit_non_user_code_expression = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            non_user_code,
            false_keyword,
        );
        let exit_non_user_code_statement = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(exit_non_user_code_expression));
        ec.borrow()
            .set_source_map_range(exit_non_user_code_statement, expression_loc);

        let mut statements: Vec<NodeId> =
            vec![iterator_value_statement, exit_non_user_code_statement];
        let binding = ec.borrow_mut().factory.create_for_of_binding_statement(
            cx.nodes,
            initializer.expect("for-of has an initializer"),
            value,
        );
        let visited_binding = self
            .txv(ec)
            .visit_node(cx, Some(binding))
            .unwrap_or(binding);
        statements.push(visited_binding);

        let mut body_location = tsc_core::text::TextRange::default();
        let mut statements_location = tsc_core::text::TextRange::default();
        let statement = self
            .txv(ec)
            .visit_embedded_statement(cx, statement)
            .expect("embedded statement present");
        if ast::is_block(&cx.nodes[statement]) {
            if let Some(stmts) = cx.nodes[statement].statements() {
                statements.extend(stmts.iter().copied());
            }
            body_location = cx.nodes[statement].loc;
            statements_location = cx.nodes[statement]
                .statement_list()
                .map(|l| l.loc)
                .unwrap_or_default();
        } else {
            statements.push(statement);
        }

        let mut stmt_list = ec.borrow_mut().factory.new_node_list(statements);
        stmt_list.loc = statements_location;
        let block = ec
            .borrow_mut()
            .factory
            .new_block(cx.nodes, Some(stmt_list), true);
        cx.nodes[block].loc = body_location;
        block
    }

    /// `(tx *forawaitTransformer) createDownlevelAwait`.
    fn create_downlevel_await(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        expression: NodeId,
    ) -> NodeId {
        if self.enclosing_function_flags.get() & FunctionFlags::GENERATOR != FunctionFlags::NORMAL {
            let awaited = ec
                .borrow_mut()
                .factory
                .new_await_helper(cx.nodes, expression);
            return ec.borrow_mut().factory.new_yield_expression(
                cx.nodes,
                None, /*asterisk_token*/
                Some(awaited),
            );
        }
        ec.borrow_mut()
            .factory
            .new_await_expression(cx.nodes, Some(expression))
    }

    /// `(tx *forawaitTransformer) transformForAwaitOfStatement`.
    fn transform_for_await_of_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        outermost_labeled_statement: Option<NodeId>,
        ancestor_facts: u32,
    ) -> NodeId {
        let expression_node = cx.nodes[node].as_for_in_or_of_statement().expression;
        let expression_loc = expression_node.map(|e| cx.nodes[e].loc).unwrap_or_default();
        let expression = self.txv(ec).visit_node(cx, expression_node);

        let iterator = if expression.is_some_and(|e| ast::is_identifier(&cx.nodes[e])) {
            ec.borrow_mut()
                .factory
                .new_generated_name_for_node(cx.nodes, expression.unwrap())
        } else {
            ec.borrow_mut().factory.new_temp_variable(cx.nodes)
        };

        let result = if expression.is_some_and(|e| ast::is_identifier(&cx.nodes[e])) {
            ec.borrow_mut()
                .factory
                .new_generated_name_for_node(cx.nodes, iterator)
        } else {
            ec.borrow_mut().factory.new_temp_variable(cx.nodes)
        };

        let non_user_code = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
        let done = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
        ec.borrow_mut().add_variable_declaration(cx.nodes, done);
        let error_record = ec.borrow_mut().factory.new_unique_name(cx.nodes, "e");
        let catch_variable = ec
            .borrow_mut()
            .factory
            .new_generated_name_for_node(cx.nodes, error_record);
        let return_method = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
        let call_values = ec
            .borrow_mut()
            .factory
            .new_async_values_helper(cx.nodes, expression.expect("for-of expression"));
        cx.nodes[call_values].loc = expression_loc;
        let next_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "next");
        let next_access = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(iterator),
            None,
            Some(next_ident),
            ast::NodeFlags::NONE,
        );
        let empty_args = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
        let call_next = ec.borrow_mut().factory.new_call_expression(
            cx.nodes,
            Some(next_access),
            None,
            None,
            Some(empty_args),
            ast::NodeFlags::NONE,
        );
        let done_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "done");
        let get_done = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(result),
            None,
            Some(done_ident),
            ast::NodeFlags::NONE,
        );
        let value_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "value");
        let get_value = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(result),
            None,
            Some(value_ident),
            ast::NodeFlags::NONE,
        );
        let call_return = ec.borrow_mut().factory.new_function_call_call(
            cx.nodes,
            return_method,
            Some(iterator),
            vec![],
        );

        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, error_record);
        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, return_method);

        // if we are enclosed in an outer loop ensure we reset 'errorRecord' per each iteration
        let initializer = if ancestor_facts & ITERATION_CONTAINER != 0 {
            let void_zero = ec.borrow_mut().factory.new_void_zero_expression(cx.nodes);
            let reset = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                error_record,
                void_zero,
            );
            ec.borrow_mut()
                .factory
                .inline_expressions(cx.nodes, &[reset, call_values])
        } else {
            Some(call_values)
        };

        // Build the for statement
        let iterator_decl = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(iterator),
            None,
            None,
            initializer,
        );
        cx.nodes[iterator_decl].loc = expression_loc;
        let true_keyword = ec
            .borrow_mut()
            .factory
            .new_keyword_expression(cx.nodes, Kind::TrueKeyword);
        let non_user_code_decl = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(non_user_code),
            None,
            None,
            Some(true_keyword),
        );
        let result_decl = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(result),
            None,
            None,
            None,
        );
        let decls = ec.borrow_mut().factory.new_node_list(vec![
            non_user_code_decl,
            iterator_decl,
            result_decl,
        ]);
        let var_decl_list = ec.borrow_mut().factory.new_variable_declaration_list(
            cx.nodes,
            Some(decls),
            ast::NodeFlags::NONE,
        );
        cx.nodes[var_decl_list].loc = expression_loc;

        let downlevel_await_next = self.create_downlevel_await(ec, cx, call_next);
        let assign_result = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            result,
            downlevel_await_next,
        );
        let assign_done = ec
            .borrow_mut()
            .factory
            .new_assignment_expression(cx.nodes, done, get_done);
        let not_done = ec.borrow_mut().factory.new_prefix_unary_expression(
            cx.nodes,
            Kind::ExclamationToken,
            Some(done),
        );
        let condition = ec
            .borrow_mut()
            .factory
            .inline_expressions(cx.nodes, &[assign_result, assign_done, not_done]);

        let true_keyword = ec
            .borrow_mut()
            .factory
            .new_keyword_expression(cx.nodes, Kind::TrueKeyword);
        let incrementor = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            non_user_code,
            true_keyword,
        );

        let body = self.convert_for_of_statement_head(ec, cx, node, get_value, non_user_code);
        let for_statement = ec.borrow_mut().factory.new_for_statement(
            cx.nodes,
            Some(var_decl_list),
            condition,
            Some(incrementor),
            Some(body),
        );
        cx.nodes[for_statement].loc = cx.nodes[node].loc;
        ec.borrow()
            .add_emit_flags(for_statement, EmitFlags::NO_TOKEN_TRAILING_SOURCE_MAPS);
        ec.borrow().set_original(for_statement, node);

        // Build the try/catch/finally
        let inner = match outermost_labeled_statement {
            Some(label) => {
                ec.borrow_mut()
                    .factory
                    .restore_enclosing_label(cx.nodes, for_statement, label)
            }
            None => for_statement,
        };
        let try_stmts = ec.borrow_mut().factory.new_node_list([inner]);
        let try_block = ec
            .borrow_mut()
            .factory
            .new_block(cx.nodes, Some(try_stmts), true);

        // catch clause: { e_1 = { error: e_2 }; }
        let error_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "error");
        let error_prop = ec.borrow_mut().factory.new_property_assignment(
            cx.nodes,
            None,
            Some(error_ident),
            None,
            None,
            Some(catch_variable),
        );
        let props = ec.borrow_mut().factory.new_node_list([error_prop]);
        let obj_literal =
            ec.borrow_mut()
                .factory
                .new_object_literal_expression(cx.nodes, Some(props), false);
        let assign_error =
            ec.borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, error_record, obj_literal);
        let catch_expr_stmt = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(assign_error));
        let catch_stmts = ec.borrow_mut().factory.new_node_list([catch_expr_stmt]);
        let catch_body = ec
            .borrow_mut()
            .factory
            .new_block(cx.nodes, Some(catch_stmts), false);
        ec.borrow()
            .add_emit_flags(catch_body, EmitFlags::SINGLE_LINE);
        let catch_var_decl = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(catch_variable),
            None,
            None,
            None,
        );
        let catch_clause = ec.borrow_mut().factory.new_catch_clause(
            cx.nodes,
            Some(catch_var_decl),
            Some(catch_body),
        );

        // finally block
        // inner try: if (!nonUserCode && !done && (returnMethod = iterator.return)) await returnMethod.call(iterator);
        let not_non_user_code = ec.borrow_mut().factory.new_prefix_unary_expression(
            cx.nodes,
            Kind::ExclamationToken,
            Some(non_user_code),
        );
        let not_done = ec.borrow_mut().factory.new_prefix_unary_expression(
            cx.nodes,
            Kind::ExclamationToken,
            Some(done),
        );
        let and_token = ec
            .borrow_mut()
            .factory
            .new_token(cx.nodes, Kind::AmpersandAmpersandToken);
        let left_and = ec.borrow_mut().factory.new_binary_expression(
            cx.nodes,
            None,
            Some(not_non_user_code),
            None,
            Some(and_token),
            Some(not_done),
        );
        let return_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "return");
        let return_access = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(iterator),
            None,
            Some(return_ident),
            ast::NodeFlags::NONE,
        );
        let assign_return_method = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            return_method,
            return_access,
        );
        let and_token2 = ec
            .borrow_mut()
            .factory
            .new_token(cx.nodes, Kind::AmpersandAmpersandToken);
        let inner_if_condition = ec.borrow_mut().factory.new_binary_expression(
            cx.nodes,
            None,
            Some(left_and),
            None,
            Some(and_token2),
            Some(assign_return_method),
        );
        let awaited_call_return = self.create_downlevel_await(ec, cx, call_return);
        let inner_if_then = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(awaited_call_return));
        let inner_if_statement = ec.borrow_mut().factory.new_if_statement(
            cx.nodes,
            Some(inner_if_condition),
            Some(inner_if_then),
            None,
        );
        ec.borrow()
            .add_emit_flags(inner_if_statement, EmitFlags::SINGLE_LINE);

        let inner_try_stmts = ec.borrow_mut().factory.new_node_list([inner_if_statement]);
        let inner_try_block =
            ec.borrow_mut()
                .factory
                .new_block(cx.nodes, Some(inner_try_stmts), false);

        // inner finally: if (errorRecord) throw errorRecord.error;
        let error_ident2 = ec.borrow_mut().factory.new_identifier(cx.nodes, "error");
        let error_access = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(error_record),
            None,
            Some(error_ident2),
            ast::NodeFlags::NONE,
        );
        let throw_stmt = ec
            .borrow_mut()
            .factory
            .new_throw_statement(cx.nodes, Some(error_access));
        let inner_finally_if = ec.borrow_mut().factory.new_if_statement(
            cx.nodes,
            Some(error_record),
            Some(throw_stmt),
            None,
        );
        ec.borrow()
            .add_emit_flags(inner_finally_if, EmitFlags::SINGLE_LINE);
        let inner_finally_stmts = ec.borrow_mut().factory.new_node_list([inner_finally_if]);
        let inner_finally_block =
            ec.borrow_mut()
                .factory
                .new_block(cx.nodes, Some(inner_finally_stmts), false);
        ec.borrow()
            .add_emit_flags(inner_finally_block, EmitFlags::SINGLE_LINE);

        let inner_try_statement = ec.borrow_mut().factory.new_try_statement(
            cx.nodes,
            Some(inner_try_block),
            None,
            Some(inner_finally_block),
        );
        let finally_stmts = ec.borrow_mut().factory.new_node_list([inner_try_statement]);
        let finally_block = ec
            .borrow_mut()
            .factory
            .new_block(cx.nodes, Some(finally_stmts), true);

        ec.borrow_mut().factory.new_try_statement(
            cx.nodes,
            Some(try_block),
            Some(catch_clause),
            Some(finally_block),
        )
    }

    /// `(tx *forawaitTransformer) visitConstructorDeclaration`.
    fn visit_constructor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_enclosing_function_flags = self
            .enclosing_function_flags
            .replace(get_function_flags(Some(&cx.nodes[node])));
        let txv = self.txv(ec);
        let modifiers = cx.nodes[node].modifiers().cloned();
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_parameters = ec_visit_parameters(&txv, cx, parameters);
        let body = cx.nodes[node].body();
        let visited_body = ec_visit_function_body(&txv, cx, body);
        let updated = ec
            .borrow_mut()
            .factory
            .update_constructor_declaration(
                cx.nodes,
                node,
                modifiers,
                None, /*type_parameters*/
                visited_parameters,
                None, /*type_node*/
                None, /*full_signature*/
                visited_body,
            )
            .unwrap_or(node);
        self.enclosing_function_flags
            .set(saved_enclosing_function_flags);
        Some(updated)
    }

    /// `(tx *forawaitTransformer) visitGetAccessorDeclaration`.
    fn visit_get_accessor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_enclosing_function_flags = self
            .enclosing_function_flags
            .replace(get_function_flags(Some(&cx.nodes[node])));
        let txv = self.txv(ec);
        let modifiers = cx.nodes[node].modifiers().cloned();
        let name = cx.nodes[node].name();
        let visited_name = txv.visit_node(cx, name);
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_parameters = ec_visit_parameters(&txv, cx, parameters);
        let body = cx.nodes[node].body();
        let visited_body = ec_visit_function_body(&txv, cx, body);
        let updated = ec
            .borrow_mut()
            .factory
            .update_get_accessor_declaration(
                cx.nodes,
                node,
                modifiers,
                visited_name,
                None, /*type_parameters*/
                visited_parameters,
                None, /*type_node*/
                None, /*full_signature*/
                visited_body,
            )
            .unwrap_or(node);
        self.enclosing_function_flags
            .set(saved_enclosing_function_flags);
        Some(updated)
    }

    /// `(tx *forawaitTransformer) visitSetAccessorDeclaration`.
    fn visit_set_accessor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_enclosing_function_flags = self
            .enclosing_function_flags
            .replace(get_function_flags(Some(&cx.nodes[node])));
        let txv = self.txv(ec);
        let modifiers = cx.nodes[node].modifiers().cloned();
        let name = cx.nodes[node].name();
        let visited_name = txv.visit_node(cx, name);
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_parameters = ec_visit_parameters(&txv, cx, parameters);
        let body = cx.nodes[node].body();
        let visited_body = ec_visit_function_body(&txv, cx, body);
        let updated = ec
            .borrow_mut()
            .factory
            .update_set_accessor_declaration(
                cx.nodes,
                node,
                modifiers,
                visited_name,
                None, /*type_parameters*/
                visited_parameters,
                None, /*type_node*/
                None, /*full_signature*/
                visited_body,
            )
            .unwrap_or(node);
        self.enclosing_function_flags
            .set(saved_enclosing_function_flags);
        Some(updated)
    }

    /// `(tx *forawaitTransformer) visitMethodDeclaration`.
    fn visit_method_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_enclosing_function_flags = self
            .enclosing_function_flags
            .replace(get_function_flags(Some(&cx.nodes[node])));
        let txv = self.txv(ec);
        let flags = self.enclosing_function_flags.get();

        let original_modifiers = cx.nodes[node].modifiers().cloned();
        let modifiers = if flags & FunctionFlags::GENERATOR != FunctionFlags::NORMAL {
            self.visit_modifiers_no_async(cx, original_modifiers)
        } else {
            original_modifiers
        };

        let decl_asterisk = cx.nodes[node]
            .as_method_declaration()
            .function_like_with_body_base
            .body_base
            .asterisk_token;
        let asterisk_token = if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL {
            None
        } else {
            decl_asterisk
        };

        let (parameters, body);
        if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL
            && flags & FunctionFlags::GENERATOR != FunctionFlags::NORMAL
        {
            parameters =
                Some(self.transform_async_generator_function_parameter_list(ec, &txv, cx, node));
            body = Some(self.transform_async_generator_function_body(ec, cx, node));
        } else {
            let params = cx.nodes[node].parameter_list().cloned();
            parameters = ec_visit_parameters(&txv, cx, params);
            let decl_body = cx.nodes[node].body();
            body = ec_visit_function_body(&txv, cx, decl_body);
        }

        let name = cx.nodes[node].name();
        let visited_name = txv.visit_node(cx, name);
        let updated = ec
            .borrow_mut()
            .factory
            .update_method_declaration(
                cx.nodes,
                node,
                modifiers,
                asterisk_token,
                visited_name,
                None, /*postfix_token*/
                None, /*type_parameters*/
                parameters,
                None, /*type_node*/
                None, /*full_signature*/
                body,
            )
            .unwrap_or(node);
        self.enclosing_function_flags
            .set(saved_enclosing_function_flags);
        Some(updated)
    }

    /// `(tx *forawaitTransformer) visitFunctionDeclaration`.
    fn visit_function_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_enclosing_function_flags = self
            .enclosing_function_flags
            .replace(get_function_flags(Some(&cx.nodes[node])));
        let txv = self.txv(ec);
        let flags = self.enclosing_function_flags.get();

        let original_modifiers = cx.nodes[node].modifiers().cloned();
        let modifiers = if flags & FunctionFlags::GENERATOR != FunctionFlags::NORMAL {
            self.visit_modifiers_no_async(cx, original_modifiers)
        } else {
            original_modifiers
        };

        let decl_asterisk = cx.nodes[node]
            .as_function_declaration()
            .function_like_with_body_base
            .body_base
            .asterisk_token;
        let asterisk_token = if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL {
            None
        } else {
            decl_asterisk
        };

        let (parameters, body);
        if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL
            && flags & FunctionFlags::GENERATOR != FunctionFlags::NORMAL
        {
            parameters =
                Some(self.transform_async_generator_function_parameter_list(ec, &txv, cx, node));
            body = Some(self.transform_async_generator_function_body(ec, cx, node));
        } else {
            let params = cx.nodes[node].parameter_list().cloned();
            parameters = ec_visit_parameters(&txv, cx, params);
            let decl_body = cx.nodes[node].body();
            body = ec_visit_function_body(&txv, cx, decl_body);
        }

        let name = cx.nodes[node].name();
        let updated = ec
            .borrow_mut()
            .factory
            .update_function_declaration(
                cx.nodes,
                node,
                modifiers,
                asterisk_token,
                name,
                None, /*type_parameters*/
                parameters,
                None, /*type_node*/
                None, /*full_signature*/
                body,
            )
            .unwrap_or(node);
        self.enclosing_function_flags
            .set(saved_enclosing_function_flags);
        Some(updated)
    }

    /// `(tx *forawaitTransformer) visitArrowFunction`.
    fn visit_arrow_function(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_enclosing_function_flags = self
            .enclosing_function_flags
            .replace(get_function_flags(Some(&cx.nodes[node])));
        let txv = self.txv(ec);
        let modifiers = cx.nodes[node].modifiers().cloned();
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_parameters = ec_visit_parameters(&txv, cx, parameters);
        let body = cx.nodes[node].body();
        let visited_body = ec_visit_function_body(&txv, cx, body);
        let equals_greater_than_token =
            cx.nodes[node].as_arrow_function().equals_greater_than_token;
        let updated = ec
            .borrow_mut()
            .factory
            .update_arrow_function(
                cx.nodes,
                node,
                modifiers,
                None, /*type_parameters*/
                visited_parameters,
                None, /*type_node*/
                None, /*full_signature*/
                equals_greater_than_token,
                visited_body,
            )
            .unwrap_or(node);
        self.enclosing_function_flags
            .set(saved_enclosing_function_flags);
        Some(updated)
    }

    /// `(tx *forawaitTransformer) visitFunctionExpression`.
    fn visit_function_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_enclosing_function_flags = self
            .enclosing_function_flags
            .replace(get_function_flags(Some(&cx.nodes[node])));
        let txv = self.txv(ec);
        let flags = self.enclosing_function_flags.get();

        let original_modifiers = cx.nodes[node].modifiers().cloned();
        let modifiers = if flags & FunctionFlags::GENERATOR != FunctionFlags::NORMAL {
            self.visit_modifiers_no_async(cx, original_modifiers)
        } else {
            original_modifiers
        };

        let decl_asterisk = cx.nodes[node]
            .as_function_expression()
            .function_like_with_body_base
            .body_base
            .asterisk_token;
        let asterisk_token = if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL {
            None
        } else {
            decl_asterisk
        };

        let (parameters, body);
        if flags & FunctionFlags::ASYNC != FunctionFlags::NORMAL
            && flags & FunctionFlags::GENERATOR != FunctionFlags::NORMAL
        {
            parameters =
                Some(self.transform_async_generator_function_parameter_list(ec, &txv, cx, node));
            body = Some(self.transform_async_generator_function_body(ec, cx, node));
        } else {
            let params = cx.nodes[node].parameter_list().cloned();
            parameters = ec_visit_parameters(&txv, cx, params);
            let decl_body = cx.nodes[node].body();
            body = ec_visit_function_body(&txv, cx, decl_body);
        }

        let name = cx.nodes[node].name();
        let updated = ec
            .borrow_mut()
            .factory
            .update_function_expression(
                cx.nodes,
                node,
                modifiers,
                asterisk_token,
                name,
                None, /*type_parameters*/
                parameters,
                None, /*type_node*/
                None, /*full_signature*/
                body,
            )
            .unwrap_or(node);
        self.enclosing_function_flags
            .set(saved_enclosing_function_flags);
        Some(updated)
    }

    /// `(tx *forawaitTransformer) transformAsyncGeneratorFunctionParameterList`.
    fn transform_async_generator_function_parameter_list(
        &self,
        ec: &Ec,
        txv: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeList {
        let parameters: Vec<NodeId> = cx.nodes[node]
            .parameters()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        if super::r#async::is_simple_parameter_list(cx, &parameters) {
            let list = cx.nodes[node].parameter_list().cloned();
            return ec_visit_parameters(txv, cx, list).expect("parameter list present");
        }
        // Add fixed parameters to preserve the function's `length` property.
        let mut new_parameters: Vec<NodeId> = Vec::new();
        for parameter in parameters {
            let p = cx.nodes[parameter].as_parameter_declaration();
            if p.initializer.is_some() || p.dot_dot_dot_token.is_some() {
                break;
            }
            let param_name = cx.nodes[parameter].name().expect("parameter has a name");
            let options = AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                ..Default::default()
            };
            let generated_name = ec
                .borrow_mut()
                .factory
                .new_generated_name_for_node_ex(cx.nodes, param_name, &options);
            let new_parameter = ec.borrow_mut().factory.new_parameter_declaration(
                cx.nodes,
                None,
                None,
                Some(generated_name),
                None,
                None,
                None,
            );
            new_parameters.push(new_parameter);
        }
        let mut new_parameters_array = ec.borrow_mut().factory.new_node_list(new_parameters);
        new_parameters_array.loc = cx.nodes[node]
            .parameter_list()
            .map(|l| l.loc)
            .unwrap_or_default();
        new_parameters_array
    }

    /// `(tx *forawaitTransformer) transformAsyncGeneratorFunctionBody`.
    fn transform_async_generator_function_body(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let parameters: Vec<NodeId> = cx.nodes[node]
            .parameters()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        let txv = self.txv(ec);
        let mut inner_parameters: Option<NodeList> = None;
        if !super::r#async::is_simple_parameter_list(cx, &parameters) {
            let list = cx.nodes[node].parameter_list().cloned();
            inner_parameters = ec_visit_parameters(&txv, cx, list);
        }

        let saved_captured_super_properties = self
            .super_access
            .captured_super_properties
            .replace(Some(OrderedSet::new()));
        let saved_has_super_element_access =
            self.super_access.has_super_element_access.replace(false);
        let saved_has_super_property_assignment = self
            .super_access
            .has_super_property_assignment
            .replace(false);
        let saved_super_binding = self.super_access.super_binding.replace(Some({
            let options = AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::OPTIMISTIC | GeneratedIdentifierFlags::FILE_LEVEL,
                ..Default::default()
            };
            ec.borrow_mut()
                .factory
                .new_unique_name_ex(cx.nodes, "_super", &options)
        }));
        let saved_super_index_binding = self.super_access.super_index_binding.replace(Some({
            let options = AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::OPTIMISTIC | GeneratedIdentifierFlags::FILE_LEVEL,
                ..Default::default()
            };
            ec.borrow_mut()
                .factory
                .new_unique_name_ex(cx.nodes, "_superIndex", &options)
        }));

        let body = cx.nodes[node].body().expect("function-like has a body");
        let statements = cx.nodes[body].statement_list().cloned();
        let visited_statements = txv.visit_nodes(cx, statements);
        let multi_line = cx.nodes[body].as_block().multi_line;
        let mut async_body = ec
            .borrow_mut()
            .factory
            .update_block(cx.nodes, body, visited_statements, multi_line)
            .unwrap_or(body);
        let statements = cx.nodes[async_body].statement_list().cloned();
        let merged = ec
            .borrow_mut()
            .end_and_merge_variable_environment_list(cx.nodes, statements);
        let multi_line = cx.nodes[async_body].as_block().multi_line;
        async_body = ec
            .borrow_mut()
            .factory
            .update_block(cx.nodes, async_body, merged, multi_line)
            .unwrap_or(async_body);

        // Substitute super property accesses with _super/_superIndex helpers
        let emit_super_helpers = self
            .super_access
            .captured_super_properties
            .borrow()
            .as_ref()
            .is_some_and(|s| s.size() > 0)
            || self.super_access.has_super_element_access.get();
        if emit_super_helpers {
            if let Some(new_body) = self
                .super_access
                .substitute_super_accesses_in_body(cx, async_body)
            {
                async_body = new_body;
            }
        }

        let inner_params = match inner_parameters {
            Some(params) => params,
            None => ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new()),
        };

        let name = cx.nodes[node].name().map(|name| {
            ec.borrow_mut()
                .factory
                .new_generated_name_for_node(cx.nodes, name)
        });

        let asterisk = ec
            .borrow_mut()
            .factory
            .new_token(cx.nodes, Kind::AsteriskToken);
        let generator_func = ec.borrow_mut().factory.new_function_expression(
            cx.nodes,
            None, /*modifiers*/
            Some(asterisk),
            name,
            None, /*type_parameters*/
            Some(inner_params),
            None, /*type_node*/
            None, /*full_signature*/
            Some(async_body),
        );

        let has_lexical_this = self.for_await_hierarchy_facts.get() & HAS_LEXICAL_THIS != 0;
        let async_generator = ec.borrow_mut().factory.new_async_generator_helper(
            cx.nodes,
            generator_func,
            has_lexical_this,
        );
        let return_statement = ec
            .borrow_mut()
            .factory
            .new_return_statement(cx.nodes, Some(async_generator));

        ec.borrow_mut().start_variable_environment();
        if emit_super_helpers
            && self
                .super_access
                .captured_super_properties
                .borrow()
                .as_ref()
                .is_some_and(|s| s.size() > 0)
        {
            let stmt = self
                .super_access
                .create_super_access_variable_statement(ec, cx);
            ec.borrow().add_initialization_statement(stmt);
        }

        let outer_statements_list = ec.borrow_mut().factory.new_node_list([return_statement]);
        let merged = ec
            .borrow_mut()
            .end_and_merge_variable_environment_list(cx.nodes, Some(outer_statements_list));
        let multi_line = cx.nodes[body].as_block().multi_line;
        let block = ec
            .borrow_mut()
            .factory
            .update_block(cx.nodes, body, merged, multi_line)
            .unwrap_or(body);

        if emit_super_helpers && self.super_access.has_super_element_access.get() {
            if self.super_access.has_super_property_assignment.get() {
                ec.borrow()
                    .add_emit_helper(block, &[advanced_async_super_helper()]);
            } else {
                ec.borrow().add_emit_helper(block, &[async_super_helper()]);
            }
        }

        self.super_access
            .captured_super_properties
            .replace(saved_captured_super_properties);
        self.super_access
            .has_super_element_access
            .set(saved_has_super_element_access);
        self.super_access
            .has_super_property_assignment
            .set(saved_has_super_property_assignment);
        self.super_access.super_binding.set(saved_super_binding);
        self.super_access
            .super_index_binding
            .set(saved_super_index_binding);

        block
    }
}

/// `unwrapInnermostStatementOfLabel` follows LabeledStatement chains to find
/// the innermost statement.
fn unwrap_innermost_statement_of_label(cx: &VisitorCx<'_, '_>, node: NodeId) -> NodeId {
    let mut node = node;
    loop {
        let statement = cx.nodes[node]
            .as_labeled_statement()
            .statement
            .expect("labeled statement has a statement");
        if cx.nodes[statement].kind != Kind::LabeledStatement {
            return statement;
        }
        node = statement;
    }
}

/// `newforawaitTransformer`.
pub(crate) fn new_forawait_transformer<'a>(opts: &TransformOptions<'a>) -> Option<Transformer<'a>> {
    let compiler_options = opts.compiler_options;
    make_transformer(opts, |ec| {
        let state = Rc::new(ForAwaitTransformer {
            super_access: Rc::new(SuperAccessState::default()),
            compiler_options,
            enclosing_function_flags: Cell::new(FunctionFlags::NORMAL),
            for_await_hierarchy_facts: Cell::new(0),
            exported_variable_statement: Cell::new(false),
            fallback_node_visitor: RefCell::new(None),
            no_async_modifier_visitor: RefCell::new(None),
        });
        state.super_access.init_super_access_visitor(&ec);
        {
            let weak = Rc::downgrade(&state);
            let visit: Box<VisitFn<'a>> = Box::new(
                move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    let s = weak
                        .upgrade()
                        .expect("forawaitTransformer dropped during visit");
                    s.fallback_visitor(cx, node)
                },
            );
            *state.fallback_node_visitor.borrow_mut() = Some(ec.borrow().new_node_visitor(visit));
        }
        {
            let visit: Box<VisitFn<'a>> = Box::new(
                |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    if cx.nodes[node].kind == Kind::AsyncKeyword {
                        return None;
                    }
                    Some(node)
                },
            );
            *state.no_async_modifier_visitor.borrow_mut() =
                Some(ec.borrow().new_node_visitor(visit));
        }
        Box::new(
            move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, v, cx, node)
            },
        )
    })
}
