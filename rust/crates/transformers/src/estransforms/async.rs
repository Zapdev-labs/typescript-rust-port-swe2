// Ported from tsc/internal/transformers/estransforms/async.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `newAsyncTransformer` — downlevels `async`/`await` to `__awaiter`
// generators for ES2016 and earlier.
//
// PORT notes:
//   - `asyncTransformer` embeds `transformers.Transformer`; here the state
//     lives in `Rc<AsyncTransformer>` captured by the visit closure, and the
//     running `NodeVisitor` arrives as the first callback argument. See the
//     module-level PORT notes in `mod.rs`.
//   - Go's `tx.visit` and `tx.Visitor()` are distinct: `visit` is a
//     function, `tx.Visitor()` is the visitor object that wraps it. When a
//     nested visitor (asyncBodyVisitor/fallbackNodeVisitor) invokes
//     `tx.visit`, `tx.Visitor()` inside it still means the *main* visitor —
//     not the visitor currently running. `txv` synthesizes an equivalent
//     `NodeVisitor` for the main visit function on demand (a `NodeVisitor`
//     is just a visit-fn wrapper — no state, no hooks — so a fresh one is
//     observably identical), and every `tx.Visitor()` call site uses it.
//   - `EmitContext::visit_parameters`/`visit_function_body` re-enter the
//     visitor and so go through `with_ec_mut` (see `mod.rs`).

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::functionflags::{FunctionFlags, get_function_flags};
use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId, NodeList, SubtreeFacts};
use tsc_collections::{OrderedSet, Set};
use tsc_printer::{
    AutoGenerateOptions, EmitFlags, GeneratedIdentifierFlags, advanced_async_super_helper,
    async_super_helper,
};

use super::utilities::SuperAccessState;
use super::{Ec, ec_visit_function_body, ec_visit_parameters, make_transformer, subtree_facts};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;
use crate::utilities::convert_binding_pattern_to_assignment_pattern;

// `type asyncContextFlags int` — bit flags tracking whether the visitor is
// inside a non-top-level function body (where `await` must be transformed)
// and whether the enclosing function has a lexical `this`.
const ASYNC_CONTEXT_NON_TOP_LEVEL: u32 = 1;
const ASYNC_CONTEXT_HAS_LEXICAL_THIS: u32 = 1 << 1;

/// `type lexicalArgumentsInfo struct` — the synthesized binding that captures
/// a function's `arguments` object so nested arrows keep a lexical reference.
#[derive(Clone, Copy, Default)]
struct LexicalArgumentsInfo {
    binding: Option<NodeId>,
    used: bool,
}

/// `type asyncTransformer struct`.
pub(crate) struct AsyncTransformer<'a> {
    pub super_access: Rc<SuperAccessState<'a>>,

    context_flags: Cell<u32>,

    enclosing_function_parameter_names: RefCell<Option<Set<String>>>,
    lexical_arguments: Cell<LexicalArgumentsInfo>,

    async_body_visitor: RefCell<Option<NodeVisitor<'a>>>,
    fallback_node_visitor: RefCell<Option<NodeVisitor<'a>>>,
}

impl<'a> AsyncTransformer<'a> {
    /// `setContextFlag`.
    fn set_context_flag(&self, flag: u32, val: bool) {
        if val {
            self.context_flags.set(self.context_flags.get() | flag);
        } else {
            self.context_flags.set(self.context_flags.get() & !flag);
        }
    }

    /// `inContext`.
    fn in_context(&self, flags: u32) -> bool {
        self.context_flags.get() & flags != 0
    }

    /// `inTopLevelContext`.
    fn in_top_level_context(&self) -> bool {
        !self.in_context(ASYNC_CONTEXT_NON_TOP_LEVEL)
    }

    /// `inHasLexicalThisContext`.
    fn in_has_lexical_this_context(&self) -> bool {
        self.in_context(ASYNC_CONTEXT_HAS_LEXICAL_THIS)
    }

    /// `doWithContext` — temporarily sets `flags` for the duration of `cb`.
    fn do_with_context(
        self: &Rc<Self>,
        flags: u32,
        cb: impl FnOnce(&Rc<Self>, &mut VisitorCx<'_, '_>, NodeId) -> Option<NodeId>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let flags_to_set = flags & !self.context_flags.get();
        if flags_to_set != 0 {
            self.set_context_flag(flags_to_set, true);
            let result = cb(self, cx, node);
            self.set_context_flag(flags_to_set, false);
            return result;
        }
        cb(self, cx, node)
    }

    /// A `NodeVisitor` equivalent to `tx.Visitor()` (see the module PORT
    /// note) — a fresh visitor wrapping the main `visit` function.
    fn txv(self: &Rc<Self>, ec: &Ec) -> NodeVisitor<'a> {
        let state = self.clone();
        let ec2 = ec.clone();
        ec.borrow().new_node_visitor(Box::new(
            move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec2, _v, cx, node)
            },
        ))
    }

    /// `fallbackVisitor` — the shared body of `visitFallback` and the
    /// non-async fast path of `visit`.
    fn fallback_visitor(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        let has_binding = self.lexical_arguments.get().binding.is_some();
        if self
            .super_access
            .captured_super_properties
            .borrow()
            .is_none()
            && !has_binding
        {
            return Some(node);
        }
        self.super_access.track_super_access(cx, node);
        match cx.nodes[node].kind {
            Kind::FunctionExpression
            | Kind::FunctionDeclaration
            | Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::Constructor => return Some(node),
            Kind::Parameter | Kind::BindingElement | Kind::VariableDeclaration => {
                // fall through to visitEachChild
            }
            Kind::Identifier => {
                let mut info = self.lexical_arguments.get();
                if let Some(binding) = info.binding {
                    if &*cx.nodes[node].text(cx.nodes) == "arguments"
                        && !ast::is_identifier_name(node, cx.nodes)
                        && !ast::is_label_name(node, cx.nodes)
                    {
                        info.used = true;
                        self.lexical_arguments.set(info);
                        return Some(binding);
                    }
                }
            }
            _ => {}
        }
        // `tx.fallbackNodeVisitor.VisitEachChild(node)`
        self.fallback_node_visitor
            .borrow()
            .as_ref()
            .expect("fallback visitor not initialized")
            .visit_each_child(cx, node)
            .or(Some(node))
    }

    /// `(tx *asyncTransformer) visitFallback` — the `fallbackNodeVisitor`
    /// callback.
    fn visit_fallback(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        self.fallback_visitor(cx, node)
    }

    /// `(tx *asyncTransformer) visit` — the main visit callback.
    pub(crate) fn visit(
        self: &Rc<Self>,
        ec: &Ec,
        _v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // `defer` — clear `hasLexicalThis` for the duration of this call when
        // the node opts out of lexical `this`.
        if ec.borrow().emit_flags(node) & EmitFlags::NO_LEXICAL_THIS != EmitFlags::NONE
            && self.in_has_lexical_this_context()
        {
            self.set_context_flag(ASYNC_CONTEXT_HAS_LEXICAL_THIS, false);
            let result = self.visit_inner(ec, cx, node);
            self.set_context_flag(ASYNC_CONTEXT_HAS_LEXICAL_THIS, true);
            return result;
        }
        self.visit_inner(ec, cx, node)
    }

    fn visit_inner(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if subtree_facts(cx, node)
            & (SubtreeFacts::CONTAINS_ANY_AWAIT | SubtreeFacts::CONTAINS_AWAIT)
            == SubtreeFacts::NONE
        {
            return self.fallback_visitor(cx, node);
        }
        self.super_access.track_super_access(cx, node);
        match cx.nodes[node].kind {
            // ES2017 async modifier should be elided for targets < ES2017
            Kind::AsyncKeyword => None,
            Kind::SourceFile => Some(self.visit_source_file(ec, cx, node)),
            Kind::AwaitExpression => Some(self.visit_await_expression(ec, cx, node)),
            Kind::MethodDeclaration => self.do_with_context(
                ASYNC_CONTEXT_NON_TOP_LEVEL | ASYNC_CONTEXT_HAS_LEXICAL_THIS,
                |s, c, n| s.visit_method_declaration(ec, c, n),
                cx,
                node,
            ),
            Kind::FunctionDeclaration => self.do_with_context(
                ASYNC_CONTEXT_NON_TOP_LEVEL | ASYNC_CONTEXT_HAS_LEXICAL_THIS,
                |s, c, n| s.visit_function_declaration(ec, c, n),
                cx,
                node,
            ),
            Kind::FunctionExpression => self.do_with_context(
                ASYNC_CONTEXT_NON_TOP_LEVEL | ASYNC_CONTEXT_HAS_LEXICAL_THIS,
                |s, c, n| s.visit_function_expression(ec, c, n),
                cx,
                node,
            ),
            Kind::ArrowFunction => self.do_with_context(
                ASYNC_CONTEXT_NON_TOP_LEVEL,
                |s, c, n| s.visit_arrow_function(ec, c, n),
                cx,
                node,
            ),
            Kind::GetAccessor => self.do_with_context(
                ASYNC_CONTEXT_NON_TOP_LEVEL | ASYNC_CONTEXT_HAS_LEXICAL_THIS,
                |s, c, n| s.visit_get_accessor_declaration(ec, c, n),
                cx,
                node,
            ),
            Kind::SetAccessor => self.do_with_context(
                ASYNC_CONTEXT_NON_TOP_LEVEL | ASYNC_CONTEXT_HAS_LEXICAL_THIS,
                |s, c, n| s.visit_set_accessor_declaration(ec, c, n),
                cx,
                node,
            ),
            Kind::Constructor => self.do_with_context(
                ASYNC_CONTEXT_NON_TOP_LEVEL | ASYNC_CONTEXT_HAS_LEXICAL_THIS,
                |s, c, n| s.visit_constructor_declaration(ec, c, n),
                cx,
                node,
            ),
            Kind::ClassDeclaration | Kind::ClassExpression => self.do_with_context(
                ASYNC_CONTEXT_NON_TOP_LEVEL | ASYNC_CONTEXT_HAS_LEXICAL_THIS,
                |s, c, n| s.visit_default(ec, c, n),
                cx,
                node,
            ),
            // `tx.Visitor().VisitEachChild(node)`
            _ => self.txv(ec).visit_each_child(cx, node).or(Some(node)),
        }
    }

    /// `(tx *asyncTransformer) visitDefault`.
    fn visit_default(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        self.txv(ec).visit_each_child(cx, node).or(Some(node))
    }

    /// `(tx *asyncTransformer) visitAsyncBodyNode` — the `asyncBodyVisitor`
    /// callback.
    fn visit_async_body_node(
        self: &Rc<Self>,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if is_node_with_possible_hoisted_declaration(&cx.nodes[node]) {
            match cx.nodes[node].kind {
                Kind::VariableStatement => {
                    return self.visit_variable_statement_in_async_body(ec, cx, node);
                }
                Kind::ForStatement => {
                    return Some(self.visit_for_statement_in_async_body(ec, cx, node));
                }
                Kind::ForInStatement => {
                    return Some(self.visit_for_in_statement_in_async_body(ec, cx, node));
                }
                Kind::ForOfStatement => {
                    return Some(self.visit_for_of_statement_in_async_body(ec, cx, node));
                }
                Kind::CatchClause => {
                    return Some(self.visit_catch_clause_in_async_body(v, cx, node));
                }
                Kind::Block
                | Kind::SwitchStatement
                | Kind::CaseBlock
                | Kind::CaseClause
                | Kind::DefaultClause
                | Kind::TryStatement
                | Kind::DoStatement
                | Kind::WhileStatement
                | Kind::IfStatement
                | Kind::WithStatement
                | Kind::LabeledStatement => {
                    // `tx.asyncBodyVisitor.VisitEachChild(node)`
                    return self
                        .async_body_visitor
                        .borrow()
                        .as_ref()
                        .expect("async body visitor not initialized")
                        .visit_each_child(cx, node)
                        .or(Some(node));
                }
                _ => {}
            }
        }
        // `tx.visit(node)` — the main visit function.
        self.visit(ec, v, cx, node)
    }

    /// `(tx *asyncTransformer) visitCatchClauseInAsyncBody`.
    fn visit_catch_clause_in_async_body(
        &self,
        _v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let mut catch_clause_names: Set<String> = Set::new();
        if let Some(variable_declaration) = cx.nodes[node].as_catch_clause().variable_declaration {
            self.record_declaration_name(cx, variable_declaration, &mut catch_clause_names);
        }

        // names declared in a catch variable are block scoped
        let mut catch_clause_unshadowed_names: Option<Set<String>> = None;
        for escaped_name in catch_clause_names.keys().iter() {
            let collides = self
                .enclosing_function_parameter_names
                .borrow()
                .as_ref()
                .is_some_and(|names| names.has(escaped_name.as_str()));
            if collides {
                let unshadowed = catch_clause_unshadowed_names.get_or_insert_with(|| {
                    self.enclosing_function_parameter_names
                        .borrow()
                        .as_ref()
                        .expect("enclosing names present")
                        .clone()
                });
                unshadowed.delete(escaped_name.as_str());
            }
        }

        let mut visitor = || {
            self.async_body_visitor
                .borrow()
                .as_ref()
                .expect("async body visitor not initialized")
                .visit_each_child(cx, node)
                .unwrap_or(node)
        };

        if let Some(unshadowed) = catch_clause_unshadowed_names {
            let saved = self
                .enclosing_function_parameter_names
                .replace(Some(unshadowed));
            let result = visitor();
            self.enclosing_function_parameter_names.replace(saved);
            return result;
        }
        visitor()
    }

    /// `(tx *asyncTransformer) visitVariableStatementInAsyncBody`.
    fn visit_variable_statement_in_async_body(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let decl_list = cx.nodes[node].as_variable_statement().declaration_list;
        if self.is_variable_declaration_list_with_colliding_name(cx, decl_list) {
            let expression = self.visit_variable_declaration_list_with_colliding_names(
                ec,
                cx,
                decl_list.unwrap(),
                false,
            );
            if let Some(expression) = expression {
                return Some(
                    ec.borrow_mut()
                        .factory
                        .new_expression_statement(cx.nodes, Some(expression)),
                );
            }
            return None;
        }
        // `tx.Visitor().VisitEachChild(node)`
        self.txv(ec).visit_each_child(cx, node).or(Some(node))
    }

    /// `(tx *asyncTransformer) visitForInStatementInAsyncBody`.
    fn visit_for_in_statement_in_async_body(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let d = cx.nodes[node].as_for_in_or_of_statement();
        let initializer = d.initializer;
        let expression = d.expression;
        let statement = d.statement;
        let visited_initializer =
            if self.is_variable_declaration_list_with_colliding_name(cx, initializer) {
                self.visit_variable_declaration_list_with_colliding_names(
                    ec,
                    cx,
                    initializer.unwrap(),
                    true,
                )
            } else {
                // `tx.Visitor().VisitNode`
                self.txv(ec).visit_node(cx, initializer)
            };

        let visited_expression = self.txv(ec).visit_node(cx, expression);
        let visited_statement = self
            .async_body_visitor
            .borrow()
            .as_ref()
            .expect("async body visitor not initialized")
            .visit_embedded_statement(cx, statement);
        ec.borrow_mut()
            .factory
            .update_for_in_or_of_statement(
                cx.nodes,
                node,
                None, /*await_modifier*/
                visited_initializer,
                visited_expression,
                visited_statement,
            )
            .unwrap_or(node)
    }

    /// `(tx *asyncTransformer) visitForOfStatementInAsyncBody`.
    fn visit_for_of_statement_in_async_body(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let d = cx.nodes[node].as_for_in_or_of_statement();
        let await_modifier = d.await_modifier;
        let initializer = d.initializer;
        let expression = d.expression;
        let statement = d.statement;
        let visited_initializer =
            if self.is_variable_declaration_list_with_colliding_name(cx, initializer) {
                self.visit_variable_declaration_list_with_colliding_names(
                    ec,
                    cx,
                    initializer.unwrap(),
                    true,
                )
            } else {
                self.txv(ec).visit_node(cx, initializer)
            };

        let txv = self.txv(ec);
        let visited_await = txv.visit_node(cx, await_modifier);
        let visited_expression = txv.visit_node(cx, expression);
        let visited_statement = self
            .async_body_visitor
            .borrow()
            .as_ref()
            .expect("async body visitor not initialized")
            .visit_embedded_statement(cx, statement);
        ec.borrow_mut()
            .factory
            .update_for_in_or_of_statement(
                cx.nodes,
                node,
                visited_await,
                visited_initializer,
                visited_expression,
                visited_statement,
            )
            .unwrap_or(node)
    }

    /// `(tx *asyncTransformer) visitForStatementInAsyncBody`.
    fn visit_for_statement_in_async_body(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let d = cx.nodes[node].as_for_statement();
        let initializer = d.initializer;
        let condition = d.condition;
        let incrementor = d.incrementor;
        let statement = d.iteration_statement_base.statement;
        let txv = self.txv(ec);
        let visited_initializer =
            if self.is_variable_declaration_list_with_colliding_name(cx, initializer) {
                self.visit_variable_declaration_list_with_colliding_names(
                    ec,
                    cx,
                    initializer.unwrap(),
                    false,
                )
            } else {
                txv.visit_node(cx, initializer)
            };

        let visited_condition = txv.visit_node(cx, condition);
        let visited_incrementor = txv.visit_node(cx, incrementor);
        let visited_statement = self
            .async_body_visitor
            .borrow()
            .as_ref()
            .expect("async body visitor not initialized")
            .visit_embedded_statement(cx, statement);
        ec.borrow_mut()
            .factory
            .update_for_statement(
                cx.nodes,
                node,
                visited_initializer,
                visited_condition,
                visited_incrementor,
                visited_statement,
            )
            .unwrap_or(node)
    }

    /// `(tx *asyncTransformer) visitAwaitExpression`.
    fn visit_await_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // do not downlevel a top-level await as it is module syntax...
        if self.in_top_level_context() {
            return self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
        }
        let expression = cx.nodes[node].as_await_expression().expression;
        let visited = self.txv(ec).visit_node(cx, expression);
        let yield_expr = ec
            .borrow_mut()
            .factory
            .new_yield_expression(cx.nodes, None /*asterisk_token*/, visited);
        cx.nodes[yield_expr].loc = cx.nodes[node].loc;
        ec.borrow().set_original(yield_expr, node);
        yield_expr
    }

    /// `(tx *asyncTransformer) visitConstructorDeclaration`.
    fn visit_constructor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_lexical_arguments = self.lexical_arguments.replace(LexicalArgumentsInfo {
            binding: None,
            used: false,
        });
        let txv = self.txv(ec);
        let modifiers = cx.nodes[node].modifiers().cloned();
        let visited_modifiers = txv.visit_modifiers(cx, modifiers);
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_parameters = ec_visit_parameters(&txv, cx, parameters);
        let body = self.transform_method_body(ec, cx, node);
        let updated = ec
            .borrow_mut()
            .factory
            .update_constructor_declaration(
                cx.nodes,
                node,
                visited_modifiers,
                None, /*type_parameters*/
                visited_parameters,
                None, /*type_node*/
                None, /*full_signature*/
                body,
            )
            .unwrap_or(node);
        self.lexical_arguments.set(saved_lexical_arguments);
        Some(updated)
    }

    /// `(tx *asyncTransformer) visitMethodDeclaration`.
    fn visit_method_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let function_flags = get_function_flags(Some(&cx.nodes[node]));
        let saved_lexical_arguments = self.lexical_arguments.replace(LexicalArgumentsInfo {
            binding: None,
            used: false,
        });
        let txv = self.txv(ec);

        let (parameters, body);
        if function_flags & FunctionFlags::ASYNC != FunctionFlags::NONE {
            let params = self.transform_async_function_parameter_list(ec, &txv, cx, node);
            parameters = Some(params.clone());
            body = Some(self.transform_async_function_body(ec, cx, node, Some(params)));
        } else {
            let params = cx.nodes[node].parameter_list().cloned();
            parameters = ec_visit_parameters(&txv, cx, params);
            body = self.transform_method_body(ec, cx, node);
        }

        let decl = cx.nodes[node].as_method_declaration();
        let asterisk_token = decl.function_like_with_body_base.body_base.asterisk_token;
        let name = cx.nodes[node].name();
        let modifiers = cx.nodes[node].modifiers().cloned();
        let visited_modifiers = txv.visit_modifiers(cx, modifiers);
        let updated = ec
            .borrow_mut()
            .factory
            .update_method_declaration(
                cx.nodes,
                node,
                visited_modifiers,
                asterisk_token,
                name,
                None, /*postfix_token*/
                None, /*type_parameters*/
                parameters,
                None, /*type_node*/
                None, /*full_signature*/
                body,
            )
            .unwrap_or(node);
        self.lexical_arguments.set(saved_lexical_arguments);
        Some(updated)
    }

    /// `(tx *asyncTransformer) visitGetAccessorDeclaration`.
    fn visit_get_accessor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_lexical_arguments = self.lexical_arguments.replace(LexicalArgumentsInfo {
            binding: None,
            used: false,
        });
        let txv = self.txv(ec);
        let modifiers = cx.nodes[node].modifiers().cloned();
        let visited_modifiers = txv.visit_modifiers(cx, modifiers);
        let name = cx.nodes[node].name();
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_parameters = ec_visit_parameters(&txv, cx, parameters);
        let body = self.transform_method_body(ec, cx, node);
        let updated = ec
            .borrow_mut()
            .factory
            .update_get_accessor_declaration(
                cx.nodes,
                node,
                visited_modifiers,
                name,
                None, /*type_parameters*/
                visited_parameters,
                None, /*type_node*/
                None, /*full_signature*/
                body,
            )
            .unwrap_or(node);
        self.lexical_arguments.set(saved_lexical_arguments);
        Some(updated)
    }

    /// `(tx *asyncTransformer) visitSetAccessorDeclaration`.
    fn visit_set_accessor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let saved_lexical_arguments = self.lexical_arguments.replace(LexicalArgumentsInfo {
            binding: None,
            used: false,
        });
        let txv = self.txv(ec);
        let modifiers = cx.nodes[node].modifiers().cloned();
        let visited_modifiers = txv.visit_modifiers(cx, modifiers);
        let name = cx.nodes[node].name();
        let parameters = cx.nodes[node].parameter_list().cloned();
        let visited_parameters = ec_visit_parameters(&txv, cx, parameters);
        let body = self.transform_method_body(ec, cx, node);
        let updated = ec
            .borrow_mut()
            .factory
            .update_set_accessor_declaration(
                cx.nodes,
                node,
                visited_modifiers,
                name,
                None, /*type_parameters*/
                visited_parameters,
                None, /*type_node*/
                None, /*full_signature*/
                body,
            )
            .unwrap_or(node);
        self.lexical_arguments.set(saved_lexical_arguments);
        Some(updated)
    }

    /// `(tx *asyncTransformer) visitFunctionDeclaration`.
    fn visit_function_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let function_flags = get_function_flags(Some(&cx.nodes[node]));
        let saved_lexical_arguments = self.lexical_arguments.replace(LexicalArgumentsInfo {
            binding: None,
            used: false,
        });
        let txv = self.txv(ec);

        let (parameters, body);
        if function_flags & FunctionFlags::ASYNC != FunctionFlags::NONE {
            let params = self.transform_async_function_parameter_list(ec, &txv, cx, node);
            parameters = Some(params.clone());
            body = Some(self.transform_async_function_body(ec, cx, node, Some(params)));
        } else {
            let params = cx.nodes[node].parameter_list().cloned();
            parameters = ec_visit_parameters(&txv, cx, params);
            let decl_body = cx.nodes[node].body();
            body = ec_visit_function_body(&txv, cx, decl_body);
        }

        let decl = cx.nodes[node].as_function_declaration();
        let asterisk_token = decl.function_like_with_body_base.body_base.asterisk_token;
        let name = cx.nodes[node].name();
        let modifiers = cx.nodes[node].modifiers().cloned();
        let visited_modifiers = txv.visit_modifiers(cx, modifiers);
        let visited_name = txv.visit_node(cx, name);
        let updated = ec
            .borrow_mut()
            .factory
            .update_function_declaration(
                cx.nodes,
                node,
                visited_modifiers,
                asterisk_token,
                visited_name,
                None, /*type_parameters*/
                parameters,
                None, /*type_node*/
                None, /*full_signature*/
                body,
            )
            .unwrap_or(node);
        self.lexical_arguments.set(saved_lexical_arguments);
        Some(updated)
    }

    /// `(tx *asyncTransformer) visitFunctionExpression`.
    fn visit_function_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let function_flags = get_function_flags(Some(&cx.nodes[node]));
        let saved_lexical_arguments = self.lexical_arguments.replace(LexicalArgumentsInfo {
            binding: None,
            used: false,
        });
        let txv = self.txv(ec);

        let (parameters, body);
        if function_flags & FunctionFlags::ASYNC != FunctionFlags::NONE {
            let params = self.transform_async_function_parameter_list(ec, &txv, cx, node);
            parameters = Some(params.clone());
            body = Some(self.transform_async_function_body(ec, cx, node, Some(params)));
        } else {
            let params = cx.nodes[node].parameter_list().cloned();
            parameters = ec_visit_parameters(&txv, cx, params);
            let decl_body = cx.nodes[node].body();
            body = ec_visit_function_body(&txv, cx, decl_body);
        }

        let decl = cx.nodes[node].as_function_expression();
        let asterisk_token = decl.function_like_with_body_base.body_base.asterisk_token;
        let name = cx.nodes[node].name();
        let modifiers = cx.nodes[node].modifiers().cloned();
        let visited_modifiers = txv.visit_modifiers(cx, modifiers);
        let visited_name = txv.visit_node(cx, name);
        let updated = ec
            .borrow_mut()
            .factory
            .update_function_expression(
                cx.nodes,
                node,
                visited_modifiers,
                asterisk_token,
                visited_name,
                None, /*type_parameters*/
                parameters,
                None, /*type_node*/
                None, /*full_signature*/
                body,
            )
            .unwrap_or(node);
        self.lexical_arguments.set(saved_lexical_arguments);
        Some(updated)
    }

    /// `(tx *asyncTransformer) visitArrowFunction`.
    fn visit_arrow_function(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // `arguments` in class static blocks is always an error, but we preserve Strada's emit
        // behavior for baseline compatibility. In Strada, checker-based `isArgumentsLocalBinding`
        // returns false for `arguments` in static blocks (since the binding doesn't exist due to
        // the error), so the async transform leaves them untouched.
        let no_lexical_arguments =
            ec.borrow().emit_flags(node) & EmitFlags::NO_LEXICAL_ARGUMENTS != EmitFlags::NONE;
        let saved_lexical_arguments = if no_lexical_arguments {
            Some(self.lexical_arguments.replace(LexicalArgumentsInfo {
                binding: None,
                used: false,
            }))
        } else {
            None
        };

        let result = self.visit_arrow_function_inner(ec, cx, node);

        if let Some(saved) = saved_lexical_arguments {
            self.lexical_arguments.set(saved);
        }
        Some(result)
    }

    fn visit_arrow_function_inner(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let function_flags = get_function_flags(Some(&cx.nodes[node]));
        let txv = self.txv(ec);

        let (parameters, body);
        if function_flags & FunctionFlags::ASYNC != FunctionFlags::NONE {
            let params = self.transform_async_function_parameter_list(ec, &txv, cx, node);
            parameters = Some(params.clone());
            body = Some(self.transform_async_function_body(ec, cx, node, Some(params)));
        } else {
            let params = cx.nodes[node].parameter_list().cloned();
            parameters = ec_visit_parameters(&txv, cx, params);
            let decl_body = cx.nodes[node].body();
            body = ec_visit_function_body(&txv, cx, decl_body);
        }

        let decl = cx.nodes[node].as_arrow_function();
        let equals_greater_than_token = decl.equals_greater_than_token;
        let modifiers = cx.nodes[node].modifiers().cloned();
        let visited_modifiers = txv.visit_modifiers(cx, modifiers);
        ec.borrow_mut()
            .factory
            .update_arrow_function(
                cx.nodes,
                node,
                visited_modifiers,
                None, /*type_parameters*/
                parameters,
                None, /*type_node*/
                None, /*full_signature*/
                equals_greater_than_token,
                body,
            )
            .unwrap_or(node)
    }

    /// `(tx *asyncTransformer) visitSourceFile`.
    fn visit_source_file(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if cx.nodes[node].as_source_file().is_declaration_file {
            return node;
        }

        self.set_context_flag(ASYNC_CONTEXT_NON_TOP_LEVEL, false);
        self.set_context_flag(ASYNC_CONTEXT_HAS_LEXICAL_THIS, false);
        let visited = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
        let helpers = ec.borrow_mut().read_emit_helpers();
        ec.borrow().add_emit_helper(visited, &helpers);
        visited
    }

    /// `(tx *asyncTransformer) recordDeclarationName`.
    fn record_declaration_name(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        names: &mut Set<String>,
    ) {
        let Some(name) = cx.nodes[node].name() else {
            return;
        };
        if ast::is_identifier(&cx.nodes[name]) {
            names.add(cx.nodes[name].text(cx.nodes).into_owned());
        } else if ast::is_binding_pattern(&cx.nodes[name]) {
            if let Some(elements) = &cx.nodes[name].as_binding_pattern().elements {
                let elements = elements.nodes.clone();
                for element in elements {
                    if !ast::is_omitted_expression(&cx.nodes[element]) {
                        self.record_declaration_name(cx, element, names);
                    }
                }
            }
        }
    }

    /// `(tx *asyncTransformer) isVariableDeclarationListWithCollidingName`.
    fn is_variable_declaration_list_with_colliding_name(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> bool {
        node.is_some_and(|node| {
            ast::is_variable_declaration_list(&cx.nodes[node])
                && cx.nodes[node].flags & ast::NodeFlags::BLOCK_SCOPED == ast::NodeFlags::NONE
                && {
                    let decls = cx.nodes[node]
                        .as_variable_declaration_list()
                        .declarations
                        .clone();
                    decls.as_ref().is_some_and(|decls| {
                        decls
                            .nodes
                            .iter()
                            .any(|&decl| self.collides_with_parameter_name(cx, decl))
                    })
                }
        })
    }

    /// `(tx *asyncTransformer) visitVariableDeclarationListWithCollidingNames`.
    fn visit_variable_declaration_list_with_colliding_names(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        has_receiver: bool,
    ) -> Option<NodeId> {
        self.hoist_variable_declaration_list(ec, cx, node);

        let mut variables: Vec<NodeId> = Vec::new();
        if let Some(decls) = &cx.nodes[node].as_variable_declaration_list().declarations {
            for &decl in &decls.nodes {
                if cx.nodes[decl]
                    .as_variable_declaration()
                    .initializer
                    .is_some()
                {
                    variables.push(decl);
                }
            }
        }

        if variables.is_empty() {
            if has_receiver {
                let name = cx.nodes[node]
                    .as_variable_declaration_list()
                    .declarations
                    .as_ref()
                    .expect("non-empty declarations")
                    .nodes[0];
                let name = cx.nodes[name].name().expect("declaration has a name");
                let target = if ast::is_binding_pattern(&cx.nodes[name]) {
                    {
                        let mut e = ec.borrow_mut();
                        convert_binding_pattern_to_assignment_pattern(&mut e, cx.nodes, name)
                    }
                } else {
                    name
                };
                // `tx.Visitor().VisitNode(target)`
                return self.txv(ec).visit_node(cx, Some(target));
            }
            return None;
        }

        let mut expressions: Vec<NodeId> = Vec::new();
        for variable in variables {
            expressions.push(self.transform_initialized_variable(ec, cx, variable));
        }
        ec.borrow_mut()
            .factory
            .inline_expressions(cx.nodes, &expressions)
    }

    /// `(tx *asyncTransformer) hoistVariableDeclarationList`.
    fn hoist_variable_declaration_list(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) {
        if let Some(decls) = &cx.nodes[node].as_variable_declaration_list().declarations {
            let decls = decls.nodes.clone();
            for decl in decls {
                self.hoist_variable(ec, cx, decl);
            }
        }
    }

    /// `(tx *asyncTransformer) hoistVariable`.
    fn hoist_variable(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) {
        let Some(name) = cx.nodes[node].name() else {
            return;
        };
        if ast::is_identifier(&cx.nodes[name]) {
            ec.borrow_mut().add_variable_declaration(cx.nodes, name);
        } else if ast::is_binding_pattern(&cx.nodes[name]) {
            if let Some(elements) = &cx.nodes[name].as_binding_pattern().elements {
                let elements = elements.nodes.clone();
                for element in elements {
                    if !ast::is_omitted_expression(&cx.nodes[element]) {
                        self.hoist_variable(ec, cx, element);
                    }
                }
            }
        }
    }

    /// `(tx *asyncTransformer) transformInitializedVariable`.
    fn transform_initialized_variable(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let name = cx.nodes[node].name().expect("declaration has a name");
        let initializer = cx.nodes[node].as_variable_declaration().initializer;
        let target = if ast::is_binding_pattern(&cx.nodes[name]) {
            {
                let mut e = ec.borrow_mut();
                convert_binding_pattern_to_assignment_pattern(&mut e, cx.nodes, name)
            }
        } else {
            name
        };
        let converted = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            target,
            initializer.expect("initialized variable"),
        );
        ec.borrow()
            .set_source_map_range(converted, cx.nodes[node].loc);
        // `tx.Visitor().VisitNode(converted)`
        self.txv(ec)
            .visit_node(cx, Some(converted))
            .unwrap_or(converted)
    }

    /// `(tx *asyncTransformer) collidesWithParameterName`.
    fn collides_with_parameter_name(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> bool {
        let Some(name) = cx.nodes[node].name() else {
            return false;
        };
        if ast::is_identifier(&cx.nodes[name]) {
            let text = cx.nodes[name].text(cx.nodes).into_owned();
            return self
                .enclosing_function_parameter_names
                .borrow()
                .as_ref()
                .is_some_and(|names| names.has(text.as_str()));
        }
        if ast::is_binding_pattern(&cx.nodes[name]) {
            if let Some(elements) = &cx.nodes[name].as_binding_pattern().elements {
                let elements = elements.nodes.clone();
                for element in elements {
                    if !ast::is_omitted_expression(&cx.nodes[element])
                        && self.collides_with_parameter_name(cx, element)
                    {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// `(tx *asyncTransformer) transformMethodBody`.
    fn transform_method_body(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
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

        ec.borrow_mut().start_variable_environment();
        let body = cx.nodes[node].body();
        let txv = self.txv(ec);
        let updated = ec_visit_function_body(&txv, cx, body);

        // Minor optimization, emit `_super` helper to capture `super` access in an arrow.
        let emit_super_helpers = (self
            .super_access
            .captured_super_properties
            .borrow()
            .as_ref()
            .is_some_and(|s| s.size() > 0)
            || self.super_access.has_super_element_access.get())
            && {
                let original = self.get_original_if_function_like(ec, cx, node);
                (get_function_flags(Some(&cx.nodes[original])) & FunctionFlags::ASYNC_GENERATOR)
                    != FunctionFlags::ASYNC_GENERATOR
            };

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

        let mut updated = updated.expect("function body present");
        let statements = cx.nodes[updated].statement_list().cloned();
        let merged_statements = ec
            .borrow_mut()
            .end_and_merge_variable_environment_list(cx.nodes, statements);
        if emit_super_helpers
            && self.super_access.has_super_element_access.get()
            && !cx.nodes[updated].as_block().multi_line
        {
            let new_block = ec
                .borrow_mut()
                .factory
                .new_block(cx.nodes, merged_statements, true);
            cx.nodes[new_block].loc = cx.nodes[updated].loc;
            updated = new_block;
        } else {
            let multi_line = cx.nodes[updated].as_block().multi_line;
            updated = ec
                .borrow_mut()
                .factory
                .update_block(cx.nodes, updated, merged_statements, multi_line)
                .unwrap_or(updated);
        }

        if emit_super_helpers && self.super_access.has_super_element_access.get() {
            if self.super_access.has_super_property_assignment.get() {
                ec.borrow()
                    .add_emit_helper(updated, &[advanced_async_super_helper()]);
            } else {
                ec.borrow()
                    .add_emit_helper(updated, &[async_super_helper()]);
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
        Some(updated)
    }

    /// `(tx *asyncTransformer) createCaptureArgumentsStatement`.
    fn create_capture_arguments_statement(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>) -> NodeId {
        let arguments_ident = ec
            .borrow_mut()
            .factory
            .new_identifier(cx.nodes, "arguments");
        let variable = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            self.lexical_arguments.get().binding,
            None,
            None,
            Some(arguments_ident),
        );
        let decl_list_nodes = ec.borrow_mut().factory.new_node_list([variable]);
        let decl_list = ec.borrow_mut().factory.new_variable_declaration_list(
            cx.nodes,
            Some(decl_list_nodes),
            ast::NodeFlags::NONE,
        );
        let statement =
            ec.borrow_mut()
                .factory
                .new_variable_statement(cx.nodes, None, Some(decl_list));
        ec.borrow().add_emit_flags(
            statement,
            EmitFlags::START_ON_NEW_LINE | EmitFlags::CUSTOM_PROLOGUE,
        );
        statement
    }

    /// `(tx *asyncTransformer) transformAsyncFunctionParameterList`.
    fn transform_async_function_parameter_list(
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
        if is_simple_parameter_list(cx, &parameters) {
            let list = cx.nodes[node].parameter_list().cloned();
            return ec_visit_parameters(txv, cx, list).expect("parameter list present");
        }

        let is_arrow = cx.nodes[node].kind == Kind::ArrowFunction;
        let mut new_parameters: Vec<NodeId> = Vec::new();
        for parameter in parameters {
            let p = cx.nodes[parameter].as_parameter_declaration();
            let initializer = p.initializer;
            let dot_dot_dot_token = p.dot_dot_dot_token;
            if initializer.is_some() || dot_dot_dot_token.is_some() {
                // for an arrow function, capture the remaining arguments in a rest parameter.
                // for any other function/method this isn't necessary as we can just use `arguments`.
                if is_arrow {
                    let options = AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                        ..Default::default()
                    };
                    let args_name = ec
                        .borrow_mut()
                        .factory
                        .new_unique_name_ex(cx.nodes, "args", &options);
                    let dot_dot_dot = ec
                        .borrow_mut()
                        .factory
                        .new_token(cx.nodes, Kind::DotDotDotToken);
                    let rest_parameter = ec.borrow_mut().factory.new_parameter_declaration(
                        cx.nodes,
                        None,
                        Some(dot_dot_dot),
                        Some(args_name),
                        None,
                        None,
                        None,
                    );
                    new_parameters.push(rest_parameter);
                }
                break;
            }
            // for arrow functions we capture fixed parameters to forward to `__awaiter`. For all other functions
            // we add fixed parameters to preserve the function's `length` property.
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

    /// `(tx *asyncTransformer) transformAsyncFunctionBody`.
    fn transform_async_function_body(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        outer_parameters: Option<NodeList>,
    ) -> NodeId {
        let is_arrow = cx.nodes[node].kind == Kind::ArrowFunction;
        let saved_captured_super_properties;
        let saved_has_super_element_access;
        let saved_has_super_property_assignment;
        let saved_super_binding;
        let saved_super_index_binding;
        if !is_arrow {
            saved_captured_super_properties = Some(
                self.super_access
                    .captured_super_properties
                    .replace(Some(OrderedSet::new())),
            );
            saved_has_super_element_access =
                Some(self.super_access.has_super_element_access.replace(false));
            saved_has_super_property_assignment = Some(
                self.super_access
                    .has_super_property_assignment
                    .replace(false),
            );
            let options = AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::OPTIMISTIC | GeneratedIdentifierFlags::FILE_LEVEL,
                ..Default::default()
            };
            let name = ec
                .borrow_mut()
                .factory
                .new_unique_name_ex(cx.nodes, "_super", &options);
            saved_super_binding = Some(self.super_access.super_binding.replace(Some(name)));
            let options = AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::OPTIMISTIC | GeneratedIdentifierFlags::FILE_LEVEL,
                ..Default::default()
            };
            let name =
                ec.borrow_mut()
                    .factory
                    .new_unique_name_ex(cx.nodes, "_superIndex", &options);
            saved_super_index_binding =
                Some(self.super_access.super_index_binding.replace(Some(name)));
        } else {
            saved_captured_super_properties = None;
            saved_has_super_element_access = None;
            saved_has_super_property_assignment = None;
            saved_super_binding = None;
            saved_super_index_binding = None;
        }

        let parameters: Vec<NodeId> = cx.nodes[node]
            .parameters()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        let mut inner_parameters: Option<NodeList> = None;
        if !is_simple_parameter_list(cx, &parameters) {
            let list = cx.nodes[node].parameter_list().cloned();
            let txv = self.txv(ec);
            inner_parameters = ec_visit_parameters(&txv, cx, list);
        }

        let saved_lexical_arguments = self.lexical_arguments.get();
        let capture_lexical_arguments = self.lexical_arguments.get().binding.is_none();
        if capture_lexical_arguments {
            let binding = ec
                .borrow_mut()
                .factory
                .new_unique_name(cx.nodes, "arguments");
            self.lexical_arguments.set(LexicalArgumentsInfo {
                binding: Some(binding),
                used: false,
            });
        }

        let mut arguments_expression: Option<NodeId> = None;
        if inner_parameters.is_some() {
            if is_arrow {
                // `node` does not have a simple parameter list, so `outerParameters` refers to placeholders that are
                // forwarded to `innerParameters`, matching how they are introduced in `transformAsyncFunctionParameterList`.
                let mut parameter_bindings: Vec<NodeId> = Vec::new();
                let outer_len = outer_parameters
                    .as_ref()
                    .map(|l| l.nodes.len())
                    .unwrap_or(0);
                for (i, &param) in parameters.iter().enumerate() {
                    if i >= outer_len {
                        break;
                    }
                    let (original_initializer, original_dot_dot_dot) = {
                        let original = cx.nodes[param].as_parameter_declaration();
                        (original.initializer, original.dot_dot_dot_token)
                    };
                    let outer_parameter =
                        cx.nodes[outer_parameters.as_ref().unwrap().nodes[i]].name();
                    if original_initializer.is_some() || original_dot_dot_dot.is_some() {
                        let spread = ec
                            .borrow_mut()
                            .factory
                            .new_spread_element(cx.nodes, outer_parameter);
                        parameter_bindings.push(spread);
                        break;
                    }
                    parameter_bindings.push(outer_parameter.expect("outer parameter has a name"));
                }
                let list = ec.borrow_mut().factory.new_node_list(parameter_bindings);
                arguments_expression = Some(ec.borrow_mut().factory.new_array_literal_expression(
                    cx.nodes,
                    Some(list),
                    false,
                ));
            } else {
                arguments_expression = Some(
                    ec.borrow_mut()
                        .factory
                        .new_identifier(cx.nodes, "arguments"),
                );
            }
        }

        // An async function is emit as an outer function that calls an inner
        // generator function. To preserve lexical bindings, we pass the current
        // `this` and `arguments` objects to `__awaiter`. The generator function
        // passed to `__awaiter` is executed inside of the callback to the
        // promise constructor.

        let saved_enclosing_function_parameter_names = self
            .enclosing_function_parameter_names
            .replace(Some(Set::new()));
        {
            let mut names = self.enclosing_function_parameter_names.borrow_mut();
            let names = names.as_mut().unwrap();
            for &parameter in &parameters {
                self.record_declaration_name(cx, parameter, names);
            }
        }

        let has_lexical_this = self.in_has_lexical_this_context();

        let body = cx.nodes[node].body().expect("function-like has a body");
        let mut async_body = self.transform_async_function_body_worker(ec, cx, body);
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
            .is_some_and(|s| s.size() > 0 || self.super_access.has_super_element_access.get());
        if emit_super_helpers {
            inner_parameters = self
                .super_access
                .super_access_visitor
                .borrow()
                .as_ref()
                .expect("super access visitor not initialized")
                .visit_nodes(cx, inner_parameters);
            if let Some(new_body) = self
                .super_access
                .substitute_super_accesses_in_body(cx, async_body)
            {
                async_body = new_body;
            }
        }

        let result: NodeId;
        if !is_arrow {
            ec.borrow_mut().start_variable_environment();

            // Minor optimization, emit `_super` helper to capture `super` access in an arrow.
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

            if capture_lexical_arguments && self.lexical_arguments.get().used {
                let stmt = self.create_capture_arguments_statement(ec, cx);
                ec.borrow().add_initialization_statement(stmt);
            }

            let awaiter = ec.borrow_mut().factory.new_awaiter_helper(
                cx.nodes,
                has_lexical_this,
                arguments_expression,
                inner_parameters,
                async_body,
            );
            let return_stmt = ec
                .borrow_mut()
                .factory
                .new_return_statement(cx.nodes, Some(awaiter));
            let statements_list = ec.borrow_mut().factory.new_node_list([return_stmt]);
            let merged = ec
                .borrow_mut()
                .end_and_merge_variable_environment_list(cx.nodes, Some(statements_list));
            let block = ec.borrow_mut().factory.new_block(cx.nodes, merged, true);
            cx.nodes[block].loc = cx.nodes[body].loc;

            if emit_super_helpers && self.super_access.has_super_element_access.get() {
                if self.super_access.has_super_property_assignment.get() {
                    ec.borrow()
                        .add_emit_helper(block, &[advanced_async_super_helper()]);
                } else {
                    ec.borrow().add_emit_helper(block, &[async_super_helper()]);
                }
            }

            result = block;
        } else {
            let mut res = ec.borrow_mut().factory.new_awaiter_helper(
                cx.nodes,
                has_lexical_this,
                arguments_expression,
                inner_parameters,
                async_body,
            );

            if capture_lexical_arguments && self.lexical_arguments.get().used {
                let block = ec
                    .borrow_mut()
                    .convert_to_function_block(cx.nodes, res, true /*multi_line*/);
                if !ast::is_block(&cx.nodes[res]) {
                    if let Some(first) = cx.nodes[block].statement_list().map(|l| l.nodes[0]) {
                        ec.borrow().set_original(first, res);
                    }
                }
                let block_statements = cx.nodes[block].statement_list().cloned().unwrap();
                let capture = self.create_capture_arguments_statement(ec, cx);
                let merged =
                    ec.borrow_mut()
                        .merge_environment_list(cx.nodes, &block_statements, &[capture]);
                let multi_line = cx.nodes[block].as_block().multi_line;
                res = ec
                    .borrow_mut()
                    .factory
                    .update_block(cx.nodes, block, Some(merged), multi_line)
                    .unwrap_or(block);
            }
            result = res;
        }

        self.enclosing_function_parameter_names
            .replace(saved_enclosing_function_parameter_names);
        if !is_arrow {
            self.super_access
                .captured_super_properties
                .replace(saved_captured_super_properties.unwrap());
            self.super_access
                .has_super_element_access
                .set(saved_has_super_element_access.unwrap());
            self.super_access
                .has_super_property_assignment
                .set(saved_has_super_property_assignment.unwrap());
            self.super_access
                .super_binding
                .set(saved_super_binding.unwrap());
            self.super_access
                .super_index_binding
                .set(saved_super_index_binding.unwrap());
            self.lexical_arguments.set(saved_lexical_arguments);
        } else if capture_lexical_arguments && !self.lexical_arguments.get().used {
            // If we created a new binding but it wasn't used, restore the previous state.
            // If it was used, keep the binding alive so sibling arrows can reuse it
            // (the `var` declaration hoists to the enclosing function scope).
            self.lexical_arguments.set(saved_lexical_arguments);
        } else if capture_lexical_arguments {
            // Keep the binding but clear the used flag so siblings don't re-emit the capture statement.
            let mut info = self.lexical_arguments.get();
            info.used = false;
            self.lexical_arguments.set(info);
        }
        result
    }

    /// `(tx *asyncTransformer) transformAsyncFunctionBodyWorker`.
    fn transform_async_function_body_worker(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        body: NodeId,
    ) -> NodeId {
        if ast::is_block(&cx.nodes[body]) {
            let statements = cx.nodes[body].statement_list().cloned();
            let visited_statements = self
                .async_body_visitor
                .borrow()
                .as_ref()
                .expect("async body visitor not initialized")
                .visit_nodes(cx, statements);
            let multi_line = cx.nodes[body].as_block().multi_line;
            return ec
                .borrow_mut()
                .factory
                .update_block(cx.nodes, body, visited_statements, multi_line)
                .unwrap_or(body);
        }
        // Convert expression body to block body with return statement
        let visited = self
            .async_body_visitor
            .borrow()
            .as_ref()
            .expect("async body visitor not initialized")
            .visit_node(cx, Some(body));
        let ret = ec
            .borrow_mut()
            .factory
            .new_return_statement(cx.nodes, visited);
        cx.nodes[ret].loc = cx.nodes[body].loc;
        let mut list = ec.borrow_mut().factory.new_node_list([ret]);
        list.loc = cx.nodes[body].loc;
        let block =
            ec.borrow_mut()
                .factory
                .new_block(cx.nodes, Some(list), false /*multi_line*/);
        cx.nodes[block].loc = cx.nodes[body].loc;
        block
    }

    /// `(tx *asyncTransformer) getOriginalIfFunctionLike`.
    fn get_original_if_function_like(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let original = ec.borrow().most_original(Some(node));
        if let Some(original) = original {
            if ast::is_function_like_declaration(Some(original), cx.nodes) {
                return original;
            }
        }
        node
    }
}

// assignmentTargetContainsSuperProperty checks top-down whether an assignment target
// expression contains a super property or element access (super.x or super[x]).
// This avoids relying on parent pointers (IsAssignmentTarget) which may not be set
// on synthesized AST nodes from prior transforms.
pub(crate) fn assignment_target_contains_super_property(
    cx: &VisitorCx<'_, '_>,
    node: NodeId,
) -> bool {
    match cx.nodes[node].kind {
        Kind::PropertyAccessExpression | Kind::ElementAccessExpression => cx.nodes[node]
            .expression()
            .is_some_and(|e| cx.nodes[e].kind == Kind::SuperKeyword),
        Kind::ParenthesizedExpression => cx.nodes[node]
            .as_parenthesized_expression()
            .expression
            .is_some_and(|e| assignment_target_contains_super_property(cx, e)),
        Kind::ArrayLiteralExpression => cx.nodes[node]
            .as_array_literal_expression()
            .elements
            .as_ref()
            .is_some_and(|els| {
                els.nodes
                    .iter()
                    .any(|&e| assignment_target_contains_super_property(cx, e))
            }),
        Kind::ObjectLiteralExpression => cx.nodes[node]
            .as_object_literal_expression()
            .properties
            .as_ref()
            .is_some_and(|props| {
                props.nodes.iter().any(|&prop| match cx.nodes[prop].kind {
                    Kind::PropertyAssignment => cx.nodes[prop]
                        .as_property_assignment()
                        .initializer
                        .is_some_and(|i| assignment_target_contains_super_property(cx, i)),
                    Kind::ShorthandPropertyAssignment => cx.nodes[prop]
                        .name()
                        .is_some_and(|n| assignment_target_contains_super_property(cx, n)),
                    Kind::SpreadAssignment => cx.nodes[prop]
                        .as_spread_assignment()
                        .expression
                        .is_some_and(|e| assignment_target_contains_super_property(cx, e)),
                    _ => false,
                })
            }),
        Kind::SpreadElement => cx.nodes[node]
            .as_spread_element()
            .expression
            .is_some_and(|e| assignment_target_contains_super_property(cx, e)),
        _ => false,
    }
}

// isUpdateExpression checks if a prefix/postfix unary expression is ++ or --.
pub(crate) fn is_update_expression(node: &ast::Node) -> bool {
    if ast::is_prefix_unary_expression(node) {
        let op = node.as_prefix_unary_expression().operator;
        return op == Kind::PlusPlusToken || op == Kind::MinusMinusToken;
    }
    if ast::is_postfix_unary_expression(node) {
        let op = node.as_postfix_unary_expression().operator;
        return op == Kind::PlusPlusToken || op == Kind::MinusMinusToken;
    }
    false
}

// isSimpleParameterList checks if every parameter has no initializer and an Identifier name.
pub(crate) fn is_simple_parameter_list(cx: &VisitorCx<'_, '_>, params: &[NodeId]) -> bool {
    params.iter().all(|&param| {
        let p = cx.nodes[param].as_parameter_declaration();
        if p.initializer.is_some() {
            return false;
        }
        cx.nodes[param]
            .name()
            .is_some_and(|n| ast::is_identifier(&cx.nodes[n]))
    })
}

// isNodeWithPossibleHoistedDeclaration checks if a node could contain hoisted declarations.
pub(crate) fn is_node_with_possible_hoisted_declaration(node: &ast::Node) -> bool {
    matches!(
        node.kind,
        Kind::Block
            | Kind::VariableStatement
            | Kind::WithStatement
            | Kind::IfStatement
            | Kind::SwitchStatement
            | Kind::CaseBlock
            | Kind::CaseClause
            | Kind::DefaultClause
            | Kind::LabeledStatement
            | Kind::ForStatement
            | Kind::ForInStatement
            | Kind::ForOfStatement
            | Kind::DoStatement
            | Kind::WhileStatement
            | Kind::TryStatement
            | Kind::CatchClause
    )
}

/// `newAsyncTransformer`.
pub(crate) fn new_async_transformer<'a>(opts: &TransformOptions<'a>) -> Option<Transformer<'a>> {
    make_transformer(opts, |ec| {
        let state = Rc::new(AsyncTransformer {
            super_access: Rc::new(SuperAccessState::default()),
            context_flags: Cell::new(0),
            enclosing_function_parameter_names: RefCell::new(None),
            lexical_arguments: Cell::new(LexicalArgumentsInfo {
                binding: None,
                used: false,
            }),
            async_body_visitor: RefCell::new(None),
            fallback_node_visitor: RefCell::new(None),
        });
        state.super_access.init_super_access_visitor(&ec);
        {
            let weak = Rc::downgrade(&state);
            let ec2 = ec.clone();
            let visit: Box<VisitFn<'a>> = Box::new(
                move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    let s = weak
                        .upgrade()
                        .expect("asyncTransformer dropped during visit");
                    s.visit_async_body_node(&ec2, v, cx, node)
                },
            );
            *state.async_body_visitor.borrow_mut() = Some(ec.borrow().new_node_visitor(visit));
        }
        {
            let weak = Rc::downgrade(&state);
            let ec2 = ec.clone();
            let visit: Box<VisitFn<'a>> = Box::new(
                move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    let s = weak
                        .upgrade()
                        .expect("asyncTransformer dropped during visit");
                    s.visit_fallback(cx, node)
                },
            );
            *state.fallback_node_visitor.borrow_mut() = Some(ec.borrow().new_node_visitor(visit));
            let _ = ec2;
        }
        Box::new(
            move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, v, cx, node)
            },
        )
    })
}
