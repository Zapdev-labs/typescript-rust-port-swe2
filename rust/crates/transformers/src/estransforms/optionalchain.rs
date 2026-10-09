// Ported from tsc/internal/transformers/estransforms/optionalchain.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Downlevels optional chains (`a?.b`, `a?.()`, `a?.[x]`) into conditional
// expressions over a temp-captured base.

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeFlags, NodeId, SubtreeFacts, outer_expression_kinds};
use tsc_printer::EmitFlags;

use super::utilities::create_not_null_condition;
use super::{Ec, make_transformer, visit_each_child, visit_node};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;
use crate::utilities::is_simple_copiable_expression;

/// `(ch *optionalChainTransformer) visit`.
fn visit<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    if cx.nodes[node].subtree_facts(cx.nodes) & SubtreeFacts::CONTAINS_OPTIONAL_CHAINING
        == SubtreeFacts::NONE
    {
        return Some(node);
    }
    match cx.nodes[node].kind {
        Kind::CallExpression => Some(visit_call_expression(ec, v, cx, node, false)),
        Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
            if cx.nodes[node].flags & NodeFlags::OPTIONAL_CHAIN != NodeFlags::NONE {
                return Some(visit_optional_expression(ec, v, cx, node, false, false));
            }
            Some(visit_each_child(v, cx, node))
        }
        Kind::DeleteExpression => Some(visit_delete_expression(ec, v, cx, node)),
        _ => Some(visit_each_child(v, cx, node)),
    }
}

/// `(ch *optionalChainTransformer) visitCallExpression` — `node` must be a
/// `CallExpression`.
fn visit_call_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    capture_this_arg: bool,
) -> NodeId {
    if cx.nodes[node].flags & NodeFlags::OPTIONAL_CHAIN != NodeFlags::NONE {
        // If `node` is an optional chain, then it is the outermost chain of
        // an optional expression.
        return visit_optional_expression(ec, v, cx, node, capture_this_arg, false);
    }
    let expression = cx.nodes[node].as_call_expression().expression.unwrap();
    if ast::is_parenthesized_expression(&cx.nodes[expression]) {
        let unwrapped = ast::skip_parentheses(expression, cx.nodes);
        if cx.nodes[unwrapped].flags & NodeFlags::OPTIONAL_CHAIN != NodeFlags::NONE {
            // capture thisArg for calls of parenthesized optional chains like
            // `(foo?.bar)()`
            let expression = visit_parenthesized_expression(ec, v, cx, expression, true, false);
            let args = v.visit_nodes(cx, cx.nodes[node].as_call_expression().arguments.clone());
            if ast::is_synthetic_reference_expression(&cx.nodes[expression]) {
                let (synth_expr, this_arg) = {
                    let d = cx.nodes[expression].as_synthetic_reference_expression();
                    (d.expression.unwrap(), d.this_arg)
                };
                let res = ec.borrow_mut().factory.new_function_call_call(
                    cx.nodes,
                    synth_expr,
                    this_arg,
                    args.map(|a| a.nodes.to_vec()).unwrap_or_default(),
                );
                cx.nodes[res].loc = cx.nodes[node].loc;
                ec.borrow().set_original(res, node);
                return res;
            }
            let flags = cx.nodes[node].flags;
            return ec
                .borrow_mut()
                .factory
                .update_call_expression(
                    cx.nodes,
                    node,
                    Some(expression),
                    None, // question_dot_token
                    None, // type_arguments
                    args,
                    flags,
                )
                .unwrap_or(node);
        }
    }
    visit_each_child(v, cx, node)
}

/// `(ch *optionalChainTransformer) visitParenthesizedExpression` — `node`
/// must be a `ParenthesizedExpression`.
fn visit_parenthesized_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    capture_this_arg: bool,
    is_delete: bool,
) -> NodeId {
    let inner = cx.nodes[node].expression().unwrap();
    let expr = visit_non_optional_expression(ec, v, cx, inner, capture_this_arg, is_delete);
    if ast::is_synthetic_reference_expression(&cx.nodes[expr]) {
        // `(a.b)` -> { expression `((_a = a).b)`, thisArg: `_a` }
        // `(a[b])` -> { expression `((_a = a)[b])`, thisArg: `_a` }
        let (synth_expr, this_arg) = {
            let d = cx.nodes[expr].as_synthetic_reference_expression();
            (d.expression, d.this_arg)
        };
        let updated = ec
            .borrow_mut()
            .factory
            .update_parenthesized_expression(cx.nodes, node, synth_expr)
            .unwrap_or(node);
        let res = ec.borrow_mut().factory.new_synthetic_reference_expression(
            cx.nodes,
            Some(updated),
            this_arg,
        );
        ec.borrow().set_original(res, node);
        return res;
    }
    ec.borrow_mut()
        .factory
        .update_parenthesized_expression(cx.nodes, node, Some(expr))
        .unwrap_or(node)
}

/// `(ch *optionalChainTransformer) visitPropertyOrElementAccessExpression` —
/// `node` is a `PropertyAccessExpression` or `ElementAccessExpression`.
fn visit_property_or_element_access_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    capture_this_arg: bool,
    is_delete: bool,
) -> NodeId {
    if cx.nodes[node].flags & NodeFlags::OPTIONAL_CHAIN != NodeFlags::NONE {
        // If `node` is an optional chain, then it is the outermost chain of
        // an optional expression.
        return visit_optional_expression(ec, v, cx, node, capture_this_arg, is_delete);
    }
    let mut expression = visit_node(
        v,
        cx,
        cx.nodes[node]
            .expression()
            .expect("access expression has no expression"),
    );
    tsc_debug::assert_!(
        expression.is_none_or(|e| !ast::is_synthetic_reference_expression(&cx.nodes[e]))
    );

    let mut this_arg: Option<NodeId> = None;
    if capture_this_arg {
        if !is_simple_copiable_expression(&cx.nodes[expression.unwrap()]) {
            this_arg = Some(ec.borrow_mut().factory.new_temp_variable(cx.nodes));
            ec.borrow_mut()
                .add_variable_declaration(cx.nodes, this_arg.unwrap());
            expression = Some(ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                this_arg.unwrap(),
                expression.unwrap(),
            ));
        } else {
            this_arg = expression;
        }
    }

    let mut expression = expression;
    if cx.nodes[node].kind == Kind::PropertyAccessExpression {
        let name = cx.nodes[node].as_property_access_expression().name;
        let visited_name = visit_node(v, cx, name.expect("property access has no name"));
        let flags = cx.nodes[node].flags;
        expression = Some(
            ec.borrow_mut()
                .factory
                .update_property_access_expression(
                    cx.nodes,
                    node,
                    expression,
                    None, // question_dot_token
                    visited_name,
                    flags,
                )
                .unwrap_or(node),
        );
    } else {
        let argument_expression = cx.nodes[node]
            .as_element_access_expression()
            .argument_expression;
        let visited_arg = visit_node(
            v,
            cx,
            argument_expression.expect("element access has no argument"),
        );
        let flags = cx.nodes[node].flags;
        expression = Some(
            ec.borrow_mut()
                .factory
                .update_element_access_expression(
                    cx.nodes,
                    node,
                    expression,
                    None,
                    visited_arg,
                    flags,
                )
                .unwrap_or(node),
        );
    }

    if let Some(this_arg) = this_arg {
        let res = ec.borrow_mut().factory.new_synthetic_reference_expression(
            cx.nodes,
            expression,
            Some(this_arg),
        );
        ec.borrow().set_original(res, node);
        return res;
    }
    expression.unwrap()
}

/// `(ch *optionalChainTransformer) visitDeleteExpression` — `node` must be a
/// `DeleteExpression`.
fn visit_delete_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    let expression = cx.nodes[node].expression().unwrap();
    let unwrapped = ast::skip_parentheses(expression, cx.nodes);
    if cx.nodes[unwrapped].flags & NodeFlags::OPTIONAL_CHAIN != NodeFlags::NONE {
        return visit_non_optional_expression(ec, v, cx, expression, false, true);
    }
    visit_each_child(v, cx, node)
}

/// `(ch *optionalChainTransformer) visitNonOptionalExpression`.
fn visit_non_optional_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    capture_this_arg: bool,
    is_delete: bool,
) -> NodeId {
    match cx.nodes[node].kind {
        Kind::ParenthesizedExpression => {
            visit_parenthesized_expression(ec, v, cx, node, capture_this_arg, is_delete)
        }
        Kind::ElementAccessExpression | Kind::PropertyAccessExpression => {
            visit_property_or_element_access_expression(
                ec,
                v,
                cx,
                node,
                capture_this_arg,
                is_delete,
            )
        }
        Kind::CallExpression => visit_call_expression(ec, v, cx, node, capture_this_arg),
        _ => visit_node(v, cx, node).expect("VisitNode returned no node"),
    }
}

/// `flattenResult`.
struct FlattenResult {
    expression: NodeId,
    chain: Vec<NodeId>,
}

/// `isNonNullChain`.
fn is_non_null_chain(cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
    ast::is_non_null_expression(&cx.nodes[node])
        && cx.nodes[node].flags & NodeFlags::OPTIONAL_CHAIN != NodeFlags::NONE
}

/// `flattenChain`.
fn flatten_chain(cx: &VisitorCx<'_, '_>, chain: NodeId) -> FlattenResult {
    tsc_debug::assert_!(!is_non_null_chain(cx, chain));
    let mut chain = chain;
    let mut links: Vec<NodeId> = vec![chain];
    while !ast::is_tagged_template_expression(&cx.nodes[chain])
        && cx.nodes[chain].question_dot_token().is_none()
    {
        chain = ast::skip_partially_emitted_expressions(
            cx.nodes[chain]
                .expression()
                .expect("chain segment has no expression"),
            cx.nodes,
        );
        tsc_debug::assert_!(!is_non_null_chain(cx, chain));
        links.insert(0, chain);
    }
    FlattenResult {
        expression: cx.nodes[chain]
            .expression()
            .expect("chain root has no expression"),
        chain: links,
    }
}

/// `isCallChain`.
fn is_call_chain(cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
    ast::is_call_expression(&cx.nodes[node])
        && cx.nodes[node].flags & NodeFlags::OPTIONAL_CHAIN != NodeFlags::NONE
}

/// `(ch *optionalChainTransformer) visitOptionalExpression`.
fn visit_optional_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    capture_this_arg: bool,
    is_delete: bool,
) -> NodeId {
    let r = flatten_chain(cx, node);
    let expression = r.expression;
    let chain = r.chain;
    let left = visit_non_optional_expression(
        ec,
        v,
        cx,
        ast::skip_partially_emitted_expressions(expression, cx.nodes),
        is_call_chain(cx, chain[0]),
        false,
    );
    let mut left_this_arg: Option<NodeId> = None;
    let mut captured_left = left;
    if ast::is_synthetic_reference_expression(&cx.nodes[left]) {
        left_this_arg = cx.nodes[left].as_synthetic_reference_expression().this_arg;
        captured_left = cx.nodes[left]
            .as_synthetic_reference_expression()
            .expression
            .unwrap();
    }
    let mut left_expression = ec.borrow_mut().factory.restore_outer_expressions(
        cx.nodes,
        Some(expression),
        captured_left,
        outer_expression_kinds::PARTIALLY_EMITTED_EXPRESSIONS,
    );
    let mut captured_left = captured_left;
    if !is_simple_copiable_expression(&cx.nodes[captured_left]) {
        captured_left = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, captured_left);
        left_expression = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            captured_left,
            left_expression,
        );
    }
    let mut right_expression = captured_left;
    let mut this_arg: Option<NodeId> = None;

    for (i, &segment) in chain.iter().enumerate() {
        match cx.nodes[segment].kind {
            Kind::ElementAccessExpression | Kind::PropertyAccessExpression => {
                if i == chain.len() - 1 && capture_this_arg {
                    if !is_simple_copiable_expression(&cx.nodes[right_expression]) {
                        this_arg = Some(ec.borrow_mut().factory.new_temp_variable(cx.nodes));
                        ec.borrow_mut()
                            .add_variable_declaration(cx.nodes, this_arg.unwrap());
                        right_expression = ec.borrow_mut().factory.new_assignment_expression(
                            cx.nodes,
                            this_arg.unwrap(),
                            right_expression,
                        );
                    } else {
                        this_arg = Some(right_expression);
                    }
                }
                if cx.nodes[segment].kind == Kind::ElementAccessExpression {
                    let argument_expression = cx.nodes[segment]
                        .as_element_access_expression()
                        .argument_expression;
                    let visited = visit_node(
                        v,
                        cx,
                        argument_expression.expect("element access has no argument"),
                    );
                    right_expression = ec.borrow_mut().factory.new_element_access_expression(
                        cx.nodes,
                        Some(right_expression),
                        None,
                        visited,
                        NodeFlags::NONE,
                    );
                } else {
                    let name = cx.nodes[segment].as_property_access_expression().name;
                    let visited = visit_node(v, cx, name.expect("property access has no name"));
                    right_expression = ec.borrow_mut().factory.new_property_access_expression(
                        cx.nodes,
                        Some(right_expression),
                        None,
                        visited,
                        NodeFlags::NONE,
                    );
                }
            }
            Kind::CallExpression => {
                if i == 0 && left_this_arg.is_some() {
                    if !ec.borrow().has_auto_generate_info(left_this_arg) {
                        left_this_arg = Some(
                            ec.borrow_mut()
                                .factory
                                .clone_node(cx.nodes, left_this_arg.unwrap()),
                        );
                        ec.borrow()
                            .add_emit_flags(left_this_arg.unwrap(), EmitFlags::NO_COMMENTS);
                    }
                    let mut call_this_arg = left_this_arg;
                    if cx.nodes[left_this_arg.unwrap()].kind == Kind::SuperKeyword {
                        call_this_arg = Some(ec.borrow_mut().factory.new_this_expression(cx.nodes));
                    }
                    let argument_list = cx.nodes[segment].as_call_expression().arguments.clone();
                    let visited_args = v.visit_nodes(cx, argument_list);
                    right_expression = ec.borrow_mut().factory.new_function_call_call(
                        cx.nodes,
                        right_expression,
                        call_this_arg,
                        visited_args.map(|a| a.nodes.to_vec()).unwrap_or_default(),
                    );
                } else {
                    let argument_list = cx.nodes[segment].as_call_expression().arguments.clone();
                    let visited_args = v.visit_nodes(cx, argument_list);
                    right_expression = ec.borrow_mut().factory.new_call_expression(
                        cx.nodes,
                        Some(right_expression),
                        None,
                        None,
                        visited_args,
                        NodeFlags::NONE,
                    );
                }
            }
            _ => {}
        }
        ec.borrow().set_original(right_expression, segment);
    }

    let mut target: NodeId;
    if is_delete {
        let condition = create_not_null_condition(ec, cx, left_expression, captured_left, true);
        let mut e = ec.borrow_mut();
        let question_token = e.factory.new_token(cx.nodes, Kind::QuestionToken);
        let true_expr = e.factory.new_true_expression(cx.nodes);
        let colon_token = e.factory.new_token(cx.nodes, Kind::ColonToken);
        let delete_expr = e
            .factory
            .new_delete_expression(cx.nodes, Some(right_expression));
        target = e.factory.new_conditional_expression(
            cx.nodes,
            Some(condition),
            Some(question_token),
            Some(true_expr),
            Some(colon_token),
            Some(delete_expr),
        );
    } else {
        let condition = create_not_null_condition(ec, cx, left_expression, captured_left, true);
        let mut e = ec.borrow_mut();
        let question_token = e.factory.new_token(cx.nodes, Kind::QuestionToken);
        let void_zero = e.factory.new_void_zero_expression(cx.nodes);
        let colon_token = e.factory.new_token(cx.nodes, Kind::ColonToken);
        target = e.factory.new_conditional_expression(
            cx.nodes,
            Some(condition),
            Some(question_token),
            Some(void_zero),
            Some(colon_token),
            Some(right_expression),
        );
    }
    cx.nodes[target].loc = cx.nodes[node].loc;
    if let Some(this_arg) = this_arg {
        target = ec.borrow_mut().factory.new_synthetic_reference_expression(
            cx.nodes,
            Some(target),
            Some(this_arg),
        );
    }
    ec.borrow().set_original(target, node);
    target
}

/// `newOptionalChainTransformer`.
pub(crate) fn new_optional_chain_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    make_transformer(opts, |ec| {
        Box::new(move |v, cx, node| visit(&ec, v, cx, node))
    })
}
