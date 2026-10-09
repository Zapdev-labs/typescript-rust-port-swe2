// Ported from tsc/internal/transformers/estransforms/nullishcoalescing.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Downlevels `a ?? b` to `a !== null && a !== void 0 ? a : b` (with a temp
// variable for non-simple left operands).

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{Kind, NodeId, SubtreeFacts};

use super::utilities::create_not_null_condition;
use super::{Ec, make_transformer, visit_each_child, visit_node};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;
use crate::utilities::is_simple_copiable_expression;

/// `(ch *nullishCoalescingTransformer) visit`.
fn visit<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    if cx.nodes[node].subtree_facts(cx.nodes) & SubtreeFacts::CONTAINS_NULLISH_COALESCING
        == SubtreeFacts::NONE
    {
        return Some(node);
    }
    match cx.nodes[node].kind {
        Kind::BinaryExpression => Some(visit_binary_expression(ec, v, cx, node)),
        _ => Some(visit_each_child(v, cx, node)),
    }
}

/// `(ch *nullishCoalescingTransformer) visitBinaryExpression` — `node` must
/// be a `BinaryExpression`.
fn visit_binary_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    let (left_in, right_in, operator_kind) = {
        let d = cx.nodes[node].as_binary_expression();
        (d.left, d.right, d.operator_token.map(|t| cx.nodes[t].kind))
    };
    match operator_kind {
        Some(Kind::QuestionQuestionToken) => {
            let mut left = visit_node(v, cx, left_in.expect("binary expression has no left"))
                .expect("VisitNode returned no node");
            let mut right = left;
            if !is_simple_copiable_expression(&cx.nodes[left]) {
                right = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                ec.borrow_mut().add_variable_declaration(cx.nodes, right);
                left = ec
                    .borrow_mut()
                    .factory
                    .new_assignment_expression(cx.nodes, right, left);
            }
            let condition = create_not_null_condition(ec, cx, left, right, false);
            let visited_right =
                visit_node(v, cx, right_in.expect("binary expression has no right"))
                    .expect("VisitNode returned no node");
            let mut e = ec.borrow_mut();
            let question_token = e.factory.new_token(cx.nodes, Kind::QuestionToken);
            let colon_token = e.factory.new_token(cx.nodes, Kind::ColonToken);
            e.factory.new_conditional_expression(
                cx.nodes,
                Some(condition),
                Some(question_token),
                Some(right),
                Some(colon_token),
                Some(visited_right),
            )
        }
        _ => visit_each_child(v, cx, node),
    }
}

/// `newNullishCoalescingTransformer`.
pub(crate) fn new_nullish_coalescing_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    make_transformer(opts, |ec| {
        Box::new(move |v, cx, node| visit(&ec, v, cx, node))
    })
}
