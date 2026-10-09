// Ported from tsc/internal/transformers/estransforms/logicalassignment.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Downlevels `a ||= b`, `a &&= b`, `a ??= b` to `a || (a = b)` etc., with
// temp variables for non-simple access targets.

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId, SubtreeFacts};

use super::{Ec, make_transformer, visit_each_child, visit_node};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;
use crate::utilities::is_simple_copiable_expression;

/// `(ch *logicalAssignmentTransformer) visit`.
fn visit<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    if cx.nodes[node].subtree_facts(cx.nodes) & SubtreeFacts::CONTAINS_LOGICAL_ASSIGNMENTS
        == SubtreeFacts::NONE
    {
        return Some(node);
    }
    match cx.nodes[node].kind {
        Kind::BinaryExpression => Some(visit_binary_expression(ec, v, cx, node)),
        _ => Some(visit_each_child(v, cx, node)),
    }
}

/// `(ch *logicalAssignmentTransformer) visitBinaryExpression` — `node` must
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
    let non_assignment_operator = match operator_kind {
        Some(Kind::BarBarEqualsToken) => Kind::BarBarToken,
        Some(Kind::AmpersandAmpersandEqualsToken) => Kind::AmpersandAmpersandToken,
        Some(Kind::QuestionQuestionEqualsToken) => Kind::QuestionQuestionToken,
        _ => return visit_each_child(v, cx, node),
    };

    let mut left = ast::skip_parentheses(
        visit_node(v, cx, left_in.expect("binary expression has no left"))
            .expect("VisitNode returned no node"),
        cx.nodes,
    );
    let mut assignment_target = left;
    let right = ast::skip_parentheses(
        visit_node(v, cx, right_in.expect("binary expression has no right"))
            .expect("VisitNode returned no node"),
        cx.nodes,
    );

    if ast::is_access_expression(&cx.nodes[left]) {
        let left_expression = cx.nodes[left].expression().unwrap();
        let property_access_target_simple_copiable =
            is_simple_copiable_expression(&cx.nodes[left_expression]);
        let mut property_access_target = left_expression;
        let mut property_access_target_assignment = left_expression;
        if !property_access_target_simple_copiable {
            property_access_target = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
            ec.borrow_mut()
                .add_variable_declaration(cx.nodes, property_access_target);
            property_access_target_assignment = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                property_access_target,
                left_expression,
            );
        }

        if ast::is_property_access_expression(&cx.nodes[left]) {
            let left_name = cx.nodes[left].name();
            assignment_target = ec.borrow_mut().factory.new_property_access_expression(
                cx.nodes,
                Some(property_access_target),
                None,
                left_name,
                ast::NodeFlags::NONE,
            );
            left = ec.borrow_mut().factory.new_property_access_expression(
                cx.nodes,
                Some(property_access_target_assignment),
                None,
                left_name,
                ast::NodeFlags::NONE,
            );
        } else {
            let left_argument = cx.nodes[left]
                .as_element_access_expression()
                .argument_expression
                .unwrap();
            let element_access_argument_simple_copiable =
                is_simple_copiable_expression(&cx.nodes[left_argument]);
            let mut element_access_argument = left_argument;
            let mut argument_expr = element_access_argument;
            if !element_access_argument_simple_copiable {
                element_access_argument = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                ec.borrow_mut()
                    .add_variable_declaration(cx.nodes, element_access_argument);
                argument_expr = ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    element_access_argument,
                    left_argument,
                );
            }

            assignment_target = ec.borrow_mut().factory.new_element_access_expression(
                cx.nodes,
                Some(property_access_target),
                None,
                Some(element_access_argument),
                ast::NodeFlags::NONE,
            );
            left = ec.borrow_mut().factory.new_element_access_expression(
                cx.nodes,
                Some(property_access_target_assignment),
                None,
                Some(argument_expr),
                ast::NodeFlags::NONE,
            );
        }
    }

    let mut e = ec.borrow_mut();
    let f = &mut e.factory;
    let assignment = f.new_assignment_expression(cx.nodes, assignment_target, right);
    let parenthesized = f.new_parenthesized_expression(cx.nodes, Some(assignment));
    let op_token = f.new_token(cx.nodes, non_assignment_operator);
    f.new_binary_expression(
        cx.nodes,
        None,
        Some(left),
        None,
        Some(op_token),
        Some(parenthesized),
    )
}

/// `newLogicalAssignmentTransformer`.
pub(crate) fn new_logical_assignment_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    make_transformer(opts, |ec| {
        Box::new(move |v, cx, node| visit(&ec, v, cx, node))
    })
}
