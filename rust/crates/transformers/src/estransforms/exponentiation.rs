// Ported from tsc/internal/transformers/estransforms/exponentiation.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Downlevels `a ** b` / `a **= b` to `Math.pow` calls.

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId, SubtreeFacts};

use super::{Ec, make_transformer, visit_each_child, visit_node};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;

/// `(ch *exponentiationTransformer) visit`.
fn visit<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    if cx.nodes[node].subtree_facts(cx.nodes) & SubtreeFacts::CONTAINS_EXPONENTIATION_OPERATOR
        == SubtreeFacts::NONE
    {
        return Some(node);
    }
    match cx.nodes[node].kind {
        Kind::BinaryExpression => Some(visit_binary_expression(ec, v, cx, node)),
        _ => Some(visit_each_child(v, cx, node)),
    }
}

/// `(ch *exponentiationTransformer) visitBinaryExpression` — `node` must be a
/// `BinaryExpression`.
fn visit_binary_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    let operator_kind = cx.nodes[node]
        .as_binary_expression()
        .operator_token
        .map(|t| cx.nodes[t].kind);
    match operator_kind {
        Some(Kind::AsteriskAsteriskEqualsToken) => {
            visit_exponentiation_assignment_expression(ec, v, cx, node)
        }
        Some(Kind::AsteriskAsteriskToken) => visit_exponentiation_expression(ec, v, cx, node),
        _ => visit_each_child(v, cx, node),
    }
}

/// `(ch *exponentiationTransformer) visitExponentiationAssignmentExpression`
/// — `node` must be a `BinaryExpression` with `**=`.
fn visit_exponentiation_assignment_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    let (left_in, right_in) = {
        let d = cx.nodes[node].as_binary_expression();
        (d.left, d.right)
    };
    let left = visit_node(v, cx, left_in.expect("binary expression has no left"))
        .expect("VisitNode returned no node");
    let right = visit_node(v, cx, right_in.expect("binary expression has no right"))
        .expect("VisitNode returned no node");

    let target: NodeId;
    let value: NodeId;
    if ast::is_element_access_expression(&cx.nodes[left]) {
        // Transforms `a[x] **= b` into `(_a = a)[_x = x] = Math.pow(_a[_x], b)`
        let expression_temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, expression_temp);
        let argument_expression_temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, argument_expression_temp);

        let left_expression = cx.nodes[left].expression();
        let left_argument = cx.nodes[left]
            .as_element_access_expression()
            .argument_expression;

        let obj_expr = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            expression_temp,
            left_expression.expect("element access has no expression"),
        );
        cx.nodes[obj_expr].loc = cx.nodes[left_expression.unwrap()].loc;
        let access_expr = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            argument_expression_temp,
            left_argument.expect("element access has no argument"),
        );
        cx.nodes[access_expr].loc = cx.nodes[left_argument.unwrap()].loc;

        target = ec.borrow_mut().factory.new_element_access_expression(
            cx.nodes,
            Some(obj_expr),
            None,
            Some(access_expr),
            ast::NodeFlags::NONE,
        );

        value = ec.borrow_mut().factory.new_element_access_expression(
            cx.nodes,
            Some(expression_temp),
            None,
            Some(argument_expression_temp),
            ast::NodeFlags::NONE,
        );
        cx.nodes[value].loc = cx.nodes[left].loc;
    } else if ast::is_property_access_expression(&cx.nodes[left]) {
        // Transforms `a.x **= b` into `(_a = a).x = Math.pow(_a.x, b)`
        let expression_temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, expression_temp);
        let left_expression = cx.nodes[left].expression();
        let left_name = cx.nodes[left].name();
        let assignment = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            expression_temp,
            left_expression.expect("property access has no expression"),
        );
        cx.nodes[assignment].loc = cx.nodes[left_expression.unwrap()].loc;
        target = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(assignment),
            None,
            left_name,
            ast::NodeFlags::NONE,
        );
        cx.nodes[target].loc = cx.nodes[left].loc;

        value = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(expression_temp),
            None,
            left_name,
            ast::NodeFlags::NONE,
        );
        cx.nodes[value].loc = cx.nodes[left].loc;
    } else {
        // Transforms `a **= b` into `a = Math.pow(a, b)`
        target = left;
        value = left;
    }

    let rhs =
        ec.borrow_mut()
            .factory
            .new_global_method_call(cx.nodes, "Math", "pow", vec![value, right]);
    cx.nodes[rhs].loc = cx.nodes[node].loc;
    let result = ec
        .borrow_mut()
        .factory
        .new_assignment_expression(cx.nodes, target, rhs);
    cx.nodes[result].loc = cx.nodes[node].loc;
    result
}

/// `(ch *exponentiationTransformer) visitExponentiationExpression` — `node`
/// must be a `BinaryExpression` with `**`.
fn visit_exponentiation_expression<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    let (left_in, right_in) = {
        let d = cx.nodes[node].as_binary_expression();
        (d.left, d.right)
    };
    let left = visit_node(v, cx, left_in.expect("binary expression has no left"))
        .expect("VisitNode returned no node");
    let right = visit_node(v, cx, right_in.expect("binary expression has no right"))
        .expect("VisitNode returned no node");
    let result =
        ec.borrow_mut()
            .factory
            .new_global_method_call(cx.nodes, "Math", "pow", vec![left, right]);
    cx.nodes[result].loc = cx.nodes[node].loc;
    result
}

/// `newExponentiationTransformer`.
pub(crate) fn new_exponentiation_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    make_transformer(opts, |ec| {
        Box::new(move |v, cx, node| visit(&ec, v, cx, node))
    })
}
