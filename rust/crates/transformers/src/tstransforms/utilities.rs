// Ported from tsc/internal/transformers/tstransforms/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Helpers shared by the TypeScript-specific transforms (`tstransforms`).
//
// PORT: Go's `value any` (which is `string | jsnum.Number` in practice) is
// the `tsc_evaluator::Value` enum produced by `Result::value`. `f` is the
// printer `NodeFactory` reached through `EmitContext::factory`.

use tsc_ast::{self as ast, Kind, Node, NodeId};
use tsc_evaluator::Value;
use tsc_jsnum::Number;

/// `constantExpression` — creates a literal expression for a constant value,
/// or `None` when the value has no constant-expression form (Go returns nil).
pub fn constant_expression(
    value: &Value,
    factory: &mut tsc_printer::NodeFactory,
    nodes: &mut Vec<Node>,
) -> Option<NodeId> {
    match value {
        Value::String(s) => Some(factory.new_string_literal(nodes, s, ast::TokenFlags::NONE)),
        Value::Number(n) => {
            if n.is_inf() {
                if n.0 > 0.0 {
                    return Some(factory.new_identifier(nodes, "Infinity"));
                }
                let operand = factory.new_identifier(nodes, "Infinity");
                return Some(factory.new_prefix_unary_expression(
                    nodes,
                    Kind::MinusToken,
                    Some(operand),
                ));
            }
            if n.is_nan() {
                return Some(factory.new_identifier(nodes, "NaN"));
            }
            if n.0 < 0.0 {
                let operand = constant_expression(
                    &Value::Number(Number(-n.0)),
                    factory,
                    nodes,
                )?;
                return Some(factory.new_prefix_unary_expression(
                    nodes,
                    Kind::MinusToken,
                    Some(operand),
                ));
            }
            Some(factory.new_numeric_literal(nodes, &n.string(), ast::TokenFlags::NONE))
        }
        _ => None,
    }
}
