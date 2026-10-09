// Ported from tsc/internal/transformers/estransforms/classthis.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::{self as ast, Kind, Node, NodeId};
use tsc_printer::EmitContext;

/// Gets whether a node is a `static {}` block containing only a single
/// assignment of the static `this` to the `_classThis` (or similar) variable
/// stored in the `classthis` property of the block's `EmitNode`.
pub(crate) fn is_class_this_assignment_block(
    emit_context: &EmitContext,
    nodes: &[Node],
    node: NodeId,
) -> bool {
    if ast::is_class_static_block_declaration(&nodes[node]) {
        let n = nodes[node].as_class_static_block_declaration();
        let Some(body_id) = n.body else {
            return false;
        };
        let body = nodes[body_id].as_block();
        if let Some(statements) = &body.statements
            && statements.nodes.len() == 1
        {
            let statement = statements.nodes[0];
            if ast::is_expression_statement(&nodes[statement])
                && let Some(expression) = nodes[statement].expression()
                && ast::is_assignment_expression(&nodes[expression], nodes, true)
            {
                let binary = nodes[expression].as_binary_expression();
                return binary.left.is_some_and(|l| ast::is_identifier(&nodes[l]))
                    && emit_context.class_this(node) == binary.left
                    && binary
                        .right
                        .is_some_and(|r| nodes[r].kind == Kind::ThisKeyword);
            }
        }
    }
    false
}
