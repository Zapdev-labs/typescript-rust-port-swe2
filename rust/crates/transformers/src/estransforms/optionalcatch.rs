// Ported from tsc/internal/transformers/estransforms/optionalcatch.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Downlevels `catch {}` (optional catch binding) to `catch (_a) {}`.

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{Kind, NodeId, SubtreeFacts};

use super::{Ec, make_transformer, visit_each_child};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;

/// `(ch *optionalCatchTransformer) visit`.
fn visit<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    if cx.nodes[node].subtree_facts(cx.nodes) & SubtreeFacts::CONTAINS_MISSING_CATCH_CLAUSE_VARIABLE
        == SubtreeFacts::NONE
    {
        return Some(node);
    }
    match cx.nodes[node].kind {
        Kind::CatchClause => Some(visit_catch_clause(ec, v, cx, node)),
        _ => Some(visit_each_child(v, cx, node)),
    }
}

/// `(ch *optionalCatchTransformer) visitCatchClause` — `node` must be a
/// `CatchClause`.
fn visit_catch_clause<'a>(
    ec: &Ec,
    v: &NodeVisitor<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    if cx.nodes[node]
        .as_catch_clause()
        .variable_declaration
        .is_none()
    {
        let variable_declaration = {
            let mut e = ec.borrow_mut();
            let temp = e.factory.new_temp_variable(cx.nodes);
            e.factory
                .new_variable_declaration(cx.nodes, Some(temp), None, None, None)
        };
        let block = cx.nodes[node].as_catch_clause().block;
        let block = super::visit(v, cx, block.expect("catch clause has no block"));
        return ec.borrow_mut().factory.new_catch_clause(
            cx.nodes,
            Some(variable_declaration),
            block,
        );
    }
    visit_each_child(v, cx, node)
}

/// `newOptionalCatchTransformer`.
pub(crate) fn new_optional_catch_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    make_transformer(opts, |ec| {
        Box::new(move |v, cx, node| visit(&ec, v, cx, node))
    })
}
