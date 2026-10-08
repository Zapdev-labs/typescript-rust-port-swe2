// Ported from tsc/internal/transformers/modifiervisitor.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `ExtractModifiers` — filters a `ModifierList` down to a set of allowed
// modifier kinds using a one-shot `NodeVisitor`.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{self as ast, ModifierFlags, ModifierList, Node, NodeId};
use tsc_printer::EmitContext;

use crate::transformer::Transformer;

/// `(v *modifierVisitor) visit` — drops nodes whose `ModifierToFlag` is set
/// and disjoint from `allowed` (`AllowedModifiers` on Go's `modifierVisitor`).
fn modifier_visit<'a>(allowed: ModifierFlags) -> Box<VisitFn<'a>> {
    Box::new(
        move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
            let flags = ast::modifier_to_flag(cx.nodes[node].kind);
            if flags != ModifierFlags::NONE && flags & allowed == ModifierFlags::NONE {
                return None;
            }
            Some(node)
        },
    )
}

/// `ExtractModifiers(emitContext, modifiers, allowed)` — `emit_context` is
/// `Option` mirroring Go's nilable `*printer.EmitContext` (a fresh context is
/// created in that case).
pub fn extract_modifiers(
    emit_context: Option<&Rc<RefCell<EmitContext>>>,
    nodes: &mut Vec<Node>,
    modifiers: Option<ModifierList>,
    allowed: ModifierFlags,
) -> Option<ModifierList> {
    let modifiers = modifiers?;
    let tx = Transformer::new(modifier_visit(allowed), emit_context.cloned());
    tx.with_visit_cx(nodes, |cx| {
        tx.visitor().visit_modifiers(cx, Some(modifiers))
    })
}
