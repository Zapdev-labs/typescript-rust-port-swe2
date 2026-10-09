// Ported from tsc/internal/transformers/estransforms @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The ES downlevel transforms. File layout mirrors the Go package one-to-one.
//
// PORT notes common to every file in this module:
//   - Go transformer structs (e.g. `type classFieldsTransformer struct {
//     transformers.Transformer; ... }`) embed `*Transformer` so their visit
//     methods can reach `tx.Visitor()`, `tx.Factory()`, and
//     `tx.EmitContext()`. Rust cannot capture the `Transformer` being built
//     inside its own visit closure, so each transform's state lives in an
//     `Rc`d struct captured by the closure, the `EmitContext` is captured as
//     `Rc<RefCell<EmitContext>>`, and the running `NodeVisitor` arrives as
//     the visit callback's first parameter. Go's `ch.Factory()` calls map
//     onto `ec.borrow_mut().factory` (see `f!` below).
//   - Go methods freely interleave node creation and recursive visiting.
//     Here a `RefCell<EmitContext>` borrow may never span a `v.visit_*` call
//     (the transform factory's `on_update`/`on_clone` hooks borrow the
//     context) — all `borrow`/`borrow_mut` scopes are single statements or
//     tight blocks.
//   - `update_*` factory methods return `Option<NodeId>` where `None` means
//     "unchanged" (Go returned the input pointer); call sites unwrap with
//     `.unwrap_or(node)`.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::NodeId;
use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_printer::EmitContext;

use crate::chain::TransformOptions;
use crate::transformer::Transformer;

pub mod r#async;
pub mod classfields;
pub mod classthis;
pub mod definitions;
pub mod esdecorator;
pub mod exponentiation;
pub mod forawait;
pub mod logicalassignment;
pub mod namedevaluation;
pub mod nullishcoalescing;
pub mod objectrestspread;
pub mod optionalcatch;
pub mod optionalchain;
pub mod taggedtemplate;
pub mod usestrict;
pub mod using;
pub mod utilities;

pub use definitions::*;

/// The shared emit-context handle every transform closure captures.
pub(crate) type Ec = Rc<RefCell<EmitContext>>;

/// Builds the `Rc<RefCell<EmitContext>>`/`Transformer` pair the way Go's
/// `tx.NewTransformer(tx.visit, opts.Context)` does: reuse `opts.context`
/// when present, otherwise mint a fresh `EmitContext` shared by both the
/// visit closure and the returned `Transformer`.
pub(crate) fn make_transformer<'a>(
    opts: &TransformOptions<'a>,
    visit: impl FnOnce(Ec) -> Box<tsc_ast::visitor::VisitFn<'a>>,
) -> Option<Transformer<'a>> {
    let emit_context = opts
        .context
        .clone()
        .unwrap_or_else(|| Rc::new(RefCell::new(EmitContext::new())));
    let visit = visit(emit_context.clone());
    Some(Transformer::new(visit, Some(emit_context)))
}

/// `ch.Visitor().VisitEachChild(node)` — returns `node` itself when the
/// children were unchanged (Go returns the input pointer).
#[inline]
pub(crate) fn visit_each_child(
    v: &NodeVisitor<'_>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    v.visit_each_child(cx, node).unwrap_or(node)
}

/// `ch.Visitor().Visit(node)` — the raw visit callback (no SyntaxList lift).
#[inline]
pub(crate) fn visit(
    v: &NodeVisitor<'_>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    v.visit.as_ref().and_then(|f| f(v, cx, node))
}

/// `ch.Visitor().VisitNode(node)` on a non-Option child.
#[inline]
pub(crate) fn visit_node(
    v: &NodeVisitor<'_>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    v.visit_node(cx, Some(node))
}

/// `ch.Visitor().VisitNodes(list)` — Go returns `*NodeList`; `None` input
/// yields `None`.
#[inline]
pub(crate) fn visit_nodes(
    v: &NodeVisitor<'_>,
    cx: &mut VisitorCx<'_, '_>,
    nodes: Option<tsc_ast::NodeList>,
) -> Option<tsc_ast::NodeList> {
    v.visit_nodes(cx, nodes)
}

/// Builds a short-lived `Transformer` that shares `ec` and whose visitor
/// delegates to `v` — the stand-in for `&ch.Transformer` passed to
/// `FlattenDestructuring{Assignment,Binding}` (which only ever touches
/// `tx.EmitContext()` and `tx.Visitor()`).
///
/// PORT: the adapter's own visit callback forwards `visit_node` to `v`,
/// which is exactly what Go's flattener does through the real transformer's
/// visitor (it invokes `tx.Visitor().VisitNode`).
pub(crate) fn tx_adapter<'v, 'a>(v: &'v NodeVisitor<'a>, ec: &Ec) -> Transformer<'v> {
    Transformer::new(
        Box::new(
            move |_v2: &NodeVisitor<'v>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                v.visit_node(cx, Some(node))
            },
        ),
        Some(ec.clone()),
    )
}

/// `ch.Visitor().VisitToken(token)` — no dedicated method in Go beyond
/// `VisitNode`; kept for parity with Go call sites that say `VisitToken`.
#[allow(dead_code)]
#[inline]
pub(crate) fn visit_token(
    v: &NodeVisitor<'_>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    v.visit_node(cx, Some(node))
}

/// `tx.EmitContext().VisitParameters(params, tx.Visitor())`.
///
/// PORT: `EmitContext::new_node_visitor` installs the environment-tracking
/// `visit_parameters` hook on every visitor it builds; the hook closure
/// already carries the emit context's `Shared` state, so invoking it
/// directly is identical to Go's `EmitContext` method (which calls
/// `visitor.VisitNodes` under a pushed variable environment). Calling the
/// `&mut self` `EmitContext` method through `ec.borrow_mut()` would hold
/// the `RefCell` borrow across the nested visit and panic.
#[inline]
pub(crate) fn ec_visit_parameters(
    v: &NodeVisitor<'_>,
    cx: &mut VisitorCx<'_, '_>,
    nodes: Option<tsc_ast::NodeList>,
) -> Option<tsc_ast::NodeList> {
    match &v.hooks.visit_parameters {
        Some(hook) => hook(cx, nodes, v),
        None => v.visit_nodes(cx, nodes),
    }
}

/// `tx.EmitContext().VisitFunctionBody(body, tx.Visitor())` — see
/// [`ec_visit_parameters`] for why the hook is invoked directly.
#[inline]
pub(crate) fn ec_visit_function_body(
    v: &NodeVisitor<'_>,
    cx: &mut VisitorCx<'_, '_>,
    node: Option<NodeId>,
) -> Option<NodeId> {
    let node = node?;
    match &v.hooks.visit_function_body {
        Some(hook) => hook(cx, node, v),
        None => v.visit_node(cx, Some(node)),
    }
}

/// `tx.EmitContext().VisitIterationBody(body, tx.Visitor())` — see
/// [`ec_visit_parameters`]. The no-hook fallback mirrors the unhooked
/// `visit_embedded_statement` (the `visit_node`-hook intermediate case is
/// only reachable when a `visit_node` hook is set, which these transforms
/// never do).
#[inline]
pub(crate) fn ec_visit_iteration_body(
    v: &NodeVisitor<'_>,
    cx: &mut VisitorCx<'_, '_>,
    node: Option<NodeId>,
) -> Option<NodeId> {
    let node = node?;
    match &v.hooks.visit_iteration_body {
        Some(hook) => hook(cx, node, v),
        None => match &v.hooks.visit_embedded_statement {
            Some(hook) => hook(cx, node, v),
            None => v.visit_embedded_statement(cx, Some(node)),
        },
    }
}

/// `tx.EmitContext().VisitVariableEnvironment(statements, tx.Visitor())` —
/// see [`ec_visit_parameters`].
#[inline]
pub(crate) fn ec_visit_variable_environment(
    v: &NodeVisitor<'_>,
    cx: &mut VisitorCx<'_, '_>,
    nodes: Option<tsc_ast::NodeList>,
) -> Option<tsc_ast::NodeList> {
    match &v.hooks.visit_top_level_statements {
        Some(hook) => hook(cx, nodes, v),
        None => v.visit_nodes(cx, nodes),
    }
}

/// `subtree_facts` shorthand mirroring `node.SubtreeFacts()`.
#[inline]
pub(crate) fn subtree_facts(cx: &VisitorCx<'_, '_>, node: NodeId) -> tsc_ast::SubtreeFacts {
    cx.nodes[node].subtree_facts(cx.nodes)
}

/// `node.Flags` shorthand.
#[inline]
pub(crate) fn node_flags(cx: &VisitorCx<'_, '_>, node: NodeId) -> tsc_ast::NodeFlags {
    cx.nodes[node].flags
}
