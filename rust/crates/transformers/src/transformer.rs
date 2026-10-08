// Ported from tsc/internal/transformers/transformer.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The `Transformer` bundle: an `EmitContext`, its `NodeFactory`, and the
// `NodeVisitor` that drives a transform over a `SourceFile`.
//
// PORT: In Go, `Transformer` stores `emitContext`, `factory` (which *is*
// `emitContext.Factory`), and `visitor`, and visit callbacks reach all three
// through the transformer receiver. In this port the visitor threads
// `cx.factory` — a `&mut ast::NodeFactory` — through every callback instead.
// Borrowing `emit_context.factory` for the whole visit would make the
// `EmitContext` unreachable inside callbacks (any `borrow()` would panic
// against the outstanding `borrow_mut`), so:
//
//   - `emit_context` lives in `Rc<RefCell<EmitContext>>`, shared with the
//     chain/options just as Go shares `opt.Context`, and every
//     `tx.Factory()`/`tx.EmitContext()` call inside a visit goes through
//     short-lived `borrow()`/`borrow_mut()` scopes.
//   - `Transformer` owns a *second* `ast::NodeFactory`
//     (`new_transform_factory`) used purely as `cx.factory` for the visitor
//     machinery (`visit_each_child` rebuilds, `visit_nodes`/`lift_to_block`
//     list construction). Its hooks are semantically identical to the emit
//     context's own factory hooks (`onCreate` → `SYNTHESIZED`,
//     `onUpdate`/`onClone` → `SetOriginalEx`); the only gap is `onClone`'s
//     `autoGenerate` copy — see `new_transform_factory`.
//
// Explicit `tx.Factory().New*` calls in transform code should prefer
// `emit_context.borrow_mut().factory` (the real printer factory, real hooks)
// over `cx.factory`.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{self as ast, Node, NodeFactoryHooks, NodeId};
use tsc_printer::EmitContext;

/// Builds the `ast::NodeFactory` that serves as `cx.factory` while a
/// transform's visitor runs (see the `Transformer` docs). Its hooks mirror
/// `EmitContext::new`'s factory hooks via the public `EmitContext` API.
fn new_transform_factory(emit_context: &Rc<RefCell<EmitContext>>) -> ast::NodeFactory<'static> {
    // `Weak` avoids a reference cycle: Transformer -> factory -> hooks ->
    // Rc<RefCell<EmitContext>> -> Transformer.
    let update_weak = Rc::downgrade(emit_context);
    let clone_weak = update_weak.clone();
    ast::NodeFactory::new(NodeFactoryHooks {
        // `(c *EmitContext) onCreate`
        on_create: Some(Box::new(|nodes: &mut Vec<Node>, node: NodeId| {
            nodes[node].flags |= ast::NodeFlags::SYNTHESIZED;
        })),
        // `(c *EmitContext) onUpdate` — `set_original_shared(shared, updated,
        // original, false)`, which `EmitContext::set_original_ex` calls
        // verbatim.
        on_update: Some(Box::new(
            move |_nodes: &mut Vec<Node>, updated: NodeId, original: NodeId| {
                if let Some(ctx) = update_weak.upgrade() {
                    ctx.borrow().set_original_ex(updated, original, false);
                }
            },
        )),
        // `(c *EmitContext) onClone`
        on_clone: Some(Box::new(
            move |_nodes: &mut Vec<Node>, updated: NodeId, original: NodeId| {
                let Some(ctx) = clone_weak.upgrade() else {
                    return;
                };
                ctx.borrow().set_original_ex(updated, original, false);
                // PORT(deferred): Go's onClone additionally copies the
                // `autoGenerate` entry for identifiers/private identifiers so
                // that clones of generated names keep regenerating. The
                // `auto_generate` table lives in `EmitContextShared`, which
                // is `pub(crate)` to tsc-printer, so this port cannot copy
                // the entry here. Transforms that clone generated identifiers
                // should route `clone_node` through
                // `emit_context.borrow_mut().factory` instead — the real
                // factory's onClone hook does copy the entry.
            },
        )),
    })
}

/// `type Transformer struct`.
pub struct Transformer<'a> {
    /// `emitContext *printer.EmitContext` — shared ownership, mirroring Go's
    /// pointer (a `Chain` shares one context across all components).
    emit_context: Rc<RefCell<EmitContext>>,
    /// `visitor *ast.NodeVisitor`
    visitor: NodeVisitor<'a>,
    /// The `cx.factory` used while a visit runs — the hooks-equivalent
    /// stand-in for `emit_context.factory` described above. `RefCell` so
    /// `transform_source_file` can take `&self` (chained components are
    /// shared through `Rc` inside the visit closure).
    factory: RefCell<ast::NodeFactory<'static>>,
}

impl<'a> Transformer<'a> {
    /// `(*Transformer).NewTransformer(visit, emitContext)` — initializes the
    /// transformer, creating a fresh `EmitContext` when `emit_context` is
    /// `None` (Go nil).
    ///
    /// PORT: Go panics when `NewTransformer` is called on an already
    /// initialized transformer; the Rust constructor cannot be misused that
    /// way, so that check has no counterpart.
    pub fn new(
        visit: Box<VisitFn<'a>>,
        emit_context: Option<Rc<RefCell<EmitContext>>>,
    ) -> Transformer<'a> {
        let emit_context =
            emit_context.unwrap_or_else(|| Rc::new(RefCell::new(EmitContext::new())));
        let visitor = emit_context.borrow().new_node_visitor(visit);
        let factory = RefCell::new(new_transform_factory(&emit_context));
        Transformer {
            emit_context,
            visitor,
            factory,
        }
    }

    /// `tx.EmitContext()`
    pub fn emit_context(&self) -> &Rc<RefCell<EmitContext>> {
        &self.emit_context
    }

    /// `tx.Visitor()`
    pub fn visitor(&self) -> &NodeVisitor<'a> {
        &self.visitor
    }

    /// `tx.Factory()` — runs `f` against the `printer::NodeFactory` owned by
    /// the emit context (the real, emit-context-hooked factory). Do not call
    /// while a `borrow`/`borrow_mut` of `emit_context()` is still alive.
    pub fn with_factory<R>(&self, f: impl FnOnce(&mut tsc_printer::NodeFactory) -> R) -> R {
        let mut ctx = self.emit_context.borrow_mut();
        f(&mut ctx.factory)
    }

    /// Runs `f` with a `VisitorCx` whose factory is this transformer's own
    /// transform factory — the `cx.factory` the visitor machinery uses for
    /// `visit_each_child` rebuilds and list reconstruction.
    pub fn with_visit_cx<R>(
        &self,
        nodes: &mut Vec<Node>,
        f: impl for<'cx> FnOnce(&mut VisitorCx<'cx, 'static>) -> R,
    ) -> R {
        let mut factory = self.factory.borrow_mut();
        let mut cx = VisitorCx::new(nodes, &mut factory);
        f(&mut cx)
    }

    /// `tx.TransformSourceFile(file)` — runs the visitor over `file`,
    /// returning the transformed `SourceFile` node.
    ///
    /// PORT: `NodeId` packs the owning file's index into its high bits (a
    /// Rust arena detail Go doesn't have). Both factories are synced to the
    /// file being transformed so nodes minted during the visit index into
    /// its arena.
    pub fn transform_source_file(&self, nodes: &mut Vec<Node>, file: NodeId) -> Option<NodeId> {
        let file_index = nodes[file].id.file_index();
        self.factory.borrow_mut().set_file_index(file_index);
        self.emit_context
            .borrow_mut()
            .factory
            .set_file_index(file_index);
        self.with_visit_cx(nodes, |cx| self.visitor.visit_source_file(cx, file))
    }
}
