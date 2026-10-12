// Ported from tsc/internal/checker/nodecopy.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — existing-AST-node reuse for the
// node builder (`reuseNode`, `tryReuseExistingNodeHelper`, the recovery
// boundary, `wrappingTracker`, and `getExistingNodeTreeVisitor`).
//
// PORT notes:
//
// - Go's `getExistingNodeTreeVisitor` returns an `*ast.NodeVisitor` whose
//   visit callback captures `b`, `bound`, and `visitor` itself. In this port
//   `VisitFn` is `Fn` (not `FnMut`) and `VisitorCx` already holds the arena,
//   so `b`/`c` reach the visit fn through `RefCell<&mut ...>` fields on
//   `ExistingNodeTreeState` (same pattern as `CloneBindingShared` in
//   nodebuilderimpl.rs). Borrows are scoped per statement — a borrow must
//   never be held across a `v.visit_*` call, since those re-enter the visit
//   fn and would double-borrow.
// - `VisitorCx.factory` receives a *fresh* factory built by
//   `new_nodebuilder_factory` (with `file_index` copied over) rather than
//   `&mut b.f`, because `b` is borrowed by the shared state for the duration
//   of the visit. The fresh factory has identical hooks (they weak-upgrade
//   the same `EmitContext`); only the internal `node_count`/`identifier_count`
//   counters diverge from Go, where the visitor shares `b.f`.
// - `deferredReports []func()` → `Vec<Box<dyn FnMut(&[ast::Node])>>` — the
//   port's `SymbolTracker` methods take the arena slice, so deferred reports
//   are invoked with the destination arena in `finalize_boundary`.
// - `node == nil` inputs → `Option<NodeId>`; `TypeNode` inputs stay `NodeId`
//   where callers always pass a real node.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::{self as ast, Kind, NodeId, NodeList, SymbolFlags, SymbolId};
use tsc_core::text::TextRange;
use tsc_nodebuilder as nodebuilder;
use tsc_printer::{self as printer};

use crate::checker_core::Checker;
use crate::mapper::get_mapped_type;
use crate::nodebuilderimpl::{
    NodeBuilderImpl, PropertyNameNodeKind, TrackedSymbolArgs, classify_property_name,
    new_nodebuilder_factory,
};
use crate::symboltracker::new_symbol_tracker_impl;
use crate::types::{TypeFlags, TypeId};

// ----------------------------------------------------------------------------
// reuseNode / reuseName / reuseTypeNode entry points.
// ----------------------------------------------------------------------------

impl<'a> NodeBuilderImpl<'a> {
    /// `(b *NodeBuilderImpl) reuseNode` (nodecopy.go).
    pub(crate) fn reuse_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        node: NodeId,
    ) -> Option<NodeId> {
        self.try_reuse_existing_node_helper(c, nodes, node)
    }

    /// `(b *NodeBuilderImpl) tryJSTypeNodeToTypeNode` (nodecopy.go).
    pub(crate) fn try_js_type_node_to_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        node: NodeId,
    ) -> Option<NodeId> {
        self.reuse_node(c, nodes, node)
    }

    /// `(b *NodeBuilderImpl) reuseName` (nodecopy.go).
    pub(crate) fn reuse_name(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        node: Option<NodeId>,
        is_method: bool,
    ) -> Option<NodeId> {
        let res = node.and_then(|node| self.reuse_node(c, nodes, node))?;

        let ((text, _had_text), is_string_literal) = {
            let __program = c.program.clone().expect("program");
            let n_nodes = crate::printer_util::arena_view(&__program, nodes, (res).file_index());
            (
                ast::try_get_text_of_property_name(res, &n_nodes),
                ast::is_string_literal(&n_nodes[res]),
            )
        };
        let Some(text) = text else {
            return Some(res);
        };

        let kind = classify_property_name(&text, is_string_literal, is_method);
        let res_kind = {
            let __program = c.program.clone().expect("program");
            let n_nodes = crate::printer_util::arena_view(&__program, nodes, (res).file_index());
            n_nodes[res].kind
        };
        if res_kind == Kind::Identifier && kind == PropertyNameNodeKind::Identifier {
            return Some(res);
        }
        if is_string_literal && kind == PropertyNameNodeKind::StringLiteral {
            return Some(res);
        }

        let renamed = match kind {
            PropertyNameNodeKind::Identifier => self.new_identifier(nodes, &text, None),
            PropertyNameNodeKind::StringLiteral => {
                self.f
                    .new_string_literal(nodes, &text, ast::TokenFlags::NONE)
            }
            _ => return Some(res),
        };
        self.e.borrow().set_original(renamed, res);
        self.set_text_range(c, nodes, Some(renamed), Some(res))
    }

    /// `(b *NodeBuilderImpl) reuseTypeNode` (nodecopy.go).
    pub(crate) fn reuse_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        let node = node?;
        if let Some(r) = self.reuse_node(c, nodes, node) {
            // After successful reuse during hover, probe the reused AST for
            // expandable type references so canIncreaseExpansionDepth is set
            // even though typeToTypeNode (and shouldExpandType) were never
            // called.
            if self.ctx.max_expansion_depth >= 0 && !self.ctx.can_increase_expansion_depth {
                self.walk_node_for_expandability(c, nodes, node);
            }
            return Some(r);
        }
        if let Some(tracker) = self.ctx.tracker.clone() {
            tracker.borrow_mut().report_inference_fallback(node, nodes);
        }
        let t = self.get_type_from_type_node(c, node, false, nodes);
        self.type_to_type_node_opt(c, nodes, t)
    }

    /// `(b *NodeBuilderImpl) walkNodeForExpandability` (nodecopy.go) — walks
    /// a reused AST node tree, calling `checkTypeExpandability` on each type
    /// reference, type predicate, or import type node. Short-circuits once
    /// `canIncreaseExpansionDepth` is set.
    fn walk_node_for_expandability(&mut self, c: &mut Checker, nodes: &[ast::Node], node: NodeId) {
        if self.ctx.can_increase_expansion_depth {
            return;
        }
        // Check these explicitly so we look into type arguments whether or
        // not they are in the tree.
        {
            let __program = c.program.clone().expect("program");
            let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
            let n = &nn[node];
            if ast::is_type_reference_node(n)
                || ast::is_expression_with_type_arguments(n)
                || ast::is_type_predicate_node(n)
                || ast::is_import_type_node(n)
            {
                let _ = n;
                drop(nn);
                if let Some(t) = self.get_type_from_type_node(c, node, false, nodes) {
                    self.check_type_expandability(c, Some(t));
                    if self.ctx.can_increase_expansion_depth {
                        return;
                    }
                }
            }
        }
        let __program = c.program.clone().expect("program");
        let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
        let mut children: Vec<NodeId> = Vec::new();
        nn[node].for_each_child(&nn, &mut |child| {
            children.push(child);
            false
        });
        drop(nn);
        for child in children {
            if self.ctx.can_increase_expansion_depth {
                return;
            }
            self.walk_node_for_expandability(c, nodes, child);
        }
    }
}

// ----------------------------------------------------------------------------
// recoveryBoundary / wrappingTracker (nodecopy.go).
// ----------------------------------------------------------------------------

/// `type recoveryBoundary struct` (nodecopy.go).
pub(crate) struct RecoveryBoundary<'a> {
    /// `hadError`.
    pub had_error: bool,
    /// `deferredReports` — `[]func()` → report closures taking the arena.
    pub deferred_reports: Vec<Box<dyn FnMut(&[ast::Node]) + 'a>>,
    /// `oldTracker`.
    pub old_tracker: Option<Rc<RefCell<dyn nodebuilder::SymbolTracker + 'a>>>,
    /// `oldTrackedSymbols`.
    pub old_tracked_symbols: Vec<TrackedSymbolArgs>,
    /// `trackedSymbols`.
    pub tracked_symbols: Vec<TrackedSymbolArgs>,
    /// `oldEncounteredError`.
    pub old_encountered_error: bool,
    /// `oldApproximateLength`.
    pub old_approximate_length: i32,
}

impl<'a> RecoveryBoundary<'a> {
    /// `(b *recoveryBoundary) markError` (nodecopy.go).
    fn mark_error(&mut self, f: Option<Box<dyn FnMut(&[ast::Node]) + 'a>>) {
        self.had_error = true;
        if let Some(f) = f {
            self.deferred_reports.push(f);
        }
    }
}

/// `type originalRecoveryScopeState struct` (nodecopy.go).
struct OriginalRecoveryScopeState {
    tracked_symbols_top: usize,
    unreported_errors_top: usize,
    had_error: bool,
}

/// `type wrappingTracker struct` (nodecopy.go) — a `SymbolTracker` that
/// defers error reports through the `RecoveryBoundary` so failed reuse
/// attempts can roll them back.
struct WrappingTracker<'a> {
    /// `wrapped`.
    wrapped: Option<Rc<RefCell<dyn nodebuilder::SymbolTracker + 'a>>>,
    /// `bound`.
    bound: Rc<RefCell<RecoveryBoundary<'a>>>,
}

impl<'a> nodebuilder::SymbolTracker for WrappingTracker<'a> {
    /// `(w *wrappingTracker) PopErrorFallbackNode`.
    fn pop_error_fallback_node(&mut self) {
        if let Some(w) = self.wrapped.clone() {
            w.borrow_mut().pop_error_fallback_node();
        }
    }

    /// `(w *wrappingTracker) PushErrorFallbackNode`.
    fn push_error_fallback_node(&mut self, node: NodeId) {
        if let Some(w) = self.wrapped.clone() {
            w.borrow_mut().push_error_fallback_node(node);
        }
    }

    /// `(w *wrappingTracker) ReportCyclicStructureError`.
    fn report_cyclic_structure_error(&mut self, _nodes: &[ast::Node]) {
        let wrapped = self.wrapped.clone();
        self.bound
            .borrow_mut()
            .mark_error(Some(Box::new(move |nodes| {
                if let Some(w) = &wrapped {
                    w.borrow_mut().report_cyclic_structure_error(nodes);
                }
            })));
    }

    /// `(w *wrappingTracker) ReportInaccessibleThisError`.
    fn report_inaccessible_this_error(&mut self, _nodes: &[ast::Node]) {
        let wrapped = self.wrapped.clone();
        self.bound
            .borrow_mut()
            .mark_error(Some(Box::new(move |nodes| {
                if let Some(w) = &wrapped {
                    w.borrow_mut().report_inaccessible_this_error(nodes);
                }
            })));
    }

    /// `(w *wrappingTracker) ReportInaccessibleUniqueSymbolError`.
    fn report_inaccessible_unique_symbol_error(&mut self, _nodes: &[ast::Node]) {
        let wrapped = self.wrapped.clone();
        self.bound
            .borrow_mut()
            .mark_error(Some(Box::new(move |nodes| {
                if let Some(w) = &wrapped {
                    w.borrow_mut()
                        .report_inaccessible_unique_symbol_error(nodes);
                }
            })));
    }

    /// `(w *wrappingTracker) ReportInferenceFallback` — should this also be
    /// deferred? (mirrors the Go comment)
    fn report_inference_fallback(&mut self, node: NodeId, nodes: &[ast::Node]) {
        if let Some(w) = self.wrapped.clone() {
            w.borrow_mut().report_inference_fallback(node, nodes);
        }
    }

    /// `(w *wrappingTracker) ReportLikelyUnsafeImportRequiredError`.
    fn report_likely_unsafe_import_required_error(
        &mut self,
        specifier: &str,
        symbol_name: &str,
        _nodes: &[ast::Node],
    ) {
        let wrapped = self.wrapped.clone();
        let specifier = specifier.to_owned();
        let symbol_name = symbol_name.to_owned();
        self.bound
            .borrow_mut()
            .mark_error(Some(Box::new(move |nodes| {
                if let Some(w) = &wrapped {
                    w.borrow_mut().report_likely_unsafe_import_required_error(
                        &specifier,
                        &symbol_name,
                        nodes,
                    );
                }
            })));
    }

    /// `(w *wrappingTracker) ReportNonSerializableProperty`.
    fn report_non_serializable_property(&mut self, property_name: &str, _nodes: &[ast::Node]) {
        let wrapped = self.wrapped.clone();
        let property_name = property_name.to_owned();
        self.bound
            .borrow_mut()
            .mark_error(Some(Box::new(move |nodes| {
                if let Some(w) = &wrapped {
                    w.borrow_mut()
                        .report_non_serializable_property(&property_name, nodes);
                }
            })));
    }

    /// `(w *wrappingTracker) ReportNonlocalAugmentation` — should this also
    /// be deferred? (mirrors the Go comment)
    fn report_nonlocal_augmentation(
        &mut self,
        containing_file: NodeId,
        parent_symbol: SymbolId,
        augmenting_symbol: SymbolId,
        nodes: &[ast::Node],
    ) {
        if let Some(w) = self.wrapped.clone() {
            w.borrow_mut().report_nonlocal_augmentation(
                containing_file,
                parent_symbol,
                augmenting_symbol,
                nodes,
            );
        }
    }

    /// `(w *wrappingTracker) ReportPrivateInBaseOfClassExpression`.
    fn report_private_in_base_of_class_expression(
        &mut self,
        property_name: &str,
        _nodes: &[ast::Node],
    ) {
        let wrapped = self.wrapped.clone();
        let property_name = property_name.to_owned();
        self.bound
            .borrow_mut()
            .mark_error(Some(Box::new(move |nodes| {
                if let Some(w) = &wrapped {
                    w.borrow_mut()
                        .report_private_in_base_of_class_expression(&property_name, nodes);
                }
            })));
    }

    /// `(w *wrappingTracker) ReportTruncationError` — should this also be
    /// deferred? (mirrors the Go comment)
    fn report_truncation_error(&mut self, nodes: &[ast::Node]) {
        if let Some(w) = self.wrapped.clone() {
            w.borrow_mut().report_truncation_error(nodes);
        }
    }

    /// `(w *wrappingTracker) TrackSymbol` — records into
    /// `bound.trackedSymbols` and returns `false` so the outer
    /// `SymbolTrackerImpl` records into `ctx.tracked_symbols` too.
    fn track_symbol(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
        _nodes: &[ast::Node],
        _is_symbol_accessible: &mut nodebuilder::IsSymbolAccessible<'_>,
    ) -> bool {
        self.bound
            .borrow_mut()
            .tracked_symbols
            .push(TrackedSymbolArgs {
                symbol,
                enclosing_declaration,
                meaning,
            });
        false
    }
}

impl<'a> NodeBuilderImpl<'a> {
    /// `(b *NodeBuilderImpl) createRecoveryBoundary` (nodecopy.go).
    fn create_recovery_boundary(
        &mut self,
        c: &mut Checker,
    ) -> Rc<RefCell<RecoveryBoundary<'a>>> {
        c.check_not_canceled();
        let bound = Rc::new(RefCell::new(RecoveryBoundary {
            had_error: false,
            deferred_reports: Vec::new(),
            old_tracker: self.ctx.tracker.clone(),
            old_tracked_symbols: self.ctx.tracked_symbols.borrow().clone(),
            tracked_symbols: Vec::new(),
            old_encountered_error: self.ctx.encountered_error,
            old_approximate_length: self.ctx.approximate_length,
        }));
        let wrapping = WrappingTracker {
            wrapped: self.ctx.tracker.clone(),
            bound: bound.clone(),
        };
        let wrapping: Rc<RefCell<dyn nodebuilder::SymbolTracker + 'a>> =
            Rc::new(RefCell::new(wrapping));
        let new_tracker =
            new_symbol_tracker_impl(&self.ctx, Some(wrapping), c.symbol_arena.clone());
        self.ctx.tracker = Some(Rc::new(RefCell::new(new_tracker)));
        self.ctx.tracked_symbols.borrow_mut().clear();
        bound
    }

    /// `(b *NodeBuilderImpl) finalizeBoundary` (nodecopy.go).
    ///
    /// `diag_nodes`: the arena the tracked-symbol diagnostics resolve through.
    /// Usually the same buffer as `nodes`; in the foreign-arena scratch path it
    /// is the destination (emit) buffer, because the ids handed to
    /// `track_symbol`/`handle_symbol_accessibility_error` — enclosing
    /// declarations, captured diagnostic-context nodes — were minted there.
    fn finalize_boundary(
        &mut self,
        c: &mut Checker,
        bound: &Rc<RefCell<RecoveryBoundary<'a>>>,
        nodes: &mut Vec<ast::Node>,
        diag_nodes: Option<&[ast::Node]>,
    ) -> bool {
        let (old_tracker, old_tracked, old_encountered_error, old_approximate_length, had_error) = {
            let b = bound.borrow();
            (
                b.old_tracker.clone(),
                b.old_tracked_symbols.clone(),
                b.old_encountered_error,
                b.old_approximate_length,
                b.had_error,
            )
        };
        self.ctx.tracker = old_tracker;
        *self.ctx.tracked_symbols.borrow_mut() = old_tracked;
        self.ctx.encountered_error = old_encountered_error;
        self.ctx.approximate_length = old_approximate_length;

        // Tracked-symbol replays and deferred reports carry ids minted in
        // either the working buffer (`nodes` — a scratch clone in the
        // foreign-arena path) or the destination buffer (`diag_nodes`).
        // Register both so `resolve_arena_for` can find ids in either space
        // no matter which `nodes_view` a nested call receives. Domestic
        // calls skip this: `nodes` is already the view every nested call
        // resolves against.
        let _g_nodes;
        let _g_diag;
        if diag_nodes.is_some() {
            _g_nodes = Some(crate::printer_util::LiveArenaGuard::register(nodes));
            _g_diag = diag_nodes.map(crate::printer_util::LiveArenaGuard::register);
        } else {
            _g_nodes = None;
            _g_diag = None;
        }
        let mut reports = std::mem::take(&mut bound.borrow_mut().deferred_reports);
        for f in reports.iter_mut() {
            f(nodes);
        }
        if had_error {
            return false;
        }
        let tracked = std::mem::take(&mut bound.borrow_mut().tracked_symbols);
        for a in tracked {
            if let Some(tracker) = self.ctx.tracker.clone() {
                let nodes_view: &[ast::Node] = diag_nodes.unwrap_or(nodes);
                tracker.borrow_mut().track_symbol(
                    a.symbol,
                    a.enclosing_declaration,
                    a.meaning,
                    nodes_view,
                    &mut |sym, en, mn, sc| {
                        c.is_symbol_accessible(sym, en, mn, sc, Some(nodes_view))
                    },
                );
            }
        }
        true
    }

    /// `(b *recoveryBoundary) startRecoveryScope` — free fn on the context's
    /// tracked-symbols cell (Go reaches `b.ctx` through `bound.ctx`).
    fn start_recovery_scope(
        ctx_tracked: &Rc<RefCell<Vec<TrackedSymbolArgs>>>,
        bound: &Rc<RefCell<RecoveryBoundary<'a>>>,
    ) -> OriginalRecoveryScopeState {
        let b = bound.borrow();
        OriginalRecoveryScopeState {
            tracked_symbols_top: ctx_tracked.borrow().len(),
            unreported_errors_top: b.deferred_reports.len(),
            had_error: b.had_error,
        }
    }

    /// `(b *recoveryBoundary) endRecoveryScope` (nodecopy.go).
    fn end_recovery_scope(
        ctx_tracked: &Rc<RefCell<Vec<TrackedSymbolArgs>>>,
        bound: &Rc<RefCell<RecoveryBoundary<'a>>>,
        state: OriginalRecoveryScopeState,
    ) {
        let mut b = bound.borrow_mut();
        b.had_error = state.had_error;
        ctx_tracked.borrow_mut().truncate(state.tracked_symbols_top);
        b.deferred_reports.truncate(state.unreported_errors_top);
    }

    /// `(b *NodeBuilderImpl) tryReuseExistingNodeHelper` (nodecopy.go).
    pub(crate) fn try_reuse_existing_node_helper(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        existing: NodeId,
    ) -> Option<NodeId> {
        if existing.file_index() != self.f.file_index() {
            // `existing` lives in another file's arena — the visitor must
            // read it there while appending results into `nodes`. Run the
            // visit on a scratch clone of the source arena (a `borrow()`
            // clone, since checker ancestors may hold `Ref`s on it), pad
            // it so scratch-minted ids can't alias real `nodes` ids in the
            // emit tables, then relocate the produced tail.
            let program = c.program.clone().expect("program");
            let mut src = program.nodes(existing.file_index()).to_vec();
            if src.len() < nodes.len() {
                let filler = src[0].clone();
                src.resize(nodes.len(), filler);
            }
            let tmp_base = src.len();
            let dest_base = nodes.len();
            // Mint scratch clones with the SOURCE file index: a node's
            // `file_index` names the buffer it lives in, and `arena_view`
            // reads inside the visit must resolve to `src` itself.
            let src_fi = existing.file_index();
            let saved_fi = self.f.file_index();
            self.f.set_file_index(src_fi);
            // `type_parameter_names` caches minted `NodeId`s — they are only
            // valid in the buffer they were minted into. Give the scratch
            // arena its own epoch so cached ids are recomputed here.
            let next_epoch = self.ctx.epoch_counter.get() + 1;
            self.ctx.epoch_counter.set(next_epoch);
            let saved_epoch = self.ctx.nodes_epoch.replace(next_epoch);
            let root = {
                // While the visit runs on `src`, nested checker reads may
                // hit ids in the destination buffer (`nodes`) — register it
                // so `arena_view` resolves them live instead of snapshotting.
                let live = nodes.as_slice();
                let _live_guard = crate::printer_util::LiveArenaGuard::register(live);
                self.try_reuse_existing_node_helper_in_arena(c, &mut src, existing, Some(live))
            };
            self.f.set_file_index(saved_fi);
            self.ctx.nodes_epoch.set(saved_epoch);
            let root = root?;
            return Some(self.relocate_cloned_tail(nodes, &mut src, tmp_base, dest_base, root, src_fi));
        }
        self.try_reuse_existing_node_helper_in_arena(c, nodes, existing, None)
    }

    /// The body of Go's `tryReuseExistingNodeHelper` running inside `nodes`
    /// (either the dest arena or a scratch clone of a foreign source arena).
    fn try_reuse_existing_node_helper_in_arena(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        existing: NodeId,
        extra_live: Option<&[ast::Node]>,
    ) -> Option<NodeId> {
        // The visitor's `cx.factory` cannot alias `b.f` (b is behind the
        // RefCell for the whole visit), so give it an equivalent fresh
        // factory — see the file header. Must be built before `self` is
        // borrowed into `shared`.
        let mut factory = new_nodebuilder_factory(&self.e);
        factory.set_file_index(self.f.file_index());
        let bound = self.create_recovery_boundary(c);
        // `var visitor *ast.NodeVisitor` — built per call; the shared state
        // carries `b`/`c` through cells for the `Fn` visit callback.
        let shared = Rc::new(ExistingNodeTreeState {
            b: RefCell::new(&mut *self),
            c: RefCell::new(&mut *c),
            bound: bound.clone(),
            non_local_node: Cell::new(true),
            extra_live,
        });
        let visitor = get_existing_node_tree_visitor(shared.clone());
        let transformed = {
            let mut cx = ast::VisitorCx::new(nodes, &mut factory);
            visitor.visit_node(&mut cx, Some(existing))
        };
        drop(visitor);
        drop(shared);
        if !self.finalize_boundary(c, &bound, nodes, extra_live) {
            return None;
        }
        {
            let __program = c.program.clone().expect("program");
            let nn = crate::printer_util::arena_view(&__program, nodes, (existing).file_index());
            self.ctx.approximate_length += nn[existing].loc.end() - nn[existing].loc.pos();
        }
        transformed
    }

    /// `(b *NodeBuilderImpl) getModuleSpecifierOverride` (nodecopy.go).
    pub(crate) fn get_module_specifier_override(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        parent: NodeId,
        lit: NodeId,
    ) -> Option<String> {
        let (same_file, attributes, is_type_of) = {
            let __program = c.program.clone().expect("program");
            let nn = crate::printer_util::arena_view(&__program, nodes, (lit).file_index());
            let lit_file = ast::get_source_file_of_node(Some(lit), &nn);
            let __program = c.program.clone().expect("program");
            let pn = crate::printer_util::arena_view(&__program, nodes, (parent).file_index());
            let itn = pn[parent].as_import_type_node();
            (
                self.ctx.enclosing_file == lit_file,
                itn.attributes,
                itn.is_type_of,
            )
        };
        if !same_file {
            let mut mode = tsc_core::compileroptions::RESOLUTION_MODE_NONE;
            if attributes.is_some() {
                let (m, _) = ast::import_attributes_resolution_mode_override(
                    attributes,
                    None,
                    &c.program_nodes_live(parent, nodes),
                );
                mode = m;
            }
            let name = {
                let __program = c.program.clone().expect("program");
                let nn = crate::printer_util::arena_view(&__program, nodes, (lit).file_index());
                nn[lit].text(&nn).into_owned()
            };
            let original_name = name.clone();
            let node_symbol = self.try_get_resolved_symbol_from_type_node(c, Some(parent), nodes);
            let meaning = if is_type_of {
                SymbolFlags::VALUE
            } else {
                SymbolFlags::TYPE
            };
            let mut parent_symbol: Option<SymbolId> = None;
            if node_symbol.is_some()
                && c.is_symbol_accessible(
                    node_symbol,
                    self.ctx.enclosing_declaration,
                    meaning,
                    false,
                    Some(nodes.as_slice()),
                )
                .accessibility
                    == printer::SymbolAccessibility::Accessible
            {
                parent_symbol = self
                    .lookup_symbol_chain(c, nodes, node_symbol.unwrap(), meaning, true)
                    .first()
                    .copied();
            }
            let mut name = name;
            if parent_symbol.is_some_and(|s| c.sym(s).is_external_module()) {
                name = self
                    .get_specifier_for_module_symbol(c, nodes, parent_symbol.unwrap(), mode)
                    .specifier
                    .as_string()
                    .to_owned();
            } else {
                let target_file = c.get_external_module_file_from_declaration(parent);
                if let Some(target_file) = target_file {
                    let tf_sym = c.get_symbol_of_declaration(target_file);
                    if let Some(tf_sym) = tf_sym {
                        name = self
                            .get_specifier_for_module_symbol(c, nodes, tf_sym, mode)
                            .specifier
                            .as_string()
                            .to_owned();
                    }
                }
            }
            if !name.is_empty() && name.contains("/node_modules/") {
                self.ctx.encountered_error = true;
                if let Some(tracker) = self.ctx.tracker.clone() {
                    tracker
                        .borrow_mut()
                        .report_likely_unsafe_import_required_error(&name, "", nodes);
                }
            }
            if name != original_name {
                return Some(name);
            }
        }
        None
    }

    /// `(b *NodeBuilderImpl) rewriteModuleSpecifier` (nodecopy.go).
    pub(crate) fn rewrite_module_specifier(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        parent: NodeId,
        lit: NodeId,
    ) -> NodeId {
        let Some(new_name) = self.get_module_specifier_override(c, nodes, parent, lit) else {
            return lit;
        };
        let res = self
            .f
            .new_string_literal(nodes, &new_name, ast::TokenFlags::NONE);
        self.e.borrow().set_original(res, lit);
        res
    }

    /// `(b *NodeBuilderImpl) getEnclosingDeclarationIgnoringFakeScope`
    /// (nodecopy.go).
    pub(crate) fn get_enclosing_declaration_ignoring_fake_scope(
        &mut self,
        c: &mut Checker,
        nodes: &[ast::Node],
    ) -> Option<NodeId> {
        let mut enc = self.ctx.enclosing_declaration;
        while let Some(e) = enc {
            // Same NodeId-aliasing guard as `push_fake_scope`: a stale
            // fake-scope link is only trusted when the node in the live
            // buffer is actually a Block.
            if nodes
                .get(e.local_index() as usize)
                .is_some_and(|n| n.kind == ast::Kind::Block)
                && self
                    .links
                    .try_get(&e)
                    .is_some_and(|l| l.fake_scope_for_signature_declaration.is_some())
            {
                enc = c.program_nodes_live(e, nodes)[e].parent;
            } else {
                break;
            }
        }
        enc
    }
}

// ----------------------------------------------------------------------------
// getExistingNodeTreeVisitor (nodecopy.go).
// ----------------------------------------------------------------------------

/// Shared state captured by the `getExistingNodeTreeVisitor` callbacks —
/// the port's equivalent of Go's closure over `b`, `bound`, `nonLocalNode`,
/// and `visitor`. `b`/`c` are `RefCell`-wrapped because `VisitFn` is `Fn`;
/// borrows are scoped per statement and must never be held across
/// `v.visit_*` calls (those re-enter the visit fn).
struct ExistingNodeTreeState<'b, 'a, 'e> {
    /// `b`.
    b: RefCell<&'b mut NodeBuilderImpl<'a>>,
    /// `b.ch`.
    c: RefCell<&'b mut Checker>,
    /// `bound`.
    bound: Rc<RefCell<RecoveryBoundary<'a>>>,
    /// `nonLocalNode`.
    non_local_node: Cell<bool>,
    /// The destination arena buffer while the visit runs on a scratch
    /// clone of a foreign source arena (`try_reuse_existing_node_helper`'s
    /// `nodes`). Nested name resolution may walk node ids belonging to
    /// *either* live buffer (Go follows raw pointers), so both must be
    /// reachable — see [`live_nodes_for`]. Kept on a separate lifetime so
    /// the struct stays covariant over `'e`.
    extra_live: Option<&'e [ast::Node]>,
}

type NCShared<'b, 'a, 'e> = Rc<ExistingNodeTreeState<'b, 'a, 'e>>;

/// Pick the live working buffer that physically holds `id` — `cx.nodes`
/// (the visit arena, `src` in scratch mode) or `sh.extra_live` (the dest
/// buffer while the visit runs on a scratch clone). Falls back to
/// `cx.nodes`, which makes `arena_view` degrade to a snapshot exactly as
/// passing no live buffer would.
fn live_nodes_for<'x, 'e: 'x>(
    sh: &NCShared<'_, '_, 'e>,
    cx_nodes: &'x [ast::Node],
    id: Option<NodeId>,
) -> Option<&'x [ast::Node]> {
    let Some(fi) = id.map(|i| i.file_index()) else {
        return Some(cx_nodes);
    };
    if let Some(extra) = sh.extra_live
        && extra.first().is_some_and(|n| n.id.file_index() == fi)
        && !cx_nodes.first().is_some_and(|n| n.id.file_index() == fi)
    {
        return Some(extra);
    }
    Some(cx_nodes)
}

/// `b.ctx.tracker.ReportInferenceFallback(node)` — small helper that clones
/// the tracker `Rc` out from under the `b` borrow before calling.
fn nb_report_inference_fallback(
    sh: &ExistingNodeTreeState<'_, '_, '_>,
    nodes: &[ast::Node],
    node: NodeId,
) {
    let tracker = sh.b.borrow().ctx.tracker.clone();
    if let Some(tracker) = tracker {
        tracker.borrow_mut().report_inference_fallback(node, nodes);
    }
}

/// `b.setTextRange(node, location)`.
fn nb_set_text_range(
    sh: &ExistingNodeTreeState<'_, '_, '_>,
    nodes: &mut Vec<ast::Node>,
    node: Option<NodeId>,
    location: Option<NodeId>,
) -> Option<NodeId> {
    let mut b = sh.b.borrow_mut();
    let mut c = sh.c.borrow_mut();
    b.set_text_range(&mut **c, nodes, node, location)
}

/// `(b *recoveryBoundary) startRecoveryScope` — the `ctx` back-pointer is
/// supplied by `sh`.
fn nb_start_recovery_scope(sh: &ExistingNodeTreeState<'_, '_, '_>) -> OriginalRecoveryScopeState {
    let tracked = sh.b.borrow().ctx.tracked_symbols.clone();
    let bound = sh.bound.borrow();
    OriginalRecoveryScopeState {
        tracked_symbols_top: tracked.borrow().len(),
        unreported_errors_top: bound.deferred_reports.len(),
        had_error: bound.had_error,
    }
}

/// `(b *recoveryBoundary) endRecoveryScope`.
fn nb_end_recovery_scope(sh: &ExistingNodeTreeState<'_, '_, '_>, state: OriginalRecoveryScopeState) {
    let tracked = sh.b.borrow().ctx.tracked_symbols.clone();
    let mut bound = sh.bound.borrow_mut();
    bound.had_error = state.had_error;
    tracked.borrow_mut().truncate(state.tracked_symbols_top);
    bound.deferred_reports.truncate(state.unreported_errors_top);
}

/// `bound.markError(nil)` / `bound.markError(reportFn)` — Go's `func()`
/// deferred report needs no `nodes` argument there; the port's tracker
/// methods take `&[ast::Node]`, so deferred reports are stored as
/// `FnMut(&[ast::Node])` and invoked with the destination arena.
fn nb_mark_error(sh: &ExistingNodeTreeState<'_, '_, '_>) {
    sh.bound.borrow_mut().mark_error(None);
}

/// The `attachSymbolToLeftmostIdentifier` inner visit fn (nodecopy.go).
/// `node == leftmost` attaches `sym` (and renames type parameters renamed in
/// the current context); otherwise it recurses via `VisitEachChild`.
fn attach_symbol_visit(
    sh: &NCShared<'_, '_, '_>,
    v: &ast::NodeVisitor,
    cx: &mut ast::VisitorCx<'_, '_>,
    node: NodeId,
    leftmost: NodeId,
    sym: Option<SymbolId>,
) -> Option<NodeId> {
    if node == leftmost {
        let mut name: Option<NodeId> = None;
        if let Some(sym) = sym {
            let declared_type = sh.c.borrow_mut().get_declared_type_of_symbol(sym);
            if sh
                .c
                .borrow_mut()
                .sym(sym)
                .flags
                .intersects(SymbolFlags::TYPE_PARAMETER)
            {
                let mut b = sh.b.borrow_mut();
                let mut c = sh.c.borrow_mut();
                name = Some(b.type_parameter_to_name(&mut **c, cx.nodes, declared_type));
            }
        }
        let name = match name {
            Some(name) => name,
            None => {
                let text = {
                    let c = sh.c.borrow();
                    let __program = c.program.clone().expect("program");
                    let nn = crate::printer_util::arena_view(&__program, cx.nodes, (node).file_index());
                    nn[node].text(&nn).into_owned()
                };
                let m = sh.b.borrow_mut().new_identifier(cx.nodes, &text, sym);
                m
            }
        };
        let name = nb_set_text_range(sh, cx.nodes, Some(name), Some(node))?;
        sh.b.borrow()
            .e
            .borrow()
            .add_emit_flags(name, printer::EmitFlags::NO_ASCII_ESCAPING);
        return Some(name);
    }
    let visited = v.visit_each_child(cx, node).unwrap_or(node);
    nb_set_text_range(sh, cx.nodes, Some(visited), Some(node))
}

/// `attachSymbolToLeftmostIdentifier` (nodecopy.go).
fn attach_symbol_to_leftmost_identifier(
    sh: &NCShared<'_, '_, '_>,
    cx: &mut ast::VisitorCx<'_, '_>,
    leftmost: NodeId,
    node: NodeId,
    sym: Option<SymbolId>,
) -> Option<NodeId> {
    let sh2 = sh.clone();
    let vis = ast::NodeVisitor::new(
        Box::new(
            move |v: &ast::NodeVisitor, cx: &mut ast::VisitorCx<'_, '_>, n: NodeId| {
                attach_symbol_visit(&sh2, v, cx, n, leftmost, sym)
            },
        ),
        ast::NodeVisitorHooks::default(),
    );
    // Go calls `visitorFunc(node)` directly for the root (the inner visitor
    // is only used for `node.VisitEachChild(vis)` recursion).
    attach_symbol_visit(sh, &vis, cx, node, leftmost, sym)
}

/// `trackExistingEntityName` (nodecopy.go) — note: also handles renaming
/// type parameters renamed within the current context.
/// Returns `(introducesError, newNode, symbol)`.
fn track_existing_entity_name(
    sh: &NCShared<'_, '_, '_>,
    cx: &mut ast::VisitorCx<'_, '_>,
    node: NodeId,
    override_enclosing: Option<NodeId>,
) -> (bool, Option<NodeId>, Option<SymbolId>) {
    let enclosing_declaration = override_enclosing.or(sh.b.borrow().ctx.enclosing_declaration);
    let mut introduces_error = false;
    let (leftmost, js_exports_left) = {
        let c = sh.c.borrow();
        let __program = c.program.clone().expect("program");
        let nn = crate::printer_util::arena_view(&__program, cx.nodes, (node).file_index());
        let leftmost = ast::get_first_identifier(node, &nn);
        let in_js = ast::is_in_js_file(Some(node), &nn);
        let js_special = in_js
            && (ast::is_exports_identifier(&nn[leftmost])
                || nn[leftmost]
                    .parent
                    .is_some_and(|p| ast::is_module_exports_access_expression(&nn[p], &nn))
                || (nn[leftmost]
                    .parent
                    .is_some_and(|p| ast::is_qualified_name(&nn[p]))
                    && {
                        let p = nn[leftmost].parent.unwrap();
                        let qn = nn[p].as_qualified_name();
                        qn.left.is_some_and(|l| ast::is_module_identifier(&nn[l]))
                            && qn.right.is_some_and(|r| ast::is_exports_identifier(&nn[r]))
                    }));
        (leftmost, js_special)
    };
    if js_exports_left {
        introduces_error = true;
        let cloned = {
            let mut b = sh.b.borrow_mut();
            b.f.deep_clone_node(cx.nodes, node)
        };
        return (
            introduces_error,
            nb_set_text_range(sh, cx.nodes, cloned, Some(node)),
            None,
        );
    }
    let meaning = {
        let c = sh.c.borrow();
        let __program = c.program.clone().expect("program");
        let nn = crate::printer_util::arena_view(&__program, cx.nodes, (node).file_index());
        crate::emitsupport::get_meaning_of_entity_name_reference(node, &nn)
    };
    let mut sym: Option<SymbolId>;
    let leftmost_is_this = {
        let c = sh.c.borrow();
        let __program = c.program.clone().expect("program");
        let nn = crate::printer_util::arena_view(&__program, cx.nodes, (leftmost).file_index());
        ast::is_this_identifier(&nn[leftmost])
    };
    if leftmost_is_this {
        // `this` isn't a bindable identifier - skip resolution, find a
        // relevant `this` symbol directly and avoid exhaustive scope
        // traversal.
        sym = {
            let mut c = sh.c.borrow_mut();
            let container = c.get_this_container(leftmost, false, false);
            c.get_symbol_of_declaration(container)
        };
        if {
            let mut c = sh.c.borrow_mut();
            c.is_symbol_accessible(
                sym,
                Some(leftmost),
                meaning,
                false,
                live_nodes_for(sh, cx.nodes, Some(leftmost)),
            )
            .accessibility
                != printer::SymbolAccessibility::Accessible
        } {
            introduces_error = true;
            {
                let tracker = sh.b.borrow().ctx.tracker.clone();
                if let Some(tracker) = tracker {
                    tracker
                        .borrow_mut()
                        .report_inaccessible_this_error(cx.nodes);
                }
            }
        }
        return (
            introduces_error,
            attach_symbol_to_leftmost_identifier(sh, cx, leftmost, node, sym),
            None,
        );
    }
    sym = sh.c.borrow_mut().resolve_entity_name_live(
        Some(leftmost),
        meaning,
        true,
        true,
        None,
        live_nodes_for(sh, cx.nodes, Some(leftmost)),
    );
    if sh.b.borrow().ctx.enclosing_declaration.is_some()
        && !(sym.is_some_and(|s| {
            sh.c.borrow_mut()
                .sym(s)
                .flags
                .intersects(SymbolFlags::TYPE_PARAMETER)
        }))
    {
        sym = sym.and_then(|s| {
            let mut c = sh.c.borrow_mut();
            c.get_export_symbol_of_value_symbol_if_exported(Some(s))
        });
        // Some declarations may be transplanted to a new location.
        // When this happens we need to make sure that the name has the same
        // meaning at both locations.
        // We also check for the unknownSymbol because when we create a fake
        // scope some parameters may actually not be usable either because
        // they are the expanded rest parameter, or because they are the
        // newly added parameters from the tuple, which might have different
        // meanings in the original context.
        let enc = sh.b.borrow().ctx.enclosing_declaration;
        let sym_at_location = sh.c.borrow_mut().resolve_entity_name_live(
            Some(leftmost),
            meaning,
            true,
            true,
            enc,
            live_nodes_for(sh, cx.nodes, enc.or(Some(leftmost))),
        );
        let unknown_symbol = sh.c.borrow().unknown_symbol;
        let same_reference = {
            let mut c = sh.c.borrow_mut();
            let exported = sym_at_location
                .and_then(|s| c.get_export_symbol_of_value_symbol_if_exported(Some(s)));
            match (exported, sym) {
                (Some(a), Some(b)) => c.get_symbol_if_same_reference(a, b).is_some(),
                _ => false,
            }
        };
        // Check for unusable parameters symbols
        if sym_at_location == Some(unknown_symbol)
            // If the symbol is not found, but was not found in the original
            // scope either we probably have an error, don't reuse the node
            || (sym_at_location.is_none() && sym.is_some())
            // If the symbol is found both in declaration scope and in
            // current scope then it should point to the same reference
            || (sym_at_location.is_some() && sym.is_some() && !same_reference)
        {
            // In isolated declaration we will not do rest parameter
            // expansion so there is no need to report on these.
            if sym_at_location != Some(unknown_symbol) {
                nb_report_inference_fallback(sh, cx.nodes, node);
            }
            introduces_error = true;
            let cloned = {
                let mut b = sh.b.borrow_mut();
                b.f.deep_clone_node(cx.nodes, node)
            };
            return (
                introduces_error,
                nb_set_text_range(sh, cx.nodes, cloned, Some(node)),
                sym,
            );
        } else {
            sym = sym_at_location;
        }
    }

    if let Some(sym_v) = sym {
        // If a parameter is resolvable in the current context it is also
        // visible, so no need to go to symbol accessibility.
        let (fn_scoped, value_decl) = {
            let c = sh.c.borrow();
            let s = c.sym(sym_v);
            (
                s.flags.intersects(SymbolFlags::FUNCTION_SCOPED_VARIABLE),
                s.value_declaration,
            )
        };
        if fn_scoped && value_decl.is_some() {
            let vd = value_decl.unwrap();
            let is_param = {
                let c = sh.c.borrow();
                let __program = c.program.clone().expect("program");
                let nn = crate::printer_util::arena_view(&__program, cx.nodes, (vd).file_index());
                ast::is_part_of_parameter_declaration(vd, &nn)
                    || nn[vd].kind == Kind::JSDocParameterTag
            };
            if is_param {
                return (
                    introduces_error,
                    attach_symbol_to_leftmost_identifier(sh, cx, leftmost, node, sym),
                    None,
                );
            }
        }
        let sym_is_type_param =
            sh.c.borrow_mut()
                .sym(sym_v)
                .flags
                .intersects(SymbolFlags::TYPE_PARAMETER);
        let node_is_decl_name = {
            let c = sh.c.borrow();
            let __program = c.program.clone().expect("program");
            let nn = crate::printer_util::arena_view(&__program, cx.nodes, (node).file_index());
            ast::is_declaration_name(node, &nn)
        };
        // Type parameters are visible in the current context if they are
        // resolvable.
        if !sym_is_type_param && !node_is_decl_name && {
            let mut c = sh.c.borrow_mut();
            c.is_symbol_accessible(
                sym,
                enclosing_declaration,
                meaning,
                false,
                live_nodes_for(sh, cx.nodes, enclosing_declaration),
            )
            .accessibility
                != printer::SymbolAccessibility::Accessible
        } {
            nb_report_inference_fallback(sh, cx.nodes, node);
            introduces_error = true;
        } else {
            let tracker = sh.b.borrow().ctx.tracker.clone();
            if let Some(tracker) = tracker {
                let nodes_view: &[ast::Node] = cx.nodes;
                tracker.borrow_mut().track_symbol(
                    sym_v,
                    enclosing_declaration,
                    meaning,
                    nodes_view,
                    &mut |sym, en, mn, sc| {
                        sh.c.borrow_mut()
                            .is_symbol_accessible(sym, en, mn, sc, Some(nodes_view))
                    },
                );
            }
        }
        let attached = attach_symbol_to_leftmost_identifier(sh, cx, leftmost, node, sym);
        return (introduces_error, attached, None);
    }
    let cloned = {
        let mut b = sh.b.borrow_mut();
        b.f.deep_clone_node(cx.nodes, node)
    };
    (
        introduces_error,
        nb_set_text_range(sh, cx.nodes, cloned, Some(node)),
        None,
    )
}

/// `tryVisitIndexedAccess` (nodecopy.go).
fn try_visit_indexed_access(
    sh: &NCShared<'_, '_, '_>,
    v: &ast::NodeVisitor,
    cx: &mut ast::VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    let (object_type, index_type) = {
        let d = cx.nodes[node].as_indexed_access_type_node();
        (d.object_type, d.index_type)
    };
    let result_object_type = object_type.and_then(|o| try_visit_simple_type_node(sh, v, cx, o))?;
    let index = v.visit_node(cx, index_type);
    let updated = {
        let mut b = sh.b.borrow_mut();
        b.f.update_indexed_access_type_node(cx.nodes, node, Some(result_object_type), index)
            .unwrap_or(node)
    };
    nb_set_text_range(sh, cx.nodes, Some(updated), Some(node))
}

/// `tryVisitKeyOf` (nodecopy.go).
fn try_visit_key_of(
    sh: &NCShared<'_, '_, '_>,
    v: &ast::NodeVisitor,
    cx: &mut ast::VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    let (operator, type_) = {
        let to = cx.nodes[node].as_type_operator_node();
        (to.operator, to.type_)
    };
    let t = type_.and_then(|t| try_visit_simple_type_node(sh, v, cx, t))?;
    let updated = {
        let mut b = sh.b.borrow_mut();
        b.f.update_type_operator_node(cx.nodes, node, operator, Some(t))
            .unwrap_or(node)
    };
    nb_set_text_range(sh, cx.nodes, Some(updated), Some(node))
}

/// `tryVisitTypeQuery` (nodecopy.go).
fn try_visit_type_query(
    sh: &NCShared<'_, '_, '_>,
    v: &ast::NodeVisitor,
    cx: &mut ast::VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    let (expr_name, type_arguments) = {
        let d = cx.nodes[node].as_type_query_node();
        (
            d.expr_name,
            d.node_with_type_arguments_base.type_arguments.clone(),
        )
    };
    let (introduces_error, new_expr_name, _) = expr_name
        .map(|e| track_existing_entity_name(sh, cx, e, None))
        .unwrap_or_default();
    if !introduces_error {
        let type_arguments = v.visit_nodes(cx, type_arguments.clone());
        let updated = {
            let mut b = sh.b.borrow_mut();
            b.f.update_type_query_node(cx.nodes, node, new_expr_name, type_arguments)
                .unwrap_or(node)
        };
        return nb_set_text_range(sh, cx.nodes, Some(updated), Some(node));
    }

    let type_arguments = v.visit_nodes(cx, type_arguments.clone());
    let serialized_name = expr_name.and_then(|e| {
        let mut b = sh.b.borrow_mut();
        let mut c = sh.c.borrow_mut();
        b.serialize_type_name(&mut **c, cx.nodes, e, true, type_arguments.clone())
    });
    if let Some(serialized_name) = serialized_name {
        return nb_set_text_range(sh, cx.nodes, Some(serialized_name), expr_name);
    }
    None
}

/// `tryVisitTypeReference` (nodecopy.go).
fn try_visit_type_reference(
    sh: &NCShared<'_, '_, '_>,
    v: &ast::NodeVisitor,
    cx: &mut ast::VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    {
        let c = sh.c.borrow();
        let __program = c.program.clone().expect("program");
        let nn = crate::printer_util::arena_view(&__program, cx.nodes, (node).file_index());
        if ast::is_const_type_reference(&nn[node], &nn) {
            return None;
        }
    }
    let s = {
        let mut cb = sh.c.borrow_mut();
        let mut bb = sh.b.borrow_mut();
        bb.try_get_resolved_symbol_from_type_node(&mut **cb, Some(node), cx.nodes)
    };
    let s = s?; // ???
    {
        let s_flags = sh.c.borrow_mut().sym(s).flags;
        if s_flags.intersects(SymbolFlags::TYPE_PARAMETER) {
            let declared_type = sh.c.borrow_mut().get_declared_type_of_symbol(s);
            let mapper = sh.b.borrow().ctx.mapper;
            if let Some(mapper) = mapper {
                let mut cb = sh.c.borrow_mut();
                let mapped = get_mapped_type(&mut **cb, declared_type, mapper);
                if mapped != declared_type {
                    // refers to type parameter remapped by context
                    // (TODO improvement: just return the remapped param
                    // name?)
                    return None;
                }
            }
        }
    }
    let can_reuse = {
        let mut b = sh.b.borrow_mut();
        let mut c = sh.c.borrow_mut();
        let t = b.get_type_from_type_node(&mut **c, node, false, cx.nodes);
        t.is_some_and(|t| b.can_reuse_existing_js_type_node(&mut **c, cx.nodes, node, t))
    };
    if !can_reuse {
        // fallback to serialization for jsdoc types that have insufficient
        // or incomplete type args, or are remapped by the checker in only
        // jsdoc contexts
        // TODO: remappings like `promise` -> `Promise<any>` are static, we
        // *could* statically remap the nodes, too. But that only matters for
        // `isolatedDeclarations` in JS, should we enable that.
        return None;
    }
    let (type_name, type_arguments) = {
        let d = cx.nodes[node].as_type_reference_node();
        (
            d.type_name,
            d.node_with_type_arguments_base.type_arguments.clone(),
        )
    };
    let (introduces_error, new_name, _) = type_name
        .map(|t| track_existing_entity_name(sh, cx, t, None))
        .unwrap_or_default();
    if !introduces_error {
        let type_arguments = v.visit_nodes(cx, type_arguments.clone());
        let updated = {
            let mut b = sh.b.borrow_mut();
            b.f.update_type_reference_node(cx.nodes, node, new_name, type_arguments)
                .unwrap_or(node)
        };
        return nb_set_text_range(sh, cx.nodes, Some(updated), Some(node));
    } else {
        let type_arguments = v.visit_nodes(cx, type_arguments.clone());
        let serialized_name = type_name.and_then(|t| {
            let mut b = sh.b.borrow_mut();
            let mut c = sh.c.borrow_mut();
            b.serialize_type_name(&mut **c, cx.nodes, t, false, type_arguments.clone())
        });
        if let Some(serialized_name) = serialized_name {
            return nb_set_text_range(sh, cx.nodes, Some(serialized_name), type_name);
        }
        return None;
    }
}

/// `tryVisitSimpleTypeNode` (nodecopy.go).
fn try_visit_simple_type_node(
    sh: &NCShared<'_, '_, '_>,
    v: &ast::NodeVisitor,
    cx: &mut ast::VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    let inner_node = ast::skip_parentheses(node, cx.nodes);
    match cx.nodes[inner_node].kind {
        Kind::TypeReference => try_visit_type_reference(sh, v, cx, inner_node),
        Kind::TypeQuery => try_visit_type_query(sh, v, cx, inner_node),
        Kind::IndexedAccessType => try_visit_indexed_access(sh, v, cx, inner_node),
        Kind::TypeOperator => {
            if cx.nodes[inner_node].as_type_operator_node().operator == Kind::KeyOfKeyword {
                try_visit_key_of(sh, v, cx, inner_node)
            } else {
                v.visit_node(cx, Some(node))
            }
        }
        _ => v.visit_node(cx, Some(node)),
    }
}

/// `visitExistingNodeTreeSymbolsWorker` (nodecopy.go) — the per-node worker
/// of the existing-node reuse pass.
///
/// PORT: `factory := b.f` calls become `cx.factory` (a fresh factory
/// equivalent to `b.f`, see the file header); `b.*`/`b.ch.*` calls go
/// through scoped `RefCell` borrows on `sh`.
fn visit_existing_node_tree_symbols_worker(
    sh: &NCShared<'_, '_, '_>,
    v: &ast::NodeVisitor,
    cx: &mut ast::VisitorCx<'_, '_>,
    node: NodeId,
) -> Option<NodeId> {
    // !!! TODO: the reparser *should* make all the jsdoc remapping logic
    // here redundant, assuming we only ever try to preserve reparsed nodes
    // and never walk back to the jsdoc "originals" accidentally.
    // Still, what can be ported of the logic is here, just in case.
    // Begin JSDoc handling
    match cx.nodes[node].kind {
        Kind::JSDocTypeExpression => {
            // Unwrap JSDocTypeExpressions
            let t = cx.nodes[node].as_js_doc_type_expression().type_;
            return v.visit_node(cx, t);
        }
        Kind::JSDocAllType => {
            // !!! TODO: We don't _actually_ support jsdoc namepath types,
            // emit `any` instead; verify we handle as gracefully as strada
            return Some(cx.factory.new_keyword_type_node(cx.nodes, Kind::AnyKeyword));
        }
        Kind::JSDocNullableType => {
            let t = cx.nodes[node].as_js_doc_nullable_type().type_;
            let visited = v.visit_node(cx, t);
            let kw = cx
                .factory
                .new_keyword_expression(cx.nodes, Kind::NullKeyword);
            let null_lit = cx.factory.new_literal_type_node(cx.nodes, Some(kw));
            let list = cx.factory.new_node_list(
                [visited, Some(null_lit)]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>(),
            );
            return Some(cx.factory.new_union_type_node(cx.nodes, Some(list)));
        }
        Kind::JSDocOptionalType => {
            let t = cx.nodes[node].as_js_doc_optional_type().type_;
            let visited = v.visit_node(cx, t);
            let undef = cx
                .factory
                .new_keyword_type_node(cx.nodes, Kind::UndefinedKeyword);
            let list = cx.factory.new_node_list(
                [visited, Some(undef)]
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>(),
            );
            return Some(cx.factory.new_union_type_node(cx.nodes, Some(list)));
        }
        Kind::JSDocNonNullableType => {
            // Unwrap
            let t = cx.nodes[node].as_js_doc_non_nullable_type().type_;
            return v.visit_node(cx, t);
        }
        Kind::JSDocVariadicType => {
            // !!! TODO: verify this matches how jsdoc variadics are actually
            // handled now?
            let t = cx.nodes[node].as_js_doc_variadic_type().type_;
            let visited = v.visit_node(cx, t);
            return Some(cx.factory.new_array_type_node(cx.nodes, visited));
        }
        Kind::JSDocTypeLiteral => {
            let tags = cx.nodes[node]
                .as_js_doc_type_literal()
                .js_doc_property_tags
                .to_vec();
            let mut members: Vec<NodeId> = Vec::new();
            for t in tags {
                if cx.nodes[t].kind != Kind::JSDocPropertyTag
                    && cx.nodes[t].kind != Kind::JSDocParameterTag
                {
                    continue;
                }
                let n = cx.nodes[t].name();
                let Some(n) = n else { continue };
                let target_name = if cx.nodes[n].kind == Kind::Identifier {
                    n
                } else {
                    // !!! TODO: without typesystem backup, doing this cast
                    // unguarded seems really suspect, even though it is what
                    // strada does
                    cx.nodes[n].as_qualified_name().right.unwrap_or(n)
                };
                let name = v.visit_node(cx, Some(target_name));
                let tag = cx.nodes[t].as_js_doc_parameter_or_property_tag();
                let should_be_optional = tag.is_bracketed
                    || (tag.type_expression.is_some()
                        && cx.nodes[tag.type_expression.unwrap()].kind == Kind::JSDocOptionalType);
                let question = if should_be_optional {
                    Some(cx.factory.new_token(cx.nodes, Kind::QuestionToken))
                } else {
                    None
                };
                // !!! TODO: alternate lookup locations for the type?
                // serialize on demand if it doesn't serialze? strada does
                // something funky here.
                let ty = v.visit_node(cx, cx.nodes[t].type_expression());
                members.push(
                    cx.factory.new_property_signature_declaration(
                        cx.nodes, None, name, question, ty, None,
                    ),
                );
            }
            let list = cx.factory.new_node_list(members);
            return Some(cx.factory.new_type_literal_node(cx.nodes, Some(list)));
        }
        _ => {}
    }
    // End JSDoc handling

    {
        // `ast.IsTypeReferenceNode(node) && IsIdentifier(typeName) && text
        // == ""`
        let is_empty_type_ref = {
            let d = &cx.nodes[node];
            ast::is_type_reference_node(d)
                && d.as_type_reference_node().type_name.is_some_and(|t| {
                    cx.nodes[t].kind == Kind::Identifier
                        && cx.nodes[t].as_identifier().text.is_empty()
                })
        };
        if is_empty_type_ref {
            let replacement = cx.factory.new_keyword_type_node(cx.nodes, Kind::AnyKeyword);
            sh.b.borrow().e.borrow().set_original(replacement, node);
            return Some(replacement);
        }
        if ast::is_this_type_node(&cx.nodes[node]) {
            // TODO: strada never marks `this` type nodes as an error - it
            // calls `canReuseTypeNode` on it, but that function always
            // returns `true` for `this` type nodes, which in turn fails to
            // verify that the `this` context is the same between the source
            // and target locations. The conservative thing is to _never_
            // copy a `this`. We could improve this, but strada is
            // *definitely* wrong and overbroad here. (note that we're
            // inlining uses of `canReuseTypeNode` in corsa because of the
            // unfurled host structure meaning we don't need to defer to a
            // host object for functionality it needs)
            // bound.markError(nil) // conservative approach
            return Some(node);
        }
        if ast::is_type_parameter_declaration(&cx.nodes[node]) {
            let (modifiers, name, constraint, expression, default_type) = {
                let d = cx.nodes[node].as_type_parameter_declaration();
                (
                    d.modifiers_base.modifiers.clone(),
                    d.name,
                    d.constraint,
                    d.expression,
                    d.default_type,
                )
            };
            let (_, new_name, _) = name
                .map(|n| track_existing_entity_name(sh, cx, n, None))
                .unwrap_or_default();
            let modifiers = v.visit_modifiers(cx, modifiers);
            let constraint = v.visit_node(cx, constraint);
            let expression = v.visit_node(cx, expression);
            let default_type = v.visit_node(cx, default_type);
            let updated = cx
                .factory
                .update_type_parameter_declaration(
                    cx.nodes,
                    node,
                    modifiers,
                    new_name,
                    constraint,
                    expression,
                    default_type,
                )
                .unwrap_or(node);
            return Some(updated);
        }
        if ast::is_indexed_access_type_node(&cx.nodes[node]) {
            if let Some(result) = try_visit_indexed_access(sh, v, cx, node) {
                return Some(result);
            }
            nb_mark_error(sh);
            return Some(node);
        }
        if ast::is_type_reference_node(&cx.nodes[node]) {
            if let Some(result) = try_visit_type_reference(sh, v, cx, node) {
                return Some(result);
            }
            nb_mark_error(sh);
            return Some(node);
        }
        if ast::is_type_query_node(&cx.nodes[node]) {
            if let Some(result) = try_visit_type_query(sh, v, cx, node) {
                return Some(result);
            }
            nb_mark_error(sh);
            return Some(node);
        }
        if ast::is_type_operator_node(&cx.nodes[node]) {
            let to = cx.nodes[node].as_type_operator_node();
            if to.operator == Kind::UniqueKeyword
                && to
                    .type_
                    .is_some_and(|t| cx.nodes[t].kind == Kind::SymbolKeyword)
            {
                let non_fake_enclosing = {
                    let mut b = sh.b.borrow_mut();
                    let mut c = sh.c.borrow_mut();
                    b.get_enclosing_declaration_ignoring_fake_scope(&mut **c, cx.nodes)
                };
                let same_scope = ast::find_ancestor(Some(node), cx.nodes, &mut |a, _| {
                    Some(a.id) == non_fake_enclosing
                });
                if same_scope.is_none() {
                    nb_mark_error(sh);
                    return Some(node);
                }
            } else if to.operator == Kind::KeyOfKeyword {
                if let Some(result) = try_visit_key_of(sh, v, cx, node) {
                    return Some(result);
                }
                nb_mark_error(sh);
                return Some(node);
            }
        }
        if ast::is_literal_import_type_node(&cx.nodes[node], cx.nodes) {
            // assert keyword in imported attributes is deprecated, so we
            // don't reuse types that contain it
            // Ex: import("pkg", { assert: {} }
            let itn = cx.nodes[node].as_import_type_node();
            let attrs_is_assert = itn
                .attributes
                .is_some_and(|a| cx.nodes[a].as_import_attributes().token == Kind::AssertKeyword);
            let (is_type_of, argument, attributes, qualifier, type_arguments) = (
                itn.is_type_of,
                itn.argument,
                itn.attributes,
                itn.qualifier,
                itn.node_with_type_arguments_base.type_arguments.clone(),
            );
            if attrs_is_assert {
                nb_mark_error(sh);
                return Some(node);
            }
            let t = {
                let mut b = sh.b.borrow_mut();
                let mut c = sh.c.borrow_mut();
                b.get_type_from_type_node(&mut **c, node, true, cx.nodes)
            };
            if t.is_none() {
                nb_mark_error(sh);
                return Some(node);
            }
            // !!! TODO: invalidate node reuse if js fallback logic used in
            // type param list/typeof lookup (but isn't this logic gone?)
            let original_spec = {
                // `node.AsImportTypeNode().Argument.AsLiteralTypeNode().Literal`
                let arg = argument?;
                let lit = cx.nodes[arg].as_literal_type_node().literal;
                lit?
            };
            let specifier = {
                let mut b = sh.b.borrow_mut();
                let mut c = sh.c.borrow_mut();
                b.rewrite_module_specifier(&mut **c, cx.nodes, node, original_spec)
            };
            let specifier = if specifier == original_spec {
                // visit node if not replaced
                v.visit_node(cx, Some(specifier))?
            } else {
                specifier
            };
            let arg = if specifier != original_spec {
                Some(cx.factory.new_literal_type_node(cx.nodes, Some(specifier)))
            } else {
                argument
            };
            let attributes = v.visit_node(cx, attributes);
            let qualifier = v.visit_node(cx, qualifier);
            let type_arguments = v.visit_nodes(cx, type_arguments.clone());
            let updated = cx
                .factory
                .update_import_type_node(
                    cx.nodes,
                    node,
                    is_type_of,
                    arg,
                    attributes,
                    qualifier,
                    type_arguments,
                )
                .unwrap_or(node);
            return Some(updated);
        }
    }

    // `node.Name()` computed-property handling
    {
        let name_kind = cx.nodes[node].name().map(|n| cx.nodes[n].kind);
        if name_kind == Some(Kind::ComputedPropertyName)
            && !sh.c.borrow_mut().has_late_bindable_name(node)
        {
            if !ast::has_dynamic_name(node, cx.nodes) {
                // !!! TODO: This matches strada, but rather than recursing,
                // this should probably fall down to later cases.
                // Take a `["field"]` property declaration - it still needs a
                // `: any` appended to it
                return Some(v.visit_each_child(cx, node).unwrap_or(node));
            }
            // !!! TODO: this condition matches strada, but it just seems
            // wrong? Or at the very least extraordinarily approximate, and
            // doesn't flag a builder error...
            let should_remove_declaration = {
                let name = cx.nodes[node].name().unwrap();
                let expr = cx.nodes[name].as_computed_property_name().expression;
                let allow_unresolved =
                    sh.b.borrow()
                        .ctx
                        .internal_flags
                        .intersects(nodebuilder::InternalFlags::ALLOW_UNRESOLVED_NAMES);
                let entity_name =
                    expr.is_some_and(|e| ast::is_entity_name_expression(&cx.nodes[e], cx.nodes));
                let any_type = expr.is_some_and(|_e| {
                    let t = sh.c.borrow_mut().check_computed_property_name(name);
                    sh.c.borrow().types.get(t).flags.intersects(TypeFlags::ANY)
                });
                !(allow_unresolved && entity_name && any_type)
            };
            if should_remove_declaration {
                return None;
            }
        }
    }

    // Missing-type-annotation handling — appends `: any`.
    {
        let missing_type = {
            let d = &cx.nodes[node];
            (ast::is_function_like(Some(node), cx.nodes) && d.type_().is_none())
                || (ast::is_property_declaration(d)
                    && d.type_().is_none()
                    && d.initializer().is_none())
                || (ast::is_property_signature_declaration(d)
                    && d.type_().is_none()
                    && d.initializer().is_none())
                || (ast::is_parameter_declaration(d)
                    && d.type_().is_none()
                    && d.initializer().is_none())
        };
        if missing_type {
            let mut visited = v.visit_each_child(cx, node).unwrap_or(node);
            if visited == node {
                let cloned = cx.factory.clone_node(cx.nodes, visited);
                visited = nb_set_text_range(sh, cx.nodes, Some(cloned), Some(node))?;
            }
            let node = visited;
            let new_type = cx.factory.new_keyword_type_node(cx.nodes, Kind::AnyKeyword);
            match cx.nodes[node].kind {
                Kind::PropertyDeclaration => {
                    let (modifiers, name, postfix) = {
                        let d = cx.nodes[node].as_property_declaration();
                        (
                            d.named_member_base.modifiers_base.modifiers.clone(),
                            d.named_member_base.name,
                            d.named_member_base.postfix_token,
                        )
                    };
                    return Some(
                        cx.factory
                            .update_property_declaration(
                                cx.nodes,
                                node,
                                modifiers,
                                name,
                                postfix,
                                Some(new_type),
                                None,
                            )
                            .unwrap_or(node),
                    );
                }
                Kind::PropertySignature => {
                    let (modifiers, name, postfix) = {
                        let d = cx.nodes[node].as_property_signature_declaration();
                        (
                            d.named_member_base.modifiers_base.modifiers.clone(),
                            d.named_member_base.name,
                            d.named_member_base.postfix_token,
                        )
                    };
                    return Some(
                        cx.factory
                            .update_property_signature_declaration(
                                cx.nodes,
                                node,
                                modifiers,
                                name,
                                postfix,
                                Some(new_type),
                                None,
                            )
                            .unwrap_or(node),
                    );
                }
                Kind::Parameter => {
                    let (dot_dot_dot, name, question) = {
                        let d = cx.nodes[node].as_parameter_declaration();
                        (d.dot_dot_dot_token, d.name, d.question_token)
                    };
                    return Some(
                        cx.factory
                            .update_parameter_declaration(
                                cx.nodes,
                                node,
                                None,
                                dot_dot_dot,
                                name,
                                question,
                                Some(new_type),
                                None,
                            )
                            .unwrap_or(node),
                    );
                }
                Kind::MethodSignature => {
                    let (modifiers, name, postfix, type_params, params) = {
                        let d = cx.nodes[node].as_method_signature_declaration();
                        (
                            d.named_member_base.modifiers_base.modifiers.clone(),
                            d.named_member_base.name,
                            d.named_member_base.postfix_token,
                            d.function_like_base.type_parameters.clone(),
                            d.function_like_base.parameters.clone(),
                        )
                    };
                    return Some(
                        cx.factory
                            .update_method_signature_declaration(
                                cx.nodes,
                                node,
                                modifiers,
                                name,
                                postfix,
                                type_params,
                                params,
                                Some(new_type),
                            )
                            .unwrap_or(node),
                    );
                }
                Kind::CallSignature => {
                    let (type_params, params) = {
                        let d = cx.nodes[node].as_call_signature_declaration();
                        (
                            d.function_like_base.type_parameters.clone(),
                            d.function_like_base.parameters.clone(),
                        )
                    };
                    return Some(
                        cx.factory
                            .update_call_signature_declaration(
                                cx.nodes,
                                node,
                                type_params,
                                params,
                                Some(new_type),
                            )
                            .unwrap_or(node),
                    );
                }
                Kind::JSDocSignature => {
                    let (type_params, params) = {
                        let d = cx.nodes[node].as_js_doc_signature();
                        (
                            d.function_like_base.type_parameters.clone(),
                            d.function_like_base.parameters.clone(),
                        )
                    };
                    return Some(
                        cx.factory
                            .update_js_doc_signature(
                                cx.nodes,
                                node,
                                type_params,
                                params,
                                Some(new_type),
                            )
                            .unwrap_or(node),
                    );
                }
                Kind::ConstructSignature => {
                    let (type_params, params) = {
                        let d = cx.nodes[node].as_construct_signature_declaration();
                        (
                            d.function_like_base.type_parameters.clone(),
                            d.function_like_base.parameters.clone(),
                        )
                    };
                    return Some(
                        cx.factory
                            .update_construct_signature_declaration(
                                cx.nodes,
                                node,
                                type_params,
                                params,
                                Some(new_type),
                            )
                            .unwrap_or(node),
                    );
                }
                Kind::IndexSignature => {
                    let (modifiers, params) = {
                        let d = cx.nodes[node].as_index_signature_declaration();
                        (
                            d.modifiers_base.modifiers.clone(),
                            d.function_like_base.parameters.clone(),
                        )
                    };
                    return Some(
                        cx.factory
                            .update_index_signature_declaration(
                                cx.nodes,
                                node,
                                modifiers,
                                params,
                                Some(new_type),
                            )
                            .unwrap_or(node),
                    );
                }
                Kind::FunctionType => {
                    let (type_params, params) = {
                        let d = cx.nodes[node].as_function_type_node();
                        (
                            d.function_or_constructor_type_node_base
                                .function_like_base
                                .type_parameters
                                .clone(),
                            d.function_or_constructor_type_node_base
                                .function_like_base
                                .parameters
                                .clone(),
                        )
                    };
                    return Some(
                        cx.factory
                            .update_function_type_node(
                                cx.nodes,
                                node,
                                type_params,
                                params,
                                Some(new_type),
                            )
                            .unwrap_or(node),
                    );
                }
                Kind::ConstructorType => {
                    let (modifiers, type_params, params) = {
                        let d = cx.nodes[node].as_constructor_type_node();
                        (
                            d.function_or_constructor_type_node_base
                                .modifiers_base
                                .modifiers
                                .clone(),
                            d.function_or_constructor_type_node_base
                                .function_like_base
                                .type_parameters
                                .clone(),
                            d.function_or_constructor_type_node_base
                                .function_like_base
                                .parameters
                                .clone(),
                        )
                    };
                    return Some(
                        cx.factory
                            .update_constructor_type_node(
                                cx.nodes,
                                node,
                                modifiers,
                                type_params,
                                params,
                                Some(new_type),
                            )
                            .unwrap_or(node),
                    );
                }
                _ => {}
            }
        }
    }

    // Computed property names with entity-name expressions
    if ast::is_computed_property_name(&cx.nodes[node])
        && cx.nodes[node]
            .as_computed_property_name()
            .expression
            .is_some_and(|e| ast::is_entity_name_expression(&cx.nodes[e], cx.nodes))
    {
        let expr = cx.nodes[node].as_computed_property_name().expression?;
        let (introduces_error, result, _) = track_existing_entity_name(sh, cx, expr, None);
        if !introduces_error {
            return Some(
                cx.factory
                    .update_computed_property_name(cx.nodes, node, result)
                    .unwrap_or(node),
            );
        } else {
            // !!! TODO: rewriting computed names based on evaluator /
            // typecheck results?
            // strada's behavior seems hard to justify vs marking an error
            // and moving on
            nb_mark_error(sh);
            return Some(v.visit_each_child(cx, node).unwrap_or(node));
        }
    }

    // Type predicates
    if ast::is_type_predicate_node(&cx.nodes[node]) {
        let (asserts_modifier, parameter_name, type_) = {
            let d = cx.nodes[node].as_type_predicate_node();
            (d.asserts_modifier, d.parameter_name, d.type_)
        };
        let parameter_name = if parameter_name.is_some_and(|p| cx.nodes[p].kind == Kind::Identifier)
        {
            let (introduces_error, result, _) =
                track_existing_entity_name(sh, cx, parameter_name.unwrap(), None);
            // Should not usually happen the only case is when a type
            // predicate comes from a JSDoc type annotation with it's own
            // parameter symbol definition.
            // /** @type {(v: unknown) => v is undefined} */
            // const isUndef = v => v === undefined;
            if introduces_error {
                nb_mark_error(sh);
            }
            result
        } else {
            parameter_name.map(|p| cx.factory.clone_node(cx.nodes, p))
        };
        let asserts_modifier = v.visit_node(cx, asserts_modifier);
        let type_ = v.visit_node(cx, type_);
        return Some(
            cx.factory
                .update_type_predicate_node(cx.nodes, node, asserts_modifier, parameter_name, type_)
                .unwrap_or(node),
        );
    }

    // Conditional types — the true/extends branch sees the infer scope.
    if ast::is_conditional_type_node(&cx.nodes[node]) {
        let (check_type, extends_type, true_type, false_type) = {
            let d = cx.nodes[node].as_conditional_type_node();
            (d.check_type, d.extends_type, d.true_type, d.false_type)
        };
        let check_type = v.visit_node(cx, check_type);
        let type_params = sh.c.borrow_mut().get_infer_type_parameters(node, cx.nodes);
        let dispose = {
            let mut b = sh.b.borrow_mut();
            let mut c = sh.c.borrow_mut();
            b.enter_new_scope(
                &mut **c,
                cx.nodes,
                Some(node),
                None,
                Some(type_params),
                None,
                None,
            )
        };
        let extends_type = v.visit_node(cx, extends_type);
        let true_type = v.visit_node(cx, true_type);
        dispose.restore(&mut **sh.b.borrow_mut(), cx.nodes);
        let false_type = v.visit_node(cx, false_type);
        return Some(
            cx.factory
                .update_conditional_type_node(
                    cx.nodes,
                    node,
                    check_type,
                    extends_type,
                    true_type,
                    false_type,
                )
                .unwrap_or(node),
        );
    }

    // style applications
    {
        let make_single_line = ast::is_tuple_type_node(&cx.nodes[node])
            || (!sh
                .b
                .borrow()
                .ctx
                .flags
                .intersects(nodebuilder::Flags::MULTILINE_OBJECT_LITERALS)
                && ast::is_type_literal_node(&cx.nodes[node]))
            || ast::is_mapped_type_node(&cx.nodes[node]);
        if make_single_line {
            // make tuples/types/mappedtypes single line
            let mut res = v.visit_each_child(cx, node).unwrap_or(node);
            if res == node {
                res = cx.factory.clone_node(cx.nodes, res);
                res = nb_set_text_range(sh, cx.nodes, Some(res), Some(node))?;
            }
            sh.b.borrow()
                .e
                .borrow()
                .add_emit_flags(res, printer::EmitFlags::SINGLE_LINE);
            return Some(res);
        }
    }

    if ast::is_string_literal_like(&cx.nodes[node]) {
        // Preserve the original characters of the literal (e.g. emojis) in
        // declaration emit rather than escaping them as ASCII Unicode
        // escapes. Mirrors TypeScript's behavior for synthesized string
        // literal types in the node builder (checker.ts:6853).
        let c2 = cx.factory.clone_node(cx.nodes, node);
        if cx.nodes[node].kind == Kind::StringLiteral
            && sh
                .b
                .borrow()
                .ctx
                .flags
                .intersects(nodebuilder::Flags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE)
            && !cx.nodes[c2]
                .as_string_literal()
                .literal_expression_base
                .literal_like_node_base
                .token_flags
                .intersects(ast::TokenFlags::SINGLE_QUOTE)
        {
            // set single quote on string literals
            let f = cx.nodes[c2]
                .as_string_literal()
                .literal_expression_base
                .literal_like_node_base
                .token_flags;
            cx.nodes[c2]
                .as_string_literal_mut()
                .literal_expression_base
                .literal_like_node_base
                .token_flags = f | ast::TokenFlags::SINGLE_QUOTE;
        }
        sh.b.borrow()
            .e
            .borrow()
            .add_emit_flags(c2, printer::EmitFlags::NO_ASCII_ESCAPING);
        return Some(c2);
    }

    Some(v.visit_each_child(cx, node).unwrap_or(node))
}

/// `getExistingNodeTreeVisitor` (nodecopy.go) — builds the reuse visitor.
/// PORT: returns a `NodeVisitor` over the shared `ExistingNodeTreeState`;
/// the `nonLocalNode` flag is the `Cell` on `sh`.
fn get_existing_node_tree_visitor<'v, 'a>(sh: NCShared<'v, 'a, 'v>) -> ast::NodeVisitor<'v>
where
    'a: 'v,
{
    let sh2 = sh.clone();
    let sh3 = sh.clone();
    let sh4 = sh.clone();
    ast::NodeVisitor::new(
        Box::new(
            move |v: &ast::NodeVisitor, cx: &mut ast::VisitorCx<'_, '_>, node: NodeId| {
                let sh = &sh2;
                // If there was an error in a sibling node bail early, the
                // result will be discarded anyway
                if sh.bound.borrow().had_error {
                    return Some(node);
                }
                let recover_state = nb_start_recovery_scope(sh);
                let introduces_new_scope = {
                    ast::is_function_like(Some(node), cx.nodes)
                        || ast::is_mapped_type_node(&cx.nodes[node])
                };
                let mut exit = None;
                if introduces_new_scope {
                    let mut params: Option<Vec<Option<SymbolId>>> = None;
                    let mut type_params: Option<Vec<TypeId>> = None;
                    if ast::is_function_like(Some(node), cx.nodes) {
                        let sig = sh.c.borrow_mut().get_signature_from_declaration(node);
                        let (p, tp) = {
                            let c = sh.c.borrow();
                            let s = c.signature_arena.get(sig);
                            (s.parameters.clone(), s.type_parameters.clone())
                        };
                        params = Some(p.into_iter().map(Some).collect());
                        type_params = Some(tp);
                    } else if cx.nodes[node].kind == Kind::ConditionalType {
                        // !!! TODO: impossible in combination with the scope
                        // start check???
                        type_params = Some(sh.c.borrow_mut().get_infer_type_parameters(node, cx.nodes));
                    } else if cx.nodes[node].kind == Kind::MappedType {
                        let tp = cx.nodes[node].as_mapped_type_node().type_parameter;
                        let tps = tp.and_then(|tp| {
                            let mut c = sh.c.borrow_mut();
                            c.get_symbol_of_declaration(tp)
                                .map(|s| vec![c.get_declared_type_of_type_parameter(s)])
                        });
                        type_params = tps;
                    }
                    exit = Some({
                        let mut b = sh.b.borrow_mut();
                        let mut c = sh.c.borrow_mut();
                        b.enter_new_scope(
                            &mut **c,
                            cx.nodes,
                            Some(node),
                            params,
                            type_params,
                            None,
                            None,
                        )
                    });
                }
                let mut result = visit_existing_node_tree_symbols_worker(sh, v, cx, node);
                if let Some(exit) = exit {
                    exit.restore(&mut **sh.b.borrow_mut(), cx.nodes);
                }

                if result == Some(node) && !ast::node_is_synthesized(&cx.nodes[node]) {
                    // always clone a new node
                    result = cx.factory.deep_clone_node(cx.nodes, node);
                }

                // We want to clone the subtree, so when we mark it up with
                // __pos and __end in quickfixes, we don't get odd behavior
                // because of reused nodes. We also need to clone to _remove_
                // the position information if the node comes from a
                // different file than the one the node builder is set to
                // build for (even though we are reusing the node structure,
                // the position information would make the printer print
                // invalid spans for literals and identifiers, and the
                // formatter would choke on the mismatched positional spans
                // between a parent and an injected child from another file).
                result = nb_set_text_range(sh, cx.nodes, result, Some(node));

                if sh.bound.borrow().had_error {
                    if ast::is_type_node(&cx.nodes[node])
                        && !ast::is_type_predicate_node(&cx.nodes[node])
                    {
                        nb_end_recovery_scope(sh, recover_state);
                        // TODO: this fallback matches strada behavior, but
                        // it lacks any verification that the type from
                        // `node` actually matches the type we'd expect at
                        // this traversal position within the parent type.
                        let t = {
                            let mut b = sh.b.borrow_mut();
                            let mut c = sh.c.borrow_mut();
                            b.get_type_from_type_node(&mut **c, node, false, cx.nodes)
                        };
                        let mut b = sh.b.borrow_mut();
                        let mut c = sh.c.borrow_mut();
                        return b.type_to_type_node_opt(&mut **c, cx.nodes, t);
                    }
                    let cloned = cx.factory.clone_node(cx.nodes, node);
                    return nb_set_text_range(sh, cx.nodes, Some(cloned), Some(node));
                }

                result
            },
        ),
        ast::NodeVisitorHooks {
            visit_nodes: Some(Box::new(
                move |cx: &mut ast::VisitorCx<'_, '_>,
                      nodes: Option<NodeList>,
                      v: &ast::NodeVisitor| {
                    let orig_ptr = nodes.as_ref().map(|n| n.nodes.as_ptr());
                    let res = v.visit_nodes(cx, nodes);
                    let mut res = res;
                    if sh3.non_local_node.get()
                        && let Some(res_list) = res.as_mut()
                    {
                        // Remove position data from node lists originating
                        // in other files. `res == nodes` in Go means the
                        // list was unchanged (visit_nodes returns the input
                        // value back) — detect via the backing-slice pointer
                        // and clone before mutating `loc`.
                        if orig_ptr.is_some_and(|p| std::ptr::eq(res_list.nodes.as_ptr(), p)) {
                            *res_list = res_list.clone();
                        }
                        res_list.loc = TextRange::new(-1, -1);
                    }
                    res
                },
            )),
            visit_node: Some(Box::new(
                move |cx: &mut ast::VisitorCx<'_, '_>, node: NodeId, v: &ast::NodeVisitor| {
                    // Capture if the current node is in the current file so
                    // node lists know if they can keep positions or not
                    let sh = &sh4;
                    let old_non_local_node = sh.non_local_node.get();
                    let enclosing_file = sh.b.borrow().ctx.enclosing_file;
                    let most_original =
                        sh.b.borrow()
                            .e
                            .borrow()
                            .most_original(Some(node))
                            .unwrap_or(node);
                    let file_of = {
                        let c = sh.c.borrow();
                        let __program = c.program.clone().expect("program");
                        let nn = crate::printer_util::arena_view(&__program, cx.nodes, (most_original).file_index());
                        ast::get_source_file_of_node(Some(most_original), &nn)
                    };
                    sh.non_local_node
                        .set(enclosing_file.is_none() || enclosing_file != file_of);
                    let res = v.visit_node(cx, Some(node));
                    sh.non_local_node.set(old_non_local_node);
                    res
                },
            )),
            ..Default::default()
        },
    )
}
