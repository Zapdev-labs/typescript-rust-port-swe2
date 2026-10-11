// Ported from tsc/internal/checker/symboltracker.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `SymbolTrackerImpl` — wraps an inner `nodebuilder.SymbolTracker`, records
// tracked symbols into the `NodeBuilderContext`, and marks
// `reportedDiagnostic` when the inner tracker reports.
//
// PORT notes:
//
// - `context *NodeBuilderContext` is the same object `b.ctx` points at — Go
//   mutates it through the tracker (`this.context.trackedSymbols`,
//   `this.context.reportedDiagnostic`). Rust can't store that back-pointer
//   (the tracker itself lives inside the context), so the two fields the
//   tracker mutates are shared cells on `NodeBuilderContext`
//   (`Rc<Cell<bool>>` / `Rc<RefCell<Vec<TrackedSymbolArgs>>>`) and the
//   tracker keeps clones. Same aliasing semantics, no `unsafe`.
// - `inner nodebuilder.SymbolTracker` →
//   `Option<Rc<RefCell<dyn SymbolTracker + 'a>>>`. The declarations
//   transformer's tracker is lifetime-bound (`SymbolTrackerImpl<'a>`
//   carries `Rc<dyn EmitResolver + 'a>`), so the inner slot shares the
//   enclosing context's `'a` rather than forcing `'static` (which dropped
//   all inner-tracker forwarding — the old `Box<dyn>` parameter couldn't
//   express the borrow). `Rc<RefCell>` lets `enter_context` hand clones to
//   nested contexts.
// - `NewSymbolTrackerImpl`'s `tracker.(*SymbolTrackerImpl)` peel loop has no
//   `Rc<RefCell<dyn + 'a>>` analogue (a trait method cannot name `'a`).
//   In practice the incoming tracker is the declarations transformer
//   tracker or a checker-internal one — never this wrapper type — so the
//   loop is omitted rather than approximated.
// - `*ast.Symbol` → `SymbolId`, `*ast.Node` → `Option<NodeId>`,
//   `*ast.SourceFile` → `NodeId`, matching the trait.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::{self as ast, NodeId, SymbolFlags, SymbolId};
use tsc_nodebuilder::SymbolTracker;

use crate::nodebuilderimpl::{NodeBuilderContext, TrackedSymbolArgs};

/// `type SymbolTrackerImpl struct`.
pub struct SymbolTrackerImpl<'a> {
    /// `context.trackedSymbols` — shared cell (see header).
    pub tracked_symbols: Rc<RefCell<Vec<TrackedSymbolArgs>>>,
    /// `context.reportedDiagnostic` — shared cell (see header).
    pub reported_diagnostic: Rc<Cell<bool>>,
    /// The shared symbol arena — `TrackSymbol` reads `symbol.Flags` to skip
    /// type parameters; Go reads through the `*ast.Symbol` pointer.
    pub symbols: Rc<RefCell<Vec<ast::Symbol>>>,
    /// `inner`.
    pub inner: Option<Rc<RefCell<dyn SymbolTracker + 'a>>>,
    /// `DisableTrackSymbol` — exported field in Go.
    pub disable_track_symbol: bool,
}

/// `NewSymbolTrackerImpl`. PORT: gains the shared symbol arena (`symbols`)
/// for the `symbol.Flags` read — see header.
pub fn new_symbol_tracker_impl<'a>(
    context: &NodeBuilderContext<'a>,
    tracker: Option<Rc<RefCell<dyn SymbolTracker + 'a>>>,
    symbols: Rc<RefCell<Vec<ast::Symbol>>>,
) -> SymbolTrackerImpl<'a> {
    // Go peels nested `*SymbolTrackerImpl` wrappers here; see the header
    // note for why that loop is omitted.
    SymbolTrackerImpl {
        tracked_symbols: context.tracked_symbols.clone(),
        reported_diagnostic: context.reported_diagnostic.clone(),
        symbols,
        inner: tracker,
        disable_track_symbol: false,
    }
}

impl<'a> SymbolTracker for SymbolTrackerImpl<'a> {
    /// `(this *SymbolTrackerImpl) TrackSymbol`.
    fn track_symbol(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
        nodes: &[ast::Node],
    ) -> bool {
        if !self.disable_track_symbol {
            if let Some(inner) = self.inner.as_ref()
                && inner.borrow_mut().track_symbol(symbol, enclosing_declaration, meaning, nodes)
            {
                self.on_diagnostic_reported();
                return true;
            }
            // Skip recording type parameters as they don't contribute to
            // late painted statements.
            let is_type_parameter = self.symbols.borrow()[symbol.index()]
                .flags
                .intersects(SymbolFlags::TYPE_PARAMETER);
            if !is_type_parameter {
                self.tracked_symbols.borrow_mut().push(TrackedSymbolArgs {
                    symbol,
                    enclosing_declaration,
                    meaning,
                });
            }
        }
        false
    }

    /// `(this *SymbolTrackerImpl) ReportInaccessibleThisError`.
    fn report_inaccessible_this_error(&mut self, nodes: &[ast::Node]) {
        self.on_diagnostic_reported();
        if let Some(inner) = self.inner.as_ref() {
            inner.borrow_mut().report_inaccessible_this_error(nodes);
        }
    }

    /// `(this *SymbolTrackerImpl) ReportPrivateInBaseOfClassExpression`.
    fn report_private_in_base_of_class_expression(
        &mut self,
        property_name: &str,
        nodes: &[ast::Node],
    ) {
        self.on_diagnostic_reported();
        if let Some(inner) = self.inner.as_ref() {
            inner
                .borrow_mut()
                .report_private_in_base_of_class_expression(property_name, nodes);
        }
    }

    /// `(this *SymbolTrackerImpl) ReportInaccessibleUniqueSymbolError`.
    fn report_inaccessible_unique_symbol_error(&mut self, nodes: &[ast::Node]) {
        self.on_diagnostic_reported();
        if let Some(inner) = self.inner.as_ref() {
            inner
                .borrow_mut()
                .report_inaccessible_unique_symbol_error(nodes);
        }
    }

    /// `(this *SymbolTrackerImpl) ReportCyclicStructureError`.
    fn report_cyclic_structure_error(&mut self, nodes: &[ast::Node]) {
        self.on_diagnostic_reported();
        if let Some(inner) = self.inner.as_ref() {
            inner.borrow_mut().report_cyclic_structure_error(nodes);
        }
    }

    /// `(this *SymbolTrackerImpl) ReportLikelyUnsafeImportRequiredError`.
    fn report_likely_unsafe_import_required_error(
        &mut self,
        specifier: &str,
        symbol_name: &str,
        nodes: &[ast::Node],
    ) {
        self.on_diagnostic_reported();
        if let Some(inner) = self.inner.as_ref() {
            inner.borrow_mut().report_likely_unsafe_import_required_error(
                specifier,
                symbol_name,
                nodes,
            );
        }
    }

    /// `(this *SymbolTrackerImpl) ReportTruncationError`.
    fn report_truncation_error(&mut self, nodes: &[ast::Node]) {
        self.on_diagnostic_reported();
        if let Some(inner) = self.inner.as_ref() {
            inner.borrow_mut().report_truncation_error(nodes);
        }
    }

    /// `(this *SymbolTrackerImpl) ReportNonlocalAugmentation`.
    fn report_nonlocal_augmentation(
        &mut self,
        containing_file: NodeId,
        parent_symbol: SymbolId,
        augmenting_symbol: SymbolId,
        nodes: &[ast::Node],
    ) {
        self.on_diagnostic_reported();
        if let Some(inner) = self.inner.as_ref() {
            inner.borrow_mut().report_nonlocal_augmentation(
                containing_file,
                parent_symbol,
                augmenting_symbol,
                nodes,
            );
        }
    }

    /// `(this *SymbolTrackerImpl) ReportNonSerializableProperty`.
    fn report_non_serializable_property(&mut self, property_name: &str, nodes: &[ast::Node]) {
        self.on_diagnostic_reported();
        if let Some(inner) = self.inner.as_ref() {
            inner
                .borrow_mut()
                .report_non_serializable_property(property_name, nodes);
        }
    }

    /// `(this *SymbolTrackerImpl) ReportInferenceFallback`.
    fn report_inference_fallback(&mut self, node: NodeId, nodes: &[ast::Node]) {
        if let Some(inner) = self.inner.as_ref() {
            inner.borrow_mut().report_inference_fallback(node, nodes);
        }
    }

    /// `(this *SymbolTrackerImpl) PushErrorFallbackNode`.
    fn push_error_fallback_node(&mut self, node: NodeId) {
        if let Some(inner) = self.inner.as_ref() {
            inner.borrow_mut().push_error_fallback_node(node);
        }
    }

    /// `(this *SymbolTrackerImpl) PopErrorFallbackNode`.
    fn pop_error_fallback_node(&mut self) {
        if let Some(inner) = self.inner.as_ref() {
            inner.borrow_mut().pop_error_fallback_node();
        }
    }
}

impl<'a> SymbolTrackerImpl<'a> {
    /// `(this *SymbolTrackerImpl) onDiagnosticReported`.
    fn on_diagnostic_reported(&self) {
        self.reported_diagnostic.set(true);
    }
}
