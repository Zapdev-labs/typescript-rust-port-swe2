// Ported from tsc/internal/transformers/declarations/tracker.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The declaration transform's `SymbolTracker` — the callback the nodebuilder
// uses to report symbol-accessibility and inference-fallback diagnostics
// while serializing inferred types.
//
// PORT notes:
//   - `*ast.Symbol` → `SymbolId`, `*ast.Node` → `NodeId`,
//     `*ast.SourceFile` → the SourceFile node's `NodeId`.
//   - `nodebuilder::SymbolTracker` trait methods thread `nodes: &[Node]`
//     (the trait was extended for this port — Go trackers dereference
//     `*ast.Node` pointers directly, and this tracker does not own the
//     arena). `symbols` is the live arena borrowed from
//     `TransformOptions::symbols` (shared with the transform). Reads
//     tolerate NodeIds minted inside the current resolver call
//     (synthesized nodes) by bounds-checking — Go would see the same
//     nodes as live pointers, but every such read path
//     (`get_source_file_of_node`, name lookups, diagnostics locations)
//     is only meaningful for bound parse-tree nodes.
//   - `checker.NewDiagnosticForNode` is reimplemented as the free function
//     `create_diagnostic_for_node` — identical logic to
//     `Checker::new_diagnostic_for_node` but taking the `&[Node]` arena
//     instead of the checker's `self` (the checker type cannot be depended
//     on from this crate).

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

use tsc_ast::diagnostic::{self, DiagnosticFile, DiagnosticRef};
use tsc_ast::{self as ast, FindAncestorResult, Node, NodeId, Symbol, SymbolFlags, SymbolId};
use tsc_nodebuilder::SymbolTracker;
use tsc_printer::{
    EmitResolver, SymbolAccessibility, SymbolAccessibilityResult,
};

use crate::declarations::diagnostics::{
    create_get_isolated_declaration_errors, GetIsolatedDeclarationError,
    GetSymbolAccessibilityDiagnostic,
};
use crate::declarations::host::DeclarationEmitHost;

/// `createDiagnosticForNode` — see the module PORT note above.
pub(crate) fn create_diagnostic_for_node<T: fmt::Display>(
    nodes: &[Node],
    node: Option<NodeId>,
    message: &'static tsc_diagnostics::Message,
    args: &[T],
) -> DiagnosticRef {
    let mut file = None;
    let mut loc = tsc_core::text::TextRange::default();
    if let Some(node) = node {
        if let Some(source_file) = ast::get_source_file_of_node(Some(node), nodes) {
            let sf = nodes[source_file].as_source_file();
            loc = tsc_scanner::scanner::get_error_range_for_node(sf, node, nodes);
            file = Some(DiagnosticFile::from_node(source_file, nodes));
        }
    }
    diagnostic::new_diagnostic(file, loc, message, args)
}

/// `type SymbolTrackerSharedState struct`.
pub struct SymbolTrackerSharedState<'a> {
    /// `lateMarkedStatements` — statements marked visible after their
    /// containing scope was already emitted; revisited by `transform`.
    pub late_marked_statements: Vec<NodeId>,
    /// `diagnostics` — accumulated declaration emit diagnostics.
    pub diagnostics: Vec<DiagnosticRef>,
    /// `getSymbolAccessibilityDiagnostic` — the selector installed by the
    /// current diagnostic context; `None` mirrors Go nil (panics if invoked,
    /// matching `throwDiagnostic`).
    pub get_symbol_accessibility_diagnostic: Option<GetSymbolAccessibilityDiagnostic>,
    /// `errorNameNode`.
    pub error_name_node: Option<NodeId>,
    /// `isolatedDeclarations`.
    pub isolated_declarations: bool,
    /// `stripInternal`.
    pub strip_internal: bool,
    /// `currentSourceFile` — `*ast.SourceFile` → its `NodeId`.
    pub current_source_file: Option<NodeId>,
    /// `resolver`.
    pub resolver: Rc<RefCell<dyn EmitResolver + 'a>>,
    /// `reportExpandoFunctionErrors` — installed by the transformer after
    /// construction (it needs `tx` state the shared state doesn't have).
    /// Takes the `nodes` arena like the other arena-touching callbacks.
    pub report_expando_function_errors: Option<Box<dyn Fn(NodeId, &[Node]) + 'a>>,
}

impl<'a> SymbolTrackerSharedState<'a> {
    /// `(s *SymbolTrackerSharedState) addDiagnostic`.
    pub fn add_diagnostic(&mut self, diag: DiagnosticRef) {
        self.diagnostics.push(diag);
    }
}

/// `type SymbolTrackerImpl struct`.
///
/// PORT: `SymbolTracker` trait methods are `&mut self`, so mutation happens
/// on `self` directly; interior-mutability cells are only needed for state
/// read/written while the tracker is shared (`state`, and the `nodes`
/// snapshot refreshed from `&self` contexts inside the transform).
pub struct SymbolTrackerImpl<'a> {
    /// `resolver`.
    pub resolver: Rc<RefCell<dyn EmitResolver + 'a>>,
    /// `state` — shared with the transformer (`Rc` mirrors the Go pointer
    /// `*SymbolTrackerSharedState`).
    pub state: Rc<RefCell<SymbolTrackerSharedState<'a>>>,
    /// `host`.
    #[allow(dead_code)]
    pub host: Rc<dyn DeclarationEmitHost + 'a>,
    /// `fallbackStack`.
    pub fallback_stack: Vec<NodeId>,
    /// `watchedClassSymbol` — class expression symbol watched for
    /// self-references during member serialization.
    pub watched_class_symbol: Option<SymbolId>,
    /// `classSymbolTracked`.
    pub class_symbol_tracked: bool,
    /// `getIsolatedDeclarationError`.
    get_isolated_declaration_error: GetIsolatedDeclarationError<'a>,
    // The node arena the Go implementation reaches through `*ast.Node`
    // pointers arrives as the `nodes: &[Node]` parameter on the
    // `SymbolTracker` trait methods — see `tsc-nodebuilder::SymbolTracker`.
    /// The live bound symbol arena (`TransformOptions::symbols`).
    symbols: Option<&'a RefCell<Vec<Symbol>>>,
}

impl<'a> SymbolTrackerImpl<'a> {
    /// `NewSymbolTracker(host, resolver, state)` — gains the `symbols`
    /// arena parameter (see the module PORT note).
    pub fn new(
        host: Rc<dyn DeclarationEmitHost + 'a>,
        resolver: Rc<RefCell<dyn EmitResolver + 'a>>,
        state: Rc<RefCell<SymbolTrackerSharedState<'a>>>,
        symbols: Option<&'a RefCell<Vec<Symbol>>>,
    ) -> SymbolTrackerImpl<'a> {
        SymbolTrackerImpl {
            get_isolated_declaration_error:
                create_get_isolated_declaration_errors(resolver.clone()),
            host,
            resolver,
            state,
            fallback_stack: Vec::new(),
            watched_class_symbol: None,
            class_symbol_tracked: false,
                        symbols,
        }
    }

    /// `(s *SymbolTrackerImpl) isBoundExpando`.
    fn is_bound_expando(&self, node: NodeId, nodes: &[Node]) -> bool {
        let Some(n) = nodes.get(node.local_index() as usize) else {
            return false;
        };
        if !(ast::is_expando_property_declaration(Some(node), nodes)
            && ast::is_property_access_expression(&nodes[n
                .as_binary_expression()
                .left
                .expect("expando BinaryExpression.left")]))
        {
            return false;
        }
        // Match transformExpandoAssignment: only an assignment rooted at an identifier (`f.x = ...`) can bind an expando
        // property; `this.x = ...`, `super.x = ...`, `f().x = ...` and the like have no referenced declaration.
        let ns = ast::get_leftmost_access_expression(
            nodes[node].as_binary_expression().left.unwrap(),
            nodes,
        );
        if !ast::is_identifier(&nodes[ns]) {
            return false;
        }
        let Some(ref_decl) = self
            .resolver
            .borrow()
            .get_referenced_value_declaration_unsafe(ns, nodes)
        else {
            return false;
        };
        self.resolver
            .borrow()
            .is_expando_function_declaration_unsafe(ref_decl, nodes)
    }

    /// `(s *SymbolTrackerImpl) isChildOfBoundExpando`.
    fn is_child_of_bound_expando(&self, node: NodeId, nodes: &[Node]) -> bool {
        ast::find_ancestor_or_quit(Some(node), nodes, &mut |n, nodes| {
            if ast::is_source_file(n) || ast::is_block(n) {
                return FindAncestorResult::Quit;
            }
            ast::to_find_ancestor_result(self.is_bound_expando(n.id, nodes))
        })
        .is_some()
    }

    /// `(s *SymbolTrackerImpl) errorFallbackNode`.
    fn error_fallback_node(&self) -> Option<NodeId> {
        self.fallback_stack.last().copied()
    }

    /// `(s *SymbolTrackerImpl) errorLocation`.
    fn error_location(&self) -> Option<NodeId> {
        self.state
            .borrow()
            .error_name_node
            .or_else(|| self.error_fallback_node())
    }

    /// `(s *SymbolTrackerImpl) errorDeclarationNameWithFallback`.
    fn error_declaration_name_with_fallback(&self, nodes: &[Node]) -> String {
        if let Some(error_name_node) = self.state.borrow().error_name_node {
            return tsc_scanner::utilities::declaration_name_to_string(
                Some(error_name_node),
                nodes,
            );
        }
        if let Some(fallback) = self.error_fallback_node() {
            if let Some(name) = ast::get_name_of_declaration(Some(fallback), nodes) {
                return tsc_scanner::utilities::declaration_name_to_string(Some(name), nodes);
            }
            if ast::is_export_assignment(&nodes[fallback]) {
                if nodes[fallback].as_export_assignment().is_export_equals {
                    return "export=".to_string();
                }
                return "default".to_string();
            }
        }
        "(Missing)".to_string() // same fallback declarationNameToString uses when node is zero-width (ie, nameless)
    }

    /// `(s *SymbolTrackerImpl) handleSymbolAccessibilityError` — `pub(crate)`
    /// for the transform's direct `isEntityNameVisible` handling.
    pub(crate) fn handle_symbol_accessibility_error(
        &mut self,
        symbol_accessibility_result: SymbolAccessibilityResult,
        nodes: &[Node],
    ) -> bool {
        if symbol_accessibility_result.accessibility == SymbolAccessibility::Accessible {
            // Add aliases back onto the possible imports list if they're not there so we can try them again with updated visibility info
            if !symbol_accessibility_result
                .aliases_to_make_visible
                .is_empty()
            {
                for &ref_node in &symbol_accessibility_result.aliases_to_make_visible {
                    let mut state = self.state.borrow_mut();
                    state.late_marked_statements = tsc_core::core::append_if_unique(
                        &state.late_marked_statements,
                        ref_node,
                    )
                    .into_owned();
                }
            }
            // TODO: Do all these accessibility checks inside/after the first pass in the checker when declarations are enabled, if possible

            // The checker should issue errors on unresolvable names, skip the declaration emit error for using a private/unreachable name for those
        } else if symbol_accessibility_result.accessibility != SymbolAccessibility::NotResolved {
            // Report error
            let error_info = self
                .state
                .borrow()
                .get_symbol_accessibility_diagnostic
                .as_ref()
                .and_then(|selector| selector(&symbol_accessibility_result, nodes));
            if let Some(info) = error_info {
                let diag_node = symbol_accessibility_result
                    .error_node
                    .or(info.error_node);
                let diag = if let Some(type_name) = info.type_name {
                    create_diagnostic_for_node(
                        nodes,
                        diag_node,
                        info.diagnostic_message,
                        &[
                            tsc_scanner::utilities::get_text_of_node(type_name, nodes),
                            symbol_accessibility_result.error_symbol_name.clone(),
                            symbol_accessibility_result.error_module_name.clone(),
                        ],
                    )
                } else {
                    create_diagnostic_for_node(
                        nodes,
                        diag_node,
                        info.diagnostic_message,
                        &[
                            symbol_accessibility_result.error_symbol_name.clone(),
                            symbol_accessibility_result.error_module_name.clone(),
                        ],
                    )
                };
                self.state.borrow_mut().add_diagnostic(diag);
                return true;
            }
        }
        false
    }
}

impl<'a> SymbolTracker for SymbolTrackerImpl<'a> {
    /// `(s *SymbolTrackerImpl) PopErrorFallbackNode`.
    fn pop_error_fallback_node(&mut self) {
        self.fallback_stack.pop();
    }

    /// `(s *SymbolTrackerImpl) PushErrorFallbackNode`.
    fn push_error_fallback_node(&mut self, node: NodeId) {
        self.fallback_stack.push(node);
    }

    /// `(s *SymbolTrackerImpl) ReportCyclicStructureError`.
    fn report_cyclic_structure_error(&mut self, nodes: &[Node]) {
        if let Some(location) = self.error_location() {
            let name = self.error_declaration_name_with_fallback(nodes);
            self.state.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                nodes,
                Some(location),
                &tsc_diagnostics::The_inferred_type_of_0_references_a_type_with_a_cyclic_structure_which_cannot_be_trivially_serialized_A_type_annotation_is_necessary,
                &[name],
            ));
        }
    }

    /// `(s *SymbolTrackerImpl) ReportInaccessibleThisError`.
    fn report_inaccessible_this_error(&mut self, nodes: &[Node]) {
        if let Some(location) = self.error_location() {
            let name = self.error_declaration_name_with_fallback(nodes);
            self.state.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                nodes,
                Some(location),
                &tsc_diagnostics::The_inferred_type_of_0_references_an_inaccessible_1_type_A_type_annotation_is_necessary,
                &[name, "this".to_string()],
            ));
        }
    }

    /// `(s *SymbolTrackerImpl) ReportInaccessibleUniqueSymbolError`.
    fn report_inaccessible_unique_symbol_error(&mut self, nodes: &[Node]) {
        if let Some(location) = self.error_location() {
            let name = self.error_declaration_name_with_fallback(nodes);
            self.state.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                nodes,
                Some(location),
                &tsc_diagnostics::The_inferred_type_of_0_references_an_inaccessible_1_type_A_type_annotation_is_necessary,
                &[name, "unique symbol".to_string()],
            ));
        }
    }

    /// `(s *SymbolTrackerImpl) ReportInferenceFallback`.
    fn report_inference_fallback(&mut self, node: NodeId, nodes: &[Node]) {
        if !self.state.borrow().isolated_declarations {
            return;
        }
        {
            if ast::get_source_file_of_node(Some(node), nodes)
                != self.state.borrow().current_source_file
            {
                return; // Nested error on a declaration in another file - ignore, will be reemitted if file is in the output file set
            }
            if self
                .resolver
                .borrow()
                .is_expando_function_declaration_unsafe(node, nodes)
            {
                // within a node builder call that should already lock the checker, use the unsafe call
                if let Some(report) = self.state.borrow().report_expando_function_errors.as_ref() {
                    report(node, nodes);
                }
            }
            if !self.is_child_of_bound_expando(node, nodes) {
                // expando props get an error when their host is visited by the above, this prevents a follow-on error on a non-inferrable expression
                let symbols = self
                    .symbols
                    .expect("SymbolTrackerImpl requires TransformOptions::symbols")
                    .borrow();
                let diag = (self.get_isolated_declaration_error)(node, nodes, &symbols);
                self.state.borrow_mut().add_diagnostic(diag);
            }
        }
    }

    /// `(s *SymbolTrackerImpl) ReportLikelyUnsafeImportRequiredError`.
    fn report_likely_unsafe_import_required_error(
        &mut self,
        specifier: &str,
        symbol_name: &str,
        nodes: &[Node],
    ) {
        if let Some(location) = self.error_location() {
            let name = self.error_declaration_name_with_fallback(nodes);
            let diag = if !symbol_name.is_empty() {
                create_diagnostic_for_node(
                    nodes,
                    Some(location),
                    &tsc_diagnostics::The_inferred_type_of_0_cannot_be_named_without_a_reference_to_2_from_1_This_is_likely_not_portable_A_type_annotation_is_necessary,
                    &[name, specifier.to_string(), symbol_name.to_string()],
                )
            } else {
                create_diagnostic_for_node(
                    nodes,
                    Some(location),
                    &tsc_diagnostics::The_inferred_type_of_0_cannot_be_named_without_a_reference_to_1_This_is_likely_not_portable_A_type_annotation_is_necessary,
                    &[name, specifier.to_string()],
                )
            };
            self.state.borrow_mut().add_diagnostic(diag);
        }
    }

    /// `(s *SymbolTrackerImpl) ReportNonSerializableProperty`.
    fn report_non_serializable_property(&mut self, property_name: &str, nodes: &[Node]) {
        if let Some(location) = self.error_location() {
            self.state.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                nodes,
                Some(location),
                &tsc_diagnostics::The_type_of_this_node_cannot_be_serialized_because_its_property_0_cannot_be_serialized,
                &[property_name],
            ));
        }
    }

    /// `(s *SymbolTrackerImpl) ReportNonlocalAugmentation`.
    fn report_nonlocal_augmentation(
        &mut self,
        containing_file: NodeId,
        parent_symbol: SymbolId,
        augmenting_symbol: SymbolId,
        nodes: &[Node],
    ) {
        let symbols = self
            .symbols
            .expect("SymbolTrackerImpl requires TransformOptions::symbols")
            .borrow();
        let primary_declaration = tsc_core::core::find(
            &symbols[parent_symbol.index()].declarations,
            |&d| {
                ast::get_source_file_of_node(Some(d), nodes) == Some(containing_file)
            },
        );
        let augmenting_declarations = tsc_core::core::filter(
            &symbols[augmenting_symbol.index()].declarations,
            |&d| {
                ast::get_source_file_of_node(Some(d), nodes) != Some(containing_file)
            },
        );
        if let Some(primary_declaration) = primary_declaration {
            if !augmenting_declarations.is_empty() {
                for &augmentation in augmenting_declarations.iter() {
                    let diag = create_diagnostic_for_node(
                        nodes,
                        Some(augmentation),
                        &tsc_diagnostics::Declaration_augments_declaration_in_another_file_This_cannot_be_serialized,
                        &[] as &[String],
                    );
                    let related = create_diagnostic_for_node(
                        nodes,
                        Some(primary_declaration),
                        &tsc_diagnostics::This_is_the_declaration_being_augmented_Consider_moving_the_augmenting_declaration_into_the_same_file,
                        &[] as &[String],
                    );
                    diag.lock().unwrap().add_related_info(Some(related));
                    self.state.borrow_mut().add_diagnostic(diag);
                }
            }
        }
    }

    /// `(s *SymbolTrackerImpl) ReportPrivateInBaseOfClassExpression`.
    fn report_private_in_base_of_class_expression(
        &mut self,
        property_name: &str,
        nodes: &[Node],
    ) {
        if let Some(location) = self.error_location() {
            let diag = create_diagnostic_for_node(
                nodes,
                Some(location),
                &tsc_diagnostics::Property_0_of_exported_anonymous_class_type_may_not_be_private_or_protected,
                &[property_name],
            );
            // Bounds-tolerant reads: `location` may be a synthesized node
            // minted after the arena view was captured (module PORT note).
            let parent_is_variable_declaration = nodes
                .get(location.local_index() as usize)
                .and_then(|n| n.parent)
                .and_then(|p| nodes.get(p.local_index() as usize))
                .is_some_and(ast::is_variable_declaration);
            if parent_is_variable_declaration {
                let related = create_diagnostic_for_node(
                    nodes,
                    Some(location),
                    &tsc_diagnostics::Add_a_type_annotation_to_the_variable_0,
                    &[self.error_declaration_name_with_fallback(nodes)],
                );
                diag.lock().unwrap().add_related_info(Some(related));
            }
            self.state.borrow_mut().add_diagnostic(diag);
        }
    }

    /// `(s *SymbolTrackerImpl) ReportTruncationError`.
    fn report_truncation_error(&mut self, nodes: &[Node]) {
        if let Some(location) = self.error_location() {
            self.state.borrow_mut().add_diagnostic(create_diagnostic_for_node(
                nodes,
                Some(location),
                &tsc_diagnostics::The_inferred_type_of_this_node_exceeds_the_maximum_length_the_compiler_will_serialize_An_explicit_type_annotation_is_needed,
                &[] as &[String],
            ));
        }
    }

    /// `(s *SymbolTrackerImpl) TrackSymbol`.
    fn track_symbol(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
        nodes: &[Node],
    ) -> bool {
        {
            let symbols = self
                .symbols
                .expect("SymbolTrackerImpl requires TransformOptions::symbols")
                .borrow();
            if symbols[symbol.index()].flags.intersects(SymbolFlags::TYPE_PARAMETER) {
                return false;
            }
        }
        // When watching for a class expression symbol, record its usage without
        // reporting accessibility errors — the caller will handle visibility by
        // wrapping the class in a namespace.
        if self.watched_class_symbol.is_some() && Some(symbol) == self.watched_class_symbol {
            self.class_symbol_tracked = true;
            return false;
        }
        let symbols = self
            .symbols
            .expect("SymbolTrackerImpl requires TransformOptions::symbols")
            .borrow();
        let result = self.resolver.borrow().is_symbol_accessible(
            symbol,
            enclosing_declaration,
            meaning,
            /*should_compute_alias_to_mark_visible*/ true,
            nodes,
            &symbols,
        );
        self.handle_symbol_accessibility_error(result, nodes)
    }
}
