// Ported from tsc/internal/checker/emitresolver.go @
// ec47d33c23e464a17cdf2475632cba629bee8763
//
// `EmitResolver` — the checker-side implementation of
// `tsc_printer::EmitResolver` — plus `EmitResolverLinks` and its payload
// structs (`JSXLinks`, `DeclarationLinks`, `DeclarationFileLinks`).
//
// PORT notes:
//
// - `checker *Checker` + `checkerMu *sync.Mutex` → `Rc<RefCell<Checker>>`.
//   Go methods that take the lock become `self.checker.borrow_mut()`; Go's
//   `*Unsafe` / explicitly-unlocked methods (which run while the caller
//   already holds `checkerMu`) reacquire the checker through
//   `RefCell::as_ptr` so they also work when a `borrow_mut` is already live
//   on the stack — the unsafe deref is documented at each site. This mirrors
//   the aliasing Go relies on: one ambient exclusive access, no data races
//   (the pipeline is single-threaded; `Checker` is `!Send` anyway).
// - `emitContext *printer.EmitContext` → `Rc<RefCell<EmitContext>>`, the
//   same handle shape `TransformOptions::context` and the declaration
//   transformer use. `emit_context()` can only hand out `&EmitContext`, so
//   it goes through `as_ptr` (see `emit_context` SAFETY note).
// - `isValueAliasDeclaration`/`aliasMarkingVisitor` Go method-value fields
//   become plain methods (Rust has no method values).
// - `tracker nodebuilder.SymbolTracker` arrives as `&dyn SymbolTracker` per
//   the `tsc_printer::EmitResolver` trait, but `track_symbol` is `&mut` and
//   the `NodeBuilder` serialize APIs take `Option<Box<dyn SymbolTracker>>`.
//   `tracker_ref` reacquires `&mut` behind a SAFETY-documented cast and
//   `TrackerRef` reboxes it — Go passes the same interface value through.
// - `nodes: &[Node]`/`nodes: &mut Vec<Node>` arena parameters come from the
//   trait surface; checker-internal reads go through `c.program_nodes`.
// - `NodeBuilder` gets a fresh `EmitContext` (`EmitContext::new`) — Go
//   shares `r.emitContext`, but `EmitContext` is not `Clone`/`Copy` and
//   `new_node_builder` consumes one; the builder only needs its own shared
//   tables (`PORT(deviation)`).

use std::cell::{RefCell, RefMut};
use std::rc::Rc;

use rustc_hash::FxHashSet;
use tsc_ast::{self as ast, Node, NodeId, Symbol, SymbolId};
use tsc_binder::referenceresolver::{
    ReferenceResolver, ReferenceResolverHooks, ReferenceResolverImpl, new_reference_resolver,
};
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::Tristate;
use tsc_core::{core as core_helpers, linkstore::LinkStore};
use tsc_evaluator as evaluator;
use tsc_jsnum::PseudoBigInt;
use tsc_nodebuilder::{self as nodebuilder, SymbolTracker};
use tsc_printer::{EmitContext, SymbolAccessibility, SymbolAccessibilityResult};

use crate::checker_core::{Checker, is_tuple_type};
use crate::nodebuilder::NodeBuilder;
use crate::nodebuilder::new_node_builder;
use crate::types::TypeFlags;

/// `type JSXLinks struct` (emitresolver.go) — links for jsx.
#[derive(Default)]
pub struct JsxLinks {
    /// `importRef`.
    pub import_ref: Option<NodeId>,
}

/// `type DeclarationLinks struct` (emitresolver.go) — links for
/// declarations.
#[derive(Default)]
pub struct DeclarationLinks {
    /// `isVisible` — if declaration is depended upon by exported
    /// declarations.
    pub is_visible: Tristate,
}

/// `type DeclarationFileLinks struct` (emitresolver.go).
#[derive(Default)]
pub struct DeclarationFileLinks {
    /// `aliasesMarked` — if file has had alias visibility marked.
    pub aliases_marked: bool,
}

/// `type EmitResolverLinks struct` (emitresolver.go) — owned by
/// `Checker::emit_resolver_links`.
#[derive(Default)]
pub struct EmitResolverLinks {
    /// `jsxLinks`.
    pub jsx_links: LinkStore<NodeId, JsxLinks>,
    /// `declarationLinks`.
    pub declaration_links: LinkStore<NodeId, DeclarationLinks>,
    /// `declarationFileLinks`.
    pub declaration_file_links: LinkStore<NodeId, DeclarationFileLinks>,
}

/// `type EmitResolver struct` (emitresolver.go).
pub struct EmitResolver {
    /// `checker`.
    pub(crate) checker: Rc<RefCell<Checker>>,
    /// `emitContext`.
    emit_context: Rc<RefCell<EmitContext>>,
    /// `r.checker.compilerOptions`, snapshotted so the lazily-built
    /// `referenceResolver` can borrow it (`&'static` via `Rc` pin — see
    /// `reference_resolver`).
    options: Rc<CompilerOptions>,
    /// `requestNodeBuilder`.
    request_node_builder: RefCell<Option<NodeBuilder>>,
    /// `referenceResolver`.
    reference_resolver: RefCell<Option<ReferenceResolverImpl<'static>>>,
    // `isValueAliasDeclaration`/`aliasMarkingVisitor` are plain methods —
    // see the header note.
}

/// `func newEmitResolver`.
///
/// PORT: `checker` is the shared `Rc<RefCell<Checker>>` (the caller keeps a
/// clone); `emit_context` is the `Rc<RefCell<EmitContext>>` the caller also
/// hands to the transform pipeline (see `declarations/transform.rs`).
/// Go panics on a nil emit context; here `emit_context` is a required
/// argument so that precondition is static.
pub fn new_emit_resolver(
    checker: Rc<RefCell<Checker>>,
    emit_context: Rc<RefCell<EmitContext>>,
) -> EmitResolver {
    let options = checker.borrow().compiler_options.clone();
    EmitResolver {
        checker,
        emit_context,
        options,
        request_node_builder: RefCell::new(None),
        reference_resolver: RefCell::new(None),
    }
}

/// `(r *EmitResolver) checker` access — Go's `r.checkerMu.Lock()`.
fn checker_lock<'a>(checker: &'a Rc<RefCell<Checker>>) -> RefMut<'a, Checker> {
    checker.borrow_mut()
}

/// `(r *EmitResolver) checker` access where Go deliberately does NOT lock —
/// `*Unsafe` variants and tracker-reentrant paths run while the caller's
/// lock is already held.
///
/// SAFETY: `RefCell::as_ptr` reacquires `&mut Checker` while an outer
/// `borrow_mut` may be live — that is exactly what Go's unlocked `r.checker`
/// dereference does under a held `checkerMu`. The emit pipeline is
/// single-threaded and the checker is never touched through two live
/// `&mut`s at the same instant (the outer `RefMut` is inert while the inner
/// call runs), matching Go's semantics.
#[allow(clippy::mut_from_ref)]
fn checker_unchecked<'a>(checker: &'a Rc<RefCell<Checker>>) -> &'a mut Checker {
    unsafe { &mut *checker.as_ptr() }
}

/// `tracker.TrackSymbol` — the trait hands us `&dyn SymbolTracker` while
/// `track_symbol` is `&mut`; Go passes the interface value (the same object)
/// straight through.
///
/// SAFETY: callers pass a borrow of a tracker they own; the tracker is only
/// mutated during this call and no other `&mut` to it is live — identical
/// aliasing to Go's interface value.
pub(crate) fn tracker_mut<'t>(tracker: &dyn SymbolTracker) -> &'t mut dyn SymbolTracker
where
    dyn SymbolTracker: 't,
{
    unsafe { &mut *(tracker as *const dyn SymbolTracker as *mut dyn SymbolTracker) }
}

/// Wraps the reacquired `&mut dyn SymbolTracker` so it can be handed to the
/// `NodeBuilder` serialize APIs, which take `Option<Box<dyn SymbolTracker>>`.
struct TrackerRef<'a>(&'a mut dyn SymbolTracker);

impl nodebuilder::SymbolTracker for TrackerRef<'_> {
    fn track_symbol(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: ast::SymbolFlags,
        nodes: &[Node],
    ) -> bool {
        self.0.track_symbol(symbol, enclosing_declaration, meaning, nodes)
    }
    fn report_inaccessible_this_error(&mut self, nodes: &[Node]) {
        self.0.report_inaccessible_this_error(nodes)
    }
    fn report_private_in_base_of_class_expression(
        &mut self,
        property_name: &str,
        nodes: &[Node],
    ) {
        self.0
            .report_private_in_base_of_class_expression(property_name, nodes)
    }
    fn report_inaccessible_unique_symbol_error(&mut self, nodes: &[Node]) {
        self.0.report_inaccessible_unique_symbol_error(nodes)
    }
    fn report_cyclic_structure_error(&mut self, nodes: &[Node]) {
        self.0.report_cyclic_structure_error(nodes)
    }
    fn report_likely_unsafe_import_required_error(
        &mut self,
        specifier: &str,
        symbol_name: &str,
        nodes: &[Node],
    ) {
        self.0
            .report_likely_unsafe_import_required_error(specifier, symbol_name, nodes)
    }
    fn report_truncation_error(&mut self, nodes: &[Node]) {
        self.0.report_truncation_error(nodes)
    }
    fn report_nonlocal_augmentation(
        &mut self,
        containing_file: NodeId,
        parent_symbol: SymbolId,
        augmenting_symbol: SymbolId,
        nodes: &[Node],
    ) {
        self.0.report_nonlocal_augmentation(
            containing_file,
            parent_symbol,
            augmenting_symbol,
            nodes,
        )
    }
    fn report_non_serializable_property(&mut self, property_name: &str, nodes: &[Node]) {
        self.0.report_non_serializable_property(property_name, nodes)
    }
    fn report_inference_fallback(&mut self, node: NodeId, nodes: &[Node]) {
        self.0.report_inference_fallback(node, nodes)
    }
    fn push_error_fallback_node(&mut self, node: NodeId) {
        self.0.push_error_fallback_node(node)
    }
    fn pop_error_fallback_node(&mut self) {
        self.0.pop_error_fallback_node()
    }
    fn take_symbol_tracker_impl_inner(
        &mut self,
    ) -> Option<Option<Box<dyn nodebuilder::SymbolTracker>>> {
        self.0.take_symbol_tracker_impl_inner()
    }
}

/// `c.resolveName` — invokes the checker's `resolve_name` thunk (the same
/// pattern `checker_b.rs`'s `call_resolve_name` uses; that helper is
/// module-private so it's mirrored here).
pub(crate) fn call_resolve_name(
    c: &mut Checker,
    location: Option<NodeId>,
    name: &str,
    meaning: ast::SymbolFlags,
    name_not_found_message: Option<&'static tsc_diagnostics::Message>,
    is_use: bool,
    exclude_globals: bool,
) -> Option<SymbolId> {
    let f = c.resolve_name.clone().expect("Checker::resolve_name");
    f(c, location, name, meaning, name_not_found_message, is_use, exclude_globals)
}

/// `isConstEnumOrConstEnumOnlyModule` (emitresolver.go).
pub(crate) fn is_const_enum_or_const_enum_only_module(s: &Symbol) -> bool {
    // `IsConstEnumSymbol(s)` inlined — a symbol without `CheckFlags` is
    // non-nil here, so the flag test is the whole predicate.
    s.flags.intersects(ast::SymbolFlags::CONST_ENUM)
        || s.flags.intersects(ast::SymbolFlags::CONST_ENUM_ONLY_MODULE)
}

/// `isDeclarationReadonly` (checker/utilities.go).
///
/// PORT(mirrored): the canonical helper lives in the checker's utilities.go
//  wave; this copy is removed when `utilities.rs` lands it.
fn is_declaration_readonly(declaration: NodeId, nodes: &[Node]) -> bool {
    // `!ast.IsParameterPropertyDeclaration(declaration, declaration.Parent)`
    // — a nil parent means "not a parameter property" in Go.
    ast::get_combined_modifier_flags(declaration, nodes).intersects(ast::ModifierFlags::READONLY)
        && nodes[declaration]
            .parent
            .is_none_or(|p| !ast::is_parameter_property_declaration(&nodes[declaration], &nodes[p]))
}

/// `isFreshLiteralType` (checker/utilities.go).
///
/// PORT(mirrored): as above.
fn is_fresh_literal_type(c: &Checker, t: crate::types::TypeId) -> bool {
    crate::checker_d::is_fresh_literal_type(&c.types, t)
}

/// `pseudoBigIntToString` (checker/utilities.go).
///
/// PORT(mirrored): as above.
fn pseudo_big_int_to_string(value: PseudoBigInt) -> String {
    value.string()
}

/// `isCommonJSModuleExports` (emitresolver.go).
fn is_commonjs_module_exports(node: NodeId, nodes: &[Node]) -> bool {
    if !ast::is_binary_expression(&nodes[node]) {
        return false;
    }
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    if !ast::is_expression_statement(&nodes[parent]) {
        return false;
    }
    let Some(file) = nodes[parent].parent else {
        return false;
    };
    if !ast::is_source_file(&nodes[file])
        || nodes[file]
            .as_source_file()
            .common_js_module_indicator
            .is_none()
    {
        return false;
    }
    matches!(
        ast::get_assignment_declaration_kind(node, nodes),
        ast::JsDeclarationKind::ModuleExports | ast::JsDeclarationKind::ExportsProperty
    )
}

impl EmitResolver {
    /// `(r *EmitResolver) nodeBuilder` — lazily creates the request node
    /// builder. PORT(deviation): `new_node_builder` consumes an owned
    /// `EmitContext`, so the builder gets a fresh one rather than sharing
    /// `r.emitContext` (see header).
    fn node_builder(&self, c: &Checker) -> RefMut<'_, NodeBuilder> {
        {
            let mut nb = self.request_node_builder.borrow_mut();
            if nb.is_none() {
                *nb = Some(new_node_builder(c, EmitContext::new()));
            }
        }
        RefMut::map(self.request_node_builder.borrow_mut(), |o| {
            o.as_mut().expect("node builder")
        })
    }

    /// `(r *EmitResolver) getReferenceResolver` — lazily creates the binder
    /// `ReferenceResolver`, wiring its hooks to the checker.
    ///
    /// PORT: the hooks capture the `Rc<RefCell<Checker>>` and reacquire it
    /// via `checker_unchecked` — Go's hooks are plain method values that run
    /// under the ambient `checkerMu`, so they must work both when the caller
    /// locked (a live `borrow_mut`) and when it didn't.
    fn reference_resolver(&self) -> RefMut<'_, ReferenceResolverImpl<'static>> {
        {
            let mut resolver = self.reference_resolver.borrow_mut();
            if resolver.is_none() {
                // SAFETY: `self.options` is an `Rc` clone held for the life
                // of the resolver, so the pointee stays pinned and never
                // moves or drops early — same as Go's shared `*CompilerOptions`.
                let options: &'static CompilerOptions =
                    unsafe { &*Rc::as_ptr(&self.options) };
                *resolver = Some(self.new_reference_resolver(options));
            }
        }
        RefMut::map(self.reference_resolver.borrow_mut(), |o| {
            o.as_mut().expect("reference resolver")
        })
    }

    /// The `binder.NewReferenceResolver` call inside `getReferenceResolver`.
    fn new_reference_resolver(
        &self,
        options: &'static CompilerOptions,
    ) -> ReferenceResolverImpl<'static> {
        let c = self.checker.clone();
        new_reference_resolver(
            options,
            ReferenceResolverHooks {
                resolve_name: Some(Box::new({
                    let c = c.clone();
                    move |location, name, meaning, msg, is_use, exclude_globals| {
                        call_resolve_name(
                            checker_unchecked(&c),
                            location,
                            name,
                            meaning,
                            msg,
                            is_use,
                            exclude_globals,
                        )
                    }
                })),
                get_resolved_symbol: Some(Box::new({
                    let c = c.clone();
                    move |node| checker_unchecked(&c).get_resolved_symbol_or_nil(node)
                })),
                get_merged_symbol: Some(Box::new({
                    let c = c.clone();
                    move |symbol| Some(checker_unchecked(&c).get_merged_symbol(symbol))
                })),
                get_parent_of_symbol: Some(Box::new({
                    let c = c.clone();
                    move |symbol| checker_unchecked(&c).get_parent_of_symbol(symbol)
                })),
                get_symbol_of_declaration: Some(Box::new({
                    let c = c.clone();
                    move |node| checker_unchecked(&c).get_symbol_of_declaration(node)
                })),
                get_type_only_alias_declaration: Some(Box::new({
                    let c = c.clone();
                    move |symbol, meaning| {
                        checker_unchecked(&c).get_type_only_alias_declaration_ex(symbol, meaning)
                    }
                })),
                get_export_symbol_of_value_symbol_if_exported: Some(Box::new({
                    let c = c.clone();
                    move |symbol| {
                        checker_unchecked(&c)
                            .get_export_symbol_of_value_symbol_if_exported(Some(symbol))
                    }
                })),
                get_element_access_expression_name: Some(Box::new({
                    let c = c.clone();
                    move |node| {
                        let c = checker_unchecked(&c);
                        let nodes = c.program_nodes(node);
                        let (name, ok) = c.try_get_element_access_expression_name(&nodes, node);
                        ok.then_some(name)
                    }
                })),
            },
        )
    }

    /// `(r *EmitResolver) aliasMarkingVisitorWorker` — `r.aliasMarkingVisitor`
    /// in Go (the field is initialized to this worker).
    fn alias_marking_visitor_worker(&self, c: &mut Checker, node: NodeId, nodes: &[Node]) -> bool {
        match nodes[node].kind {
            ast::Kind::BinaryExpression => {
                if is_commonjs_module_exports(node, nodes)
                    && ast::is_identifier(
                        &nodes[nodes[node].as_binary_expression().right.unwrap()],
                    )
                {
                    self.mark_linked_aliases(
                        c,
                        nodes[node].as_binary_expression().right.unwrap(),
                        nodes,
                    );
                }
            }
            ast::Kind::ExportAssignment => {
                if let Some(expression) = nodes[node].expression()
                    && nodes[expression].kind == ast::Kind::Identifier
                {
                    self.mark_linked_aliases(c, expression, nodes);
                }
            }
            ast::Kind::ExportSpecifier => {
                if let Some(name) = nodes[node].property_name_or_name() {
                    self.mark_linked_aliases(c, name, nodes);
                }
            }
            _ => {}
        }
        nodes[node].for_each_child(nodes, &mut |child| {
            self.alias_marking_visitor_worker(c, child, nodes)
        })
    }

    /// `(r *EmitResolver) markLinkedAliases` — sets the `isVisible` link on
    /// statements the Identifier or ExportName node points at; follows chains
    /// of `import d = a.b.c`.
    fn mark_linked_aliases(&self, c: &mut Checker, node: NodeId, nodes: &[Node]) {
        let mut export_symbol: Option<SymbolId> = None;
        let parent = nodes[node].parent;
        if nodes[node].kind != ast::Kind::StringLiteral
            && let Some(parent) = parent
            && (ast::is_export_assignment(&nodes[parent])
                || is_commonjs_module_exports(parent, nodes))
        {
            let text = nodes[node].text(nodes).into_owned();
            export_symbol = call_resolve_name(
                c,
                Some(node),
                &text,
                ast::SymbolFlags::VALUE
                    | ast::SymbolFlags::TYPE
                    | ast::SymbolFlags::NAMESPACE
                    | ast::SymbolFlags::ALIAS,
                None, /*nameNotFoundMessage*/
                false, /*isUse*/
                false, /*excludeGlobals*/
            );
        } else if parent.is_some_and(|p| nodes[p].kind == ast::Kind::ExportSpecifier) {
            export_symbol = c.get_target_of_export_specifier(
                parent.unwrap(),
                ast::SymbolFlags::VALUE
                    | ast::SymbolFlags::TYPE
                    | ast::SymbolFlags::NAMESPACE
                    | ast::SymbolFlags::ALIAS,
                false,
            );
        }

        let mut visited: FxHashSet<SymbolId> = FxHashSet::default(); // guard against circular imports
        while let Some(symbol) = export_symbol {
            if !visited.insert(symbol) {
                break;
            }

            let mut next_symbol: Option<SymbolId> = None;
            let declarations = c.symbol_arena.borrow()[symbol.index()].declarations.clone();
            for declaration in declarations {
                c.emit_resolver_links
                    .declaration_links
                    .get(declaration)
                    .is_visible = Tristate::True;

                // declaration arenas may differ per file — re-read through
                // the declaration's own arena like Go derefs the pointer.
                let declaration_nodes = c.program_nodes(declaration);
                if ast::is_internal_module_import_equals_declaration(
                    &declaration_nodes[declaration],
                    &declaration_nodes,
                ) {
                    // Add the referenced top container visible
                    let internal_module_reference = declaration_nodes[declaration]
                        .as_import_equals_declaration()
                        .module_reference
                        .expect("internal module reference");
                    let first_identifier =
                        ast::get_first_identifier(internal_module_reference, &declaration_nodes);
                    let text = declaration_nodes[first_identifier]
                        .text(&declaration_nodes)
                        .into_owned();
                    next_symbol = call_resolve_name(
                        c,
                        Some(declaration),
                        &text,
                        ast::SymbolFlags::VALUE
                            | ast::SymbolFlags::TYPE
                            | ast::SymbolFlags::NAMESPACE
                            | ast::SymbolFlags::ALIAS,
                        None, /*nameNotFoundMessage*/
                        false, /*isUse*/
                        false, /*excludeGlobals*/
                    );
                }
            }

            export_symbol = next_symbol;
        }
    }

    /// `(r *EmitResolver) isOptionalParameter`.
    fn is_optional_parameter(&self, c: &mut Checker, node: NodeId) -> bool {
        c.is_optional_parameter(node)
    }

    /// `(r *EmitResolver) isSymbolAccessible`.
    fn is_symbol_accessible_c(
        &self,
        c: &mut Checker,
        symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
        meaning: ast::SymbolFlags,
        should_compute_alias_to_mark_visible: bool,
    ) -> SymbolAccessibilityResult {
        c.is_symbol_accessible(
            symbol,
            enclosing_declaration,
            meaning,
            should_compute_alias_to_mark_visible,
        )
    }

    /// `(r *EmitResolver) isValueAliasDeclarationWorker` —
    /// `r.isValueAliasDeclaration` in Go (the field is initialized to this
    /// worker).
    fn is_value_alias_declaration_worker(
        &self,
        c: &mut Checker,
        node: NodeId,
        nodes: &[Node],
    ) -> bool {
        match nodes[node].kind {
            ast::Kind::ImportEqualsDeclaration => self.is_alias_resolved_to_value(
                c,
                c.get_symbol_of_declaration(node),
                false, /*excludeTypeOnlyValues*/
            ),
            ast::Kind::ImportClause
            | ast::Kind::NamespaceImport
            | ast::Kind::ImportSpecifier
            | ast::Kind::ExportSpecifier => {
                let symbol = c.get_symbol_of_declaration(node);
                symbol.is_some()
                    && self.is_alias_resolved_to_value(
                        c,
                        symbol,
                        true, /*excludeTypeOnlyValues*/
                    )
            }
            ast::Kind::ExportDeclaration => {
                let export_clause = nodes[node].as_export_declaration().export_clause;
                export_clause.is_some_and(|export_clause| {
                    ast::is_namespace_export(&nodes[export_clause])
                        || nodes[export_clause].elements().is_some_and(|elements| {
                            core_helpers::some(elements, |&e| {
                                self.is_value_alias_declaration_worker(c, e, nodes)
                            })
                        })
                })
            }
            ast::Kind::ExportAssignment => {
                if let Some(expression) = nodes[node].expression()
                    && nodes[expression].kind == ast::Kind::Identifier
                {
                    return self.is_alias_resolved_to_value(
                        c,
                        c.get_symbol_of_declaration(node),
                        true, /*excludeTypeOnlyValues*/
                    );
                }
                true
            }
            ast::Kind::BinaryExpression => {
                if is_commonjs_module_exports(node, nodes)
                    && ast::is_identifier(
                        &nodes[nodes[node].as_binary_expression().right.unwrap()],
                    )
                {
                    return self.is_alias_resolved_to_value(
                        c,
                        c.get_symbol_of_declaration(node),
                        true, /*excludeTypeOnlyValues*/
                    );
                }
                false
            }
            _ => false,
        }
    }

    /// `(r *EmitResolver) isAliasResolvedToValue`.
    fn is_alias_resolved_to_value(
        &self,
        c: &mut Checker,
        symbol: Option<SymbolId>,
        exclude_type_only_values: bool,
    ) -> bool {
        let Some(symbol) = symbol else {
            return false;
        };
        if let Some(value_declaration) = c.symbol_arena.borrow()[symbol.index()].value_declaration {
            // Ensures cjs export assignment is setup, since this symbol may
            // point at, and merge with, the file itself. If we don't, the
            // merge may not have yet occurred, and the flags check below will
            // be missing flags that are added as a result of the merge.
            let decl_nodes = c.program_nodes(value_declaration);
            if let Some(container) =
                ast::get_source_file_of_node(Some(value_declaration), &decl_nodes)
            {
                let file_symbol = c.get_symbol_of_declaration(container);
                c.resolve_external_module_symbol(file_symbol, false /*dontResolveAlias*/);
            }
        }
        let target =
            c.get_export_symbol_of_value_symbol_if_exported(Some(c.resolve_alias(symbol)));
        if target == Some(c.unknown_symbol) {
            return !exclude_type_only_values
                || c.get_type_only_alias_declaration(symbol).is_none();
        }
        // const enums and modules that contain only const enums are not
        // considered values from the emit perspective unless
        // 'preserveConstEnums' option is set to true
        c.get_symbol_flags_ex(symbol, exclude_type_only_values, true /*excludeLocalMeanings*/)
            .intersects(ast::SymbolFlags::VALUE)
            && (c.compiler_options.should_preserve_const_enums()
                || !target.is_some_and(|t| {
                    is_const_enum_or_const_enum_only_module(&c.symbol_arena.borrow()[t.index()])
                }))
    }
}

impl ReferenceResolver for EmitResolver {
    /// `(r *EmitResolver) GetReferencedExportContainer` —
    /// `binder::ReferenceResolver::get_referenced_export_container`.
    fn get_referenced_export_container(
        &mut self,
        node: NodeId,
        prefix_locals: bool,
        nodes: &[Node],
        symbols: &mut Vec<Symbol>,
    ) -> Option<NodeId> {
        if !ast::is_parse_tree_node(&nodes[node]) {
            return None;
        }
        // Go: lock; the resolver's hooks reacquire the checker themselves, so
        // no `borrow_mut` is held across this call.
        self.reference_resolver()
            .get_referenced_export_container(node, prefix_locals, nodes, symbols)
    }

    /// `(r *EmitResolver) GetReferencedImportDeclaration`.
    fn get_referenced_import_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &mut Vec<Symbol>,
    ) -> Option<NodeId> {
        let _ = symbols;
        let mut c = checker_lock(&self.checker);
        if !ast::is_parse_tree_node(&nodes[node]) {
            return c.emit_resolver_links.jsx_links.get(node).import_ref;
        }

        let symbol = c.get_referenced_value_or_alias_symbol(node);
        let is_non_local_alias = {
            let arena = c.symbol_arena.borrow();
            ast::is_non_local_alias(
                symbol.map(|s| &arena[s.index()]),
                ast::SymbolFlags::VALUE,
            )
        };
        if is_non_local_alias
            && c.get_type_only_alias_declaration_ex(
                symbol.expect("is_non_local_alias implies a symbol"),
                ast::SymbolFlags::VALUE,
            )
            .is_none()
        {
            return c
                .get_declaration_of_alias_symbol(symbol.expect("is_non_local_alias implies a symbol"));
        }
        None
    }

    /// `(r *EmitResolver) GetReferencedValueDeclaration`.
    fn get_referenced_value_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &mut Vec<Symbol>,
    ) -> Option<NodeId> {
        if !ast::is_parse_tree_node(&nodes[node]) {
            return None;
        }
        self.reference_resolver()
            .get_referenced_value_declaration(node, nodes, symbols)
    }

    /// `(r *EmitResolver) GetReferencedValueDeclarations`.
    fn get_referenced_value_declarations(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &mut Vec<Symbol>,
    ) -> Vec<NodeId> {
        if !ast::is_parse_tree_node(&nodes[node]) {
            return Vec::new();
        }
        self.reference_resolver()
            .get_referenced_value_declarations(node, nodes, symbols)
    }

    /// `(r *EmitResolver) GetElementAccessExpressionName`.
    fn get_element_access_expression_name(&mut self, expression: Option<NodeId>) -> String {
        let Some(expression) = expression else {
            return String::new();
        };
        let nodes = checker_lock(&self.checker).program_nodes(expression);
        if !ast::is_parse_tree_node(&nodes[expression]) {
            return String::new();
        }
        self.reference_resolver()
            .get_element_access_expression_name(Some(expression))
    }

    /// `(r *EmitResolver) GetReferencedMemberValueDeclaration`.
    fn get_referenced_member_value_declaration(
        &mut self,
        node: NodeId,
        nodes: &[Node],
        symbols: &mut Vec<Symbol>,
    ) -> Option<NodeId> {
        if !ast::is_parse_tree_node(&nodes[node]) {
            return None;
        }
        self.reference_resolver()
            .get_referenced_member_value_declaration(node, nodes, symbols)
    }
}

impl tsc_printer::EmitResolver for EmitResolver {
    /// `(r *EmitResolver) EmitContext`.
    fn emit_context(&self) -> &EmitContext {
        // SAFETY: callers use the returned `&EmitContext` for `&self` APIs
        // (`parse_node`, `original`) — Go returns the shared `*EmitContext`
        // directly. The underlying `Rc` keeps it alive; mutable access goes
        // through `borrow_mut` elsewhere without a live `&` escaping into
        // mutation (the trait cannot express `&EmitContext` through
        // `RefCell::borrow` otherwise).
        unsafe { &*self.emit_context.as_ptr() }
    }

    /// `(r *EmitResolver) IsReferencedAliasDeclaration`.
    fn is_referenced_alias_declaration(&self, node: NodeId, nodes: &[Node]) -> bool {
        if !checker_unchecked(&self.checker).can_collect_symbol_alias_accessibility_data
            || !ast::is_parse_tree_node(&nodes[node])
        {
            return true;
        }
        let mut c = checker_lock(&self.checker);

        if ast::is_alias_symbol_declaration(node, nodes)
            && let Some(symbol) = c.get_symbol_of_declaration(node)
        {
            let alias_links_referenced =
                c.alias_symbol_links.get(symbol).referenced;
            if alias_links_referenced {
                return true;
            }
            let target = c.alias_symbol_links.get(symbol).alias_target;
            if let Some(target) = target
                && nodes[node].modifier_flags().intersects(ast::ModifierFlags::EXPORT)
                && c.get_symbol_flags(target).intersects(ast::SymbolFlags::VALUE)
                && (c.compiler_options.should_preserve_const_enums()
                    || !is_const_enum_or_const_enum_only_module(
                        &c.symbol_arena.borrow()[target.index()],
                    ))
            {
                return true;
            }
        }
        false
    }

    /// `(r *EmitResolver) IsValueAliasDeclaration`.
    fn is_value_alias_declaration(&self, node: NodeId, nodes: &[Node]) -> bool {
        if !checker_unchecked(&self.checker).can_collect_symbol_alias_accessibility_data
            || !ast::is_parse_tree_node(&nodes[node])
        {
            return true;
        }
        let mut c = checker_lock(&self.checker);
        self.is_value_alias_declaration_worker(&mut c, node, nodes)
    }

    /// `(r *EmitResolver) IsTopLevelValueImportEqualsWithEntityName`.
    fn is_top_level_value_import_equals_with_entity_name(
        &self,
        node: NodeId,
        nodes: &[Node],
    ) -> bool {
        if !checker_unchecked(&self.checker).can_collect_symbol_alias_accessibility_data {
            return true;
        }
        if !ast::is_parse_tree_node(&nodes[node])
            || nodes[node].kind != ast::Kind::ImportEqualsDeclaration
            || nodes[node]
                .parent
                .is_none_or(|p| nodes[p].kind != ast::Kind::SourceFile)
        {
            return false;
        }
        if ast::is_import_equals_declaration(&nodes[node])
            && (ast::node_is_missing(
                nodes[node].as_import_equals_declaration().module_reference,
                nodes,
            ) || nodes[node]
                .as_import_equals_declaration()
                .module_reference
                .is_some_and(|r| nodes[r].kind == ast::Kind::ExternalModuleReference))
        {
            return false;
        }

        let mut c = checker_lock(&self.checker);
        self.is_alias_resolved_to_value(
            &mut c,
            c.get_symbol_of_declaration(node),
            false, /*excludeTypeOnlyValues*/
        )
    }

    /// `(r *EmitResolver) MarkLinkedReferencesRecursively`.
    fn mark_linked_references_recursively(&mut self, file: NodeId, nodes: &[Node]) {
        if !ast::is_parse_tree_node(&nodes[file]) {
            return;
        }
        let mut c = checker_lock(&self.checker);
        let c = &mut *c;
        // `visit` — recursive closure spelling of Go's self-calling Visitor.
        fn visit(
            c: &mut Checker,
            nodes: &[Node],
            n: NodeId,
        ) {
            if ast::is_import_equals_declaration(&nodes[n])
                && !nodes[n].modifier_flags().intersects(ast::ModifierFlags::EXPORT)
            {
                return; // These are deferred and marked in a chain when referenced
            }
            if ast::is_import_declaration(&nodes[n]) {
                return; // likewise, these are ultimately what get marked by calls on other nodes - we want to skip them
            }
            c.mark_linked_references(
                n,
                crate::checker_types::ReferenceHint::Unspecified,
                None, /*propSymbol*/
                None, /*parentType*/
            );
            nodes[n].for_each_child(nodes, &mut |child| {
                visit(c, nodes, child);
                false
            });
        }
        nodes[file].for_each_child(nodes, &mut |child| {
            visit(c, nodes, child);
            false
        });
    }

    /// `(r *EmitResolver) GetExternalModuleFileFromDeclaration`.
    fn get_external_module_file_from_declaration(
        &self,
        node: NodeId,
        nodes: &[Node],
    ) -> Option<NodeId> {
        if !ast::is_parse_tree_node(&nodes[node]) {
            return None;
        }
        let mut c = checker_lock(&self.checker);
        c.get_external_module_file_from_declaration(node)
    }

    /// `(r *EmitResolver) GetEffectiveDeclarationFlags`.
    fn get_effective_declaration_flags(
        &self,
        node: NodeId,
        flags: ast::ModifierFlags,
        _nodes: &[Node],
    ) -> ast::ModifierFlags {
        let mut c = checker_lock(&self.checker);
        c.get_effective_declaration_flags(node, flags)
    }

    /// `(r *EmitResolver) GetTypeReferenceSerializationKind` — decorator
    /// metadata.
    fn get_type_reference_serialization_kind(
        &self,
        type_name: NodeId,
        serial_scope: Option<NodeId>,
        nodes: &[Node],
    ) -> tsc_printer::TypeReferenceSerializationKind {
        use tsc_printer::TypeReferenceSerializationKind as Kind0;
        let mut c = checker_lock(&self.checker);
        let c = &mut *c;

        // `typeName == nil || location == nil` — the trait gives `NodeId` /
        // `Option<NodeId>`; a `None` scope maps to Go nil.
        if serial_scope.is_none() {
            return Kind0::Unknown;
        }
        let location = serial_scope;

        // Resolve the symbol as a value to ensure the type can be reached at
        // runtime during emit.
        let mut is_type_only = false;
        if ast::is_qualified_name(&nodes[type_name]) {
            let root_value_symbol = c.resolve_entity_name(
                Some(ast::get_first_identifier(type_name, nodes)),
                ast::SymbolFlags::VALUE,
                true,
                true,
                location,
            );

            if let Some(root_value_symbol) = root_value_symbol {
                let declarations =
                    c.symbol_arena.borrow()[root_value_symbol.index()].declarations.clone();
                if !declarations.is_empty() {
                    is_type_only = core_helpers::every(&declarations, |&d| {
                        ast::is_type_only_import_or_export_declaration(d, &c.program_nodes(d))
                    });
                }
            }
        }
        let value_symbol = c.resolve_entity_name(
            Some(type_name),
            ast::SymbolFlags::VALUE,
            true,
            true,
            location,
        );
        let mut resolved_value_symbol = value_symbol;
        if let Some(value_symbol) = value_symbol
            && c.symbol_arena.borrow()[value_symbol.index()]
                .flags
                .intersects(ast::SymbolFlags::ALIAS)
        {
            resolved_value_symbol = Some(c.resolve_alias(value_symbol));
        }

        is_type_only = is_type_only
            || value_symbol.is_some_and(|vs| {
                c.get_type_only_alias_declaration_ex(vs, ast::SymbolFlags::VALUE)
                    .is_some()
            });

        // Resolve the symbol as a type so that we can provide a more useful
        // hint for the type serializer.
        let type_symbol = c.resolve_entity_name(
            Some(type_name),
            ast::SymbolFlags::TYPE,
            true,
            true,
            location,
        );
        let mut resolved_type_symbol = type_symbol;
        if let Some(type_symbol) = type_symbol
            && c.symbol_arena.borrow()[type_symbol.index()]
                .flags
                .intersects(ast::SymbolFlags::ALIAS)
        {
            resolved_type_symbol = Some(c.resolve_alias(type_symbol));
        }
        // In case the value symbol can't be resolved (e.g. because of missing
        // declarations), use type symbol for reachability check.
        is_type_only = is_type_only
            || type_symbol.is_some_and(|ts| {
                c.get_type_only_alias_declaration_ex(ts, ast::SymbolFlags::TYPE)
                    .is_some()
            });

        if resolved_value_symbol.is_some() && resolved_value_symbol == resolved_type_symbol {
            // `getGlobalPromiseConstructorSymbolOrNil()`.
            let thunk = c.get_global_promise_constructor_symbol_or_nil.clone();
            let global_promise_symbol = thunk.and_then(|thunk| thunk(c));
            if global_promise_symbol.is_some() && resolved_value_symbol == global_promise_symbol {
                return Kind0::Promise;
            }

            let constructor_type = c.get_type_of_symbol(resolved_value_symbol.unwrap());
            if c.is_constructor_type(constructor_type) {
                if is_type_only {
                    return Kind0::TypeWithCallSignature;
                }
                return Kind0::TypeWithConstructSignatureAndValue;
            }
        }

        // We might not be able to resolve type symbol so use unknown type in
        // that case (eg error case)
        let Some(resolved_type_symbol) = resolved_type_symbol else {
            if is_type_only {
                return Kind0::ObjectType;
            }
            return Kind0::Unknown;
        };

        let type_ = c.get_declared_type_of_symbol(resolved_type_symbol);
        if c.is_error_type(type_) {
            if is_type_only {
                return Kind0::ObjectType;
            }
            return Kind0::Unknown;
        }

        if c.types.get(type_).flags.intersects(TypeFlags::ANY_OR_UNKNOWN) {
            Kind0::ObjectType
        } else if c.is_type_assignable_to_kind(
            type_,
            TypeFlags::VOID | TypeFlags::NULLABLE | TypeFlags::NEVER,
        ) {
            Kind0::VoidNullableOrNeverType
        } else if c.is_type_assignable_to_kind(type_, TypeFlags::BOOLEAN_LIKE) {
            Kind0::BooleanType
        } else if c.is_type_assignable_to_kind(type_, TypeFlags::NUMBER_LIKE) {
            Kind0::NumberLikeType
        } else if c.is_type_assignable_to_kind(type_, TypeFlags::BIGINT_LIKE) {
            Kind0::BigIntLikeType
        } else if c.is_type_assignable_to_kind(type_, TypeFlags::STRING_LIKE) {
            Kind0::StringLikeType
        } else if is_tuple_type(&c.types, type_) {
            Kind0::ArrayLikeType
        } else if c.is_type_assignable_to_kind(type_, TypeFlags::ESSYMBOL_LIKE) {
            Kind0::ESSymbolType
        } else if c.is_function_type(type_) {
            Kind0::TypeWithCallSignature
        } else if c.is_array_type(type_) {
            Kind0::ArrayLikeType
        } else {
            Kind0::ObjectType
        }
    }

    /// `(r *EmitResolver) GetConstantValue` — const enum inlining.
    fn get_constant_value(&self, node: NodeId, _nodes: &[Node]) -> Option<evaluator::Value> {
        let mut c = checker_lock(&self.checker);
        c.get_constant_value(node)
    }

    /// `(r *EmitResolver) GetJsxFactoryEntity`.
    fn get_jsx_factory_entity(&self, location: NodeId, _nodes: &[Node]) -> Option<NodeId> {
        let mut c = checker_lock(&self.checker);
        c.get_jsx_factory_entity(location)
    }

    /// `(r *EmitResolver) GetJsxFragmentFactoryEntity`.
    fn get_jsx_fragment_factory_entity(
        &self,
        location: NodeId,
        _nodes: &[Node],
    ) -> Option<NodeId> {
        let mut c = checker_lock(&self.checker);
        c.get_jsx_fragment_factory_entity(location)
    }

    /// `(r *EmitResolver) SetReferencedImportDeclaration`.
    fn set_referenced_import_declaration(
        &mut self,
        node: NodeId,
        ref_: Option<NodeId>,
        _nodes: &[Node],
    ) {
        let mut c = checker_lock(&self.checker);
        c.emit_resolver_links.jsx_links.get(node).import_ref = ref_;
    }

    /// `(r *EmitResolver) PrecalculateDeclarationEmitVisibility`.
    fn precalculate_declaration_emit_visibility(&mut self, file: NodeId, nodes: &[Node]) {
        let mut c = checker_lock(&self.checker);
        let c = &mut *c;
        if c
            .emit_resolver_links
            .declaration_file_links
            .get(file)
            .aliases_marked
        {
            return;
        }
        c.emit_resolver_links
            .declaration_file_links
            .get(file)
            .aliases_marked = true;
        // TODO: Does this even *have* to be an upfront walk? If it's not
        // possible for a `import a = a.b.c` statement to chain into exposing
        // a statement in a sibling scope, it could at least be pushed into
        // scope entry — then it wouldn't need to be recursive.
        nodes[file].for_each_child(nodes, &mut |child| {
            self.alias_marking_visitor_worker(c, child, nodes)
        });
    }

    /// `(r *EmitResolver) IsSymbolAccessible` — non-locking: only current
    /// usage is the symbol tracker, which runs inside `CreateX` calls that
    /// already hold the checker lock.
    fn is_symbol_accessible(
        &self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: ast::SymbolFlags,
        should_compute_alias_to_mark_visible: bool,
        _nodes: &[Node],
        _symbols: &[Symbol],
    ) -> SymbolAccessibilityResult {
        self.is_symbol_accessible_c(
            checker_unchecked(&self.checker),
            Some(symbol),
            enclosing_declaration,
            meaning,
            should_compute_alias_to_mark_visible,
        )
    }

    /// `(r *EmitResolver) IsEntityNameVisible`.
    fn is_entity_name_visible(
        &self,
        entity_name: NodeId,
        enclosing_declaration: Option<NodeId>,
        _nodes: &[Node],
    ) -> SymbolAccessibilityResult {
        let mut c = checker_lock(&self.checker);
        c.is_entity_name_visible(entity_name, enclosing_declaration, true)
    }

    /// `(r *EmitResolver) IsExpandoFunctionDeclaration`.
    fn is_expando_function_declaration(&self, node: NodeId, nodes: &[Node]) -> bool {
        let _c = checker_lock(&self.checker);
        self.is_expando_function_declaration_unsafe(node, nodes)
    }

    /// `(r *EmitResolver) IsExpandoFunctionDeclarationUnsafe`.
    fn is_expando_function_declaration_unsafe(&self, node: NodeId, nodes: &[Node]) -> bool {
        // node = r.emitContext.ParseNode(node)
        if !ast::is_parse_tree_node(&nodes[node]) {
            return false;
        }
        // this is substantially different from strada, but so is expando
        // property checking
        // (the `symbols` trait param is unused — the checker owns the arena)
        let props = self.get_properties_of_container_function(node, nodes, &[]);
        props.iter().any(|&p| {
            let value_declaration =
                checker_unchecked(&self.checker).symbol_arena.borrow()[p.index()].value_declaration;
            ast::is_expando_property_declaration(value_declaration, nodes)
        })
    }

    /// `(r *EmitResolver) IsLiteralConstDeclaration`.
    fn is_literal_const_declaration(&self, node: NodeId, nodes: &[Node]) -> bool {
        // node = r.emitContext.ParseNode(node)
        if !ast::is_parse_tree_node(&nodes[node]) {
            return false;
        }
        if is_declaration_readonly(node, nodes)
            || (ast::is_variable_declaration(&nodes[node])
                && ast::is_var_const(node, nodes))
        {
            let mut c = checker_lock(&self.checker);
            let Some(s) = c.get_symbol_of_declaration(node) else {
                return false;
            };
            let t = c.get_type_of_symbol(s);
            return is_fresh_literal_type(&c, t);
        }
        false
    }

    /// `(r *EmitResolver) RequiresAddingImplicitUndefined`.
    fn requires_adding_implicit_undefined(
        &self,
        declaration: NodeId,
        symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
        nodes: &[Node],
        _symbols: &[Symbol],
    ) -> bool {
        if !ast::is_parse_tree_node(&nodes[declaration]) {
            return false;
        }
        let mut c = checker_lock(&self.checker);
        c.requires_adding_implicit_undefined(declaration, symbol, enclosing_declaration)
    }

    /// `(r *EmitResolver) IsDeclarationVisible` — only locks on the external
    /// API func to prevent deadlocks.
    fn is_declaration_visible(&self, node: NodeId, _nodes: &[Node]) -> bool {
        let mut c = checker_lock(&self.checker);
        c.is_declaration_visible(node)
    }

    /// `(r *EmitResolver) IsNameResolvable` — returns `true` if the given
    /// `name` resolves to any symbol at `location`.
    fn is_name_resolvable(&self, location: Option<NodeId>, name: &str, _nodes: &[Node]) -> bool {
        let mut c = checker_lock(&self.checker);
        let c = &mut *c;
        call_resolve_name(
            c,
            location,
            name,
            ast::SymbolFlags::VALUE | ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE,
            None,  /*nameNotFoundMessage*/
            false, /*isUse*/
            false, /*excludeGlobals*/
        )
        .is_some()
    }

    /// `(r *EmitResolver) IsImportRequiredByAugmentation`.
    fn is_import_required_by_augmentation(&self, decl: NodeId, nodes: &[Node]) -> bool {
        if !ast::is_parse_tree_node(&nodes[decl]) {
            return false;
        }
        let Some(file) = ast::get_source_file_of_node(Some(decl), nodes) else {
            return false;
        };
        let Some(file_symbol) = nodes[file].symbol() else {
            // script file
            return false;
        };
        let import_target = self.get_external_module_file_from_declaration(decl, nodes);
        let Some(import_target) = import_target else {
            return false;
        };
        if import_target == file {
            return false;
        }
        let mut c = checker_lock(&self.checker);
        let exports = c.get_exports_of_module(file_symbol);
        for s in exports.values() {
            let merged = c.get_merged_symbol(*s);
            if merged != *s {
                let declarations = c.symbol_arena.borrow()[merged.index()].declarations.clone();
                if !declarations.is_empty() {
                    for d in declarations {
                        let decl_nodes = c.program_nodes(d);
                        let decl_file = ast::get_source_file_of_node(Some(d), &decl_nodes);
                        if decl_file == Some(import_target) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// `(r *EmitResolver) IsDefinitelyReferenceToGlobalSymbolObject`.
    fn is_definitely_reference_to_global_symbol_object(
        &self,
        node: NodeId,
        nodes: &[Node],
    ) -> bool {
        if !ast::is_property_access_expression(&nodes[node])
            || !nodes[node].name().is_some_and(|n| ast::is_identifier(&nodes[n]))
            || !(nodes[node]
                .expression()
                .is_some_and(|e| ast::is_property_access_expression(&nodes[e]))
                || nodes[node]
                    .expression()
                    .is_some_and(|e| ast::is_identifier(&nodes[e])))
        {
            return false;
        }
        let expression = nodes[node].expression().expect("expression");
        if nodes[expression].kind == ast::Kind::Identifier {
            if nodes[expression].text(nodes) != "Symbol" {
                return false;
            }
            let mut c = checker_lock(&self.checker);
            // Exactly `Symbol.something` and `Symbol` either does not resolve
            // or definitely resolves to the global Symbol
            return c.get_resolved_symbol(expression)
                == c.get_global_symbol(
                    "Symbol",
                    ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE,
                    None, /*diagnostic*/
                )
                .expect("global Symbol");
        }
        let expr_expression = nodes[expression].expression();
        let expr_name = nodes[expression].name();
        if expr_expression.is_none_or(|e| nodes[e].kind != ast::Kind::Identifier)
            || expr_expression.is_none_or(|e| nodes[e].text(nodes) != "globalThis")
            || expr_name.is_none_or(|n| nodes[n].text(nodes) != "Symbol")
        {
            return false;
        }
        let mut c = checker_lock(&self.checker);
        // Exactly `globalThis.Symbol.something` and `globalThis` resolves to
        // the global `globalThis`
        c.get_resolved_symbol(expr_expression.unwrap()) == c.global_this_symbol
    }

    /// `(r *EmitResolver) IsImplementationOfOverload`.
    fn is_implementation_of_overload(&self, node: NodeId, nodes: &[Node]) -> bool {
        // node = r.emitContext.ParseNode(node)
        if !ast::is_parse_tree_node(&nodes[node]) {
            return false;
        }
        if ast::node_is_present(nodes[node].body(), nodes) {
            if ast::is_get_accessor_declaration(&nodes[node])
                || ast::is_set_accessor_declaration(&nodes[node])
            {
                return false; // Get or set accessors can never be overload implementations, but can have up to 2 signatures
            }
            let mut c = checker_lock(&self.checker);
            // `c.GetSignaturesOfSymbol(c.GetSymbolOfDeclaration(node))` —
            // the Rust port takes `Option<SymbolId>` for the Go nilable
            // symbol, so the `let Some` unwrap isn't needed.
            let signatures_of_symbol =
                c.get_signatures_of_symbol(c.get_symbol_of_declaration(node));
            // If this function body corresponds to function with multiple
            // signature, it is implementation of overload
            // e.g.: function foo(a: string): string;
            //       function foo(a: number): number;
            //       function foo(a: any) { // This is implementation of the overloads
            //           return a;
            //       }
            if signatures_of_symbol.len() > 1 {
                return true;
            }
            // If there is single signature for the symbol, it is overload if
            // that signature isn't coming from the node
            // e.g.: function foo(a: string): string;
            //       function foo(a: any) { // This is implementation of the overloads
            //           return a;
            //       }
            if signatures_of_symbol.len() == 1 {
                let signature = signatures_of_symbol[0];
                if signature == c.get_signature_of_full_signature_type(node) {
                    return false;
                }
                let declaration = c.signature_arena.get(signature).declaration;
                if declaration != Some(node)
                    && declaration.is_some_and(|d| {
                        !c.program_nodes(d)[d].flags.intersects(ast::NodeFlags::JSDOC)
                    })
                {
                    return true;
                }
            }
        }
        false
    }

    /// `(r *EmitResolver) GetEnumMemberValue`.
    fn get_enum_member_value(&self, node: NodeId, nodes: &[Node]) -> evaluator::Result {
        // node = r.emitContext.ParseNode(node)
        if !ast::is_parse_tree_node(&nodes[node]) {
            return evaluator::new_result(None, false, false, false);
        }
        let mut c = checker_lock(&self.checker);

        if let Some(parent) = nodes[node].parent {
            c.compute_enum_member_values(parent);
        }
        if !c.enum_member_links.has(&node) {
            return evaluator::new_result(None, false, false, false);
        }
        c.enum_member_links.get(node).value.clone()
    }

    /// `(r *EmitResolver) IsLateBound`.
    fn is_late_bound(&self, node: NodeId, nodes: &[Node]) -> bool {
        // TODO: Require an emitContext to construct an EmitResolver, remove
        // all emitContext arguments
        // node = r.emitContext.ParseNode(node)
        if !ast::is_parse_tree_node(&nodes[node]) {
            return false;
        }
        let mut c = checker_lock(&self.checker);
        let Some(symbol) = c.get_symbol_of_declaration(node) else {
            return false;
        };
        c.symbol_arena.borrow()[symbol.index()]
            .check_flags
            .intersects(ast::checkflags::CheckFlags::LATE)
    }

    /// `(r *EmitResolver) IsOptionalParameter`.
    fn is_optional_parameter(&self, node: NodeId, _nodes: &[Node]) -> bool {
        let mut c = checker_lock(&self.checker);
        self.is_optional_parameter(&mut c, node)
    }

    /// `(r *EmitResolver) IsThisPropertyAssignmentDeclarationRedundant` —
    /// see the Go doc comment on `emitresolver.go` (a JS `this.<name> = ...`
    /// expando assignment is omitted when an `extends` base type already
    /// provides an identical member).
    fn is_this_property_assignment_declaration_redundant(
        &self,
        node: NodeId,
        _nodes: &[Node],
    ) -> bool {
        let mut c = checker_lock(&self.checker);
        let c = &mut *c;

        let Some(s) = c.get_symbol_of_declaration(node) else {
            return false;
        };
        let Some(parent) = c.symbol_arena.borrow()[s.index()].parent else {
            return false;
        };
        let s_name = c.symbol_arena.borrow()[s.index()].name.clone();
        let parent_type = c.get_declared_type_of_symbol(parent);
        for base in c.get_base_types(parent_type) {
            let Some(base_prop) = c.get_property_of_type(base, &s_name) else {
                continue;
            };
            let base_prop_flags = c.symbol_arena.borrow()[base_prop.index()].flags;
            if base_prop_flags.intersects(
                ast::SymbolFlags::ACCESSOR | ast::SymbolFlags::METHOD | ast::SymbolFlags::FUNCTION,
            ) {
                return true;
            }
            let s_flags = c.symbol_arena.borrow()[s.index()].flags;
            if c.is_readonly_symbol(base_prop) == c.is_readonly_symbol(s)
                && s_flags.intersects(ast::SymbolFlags::OPTIONAL)
                    == base_prop_flags.intersects(ast::SymbolFlags::OPTIONAL)
                && c.is_type_identical_to(
                    c.get_type_of_symbol(s),
                    c.get_type_of_symbol(base_prop),
                )
            {
                return true;
            }
        }
        false
    }

    /// `(r *EmitResolver) GetPropertiesOfContainerFunction` — explicitly _not
    /// locked_: it is only called via error reporters invoked via node
    /// builder calls to the symbol tracker already within locked contexts.
    fn get_properties_of_container_function(
        &self,
        node: NodeId,
        _nodes: &[Node],
        _symbols: &[Symbol],
    ) -> Vec<SymbolId> {
        let c = checker_unchecked(&self.checker);
        let Some(s) = c.get_symbol_of_declaration(node) else {
            return Vec::new();
        };
        let t = c.get_type_of_symbol(s);
        c.get_properties_of_type(t)
    }

    /// `(r *EmitResolver) RequiresAddingImplicitUndefinedUnsafe` — NO
    /// LOCKING: only called in contexts that already have a checker lock.
    fn requires_adding_implicit_undefined_unsafe(
        &self,
        declaration: NodeId,
        symbol: Option<SymbolId>,
        enclosing_declaration: Option<NodeId>,
        nodes: &[Node],
        _symbols: &[Symbol],
    ) -> bool {
        if !ast::is_parse_tree_node(&nodes[declaration]) {
            return false;
        }
        checker_unchecked(&self.checker).requires_adding_implicit_undefined(
            declaration,
            symbol,
            enclosing_declaration,
        )
    }

    /// `(r *EmitResolver) GetReferencedValueDeclarationUnsafe` — NO
    /// LOCKING: Go omits `checkerMu` here (the resolver's hooks reacquire
    /// the checker themselves via `checker_unchecked`).
    fn get_referenced_value_declaration_unsafe(
        &self,
        node: NodeId,
        nodes: &[Node],
    ) -> Option<NodeId> {
        let c = checker_unchecked(&self.checker);
        let mut symbols = c.symbol_arena.borrow_mut();
        self.reference_resolver()
            .get_referenced_value_declaration(node, nodes, &mut symbols)
        // (`&mut symbols` auto-derefs `RefMut<Vec<Symbol>>` → `&mut Vec<Symbol>`)
    }

    /// `(r *EmitResolver) CreateReturnTypeOfSignatureDeclaration`.
    fn create_return_type_of_signature_declaration(
        &self,
        signature_declaration: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: &dyn nodebuilder::SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        let Some(original) = self
            .emit_context
            .borrow()
            .parse_node(nodes, signature_declaration)
        else {
            return Some(
                self.emit_context
                    .borrow_mut()
                    .factory
                    .new_keyword_type_node(nodes, ast::Kind::AnyKeyword),
            );
        };

        let mut c = checker_lock(&self.checker);
        let tracker = tracker_mut(tracker);
        self.node_builder(&c).serialize_return_type_for_signature(
            &mut c,
            nodes,
            original,
            enclosing_declaration,
            flags,
            internal_flags,
            Some(Box::new(TrackerRef(tracker))),
        )
    }

    /// `(r *EmitResolver) CreateTypeParametersOfSignatureDeclaration`.
    fn create_type_parameters_of_signature_declaration(
        &self,
        signature_declaration: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: &dyn nodebuilder::SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Vec<NodeId> {
        let Some(original) = self
            .emit_context
            .borrow()
            .parse_node(nodes, signature_declaration)
        else {
            return Vec::new();
        };

        let mut c = checker_lock(&self.checker);
        let tracker = tracker_mut(tracker);
        self.node_builder(&c).serialize_type_parameters_for_signature(
            &mut c,
            nodes,
            original,
            enclosing_declaration,
            flags,
            internal_flags,
            Some(Box::new(TrackerRef(tracker))),
        )
    }

    /// `(r *EmitResolver) CreateTypeOfDeclaration`.
    fn create_type_of_declaration(
        &self,
        declaration: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: &dyn nodebuilder::SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        if self
            .emit_context
            .borrow()
            .parse_node(nodes, declaration)
            .is_none()
        {
            return Some(
                self.emit_context
                    .borrow_mut()
                    .factory
                    .new_keyword_type_node(nodes, ast::Kind::AnyKeyword),
            );
        }

        let mut c = checker_lock(&self.checker);
        // Get type of the symbol if this is the valid symbol otherwise get
        // type at location.
        //
        // PORT: Go passes `symbol` (possibly nil) into
        // `SerializeTypeForDeclaration`, where a nil symbol resolves to the
        // error type — serialized as `any`. The Rust API takes a
        // non-`Option` `SymbolId`, so a missing symbol takes the same `any`
        // fallback explicitly.
        let Some(symbol) = c.get_symbol_of_declaration(declaration) else {
            return Some(
                self.emit_context
                    .borrow_mut()
                    .factory
                    .new_keyword_type_node(nodes, ast::Kind::AnyKeyword),
            );
        };
        let tracker = tracker_mut(tracker);
        self.node_builder(&c).serialize_type_for_declaration(
            &mut c,
            nodes,
            declaration,
            symbol,
            enclosing_declaration,
            flags | nodebuilder::Flags::MULTILINE_OBJECT_LITERALS,
            internal_flags,
            Some(Box::new(TrackerRef(tracker))),
        )
    }

    /// `(r *EmitResolver) CreateLiteralConstValue`.
    fn create_literal_const_value(
        &self,
        node: NodeId,
        tracker: &dyn nodebuilder::SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        let node = self.emit_context.borrow().parse_node(nodes, node);
        let t = {
            let mut c = checker_lock(&self.checker);
            c.get_symbol_of_declaration(node?)
                .map(|s| c.get_type_of_symbol(s))
        };
        let Some(t) = t else {
            return None; // TODO: How!? Maybe this should be a panic. All symbols should have a type.
        };

        let mut enum_result: Option<NodeId> = None;
        if checker_lock(&self.checker)
            .types
            .get(t)
            .flags
            .intersects(TypeFlags::ENUM_LIKE)
        {
            let mut c = checker_lock(&self.checker);
            let symbol = c.types.get(t).symbol;
            let tracker = tracker_mut(tracker);
            enum_result = self.node_builder(&c).symbol_to_expression(
                &mut c,
                nodes,
                symbol.expect("enum-like type symbol"),
                ast::SymbolFlags::VALUE,
                node,
                nodebuilder::Flags::NONE,
                nodebuilder::InternalFlags::NONE,
                Some(Box::new(TrackerRef(tracker))),
            );
            // What about regularTrueType/regularFalseType - since those
            // aren't fresh, we never make initializers from them
            // TODO: handle those if this function is ever used for more than
            // initializers in declaration emit
        } else {
            // `t == c.trueType` / `t == c.falseType` — read through the
            // shared checker handle (Go reads `c.trueType` under the lock
            // that produced `t` above; the borrow is already released).
            let c = self.checker.borrow();
            if t == c.true_type {
                enum_result = Some(self.emit_context.borrow_mut().factory.new_keyword_expression(
                    nodes,
                    ast::Kind::TrueKeyword,
                ));
            } else if t == c.false_type {
                enum_result = Some(self.emit_context.borrow_mut().factory.new_keyword_expression(
                    nodes,
                    ast::Kind::FalseKeyword,
                ));
            }
        }
        if enum_result.is_some() {
            return enum_result;
        }
        {
            let c = checker_lock(&self.checker);
            if !c.types.get(t).flags.intersects(TypeFlags::LITERAL) {
                return None; // non-literal type
            }
            let value = c.types.get(t).as_literal_type().value.clone();
            drop(c);
            match value {
                Some(evaluator::Value::String(value)) => {
                    return Some(self.emit_context.borrow_mut().factory.new_string_literal(
                        nodes,
                        &value,
                        ast::TokenFlags::NONE,
                    ));
                }
                Some(evaluator::Value::Number(value)) => {
                    if value.is_inf() {
                        if value > 0.0.into() {
                            return Some(
                                self.emit_context.borrow_mut().factory.new_identifier(
                                    nodes,
                                    "Infinity",
                                ),
                            );
                        }
                        let inner = self
                            .emit_context
                            .borrow_mut()
                            .factory
                            .new_identifier(nodes, "Infinity");
                        return Some(
                            self.emit_context
                                .borrow_mut()
                                .factory
                                .new_prefix_unary_expression(
                                    nodes,
                                    ast::Kind::MinusToken,
                                    Some(inner),
                                ),
                        );
                    }
                    if value.is_nan() {
                        return Some(
                            self.emit_context
                                .borrow_mut()
                                .factory
                                .new_identifier(nodes, "NaN"),
                        );
                    }
                    if value.abs() != value {
                        // negative
                        let inner = self.emit_context.borrow_mut().factory.new_numeric_literal(
                            nodes,
                            &value.string()[1..],
                            ast::TokenFlags::NONE,
                        );
                        return Some(
                            self.emit_context
                                .borrow_mut()
                                .factory
                                .new_prefix_unary_expression(
                                    nodes,
                                    ast::Kind::MinusToken,
                                    Some(inner),
                                ),
                        );
                    }
                    return Some(self.emit_context.borrow_mut().factory.new_numeric_literal(
                        nodes,
                        &value.string(),
                        ast::TokenFlags::NONE,
                    ));
                }
                Some(evaluator::Value::PseudoBigInt(value)) => {
                    return Some(self.emit_context.borrow_mut().factory.new_big_int_literal(
                        nodes,
                        &(pseudo_big_int_to_string(value) + "n"),
                        ast::TokenFlags::NONE,
                    ));
                }
                Some(evaluator::Value::Bool(value)) => {
                    let kind = if value {
                        ast::Kind::TrueKeyword
                    } else {
                        ast::Kind::FalseKeyword
                    };
                    return Some(self.emit_context.borrow_mut().factory.new_keyword_expression(
                        nodes, kind,
                    ));
                }
                None => {}
            }
        }
        panic!("unhandled literal const value kind")
    }

    /// `(r *EmitResolver) CreateTypeOfExpression`.
    fn create_type_of_expression(
        &self,
        expression: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: &dyn nodebuilder::SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        let Some(expression) = self.emit_context.borrow().parse_node(nodes, expression) else {
            return Some(
                self.emit_context
                    .borrow_mut()
                    .factory
                    .new_keyword_type_node(nodes, ast::Kind::AnyKeyword),
            );
        };

        let mut c = checker_lock(&self.checker);
        let tracker = tracker_mut(tracker);
        self.node_builder(&c).serialize_type_for_expression(
            &mut c,
            nodes,
            expression,
            enclosing_declaration,
            flags | nodebuilder::Flags::MULTILINE_OBJECT_LITERALS,
            internal_flags,
            Some(Box::new(TrackerRef(tracker))),
        )
    }

    /// `(r *EmitResolver) CreateLateBoundIndexSignatures`.
    fn create_late_bound_index_signatures(
        &self,
        container: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: &dyn nodebuilder::SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Vec<NodeId> {
        let Some(container) = self.emit_context.borrow().parse_node(nodes, container) else {
            return Vec::new();
        };
        let mut c = checker_lock(&self.checker);
        let c = &mut *c;

        let Some(sym) = nodes[container].symbol() else {
            return Vec::new();
        };
        let sym_type = c.get_type_of_symbol(sym);
        let static_infos = c.get_index_infos_of_type(sym_type);
        let instance_index_symbol = c.get_index_symbol(sym);
        let mut instance_infos = Vec::new();
        if let Some(instance_index_symbol) = instance_index_symbol {
            let members = c.get_members_of_symbol(sym);
            let sibling_symbols: Vec<SymbolId> = members.values().copied().collect();
            instance_infos =
                c.get_index_infos_of_index_symbol(instance_index_symbol, sibling_symbols);
        }

        let mut result: Vec<NodeId> = Vec::new();
        for (i, info_list) in [static_infos, instance_infos].into_iter().enumerate() {
            let is_static = i == 0;
            if info_list.is_empty() {
                continue;
            }
            for info in info_list {
                if c.index_info_arena.get(info).declaration.is_some() {
                    continue;
                }
                if info == c.any_base_type_index_info {
                    continue; // inherited, but looks like a late-bound signature because it has no declarations
                }
                let components = c.index_info_arena.get(info).components.clone();
                if !components.is_empty() {
                    // !!! TODO: Complete late-bound index info support -
                    // getObjectLiteralIndexInfo does not yet add late bound
                    // components to index signatures
                    let all_component_computed_names_serializable =
                        enclosing_declaration.is_some()
                            && core_helpers::every(&components, |&component| {
                                let Some(name) = nodes[component].name() else {
                                    return false;
                                };
                                ast::is_computed_property_name(&nodes[name])
                                    && nodes[name]
                                        .expression()
                                        .is_some_and(|e| {
                                            ast::is_entity_name_expression(&nodes[e], nodes)
                                                && c
                                                    .is_entity_name_visible(
                                                        e,
                                                        enclosing_declaration,
                                                        false,
                                                    )
                                                    .accessibility
                                                    == SymbolAccessibility::Accessible
                                        })
                            });
                    if all_component_computed_names_serializable {
                        for component in &components {
                            let component = *component;
                            if c.has_late_bindable_name(component) {
                                // skip late bound props that contribute to
                                // the index signature - they'll be preserved
                                // via other means
                                continue;
                            }

                            let name_expr = nodes[component].name().and_then(|n| nodes[n].expression());
                            let first_identifier = ast::get_first_identifier(
                                name_expr.expect("component computed name expression"),
                                nodes,
                            );
                            let text = nodes[first_identifier].text(nodes).into_owned();
                            let name = call_resolve_name(
                                c,
                                Some(first_identifier),
                                &text,
                                ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE,
                                None, /*nameNotFoundMessage*/
                                true, /*isUse*/
                                false, /*excludeGlobals*/
                            );
                            if let Some(name) = name {
                                tracker_mut(tracker).track_symbol(
                                    name,
                                    enclosing_declaration,
                                    ast::SymbolFlags::VALUE,
                                );
                            }

                            let mut mods: Vec<NodeId> = Vec::new();
                            if is_static {
                                mods.push(self.emit_context.borrow_mut().factory.new_token(
                                    nodes,
                                    ast::Kind::StaticKeyword,
                                ));
                            }
                            if c.index_info_arena.get(info).is_readonly {
                                mods.push(self.emit_context.borrow_mut().factory.new_token(
                                    nodes,
                                    ast::Kind::ReadonlyKeyword,
                                ));
                            }
                            let modifier_list = if mods.is_empty() {
                                None
                            } else {
                                Some(
                                    self.emit_context
                                        .borrow()
                                        .factory
                                        .new_modifier_list(nodes, mods),
                                )
                            };
                            let component_symbol = nodes[component].symbol();
                            let type_node = component_symbol.and_then(|sym| {
                                let t = c.get_type_of_symbol(sym);
                                self.node_builder(c).type_to_type_node(
                                    c,
                                    nodes,
                                    t,
                                    enclosing_declaration,
                                    flags,
                                    internal_flags,
                                    Some(Box::new(TrackerRef(tracker_mut(tracker)))),
                                )
                            });
                            // `f.NewPropertyDeclaration(modifiers,
                            // component.Name(), component.QuestionToken(),
                            // typeNode, nil)` — hoist reads out of the `&mut
                            // nodes` call.
                            let component_name = nodes[component].name();
                            let component_question_token =
                                nodes[component].question_token(nodes);
                            let decl = self.emit_context.borrow_mut().factory.new_property_declaration(
                                nodes,
                                modifier_list,
                                component_name,
                                component_question_token,
                                type_node,
                                None,
                            );
                            result.push(decl);
                        }
                        continue;
                    }
                }
                let node = self.node_builder(c).index_info_to_index_signature_declaration(
                    c,
                    nodes,
                    info,
                    enclosing_declaration,
                    flags,
                    internal_flags,
                    Some(Box::new(TrackerRef(tracker_mut(tracker)))),
                );
                let node = node.and_then(|node| {
                    if is_static {
                        let mut mod_nodes: Vec<NodeId> = vec![self
                            .emit_context
                            .borrow_mut()
                            .factory
                            .new_token(nodes, ast::Kind::StaticKeyword)];
                        mod_nodes.extend(
                            nodes[node]
                                .modifier_nodes()
                                .map(|m| m.to_vec())
                                .unwrap_or_default(),
                        );
                        let mods = self
                            .emit_context
                            .borrow()
                            .factory
                            .new_modifier_list(nodes, mod_nodes);
                        // `f.UpdateIndexSignatureDeclaration(node,
                        // modifiers, node.Parameters(), node.Type())` —
                        // hoist the node reads: `nodes` is already borrowed
                        // as `&mut` by the factory call.
                        let parameters = nodes[node].parameter_list().cloned();
                        let type_node_ = nodes[node].type_();
                        return self
                            .emit_context
                            .borrow_mut()
                            .factory
                            .update_index_signature_declaration(
                                nodes,
                                node,
                                Some(mods),
                                parameters,
                                type_node_,
                            )
                            .or(Some(node));
                    }
                    Some(node)
                });
                if let Some(node) = node {
                    result.push(node);
                }
            }
        }
        result
    }

    /// `(r *EmitResolver) TryJSTypeNodeToTypeNode`.
    fn try_js_type_node_to_type_node(
        &self,
        type_node: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: &dyn nodebuilder::SymbolTracker,
        nodes: &mut Vec<Node>,
    ) -> Option<NodeId> {
        let type_node = self.emit_context.borrow().parse_node(nodes, type_node);
        let mut c = checker_lock(&self.checker);
        let tracker = tracker_mut(tracker);
        self.node_builder(&c).try_js_type_node_to_type_node(
            &mut c,
            nodes,
            type_node?,
            enclosing_declaration,
            flags,
            internal_flags,
            Some(Box::new(TrackerRef(tracker))),
        )
    }
}
