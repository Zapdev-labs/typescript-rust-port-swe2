// Ported from tsc/internal/checker/nodebuilderimpl.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the `NodeBuilderImpl` core: the
// type-to-type-node serializer, symbol-chain resolution, module specifier
// generation, signature/parameter serialization, and per-location
// serialization caches.
//
// PORT notes:
//
// - `*ast.Node` → `Option<NodeId>` where nil-able (`NodeId` where Go asserts
//   non-nil through usage), `*ast.Symbol` → `SymbolId`, `*Type` → `TypeId`,
//   `*Signature` → `SignatureId`, `*TypePredicate` → `&TypePredicate` /
//   `Option<&TypePredicate>`, `*ast.SourceFile` → the file's `NodeId`,
//   `*ast.Identifier` → `NodeId`, `*TypeMapper` → `Option<TypeMapperId>`,
//   `module.ModeAwareCache[T]` → `tsc_module::ModeAwareCache<T>`,
//   `collections.Set[TypeId]` → `OrderedSet<TypeId>`,
//   `*pseudochecker.PseudoType` → `Option<PseudoTypeRef>` (Go nil) or
//   `PseudoTypeRef` where non-nil.
// - `ch *Checker` / `e *printer.EmitContext` handling: methods take
//   `c: &mut Checker` explicitly (SPEC §5.4); `e` lives on the struct in
//   `Rc<RefCell<>>` so visitor closures can reach the emit tables (see the
//   `Transformer` precedent in crates/transformers/src/transformer.rs).
// - The `f *ast.NodeFactory` is a *second* factory whose hooks mirror
//   `EmitContext::new`'s (onCreate → SYNTHESIZED, onUpdate/onClone →
//   `set_original_ex`), same deviation and rationale as `transformer.rs`'s
//   `new_transform_factory`: `cx.factory` must be borrowable while visit
//   closures hold the emit context. `onClone`'s `autoGenerate` copy is not
//   reproducible here (the table is `pub(crate)` to tsc-printer).
// - Node arenas: synthesized nodes are minted into `nodes`, the destination
//   file's `Vec<ast::Node>` (the factory `file_index` is set to it in
//   `enter_context`). Reads of nodes that may live in other files (symbol
//   declarations, type-attachment nodes, module targets) go through
//   `Checker::program_nodes`.
// - `b.ctx` is a `NodeBuilderContext` value swapped by `enter_context` /
//   `pop_context` in nodebuilder.rs (Go swaps a `*NodeBuilderContext`).
// - `cloneBindingNameVisitor` is not stored (Go caches it on the impl); the
//   closure needs `&mut self`/`&mut Checker`, so `clone_binding_name` builds
//   an equivalent visitor per call, passing state through `RefCell`s — see
//   `clone_binding_name`.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, Kind, NodeId, NodeList, SymbolFlags, SymbolId};
use tsc_collections::{CopyOnWriteMap, CopyOnWriteSet, OrderedSet};
use tsc_core::compileroptions::{RESOLUTION_MODE_ESM, RESOLUTION_MODE_NONE, ResolutionMode};
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::linkstore::LinkStore;
use tsc_core::options_generated::{ModuleKind, ModuleResolutionKind};
use tsc_jsnum as jsnum;
use tsc_nodebuilder as nodebuilder;
use tsc_printer::{self as printer, EmitContext};
use tsc_pseudochecker::{self as pseudochecker, PseudoTypeKind};
use tsc_scanner as scanner;
use tsc_stringutil as stringutil;

use crate::checker_core::{
    CacheHashKey, Checker, get_non_distributed_type_parameter, is_this_type_parameter,
};
use crate::checker_types::{Host, MappedTypeModifiers, TypeFacts};
use crate::mapper::TypeMapperId;
use crate::types::{
    ElementFlags, IndexInfo, IndexInfoId, ObjectFlags, SignatureFlags, SignatureId, SignatureKind,
    TypeAlias, TypeArena, TypeFlags, TypeId, TypePredicate, TypePredicateKind,
};

/// `type CompositeSymbolIdentity struct`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct CompositeSymbolIdentity {
    /// `isConstructorNode`.
    pub is_constructor_node: bool,
    /// `symbolId`.
    pub symbol_id: SymbolId,
    /// `nodeId`.
    pub node_id: NodeId,
}

/// `type TrackedSymbolArgs struct`.
#[derive(Clone, Copy)]
pub struct TrackedSymbolArgs {
    /// `symbol`.
    pub symbol: SymbolId,
    /// `enclosingDeclaration`.
    pub enclosing_declaration: Option<NodeId>,
    /// `meaning`.
    pub meaning: SymbolFlags,
}

/// `type SerializedTypeEntry struct`.
#[derive(Default)]
pub struct SerializedTypeEntry {
    /// `node`.
    pub node: Option<NodeId>,
    /// `truncating`.
    pub truncating: bool,
    /// `addedLength`.
    pub added_length: i32,
    /// `trackedSymbols`.
    pub tracked_symbols: Vec<TrackedSymbolArgs>,
    /// Fingerprint of the cached node at insertion time. Go's entry is a
    /// `*Node` pointer that stays valid for the checker run; ours may mint
    /// into a scratch arena that is later dropped, and the id can then alias
    /// an unrelated node in the current buffer. Verifying kind/pos/end on a
    /// cache hit catches that staleness and forces a reserialize.
    pub kind: Kind,
    /// `pos` of the cached node.
    pub pos: i32,
    /// `end` of the cached node.
    pub end: i32,
}

/// `type CompositeTypeCacheIdentity struct`.
#[derive(Clone, Default, PartialEq, Eq, Hash)]
pub struct CompositeTypeCacheIdentity {
    /// `typeId`.
    pub type_id: TypeId,
    /// `flags`.
    pub flags: nodebuilder::Flags,
    /// `internalFlags`.
    pub internal_flags: nodebuilder::InternalFlags,
    /// `inferTypeParameters`.
    pub infer_type_parameters: CacheHashKey,
}

/// `type NodeBuilderLinks struct`.
#[derive(Default)]
pub struct NodeBuilderLinks {
    /// `serializedTypes` — collection of types serialized at this location.
    pub serialized_types: FxHashMap<CompositeTypeCacheIdentity, SerializedTypeEntry>,
    /// `fakeScopeForSignatureDeclaration` — if present, this is a fake scope
    /// injected into an enclosing declaration chain. Go stores `*string`;
    /// `Option<String>` carries the discriminated kind ("params" |
    /// "typeParams").
    pub fake_scope_for_signature_declaration: Option<String>,
}

/// `type NodeBuilderSymbolLinks struct`.
#[derive(Default)]
pub struct NodeBuilderSymbolLinks {
    /// `specifierCache`.
    pub specifier_cache: tsc_module::ModeAwareCache<ModuleSpecifierResult>,
}

/// `type moduleSpecifierResult struct`.
#[derive(Clone, Default)]
pub struct ModuleSpecifierResult {
    /// `specifier`.
    pub specifier: tsc_tspath::ModuleSpecifier,
    /// `importAttributesType` — `*Type` → `Option<TypeId>`.
    pub import_attributes_type: Option<TypeId>,
}

/// `type NodeBuilderContext struct` — all fields are ported; `host` is the
/// `modulespecifiers.ModuleSpecifierGenerationHost` implemented by `Program`,
/// stored as `Rc<dyn Host>`.
#[derive(Default)]
pub struct NodeBuilderContext<'a> {
    /// `host` — `modulespecifiers.ModuleSpecifierGenerationHost`.
    pub host: Option<Rc<dyn Host>>,
    /// `tracker` — `Rc<RefCell>` so visit closures (e.g. the computed-name
    /// tracker inside `clone_binding_name`) can reach the tracker while
    /// `b`/`c` are borrowed elsewhere — Go shares it via `b.ctx.tracker`.
    /// `+ 'a` rather than `'static` so the declarations transformer's
    /// lifetime-bound tracker forwards through — see `symboltracker.rs`.
    pub tracker: Option<Rc<RefCell<dyn nodebuilder::SymbolTracker + 'a>>>,
    /// `approximateLength`.
    pub approximate_length: i32,
    /// `maxTruncationLength`.
    pub max_truncation_length: i32,
    /// `encounteredError`.
    pub encountered_error: bool,
    /// `truncating`.
    pub truncating: bool,
    /// `reportedDiagnostic` — `Rc<Cell>` shared with `SymbolTrackerImpl`,
    /// which sets it in Go via its `context` back-pointer (Go:
    /// `this.context.reportedDiagnostic = true`). See symboltracker.rs.
    pub reported_diagnostic: Rc<Cell<bool>>,
    /// `flags`.
    pub flags: nodebuilder::Flags,
    /// `internalFlags`.
    pub internal_flags: nodebuilder::InternalFlags,
    /// `depth`.
    pub depth: i32,
    /// `maxExpansionDepth` — -1 means no expansion, 0+ = verbosity levels.
    pub max_expansion_depth: i32,
    /// `typeStack`.
    pub type_stack: Vec<TypeId>,
    /// `canIncreaseExpansionDepth`.
    pub can_increase_expansion_depth: bool,
    /// `expansionTruncated`.
    pub expansion_truncated: bool,
    /// `enclosingDeclaration`.
    pub enclosing_declaration: Option<NodeId>,
    /// `enclosingFile` — `*ast.SourceFile` → the file's `NodeId`.
    pub enclosing_file: Option<NodeId>,
    /// `inferTypeParameters`.
    pub infer_type_parameters: Vec<TypeId>,
    /// `visitedTypes`.
    pub visited_types: OrderedSet<TypeId>,
    /// `symbolDepth`.
    pub symbol_depth: FxHashMap<CompositeSymbolIdentity, i32>,
    /// `trackedSymbols` — `Rc<RefCell>` shared with `SymbolTrackerImpl`
    /// (Go's `this.context.trackedSymbols = append(...)`).
    pub tracked_symbols: Rc<RefCell<Vec<TrackedSymbolArgs>>>,
    /// `mapper`.
    pub mapper: Option<TypeMapperId>,
    /// `reverseMappedStack`.
    pub reverse_mapped_stack: Vec<SymbolId>,
    /// `enclosingSymbolTypes`.
    pub enclosing_symbol_types: FxHashMap<SymbolId, TypeId>,
    /// `suppressReportInferenceFallback`.
    pub suppress_report_inference_fallback: bool,
    /// `remappedSymbolReferences`.
    pub remapped_symbol_references: FxHashMap<SymbolId, SymbolId>,

    // per signature scope state
    /// `typeParameterNames` — `CopyOnWriteMap[TypeId, *ast.Identifier]` →
    /// `CopyOnWriteMap<TypeId, (NodeId, u64)>`. The `u64` is the
    /// `nodes_epoch` the id was minted under: a cached id is only valid in
    /// the arena buffer it was minted into (Go's shared heap makes any
    /// `*ast.Identifier` valid everywhere; per-file arenas do not).
    pub type_parameter_names: CopyOnWriteMap<TypeId, (NodeId, u64)>,
    /// `nodes_epoch` — bumped every time the builder's working arena
    /// switches to a scratch clone of another file's arena (see
    /// `try_reuse_existing_node_helper` / `deep_clone_node_in` /
    /// `clone_binding_name`). Arena-bound caches compare against it.
    pub nodes_epoch: std::cell::Cell<u64>,
    /// `epoch_counter` — allocator for `nodes_epoch`.
    pub epoch_counter: std::cell::Cell<u64>,
    /// The decided display text for a type parameter — arena-independent,
    /// unlike `type_parameter_names` entries which point into one buffer.
    /// Used to remint the same name into scratch arenas (Go reuses the
    /// same `*ast.Identifier` everywhere via its shared heap).
    pub type_parameter_name_texts: CopyOnWriteMap<TypeId, String>,
    /// `typeParameterNamesByText`.
    pub type_parameter_names_by_text: CopyOnWriteSet<String>,
    /// `typeParameterNamesByTextNextNameCount`.
    pub type_parameter_names_by_text_next_name_count: CopyOnWriteMap<String, i32>,
    /// `typeParameterSymbolList`.
    pub type_parameter_symbol_list: CopyOnWriteSet<SymbolId>,
}

/// The `func()` returned by `saveRestoreFlags` — a snapshot of the
/// flags/depth fields, restored via `restore` (a closure can't disjointly
/// borrow `b.ctx`).
#[derive(Clone, Copy)]
pub struct SaveRestoreFlags {
    /// `flags`.
    pub flags: nodebuilder::Flags,
    /// `internalFlags`.
    pub internal_flags: nodebuilder::InternalFlags,
    /// `depth`.
    pub depth: i32,
}

impl SaveRestoreFlags {
    /// The Go `func()` cleanup: restore `flags`, `internalFlags`, `depth`.
    pub fn restore(self, ctx: &mut NodeBuilderContext<'_>) {
        ctx.flags = self.flags;
        ctx.internal_flags = self.internal_flags;
        ctx.depth = self.depth;
    }
}

/// `type NodeBuilderImpl struct` — the checker back-pointer `ch *Checker`
/// becomes an explicit `&mut Checker` parameter on the methods that need it
/// (SPEC §5.4); `e`/`pc` live on the struct. `cloneBindingNameVisitor` is
/// built per-call (see header).
pub struct NodeBuilderImpl<'a> {
    // host members
    /// `f` — the "second" factory with emit-context hooks (see header).
    pub f: ast::NodeFactory<'a>,
    /// `e` — `*printer.EmitContext`.
    pub e: Rc<RefCell<EmitContext>>,
    /// `pc`.
    pub pc: pseudochecker::PseudoChecker,

    // cache
    /// `links` — `core.LinkStore[*ast.Node, NodeBuilderLinks]` keyed by
    /// `NodeId`.
    pub links: LinkStore<NodeId, NodeBuilderLinks>,
    /// `symbolLinks`.
    pub symbol_links: LinkStore<SymbolId, NodeBuilderSymbolLinks>,

    // state
    /// `ctx`.
    pub ctx: NodeBuilderContext<'a>,

    // symbols for synthesized identifiers, needed for e.g. inlay hints
    /// `idToSymbol` — `map[*ast.IdentifierNode]*ast.Symbol` keyed by the
    /// identifier's `NodeId`.
    pub id_to_symbol: FxHashMap<NodeId, SymbolId>,
}

/// Builds `b.f` — an `ast::NodeFactory` whose hooks mirror
/// `EmitContext::new`'s (onCreate → SYNTHESIZED, onUpdate/onClone →
/// `set_original_ex`). Same construction as
/// `transformers::new_transform_factory` (the visitor's `cx.factory` cannot
/// alias the emit context's factory).
pub(crate) fn new_nodebuilder_factory(e: &Rc<RefCell<EmitContext>>) -> ast::NodeFactory<'static> {
    // `Weak` avoids a reference cycle: impl -> factory -> hooks -> emit ctx.
    let update_weak = Rc::downgrade(e);
    let clone_weak = update_weak.clone();
    ast::NodeFactory::new(ast::NodeFactoryHooks {
        on_create: Some(Box::new(|nodes: &mut Vec<ast::Node>, node: NodeId| {
            nodes[node].flags |= ast::NodeFlags::SYNTHESIZED;
        })),
        on_update: Some(Box::new(
            move |_nodes: &mut Vec<ast::Node>, updated: NodeId, original: NodeId| {
                if let Some(ctx) = update_weak.upgrade() {
                    ctx.borrow().set_original_ex(updated, original, false);
                }
            },
        )),
        on_clone: Some(Box::new(
            move |_nodes: &mut Vec<ast::Node>, updated: NodeId, original: NodeId| {
                let Some(ctx) = clone_weak.upgrade() else {
                    return;
                };
                ctx.borrow().set_original_ex(updated, original, false);
                // PORT(deferred): Go's onClone additionally copies the
                // `autoGenerate` entry for identifiers/private identifiers;
                // `auto_generate` is `pub(crate)` to tsc-printer. Same gap as
                // `transformers::new_transform_factory`.
            },
        )),
    })
}

impl<'a> NodeBuilderImpl<'a> {
    /// `defaultMaximumTruncationLength`.
    pub const DEFAULT_MAXIMUM_TRUNCATION_LENGTH: i32 = 160;
    /// `noTruncationMaximumTruncationLength`.
    pub const NO_TRUNCATION_MAXIMUM_TRUNCATION_LENGTH: i32 = 1_000_000;
    /// `MAX_REVERSE_MAPPED_NESTING_INSPECTION_DEPTH`.
    pub const MAX_REVERSE_MAPPED_NESTING_INSPECTION_DEPTH: usize = 3;
}

// Node builder utility functions

/// `newNodeBuilderImpl`. PORT: `e` is wrapped in `Rc<RefCell>` (see header);
/// `cloneBindingNameVisitor` is not stored. `'a` is free — callers bind it
/// to the tracker lifetime they intend to feed `enter_context`.
pub fn new_node_builder_impl<'a>(
    c: &Checker,
    e: EmitContext,
    id_to_symbol: FxHashMap<NodeId, SymbolId>,
) -> NodeBuilderImpl<'a> {
    let e = Rc::new(RefCell::new(e));
    let f = new_nodebuilder_factory(&e);
    NodeBuilderImpl {
        f,
        e,
        pc: pseudochecker::PseudoChecker::new(
            c.strict_null_checks,
            c.exact_optional_property_types,
        ),
        links: LinkStore::new(),
        symbol_links: LinkStore::new(),
        ctx: NodeBuilderContext::default(),
        id_to_symbol,
    }
}

// Local arena helpers — each short-borrows the arena and copies the needed
// fields so `&mut Checker` calls never alias a live borrow.

/// `symbol.flags` read through the arena.
fn symbol_flags(c: &Checker, s: SymbolId) -> SymbolFlags {
    c.symbol_arena.get_ref(s).flags
}

/// `symbol.checkFlags` read through the arena.
fn symbol_check_flags(c: &Checker, s: SymbolId) -> ast::checkflags::CheckFlags {
    c.symbol_arena.get_ref(s).check_flags
}

/// `symbol.name` (cloned) read through the arena.
fn symbol_name(c: &Checker, s: SymbolId) -> String {
    c.symbol_arena.get_ref(s).name.to_string()
}

/// `ast.SymbolName` — decodes private-identifier class element names from
/// their declaration name node (`#context` rather than the internal
/// `\u{FFFD}#id@#context` encoding).
fn declaration_symbol_name(c: &Checker, s: SymbolId, nodes: &[ast::Node]) -> String {
    let arena = c.symbol_arena.clone();
    let sym = &arena[s.index()];
    let view = match sym.value_declaration {
        Some(vd) => crate::printer_util::resolve_arena_for(
            c.program.as_ref().expect("program"),
            nodes,
            vd,
        ),
        None => crate::printer_util::ArenaView::Working(nodes),
    };
    ast::symbol_name(sym, &view).into_owned()
}

/// `symbol.declarations` (cloned) read through the arena.
fn symbol_declarations(c: &Checker, s: SymbolId) -> Vec<NodeId> {
    c.symbol_arena.get_ref(s).declarations.clone()
}

/// `symbol.parent` read through the arena.
fn symbol_parent(c: &Checker, s: SymbolId) -> Option<SymbolId> {
    c.symbol_arena.get_ref(s).parent
}

/// `symbol.valueDeclaration` read through the arena.
fn symbol_value_declaration(c: &Checker, s: SymbolId) -> Option<NodeId> {
    c.symbol_arena.get_ref(s).value_declaration
}

/// `symbol.exports` — shared `Rc` handle (refcount bump) read through the arena.
fn symbol_exports(c: &Checker, s: SymbolId) -> Rc<ast::SymbolTable> {
    c.symbol_arena.get_ref(s).exports.clone()
}

/// `ast.GetSymbolId` — the arena index *is* the id.
fn get_symbol_id(s: SymbolId) -> SymbolId {
    s
}

/// `ast.GetNodeId` — the arena slot *is* the id.
fn get_node_id(n: NodeId) -> NodeId {
    n
}

/// `ast.SymbolName` — the *escaped* writeable name of a symbol.
fn ast_symbol_name(c: &Checker, s: SymbolId) -> String {
    ast::symbol::escape_symbol_name(&c.symbol_arena.get_ref(s).name).into_owned()
}

/// `t.flags` / `t.objectFlags` / `t.symbol` / `t.alias` reads.
fn type_flags(c: &Checker, t: TypeId) -> TypeFlags {
    c.types_handle().get(t).flags
}
fn type_object_flags(c: &Checker, t: TypeId) -> ObjectFlags {
    c.types_handle().get(t).object_flags
}
fn type_symbol(c: &Checker, t: TypeId) -> Option<SymbolId> {
    c.types_handle().get(t).symbol
}
fn type_alias(c: &Checker, t: TypeId) -> Option<TypeAlias> {
    c.types_handle().get(t).alias.clone()
}
fn type_id(c: &Checker, t: TypeId) -> TypeId {
    c.types_handle().get(t).id
}

/// `Option<NodeId>`-in-same-arena-or-none helper for `is_entity_name`.
fn is_entity_name_opt(node: Option<NodeId>, nodes: &[ast::Node]) -> bool {
    node.is_some_and(|n| ast::is_entity_name(&nodes[n]))
}

/// `Option<NodeId>` variant of `ast::is_identifier`.
fn is_identifier_opt(node: Option<NodeId>, nodes: &[ast::Node]) -> bool {
    node.is_some_and(|n| ast::is_identifier(&nodes[n]))
}

impl<'a> NodeBuilderImpl<'a> {
    /// `(b *NodeBuilderImpl) saveRestoreFlags` — Go returns `func()`; here a
    /// snapshot value restored via `Restore::restore` (the closure can't
    /// borrow `b` long-term).
    pub fn save_restore_flags(&self) -> SaveRestoreFlags {
        SaveRestoreFlags {
            flags: self.ctx.flags,
            internal_flags: self.ctx.internal_flags,
            depth: self.ctx.depth,
        }
    }

    /// `(b *NodeBuilderImpl) checkTruncationLength`.
    pub fn check_truncation_length(&mut self) -> bool {
        if self.ctx.truncating {
            return self.ctx.truncating;
        }
        let max_length;
        if self.ctx.flags.intersects(nodebuilder::Flags::NO_TRUNCATION) {
            max_length = Self::NO_TRUNCATION_MAXIMUM_TRUNCATION_LENGTH;
        } else if self.ctx.max_truncation_length > 0 {
            max_length = self.ctx.max_truncation_length;
        } else {
            max_length = Self::DEFAULT_MAXIMUM_TRUNCATION_LENGTH;
        }
        self.ctx.truncating = self.ctx.approximate_length > max_length;
        self.ctx.truncating
    }

    /// `(b *NodeBuilderImpl) checkTruncationLengthIfExpanding` — returns true
    /// if maxExpansionDepth >= 0 and truncation length exceeded. When
    /// expanding, we need to mark the output as truncated so we know not to
    /// offer further expansion.
    pub fn check_truncation_length_if_expanding(&mut self) -> bool {
        if self.ctx.max_expansion_depth >= 0 && self.check_truncation_length() {
            self.ctx.expansion_truncated = true;
            return true;
        }
        false
    }

    /// `(b *NodeBuilderImpl) isExpandableType` — reports whether t has a
    /// named representation that could be inlined as its structural form
    /// during hover expansion. Filters out lib types. When isAlias is true,
    /// checks whether t's alias symbol is from user code (not lib).
    fn is_expandable_type(&self, c: &mut Checker, t: TypeId, is_alias: bool) -> bool {
        if is_alias {
            return !c.is_lib_symbol_for_hover_verbosity(type_alias(c, t).and_then(|a| a.symbol));
        }
        if c.is_lib_type_for_hover_verbosity(t) {
            return false;
        }
        let object_flags = type_object_flags(c, t);
        if type_flags(c, t).intersects(TypeFlags::ENUM_LIKE)
            || object_flags.intersects(ObjectFlags::REFERENCE)
            || object_flags.intersects(ObjectFlags::CLASS_OR_INTERFACE)
        {
            return true;
        }
        if object_flags.intersects(ObjectFlags::ANONYMOUS)
            && let Some(symbol) = type_symbol(c, t)
            && symbol_flags(c, symbol).intersects(
                SymbolFlags::CLASS
                    | SymbolFlags::ENUM
                    | SymbolFlags::VALUE_MODULE
                    | SymbolFlags::FUNCTION
                    | SymbolFlags::METHOD,
            )
        {
            return true;
        }
        false
    }

    /// `(b *NodeBuilderImpl) isTypeOnStack` — reports whether t is already
    /// being processed in the current expansion, excluding the last element
    /// (which is the type currently being serialized by typeToTypeNode).
    fn is_type_on_stack(&self, t: TypeId) -> bool {
        let stack_len = self.ctx.type_stack.len();
        for i in 0..stack_len.saturating_sub(1) {
            if self.ctx.type_stack[i] == t {
                return true;
            }
        }
        false
    }

    /// `(b *NodeBuilderImpl) shouldExpandType` — decides whether to expand
    /// this type at the current depth.
    fn should_expand_type(&mut self, c: &mut Checker, t: TypeId, is_alias: bool) -> bool {
        if self.ctx.max_expansion_depth < 0 {
            return false;
        }
        if !self.is_expandable_type(c, t, is_alias) {
            return false;
        }
        if self.is_type_on_stack(t) {
            return false;
        }
        if self.ctx.depth < self.ctx.max_expansion_depth {
            return true;
        }
        self.ctx.can_increase_expansion_depth = true;
        false
    }

    /// `(b *NodeBuilderImpl) isActivelyExpanding`.
    pub fn is_actively_expanding(&self) -> bool {
        self.ctx.max_expansion_depth > 0 && self.ctx.depth < self.ctx.max_expansion_depth
    }

    /// `(b *NodeBuilderImpl) checkTypeExpandability` — probes whether a type
    /// (or its type arguments) could be expanded, for use after type-node
    /// reuse where shouldExpandType was never called.
    pub(crate) fn check_type_expandability(&mut self, c: &mut Checker, t: Option<TypeId>) {
        let Some(t) = t else { return };
        if self.ctx.max_expansion_depth < 0 || self.ctx.can_increase_expansion_depth {
            return;
        }
        // Push t onto the type stack so shouldExpandType's cycle detection
        // works correctly.
        self.ctx.type_stack.push(t);
        let result = self.check_type_expandability_inner(c, t);
        self.ctx.type_stack.pop();
        let _ = result;
    }

    pub(crate) fn check_type_expandability_inner(&mut self, c: &mut Checker, t: TypeId) {
        // If t is an ancestor in the current expansion, return early to
        // avoid unbounded recursion.
        if self.is_type_on_stack(t) {
            return;
        }
        if type_alias(c, t).is_some() {
            self.should_expand_type(c, t, true);
        }
        if !self.ctx.can_increase_expansion_depth {
            self.should_expand_type(c, t, false);
        }
        if self.ctx.can_increase_expansion_depth {
            return;
        }
        // Recurse into type arguments (e.g., check Apple in Promise<Apple>).
        if type_object_flags(c, t).intersects(ObjectFlags::REFERENCE) {
            for arg in c.get_type_arguments(t) {
                self.check_type_expandability(c, Some(arg));
                if self.ctx.can_increase_expansion_depth {
                    return;
                }
            }
        }
    }

    /// `(b *NodeBuilderImpl) appendReferenceToType`.
    fn append_reference_to_type(
        &mut self,
        _c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        root: NodeId,
        ref_: NodeId,
    ) -> Option<NodeId> {
        if ast::is_import_type_node(&nodes[root]) {
            // first shift type arguments
            let (is_type_of, argument, attributes) = {
                let imprt = nodes[root].as_import_type_node();
                (imprt.is_type_of, imprt.argument, imprt.attributes)
            };
            // then move qualifiers
            let ids = get_access_stack(nodes, ref_);
            let mut qualifier = nodes[root].as_import_type_node().qualifier;
            for id in ids {
                if let Some(q) = qualifier {
                    qualifier = Some(self.f.new_qualified_name(nodes, Some(q), Some(id)));
                } else {
                    qualifier = Some(id);
                }
            }
            let type_argument_list = nodes[ref_]
                .type_arguments()
                .map(|a| self.f.new_node_list(a.to_vec()));
            return self.f.update_import_type_node(
                nodes,
                root,
                is_type_of,
                argument,
                attributes,
                qualifier,
                type_argument_list,
            );
        } else if ast::is_type_reference_node(&nodes[root]) {
            let type_name = nodes[root].as_type_reference_node().type_name;
            let ref_args = nodes[ref_]
                .type_arguments()
                .map(|a| self.f.new_node_list(a.to_vec()));
            if self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::USE_INSTANTIATION_EXPRESSIONS)
                && nodes[root].type_arguments().is_some_and(|l| !l.is_empty())
            {
                let mut expr =
                    self.create_access_expression(nodes, type_name.unwrap_or(NodeId::NONE));
                let type_args = nodes[root]
                    .type_arguments()
                    .map(|a| self.f.new_node_list(a.to_vec()));
                expr = self.create_expression_with_type_arguments(nodes, expr, type_args);
                for id in get_access_stack(nodes, ref_) {
                    expr = self.f.new_property_access_expression(
                        nodes,
                        Some(expr),
                        None,
                        Some(id),
                        ast::NodeFlags::NONE,
                    );
                }
                return Some(expr);
            }
            let mut type_name = type_name;
            for id in get_access_stack(nodes, ref_) {
                type_name = Some(self.f.new_qualified_name(nodes, type_name, Some(id)));
            }
            return self
                .f
                .update_type_reference_node(nodes, root, type_name, ref_args);
        }
        let mut expr = self.create_access_expression(nodes, root);
        for id in get_access_stack(nodes, ref_) {
            expr = self.f.new_property_access_expression(
                nodes,
                Some(expr),
                None,
                Some(id),
                ast::NodeFlags::NONE,
            );
        }
        Some(expr)
    }

    /// `(b *NodeBuilderImpl) createElidedInformationPlaceholder`.
    fn create_elided_information_placeholder(&mut self, nodes: &mut Vec<ast::Node>) -> NodeId {
        self.ctx.approximate_length += 3;
        if !self.ctx.flags.intersects(nodebuilder::Flags::NO_TRUNCATION) {
            let id = self.f.new_identifier(nodes, "...");
            return self.f.new_type_reference_node(nodes, Some(id), None);
        }
        let node = self.f.new_keyword_type_node(nodes, Kind::AnyKeyword);
        self.e.borrow().add_synthetic_leading_comment(
            node,
            Kind::MultiLineCommentTrivia,
            "elided",
            false,
        )
    }

    /// `(b *NodeBuilderImpl) mapToTypeNodes`.
    fn map_to_type_nodes(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        list: &[TypeId],
        is_bare_list: bool,
    ) -> Option<NodeList> {
        if list.is_empty() {
            return None;
        }

        if self.check_truncation_length() {
            if !is_bare_list {
                let node;
                if self.ctx.flags.intersects(nodebuilder::Flags::NO_TRUNCATION) {
                    let n = self.f.new_keyword_type_node(nodes, Kind::AnyKeyword);
                    node = self.e.borrow().add_synthetic_leading_comment(
                        n,
                        Kind::MultiLineCommentTrivia,
                        "elided",
                        false,
                    );
                } else {
                    let id = self.f.new_identifier(nodes, "...");
                    node = self.f.new_type_reference_node(nodes, Some(id), None);
                }
                return Some(self.f.new_node_list([node]));
            } else if list.len() > 2 {
                let mut list_nodes = vec![
                    Some(self.type_to_type_node(c, nodes, list[0])),
                    None,
                    Some(self.type_to_type_node(c, nodes, list[list.len() - 1])),
                ];

                if self.ctx.flags.intersects(nodebuilder::Flags::NO_TRUNCATION) {
                    let n = self.f.new_keyword_type_node(nodes, Kind::AnyKeyword);
                    list_nodes[1] = Some(self.e.borrow().add_synthetic_leading_comment(
                        n,
                        Kind::MultiLineCommentTrivia,
                        &format!("... {} more elided ...", list.len() - 2),
                        false,
                    ));
                } else {
                    let text = format!("... {} more ...", list.len() - 2);
                    let id = self.f.new_identifier(nodes, &text);
                    list_nodes[1] = Some(self.f.new_type_reference_node(nodes, Some(id), None));
                }
                return Some(
                    self.f
                        .new_node_list(list_nodes.into_iter().flatten().collect::<Vec<_>>()),
                );
            }
        }

        let may_have_name_collisions = !self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::USE_FULLY_QUALIFIED_TYPE);
        // `*collections.MultiMap[string, seenName]` → name → Vec<(type, index)>.
        let mut seen_names: Option<FxHashMap<String, Vec<(TypeId, usize)>>> =
            may_have_name_collisions.then(FxHashMap::default);

        let mut result: Vec<NodeId> = Vec::with_capacity(list.len());

        for (i, &t) in list.iter().enumerate() {
            let display_index = i + 1;
            if self.check_truncation_length() && display_index + 2 < list.len() - 1 {
                if self.ctx.flags.intersects(nodebuilder::Flags::NO_TRUNCATION) {
                    let n = self.f.new_keyword_type_node(nodes, Kind::AnyKeyword);
                    result.push(self.e.borrow().add_synthetic_leading_comment(
                        n,
                        Kind::MultiLineCommentTrivia,
                        &format!("... {} more elided ...", list.len() - display_index),
                        false,
                    ));
                } else {
                    let text = format!("... {} more ...", list.len() - display_index);
                    let id = self.f.new_identifier(nodes, &text);
                    result.push(self.f.new_type_reference_node(nodes, Some(id), None));
                }
                result.push(self.type_to_type_node(c, nodes, list[list.len() - 1]));
                break;
            }
            self.ctx.approximate_length += 2; // Account for whitespace + separator
            let type_node = self.type_to_type_node(c, nodes, t);
            {
                result.push(type_node);
                if let Some(seen) = seen_names.as_mut()
                    && is_identifier_type_reference(nodes, type_node)
                {
                    let text = nodes[nodes[type_node].as_type_reference_node().type_name.unwrap()]
                        .text(nodes)
                        .into_owned();
                    seen.entry(text).or_default().push((t, result.len() - 1));
                }
            }
        }

        if let Some(seen) = seen_names {
            // To avoid printing types like `[Foo, Foo]` or `Bar & Bar` where
            // occurrences of the same name actually come from different
            // namespaces, go through the single-identifier type reference
            // nodes we just generated, and see if any names were generated
            // more than once while referring to different types. If so,
            // regenerate the type node for each entry by that name with the
            // `UseFullyQualifiedType` flag enabled.
            let restore_flags = self.save_restore_flags();
            self.ctx.flags |= nodebuilder::Flags::USE_FULLY_QUALIFIED_TYPE;
            for types in seen.values() {
                if !array_is_homogeneous(types, |a, b| types_are_same_reference(c, a.0, b.0)) {
                    for seen_entry in types {
                        let i = seen_entry.1;
                        let t = seen_entry.0;
                        result[i] = self.type_to_type_node(c, nodes, t);
                    }
                }
            }
            restore_flags.restore(&mut self.ctx);
        }

        Some(self.f.new_node_list(result))
    }

    /// `(b *NodeBuilderImpl) serializeTypeName`.
    pub(crate) fn serialize_type_name(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        node: NodeId,
        is_type_of: bool,
        type_arguments: Option<NodeList>,
    ) -> Option<NodeId> {
        let meaning = if is_type_of {
            SymbolFlags::VALUE
        } else {
            SymbolFlags::TYPE
        };
        let symbol =
            c.resolve_entity_name_live(Some(node), meaning, true, false, Some(node), Some(nodes));
        let symbol = symbol?;

        let mut resolved_symbol = symbol;
        if symbol_flags(c, symbol).intersects(SymbolFlags::ALIAS) {
            resolved_symbol = c.resolve_alias(symbol);
        }

        if c.is_symbol_accessible(
            Some(symbol),
            self.ctx.enclosing_declaration,
            meaning,
            false,
            Some(nodes),
        )
        .accessibility
            != printer::SymbolAccessibility::Accessible
        {
            return None;
        }
        self.symbol_to_type_node(c, nodes, resolved_symbol, meaning, type_arguments)
    }

    /// `(b *NodeBuilderImpl) setCommentRange`.
    pub(crate) fn set_comment_range(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        node: NodeId,
        range_: Option<NodeId>,
    ) {
        let Some(range_) = range_ else { return };
        if let Some(enclosing_file) = self.ctx.enclosing_file {
            let range_file = ast::get_source_file_of_node(Some(range_), &c.program_nodes_live(range_, nodes));
            if Some(enclosing_file) == range_file {
                // Copy comments to node for declaration emit
                self.e.borrow().assign_comment_range(nodes, node, range_);
            }
        }
        let _ = nodes;
    }

    /// `(b *NodeBuilderImpl) typeNodeIsEquivalentToType`.
    fn type_node_is_equivalent_to_type(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        annotated_declaration: Option<NodeId>,
        t: TypeId,
        type_from_type_node: TypeId,
    ) -> bool {
        if type_from_type_node == t {
            return true;
        }
        let Some(annotated_declaration) = annotated_declaration else {
            return false;
        };
        // !!!
        // used to be hasEffectiveQuestionToken for JSDoc
        if crate::utilities::is_optional_declaration(&nodes[annotated_declaration], nodes) {
            return c.get_type_with_facts(t, TypeFacts::NE_UNDEFINED) == type_from_type_node;
        }
        false
    }

    /// `(b *NodeBuilderImpl) canReuseExistingJSTypeNode`.
    pub(crate) fn can_reuse_existing_js_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        existing: NodeId,
        t: TypeId,
    ) -> bool {
        c.get_intended_type_from_js_doc_type_reference(existing, nodes).is_none()
            && self.existing_type_node_is_not_reference_or_is_reference_with_compatible_type_argument_count(c, nodes, existing, t)
    }

    /// `(b *NodeBuilderImpl) tryGetResolvedSymbolFromTypeNode`.
    pub(crate) fn try_get_resolved_symbol_from_type_node(
        &mut self,
        c: &mut Checker,
        node: Option<NodeId>,
            nodes: &[ast::Node],) -> Option<SymbolId> {
        let node = node?;
        let __program = c.program.clone().expect("program");
        let n_nodes = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
        n_nodes[node].parent?;
        c.get_type_from_type_node(node);
        // call to ensure symbol is resolved
        c.symbol_node_links
            .try_get(node)
            .and_then(|l| l.resolved_symbol)
    }

    /// `(b *NodeBuilderImpl)
    /// existingTypeNodeIsNotReferenceOrIsReferenceWithCompatibleTypeArgumentCount`.
    fn existing_type_node_is_not_reference_or_is_reference_with_compatible_type_argument_count(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        existing: NodeId,
        t: TypeId,
    ) -> bool {
        // In JS, you can say something like `Foo` and get a `Foo<any>`
        // implicitly - we don't want to preserve that original `Foo` in
        // these cases, though.
        if !type_object_flags(c, t).intersects(ObjectFlags::REFERENCE) {
            return true;
        }
        let __program = c.program.clone().expect("program");
        let e_nodes = crate::printer_util::arena_view(&__program, nodes, (existing).file_index());
        if !ast::is_type_reference_node(&e_nodes[existing]) {
            return true;
        }
        let existing_args_len = e_nodes[existing]
            .type_arguments()
            .map(|l| l.len())
            .unwrap_or(0);

        let Some(symbol) = self.try_get_resolved_symbol_from_type_node(c, Some(existing), nodes) else {
            return true;
        };

        // `type` is a reference type, and `existing` is a type reference
        // node, but we still need to make sure they refer to the _same_
        // target type before we go comparing their type argument counts.

        let existing_target = c.get_declared_type_of_symbol(symbol);
        let __arena_target = c.types.clone();
        let target = __arena_target
            .get(t)
            .data
            .as_type_reference()
            .and_then(|r| r.object_type.target);
        if Some(existing_target) != target {
            return true;
        }
        let target_type_params: Vec<TypeId> = c
            .types_handle()
            .get(target.unwrap())
            .data
            .as_interface_type()
            .map(|i| i.type_parameters().to_vec())
            .unwrap_or_default();
        let min_args = c.get_min_type_argument_count(&target_type_params);
        existing_args_len >= min_args
    }

    /// `(b *NodeBuilderImpl) tryReuseExistingNonParameterTypeNode`.
    fn try_reuse_existing_non_parameter_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        existing: NodeId,
        t: TypeId,
        host: Option<NodeId>,
        annotation_type: Option<TypeId>,
    ) -> Option<NodeId> {
        let host = host.or(self.ctx.enclosing_declaration);
        let annotation_type = match annotation_type {
            Some(t) => Some(t),
            None => self.get_type_from_type_node(c, existing, true, nodes),
        };
        if let Some(annotation_type) = annotation_type
            && self.type_node_is_equivalent_to_type(c, nodes, host, t, annotation_type)
            && self.can_reuse_existing_js_type_node(c, nodes, existing, t)
        {
            let result = self.try_reuse_existing_node_helper(c, nodes, existing);
            if result.is_some() {
                return result;
            }
        }
        None
    }

    /// `(b *NodeBuilderImpl) getResolvedTypeWithoutAbstractConstructSignatures`.
    fn get_resolved_type_without_abstract_construct_signatures(
        &mut self,
        c: &mut Checker,
        t: TypeId,
    ) -> TypeId {
        // `StructuredType` isn't `Clone`; extract the needed fields under a
        // single short borrow so `&mut Checker` calls below don't alias.
        let (all_construct_sigs, members, index_info_list, call_sigs, cached) = {
            let __arena_guard = c.types.clone();
            let guard = __arena_guard.get(t);
            let st = guard.data.as_structured_type();
            match st {
                Some(st) => (
                    st.construct_signatures().to_vec(),
                    st.members.clone(),
                    st.index_infos.clone(),
                    st.call_signatures().to_vec(),
                    st.object_type_without_abstract_construct_signatures,
                ),
                None => Default::default(),
            }
        };
        if all_construct_sigs.is_empty() {
            return t;
        }
        if let Some(t2) = cached {
            return t2;
        }
        let construct_signatures: Vec<SignatureId> = all_construct_sigs
            .iter()
            .copied()
            .filter(|&signature| {
                !c.signature_arena
                    .get(signature)
                    .flags
                    .intersects(SignatureFlags::ABSTRACT)
            })
            .collect();
        if construct_signatures.len() == all_construct_sigs.len() {
            c.types_handle()
                .get_mut(t)
                .data
                .as_structured_type_mut()
                .unwrap()
                .object_type_without_abstract_construct_signatures = Some(t);
            return t;
        }
        let index_infos: Vec<IndexInfoId> = index_info_list
            .iter()
            .map(|i| c.index_info_arena.alloc(i.clone()))
            .collect();
        let __arena_type_symbol = c.types.clone();
        let type_symbol = __arena_type_symbol.get(t).symbol;
        let type_copy = c.new_anonymous_type(
            type_symbol,
            members,
            &call_sigs,
            &construct_signatures,
            &index_infos,
        );
        c.types_handle()
            .get_mut(t)
            .data
            .as_structured_type_mut()
            .unwrap()
            .object_type_without_abstract_construct_signatures = Some(type_copy);
        c.types_handle()
            .get_mut(type_copy)
            .data
            .as_structured_type_mut()
            .unwrap()
            .object_type_without_abstract_construct_signatures = Some(type_copy);
        type_copy
    }

    /// `(b *NodeBuilderImpl) symbolToNode`.
    pub fn symbol_to_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: SymbolFlags,
    ) -> Option<NodeId> {
        if self
            .ctx
            .internal_flags
            .intersects(nodebuilder::InternalFlags::WRITE_COMPUTED_PROPS)
        {
            if let Some(value_declaration) = symbol_value_declaration(c, symbol) {
                let __program = c.program.clone().expect("program");
                let dn = crate::printer_util::arena_view(&__program, nodes, (value_declaration).file_index());
                let name = ast::get_name_of_declaration(Some(value_declaration), &dn);
                if let Some(name) = name
                    && ast::is_computed_property_name(&dn[name])
                {
                    return Some(name);
                }
            }
            if c.value_symbol_links.has(symbol) {
                let name_type = c.value_symbol_links.get(symbol).name_type;
                if let Some(name_type) = name_type
                    && type_flags(c, name_type)
                        .intersects(TypeFlags::ENUM_LITERAL | TypeFlags::UNIQUE_ES_SYMBOL)
                {
                    let old_enclosing = self.ctx.enclosing_declaration;
                    self.ctx.enclosing_declaration =
                        symbol_value_declaration(c, type_symbol(c, name_type)?);
                    let expr = self.symbol_to_expression_worker(
                        c,
                        nodes,
                        type_symbol(c, name_type)?,
                        meaning,
                    );
                    let result = self.f.new_computed_property_name(nodes, expr);
                    self.ctx.enclosing_declaration = old_enclosing;
                    return Some(result);
                }
            }
        }
        self.symbol_to_expression(c, nodes, symbol, meaning)
    }

    /// `(b *NodeBuilderImpl) symbolToName`.
    pub fn symbol_to_name(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: SymbolFlags,
        expects_identifier: bool,
    ) -> Option<NodeId> {
        let chain = self.lookup_symbol_chain(c, nodes, symbol, meaning, false);
        if expects_identifier
            && chain.len() != 1
            && !self.ctx.encountered_error
            && self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::ALLOW_QUALIFIED_NAME_IN_PLACE_OF_IDENTIFIER)
        {
            self.ctx.encountered_error = true;
        }
        self.create_entity_name_from_symbol_chain(c, nodes, &chain, chain.len() - 1)
    }

    /// `(b *NodeBuilderImpl) createEntityNameFromSymbolChain`.
    fn create_entity_name_from_symbol_chain(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        chain: &[SymbolId],
        index: usize,
    ) -> Option<NodeId> {
        // typeParameterNodes := b.lookupTypeParameterNodes(chain, index)
        let symbol = *chain.get(index)?;

        if index == 0 {
            self.ctx.flags |= nodebuilder::Flags::IN_INITIAL_ENTITY_NAME;
        }
        let sym_name = self.get_name_of_symbol_as_written(c, nodes, symbol);
        if index == 0 {
            self.ctx
                .flags
                .remove(nodebuilder::Flags::IN_INITIAL_ENTITY_NAME);
        }

        let identifier = self.new_identifier(nodes, &sym_name, Some(symbol));
        self.e
            .borrow()
            .add_emit_flags(identifier, printer::EmitFlags::NO_ASCII_ESCAPING);
        // !!! TODO: smuggle type arguments out
        if index > 0 {
            let left = self.create_entity_name_from_symbol_chain(c, nodes, chain, index - 1);
            return Some(self.f.new_qualified_name(nodes, left, Some(identifier)));
        }
        Some(identifier)
    }

    /// `(b *NodeBuilderImpl) symbolToEntityNameNode`.
    // TODO: Audit usages of symbolToEntityNameNode - they should probably
    // all be symbolToName
    fn symbol_to_entity_name_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
    ) -> Option<NodeId> {
        let name = symbol_name(c, symbol);
        let identifier = self.new_identifier(nodes, &name, Some(symbol));
        if let Some(parent) = symbol_parent(c, symbol) {
            let left = self.symbol_to_entity_name_node(c, nodes, parent);
            return Some(self.f.new_qualified_name(nodes, left, Some(identifier)));
        }
        Some(identifier)
    }

    /// `(b *NodeBuilderImpl) symbolToTypeNode`.
    pub fn symbol_to_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        mask: SymbolFlags,
        type_arguments: Option<NodeList>,
    ) -> Option<NodeId> {
        let yield_module_symbol = !self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE);
        let chain = self.lookup_symbol_chain(c, nodes, symbol, mask, yield_module_symbol);
        // If we're using aliases outside the current scope, dont bother with the module
        if chain.is_empty() {
            // TODO: shouldn't be possible, `lookupSymbolChain` should always
            // at least return the input symbol and issue an error
            return None;
        }
        let is_type_of = mask == SymbolFlags::VALUE;
        if symbol_declarations(c, chain[0]).iter().any(|&d| {
            crate::symbolaccessibility::has_non_global_augmentation_external_module_symbol(d, c, Some(nodes))
        }) {
            // module is root, must use `ImportTypeNode`
            let non_root_parts: Option<NodeId> = if chain.len() > 1 {
                self.create_access_from_symbol_chain(
                    c,
                    nodes,
                    &chain,
                    chain.len() - 1,
                    1,
                    type_arguments.clone(),
                )
            } else {
                None
            };
            let mut type_parameter_nodes = type_arguments.clone();
            if type_parameter_nodes.is_none() {
                type_parameter_nodes = self.lookup_type_parameter_nodes(c, nodes, &chain, 0);
            }
            // TODO: Just use b.ctx.enclosingFile ? Or is the delayed lookup
            // important for context moves?
            let most_original_decl = self
                .e
                .borrow()
                .most_original(self.ctx.enclosing_declaration);
            let context_file = most_original_decl
                .and_then(|d| ast::get_source_file_of_node(Some(d), &c.program_nodes_live(d, nodes)));
            let target_file = get_source_file_of_module_symbol(c, chain[0], nodes);
            let mut specifier_result = ModuleSpecifierResult::default();
            let mut import_mode_override = RESOLUTION_MODE_NONE;
            let module_resolution = c.module_resolution_kind;
            if module_resolution == ModuleResolutionKind::Node16
                || module_resolution == ModuleResolutionKind::NodeNext
            {
                // An `import` type directed at an esm format file is only
                // going to resolve in esm mode - set the esm mode assertion
                if let (Some(target_file), Some(context_file)) = (target_file, context_file) {
                    let program = c.program.clone();
                    if let Some(program) = program.as_ref() {
                        let __program = c.program.clone().expect("program");
                        let target_nodes = crate::printer_util::arena_view(&__program, nodes, (target_file).file_index());
                        let __program = c.program.clone().expect("program");
                        let context_nodes = crate::printer_util::arena_view(&__program, nodes, (context_file).file_index());
                        let target_format = program.get_emit_module_format_of_file(
                            target_nodes[target_file].as_source_file(),
                        );
                        let context_format = program.get_emit_module_format_of_file(
                            context_nodes[context_file].as_source_file(),
                        );
                        if target_format == ModuleKind::ESNext && target_format != context_format {
                            specifier_result = self.get_specifier_for_module_symbol(
                                c,
                                nodes,
                                chain[0],
                                ModuleKind::ESNext,
                            );
                            import_mode_override = ModuleKind::ESNext;
                        }
                    }
                }
            }
            if specifier_result.specifier.as_string().is_empty() {
                specifier_result =
                    self.get_specifier_for_module_symbol(c, nodes, chain[0], RESOLUTION_MODE_NONE);
            }
            if !self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::ALLOW_NODE_MODULES_RELATIVE_PATHS)
                && specifier_result
                    .specifier
                    .as_string()
                    .contains("/node_modules/")
            {
                let old_specifier_result = specifier_result.clone();
                if module_resolution == ModuleResolutionKind::Node16
                    || module_resolution == ModuleResolutionKind::NodeNext
                {
                    // We might be able to write a portable import type using
                    // a mode override; try specifier generation again, but
                    // with a different mode set
                    let context_format = context_file.and_then(|f| {
                        let __program = c.program.clone().expect("program");
                        let fn_ = crate::printer_util::arena_view(&__program, nodes, (f).file_index());
                        c.program.as_ref().map(|program| {
                            program.get_emit_module_format_of_file(fn_[f].as_source_file())
                        })
                    });
                    let swapped_mode = if context_format == Some(ModuleKind::ESNext) {
                        ModuleKind::CommonJS
                    } else {
                        ModuleKind::ESNext
                    };
                    specifier_result =
                        self.get_specifier_for_module_symbol(c, nodes, chain[0], swapped_mode);
                    if specifier_result
                        .specifier
                        .as_string()
                        .contains("/node_modules/")
                    {
                        // Still unreachable :(
                        specifier_result = old_specifier_result.clone();
                    } else {
                        import_mode_override = swapped_mode;
                    }
                }

                if import_mode_override == RESOLUTION_MODE_NONE {
                    // If ultimately we can only name the symbol with a
                    // reference that dives into a `node_modules` folder, we
                    // should error since declaration files with these kinds
                    // of references are liable to fail when published :(
                    self.ctx.encountered_error = true;
                    if let Some(tracker) = self.ctx.tracker.clone() {
                        tracker
                            .borrow_mut()
                            .report_likely_unsafe_import_required_error(
                                old_specifier_result.specifier.as_string(),
                                &c.symbol_arena.get_ref(symbol).name,
                                nodes,
                            );
                    }
                }
            }

            let attributes = self.create_import_attributes_for_module_specifier(
                c,
                nodes,
                &specifier_result,
                import_mode_override,
            );
            let specifier_string = specifier_result.specifier.as_string().to_owned();
            let lit_expr = self.new_string_literal(c, nodes, &specifier_string);
            let lit = self.f.new_literal_type_node(nodes, Some(lit_expr));
            self.ctx.approximate_length += specifier_string.len() as i32 + 10; // specifier + import("")
            if non_root_parts.is_none() || is_entity_name_opt(non_root_parts, nodes) {
                if non_root_parts.is_some() {
                    // !!! TODO: smuggle type arguments out
                    // const lastId = isIdentifier(nonRootParts) ? nonRootParts : nonRootParts.right;
                    // setIdentifierTypeArguments(lastId, /*typeArguments*/ undefined);
                }
                return Some(self.f.new_import_type_node(
                    nodes,
                    is_type_of,
                    Some(lit),
                    attributes,
                    non_root_parts,
                    type_parameter_nodes,
                ));
            }

            let split_node = get_topmost_indexed_access_type(nodes, non_root_parts?);
            let qualifier = nodes[split_node].as_indexed_access_type_node().object_type;
            let object_type = self.f.new_import_type_node(
                nodes,
                is_type_of,
                Some(lit),
                attributes,
                qualifier,
                type_parameter_nodes,
            );
            return Some(self.f.new_indexed_access_type_node(
                nodes,
                Some(object_type),
                nodes[split_node].as_indexed_access_type_node().index_type,
            ));
        }

        let entity_name = self.create_access_from_symbol_chain(
            c,
            nodes,
            &chain,
            chain.len() - 1,
            0,
            type_arguments.clone(),
        )?;
        if ast::is_indexed_access_type_node(&nodes[entity_name]) {
            return Some(entity_name); // Indexed accesses can never be `typeof`
        }
        if ast::is_entity_name(&nodes[entity_name]) {
            if is_type_of {
                return Some(self.f.new_type_query_node(nodes, Some(entity_name), None));
            }
            return Some(
                self.f
                    .new_type_reference_node(nodes, Some(entity_name), type_arguments),
            );
        }
        if is_type_of && ast::is_expression_with_type_arguments(&nodes[entity_name]) {
            let (expr, expr_args) = {
                let e = nodes[entity_name].as_expression_with_type_arguments();
                (e.expression, e.type_arguments.clone())
            };
            let cloned = self.f.deep_clone_node(nodes, expr?);
            return Some(self.f.new_type_query_node(nodes, cloned, expr_args));
        }
        Some(entity_name)
    }

    /// `(b *NodeBuilderImpl) createAccessFromSymbolChain`.
    fn create_access_from_symbol_chain(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        chain: &[SymbolId],
        index: usize,
        stopper: usize,
        override_type_arguments: Option<NodeList>,
    ) -> Option<NodeId> {
        let mut type_parameter_nodes = override_type_arguments.clone();
        if index != chain.len() - 1 {
            type_parameter_nodes = self
                .lookup_type_parameter_nodes(c, nodes, chain, index)
                .map(NodeList::from);
        }
        let symbol = *chain.get(index)?;
        let parent: Option<SymbolId> = if index > 0 {
            Some(chain[index - 1])
        } else {
            None
        };

        let mut sym_name = String::new();
        if index == 0 {
            self.ctx.flags |= nodebuilder::Flags::IN_INITIAL_ENTITY_NAME;
            sym_name = self.get_name_of_symbol_as_written(c, nodes, symbol);
            self.ctx.approximate_length += sym_name.len() as i32 + 1;
            self.ctx
                .flags
                .remove(nodebuilder::Flags::IN_INITIAL_ENTITY_NAME);
        } else {
            // lookup a ref to symbol within parent to handle export aliases
            if let Some(parent) = parent {
                let exports = c.get_exports_of_symbol(parent);
                if !exports.is_empty() {
                    // avoid exhaustive iteration in the common case
                    let name = symbol_name(c, symbol);
                    if name != ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                        && !crate::utilities::is_late_bound_name(&name)
                        && exports.get(name.as_str()).is_some_and(|&res| {
                            c.get_symbol_if_same_reference(res, symbol).is_some()
                        })
                    {
                        sym_name = name;
                    } else {
                        let mut results: FxHashMap<SymbolId, String> = FxHashMap::default();
                        for (ex_name, &ex) in &*exports {
                            if c.get_symbol_if_same_reference(ex, symbol).is_some()
                                && !crate::utilities::is_late_bound_name(ex_name)
                                && ex_name.as_ref()
                                    != ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                            {
                                results.insert(ex, ex_name.to_string());
                                // must collect all results and sort them -
                                // exports are randomly iterated
                            }
                        }
                        let mut result_symbols: Vec<SymbolId> = results.keys().copied().collect();
                        if !result_symbols.is_empty() {
                            c.sort_symbols(&mut result_symbols);
                            sym_name = results[&result_symbols[0]].clone();
                        }
                    }
                }
            }
        }

        if sym_name.is_empty() {
            let mut name: Option<NodeId> = None;
            for &d in &symbol_declarations(c, symbol) {
                let __program = c.program.clone().expect("program");
                let dn = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
                name = ast::get_name_of_declaration(Some(d), &dn);
                if name.is_some() {
                    break;
                }
            }
            if let Some(name) = name {
                let __program = c.program.clone().expect("program");
                let nn = crate::printer_util::arena_view(&__program, nodes, (name).file_index());
                if ast::is_computed_property_name(&nn[name])
                    && is_entity_name_opt(nn[name].expression(), &nn)
                {
                    // `name.Expression()` may live in a different arena;
                    // reuse the foreign-file id if arenas coincide. Captured
                    // before the `nodes` mutations below release `nn`.
                    let rhs_expr = nn[name].expression();
                    drop(nn);
                    let lhs = self.create_access_from_symbol_chain(
                        c,
                        nodes,
                        chain,
                        index - 1,
                        stopper,
                        override_type_arguments.clone(),
                    )?;
                    if ast::is_entity_name(&nodes[lhs]) {
                        let query_inner = self.f.new_type_query_node(nodes, Some(lhs), None);
                        let lhs = self.f.new_parenthesized_type_node(nodes, Some(query_inner));
                        let rhs = self.f.new_type_query_node(nodes, rhs_expr, None);
                        return Some(self.f.new_indexed_access_type_node(
                            nodes,
                            Some(lhs),
                            Some(rhs),
                        ));
                    }
                    return Some(lhs);
                }
            }
            sym_name = self.get_name_of_symbol_as_written(c, nodes, symbol);
        }
        self.ctx.approximate_length += sym_name.len() as i32 + 1;

        if !self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::FORBID_INDEXED_ACCESS_SYMBOL_REFERENCES)
            && parent.is_some()
        {
            let members = c.get_members_of_symbol(parent.unwrap());
            if !members.is_empty() {
                let name = symbol_name(c, symbol);
                if members
                    .get(name.as_str())
                    .is_some_and(|&m| c.get_symbol_if_same_reference(m, symbol).is_some())
                {
                    // Should use an indexed access
                    let lhs = self.create_access_from_symbol_chain(
                        c,
                        nodes,
                        chain,
                        index - 1,
                        stopper,
                        override_type_arguments.clone(),
                    )?;
                    let lit_expr = self.new_string_literal(c, nodes, &sym_name);
                    let literal = self.f.new_literal_type_node(nodes, Some(lit_expr));
                    if ast::is_indexed_access_type_node(&nodes[lhs]) {
                        return Some(self.f.new_indexed_access_type_node(
                            nodes,
                            Some(lhs),
                            Some(literal),
                        ));
                    }
                    let object =
                        self.f
                            .new_type_reference_node(nodes, Some(lhs), type_parameter_nodes);
                    return Some(self.f.new_indexed_access_type_node(
                        nodes,
                        Some(object),
                        Some(literal),
                    ));
                }
            }
        }

        let identifier = self.new_identifier(nodes, &sym_name, Some(symbol));
        self.e
            .borrow()
            .add_emit_flags(identifier, printer::EmitFlags::NO_ASCII_ESCAPING);

        if index > stopper {
            let lhs = self.create_access_from_symbol_chain(
                c,
                nodes,
                chain,
                index - 1,
                stopper,
                override_type_arguments.clone(),
            )?;
            if !self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::USE_INSTANTIATION_EXPRESSIONS)
                || (ast::is_entity_name(&nodes[lhs])
                    && type_parameter_nodes
                        .as_ref()
                        .is_none_or(|l| l.nodes.is_empty()))
            {
                return Some(
                    self.f
                        .new_qualified_name(nodes, Some(lhs), Some(identifier)),
                );
            }
            let expr = self.create_access_expression(nodes, lhs);
            let prop_access = self.f.new_property_access_expression(
                nodes,
                Some(expr),
                None,
                Some(identifier),
                ast::NodeFlags::NONE,
            );
            return Some(self.create_expression_with_type_arguments(
                nodes,
                prop_access,
                type_parameter_nodes,
            ));
        }
        Some(identifier)
    }

    /// `(b *NodeBuilderImpl) symbolToExpression`.
    pub fn symbol_to_expression(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        mask: SymbolFlags,
    ) -> Option<NodeId> {
        if let Some(tracker) = self.ctx.tracker.clone() {
            let nodes_view: &[ast::Node] = nodes;
            tracker.borrow_mut().track_symbol(
                symbol,
                self.ctx.enclosing_declaration,
                mask,
                nodes_view,
                &mut |sym, en, mn, sc| {
                    c.is_symbol_accessible(sym, en, mn, sc, Some(nodes_view))
                },
            );
        }
        self.symbol_to_expression_worker(c, nodes, symbol, mask)
    }

    /// `(b *NodeBuilderImpl) symbolToExpressionWorker`.
    pub fn symbol_to_expression_worker(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        mask: SymbolFlags,
    ) -> Option<NodeId> {
        let chain = self.lookup_symbol_chain_worker(c, nodes, symbol, mask, false);
        self.create_expression_from_symbol_chain(c, nodes, &chain, chain.len() - 1)
    }

    /// `(b *NodeBuilderImpl) createExpressionFromSymbolChain`.
    fn create_expression_from_symbol_chain(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        chain: &[SymbolId],
        index: usize,
    ) -> Option<NodeId> {
        let type_parameter_nodes =
            self.lookup_expression_chain_type_argument_nodes(c, nodes, chain, index);
        let symbol = *chain.get(index)?;

        if index == 0 {
            self.ctx.flags |= nodebuilder::Flags::IN_INITIAL_ENTITY_NAME;
        }
        let mut sym_name = self.get_name_of_symbol_as_written(c, nodes, symbol);
        if index == 0 {
            self.ctx
                .flags
                .remove(nodebuilder::Flags::IN_INITIAL_ENTITY_NAME);
        }

        if starts_with_single_or_double_quote(&sym_name)
            && symbol_declarations(c, symbol).iter().any(|&d| {
                crate::symbolaccessibility::has_non_global_augmentation_external_module_symbol(d, c, Some(nodes))
            })
        {
            let specifier_result =
                self.get_specifier_for_module_symbol(c, nodes, symbol, RESOLUTION_MODE_NONE);
            self.ctx.approximate_length += 2 + specifier_result.specifier.as_string().len() as i32;
            return Some(self.new_string_literal(c, nodes, specifier_result.specifier.as_string()));
        }

        if index == 0 || can_use_property_access(&sym_name) {
            let identifier = self.new_identifier(nodes, &sym_name, Some(symbol));
            self.e
                .borrow()
                .add_emit_flags(identifier, printer::EmitFlags::NO_ASCII_ESCAPING);
            self.ctx.approximate_length += 1 + sym_name.len() as i32;
            if index > 0 {
                let lhs = self.create_expression_from_symbol_chain(c, nodes, chain, index - 1);
                let result = self.f.new_property_access_expression(
                    nodes,
                    lhs,
                    None,
                    Some(identifier),
                    ast::NodeFlags::NONE,
                );
                self.e
                    .borrow()
                    .add_emit_flags(result, printer::EmitFlags::NO_INDENTATION);
                return Some(self.create_expression_with_type_arguments(
                    nodes,
                    result,
                    type_parameter_nodes,
                ));
            }
            return Some(self.create_expression_with_type_arguments(
                nodes,
                identifier,
                type_parameter_nodes,
            ));
        }

        if starts_with_square_bracket(&sym_name) {
            sym_name = sym_name[1..sym_name.len() - 1].to_owned();
        }

        let mut expression: Option<NodeId> = None;
        if starts_with_single_or_double_quote(&sym_name)
            && !symbol_flags(c, symbol).intersects(SymbolFlags::ENUM_MEMBER)
        {
            let literal_text = stringutil::unquote_string(sym_name.as_bytes());
            self.ctx.approximate_length += literal_text.len() as i32 + 2;
            expression = Some(self.new_string_literal_ex(
                c,
                nodes,
                &String::from_utf8_lossy(&literal_text),
                sym_name.as_bytes()[0] == b'\'',
            ));
        } else if jsnum::from_string(&sym_name).string() == sym_name {
            // TODO: the following in strada would assert if the number is
            // negative, but no such assertion exists here.
            // Moreover, what's even guaranteeing the name *isn't* -1 here
            // anyway? Needs double-checking.
            self.ctx.approximate_length += sym_name.len() as i32;
            expression = Some(
                self.f
                    .new_numeric_literal(nodes, &sym_name, ast::TokenFlags::NONE),
            );
        }
        if expression.is_none() {
            self.ctx.approximate_length += sym_name.len() as i32;
            let identifier = self.new_identifier(nodes, &sym_name, Some(symbol));
            self.e
                .borrow()
                .add_emit_flags(identifier, printer::EmitFlags::NO_ASCII_ESCAPING);
            expression = Some(identifier);
        }
        self.ctx.approximate_length += 2; // []
        let lhs = self.create_expression_from_symbol_chain(c, nodes, chain, index - 1);
        let element_access = self.f.new_element_access_expression(
            nodes,
            lhs,
            None,
            expression,
            ast::NodeFlags::NONE,
        );
        Some(self.create_expression_with_type_arguments(
            nodes,
            element_access,
            type_parameter_nodes,
        ))
    }

    /// `(b *NodeBuilderImpl) getNameOfSymbolFromNameType`.
    fn get_name_of_symbol_from_name_type(&mut self, c: &mut Checker, symbol: SymbolId) -> String {
        if c.value_symbol_links.has(symbol) {
            let name_type = c.value_symbol_links.get(symbol).name_type;
            let Some(name_type) = name_type else {
                return String::new();
            };
            if type_flags(c, name_type).intersects(TypeFlags::STRING_OR_NUMBER_LITERAL) {
                let name = match c
                    .types_handle()
                    .get(name_type)
                    .as_literal_type()
                    .value
                    .as_ref()
                {
                    Some(tsc_evaluator::Value::String(s)) => s.clone(),
                    Some(tsc_evaluator::Value::Number(n)) => n.string(),
                    _ => String::new(),
                };
                if !scanner::utilities::is_identifier_text(&name, LanguageVariant::Standard)
                    && !crate::utilities::is_numeric_literal_name(&name)
                {
                    return crate::checker_core::value_to_string(
                        c.types_handle()
                            .get(name_type)
                            .as_literal_type()
                            .value
                            .as_ref(),
                    );
                }
                if crate::utilities::is_numeric_literal_name(&name) && name.starts_with('-') {
                    return format!("[{}]", name);
                }
                return name;
            }
            if type_flags(c, name_type).intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
                // `nameType.AsUniqueESSymbolType().symbol` — the port stores
                // `symbol` on `TypeBase`, not the data payload.
                let es_symbol = type_symbol(c, name_type);
                let text = self.get_name_of_symbol_as_written(
                    c,
                    &mut Vec::new(),
                    es_symbol.unwrap_or(SymbolId::NONE),
                );
                return format!("[{}]", text);
            }
        }
        String::new()
    }

    /// `(b *NodeBuilderImpl) getNameOfSymbolAsWritten`.
    // Gets a human-readable name for a symbol. Should *not* be used for the
    // right-hand side of a `.` -- use `symbolName(symbol)` for that instead.
    //
    // Unlike `symbolName(symbol)`, this will include quotes if the name is
    // from a string literal. It will also use a representation of a number
    // as written instead of a decimal form, e.g. `0o11` instead of `9`.
    fn get_name_of_symbol_as_written(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
    ) -> String {
        let mut symbol = symbol;
        if let Some(&result) = self.ctx.remapped_symbol_references.get(&symbol) {
            symbol = result;
        }
        let declarations = symbol_declarations(c, symbol);
        let s_name = symbol_name(c, symbol);
        if s_name == ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT
            && !self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE)
            && (!self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::IN_INITIAL_ENTITY_NAME)
                // if the symbol is synthesized, it will only be referenced
                // externally it must print as `default`
                || declarations.is_empty()
                // if not in the same binding context (source file, module
                // declaration), it must print as `default`
                || (self.ctx.enclosing_declaration.is_some() && {
                    let decl_binding = {
                                                let __program = c.program.clone().expect("program");
                        let dn0 = crate::printer_util::arena_view(&__program, nodes, (declarations[0]).file_index());;
                        ast::find_ancestor(Some(declarations[0]), &dn0, &mut |n, nodes| {
                            is_default_binding_context(n, nodes)
                        })
                    };
                    let enclosing_binding = self.ctx.enclosing_declaration.and_then(|e| {
                                                let __program = c.program.clone().expect("program");
                        crate::printer_util::find_ancestor_resolved(&__program, nodes, Some(e), &mut |n, nodes| {
                            is_default_binding_context(n, nodes)
                        })
                    });
                    decl_binding != enclosing_binding
                }))
        {
            return "default".to_owned();
        }
        if !declarations.is_empty() {
            // Try using a declaration with a name, first
            let name = declarations.iter().find_map(|&d| {
                let __program = c.program.clone().expect("program");
                let dn = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
                ast::get_name_of_declaration(Some(d), &dn)
            });
            if let Some(name) = name {
                // !!! TODO: JS Object.defineProperty declarations
                // if ast.IsCallExpression(declaration) && ast.IsBindableObjectDefinePropertyCall(declaration) {
                //   return symbol.Name
                // }
                let __program = c.program.clone().expect("program");
                let nn = crate::printer_util::arena_view(&__program, nodes, (name).file_index());
                if ast::is_computed_property_name(&nn[name])
                    && !symbol_check_flags(c, symbol).intersects(ast::checkflags::CheckFlags::LATE)
                    && c.value_symbol_links.has(symbol)
                {
                    let name_type = c.value_symbol_links.get(symbol).name_type;
                    if name_type.is_some_and(|nt| {
                        type_flags(c, nt).intersects(TypeFlags::STRING_OR_NUMBER_LITERAL)
                    }) {
                        let result = self.get_name_of_symbol_from_name_type(c, symbol);
                        if !result.is_empty() {
                            return result;
                        }
                    }
                }
                return scanner::utilities::declaration_name_to_string(Some(name), &nn);
            }
            let declaration = declarations[0]; // Declaration may be nameless, but we'll try anyway
            let __program = c.program.clone().expect("program");
            let dn = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
            if dn[declaration]
                .parent
                .is_some_and(|p| c.program_nodes_live(p, nodes)[p].kind == Kind::VariableDeclaration)
            {
                let parent = dn[declaration].parent.unwrap();
                let __program = c.program.clone().expect("program");
                let parent_nodes = crate::printer_util::arena_view(&__program, nodes, (parent).file_index());
                let var_name = parent_nodes[parent].as_variable_declaration().name;
                let __program = c.program.clone().expect("program");
                let name_nodes = crate::printer_util::arena_view(&__program, nodes, (var_name.unwrap_or(parent)).file_index());
                return scanner::utilities::declaration_name_to_string(var_name, &name_nodes);
            }
            if ast::is_class_expression(&dn[declaration])
                || ast::is_function_expression(&dn[declaration])
                || ast::is_arrow_function(&dn[declaration])
            {
                if !self.ctx.encountered_error
                    && !self
                        .ctx
                        .flags
                        .intersects(nodebuilder::Flags::ALLOW_ANONYMOUS_IDENTIFIER)
                {
                    self.ctx.encountered_error = true;
                }
                match dn[declaration].kind {
                    Kind::ClassExpression => return "(Anonymous class)".to_owned(),
                    Kind::FunctionExpression | Kind::ArrowFunction => {
                        return "(Anonymous function)".to_owned();
                    }
                    _ => {}
                }
            }
        }
        let name = self.get_name_of_symbol_from_name_type(c, symbol);
        if !name.is_empty() {
            return name;
        }
        ast::symbol::escape_internal_symbol_name(&s_name).into_owned()
    }

    /// `(b *NodeBuilderImpl) getTypeParametersOfClassOrInterface`.
    // The full set of type parameters for a generic class or interface type
    // consists of its outer type parameters plus its locally declared type
    // parameters.
    fn get_type_parameters_of_class_or_interface(
        &mut self,
        c: &mut Checker,
        nodes: &[ast::Node],
        symbol: SymbolId,
    ) -> Vec<TypeId> {
        let mut result = c.get_outer_type_parameters_of_class_or_interface(symbol, nodes);
        result.extend(c.get_local_type_parameters_of_class_or_interface_or_type_alias(symbol, nodes));
        result
    }

    /// `(b *NodeBuilderImpl) lookupTypeParameterNodes`.
    fn lookup_type_parameter_nodes(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        chain: &[SymbolId],
        index: usize,
    ) -> Option<NodeList> {
        debug_assert!(!chain.is_empty() && index < chain.len());
        let symbol = chain[index];
        let symbol_id = get_symbol_id(symbol);
        if self.ctx.type_parameter_symbol_list.has(&symbol_id) {
            return None;
        }
        self.ctx.type_parameter_symbol_list.add(symbol_id);

        if self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME)
            && index < chain.len() - 1
        {
            if let Some(type_argument_nodes) =
                self.lookup_instantiated_type_argument_nodes(c, nodes, chain, index)
            {
                return Some(type_argument_nodes);
            }
            let type_parameter_nodes =
                self.type_parameters_to_type_parameter_declarations(c, nodes, symbol);
            if !type_parameter_nodes.is_empty() {
                return Some(self.f.new_node_list(type_parameter_nodes));
            }
            return None;
        }

        None
    }

    /// `(b *NodeBuilderImpl) lookupSymbolChain`.
    // TODO: move `lookupSymbolChain` and co to `symbolaccessibility.go` (but
    // getSpecifierForModuleSymbol uses much context which makes that hard?)
    pub(crate) fn lookup_symbol_chain(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: SymbolFlags,
        yield_module_symbol: bool,
    ) -> Vec<SymbolId> {
        if let Some(tracker) = self.ctx.tracker.clone() {
            let nodes_view: &[ast::Node] = nodes;
            tracker.borrow_mut().track_symbol(
                symbol,
                self.ctx.enclosing_declaration,
                meaning,
                nodes_view,
                &mut |sym, en, mn, sc| {
                    c.is_symbol_accessible(sym, en, mn, sc, Some(nodes_view))
                },
            );
        }
        self.lookup_symbol_chain_worker(c, nodes, symbol, meaning, yield_module_symbol)
    }

    /// `(b *NodeBuilderImpl) lookupSymbolChainWorker`.
    fn lookup_symbol_chain_worker(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: SymbolFlags,
        yield_module_symbol: bool,
    ) -> Vec<SymbolId> {
        // Try to get qualified name if the symbol is not a type parameter
        // and there is an enclosing declaration.
        let is_type_parameter = symbol_flags(c, symbol).intersects(SymbolFlags::TYPE_PARAMETER);
        if !is_type_parameter
            && (self.ctx.enclosing_declaration.is_some()
                || self
                    .ctx
                    .flags
                    .intersects(nodebuilder::Flags::USE_FULLY_QUALIFIED_TYPE))
            && !self
                .ctx
                .internal_flags
                .intersects(nodebuilder::InternalFlags::DO_NOT_INCLUDE_SYMBOL_CHAIN)
        {
            let chain = self.get_symbol_chain(c, nodes, symbol, meaning, true, yield_module_symbol);
            debug_assert!(!chain.is_empty());
            chain
        } else {
            vec![symbol]
        }
    }

    /// `(b *NodeBuilderImpl) getSymbolChain`.
    ///
    /// @param endOfChain Set to false for recursive calls; non-recursive
    /// calls should always output something.
    fn get_symbol_chain(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: SymbolFlags,
        end_of_chain: bool,
        yield_module_symbol: bool,
    ) -> Vec<SymbolId> {
        let mut accessible_symbol_chain = c.get_accessible_symbol_chain(
            symbol,
            self.ctx.enclosing_declaration,
            meaning,
            self.ctx
                .flags
                .intersects(nodebuilder::Flags::USE_ONLY_EXTERNAL_ALIASING),
            Some(nodes),
        );
        let mut qualifier_meaning = meaning;
        if accessible_symbol_chain.len() > 1 {
            qualifier_meaning = crate::symbolaccessibility::get_qualified_left_meaning(meaning);
        }
        if accessible_symbol_chain.is_empty()
            || c.needs_qualification(
                accessible_symbol_chain[0],
                self.ctx.enclosing_declaration,
                qualifier_meaning, Some(nodes))
        {
            // Go up and add our parent.
            let mut root = symbol;
            if !accessible_symbol_chain.is_empty() {
                root = accessible_symbol_chain[0];
            }
            let parents = c.get_containers_of_symbol(root, self.ctx.enclosing_declaration, meaning, Some(nodes));
            if !parents.is_empty() {
                let mut parent_specifiers: Vec<SortedSymbolNamePair> = parents
                    .iter()
                    .map(|&parent| {
                        if symbol_declarations(c, parent).iter().any(|&d| {
                            crate::symbolaccessibility::has_non_global_augmentation_external_module_symbol(d, c, Some(nodes))
                        }) {
                            SortedSymbolNamePair {
                                sym: parent,
                                name: self
                                    .get_specifier_for_module_symbol(c, nodes, parent, RESOLUTION_MODE_NONE)
                                    .specifier
                                    .as_string()
                                    .to_owned(),
                            }
                        } else {
                            SortedSymbolNamePair { sym: parent, name: String::new() }
                        }
                    })
                    .collect();
                parent_specifiers.sort_by(|a, b| self.sort_by_best_name(c, a, b));
                for pair in &parent_specifiers {
                    let parent = pair.sym;
                    let parent_chain = self.get_symbol_chain(
                        c,
                        nodes,
                        parent,
                        crate::symbolaccessibility::get_qualified_left_meaning(meaning),
                        false,
                        yield_module_symbol,
                    );
                    if !parent_chain.is_empty() {
                        let parent_exports = symbol_exports(c, parent);
                        if let Some(&exported) =
                            parent_exports.get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                            && c.get_symbol_if_same_reference(exported, symbol).is_some()
                        {
                            // parentChain root _is_ symbol - symbol is a
                            // module export=, so it kinda looks like it's own
                            // parent. No need to lookup an alias for the
                            // symbol in itself
                            accessible_symbol_chain = parent_chain;
                            break;
                        }
                        let mut next_syms = accessible_symbol_chain.clone();
                        if next_syms.is_empty() {
                            let mut fallback = c.get_alias_for_symbol_in_container(parent, symbol);
                            if fallback.is_none() {
                                fallback = Some(symbol);
                            }
                            next_syms.push(fallback.unwrap());
                        }
                        let mut new_chain = parent_chain;
                        new_chain.extend(next_syms);
                        accessible_symbol_chain = new_chain;
                        break;
                    }
                }
            }
        }
        if !accessible_symbol_chain.is_empty() {
            return accessible_symbol_chain;
        }
        if end_of_chain
            // If a parent symbol is an anonymous type, don't write it.
            || !symbol_flags(c, symbol)
                .intersects(SymbolFlags::TYPE_LITERAL | SymbolFlags::OBJECT_LITERAL)
        {
            // If a parent symbol is an external module, don't write it. (We
            // prefer just `x` vs `"foo/bar".x`.)
            if !end_of_chain
                && !yield_module_symbol
                && symbol_declarations(c, symbol).iter().any(|&d| {
                    crate::symbolaccessibility::has_non_global_augmentation_external_module_symbol(
                        d, c, Some(nodes))
                })
            {
                return Vec::new();
            }
            return vec![symbol];
        }
        Vec::new()
    }

    /// `(b_ *NodeBuilderImpl) sortByBestName`.
    fn sort_by_best_name(
        &mut self,
        c: &mut Checker,
        a: &SortedSymbolNamePair,
        b: &SortedSymbolNamePair,
    ) -> std::cmp::Ordering {
        let specifier_a = &a.name;
        let specifier_b = &b.name;
        if !specifier_a.is_empty() && !specifier_b.is_empty() {
            let is_b_relative = tsc_tspath::path_is_relative(specifier_b);
            if tsc_tspath::path_is_relative(specifier_a) == is_b_relative {
                // Both relative or both non-relative, sort by number of parts
                return tsc_modulespecifiers::compare::count_path_components(specifier_a).cmp(
                    &tsc_modulespecifiers::compare::count_path_components(specifier_b),
                );
            }
            if is_b_relative {
                // A is non-relative, B is relative: prefer A
                return std::cmp::Ordering::Less;
            }
            // A is relative, B is non-relative: prefer B
            return std::cmp::Ordering::Greater;
        }
        // must sort symbols for stable ordering
        let compare = c
            .compare_symbols
            .clone()
            .expect("compareSymbols is initialized by new_checker");
        compare(c, Some(a.sym), Some(b.sym)).cmp(&0)
    }

    /// `(b *NodeBuilderImpl) getSpecifierForModuleSymbol`.
    pub(crate) fn get_specifier_for_module_symbol(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        override_import_mode: ResolutionMode,
    ) -> ModuleSpecifierResult {
        let enclosing_declaration = self
            .e
            .borrow()
            .most_original(self.ctx.enclosing_declaration);
        let original_module_specifier = enclosing_declaration.and_then(|d| {
            let __program = c.program.clone().expect("program");
            let dn = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
            if can_have_module_specifier(&dn[d]) {
                try_get_module_specifier_from_declaration(d, &dn)
            } else {
                None
            }
        });
        let original_import_attributes_type = original_module_specifier
            .and_then(|s| c.get_import_attributes_type_for_module_specifier(s));

        let mut file = get_declaration_of_kind_of_symbol(c, symbol, Kind::SourceFile, nodes);
        if file.is_none() {
            let equivalent_symbol = symbol_declarations(c, symbol)
                .iter()
                .find_map(|&d| c.get_file_symbol_if_file_symbol_export_equals_container(d, symbol, None));
            if let Some(equivalent_symbol) = equivalent_symbol {
                file = get_declaration_of_kind_of_symbol(c, equivalent_symbol, Kind::SourceFile, nodes);
            }
        }

        if file.is_none() {
            let declaration = symbol_declarations(c, symbol).iter().copied().find(|&d| {
                let __program = c.program.clone().expect("program");
                let dn = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
                ast::is_module_with_string_literal_name(&dn[d], &dn)
            });
            if let Some(declaration) = declaration {
                let __program = c.program.clone().expect("program");
                let dn = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
                let specifier = tsc_tspath::to_module_specifier(
                    &dn[dn[declaration].name().expect("module declaration name")].text(&dn),
                );
                if let Some(original_import_attributes_type) = original_import_attributes_type
                    && self.module_specifier_resolves_to_symbol(
                        c,
                        &specifier,
                        original_import_attributes_type,
                        symbol,
                    )
                {
                    return ModuleSpecifierResult {
                        specifier,
                        import_attributes_type: Some(original_import_attributes_type),
                    };
                }
                return ModuleSpecifierResult {
                    specifier,
                    import_attributes_type: Some(c.get_type_of_module_import_attributes(symbol)),
                };
            }
            if let Some(specifier) =
                ast::symbol::try_get_ambient_module_name_from_symbol_name(&symbol_name(c, symbol))
            {
                return ModuleSpecifierResult {
                    specifier: tsc_tspath::to_module_specifier(&specifier),
                    import_attributes_type: None,
                };
            }
        }
        if self.ctx.enclosing_file.is_none() {
            if let Some(specifier) =
                ast::symbol::try_get_ambient_module_name_from_symbol_name(&symbol_name(c, symbol))
            {
                return ModuleSpecifierResult {
                    specifier: tsc_tspath::to_module_specifier(&specifier),
                    import_attributes_type: None,
                };
            }
            let module_file = get_source_file_of_module_symbol(c, symbol, nodes);
            let specifier = module_file
                .map(|f| {
                    let __program = c.program.clone().expect("program");
                    let fn_ = crate::printer_util::arena_view(&__program, nodes, (f).file_index());
                    tsc_tspath::to_module_specifier(fn_[f].as_source_file().file_name().as_string())
                })
                .unwrap_or_default();
            return ModuleSpecifierResult {
                specifier,
                import_attributes_type: None,
            };
        }

        let context_file = self.ctx.enclosing_file.unwrap();
        let mut resolution_mode = override_import_mode;
        if resolution_mode == RESOLUTION_MODE_NONE && original_module_specifier.is_some() {
            let host = self.ctx.host.clone();
            let __program = c.program.clone().expect("program");
            let fn_ = crate::printer_util::arena_view(&__program, nodes, (context_file).file_index());
            resolution_mode = host.as_ref().unwrap().get_mode_for_usage_location(
                fn_[context_file].as_source_file(),
                original_module_specifier.unwrap(),
            );
        } else if resolution_mode == RESOLUTION_MODE_NONE {
            let host = self.ctx.host.clone();
            let __program = c.program.clone().expect("program");
            let fn_ = crate::printer_util::arena_view(&__program, nodes, (context_file).file_index());
            resolution_mode = host
                .as_ref()
                .unwrap()
                .get_default_resolution_mode_for_file(fn_[context_file].as_source_file());
        }
        let cache_key = tsc_module::ModeAwareCacheKey {
            name: {
                let __program = c.program.clone().expect("program");
                let fn_ = crate::printer_util::arena_view(&__program, nodes, (context_file).file_index());
                fn_[context_file]
                    .as_source_file()
                    .path_key()
                    .as_string()
                    .to_owned()
            },
            mode: resolution_mode,
        };
        let cached = self
            .symbol_links
            .get(symbol)
            .specifier_cache
            .get(&cache_key)
            .cloned();
        if let Some(result) = cached {
            return self.module_specifier_result_for_symbol(
                c,
                result,
                original_import_attributes_type,
                symbol,
            );
        }
        // For declaration bundles, we need to generate absolute paths
        // relative to the common source dir for imports, just like how the
        // declaration emitter does for the ambient module declarations - we
        // can easily accomplish this using the `baseUrl` compiler option
        // (which we would otherwise never use in declaration emit) and a
        // non-relative specifier preference
        let specifier_compiler_options = c.compiler_options.clone();
        let specifier_pref =
            tsc_modulespecifiers::ImportModuleSpecifierPreference::PROJECT_RELATIVE;
        let ending_pref = if resolution_mode == RESOLUTION_MODE_ESM {
            tsc_modulespecifiers::ImportModuleSpecifierEndingPreference::JS
        } else {
            tsc_modulespecifiers::ImportModuleSpecifierEndingPreference::NONE
        };
        let host_adapter = HostAdapter(
            self.ctx
                .host
                .clone()
                .expect("NodeBuilderContext.host must be set for specifier generation"),
        );
        let __program = c.program.clone().expect("program");
        let file_nodes = crate::printer_util::arena_view(&__program, nodes, (context_file).file_index());
        let symbol_arena = c.symbol_arena.clone();
        let symbol_arena_ref = symbol_arena.clone();
        let checker_adapter = CheckerShapeAdapter::new(&mut *c);
        // Node ids the specifier machinery dereferences may live in other
        // files' arenas — Go's single global heap hid this. `resolve`
        // routes a file index to its arena (live `nodes` buffer, registered
        // live arenas, or a program snapshot).
        let resolve_program = __program.clone();
        let resolve_nodes: &[ast::Node] = nodes;
        let resolve = move |fi: u32| {
            Some(
                match crate::printer_util::arena_view(&resolve_program, resolve_nodes, fi) {
                    crate::printer_util::ArenaView::Snapshot(rc) => rc,
                    crate::printer_util::ArenaView::Working(s) => {
                        std::rc::Rc::new(ast::NodeArenaBuf::new(s.to_vec()))
                    }
                },
            )
        };
        let module_specifiers_result = tsc_modulespecifiers::get_module_specifiers(
            symbol,
            &checker_adapter,
            &specifier_compiler_options,
            file_nodes[context_file].as_source_file(),
            &host_adapter,
            &tsc_modulespecifiers::UserPreferences {
                import_module_specifier_preference: specifier_pref,
                import_module_specifier_ending: ending_pref,
                ..Default::default()
            },
            &tsc_modulespecifiers::ModuleSpecifierOptions {
                override_import_mode,
            },
            false, // forAutoImports
            &symbol_arena_ref,
            nodes,
            &resolve,
        );
        drop(symbol_arena_ref);
        debug_assert!(!module_specifiers_result.specifiers.is_empty());
        let mut result = ModuleSpecifierResult {
            specifier: module_specifiers_result.specifiers[0].clone(),
            import_attributes_type: None,
        };
        if let Some(ambient_module_symbol) = module_specifiers_result.ambient_module_symbol {
            result.import_attributes_type =
                Some(c.get_type_of_module_import_attributes(ambient_module_symbol));
        }
        self.symbol_links
            .get(symbol)
            .specifier_cache
            .insert(cache_key, result.clone());
        self.module_specifier_result_for_symbol(c, result, original_import_attributes_type, symbol)
    }

    /// `(b *NodeBuilderImpl) moduleSpecifierResultForSymbol`.
    fn module_specifier_result_for_symbol(
        &mut self,
        c: &mut Checker,
        mut result: ModuleSpecifierResult,
        import_attributes_type: Option<TypeId>,
        symbol: SymbolId,
    ) -> ModuleSpecifierResult {
        if let Some(import_attributes_type) = import_attributes_type
            && self.module_specifier_resolves_to_symbol(
                c,
                &result.specifier,
                import_attributes_type,
                symbol,
            )
        {
            result.import_attributes_type = Some(import_attributes_type);
        }
        result
    }

    /// `(b *NodeBuilderImpl) moduleSpecifierResolvesToSymbol`.
    fn module_specifier_resolves_to_symbol(
        &mut self,
        c: &mut Checker,
        specifier: &tsc_tspath::ModuleSpecifier,
        import_attributes_type: TypeId,
        symbol: SymbolId,
    ) -> bool {
        let mut location = self.ctx.enclosing_declaration;
        if location.is_none() && self.ctx.enclosing_file.is_some() {
            location = self.ctx.enclosing_file;
        }
        let Some(location) = location else {
            return false;
        };
        let resolved = c.resolve_external_module(
            location,
            specifier.as_string(),
            None,
            None,
            false, // isForAugmentation
            Some(import_attributes_type),
        );
        resolved.is_some() && c.get_merged_symbol(resolved.unwrap()) == c.get_merged_symbol(symbol)
    }

    /// `(b *NodeBuilderImpl) createImportAttributesForModuleSpecifier`.
    fn create_import_attributes_for_module_specifier(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        result: &ModuleSpecifierResult,
        import_mode_override: ResolutionMode,
    ) -> Option<NodeId> {
        let is_empty_attributes_type = result.import_attributes_type.is_none()
            || c.is_empty_object_type(result.import_attributes_type.unwrap());
        if is_empty_attributes_type && import_mode_override == RESOLUTION_MODE_NONE {
            return None;
        }

        let mut properties: Vec<SymbolId> = Vec::new();
        if !is_empty_attributes_type {
            properties = c.get_properties_of_type(result.import_attributes_type.unwrap());
        }
        properties.sort_by(|a, b| symbol_name(c, *a).cmp(&symbol_name(c, *b)));
        let mut attributes: Vec<NodeId> = Vec::with_capacity(properties.len() + 1);
        if import_mode_override != RESOLUTION_MODE_NONE {
            let resolution_mode = if import_mode_override == RESOLUTION_MODE_ESM {
                "import"
            } else {
                "require"
            };
            let name = self.new_string_literal(c, nodes, "resolution-mode");
            let value = self.new_string_literal(c, nodes, resolution_mode);
            attributes.push(self.f.new_import_attribute(nodes, Some(name), Some(value)));
            self.ctx.approximate_length +=
                ("resolution-mode".len() + resolution_mode.len() + 6) as i32; // `"resolution-mode": "value"`
        }
        for &property in &properties {
            let name = symbol_name(c, property);
            let property_type = c.get_type_of_symbol(property);
            if !type_flags(c, property_type).intersects(TypeFlags::STRING_LITERAL) {
                continue;
            }
            let value = crate::checker_d::get_string_literal_value(&c.types, property_type);
            let name_node =
                if scanner::utilities::is_identifier_text(&name, LanguageVariant::Standard) {
                    self.f.new_identifier(nodes, &name)
                } else {
                    self.ctx.approximate_length += 2;
                    self.new_string_literal(c, nodes, &name)
                };
            let value_node = self.new_string_literal(c, nodes, &value);
            attributes.push(
                self.f
                    .new_import_attribute(nodes, Some(name_node), Some(value_node)),
            );
            self.ctx.approximate_length += (name.len() + value.len() + 4) as i32; // `name: "value"`
        }
        if attributes.is_empty() {
            return None;
        }
        self.ctx.approximate_length += 16 + 2 * (attributes.len() as i32 - 1); // `, { with: { , ... , } }`
        Some(self.f.new_import_attributes(
            nodes,
            Kind::WithKeyword,
            Some(self.f.new_node_list(attributes)),
            false,
        ))
    }

    /// `(b *NodeBuilderImpl) typeParameterToDeclarationWithConstraint`.
    fn type_parameter_to_declaration_with_constraint(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        type_parameter: TypeId,
        constraint_node: Option<NodeId>,
    ) -> NodeId {
        let restore_flags = self.save_restore_flags();
        // Avoids potential infinite loop when building for a claimspace with a generic
        self.ctx
            .flags
            .remove(nodebuilder::Flags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME);
        let modifier_flags = c.get_type_parameter_modifiers(type_parameter);
        let modifiers = ast::create_modifiers_from_modifier_flags(modifier_flags, &mut |kind| {
            self.f.new_token(nodes, kind)
        });
        let modifiers_list = if !modifiers.is_empty() {
            Some(self.f.new_modifier_list(nodes, modifiers))
        } else {
            None
        };
        let name = self.type_parameter_to_name(c, nodes, type_parameter);
        let default_parameter = c.get_default_from_type_parameter(type_parameter);
        let default_parameter_declaration_node =
            default_parameter.map(|default| self.type_to_type_node(c, nodes, default));
        restore_flags.restore(&mut self.ctx);
        self.f.new_type_parameter_declaration(
            nodes,
            modifiers_list,
            Some(name),
            constraint_node,
            None, // expression
            default_parameter_declaration_node,
        )
    }

    /// `(b *NodeBuilderImpl) setTextRange`.
    ///
    /// Unlike the utilities `setTextRange`, this checks if the `location`
    /// we're trying to set on `range` is within the same file as the active
    /// context. If not, the range is not applied. This prevents us from
    /// copying ranges across files, which will confuse the node printer (as
    /// it assumes all node ranges are within the current file).
    /// Additionally, if `range` _isn't synthetic_, or isn't in the current
    /// file, it will _copy_ it to _remove_ its position information.
    ///
    /// It also calls `setOriginalNode` to set up an `.original` pointer,
    /// since you basically *always* want these in the node builder.
    pub(crate) fn set_text_range(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        range_: Option<NodeId>,
        location: Option<NodeId>,
    ) -> Option<NodeId> {
        let Some(mut range_) = range_ else {
            return range_;
        };
        // `nodes` is the builder's live working arena (`self.f.file_index()`).
        // The arena may be checked out or `nodes_mut`-borrowed for the whole
        // build, so ids minted for that file must be read through `nodes` —
        // a fresh `program.nodes` borrow would either panic on the held
        // `RefMut` or hit the checkout's frozen mirror without the synthetic
        // nodes appended during this build.
        let f_index = self.f.file_index();
        let in_nodes = |id: NodeId| id.file_index() == f_index;
        let most_original_of_range = self
            .e
            .borrow()
            .most_original(Some(range_))
            .unwrap_or(range_);
        let enclosing_file_matches = match (self.ctx.enclosing_file, most_original_of_range) {
            (Some(file), mo) => {
                if in_nodes(mo) {
                    ast::get_source_file_of_node(Some(mo), nodes) == Some(file)
                } else {
                    let __program = c.program.clone().expect("program");
                    let mo_nodes = crate::printer_util::arena_view(&__program, nodes, (mo).file_index());
                    ast::get_source_file_of_node(Some(mo), &mo_nodes) == Some(file)
                }
            }
            _ => false,
        };
        let (range_is_synthesized, range_has_synth_flag) = if in_nodes(range_) {
            (
                ast::node_is_synthesized(&nodes[range_]),
                nodes[range_]
                    .flags
                    .intersects(ast::NodeFlags::SYNTHESIZED),
            )
        } else {
            let __program = c.program.clone().expect("program");
            let range_nodes = crate::printer_util::arena_view(&__program, nodes, (range_).file_index());
            (
                ast::node_is_synthesized(&range_nodes[range_]),
                range_nodes[range_]
                    .flags
                    .intersects(ast::NodeFlags::SYNTHESIZED),
            )
        };
        if !range_is_synthesized
            || !range_has_synth_flag
            || self.ctx.enclosing_file.is_none()
            || !enclosing_file_matches
        {
            let original = range_;
            // if `range` is synthesized or originates in another file, copy
            // it so it definitely has synthetic positions
            range_ = self.f.clone_node(nodes, range_);
            nodes[range_].loc = tsc_core::text::TextRange::new(-1, -1);
            if let Some(&symbol) = self.id_to_symbol.get(&original) {
                self.id_to_symbol.insert(range_, symbol);
            }
        }
        let Some(location) = location else {
            return Some(range_);
        };
        if range_ == location {
            return Some(range_);
        }
        // Don't overwrite the original node if `range` has an `original`
        // node that points either directly or indirectly to `location`
        let mut original = self.e.borrow().original(range_);
        while let Some(o) = original {
            if o == location {
                break;
            }
            original = self.e.borrow().original(o);
        }
        if original.is_none() {
            self.e.borrow().set_original_ex(range_, location, true);
        }

        // only set positions if range comes from the same file since copying
        // text across files isn't supported by the emitter
        let most_original_of_location = self
            .e
            .borrow()
            .most_original(Some(location))
            .unwrap_or(location);
        let location_file_matches = self.ctx.enclosing_file.is_some() && {
            let mo = most_original_of_location;
            if in_nodes(mo) {
                self.ctx.enclosing_file == ast::get_source_file_of_node(Some(mo), nodes)
            } else {
                let __program = c.program.clone().expect("program");
                let mo_nodes = crate::printer_util::arena_view(&__program, nodes, (mo).file_index());
                self.ctx.enclosing_file == ast::get_source_file_of_node(Some(mo), &mo_nodes)
            }
        };
        if location_file_matches {
            let loc = if in_nodes(location) {
                nodes[location].loc
            } else {
                let __program = c.program.clone().expect("program");
                let loc_nodes = crate::printer_util::arena_view(&__program, nodes, (location).file_index());
                loc_nodes[location].loc
            };
            nodes[range_].loc = loc;
            return Some(range_);
        }
        nodes[range_].loc = tsc_core::text::TextRange::new(-1, -1);
        Some(range_)
    }

    /// `(b *NodeBuilderImpl) typeParameterShadowsOtherTypeParameterInScope`.
    fn type_parameter_shadows_other_type_parameter_in_scope(
        &mut self,
        c: &mut Checker,
        nodes: &[ast::Node],
        name: &str,
        type_parameter: TypeId,
    ) -> bool {
        let result = c.resolve_name_via_binder_live(
            self.ctx.enclosing_declaration,
            name,
            ast::SymbolFlags::TYPE,
            None,
            false,
            false,
            Some(nodes),
        );
        if let Some(result) = result
            && symbol_flags(c, result).intersects(ast::SymbolFlags::TYPE_PARAMETER)
        {
            return Some(result) != type_symbol(c, type_parameter);
        }
        false
    }

    /// `(b *NodeBuilderImpl) typeParameterToName`.
    pub fn type_parameter_to_name(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        type_parameter: TypeId,
    ) -> NodeId {
        let tp_symbol = type_symbol(c, type_parameter).unwrap_or(SymbolId::NONE);
        if self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
        {
            if let Some(&(cached, epoch)) = self.ctx.type_parameter_names.get(&type_parameter)
                && epoch == self.ctx.nodes_epoch.get()
            {
                return cached;
            }
            // The tp was named under a different arena epoch — remint the
            // decided text into the current buffer rather than re-running
            // the rename loop (which would claim yet another name).
            if let Some(text) = self
                .ctx
                .type_parameter_name_texts
                .get(&type_parameter)
                .cloned()
            {
                let sym = (tp_symbol != SymbolId::NONE).then_some(tp_symbol);
                let result = self.new_identifier(nodes, &text, sym);
                self.ctx
                    .type_parameter_names
                    .set(type_parameter, (result, self.ctx.nodes_epoch.get()));
                return result;
            }
        }
        let mut result = self
            .symbol_to_name(c, nodes, tp_symbol, ast::SymbolFlags::TYPE, true)
            .unwrap_or(NodeId::NONE);
        if result == NodeId::NONE || !ast::is_identifier(&nodes[result]) {
            return self.f.new_identifier(nodes, "(Missing type parameter)");
        }
        let decls = if tp_symbol != SymbolId::NONE {
            symbol_declarations(c, tp_symbol)
        } else {
            Vec::new()
        };
        if !decls.is_empty() {
            let decl = decls[0];
            let __program = c.program.clone().expect("program");
            let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (decl).file_index());
            if ast::is_type_parameter_declaration(&decl_nodes[decl]) {
                result = self
                    .set_text_range(c, nodes, Some(result), decl_nodes[decl].name())
                    .unwrap_or(result);
            }
        }
        if self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
        {
            let raw_text = nodes[result].text(nodes).into_owned();
            let mut i = self
                .ctx
                .type_parameter_names_by_text_next_name_count
                .get(&raw_text)
                .copied()
                .unwrap_or(0);
            let mut text = raw_text.clone();

            loop {
                if !self.ctx.type_parameter_names_by_text.has(&text)
                    && !self.type_parameter_shadows_other_type_parameter_in_scope(
                        c,
                        nodes,
                        &text,
                        type_parameter,
                    )
                {
                    break;
                }
                i += 1;
                text = format!("{}_{}", raw_text, i);
            }

            if text != raw_text {
                // !!! TODO: smuggle type arguments out
                // const typeArguments = getIdentifierTypeArguments(result);
                result = self.new_identifier(nodes, &text, type_symbol(c, type_parameter));
                // setIdentifierTypeArguments(result, typeArguments);
            }

            // avoiding iterations of the above loop turns out to be worth it
            // when `i` starts to get large, so we cache the max `i` we've
            // used thus far, to save work later
            self.ctx
                .type_parameter_names_by_text_next_name_count
                .set(raw_text.clone(), i);
            self.ctx
                .type_parameter_names
                .set(type_parameter, (result, self.ctx.nodes_epoch.get()));
            self.ctx
                .type_parameter_name_texts
                .set(type_parameter, text.clone());
            self.ctx.type_parameter_names_by_text.add(text);
        }

        result
    }

    /// `(b *NodeBuilderImpl) isMappedTypeHomomorphic`.
    fn is_mapped_type_homomorphic(&mut self, c: &mut Checker, mapped: TypeId) -> bool {
        c.get_homomorphic_type_variable(mapped).is_some()
    }

    /// `(b *NodeBuilderImpl) isHomomorphicMappedTypeWithNonHomomorphicInstantiation`.
    fn is_homomorphic_mapped_type_with_non_homomorphic_instantiation(
        &mut self,
        c: &mut Checker,
        mapped: TypeId,
    ) -> bool {
        let __arena_target = c.types.clone();
        let target = __arena_target
            .get(mapped)
            .as_mapped_type()
            .object_type
            .target;
        target.is_some()
            && !self.is_mapped_type_homomorphic(c, mapped)
            && self.is_mapped_type_homomorphic(c, target.unwrap())
    }

    /// `(b *NodeBuilderImpl) createMappedTypeNodeFromType`.
    fn create_mapped_type_node_from_type(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
    ) -> NodeId {
        debug_assert!(type_flags(c, t).intersects(TypeFlags::OBJECT));
        let (declaration, readonly_kind, question_kind, name_type_present) = {
            let __arena_t_guard = c.types.clone();
            let t_guard = __arena_t_guard.get(t);
            let mapped = t_guard.as_mapped_type();
            let declaration = mapped.declaration;
            let (readonly_kind, question_kind, name_type_present) = declaration
                .map(|d| {
                    let __program = c.program.clone().expect("program");
                    let dn = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
                    let md = dn[d].as_mapped_type_node();
                    (
                        md.readonly_token.map(|tok| dn[tok].kind),
                        md.question_token.map(|tok| dn[tok].kind),
                        md.name_type.is_some(),
                    )
                })
                .unwrap_or((None, None, false));
            (declaration, readonly_kind, question_kind, name_type_present)
        };
        let readonly_token = readonly_kind.map(|k| self.f.new_token(nodes, k));
        let question_token = question_kind.map(|k| self.f.new_token(nodes, k));
        // Every arm of the mapped-type constraint selection below assigns
        // this exactly once — deferred init.
        let appropriate_constraint_type_node: Option<NodeId>;
        let mut new_type_variable: Option<NodeId> = None;
        let mut template_type = c.get_template_type_from_mapped_type(t);
        let type_parameter = c.get_type_parameter_from_mapped_type(t);

        // If the mapped type isn't `keyof` constraint-declared, _but_ still has
        // modifiers preserved, and its naive instantiation won't preserve
        // modifiers because its constraint isn't `keyof` constrained, we have
        // work to do
        let needs_modifier_preserving_wrapper = !c
            .is_mapped_type_with_keyof_constraint_declaration(t)
            && !c
                .get_modifiers_type_from_mapped_type(t)
                .is_some_and(|mt| type_flags(c, mt).intersects(TypeFlags::UNKNOWN))
            && self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
            && !(c
                .get_constraint_type_from_mapped_type(t)
                .is_some_and(|ct| type_flags(c, ct).intersects(TypeFlags::TYPE_PARAMETER))
                && c.get_constraint_type_from_mapped_type(t)
                    .and_then(|ct| c.get_constraint_of_type_parameter(ct))
                    .is_some_and(|cc| type_flags(c, cc).intersects(TypeFlags::INDEX)));

        if c.is_mapped_type_with_keyof_constraint_declaration(t) {
            // We have a { [P in keyof T]: X }
            // We do this to ensure we retain the toplevel keyof-ness of the
            // type which may be lost due to keyof distribution during
            // `getConstraintTypeFromMappedType`
            if self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
                && self.is_homomorphic_mapped_type_with_non_homomorphic_instantiation(c, t)
            {
                let new_param_sym = c.new_symbol(ast::SymbolFlags::TYPE_PARAMETER, "T");
                let new_constraint_param = c.new_type_parameter(Some(new_param_sym));
                let name = self.type_parameter_to_name(c, nodes, new_constraint_param);
                let __arena_target = c.types.clone();
                let target = __arena_target.get(t).target();
                new_type_variable = Some(self.f.new_type_reference_node(nodes, Some(name), None));
                if let Some(target) = target {
                    let target_type_parameter = c.get_type_parameter_from_mapped_type(target);
                    let target_modifiers_type = c.get_modifiers_type_from_mapped_type(target);
                    let target_template = c.get_template_type_from_mapped_type(target);
                    if let (Some(tp), Some(mt), Some(tt)) = (
                        target_type_parameter,
                        target_modifiers_type,
                        target_template,
                    ) {
                        let mapper = crate::mapper::new_type_mapper(
                            c,
                            vec![tp, mt],
                            vec![type_parameter.unwrap_or(TypeId::NONE), new_constraint_param],
                        );
                        template_type = Some(c.instantiate_type(tt, Some(mapper)));
                    }
                }
            }
            let index_target = match new_type_variable {
                Some(v) => Some(v),
                None => c
                    .get_modifiers_type_from_mapped_type(t)
                    .map(|mt| self.type_to_type_node(c, nodes, mt)),
            };
            appropriate_constraint_type_node = Some(self.f.new_type_operator_node(
                nodes,
                Kind::KeyOfKeyword,
                index_target,
            ));
        } else if needs_modifier_preserving_wrapper {
            // So, step 1: new type variable
            let new_param_sym = c.new_symbol(ast::SymbolFlags::TYPE_PARAMETER, "T");
            let new_param = c.new_type_parameter(Some(new_param_sym));
            let name = self.type_parameter_to_name(c, nodes, new_param);
            new_type_variable = Some(self.f.new_type_reference_node(nodes, Some(name), None));
            // step 2: make that new type variable itself the constraint node,
            // making the mapped type `{[K in T_1]: Template}`
            appropriate_constraint_type_node = new_type_variable;
        } else {
            appropriate_constraint_type_node = c
                .get_constraint_type_from_mapped_type(t)
                .map(|ct| self.type_to_type_node(c, nodes, ct));
        }

        // nameType and templateType nodes have to be in the new scope
        let scope_type_params: Vec<TypeId> = c
            .get_type_parameter_from_mapped_type(t)
            .into_iter()
            .collect();
        let cleanup = self.enter_new_scope(
            c,
            nodes,
            declaration,
            None,
            Some(scope_type_params),
            None,
            None,
        );
        let type_parameter_declaration_node = self.type_parameter_to_declaration_with_constraint(
            c,
            nodes,
            type_parameter.unwrap_or(TypeId::NONE),
            appropriate_constraint_type_node,
        );
        let name_type_node = if name_type_present {
            c.get_name_type_from_mapped_type(t)
                .map(|nt| self.type_to_type_node(c, nodes, nt))
        } else {
            None
        };
        let include_optional =
            get_mapped_type_modifiers_local(c, t, nodes).intersects(MappedTypeModifiers::INCLUDE_OPTIONAL);
        let template_type_node = template_type.map(|tt| {
            let tt = c.remove_missing_type(tt, include_optional);
            self.type_to_type_node(c, nodes, tt)
        });
        cleanup.restore(self, nodes);
        let result = self.f.new_mapped_type_node(
            nodes,
            readonly_token,
            Some(type_parameter_declaration_node),
            name_type_node,
            question_token,
            template_type_node,
            None,
        );
        self.ctx.approximate_length += 10;
        self.e
            .borrow()
            .add_emit_flags(result, printer::EmitFlags::SINGLE_LINE);

        if self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
            && self.is_homomorphic_mapped_type_with_non_homomorphic_instantiation(c, t)
        {
            // homomorphic mapped type with a non-homomorphic naive inlining
            // wrap it with a conditional like `SomeModifiersType extends
            // infer U ? {..the mapped type...} : never` to ensure the
            // resulting type stays homomorphic
            let mut raw_constraint_type_from_declaration = declaration.and_then(|d| {
                let __program = c.program.clone().expect("program");
                let dn = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
                let cn = dn[d]
                    .as_mapped_type_node()
                    .type_parameter
                    .and_then(|tp| dn[tp].as_type_parameter_declaration().constraint)
                    // Go: `Constraint.Type()` — the node's `type` field (e.g.
                    // the operand of `keyof T`), not the constraint node's own
                    // resolved type.
                    .and_then(|cn| dn[cn].type_());
                cn.map(|cn| self.get_type_from_type_node(c, cn, false, nodes))
                    .flatten()
            });
            if let Some(raw) = raw_constraint_type_from_declaration {
                raw_constraint_type_from_declaration = c.get_constraint_of_type_parameter(raw);
            }
            let raw_constraint_type_from_declaration =
                raw_constraint_type_from_declaration.unwrap_or(c.unknown_type);
            let __arena_mapped_mapper = c.types.clone();
            let mapped_mapper = __arena_mapped_mapper
                .get(t)
                .as_mapped_type()
                .object_type
                .mapper;
            let original_constraint =
                c.instantiate_type(raw_constraint_type_from_declaration, mapped_mapper);
            let original_constraint_node =
                if !type_flags(c, original_constraint).intersects(TypeFlags::UNKNOWN) {
                    Some(self.type_to_type_node(c, nodes, original_constraint))
                } else {
                    None
                };
            let modifiers_node = c
                .get_modifiers_type_from_mapped_type(t)
                .map(|mt| self.type_to_type_node(c, nodes, mt));
            let cloned_name = new_type_variable.and_then(|v| {
                nodes[v]
                    .as_type_reference_node()
                    .type_name
                    .and_then(|n| self.f.clone_node(nodes, n).into())
            });
            let cloned_name = cloned_name.map(|n| match n {
                x => x,
            });
            let infer_param = self.f.new_type_parameter_declaration(
                nodes,
                None,
                cloned_name,
                original_constraint_node,
                None,
                None,
            );
            let infer_node = self.f.new_infer_type_node(nodes, Some(infer_param));
            let never_node = self.f.new_keyword_type_node(nodes, Kind::NeverKeyword);
            return self.f.new_conditional_type_node(
                nodes,
                modifiers_node,
                Some(infer_node),
                Some(result),
                Some(never_node),
            );
        } else if needs_modifier_preserving_wrapper {
            // and step 3: once the mapped type is reconstructed, create a
            // `ConstraintType extends infer T_1 extends keyof ModifiersType ?
            // {[K in T_1]: Template} : never`
            // subtly different from the `keyof` constraint case, by including
            // the `keyof` constraint on the `infer` type parameter, it
            // doesn't rely on the constraint type being itself constrained to
            // a `keyof` type to preserve its modifier-preserving behavior.
            let constraint_node = c
                .get_constraint_type_from_mapped_type(t)
                .map(|ct| self.type_to_type_node(c, nodes, ct));
            let cloned_name = new_type_variable
                .and_then(|v| nodes[v].as_type_reference_node().type_name)
                .map(|n| self.f.clone_node(nodes, n));
            let keyof_operand = c
                .get_modifiers_type_from_mapped_type(t)
                .map(|mt| self.type_to_type_node(c, nodes, mt));
            let keyof_node =
                self.f
                    .new_type_operator_node(nodes, Kind::KeyOfKeyword, keyof_operand);
            let infer_param = self.f.new_type_parameter_declaration(
                nodes,
                None,
                cloned_name,
                Some(keyof_node),
                None,
                None,
            );
            let infer_node = self.f.new_infer_type_node(nodes, Some(infer_param));
            let never_node = self.f.new_keyword_type_node(nodes, Kind::NeverKeyword);
            return self.f.new_conditional_type_node(
                nodes,
                constraint_node,
                Some(infer_node),
                Some(result),
                Some(never_node),
            );
        }

        result
    }

    /// `(b *NodeBuilderImpl) typePredicateToTypePredicateNode`.
    pub fn type_predicate_to_type_predicate_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        predicate: &TypePredicate,
    ) -> NodeId {
        let asserts_modifier = if predicate.kind == TypePredicateKind::AssertsIdentifier
            || predicate.kind == TypePredicateKind::AssertsThis
        {
            Some(self.f.new_token(nodes, Kind::AssertsKeyword))
        } else {
            None
        };
        let parameter_name = if predicate.kind == TypePredicateKind::Identifier
            || predicate.kind == TypePredicateKind::AssertsIdentifier
        {
            let parameter_name = self.f.new_identifier(nodes, &predicate.parameter_name);
            self.e
                .borrow()
                .add_emit_flags(parameter_name, printer::EmitFlags::NO_ASCII_ESCAPING);
            parameter_name
        } else {
            self.f.new_this_type_node(nodes)
        };
        let type_node = predicate.t.map(|t| self.type_to_type_node(c, nodes, t));
        self.f
            .new_type_predicate_node(nodes, asserts_modifier, Some(parameter_name), type_node)
    }

    /// `(b *NodeBuilderImpl) typeToTypeNodeHelperWithPossibleReusableTypeNode`.
    fn type_to_type_node_helper_with_possible_reusable_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: Option<TypeId>,
        type_node: Option<NodeId>,
    ) -> NodeId {
        let Some(t) = t else {
            return self.f.new_keyword_type_node(nodes, Kind::AnyKeyword);
        };
        if !self.is_actively_expanding()
            && type_node.is_some()
            && self.get_type_from_type_node(c, type_node.unwrap(), false, nodes) == Some(t)
        {
            if let Some(reused) = self.try_reuse_existing_node_helper(c, nodes, type_node.unwrap())
            {
                self.check_type_expandability(c, Some(t));
                return reused;
            }
        }
        self.type_to_type_node(c, nodes, t)
    }

    /// `(b *NodeBuilderImpl) typeParameterToDeclaration`.
    pub(crate) fn type_parameter_to_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        parameter: TypeId,
    ) -> NodeId {
        let constraint = c.get_constraint_of_type_parameter(parameter);
        let constraint_node = constraint.map(|constraint| {
            let constraint_decl = c.get_constraint_declaration(parameter);
            self.type_to_type_node_helper_with_possible_reusable_type_node(
                c,
                nodes,
                Some(constraint),
                constraint_decl,
            )
        });
        self.type_parameter_to_declaration_with_constraint(c, nodes, parameter, constraint_node)
    }

    /// `(b *NodeBuilderImpl) symbolToTypeParameterDeclarations`.
    pub fn symbol_to_type_parameter_declarations(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
    ) -> Vec<NodeId> {
        self.type_parameters_to_type_parameter_declarations(c, nodes, symbol)
    }

    /// `(b *NodeBuilderImpl) typeParametersToTypeParameterDeclarations`.
    pub fn type_parameters_to_type_parameter_declarations(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
    ) -> Vec<NodeId> {
        let target_symbol = get_target_symbol(c, symbol);
        let target_flags = symbol_flags(c, target_symbol);
        if target_flags.intersects(
            ast::SymbolFlags::CLASS | ast::SymbolFlags::INTERFACE | ast::SymbolFlags::ALIAS,
        ) {
            let mut results = Vec::new();
            let params = c.get_local_type_parameters_of_class_or_interface_or_type_alias(symbol, nodes);
            for param in params.iter().copied() {
                results.push(self.type_parameter_to_declaration(c, nodes, param));
            }
            return results;
        } else if target_flags.intersects(ast::SymbolFlags::FUNCTION) {
            let mut results = Vec::new();
            let value_declaration = symbol_value_declaration(c, symbol);
            let params = value_declaration
                .map(|d| c.get_type_parameters_from_declaration(d))
                .unwrap_or_default();
            for param in params {
                results.push(self.type_parameter_to_declaration(c, nodes, param));
            }
            return results;
        }
        Vec::new()
    }

    /// `(b *NodeBuilderImpl) symbolToParameterDeclaration`.
    pub fn symbol_to_parameter_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        parameter_symbol: SymbolId,
        preserve_modifier_flags: bool,
    ) -> NodeId {
        let parameter_declaration = get_effective_parameter_declaration(c, parameter_symbol, nodes);

        let parameter_type = c.get_type_of_symbol(parameter_symbol);
        let parameter_type_node = self.serialize_type_for_declaration(
            c,
            nodes,
            parameter_declaration,
            Some(parameter_type),
            Some(parameter_symbol),
            true,
        );
        let mut modifiers = None;
        if !self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::OMIT_PARAMETER_MODIFIERS)
            && preserve_modifier_flags
            && let Some(parameter_declaration) = parameter_declaration
        {
            let __program = c.program.clone().expect("program");
            let pd_nodes = crate::printer_util::arena_view(&__program, nodes, (parameter_declaration).file_index());
            if ast::can_have_modifiers(&pd_nodes[parameter_declaration]) {
                let originals: Vec<NodeId> = pd_nodes[parameter_declaration]
                    .modifier_nodes()
                    .map(|ms| {
                        ms.iter()
                            .copied()
                            .filter(|&m| ast::is_modifier(&pd_nodes[m]))
                            .collect()
                    })
                    .unwrap_or_default();
                if !originals.is_empty() {
                    let clones: Vec<NodeId> = originals
                        .iter()
                        .map(|&m| self.f.clone_node(nodes, m))
                        .collect();
                    modifiers = Some(self.f.new_modifier_list(nodes, clones));
                }
            }
        }
        let is_rest = parameter_declaration.is_some_and(|d| {
            let __program = c.program.clone().expect("program");
            let pd_nodes = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
            is_rest_parameter(&pd_nodes, d)
        }) || symbol_check_flags(c, parameter_symbol)
            .intersects(ast::checkflags::CheckFlags::REST_PARAMETER);
        let dot_dot_dot_token = if is_rest {
            Some(self.f.new_token(nodes, Kind::DotDotDotToken))
        } else {
            None
        };
        let name = self.parameter_to_parameter_declaration_name(
            c,
            nodes,
            parameter_symbol,
            parameter_declaration,
        );
        let is_optional = parameter_declaration.is_some_and(|d| c.is_optional_parameter(d))
            || symbol_check_flags(c, parameter_symbol)
                .intersects(ast::checkflags::CheckFlags::OPTIONAL_PARAMETER);
        let question_token = if is_optional {
            Some(self.f.new_token(nodes, Kind::QuestionToken))
        } else {
            None
        };

        let parameter_node = self.f.new_parameter_declaration(
            nodes,
            modifiers,
            dot_dot_dot_token,
            name,
            question_token,
            Some(parameter_type_node),
            None, // initializer
        );
        self.ctx.approximate_length += (symbol_name(c, parameter_symbol).len() + 3) as i32;
        parameter_node
    }

    /// `(b *NodeBuilderImpl) parameterToParameterDeclarationName`.
    pub(crate) fn parameter_to_parameter_declaration_name(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        parameter_symbol: SymbolId,
        parameter_declaration: Option<NodeId>,
    ) -> Option<NodeId> {
        let name = parameter_declaration.and_then(|d| {
            let __program = c.program.clone().expect("program");
            let pd_nodes = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
            pd_nodes[d].name()
        });
        let Some(name) = name else {
            return Some(self.new_identifier(
                nodes,
                &symbol_name(c, parameter_symbol),
                Some(parameter_symbol),
            ));
        };
        let __program = c.program.clone().expect("program");
        let name_nodes = crate::printer_util::arena_view(&__program, nodes, (name).file_index());
        match name_nodes[name].kind {
            Kind::Identifier => {
                drop(name_nodes);
                let cloned = self.deep_clone_node_in(c, nodes, name);
                if let Some(cloned) = cloned {
                    self.e
                        .borrow()
                        .set_emit_flags(cloned, printer::EmitFlags::NO_ASCII_ESCAPING);
                    self.id_to_symbol.insert(cloned, parameter_symbol);
                }
                cloned
            }
            Kind::QualifiedName => {
                let right = name_nodes[name].as_qualified_name().right;
                drop(name_nodes);
                let cloned = right.and_then(|r| self.deep_clone_node_in(c, nodes, r));
                if let Some(cloned) = cloned {
                    self.e
                        .borrow()
                        .set_emit_flags(cloned, printer::EmitFlags::NO_ASCII_ESCAPING);
                    self.id_to_symbol.insert(cloned, parameter_symbol);
                }
                cloned
            }
            _ => Some(self.clone_binding_name(c, nodes, name)),
        }
    }

    /// `f.DeepCloneNode(node)` where `node` may live in another file's arena.
    /// Go reads the source through raw pointers and appends clones anywhere;
    /// the port clones inside the source arena (`nodes_mut` — a different
    /// `RefCell` than `nodes`, so no borrow conflict) and relocates the
    /// appended tail into `nodes`, remapping ids like `clone_binding_name`.
    /// Only valid when `nodes` is the `self.f.file_index()` arena.
    pub(crate) fn deep_clone_node_in(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        node: NodeId,
    ) -> Option<NodeId> {
        // Fast path only when `nodes` physically contains `node` (its
        // packed id self-verifies against the slot) — a `file_index` match
        // alone is not enough: an id minted into a since-dropped scratch
        // buffer shares the file index but resolves to nothing here.
        if crate::printer_util::buffer_resolves_id(nodes, node) {
            return self.f.deep_clone_node(nodes, node);
        }
        let program = c.program.clone().expect("program");
        // Resolve the foreign buffer WITHOUT cloning it — a registered
        // live buffer first (builder-minted trees can live in a working
        // buffer newer than the program snapshot), else the program
        // arena's shared snapshot. The old path cloned the whole source
        // arena (O(arena) memcpy + a padding `resize` of Node clones) per
        // call; grafting copies only the subtree, then `deep_clone_node`
        // runs same-buffer. Result is identical: the returned tree's
        // `most_original` chain ends at the foreign source node.
        let src_buf = crate::printer_util::live_arena_lookup_for(node)
            .unwrap_or_else(|| program.nodes(node.file_index()));
        let src: &[ast::Node] = &src_buf;
        if !crate::printer_util::buffer_resolves_id(src, node)
            || !crate::printer_util::subtree_clonable_in(src, node)
        {
            // The tree was minted into a scratch buffer that no longer
            // exists — Go's heap would still hold it, but there is nothing
            // to clone here. Callers treat `None` as "unchanged".
            return None;
        }
        let grafted = {
            let mut memo = FxHashMap::default();
            self.graft_foreign(nodes, src, node, &mut memo)
        };
        self.f.deep_clone_node(nodes, grafted)
    }

    /// Grafts `id`'s subtree from `src` (a foreign arena) into `nodes`,
    /// remapping all child `NodeId`s — same shape as
    /// `DeclarationTransformer::graft_subtree`. Grafted nodes record the
    /// foreign source as their `original` so `most_original` still reaches
    /// the real declaration.
    fn graft_foreign(
        &mut self,
        nodes: &mut Vec<ast::Node>,
        src: &[ast::Node],
        id: NodeId,
        memo: &mut FxHashMap<NodeId, NodeId>,
    ) -> NodeId {
        if let Some(&g) = memo.get(&id) {
            return g;
        }
        let mut n = src[id].clone();
        let g = NodeId::new(self.f.file_index(), nodes.len() as u64);
        n.id = g;
        n.parent = None;
        nodes.push(n);
        memo.insert(id, g);
        self.e.borrow().set_original_ex(g, id, false);
        let mut data = nodes[g].data.clone();
        data.map_node_ids(&mut |c| {
            if !crate::printer_util::buffer_resolves_id(src, c) {
                return c;
            }
            let gc = self.graft_foreign(nodes, src, c, memo);
            nodes[gc].parent = Some(g);
            gc
        });
        nodes[g].data = data;
        g
    }

    /// `(b *NodeBuilderImpl) cloneBindingName`.
    ///
    /// PORT: Go caches a `cloneBindingNameVisitor` (a `NodeVisitor` whose
    /// visit fn is `cloneBindingName` itself) on the impl; here the visitor's
    /// visit fn cannot capture `&mut self`/`&mut Checker` (the `VisitFn` is
    /// `Fn` + `cx.factory` already borrows `self.f`), so the per-node work is
    /// factored into `clone_binding_name_visit`, and shared state goes
    /// through `RefCell`s (`CloneBindingShared`). For a `node` in another
    /// file's arena, the visit runs on a clone of that arena and the
    /// produced tail is relocated into `nodes` by `relocate_cloned_tail`.
    fn clone_binding_name(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        node: NodeId,
    ) -> NodeId {
        if node.file_index() != self.f.file_index() {
            // `node` lives in another file's arena — graft its subtree
            // into `nodes` (O(subtree); the old path cloned the whole
            // source arena + padded it) and run the visit same-buffer.
            // `arena_view` reads of ungrafted foreign ids resolve through
            // the live-arena registry or program arenas as before.
            let program = c.program.clone().expect("program");
            let src_buf = crate::printer_util::live_arena_lookup_for(node)
                .unwrap_or_else(|| program.nodes(node.file_index()));
            let src: &[ast::Node] = &src_buf;
            if !crate::printer_util::buffer_resolves_id(src, node)
                || !crate::printer_util::subtree_clonable_in(src, node)
            {
                return node;
            }
            let grafted = {
                let mut memo = FxHashMap::default();
                self.graft_foreign(nodes, src, node, &mut memo)
            };
            return self.clone_binding_name_in_arena(c, nodes, grafted);
        }
        self.clone_binding_name_in_arena(c, nodes, node)
    }

    /// The body of Go's `cloneBindingName` running inside `arena` (either
    /// `nodes` or a source-arena clone for foreign subtrees).
    fn clone_binding_name_in_arena(
        &mut self,
        c: &mut Checker,
        arena: &mut Vec<ast::Node>,
        node: NodeId,
    ) -> NodeId {
        // Split borrows for the visit-fn closure: `f` is borrowed by
        // `VisitorCx`; everything else `cloneBindingName` touches goes
        // through `CloneBindingShared`'s cells.
        let c_cell: RefCell<&mut Checker> = RefCell::new(c);
        let shared = CloneBindingShared {
            c: &c_cell,
            tracker: self.ctx.tracker.clone(),
            enclosing_declaration: self.ctx.enclosing_declaration,
            e: self.e.clone(),
        };
        let visitor = ast::visitor::NodeVisitor::new(
            Box::new(
                move |v: &ast::visitor::NodeVisitor,
                      cx: &mut ast::visitor::VisitorCx,
                      n: NodeId|
                      -> Option<NodeId> {
                    Some(clone_binding_name_visit(&shared, v, cx, n))
                },
            ),
            ast::visitor::NodeVisitorHooks::default(),
        );
        let visited = {
            let mut cx = ast::visitor::VisitorCx::new(arena, &mut self.f);
            visitor.visit_each_child(&mut cx, node).unwrap_or(node)
        };
        // `visitor` owns `shared`, which borrows `c_cell` — drop it before
        // `into_inner`.
        drop(visitor);
        let c = c_cell.into_inner();
        let _ = c;

        // Binding elements lose their initializer.
        let visited = if ast::is_binding_element(&arena[visited]) {
            let (dot_dot_dot, property_name, name) = {
                let binding_element = arena[visited].as_binding_element();
                (
                    binding_element.dot_dot_dot_token,
                    binding_element.property_name,
                    binding_element.name,
                )
            };
            self.f
                .update_binding_element(
                    arena,
                    visited,
                    dot_dot_dot,
                    property_name,
                    name,
                    None, // remove initializer
                )
                .unwrap_or(visited)
        } else {
            visited
        };

        let visited = if !ast::node_is_synthesized(&arena[visited]) {
            self.f.deep_clone_node(arena, visited).unwrap_or(visited)
        } else {
            visited
        };

        self.e.borrow().set_emit_flags(
            visited,
            printer::EmitFlags::SINGLE_LINE | printer::EmitFlags::NO_ASCII_ESCAPING,
        );
        visited
    }

    /// Relocate the cloned subtree tail `tmp[tmp_base..]` into `nodes`.
    ///
    /// The clone pass minted ids in `tmp`-space with `src_fi` — the file
    /// index of the arena `tmp` physically is a clone of — so that
    /// `arena_view`-style lookups inside the visit resolve to `tmp`
    /// itself (a node's `file_index` always names the buffer it lives
    /// in). Since `NodeData` has no mutable child-field walker, a second
    /// `visit_each_child` pass rebuilds every node with children
    /// rewritten to dest-space ids, producing a second tail; both tails
    /// are then appended to `nodes` in order so that
    /// `tmp_id.local - tmp_base + dest_base` is the dest position of every
    /// cloned node (pass-2 parents reference the dest ids of pass-2
    /// children — consistent because tails move contiguously).
    pub(crate) fn relocate_cloned_tail(
        &mut self,
        nodes: &mut Vec<ast::Node>,
        tmp: &mut Vec<ast::Node>,
        tmp_base: usize,
        dest_base: usize,
        root: NodeId,
        src_fi: u32,
    ) -> NodeId {
        let dest_file_index = self.f.file_index();
        let remap = move |id: NodeId| -> NodeId {
            if id.is_none()
                || (id.file_index() != src_fi && id.file_index() != dest_file_index)
                || (id.local_index() as usize) < tmp_base
            {
                // Not a scratch-minted id: a real `nodes`/`src` id or a
                // foreign id — all already name their node correctly.
                return id;
            }
            NodeId::new(
                dest_file_index,
                (dest_base + (id.local_index() as usize - tmp_base)) as u64,
            )
        };
        let remap_visitor = ast::visitor::NodeVisitor::new(
            Box::new(
                move |v: &ast::visitor::NodeVisitor,
                      cx: &mut ast::visitor::VisitorCx,
                      n: NodeId|
                      -> Option<NodeId> {
                    if n.file_index() != src_fi && n.file_index() != dest_file_index {
                        // A foreign node embedded in the cloned tree —
                        // `tmp` is the source-arena clone so it reads
                        // correctly; copy it into the tail so the result
                        // tree carries only dest-space ids.
                        let cloned =
                            cx.factory.deep_clone_node(cx.nodes, n).unwrap_or(n);
                        return Some(remap(cloned));
                    }
                    if (n.local_index() as usize) < tmp_base {
                        // A real `src`/`nodes` id (minted before the
                        // scratch tail began) — keep it; indexing `tmp`
                        // already reads the right node.
                        return Some(n);
                    }
                    let visited = v.visit_each_child(cx, n).unwrap_or(n);
                    Some(remap(visited))
                },
            ),
            ast::visitor::NodeVisitorHooks::default(),
        );
        let root_dest = {
            let mut cx = ast::visitor::VisitorCx::new(tmp, &mut self.f);
            // `visit_each_child` on `root` runs the visit fn on each of its
            // children — which recurse — and rebuilds root last; the return
            // is already a dest-space id.
            remap_visitor
                .visit_node(&mut cx, Some(root))
                .unwrap_or_else(|| remap(root))
        };
        // Move the whole tail (both tails — pass-2 nodes are appended after
        // tmp.len() at pass-2 start) into `nodes`, fixing `id` fields.
        // `Node` is not `Clone`, so `drain` moves the elements out by value;
        // for the foreign-arena caller this also restores the source arena
        // to its original length.
        let tail_len = tmp.len() - tmp_base;
        for (i, mut n) in tmp.drain(tmp_base..).enumerate() {
            n.id = NodeId::new(dest_file_index, (dest_base + i) as u64);
            nodes.push(n);
        }
        // Copy emit-table entries minted with tmp-space ids onto dest ids.
        // Pass-1 mints are keyed under `src_fi`, pass-2 mints (made by the
        // remap visitor's factory, which targets the dest arena) under
        // `dest_file_index` — both key spaces land at the same tmp locals.
        for i in 0..tail_len {
            let tmp_local = (tmp_base + i) as u64;
            let dest_id = NodeId::new(dest_file_index, (dest_base + i) as u64);
            // Each scratch slot has one physical node; its emit entries may
            // be keyed under `src_fi` (pass-1 mints) or `dest_file_index`
            // (pass-2 mints from the remap visitor's factory) — read both
            // key spaces but write the dest entries once.
            let src_tmp_id = NodeId::new(src_fi, tmp_local);
            let dest_tmp_id = NodeId::new(dest_file_index, tmp_local);
            let flags = {
                let e = self.e.borrow();
                let f = e.emit_flags(src_tmp_id);
                if f != printer::EmitFlags::NONE {
                    f
                } else {
                    e.emit_flags(dest_tmp_id)
                }
            };
            if flags != printer::EmitFlags::NONE {
                self.e.borrow().set_emit_flags(dest_id, flags);
            }
            // `same_key` — when `dest_base == tmp_base`, a pass-2 mint's
            // dest-keyed entry sits at the very `dest_id` we're writing;
            // remapping the value requires overwriting the entry we read.
            let (original, same_key) = {
                let e = self.e.borrow();
                match e.original(src_tmp_id) {
                    Some(o) => (Some(o), false),
                    None => (e.original(dest_tmp_id), dest_tmp_id == dest_id),
                }
            };
            if let Some(original) = original {
                let remapped_original = if (original.file_index() == src_fi
                    || original.file_index() == dest_file_index)
                    && original.local_index() as usize >= tmp_base
                {
                    // Originals minted during the clone are remapped;
                    // originals pointing into the source arena keep
                    // their source-file ids.
                    NodeId::new(
                        dest_file_index,
                        (dest_base + (original.local_index() as usize - tmp_base)) as u64,
                    )
                } else {
                    original
                };
                self.e
                    .borrow()
                    .set_original_ex(dest_id, remapped_original, same_key);
            }
            for tmp_id in [src_tmp_id, dest_tmp_id] {
                if tmp_id == dest_id {
                    continue;
                }
                if let Some(&symbol) = self.id_to_symbol.get(&tmp_id) {
                    self.id_to_symbol.insert(dest_id, symbol);
                    self.id_to_symbol.remove(&tmp_id);
                }
                // Scratch-minted ids alias the dest file's id space —
                // dispose the tmp entries so they can't be picked up by
                // future real ids minted at the same local index.
                self.e.borrow().dispose_emit_node(tmp_id);
            }
        }
        root_dest
    }

    /// `(b *NodeBuilderImpl) serializeTypeForExpression`.
    pub(crate) fn serialize_type_for_expression(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        expr: NodeId,
    ) -> NodeId {
        // !!! TODO: shim, add node reuse
        let regular = get_regular_type_of_expression(c, expr, nodes);
        let widened = c.get_widened_type(regular);
        let t = c.instantiate_type(widened, self.ctx.mapper);
        self.type_to_type_node(c, nodes, t)
    }

    /// `(b *NodeBuilderImpl) serializeInferredReturnTypeForSignature`.
    fn serialize_inferred_return_type_for_signature(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        signature: SignatureId,
        return_type: TypeId,
    ) -> NodeId {
        let old_suppress_report_inference_fallback = self.ctx.suppress_report_inference_fallback;
        self.ctx.suppress_report_inference_fallback = true;
        let type_predicate = c.get_type_predicate_of_signature(signature);
        let return_type_node = if let Some(type_predicate) = type_predicate {
            let predicate = if let Some(mapper) = self.ctx.mapper {
                c.instantiate_type_predicate(&type_predicate, Some(mapper))
            } else {
                type_predicate
            };
            self.type_predicate_to_type_predicate_node_helper(c, nodes, &predicate)
        } else {
            self.type_to_type_node(c, nodes, return_type)
        };
        self.ctx.suppress_report_inference_fallback = old_suppress_report_inference_fallback;
        return_type_node
    }

    /// `(b *NodeBuilderImpl) typePredicateToTypePredicateNodeHelper`.
    fn type_predicate_to_type_predicate_node_helper(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        type_predicate: &TypePredicate,
    ) -> NodeId {
        let asserts_modifier = if type_predicate.kind == TypePredicateKind::AssertsThis
            || type_predicate.kind == TypePredicateKind::AssertsIdentifier
        {
            Some(self.f.new_token(nodes, Kind::AssertsKeyword))
        } else {
            None
        };
        let parameter_name = if type_predicate.kind == TypePredicateKind::Identifier
            || type_predicate.kind == TypePredicateKind::AssertsIdentifier
        {
            let parameter_name = self.new_identifier(nodes, &type_predicate.parameter_name, None);
            self.e
                .borrow()
                .set_emit_flags(parameter_name, printer::EmitFlags::NO_ASCII_ESCAPING);
            parameter_name
        } else {
            self.f.new_this_type_node(nodes)
        };
        let type_node = type_predicate
            .t
            .map(|t| self.type_to_type_node(c, nodes, t));
        self.f
            .new_type_predicate_node(nodes, asserts_modifier, Some(parameter_name), type_node)
    }

    /// `(b *NodeBuilderImpl) signatureToSignatureDeclarationHelper`.
    pub fn signature_to_signature_declaration_helper(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        signature: SignatureId,
        kind: Kind,
        options: SignatureToSignatureDeclarationOptions,
    ) -> NodeId {
        let mut type_parameters: Vec<NodeId> = Vec::new();

        let (expanded_params, cleanup) = self.enter_signature_scope(c, nodes, signature);
        self.ctx.approximate_length += 3;
        // Usually a signature contributes a few more characters than this,
        // but 3 is the minimum.

        let (sig_target, sig_mapper, sig_type_parameters, sig_parameters, sig_flags) = {
            let sig = c.signature_arena.get(signature);
            (
                sig.target,
                sig.mapper,
                sig.type_parameters.clone(),
                sig.parameters.clone(),
                sig.flags,
            )
        };
        if self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::WRITE_TYPE_ARGUMENTS_OF_SIGNATURE)
            && sig_target.is_some()
            && sig_mapper.is_some()
            && !c
                .signature_arena
                .get(sig_target.unwrap())
                .type_parameters
                .is_empty()
        {
            let target_params = c
                .signature_arena
                .get(sig_target.unwrap())
                .type_parameters
                .clone();
            for parameter in target_params.iter().copied() {
                let instantiated = c.instantiate_type(parameter, sig_mapper);
                type_parameters.push(self.type_to_type_node(c, nodes, instantiated));
            }
        } else {
            for parameter in sig_type_parameters.iter().copied() {
                type_parameters.push(self.type_parameter_to_declaration(c, nodes, parameter));
            }
        }

        let restore_flags = self.save_restore_flags();
        self.ctx
            .flags
            .remove(nodebuilder::Flags::SUPPRESS_ANY_RETURN_TYPE);
        // If the expanded parameter list had a variadic in a non-trailing
        // position, don't expand it.
        let use_original_params = expanded_params.iter().any(|p| {
            p.is_some()
                && *p != expanded_params.last().copied().flatten()
                && symbol_check_flags(c, p.unwrap())
                    .intersects(ast::checkflags::CheckFlags::REST_PARAMETER)
        });
        let params_source: Vec<Option<SymbolId>> = if use_original_params {
            sig_parameters.iter().map(|p| Some(*p)).collect()
        } else {
            expanded_params
        };
        let mut parameters: Vec<NodeId> = params_source
            .iter()
            .map(|parameter| {
                parameter.map(|p| {
                    self.symbol_to_parameter_declaration(c, nodes, p, kind == Kind::Constructor)
                })
            })
            .collect::<Vec<_>>()
            .into_iter()
            .flatten()
            .collect();
        let this_parameter = if self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::OMIT_THIS_PARAMETER)
        {
            None
        } else {
            self.try_get_this_parameter_declaration(c, nodes, signature)
        };
        if let Some(this_parameter) = this_parameter {
            parameters.insert(0, this_parameter);
        }
        restore_flags.restore(&mut self.ctx);

        let mut return_type_node =
            self.serialize_return_type_for_signature(c, nodes, signature, true);

        let mut modifiers = options.modifiers.clone();
        if kind == Kind::ConstructorType && sig_flags.intersects(SignatureFlags::ABSTRACT) {
            let flags = ast::modifiers_to_flags(&modifiers, nodes);
            modifiers = ast::create_modifiers_from_modifier_flags(
                flags | ast::ModifierFlags::ABSTRACT,
                &mut |kind: Kind| self.f.new_token(nodes, kind),
            );
        }

        let param_list = self.f.new_node_list(parameters);
        let type_param_list = if type_parameters.is_empty() {
            None
        } else {
            Some(self.f.new_node_list(type_parameters))
        };
        let modifier_list = if modifiers.is_empty() {
            None
        } else {
            Some(self.f.new_modifier_list(nodes, modifiers))
        };
        let name = options
            .name
            .unwrap_or_else(|| self.f.new_identifier(nodes, ""));

        let node = match kind {
            Kind::CallSignature => self.f.new_call_signature_declaration(
                nodes,
                type_param_list,
                Some(param_list),
                return_type_node,
            ),
            Kind::ConstructSignature => self.f.new_construct_signature_declaration(
                nodes,
                type_param_list,
                Some(param_list),
                return_type_node,
            ),
            Kind::MethodSignature => self.f.new_method_signature_declaration(
                nodes,
                modifier_list,
                Some(name),
                options.question_token,
                type_param_list,
                Some(param_list),
                return_type_node,
            ),
            Kind::MethodDeclaration => self.f.new_method_declaration(
                nodes,
                modifier_list,
                None, // asteriskToken
                Some(name),
                None, // questionToken
                type_param_list,
                Some(param_list),
                return_type_node,
                None, // fullSignature
                None, // body
            ),
            Kind::Constructor => self.f.new_constructor_declaration(
                nodes,
                modifier_list,
                None, // typeParamList
                Some(param_list),
                None, // returnTypeNode
                None, // fullSignature
                None, // body
            ),
            Kind::GetAccessor => self.f.new_get_accessor_declaration(
                nodes,
                modifier_list,
                Some(name),
                None, // typeParamList
                Some(param_list),
                return_type_node,
                None, // fullSignature
                None, // body
            ),
            Kind::SetAccessor => self.f.new_set_accessor_declaration(
                nodes,
                modifier_list,
                Some(name),
                None, // typeParamList
                Some(param_list),
                None, // returnTypeNode
                None, // fullSignature
                None, // body
            ),
            Kind::IndexSignature => self.f.new_index_signature_declaration(
                nodes,
                modifier_list,
                Some(param_list),
                return_type_node,
            ),
            // !!! JSDoc Support
            // Kind::JSDocFunctionType => ...
            Kind::FunctionType => {
                if return_type_node.is_none() {
                    let empty_name = self.f.new_identifier(nodes, "");
                    return_type_node = Some(self.f.new_type_reference_node(
                        nodes,
                        Some(empty_name),
                        None,
                    ));
                }
                self.f.new_function_type_node(
                    nodes,
                    type_param_list,
                    Some(param_list),
                    return_type_node,
                )
            }
            Kind::ConstructorType => {
                if return_type_node.is_none() {
                    let empty_name = self.f.new_identifier(nodes, "");
                    return_type_node = Some(self.f.new_type_reference_node(
                        nodes,
                        Some(empty_name),
                        None,
                    ));
                }
                self.f.new_constructor_type_node(
                    nodes,
                    modifier_list,
                    type_param_list,
                    Some(param_list),
                    return_type_node,
                )
            }
            Kind::FunctionDeclaration => self.f.new_function_declaration(
                nodes,
                modifier_list,
                None, // asteriskToken
                Some(name),
                type_param_list,
                Some(param_list),
                return_type_node,
                None, // fullSignature
                None, // body
            ),
            Kind::FunctionExpression => {
                let body = self
                    .f
                    .new_block(nodes, Some(self.f.new_node_list(Vec::new())), false);
                self.f.new_function_expression(
                    nodes,
                    modifier_list,
                    None, // asteriskToken
                    Some(name),
                    type_param_list,
                    Some(param_list),
                    return_type_node,
                    None, // fullSignature
                    Some(body),
                )
            }
            Kind::ArrowFunction => {
                let body = self
                    .f
                    .new_block(nodes, Some(self.f.new_node_list(Vec::new())), false);
                self.f.new_arrow_function(
                    nodes,
                    modifier_list,
                    type_param_list,
                    Some(param_list),
                    return_type_node,
                    None, // fullSignature
                    None, // equalsGreaterThanToken
                    Some(body),
                )
            }
            _ => panic!("Unhandled kind in signatureToSignatureDeclarationHelper"),
        };

        // !!! TODO: Smuggle type arguments of signatures out for quickinfo

        cleanup.restore(self, nodes);
        node
    }

    /// `(b *NodeBuilderImpl) tryGetThisParameterDeclaration`.
    fn try_get_this_parameter_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        signature: SignatureId,
    ) -> Option<NodeId> {
        let (this_parameter, declaration) = {
            let sig = c.signature_arena.get(signature);
            (sig.this_parameter, sig.declaration)
        };
        if let Some(this_parameter) = this_parameter {
            return Some(self.symbol_to_parameter_declaration(c, nodes, this_parameter, false));
        }
        if let Some(declaration) = declaration {
            let __program = c.program.clone().expect("program");
            let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
            if ast::is_in_js_file(Some(declaration), &decl_nodes) {
                // !!! JSDoc Support — Go leaves this commented out as well.
            }
        }
        None
    }

    /// `(b *NodeBuilderImpl) serializeReturnTypeForSignature`.
    ///
    /// Serializes the return type of the signature by first trying to use the
    /// syntactic printer if possible and falling back to the checker type if
    /// not.
    pub(crate) fn serialize_return_type_for_signature(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        signature: SignatureId,
        try_reuse: bool,
    ) -> Option<NodeId> {
        let suppress_any = self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::SUPPRESS_ANY_RETURN_TYPE);
        let restore_flags = self.save_restore_flags();
        if suppress_any {
            self.ctx
                .flags
                .remove(nodebuilder::Flags::SUPPRESS_ANY_RETURN_TYPE); // suppress only toplevel `any`s
        }
        let mut return_type_node: Option<NodeId> = None;

        let sig_declaration = c.signature_arena.get(signature).declaration;
        let return_type;
        if let Some(declaration) = sig_declaration {
            let __program = c.program.clone().expect("program");
            let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
            if !ast::node_is_synthesized(&decl_nodes[declaration]) {
                let symbol = c.get_symbol_of_declaration(declaration);
                return_type =
                    match symbol.and_then(|s| self.ctx.enclosing_symbol_types.get(&s).copied()) {
                        Some(t) => t,
                        None => {
                            let rt = c.get_return_type_of_signature(signature);
                            c.instantiate_type(rt, self.ctx.mapper)
                        }
                    };
            } else {
                return_type = c.get_return_type_of_signature(signature);
            }
        } else {
            return_type = c.get_return_type_of_signature(signature);
        }
        if !(suppress_any && crate::types::is_type_any(&c.types, return_type)) {
            if !self.is_actively_expanding()
                && try_reuse
                && self.ctx.enclosing_declaration.is_some()
                && let Some(declaration) = sig_declaration
            {
                let decl_nodes_is_synth = {
                    let __program = c.program.clone().expect("program");
                    let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
                    ast::node_is_synthesized(&decl_nodes[declaration])
                };
                if !decl_nodes_is_synth {
                    let declaration_symbol = c.get_symbol_of_declaration(declaration);
                    let restore =
                        declaration_symbol.map(|s| self.add_symbol_type_to_context(s, return_type));
                    let pt = {
                        let __program = c.program.clone().expect("program");
                        let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
                        let symbols = c.symbol_arena.clone();
                        self.pc
                            .get_return_type_of_signature(declaration, &decl_nodes, &symbols)
                    };
                    if self.pseudo_type_equivalent_to_type(
                        c,
                        nodes,
                        &pt,
                        return_type,
                        false,
                        !self.ctx.suppress_report_inference_fallback,
                    ) {
                        // Also verify the pseudo type captures any inferred
                        // type predicate, not just the boolean return type.
                        // The pseudochecker is unaware of inferred type
                        // predicates, so it produces boolean where the checker
                        // infers e.g. `x is string`.
                        let type_predicate = c.get_type_predicate_of_signature(signature);
                        let mut pt = Some(pt);
                        if let Some(type_predicate) = type_predicate.as_ref() {
                            if !self.pseudo_return_type_matches_predicate(
                                c,
                                pt.as_ref().unwrap(),
                                type_predicate, nodes) {
                                if !self.ctx.suppress_report_inference_fallback
                                    && let Some(tracker) = self.ctx.tracker.clone()
                                {
                                    tracker
                                        .borrow_mut()
                                        .report_inference_fallback(declaration, nodes);
                                }
                                pt = None;
                            }
                        }
                        if let Some(pt) = pt {
                            // !!! TODO: If annotated type node is a reference
                            // with insufficient type arguments, we should still
                            // fall back to type serialization — see
                            // canReuseTypeNodeAnnotation in strada for context.
                            return_type_node = self.pseudo_type_to_node_with_checker_fallback(
                                c,
                                nodes,
                                pt,
                                Some(return_type),
                            );
                        }
                    }
                    if let Some(restore) = restore {
                        restore(&mut self.ctx);
                    }
                }
            }
            if return_type_node.is_none() {
                return_type_node = Some(self.serialize_inferred_return_type_for_signature(
                    c,
                    nodes,
                    signature,
                    return_type,
                ));
            }
        }

        if return_type_node.is_none() && !suppress_any {
            return_type_node = Some(self.f.new_keyword_type_node(nodes, Kind::AnyKeyword));
        }
        restore_flags.restore(&mut self.ctx);
        return_type_node
    }

    /// `(b *NodeBuilderImpl) isTriviallySerializableComputedName`.
    fn is_trivially_serializable_computed_name(&mut self, c: &mut Checker, e: NodeId,
        nodes: &[ast::Node],) -> bool {
        let __program = c.program.clone().expect("program");
        let e_nodes = crate::printer_util::arena_view(&__program, nodes, (e).file_index());
        let shape_good = e_nodes[e].name().is_some_and(|name| {
            ast::is_computed_property_name(&e_nodes[name])
                && e_nodes[name]
                    .expression()
                    .is_some_and(|expr| ast::is_entity_name_expression(&e_nodes[expr], &e_nodes))
        });
        if !shape_good {
            return false;
        }
        let name = e_nodes[e].name().unwrap();
        let expr = e_nodes[name].expression().unwrap();
        c.is_entity_name_visible(expr, self.ctx.enclosing_declaration, false, Some(&*nodes))
            .accessibility
            == printer::SymbolAccessibility::Accessible
    }

    /// `(b *NodeBuilderImpl) indexInfoToObjectComputedNamesOrSignatureDeclaration`.
    fn index_info_to_object_computed_names_or_signature_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        index_info: &IndexInfo,
        type_node: Option<NodeId>,
    ) -> Vec<NodeId> {
        if !index_info.components.is_empty() {
            // Index info is derived from object or class computed property
            // names (plus explicit named members) — we can clone those
            // instead of writing out the result computed index signature.
            let all_component_computed_names_serializable =
                self.ctx.enclosing_declaration.is_some()
                    && index_info
                        .components
                        .iter()
                        .all(|&e| self.is_trivially_serializable_computed_name(c, e, nodes));
            if all_component_computed_names_serializable {
                // Only use computed name serialization form if all components
                // are visible and take the `a.b.c` form.
                let new_components: Vec<NodeId> = index_info
                    .components
                    .iter()
                    .copied()
                    .filter(|&e| !c.has_late_bindable_name(e))
                    .collect();
                let mut bailed = false;
                let mut results: Vec<NodeId> = Vec::new();
                for e in new_components {
                    let __program = c.program.clone().expect("program");
                    let e_nodes = crate::printer_util::arena_view(&__program, nodes, (e).file_index());
                    let e_name = e_nodes[e].name();
                    let name = e_name.and_then(|n| self.reuse_node(c, nodes, n));
                    if let Some(name) = name {
                        // Still need to track visibility even if we've
                        // already checked it to paint references as used.
                        let expr = {
                            let __program = c.program.clone().expect("program");
                            let e_nodes = crate::printer_util::arena_view(&__program, nodes, (e).file_index());
                            e_nodes[e_nodes[e].name().unwrap()].expression()
                        };
                        if let Some(expr) = expr {
                            let enclosing = self.ctx.enclosing_declaration;
                            self.track_computed_name(c, nodes, expr, enclosing);
                        }
                        let mods = if index_info.is_readonly {
                            let readonly = self.f.new_token(nodes, Kind::ReadonlyKeyword);
                            Some(self.f.new_modifier_list(nodes, [readonly]))
                        } else {
                            None
                        };
                        let postfix_token = {
                            let __program = c.program.clone().expect("program");
                            let e_nodes = crate::printer_util::arena_view(&__program, nodes, (e).file_index());
                            e_nodes[e]
                                .postfix_token()
                                .map(|p| self.deep_clone_node_in(c, nodes, p).unwrap_or(p))
                        };
                        // PORT: Go `PostfixToken().Clone(b.f)` clones in the
                        // source arena; deep_clone_node in the destination
                        // arena requires the token to be arena-local — for
                        // foreign tokens this falls back to a fresh token of
                        // the same kind.
                        let current_type_node = if let Some(type_node) = type_node {
                            self.deep_clone_node_in(c, nodes, type_node)
                                .unwrap_or(type_node)
                        } else {
                            let e_symbol = {
                                let __program = c.program.clone().expect("program");
                                let e_nodes = crate::printer_util::arena_view(&__program, nodes, (e).file_index());
                                e_nodes[e].symbol()
                            };
                            let t = c.get_type_of_symbol(e_symbol.unwrap_or(SymbolId::NONE));
                            self.type_to_type_node(c, nodes, t)
                        };
                        let sig = self.f.new_property_signature_declaration(
                            nodes,
                            mods,
                            Some(name),
                            postfix_token,
                            Some(current_type_node),
                            None,
                        );
                        // `sig.Loc = e.Loc` — copy the text range.
                        nodes[sig].loc = c.program_nodes_live(e, nodes)[e].loc;
                        results.push(sig);
                    } else {
                        bailed = true;
                    }
                }
                if !bailed {
                    return results;
                }
            }
        }
        vec![self.index_info_to_index_signature_declaration_helper(c, nodes, index_info, type_node)]
    }

    /// `(b *NodeBuilderImpl) indexInfoToIndexSignatureDeclarationHelper`.
    pub(crate) fn index_info_to_index_signature_declaration_helper(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        index_info: &IndexInfo,
        mut type_node: Option<NodeId>,
    ) -> NodeId {
        let name = get_name_from_index_info_data(c, index_info, nodes);
        let key_type = index_info.key_type.unwrap_or(c.error_type);
        let indexer_type_node = self.type_to_type_node(c, nodes, key_type);

        let index_name = self.new_identifier(nodes, &name, None);
        let indexing_parameter = self.f.new_parameter_declaration(
            nodes,
            None,
            None,
            Some(index_name),
            None,
            Some(indexer_type_node),
            None,
        );
        if type_node.is_none() {
            if index_info.value_type.is_none() {
                type_node = Some(self.f.new_keyword_type_node(nodes, Kind::AnyKeyword));
            } else {
                let vt = index_info.value_type.unwrap();
                let tn = self.type_to_type_node(c, nodes, vt);
                type_node = Some(tn);
            }
        }
        if index_info.value_type.is_none()
            && !self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::ALLOW_EMPTY_INDEX_INFO_TYPE)
        {
            self.ctx.encountered_error = true;
        }
        self.ctx.approximate_length += name.len() as i32 + 4;
        let modifiers = if index_info.is_readonly {
            self.ctx.approximate_length += 9;
            let readonly = self.f.new_token(nodes, Kind::ReadonlyKeyword);
            Some(self.f.new_modifier_list(nodes, [readonly]))
        } else {
            None
        };
        let param_list = self.f.new_node_list([indexing_parameter]);
        self.f
            .new_index_signature_declaration(nodes, modifiers, Some(param_list), type_node)
    }

    /// `(b *NodeBuilderImpl) serializeTypeForDeclaration`.
    ///
    /// Unlike `typeToTypeNodeHelper`, this handles setting up the
    /// `AllowUniqueESSymbolType` flag so a `unique symbol` is returned when
    /// appropriate for the input symbol, rather than `typeof sym`.
    ///
    /// * `declaration` — The preferred declaration to pull existing type
    ///   nodes from (the symbol will be used as a fallback to find any
    ///   annotated declaration)
    /// * `t` — The type to write; an existing annotation must match this
    ///   type if it's used, otherwise this is the type serialized as a new
    ///   type node
    /// * `symbol` — The symbol is used both to find an existing annotation if
    ///   declaration is not provided, and to determine if `unique symbol`
    ///   should be printed
    pub fn serialize_type_for_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        declaration: Option<NodeId>,
        t: Option<TypeId>,
        symbol: Option<SymbolId>,
        try_reuse: bool,
    ) -> NodeId {
        let mut declaration = declaration;
        if declaration.is_none()
            && let Some(symbol) = symbol
        {
            declaration = symbol_value_declaration(c, symbol);
            if declaration.is_none() {
                // TODO: prefer annotated declarations like in strada (but
                // does this ever even matter in practice? All callers should
                // supply a declaration!)
                declaration = symbol_declarations(c, symbol).first().copied();
            }
        }
        let mut symbol = symbol;
        if symbol.is_none()
            && let Some(declaration) = declaration
        {
            symbol = c.get_symbol_of_declaration(declaration);
        }
        let mut t = t;
        if t.is_none() {
            if symbol.is_none() {
                if let Some(declaration) = declaration {
                    let __program = c.program.clone().expect("program");
                    let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
                    if ast::is_variable_like(&decl_nodes[declaration]) {
                        t = c.get_type_for_variable_like_declaration(
                            declaration,
                            false,
                            crate::checker_core::CheckMode::NORMAL,
                        );
                    } else {
                        t = Some(c.error_type);
                    }
                } else {
                    t = Some(c.error_type);
                }
            } else {
                let sym = symbol.unwrap();
                t = self.ctx.enclosing_symbol_types.get(&sym).copied();
                if t.is_none() {
                    let decl_kind = declaration.map(|d| c.program_nodes_live(d, nodes)[d].kind);
                    if symbol_flags(c, sym).intersects(SymbolFlags::ACCESSOR)
                        && decl_kind == Some(Kind::SetAccessor)
                    {
                        let wt = c.get_write_type_of_symbol(sym);
                        t = Some(c.instantiate_type(wt, self.ctx.mapper));
                    } else if !symbol_flags(c, sym)
                        .intersects(SymbolFlags::TYPE_LITERAL | SymbolFlags::SIGNATURE)
                    {
                        let tos = c.get_type_of_symbol(sym);
                        let wt = c.get_widened_literal_type(tos);
                        t = Some(c.instantiate_type(wt, self.ctx.mapper));
                    } else {
                        t = Some(c.error_type);
                    }
                }
            }
        }
        let t = t.unwrap_or(c.error_type);

        let requires_adding_undefined = declaration.is_some_and(|d| {
            let __program = c.program.clone().expect("program");
            let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
            (ast::is_parameter_declaration(&decl_nodes[d])
                || ast::is_property_signature_declaration(&decl_nodes[d])
                || ast::is_property_declaration(&decl_nodes[d]))
                && c.requires_adding_implicit_undefined(d, symbol, self.ctx.enclosing_declaration)
        });
        let add_undefined_for_parameter = requires_adding_undefined
            && declaration.is_some_and(|d| {
                let __program = c.program.clone().expect("program");
                let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
                ast::is_parameter_declaration(&decl_nodes[d])
            });
        let t = if add_undefined_for_parameter {
            c.get_optional_type(t, false)
        } else {
            t
        };

        let restore_flags = self.save_restore_flags();
        let t_flags = type_flags(c, t);
        let t_symbol = type_symbol(c, t);
        if t_flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL)
            && t_symbol == symbol
            && (self.ctx.enclosing_declaration.is_none()
                || symbol.is_some_and(|sym| {
                    symbol_declarations(c, sym).iter().any(|&d| {
                        let __program = c.program.clone().expect("program");
                        let d_nodes = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
                        ast::get_source_file_of_node(Some(d), &d_nodes) == self.ctx.enclosing_file
                    })
                }))
        {
            self.ctx.flags |= nodebuilder::Flags::ALLOW_UNIQUE_ES_SYMBOL_TYPE;
        }
        let mut result: Option<NodeId> = None;
        let mut reported_inference_fallback = false;
        // !!! expandable hover support
        if !self.is_actively_expanding()
            && try_reuse
            && self.ctx.enclosing_declaration.is_some()
            && declaration.is_some()
        {
            let declaration = declaration.unwrap();
            let __program = c.program.clone().expect("program");
            let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
            let is_accessor_decl = ast::is_accessor(&decl_nodes[declaration]);
            if is_accessor_decl
                || (ast::has_inferred_type(&decl_nodes[declaration])
                    && !ast::node_is_synthesized(&decl_nodes[declaration])
                    && !type_object_flags(c, t).intersects(ObjectFlags::REQUIRES_WIDENING))
            {
                let remove = symbol.map(|s| self.add_symbol_type_to_context(s, t));
                let __program = c.program.clone().expect("program");
                let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
                let symbols = c.symbol_arena.clone();
                let mut pt = if is_accessor_decl {
                    self.pc
                        .get_type_of_accessor(declaration, &decl_nodes, &symbols)
                } else {
                    self.pc
                        .get_type_of_declaration(declaration, &decl_nodes, &symbols)
                };
                drop(symbols);
                if pt.kind() == PseudoTypeKind::NoResult
                    && ast::is_binary_expression(&decl_nodes[declaration])
                    && symbol.is_some()
                    && let Some(annotated_decl) = symbol_declarations(c, symbol.unwrap())
                        .iter()
                        .copied()
                        .find(|&d| {
                            let __program = c.program.clone().expect("program");
                            let dn = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
                            has_type_annotation(d, &dn)
                        })
                {
                    // Binary expressions have a first-in-wins type annotation
                    // system. The first one with an annotation supplies the
                    // type for the rest.
                    let __program = c.program.clone().expect("program");
                    let dn = crate::printer_util::arena_view(&__program, nodes, (annotated_decl).file_index());
                    let symbols = c.symbol_arena.clone();
                    pt = self
                        .pc
                        .get_type_of_declaration(annotated_decl, &dn, &symbols);
                }
                let report_errors = !self.ctx.suppress_report_inference_fallback;
                let is_optional_annotated = !requires_adding_undefined && {
                    let __program = c.program.clone().expect("program");
                    let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
                    let decl = &decl_nodes[declaration];
                    (ast::is_parameter_declaration(decl)
                        || ast::is_property_signature_declaration(decl)
                        || ast::is_property_declaration(decl))
                        && crate::utilities::is_optional_declaration(decl, &decl_nodes)
                };
                drop(decl_nodes);
                if self.pseudo_type_equivalent_to_type(
                    c,
                    nodes,
                    &pt,
                    t,
                    is_optional_annotated,
                    report_errors,
                ) {
                    // !!! TODO: If annotated type node is a reference with
                    // insufficient type arguments, we should still fall back
                    // to type serialization — see canReuseTypeNodeAnnotation
                    // in strada for context.
                    let mut pt = pt;
                    if let Some(ptt) = self.pseudo_type_to_type(c, &pt)
                        && requires_adding_undefined
                        && contains_non_missing_undefined_type(c, t)
                        && !contains_non_missing_undefined_type(c, ptt)
                    {
                        pt = pseudochecker::new_pseudo_type_union(vec![
                            pt,
                            pseudochecker::pseudo_type_undefined(),
                        ]);
                    }
                    result = self.pseudo_type_to_node_with_checker_fallback(c, nodes, pt, Some(t));
                } else {
                    // Equivalence failed; if errors from inferred-with-errors
                    // pseudo types were reported, note it so we can suppress
                    // nested errors during the fallback `typeToTypeNode`
                    // serialization (mirroring the suppression that
                    // `pseudoTypeToNodeWithCheckerFallback` provides).
                    reported_inference_fallback = report_errors
                        && pt.kind() == PseudoTypeKind::Inferred
                        && !pt.as_pseudo_type_inferred().error_nodes.is_empty();
                    let mut should_add_undefined = false;
                    if requires_adding_undefined {
                        if let Some(ptt) = self.pseudo_type_to_type(c, &pt) {
                            should_add_undefined = !contains_non_missing_undefined_type(c, ptt);
                        } else {
                            let __program = c.program.clone().expect("program");
                            let decl_nodes = crate::printer_util::arena_view(
                                &__program,
                                nodes,
                                (declaration).file_index(),
                            );
                            should_add_undefined =
                                !pseudochecker::could_already_refer_to_undefined_type(
                                    &pt,
                                    &decl_nodes,
                                );
                        }
                    }
                    if should_add_undefined {
                        let pt = pseudochecker::new_pseudo_type_union(vec![
                            pt,
                            pseudochecker::pseudo_type_undefined(),
                        ]);
                        if self.pseudo_type_equivalent_to_type(
                            c,
                            nodes,
                            &pt,
                            t,
                            false,
                            report_errors,
                        ) {
                            result = self.pseudo_type_to_node_with_checker_fallback(
                                c,
                                nodes,
                                pt,
                                Some(t),
                            );
                            reported_inference_fallback = false;
                        }
                    }
                }
                if let Some(remove) = remove {
                    remove(&mut self.ctx);
                }
            }
        }
        if result.is_none() {
            if reported_inference_fallback {
                let old_suppress = self.ctx.suppress_report_inference_fallback;
                self.ctx.suppress_report_inference_fallback = true;
                result = Some(self.type_to_type_node(c, nodes, t));
                self.ctx.suppress_report_inference_fallback = old_suppress;
            } else {
                result = Some(self.type_to_type_node(c, nodes, t));
            }
        }
        restore_flags.restore(&mut self.ctx);
        result.unwrap_or_else(|| self.f.new_keyword_type_node(nodes, Kind::AnyKeyword))
    }

    /// `(b *NodeBuilderImpl) shouldUsePlaceholderForProperty`.
    pub fn should_use_placeholder_for_property(
        &mut self,
        c: &mut Checker,
        property_symbol: SymbolId,
    ) -> bool {
        // Reverse mapped type placeholders are for display, not declaration
        // emit.
        if !self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::ALLOW_ANONYMOUS_IDENTIFIER)
        {
            return false;
        }
        // Use placeholders for reverse mapped types we've either
        // (1) already descended into, or
        // (2) are nested reverse mappings within a mapping over a
        //     non-anonymous type, or
        // (3) are deeply nested properties that originate from the same
        //     mapped type.
        // Condition (2) is a restriction mostly just to reduce the blowup in
        // printback size from doing, e.g., a deep reverse mapping over
        // `Window`. Since anonymous types usually come from expressions,
        // this allows us to preserve the output for deep mappings which
        // likely come from expressions, while truncating those parts which
        // come from mappings over library functions.
        // Condition (3) limits printing of possibly infinitely deep reverse
        // mapped types.
        if !symbol_check_flags(c, property_symbol)
            .intersects(ast::checkflags::CheckFlags::REVERSE_MAPPED)
        {
            return false;
        }
        // (1)
        if self.ctx.reverse_mapped_stack.contains(&property_symbol) {
            return true;
        }
        // (2)
        if let Some(&last) = self.ctx.reverse_mapped_stack.last()
            && c.reverse_mapped_symbol_links.has(&last)
        {
            let property_type = c
                .reverse_mapped_symbol_links
                .try_get(&last)
                .unwrap()
                .property_type;
            if property_type
                .is_some_and(|pt| !type_object_flags(c, pt).intersects(ObjectFlags::ANONYMOUS))
            {
                return true;
            }
        }
        // (3) — we only inspect the last
        // MAX_REVERSE_MAPPED_NESTING_INSPECTION_DEPTH elements of the stack
        // for approximate matches to catch tight infinite loops.
        // TODO: Why? Reasoning lost to time. this could probably stand to be
        // improved?
        if self.ctx.reverse_mapped_stack.len() < Self::MAX_REVERSE_MAPPED_NESTING_INSPECTION_DEPTH {
            return false;
        }
        if !c.reverse_mapped_symbol_links.has(&property_symbol) {
            return false;
        }
        let prop_mapped_type = c
            .reverse_mapped_symbol_links
            .try_get(&property_symbol)
            .unwrap()
            .mapped_type;
        let prop_mapped_symbol = prop_mapped_type.and_then(|m| type_symbol(c, m));
        let Some(prop_mapped_symbol) = prop_mapped_symbol else {
            return false;
        };
        for i in 0..self.ctx.reverse_mapped_stack.len() {
            if i > Self::MAX_REVERSE_MAPPED_NESTING_INSPECTION_DEPTH {
                break;
            }
            let prop = self.ctx.reverse_mapped_stack[self.ctx.reverse_mapped_stack.len() - 1 - i];
            if c.reverse_mapped_symbol_links.has(&prop) {
                let mapped_type = c
                    .reverse_mapped_symbol_links
                    .try_get(&prop)
                    .unwrap()
                    .mapped_type;
                if mapped_type.is_some_and(|m| type_symbol(c, m) == Some(prop_mapped_symbol)) {
                    return true;
                }
            }
        }
        false
    }

    /// `(b *NodeBuilderImpl) trackComputedName` — direct-call form; the
    /// cloneBindingName visit-fn path goes through
    /// `track_computed_name_shared`.
    pub fn track_computed_name(
        &mut self,
        c: &mut Checker,
        nodes: &[ast::Node],
        access_expression: NodeId,
        enclosing_declaration: Option<NodeId>,
    ) {
        // get symbol of the first identifier of the entityName
        let __program = c.program.clone().expect("program");
        let expr_nodes = crate::printer_util::arena_view(&__program, nodes, (access_expression).file_index());
        let first_identifier = ast::get_first_identifier(access_expression, &expr_nodes);
        let text = expr_nodes[first_identifier].text(&expr_nodes).into_owned();
        let name = c.resolve_name_via_binder_live(
            enclosing_declaration,
            &text,
            SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
            None,
            true, // isUse
            false,
            Some(nodes),
        );
        let tracked = if let Some(name) = name {
            Some(name)
        } else {
            // Name does not resolve at target location, track symbol at dest
            // location (should be inaccessible).
            c.resolve_name_via_binder_live(
                Some(first_identifier),
                &text,
                SymbolFlags::VALUE | SymbolFlags::EXPORT_VALUE,
                None,
                true,
                false,
                Some(nodes),
            )
        };
        if let Some(tracked) = tracked
            && let Some(tracker) = self.ctx.tracker.clone()
        {
            let nodes_view: &[ast::Node] = nodes;
            tracker.borrow_mut().track_symbol(
                tracked,
                enclosing_declaration,
                SymbolFlags::VALUE,
                nodes_view,
                &mut |sym, en, mn, sc| {
                    c.is_symbol_accessible(sym, en, mn, sc, Some(nodes_view))
                },
            );
        }
    }

    /// `(b *NodeBuilderImpl) createPropertyNameNodeForIdentifierOrLiteral`.
    fn create_property_name_node_for_identifier_or_literal(
        &mut self,
        _c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        name: &str,
        single_quote: bool,
        string_named: bool,
        is_method: bool,
        symbol: Option<SymbolId>,
    ) -> NodeId {
        match classify_property_name(name, string_named, is_method) {
            PropertyNameNodeKind::Identifier => self.new_identifier(nodes, name, symbol),
            PropertyNameNodeKind::NumericLiteral => {
                self.f
                    .new_numeric_literal(nodes, name, ast::TokenFlags::NONE)
            }
            PropertyNameNodeKind::StringLiteral => self.f.new_string_literal(
                nodes,
                name,
                if single_quote {
                    ast::TokenFlags::SINGLE_QUOTE
                } else {
                    ast::TokenFlags::NONE
                },
            ),
        }
    }

    /// `(b *NodeBuilderImpl) isStringNamed`.
    fn is_string_named(&mut self, c: &mut Checker, d: NodeId,
        nodes: &[ast::Node],) -> bool {
        let __program = c.program.clone().expect("program");
        let d_nodes = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
        let Some(name) = ast::get_name_of_declaration(Some(d), &d_nodes) else {
            return false;
        };
        if ast::is_computed_property_name(&d_nodes[name]) {
            let expr = d_nodes[name].expression();
            let Some(expr) = expr else { return false };
            let t = c.check_expression(expr);
            return type_flags(c, t).intersects(TypeFlags::STRING_LIKE);
        }
        if ast::is_element_access_expression(&d_nodes[name]) {
            let arg = d_nodes[name]
                .as_element_access_expression()
                .argument_expression;
            let Some(arg) = arg else { return false };
            let t = c.check_expression(arg);
            return type_flags(c, t).intersects(TypeFlags::STRING_LIKE);
        }
        ast::is_string_literal(&d_nodes[name])
    }

    /// `(b *NodeBuilderImpl) isSingleQuotedStringNamed`.
    fn is_single_quoted_string_named(&mut self, c: &mut Checker, d: NodeId,
        nodes: &[ast::Node],) -> bool {
        let __program = c.program.clone().expect("program");
        let d_nodes = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
        let Some(name) = ast::get_name_of_declaration(Some(d), &d_nodes) else {
            return false;
        };
        ast::is_string_literal(&d_nodes[name])
            && d_nodes[name]
                .as_string_literal()
                .literal_expression_base
                .literal_like_node_base
                .token_flags
                .intersects(ast::TokenFlags::SINGLE_QUOTE)
    }

    /// `(b *NodeBuilderImpl) getPropertyNameNodeForSymbol`.
    pub fn get_property_name_node_for_symbol(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
    ) -> NodeId {
        // For hash-private names, clone the original private identifier from
        // the declaration.
        if let Some(value_declaration) = symbol_value_declaration(c, symbol) {
            let __program = c.program.clone().expect("program");
            let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (value_declaration).file_index());
            if let Some(decl_name) = decl_nodes[value_declaration].name()
                && ast::is_private_identifier(&decl_nodes[decl_name])
            {
                return self
                    .deep_clone_node_in(c, nodes, decl_name)
                    .unwrap_or(decl_name);
            }
        }
        let declarations = symbol_declarations(c, symbol);
        let string_named =
            !declarations.is_empty() && declarations.iter().all(|&d| self.is_string_named(c, d, nodes));
        let single_quote = !declarations.is_empty()
            && declarations
                .iter()
                .all(|&d| self.is_single_quoted_string_named(c, d, nodes));
        let is_method = symbol_flags(c, symbol).intersects(SymbolFlags::METHOD);
        if let Some(from_name_type) = self.get_property_name_node_for_symbol_from_name_type(
            c,
            nodes,
            symbol,
            enclosing_declaration,
            single_quote,
            string_named,
            is_method,
        ) {
            return from_name_type;
        }

        let mut name = symbol_name(c, symbol);
        let private_name_prefix = format!("{}#", ast::symbol::INTERNAL_SYMBOL_NAME_PREFIX);
        if name.starts_with(&private_name_prefix) {
            // symbol IDs are unstable — replace #nnn# with #private#
            let stripped = &name[private_name_prefix.len()..];
            let stripped = stripped.trim_start_matches(|ch: char| ch.is_ascii_digit());
            name = format!("__#private{}", stripped);
        }

        self.create_property_name_node_for_identifier_or_literal(
            c,
            nodes,
            &name,
            single_quote,
            string_named,
            is_method,
            Some(symbol),
        )
    }

    /// `(b *NodeBuilderImpl) getPropertyNameNodeForSymbolFromNameType`.
    /// See `getNameOfSymbolFromNameType` for a stringy equivalent.
    fn get_property_name_node_for_symbol_from_name_type(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        single_quote: bool,
        string_named: bool,
        is_method: bool,
    ) -> Option<NodeId> {
        if !c.value_symbol_links.has(symbol) {
            return None;
        }
        let name_type = c.value_symbol_links.get(symbol).name_type;
        let name_type = name_type?;
        let mut enum_enclosing_declaration = enclosing_declaration;
        if enum_enclosing_declaration.is_none() {
            enum_enclosing_declaration = self.ctx.enclosing_file;
        }
        let nt_flags = type_flags(c, name_type);
        if nt_flags.intersects(TypeFlags::ENUM_LITERAL) {
            let nt_symbol = type_symbol(c, name_type);
            let enum_symbol = nt_symbol.and_then(|s| symbol_parent(c, s)).or(nt_symbol);
            if let (Some(enum_symbol), Some(enum_enclosing_declaration)) =
                (enum_symbol, enum_enclosing_declaration)
                && c.is_symbol_accessible_by_flags(
                    Some(enum_symbol),
                    Some(enum_enclosing_declaration),
                    SymbolFlags::VALUE, Some(nodes))
            {
                let save_enclosing_declaration = self.ctx.enclosing_declaration;
                self.ctx.enclosing_declaration = Some(enum_enclosing_declaration);
                let expr =
                    self.symbol_to_expression(c, nodes, nt_symbol.unwrap(), SymbolFlags::VALUE);
                self.ctx.enclosing_declaration = save_enclosing_declaration;
                return Some(self.f.new_computed_property_name(nodes, expr));
            }
        }
        if nt_flags.intersects(TypeFlags::STRING_OR_NUMBER_LITERAL) {
            let name = {
                let __arena_lit = c.types.clone();
                let lit = __arena_lit.get(name_type).as_literal_type().value.clone();
                match lit {
                    Some(tsc_evaluator::Value::Number(n)) => n.to_string(),
                    Some(tsc_evaluator::Value::String(s)) => s,
                    _ => String::new(),
                }
            };
            if !scanner::utilities::is_identifier_text(&name, LanguageVariant::Standard)
                && (string_named || !crate::utilities::is_numeric_literal_name(&name))
            {
                let node = self.f.new_string_literal(
                    nodes,
                    &name,
                    if single_quote {
                        ast::TokenFlags::SINGLE_QUOTE
                    } else {
                        ast::TokenFlags::NONE
                    },
                );
                return Some(node);
            }
            if crate::utilities::is_numeric_literal_name(&name) && name.starts_with('-') {
                let operand = self
                    .f
                    .new_numeric_literal(nodes, &name[1..], ast::TokenFlags::NONE);
                let unary =
                    self.f
                        .new_prefix_unary_expression(nodes, Kind::MinusToken, Some(operand));
                return Some(self.f.new_computed_property_name(nodes, Some(unary)));
            }
            return Some(self.create_property_name_node_for_identifier_or_literal(
                c,
                nodes,
                &name,
                single_quote,
                string_named,
                is_method,
                Some(symbol),
            ));
        }
        if nt_flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
            // The reference was tracked in the destination scope by
            // `trackComputedName`. Reconstructing its spelling in the source
            // scope must not paint that scope's declarations visible.
            let __arena_sym = c.types.clone();
            let sym = __arena_sym.get(name_type).symbol;
            let expr = self.symbol_to_expression_worker(
                c,
                nodes,
                sym.unwrap_or(SymbolId::NONE),
                SymbolFlags::VALUE,
            );
            return Some(self.f.new_computed_property_name(nodes, expr));
        }
        None
    }

    /// `(b *NodeBuilderImpl) addPropertyToElementList`.
    pub fn add_property_to_element_list(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        property_symbol: SymbolId,
        mut type_elements: Vec<NodeId>,
    ) -> Vec<NodeId> {
        let property_is_reverse_mapped = symbol_check_flags(c, property_symbol)
            .intersects(ast::checkflags::CheckFlags::REVERSE_MAPPED);
        let property_type;
        if self.should_use_placeholder_for_property(c, property_symbol) {
            property_type = c.any_type;
        } else {
            property_type = c.get_non_missing_type_of_symbol(property_symbol);
        }
        let save_enclosing_declaration = self.ctx.enclosing_declaration;
        self.ctx.enclosing_declaration = None;
        if crate::utilities::is_late_bound_name(&symbol_name(c, property_symbol)) {
            let declarations = symbol_declarations(c, property_symbol);
            if !declarations.is_empty() {
                let decl = declarations[0];
                if c.has_late_bindable_name(decl) {
                    let __program = c.program.clone().expect("program");
                    let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (decl).file_index());
                    if ast::is_binary_expression(&decl_nodes[decl]) {
                        let name = ast::get_name_of_declaration(Some(decl), &decl_nodes);
                        if let Some(name) = name
                            && ast::is_element_access_expression(&decl_nodes[name])
                            && decl_nodes[name]
                                .as_element_access_expression()
                                .argument_expression
                                .is_some_and(|arg| {
                                    ast::is_property_access_entity_name_expression(
                                        &decl_nodes[arg],
                                        false, // allowJs
                                        &decl_nodes,
                                    )
                                })
                        {
                            let arg = decl_nodes[name]
                                .as_element_access_expression()
                                .argument_expression
                                .unwrap();
                            self.track_computed_name(c, nodes, arg, save_enclosing_declaration);
                        }
                    } else if let Some(name_expr) = decl_nodes[decl]
                        .name()
                        .and_then(|n| decl_nodes[n].expression())
                    {
                        self.track_computed_name(c, nodes, name_expr, save_enclosing_declaration);
                    }
                }
            } else if let Some(tracker) = self.ctx.tracker.clone() {
                let name = c.symbol_to_string(property_symbol);
                tracker
                    .borrow_mut()
                    .report_non_serializable_property(&name, nodes);
            }
        }
        if let Some(value_declaration) = symbol_value_declaration(c, property_symbol) {
            self.ctx.enclosing_declaration = Some(value_declaration);
        } else {
            let declarations = symbol_declarations(c, property_symbol);
            if let Some(&decl) = declarations.first() {
                self.ctx.enclosing_declaration = Some(decl);
            } else {
                self.ctx.enclosing_declaration = save_enclosing_declaration;
            }
        }
        let property_name = self.get_property_name_node_for_symbol(
            c,
            nodes,
            property_symbol,
            save_enclosing_declaration,
        );
        self.ctx.enclosing_declaration = save_enclosing_declaration;
        self.ctx.approximate_length += symbol_name(c, property_symbol).len() as i32 + 1;

        if symbol_flags(c, property_symbol).intersects(SymbolFlags::ACCESSOR) {
            let write_type = c.get_write_type_of_symbol(property_symbol);
            if !c.is_error_type(property_type) && !c.is_error_type(write_type) {
                let prop_declaration = get_declaration_of_kind_of_symbol(
                    c,
                    property_symbol,
                    Kind::PropertyDeclaration, nodes);
                if property_type != write_type
                    || (symbol_parent(c, property_symbol)
                        .is_some_and(|p| symbol_flags(c, p).intersects(SymbolFlags::CLASS))
                        && prop_declaration.is_none())
                {
                    let symbol_mapper = if c.value_symbol_links.has(property_symbol) {
                        c.value_symbol_links.get(property_symbol).mapper
                    } else {
                        None
                    };
                    if let Some(getter_declaration) =
                        get_declaration_of_kind_of_symbol(c, property_symbol, Kind::GetAccessor, nodes)
                    {
                        let mut getter_signature =
                            c.get_signature_from_declaration(getter_declaration);
                        if let Some(mapper) = symbol_mapper {
                            getter_signature =
                                c.instantiate_signature(getter_signature, Some(mapper));
                        }
                        let getter = self.signature_to_signature_declaration_helper(
                            c,
                            nodes,
                            getter_signature,
                            Kind::GetAccessor,
                            SignatureToSignatureDeclarationOptions {
                                name: Some(property_name),
                                ..Default::default()
                            },
                        );
                        self.set_comment_range(c, nodes, getter, Some(getter_declaration));
                        type_elements.push(getter);
                    }
                    if let Some(setter_declaration) =
                        get_declaration_of_kind_of_symbol(c, property_symbol, Kind::SetAccessor, nodes)
                    {
                        let mut setter_signature =
                            c.get_signature_from_declaration(setter_declaration);
                        if let Some(mapper) = symbol_mapper {
                            setter_signature =
                                c.instantiate_signature(setter_signature, Some(mapper));
                        }
                        let setter = self.signature_to_signature_declaration_helper(
                            c,
                            nodes,
                            setter_signature,
                            Kind::SetAccessor,
                            SignatureToSignatureDeclarationOptions {
                                name: Some(property_name),
                                ..Default::default()
                            },
                        );
                        self.set_comment_range(c, nodes, setter, Some(setter_declaration));
                        type_elements.push(setter);
                    }
                    return type_elements;
                } else if symbol_parent(c, property_symbol)
                    .is_some_and(|p| symbol_flags(c, p).intersects(SymbolFlags::CLASS))
                    && prop_declaration.is_some_and(|prop_declaration| {
                        let __program = c.program.clone().expect("program");
                        let pd_nodes = crate::printer_util::arena_view(&__program, nodes, (prop_declaration).file_index());
                        pd_nodes[prop_declaration]
                            .modifier_nodes()
                            .is_some_and(|ms| {
                                ms.iter()
                                    .any(|&m| pd_nodes[m].kind == Kind::AccessorKeyword)
                            })
                    })
                {
                    let prop_declaration = prop_declaration.unwrap();
                    let fake_getter_signature = c.new_signature(
                        SignatureFlags::NONE,
                        None,
                        Vec::new(),
                        None,
                        Vec::new(),
                        Some(property_type),
                        None,
                        0,
                    );
                    let fake_getter_declaration = self.signature_to_signature_declaration_helper(
                        c,
                        nodes,
                        fake_getter_signature,
                        Kind::GetAccessor,
                        SignatureToSignatureDeclarationOptions {
                            name: Some(property_name),
                            ..Default::default()
                        },
                    );
                    self.set_comment_range(
                        c,
                        nodes,
                        fake_getter_declaration,
                        Some(prop_declaration),
                    );
                    type_elements.push(fake_getter_declaration);

                    let setter_param = c.new_symbol(SymbolFlags::FUNCTION_SCOPED_VARIABLE, "arg");
                    c.value_symbol_links.get(setter_param).resolved_type = Some(write_type);
                    let fake_setter_signature = c.new_signature(
                        SignatureFlags::NONE,
                        None,
                        Vec::new(),
                        None,
                        vec![setter_param],
                        Some(c.void_type),
                        None,
                        0,
                    );
                    let fake_setter_declaration = self.signature_to_signature_declaration_helper(
                        c,
                        nodes,
                        fake_setter_signature,
                        Kind::SetAccessor,
                        SignatureToSignatureDeclarationOptions {
                            name: Some(property_name),
                            ..Default::default()
                        },
                    );
                    type_elements.push(fake_setter_declaration);
                    return type_elements;
                }
            }
        }

        let optional_token = if symbol_flags(c, property_symbol).intersects(SymbolFlags::OPTIONAL) {
            Some(self.f.new_token(nodes, Kind::QuestionToken))
        } else {
            None
        };
        if symbol_flags(c, property_symbol).intersects(SymbolFlags::FUNCTION | SymbolFlags::METHOD)
            && c.get_properties_of_object_type(property_type).is_empty()
            && !c.is_readonly_symbol(property_symbol)
        {
            let filtered = c.filter_type(property_type, &|c: &mut Checker, t: TypeId| {
                !type_flags(c, t).intersects(TypeFlags::UNDEFINED)
            });
            let signatures = c.get_signatures_of_type(filtered, SignatureKind::Call);
            for signature in &signatures {
                let signature = *signature;
                let method_declaration = self.signature_to_signature_declaration_helper(
                    c,
                    nodes,
                    signature,
                    Kind::MethodSignature,
                    SignatureToSignatureDeclarationOptions {
                        name: Some(property_name),
                        question_token: optional_token,
                        ..Default::default()
                    },
                );
                let sig_decl = c
                    .signature_arena
                    .get(signature)
                    .declaration
                    .or(symbol_value_declaration(c, property_symbol));
                self.set_comment_range(c, nodes, method_declaration, sig_decl);
                type_elements.push(method_declaration);
            }
            if !signatures.is_empty() || optional_token.is_none() {
                return type_elements;
            }
        }
        let property_type_node;
        if self.should_use_placeholder_for_property(c, property_symbol) {
            property_type_node = Some(self.create_elided_information_placeholder(nodes));
        } else {
            if property_is_reverse_mapped {
                self.ctx.reverse_mapped_stack.push(property_symbol);
            }
            property_type_node = Some(self.serialize_type_for_declaration(
                c,
                nodes,
                None, // declaration
                Some(property_type),
                Some(property_symbol),
                true,
            ));
            if property_is_reverse_mapped {
                self.ctx.reverse_mapped_stack.pop();
            }
        }

        let modifiers = if c.is_readonly_symbol(property_symbol) {
            let readonly = self.f.new_token(nodes, Kind::ReadonlyKeyword);
            self.ctx.approximate_length += 9;
            Some(self.f.new_modifier_list(nodes, [readonly]))
        } else {
            None
        };
        let property_signature = self.f.new_property_signature_declaration(
            nodes,
            modifiers,
            Some(property_name),
            optional_token,
            property_type_node,
            None,
        );

        let vd = symbol_value_declaration(c, property_symbol);
        self.set_comment_range(c, nodes, property_signature, vd);
        type_elements.push(property_signature);

        type_elements
    }

    /// `(b *NodeBuilderImpl) createTypeNodesFromResolvedType`.
    pub fn create_type_nodes_from_resolved_type(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        resolved_type: TypeId,
    ) -> Option<NodeList> {
        if self.check_truncation_length() {
            if self.ctx.flags.intersects(nodebuilder::Flags::NO_TRUNCATION) {
                let elem = self.f.new_not_emitted_type_element(nodes);
                let commented = self.e.borrow().add_synthetic_trailing_comment(
                    elem,
                    Kind::MultiLineCommentTrivia,
                    "elided",
                    false, // hasTrailingNewLine
                );
                return Some(self.f.new_node_list([commented]));
            }
            let ellipsis = self.f.new_identifier(nodes, "...");
            let prop = self.f.new_property_signature_declaration(
                nodes,
                None,
                Some(ellipsis),
                None,
                None,
                None,
            );
            return Some(self.f.new_node_list([prop]));
        }
        let mut type_elements: Vec<NodeId> = Vec::new();
        let (call_sigs, ctor_sigs, index_infos, properties, object_flags) = {
            let __arena_g = c.types.clone();
            let g = __arena_g.get(resolved_type);
            let st = g.as_structured_type().expect("structured type");
            (
                st.call_signatures().to_vec(),
                st.construct_signatures().to_vec(),
                st.index_infos.clone(),
                st.properties.clone(),
                g.object_flags,
            )
        };
        for signature in call_sigs {
            let elem = self.signature_to_signature_declaration_helper(
                c,
                nodes,
                signature,
                Kind::CallSignature,
                SignatureToSignatureDeclarationOptions::default(),
            );
            type_elements.push(elem);
        }
        for signature in ctor_sigs {
            if c.signature_arena
                .get(signature)
                .flags
                .intersects(SignatureFlags::ABSTRACT)
            {
                continue;
            }
            let elem = self.signature_to_signature_declaration_helper(
                c,
                nodes,
                signature,
                Kind::ConstructSignature,
                SignatureToSignatureDeclarationOptions::default(),
            );
            type_elements.push(elem);
        }
        for info in &index_infos {
            let type_node = if object_flags.intersects(ObjectFlags::REVERSE_MAPPED)
                && self
                    .ctx
                    .flags
                    .intersects(nodebuilder::Flags::ALLOW_ANONYMOUS_IDENTIFIER)
            {
                Some(self.create_elided_information_placeholder(nodes))
            } else {
                None
            };
            type_elements.extend(
                self.index_info_to_object_computed_names_or_signature_declaration(
                    c, nodes, info, type_node,
                ),
            );
        }

        if properties.is_empty() {
            return Some(self.f.new_node_list(type_elements));
        }

        let mut i = 0;
        for (idx, &property_symbol) in properties.iter().enumerate() {
            if crate::nodebuilder_hover::is_expanding(&self.ctx)
                && symbol_flags(c, property_symbol).intersects(SymbolFlags::PROTOTYPE)
            {
                continue;
            }
            i += 1;
            if self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL)
            {
                if symbol_flags(c, property_symbol).intersects(SymbolFlags::PROTOTYPE) {
                    continue;
                }
                if crate::utilities::get_declaration_modifier_flags_from_symbol(c, property_symbol)
                    .intersects(ast::ModifierFlags::PRIVATE | ast::ModifierFlags::PROTECTED)
                    && let Some(tracker) = self.ctx.tracker.clone()
                {
                    tracker
                        .borrow_mut()
                        .report_private_in_base_of_class_expression(
                            &symbol_name(c, property_symbol),
                            nodes,
                        );
                }
                if is_private_identifier_symbol(c, property_symbol)
                    && let Some(tracker) = self.ctx.tracker.clone()
                {
                    tracker
                        .borrow_mut()
                        .report_private_in_base_of_class_expression(
                            &declaration_symbol_name(c, property_symbol, nodes),
                            nodes,
                        );
                }
            }
            if self.check_truncation_length() && (i + 2 < properties.len() - 1) {
                if self.ctx.flags.intersects(nodebuilder::Flags::NO_TRUNCATION) {
                    if let Some(&last) = type_elements.last() {
                        let text = format!("... {} more elided ...", properties.len() - i);
                        let last_index = type_elements.len() - 1;
                        type_elements[last_index] = self.e.borrow().add_synthetic_trailing_comment(
                            last,
                            Kind::MultiLineCommentTrivia,
                            &text,
                            false, // hasTrailingNewLine
                        );
                    }
                } else {
                    let text = format!("... {} more ...", properties.len() - i);
                    let id = self.f.new_identifier(nodes, &text);
                    let prop = self.f.new_property_signature_declaration(
                        nodes,
                        None,
                        Some(id),
                        None,
                        None,
                        None,
                    );
                    type_elements.push(prop);
                }
                let last_property = *properties.last().unwrap();
                type_elements =
                    self.add_property_to_element_list(c, nodes, last_property, type_elements);
                return if type_elements.is_empty() {
                    None
                } else {
                    Some(self.f.new_node_list(type_elements))
                };
            }
            let _ = idx;
            type_elements =
                self.add_property_to_element_list(c, nodes, property_symbol, type_elements);
        }
        if type_elements.is_empty() {
            None
        } else {
            Some(self.f.new_node_list(type_elements))
        }
    }

    /// `(b *NodeBuilderImpl) createTypeNodeFromObjectType`.
    fn create_type_node_from_object_type(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
    ) -> NodeId {
        if c.is_generic_mapped_type(t)
            || (type_object_flags(c, t).intersects(ObjectFlags::MAPPED)
                && c.types_handle().get(t).as_mapped_type().contains_error)
        {
            return self.create_mapped_type_node_from_type(c, nodes, t);
        }

        let resolved = c.resolve_structured_type_members(t);
        let (call_sigs, ctor_sigs, has_props_or_indexes) = {
            let __arena_g = c.types.clone();
            let g = __arena_g.get(resolved);
            let st = g.as_structured_type().expect("structured type");
            (
                st.call_signatures().to_vec(),
                st.construct_signatures().to_vec(),
                !st.properties.is_empty() || !st.index_infos.is_empty(),
            )
        };
        if !has_props_or_indexes {
            if call_sigs.is_empty() && ctor_sigs.is_empty() {
                self.ctx.approximate_length += 2;
                let result = self
                    .f
                    .new_type_literal_node(nodes, Some(self.f.new_node_list(Vec::new())));
                self.e
                    .borrow()
                    .set_emit_flags(result, printer::EmitFlags::SINGLE_LINE);
                return result;
            }

            if call_sigs.len() == 1 && ctor_sigs.is_empty() {
                return self.signature_to_signature_declaration_helper(
                    c,
                    nodes,
                    call_sigs[0],
                    Kind::FunctionType,
                    SignatureToSignatureDeclarationOptions::default(),
                );
            }

            if ctor_sigs.len() == 1 && call_sigs.is_empty() {
                return self.signature_to_signature_declaration_helper(
                    c,
                    nodes,
                    ctor_sigs[0],
                    Kind::ConstructorType,
                    SignatureToSignatureDeclarationOptions::default(),
                );
            }
        }

        let abstract_signatures: Vec<SignatureId> = ctor_sigs
            .iter()
            .copied()
            .filter(|&s| {
                c.signature_arena
                    .get(s)
                    .flags
                    .intersects(SignatureFlags::ABSTRACT)
            })
            .collect();
        if !abstract_signatures.is_empty() {
            let mut types: Vec<TypeId> = abstract_signatures
                .iter()
                .map(|&s| c.get_or_create_type_from_signature(s))
                .collect();
            // count the number of type elements excluding abstract
            // constructors
            let (index_info_count, property_count) = {
                let __arena_g = c.types.clone();
                let g = __arena_g.get(resolved);
                let st = g.as_structured_type().expect("structured type");
                let property_count = if self
                    .ctx
                    .flags
                    .intersects(nodebuilder::Flags::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL)
                {
                    st.properties
                        .iter()
                        .filter(|&&p| !symbol_flags(c, p).intersects(SymbolFlags::PROTOTYPE))
                        .count()
                } else {
                    st.properties.len()
                };
                (st.index_infos.len(), property_count)
            };
            let type_element_count = call_sigs.len()
                + (ctor_sigs.len() - abstract_signatures.len())
                + index_info_count
                + property_count;
            // don't include an empty object literal if there were no other
            // static-side properties to write, i.e. `abstract class C { }`
            // becomes `abstract new () => {}` and not
            // `(abstract new () => {}) & {}`
            if type_element_count != 0 {
                // create a copy of the object type without any abstract
                // construct signatures.
                types.push(
                    self.get_resolved_type_without_abstract_construct_signatures(c, resolved),
                );
            }
            let intersection = c.get_intersection_type(&types);
            return self.type_to_type_node(c, nodes, intersection);
        }

        let restore_flags = self.save_restore_flags();
        self.ctx.flags |= nodebuilder::Flags::IN_OBJECT_TYPE_LITERAL;
        let members = self.create_type_nodes_from_resolved_type(c, nodes, resolved);
        restore_flags.restore(&mut self.ctx);
        let type_literal_node = self.f.new_type_literal_node(nodes, members);
        self.ctx.approximate_length += 2;
        self.e.borrow().set_emit_flags(
            type_literal_node,
            if self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::MULTILINE_OBJECT_LITERALS)
            {
                printer::EmitFlags::NONE
            } else {
                printer::EmitFlags::SINGLE_LINE
            },
        );
        type_literal_node
    }

    /// `(b *NodeBuilderImpl) shouldWriteTypeOfFunctionSymbol`.
    fn should_write_type_of_function_symbol(
        &mut self,
        c: &mut Checker,
        symbol: SymbolId,
        type_id: TypeId,
            nodes: &[ast::Node],) -> (bool, SymbolId) {
        // `typeof C.name` can only be written when the member name is a
        // valid identifier.
        let is_static_method_symbol = symbol_flags(c, symbol).intersects(SymbolFlags::METHOD)
            && scanner::utilities::is_identifier_text(
                &symbol_name(c, symbol),
                LanguageVariant::Standard,
            )
            && symbol_declarations(c, symbol).iter().any(|&declaration| {
                let __program = c.program.clone().expect("program");
                let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
                ast::is_static(&decl_nodes[declaration])
                    && !ast::get_name_of_declaration(Some(declaration), &decl_nodes)
                        .is_some_and(|n| c.is_late_bindable_index_signature(n))
            });
        let mut is_non_local_function_symbol = false;
        let mut is_function_expression_symbol = false;
        if symbol_flags(c, symbol).intersects(SymbolFlags::FUNCTION) {
            if symbol_parent(c, symbol).is_some() {
                is_non_local_function_symbol = true;
            } else {
                for declaration in symbol_declarations(c, symbol) {
                    let __program = c.program.clone().expect("program");
                    let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
                    let parent = decl_nodes[declaration].parent;
                    let parent_kind = parent.map(|p| decl_nodes[p].kind);
                    if parent_kind == Some(Kind::SourceFile)
                        || parent_kind == Some(Kind::ModuleBlock)
                    {
                        is_non_local_function_symbol = true;
                        break;
                    }
                    let is_function_expression_symbol_here = parent.is_some_and(|p| {
                        let parent2 = decl_nodes[p].parent;
                        let parent3 = parent2.and_then(|p2| decl_nodes[p2].parent);
                        let parent4 = parent3.and_then(|p3| decl_nodes[p3].parent);
                        ast::is_function_expression_or_arrow_function(&decl_nodes[declaration])
                            && ast::is_variable_declaration(&decl_nodes[p])
                            && parent2.is_some_and(|p2| {
                                ast::is_variable_declaration_list(&decl_nodes[p2])
                            })
                            && parent3.is_some_and(|p3| ast::is_variable_statement(&decl_nodes[p3]))
                            && parent4.is_some_and(|p4| {
                                decl_nodes[p4].kind == Kind::SourceFile
                                    || decl_nodes[p4].kind == Kind::ModuleBlock
                            })
                    });
                    if is_function_expression_symbol_here {
                        is_non_local_function_symbol = true;
                        is_function_expression_symbol = true;
                        break;
                    }
                }
            }
        }
        let mut symbol = symbol;
        if is_static_method_symbol || is_non_local_function_symbol {
            if is_function_expression_symbol
                && let Some(value_declaration) = symbol_value_declaration(c, symbol)
            {
                let __program = c.program.clone().expect("program");
                let vd_nodes = crate::printer_util::arena_view(&__program, nodes, (value_declaration).file_index());
                if vd_nodes[value_declaration].parent.is_some()
                    && vd_nodes[value_declaration].parent != self.ctx.enclosing_declaration
                {
                    let parent = vd_nodes[value_declaration].parent.unwrap();
                    if let Some(parent_symbol) = vd_nodes[parent].symbol() {
                        symbol = c.get_merged_symbol(parent_symbol);
                    }
                }
            }
            // typeof is allowed only for static/non local functions
            return (
                (self
                    .ctx
                    .flags
                    .intersects(nodebuilder::Flags::USE_TYPE_OF_FUNCTION)
                    || self.ctx.visited_types.has(&type_id))
                    && (!self
                        .ctx
                        .flags
                        .intersects(nodebuilder::Flags::USE_STRUCTURAL_FALLBACK)
                        || c.is_value_symbol_accessible(
                            Some(symbol),
                            self.ctx.enclosing_declaration, Some(nodes))),
                symbol,
            );
        }
        (false, symbol)
    }

    /// `(b *NodeBuilderImpl) createAnonymousTypeNode`.
    fn create_anonymous_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
    ) -> NodeId {
        self.create_anonymous_type_node_ex(c, nodes, t, false, false)
    }

    /// `(b *NodeBuilderImpl) shouldEmitTypeOfSymbol`.
    fn should_emit_type_of_symbol(
        &mut self,
        c: &mut Checker,
        force_expansion: bool,
        force_class_expansion: bool,
        is_instance_type: SymbolFlags,
        symbol: SymbolId,
        type_id: TypeId,
            nodes: &[ast::Node],) -> (bool, SymbolId) {
        if force_expansion {
            return (false, symbol);
        }
        let non_function_result = (symbol_flags(c, symbol).intersects(SymbolFlags::CLASS)
            && !force_class_expansion
            && c.get_base_type_variable_of_class(symbol).is_none()
            && !(symbol_value_declaration(c, symbol).is_some_and(|vd| {
                let __program = c.program.clone().expect("program");
                let vd_nodes = crate::printer_util::arena_view(&__program, nodes, (vd).file_index());
                ast::is_class_like(Some(vd), &vd_nodes)
            }) && self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL)
                && {
                    let vd = symbol_value_declaration(c, symbol).unwrap();
                    let __program = c.program.clone().expect("program");
                    let vd_nodes = crate::printer_util::arena_view(&__program, nodes, (vd).file_index());
                    !ast::is_class_declaration(&vd_nodes[vd])
                        || c.is_symbol_accessible(
                            Some(symbol),
                            self.ctx.enclosing_declaration,
                            is_instance_type,
                            false, // shouldComputeAliasesToMakeVisible
                            Some(nodes),
                        )
                        .accessibility
                            != printer::SymbolAccessibility::Accessible
                }))
            || symbol_flags(c, symbol).intersects(SymbolFlags::ENUM | SymbolFlags::VALUE_MODULE);
        if non_function_result {
            return (true, symbol);
        }
        self.should_write_type_of_function_symbol(c, symbol, type_id, nodes)
    }

    /// `(b *NodeBuilderImpl) createAnonymousTypeNodeEx`.
    fn create_anonymous_type_node_ex(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
        force_class_expansion: bool,
        force_expansion: bool,
    ) -> NodeId {
        let type_id = type_id(c, t);
        if let Some(symbol) = type_symbol(c, t) {
            let is_instantiation_expression_type =
                type_object_flags(c, t).intersects(ObjectFlags::INSTANTIATION_EXPRESSION_TYPE);
            if is_instantiation_expression_type {
                let __arena_existing = c.types.clone();
                let existing = __arena_existing
                    .get(t)
                    .as_instantiation_expression_type()
                    .node;
                // instantiationExpressionType.node is unreliable for
                // constituents of unions and intersections — see the Go
                // comment for the `ErrAlias` example.
                if existing.is_some_and(|e| {
                    let __program = c.program.clone().expect("program");
                    let e_nodes = crate::printer_util::arena_view(&__program, nodes, (e).file_index());
                    ast::is_type_query_node(&e_nodes[e])
                }) && self.get_type_from_type_node(c, existing.unwrap(), false, nodes) == Some(t)
                {
                    // Guard against unbounded recursion when the existing
                    // typeof node fails to be reused (e.g. its entity name
                    // isn't accessible from this scope) and the recovery
                    // boundary's fallback re-enters `typeToTypeNode` with the
                    // very same instantiation type, which would in turn try
                    // to reuse the same node again. Mark the type as visited
                    // around the reuse attempt so the inner recursion bottoms
                    // out via the `visitedTypes` guard below.
                    if self.ctx.visited_types.has(&type_id) {
                        return self.create_cyclic_structure_placeholder(c, nodes);
                    }
                    self.ctx.visited_types.add(type_id);
                    let type_node = self.try_reuse_existing_non_parameter_type_node(
                        c,
                        nodes,
                        existing.unwrap(),
                        t,
                        None,
                        None,
                    );
                    self.ctx.visited_types.delete(&type_id);
                    if let Some(type_node) = type_node {
                        return type_node;
                    }
                }
                if self.ctx.visited_types.has(&type_id) {
                    return self.create_cyclic_structure_placeholder(c, nodes);
                }
                return self.visit_and_transform_type(
                    c,
                    nodes,
                    t,
                    NodeBuilderImpl::create_type_node_from_object_type,
                );
            }
            let is_instance_type = if is_class_instance_side(c, t) {
                SymbolFlags::TYPE
            } else {
                SymbolFlags::VALUE
            };

            // !!! JS support — see Go comment (isJSConstructor branch is not
            // ported in Go either).
            let (ok, symbol) = self.should_emit_type_of_symbol(
                c,
                force_expansion,
                force_class_expansion,
                is_instance_type,
                symbol,
                type_id, nodes);
            if ok {
                if self.should_expand_type(c, t, false /*isAlias*/) {
                    self.ctx.depth += 1;
                } else {
                    return self
                        .symbol_to_type_node(c, nodes, symbol, is_instance_type, None)
                        .unwrap_or_else(|| self.create_elided_information_placeholder(nodes));
                }
            }
            if self.ctx.visited_types.has(&type_id) {
                // If type is an anonymous type literal in a type alias
                // declaration, use type alias name.
                if let Some(type_alias) = get_type_alias_for_type_literal(c, t, nodes) {
                    // The specified symbol flags need to be reinterpreted as
                    // type flags.
                    return self
                        .symbol_to_type_node(c, nodes, type_alias, SymbolFlags::TYPE, None)
                        .unwrap_or_else(|| self.create_elided_information_placeholder(nodes));
                }
                return self.create_cyclic_structure_placeholder(c, nodes);
            }
            self.visit_and_transform_type(
                c,
                nodes,
                t,
                NodeBuilderImpl::create_type_node_from_object_type,
            )
        } else if type_object_flags(c, t).intersects(ObjectFlags::REVERSE_MAPPED)
            && !self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::ALLOW_ANONYMOUS_IDENTIFIER)
        {
            if self.ctx.visited_types.has(&type_id) {
                return self.create_cyclic_structure_placeholder(c, nodes);
            }
            self.visit_and_transform_type(
                c,
                nodes,
                t,
                NodeBuilderImpl::create_type_node_from_object_type,
            )
        } else {
            // Reverse mapped types use property and index signature
            // placeholders for display.
            self.create_type_node_from_object_type(c, nodes, t)
        }
    }

    /// `(b *NodeBuilderImpl) getTypeFromTypeNode`.
    pub fn get_type_from_type_node(
        &mut self,
        c: &mut Checker,
        node: NodeId,
        no_mapped_types: bool,
            nodes: &[ast::Node],) -> Option<TypeId> {
        // !!! noMappedTypes optional param support
        let __program = c.program.clone().expect("program");
        let node_nodes = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
        if node_nodes[node].parent.is_none() {
            return Some(c.error_type);
        }
        let t = c.get_type_from_type_node(node);
        if self.ctx.mapper.is_none() {
            return Some(t);
        }

        let instantiated = c.instantiate_type(t, self.ctx.mapper);
        if no_mapped_types && instantiated != t {
            return None;
        }
        Some(instantiated)
    }

    /// `(b *NodeBuilderImpl) typeToTypeNodeOrCircularityElision`.
    fn type_to_type_node_or_circularity_elision(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
    ) -> NodeId {
        if type_flags(c, t).intersects(TypeFlags::UNION) {
            if self.ctx.visited_types.has(&type_id(c, t)) {
                return self.create_cyclic_structure_placeholder(c, nodes);
            }
            return self.visit_and_transform_type(
                c,
                nodes,
                t,
                NodeBuilderImpl::type_to_type_node_non_nil,
            );
        }
        self.type_to_type_node(c, nodes, t)
    }

    /// Adapter for `visit_and_transform_type`'s `FnMut -> NodeId` shape over
    /// `type_to_type_node` (which takes `TypeId`, not `Option`).
    fn type_to_type_node_non_nil(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
    ) -> NodeId {
        self.type_to_type_node(c, nodes, t)
    }

    /// `(b *NodeBuilderImpl) createCyclicStructurePlaceholder`.
    fn create_cyclic_structure_placeholder(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
    ) -> NodeId {
        let _ = c;
        if !self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::ALLOW_ANONYMOUS_IDENTIFIER)
        {
            self.ctx.encountered_error = true;
            if let Some(tracker) = self.ctx.tracker.clone() {
                tracker.borrow_mut().report_cyclic_structure_error(nodes);
            }
        }
        self.create_elided_information_placeholder(nodes)
    }

    /// `(b *NodeBuilderImpl) conditionalTypeToTypeNode`.
    fn conditional_type_to_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
    ) -> NodeId {
        if self.check_truncation_length() {
            return self.create_elided_information_placeholder(nodes);
        }
        let (
            root_node,
            root_check_type,
            root_extends_type,
            root_is_distributive,
            root_infer_type_parameters,
            check_type,
            extends_type,
            mapper,
        ) = {
            let __arena_t_guard = c.types.clone();
            let t_guard = __arena_t_guard.get(t);
            let ct = t_guard.as_conditional_type();
            let root = ct.root.as_ref().expect("conditional type root");
            (
                root.node,
                root.check_type,
                root.extends_type,
                root.is_distributive,
                root.infer_type_parameters.clone(),
                ct.check_type,
                ct.extends_type,
                ct.mapper,
            )
        };
        let check_type_node = self.type_to_type_node(c, nodes, check_type.unwrap_or(c.error_type));
        self.ctx.approximate_length += 15;
        if self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
            && root_is_distributive
            && !type_flags(c, check_type.unwrap_or(TypeId::NONE))
                .intersects(TypeFlags::TYPE_PARAMETER)
        {
            let new_param_symbol =
                c.new_symbol(SymbolFlags::TYPE_PARAMETER, "T" /* as __String */);
            let new_param = c.new_type_parameter(Some(new_param_symbol));
            let name = self.type_parameter_to_name(c, nodes, new_param);
            let new_type_variable = self.f.new_type_reference_node(nodes, Some(name), None);
            self.ctx.approximate_length += 37;
            // 15 each for two added conditionals, 7 for an added infer type
            let new_mapper = crate::mapper::prepend_type_mapping(
                c,
                root_check_type.unwrap_or(TypeId::NONE),
                new_param,
                mapper,
            );
            let save_infer_type_parameters = std::mem::replace(
                &mut self.ctx.infer_type_parameters,
                root_infer_type_parameters.to_vec(),
            );
            let extends_instantiated =
                c.instantiate_type(root_extends_type.unwrap_or(TypeId::NONE), Some(new_mapper));
            let extends_type_node = self.type_to_type_node(c, nodes, extends_instantiated);
            self.ctx.infer_type_parameters = save_infer_type_parameters;
            let (true_type_id, false_type_id) = {
                let cond_nodes = root_node.map(|n| c.program_nodes_live(n, nodes));
                let cond = cond_nodes.as_ref().map(|cn| cn.clone());
                let _ = cond;
                // `t.root.node.TrueType`/`FalseType` — read through the
                // root node's own arena.
                let root_node = root_node.unwrap_or(NodeId::NONE);
                let __program = c.program.clone().expect("program");
                let rn = crate::printer_util::arena_view(&__program, nodes, (root_node).file_index());
                (
                    rn[root_node].as_conditional_type_node().true_type,
                    rn[root_node].as_conditional_type_node().false_type,
                )
            };
            let true_t =
                self.get_type_from_type_node(c, true_type_id.unwrap_or(NodeId::NONE), false, nodes);
            let true_instantiated =
                c.instantiate_type(true_t.unwrap_or(c.error_type), Some(new_mapper));
            let true_type_node =
                self.type_to_type_node_or_circularity_elision(c, nodes, true_instantiated);
            let false_t =
                self.get_type_from_type_node(c, false_type_id.unwrap_or(NodeId::NONE), false, nodes);
            let false_instantiated =
                c.instantiate_type(false_t.unwrap_or(c.error_type), Some(new_mapper));
            let false_type_node =
                self.type_to_type_node_or_circularity_elision(c, nodes, false_instantiated);

            // outermost conditional makes `T` a type parameter, allowing the
            // inner conditionals to be distributive; second conditional makes
            // `T` have `T & checkType` substitution, so it is correctly
            // usable as the checkType; inner conditional runs the check the
            // user provided on the check type (distributively) and returns
            // the result. See the Go comment for the simplification notes.
            let new_id = {
                let tr = nodes[new_type_variable].as_type_reference_node();
                let type_name = tr.type_name.unwrap_or(NodeId::NONE);
                self.f
                    .deep_clone_node(nodes, type_name)
                    .unwrap_or(type_name)
            };
            let tp_decl =
                self.f
                    .new_type_parameter_declaration(nodes, None, Some(new_id), None, None, None);
            let synthetic_extends_node = self.f.new_infer_type_node(nodes, Some(tp_decl));
            let inner_check_conditional_node = self.f.new_conditional_type_node(
                nodes,
                Some(new_type_variable),
                Some(extends_type_node),
                Some(true_type_node),
                Some(false_type_node),
            );
            let name_clone = self.f.deep_clone_node(nodes, name).unwrap_or(name);
            let name_ref = self
                .f
                .new_type_reference_node(nodes, Some(name_clone), None);
            let cloned_check = self
                .f
                .deep_clone_node(nodes, check_type_node)
                .unwrap_or(check_type_node);
            let never_node = self.f.new_keyword_type_node(nodes, Kind::NeverKeyword);
            let synthetic_true_node = self.f.new_conditional_type_node(
                nodes,
                Some(name_ref),
                Some(cloned_check),
                Some(inner_check_conditional_node),
                Some(never_node),
            );
            let never_node2 = self.f.new_keyword_type_node(nodes, Kind::NeverKeyword);
            return self.f.new_conditional_type_node(
                nodes,
                Some(check_type_node),
                Some(synthetic_extends_node),
                Some(synthetic_true_node),
                Some(never_node2),
            );
        }
        let save_infer_type_parameters = std::mem::replace(
            &mut self.ctx.infer_type_parameters,
            root_infer_type_parameters.to_vec(),
        );
        let extends_type_node =
            self.type_to_type_node(c, nodes, extends_type.unwrap_or(c.error_type));
        self.ctx.infer_type_parameters = save_infer_type_parameters;
        let true_t = c.get_true_type_from_conditional_type(t);
        let true_type_node = self.type_to_type_node_or_circularity_elision(c, nodes, true_t);
        let false_t = c.get_false_type_from_conditional_type(t);
        let false_type_node = self.type_to_type_node_or_circularity_elision(c, nodes, false_t);
        self.f.new_conditional_type_node(
            nodes,
            Some(check_type_node),
            Some(extends_type_node),
            Some(true_type_node),
            Some(false_type_node),
        )
    }

    /// `(b *NodeBuilderImpl) getParentSymbolOfTypeParameter`.
    fn get_parent_symbol_of_type_parameter(
        &mut self,
        c: &mut Checker,
        type_parameter: TypeId,
            nodes: &[ast::Node],) -> Option<SymbolId> {
        let tp_symbol = type_symbol(c, type_parameter);
        let tp =
            tp_symbol.and_then(|s| get_declaration_of_kind_of_symbol(c, s, Kind::TypeParameter, nodes));
        let host = tp.and_then(|tp| {
            // !!! JSDoc support — see Go comment.
            let __program = c.program.clone().expect("program");
            let tp_nodes = crate::printer_util::arena_view(&__program, nodes, (tp).file_index());
            tp_nodes[tp].parent
        });
        host.and_then(|host| c.get_symbol_of_node(host))
    }

    /// `(b *NodeBuilderImpl) arrayOrTupleTypeToNode`.
    fn array_or_tuple_type_to_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
    ) -> NodeId {
        let mut type_arguments = c.get_type_arguments(t);
        let __arena_target = c.types.clone();
        let target = __arena_target.get(t).target();
        if target == Some(c.global_array_type) || target == Some(c.global_readonly_array_type) {
            if self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::WRITE_ARRAY_AS_GENERIC_TYPE)
            {
                let type_argument_node = self.type_to_type_node(c, nodes, type_arguments[0]);
                let target_symbol = target.and_then(|tt| type_symbol(c, tt));
                let name = if target == Some(c.global_array_type) {
                    "Array"
                } else {
                    "ReadonlyArray"
                };
                let id = self.new_identifier(nodes, name, target_symbol);
                let args = self.f.new_node_list([type_argument_node]);
                return self.f.new_type_reference_node(nodes, Some(id), Some(args));
            }
            let element_type = self.type_to_type_node(c, nodes, type_arguments[0]);
            let array_type = self.f.new_array_type_node(nodes, Some(element_type));
            if target == Some(c.global_array_type) {
                return array_type;
            }
            return self
                .f
                .new_type_operator_node(nodes, Kind::ReadonlyKeyword, Some(array_type));
        }

        // debug.Assert(t.Target().objectFlags & ObjectFlagsTuple != 0)
        let element_infos = target
            .map(|tt| {
                c.types_handle()
                    .get(tt)
                    .as_tuple_type()
                    .element_infos
                    .clone()
            })
            .unwrap_or_default();
        let readonly = target
            .map(|tt| c.types_handle().get(tt).as_tuple_type().readonly)
            .unwrap_or(false);
        type_arguments = type_arguments
            .iter()
            .enumerate()
            .map(|(i, &arg)| {
                let is_optional = element_infos
                    .get(i)
                    .is_some_and(|info| info.flags.intersects(ElementFlags::OPTIONAL));
                c.remove_missing_type(arg, is_optional)
            })
            .collect();
        if !type_arguments.is_empty() {
            let arity = c.get_type_reference_arity(t) as usize;
            if let Some(mut tuple_constituent_nodes) = self.map_to_type_nodes(
                c,
                nodes,
                &type_arguments[0..arity],
                false, /*isBareList*/
            ) {
                for i in 0..tuple_constituent_nodes.nodes.len() {
                    let info = element_infos.get(i).cloned().unwrap_or_default();
                    let flags = info.flags;
                    let labeled_element_declaration = info.labeled_declaration;

                    if labeled_element_declaration.is_some() {
                        let dot_dot_dot_token = if flags.intersects(ElementFlags::VARIABLE) {
                            Some(self.f.new_token(nodes, Kind::DotDotDotToken))
                        } else {
                            None
                        };
                        let label = c.get_tuple_element_label(info, None, i);
                        let label_id = self.new_identifier(nodes, &label, None);
                        let question_token = if flags.intersects(ElementFlags::OPTIONAL) {
                            Some(self.f.new_token(nodes, Kind::QuestionToken))
                        } else {
                            None
                        };
                        let inner = tuple_constituent_nodes.nodes[i];
                        let type_node = if flags.intersects(ElementFlags::REST) {
                            self.f.new_array_type_node(nodes, Some(inner))
                        } else {
                            inner
                        };
                        std::rc::Rc::make_mut(&mut tuple_constituent_nodes.nodes)[i] = self.f.new_named_tuple_member(
                            nodes,
                            dot_dot_dot_token,
                            Some(label_id),
                            question_token,
                            Some(type_node),
                        );
                    } else if flags.intersects(ElementFlags::VARIABLE) {
                        let inner = tuple_constituent_nodes.nodes[i];
                        let type_node = if flags.intersects(ElementFlags::REST) {
                            self.f.new_array_type_node(nodes, Some(inner))
                        } else {
                            inner
                        };
                        std::rc::Rc::make_mut(&mut tuple_constituent_nodes.nodes)[i] =
                            self.f.new_rest_type_node(nodes, Some(type_node));
                    } else if flags.intersects(ElementFlags::OPTIONAL) {
                        let inner = tuple_constituent_nodes.nodes[i];
                        std::rc::Rc::make_mut(&mut tuple_constituent_nodes.nodes)[i] =
                            self.f.new_optional_type_node(nodes, Some(inner));
                    }
                }
                let tuple_type_node = self
                    .f
                    .new_tuple_type_node(nodes, Some(tuple_constituent_nodes));
                self.e
                    .borrow()
                    .set_emit_flags(tuple_type_node, printer::EmitFlags::SINGLE_LINE);
                if readonly {
                    return self.f.new_type_operator_node(
                        nodes,
                        Kind::ReadonlyKeyword,
                        Some(tuple_type_node),
                    );
                }
                return tuple_type_node;
            }
        }
        if self.ctx.encountered_error
            || self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::ALLOW_EMPTY_TUPLE)
        {
            let tuple_type_node = self
                .f
                .new_tuple_type_node(nodes, Some(self.f.new_node_list(Vec::new())));
            self.e
                .borrow()
                .set_emit_flags(tuple_type_node, printer::EmitFlags::SINGLE_LINE);
            if readonly {
                return self.f.new_type_operator_node(
                    nodes,
                    Kind::ReadonlyKeyword,
                    Some(tuple_type_node),
                );
            }
            return tuple_type_node;
        }
        self.ctx.encountered_error = true;
        // TODO: GH#18217 — Go returns nil here; callers map to `any`.
        self.f.new_keyword_type_node(nodes, Kind::AnyKeyword)
    }

    /// `(b *NodeBuilderImpl) typeReferenceToTypeNode`.
    fn type_reference_to_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
    ) -> NodeId {
        let type_arguments = c.get_type_arguments(t);
        let t_symbol = type_symbol(c, t);
        if self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL)
            && t_symbol
                .and_then(|s| symbol_value_declaration(c, s))
                .is_some_and(|vd| {
                    let __program = c.program.clone().expect("program");
                    let vd_nodes = crate::printer_util::arena_view(&__program, nodes, (vd).file_index());
                    ast::is_class_like(Some(vd), &vd_nodes)
                })
            && t_symbol.is_some_and(|s| {
                !c.is_value_symbol_accessible(Some(s), self.ctx.enclosing_declaration, Some(nodes))
            })
        {
            return self.create_anonymous_type_node(c, nodes, t);
        }

        let __arena_target = c.types.clone();
        let target = __arena_target.get(t).target().unwrap_or(t);
        let __arena_outer_type_parameters = c.types.clone();
        let outer_type_parameters = __arena_outer_type_parameters
            .get(target)
            .as_interface_type()
            .map(|it| it.outer_type_parameters().to_vec())
            .unwrap_or_default();
        let mut i = 0usize;
        let mut result_type: Option<NodeId> = None;
        if !outer_type_parameters.is_empty() {
            let length = outer_type_parameters.len();
            while i < length {
                // Find group of type arguments for type parameters with the
                // same declaring container.
                let start = i;
                let parent = self.get_parent_symbol_of_type_parameter(c, outer_type_parameters[i], nodes);
                loop {
                    i += 1;
                    if !(i < length
                        && self.get_parent_symbol_of_type_parameter(c, outer_type_parameters[i], nodes)
                            == parent)
                    {
                        break;
                    }
                }
                // When type parameters are their own type arguments for the
                // whole group (i.e. we have the default outer type
                // arguments), we don't show the group.
                if outer_type_parameters[start..i]
                    != type_arguments.get(start..i).unwrap_or(&[])[..]
                {
                    let type_argument_slice = self.map_to_type_nodes(
                        c,
                        nodes,
                        &type_arguments[start..i],
                        false, // isBareList
                    );
                    let restore_flags = self.save_restore_flags();
                    self.ctx.flags |= nodebuilder::Flags::FORBID_INDEXED_ACCESS_SYMBOL_REFERENCES;
                    let ref_ = parent.and_then(|parent| {
                        self.symbol_to_type_node(
                            c,
                            nodes,
                            parent,
                            SymbolFlags::TYPE,
                            type_argument_slice,
                        )
                    });
                    restore_flags.restore(&mut self.ctx);
                    if let Some(ref_) = ref_ {
                        result_type = match result_type {
                            None => Some(ref_),
                            Some(result) => self.append_reference_to_type(c, nodes, result, ref_),
                        };
                    }
                }
            }
        }
        let mut type_argument_nodes: Option<NodeList> = None;
        if !type_arguments.is_empty() {
            let mut type_parameter_count = 0usize;
            let __arena_type_params = c.types.clone();
            let type_params = __arena_type_params
                .get(target)
                .as_interface_type()
                .map(|it| it.type_parameters().to_vec());
            if let Some(type_params) = &type_params {
                type_parameter_count = type_params.len().min(type_arguments.len());

                // Maybe we should do this for more types, but for now we only
                // elide type arguments that are identical to their associated
                // type parameters' defaults for `Iterable`, `IterableIterator`,
                // `AsyncIterable`, and `AsyncIterableIterator` to provide
                // backwards-compatible .d.ts emit due to each now having three
                // type parameters instead of only one.
                let global_iterable = c.get_global_iterable_type.clone().expect("thunk")(c);
                let global_iterable_iterator =
                    c.get_global_iterable_iterator_type.clone().expect("thunk")(c);
                let global_async_iterable =
                    c.get_global_async_iterable_type.clone().expect("thunk")(c);
                let global_async_iterable_iterator = c
                    .get_global_async_iterable_iterator_type
                    .clone()
                    .expect("thunk")(c);
                if c.is_reference_to_type(t, global_iterable)
                    || c.is_reference_to_type(t, global_iterable_iterator)
                    || c.is_reference_to_type(t, global_async_iterable)
                    || c.is_reference_to_type(t, global_async_iterable_iterator)
                {
                    let __arena_ref_node = c.types.clone();
                    let ref_node = __arena_ref_node.get(t).as_type_reference().node;
                    let ref_node_type_arguments_len = ref_node.and_then(|n| {
                        let __program = c.program.clone().expect("program");
                        let nn = crate::printer_util::arena_view(&__program, nodes, (n).file_index());
                        if ast::is_type_reference_node(&nn[n]) {
                            nn[n].type_arguments().map(|l| l.len())
                        } else {
                            None
                        }
                    });
                    if ref_node.is_none()
                        || ref_node_type_arguments_len.is_none_or(|l| l < type_parameter_count)
                    {
                        while type_parameter_count > 0 {
                            let type_argument = type_arguments[type_parameter_count - 1];
                            let type_parameter = type_params[type_parameter_count - 1];
                            let default_type = c.get_default_from_type_parameter(type_parameter);
                            if default_type.is_none()
                                || !c.is_type_identical_to(type_argument, default_type.unwrap())
                            {
                                break;
                            }
                            type_parameter_count -= 1;
                        }
                    }
                }
            }

            type_argument_nodes = self.map_to_type_nodes(
                c,
                nodes,
                &type_arguments[i..type_parameter_count],
                false, // isBareList
            );
        }
        let restore_flags = self.save_restore_flags();
        self.ctx
            .flags
            .insert(nodebuilder::Flags::FORBID_INDEXED_ACCESS_SYMBOL_REFERENCES);
        let final_ref = t_symbol.and_then(|s| {
            self.symbol_to_type_node(c, nodes, s, SymbolFlags::TYPE, type_argument_nodes)
        });
        restore_flags.restore(&mut self.ctx);
        match (result_type, final_ref) {
            (None, final_ref) => {
                final_ref.unwrap_or_else(|| self.f.new_keyword_type_node(nodes, Kind::AnyKeyword))
            }
            (Some(result), Some(final_ref)) => self
                .append_reference_to_type(c, nodes, result, final_ref)
                .unwrap_or(result),
            (Some(result), None) => result,
        }
    }

    /// `(b *NodeBuilderImpl) visitAndTransformType`.
    fn visit_and_transform_type(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
        transform: impl FnOnce(&mut Self, &mut Checker, &mut Vec<ast::Node>, TypeId) -> NodeId,
    ) -> NodeId {
        if self.check_truncation_length() {
            return self.create_elided_information_placeholder(nodes);
        }

        let mut t_id = type_id(c, t);
        let is_array_or_tuple = c.is_array_or_tuple_type(t);
        if is_array_or_tuple {
            // Deferred and regular references share a cycle identity.
            let __arena_target = c.types.clone();
            let target = __arena_target.get(t).target().unwrap_or(t);
            let args = c.get_type_arguments(t);
            let new_ref = c.create_type_reference(target, &args);
            t_id = type_id(c, new_ref);
        }
        if self.ctx.visited_types.has(&t_id) {
            return self.create_cyclic_structure_placeholder(c, nodes);
        }

        let is_constructor_object = type_object_flags(c, t).intersects(ObjectFlags::ANONYMOUS)
            && type_symbol(c, t).is_some_and(|s| symbol_flags(c, s).intersects(SymbolFlags::CLASS));
        let id: Option<CompositeSymbolIdentity> = if is_array_or_tuple {
            // Do not bound finite container nesting by the shared Array
            // symbol or tuple origin.
            None
        } else if type_object_flags(c, t).intersects(ObjectFlags::REFERENCE)
            && c.types_handle().get(t).as_type_reference().node.is_some()
        {
            Some(CompositeSymbolIdentity {
                is_constructor_node: false,
                symbol_id: SymbolId::NONE,
                node_id: c.types_handle().get(t).as_type_reference().node.unwrap(),
            })
        } else if type_flags(c, t).intersects(TypeFlags::CONDITIONAL) {
            Some(CompositeSymbolIdentity {
                is_constructor_node: false,
                symbol_id: SymbolId::NONE,
                node_id: c
                    .types_handle()
                    .get(t)
                    .as_conditional_type()
                    .root
                    .as_ref()
                    .and_then(|r| r.node)
                    .unwrap_or(NodeId::NONE),
            })
        } else if let Some(symbol) = type_symbol(c, t) {
            Some(CompositeSymbolIdentity {
                is_constructor_node: is_constructor_object,
                symbol_id: symbol,
                node_id: NodeId::NONE,
            })
        } else {
            None
        };
        // Since instantiations of the same anonymous type have the same
        // symbol, tracking symbols instead of types allows us to catch
        // circular references to instantiations of the same anonymous type.

        let mut key = CompositeTypeCacheIdentity {
            type_id: t_id,
            flags: self.ctx.flags,
            internal_flags: self.ctx.internal_flags,
            infer_type_parameters: CacheHashKey::default(),
        };
        if !self.ctx.infer_type_parameters.is_empty() {
            key.infer_type_parameters =
                crate::checker_types::get_type_list_key(&self.ctx.infer_type_parameters);
        }
        // Don't rely on type cache if we're expanding a type, because we need
        // to compute `canIncreaseExpansionDepth`.
        let can_use_cache = self.ctx.max_expansion_depth < 0;
        if can_use_cache
            && let Some(enclosing) = self.ctx.enclosing_declaration
            && self.links.has(&enclosing)
        {
            let links = self.links.get(enclosing);
            let hit = links.serialized_types.get(&key).map(|r| {
                (
                    r.node,
                    r.truncating,
                    r.added_length,
                    r.tracked_symbols.clone(),
                    (r.kind, r.pos, r.end),
                )
            });
            if let Some((cached_node, truncating, added_length, tracked_symbols, fingerprint)) = hit
            {
                // The cached tree was minted into whatever buffer produced
                // it — often a scratch arena that no longer exists (Go's
                // heap keeps it alive; ours does not). Only reuse the entry
                // when the whole subtree still resolves in `nodes` or in
                // the node's home arena; otherwise fall through and
                // reserialize the type. The kind/pos/end fingerprint guards
                // against ids that still resolve but now alias a different
                // physical node.
                let fingerprint_matches =
                    |buf: &[ast::Node], n: NodeId| -> bool {
                        let (kind, pos, end) = fingerprint;
                        buf[n].kind == kind && buf[n].pos() == pos && buf[n].end() == end
                    };
                let reusable = match cached_node {
                    None => true,
                    Some(n)
                        if crate::printer_util::buffer_resolves_id(nodes, n)
                            && fingerprint_matches(nodes, n) =>
                    {
                        crate::printer_util::subtree_clonable_in(nodes, n)
                    }
                    Some(n) => {
                        let program = c.program.clone().expect("program");
                        let src = crate::printer_util::live_arena_lookup_for(n)
                            .map(|rc| (*rc).clone())
                            .unwrap_or_else(|| program.nodes(n.file_index()).to_vec());
                        crate::printer_util::buffer_resolves_id(&src, n)
                            && fingerprint_matches(&src, n)
                            && crate::printer_util::subtree_clonable_in(&src, n)
                    }
                };
                if !reusable {
                    links.serialized_types.remove(&key);
                    // fall through to `transform`
                } else {
                    // TODO: check if we instead store late painted statements
                    // associated with this?
                    for arg in &tracked_symbols {
                        if let Some(tracker) = self.ctx.tracker.clone() {
                            let nodes_view: &[ast::Node] = nodes;
                            tracker.borrow_mut().track_symbol(
                                arg.symbol,
                                arg.enclosing_declaration,
                                arg.meaning,
                                nodes_view,
                                &mut |sym, en, mn, sc| {
                                    c.is_symbol_accessible(
                                        sym,
                                        en,
                                        mn,
                                        sc,
                                        Some(nodes_view),
                                    )
                                },
                            );
                        }
                    }
                    if truncating {
                        self.ctx.truncating = true;
                    }
                    self.ctx.approximate_length += added_length;
                    if let Some(cached_node) = cached_node {
                        return self
                            .deep_clone_node_in(c, nodes, cached_node)
                            .unwrap_or(cached_node);
                    }
                }
            }
        }

        let mut reverse_mapped_origin: Option<CompositeSymbolIdentity> = None;
        let mut reverse_mapped_depth = 0;
        if type_object_flags(c, t).intersects(ObjectFlags::REVERSE_MAPPED) {
            // Growing type arguments can prevent a reverse mapped type from
            // repeating. Bound expansion by its mapped declaration as well as
            // its type identity.
            let __arena_origin_node = c.types.clone();
            let origin_node = __arena_origin_node
                .get(t)
                .as_reverse_mapped_type()
                .mapped_type
                .and_then(|mt| c.types_handle().get(mt).as_mapped_type().declaration);
            let origin = CompositeSymbolIdentity {
                is_constructor_node: false,
                symbol_id: SymbolId::NONE,
                node_id: origin_node.unwrap_or(NodeId::NONE),
            };
            let depth = *self.ctx.symbol_depth.get(&origin).unwrap_or(&0);
            if depth >= 100 {
                self.ctx.truncating = true;
                return self.create_elided_information_placeholder(nodes);
            }
            self.ctx.symbol_depth.insert(origin, depth + 1);
            reverse_mapped_origin = Some(origin);
            reverse_mapped_depth = depth;
        }

        let mut depth = 0;
        if let Some(id) = id {
            depth = *self.ctx.symbol_depth.get(&id).unwrap_or(&0);
            if depth > 10 {
                self.ctx.truncating = true;
                if let Some(origin) = reverse_mapped_origin {
                    self.ctx.symbol_depth.insert(origin, reverse_mapped_depth);
                }
                return self.create_elided_information_placeholder(nodes);
            }
            self.ctx.symbol_depth.insert(id, depth + 1);
        }
        self.ctx.visited_types.add(t_id);
        let prev_tracked_symbols = std::mem::replace(
            &mut self.ctx.tracked_symbols,
            Rc::new(RefCell::new(Vec::new())),
        );
        let start_length = self.ctx.approximate_length;
        let result = transform(self, c, nodes, t);
        let added_length = self.ctx.approximate_length - start_length;
        if can_use_cache && !self.ctx.reported_diagnostic.get() && !self.ctx.encountered_error {
            if let Some(enclosing) = self.ctx.enclosing_declaration {
                let links = self.links.get(enclosing);
                links.serialized_types.insert(
                    key,
                    {
                        // `result` may live in `nodes` or in a still-live
                        // scratch arena; fingerprint whichever buffer holds
                        // it so a later hit can verify the id still names
                        // the same physical node.
                        let fp_buf: &[ast::Node] = nodes;
                        let resolved = if crate::printer_util::buffer_resolves_id(fp_buf, result)
                        {
                            Some((fp_buf[result].kind, fp_buf[result].pos(), fp_buf[result].end()))
                        } else {
                            crate::printer_util::live_arena_lookup_for(result).and_then(|rc| {
                                let buf: &[ast::Node] = &rc;
                                crate::printer_util::buffer_resolves_id(buf, result).then(|| {
                                    (buf[result].kind, buf[result].pos(), buf[result].end())
                                })
                            })
                        };
                        let (kind, pos, end) =
                            resolved.unwrap_or((Kind::Unknown, i32::MIN, i32::MIN));
                        SerializedTypeEntry {
                            node: Some(result),
                            truncating: self.ctx.truncating,
                            added_length,
                            tracked_symbols: self.ctx.tracked_symbols.borrow().clone(),
                            kind,
                            pos,
                            end,
                        }
                    },
                );
            }
        }
        self.ctx.visited_types.delete(&t_id);
        if let Some(id) = id {
            self.ctx.symbol_depth.insert(id, depth);
        }
        self.ctx.tracked_symbols = prev_tracked_symbols;
        if let Some(origin) = reverse_mapped_origin {
            self.ctx.symbol_depth.insert(origin, reverse_mapped_depth);
        }
        result
    }

    /// `(b *NodeBuilderImpl) typeToTypeNode`.
    pub fn type_to_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: TypeId,
    ) -> NodeId {
        self.type_to_type_node_opt(c, nodes, Some(t))
            .unwrap_or_else(|| self.f.new_keyword_type_node(nodes, Kind::AnyKeyword))
    }

    /// `(b *NodeBuilderImpl) typeToTypeNode` with Go's nilable `t`.
    pub fn type_to_type_node_opt(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        t: Option<TypeId>,
    ) -> Option<NodeId> {
        let in_type_alias = self.ctx.flags & nodebuilder::Flags::IN_TYPE_ALIAS;
        self.ctx.flags.remove(nodebuilder::Flags::IN_TYPE_ALIAS);

        let Some(mut t) = t else {
            if !self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::ALLOW_EMPTY_UNION_OR_INTERSECTION)
            {
                self.ctx.encountered_error = true;
                return None;
                // TODO: GH#18217
            }
            self.ctx.approximate_length += 3;
            return Some(self.f.new_keyword_type_node(nodes, Kind::AnyKeyword));
        };

        t = get_non_distributed_type_parameter(&c.types, t);

        // Push type onto typeStack for expansion depth tracking.
        let pushed = self.ctx.max_expansion_depth >= 0;
        if pushed {
            self.ctx.type_stack.push(t);
        }
        let result = self.type_to_type_node_inner(c, nodes, t, in_type_alias);
        if pushed {
            self.ctx.type_stack.pop();
        }
        result
    }

    /// The body of `typeToTypeNode` after the nil/stack handling.
    fn type_to_type_node_inner(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        mut t: TypeId,
        in_type_alias: nodebuilder::Flags,
    ) -> Option<NodeId> {
        if !self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::NO_TYPE_REDUCTION)
        {
            t = c.get_reduced_type(t);
        }

        let t_flags = type_flags(c, t);
        if t_flags.intersects(TypeFlags::ANY) {
            if let Some(alias) = type_alias(c, t) {
                return Some(alias_to_type_reference_node(self, c, nodes, &alias));
            }
            if t == c.unresolved_type {
                let kw = self.f.new_keyword_type_node(nodes, Kind::AnyKeyword);
                return Some(self.e.borrow().add_synthetic_leading_comment(
                    kw,
                    Kind::MultiLineCommentTrivia,
                    "unresolved",
                    false, // hasTrailingNewLine
                ));
            }
            self.ctx.approximate_length += 3;
            let kind = if t == c.intrinsic_marker_type {
                Kind::IntrinsicKeyword
            } else {
                Kind::AnyKeyword
            };
            return Some(self.f.new_keyword_type_node(nodes, kind));
        }
        if t_flags.intersects(TypeFlags::UNKNOWN) {
            return Some(self.f.new_keyword_type_node(nodes, Kind::UnknownKeyword));
        }
        if t_flags.intersects(TypeFlags::STRING) {
            self.ctx.approximate_length += 6;
            return Some(self.f.new_keyword_type_node(nodes, Kind::StringKeyword));
        }
        if t_flags.intersects(TypeFlags::NUMBER) {
            self.ctx.approximate_length += 6;
            return Some(self.f.new_keyword_type_node(nodes, Kind::NumberKeyword));
        }
        if t_flags.intersects(TypeFlags::BIG_INT) {
            self.ctx.approximate_length += 6;
            return Some(self.f.new_keyword_type_node(nodes, Kind::BigIntKeyword));
        }
        if t_flags.intersects(TypeFlags::BOOLEAN) && type_alias(c, t).is_none() {
            self.ctx.approximate_length += 7;
            return Some(self.f.new_keyword_type_node(nodes, Kind::BooleanKeyword));
        }
        let mut expanding_enum = false;
        if t_flags.intersects(TypeFlags::ENUM_LIKE) {
            let t_symbol = type_symbol(c, t);
            if t_symbol.is_some_and(|s| symbol_flags(c, s).intersects(SymbolFlags::ENUM_MEMBER)) {
                let t_symbol = t_symbol.unwrap();
                let parent_symbol = c.get_parent_of_symbol(t_symbol);
                if let Some(parent_symbol) = parent_symbol {
                    let parent_name =
                        self.symbol_to_type_node(c, nodes, parent_symbol, SymbolFlags::TYPE, None);
                    if c.get_declared_type_of_symbol(parent_symbol) == t {
                        return parent_name;
                    }
                    let Some(parent_name) = parent_name else {
                        return None;
                    };
                    let member_name = symbol_name(c, t_symbol);
                    if scanner::utilities::is_identifier_text(
                        &member_name,
                        LanguageVariant::Standard,
                    ) {
                        let member_id = self.f.new_identifier(nodes, &member_name);
                        let ref_ = self.f.new_type_reference_node(nodes, Some(member_id), None);
                        return self.append_reference_to_type(c, nodes, parent_name, ref_);
                    }
                    if ast::is_import_type_node(&nodes[parent_name]) {
                        nodes[parent_name].as_import_type_node_mut().is_type_of = true;
                        // mutably update, node is freshly manufactured anyhow
                        let member_lit = self.new_string_literal(c, nodes, &member_name);
                        let lit = self.f.new_literal_type_node(nodes, Some(member_lit));
                        return Some(self.f.new_indexed_access_type_node(
                            nodes,
                            Some(parent_name),
                            Some(lit),
                        ));
                    } else if ast::is_type_reference_node(&nodes[parent_name]) {
                        let type_name = nodes[parent_name].as_type_reference_node().type_name;
                        let query = self.f.new_type_query_node(nodes, type_name, None);
                        let member_lit = self.new_string_literal(c, nodes, &member_name);
                        let lit = self.f.new_literal_type_node(nodes, Some(member_lit));
                        return Some(self.f.new_indexed_access_type_node(
                            nodes,
                            Some(query),
                            Some(lit),
                        ));
                    } else {
                        panic!("Unhandled type node kind returned from `symbolToTypeNode`.");
                    }
                }
            }
            if !t_flags.intersects(TypeFlags::UNION)
                || !self.should_expand_type(c, t, false /*isAlias*/)
            {
                if let Some(symbol) = type_symbol(c, t) {
                    return self.symbol_to_type_node(c, nodes, symbol, SymbolFlags::TYPE, None);
                }
            } else {
                expanding_enum = true;
            }
        }
        if t_flags.intersects(TypeFlags::STRING_LITERAL) {
            let value = match c.types_handle().get(t).as_literal_type().value.clone() {
                Some(tsc_evaluator::Value::String(s)) => s,
                _ => String::new(),
            };
            self.ctx.approximate_length += value.len() as i32 + 2;
            let lit = self.new_string_literal(c, nodes, &value);
            self.e
                .borrow()
                .add_emit_flags(lit, printer::EmitFlags::NO_ASCII_ESCAPING);
            return Some(self.f.new_literal_type_node(nodes, Some(lit)));
        }
        if t_flags.intersects(TypeFlags::NUMBER_LITERAL) {
            let value = match c.types_handle().get(t).as_literal_type().value.clone() {
                Some(tsc_evaluator::Value::Number(n)) => n,
                _ => jsnum::Number(0.0),
            };
            self.ctx.approximate_length += value.to_string().len() as i32;
            if value.0 < 0.0 {
                let text = value.to_string();
                let operand = self
                    .f
                    .new_numeric_literal(nodes, &text[1..], ast::TokenFlags::NONE);
                let unary =
                    self.f
                        .new_prefix_unary_expression(nodes, Kind::MinusToken, Some(operand));
                return Some(self.f.new_literal_type_node(nodes, Some(unary)));
            }
            let text = value.to_string();
            let lit = self
                .f
                .new_numeric_literal(nodes, &text, ast::TokenFlags::NONE);
            return Some(self.f.new_literal_type_node(nodes, Some(lit)));
        }
        if t_flags.intersects(TypeFlags::BIG_INT_LITERAL) {
            let value = crate::checker_d::get_big_int_literal_value(&c.types, t);
            let text = crate::utilities::pseudo_big_int_to_string(value);
            self.ctx.approximate_length += text.len() as i32 + 1;
            let lit = self
                .f
                .new_big_int_literal(nodes, &format!("{text}n"), ast::TokenFlags::NONE);
            return Some(self.f.new_literal_type_node(nodes, Some(lit)));
        }
        if t_flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
            let value = matches!(
                c.types_handle().get(t).as_literal_type().value,
                Some(tsc_evaluator::Value::Bool(true))
            );
            if value {
                self.ctx.approximate_length += 4;
                let lit = self.f.new_keyword_expression(nodes, Kind::TrueKeyword);
                return Some(self.f.new_literal_type_node(nodes, Some(lit)));
            }
            self.ctx.approximate_length += 5;
            let lit = self.f.new_keyword_expression(nodes, Kind::FalseKeyword);
            return Some(self.f.new_literal_type_node(nodes, Some(lit)));
        }
        if t_flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
            if !self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::ALLOW_UNIQUE_ES_SYMBOL_TYPE)
            {
                let t_symbol = type_symbol(c, t);
                if t_symbol.is_some_and(|s| {
                    c.is_value_symbol_accessible(Some(s), self.ctx.enclosing_declaration, Some(nodes))
                }) {
                    self.ctx.approximate_length += 6;
                    return self.symbol_to_type_node(
                        c,
                        nodes,
                        t_symbol.unwrap(),
                        SymbolFlags::VALUE,
                        None,
                    );
                }
                if let Some(tracker) = self.ctx.tracker.clone() {
                    tracker
                        .borrow_mut()
                        .report_inaccessible_unique_symbol_error(nodes);
                }
            }
            self.ctx.approximate_length += 13;
            let symbol_kw = self.f.new_keyword_type_node(nodes, Kind::SymbolKeyword);
            return Some(self.f.new_type_operator_node(
                nodes,
                Kind::UniqueKeyword,
                Some(symbol_kw),
            ));
        }
        if t_flags.intersects(TypeFlags::VOID) {
            self.ctx.approximate_length += 4;
            return Some(self.f.new_keyword_type_node(nodes, Kind::VoidKeyword));
        }
        if t_flags.intersects(TypeFlags::UNDEFINED) {
            self.ctx.approximate_length += 9;
            return Some(self.f.new_keyword_type_node(nodes, Kind::UndefinedKeyword));
        }
        if t_flags.intersects(TypeFlags::NULL) {
            self.ctx.approximate_length += 4;
            let lit = self.f.new_keyword_expression(nodes, Kind::NullKeyword);
            return Some(self.f.new_literal_type_node(nodes, Some(lit)));
        }
        if t_flags.intersects(TypeFlags::NEVER) {
            self.ctx.approximate_length += 5;
            return Some(self.f.new_keyword_type_node(nodes, Kind::NeverKeyword));
        }
        if t_flags.intersects(TypeFlags::ES_SYMBOL) {
            self.ctx.approximate_length += 6;
            return Some(self.f.new_keyword_type_node(nodes, Kind::SymbolKeyword));
        }
        if t_flags.intersects(TypeFlags::NON_PRIMITIVE) {
            self.ctx.approximate_length += 6;
            return Some(self.f.new_keyword_type_node(nodes, Kind::ObjectKeyword));
        }
        if is_this_type_parameter(&c.types, t) {
            if self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::IN_OBJECT_TYPE_LITERAL)
            {
                if !self.ctx.encountered_error
                    && !self
                        .ctx
                        .flags
                        .intersects(nodebuilder::Flags::ALLOW_THIS_IN_OBJECT_LITERAL)
                {
                    self.ctx.encountered_error = true;
                }
                if let Some(tracker) = self.ctx.tracker.clone() {
                    tracker.borrow_mut().report_inaccessible_this_error(nodes);
                }
            }
            self.ctx.approximate_length += 4;
            return Some(self.f.new_this_type_node(nodes));
        }

        if in_type_alias.is_empty()
            && let Some(alias) = type_alias(c, t)
            && (self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE)
                || alias.symbol().is_some_and(|sym| {
                    c.is_type_symbol_accessible(Some(sym), self.ctx.enclosing_declaration, Some(nodes))
                }))
        {
            // If we should expand this type alias, skip the alias and fall
            // through to expand the underlying type.
            if !self.should_expand_type(c, t, true /*isAlias*/) {
                let sym = alias.symbol();
                let type_argument_nodes = self.map_to_type_nodes(
                    c,
                    nodes,
                    alias.type_arguments(),
                    false, /*isBareList*/
                );
                if let Some(sym) = sym {
                    if is_reserved_member_name(&symbol_name(c, sym))
                        && !symbol_flags(c, sym).intersects(SymbolFlags::CLASS)
                    {
                        let empty = self.f.new_identifier(nodes, "");
                        return Some(self.f.new_type_reference_node(
                            nodes,
                            Some(empty),
                            type_argument_nodes,
                        ));
                    }
                    if let Some(type_argument_nodes) = &type_argument_nodes
                        && type_argument_nodes.nodes.len() == 1
                        && Some(sym) == c.types_handle().get(c.global_array_type).symbol
                    {
                        return Some(
                            self.f
                                .new_array_type_node(nodes, Some(type_argument_nodes.nodes[0])),
                        );
                    }
                    return self.symbol_to_type_node(
                        c,
                        nodes,
                        sym,
                        SymbolFlags::TYPE,
                        type_argument_nodes,
                    );
                }
            }
            // Expanding: increment depth and process the underlying type.
            self.ctx.depth += 1;
            let object_flags = type_object_flags(c, t);
            let result = self.type_to_type_node_dispatch_object(
                c,
                nodes,
                t,
                t_flags,
                object_flags,
                expanding_enum,
            );
            self.ctx.depth -= 1;
            return result;
        }

        let object_flags = type_object_flags(c, t);
        self.type_to_type_node_dispatch_object(c, nodes, t, t_flags, object_flags, expanding_enum)
    }

    /// The `objectFlags`-dispatch tail of `typeToTypeNode` — split out so the
    /// alias-expansion `defer` doesn't need a closure.
    fn type_to_type_node_dispatch_object(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        mut t: TypeId,
        t_flags: TypeFlags,
        object_flags: ObjectFlags,
        expanding_enum: bool,
    ) -> Option<NodeId> {
        if object_flags.intersects(ObjectFlags::REFERENCE) {
            // debug.Assert(t.flags & TypeFlagsObject != 0)
            // When expanding, expand type references to their structural
            // form.
            if self.should_expand_type(c, t, false /*isAlias*/) {
                self.ctx.depth += 1;
                let result = self.create_anonymous_type_node_ex(
                    c, nodes, t, true, /*forceClassExpansion*/ true, /*forceExpansion*/
                );
                self.ctx.depth -= 1;
                return Some(result);
            }
            if c.is_array_or_tuple_type(t) {
                return Some(self.visit_and_transform_type(
                    c,
                    nodes,
                    t,
                    NodeBuilderImpl::array_or_tuple_type_to_node,
                ));
            } else if c.types_handle().get(t).as_type_reference().node.is_some() {
                return Some(self.visit_and_transform_type(
                    c,
                    nodes,
                    t,
                    NodeBuilderImpl::type_reference_to_type_node,
                ));
            }
            return Some(self.type_reference_to_type_node(c, nodes, t));
        }
        if t_flags.intersects(TypeFlags::TYPE_PARAMETER)
            || object_flags.intersects(ObjectFlags::CLASS_OR_INTERFACE)
        {
            // When expanding class or interface types, show their structural
            // form.
            if object_flags.intersects(ObjectFlags::CLASS_OR_INTERFACE)
                && self.should_expand_type(c, t, false /*isAlias*/)
            {
                self.ctx.depth += 1;
                let result = self.create_anonymous_type_node_ex(c, nodes, t, true, true);
                self.ctx.depth -= 1;
                return Some(result);
            }
            if t_flags.intersects(TypeFlags::TYPE_PARAMETER)
                && self.ctx.infer_type_parameters.contains(&t)
            {
                self.ctx.approximate_length += type_symbol(c, t)
                    .map(|s| symbol_name(c, s).len() as i32)
                    .unwrap_or(0)
                    + 6;
                let mut constraint_node: Option<NodeId> = None;
                let constraint = c.get_constraint_of_type_parameter(t);
                if let Some(constraint) = constraint {
                    // If the infer type has a constraint that is not the same
                    // as the constraint we would have normally inferred based
                    // on b, we emit the constraint using `infer T extends ?`.
                    // We omit inferred constraints from type references as
                    // they may be elided.
                    let inferred_constraint = c.get_inferred_type_parameter_constraint(
                        t, true, /*omitTypeReferences*/
                    );
                    if !(inferred_constraint.is_some()
                        && c.is_type_identical_to(constraint, inferred_constraint.unwrap()))
                    {
                        self.ctx.approximate_length += 9;
                        constraint_node = Some(self.type_to_type_node(c, nodes, constraint));
                    }
                }
                let decl = self.type_parameter_to_declaration_with_constraint(
                    c,
                    nodes,
                    t,
                    constraint_node,
                );
                return Some(self.f.new_infer_type_node(nodes, Some(decl)));
            }
            if self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
                && t_flags.intersects(TypeFlags::TYPE_PARAMETER)
            {
                let name = self.type_parameter_to_name(c, nodes, t);
                let text = nodes[name].text(nodes).into_owned();
                self.ctx.approximate_length += text.len() as i32;
                let t_symbol = type_symbol(c, t);
                let id = self.new_identifier(nodes, &text, t_symbol);
                return Some(self.f.new_type_reference_node(nodes, Some(id), None));
            }
            // Ignore constraint/default when creating a usage (as opposed to
            // declaration) of a type parameter.
            if let Some(symbol) = type_symbol(c, t) {
                return self.symbol_to_type_node(c, nodes, symbol, SymbolFlags::TYPE, None);
            }
            let name = if (t == c.marker_super_type_for_check || t == c.marker_sub_type_for_check)
                && c.variance_type_parameter.is_some()
                && type_symbol(c, c.variance_type_parameter.unwrap()).is_some()
            {
                let prefix = if t == c.marker_sub_type_for_check {
                    "sub-"
                } else {
                    "super-"
                };
                format!(
                    "{}{}",
                    prefix,
                    symbol_name(
                        c,
                        type_symbol(c, c.variance_type_parameter.unwrap()).unwrap()
                    )
                )
            } else {
                "?".to_string()
            };
            let id = self.new_identifier(nodes, &name, None);
            return Some(self.f.new_type_reference_node(nodes, Some(id), None));
        }
        if t_flags.intersects(TypeFlags::UNION)
            && let Some(origin) = c.types_handle().get(t).as_union_type().origin
        {
            t = origin;
        }
        let mut t_flags = type_flags(c, t);
        let _ = &mut t_flags;
        if t_flags.intersects(TypeFlags::UNION | TypeFlags::INTERSECTION) {
            let types: Vec<TypeId> = if t_flags.intersects(TypeFlags::UNION) {
                let __arena_union_types = c.types.clone();
                let union_types = __arena_union_types
                    .get(t)
                    .as_union_type()
                    .union_or_intersection
                    .types
                    .clone();
                c.format_union_types(&union_types, expanding_enum)
            } else {
                c.types_handle()
                    .get(t)
                    .as_intersection_type()
                    .union_or_intersection
                    .types
                    .to_vec()
            };
            if types.len() == 1 {
                return Some(self.type_to_type_node(c, nodes, types[0]));
            }
            let type_nodes = self.map_to_type_nodes(c, nodes, &types, true /*isBareList*/);
            if let Some(type_nodes) = &type_nodes
                && !type_nodes.nodes.is_empty()
            {
                if t_flags.intersects(TypeFlags::UNION) {
                    return Some(self.f.new_union_type_node(nodes, Some(type_nodes.clone())));
                }
                return Some(
                    self.f
                        .new_intersection_type_node(nodes, Some(type_nodes.clone())),
                );
            }
            if !self.ctx.encountered_error
                && !self
                    .ctx
                    .flags
                    .intersects(nodebuilder::Flags::ALLOW_EMPTY_UNION_OR_INTERSECTION)
            {
                self.ctx.encountered_error = true;
            }
            return None;
            // TODO: GH#18217
        }
        let object_flags = type_object_flags(c, t);
        if object_flags.intersects(ObjectFlags::ANONYMOUS | ObjectFlags::MAPPED) {
            // debug.Assert(t.flags & TypeFlagsObject != 0)
            // The type is an object literal type.
            return Some(self.create_anonymous_type_node(c, nodes, t));
        }
        if t_flags.intersects(TypeFlags::INDEX) {
            let __arena_indexed_type = c.types.clone();
            let indexed_type = __arena_indexed_type.get(t).as_index_type().target;
            self.ctx.approximate_length += 6;
            let index_type_node =
                self.type_to_type_node(c, nodes, indexed_type.unwrap_or(c.error_type));
            return Some(self.f.new_type_operator_node(
                nodes,
                Kind::KeyOfKeyword,
                Some(index_type_node),
            ));
        }
        if t_flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            let (texts, types_) = {
                let __arena_t_guard = c.types.clone();
                let t_guard = __arena_t_guard.get(t);
                let tlt = t_guard.as_template_literal_type();
                (tlt.texts.clone(), tlt.types.clone())
            };
            let template_head =
                self.f
                    .new_template_head(nodes, &texts[0], "", ast::TokenFlags::NONE);
            self.e
                .borrow()
                .add_emit_flags(template_head, printer::EmitFlags::NO_ASCII_ESCAPING);
            let mut span_nodes: Vec<NodeId> = Vec::new();
            for (i, &t_) in types_.iter().enumerate() {
                let res = if i < types_.len() - 1 {
                    self.f
                        .new_template_middle(nodes, &texts[i + 1], "", ast::TokenFlags::NONE)
                } else {
                    self.f
                        .new_template_tail(nodes, &texts[i + 1], "", ast::TokenFlags::NONE)
                };
                self.e
                    .borrow()
                    .add_emit_flags(res, printer::EmitFlags::NO_ASCII_ESCAPING);
                let span_type = self.type_to_type_node(c, nodes, t_);
                span_nodes.push(self.f.new_template_literal_type_span(
                    nodes,
                    Some(span_type),
                    Some(res),
                ));
            }
            let template_spans = self.f.new_node_list(span_nodes);
            self.ctx.approximate_length += 2;
            return Some(self.f.new_template_literal_type_node(
                nodes,
                Some(template_head),
                Some(template_spans),
            ));
        }
        if t_flags.intersects(TypeFlags::STRING_MAPPING) {
            let __arena_target = c.types.clone();
            let target = __arena_target.get(t).as_string_mapping_type().target;
            let type_node = self.type_to_type_node(c, nodes, target.unwrap_or(c.error_type));
            let __arena_symbol = c.types.clone();
            let symbol = __arena_symbol.get(t).symbol;
            let args = self.f.new_node_list([type_node]);
            return symbol.and_then(|s| {
                self.symbol_to_type_node(c, nodes, s, SymbolFlags::TYPE, Some(args))
            });
        }
        if t_flags.intersects(TypeFlags::INDEXED_ACCESS) {
            let (object_type, index_type) = {
                let __arena_t_guard = c.types.clone();
                let t_guard = __arena_t_guard.get(t);
                let iat = t_guard.as_indexed_access_type();
                (iat.object_type, iat.index_type)
            };
            let object_type_node =
                self.type_to_type_node(c, nodes, object_type.unwrap_or(c.error_type));
            let index_type_node =
                self.type_to_type_node(c, nodes, index_type.unwrap_or(c.error_type));
            self.ctx.approximate_length += 2;
            return Some(self.f.new_indexed_access_type_node(
                nodes,
                Some(object_type_node),
                Some(index_type_node),
            ));
        }
        if t_flags.intersects(TypeFlags::CONDITIONAL) {
            return Some(self.visit_and_transform_type(
                c,
                nodes,
                t,
                NodeBuilderImpl::conditional_type_to_type_node,
            ));
        }
        if t_flags.intersects(TypeFlags::SUBSTITUTION) {
            let __arena_base_type = c.types.clone();
            let base_type = __arena_base_type.get(t).as_substitution_type().base_type;
            let type_node = self.type_to_type_node(c, nodes, base_type.unwrap_or(c.error_type));
            if !c.is_no_infer_type(t) {
                return Some(type_node);
            }
            let no_infer_symbol = c.get_global_type_alias_symbol("NoInfer", 1, false);
            if let Some(no_infer_symbol) = no_infer_symbol {
                let args = self.f.new_node_list([type_node]);
                return self.symbol_to_type_node(
                    c,
                    nodes,
                    no_infer_symbol,
                    SymbolFlags::TYPE,
                    Some(args),
                );
            }
            return Some(type_node);
        }

        panic!("Should be unreachable.")
    }

    /// `(b *NodeBuilderImpl) newStringLiteral`.
    pub fn new_string_literal(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        text: &str,
    ) -> NodeId {
        let _ = c;
        self.new_string_literal_ex(c, nodes, text, false /*isSingleQuote*/)
    }

    /// `(b *NodeBuilderImpl) newStringLiteralEx`.
    pub fn new_string_literal_ex(
        &mut self,
        _c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        text: &str,
        is_single_quote: bool,
    ) -> NodeId {
        let mut flags = ast::TokenFlags::NONE;
        if is_single_quote
            || self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE)
        {
            flags |= ast::TokenFlags::SINGLE_QUOTE;
        }
        self.f.new_string_literal(nodes, text, flags)
    }

    /// `(b *NodeBuilderImpl) newIdentifier`.
    pub fn new_identifier(
        &mut self,
        nodes: &mut Vec<ast::Node>,
        text: &str,
        symbol: Option<SymbolId>,
    ) -> NodeId {
        let id = self.f.new_identifier(nodes, text);
        if let Some(symbol) = symbol {
            self.id_to_symbol.insert(id, symbol);
        }
        id
    }

    /// `(b *NodeBuilderImpl) createAccessExpression`.
    fn create_access_expression(&mut self, nodes: &mut Vec<ast::Node>, node: NodeId) -> NodeId {
        if ast::is_qualified_name(&nodes[node]) {
            let (left, right) = {
                let q = nodes[node].as_qualified_name();
                (q.left, q.right)
            };
            let left_expr = self.create_access_expression(nodes, left.unwrap_or(NodeId::NONE));
            let right_clone = right
                .and_then(|r| self.f.deep_clone_node(nodes, r))
                .unwrap_or(NodeId::NONE);
            self.f.new_property_access_expression(
                nodes,
                Some(left_expr),
                None, // questionDotToken
                Some(right_clone),
                ast::NodeFlags::NONE,
            )
        } else if ast::is_identifier(&nodes[node])
            || ast::is_property_access_expression(&nodes[node])
            || ast::is_expression_with_type_arguments(&nodes[node])
        {
            self.f.deep_clone_node(nodes, node).unwrap_or(node)
        } else {
            panic!("unexpected access node kind: {:?}", nodes[node].kind)
        }
    }

    /// `(b *NodeBuilderImpl) createExpressionWithTypeArguments`.
    fn create_expression_with_type_arguments(
        &mut self,
        nodes: &mut Vec<ast::Node>,
        expr: NodeId,
        type_arguments: Option<NodeList>,
    ) -> NodeId {
        if type_arguments.as_ref().is_none_or(|t| t.nodes.is_empty()) {
            return expr;
        }
        self.f
            .new_expression_with_type_arguments(nodes, Some(expr), type_arguments)
    }

    /// `(b *NodeBuilderImpl) lookupInstantiatedTypeArgumentNodes`.
    fn lookup_instantiated_type_argument_nodes(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        chain: &[SymbolId],
        index: usize,
    ) -> Option<NodeList> {
        if self.should_write_type_parameters_in_qualified_name(chain, index) {
            let symbol = chain[index];
            let next_symbol = chain[index + 1];
            if !symbol_check_flags(c, next_symbol)
                .intersects(ast::checkflags::CheckFlags::INSTANTIATED)
            {
                return None;
            }

            let mut target_symbol = symbol;
            if symbol_flags(c, symbol).intersects(SymbolFlags::ALIAS)
                && !c.can_get_type_parameters_of_class_or_interface(symbol, nodes)
            {
                target_symbol = c.resolve_alias(symbol);
            }

            if !c.can_get_type_parameters_of_class_or_interface(target_symbol, nodes) {
                return None;
            }

            let params = self.get_type_parameters_of_class_or_interface(c, nodes, target_symbol);
            let target_mapper = if c.value_symbol_links.has(next_symbol) {
                c.value_symbol_links.get(next_symbol).mapper
            } else {
                None
            };
            let params = if let Some(mapper) = target_mapper {
                params
                    .iter()
                    .map(|&p| c.instantiate_type(p, Some(mapper)))
                    .collect()
            } else {
                params
            };
            return self.map_to_type_nodes(c, nodes, &params, false /*isBareList*/);
        }
        None
    }

    /// `(b *NodeBuilderImpl) lookupExpressionChainTypeArgumentNodes`.
    fn lookup_expression_chain_type_argument_nodes(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        chain: &[SymbolId],
        index: usize,
    ) -> Option<NodeList> {
        if self.should_write_type_parameters_in_qualified_name(chain, index) {
            let symbol = chain[index];
            if self.ctx.type_parameter_symbol_list.has(&symbol) {
                return None;
            }

            self.ctx.type_parameter_symbol_list.add(symbol);
            if let Some(type_argument_nodes) =
                self.lookup_instantiated_type_argument_nodes(c, nodes, chain, index)
            {
                return Some(type_argument_nodes);
            }
            let type_parameter_nodes =
                self.type_parameters_to_type_parameter_declarations(c, nodes, symbol);
            if !type_parameter_nodes.is_empty() {
                return Some(self.f.new_node_list(type_parameter_nodes));
            }
        }
        None
    }

    /// `(b *NodeBuilderImpl) shouldWriteTypeParametersInQualifiedName`.
    fn should_write_type_parameters_in_qualified_name(
        &self,
        chain: &[SymbolId],
        index: usize,
    ) -> bool {
        self.ctx
            .flags
            .intersects(nodebuilder::Flags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME)
            && index + 1 < chain.len()
    }
}

/// `getTopmostIndexedAccessType`.
fn get_topmost_indexed_access_type(nodes: &[ast::Node], node: NodeId) -> NodeId {
    if let Some(object_type) = nodes[node].as_indexed_access_type_node().object_type
        && ast::is_indexed_access_type_node(&nodes[object_type])
    {
        return get_topmost_indexed_access_type(nodes, object_type);
    }
    node
}

/// `getAccessStack` — collects the trailing identifiers of a qualified name
/// chain, rightmost-first order restored to left-to-right. PORT: shared by
/// `append_reference_to_type` (Go's helper is file-local).
///
/// PORT: Go starts at `ref.AsTypeReferenceNode().TypeName` — the stack is
/// built from the *name* of the reference, not the reference node itself.
fn get_access_stack(nodes: &[ast::Node], node: NodeId) -> Vec<NodeId> {
    let mut stack = Vec::new();
    let mut current = match nodes[node].kind {
        Kind::TypeReference => nodes[node]
            .as_type_reference_node()
            .type_name
            .unwrap_or(NodeId::NONE),
        _ => node,
    };
    loop {
        match nodes[current].kind {
            Kind::QualifiedName => {
                let q = nodes[current].as_qualified_name();
                stack.push(q.right.unwrap_or(NodeId::NONE));
                if let Some(left) = q.left {
                    current = left;
                    continue;
                }
                break;
            }
            Kind::PropertyAccessExpression => {
                let p = nodes[current].as_property_access_expression();
                if let Some(name) = p.name {
                    stack.push(name);
                }
                if let Some(expr) = p.expression {
                    current = expr;
                    continue;
                }
                break;
            }
            Kind::Identifier => {
                stack.push(current);
                break;
            }
            _ => break,
        }
    }
    // The walk collects right-to-left; Go's `prepend` order yields
    // left-to-right — the order callers apply when extending the name.
    stack.reverse();
    stack
}

/// `isIdentifierTypeReference`.
fn is_identifier_type_reference(nodes: &[ast::Node], node: NodeId) -> bool {
    ast::is_type_reference_node(&nodes[node])
        && nodes[node]
            .as_type_reference_node()
            .type_name
            .is_some_and(|n| ast::is_identifier(&nodes[n]))
}

/// `arrayIsHomogeneous`.
fn array_is_homogeneous<T: Copy>(array: &[T], comparer: impl Fn(T, T) -> bool) -> bool {
    if array.len() < 2 {
        return true;
    }
    let first = array[0];
    array[1..].iter().all(|&target| comparer(first, target))
}

/// `typesAreSameReference`.
fn types_are_same_reference(c: &Checker, a: TypeId, b: TypeId) -> bool {
    if a == b {
        return true;
    }
    let (a_sym, b_sym) = (type_symbol(c, a), type_symbol(c, b));
    if a_sym.is_some() && a_sym == b_sym {
        return true;
    }
    let (a_alias, b_alias) = (type_alias(c, a), type_alias(c, b));
    a_alias.is_some() && a_alias.and_then(|al| al.symbol) == b_alias.and_then(|al| al.symbol)
}

// `isExpanding` (nodebuilder_hover.go:16) lives in `nodebuilder_hover.rs` —
// `crate::nodebuilder_hover::is_expanding`.

/// `isReservedMemberName` (utilities.go:1677) — a reserved member name
/// consists of the byte 0xFE (invalid UTF-8 start) followed by one or more
/// characters where the first is not `@` or `#`. PORT: file-local until
/// utilities.go's copy lands.
fn is_reserved_member_name(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some('\u{FFFD}'))
        && matches!(chars.next(), Some(c) if c != '@' && c != '#')
}

/// `IsPrivateIdentifierSymbol` (utilities.go:1022). PORT: file-local until
/// utilities.go's copy lands.
fn is_private_identifier_symbol(c: &Checker, symbol: SymbolId) -> bool {
    if symbol == SymbolId::NONE {
        return false;
    }
    c.symbol_arena.get_ref(symbol)
        .name
        .starts_with(&(ast::symbol::INTERNAL_SYMBOL_NAME_PREFIX.to_string() + "#"))
}

/// `containsNonMissingUndefinedType` (utilities.go:1647). PORT: file-local
/// until utilities.go's copy lands.
fn contains_non_missing_undefined_type(c: &Checker, t: TypeId) -> bool {
    let candidate = if type_flags(c, t).intersects(TypeFlags::UNION) {
        c.types_handle()
            .get(t)
            .as_union_type()
            .union_or_intersection
            .types
            .first()
            .copied()
            .unwrap_or(t)
    } else {
        t
    };
    type_flags(c, candidate).intersects(TypeFlags::UNDEFINED) && candidate != c.missing_type
}

/// `signatureHasRestParameter` (checker.go). PORT: file-local; checker_c.rs
/// declares its own copy.
fn signature_has_rest_parameter(c: &Checker, sig: SignatureId) -> bool {
    c.signature_arena
        .get(sig)
        .flags
        .intersects(SignatureFlags::HAS_REST_PARAMETER)
}

/// `isRestParameter` (checker.go).
fn is_rest_parameter(nodes: &[ast::Node], param: NodeId) -> bool {
    nodes[param]
        .as_parameter_declaration()
        .dot_dot_dot_token
        .is_some()
}

/// `getNameFromIndexInfo` (checker.go).
fn get_name_from_index_info(c: &Checker, info: IndexInfoId,
        nodes: &[ast::Node],) -> String {
    if let Some(declaration) = c.index_info_arena.get(info).declaration {
        let __program = c.program.clone().expect("program");
        let nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
        if let Some(first_param) = nodes[declaration].parameters().and_then(|l| l.first()) {
            return scanner::utilities::declaration_name_to_string(
                nodes[*first_param].name(),
                &nodes,
            );
        }
    }
    "x".to_string()
}

/// `getMappedTypeModifiers` (checker.go:29541) — PORT: file-local copy;
/// checker_d.rs's copy is module-private.
fn get_mapped_type_modifiers_local(c: &Checker, t: TypeId,
        nodes: &[ast::Node],) -> MappedTypeModifiers {
    let Some(declaration) = c.types_handle().get(t).as_mapped_type().declaration else {
        return MappedTypeModifiers::NONE;
    };
    let __program = c.program.clone().expect("program");
    let nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
    let declaration = &nodes[declaration];
    let mut modifiers = MappedTypeModifiers::NONE;
    if let Some(readonly_token) = declaration.as_mapped_type_node().readonly_token {
        modifiers |= if nodes[readonly_token].kind == Kind::MinusToken {
            MappedTypeModifiers::EXCLUDE_READONLY
        } else {
            MappedTypeModifiers::INCLUDE_READONLY
        };
    }
    if let Some(question_token) = declaration.as_mapped_type_node().question_token {
        modifiers |= if nodes[question_token].kind == Kind::MinusToken {
            MappedTypeModifiers::EXCLUDE_OPTIONAL
        } else {
            MappedTypeModifiers::INCLUDE_OPTIONAL
        };
    }
    modifiers
}

/// `c.getTargetSymbol` (checker.go:22087) — if the symbol is instantiated
/// its flags are not copied from the 'target', so get the original target
/// symbol to work with the correct set of flags. PORT: file-local until
/// checker.go's copy lands.
pub(crate) fn get_target_symbol(c: &mut Checker, s: SymbolId) -> SymbolId {
    c.get_target_symbol(s)
}

/// `c.getRegularTypeOfExpression` (checker.go:32668). PORT: file-local until
/// checker.go's copy lands.
fn get_regular_type_of_expression(c: &mut Checker, expr: NodeId,
        nodes: &[ast::Node],) -> TypeId {
    let mut expr = expr;
    let __program = c.program.clone().expect("program");
    let nodes = crate::printer_util::arena_view(&__program, nodes, (expr).file_index());
    if ast::is_right_side_of_qualified_name_or_property_access(expr, &nodes) {
        if let Some(parent) = nodes[expr].parent {
            expr = parent;
        }
    }
    let t = c.get_type_of_expression(expr);
    c.get_regular_type_of_literal_type(t)
}

/// Shared state for the `cloneBindingName` visitor — the `b`/`c` pieces the
/// per-node visit fn needs, routed through cells since `VisitFn` is `Fn`
/// (not `FnMut`) and `cx.factory` already borrows `self.f`.
struct CloneBindingShared<'s, 'x, 't> {
    /// `b.ch` — `RefCell` so the `Fn` visit fn can call `&mut` methods.
    c: &'s RefCell<&'x mut Checker>,
    /// `b.ctx.tracker`.
    tracker: Option<Rc<RefCell<dyn nodebuilder::SymbolTracker + 't>>>,
    /// `b.ctx.enclosingDeclaration`.
    enclosing_declaration: Option<NodeId>,
    /// `b.e`.
    e: Rc<RefCell<EmitContext>>,
}

/// `(b *NodeBuilderImpl) trackComputedName` on shared state — the visit-fn
/// path. `track_computed_name` (method) wraps this for direct callers.
fn track_computed_name_shared(
    shared: &CloneBindingShared<'_, '_, '_>,
    nodes: &[ast::Node],
    access_expression: NodeId,
) {
    // get symbol of the first identifier of the entityName
    let first_identifier = ast::get_first_identifier(access_expression, nodes);
    let text = nodes[first_identifier].text(nodes).into_owned();
    let mut cm = shared.c.borrow_mut();
    let name = cm.resolve_name_via_binder_live(
        shared.enclosing_declaration,
        &text,
        ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE,
        None,
        true, // isUse
        false,
        Some(nodes),
    );
    let tracked = if let Some(name) = name {
        Some(name)
    } else {
        // Name does not resolve at target location, track symbol at dest
        // location (should be inaccessible)
        cm.resolve_name_via_binder_live(
            Some(first_identifier),
            &text,
            ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE,
            None,
            true,
            false,
            Some(nodes),
        )
    };
    drop(cm);
    if let Some(tracked) = tracked
        && let Some(tracker) = &shared.tracker
    {
        tracker.borrow_mut().track_symbol(
            tracked,
            shared.enclosing_declaration,
            ast::SymbolFlags::VALUE,
            nodes,
            &mut |sym, en, mn, sc| {
                shared
                    .c
                    .borrow_mut()
                    .is_symbol_accessible(sym, en, mn, sc, Some(nodes))
            },
        );
    }
}

/// The `cloneBindingName` visit fn — the body of Go's `cloneBindingName`
/// applied per visited node.
fn clone_binding_name_visit(
    shared: &CloneBindingShared<'_, '_, '_>,
    v: &ast::visitor::NodeVisitor,
    cx: &mut ast::visitor::VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    if ast::is_computed_property_name(&cx.nodes[node])
        && shared.c.borrow_mut().is_late_bindable_name(node)
        && let Some(expr) = cx.nodes[node].expression()
    {
        track_computed_name_shared(shared, cx.nodes, expr);
    }

    let visited = v.visit_each_child(cx, node).unwrap_or(node);

    let visited = if ast::is_binding_element(&cx.nodes[visited]) {
        let (dot_dot_dot, property_name, name) = {
            let binding_element = cx.nodes[visited].as_binding_element();
            (
                binding_element.dot_dot_dot_token,
                binding_element.property_name,
                binding_element.name,
            )
        };
        cx.factory
            .update_binding_element(
                cx.nodes,
                visited,
                dot_dot_dot,
                property_name,
                name,
                None, // remove initializer
            )
            .unwrap_or(visited)
    } else {
        visited
    };

    let visited = if !ast::node_is_synthesized(&cx.nodes[visited]) {
        cx.factory
            .deep_clone_node(cx.nodes, visited)
            .unwrap_or(visited)
    } else {
        visited
    };

    shared.e.borrow().set_emit_flags(
        visited,
        printer::EmitFlags::SINGLE_LINE | printer::EmitFlags::NO_ASCII_ESCAPING,
    );
    visited
}

/// `canUsePropertyAccess`.
fn can_use_property_access(name: &str) -> bool {
    if name.is_empty() {
        return false;
    }
    // TODO: in strada, this only used `isIdentifierStart` on the first
    // character, while this checks the whole string for validity - possible
    // strada bug?
    if let Some(rest) = name.strip_prefix('#') {
        return !rest.is_empty()
            && scanner::utilities::is_identifier_text(rest, LanguageVariant::Standard);
    }
    scanner::utilities::is_identifier_text(name, LanguageVariant::Standard)
}

/// `startsWithSingleOrDoubleQuote`.
fn starts_with_single_or_double_quote(str_: &str) -> bool {
    str_.starts_with('\'') || str_.starts_with('"')
}

/// `startsWithSquareBracket`.
fn starts_with_square_bracket(str_: &str) -> bool {
    str_.starts_with('[')
}

/// `isDefaultBindingContext`.
fn is_default_binding_context(node: &ast::Node, nodes: &[ast::Node]) -> bool {
    node.kind == Kind::SourceFile || ast::is_ambient_module(node, nodes)
}

/// `sortedSymbolNamePair`.
struct SortedSymbolNamePair {
    sym: SymbolId,
    name: String,
}

/// `canHaveModuleSpecifier`.
fn can_have_module_specifier(node: &ast::Node) -> bool {
    matches!(
        node.kind,
        Kind::VariableDeclaration
            | Kind::BindingElement
            | Kind::ImportDeclaration
            | Kind::ExportDeclaration
            | Kind::ImportEqualsDeclaration
            | Kind::ImportClause
            | Kind::NamespaceExport
            | Kind::NamespaceImport
            | Kind::ExportSpecifier
            | Kind::ImportSpecifier
            | Kind::ImportType
    )
}

/// `TryGetModuleSpecifierFromDeclaration`.
pub fn try_get_module_specifier_from_declaration(
    node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    let res = try_get_module_specifier_from_declaration_worker(node, nodes)?;
    if !ast::is_string_literal(&nodes[res]) {
        return None;
    }
    Some(res)
}

/// `tryGetModuleSpecifierFromDeclarationWorker`.
fn try_get_module_specifier_from_declaration_worker(
    node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    match nodes[node].kind {
        Kind::VariableDeclaration | Kind::BindingElement => {
            let module_call =
                ast::find_ancestor(nodes[node].initializer(), nodes, &mut |n, nodes| {
                    ast::is_require_call(n, true, nodes) || ast::is_import_call(n, nodes)
                })?;
            nodes[module_call]
                .arguments()
                .and_then(|args| args.first().copied())
        }
        Kind::ImportDeclaration | Kind::ExportDeclaration | Kind::JSDocImportTag => {
            nodes[node].module_specifier()
        }
        Kind::ImportEqualsDeclaration => {
            let ref_ = nodes[node]
                .as_import_equals_declaration()
                .module_reference?;
            if nodes[ref_].kind != Kind::ExternalModuleReference {
                return None;
            }
            nodes[ref_].expression()
        }
        Kind::ImportClause => nodes[node].parent.and_then(|p| nodes[p].module_specifier()),
        Kind::NamespaceExport => nodes[node].parent.and_then(|p| nodes[p].module_specifier()),
        Kind::NamespaceImport => nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .and_then(|p| nodes[p].module_specifier()),
        Kind::ExportSpecifier => nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .and_then(|p| nodes[p].module_specifier()),
        Kind::ImportSpecifier => nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .and_then(|p| nodes[p].parent)
            .and_then(|p| nodes[p].module_specifier()),
        Kind::ImportType => {
            if ast::is_literal_import_type_node(&nodes[node], nodes) {
                nodes[node]
                    .as_import_type_node()
                    .argument
                    .and_then(|arg| nodes[arg].as_literal_type_node().literal)
            } else {
                None
            }
        }
        _ => unreachable!("can_have_module_specifier guards this"),
    }
}

/// `ast.GetDeclarationOfKind` on a `SymbolId` — the Go helper dereferences
/// `symbol.Declarations` through the global heap; here each declaration is
/// read through its own file's arena via `program_nodes`.
fn get_declaration_of_kind_of_symbol(c: &Checker, symbol: SymbolId, kind: Kind,
        nodes: &[ast::Node],) -> Option<NodeId> {
    symbol_declarations(c, symbol)
        .iter()
        .copied()
        .find(|&d| c.program_nodes_live(d, nodes)[d].kind == kind)
}

/// `ast.GetSourceFileOfModule` on a `SymbolId` — Go walks
/// `value_declaration`/`GetNonAugmentationDeclaration` then
/// `GetSourceFileOfNode`; each step here routes through `program_nodes`.
fn get_source_file_of_module_symbol(c: &Checker, symbol: SymbolId,
        nodes: &[ast::Node],) -> Option<NodeId> {
    let (value_declaration, declarations) = {
        let arena = c.symbol_arena.clone();
        let s = &arena[symbol.index()];
        (s.value_declaration, s.declarations.clone())
    };
    let declaration = value_declaration.or_else(|| {
        // `GetNonAugmentationDeclaration`.
        declarations.iter().copied().find(|&d| {
            let __program = c.program.clone().expect("program");
            let dn = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
            !ast::is_external_module_augmentation(&dn[d], &dn)
                && !ast::is_global_scope_augmentation(&dn[d])
        })
    });
    declaration.and_then(|d| ast::get_source_file_of_node(Some(d), &c.program_nodes_live(d, nodes)))
}

/// `HostAdapter` — bridges `Rc<dyn Host>` (the checker `Program` trait
/// object, which is the nodebuilder `host`) to the concrete
/// `ModuleSpecifierGenerationHost` generic parameter required by
/// `tsc_modulespecifiers::get_module_specifiers` (its `H` bound is not
/// `?Sized`, so `&dyn Host` can't be passed directly).
pub(crate) struct HostAdapter(pub Rc<dyn Host>);

impl tsc_outputpaths::OutputPathsHost for HostAdapter {
    fn common_source_directory(&self) -> tsc_tspath::RootedDirectoryPath {
        self.0.common_source_directory()
    }
    fn content_mapper_extensions(&self) -> &[String] {
        self.0.content_mapper_extensions()
    }
    fn case_sensitivity(&self) -> tsc_tspath::CaseSensitivity {
        self.0.case_sensitivity()
    }
}

impl tsc_modulespecifiers::ModuleSpecifierGenerationHost for HostAdapter {
    fn get_symlink_cache(&self) -> Option<&tsc_symlinks::KnownSymlinks> {
        self.0.get_symlink_cache()
    }
    fn get_global_typings_cache_location(&self) -> tsc_tspath::RootedDirectoryPath {
        self.0.get_global_typings_cache_location()
    }
    fn base_directory(&self) -> tsc_tspath::RootedDirectoryPath {
        self.0.base_directory()
    }
    fn get_project_reference_from_source(
        &self,
        path: &tsc_tspath::PathKey,
    ) -> Option<std::sync::Arc<tsc_tsoptions::parsedcommandline::SourceOutputAndProjectReference>>
    {
        self.0.get_project_reference_from_source(path)
    }
    fn get_redirect_targets(&self, path: &tsc_tspath::PathKey) -> Vec<tsc_tspath::RootedFilePath> {
        self.0.get_redirect_targets(path)
    }
    fn get_source_of_project_reference_if_output_included(
        &self,
        file: &dyn ast::HasFileName,
    ) -> tsc_tspath::RootedFilePath {
        self.0
            .get_source_of_project_reference_if_output_included(file)
    }
    fn file_exists(&self, path: &tsc_tspath::RootedFilePath) -> bool {
        self.0.file_exists(path)
    }
    fn get_nearest_ancestor_directory_with_package_json(
        &self,
        dirname: &tsc_tspath::RootedDirectoryPath,
    ) -> tsc_tspath::RootedDirectoryPath {
        self.0
            .get_nearest_ancestor_directory_with_package_json(dirname)
    }
    fn get_package_json_info(
        &self,
        pkg_json_path: &tsc_tspath::RootedFilePath,
    ) -> Option<std::sync::Arc<tsc_packagejson::InfoCacheEntry>> {
        self.0.get_package_json_info(pkg_json_path)
    }
    fn get_default_resolution_mode_for_file(&self, file: &dyn ast::HasFileName) -> ResolutionMode {
        self.0.get_default_resolution_mode_for_file(file)
    }
    fn get_resolved_module_from_module_specifier(
        &self,
        file: &dyn ast::HasFileName,
        module_specifier: NodeId,
    ) -> Option<tsc_module::ResolvedModule> {
        self.0
            .get_resolved_module_from_module_specifier(file, module_specifier)
    }
    fn get_mode_for_usage_location(
        &self,
        file: &dyn ast::HasFileName,
        module_specifier: NodeId,
    ) -> ResolutionMode {
        self.0.get_mode_for_usage_location(file, module_specifier)
    }
}

/// `CheckerShapeAdapter` — `tsc_modulespecifiers::CheckerShape` requires
/// `&self` methods, but `Checker::get_symbol_at_location` / `resolve_alias`
/// take `&mut self` (checker mutation). The adapter holds the checker in a
/// `RefCell` so the `&self` trait methods can reborrow `&mut` per call.
pub(crate) struct CheckerShapeAdapter<'a> {
    pub c: RefCell<&'a mut Checker>,
}

impl<'a> CheckerShapeAdapter<'a> {
    pub fn new(c: &'a mut Checker) -> Self {
        CheckerShapeAdapter { c: RefCell::new(c) }
    }
}

impl tsc_modulespecifiers::CheckerShape for CheckerShapeAdapter<'_> {
    fn get_symbol_at_location(&self, node: NodeId) -> Option<SymbolId> {
        // `Checker::get_symbol_at_location` (checker_d.rs) takes `&mut self`;
        // the trait requires `&self`, so route through the RefCell.
        // Go `getSymbolAtLocation(node)` in this context uses `ignoreErrors=true`.
        self.c.borrow_mut().get_symbol_at_location(node, true)
    }
    fn get_aliased_symbol(&self, symbol: SymbolId) -> SymbolId {
        self.c.borrow_mut().resolve_alias(symbol)
    }
}

/// `SignatureToSignatureDeclarationOptions` — Go's `options` pointer becomes
/// `Option`-wrapped fields on a `Copy` struct.
#[derive(Clone, Default)]
pub struct SignatureToSignatureDeclarationOptions {
    /// `modifiers` — `[]*ast.Node` → `Vec<NodeId>`.
    pub modifiers: Vec<NodeId>,
    /// `name` — `*ast.PropertyName`.
    pub name: Option<NodeId>,
    /// `questionToken`.
    pub question_token: Option<NodeId>,
}

/// `propertyNameNodeKind`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum PropertyNameNodeKind {
    /// `propertyNameNodeKindIdentifier`.
    Identifier,
    /// `propertyNameNodeKindNumericLiteral`.
    NumericLiteral,
    /// `propertyNameNodeKindStringLiteral`.
    StringLiteral,
}

/// `classifyPropertyName`.
pub(crate) fn classify_property_name(
    name: &str,
    string_named: bool,
    is_method: bool,
) -> PropertyNameNodeKind {
    if is_method && name == "new" {
        return PropertyNameNodeKind::StringLiteral;
    }
    if scanner::utilities::is_identifier_text(name, LanguageVariant::Standard) {
        return PropertyNameNodeKind::Identifier;
    }
    if !string_named
        && crate::utilities::is_numeric_literal_name(name)
        && jsnum::from_string(name).0 >= 0.0
    {
        PropertyNameNodeKind::NumericLiteral
    } else {
        PropertyNameNodeKind::StringLiteral
    }
}

/// `hasTypeAnnotation`.
fn has_type_annotation(declaration: NodeId, nodes: &[ast::Node]) -> bool {
    if declaration.is_none() || nodes[declaration].type_().is_none() {
        return false;
    }
    // Type alias declarations have a `.Type()` that is their type
    // definition, not a type annotation on a value. Exclude them so callers
    // don't mistake them for annotated value declarations.
    if ast::is_type_alias_declaration(&nodes[declaration])
        || ast::is_js_type_alias_declaration(&nodes[declaration])
    {
        return false;
    }
    true
}

/// `getTypeAliasForTypeLiteral`.
fn get_type_alias_for_type_literal(c: &mut Checker, t: TypeId,
        nodes: &[ast::Node],) -> Option<SymbolId> {
    let symbol = type_symbol(c, t);
    if let Some(symbol) = symbol
        && symbol_flags(c, symbol).intersects(SymbolFlags::TYPE_LITERAL)
    {
        let declarations = symbol_declarations(c, symbol);
        if let Some(&decl) = declarations.first() {
            let __program = c.program.clone().expect("program");
            let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (decl).file_index());
            let node = decl_nodes[decl]
                .parent
                .and_then(|p| ast::walk_up_parenthesized_types(p, &decl_nodes));
            if node.is_some_and(|n| ast::is_type_alias_declaration(&decl_nodes[n])) {
                return c.get_symbol_of_declaration(node.unwrap());
            }
        }
    }
    None
}

/// `isClassInstanceSide`.
fn is_class_instance_side(c: &mut Checker, t: TypeId) -> bool {
    let Some(symbol) = type_symbol(c, t) else {
        return false;
    };
    if !symbol_flags(c, symbol).intersects(SymbolFlags::CLASS) {
        return false;
    }
    let declared = c.get_declared_type_of_class_or_interface(symbol);
    t == declared
        || (type_flags(c, t).intersects(TypeFlags::OBJECT)
            && type_object_flags(c, t).intersects(ObjectFlags::IS_CLASS_INSTANCE_CLONE))
}

/// `getEffectiveParameterDeclaration`.
fn get_effective_parameter_declaration(c: &Checker, symbol: SymbolId,
        nodes: &[ast::Node],) -> Option<NodeId> {
    if let Some(decl) = get_declaration_of_kind_of_symbol(c, symbol, Kind::Parameter, nodes) {
        return Some(decl);
    }
    if !symbol_flags(c, symbol).intersects(SymbolFlags::TRANSIENT) {
        return get_declaration_of_kind_of_symbol(c, symbol, Kind::JSDocParameterTag, nodes);
    }
    None
}

/// `getNameFromIndexInfo` on an `&IndexInfo` value (the resolved type's
/// `indexInfos` are values, not interned ids — see `get_name_from_index_info`
/// for the interned form).
fn get_name_from_index_info_data(c: &Checker, index_info: &IndexInfo,
        nodes: &[ast::Node],) -> String {
    if let Some(declaration) = index_info.declaration {
        let __program = c.program.clone().expect("program");
        let decl_nodes = crate::printer_util::arena_view(&__program, nodes, (declaration).file_index());
        if let Some(first_param) = decl_nodes[declaration].parameters().and_then(|l| l.first()) {
            return scanner::utilities::declaration_name_to_string(
                decl_nodes[*first_param].name(),
                &decl_nodes,
            );
        }
    }
    "x".to_string()
}

/// `(t *TypeAlias) ToTypeReferenceNode` — free fn since `TypeAlias` is a
/// value type (not an id into a `b`-owned arena).
fn alias_to_type_reference_node(
    b: &mut NodeBuilderImpl<'_>,
    c: &mut Checker,
    nodes: &mut Vec<ast::Node>,
    alias: &TypeAlias,
) -> NodeId {
    let entity = alias
        .symbol()
        .and_then(|s| b.symbol_to_entity_name_node(c, nodes, s));
    let args = b.map_to_type_nodes(c, nodes, alias.type_arguments(), false /*isBareList*/);
    b.f.new_type_reference_node(nodes, entity, args)
}

/// `t.flags & TypeFlagsUndefined == 0` — the `filter_type` predicate used in
/// `addPropertyToElementList` (kept as a fn item for the `dyn Fn` param).
#[allow(dead_code)]
fn t_is_not_undefined(c: &mut Checker, t: TypeId) -> bool {
    !type_flags(c, t).intersects(TypeFlags::UNDEFINED)
}

// ----------------------------------------------------------------------------
// `*Checker` helpers required by the nodebuilder port (Go: checker.go).
// These are `checker.go` utilities that the nodebuilder cluster calls into;
// they live here because the nodebuilder port is their first consumer.
// ----------------------------------------------------------------------------

impl Checker {
    /// `(c *Checker) getTypeReferenceArity` (checker.go).
    pub(crate) fn get_type_reference_arity(&mut self, t: TypeId) -> usize {
        let Some(target) = c_ref_target(&self.types, t) else {
            return 0;
        };
        self.types_handle()
            .get(target)
            .as_interface_type()
            .map(|i| i.type_parameters().len())
            .unwrap_or(0)
    }

    /// `(c *Checker) isArrayOrTupleType` (checker.go).
    pub(crate) fn is_array_or_tuple_type(&self, t: TypeId) -> bool {
        self.is_array_type(t) || crate::checker_core::is_tuple_type(&self.types, t)
    }

    /// `(c *Checker) getClassOrInterfaceLikeDeclaration` (checker.go).
    pub(crate) fn get_class_or_interface_like_declaration(
        &self,
        symbol: SymbolId,
            nodes: &[ast::Node],) -> Option<NodeId> {
        let flags = symbol_flags(self, symbol);
        if flags.intersects(ast::SymbolFlags::CLASS | ast::SymbolFlags::FUNCTION) {
            return symbol_value_declaration(self, symbol);
        }
        symbol_declarations(self, symbol).into_iter().find(|&d| {
            let __program = self.program.clone().expect("program");
            let dn = crate::printer_util::arena_view(&__program, nodes, (d).file_index());
            if ast::is_interface_declaration(&dn[d]) {
                return true;
            }
            if !ast::is_variable_declaration(&dn[d]) {
                return false;
            }
            dn[d]
                .initializer()
                .is_some_and(|i| ast::is_function_expression_or_arrow_function(&dn[i]))
        })
    }

    /// `(c *Checker) canGetTypeParametersOfClassOrInterface` (checker.go).
    pub(crate) fn can_get_type_parameters_of_class_or_interface(
        &self,
        symbol: SymbolId,
        nodes: &[ast::Node],
    ) -> bool {
        self.get_class_or_interface_like_declaration(symbol, nodes)
            .is_some()
    }

    /// `(c *Checker) getOuterTypeParametersOfClassOrInterface` (checker.go).
    pub(crate) fn get_outer_type_parameters_of_class_or_interface(
        &mut self,
        symbol: SymbolId,
            nodes: &[ast::Node],) -> Vec<TypeId> {
        let declaration = self.get_class_or_interface_like_declaration(symbol, nodes).expect(
            "Class was missing valueDeclaration -OR- non-class had no interface declarations",
        );
        self.get_outer_type_parameters(declaration, false /*includeThisTypes*/, nodes)
    }

    /// `(c *Checker) getOuterTypeParameters` (checker.go) — outer type
    /// parameters of a node, or empty if none.
    pub(crate) fn get_outer_type_parameters(
        &mut self,
        node: NodeId,
        include_this_types: bool,
            nodes: &[ast::Node],) -> Vec<TypeId> {
        let mut node = node;
        loop {
            node = match self.program_nodes_live(node, nodes)[node].parent {
                Some(p) => p,
                None => return Vec::new(),
            };
            let __program = self.program.clone().expect("program");
            let kind = crate::printer_util::arena_view(&__program, nodes, (node).file_index())[node].kind;
            if !matches!(
                kind,
                Kind::ClassDeclaration
                    | Kind::ClassExpression
                    | Kind::InterfaceDeclaration
                    | Kind::CallSignature
                    | Kind::ConstructSignature
                    | Kind::MethodSignature
                    | Kind::FunctionType
                    | Kind::ConstructorType
                    | Kind::FunctionDeclaration
                    | Kind::MethodDeclaration
                    | Kind::FunctionExpression
                    | Kind::ArrowFunction
                    | Kind::TypeAliasDeclaration
                    | Kind::JSTypeAliasDeclaration
                    | Kind::MappedType
                    | Kind::ConditionalType
            ) {
                continue;
            }
            let mut outer_type_parameters =
                self.get_outer_type_parameters(node, include_this_types, nodes);
            {
                let __program = self.program.clone().expect("program");
                let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
                let is_fn_like = kind == Kind::FunctionExpression
                    || kind == Kind::ArrowFunction
                    || ast::is_object_literal_method(node, &nn);
                if is_fn_like && self.is_context_sensitive(node) {
                    let sym = self.get_symbol_of_declaration(node);
                    if let Some(sym) = sym {
                        let t = self.get_type_of_symbol(sym);
                        if let Some(signature) = self
                            .get_signatures_of_type(t, SignatureKind::Call)
                            .first()
                            .copied()
                        {
                            let tps = self.signature_arena.get(signature).type_parameters.clone();
                            if !tps.is_empty() {
                                outer_type_parameters.extend(tps.iter().copied());
                            }
                        }
                    }
                }
            }
            if kind == Kind::MappedType {
                let mapped = {
                    let __program = self.program.clone().expect("program");
                    let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
                    nn[node].as_mapped_type_node().type_parameter
                };
                if let Some(mapped) = mapped
                    && let Some(sym) = self.get_symbol_of_declaration(mapped)
                {
                    outer_type_parameters.push(self.get_declared_type_of_type_parameter(sym));
                }
                return outer_type_parameters;
            }
            if kind == Kind::ConditionalType {
                outer_type_parameters.extend(self.get_infer_type_parameters(node, nodes));
                return outer_type_parameters;
            }
            let type_parameter_decls: Vec<NodeId> = self.program_nodes_live(node, nodes)[node]
                .type_parameters()
                .unwrap_or(&[])
                .to_vec();
            let mut outer_and_own =
                self.append_type_parameters(outer_type_parameters, &type_parameter_decls, nodes);
            let mut this_type: Option<TypeId> = None;
            if include_this_types
                && matches!(
                    kind,
                    Kind::ClassDeclaration | Kind::ClassExpression | Kind::InterfaceDeclaration
                )
            {
                if let Some(sym) = self.get_symbol_of_declaration(node) {
                    let declared = self.get_declared_type_of_class_or_interface(sym);
                    this_type = self
                        .types_handle()
                        .get(declared)
                        .as_interface_type()
                        .and_then(|i| i.this_type());
                }
            }
            if let Some(this_type) = this_type {
                outer_and_own.push(this_type);
            }
            return outer_and_own;
        }
    }

    /// `(c *Checker) getInferTypeParameters` (checker.go).
    pub(crate) fn get_infer_type_parameters(&mut self, node: NodeId,
        nodes: &[ast::Node],) -> Vec<TypeId> {
        let mut result = Vec::new();
        let locals: Vec<SymbolId> = {
            let __program = self.program.clone().expect("program");
            let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
            nn[node]
                .locals()
                .map(|l| l.values().copied().collect())
                .unwrap_or_default()
        };
        for symbol in locals {
            if symbol_flags(self, symbol).intersects(ast::SymbolFlags::TYPE_PARAMETER) {
                result.push(self.get_declared_type_of_symbol(symbol));
            }
        }
        // Go: `slices.SortFunc(result, CompareTypes)` (checker.go:24303) —
        // full type comparator, not raw type-id order.
        result.sort_by(|&a, &b| {
            crate::utilities::compare_types(
                &self.types,
                &self.symbol_arena,
                &self.type_mappers,
                self.program.as_ref(),
                a,
                b,
            )
            .cmp(&0)
        });
        result
    }

    /// `(c *Checker) getLocalTypeParametersOfClassOrInterfaceOrTypeAlias`
    /// (checker.go).
    pub(crate) fn get_local_type_parameters_of_class_or_interface_or_type_alias(
        &mut self,
        symbol: SymbolId,
            nodes: &[ast::Node],) -> Vec<TypeId> {
        self.append_local_type_parameters_of_class_or_interface_or_type_alias(Vec::new(), symbol, nodes)
    }

    /// `(c *Checker) appendLocalTypeParametersOfClassOrInterfaceOrTypeAlias`
    /// (checker.go).
    pub(crate) fn append_local_type_parameters_of_class_or_interface_or_type_alias(
        &mut self,
        mut types: Vec<TypeId>,
        symbol: SymbolId,
        nodes: &[ast::Node],) -> Vec<TypeId> {
        for node in symbol_declarations(self, symbol) {
            let __program = self.program.clone().expect("program");
            let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
            let kind = nn[node].kind;
            if matches!(
                kind,
                Kind::InterfaceDeclaration | Kind::ClassDeclaration | Kind::ClassExpression
            ) || crate::utilities::is_type_alias(&nn[node])
            {
                let decls: Vec<NodeId> = nn[node].type_parameters().unwrap_or(&[]).to_vec();
                types = self.append_type_parameters(types, &decls, nodes);
            }
        }
        types
    }

    /// `(c *Checker) appendTypeParameters` (checker.go).
    pub(crate) fn append_type_parameters(
        &mut self,
        mut type_parameters: Vec<TypeId>,
        declarations: &[NodeId],
            nodes: &[ast::Node],) -> Vec<TypeId> {
        for &declaration in declarations {
            if let Some(sym) = self.get_symbol_of_declaration(declaration) {
                let tp = self.get_declared_type_of_type_parameter(sym);
                if !type_parameters.contains(&tp) {
                    type_parameters.push(tp);
                }
            }
        }
        type_parameters
    }

    /// `(c *Checker) getIntendedTypeFromJSDocTypeReference` (checker.go).
    pub(crate) fn get_intended_type_from_js_doc_type_reference(
        &mut self,
        node: NodeId,
        nodes: &[ast::Node],) -> Option<TypeId> {
        let (is_jsdoc, type_name_text, type_args) = {
            let __program = self.program.clone().expect("program");
            let nn = crate::printer_util::arena_view(&__program, nodes, (node).file_index());
            if !nn[node].flags.intersects(ast::NodeFlags::JSDOC)
                || !ast::is_type_reference_node(&nn[node])
            {
                return None;
            }
            let type_name = nn[node].as_type_reference_node().type_name?;
            if !ast::is_identifier(&nn[type_name]) {
                return None;
            }
            let text = nn[type_name].text(&nn).into_owned();
            let args: Vec<NodeId> = nn[node].type_arguments().unwrap_or(&[]).to_vec();
            (true, text, args)
        };
        let _ = is_jsdoc;
        match type_name_text.as_str() {
            "String" => {
                self.check_no_type_arguments(node, None);
                Some(self.string_type)
            }
            "Number" => {
                self.check_no_type_arguments(node, None);
                Some(self.number_type)
            }
            "BigInt" => {
                self.check_no_type_arguments(node, None);
                Some(self.bigint_type)
            }
            "Boolean" => {
                self.check_no_type_arguments(node, None);
                Some(self.boolean_type)
            }
            "Void" => {
                self.check_no_type_arguments(node, None);
                Some(self.void_type)
            }
            "Undefined" => {
                self.check_no_type_arguments(node, None);
                Some(self.undefined_type)
            }
            "Null" => {
                self.check_no_type_arguments(node, None);
                Some(self.null_type)
            }
            "Function" | "function" => {
                self.check_no_type_arguments(node, None);
                Some(self.global_function_type)
            }
            "array" => {
                if type_args.is_empty() && !self.no_implicit_any {
                    Some(self.any_array_type)
                } else {
                    None
                }
            }
            "promise" => {
                if type_args.is_empty() && !self.no_implicit_any {
                    Some(self.create_promise_type(self.any_type))
                } else {
                    None
                }
            }
            "Object" => {
                if type_args.len() == 2 {
                    if let Some(record_symbol) =
                        self.get_global_record_symbol.clone().and_then(|t| t(self))
                    {
                        let index_type = self.get_type_from_type_node(type_args[0]);
                        if self.is_valid_index_key_type(index_type) {
                            let value = self.get_type_from_type_node(type_args[1]);
                            return Some(self.get_type_alias_instantiation(
                                record_symbol,
                                &[index_type, value],
                                None,
                            ));
                        }
                    }
                    return Some(self.any_type);
                }
                if !self.no_implicit_any {
                    self.check_no_type_arguments(node, None);
                    Some(self.any_type)
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

/// `t.Target()` — the reference target (`TypeReference.target` →
/// `ObjectType.target`).
fn c_ref_target(types: &TypeArena, t: TypeId) -> Option<TypeId> {
    types
        .get(t)
        .data
        .as_type_reference()
        .and_then(|r| r.object_type.target)
}
