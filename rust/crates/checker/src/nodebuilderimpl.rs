// PORT(partial) — scaffolding from tsc/internal/checker/nodebuilderimpl.go @
// ec47d33c23e464a17cdf2475632cba629bee8763
//
// nodebuilderimpl.go itself is NOT part of the foundation phase (it is a
// multi-thousand-line `*NodeBuilderImpl` method file). This file carries only
// the data structures that `nodebuilderscopes.go`, `symboltracker.go` and the
// checker links need to compile: `CompositeSymbolIdentity`,
// `TrackedSymbolArgs`, `SerializedTypeEntry`, `CompositeTypeCacheIdentity`,
// `NodeBuilderLinks`, `NodeBuilderSymbolLinks`, `NodeBuilderContext` and a
// partial `NodeBuilderImpl`. The real implementation lands with the
// nodebuilder port; all members are `pub` so the deferred code can fill in.
//
// Pointer conversions: `*ast.Symbol` → `SymbolId`, `*ast.Node` → `NodeId`,
// `*Type` → `TypeId`, `*TypeMapper` → `Option<TypeMapperId>`,
// `*ast.SourceFile` → its `NodeId`, `*ast.Identifier` → `NodeId`,
// `module.ModeAwareCache[T]` → `tsc_module::ModeAwareCache<T>`, and
// `collections.Set[TypeId]` → `OrderedSet<TypeId>`.

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, NodeId, SymbolFlags, SymbolId};
use tsc_collections::{CopyOnWriteMap, CopyOnWriteSet, OrderedSet};
use tsc_core::linkstore::LinkStore;
use tsc_nodebuilder as nodebuilder;

use crate::checker_core::CacheHashKey;
use crate::mapper::TypeMapperId;
use crate::types::TypeId;

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
pub struct ModuleSpecifierResult {
    /// `specifier`.
    pub specifier: tsc_tspath::ModuleSpecifier,
    /// `importAttributesType`.
    pub import_attributes_type: Option<TypeId>,
}

/// `type NodeBuilderContext struct` — PORT(partial): all fields are ported
/// except `host` (`modulespecifiers.ModuleSpecifierGenerationHost` — the
/// module-specifier host interface is deferred) and `tracker` stays a plain
/// trait object.
#[derive(Default)]
pub struct NodeBuilderContext {
    // PORT(deferred): `host Host` — `modulespecifiers.ModuleSpecifierGenerationHost`
    // is not yet ported (no tsc-modulespecifiers crate in this phase).
    /// `tracker`.
    pub tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
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
    pub reported_diagnostic: std::rc::Rc<std::cell::Cell<bool>>,
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
    pub tracked_symbols: std::rc::Rc<std::cell::RefCell<Vec<TrackedSymbolArgs>>>,
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
    /// `CopyOnWriteMap<TypeId, NodeId>`.
    pub type_parameter_names: CopyOnWriteMap<TypeId, NodeId>,
    /// `typeParameterNamesByText`.
    pub type_parameter_names_by_text: CopyOnWriteSet<String>,
    /// `typeParameterNamesByTextNextNameCount`.
    pub type_parameter_names_by_text_next_name_count: CopyOnWriteMap<String, i32>,
    /// `typeParameterSymbolList`.
    pub type_parameter_symbol_list: CopyOnWriteSet<SymbolId>,
}

/// `type NodeBuilderImpl struct` — PORT(partial): the checker back-pointer
/// `ch *Checker` becomes an explicit `&mut Checker` parameter on the methods
/// that need it (SPEC §5.4), and `e *printer.EmitContext` /
/// `pc *pseudochecker.PseudoChecker` / `cloneBindingNameVisitor` are deferred
/// with the rest of nodebuilderimpl.go.
pub struct NodeBuilderImpl<'a> {
    // host members
    /// `f`.
    pub f: ast::NodeFactory<'a>,
    // PORT(deferred): `ch *Checker` — passed as `&mut Checker` to methods.
    // PORT(deferred): `e *printer.EmitContext`, `pc *pseudochecker.PseudoChecker`.

    // cache
    /// `links` — `core.LinkStore[*ast.Node, NodeBuilderLinks]` keyed by
    /// `NodeId`.
    pub links: LinkStore<NodeId, NodeBuilderLinks>,
    /// `symbolLinks`.
    pub symbol_links: LinkStore<SymbolId, NodeBuilderSymbolLinks>,

    // state
    /// `ctx`.
    pub ctx: NodeBuilderContext,

    // PORT(deferred): `cloneBindingNameVisitor *ast.NodeVisitor`.

    // symbols for synthesized identifiers, needed for e.g. inlay hints
    /// `idToSymbol` — `map[*ast.IdentifierNode]*ast.Symbol` keyed by the
    /// identifier's `NodeId`.
    pub id_to_symbol: FxHashMap<NodeId, SymbolId>,
}

impl<'a> NodeBuilderImpl<'a> {
    /// `defaultMaximumTruncationLength`.
    pub const DEFAULT_MAXIMUM_TRUNCATION_LENGTH: i32 = 160;
    /// `noTruncationMaximumTruncationLength`.
    pub const NO_TRUNCATION_MAXIMUM_TRUNCATION_LENGTH: i32 = 1_000_000;
}
