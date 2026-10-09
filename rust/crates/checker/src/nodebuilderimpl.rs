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
use tsc_core::compileroptions::{
    ResolutionMode, RESOLUTION_MODE_ESM, RESOLUTION_MODE_NONE,
};
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::{ModuleKind, ModuleResolutionKind};
use tsc_core::linkstore::LinkStore;
use tsc_jsnum as jsnum;
use tsc_nodebuilder as nodebuilder;
use tsc_printer::{self as printer, EmitContext};
use tsc_pseudochecker::{self as pseudochecker, PseudoType, PseudoTypeKind, PseudoTypeRef};
use tsc_scanner as scanner;
use tsc_stringutil as stringutil;

use crate::checker_core::{CacheHashKey, Checker};
use crate::checker_types::{Host, MappedTypeModifiers, TypeFacts};
use crate::mapper::TypeMapperId;
use crate::nodebuilderscopes::collect_binding_pattern_symbols;
use crate::types::{
    ConditionalType, ElementFlags, IndexInfo, IndexInfoId, ObjectFlags, Signature,
    SignatureFlags, SignatureId, SignatureKind, TypeAlias, TypeFlags, TypeId, TypeParameter,
    TypePredicate, TypePredicateKind,
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
pub struct NodeBuilderContext {
    /// `host` — `modulespecifiers.ModuleSpecifierGenerationHost`.
    pub host: Option<Rc<dyn Host>>,
    /// `tracker` — `Rc<RefCell>` so visit closures (e.g. the computed-name
    /// tracker inside `clone_binding_name`) can reach the tracker while
    /// `b`/`c` are borrowed elsewhere — Go shares it via `b.ctx.tracker`.
    pub tracker: Option<Rc<RefCell<dyn nodebuilder::SymbolTracker>>>,
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
    /// `CopyOnWriteMap<TypeId, NodeId>`.
    pub type_parameter_names: CopyOnWriteMap<TypeId, NodeId>,
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
    pub fn restore(self, ctx: &mut NodeBuilderContext) {
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
    pub ctx: NodeBuilderContext,

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
fn new_nodebuilder_factory(e: &Rc<RefCell<EmitContext>>) -> ast::NodeFactory<'static> {
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
/// `cloneBindingNameVisitor` is not stored.
pub fn new_node_builder_impl(
    c: &Checker,
    e: EmitContext,
    id_to_symbol: FxHashMap<NodeId, SymbolId>,
) -> NodeBuilderImpl<'static> {
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
    c.symbol_arena.borrow()[s.index()].flags
}

/// `symbol.checkFlags` read through the arena.
fn symbol_check_flags(c: &Checker, s: SymbolId) -> ast::checkflags::CheckFlags {
    c.symbol_arena.borrow()[s.index()].check_flags
}

/// `symbol.name` (cloned) read through the arena.
fn symbol_name(c: &Checker, s: SymbolId) -> String {
    c.symbol_arena.borrow()[s.index()].name.clone()
}

/// `symbol.declarations` (cloned) read through the arena.
fn symbol_declarations(c: &Checker, s: SymbolId) -> Vec<NodeId> {
    c.symbol_arena.borrow()[s.index()].declarations.clone()
}

/// `symbol.parent` read through the arena.
fn symbol_parent(c: &Checker, s: SymbolId) -> Option<SymbolId> {
    c.symbol_arena.borrow()[s.index()].parent
}

/// `symbol.valueDeclaration` read through the arena.
fn symbol_value_declaration(c: &Checker, s: SymbolId) -> Option<NodeId> {
    c.symbol_arena.borrow()[s.index()].value_declaration
}

/// `symbol.exports` (cloned) read through the arena.
fn symbol_exports(c: &Checker, s: SymbolId) -> ast::SymbolTable {
    c.symbol_arena.borrow()[s.index()].exports.clone()
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
    ast::symbol::escape_symbol_name(&c.symbol_arena.borrow()[s.index()].name).into_owned()
}

/// `t.flags` / `t.objectFlags` / `t.symbol` / `t.alias` reads.
fn type_flags(c: &Checker, t: TypeId) -> TypeFlags {
    c.types.get(t).flags
}
fn type_object_flags(c: &Checker, t: TypeId) -> ObjectFlags {
    c.types.get(t).object_flags
}
fn type_symbol(c: &Checker, t: TypeId) -> Option<SymbolId> {
    c.types.get(t).symbol
}
fn type_alias(c: &Checker, t: TypeId) -> Option<TypeAlias> {
    c.types.get(t).alias.clone()
}
fn type_id(c: &Checker, t: TypeId) -> TypeId {
    c.types.get(t).id
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
            return !c.is_lib_symbol_for_hover_verbosity(
                type_alias(c, t).and_then(|a| a.symbol).unwrap_or(SymbolId::NONE),
            );
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
    fn check_type_expandability(&mut self, c: &mut Checker, t: Option<TypeId>) {
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

    fn check_type_expandability_inner(&mut self, c: &mut Checker, t: TypeId) {
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
        c: &mut Checker,
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
            let type_argument_list = nodes[ref_].type_arguments(nodes).cloned();
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
            let ref_args = nodes[ref_].type_arguments(nodes).cloned();
            if self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::USE_INSTANTIATION_EXPRESSIONS)
                && nodes[root]
                    .as_type_reference_node()
                    .type_arguments
                    .as_ref()
                    .is_some_and(|l| !l.nodes.is_empty())
            {
                let mut expr =
                    self.create_access_expression(nodes, type_name);
                let type_args = nodes[root].as_type_reference_node().type_arguments.clone();
                expr = self.create_expression_with_type_arguments(nodes, Some(expr), type_args)?;
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
        let mut expr = self.create_access_expression(nodes, Some(root))?;
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
    fn create_elided_information_placeholder(
        &mut self,
        nodes: &mut Vec<ast::Node>,
    ) -> NodeId {
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
                    self.type_to_type_node(c, nodes, list[0]),
                    None,
                    self.type_to_type_node(c, nodes, list[list.len() - 1]),
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

        let may_have_name_collisions =
            !self.ctx.flags.intersects(nodebuilder::Flags::USE_FULLY_QUALIFIED_TYPE);
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
                let type_node = self.type_to_type_node(c, nodes, list[list.len() - 1]);
                if let Some(type_node) = type_node {
                    result.push(type_node);
                }
                break;
            }
            self.ctx.approximate_length += 2; // Account for whitespace + separator
            let type_node = self.type_to_type_node(c, nodes, t);
            if let Some(type_node) = type_node {
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
                        result[i] = self.type_to_type_node(c, nodes, t).unwrap_or(result[i]);
                    }
                }
            }
            restore_flags.restore(&mut self.ctx);
        }

        Some(self.f.new_node_list(result))
    }

    /// `(b *NodeBuilderImpl) serializeTypeName`.
    fn serialize_type_name(
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
        let symbol = c.resolve_entity_name(node, meaning, true, false, Some(node));
        let symbol = symbol?;

        let mut resolved_symbol = symbol;
        if symbol_flags(c, symbol).intersects(SymbolFlags::ALIAS) {
            resolved_symbol = c.resolve_alias(symbol);
        }

        if c.is_symbol_accessible(symbol, self.ctx.enclosing_declaration, meaning, false)
            .accessibility
            != printer::SymbolAccessibility::ACCESSIBLE
        {
            return None;
        }
        self.symbol_to_type_node(c, nodes, resolved_symbol, meaning, type_arguments)
    }

    /// `(b *NodeBuilderImpl) setCommentRange`.
    fn set_comment_range(&mut self, c: &mut Checker, nodes: &mut Vec<ast::Node>, node: NodeId, range_: Option<NodeId>) {
        let Some(range_) = range_ else { return };
        if let Some(enclosing_file) = self.ctx.enclosing_file {
            let range_file = ast::get_source_file_of_node(Some(range_), &c.program_nodes(range_));
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
        if crate::utilities::is_optional_declaration(annotated_declaration, nodes) {
            return c.get_type_with_facts(t, crate::types::TypeFacts::NE_UNDEFINED)
                == type_from_type_node;
        }
        false
    }

    /// `(b *NodeBuilderImpl) canReuseExistingJSTypeNode`.
    fn can_reuse_existing_js_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        existing: NodeId,
        t: TypeId,
    ) -> bool {
        c.get_intended_type_from_js_doc_type_reference(existing).is_none()
            && self.existing_type_node_is_not_reference_or_is_reference_with_compatible_type_argument_count(c, nodes, existing, t)
    }

    /// `(b *NodeBuilderImpl) tryGetResolvedSymbolFromTypeNode`.
    fn try_get_resolved_symbol_from_type_node(
        &mut self,
        c: &mut Checker,
        node: Option<NodeId>,
    ) -> Option<SymbolId> {
        let node = node?;
        let n_nodes = c.program_nodes(node);
        n_nodes[node].parent?;
        c.get_type_from_type_node(node);
        // call to ensure symbol is resolved
        c.symbol_node_links.try_get(node).and_then(|l| l.resolved_symbol)
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
        let e_nodes = c.program_nodes(existing);
        if !ast::is_type_reference_node(&e_nodes[existing]) {
            return true;
        }
        let existing_args_len = e_nodes[existing]
            .type_arguments(&e_nodes)
            .map(|l| l.nodes.len())
            .unwrap_or(0);

        let Some(symbol) = self.try_get_resolved_symbol_from_type_node(c, Some(existing)) else {
            return true;
        };

        // `type` is a reference type, and `existing` is a type reference
        // node, but we still need to make sure they refer to the _same_
        // target type before we go comparing their type argument counts.

        let existing_target = c.get_declared_type_of_symbol(symbol);
        let target = c.types.get(t).data.as_type_reference().and_then(|r| r.object_type.target);
        if existing_target.is_none() || existing_target != target {
            return true;
        }
        let min_args = c.get_min_type_argument_count(
            c.types
                .get(target.unwrap())
                .data
                .as_interface_type()
                .map(|i| i.type_parameters())
                .unwrap_or(&[]),
        );
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
            None => self.get_type_from_type_node(c, existing, true),
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
        let structured = c.types.get(t).data.structured_type().cloned().unwrap_or_default();
        if structured.construct_signatures().is_empty() {
            return t;
        }
        if let Some(t2) = structured.object_type_without_abstract_construct_signatures {
            return t2;
        }
        let construct_signatures: Vec<SignatureId> = structured
            .construct_signatures()
            .iter()
            .copied()
            .filter(|&signature| {
                !c.signature_arena
                    .get(signature)
                    .flags
                    .intersects(SignatureFlags::ABSTRACT)
            })
            .collect();
        if construct_signatures.len() == structured.construct_signatures().len() {
            c.types
                .get_mut(t)
                .data
                .structured_type_mut()
                .unwrap()
                .object_type_without_abstract_construct_signatures = Some(t);
            return t;
        }
        let type_copy = c.new_anonymous_type(
            t.symbol_of_structured(&structured),
            structured.members.clone(),
            structured.call_signatures().to_vec(),
            if !construct_signatures.is_empty() {
                construct_signatures
            } else {
                Vec::new()
            },
            structured.index_infos.clone(),
        );
        c.types
            .get_mut(t)
            .data
            .structured_type_mut()
            .unwrap()
            .object_type_without_abstract_construct_signatures = Some(type_copy);
        c.types
            .get_mut(type_copy)
            .data
            .structured_type_mut()
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
                let dn = c.program_nodes(value_declaration);
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
        let symbol_name = self.get_name_of_symbol_as_written(c, nodes, symbol);
        if index == 0 {
            self.ctx.flags.remove(nodebuilder::Flags::IN_INITIAL_ENTITY_NAME);
        }

        let identifier = self.new_identifier(nodes, &symbol_name, Some(symbol));
        self.e.borrow().add_emit_flags(identifier, printer::EmitFlags::NO_ASCII_ESCAPING);
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
        if symbol_declarations(c, chain[0])
            .iter()
            .any(|&d| crate::symbolaccessibility::has_non_global_augmentation_external_module_symbol(d, c))
        {
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
            let most_original_decl =
                self.e.borrow().most_original(self.ctx.enclosing_declaration);
            let context_file = most_original_decl
                .and_then(|d| ast::get_source_file_of_node(Some(d), &c.program_nodes(d)));
            let target_file = get_source_file_of_module_symbol(c, chain[0]);
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
                        let target_nodes = c.program_nodes(target_file);
                        let context_nodes = c.program_nodes(context_file);
                        let target_format = program.get_emit_module_format_of_file(
                            target_nodes[target_file].as_source_file(),
                        );
                        let context_format = program.get_emit_module_format_of_file(
                            context_nodes[context_file].as_source_file(),
                        );
                        if target_format == ModuleKind::ESNext
                            && target_format != context_format
                        {
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
                        let fn_ = c.program_nodes(f);
                        c.program.as_ref().map(|program| {
                            program
                                .get_emit_module_format_of_file(fn_[f].as_source_file())
                        })
                    });
                    let swapped_mode = if context_format == Some(ModuleKind::ESNext) {
                        ModuleKind::CommonJS
                    } else {
                        ModuleKind::ESNext
                    };
                    specifier_result = self.get_specifier_for_module_symbol(
                        c,
                        nodes,
                        chain[0],
                        swapped_mode,
                    );
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
                        tracker.borrow_mut().report_likely_unsafe_import_required_error(
                            old_specifier_result.specifier.as_string(),
                            &c.symbol_arena.borrow()[symbol.index()].name,
                            nodes,
                        );
                    }
                }
            }

            let attributes =
                self.create_import_attributes_for_module_specifier(c, nodes, &specifier_result, import_mode_override);
            let specifier_string = specifier_result.specifier.as_string().to_owned();
            let lit = self
                .f
                .new_literal_type_node(nodes, Some(self.new_string_literal(nodes, &specifier_string)));
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
            let object_type =
                self.f
                    .new_import_type_node(nodes, is_type_of, Some(lit), attributes, qualifier, type_parameter_nodes);
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
            return Some(self.f.new_type_reference_node(nodes, Some(entity_name), type_arguments));
        }
        if is_type_of && ast::is_expression_with_type_arguments(&nodes[entity_name]) {
            let (expr, expr_args) = {
                let e = nodes[entity_name].as_expression_with_type_arguments();
                (e.expression, e.type_arguments.clone())
            };
            let cloned = self.f.deep_clone_node(nodes, expr);
            return Some(self.f.new_type_query_node(nodes, Some(cloned), expr_args));
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
            type_parameter_nodes =
                self.lookup_type_parameter_nodes(c, nodes, chain, index).map(NodeList::from);
        }
        let symbol = *chain.get(index)?;
        let parent: Option<SymbolId> = if index > 0 { Some(chain[index - 1]) } else { None };

        let mut symbol_name = String::new();
        if index == 0 {
            self.ctx.flags |= nodebuilder::Flags::IN_INITIAL_ENTITY_NAME;
            symbol_name = self.get_name_of_symbol_as_written(c, nodes, symbol);
            self.ctx.approximate_length += symbol_name.len() as i32 + 1;
            self.ctx.flags.remove(nodebuilder::Flags::IN_INITIAL_ENTITY_NAME);
        } else {
            // lookup a ref to symbol within parent to handle export aliases
            if let Some(parent) = parent {
                let exports = c.get_exports_of_symbol(parent);
                if !exports.is_empty() {
                    // avoid exhaustive iteration in the common case
                    let name = symbol_name(c, symbol);
                    if name != ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                        && !crate::utilities::is_late_bound_name(&name)
                        && exports
                            .get(&name)
                            .is_some_and(|&res| c.get_symbol_if_same_reference(res, symbol).is_some())
                    {
                        symbol_name = name;
                    } else {
                        let mut results: FxHashMap<SymbolId, String> = FxHashMap::default();
                        for (ex_name, &ex) in exports.iter() {
                            if c.get_symbol_if_same_reference(ex, symbol).is_some()
                                && !crate::utilities::is_late_bound_name(ex_name)
                                && ex_name != ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                            {
                                results.insert(ex, ex_name.clone());
                                // must collect all results and sort them -
                                // exports are randomly iterated
                            }
                        }
                        let mut result_symbols: Vec<SymbolId> = results.keys().copied().collect();
                        if !result_symbols.is_empty() {
                            c.sort_symbols(&mut result_symbols);
                            symbol_name = results[&result_symbols[0]].clone();
                        }
                    }
                }
            }
        }

        if symbol_name.is_empty() {
            let mut name: Option<NodeId> = None;
            for &d in &symbol_declarations(c, symbol) {
                let dn = c.program_nodes(d);
                name = ast::get_name_of_declaration(Some(d), &dn);
                if name.is_some() {
                    break;
                }
            }
            if let Some(name) = name {
                let nn = c.program_nodes(name);
                if ast::is_computed_property_name(&nn[name])
                    && is_entity_name_opt(nn[name].expression(), &nn)
                {
                    let lhs = self.create_access_from_symbol_chain(
                        c,
                        nodes,
                        chain,
                        index - 1,
                        stopper,
                        override_type_arguments.clone(),
                    )?;
                    if ast::is_entity_name(&nodes[lhs]) {
                        let lhs = self.f.new_parenthesized_type_node(
                            nodes,
                            Some(self.f.new_type_query_node(nodes, Some(lhs), None)),
                        );
                        return Some(self.f.new_indexed_access_type_node(
                            nodes,
                            Some(lhs),
                            self.f.new_type_query_node(
                                nodes,
                                nn[name].expression().map(|e| {
                                    // `name.Expression()` may live in a
                                    // different arena; reuse the
                                    // foreign-file id if arenas coincide.
                                    e
                                }),
                                None,
                            ),
                        ));
                    }
                    return Some(lhs);
                }
            }
            symbol_name = self.get_name_of_symbol_as_written(c, nodes, symbol);
        }
        self.ctx.approximate_length += symbol_name.len() as i32 + 1;

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
                    .get(&name)
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
                    let literal = self
                        .f
                        .new_literal_type_node(nodes, Some(self.new_string_literal(nodes, &symbol_name)));
                    if ast::is_indexed_access_type_node(&nodes[lhs]) {
                        return Some(self.f.new_indexed_access_type_node(nodes, Some(lhs), Some(literal)));
                    }
                    let object = self.f.new_type_reference_node(nodes, Some(lhs), type_parameter_nodes);
                    return Some(self.f.new_indexed_access_type_node(nodes, Some(object), Some(literal)));
                }
            }
        }

        let identifier = self.new_identifier(nodes, &symbol_name, Some(symbol));
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
                return Some(self.f.new_qualified_name(nodes, Some(lhs), Some(identifier)));
            }
            let expr = self.create_access_expression(nodes, Some(lhs));
            let prop_access = self.f.new_property_access_expression(
                nodes,
                expr,
                None,
                Some(identifier),
                ast::NodeFlags::NONE,
            );
            return self.create_expression_with_type_arguments(nodes, Some(prop_access), type_parameter_nodes);
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
            tracker
                .borrow_mut()
                .track_symbol(symbol, self.ctx.enclosing_declaration, mask, nodes);
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
        let mut symbol_name = self.get_name_of_symbol_as_written(c, nodes, symbol);
        if index == 0 {
            self.ctx.flags.remove(nodebuilder::Flags::IN_INITIAL_ENTITY_NAME);
        }

        if starts_with_single_or_double_quote(&symbol_name)
            && symbol_declarations(c, symbol).iter().any(|&d| {
                crate::symbolaccessibility::has_non_global_augmentation_external_module_symbol(d, c)
            })
        {
            let specifier_result =
                self.get_specifier_for_module_symbol(c, nodes, symbol, RESOLUTION_MODE_NONE);
            self.ctx.approximate_length += 2 + specifier_result.specifier.as_string().len() as i32;
            return Some(self.new_string_literal(nodes, specifier_result.specifier.as_string()));
        }

        if index == 0 || can_use_property_access(&symbol_name) {
            let identifier = self.new_identifier(nodes, &symbol_name, Some(symbol));
            self.e
                .borrow()
                .add_emit_flags(identifier, printer::EmitFlags::NO_ASCII_ESCAPING);
            self.ctx.approximate_length += 1 + symbol_name.len() as i32;
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
                return self.create_expression_with_type_arguments(nodes, Some(result), type_parameter_nodes);
            }
            return self.create_expression_with_type_arguments(nodes, Some(identifier), type_parameter_nodes);
        }

        if starts_with_square_bracket(&symbol_name) {
            symbol_name = symbol_name[1..symbol_name.len() - 1].to_owned();
        }

        let mut expression: Option<NodeId> = None;
        if starts_with_single_or_double_quote(&symbol_name)
            && !symbol_flags(c, symbol).intersects(SymbolFlags::ENUM_MEMBER)
        {
            let literal_text = stringutil::unquote_string(&symbol_name);
            self.ctx.approximate_length += literal_text.len() as i32 + 2;
            expression = Some(self.new_string_literal_ex(
                nodes,
                &literal_text,
                symbol_name.as_bytes()[0] == b'\'',
            ));
        } else if jsnum::from_string(&symbol_name).string() == symbol_name {
            // TODO: the following in strada would assert if the number is
            // negative, but no such assertion exists here.
            // Moreover, what's even guaranteeing the name *isn't* -1 here
            // anyway? Needs double-checking.
            self.ctx.approximate_length += symbol_name.len() as i32;
            expression =
                Some(self.f.new_numeric_literal(nodes, &symbol_name, ast::TokenFlags::NONE));
        }
        if expression.is_none() {
            self.ctx.approximate_length += symbol_name.len() as i32;
            let identifier = self.new_identifier(nodes, &symbol_name, Some(symbol));
            self.e
                .borrow()
                .add_emit_flags(identifier, printer::EmitFlags::NO_ASCII_ESCAPING);
            expression = Some(identifier);
        }
        self.ctx.approximate_length += 2; // []
        let lhs = self.create_expression_from_symbol_chain(c, nodes, chain, index - 1);
        let element_access =
            self.f
                .new_element_access_expression(nodes, lhs, None, expression, ast::NodeFlags::NONE);
        self.create_expression_with_type_arguments(nodes, Some(element_access), type_parameter_nodes)
    }

    /// `(b *NodeBuilderImpl) getNameOfSymbolFromNameType`.
    fn get_name_of_symbol_from_name_type(&mut self, c: &mut Checker, symbol: SymbolId) -> String {
        if c.value_symbol_links.has(symbol) {
            let name_type = c.value_symbol_links.get(symbol).name_type;
            let Some(name_type) = name_type else {
                return String::new();
            };
            if type_flags(c, name_type).intersects(TypeFlags::STRING_OR_NUMBER_LITERAL) {
                let name = match c.types.get(name_type).data.as_literal_type().value.as_ref() {
                    Some(tsc_evaluator::Value::String(s)) => s.clone(),
                    Some(tsc_evaluator::Value::Number(n)) => n.to_js_string(),
                    _ => String::new(),
                };
                if !scanner::utilities::is_identifier_text(&name, LanguageVariant::Standard)
                    && !crate::utilities::is_numeric_literal_name(&name)
                {
                    return crate::checker_core::value_to_string(
                        c.types.get(name_type).data.as_literal_type().value.as_ref(),
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
        _nodes: &mut Vec<ast::Node>,
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
                        let dn0 = c.program_nodes(declarations[0]);
                        ast::find_ancestor(Some(declarations[0]), &dn0, &mut |n, nodes| {
                            is_default_binding_context(n, nodes)
                        })
                    };
                    let enclosing_binding = self.ctx.enclosing_declaration.and_then(|e| {
                        let en = c.program_nodes(e);
                        ast::find_ancestor(Some(e), &en, &mut |n, nodes| {
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
                let dn = c.program_nodes(d);
                ast::get_name_of_declaration(Some(d), &dn)
            });
            if let Some(name) = name {
                // !!! TODO: JS Object.defineProperty declarations
                // if ast.IsCallExpression(declaration) && ast.IsBindableObjectDefinePropertyCall(declaration) {
                //   return symbol.Name
                // }
                let nn = c.program_nodes(name);
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
            let dn = c.program_nodes(declaration);
            if dn[declaration].parent.is_some_and(|p| {
                c.program_nodes(p)[p].kind == Kind::VariableDeclaration
            }) {
                let parent = dn[declaration].parent.unwrap();
                let parent_nodes = c.program_nodes(parent);
                let var_name = parent_nodes[parent]
                    .as_variable_declaration()
                    .name;
                let name_nodes = c.program_nodes(var_name.unwrap_or(parent));
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
        ast::symbol::escape_internal_symbol_name(&s_name)
    }

    /// `(b *NodeBuilderImpl) getTypeParametersOfClassOrInterface`.
    // The full set of type parameters for a generic class or interface type
    // consists of its outer type parameters plus its locally declared type
    // parameters.
    fn get_type_parameters_of_class_or_interface(
        &mut self,
        c: &mut Checker,
        symbol: SymbolId,
    ) -> Vec<TypeId> {
        let mut result = c.get_outer_type_parameters_of_class_or_interface(symbol);
        result.extend(
            c.get_local_type_parameters_of_class_or_interface_or_type_alias(symbol),
        );
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
    fn lookup_symbol_chain(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: SymbolFlags,
        yield_module_symbol: bool,
    ) -> Vec<SymbolId> {
        if let Some(tracker) = self.ctx.tracker.clone() {
            tracker
                .borrow_mut()
                .track_symbol(symbol, self.ctx.enclosing_declaration, meaning, nodes);
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
        );
        let mut qualifier_meaning = meaning;
        if accessible_symbol_chain.len() > 1 {
            qualifier_meaning = crate::symbolaccessibility::get_qualified_left_meaning(meaning);
        }
        if accessible_symbol_chain.is_empty()
            || c.needs_qualification(
                accessible_symbol_chain[0],
                self.ctx.enclosing_declaration,
                qualifier_meaning,
            )
        {
            // Go up and add our parent.
            let mut root = symbol;
            if !accessible_symbol_chain.is_empty() {
                root = accessible_symbol_chain[0];
            }
            let parents = c.get_containers_of_symbol(root, self.ctx.enclosing_declaration, meaning);
            if !parents.is_empty() {
                let mut parent_specifiers: Vec<SortedSymbolNamePair> = parents
                    .iter()
                    .map(|&parent| {
                        if symbol_declarations(c, parent).iter().any(|&d| {
                            crate::symbolaccessibility::has_non_global_augmentation_external_module_symbol(d, c)
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
                        if let Some(&exported) = parent_exports.get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
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
                            let mut fallback =
                                c.get_alias_for_symbol_in_container(parent, symbol);
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
                    crate::symbolaccessibility::has_non_global_augmentation_external_module_symbol(d, c)
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
                return tsc_modulespecifiers::compare::count_path_components(specifier_a)
                    .cmp(&tsc_modulespecifiers::compare::count_path_components(specifier_b));
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
    fn get_specifier_for_module_symbol(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        override_import_mode: ResolutionMode,
    ) -> ModuleSpecifierResult {
        let enclosing_declaration = self.e.borrow().most_original(self.ctx.enclosing_declaration);
        let original_module_specifier = enclosing_declaration.and_then(|d| {
            let dn = c.program_nodes(d);
            if can_have_module_specifier(&dn[d]) {
                try_get_module_specifier_from_declaration(d, &dn)
            } else {
                None
            }
        });
        let original_import_attributes_type = original_module_specifier
            .and_then(|s| c.get_import_attributes_type_for_module_specifier(s));

        let mut file = get_declaration_of_kind_of_symbol(c, symbol, Kind::SourceFile);
        if file.is_none() {
            let equivalent_symbol = symbol_declarations(c, symbol).iter().find_map(|&d| {
                c.get_file_symbol_if_file_symbol_export_equals_container(d, symbol)
            });
            if let Some(equivalent_symbol) = equivalent_symbol {
                file = get_declaration_of_kind_of_symbol(c, equivalent_symbol, Kind::SourceFile);
            }
        }

        if file.is_none() {
            let declaration = symbol_declarations(c, symbol)
                .iter()
                .copied()
                .find(|&d| {
                    let dn = c.program_nodes(d);
                    ast::is_module_with_string_literal_name(&dn[d])
                });
            if let Some(declaration) = declaration {
                let dn = c.program_nodes(declaration);
                let specifier = tsc_tspath::to_module_specifier(&dn[declaration].text(&dn));
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
            let module_file = get_source_file_of_module_symbol(c, symbol);
            let specifier = module_file
                .map(|f| {
                    let fn_ = c.program_nodes(f);
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
            let fn_ = c.program_nodes(context_file);
            resolution_mode = host.as_ref().unwrap().get_mode_for_usage_location(
                fn_[context_file].as_source_file(),
                original_module_specifier.unwrap(),
            );
        } else if resolution_mode == RESOLUTION_MODE_NONE {
            let host = self.ctx.host.clone();
            let fn_ = c.program_nodes(context_file);
            resolution_mode = host
                .as_ref()
                .unwrap()
                .get_default_resolution_mode_for_file(fn_[context_file].as_source_file());
        }
        let cache_key = tsc_module::ModeAwareCacheKey {
            name: {
                let fn_ = c.program_nodes(context_file);
                fn_[context_file].as_source_file().path_key().as_string().to_owned()
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
        let file_nodes = c.program_nodes(context_file);
        let symbol_arena = c.symbol_arena.clone();
        let symbol_arena_ref = symbol_arena.borrow();
        let checker_adapter = CheckerShapeAdapter::new(&mut *c);
        // PORT(note): the `nodes` arena passed to modulespecifiers is the
        // destination arena; declaration NodeIds it dereferences may live in
        // other files' arenas — Go's single global heap hid this. Declared in
        // PORTING-NOTES.md.
        let module_specifiers_result = tsc_modulespecifiers::get_module_specifiers(
            symbol,
            &checker_adapter,
            &specifier_compiler_options,
            file_nodes[context_file].as_source_file(),
            &host_adapter,
            tsc_modulespecifiers::UserPreferences {
                import_module_specifier_preference: specifier_pref,
                import_module_specifier_ending: ending_pref,
                ..Default::default()
            },
            tsc_modulespecifiers::ModuleSpecifierOptions {
                override_import_mode,
            },
            false, // forAutoImports
            &symbol_arena_ref,
            nodes,
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
        self.module_specifier_result_for_symbol(
            c,
            result,
            original_import_attributes_type,
            symbol,
        )
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
        resolved.is_some()
            && c.get_merged_symbol(resolved.unwrap()) == c.get_merged_symbol(symbol)
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
            let name = self.new_string_literal(nodes, "resolution-mode");
            let value = self.new_string_literal(nodes, resolution_mode);
            attributes.push(self.f.new_import_attribute(nodes, name, Some(value)));
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
            let name_node = if scanner::utilities::is_identifier_text(&name, LanguageVariant::Standard) {
                self.f.new_identifier(nodes, &name)
            } else {
                self.ctx.approximate_length += 2;
                self.new_string_literal(nodes, &name)
            };
            let value_node = self.new_string_literal(nodes, &value);
            attributes.push(self.f.new_import_attribute(nodes, name_node, Some(value_node)));
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
        let modifiers =
            ast::create_modifiers_from_modifier_flags(modifier_flags, &mut |kind| {
                self.f.new_token(nodes, kind)
            });
        let modifiers_list = if !modifiers.is_empty() {
            Some(self.f.new_modifier_list(nodes, modifiers))
        } else {
            None
        };
        let name = self.type_parameter_to_name(c, nodes, type_parameter);
        let default_parameter = c.get_default_from_type_parameter(type_parameter);
        let default_parameter_declaration_node = default_parameter
            .map(|default| self.type_to_type_node(c, nodes, default));
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
    fn set_text_range(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        range_: Option<NodeId>,
        location: Option<NodeId>,
    ) -> Option<NodeId> {
        let Some(mut range_) = range_ else {
            return range_;
        };
        let range_nodes = c.program_nodes(range_);
        let most_original_of_range = self
            .e
            .borrow()
            .most_original(&range_nodes, range_)
            .unwrap_or(range_);
        let enclosing_file_matches = match (self.ctx.enclosing_file, most_original_of_range) {
            (Some(file), mo) => {
                let mo_nodes = c.program_nodes(mo);
                ast::get_source_file_of_node(mo, &mo_nodes) == Some(file)
            }
            _ => false,
        };
        if !ast::node_is_synthesized(&range_nodes[range_])
            || !range_nodes[range_]
                .flags
                .intersects(ast::NodeFlags::SYNTHESIZED)
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
        let location_nodes = c.program_nodes(location);
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
        let loc_nodes = c.program_nodes(location);
        let most_original_of_location = self
            .e
            .borrow()
            .most_original(&loc_nodes, location)
            .unwrap_or(location);
        let mo_nodes = c.program_nodes(most_original_of_location);
        if self.ctx.enclosing_file.is_some()
            && self.ctx.enclosing_file
                == ast::get_source_file_of_node(most_original_of_location, &mo_nodes)
        {
            let _ = location_nodes;
            nodes[range_].loc = loc_nodes[location].loc;
            return Some(range_);
        }
        nodes[range_].loc = tsc_core::text::TextRange::new(-1, -1);
        Some(range_)
    }

    /// `(b *NodeBuilderImpl) typeParameterShadowsOtherTypeParameterInScope`.
    fn type_parameter_shadows_other_type_parameter_in_scope(
        &mut self,
        c: &mut Checker,
        name: &str,
        type_parameter: TypeId,
    ) -> bool {
        let f = c.resolve_name.clone().expect("Checker::resolve_name");
        let result = f(
            c,
            self.ctx.enclosing_declaration,
            name,
            ast::SymbolFlags::TYPE,
            None,
            false,
            false,
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
        if self
            .ctx
            .flags
            .intersects(nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
            && let Some(&cached) = self.ctx.type_parameter_names.get(&type_parameter)
        {
            return cached;
        }
        let tp_symbol = type_symbol(c, type_parameter).unwrap_or(SymbolId::NONE);
        let mut result = self.symbol_to_name(c, nodes, tp_symbol, ast::SymbolFlags::TYPE, true);
        if !ast::is_identifier(&nodes[result]) {
            return self.f.new_identifier(nodes, "(Missing type parameter)");
        }
        let decls = if tp_symbol != SymbolId::NONE {
            symbol_declarations(c, tp_symbol)
        } else {
            Vec::new()
        };
        if !decls.is_empty() {
            let decl = decls[0];
            let decl_nodes = c.program_nodes(decl);
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
                result = self.new_identifier(
                    nodes,
                    &text,
                    type_symbol(c, type_parameter),
                );
                // setIdentifierTypeArguments(result, typeArguments);
            }

            // avoiding iterations of the above loop turns out to be worth it
            // when `i` starts to get large, so we cache the max `i` we've
            // used thus far, to save work later
            self.ctx
                .type_parameter_names_by_text_next_name_count
                .set(raw_text, i);
            self.ctx.type_parameter_names.set(type_parameter, result);
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
        let target = c.types.get(mapped).as_mapped_type().object_type.target;
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
            let mapped = c.types.get(t).as_mapped_type();
            let declaration = mapped.declaration;
            let (readonly_kind, question_kind, name_type_present) = declaration
                .map(|d| {
                    let dn = c.program_nodes(d);
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
        let mut appropriate_constraint_type_node: Option<NodeId> = None;
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
                let new_constraint_param =
                    c.new_type_parameter(Some(c.new_symbol(ast::SymbolFlags::TYPE_PARAMETER, "T")));
                let name = self.type_parameter_to_name(c, nodes, new_constraint_param);
                let target = c.types.get(t).target();
                new_type_variable =
                    Some(self.f.new_type_reference_node(nodes, Some(name), None));
                if let Some(target) = target {
                    let target_type_parameter = c.get_type_parameter_from_mapped_type(target);
                    let target_modifiers_type = c.get_modifiers_type_from_mapped_type(target);
                    let target_template = c.get_template_type_from_mapped_type(target);
                    if let (Some(tp), Some(mt), Some(tt)) =
                        (target_type_parameter, target_modifiers_type, target_template)
                    {
                        let mapper = crate::mapper::new_type_mapper_simple(
                            c,
                            &[tp, mt],
                            &[type_parameter.unwrap_or(TypeId::NONE), new_constraint_param],
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
            let new_param =
                c.new_type_parameter(Some(c.new_symbol(ast::SymbolFlags::TYPE_PARAMETER, "T")));
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
        let cleanup = self.enter_new_scope(
            c,
            nodes,
            declaration,
            None,
            Some(
                c.get_type_parameter_from_mapped_type(t)
                    .into_iter()
                    .collect::<Vec<_>>(),
            ),
            None,
            None,
        );
        let type_parameter_declaration_node = self
            .type_parameter_to_declaration_with_constraint(
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
        let include_optional = get_mapped_type_modifiers_local(c, t)
            .intersects(MappedTypeModifiers::INCLUDE_OPTIONAL);
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
                let dn = c.program_nodes(d);
                dn[d]
                    .as_mapped_type_node()
                    .type_parameter
                    .and_then(|tp| dn[tp].as_type_parameter_declaration().constraint)
                    .and_then(|cn| dn[cn].as_type_reference().map(|_| cn))
                    .map(|cn| self.get_type_from_type_node(c, cn, false))
                    .flatten()
            });
            if let Some(raw) = raw_constraint_type_from_declaration {
                raw_constraint_type_from_declaration = c.get_constraint_of_type_parameter(raw);
            }
            let raw_constraint_type_from_declaration =
                raw_constraint_type_from_declaration.unwrap_or(c.unknown_type);
            let mapped_mapper = c.types.get(t).as_mapped_type().object_type.mapper;
            let original_constraint =
                c.instantiate_type(raw_constraint_type_from_declaration, mapped_mapper);

            let original_constraint_node = if !type_flags(c, original_constraint)
                .intersects(TypeFlags::UNKNOWN)
            {
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
            return self.f.new_conditional_type_node(
                nodes,
                modifiers_node,
                Some(infer_node),
                Some(result),
                Some(self.f.new_keyword_type_node(nodes, Kind::NeverKeyword)),
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
            let keyof_node = self.f.new_type_operator_node(
                nodes,
                Kind::KeyOfKeyword,
                c.get_modifiers_type_from_mapped_type(t)
                    .map(|mt| self.type_to_type_node(c, nodes, mt)),
            );
            let infer_param = self.f.new_type_parameter_declaration(
                nodes,
                None,
                cloned_name,
                Some(keyof_node),
                None,
                None,
            );
            let infer_node = self.f.new_infer_type_node(nodes, Some(infer_param));
            return self.f.new_conditional_type_node(
                nodes,
                constraint_node,
                Some(infer_node),
                Some(result),
                Some(self.f.new_keyword_type_node(nodes, Kind::NeverKeyword)),
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
        let asserts_modifier = if predicate.kind == TypePredicateKind::ASSERTS_IDENTIFIER
            || predicate.kind == TypePredicateKind::ASSERTS_THIS
        {
            Some(self.f.new_token(nodes, Kind::AssertsKeyword))
        } else {
            None
        };
        let parameter_name = if predicate.kind == TypePredicateKind::IDENTIFIER
            || predicate.kind == TypePredicateKind::ASSERTS_IDENTIFIER
        {
            let parameter_name = self.f.new_identifier(nodes, &predicate.parameter_name);
            self.e
                .borrow()
                .add_emit_flags(parameter_name, printer::EmitFlags::NO_ASCII_ESCAPING);
            parameter_name
        } else {
            self.f.new_this_type_node(nodes)
        };
        let type_node = predicate
            .t
            .map(|t| self.type_to_type_node(c, nodes, t));
        self.f.new_type_predicate_node(
            nodes,
            asserts_modifier,
            Some(parameter_name),
            type_node,
        )
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
            && self.get_type_from_type_node(c, type_node.unwrap(), false) == Some(t)
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
    fn type_parameter_to_declaration(
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
        self.type_parameter_to_declaration_with_constraint(
            c,
            nodes,
            parameter,
            constraint_node,
        )
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
            let params =
                c.get_local_type_parameters_of_class_or_interface_or_type_alias(symbol);
            for param in params.iter().copied().flatten() {
                results.push(self.type_parameter_to_declaration(c, nodes, param));
            }
            return results;
        } else if target_flags.intersects(ast::SymbolFlags::FUNCTION) {
            let mut results = Vec::new();
            let value_declaration = symbol_value_declaration(c, symbol);
            let params = value_declaration
                .map(|d| c.get_type_parameters_from_declaration(d))
                .unwrap_or_default();
            for param in params.into_iter().flatten() {
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
        let parameter_declaration = get_effective_parameter_declaration(c, parameter_symbol);

        let parameter_type = c.get_type_of_symbol(parameter_symbol);
        let parameter_type_node = self.serialize_type_for_declaration(
            c,
            nodes,
            parameter_declaration,
            Some(parameter_type),
            parameter_symbol,
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
            let pd_nodes = c.program_nodes(parameter_declaration);
            if ast::can_have_modifiers(&pd_nodes[parameter_declaration]) {
                let originals: Vec<NodeId> = pd_nodes[parameter_declaration]
                    .modifier_nodes(&pd_nodes)
                    .iter()
                    .copied()
                    .filter(|&m| ast::is_modifier(&pd_nodes[m]))
                    .collect();
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
            let pd_nodes = c.program_nodes(d);
            is_rest_parameter(&pd_nodes, d)
        }) || symbol_check_flags(c, parameter_symbol)
            .intersects(ast::checkflags::CheckFlags::REST_PARAMETER);
        let dot_dot_dot_token = if is_rest {
            Some(self.f.new_token(nodes, Kind::DotDotDotToken))
        } else {
            None
        };
        let name =
            self.parameter_to_parameter_declaration_name(c, nodes, parameter_symbol, parameter_declaration);
        let is_optional = parameter_declaration.is_some_and(|d| {
            c.is_optional_parameter(d)
        }) || symbol_check_flags(c, parameter_symbol)
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
        self.ctx.approximate_length +=
            (symbol_name(c, parameter_symbol).len() + 3) as i32;
        parameter_node
    }

    /// `(b *NodeBuilderImpl) parameterToParameterDeclarationName`.
    fn parameter_to_parameter_declaration_name(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        parameter_symbol: SymbolId,
        parameter_declaration: Option<NodeId>,
    ) -> Option<NodeId> {
        let name = parameter_declaration.and_then(|d| {
            let pd_nodes = c.program_nodes(d);
            pd_nodes[d].name()
        });
        let Some(name) = name else {
            return Some(self.new_identifier(
                nodes,
                &symbol_name(c, parameter_symbol),
                Some(parameter_symbol),
            ));
        };
        let name_nodes = c.program_nodes(name);
        match name_nodes[name].kind {
            Kind::Identifier => {
                let cloned = self.f.deep_clone_node(nodes, name);
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
                let cloned = right.and_then(|r| self.f.deep_clone_node(nodes, r));
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
            let src_nodes = c.program_nodes(node);
            let mut tmp = (*src_nodes).clone();
            let tmp_base = tmp.len();
            let dest_base = nodes.len();
            let root = self.clone_binding_name_in_arena(c, &mut tmp, node);
            return self.relocate_cloned_tail(nodes, &mut tmp, tmp_base, dest_base, root);
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
        let c = c_cell.into_inner();
        let _ = c;

        // Binding elements lose their initializer.
        let visited = if ast::is_binding_element(&arena[visited]) {
            let (dot_dot_dot, property_name, name) = {
                let binding_element = arena[visited].as_binding_element();
                (
                    binding_element.dot_dot_dot_token,
                    binding_element.property_name,
                    binding_element.name(),
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
    /// The clone pass minted ids in `tmp`-space (`file_index` = dest file,
    /// local index into `tmp`). Since `NodeData` has no mutable child-field
    /// walker, a second `visit_each_child` pass rebuilds every node with
    /// children rewritten to dest-space ids, producing a second tail; both
    /// tails are then appended to `nodes` in order so that
    /// `tmp_id.local - tmp_base + dest_base` is the dest position of every
    /// cloned node (pass-2 parents reference the dest ids of pass-2
    /// children — consistent because tails move contiguously).
    fn relocate_cloned_tail(
        &mut self,
        nodes: &mut Vec<ast::Node>,
        tmp: &mut Vec<ast::Node>,
        tmp_base: usize,
        dest_base: usize,
        root: NodeId,
    ) -> NodeId {
        let dest_file_index = self.f.file_index();
        let remap = move |id: NodeId| -> NodeId {
            if id.is_none() {
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
        let tail_len = tmp.len() - tmp_base;
        for i in 0..tail_len {
            let mut n = tmp[tmp_base + i].clone();
            n.id = NodeId::new(dest_file_index, (dest_base + i) as u64);
            nodes.push(n);
        }
        // Copy emit-table entries minted with tmp-space ids onto dest ids.
        for i in 0..tail_len {
            let tmp_id = NodeId::new(dest_file_index, (tmp_base + i) as u64);
            let dest_id = NodeId::new(dest_file_index, (dest_base + i) as u64);
            let flags = self.e.borrow().emit_flags(tmp_id);
            if !flags.is_empty() {
                self.e.borrow().set_emit_flags(dest_id, flags);
            }
            if let Some(original) = self.e.borrow().original(tmp_id) {
                let remapped_original = if original.local_index() as usize >= tmp_base {
                    // Originals minted during the clone are remapped;
                    // originals pointing into the source arena keep their
                    // source-file ids.
                    NodeId::new(
                        dest_file_index,
                        (dest_base + (original.local_index() as usize - tmp_base)) as u64,
                    )
                } else {
                    original
                };
                self.e
                    .borrow()
                    .set_original_ex(dest_id, remapped_original, false);
            }
            if let Some(&symbol) = self.id_to_symbol.get(&tmp_id) {
                self.id_to_symbol.insert(dest_id, symbol);
            }
        }
        root_dest
    }

    /// `(b *NodeBuilderImpl) serializeTypeForExpression`.
    fn serialize_type_for_expression(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        expr: NodeId,
    ) -> NodeId {
        // !!! TODO: shim, add node reuse
        let widened = c.get_widened_type(get_regular_type_of_expression(c, expr));
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
                c.instantiate_type_predicate(type_predicate, Some(mapper))
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
        let asserts_modifier = if type_predicate.kind == TypePredicateKind::ASSERTS_THIS
            || type_predicate.kind == TypePredicateKind::ASSERTS_IDENTIFIER
        {
            Some(self.f.new_token(nodes, Kind::AssertsKeyword))
        } else {
            None
        };
        let parameter_name = if type_predicate.kind == TypePredicateKind::IDENTIFIER
            || type_predicate.kind == TypePredicateKind::ASSERTS_IDENTIFIER
        {
            let parameter_name =
                self.new_identifier(nodes, &type_predicate.parameter_name, None);
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
fn get_access_stack(nodes: &[ast::Node], node: NodeId) -> Vec<NodeId> {
    let mut stack = Vec::new();
    let mut current = node;
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

/// `isExpanding` (nodebuilder_hover.go) — declared here since
/// `createTypeNodesFromResolvedType` uses it; hover-specific code lands in
/// nodebuilder_hover.rs.
fn is_expanding(ctx: &NodeBuilderContext) -> bool {
    ctx.max_expansion_depth != -1
}

/// `isReservedMemberName` (utilities.go:1677) — a reserved member name
/// consists of the byte 0xFE (invalid UTF-8 start) followed by one or more
/// characters where the first is not `@` or `#`. PORT: file-local until
/// utilities.go's copy lands.
fn is_reserved_member_name(name: &str) -> bool {
    let b = name.as_bytes();
    b.len() >= 2 && b[0] == 0xFE && b[1] != b'@' && b[1] != b'#'
}

/// `IsPrivateIdentifierSymbol` (utilities.go:1022). PORT: file-local until
/// utilities.go's copy lands.
fn is_private_identifier_symbol(c: &Checker, symbol: SymbolId) -> bool {
    if symbol == SymbolId::NONE {
        return false;
    }
    c.symbol_arena.borrow()[symbol.index()]
        .name
        .starts_with(&(ast::symbol::INTERNAL_SYMBOL_NAME_PREFIX.to_string() + "#"))
}

/// `containsNonMissingUndefinedType` (utilities.go:1647). PORT: file-local
/// until utilities.go's copy lands.
fn contains_non_missing_undefined_type(c: &Checker, t: TypeId) -> bool {
    let candidate = if type_flags(c, t).intersects(TypeFlags::UNION) {
        c.types
            .get(t)
            .as_union_type()
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
fn get_name_from_index_info(c: &Checker, info: IndexInfoId) -> String {
    if let Some(declaration) = c.index_info_arena.get(info).declaration {
        let nodes = c.program_nodes(declaration);
        if let Some(first_param) = nodes[declaration]
            .as_index_signature_declaration()
            .parameters
            .as_ref()
            .and_then(|l| l.nodes.first())
        {
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
fn get_mapped_type_modifiers_local(c: &Checker, t: TypeId) -> MappedTypeModifiers {
    let Some(declaration) = c.types.get(t).as_mapped_type().declaration else {
        return MappedTypeModifiers::NONE;
    };
    let nodes = c.program_nodes(declaration);
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
pub(crate) fn get_target_symbol(c: &Checker, s: SymbolId) -> SymbolId {
    if symbol_check_flags(c, s).intersects(ast::checkflags::CheckFlags::INSTANTIATED) {
        if let Some(target) = c.value_symbol_links.get(s).target {
            return target;
        }
    }
    s
}

/// `c.getRegularTypeOfExpression` (checker.go:32668). PORT: file-local until
/// checker.go's copy lands.
fn get_regular_type_of_expression(c: &mut Checker, expr: NodeId) -> TypeId {
    let mut expr = expr;
    let nodes = c.program_nodes(expr);
    if ast::is_right_side_of_qualified_name_or_property_access(&nodes[expr]) {
        if let Some(parent) = nodes[expr].parent {
            expr = parent;
        }
    }
    c.get_regular_type_of_literal_type(c.get_type_of_expression(expr))
}

/// Shared state for the `cloneBindingName` visitor — the `b`/`c` pieces the
/// per-node visit fn needs, routed through cells since `VisitFn` is `Fn`
/// (not `FnMut`) and `cx.factory` already borrows `self.f`.
struct CloneBindingShared<'s, 'x> {
    /// `b.ch` — `RefCell` so the `Fn` visit fn can call `&mut` methods.
    c: &'s RefCell<&'x mut Checker>,
    /// `b.ctx.tracker`.
    tracker: Option<Rc<RefCell<dyn nodebuilder::SymbolTracker>>>,
    /// `b.ctx.enclosingDeclaration`.
    enclosing_declaration: Option<NodeId>,
    /// `b.e`.
    e: Rc<RefCell<EmitContext>>,
}

/// `(b *NodeBuilderImpl) trackComputedName` on shared state — the visit-fn
/// path. `track_computed_name` (method) wraps this for direct callers.
fn track_computed_name_shared(
    shared: &CloneBindingShared<'_, '_>,
    nodes: &[ast::Node],
    access_expression: NodeId,
) {
    // get symbol of the first identifier of the entityName
    let first_identifier = ast::get_first_identifier(access_expression, nodes);
    let text = nodes[first_identifier].text(nodes).into_owned();
    let mut cm = shared.c.borrow_mut();
    let resolve = cm.resolve_name.clone().expect("Checker::resolve_name");
    let name = resolve(
        &mut cm,
        shared.enclosing_declaration,
        &text,
        ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE,
        None,
        true, // isUse
        false,
    );
    let tracked = if let Some(name) = name {
        Some(name)
    } else {
        // Name does not resolve at target location, track symbol at dest
        // location (should be inaccessible)
        let resolve = cm.resolve_name.clone().expect("Checker::resolve_name");
        resolve(
            &mut cm,
            Some(first_identifier),
            &text,
            ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE,
            None,
            true,
            false,
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
        );
    }
}

/// The `cloneBindingName` visit fn — the body of Go's `cloneBindingName`
/// applied per visited node.
fn clone_binding_name_visit(
    shared: &CloneBindingShared<'_, '_>,
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
                binding_element.name(),
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
        return !rest.is_empty() && scanner::utilities::is_identifier_text(rest, LanguageVariant::Standard);
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
            nodes[module_call].arguments().first().copied()
        }
        Kind::ImportDeclaration | Kind::ExportDeclaration | Kind::JSDocImportTag => {
            nodes[node].module_specifier()
        }
        Kind::ImportEqualsDeclaration => {
            let ref_ = nodes[node].as_import_equals_declaration().module_reference?;
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
fn get_declaration_of_kind_of_symbol(c: &Checker, symbol: SymbolId, kind: Kind) -> Option<NodeId> {
    symbol_declarations(c, symbol)
        .iter()
        .copied()
        .find(|&d| c.program_nodes(d)[d].kind == kind)
}

/// `ast.GetSourceFileOfModule` on a `SymbolId` — Go walks
/// `value_declaration`/`GetNonAugmentationDeclaration` then
/// `GetSourceFileOfNode`; each step here routes through `program_nodes`.
fn get_source_file_of_module_symbol(c: &Checker, symbol: SymbolId) -> Option<NodeId> {
    let (value_declaration, declarations) = {
        let arena = c.symbol_arena.borrow();
        let s = &arena[symbol.index()];
        (s.value_declaration, s.declarations.clone())
    };
    let declaration = value_declaration.or_else(|| {
        // `GetNonAugmentationDeclaration`.
        declarations.iter().copied().find(|&d| {
            let dn = c.program_nodes(d);
            !ast::is_external_module_augmentation(&dn[d], &dn)
                && !ast::is_global_scope_augmentation(&dn[d])
        })
    });
    declaration
        .and_then(|d| ast::get_source_file_of_node(Some(d), &c.program_nodes(d)))
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
        // `get_symlink_cache` borrows from the host; the trait-object can't
        // return a borrow through the Rc, so this is a PORT(deferred) gap.
        // Go's host returns the program's cache; the underlying call is
        // nil-safe in modulespecifiers.
        None
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
    ) -> Option<std::sync::Arc<tsc_tsoptions::parsedcommandline::SourceOutputAndProjectReference>> {
        self.0.get_project_reference_from_source(path)
    }
    fn get_redirect_targets(&self, path: &tsc_tspath::PathKey) -> Vec<tsc_tspath::RootedFilePath> {
        self.0.get_redirect_targets(path)
    }
    fn get_source_of_project_reference_if_output_included(
        &self,
        file: &dyn ast::HasFileName,
    ) -> tsc_tspath::RootedFilePath {
        self.0.get_source_of_project_reference_if_output_included(file)
    }
    fn file_exists(&self, path: &tsc_tspath::RootedFilePath) -> bool {
        self.0.file_exists(path)
    }
    fn get_nearest_ancestor_directory_with_package_json(
        &self,
        dirname: &tsc_tspath::RootedDirectoryPath,
    ) -> tsc_tspath::RootedDirectoryPath {
        self.0.get_nearest_ancestor_directory_with_package_json(dirname)
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
        self.0.get_resolved_module_from_module_specifier(file, module_specifier)
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
        // PORT(deferred): `Checker::GetSymbolAtLocation` (checker.go:32134)
        // is not yet ported — the trait requires `&self` anyway, so it must
        // be routed through a RefCell once it lands.
        let _ = (&self.c, node);
        unimplemented!("PORT(deferred): Checker::get_symbol_at_location")
    }
    fn get_aliased_symbol(&self, symbol: SymbolId) -> SymbolId {
        self.c.borrow_mut().resolve_alias(symbol)
    }
}
