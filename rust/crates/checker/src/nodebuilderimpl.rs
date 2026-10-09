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
use tsc_core::core::ResolutionMode;
use tsc_core::linkstore::LinkStore;
use tsc_jsnum as jsnum;
use tsc_nodebuilder as nodebuilder;
use tsc_printer::{self as printer, EmitContext};
use tsc_pseudochecker::{self as pseudochecker, PseudoType, PseudoTypeKind, PseudoTypeRef};
use tsc_scanner as scanner;
use tsc_stringutil as stringutil;

use crate::checker_core::{CacheHashKey, Checker};
use crate::checker_types::Host;
use crate::mapper::TypeMapperId;
use crate::nodebuilderscopes::collect_binding_pattern_symbols;
use crate::types::{
    ConditionalType, ElementFlags, IndexInfo, IndexInfoId, MappedTypeModifiers, ObjectFlags,
    Signature, SignatureFlags, SignatureId, SignatureKind, TypeAlias, TypeFlags, TypeId,
    TypeParameter, TypePredicate, TypePredicateKind,
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
fn symbol_check_flags(c: &Checker, s: SymbolId) -> ast::CheckFlags {
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
    ast::escape_symbol_name(&c.symbol_arena.borrow()[s.index()].name).into_owned()
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
            self.ctx.flags ^= nodebuilder::Flags::IN_INITIAL_ENTITY_NAME;
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
}
