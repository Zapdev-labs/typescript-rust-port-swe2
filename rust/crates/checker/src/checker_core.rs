// PORT(partial) — scaffolding shared by the foundation-phase port.
//
// This file is NOT a port of any single Go file. It collects:
//
// 1. Small support types from `tsc/internal/checker/checker.go`
//    (`CacheHashKey`, `CheckMode`, inference bookkeeping types) that the
//    ported foundation files reference.
// 2. A `PORT(partial)` `Checker` stub exposing exactly the fields and method
//    signatures the ported files call. Method bodies are deferred to the
//    checker.rs agent; each stub is `unimplemented!` with a
//    `PORT(deferred)` note naming its Go origin.
// 3. Free helpers mirrored verbatim from deferred Go files (`utilities.go`,
//    `checker.go`, `relater.go`, `inference.go`) because `mapper.go` and
//    `tracer.go` call them. Each is tagged `// PORT(mirrored)` — when the
//    deferred file lands, these move home.
// 4. `JsxFlags`/`JsxElementLinks` placeholders for the `jsx_element_links`
//    link store (jsx.go is deferred entirely).

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::{Arc, RwLock};

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, NodeId, SymbolId};
use tsc_collections::OrderedSet;
use tsc_core::linkstore::LinkStore;
use tsc_evaluator as evaluator;
use tsc_tracing as tracing;

use crate::flagdef::flag_type;
use crate::links::{NodeLinkStore, SymbolArenaLinkStore};
use crate::mapper::{TypeMapperArena, TypeMapperId};
use crate::tracer::Tracer;
use crate::types::{
    AliasSymbolLinks, AssertionLinks, ArrayLiteralLinks, ComputedNameNodeLinks,
    ContainingSymbolLinks, DeclaredTypeLinks, DeferredSymbolLinks, EnumMemberLinks,
    ExportTypeLinks, LateBoundLinks, MappedSymbolLinks, MarkedAssignmentSymbolLinks,
    MembersAndExportsLinks, ModuleSymbolLinks, NodeLinks, ObjectFlags, ReverseMappedSymbolLinks,
    Signature, SignatureArena, SignatureId, SignatureLinks, SourceFileLinks, SpreadLinks,
    SwitchStatementLinks, SymbolNodeLinks, SymbolReferenceLinks, Type, TypeAliasLinks, TypeArena,
    TypeData, TypeFlags, TypeId, TypeNodeLinks, TypeParameter, ValueSymbolLinks, VarianceLinks,
};

/// `type CacheHashKey xxh3.Uint128` (checker.go) — `tsc_ast::Uint128` is the
/// existing port of `xxh3.Uint128`.
pub type CacheHashKey = ast::Uint128;

// CheckMode

flag_type! {
    /// `type CheckMode uint32` (checker.go).
    pub struct CheckMode(pub u32);
}

impl CheckMode {
    /// `CheckModeNormal` — normal type checking.
    pub const NORMAL: CheckMode = CheckMode(0);
    /// `CheckModeContextual` — explicitly assigned contextual type,
    /// therefore not cacheable.
    pub const CONTEXTUAL: CheckMode = CheckMode(1 << 0);
    /// `CheckModeInferential` — inferential typing.
    pub const INFERENTIAL: CheckMode = CheckMode(1 << 1);
    /// `CheckModeSkipContextSensitive` — skip context sensitive function
    /// expressions.
    pub const SKIP_CONTEXT_SENSITIVE: CheckMode = CheckMode(1 << 2);
    /// `CheckModeSkipGenericFunctions` — skip single signature generic
    /// functions.
    pub const SKIP_GENERIC_FUNCTIONS: CheckMode = CheckMode(1 << 3);
    /// `CheckModeIsForSignatureHelp` — call resolution for purposes of
    /// signature help.
    pub const IS_FOR_SIGNATURE_HELP: CheckMode = CheckMode(1 << 4);
    /// `CheckModeRestBindingElement` — checking a type that is going to be
    /// used to determine the type of a rest binding element.
    pub const REST_BINDING_ELEMENT: CheckMode = CheckMode(1 << 5);
    /// `CheckModeTypeOnly` — called from `getTypeOfExpression`, diagnostics
    /// may be omitted.
    pub const TYPE_ONLY: CheckMode = CheckMode(1 << 6);
    /// `CheckModeForceTuple`.
    pub const FORCE_TUPLE: CheckMode = CheckMode(1 << 7);
}

// InferenceFlags

flag_type! {
    /// `type InferenceFlags uint32` (checker.go).
    pub struct InferenceFlags(pub u32);
}

impl InferenceFlags {
    /// `InferenceFlagsNoDefault` — infer silentNeverType for no inferences
    /// (otherwise anyType or unknownType).
    pub const NO_DEFAULT: InferenceFlags = InferenceFlags(1 << 0);
    /// `InferenceFlagsAnyDefault` — infer anyType (in JS files) for no
    /// inferences (otherwise unknownType).
    pub const ANY_DEFAULT: InferenceFlags = InferenceFlags(1 << 1);
    /// `InferenceFlagsSkippedGenericFunction` — a generic function was
    /// skipped during inference.
    pub const SKIPPED_GENERIC_FUNCTION: InferenceFlags = InferenceFlags(1 << 2);
    /// `InferenceFlagsNoConstraintChecks`.
    pub const NO_CONSTRAINT_CHECKS: InferenceFlags = InferenceFlags(1 << 3);
}

// InferencePriority

flag_type! {
    /// `type InferencePriority int32` (checker.go).
    pub struct InferencePriority(pub i32);
}

impl InferencePriority {
    /// `InferencePriorityNone`.
    pub const NONE_PRIORITY: InferencePriority = InferencePriority(0);
    /// `InferencePriorityNakedTypeVariable` — naked type variable in union
    /// or intersection type.
    pub const NAKED_TYPE_VARIABLE: InferencePriority = InferencePriority(1 << 0);
    /// `InferencePrioritySpeculativeTuple` — speculative tuple inference.
    pub const SPECULATIVE_TUPLE: InferencePriority = InferencePriority(1 << 1);
    /// `InferencePrioritySubstituteSource` — source of inference originated
    /// within a substitution type's substitute.
    pub const SUBSTITUTE_SOURCE: InferencePriority = InferencePriority(1 << 2);
    /// `InferencePriorityHomomorphicMappedType` — reverse inference for
    /// homomorphic mapped type.
    pub const HOMOMORPHIC_MAPPED_TYPE: InferencePriority = InferencePriority(1 << 3);
    /// `InferencePriorityPartialHomomorphicMappedType` — partial reverse
    /// inference for homomorphic mapped type.
    pub const PARTIAL_HOMOMORPHIC_MAPPED_TYPE: InferencePriority = InferencePriority(1 << 4);
    /// `InferencePriorityMappedTypeConstraint` — reverse inference for
    /// mapped type.
    pub const MAPPED_TYPE_CONSTRAINT: InferencePriority = InferencePriority(1 << 5);
    /// `InferencePriorityContravariantConditional` — conditional type in
    /// contravariant position.
    pub const CONTRAVARIANT_CONDITIONAL: InferencePriority = InferencePriority(1 << 6);
    /// `InferencePriorityReturnType` — inference made from return type of
    /// generic function.
    pub const RETURN_TYPE: InferencePriority = InferencePriority(1 << 7);
    /// `InferencePriorityLiteralKeyof` — inference made from a string
    /// literal to a keyof T.
    pub const LITERAL_KEYOF: InferencePriority = InferencePriority(1 << 8);
    /// `InferencePriorityNoConstraints` — don't infer from constraints of
    /// instantiable types.
    pub const NO_CONSTRAINTS: InferencePriority = InferencePriority(1 << 9);
    /// `InferencePriorityAlwaysStrict` — always use strict rules for
    /// contravariant inferences.
    pub const ALWAYS_STRICT: InferencePriority = InferencePriority(1 << 10);
    /// `InferencePriorityMaxValue` — seed for inference priority tracking.
    pub const MAX_VALUE: InferencePriority = InferencePriority(1 << 11);
    /// `InferencePriorityCircularity` — inference circularity (value less
    /// than all other priorities).
    pub const CIRCULARITY: InferencePriority = InferencePriority(-1);

    /// `InferencePriorityPriorityImpliesCombination` — these priorities
    /// imply that the resulting type should be a combination of all
    /// candidates.
    pub const PRIORITY_IMPLIES_COMBINATION: InferencePriority = InferencePriority(
        Self::RETURN_TYPE.0 | Self::MAPPED_TYPE_CONSTRAINT.0 | Self::LITERAL_KEYOF.0,
    );
}

// InferenceContext

/// `type InferenceContext struct` (checker.go).
#[derive(Default)]
pub struct InferenceContext {
    /// `inferences` — inferences made for each type parameter. Go stores
    /// `[]*InferenceInfo` and mutates through the pointer; a plain `Vec`
    /// with index mutation is equivalent.
    pub inferences: Vec<InferenceInfo>,
    /// `signature` — generic signature for which inferences are made
    /// (if any).
    pub signature: Option<SignatureId>,
    /// `flags` — inference flags.
    pub flags: InferenceFlags,
    /// `compareTypes` — type comparer function.
    pub compare_types: Option<Box<crate::types::TypeComparer<'static>>>,
    /// `mapper` — mapper that fixes inferences.
    pub mapper: Option<TypeMapperId>,
    /// `nonFixingMapper` — mapper that doesn't fix inferences.
    pub non_fixing_mapper: Option<TypeMapperId>,
    /// `returnMapper` — type mapper for inferences from return types
    /// (if any).
    pub return_mapper: Option<TypeMapperId>,
    /// `outerReturnMapper` — type mapper for inferences from return types of
    /// outer function (if any).
    pub outer_return_mapper: Option<TypeMapperId>,
    /// `inferredTypeParameters` — inferred type parameters for function
    /// result.
    pub inferred_type_parameters: Vec<TypeId>,
    /// `intraExpressionInferenceSites`.
    pub intra_expression_inference_sites: Vec<IntraExpressionInferenceSite>,
}

/// `type InferenceContextId uint32` — index into `Checker::inference_contexts`
/// (Go `*InferenceContext`).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[repr(transparent)]
pub struct InferenceContextId(pub u32);

impl InferenceContextId {
    /// The absent value.
    pub const NONE: InferenceContextId = InferenceContextId(u32::MAX);

    /// The arena index of this id.
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// `type InferenceInfo struct` (checker.go).
#[derive(Default)]
pub struct InferenceInfo {
    /// `typeParameter` — type parameter for which inferences are being made.
    pub type_parameter: Option<TypeId>,
    /// `candidates` — candidates in covariant positions in decreasing depth
    /// order.
    pub candidates: Vec<TypeId>,
    /// `contraCandidates` — candidates in contravariant positions.
    pub contra_candidates: Vec<TypeId>,
    /// `inferredType` — cache for resolved inferred type.
    pub inferred_type: Option<TypeId>,
    /// `priority` — priority of current inference set.
    pub priority: InferencePriority,
    /// `topLevel` — true if all inferences are to top level occurrences.
    pub top_level: bool,
    /// `isFixed` — true if inferences are fixed.
    pub is_fixed: bool,
    /// `impliedArity` — implied arity (or -1).
    pub implied_arity: i32,
}

/// `type IntraExpressionInferenceSite struct` (checker.go).
#[derive(Default)]
pub struct IntraExpressionInferenceSite {
    /// `node`.
    pub node: Option<NodeId>,
    /// `t`.
    pub t: Option<TypeId>,
}

/// `type InferenceContextInfo struct` (checker.go).
#[derive(Default)]
pub struct InferenceContextInfo {
    /// `node`.
    pub node: Option<NodeId>,
    /// `context`.
    pub context: Option<InferenceContextId>,
}

// WideningKind

/// `type WideningKind int32` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum WideningKind {
    /// `WideningKindNormal`
    #[default]
    Normal = 0,
    /// `WideningKindFunctionReturn`
    FunctionReturn = 1,
    /// `WideningKindGeneratorNext`
    GeneratorNext = 2,
    /// `WideningKindGeneratorYield`
    GeneratorYield = 3,
}

// EnumLiteralKey

/// `type EnumLiteralKey struct` (checker.go).
#[derive(Clone, Debug)]
pub struct EnumLiteralKey {
    /// `enumSymbol`.
    pub enum_symbol: Option<SymbolId>,
    /// `value`.
    pub value: Option<evaluator::Value>,
}

// JsxFlags / JsxElementLinks — placeholders mirrored from jsx.go (deferred).

flag_type! {
    /// `type JsxFlags uint32` (jsx.go — deferred file; only the flag type is
    /// needed for `JsxElementLinks` to compile).
    /// PORT(deferred): constant values land with jsx.go.
    pub struct JsxFlags(pub u32);
}

/// `type JsxElementLinks struct` (jsx.go — deferred file).
/// PORT(deferred): fields ported now so `jsx_element_links` compiles; the
/// jsx.go agent owns additions.
#[derive(Default)]
pub struct JsxElementLinks {
    /// `jsxFlags`.
    pub jsx_flags: JsxFlags,
    /// `resolvedJsxElementAttributesType`.
    pub resolved_jsx_element_attributes_type: Option<TypeId>,
    /// `jsxNamespace`.
    pub jsx_namespace: Option<SymbolId>,
    /// `jsxImplicitImportContainer`.
    pub jsx_implicit_import_container: Option<SymbolId>,
    /// `firstJSXTagInFile`.
    pub first_jsx_tag_in_file: Option<NodeId>,
}

// RecursionId — `type RecursionId struct { value any }` (relater.go).

/// `type RecursionId struct` (relater.go — deferred file; mirrored because
/// `tracer.go` reads `.value`).
///
/// PORT: `value any` held `*ast.Node | *ast.Symbol | *Type` and Go keyed
/// `map[any]int` on kind+pointer. `tracing::RecursionIdentity` is the
/// hashable port — `Object` tokens are kind-tagged (high bits) so ids of
/// different kinds never collide. See `as_recursion_id_*` below.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct RecursionId {
    /// `value`.
    pub value: tracing::RecursionIdentity,
}

/// `asRecursionId` for `*ast.Node` (relater.go).
fn as_recursion_id_node(node: NodeId) -> RecursionId {
    RecursionId {
        value: tracing::RecursionIdentity::Object(node.0),
    }
}

// Symbol/type tokens live in the top tag bits of the u64. NodeId occupies
// `file:20|local:44`, so a collision with a tagged symbol/type token would
// require a file index ≥ 2^18 — far above `NodeId::MAX_FILE_INDEX`-bounded
// real programs. (Go keys on type-tagged pointers, which cannot collide;
// this reproduces that distinctness within one checker's map.)
const RECURSION_ID_SYMBOL_TAG: u64 = 1 << 62;
const RECURSION_ID_TYPE_TAG: u64 = 2 << 62;

/// `asRecursionId` for `*ast.Symbol` (relater.go).
fn as_recursion_id_symbol(symbol: SymbolId) -> RecursionId {
    RecursionId {
        value: tracing::RecursionIdentity::Object(RECURSION_ID_SYMBOL_TAG | symbol.0 as u64),
    }
}

/// `asRecursionId` for `*Type` (relater.go).
fn as_recursion_id_type(t: TypeId) -> RecursionId {
    RecursionId {
        value: tracing::RecursionIdentity::Object(RECURSION_ID_TYPE_TAG | t.0 as u64),
    }
}

// Mirrored free helpers — small functions from deferred Go files that the
// ported foundation files call.

/// `isThisTypeParameter` (utilities.go:1056 — deferred file; mirrored for
/// mapper.rs `MapsThisOnly`). PORT(mirrored): takes the type arena for the
/// `*Type` dereference.
pub fn is_this_type_parameter(types: &TypeArena, t: TypeId) -> bool {
    let ty = types.get(t);
    ty.flags.intersects(TypeFlags::TYPE_PARAMETER) && ty.as_type_parameter().is_this_type
}

/// `isObjectOrArrayLiteralType` (utilities.go:1033 — deferred file;
/// mirrored for `get_recursion_identity_from_target`).
pub fn is_object_or_array_literal_type(t: &Type) -> bool {
    t.object_flags
        .intersects(ObjectFlags::OBJECT_LITERAL | ObjectFlags::ARRAY_LITERAL)
}

/// `isTupleType` (checker.go:24013 — deferred file; mirrored for
/// `get_recursion_identity_from_target` and `types.rs` docs).
/// PORT(mirrored): `t.Target()` dereferences a sibling element, so the arena
/// is a parameter.
pub fn is_tuple_type(types: &TypeArena, t: TypeId) -> bool {
    let ty = types.get(t);
    if !ty.object_flags.intersects(ObjectFlags::REFERENCE) {
        return false;
    }
    let Some(target) = ty.target() else {
        return false;
    };
    types.get(target).object_flags.intersects(ObjectFlags::TUPLE)
}

/// `IsTupleType` — exported sibling (checker.go `IsTupleType` is in
/// exports.go, deferred; this mirrors `isTupleType`).
pub fn is_tuple_type_exported(types: &TypeArena, t: TypeId) -> bool {
    is_tuple_type(types, t)
}

/// `getNonDistributedTypeParameter` (checker.go:23533 — deferred file;
/// mirrored for mapper.rs factory functions).
pub fn get_non_distributed_type_parameter(types: &TypeArena, t: TypeId) -> TypeId {
    {
        let ty = types.get(t);
        if ty.flags.intersects(TypeFlags::TYPE_PARAMETER) {
            let tp: &TypeParameter = ty.as_type_parameter();
            if tp.is_distributed {
                if let Some(c) = tp.constraint {
                    return c;
                }
            }
        }
    }
    t
}

/// `ValueToString` (utilities.go:1749 — deferred file; mirrored for
/// `LiteralType`'s `Display`). PORT: `printer.EscapeString` comes from
/// tsc-printer.
pub fn value_to_string(value: Option<&evaluator::Value>) -> String {
    match value {
        Some(evaluator::Value::String(s)) => {
            format!("\"{}\"", tsc_printer::escape_string(s, tsc_printer::QuoteChar::DoubleQuote))
        }
        Some(evaluator::Value::Number(n)) => n.to_string(),
        Some(evaluator::Value::Bool(b)) => {
            if *b {
                "true".to_string()
            } else {
                "false".to_string()
            }
        }
        Some(evaluator::Value::PseudoBigInt(b)) => format!("{b}n"),
        None => panic!("unhandled value type in valueToString"),
    }
}

/// `clearCachedInferences` (inference.go:1655 — deferred file; mirrored for
/// `InferenceTypeMapper::map`).
pub fn clear_cached_inferences(inferences: &mut [InferenceInfo]) {
    for inference in inferences.iter_mut() {
        if !inference.is_fixed {
            inference.inferred_type = None;
        }
    }
}

/// `getRecursionIdentity` (relater.go — deferred file; mirrored for
/// tracer.rs). PORT(mirrored): `getRecursionIdentityTarget` calls the
/// deferred `Checker::get_modifiers_type_from_mapped_type`, so this takes
/// `c: &mut Checker` — the tracer routes it through a hook since
/// `TracedType` must stay `Send + Sync`.
pub fn get_recursion_identity(c: &mut Checker, t: TypeId) -> RecursionId {
    let target = get_recursion_identity_target(c, t);
    get_recursion_identity_from_target(c, target)
}

/// `getRecursionIdentityTarget` (relater.go). PORT(mirrored): see above.
fn get_recursion_identity_target(c: &mut Checker, t: TypeId) -> TypeId {
    let ty = c.types.get(t);
    if ty.flags.intersects(TypeFlags::INDEXED_ACCESS) {
        let object_type = ty.as_indexed_access_type().object_type;
        drop(ty);
        return get_recursion_identity_target(c, object_type.unwrap());
    }
    if ty
        .object_flags
        .contains(ObjectFlags::INSTANTIATED_MAPPED)
    {
        drop(ty);
        let target = c.get_modifiers_type_from_mapped_type(t);
        if let Some(target) = target {
            // Stage `target`'s symbol/types before the nested `types.get` —
            // no read guard may be held across another arena read.
            let (has_symbol, constituents_have_symbol) = {
                let tt = c.types.get(target);
                let has_symbol = tt.symbol.is_some();
                let constituents_have_symbol = tt.flags.intersects(TypeFlags::INTERSECTION)
                    && {
                        let types = tt.types().to_vec();
                        drop(tt);
                        types.iter().any(|&s| c.types.get(s).symbol.is_some())
                    };
                (has_symbol, constituents_have_symbol)
            };
            if has_symbol || constituents_have_symbol {
                return get_recursion_identity_target(c, target);
            }
        }
    }
    t
}

/// `getRecursionIdentityFromTarget` (relater.go). PORT(mirrored): `t.symbol`
/// flag reads index the shared symbol arena. Reads are staged into locals —
/// holding a `TypeArena` read guard across another `types.get` is a
/// same-thread RwLock re-entry (deadlock if a writer is queued).
fn get_recursion_identity_from_target(c: &mut Checker, t: TypeId) -> RecursionId {
    // Stage the fields Go reads off `t` before nested arena lookups.
    let (flags, object_flags, symbol, ref_node, cond_root_node) = {
        let ty = c.types.get(t);
        let ref_node = if ty.object_flags.intersects(ObjectFlags::REFERENCE) {
            ty.data.as_type_reference().and_then(|r| r.node)
        } else {
            None
        };
        let cond_root_node = if ty.flags.intersects(TypeFlags::CONDITIONAL) {
            ty.as_conditional_type()
                .root
                .as_ref()
                .and_then(|root| root.node)
        } else {
            None
        };
        (
            ty.flags,
            ty.object_flags,
            ty.symbol,
            ref_node,
            cond_root_node,
        )
    };
    // Object and array literals are known not to contain recursive
    // references and don't need a recursion identity.
    if flags.intersects(TypeFlags::OBJECT) && !is_object_or_array_literal_type(&c.types.get(t)) {
        if let Some(node) = ref_node {
            // Deferred type references are tracked through their associated
            // AST node. This gives us finer granularity than using their
            // associated target because each manifest type reference has a
            // unique AST node.
            return as_recursion_id_node(node);
        }
        if let Some(symbol) = symbol {
            // We track object types that have a symbol by that symbol
            // (representing the origin of the type), but exclude the static
            // sides of classes (since they share their symbols with the
            // instance sides) and type references that originate in
            // resolution of AST type nodes (since such type nodes cannot be
            // the source of generative recursion without first being
            // instantiated).
            let sym_is_class = c.symbols.borrow()[symbol.index()]
                .flags
                .intersects(ast::SymbolFlags::CLASS);
            if !(object_flags.intersects(ObjectFlags::ANONYMOUS) && sym_is_class)
                && !object_flags.intersects(ObjectFlags::FROM_TYPE_NODE)
            {
                return as_recursion_id_symbol(symbol);
            }
        }
        if is_tuple_type(&c.types, t) && !object_flags.intersects(ObjectFlags::FROM_TYPE_NODE) {
            if let Some(target) = c.types.get(t).target() {
                return as_recursion_id_type(target);
            }
        }
    }
    if flags.intersects(TypeFlags::TYPE_PARAMETER) && symbol.is_some() {
        // We use the symbol of the type parameter such that all "fresh"
        // instantiations of that type parameter have the same recursion
        // identity.
        return as_recursion_id_symbol(symbol.unwrap());
    }
    if flags.intersects(TypeFlags::CONDITIONAL) {
        // The root object represents the origin of the conditional type.
        if let Some(node) = cond_root_node {
            return as_recursion_id_node(node);
        }
    }
    as_recursion_id_type(t)
}

// Checker — PORT(partial) stub.

/// `type Checker struct` — PORT(partial). Only the fields referenced by the
/// foundation-phase files are declared; the real checker agent will extend
/// this (likely in checker.rs, moving this declaration) with program state,
/// interned types, relation caches, diagnostics state, etc.
///
/// Field notes:
/// - `types`/`signatures`/`type_mappers`/`inference_contexts` are the arenas
///   standing in for Go heap objects (`*Type` → `TypeId` etc.).
/// - Link stores: `core.LinkStore[*ast.Node, X]` → `LinkStore<NodeId, X>`,
///   `core.LinkStore[*ast.Symbol, X]` → `LinkStore<SymbolId, X>`,
///   `nodeLinkStore`/`symbolArenaLinkStore` → the links.rs wrappers keyed by
///   `NodeId`/`SymbolId`, `core.LinkStore[*ast.SourceFile, X]` → keyed by the
///   source file's `NodeId`.
/// - `pattern_for_type` (`map[*Type]*ast.Node`) is `Arc<RwLock<_>>` so the
///   `Send + Sync` `TracedType` adapter can read it post-hoc.
/// - `tracer` is `Option` — Go's nilable `*Tracer`.
pub struct Checker {
    /// `id`.
    pub id: u32,
    /// Arena of all `Type` elements created by this checker (Go: heap).
    pub types: TypeArena,
    /// Arena of all `Signature` elements (Go: `*Signature` heap objects).
    pub signatures: SignatureArena,
    /// Arena of all `TypeMapper` elements (Go: `*TypeMapper` heap objects).
    /// `Arc`-shareable so `map` can take `&mut self` — see mapper.rs.
    pub type_mappers: TypeMapperArena,
    /// Arena of `InferenceContext` (Go: `*InferenceContext` heap objects).
    pub inference_contexts: Vec<InferenceContext>,
    /// `unknownType`.
    pub unknown_type: TypeId,
    /// `symbols` — the program's symbol arena (`[]ast.Symbol`); needed by
    /// `get_recursion_identity_from_target` and the tracker/scope helpers.
    /// PORT: `Rc<RefCell>` because `SymbolTrackerImpl` (stored inside
    /// `NodeBuilderContext`) reads `symbol.Flags` through it — Go reads the
    /// flag through the `*ast.Symbol` pointer. Mutation during checking is
    /// rare; readers take short borrows.
    pub symbols: Rc<RefCell<Vec<ast::Symbol>>>,
    /// `patternForType` (`map[*Type]*ast.Node`).
    pub pattern_for_type: Arc<RwLock<FxHashMap<TypeId, NodeId>>>,
    /// `tracer`.
    pub tracer: Option<Tracer>,
    /// `skipDirectInferenceNodes` (`collections.Set[*ast.Node]`).
    pub skip_direct_inference_nodes: OrderedSet<NodeId>,
    /// `isInferencePartiallyBlocked`.
    pub is_inference_partially_blocked: bool,

    // Link stores (checker.go).
    /// `nodeLinks`.
    pub node_links: LinkStore<NodeId, NodeLinks>,
    /// `signatureLinks`.
    pub signature_links: LinkStore<NodeId, SignatureLinks>,
    /// `symbolNodeLinks`.
    pub symbol_node_links: NodeLinkStore<SymbolNodeLinks>,
    /// `typeNodeLinks`.
    pub type_node_links: LinkStore<NodeId, TypeNodeLinks>,
    /// `enumMemberLinks`.
    pub enum_member_links: LinkStore<NodeId, EnumMemberLinks>,
    /// `assertionLinks`.
    pub assertion_links: LinkStore<NodeId, AssertionLinks>,
    /// `arrayLiteralLinks`.
    pub array_literal_links: LinkStore<NodeId, ArrayLiteralLinks>,
    /// `switchStatementLinks`.
    pub switch_statement_links: LinkStore<NodeId, SwitchStatementLinks>,
    /// `jsxElementLinks`.
    pub jsx_element_links: LinkStore<NodeId, JsxElementLinks>,
    /// `computedNameLinks`.
    pub computed_name_links: LinkStore<NodeId, ComputedNameNodeLinks>,
    /// `symbolReferenceLinks`.
    pub symbol_reference_links: LinkStore<SymbolId, SymbolReferenceLinks>,
    /// `valueSymbolLinks`.
    pub value_symbol_links: SymbolArenaLinkStore<ValueSymbolLinks>,
    /// `mappedSymbolLinks`.
    pub mapped_symbol_links: LinkStore<SymbolId, MappedSymbolLinks>,
    /// `deferredSymbolLinks`.
    pub deferred_symbol_links: LinkStore<SymbolId, DeferredSymbolLinks>,
    /// `aliasSymbolLinks`.
    pub alias_symbol_links: LinkStore<SymbolId, AliasSymbolLinks>,
    /// `moduleSymbolLinks`.
    pub module_symbol_links: LinkStore<SymbolId, ModuleSymbolLinks>,
    /// `lateBoundLinks`.
    pub late_bound_links: LinkStore<SymbolId, LateBoundLinks>,
    /// `exportTypeLinks`.
    pub export_type_links: LinkStore<SymbolId, ExportTypeLinks>,
    /// `membersAndExportsLinks`.
    pub members_and_exports_links: LinkStore<SymbolId, MembersAndExportsLinks>,
    /// `typeAliasLinks`.
    pub type_alias_links: LinkStore<SymbolId, TypeAliasLinks>,
    /// `declaredTypeLinks`.
    pub declared_type_links: LinkStore<SymbolId, DeclaredTypeLinks>,
    /// `spreadLinks`.
    pub spread_links: LinkStore<SymbolId, SpreadLinks>,
    /// `varianceLinks`.
    pub variance_links: LinkStore<SymbolId, VarianceLinks>,
    /// `ReverseMappedSymbolLinks`.
    pub reverse_mapped_symbol_links: LinkStore<SymbolId, ReverseMappedSymbolLinks>,
    /// `markedAssignmentSymbolLinks`.
    pub marked_assignment_symbol_links: LinkStore<SymbolId, MarkedAssignmentSymbolLinks>,
    /// `symbolContainerLinks`.
    pub symbol_container_links: LinkStore<SymbolId, ContainingSymbolLinks>,
    /// `sourceFileLinks` — keyed by the source file's `NodeId`.
    pub source_file_links: LinkStore<NodeId, SourceFileLinks>,
}

impl Checker {
    /// Construct the partial checker stub. Arena element 0 is a tombstone so
    /// `TypeId`/`SignatureId` index-0 values can't alias a real element —
    /// Go hands out ids ≥ 1.
    pub fn new_stub() -> Checker {
        // PORT(partial): the real constructor (NewChecker) lands in
        // checker.rs; this exists so foundation code can name a Checker.
        let types = TypeArena::default();
        types.alloc(Type {
            id: TypeId(0),
            data: TypeData::Intrinsic(Default::default()),
            ..Default::default()
        });
        let mut signatures = SignatureArena::default();
        signatures.alloc(Signature::default());
        Checker {
            id: 0,
            types,
            signatures,
            type_mappers: TypeMapperArena::default(),
            inference_contexts: Vec::new(),
            unknown_type: TypeId::NONE,
            symbols: Rc::new(RefCell::new(Vec::new())),
            pattern_for_type: Arc::new(RwLock::new(FxHashMap::default())),
            tracer: None,
            skip_direct_inference_nodes: OrderedSet::new(),
            is_inference_partially_blocked: false,
            node_links: LinkStore::new(),
            signature_links: LinkStore::new(),
            symbol_node_links: NodeLinkStore::default(),
            type_node_links: LinkStore::new(),
            enum_member_links: LinkStore::new(),
            assertion_links: LinkStore::new(),
            array_literal_links: LinkStore::new(),
            switch_statement_links: LinkStore::new(),
            jsx_element_links: LinkStore::new(),
            computed_name_links: LinkStore::new(),
            symbol_reference_links: LinkStore::new(),
            value_symbol_links: SymbolArenaLinkStore::default(),
            mapped_symbol_links: LinkStore::new(),
            deferred_symbol_links: LinkStore::new(),
            alias_symbol_links: LinkStore::new(),
            module_symbol_links: LinkStore::new(),
            late_bound_links: LinkStore::new(),
            export_type_links: LinkStore::new(),
            members_and_exports_links: LinkStore::new(),
            type_alias_links: LinkStore::new(),
            declared_type_links: LinkStore::new(),
            spread_links: LinkStore::new(),
            variance_links: LinkStore::new(),
            reverse_mapped_symbol_links: LinkStore::new(),
            marked_assignment_symbol_links: LinkStore::new(),
            symbol_container_links: LinkStore::new(),
            source_file_links: LinkStore::new(),
        }
    }

    // Deferred method stubs — signatures only; bodies land with checker.rs
    // and the deferred Go files they live in. Each panics like an unwritten
    // port should.

    /// `c.instantiateType` (checker.go). PORT(deferred): instantiation
    /// machinery.
    pub fn instantiate_type(&mut self, t: TypeId, m: Option<TypeMapperId>) -> TypeId {
        let _ = (t, m);
        unimplemented!("PORT(deferred): Checker::instantiate_type lands with checker.go")
    }

    /// `c.inferFromIntraExpressionSites` (inference.go).
    pub fn infer_from_intra_expression_sites(&mut self, n: InferenceContextId) {
        let _ = n;
        unimplemented!("PORT(deferred): inferFromIntraExpressionSites lands with inference.go")
    }

    /// `c.getInferredType` (inference.go).
    pub fn get_inferred_type(&mut self, n: InferenceContextId, index: usize) -> TypeId {
        let _ = (n, index);
        unimplemented!("PORT(deferred): getInferredType lands with inference.go")
    }

    /// `c.getModifiersTypeFromMappedType` (checker.go) — needed by
    /// `get_recursion_identity_target`.
    pub fn get_modifiers_type_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        let _ = t;
        unimplemented!("PORT(deferred): getModifiersTypeFromMappedType lands with checker.go")
    }

    /// `c.TypeToString` — needed by the tracing adapter's `Display`.
    /// PORT(deferred): typeToString lands with nodebuilderimpl.go; the
    /// tracer calls it through a hook (see TracedCheckerContext) because
    /// `TracedType` must be `Send + Sync`.
    pub fn type_to_string(&mut self, t: TypeId) -> String {
        let _ = t;
        unimplemented!("PORT(deferred): TypeToString lands with nodebuilderimpl.go")
    }

    /// `c.getExpandedParameters` — needed by `enter_signature_scope`.
    /// Go returns `[][]*ast.Symbol` and the caller takes `[0]`.
    pub fn get_expanded_parameters(
        &mut self,
        signature: SignatureId,
        skip_union_expanding: bool,
    ) -> Vec<Vec<SymbolId>> {
        let _ = (signature, skip_union_expanding);
        unimplemented!("PORT(deferred): getExpandedParameters lands with checker.go")
    }

    /// `c.getSymbolOfDeclaration` (checker.go).
    pub fn get_symbol_of_declaration(&mut self, node: NodeId) -> Option<SymbolId> {
        let _ = node;
        unimplemented!("PORT(deferred): getSymbolOfDeclaration lands with checker.go")
    }

    /// `c.containsArgumentsReference` (checker.go) — needed by the deferred
    /// `check_unmatched_js_doc_parameters`.
    pub fn contains_arguments_reference(&self, node: NodeId) -> bool {
        let _ = node;
        unimplemented!("PORT(deferred): containsArgumentsReference lands with checker.go")
    }

    /// `c.isArrayType` (checker.go).
    pub fn is_array_type(&self, t: TypeId) -> bool {
        let _ = t;
        unimplemented!("PORT(deferred): isArrayType lands with checker.go")
    }

    /// `c.getTypeFromTypeNode` (checker.go).
    pub fn get_type_from_type_node(&mut self, node: NodeId) -> TypeId {
        let _ = node;
        unimplemented!("PORT(deferred): getTypeFromTypeNode lands with checker.go")
    }

    /// `c.getResolvedSignatureWorker` (checker.go) — needed by
    /// `services.rs::get_resolved_signature_for_signature_help`.
    pub fn get_resolved_signature_worker(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
        argument_count: i32,
    ) -> (Option<SignatureId>, Vec<SignatureId>) {
        let _ = (node, check_mode, argument_count);
        unimplemented!("PORT(deferred): getResolvedSignatureWorker lands with checker.go")
    }

    /// `c.runWithoutResolvedSignatureCaching` (services.go — a Checker
    /// method; ported because the free function
    /// `get_resolved_signature_for_signature_help` routes through it).
    ///
    /// PORT: Go maps `*SignatureLinks`/`*ValueSymbolLinks` (link-store
    /// entries) to their cleared values; link-store entries are keyed by
    /// `NodeId`/`SymbolId` here, so the caches key by the owning node/symbol
    /// — each ancestor is visited once, so the restore order is equivalent.
    /// `get_symbol_of_declaration` is still `PORT(deferred)` and panics on
    /// the function-expression branch until checker.rs lands.
    pub fn run_without_resolved_signature_caching<T>(
        &mut self,
        nodes: &[ast::Node],
        node: NodeId,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let mut callback = |n: &ast::Node, ns: &[ast::Node]| {
            ast::is_call_like_or_function_like_expression(n, ns)
        };
        let mut ancestor_node = ast::find_ancestor(Some(node), nodes, &mut callback);
        if ancestor_node.is_none() {
            return f(self);
        }
        // `cachedResolvedSignatures map[*SignatureLinks]*Signature`
        let mut cached_resolved_signatures: Vec<(NodeId, Option<SignatureId>)> = Vec::new();
        // `cachedTypes map[*ValueSymbolLinks]*Type`
        let mut cached_types: Vec<(SymbolId, Option<TypeId>)> = Vec::new();
        while let Some(ancestor) = ancestor_node {
            let signature_links = self.signature_links.get(ancestor);
            cached_resolved_signatures.push((ancestor, signature_links.resolved_signature));
            signature_links.resolved_signature = None;
            if ast::is_function_expression_or_arrow_function(&nodes[ancestor]) {
                let symbol = self
                    .get_symbol_of_declaration(ancestor)
                    .expect("getSymbolOfDeclaration: nil symbol (Go would panic on GetSymbolId(nil))");
                let symbol_links = self.value_symbol_links.get(symbol);
                cached_types.push((symbol, symbol_links.resolved_type));
                symbol_links.resolved_type = None;
            }
            ancestor_node = ast::find_ancestor(nodes[ancestor].parent, nodes, &mut callback);
        }
        let result = f(self);
        for (node, resolved_signature) in cached_resolved_signatures {
            self.signature_links.get(node).resolved_signature = resolved_signature;
        }
        for (symbol, resolved_type) in cached_types {
            self.value_symbol_links.get(symbol).resolved_type = resolved_type;
        }
        result
    }

    /// `c.error` (checker.go) — diagnostics sink; used by deferred JSDoc
    /// checking. Convention follows tsc-parser: `&'static Message` +
    /// `args: &[String]`; returns the produced diagnostic like Go's
    /// `*ast.Diagnostic` (`Option` for the nil-producing paths).
    /// PORT(deferred): body lands with checker.go diagnostics.
    pub fn error(
        &mut self,
        location: Option<NodeId>,
        message: &'static tsc_diagnostics::Message,
        args: &[String],
    ) -> Option<ast::diagnostic::DiagnosticRef> {
        let _ = (location, message, args);
        unimplemented!("PORT(deferred): Checker::error lands with checker.go diagnostics")
    }

    /// `c.errorOrSuggestion` (checker.go).
    pub fn error_or_suggestion(
        &mut self,
        is_error: bool,
        location: Option<NodeId>,
        message: &'static tsc_diagnostics::Message,
        args: &[String],
    ) {
        let _ = (is_error, location, message, args);
        unimplemented!("PORT(deferred): Checker::errorOrSuggestion lands with checker.go")
    }

    /// `c.getTypeParameterFromMappedType` (checker.go) — for
    /// `MappedType::resolve_components`.
    pub fn get_type_parameter_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        let _ = t;
        unimplemented!("PORT(deferred): getTypeParameterFromMappedType lands with checker.go")
    }

    /// `c.getConstraintTypeFromMappedType` (checker.go).
    pub fn get_constraint_type_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        let _ = t;
        unimplemented!("PORT(deferred): getConstraintTypeFromMappedType lands with checker.go")
    }

    /// `c.getNameTypeFromMappedType` (checker.go).
    pub fn get_name_type_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        let _ = t;
        unimplemented!("PORT(deferred): getNameTypeFromMappedType lands with checker.go")
    }

    /// `c.getTemplateTypeFromMappedType` (checker.go).
    pub fn get_template_type_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        let _ = t;
        unimplemented!("PORT(deferred): getTemplateTypeFromMappedType lands with checker.go")
    }

    /// `c.getTypeOfSymbol` (checker.go).
    pub fn get_type_of_symbol(&mut self, symbol: SymbolId) -> TypeId {
        let _ = symbol;
        unimplemented!("PORT(deferred): getTypeOfSymbol lands with checker.go")
    }

    /// `c.tracer.RecordType(t)` — Go's `wrapType` reads `t.checker` fields
    /// (`patternForType`, recursion identity, `TypeToString`) lazily at dump
    /// time. The `Send + Sync` `TracedType` adapter can't hold `&mut
    /// Checker`, so `RecursionIdentity` is resolved eagerly here (its inputs
    /// are creation-time fields — see tracer.rs header) and `Display`
    /// returns "" until `type_to_string` lands.
    /// PORT(deferred): `get_recursion_identity` routes through the deferred
    /// `get_modifiers_type_from_mapped_type`, so recording an
    /// `InstantiatedMapped` type panics until checker.rs lands.
    pub fn trace_record_type(&mut self, t: TypeId) {
        let Some(tracer) = &self.tracer else {
            return;
        };
        // Clone the arena handle before the `&mut self` identity call.
        let types = self.types.clone();
        let pattern_for_type = self.pattern_for_type.clone();
        let _ = tracer;
        let recursion_identity = Some(get_recursion_identity(self, t).value);
        let adapter: Arc<dyn tsc_tracing::TracedType> =
            Arc::new(crate::tracer::TracedTypeAdapter {
                t,
                types,
                pattern_for_type,
                recursion_identity,
            });
        self.tracer.as_ref().unwrap().record_type(adapter);
    }

    /// `(t *MappedType) ResolveComponents` — implemented here because the
    /// `TypeArena` guard can't call `&mut c` methods while borrowed.
    /// PORT(mirrored from types.go MappedType.ResolveComponents).
    pub fn resolve_mapped_type_components(&mut self, t: TypeId) {
        let type_parameter = self.get_type_parameter_from_mapped_type(t);
        self.types.get_mut(t).as_mapped_type_mut().type_parameter = type_parameter;
        let constraint_type = self.get_constraint_type_from_mapped_type(t);
        self.types
            .get_mut(t)
            .as_mapped_type_mut()
            .constraint_type = constraint_type;
        let name_type = self.get_name_type_from_mapped_type(t);
        self.types.get_mut(t).as_mapped_type_mut().name_type = name_type;
        let template_type = self.get_template_type_from_mapped_type(t);
        self.types
            .get_mut(t)
            .as_mapped_type_mut()
            .template_type = template_type;
    }
}
