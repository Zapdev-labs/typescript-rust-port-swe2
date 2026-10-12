// PORT(partial) — `checker.go` state skeleton plus shared scaffolding.
//
// This file contains:
//
// 1. The `Checker` struct mirroring Go's `checker.go` field list in
//    declaration order (~320 fields), plus the port-added arenas that
//    replace Go heap pointers (`TypeArena`, `TypeMapperArena`, symbol/
//    signature/index-info arenas, inference contexts).
// 2. `new_checker` — a faithful port of Go `NewChecker`'s initialization
//    sequence — and the constructor helpers it calls. Helpers that depend
//    on still-deferred machinery (`get_union_type`, `resolve_name`,
//    symbol merges, `get_type_arguments`, `evaluate_entity`) panic via
//    `unimplemented!` with a `PORT(deferred)` note naming their Go origin.
// 3. Small support types from `tsc/internal/checker/checker.go`
//    (`CacheHashKey`, `CheckMode`, inference bookkeeping) used by the
//    ported foundation files, plus free helpers mirrored from
//    `utilities.go`/`relater.go`/`inference.go` — each tagged
//    `// PORT(mirrored)` until its home file lands.
// 4. `JsxFlags`/`JsxElementLinks` placeholders for the `jsx_element_links`
//    link store (jsx.go is deferred entirely).

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Arc, Mutex, Once, RwLock};

use rustc_hash::FxHashMap;
use tsc_ast::{FlowNodeId, NodeId, SymbolId, SymbolTable, self as ast};
use tsc_collections::OrderedSet;
use tsc_core::context::Context;
use tsc_core::linkstore::LinkStore;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::options_generated::{ModuleKind, ModuleResolutionKind, ScriptTarget};
use tsc_evaluator as evaluator;
use tsc_jsnum::PseudoBigInt;
use tsc_scanner::scanner::Scanner;
use tsc_tracing as tracing;

use crate::checker_types::{
    AssignmentReducedKey, CachedSignatureKey, CachedTypeKey, CachedTypeKind, ContextualInfo,
    DeferredDiagnosticCallback, DiscriminatedContextualTypeKey, EvaluatorThunk, FlowLoopInfo,
    FlowLoopKey, InstantiationExpressionKey, IterationTypes, IterationTypesKey,
    IterationTypesResolver, NameResolverThunk, NarrowedTypeKey, NodeBoolThunk,
    NonExistentPropertyKey, NumberLiteralKey, PropertiesTypesKey, ReverseMappedTypeKey,
    StringMappingKey, SubstitutionTypeKey, SymbolChainComparerThunk, SymbolComparerThunk,
    ThisAssignmentDeclarationKind, TypeBoolThunk, TypeResolution, TypeThunk, UnionOfUnionKey,
    UnionReduction, VarianceStackEntry,
};
use crate::emitresolver::EmitResolverLinks;
use crate::flagdef::flag_type;
use crate::flow::{FlowState, SharedFlow};
use crate::inference::InferenceState;
use crate::links::{NodeLinkStore, SymbolArenaLinkStore};
use crate::mapper::{TypeMapperArena, TypeMapperId};
use crate::nodebuilder::NodeBuilder;
use crate::relater::{ExpandingFlags, Relater, RelationComparisonResult, SharedRelation};
use crate::symbolaccessibility::{ExternalModuleContainerIndex, SymbolTableId};
use crate::tracer::Tracer;
use crate::types::{
    AliasSymbolLinks, ArrayLiteralLinks, AssertionLinks, ComputedNameNodeLinks,
    ContainingSymbolLinks, DeclaredTypeLinks, DeferredSymbolLinks, EnumMemberLinks,
    ExportTypeLinks, IndexInfo, IndexInfoArena, IndexInfoId, LateBoundLinks, MappedSymbolLinks,
    MarkedAssignmentSymbolLinks, MembersAndExportsLinks, ModuleSymbolLinks, NodeLinks, ObjectFlags,
    ReverseMappedSymbolLinks, Signature, SignatureArena, SignatureId, SignatureLinks,
    SourceFileLinks, SpreadLinks, SwitchStatementLinks, SymbolNodeLinks, SymbolReferenceLinks,
    Type, TypeAliasLinks, TypeArena, TypeData, TypeFlags, TypeId, TypeNodeLinks, TypeParameter,
    TypePredicate, ValueSymbolLinks, VarianceFlags, VarianceLinks,
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
#[derive(Default, Clone)]
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

/// `type EnumLiteralKey struct` (checker.go) — `map[EnumLiteralKey]*Type`
/// key. Go keys on `{enumSymbol *ast.Symbol, value any}` where `value` is
/// `string | jsnum.Number | jsnum.PseudoBigInt`; NaN enum members never
/// reach this map (`enumNaNLiteralTypes` handles them), so `Eq`/`Hash` on
/// `Number`'s bits matches Go map semantics.
#[derive(Clone, Debug)]
pub struct EnumLiteralKey {
    /// `enumSymbol`.
    pub enum_symbol: Option<SymbolId>,
    /// `value`.
    pub value: Option<evaluator::Value>,
}

impl PartialEq for EnumLiteralKey {
    fn eq(&self, other: &Self) -> bool {
        self.enum_symbol == other.enum_symbol && self.value == other.value
    }
}

impl Eq for EnumLiteralKey {}

impl std::hash::Hash for EnumLiteralKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.enum_symbol.hash(state);
        match &self.value {
            None => state.write_u8(0),
            Some(evaluator::Value::String(s)) => {
                state.write_u8(1);
                s.hash(state);
            }
            Some(evaluator::Value::Number(n)) => {
                state.write_u8(2);
                state.write_u64(if n.0 == 0.0 { 0 } else { n.0.to_bits() });
            }
            Some(evaluator::Value::Bool(b)) => {
                state.write_u8(3);
                b.hash(state);
            }
            Some(evaluator::Value::PseudoBigInt(b)) => {
                state.write_u8(4);
                b.hash(state);
            }
        }
    }
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
pub(crate) fn as_recursion_id_node(node: NodeId) -> RecursionId {
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

// `IsTypeAny` / `isTypeUsableAsPropertyName` — canonical definitions live in
// `crate::types`; re-exported for `crate::checker_core::is_type_any` call
// sites.
pub use crate::types::{is_type_any, is_type_usable_as_property_name};

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
    types
        .get(target)
        .object_flags
        .intersects(ObjectFlags::TUPLE)
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
            format!(
                "\"{}\"",
                tsc_printer::escape_string(s, tsc_printer::QuoteChar::DoubleQuote)
            )
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
    let __arena_ty = c.types.clone();
    let ty = __arena_ty.get(t);
    if ty.flags.intersects(TypeFlags::INDEXED_ACCESS) {
        let object_type = ty.as_indexed_access_type().object_type;
        drop(ty);
        return get_recursion_identity_target(c, object_type.unwrap());
    }
    if ty.object_flags.contains(ObjectFlags::INSTANTIATED_MAPPED) {
        drop(ty);
        let target = c.get_modifiers_type_from_mapped_type(t);
        if let Some(target) = target {
            // Stage `target`'s symbol/types before the nested `types.get` —
            // no read guard may be held across another arena read.
            let (has_symbol, constituents_have_symbol) = {
                let __arena_tt = c.types.clone();
                let tt = __arena_tt.get(target);
                let has_symbol = tt.symbol.is_some();
                let constituents_have_symbol = tt.flags.intersects(TypeFlags::INTERSECTION) && {
                    let types = tt.types().to_vec();
                    drop(tt);
                    types
                        .iter()
                        .any(|&s| c.types_handle().get(s).symbol.is_some())
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
        let __arena_ty = c.types.clone();
        let ty = __arena_ty.get(t);
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
    if flags.intersects(TypeFlags::OBJECT)
        && !is_object_or_array_literal_type(&c.types_handle().get(t))
    {
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
            let sym_is_class = c.symbol_arena.borrow()[symbol.index()]
                .flags
                .intersects(ast::SymbolFlags::CLASS);
            if !(object_flags.intersects(ObjectFlags::ANONYMOUS) && sym_is_class)
                && !object_flags.intersects(ObjectFlags::FROM_TYPE_NODE)
            {
                return as_recursion_id_symbol(symbol);
            }
        }
        if is_tuple_type(&c.types, t) && !object_flags.intersects(ObjectFlags::FROM_TYPE_NODE) {
            if let Some(target) = c.types_handle().get(t).target() {
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

// Checker — the full checker.go `type Checker struct` field list.

/// `type Checker struct` (checker.go) — PORT: every Go field is declared
/// below in Go declaration order. Pointer-heavy state maps to the
/// established id/arena scheme:
///
/// - `*Type` → `TypeId`, `*Signature` → `SignatureId`,
///   `*TypeMapper` → `TypeMapperId`, `*IndexInfo` → `IndexInfoId`,
///   `*ast.Node`/`ast.NodeId` → `NodeId`, `*ast.Symbol`/`ast.SymbolId` →
///   `SymbolId`, `*ast.FlowNode` → `FlowNodeId`.
/// - `core.LinkStore[*ast.Node, X]` → `LinkStore<NodeId, X>`,
///   `core.LinkStore[*ast.Symbol, X]` → `LinkStore<SymbolId, X>`,
///   `nodeLinkStore`/`symbolArenaLinkStore` → the links.rs wrappers,
///   `core.LinkStore[*ast.SourceFile, X]` → keyed by the source file's
///   `NodeId`.
/// - `collections.Set[T]` → `OrderedSet<T>`.
/// - `map[K]*Type`/`map[K]*Signature`/`map[K]*ast.Symbol` →
///   `FxHashMap<K, TypeId>`/`FxHashMap<K, SignatureId>`/`FxHashMap<K, SymbolId>`.
/// - Function fields (`getGlobalXType`, `resolveName`, `compareSymbols`,
///   `evaluate`, the `isXType`/`markNodeAssignments`/`compareTypesAssignable`
///   closures) are `Rc`/`Box` thunks taking `&mut Checker` — Go closures
///   capture the checker; here the receiver is explicit so a caller can
///   clone the `Rc`, drop the field borrow, and invoke with `&mut self`
///   (the `TypeMapperArena` closure pattern, SPEC §5.4).
/// - `*Relation` fields are `SharedRelation` (`Rc<RefCell<Relation>>`) —
///   `Relater::relation` aliases the same object, exactly like Go.
/// - `pattern_for_type` (`map[*Type]*ast.Node`) is `Arc<RwLock<_>>` so the
///   `Send + Sync` `TracedType` adapter can read it post-hoc.
/// - `sync.Once` → `std::sync::Once`; `sync.Mutex` → `std::sync::Mutex<()>`.
/// - Non-pointer Go fields that are always populated by `NewChecker`
///   (`*Type` sentinels, symbols, signatures, mappers) use bare ids —
///   `TypeId::NONE`/`SymbolId::NONE`/etc. is the Go nil value until
///   `new_checker` assigns them.
///
/// Port-added arenas (no Go counterpart — Go's heap objects): `types`,
/// `type_mappers`, `inference_contexts`. `symbol_arena`/`signature_arena`/
/// `index_info_arena` are the Go `symbolArena`/`signatureArena`/
/// `indexInfoArena` fields at their Go positions.
pub struct Checker {
    // ==== Port-added arenas (Go heap objects — not Go struct fields) ====
    /// Arena of all `Type` elements created by this checker (Go: heap).
    pub types: TypeArena,
    /// Arena of all `TypeMapper` elements (Go: `*TypeMapper` heap objects).
    /// `Arc`-shareable so `map` can take `&mut self` — see mapper.rs.
    pub type_mappers: TypeMapperArena,
    /// Arena of `InferenceContext` (Go: `*InferenceContext` heap objects).
    pub inference_contexts: Vec<InferenceContext>,

    // ==== checker.go fields, in Go declaration order ====
    /// `id`.
    pub id: u32,
    /// `program`.
    pub program: Option<Rc<dyn crate::checker_types::Program>>,
    /// `compilerOptions`.
    pub compiler_options: Rc<CompilerOptions>,
    /// `files` — `[]*ast.SourceFile` → the source files' `NodeId`s.
    pub files: Vec<NodeId>,
    /// `fileIndexMap` — `map[*ast.SourceFile]int`.
    pub file_index_map: FxHashMap<NodeId, usize>,
    /// `compareSymbols` — `func(*ast.Symbol, *ast.Symbol) int`.
    pub compare_symbols: Option<Rc<SymbolComparerThunk<'static>>>,
    /// `compareSymbolChains` — `func([]*ast.Symbol, []*ast.Symbol) int`.
    pub compare_symbol_chains: Option<Rc<SymbolChainComparerThunk<'static>>>,
    /// `TypeCount`.
    pub type_count: u32,
    /// `SymbolCount`.
    pub symbol_count: u32,
    /// `SignatureCount`.
    pub signature_count: u32,
    /// `TotalInstantiationCount`.
    pub total_instantiation_count: u32,
    /// `instantiationCount`.
    pub instantiation_count: u32,
    /// `instantiationStack`.
    pub instantiation_stack: Vec<TypeId>,
    /// `conditionalConstraintDepth`.
    pub conditional_constraint_depth: u32,
    /// `inlineLevel`.
    pub inline_level: i32,
    /// `serializationLevel`.
    pub serialization_level: i32,
    /// `currentNode`.
    pub current_node: Option<NodeId>,
    /// `varianceTypeParameter`.
    pub variance_type_parameter: Option<TypeId>,
    /// `languageVersion`.
    pub language_version: ScriptTarget,
    /// `moduleKind`.
    pub module_kind: ModuleKind,
    /// `moduleResolutionKind`.
    pub module_resolution_kind: ModuleResolutionKind,
    /// `isInferencePartiallyBlocked`.
    pub is_inference_partially_blocked: bool,
    /// `legacyDecorators`.
    pub legacy_decorators: bool,
    /// `emitStandardClassFields`.
    pub emit_standard_class_fields: bool,
    /// `strictNullChecks`.
    pub strict_null_checks: bool,
    /// `strictFunctionTypes`.
    pub strict_function_types: bool,
    /// `strictBindCallApply`.
    pub strict_bind_call_apply: bool,
    /// `strictPropertyInitialization`.
    pub strict_property_initialization: bool,
    /// `strictBuiltinIteratorReturn`.
    pub strict_builtin_iterator_return: bool,
    /// `noImplicitAny`.
    pub no_implicit_any: bool,
    /// `noImplicitThis`.
    pub no_implicit_this: bool,
    /// `useUnknownInCatchVariables`.
    pub use_unknown_in_catch_variables: bool,
    /// `exactOptionalPropertyTypes`.
    pub exact_optional_property_types: bool,
    /// `canCollectSymbolAliasAccessibilityData`.
    pub can_collect_symbol_alias_accessibility_data: bool,
    /// `wasCanceled`.
    pub was_canceled: bool,
    /// `arrayVariances`.
    pub array_variances: Vec<VarianceFlags>,
    /// `globals` — `Rc<RefCell>` so `binder::NameResolver` shares the live
    /// table (Go shares the map header; later `mergeSymbol` inserts are
    /// visible to in-flight resolvers).
    pub globals: Rc<RefCell<SymbolTable>>,
    /// `evaluate` — `evaluator.Evaluator` (see `EvaluatorThunk` for the
    /// `&mut Checker` receiver addition).
    pub evaluate: Option<Rc<EvaluatorThunk<'static>>>,
    /// `stringLiteralTypes`.
    pub string_literal_types: FxHashMap<String, TypeId>,
    /// `numberLiteralTypes` — `map[jsnum.Number]*Type` (see
    /// `NumberLiteralKey` for the float64-key port).
    pub number_literal_types: FxHashMap<NumberLiteralKey, TypeId>,
    /// `nanType`.
    pub nan_type: Option<TypeId>,
    /// `bigintLiteralTypes` — `map[jsnum.PseudoBigInt]*Type`.
    pub bigint_literal_types: FxHashMap<PseudoBigInt, TypeId>,
    /// `enumLiteralTypes`.
    pub enum_literal_types: FxHashMap<EnumLiteralKey, TypeId>,
    /// `enumNaNLiteralTypes` — `map[*ast.Symbol]*Type`.
    pub enum_nan_literal_types: FxHashMap<SymbolId, TypeId>,
    /// `indexedAccessTypes`.
    pub indexed_access_types: FxHashMap<CacheHashKey, TypeId>,
    /// `templateLiteralTypes`.
    pub template_literal_types: FxHashMap<CacheHashKey, TypeId>,
    /// `stringMappingTypes`.
    pub string_mapping_types: FxHashMap<StringMappingKey, TypeId>,
    /// `uniqueESSymbolTypes` — `map[*ast.Symbol]*Type`.
    pub unique_es_symbol_types: FxHashMap<SymbolId, TypeId>,
    /// `thisExpandoKinds` — `map[*ast.Symbol]thisAssignmentDeclarationKind`.
    pub this_expando_kinds: FxHashMap<SymbolId, ThisAssignmentDeclarationKind>,
    /// `thisExpandoLocations` — `map[*ast.Symbol]*ast.Node`.
    pub this_expando_locations: FxHashMap<SymbolId, Option<NodeId>>,
    /// `subtypeReductionCache`.
    pub subtype_reduction_cache: FxHashMap<CacheHashKey, Vec<TypeId>>,
    /// `cachedTypes`.
    pub cached_types: FxHashMap<CachedTypeKey, TypeId>,
    /// `cachedSignatures`.
    pub cached_signatures: FxHashMap<CachedSignatureKey, SignatureId>,
    /// `undefinedProperties`.
    pub undefined_properties: FxHashMap<String, SymbolId>,
    /// `narrowedTypes`.
    pub narrowed_types: FxHashMap<NarrowedTypeKey, TypeId>,
    /// `assignmentReducedTypes`.
    pub assignment_reduced_types: FxHashMap<AssignmentReducedKey, TypeId>,
    /// `discriminatedContextualTypes`.
    pub discriminated_contextual_types: FxHashMap<DiscriminatedContextualTypeKey, TypeId>,
    /// `instantiationExpressionTypes`.
    pub instantiation_expression_types: FxHashMap<InstantiationExpressionKey, TypeId>,
    /// `substitutionTypes`.
    pub substitution_types: FxHashMap<SubstitutionTypeKey, TypeId>,
    /// `reverseMappedCache`.
    pub reverse_mapped_cache: FxHashMap<ReverseMappedTypeKey, TypeId>,
    /// `reverseHomomorphicMappedCache`.
    pub reverse_homomorphic_mapped_cache: FxHashMap<ReverseMappedTypeKey, TypeId>,
    /// `iterationTypesCache`.
    pub iteration_types_cache: FxHashMap<IterationTypesKey, IterationTypes>,
    /// `markerTypes` — `collections.Set[*Type]`.
    pub marker_types: OrderedSet<TypeId>,
    /// `resolvingExplicitTypeOfSymbol` — `collections.Set[*ast.Symbol]`.
    pub resolving_explicit_type_of_symbol: OrderedSet<SymbolId>,
    /// `undefinedSymbol`.
    pub undefined_symbol: SymbolId,
    /// `argumentsSymbol`.
    pub arguments_symbol: SymbolId,
    /// `requireSymbol`.
    pub require_symbol: SymbolId,
    /// `unknownSymbol`.
    pub unknown_symbol: SymbolId,
    /// `unresolvedSymbols`.
    pub unresolved_symbols: FxHashMap<String, SymbolId>,
    /// `errorTypes`.
    pub error_types: FxHashMap<CacheHashKey, TypeId>,
    /// `moduleSymbols` — `map[*ast.Node]*ast.Symbol`.
    pub module_symbols: FxHashMap<NodeId, SymbolId>,
    /// `globalThisSymbol`.
    pub global_this_symbol: SymbolId,
    /// `symbolTableAliasCache` — `map[symbolTableID][]*ast.Symbol`.
    pub symbol_table_alias_cache: FxHashMap<SymbolTableId, Vec<SymbolId>>,
    /// `classExpressionNameTables` — `map[ast.NodeId]ast.SymbolTable`.
    pub class_expression_name_tables: FxHashMap<NodeId, SymbolTable>,
    /// `resolveName`.
    pub resolve_name: Option<Rc<NameResolverThunk<'static>>>,
    /// `resolveNameForSymbolSuggestion`.
    pub resolve_name_for_symbol_suggestion: Option<Rc<NameResolverThunk<'static>>>,
    /// `tupleTypes`.
    pub tuple_types: FxHashMap<CacheHashKey, TypeId>,
    /// `unionTypes`.
    pub union_types: FxHashMap<CacheHashKey, TypeId>,
    /// `unionOfUnionTypes`.
    pub union_of_union_types: FxHashMap<UnionOfUnionKey, TypeId>,
    /// `intersectionTypes`.
    pub intersection_types: FxHashMap<CacheHashKey, TypeId>,
    /// `propertiesTypes`.
    pub properties_types: FxHashMap<PropertiesTypesKey, TypeId>,
    /// `diagnostics`. `DiagnosticsCollection` clones share the underlying
    /// `Arc<Mutex>` state — Go shares `*DiagnosticsCollection` by pointer,
    /// so errors produced during `checkSourceFile` land in the same store
    /// the worker reads afterwards.
    pub diagnostics: ast::diagnostic::DiagnosticsCollection,
    /// `suggestionDiagnostics`.
    pub suggestion_diagnostics: ast::diagnostic::DiagnosticsCollection,
    /// `symbolArena` — `core.Arena[ast.Symbol]`; `Rc<RefCell>` because
    /// `SymbolTrackerImpl` (stored inside `NodeBuilderContext`) reads
    /// `symbol.flags` through it — Go reads the flag through the
    /// `*ast.Symbol` pointer. Mutation during checking is rare; readers
    /// take short borrows.
    pub symbol_arena: Rc<RefCell<Vec<ast::Symbol>>>,
    /// `signatureArena` — `core.Arena[Signature]`.
    pub signature_arena: SignatureArena,
    /// `indexInfoArena` — `core.Arena[IndexInfo]`.
    pub index_info_arena: IndexInfoArena,
    /// `mergedSymbols` — `map[*ast.Symbol]*ast.Symbol`.
    pub merged_symbols: FxHashMap<SymbolId, SymbolId>,
    /// `mergedExportsChecked` — `collections.Set[*ast.Symbol]`.
    pub merged_exports_checked: OrderedSet<SymbolId>,
    /// `factory` — `ast.NodeFactory`.
    pub factory: ast::NodeFactory<'static>,
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
    /// `externalModuleContainers`.
    pub external_module_containers: Option<ExternalModuleContainerIndex>,
    /// `sourceFileLinks` — keyed by the source file's `NodeId`.
    pub source_file_links: LinkStore<NodeId, SourceFileLinks>,
    /// PORT(addition): per-file scratch arena clones used when a lazy-JSDoc
    /// mutation site runs while an ancestor holds a shared `Ref` on the real
    /// arena. Cloned once per file (not per call); the reads they serve —
    /// deprecated-tag queries over parse-time nodes — observe only
    /// parse-stable fields, so divergence from the live arena is benign.
    /// JSDoc nodes minted in a scratch are scratch-relative: they must never
    /// escape into diagnostics or emit tables.
    pub jsdoc_scratch_arenas: FxHashMap<u32, Vec<ast::Node>>,
    /// `regExpScanner`. PORT(deferred): `Scanner<'a>` borrows its text, so
    /// the lazy `getRegularExpressionScanner` rebinding lands with the
    /// regex-checking code; `'static` is the storage lifetime here.
    pub reg_exp_scanner: Option<Box<Scanner<'static>>>,
    /// `patternForType` (`map[*Type]*ast.Node`) — `Arc<RwLock>` so the
    /// `Send + Sync` `TracedType` adapter can read it post-hoc.
    pub pattern_for_type: Arc<RwLock<FxHashMap<TypeId, NodeId>>>,
    /// `contextFreeTypes` — `map[*ast.Node]*Type`.
    pub context_free_types: FxHashMap<NodeId, TypeId>,
    /// `anyType`.
    pub any_type: TypeId,
    /// `autoType`.
    pub auto_type: TypeId,
    /// `wildcardType`.
    pub wildcard_type: TypeId,
    /// `blockedStringType`.
    pub blocked_string_type: TypeId,
    /// `errorType`.
    pub error_type: TypeId,
    /// `unresolvedType`.
    pub unresolved_type: TypeId,
    /// `nonInferrableAnyType`.
    pub non_inferrable_any_type: TypeId,
    /// `intrinsicMarkerType`.
    pub intrinsic_marker_type: TypeId,
    /// `unknownType`.
    pub unknown_type: TypeId,
    /// `undefinedType`.
    pub undefined_type: TypeId,
    /// `undefinedWideningType`.
    pub undefined_widening_type: TypeId,
    /// `missingType`.
    pub missing_type: TypeId,
    /// `undefinedOrMissingType`.
    pub undefined_or_missing_type: TypeId,
    /// `optionalType`.
    pub optional_type: TypeId,
    /// `nullType`.
    pub null_type: TypeId,
    /// `nullWideningType`.
    pub null_widening_type: TypeId,
    /// `stringType`.
    pub string_type: TypeId,
    /// `numberType`.
    pub number_type: TypeId,
    /// `bigintType`.
    pub bigint_type: TypeId,
    /// `regularFalseType`.
    pub regular_false_type: TypeId,
    /// `falseType`.
    pub false_type: TypeId,
    /// `regularTrueType`.
    pub regular_true_type: TypeId,
    /// `trueType`.
    pub true_type: TypeId,
    /// `booleanType`.
    pub boolean_type: TypeId,
    /// `esSymbolType`.
    pub es_symbol_type: TypeId,
    /// `voidType`.
    pub void_type: TypeId,
    /// `neverType`.
    pub never_type: TypeId,
    /// `silentNeverType`.
    pub silent_never_type: TypeId,
    /// `implicitNeverType`.
    pub implicit_never_type: TypeId,
    /// `unreachableNeverType`.
    pub unreachable_never_type: TypeId,
    /// `nonPrimitiveType`.
    pub non_primitive_type: TypeId,
    /// `stringOrNumberType`.
    pub string_or_number_type: TypeId,
    /// `stringNumberSymbolType`.
    pub string_number_symbol_type: TypeId,
    /// `numberOrBigIntType`.
    pub number_or_big_int_type: TypeId,
    /// `templateConstraintType`.
    pub template_constraint_type: TypeId,
    /// `numericStringType`.
    pub numeric_string_type: TypeId,
    /// `uniqueLiteralType`.
    pub unique_literal_type: TypeId,
    /// `uniqueLiteralMapper`.
    pub unique_literal_mapper: TypeMapperId,
    /// `reliabilityFlags`.
    pub reliability_flags: RelationComparisonResult,
    /// `reportUnreliableMapper`.
    pub report_unreliable_mapper: TypeMapperId,
    /// `reportUnmeasurableMapper`.
    pub report_unmeasurable_mapper: TypeMapperId,
    /// `restrictiveMapper`.
    pub restrictive_mapper: TypeMapperId,
    /// `permissiveMapper`.
    pub permissive_mapper: TypeMapperId,
    /// `emptyObjectType`.
    pub empty_object_type: TypeId,
    /// `emptyJsxObjectType`.
    pub empty_jsx_object_type: TypeId,
    /// `emptyFreshJsxObjectType`.
    pub empty_fresh_jsx_object_type: TypeId,
    /// `emptyTypeLiteralType`.
    pub empty_type_literal_type: TypeId,
    /// `unknownEmptyObjectType`.
    pub unknown_empty_object_type: TypeId,
    /// `unknownUnionType`.
    pub unknown_union_type: TypeId,
    /// `emptyGenericType`.
    pub empty_generic_type: TypeId,
    /// `anyFunctionType`.
    pub any_function_type: TypeId,
    /// `noConstraintType`.
    pub no_constraint_type: TypeId,
    /// `circularConstraintType`.
    pub circular_constraint_type: TypeId,
    /// `resolvingDefaultType`.
    pub resolving_default_type: TypeId,
    /// `markerSuperType`.
    pub marker_super_type: TypeId,
    /// `markerSubType`.
    pub marker_sub_type: TypeId,
    /// `markerOtherType`.
    pub marker_other_type: TypeId,
    /// `markerSuperTypeForCheck`.
    pub marker_super_type_for_check: TypeId,
    /// `markerSubTypeForCheck`.
    pub marker_sub_type_for_check: TypeId,
    /// `noTypePredicate` — `*TypePredicate`; `Rc` since signatures borrow
    /// the same singleton.
    pub no_type_predicate: Option<Rc<TypePredicate>>,
    /// `anySignature`.
    pub any_signature: SignatureId,
    /// `unknownSignature`.
    pub unknown_signature: SignatureId,
    /// `resolvingSignature`.
    pub resolving_signature: SignatureId,
    /// `silentNeverSignature`.
    pub silent_never_signature: SignatureId,
    /// `cachedArgumentsReferenced` — `map[*ast.Node]bool`.
    pub cached_arguments_referenced: FxHashMap<NodeId, bool>,
    /// `enumNumberIndexInfo`.
    pub enum_number_index_info: IndexInfoId,
    /// `anyBaseTypeIndexInfo`.
    pub any_base_type_index_info: IndexInfoId,
    /// `patternAmbientModules`.
    pub pattern_ambient_modules: Vec<ast::PatternAmbientModule>,
    /// `patternAmbientModuleAugmentations`.
    pub pattern_ambient_module_augmentations: SymbolTable,
    /// `patternAmbientModuleAugmentationTargets`.
    pub pattern_ambient_module_augmentation_targets: SymbolTable,
    /// `moduleImportAttributesTypes` — `map[*ast.Symbol]*Type`.
    pub module_import_attributes_types: FxHashMap<SymbolId, TypeId>,
    /// `globalObjectType`.
    pub global_object_type: TypeId,
    /// `globalFunctionType`.
    pub global_function_type: TypeId,
    /// `globalCallableFunctionType`.
    pub global_callable_function_type: TypeId,
    /// `globalNewableFunctionType`.
    pub global_newable_function_type: TypeId,
    /// `globalArrayType`.
    pub global_array_type: TypeId,
    /// `globalReadonlyArrayType`.
    pub global_readonly_array_type: TypeId,
    /// `globalStringType`.
    pub global_string_type: TypeId,
    /// `globalNumberType`.
    pub global_number_type: TypeId,
    /// `globalBooleanType`.
    pub global_boolean_type: TypeId,
    /// `globalRegExpType`.
    pub global_reg_exp_type: TypeId,
    /// `globalThisType`.
    pub global_this_type: TypeId,
    /// `anyArrayType`.
    pub any_array_type: TypeId,
    /// `autoArrayType`.
    pub auto_array_type: TypeId,
    /// `anyReadonlyArrayType`.
    pub any_readonly_array_type: TypeId,
    /// `deferredGlobalImportMetaExpressionType`.
    pub deferred_global_import_meta_expression_type: Option<TypeId>,
    /// `contextualBindingPatterns`.
    pub contextual_binding_patterns: Vec<NodeId>,
    /// `emptyStringType`.
    pub empty_string_type: TypeId,
    /// `zeroType`.
    pub zero_type: TypeId,
    /// `zeroBigIntType`.
    pub zero_big_int_type: TypeId,
    /// `typeofType`.
    pub typeof_type: TypeId,
    /// `typeResolutions`.
    pub type_resolutions: Vec<TypeResolution>,
    /// `resolutionStart`.
    pub resolution_start: i32,
    /// `varianceStack`.
    pub variance_stack: Vec<VarianceStackEntry>,
    /// `callResolutionStack`.
    pub call_resolution_stack: Vec<NodeId>,
    /// `apparentArgumentCount` — `*int`; read-only sharing in
    /// `getResolvedSignatureWorker`, so `Option<i32>` suffices.
    pub apparent_argument_count: Option<i32>,
    /// `lastGetCombinedNodeFlagsNode`.
    pub last_get_combined_node_flags_node: Option<NodeId>,
    /// `lastGetCombinedNodeFlagsResult`.
    pub last_get_combined_node_flags_result: ast::NodeFlags,
    /// `lastGetCombinedModifierFlagsNode`.
    pub last_get_combined_modifier_flags_node: Option<NodeId>,
    /// `lastGetCombinedModifierFlagsResult`.
    pub last_get_combined_modifier_flags_result: ast::ModifierFlags,
    /// `freeinferenceState` — `*InferenceState` free list.
    pub free_inference_state: Option<Box<InferenceState>>,
    /// `freeFlowState` — `*FlowState` free list.
    pub free_flow_state: Option<Box<FlowState>>,
    /// `flowLoopCache`.
    pub flow_loop_cache: FxHashMap<FlowLoopKey, TypeId>,
    /// `flowLoopStack`.
    pub flow_loop_stack: Vec<FlowLoopInfo>,
    /// `sharedFlows`.
    pub shared_flows: Vec<SharedFlow>,
    /// `antecedentTypes`.
    pub antecedent_types: Vec<TypeId>,
    /// `flowAnalysisDisabled`.
    pub flow_analysis_disabled: bool,
    /// `flowInvocationCount`.
    pub flow_invocation_count: i32,
    /// `flowTypeCache` — `map[*ast.Node]*Type`.
    pub flow_type_cache: FxHashMap<NodeId, TypeId>,
    /// `lastFlowNode` — `FlowNodeId::NONE` is Go nil.
    pub last_flow_node: FlowNodeId,
    /// `lastFlowNodeReachable`.
    pub last_flow_node_reachable: bool,
    /// `flowNodeReachable` — `map[*ast.FlowNode]bool`.
    pub flow_node_reachable: FxHashMap<FlowNodeId, bool>,
    /// `flowNodePostSuper` — `map[*ast.FlowNode]bool`.
    pub flow_node_post_super: FxHashMap<FlowNodeId, bool>,
    /// `renamedBindingElementsInTypes`.
    pub renamed_binding_elements_in_types: Vec<NodeId>,
    /// `contextualInfos`.
    pub contextual_infos: Vec<ContextualInfo>,
    /// `inferenceContextInfos`.
    pub inference_context_infos: Vec<InferenceContextInfo>,
    /// `awaitedTypeStack`.
    pub awaited_type_stack: Vec<TypeId>,
    /// `reverseMappedSourceStack`.
    pub reverse_mapped_source_stack: Vec<TypeId>,
    /// `reverseMappedTargetStack`.
    pub reverse_mapped_target_stack: Vec<TypeId>,
    /// `reverseExpandingFlags`.
    pub reverse_expanding_flags: ExpandingFlags,
    /// `freeRelater` — `*Relater` free list.
    pub free_relater: Option<Box<Relater>>,
    /// Snapshot of the relater active in the innermost enclosing
    /// `check_type_related_to_ex` frame, plus a pool of checked-out worker
    /// relaters. Go comparer closures capture `r` directly so they re-enter
    /// the live relater even on non-reporting paths (e.g. `context_compare`
    /// during signature inference). The port can't capture `&mut Relater` in
    /// a `'static` comparer box, so `compare_via` falls back to a pooled
    /// relater seeded from this snapshot: `relation` is `Rc`-shared (same
    /// results cache) and the stacks carry the entry-time in-flight keys for
    /// cycle detection.
    pub relater_seed: Option<Relater>,
    /// See `relater_seed`.
    pub relater_pool: Vec<Relater>,
    /// `subtypeRelation`.
    pub subtype_relation: SharedRelation,
    /// `strictSubtypeRelation`.
    pub strict_subtype_relation: SharedRelation,
    /// `assignableRelation`.
    pub assignable_relation: SharedRelation,
    /// `comparableRelation`.
    pub comparable_relation: SharedRelation,
    /// `identityRelation`.
    pub identity_relation: SharedRelation,
    /// `enumRelation`.
    pub enum_relation: FxHashMap<crate::checker_types::EnumRelationKey, RelationComparisonResult>,
    /// `getGlobalESSymbolType`.
    pub get_global_es_symbol_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalBigIntType`.
    pub get_global_big_int_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalImportMetaType`.
    pub get_global_import_meta_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalImportAttributesType`.
    pub get_global_import_attributes_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalImportAttributesTypeChecked`.
    pub get_global_import_attributes_type_checked: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalNonNullableTypeAliasOrNil`.
    pub get_global_non_nullable_type_alias_or_nil:
        Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalExtractSymbol`.
    pub get_global_extract_symbol: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalDisposableType`.
    pub get_global_disposable_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAsyncDisposableType`.
    pub get_global_async_disposable_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAwaitedSymbol`.
    pub get_global_awaited_symbol: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalAwaitedSymbolOrNil`.
    pub get_global_awaited_symbol_or_nil: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalNaNSymbolOrNil`.
    pub get_global_nan_symbol_or_nil: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalRecordSymbol`.
    pub get_global_record_symbol: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalTemplateStringsArrayType`.
    pub get_global_template_strings_array_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalESSymbolConstructorSymbolOrNil`.
    pub get_global_es_symbol_constructor_symbol_or_nil:
        Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalESSymbolConstructorTypeSymbolOrNil`.
    pub get_global_es_symbol_constructor_type_symbol_or_nil:
        Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalImportCallOptionsType`.
    pub get_global_import_call_options_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalImportCallOptionsTypeChecked`.
    pub get_global_import_call_options_type_checked: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalPromiseType`.
    pub get_global_promise_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalPromiseTypeChecked`.
    pub get_global_promise_type_checked: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalPromiseLikeType`.
    pub get_global_promise_like_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAbstractModuleSourceType`.
    pub get_global_abstract_module_source_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalPromiseConstructorSymbol`.
    pub get_global_promise_constructor_symbol:
        Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalPromiseConstructorSymbolOrNil`.
    pub get_global_promise_constructor_symbol_or_nil:
        Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalOmitSymbol`.
    pub get_global_omit_symbol: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalNoInferSymbolOrNil`.
    pub get_global_no_infer_symbol_or_nil: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
    /// `getGlobalIteratorType`.
    pub get_global_iterator_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalIterableType`.
    pub get_global_iterable_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalIterableTypeChecked`.
    pub get_global_iterable_type_checked: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalIterableIteratorType`.
    pub get_global_iterable_iterator_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalIterableIteratorTypeChecked`.
    pub get_global_iterable_iterator_type_checked: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalIteratorObjectType`.
    pub get_global_iterator_object_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalGeneratorType`.
    pub get_global_generator_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAsyncIteratorType`.
    pub get_global_async_iterator_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAsyncIterableType`.
    pub get_global_async_iterable_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAsyncIterableTypeChecked`.
    pub get_global_async_iterable_type_checked: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAsyncIterableIteratorType`.
    pub get_global_async_iterable_iterator_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAsyncIterableIteratorTypeChecked`.
    pub get_global_async_iterable_iterator_type_checked: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAsyncIteratorObjectType`.
    pub get_global_async_iterator_object_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalAsyncGeneratorType`.
    pub get_global_async_generator_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalIteratorYieldResultType`.
    pub get_global_iterator_yield_result_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalIteratorReturnResultType`.
    pub get_global_iterator_return_result_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalTypedPropertyDescriptorType`.
    pub get_global_typed_property_descriptor_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalClassDecoratorContextType`.
    pub get_global_class_decorator_context_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalClassMethodDecoratorContextType`.
    pub get_global_class_method_decorator_context_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalClassGetterDecoratorContextType`.
    pub get_global_class_getter_decorator_context_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalClassSetterDecoratorContextType`.
    pub get_global_class_setter_decorator_context_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalClassAccessorDecoratorContxtType` — Go's misspelled field
    /// (`Contxt`), kept for grep parity.
    pub get_global_class_accessor_decorator_contxt_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalClassAccessorDecoratorContextType`.
    pub get_global_class_accessor_decorator_context_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalClassAccessorDecoratorTargetType`.
    pub get_global_class_accessor_decorator_target_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalClassAccessorDecoratorResultType`.
    pub get_global_class_accessor_decorator_result_type: Option<Rc<TypeThunk<'static>>>,
    /// `getGlobalClassFieldDecoratorContextType`.
    pub get_global_class_field_decorator_context_type: Option<Rc<TypeThunk<'static>>>,
    /// `syncIterationTypesResolver`.
    pub sync_iteration_types_resolver: Option<Box<IterationTypesResolver>>,
    /// `asyncIterationTypesResolver`.
    pub async_iteration_types_resolver: Option<Box<IterationTypesResolver>>,
    /// `isPrimitiveOrObjectOrEmptyType`.
    pub is_primitive_or_object_or_empty_type: Option<Rc<TypeBoolThunk<'static>>>,
    /// `containsMissingType`.
    pub contains_missing_type: Option<Rc<TypeBoolThunk<'static>>>,
    /// `couldContainTypeVariables`.
    pub could_contain_type_variables: Option<Rc<TypeBoolThunk<'static>>>,
    /// `isStringIndexSignatureOnlyType`.
    pub is_string_index_signature_only_type: Option<Rc<TypeBoolThunk<'static>>>,
    /// `markNodeAssignments`.
    pub mark_node_assignments: Option<Rc<NodeBoolThunk<'static>>>,
    /// `compareTypesAssignable`.
    pub compare_types_assignable: Option<Rc<crate::types::TypeComparer<'static>>>,
    /// `emitResolverLinks`.
    pub emit_resolver_links: EmitResolverLinks,
    /// `_jsxNamespace`.
    pub jsx_namespace: String,
    /// `_jsxFactoryEntity`.
    pub jsx_factory_entity: Option<NodeId>,
    /// `skipDirectInferenceNodes` — `collections.Set[*ast.Node]`.
    pub skip_direct_inference_nodes: OrderedSet<NodeId>,
    /// `ctx` — `context.Context`.
    pub ctx: Context,
    /// `packagesMap`.
    pub packages_map: FxHashMap<String, bool>,
    /// `activeMappers`.
    pub active_mappers: Vec<TypeMapperId>,
    /// `activeTypeMappersCaches`.
    pub active_type_mappers_caches: Vec<FxHashMap<CacheHashKey, TypeId>>,
    /// `ambientModulesOnce` — `sync.Once`. PORT(deferred): Go's
    /// `once.Do(func(){ c.ambientModules = ... })` needs care around the
    /// disjoint-field borrow; wave-2 may move `ambient_modules` behind
    /// `RefCell` or compute eagerly.
    pub ambient_modules_once: Once,
    /// `ambientModules`.
    pub ambient_modules: Vec<SymbolId>,
    /// `withinUnreachableCode`.
    pub within_unreachable_code: bool,
    /// `reportedUnreachableNodes` — `collections.Set[*ast.Node]`.
    pub reported_unreachable_nodes: OrderedSet<NodeId>,
    /// `nonExistentProperties` — `collections.Set[NonExistentPropertyKey]`.
    pub non_existent_properties: OrderedSet<NonExistentPropertyKey>,
    /// `deferredDiagnosticCallbacks` — `[]func()`.
    pub deferred_diagnostic_callbacks: Vec<DeferredDiagnosticCallback<'static>>,
    /// `typeToStringNodebuilder`.
    pub type_to_string_nodebuilder: Option<Box<NodeBuilder<'static>>>,
    /// `mu` — `sync.Mutex`.
    pub mu: Mutex<()>,
    /// `tracer` — `*Tracer`, optional.
    pub tracer: Option<Tracer>,
}

/// `var nextCheckerID atomic.Uint32` (checker.go).
static NEXT_CHECKER_ID: AtomicU32 = AtomicU32::new(0);

impl Checker {
    /// `&Checker{}` — the Go zero value with every field defaulted, plus
    /// tombstone arena elements 0 so `TypeId(0)`/`SignatureId(0)`/
    /// `IndexInfoId(0)` can't alias a real element (Go hands out ids ≥ 1).
    /// `new_checker` then assigns fields in `NewChecker` order.
    fn empty() -> Checker {
        let types = TypeArena::default();
        types.alloc(Type {
            id: TypeId(0),
            data: TypeData::Intrinsic(Default::default()),
            ..Default::default()
        });
        let mut signature_arena = SignatureArena::default();
        signature_arena.alloc(Signature::default());
        let mut index_info_arena = IndexInfoArena::default();
        index_info_arena.alloc(IndexInfo::default());
        Checker {
            types,
            type_mappers: TypeMapperArena::default(),
            inference_contexts: Vec::new(),
            id: 0,
            program: None,
            compiler_options: Rc::new(CompilerOptions::default()),
            files: Vec::new(),
            file_index_map: FxHashMap::default(),
            compare_symbols: None,
            compare_symbol_chains: None,
            type_count: 0,
            symbol_count: 0,
            signature_count: 0,
            total_instantiation_count: 0,
            instantiation_count: 0,
            instantiation_stack: Vec::new(),
            conditional_constraint_depth: 0,
            inline_level: 0,
            serialization_level: 0,
            current_node: None,
            variance_type_parameter: None,
            language_version: ScriptTarget::default(),
            module_kind: ModuleKind::default(),
            module_resolution_kind: ModuleResolutionKind::default(),
            is_inference_partially_blocked: false,
            legacy_decorators: false,
            emit_standard_class_fields: false,
            strict_null_checks: false,
            strict_function_types: false,
            strict_bind_call_apply: false,
            strict_property_initialization: false,
            strict_builtin_iterator_return: false,
            no_implicit_any: false,
            no_implicit_this: false,
            use_unknown_in_catch_variables: false,
            exact_optional_property_types: false,
            can_collect_symbol_alias_accessibility_data: false,
            was_canceled: false,
            array_variances: Vec::new(),
            globals: Rc::new(RefCell::new(SymbolTable::new())),
            evaluate: None,
            string_literal_types: FxHashMap::default(),
            number_literal_types: FxHashMap::default(),
            nan_type: None,
            bigint_literal_types: FxHashMap::default(),
            enum_literal_types: FxHashMap::default(),
            enum_nan_literal_types: FxHashMap::default(),
            indexed_access_types: FxHashMap::default(),
            template_literal_types: FxHashMap::default(),
            string_mapping_types: FxHashMap::default(),
            unique_es_symbol_types: FxHashMap::default(),
            this_expando_kinds: FxHashMap::default(),
            this_expando_locations: FxHashMap::default(),
            subtype_reduction_cache: FxHashMap::default(),
            cached_types: FxHashMap::default(),
            cached_signatures: FxHashMap::default(),
            undefined_properties: FxHashMap::default(),
            narrowed_types: FxHashMap::default(),
            assignment_reduced_types: FxHashMap::default(),
            discriminated_contextual_types: FxHashMap::default(),
            instantiation_expression_types: FxHashMap::default(),
            substitution_types: FxHashMap::default(),
            reverse_mapped_cache: FxHashMap::default(),
            reverse_homomorphic_mapped_cache: FxHashMap::default(),
            iteration_types_cache: FxHashMap::default(),
            marker_types: OrderedSet::new(),
            resolving_explicit_type_of_symbol: OrderedSet::new(),
            undefined_symbol: SymbolId::NONE,
            arguments_symbol: SymbolId::NONE,
            require_symbol: SymbolId::NONE,
            unknown_symbol: SymbolId::NONE,
            unresolved_symbols: FxHashMap::default(),
            error_types: FxHashMap::default(),
            module_symbols: FxHashMap::default(),
            global_this_symbol: SymbolId::NONE,
            symbol_table_alias_cache: FxHashMap::default(),
            class_expression_name_tables: FxHashMap::default(),
            resolve_name: None,
            resolve_name_for_symbol_suggestion: None,
            tuple_types: FxHashMap::default(),
            union_types: FxHashMap::default(),
            union_of_union_types: FxHashMap::default(),
            intersection_types: FxHashMap::default(),
            properties_types: FxHashMap::default(),
            diagnostics: ast::diagnostic::DiagnosticsCollection::new(),
            suggestion_diagnostics: ast::diagnostic::DiagnosticsCollection::new(),
            symbol_arena: Rc::new(RefCell::new(Vec::new())),
            signature_arena,
            index_info_arena,
            merged_symbols: FxHashMap::default(),
            merged_exports_checked: OrderedSet::new(),
            factory: ast::NodeFactory::default(),
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
            external_module_containers: None,
            source_file_links: LinkStore::new(),
            jsdoc_scratch_arenas: FxHashMap::default(),
            reg_exp_scanner: None,
            pattern_for_type: Arc::new(RwLock::new(FxHashMap::default())),
            context_free_types: FxHashMap::default(),
            any_type: TypeId::NONE,
            auto_type: TypeId::NONE,
            wildcard_type: TypeId::NONE,
            blocked_string_type: TypeId::NONE,
            error_type: TypeId::NONE,
            unresolved_type: TypeId::NONE,
            non_inferrable_any_type: TypeId::NONE,
            intrinsic_marker_type: TypeId::NONE,
            unknown_type: TypeId::NONE,
            undefined_type: TypeId::NONE,
            undefined_widening_type: TypeId::NONE,
            missing_type: TypeId::NONE,
            undefined_or_missing_type: TypeId::NONE,
            optional_type: TypeId::NONE,
            null_type: TypeId::NONE,
            null_widening_type: TypeId::NONE,
            string_type: TypeId::NONE,
            number_type: TypeId::NONE,
            bigint_type: TypeId::NONE,
            regular_false_type: TypeId::NONE,
            false_type: TypeId::NONE,
            regular_true_type: TypeId::NONE,
            true_type: TypeId::NONE,
            boolean_type: TypeId::NONE,
            es_symbol_type: TypeId::NONE,
            void_type: TypeId::NONE,
            never_type: TypeId::NONE,
            silent_never_type: TypeId::NONE,
            implicit_never_type: TypeId::NONE,
            unreachable_never_type: TypeId::NONE,
            non_primitive_type: TypeId::NONE,
            string_or_number_type: TypeId::NONE,
            string_number_symbol_type: TypeId::NONE,
            number_or_big_int_type: TypeId::NONE,
            template_constraint_type: TypeId::NONE,
            numeric_string_type: TypeId::NONE,
            unique_literal_type: TypeId::NONE,
            unique_literal_mapper: TypeMapperId::NONE,
            reliability_flags: RelationComparisonResult::NONE,
            report_unreliable_mapper: TypeMapperId::NONE,
            report_unmeasurable_mapper: TypeMapperId::NONE,
            restrictive_mapper: TypeMapperId::NONE,
            permissive_mapper: TypeMapperId::NONE,
            empty_object_type: TypeId::NONE,
            empty_jsx_object_type: TypeId::NONE,
            empty_fresh_jsx_object_type: TypeId::NONE,
            empty_type_literal_type: TypeId::NONE,
            unknown_empty_object_type: TypeId::NONE,
            unknown_union_type: TypeId::NONE,
            empty_generic_type: TypeId::NONE,
            any_function_type: TypeId::NONE,
            no_constraint_type: TypeId::NONE,
            circular_constraint_type: TypeId::NONE,
            resolving_default_type: TypeId::NONE,
            marker_super_type: TypeId::NONE,
            marker_sub_type: TypeId::NONE,
            marker_other_type: TypeId::NONE,
            marker_super_type_for_check: TypeId::NONE,
            marker_sub_type_for_check: TypeId::NONE,
            no_type_predicate: None,
            any_signature: SignatureId::NONE,
            unknown_signature: SignatureId::NONE,
            resolving_signature: SignatureId::NONE,
            silent_never_signature: SignatureId::NONE,
            cached_arguments_referenced: FxHashMap::default(),
            enum_number_index_info: IndexInfoId::NONE,
            any_base_type_index_info: IndexInfoId::NONE,
            pattern_ambient_modules: Vec::new(),
            pattern_ambient_module_augmentations: SymbolTable::new(),
            pattern_ambient_module_augmentation_targets: SymbolTable::new(),
            module_import_attributes_types: FxHashMap::default(),
            global_object_type: TypeId::NONE,
            global_function_type: TypeId::NONE,
            global_callable_function_type: TypeId::NONE,
            global_newable_function_type: TypeId::NONE,
            global_array_type: TypeId::NONE,
            global_readonly_array_type: TypeId::NONE,
            global_string_type: TypeId::NONE,
            global_number_type: TypeId::NONE,
            global_boolean_type: TypeId::NONE,
            global_reg_exp_type: TypeId::NONE,
            global_this_type: TypeId::NONE,
            any_array_type: TypeId::NONE,
            auto_array_type: TypeId::NONE,
            any_readonly_array_type: TypeId::NONE,
            deferred_global_import_meta_expression_type: None,
            contextual_binding_patterns: Vec::new(),
            empty_string_type: TypeId::NONE,
            zero_type: TypeId::NONE,
            zero_big_int_type: TypeId::NONE,
            typeof_type: TypeId::NONE,
            type_resolutions: Vec::new(),
            resolution_start: 0,
            variance_stack: Vec::new(),
            call_resolution_stack: Vec::new(),
            apparent_argument_count: None,
            last_get_combined_node_flags_node: None,
            last_get_combined_node_flags_result: ast::NodeFlags::default(),
            last_get_combined_modifier_flags_node: None,
            last_get_combined_modifier_flags_result: ast::ModifierFlags::default(),
            free_inference_state: None,
            free_flow_state: None,
            flow_loop_cache: FxHashMap::default(),
            flow_loop_stack: Vec::new(),
            shared_flows: Vec::new(),
            antecedent_types: Vec::new(),
            flow_analysis_disabled: false,
            flow_invocation_count: 0,
            flow_type_cache: FxHashMap::default(),
            last_flow_node: FlowNodeId::NONE,
            last_flow_node_reachable: false,
            flow_node_reachable: FxHashMap::default(),
            flow_node_post_super: FxHashMap::default(),
            renamed_binding_elements_in_types: Vec::new(),
            contextual_infos: Vec::new(),
            inference_context_infos: Vec::new(),
            awaited_type_stack: Vec::new(),
            reverse_mapped_source_stack: Vec::new(),
            reverse_mapped_target_stack: Vec::new(),
            reverse_expanding_flags: ExpandingFlags::NONE,
            free_relater: None,
            relater_seed: None,
            relater_pool: Vec::new(),
            subtype_relation: SharedRelation::default(),
            strict_subtype_relation: SharedRelation::default(),
            assignable_relation: SharedRelation::default(),
            comparable_relation: SharedRelation::default(),
            identity_relation: SharedRelation::default(),
            enum_relation: FxHashMap::default(),
            get_global_es_symbol_type: None,
            get_global_big_int_type: None,
            get_global_import_meta_type: None,
            get_global_import_attributes_type: None,
            get_global_import_attributes_type_checked: None,
            get_global_non_nullable_type_alias_or_nil: None,
            get_global_extract_symbol: None,
            get_global_disposable_type: None,
            get_global_async_disposable_type: None,
            get_global_awaited_symbol: None,
            get_global_awaited_symbol_or_nil: None,
            get_global_nan_symbol_or_nil: None,
            get_global_record_symbol: None,
            get_global_template_strings_array_type: None,
            get_global_es_symbol_constructor_symbol_or_nil: None,
            get_global_es_symbol_constructor_type_symbol_or_nil: None,
            get_global_import_call_options_type: None,
            get_global_import_call_options_type_checked: None,
            get_global_promise_type: None,
            get_global_promise_type_checked: None,
            get_global_promise_like_type: None,
            get_global_abstract_module_source_type: None,
            get_global_promise_constructor_symbol: None,
            get_global_promise_constructor_symbol_or_nil: None,
            get_global_omit_symbol: None,
            get_global_no_infer_symbol_or_nil: None,
            get_global_iterator_type: None,
            get_global_iterable_type: None,
            get_global_iterable_type_checked: None,
            get_global_iterable_iterator_type: None,
            get_global_iterable_iterator_type_checked: None,
            get_global_iterator_object_type: None,
            get_global_generator_type: None,
            get_global_async_iterator_type: None,
            get_global_async_iterable_type: None,
            get_global_async_iterable_type_checked: None,
            get_global_async_iterable_iterator_type: None,
            get_global_async_iterable_iterator_type_checked: None,
            get_global_async_iterator_object_type: None,
            get_global_async_generator_type: None,
            get_global_iterator_yield_result_type: None,
            get_global_iterator_return_result_type: None,
            get_global_typed_property_descriptor_type: None,
            get_global_class_decorator_context_type: None,
            get_global_class_method_decorator_context_type: None,
            get_global_class_getter_decorator_context_type: None,
            get_global_class_setter_decorator_context_type: None,
            get_global_class_accessor_decorator_contxt_type: None,
            get_global_class_accessor_decorator_context_type: None,
            get_global_class_accessor_decorator_target_type: None,
            get_global_class_accessor_decorator_result_type: None,
            get_global_class_field_decorator_context_type: None,
            sync_iteration_types_resolver: None,
            async_iteration_types_resolver: None,
            is_primitive_or_object_or_empty_type: None,
            contains_missing_type: None,
            could_contain_type_variables: None,
            is_string_index_signature_only_type: None,
            mark_node_assignments: None,
            compare_types_assignable: None,
            emit_resolver_links: EmitResolverLinks::default(),
            jsx_namespace: String::new(),
            jsx_factory_entity: None,
            skip_direct_inference_nodes: OrderedSet::new(),
            ctx: Context::default(),
            packages_map: FxHashMap::default(),
            active_mappers: Vec::new(),
            active_type_mappers_caches: Vec::new(),
            ambient_modules_once: Once::new(),
            ambient_modules: Vec::new(),
            within_unreachable_code: false,
            reported_unreachable_nodes: OrderedSet::new(),
            non_existent_properties: OrderedSet::new(),
            deferred_diagnostic_callbacks: Vec::new(),
            type_to_string_nodebuilder: None,
            mu: Mutex::new(()),
            tracer: None,
        }
    }

    /// Construct the partial checker stub — `Checker::empty()` plus the
    /// arena tombstones. `new_checker` is the faithful `NewChecker` port;
    /// this exists so foundation code can name a `Checker` without a
    /// `Program`.
    pub fn new_stub() -> Checker {
        Checker::empty()
    }

    // Deferred method stubs — signatures only; bodies land with checker.rs
    // and the deferred Go files they live in. Each panics like an unwritten
    // port should.

    /// `c.instantiateType` (checker.go) — delegates to
    /// `instantiate_type_with_alias` (ported in `checker_c.rs`).
    pub fn instantiate_type(&mut self, t: TypeId, m: Option<TypeMapperId>) -> TypeId {
        self.instantiate_type_with_alias(t, m, None)
    }

    /// `c.inferFromIntraExpressionSites` (inference.go). PORT: delegates to
    /// the free function in `crate::inference` (that module can't define
    /// another `impl Checker` method with this name).
    pub fn infer_from_intra_expression_sites(&mut self, n: InferenceContextId) {
        crate::inference::infer_from_intra_expression_sites(self, n)
    }

    /// `c.getInferredType` (inference.go). PORT: delegates to the free
    /// function in `crate::inference`.
    pub fn get_inferred_type(&mut self, n: InferenceContextId, index: usize) -> TypeId {
        crate::inference::get_inferred_type(self, n, index)
    }

    /// `c.getModifiersTypeFromMappedType` (checker.go) — needed by
    /// `get_recursion_identity_target`.
    pub fn get_modifiers_type_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        if self
            .types_handle()
            .get(t)
            .as_mapped_type()
            .modifiers_type
            .is_none()
        {
            let mapper = self
                .types_handle()
                .get(t)
                .as_mapped_type()
                .object_type
                .mapper;
            let modifiers_type = if self.is_mapped_type_with_keyof_constraint_declaration(t) {
                // If the constraint declaration is a 'keyof T' node, the modifiers type is T. We check
                // AST nodes here because, when T is a non-generic type, the logic below eagerly resolves
                // 'keyof T' to a literal union type and we can't recover T from that type.
                let constraint_decl = self
                    .get_constraint_declaration_for_mapped_type(t)
                    .expect("keyof constraint declaration");
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((constraint_decl).file_index());
                let ty_node = nodes[constraint_decl]
                    .type_()
                    .expect("type operator operand");
                let ty = self.get_type_from_type_node(ty_node);
                self.instantiate_type(ty, mapper)
            } else {
                // Otherwise, get the declared constraint type, and if the constraint type is a type parameter,
                // get the constraint of that type parameter. If the resulting type is an indexed type 'keyof T',
                // the modifiers type is T. Otherwise, the modifiers type is unknown.
                let declaration = self
                    .types_handle()
                    .get(t)
                    .as_mapped_type()
                    .declaration
                    .expect("mapped type declaration");
                let declared_type = self.get_type_from_mapped_type_node(declaration);
                let constraint =
                    crate::checker_c::get_constraint_type_from_mapped_type(self, declared_type);
                let mut extended_constraint = constraint;
                if let Some(c) = constraint
                    && self
                        .types_handle()
                        .get(c)
                        .flags
                        .intersects(TypeFlags::TYPE_PARAMETER)
                {
                    let nd = get_non_distributed_type_parameter(&self.types, c);
                    extended_constraint = self.get_constraint_of_type_parameter(nd);
                }
                match extended_constraint {
                    Some(ec)
                        if self
                            .types_handle()
                            .get(ec)
                            .flags
                            .intersects(TypeFlags::INDEX) =>
                    {
                        let target = self
                            .types_handle()
                            .get(ec)
                            .as_index_type()
                            .target
                            .expect("index type target");
                        self.instantiate_type(target, mapper)
                    }
                    _ => self.unknown_type,
                }
            };
            self.types_handle()
                .get_mut(t)
                .as_mapped_type_mut()
                .modifiers_type = Some(modifiers_type);
        }
        self.types_handle().get(t).as_mapped_type().modifiers_type
    }

    // `c.TypeToString` / `typeToString` are implemented in
    // `printer_util.rs` (checker/printer.go).

    /// `c.getExpandedParameters` — needed by `enter_signature_scope`.
    /// Go returns `[][]*ast.Symbol` and the caller takes `[0]`.
    pub fn get_expanded_parameters(
        &mut self,
        signature: SignatureId,
        skip_union_expanding: bool,
    ) -> Vec<Vec<SymbolId>> {
        fn get_uniq_associated_names_from_tuple_type(
            c: &mut Checker,
            t: TypeId,
            rest_symbol: SymbolId,
        ) -> Vec<String> {
            let target = c.types_handle().get(t).target().expect("tuple target");
            let infos = c
                .types_handle()
                .get(target)
                .as_tuple_type()
                .element_infos
                .clone();
            let mut names: Vec<String> = infos
                .iter()
                .enumerate()
                .map(|(i, info)| c.get_tuple_element_label(info.clone(), Some(rest_symbol), i))
                .collect();
            if !names.is_empty() {
                let mut duplicates: Vec<usize> = Vec::new();
                let mut unique_names: FxHashMap<String, bool> = FxHashMap::default();
                for (i, name) in names.iter().enumerate() {
                    if unique_names.contains_key(name) {
                        duplicates.push(i);
                    } else {
                        unique_names.insert(name.clone(), true);
                    }
                }
                let mut counters: FxHashMap<String, i32> = FxHashMap::default();
                for i in duplicates {
                    let counter = *counters.get(&names[i]).unwrap_or(&1);
                    let mut counter = counter;
                    let name = loop {
                        let name = format!("{}_{}", names[i], counter);
                        if unique_names.contains_key(&name) {
                            counter += 1;
                        } else {
                            unique_names.insert(name.clone(), true);
                            break name;
                        }
                    };
                    names[i] = name;
                    counters.insert(names[i].clone(), counter + 1);
                }
            }
            names
        }

        fn expand_signature_parameters_with_tuple_members(
            c: &mut Checker,
            rest_type: TypeId,
            rest_index: usize,
            rest_symbol: SymbolId,
            parameters: &[SymbolId],
        ) -> Vec<SymbolId> {
            let element_types = c.get_type_arguments(rest_type);
            let associated_names =
                get_uniq_associated_names_from_tuple_type(c, rest_type, rest_symbol);
            let target = c
                .types_handle()
                .get(rest_type)
                .target()
                .expect("tuple target");
            let element_infos = c
                .types_handle()
                .get(target)
                .as_tuple_type()
                .element_infos
                .clone();
            let mut rest_params: Vec<SymbolId> = Vec::with_capacity(element_types.len());
            for (i, &t) in element_types.iter().enumerate() {
                let name = associated_names[i].clone();
                let flags = element_infos[i].flags;
                let check_flags = if flags.intersects(crate::types::ElementFlags::VARIABLE) {
                    ast::checkflags::CheckFlags::REST_PARAMETER
                } else if flags.intersects(crate::types::ElementFlags::OPTIONAL) {
                    ast::checkflags::CheckFlags::OPTIONAL_PARAMETER
                } else {
                    ast::checkflags::CheckFlags::NONE
                };
                let symbol = c.new_symbol_ex(
                    ast::SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                    &name,
                    check_flags,
                );
                let resolved_type = if flags.intersects(crate::types::ElementFlags::REST) {
                    c.create_array_type(t)
                } else {
                    t
                };
                c.value_symbol_links.get(symbol).resolved_type = Some(resolved_type);
                rest_params.push(symbol);
            }
            let mut result = parameters[..rest_index].to_vec();
            result.extend(rest_params);
            result
        }

        if !crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(signature)) {
            let parameters = self.signature_arena.get(signature).parameters.clone();
            return vec![parameters];
        }
        let parameters = self.signature_arena.get(signature).parameters.clone();
        let rest_index = parameters.len() - 1;
        let rest_symbol = parameters[rest_index];
        let rest_type = self.get_type_of_symbol(rest_symbol);

        if is_tuple_type(&self.types, rest_type) {
            return vec![expand_signature_parameters_with_tuple_members(
                self,
                rest_type,
                rest_index,
                rest_symbol,
                &parameters,
            )];
        }
        let rest_flags = self.types_handle().get(rest_type).flags;
        if !skip_union_expanding && rest_flags.intersects(TypeFlags::UNION) {
            let union_types = self.types_handle().get(rest_type).types().to_vec();
            if union_types.iter().all(|&t| is_tuple_type(&self.types, t)) {
                return union_types
                    .iter()
                    .map(|&t| {
                        expand_signature_parameters_with_tuple_members(
                            self,
                            t,
                            rest_index,
                            rest_symbol,
                            &parameters,
                        )
                    })
                    .collect();
            }
        }
        vec![parameters]
    }

    /// `c.getSymbolOfDeclaration` (checker.go).
    pub fn get_symbol_of_declaration(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = crate::printer_util::resolve_arena_for(&__program, &[], node);
        let symbol = nodes.get(node.local_index() as usize)?.symbol();
        symbol.map(|s| {
            let late = self.get_late_bound_symbol(s);
            self.get_merged_symbol(late)
        })
    }

    // `c.containsArgumentsReference` (checker.go:32675) is implemented in
    // `checker_d.rs` (needs `&mut self` for `get_resolved_symbol`).

    /// `c.isArrayType` (checker.go) — delegates to the free function in
    /// `checker_c.rs`.
    pub fn is_array_type(&self, t: TypeId) -> bool {
        crate::checker_c::is_array_type(self, t)
    }

    /// `c.getTypeFromTypeNode` (checker.go) — delegates to the free function
    /// in `checker_c.rs`.
    pub fn get_type_from_type_node(&mut self, node: NodeId) -> TypeId {
        crate::checker_c::get_type_from_type_node(self, node)
    }

    /// `c.getResolvedSignatureWorker` (checker.go) — needed by
    /// `services.rs::get_resolved_signature_for_signature_help`.
    pub fn get_resolved_signature_worker(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
        argument_count: i32,
    ) -> (Option<SignatureId>, Vec<SignatureId>) {
        self.apparent_argument_count = Some(argument_count);
        let mut candidates_out_array: Vec<SignatureId> = Vec::new();
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let res = if ast::is_parse_tree_node(&nodes[node]) {
            self.get_resolved_signature(node, Some(&mut candidates_out_array), check_mode)
        } else {
            None
        };
        self.apparent_argument_count = None;
        (res, candidates_out_array)
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
        let mut callback =
            |n: &ast::Node, ns: &[ast::Node]| ast::is_call_like_or_function_like_expression(n, ns);
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
                let symbol = self.get_symbol_of_declaration(ancestor).expect(
                    "getSymbolOfDeclaration: nil symbol (Go would panic on GetSymbolId(nil))",
                );
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
    pub fn error(
        &mut self,
        location: Option<NodeId>,
        message: &'static tsc_diagnostics::Message,
        args: &[String],
    ) -> Option<ast::diagnostic::DiagnosticRef> {
        let diagnostic = self.new_diagnostic_for_node(location, message, args);
        Some(self.add_diagnostic(&diagnostic))
    }

    /// `c.errorOrSuggestion` (checker.go).
    pub fn error_or_suggestion(
        &mut self,
        is_error: bool,
        location: Option<NodeId>,
        message: &'static tsc_diagnostics::Message,
        args: &[String],
    ) {
        let diagnostic = self.new_diagnostic_for_node(location, message, args);
        self.add_error_or_suggestion(is_error, &diagnostic);
    }

    /// `c.getTypeParameterFromMappedType` (checker.go) — for
    /// `MappedType::resolve_components`. Delegates to `checker_c.rs`.
    pub fn get_type_parameter_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        crate::checker_c::get_type_parameter_from_mapped_type(self, t)
    }

    /// `c.getConstraintTypeFromMappedType` (checker.go) — delegates to
    /// `checker_c.rs`.
    pub fn get_constraint_type_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        crate::checker_c::get_constraint_type_from_mapped_type(self, t)
    }

    /// `c.getNameTypeFromMappedType` (checker.go) — delegates to
    /// `checker_c.rs`.
    pub fn get_name_type_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        crate::checker_c::get_name_type_from_mapped_type(self, t)
    }

    /// `c.getTemplateTypeFromMappedType` (checker.go) — delegates to
    /// `checker_c.rs`.
    pub fn get_template_type_from_mapped_type(&mut self, t: TypeId) -> Option<TypeId> {
        crate::checker_c::get_template_type_from_mapped_type(self, t)
    }

    /// `c.getTypeOfSymbol` (checker.go) — implemented in checker_c.rs.

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
        let __arena_types = self.types.clone();
        let types = __arena_types.clone();
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
        self.types_handle()
            .get_mut(t)
            .as_mapped_type_mut()
            .type_parameter = type_parameter;
        let constraint_type = self.get_constraint_type_from_mapped_type(t);
        self.types_handle()
            .get_mut(t)
            .as_mapped_type_mut()
            .constraint_type = constraint_type;
        let name_type = self.get_name_type_from_mapped_type(t);
        self.types_handle()
            .get_mut(t)
            .as_mapped_type_mut()
            .name_type = name_type;
        let template_type = self.get_template_type_from_mapped_type(t);
        self.types_handle()
            .get_mut(t)
            .as_mapped_type_mut()
            .template_type = template_type;
    }
}

// ======== new_checker — `func NewChecker` (checker.go) and constructor helpers ========
//
// `NewChecker`'s sequence is ported faithfully; helpers whose Go bodies need
// still-deferred machinery (`get_union_type`, `get_template_literal_type`,
// `get_type_arguments`, `evaluate_entity`, the `resolve_name` binder wiring,
// `initialize_checker`'s symbol merges) panic via `unimplemented!` when first
// reached — `new_checker` currently panics at `boolean_type`'s `get_union_type`
// until wave-2 fills those in.

/// `createFileIndexMap` (checker.go).
fn create_file_index_map(files: &[NodeId]) -> FxHashMap<NodeId, usize> {
    files.iter().enumerate().map(|(i, &f)| (f, i)).collect()
}

/// `countGlobalSymbols` (checker.go). Needs each file's node arena for
/// `IsExternalOrCommonJSModule`/`locals` — `program.nodes` supplies it.
fn count_global_symbols(
    files: &[NodeId],
    program: &Rc<dyn crate::checker_types::Program>,
) -> usize {
    let mut count = 0;
    for &file in files {
        let nodes = program.nodes(file.file_index());
        if !ast::is_external_or_commonjs_module(nodes[file].as_source_file()) {
            if let Some(locals) = nodes[file].locals() {
                count += locals.size();
            }
        }
    }
    count
}

/// `createSymbolTable` (utilities.go).
pub fn create_symbol_table(
    symbols: &[SymbolId],
    symbol_arena: &RefCell<Vec<ast::Symbol>>,
) -> SymbolTable {
    if symbols.is_empty() {
        return SymbolTable::new();
    }
    let mut result = SymbolTable::with_size_hint(symbols.len());
    let arena = symbol_arena.borrow();
    for &symbol in symbols {
        result.set(arena[symbol.index()].name.clone(), symbol);
    }
    result
}

/// `c.patternAmbientModules = append(c.patternAmbientModules,
/// file.PatternAmbientModules...)` — `initialize_checker`'s per-file gather.
fn gather_pattern_ambient_modules(file: &ast::Node, out: &mut Vec<ast::PatternAmbientModule>) {
    out.extend_from_slice(&file.as_source_file().pattern_ambient_modules);
}

/// Mutable state shared across `getTemplateLiteralType`'s recursive `addSpans`
/// inner function (checker.go:29704) — `newTypes`/`newTexts` collect the
/// placeholders while `sb` accumulates literal text, `textLength` tracks the
/// combined length already moved into `newTexts`, and `tooLarge` records a
/// span/size overflow.
struct TemplateLiteralSpanState {
    new_types: Vec<TypeId>,
    new_texts: Vec<String>,
    sb: String,
    text_length: usize,
    too_large: bool,
}

impl Checker {
    /// `func NewChecker` (checker.go) — PORT: fields are assigned in the same
    /// order as Go. Go returns `(*Checker, *sync.Mutex)`; the mutex is the
    /// `mu` field, so this returns just `Checker`.
    pub fn new_checker(
        program: Rc<dyn crate::checker_types::Program>,
        tracer: Option<Tracer>,
    ) -> Checker {
        program.bind_source_files();

        let mut c = Checker::empty();
        c.id = NEXT_CHECKER_ID.fetch_add(1, Ordering::Relaxed);
        c.tracer = tracer;
        c.program = Some(program.clone());
        // Alias the program's global symbol arena (SPEC §5.2): binder ids and
        // checker-created symbols share one `Vec`, standing in for Go's
        // `*ast.Symbol` pointer identity.
        c.symbol_arena = program.symbols();
        c.compiler_options = program.options();
        c.files = program.source_files();
        c.file_index_map = create_file_index_map(&c.files);
        // Closure optimization — Go assigns method values; the port routes
        // through `&mut Checker` thunks.
        c.compare_symbols = Some(Rc::new(|c: &mut Checker, s1, s2| {
            c.compare_symbols_worker(s1, s2)
        }));
        c.compare_symbol_chains = Some(Rc::new(|c: &mut Checker, a, b| {
            c.compare_symbol_chains_worker(a, b)
        }));
        c.language_version = c.compiler_options.get_emit_script_target();
        c.module_kind = c.compiler_options.get_emit_module_kind();
        c.module_resolution_kind = c.compiler_options.get_module_resolution_kind();
        c.legacy_decorators = c.compiler_options.experimental_decorators.is_true();
        c.emit_standard_class_fields = c.compiler_options.get_emit_standard_class_fields();
        c.strict_null_checks = c
            .compiler_options
            .get_strict_option_value(c.compiler_options.strict_null_checks);
        c.strict_function_types = c
            .compiler_options
            .get_strict_option_value(c.compiler_options.strict_function_types);
        c.strict_bind_call_apply = c
            .compiler_options
            .get_strict_option_value(c.compiler_options.strict_bind_call_apply);
        c.strict_property_initialization = c
            .compiler_options
            .get_strict_option_value(c.compiler_options.strict_property_initialization);
        c.strict_builtin_iterator_return = c
            .compiler_options
            .get_strict_option_value(c.compiler_options.strict_builtin_iterator_return);
        c.no_implicit_any = c
            .compiler_options
            .get_strict_option_value(c.compiler_options.no_implicit_any);
        c.no_implicit_this = c
            .compiler_options
            .get_strict_option_value(c.compiler_options.no_implicit_this);
        c.use_unknown_in_catch_variables = c
            .compiler_options
            .get_strict_option_value(c.compiler_options.use_unknown_in_catch_variables);
        c.exact_optional_property_types =
            c.compiler_options.exact_optional_property_types.is_true();
        c.can_collect_symbol_alias_accessibility_data = c
            .compiler_options
            .verbatim_module_syntax
            .is_false_or_unknown();
        c.array_variances = vec![VarianceFlags::COVARIANT];
        *c.globals.borrow_mut() =
            SymbolTable::with_size_hint(count_global_symbols(&c.files, &program));
        // PORT: Go `evaluator.NewEvaluator(c.evaluateEntity,
        // ast.OEKParentheses)` — the thunk rebuilds the stateless evaluator
        // around `evaluate_entity` so template/binary/unary expressions are
        // folded before entity lookup.
        c.evaluate = Some(Rc::new(|c: &mut Checker, expr, location, nodes| {
            let mut evaluator = tsc_evaluator::new_evaluator(
                |e: NodeId, l: Option<NodeId>, ns: &[ast::Node]| c.evaluate_entity(e, l, ns),
                tsc_ast::utilities::outer_expression_kinds::PARENTHESES,
            );
            evaluator(expr, location, nodes)
        }));
        c.undefined_symbol = c.new_symbol(ast::SymbolFlags::PROPERTY, "undefined");
        c.arguments_symbol = c.new_symbol(ast::SymbolFlags::PROPERTY, "arguments");
        c.require_symbol = c.new_symbol(ast::SymbolFlags::PROPERTY, "require");
        c.unknown_symbol = c.new_symbol(ast::SymbolFlags::PROPERTY, "unknown");
        c.global_this_symbol = c.new_symbol_ex(
            ast::SymbolFlags::MODULE,
            "globalThis",
            ast::checkflags::CheckFlags::READONLY,
        );
        // `c.globalThisSymbol.Exports = c.globals` — Go shares the map header
        // (later `c.globals` inserts show through `exports`); `Symbol.exports`
        // is a value field here, so this is a snapshot. PORT(divergence):
        // `globals` itself is now `Rc<RefCell<SymbolTable>>`; callers that
        // need live sharing go through `globals`, not `exports`.
        let globals = c.globals.borrow().clone();
        c.symbol_arena.borrow_mut()[c.global_this_symbol.index()].exports = globals;
        let name = c.symbol_arena.borrow()[c.global_this_symbol.index()]
            .name
            .clone();
        c.globals.borrow_mut().set(name, c.global_this_symbol);
        c.resolve_name = Some(c.create_name_resolver());
        c.resolve_name_for_symbol_suggestion = Some(c.create_name_resolver_for_suggestion());
        // Type/cache maps — empty by `Checker::empty()` (Go `make(map)`).
        c.any_type = c.new_intrinsic_type(TypeFlags::ANY, "any");
        c.auto_type =
            c.new_intrinsic_type_ex(TypeFlags::ANY, "any", ObjectFlags::NON_INFERRABLE_TYPE);
        c.wildcard_type = c.new_intrinsic_type(TypeFlags::ANY, "any");
        c.blocked_string_type = c.new_intrinsic_type(TypeFlags::ANY, "any");
        c.error_type = c.new_intrinsic_type(TypeFlags::ANY, "error");
        c.unresolved_type = c.new_intrinsic_type(TypeFlags::ANY, "unresolved");
        c.non_inferrable_any_type =
            c.new_intrinsic_type_ex(TypeFlags::ANY, "any", ObjectFlags::CONTAINS_WIDENING_TYPE);
        c.intrinsic_marker_type = c.new_intrinsic_type(TypeFlags::ANY, "intrinsic");
        c.unknown_type = c.new_intrinsic_type(TypeFlags::UNKNOWN, "unknown");
        c.undefined_type = c.new_intrinsic_type(TypeFlags::UNDEFINED, "undefined");
        c.undefined_widening_type = c.create_widening_type(c.undefined_type);
        c.missing_type = c.new_intrinsic_type(TypeFlags::UNDEFINED, "undefined");
        c.undefined_or_missing_type = if c.exact_optional_property_types {
            c.missing_type
        } else {
            c.undefined_type
        };
        c.optional_type = c.new_intrinsic_type(TypeFlags::UNDEFINED, "undefined");
        c.null_type = c.new_intrinsic_type(TypeFlags::NULL, "null");
        c.null_widening_type = c.create_widening_type(c.null_type);
        c.string_type = c.new_intrinsic_type(TypeFlags::STRING, "string");
        c.number_type = c.new_intrinsic_type(TypeFlags::NUMBER, "number");
        c.bigint_type = c.new_intrinsic_type(TypeFlags::BIG_INT, "bigint");
        c.regular_false_type = c.new_literal_type(
            TypeFlags::BOOLEAN_LITERAL,
            Some(evaluator::Value::Bool(false)),
            None,
        );
        c.false_type = c.new_literal_type(
            TypeFlags::BOOLEAN_LITERAL,
            Some(evaluator::Value::Bool(false)),
            Some(c.regular_false_type),
        );
        if let TypeData::Literal(d) = &mut c.types_handle().get_mut(c.regular_false_type).data {
            d.fresh_type = Some(c.false_type);
        }
        if let TypeData::Literal(d) = &mut c.types_handle().get_mut(c.false_type).data {
            d.fresh_type = Some(c.false_type);
        }
        c.regular_true_type = c.new_literal_type(
            TypeFlags::BOOLEAN_LITERAL,
            Some(evaluator::Value::Bool(true)),
            None,
        );
        c.true_type = c.new_literal_type(
            TypeFlags::BOOLEAN_LITERAL,
            Some(evaluator::Value::Bool(true)),
            Some(c.regular_true_type),
        );
        if let TypeData::Literal(d) = &mut c.types_handle().get_mut(c.regular_true_type).data {
            d.fresh_type = Some(c.true_type);
        }
        if let TypeData::Literal(d) = &mut c.types_handle().get_mut(c.true_type).data {
            d.fresh_type = Some(c.true_type);
        }
        c.boolean_type = c.get_union_type(&[c.regular_false_type, c.regular_true_type]);
        c.es_symbol_type = c.new_intrinsic_type(TypeFlags::ES_SYMBOL, "symbol");
        c.void_type = c.new_intrinsic_type(TypeFlags::VOID, "void");
        c.never_type = c.new_intrinsic_type(TypeFlags::NEVER, "never");
        c.silent_never_type =
            c.new_intrinsic_type_ex(TypeFlags::NEVER, "never", ObjectFlags::NON_INFERRABLE_TYPE);
        c.implicit_never_type = c.new_intrinsic_type(TypeFlags::NEVER, "never");
        c.unreachable_never_type = c.new_intrinsic_type(TypeFlags::NEVER, "never");
        c.non_primitive_type = c.new_intrinsic_type(TypeFlags::NON_PRIMITIVE, "object");
        c.string_or_number_type = c.get_union_type(&[c.string_type, c.number_type]);
        c.string_number_symbol_type =
            c.get_union_type(&[c.string_type, c.number_type, c.es_symbol_type]);
        c.number_or_big_int_type = c.get_union_type(&[c.number_type, c.bigint_type]);
        // The `${number}` type.
        c.numeric_string_type =
            c.get_template_literal_type(&["".to_string(), "".to_string()], &[c.number_type]);
        c.template_constraint_type = c.get_union_type(&[
            c.string_type,
            c.number_type,
            c.boolean_type,
            c.bigint_type,
            c.null_type,
            c.undefined_type,
        ]);
        // Special `never` flagged by union reduction to behave as a literal.
        c.unique_literal_type = c.new_intrinsic_type(TypeFlags::NEVER, "never");
        c.unique_literal_mapper = crate::mapper::new_function_type_mapper(&mut c, |c, t| {
            c.get_unique_literal_type_for_type_parameter(t)
        });
        c.report_unreliable_mapper =
            crate::mapper::new_function_type_mapper(&mut c, |c, t| c.report_unreliable_worker(t));
        c.report_unmeasurable_mapper =
            crate::mapper::new_function_type_mapper(&mut c, |c, t| c.report_unmeasurable_worker(t));
        c.restrictive_mapper =
            crate::mapper::new_function_type_mapper(&mut c, |c, t| c.restrictive_mapper_worker(t));
        c.permissive_mapper =
            crate::mapper::new_function_type_mapper(&mut c, |c, t| c.permissive_mapper_worker(t));
        c.empty_object_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.empty_jsx_object_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.empty_fresh_jsx_object_type =
            c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        let type_literal_symbol = c.new_symbol(
            ast::SymbolFlags::TYPE_LITERAL,
            ast::symbol::INTERNAL_SYMBOL_NAME_TYPE,
        );
        c.empty_type_literal_type =
            c.new_anonymous_type(Some(type_literal_symbol), SymbolTable::new(), &[], &[], &[]);
        c.unknown_empty_object_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.unknown_union_type = c.create_unknown_union_type();
        c.empty_generic_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        // `c.emptyGenericType.AsObjectType().instantiations = make(map)` — the
        // port's field is already an empty map.
        c.any_function_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.types_handle()
            .get_mut(c.any_function_type)
            .object_flags
            .insert(ObjectFlags::NON_INFERRABLE_TYPE);
        c.no_constraint_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.circular_constraint_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.resolving_default_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.marker_super_type = c.new_type_parameter(None);
        c.marker_sub_type = c.new_type_parameter(None);
        if let TypeData::TypeParameter(d) = &mut c.types_handle().get_mut(c.marker_sub_type).data {
            d.constraint = Some(c.marker_super_type);
        }
        c.marker_other_type = c.new_type_parameter(None);
        c.marker_super_type_for_check = c.new_type_parameter(None);
        c.marker_sub_type_for_check = c.new_type_parameter(None);
        if let TypeData::TypeParameter(d) =
            &mut c.types_handle().get_mut(c.marker_sub_type_for_check).data
        {
            d.constraint = Some(c.marker_super_type_for_check);
        }
        c.no_type_predicate = Some(Rc::new(TypePredicate {
            kind: crate::types::TypePredicateKind::Identifier,
            parameter_index: 0,
            parameter_name: "<<unresolved>>".to_string(),
            t: Some(c.any_type),
        }));
        c.any_signature = c.new_signature(
            crate::types::SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            Vec::new(),
            Some(c.any_type),
            None,
            0,
        );
        c.unknown_signature = c.new_signature(
            crate::types::SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            Vec::new(),
            Some(c.error_type),
            None,
            0,
        );
        c.resolving_signature = c.new_signature(
            crate::types::SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            Vec::new(),
            Some(c.any_type),
            None,
            0,
        );
        c.silent_never_signature = c.new_signature(
            crate::types::SignatureFlags::NONE,
            None,
            Vec::new(),
            None,
            Vec::new(),
            Some(c.silent_never_type),
            None,
            0,
        );
        c.enum_number_index_info = c.index_info_arena.alloc(IndexInfo {
            key_type: Some(c.number_type),
            value_type: Some(c.string_type),
            is_readonly: true,
            ..Default::default()
        });
        c.any_base_type_index_info = c.index_info_arena.alloc(IndexInfo {
            key_type: Some(c.string_type),
            value_type: Some(c.any_type),
            is_readonly: false,
            ..Default::default()
        });
        c.empty_string_type = c.get_string_literal_type("");
        c.zero_type = c.get_number_literal_type(tsc_jsnum::Number(0.0));
        c.zero_big_int_type = c.get_big_int_literal_type(PseudoBigInt::default());
        // `slices.Sorted(maps.Keys(typeofNEFacts))`.
        let mut typeof_names: Vec<&'static str> = vec![
            "string",
            "number",
            "bigint",
            "boolean",
            "symbol",
            "undefined",
            "object",
            "function",
        ];
        typeof_names.sort();
        let typeof_types: Vec<TypeId> = typeof_names
            .iter()
            .map(|name| c.get_string_literal_type(name))
            .collect();
        c.typeof_type = c.get_union_type(&typeof_types);
        // Relations — `Checker::empty()` shares fresh `Relation`s.
        c.get_global_es_symbol_type = Some(c.get_global_type_resolver("Symbol", 0, false));
        c.get_global_big_int_type = Some(c.get_global_type_resolver("BigInt", 0, false));
        c.get_global_import_meta_type = Some(c.get_global_type_resolver("ImportMeta", 0, true));
        c.get_global_import_attributes_type =
            Some(c.get_global_type_resolver("ImportAttributes", 0, false));
        c.get_global_import_attributes_type_checked =
            Some(c.get_global_type_resolver("ImportAttributes", 0, true));
        c.get_global_non_nullable_type_alias_or_nil =
            Some(c.get_global_type_alias_resolver("NonNullable", 1, false));
        c.get_global_extract_symbol = Some(c.get_global_type_alias_resolver("Extract", 2, true));
        c.get_global_disposable_type = Some(c.get_global_type_resolver("Disposable", 0, true));
        c.get_global_async_disposable_type =
            Some(c.get_global_type_resolver("AsyncDisposable", 0, true));
        c.get_global_awaited_symbol = Some(c.get_global_type_alias_resolver("Awaited", 1, true));
        c.get_global_awaited_symbol_or_nil =
            Some(c.get_global_type_alias_resolver("Awaited", 1, false));
        c.get_global_nan_symbol_or_nil = Some(c.get_global_value_symbol_resolver("NaN", false));
        c.get_global_record_symbol = Some(c.get_global_type_alias_resolver("Record", 2, true));
        c.get_global_template_strings_array_type =
            Some(c.get_global_type_resolver("TemplateStringsArray", 0, true));
        c.get_global_es_symbol_constructor_symbol_or_nil =
            Some(c.get_global_value_symbol_resolver("Symbol", false));
        c.get_global_es_symbol_constructor_type_symbol_or_nil =
            Some(c.get_global_type_symbol_resolver("SymbolConstructor", false));
        c.get_global_import_call_options_type =
            Some(c.get_global_type_resolver("ImportCallOptions", 0, false));
        c.get_global_import_call_options_type_checked =
            Some(c.get_global_type_resolver("ImportCallOptions", 0, true));
        c.get_global_promise_type = Some(c.get_global_type_resolver("Promise", 1, false));
        c.get_global_promise_type_checked = Some(c.get_global_type_resolver("Promise", 1, true));
        c.get_global_promise_like_type = Some(c.get_global_type_resolver("PromiseLike", 1, true));
        c.get_global_abstract_module_source_type =
            Some(c.get_global_type_resolver("AbstractModuleSource", 0, true));
        c.get_global_promise_constructor_symbol =
            Some(c.get_global_value_symbol_resolver("Promise", true));
        c.get_global_promise_constructor_symbol_or_nil =
            Some(c.get_global_value_symbol_resolver("Promise", false));
        c.get_global_omit_symbol = Some(c.get_global_type_alias_resolver("Omit", 2, true));
        c.get_global_no_infer_symbol_or_nil =
            Some(c.get_global_type_alias_resolver("NoInfer", 1, false));
        c.get_global_iterator_type = Some(c.get_global_type_resolver("Iterator", 3, false));
        c.get_global_iterable_type = Some(c.get_global_type_resolver("Iterable", 3, false));
        c.get_global_iterable_type_checked = Some(c.get_global_type_resolver("Iterable", 3, true));
        c.get_global_iterable_iterator_type =
            Some(c.get_global_type_resolver("IterableIterator", 3, false));
        c.get_global_iterable_iterator_type_checked =
            Some(c.get_global_type_resolver("IterableIterator", 3, true));
        c.get_global_iterator_object_type =
            Some(c.get_global_type_resolver("IteratorObject", 3, false));
        c.get_global_generator_type = Some(c.get_global_type_resolver("Generator", 3, false));
        c.get_global_async_iterator_type =
            Some(c.get_global_type_resolver("AsyncIterator", 3, false));
        c.get_global_async_iterable_type =
            Some(c.get_global_type_resolver("AsyncIterable", 3, false));
        c.get_global_async_iterable_type_checked =
            Some(c.get_global_type_resolver("AsyncIterable", 3, true));
        c.get_global_async_iterable_iterator_type =
            Some(c.get_global_type_resolver("AsyncIterableIterator", 3, false));
        c.get_global_async_iterable_iterator_type_checked =
            Some(c.get_global_type_resolver("AsyncIterableIterator", 3, true));
        c.get_global_async_iterator_object_type =
            Some(c.get_global_type_resolver("AsyncIteratorObject", 3, false));
        c.get_global_async_generator_type =
            Some(c.get_global_type_resolver("AsyncGenerator", 3, false));
        c.get_global_iterator_yield_result_type =
            Some(c.get_global_type_resolver("IteratorYieldResult", 1, false));
        c.get_global_iterator_return_result_type =
            Some(c.get_global_type_resolver("IteratorReturnResult", 1, false));
        c.get_global_typed_property_descriptor_type =
            Some(c.get_global_type_resolver("TypedPropertyDescriptor", 1, true));
        c.get_global_class_decorator_context_type =
            Some(c.get_global_type_resolver("ClassDecoratorContext", 1, true));
        c.get_global_class_method_decorator_context_type =
            Some(c.get_global_type_resolver("ClassMethodDecoratorContext", 2, true));
        c.get_global_class_getter_decorator_context_type =
            Some(c.get_global_type_resolver("ClassGetterDecoratorContext", 2, true));
        c.get_global_class_setter_decorator_context_type =
            Some(c.get_global_type_resolver("ClassSetterDecoratorContext", 2, true));
        c.get_global_class_accessor_decorator_contxt_type =
            Some(c.get_global_type_resolver("ClassAccessorDecoratorContext", 2, true));
        c.get_global_class_accessor_decorator_context_type =
            Some(c.get_global_type_resolver("ClassAccessorDecoratorContext", 2, true));
        c.get_global_class_accessor_decorator_target_type =
            Some(c.get_global_type_resolver("ClassAccessorDecoratorTarget", 2, true));
        c.get_global_class_accessor_decorator_result_type =
            Some(c.get_global_type_resolver("ClassAccessorDecoratorResult", 2, true));
        c.get_global_class_field_decorator_context_type =
            Some(c.get_global_type_resolver("ClassFieldDecoratorContext", 2, true));
        c.initialize_closures();
        c.initialize_iteration_resolvers();
        c.initialize_checker();
        // Go returns `&c.mu` too; `mu` is the `Checker` field.
        c
    }

    // ======== NewChecker helpers ========

    /// `(c *Checker) getGlobalTypeResolver` — `core.Memoize` becomes an
    /// `Rc<RefCell<Option<..>>>` cell inside the `Rc` thunk so memoization is
    /// shared with every field/resolver that clones the `Rc` (Go shares the
    /// same func value).
    pub fn get_global_type_resolver(
        &self,
        name: &'static str,
        arity: i32,
        report_errors: bool,
    ) -> Rc<TypeThunk<'static>> {
        let cache: Rc<RefCell<Option<TypeId>>> = Rc::new(RefCell::new(None));
        Rc::new(move |c: &mut Checker| {
            if let Some(t) = *cache.borrow() {
                return t;
            }
            let t = c.get_global_type(name, arity, report_errors);
            *cache.borrow_mut() = Some(t);
            t
        })
    }

    /// `(c *Checker) getGlobalTypeAliasResolver`.
    pub fn get_global_type_alias_resolver(
        &self,
        name: &'static str,
        arity: i32,
        report_errors: bool,
    ) -> Rc<crate::checker_types::SymbolThunk<'static>> {
        let cache: Rc<RefCell<Option<Option<SymbolId>>>> = Rc::new(RefCell::new(None));
        Rc::new(move |c: &mut Checker| {
            if let Some(s) = *cache.borrow() {
                return s;
            }
            let s = c.get_global_type_alias_symbol(name, arity, report_errors);
            *cache.borrow_mut() = Some(s);
            s
        })
    }

    /// `(c *Checker) getGlobalValueSymbolResolver`.
    pub fn get_global_value_symbol_resolver(
        &self,
        name: &'static str,
        report_errors: bool,
    ) -> Rc<crate::checker_types::SymbolThunk<'static>> {
        let cache: Rc<RefCell<Option<Option<SymbolId>>>> = Rc::new(RefCell::new(None));
        Rc::new(move |c: &mut Checker| {
            if let Some(s) = *cache.borrow() {
                return s;
            }
            let s = c.get_global_symbol(
                name,
                ast::SymbolFlags::VALUE,
                report_errors.then_some(&tsc_diagnostics::Cannot_find_global_value_0),
            );
            *cache.borrow_mut() = Some(s);
            s
        })
    }

    /// `(c *Checker) getGlobalTypeSymbolResolver`.
    pub fn get_global_type_symbol_resolver(
        &self,
        name: &'static str,
        report_errors: bool,
    ) -> Rc<crate::checker_types::SymbolThunk<'static>> {
        let cache: Rc<RefCell<Option<Option<SymbolId>>>> = Rc::new(RefCell::new(None));
        Rc::new(move |c: &mut Checker| {
            if let Some(s) = *cache.borrow() {
                return s;
            }
            let s = c.get_global_symbol(
                name,
                ast::SymbolFlags::TYPE,
                report_errors.then_some(&tsc_diagnostics::Cannot_find_global_type_0),
            );
            *cache.borrow_mut() = Some(s);
            s
        })
    }

    /// `(c *Checker) getGlobalTypesResolver`.
    pub fn get_global_types_resolver(
        &self,
        names: &'static [&'static str],
        arity: i32,
        report_errors: bool,
    ) -> Rc<crate::checker_types::TypeListThunk<'static>> {
        let cache: Rc<RefCell<Option<Vec<TypeId>>>> = Rc::new(RefCell::new(None));
        Rc::new(move |c: &mut Checker| {
            if let Some(ts) = &*cache.borrow() {
                return ts.clone();
            }
            let ts: Vec<TypeId> = names
                .iter()
                .map(|name| c.get_global_type(name, arity, report_errors))
                .collect();
            *cache.borrow_mut() = Some(ts.clone());
            ts
        })
    }

    /// `(c *Checker) getGlobalTypeAliasSymbol`.
    pub fn get_global_type_alias_symbol(
        &mut self,
        name: &str,
        arity: i32,
        report_errors: bool,
    ) -> Option<SymbolId> {
        let symbol = self.get_global_symbol(
            name,
            ast::SymbolFlags::TYPE_ALIAS,
            report_errors.then_some(&tsc_diagnostics::Cannot_find_global_type_0),
        )?;
        // Resolve the declared type of the symbol. This resolves type
        // parameters for the type alias so that we can check arity.
        self.get_declared_type_of_symbol(symbol);
        let type_parameter_count = self.type_alias_links.get(symbol).type_parameters.len();
        if type_parameter_count != arity as usize {
            if report_errors {
                let decl = {
                    let arena = self.symbol_arena.borrow();
                    arena[symbol.index()]
                        .declarations
                        .iter()
                        .copied()
                        .find(|&d| {
                            let __program = self.program.clone().expect("program");
                            let nodes = __program.nodes((d).file_index());
                            ast::is_type_alias_declaration(&nodes[d])
                        })
                };
                let arg = self.symbol_display_name(symbol);
                self.error(
                    decl,
                    &tsc_diagnostics::Global_type_0_must_have_1_type_parameter_s,
                    &[arg, arity.to_string()],
                );
            }
            return None;
        }
        Some(symbol)
    }

    /// `(c *Checker) getGlobalType` — resolve to the global class or
    /// interface by the given name and arity, or
    /// `emptyObjectType`/`emptyGenericType` otherwise.
    pub fn get_global_type(&mut self, name: &str, arity: i32, report_errors: bool) -> TypeId {
        let symbol = self.get_global_symbol(
            name,
            ast::SymbolFlags::TYPE,
            report_errors.then_some(&tsc_diagnostics::Cannot_find_global_type_0),
        );
        if let Some(symbol) = symbol {
            let flags = self.symbol_arena.borrow()[symbol.index()].flags;
            if flags.intersects(ast::SymbolFlags::CLASS | ast::SymbolFlags::INTERFACE) {
                let t = self.get_declared_type_of_symbol(symbol);
                let __arena_type_parameter_count = self.types.clone();
                let type_parameter_count = __arena_type_parameter_count
                    .get(t)
                    .as_interface_type()
                    .expect("interface type")
                    .type_parameters()
                    .len();
                if type_parameter_count == arity as usize {
                    return t;
                }
                if report_errors {
                    let decl = self.get_global_type_declaration(symbol);
                    let arg = self.symbol_display_name(symbol);
                    self.error(
                        decl,
                        &tsc_diagnostics::Global_type_0_must_have_1_type_parameter_s,
                        &[arg, arity.to_string()],
                    );
                }
            } else if report_errors {
                let decl = self.get_global_type_declaration(symbol);
                let arg = self.symbol_display_name(symbol);
                self.error(
                    decl,
                    &tsc_diagnostics::Global_type_0_must_be_a_class_or_interface_type,
                    &[arg],
                );
            }
        }
        if arity != 0 {
            return self.empty_generic_type;
        }
        self.empty_object_type
    }

    /// `getGlobalTypeDeclaration` (checker.go) — a checker method here for the
    /// node arena.
    pub fn get_global_type_declaration(&self, symbol: SymbolId) -> Option<NodeId> {
        let declarations = self.symbol_arena.borrow()[symbol.index()]
            .declarations
            .clone();
        for declaration in declarations {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((declaration).file_index());
            match nodes[declaration].kind {
                ast::Kind::ClassDeclaration
                | ast::Kind::InterfaceDeclaration
                | ast::Kind::EnumDeclaration
                | ast::Kind::TypeAliasDeclaration => return Some(declaration),
                _ => {}
            }
        }
        None
    }

    /// `(c *Checker) getGlobalSymbol` — `resolveName` with `isReference`
    /// arbitrary (don't track references for global symbols).
    pub fn get_global_symbol(
        &mut self,
        name: &str,
        meaning: ast::SymbolFlags,
        diagnostic: Option<&'static tsc_diagnostics::Message>,
    ) -> Option<SymbolId> {
        let resolve = self
            .resolve_name
            .clone()
            .expect("resolveName not initialized");
        resolve(self, None, name, meaning, diagnostic, false, false)
    }

    /// `(c *Checker) initializeClosures` (checker.go).
    pub fn initialize_closures(&mut self) {
        self.is_primitive_or_object_or_empty_type = Some(Rc::new(|c: &mut Checker, t: TypeId| {
            c.types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::PRIMITIVE | TypeFlags::NON_PRIMITIVE)
                || c.is_empty_anonymous_object_type(t)
        }));
        self.contains_missing_type = Some(Rc::new(|c: &mut Checker, t: TypeId| {
            if t == c.missing_type {
                return true;
            }
            let __arena_ty = c.types.clone();
            let ty = __arena_ty.get(t);
            ty.flags.intersects(TypeFlags::UNION) && ty.types().first() == Some(&c.missing_type)
        }));
        self.could_contain_type_variables = Some(Rc::new(|c: &mut Checker, t: TypeId| {
            c.could_contain_type_variables_worker(t)
        }));
        self.is_string_index_signature_only_type = Some(Rc::new(|c: &mut Checker, t: TypeId| {
            c.is_string_index_signature_only_type_worker(t)
        }));
        self.mark_node_assignments = Some(Rc::new(|c: &mut Checker, node: NodeId| {
            c.mark_node_assignments_worker(node)
        }));
        self.compare_types_assignable =
            Some(Rc::new(|c: &mut Checker, source, target, report_errors| {
                c.compare_types_assignable_worker(source, target, report_errors)
            }));
    }

    /// `(c *Checker) initializeIterationResolvers` (checker.go).
    pub fn initialize_iteration_resolvers(&mut self) {
        self.sync_iteration_types_resolver = Some(Box::new(IterationTypesResolver {
            iterator_symbol_name: "iterator".to_string(),
            get_global_iterator_type: self.get_global_iterator_type.clone(),
            get_global_iterable_type: self.get_global_iterable_type.clone(),
            get_global_iterable_type_checked: self.get_global_iterable_type_checked.clone(),
            get_global_iterable_iterator_type: self.get_global_iterable_iterator_type.clone(),
            get_global_iterable_iterator_type_checked: self
                .get_global_iterable_iterator_type_checked
                .clone(),
            get_global_iterator_object_type: self.get_global_iterator_object_type.clone(),
            get_global_generator_type: self.get_global_generator_type.clone(),
            get_global_builtin_iterator_types: Some(self.get_global_types_resolver(
                &["ArrayIterator", "MapIterator", "SetIterator", "StringIterator"],
                1,
                false,
            )),
            resolve_iteration_type: Some(Rc::new(|_c: &mut Checker, t: TypeId, _error_node| t)),
            must_have_a_next_method_diagnostic: Some(
                &tsc_diagnostics::An_iterator_must_have_a_next_method,
            ),
            must_be_a_method_diagnostic: Some(
                &tsc_diagnostics::The_0_property_of_an_iterator_must_be_a_method,
            ),
            must_have_a_value_diagnostic: Some(
                &tsc_diagnostics::The_type_returned_by_the_0_method_of_an_iterator_must_have_a_value_property,
            ),
        }));
        self.async_iteration_types_resolver = Some(Box::new(IterationTypesResolver {
            iterator_symbol_name: "asyncIterator".to_string(),
            get_global_iterator_type: self.get_global_async_iterator_type.clone(),
            get_global_iterable_type: self.get_global_async_iterable_type.clone(),
            get_global_iterable_type_checked: self.get_global_async_iterable_type_checked.clone(),
            get_global_iterable_iterator_type: self
                .get_global_async_iterable_iterator_type
                .clone(),
            get_global_iterable_iterator_type_checked: self
                .get_global_async_iterable_iterator_type_checked
                .clone(),
            get_global_iterator_object_type: self.get_global_async_iterator_object_type.clone(),
            get_global_generator_type: self.get_global_async_generator_type.clone(),
            get_global_builtin_iterator_types: Some(self.get_global_types_resolver(
                &["ReadableStreamAsyncIterator"],
                1,
                false,
            )),
            resolve_iteration_type: Some(Rc::new(|c: &mut Checker, t: TypeId, error_node| {
                c.get_awaited_type_ex(
                    t,
                    error_node,
                    Some(
                        &tsc_diagnostics::Type_of_await_operand_must_either_be_a_valid_promise_or_must_not_contain_a_callable_then_member,
                    ),
                    &[],
                )
                .unwrap_or(c.error_type)
            })),
            must_have_a_next_method_diagnostic: Some(
                &tsc_diagnostics::An_async_iterator_must_have_a_next_method,
            ),
            must_be_a_method_diagnostic: Some(
                &tsc_diagnostics::The_0_property_of_an_async_iterator_must_be_a_method,
            ),
            must_have_a_value_diagnostic: Some(
                &tsc_diagnostics::The_type_returned_by_the_0_method_of_an_async_iterator_must_be_a_promise_for_a_type_with_a_value_property,
            ),
        }));
    }

    /// `(c *Checker) initializeChecker` (checker.go) — PORT(partial): the
    /// loop structure is faithful; `merge_global_symbol` (via
    /// `merge_symbol`/`get_merged_symbol`), `merge_module_augmentation`,
    /// `merge_pattern_ambient_modules`, and the `get_global_type`
    /// resolutions panic via `unimplemented!`/deferred machinery until
    /// wave-2 (they need `resolve_name` and symbol merging).
    pub fn initialize_checker(&mut self) {
        let __init_t = std::time::Instant::now();
        // Initialize global symbol table
        let mut ambient_module_symbols: Vec<SymbolId> = Vec::new();
        let mut augmentations: Vec<Vec<NodeId>> = Vec::new();
        let files = self.files.clone();
        // PORT(borrowck): clone the program `Rc` so per-file `Ref` arena
        // borrows don't pin `*self` while `merge_*` needs `&mut`.
        let __program = self.program.clone().expect("program");
        for file in &files {
            let nodes = __program.nodes(file.file_index());
            let file_node = &nodes[*file];
            if !ast::is_external_or_commonjs_module(file_node.as_source_file()) {
                // It is an error for a non-external-module (i.e. script) to
                // declare its own `globalThis`.
                if let Some(locals) = file_node.locals() {
                    if let Some(&file_global_this_symbol) = locals.get("globalThis") {
                        let declarations = self.symbol_arena.borrow()
                            [file_global_this_symbol.index()]
                        .declarations
                        .clone();
                        for d in declarations {
                            let diagnostic = self.new_diagnostic_for_node(
                                Some(d),
                                &tsc_diagnostics::Declaration_name_conflicts_with_built_in_global_identifier_0,
                                &["globalThis".to_string()],
                            );
                            self.diagnostics.add(&diagnostic);
                        }
                    }
                    // We defer merging of global ambient module declarations
                    // since they may require other global symbols and types
                    // to be resolved.
                    for (_, &symbol) in locals.entries() {
                        let (flags, name) = {
                            let arena = self.symbol_arena.borrow();
                            (
                                arena[symbol.index()].flags,
                                arena[symbol.index()].name.clone(),
                            )
                        };
                        if flags.intersects(ast::SymbolFlags::MODULE)
                            && ast::symbol::is_ambient_module_symbol_name(&name)
                        {
                            ambient_module_symbols.push(symbol);
                        } else {
                            self.merge_global_symbol(symbol);
                        }
                    }
                }
            }
            gather_pattern_ambient_modules(&nodes[*file], &mut self.pattern_ambient_modules);
            augmentations.push(nodes[*file].as_source_file().module_augmentations.to_vec());
            if let Some(_file_symbol) = file_node.symbol() {
                // Merge in UMD exports with first-in-wins semantics
                // (see #9771)
                for (name, &symbol) in nodes[*file].as_source_file().global_exports.entries() {
                    if self.globals.borrow().get(name).is_none() {
                        self.globals.borrow_mut().set(name.clone(), symbol);
                    }
                }
            }
        }
        // We do global augmentations separately from module augmentations
        // (and before creating global types) because they
        //  1. Affect global types. We won't have the correct global types
        //     until global augmentations are merged. Also,
        //  2. Module augmentation instantiation requires creating the type of
        //     a module, which, in turn, can require checking for an export or
        //     property on the module (if export=) which, in turn, can fall
        //     back to the apparent type of the module — either
        //     globalObjectType or globalFunctionType — which wouldn't exist
        //     if we did module augmentations prior to finalizing the global
        //     types.
        for list in &augmentations {
            for &augmentation in list {
                let nodes = __program.nodes(augmentation.file_index());
                let parent = nodes[augmentation].parent.unwrap_or(NodeId::NONE);
                if ast::is_global_scope_augmentation(&nodes[parent]) {
                    self.merge_module_augmentation(augmentation);
                }
            }
        }
        self.add_undefined_to_globals_or_error_on_redeclaration();
        self.value_symbol_links
            .get(self.undefined_symbol)
            .resolved_type = Some(self.undefined_widening_type);
        self.value_symbol_links
            .get(self.arguments_symbol)
            .resolved_type = Some(self.get_global_type("IArguments", 0, true));
        self.value_symbol_links
            .get(self.unknown_symbol)
            .resolved_type = Some(self.error_type);
        let global_this_type =
            self.new_object_type(ObjectFlags::ANONYMOUS, Some(self.global_this_symbol));
        self.value_symbol_links
            .get(self.global_this_symbol)
            .resolved_type = Some(global_this_type);
        // Initialize special types
        self.global_array_type = self.get_global_type("Array", 1, true);
        self.global_object_type = self.get_global_type("Object", 0, true);
        self.global_function_type = self.get_global_type("Function", 0, true);
        self.global_callable_function_type =
            self.get_global_strict_function_type("CallableFunction");
        self.global_newable_function_type = self.get_global_strict_function_type("NewableFunction");
        self.global_string_type = self.get_global_type("String", 0, true);
        self.global_number_type = self.get_global_type("Number", 0, true);
        self.global_boolean_type = self.get_global_type("Boolean", 0, true);
        self.global_reg_exp_type = self.get_global_type("RegExp", 0, true);
        self.any_array_type = self.create_array_type(self.any_type);
        self.auto_array_type = self.create_array_type(self.auto_type);
        if self.auto_array_type == self.empty_object_type {
            // autoArrayType is used as a marker, so even if global Array type
            // is not defined, it needs to be a unique type
            self.auto_array_type = self.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        }
        self.global_readonly_array_type = self.get_global_type("ReadonlyArray", 1, false);
        if self.global_readonly_array_type == self.empty_generic_type {
            self.global_readonly_array_type = self.global_array_type;
        }
        self.any_readonly_array_type = self.create_type_from_generic_global_type(
            self.global_readonly_array_type,
            &[self.any_type],
        );
        self.global_this_type = self.get_global_type("ThisType", 1, false);
        // Now merge global ambient module declarations
        for &symbol in &ambient_module_symbols {
            self.merge_global_symbol(symbol);
        }
        self.merge_pattern_ambient_modules();
        // merge _nonglobal_ module augmentations. this needs to be done after
        // global symbol table is initialized to make sure that all ambient
        // modules are indexed
        for list in &augmentations {
            for &augmentation in list {
                let nodes = __program.nodes(augmentation.file_index());
                let parent = nodes[augmentation].parent.unwrap_or(NodeId::NONE);
                if !ast::is_global_scope_augmentation(&nodes[parent]) {
                    self.merge_module_augmentation(augmentation);
                }
            }
        }
        // `globalThisSymbol.exports` was snapshotted before the merges above;
        // Go shares `c.globals`'s map header so post-merge lookups (e.g.
        // `globalThis.IteratorObject`) see augmentation members. Re-sync here.
        self.symbol_arena.borrow_mut()[self.global_this_symbol.index()].exports =
            self.globals.borrow().clone();
        if std::env::var("TSC_FILE_TIME").is_ok() {
            eprintln!("[init-checker] {:?}", __init_t.elapsed());
        }
    }

    /// `(c *Checker) mergeGlobalSymbol` (checker.go).
    pub fn merge_global_symbol(&mut self, symbol: SymbolId) {
        let name = self.symbol_arena.borrow()[symbol.index()].name.clone();
        let global_symbol = self.globals.borrow().get(&name).copied();
        let merged = match global_symbol {
            Some(global_symbol) => self.merge_symbol(global_symbol, symbol, false),
            None => self.get_merged_symbol(symbol),
        };
        self.globals.borrow_mut().set(name, merged);
    }

    /// `(c *Checker) mergeSymbol` (checker.go) — symbol merging.
    pub fn merge_symbol(
        &mut self,
        target: SymbolId,
        source: SymbolId,
        unidirectional: bool,
    ) -> SymbolId {
        let mut target = target;
        let (target_flags, source_flags) = {
            let arena = self.symbol_arena.borrow();
            (arena[target.index()].flags, arena[source.index()].flags)
        };
        if !target_flags.intersects(crate::checker_b::get_excluded_symbol_flags(source_flags))
            || (source_flags | target_flags).intersects(ast::SymbolFlags::ASSIGNMENT)
        {
            if source == target {
                // This can happen when an export assigned namespace exports something also erroneously exported at the top level
                // See `declarationFileNoCrashOnExtraExportModifier` for an example
                return target;
            }
            if !target_flags.intersects(ast::SymbolFlags::TRANSIENT) {
                let resolved_target = self.resolve_symbol(target);
                if resolved_target == self.unknown_symbol {
                    return source;
                }
                let resolved_target_flags = self.sym(resolved_target).flags;
                if !resolved_target_flags
                    .intersects(crate::checker_b::get_excluded_symbol_flags(source_flags))
                    || (source_flags | resolved_target_flags)
                        .intersects(ast::SymbolFlags::ASSIGNMENT)
                {
                    target = self.clone_symbol(resolved_target);
                } else {
                    self.report_merge_symbol_error(target, source);
                    return source;
                }
            }
            let target_flags = self.sym(target).flags;
            // Javascript static-property-assignment declarations always merge, even though they are also values
            if source_flags.intersects(ast::SymbolFlags::VALUE_MODULE)
                && target_flags.intersects(ast::SymbolFlags::VALUE_MODULE)
                && target_flags.intersects(ast::SymbolFlags::CONST_ENUM_ONLY_MODULE)
                && !source_flags.intersects(ast::SymbolFlags::CONST_ENUM_ONLY_MODULE)
            {
                // reset flag when merging instantiated module into value module that has only const enums
                self.sym_mut(target)
                    .flags
                    .remove(ast::SymbolFlags::CONST_ENUM_ONLY_MODULE);
            }
            let mut source_flags = source_flags;
            let target_flags = self.sym(target).flags;
            if !target_flags.intersects(ast::SymbolFlags::CONST_ENUM_ONLY_MODULE) {
                source_flags.remove(ast::SymbolFlags::CONST_ENUM_ONLY_MODULE);
            }
            self.sym_mut(target).flags.insert(source_flags);
            let source_value_declaration = self.sym(source).value_declaration;
            if let Some(value_declaration) = source_value_declaration {
                let __program = self.program.clone().expect("program");
                let mut arena = self.symbol_arena.borrow_mut();
                tsc_binder::binder::set_value_declaration(
                    &mut arena,
                    target,
                    value_declaration,
                    &|id| {
                        let nodes = __program.nodes(id.file_index());
                        nodes[id].clone()
                    },
                );
            }
            let source_declarations = self.sym(source).declarations.clone();
            self.symbol_arena.borrow_mut()[target.index()]
                .declarations
                .extend(source_declarations);
            let source_members = self.sym(source).members.clone();
            if !source_members.is_empty() {
                let mut target_members = self.sym(target).members.clone();
                self.merge_symbol_table(&mut target_members, &source_members, unidirectional, None);
                self.symbol_arena.borrow_mut()[target.index()].members = target_members;
            }
            let source_exports = self.sym(source).exports.clone();
            if !source_exports.is_empty() {
                let mut target_exports = self.sym(target).exports.clone();
                self.merge_symbol_table(
                    &mut target_exports,
                    &source_exports,
                    unidirectional,
                    Some(target),
                );
                self.symbol_arena.borrow_mut()[target.index()].exports = target_exports;
            }
            if !unidirectional {
                self.record_merged_symbol(target, source);
            }
        } else if target_flags.intersects(ast::SymbolFlags::NAMESPACE_MODULE) {
            // Do not report an error when merging `var globalThis` with the built-in `globalThis`,
            // as we will already report a "Declaration name conflicts..." error, and this error
            // won't make much sense.
            if target != self.global_this_symbol {
                let first_declaration = crate::checker_b::get_first_declaration(self, source);
                let __program = self.program.clone().expect("program");
                let nodes =
                    __program.nodes(first_declaration.expect("first declaration").file_index());
                let name_node = ast::get_name_of_declaration(first_declaration, &nodes);
                let target_str = self.symbol_to_string(Some(target));
                self.error(
                    name_node,
                    &tsc_diagnostics::Cannot_augment_module_0_with_value_exports_because_it_resolves_to_a_non_module_entity,
                    &[target_str],
                );
            }
        } else {
            self.report_merge_symbol_error(target, source);
        }
        target
    }

    /// `(c *Checker) getMergedSymbol` (checker.go).
    ///
    /// PORT: `merged_symbols` maps a source `SymbolId` to its merged target
    /// (`recordMergedSymbol` inserts `source -> target`), folding Go's
    /// `MergeId` indirection into a direct lookup.
    pub fn get_merged_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        if symbol != SymbolId::NONE
            && let Some(&merged) = self.merged_symbols.get(&symbol)
        {
            return merged;
        }
        symbol
    }

    /// `(c *Checker) mergeModuleAugmentation` (checker.go).
    pub fn merge_module_augmentation(&mut self, module_name: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((module_name).file_index());
        let module_node = nodes[module_name]
            .parent
            .expect("module augmentation parent");
        let augmentation_symbol = nodes[module_node]
            .symbol()
            .expect("module augmentation symbol");
        if self.sym(augmentation_symbol).declarations.first().copied() != Some(module_node) {
            // this is a combined symbol for multiple augmentations within the same file.
            // its symbol already has accumulated information for all declarations
            // so we need to add it just once - do the work only for first declaration
            return;
        }
        if ast::is_global_scope_augmentation(&nodes[module_node]) {
            let augmentation_exports = self.sym(augmentation_symbol).exports.clone();
            let mut globals = self.globals.borrow().clone();
            self.merge_symbol_table(&mut globals, &augmentation_exports, false, None);
            // Go shares `globalThisSymbol.Exports` with `c.globals` (same
            // map header), so merging `namespace globalThis { ... }` into
            // `globals["globalThis"]` writes the namespace's members into
            // `globals` itself. `Symbol.exports` is a value field here —
            // fold the merged symbol's exports back so augmented
            // `globalThis` members become true globals.
            if augmentation_exports.get("globalThis").is_some()
                && let Some(&merged_global_this) = globals.get("globalThis")
            {
                let global_this_exports = self.sym(merged_global_this).exports.clone();
                self.merge_symbol_table(&mut globals, &global_this_exports, false, None);
            }
            *self.globals.borrow_mut() = globals;
        } else {
            // find a module that about to be augmented
            // do not validate names of augmentations that are defined in ambient context
            let module_not_found_error = if !nodes[module_node]
                .parent
                .map(|p| nodes[p].flags.intersects(ast::NodeFlags::AMBIENT))
                .unwrap_or(false)
            {
                Some(&tsc_diagnostics::Invalid_module_name_in_augmentation_module_0_cannot_be_found)
            } else {
                None
            };
            // We ban import attributes on module augmentation declarations.
            let main_module = self.resolve_external_module_name_worker(
                module_name,
                Some(module_name),
                module_not_found_error,
                false, /*ignoreErrors*/
                true,  /*isForAugmentation*/
                None,  /*importAttributesType*/
            );
            let Some(main_module) = main_module else {
                return;
            };
            // obtain item referenced by 'export='
            let main_module = self
                .resolve_external_module_symbol(Some(main_module), false)
                .expect("resolved external module symbol");
            if self
                .sym(main_module)
                .flags
                .intersects(ast::SymbolFlags::NAMESPACE)
            {
                // If we're merging an augmentation to a pattern ambient module, we want to
                // perform the merge unidirectionally from the augmentation ('a.foo') to
                // the pattern ('*.foo'), so that 'getMergedSymbol()' on a.foo gives you
                // all the exports both from the pattern and from the augmentation, but
                // 'getMergedSymbol()' on *.foo only gives you exports from *.foo.
                let is_pattern_target = self.pattern_ambient_modules.clone().iter().any(|module| {
                    module
                        .symbol
                        .map(|s| Some(main_module) == Some(self.get_merged_symbol(s)))
                        .unwrap_or(false)
                });
                if is_pattern_target {
                    let merged = self.merge_symbol(
                        augmentation_symbol,
                        main_module,
                        true, /*unidirectional*/
                    );
                    // moduleName will be a StringLiteral since this is not `declare global`.
                    let text = nodes[module_name].text(&nodes).into_owned();
                    self.pattern_ambient_module_augmentations
                        .set(text.clone(), merged);
                    self.pattern_ambient_module_augmentation_targets
                        .set(text, main_module);
                } else {
                    let main_module_exports_star = self
                        .sym(main_module)
                        .exports
                        .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_STAR)
                        .copied();
                    let augmentation_exports = self.sym(augmentation_symbol).exports.clone();
                    if main_module_exports_star.is_some() && !augmentation_exports.is_empty() {
                        // We may need to merge the module augmentation's exports into the target symbols of the resolved exports
                        let resolved_exports = self.get_resolved_members_or_exports_of_symbol(
                            main_module,
                            crate::types::MembersOrExportsResolutionKind::ResolvedExports,
                        );
                        let target_exports = self.sym(main_module).exports.clone();
                        for (key, &value) in augmentation_exports.entries() {
                            if resolved_exports.get(key).is_some()
                                && target_exports.get(key).is_none()
                            {
                                self.merge_symbol(
                                    *resolved_exports.get(key).unwrap(),
                                    value,
                                    false, /*unidirectional*/
                                );
                            }
                        }
                    }
                    self.merge_symbol(
                        main_module,
                        augmentation_symbol,
                        false, /*unidirectional*/
                    );
                }
            } else {
                // moduleName will be a StringLiteral since this is not `declare global`.
                let text = nodes[module_name].text(&nodes).into_owned();
                self.error(
                    Some(module_name),
                    &tsc_diagnostics::Cannot_augment_module_0_because_it_resolves_to_a_non_module_entity,
                    &[text],
                );
            }
        }
    }

    /// `(c *Checker) mergePatternAmbientModules` (checker.go).
    pub fn merge_pattern_ambient_modules(&mut self) {
        let mut groups_by_pattern: FxHashMap<String, Vec<usize>> = FxHashMap::default();
        let mut grouped: Vec<ast::PatternAmbientModule> =
            Vec::with_capacity(self.pattern_ambient_modules.len());
        let pattern_ambient_modules = self.pattern_ambient_modules.clone();
        for module in &pattern_ambient_modules {
            let Some(module_symbol) = module.symbol else {
                continue;
            };
            let attributes_type = self.get_type_of_module_import_attributes(module_symbol);
            let mut group_index: i32 = -1;
            let pattern_text = module.pattern.text.clone();
            for &index in groups_by_pattern.get(&pattern_text).into_iter().flatten() {
                let other_symbol = grouped[index]
                    .symbol
                    .expect("pattern ambient module symbol");
                let other_attributes = self.get_type_of_module_import_attributes(other_symbol);
                if self.is_type_identical_to(attributes_type, other_attributes) {
                    group_index = index as i32;
                    break;
                }
            }
            if group_index == -1 {
                groups_by_pattern
                    .entry(pattern_text.clone())
                    .or_default()
                    .push(grouped.len());
                grouped.push(ast::PatternAmbientModule {
                    pattern: module.pattern.clone(),
                    symbol: module.symbol,
                });
            } else {
                let merged = self.merge_symbol(
                    grouped[group_index as usize].symbol.unwrap(),
                    module_symbol,
                    false, /*unidirectional*/
                );
                grouped[group_index as usize].symbol = Some(merged);
            }
        }
        for module in &pattern_ambient_modules {
            if let Some(module_symbol) = module.symbol {
                let name = self.sym(module_symbol).name.clone();
                if self.globals.borrow().get(&name).is_some() {
                    let merged = self.get_merged_symbol(module_symbol);
                    self.globals.borrow_mut().set(name, merged);
                }
            }
        }
        self.pattern_ambient_modules = grouped;
    }

    /// `(c *Checker) addUndefinedToGlobalsOrErrorOnRedeclaration`
    /// (checker.go).
    pub fn add_undefined_to_globals_or_error_on_redeclaration(&mut self) {
        let name = self.symbol_arena.borrow()[self.undefined_symbol.index()]
            .name
            .clone();
        let target_symbol = self.globals.borrow().get(&name).copied();
        if let Some(target_symbol) = target_symbol {
            let declarations = self.symbol_arena.borrow()[target_symbol.index()]
                .declarations
                .clone();
            for declaration in declarations {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((declaration).file_index());
                if !ast::is_type_declaration(declaration, &nodes) {
                    let diagnostic = self.new_diagnostic_for_node(
                        Some(declaration),
                        &tsc_diagnostics::Declaration_name_conflicts_with_built_in_global_identifier_0,
                        &[name.clone()],
                    );
                    self.diagnostics.add(&diagnostic);
                }
            }
        } else {
            self.globals.borrow_mut().set(name, self.undefined_symbol);
        }
    }

    /// `(c *Checker) createNameResolver` — PORT(deferred): the Go
    /// `binder.NameResolver` hooks (`getSymbolOfDeclaration`, `error`,
    /// `lookup`, `symbolReferenced`, scope-change caches, failed/resolved
    /// callbacks) all need `&mut Checker`, but `binder::NameResolver`'s hook
    /// signatures don't take it — wave-2 either extends the hooks or inlines
    /// the resolver. The returned thunk defers to `resolve_name_via_binder`
    /// at call time so `new_checker` completes.
    pub fn create_name_resolver(&self) -> Rc<NameResolverThunk<'static>> {
        Rc::new(
            |c: &mut Checker, location, name, meaning, message, is_use, exclude_globals| {
                c.resolve_name_via_binder(location, name, meaning, message, is_use, exclude_globals)
            },
        )
    }

    /// `(c *Checker) createNameResolverForSuggestion` — PORT(deferred): same
    /// hook limitation as `create_name_resolver`.
    pub fn create_name_resolver_for_suggestion(&self) -> Rc<NameResolverThunk<'static>> {
        Rc::new(
            |c: &mut Checker, location, name, meaning, message, is_use, exclude_globals| {
                c.resolve_name_for_suggestion_via_binder(
                    location,
                    name,
                    meaning,
                    message,
                    is_use,
                    exclude_globals,
                )
            },
        )
    }

    /// `binder::NameResolver::Resolve` wired for `resolve_name` —
    /// the `Checker` is installed as the resolver's `NameResolverHost` so Go's
    /// `c.*` hooks route to the real methods.
    #[allow(clippy::too_many_arguments)]
    pub fn resolve_name_via_binder(
        &mut self,
        location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
        name_not_found_message: Option<&'static tsc_diagnostics::Message>,
        is_use: bool,
        exclude_globals: bool,
    ) -> Option<SymbolId> {
        self.resolve_name_via_binder_live(
            location,
            name,
            meaning,
            name_not_found_message,
            is_use,
            exclude_globals,
            None,
        )
    }

    /// `resolve_name_via_binder` with a live-arena override — used when the
    /// caller holds the file's checked-out working buffer (node-builder /
    /// emit paths) so name resolution sees synthetic nodes minted
    /// mid-operation, matching Go's shared-slice reads.
    pub fn resolve_name_via_binder_live(
        &mut self,
        location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
        name_not_found_message: Option<&'static tsc_diagnostics::Message>,
        is_use: bool,
        exclude_globals: bool,
        live_nodes: Option<&[ast::Node]>,
    ) -> Option<SymbolId> {
        self.resolve_name_with_binder(
            location,
            name,
            meaning,
            name_not_found_message,
            is_use,
            exclude_globals,
            false,
            live_nodes,
        )
    }

    /// `binder::NameResolver::Resolve` (suggestion variant).
    #[allow(clippy::too_many_arguments)]
    pub fn resolve_name_for_suggestion_via_binder(
        &mut self,
        location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
        name_not_found_message: Option<&'static tsc_diagnostics::Message>,
        is_use: bool,
        exclude_globals: bool,
    ) -> Option<SymbolId> {
        self.resolve_name_with_binder(
            location,
            name,
            meaning,
            name_not_found_message,
            is_use,
            exclude_globals,
            true,
            None,
        )
    }

    /// Shared body for `resolve_name_via_binder` /
    /// `resolve_name_for_suggestion_via_binder`: builds the
    /// `binder::NameResolver` Go stores at construction time, on the stack —
    /// the `host` wiring makes Go's hook calls delegate to `self`.
    /// `live_nodes` is the caller's checked-out working buffer for the arena
    /// being resolved in — see [`crate::printer_util::arena_view`].
    #[allow(clippy::too_many_arguments)]
    fn resolve_name_with_binder(
        &mut self,
        location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
        name_not_found_message: Option<&'static tsc_diagnostics::Message>,
        is_use: bool,
        exclude_globals: bool,
        for_suggestion: bool,
        live_nodes: Option<&[ast::Node]>,
    ) -> Option<SymbolId> {
        // The resolver walks `location`'s ancestors within its own file arena.
        // With no location (global lookups) the arena is only read for the
        // error paths, which are guarded on `original_location.is_some()`.
        // PORT(borrowck): `nodes` must stay live across `resolver.resolve`,
        // which borrows `&mut self` through `host` — borrow the arena from a
        // cloned program handle instead of `*self`.
        let __program = self.program.clone().expect("program");
        let nodes = match location {
            Some(loc) => crate::printer_util::arena_view(
                &__program,
                live_nodes.unwrap_or(&[]),
                loc.file_index(),
            ),
            // PORT: Go never reads `c.files` for a nil location (global
            // lookups walk `globals` only), so an empty program yields an
            // empty arena view instead of Go's `files[0]` index panic.
            None => crate::printer_util::ArenaView::Snapshot(
                self.files
                    .first()
                    .map(|f| __program.nodes(f.file_index()))
                    .unwrap_or_default(),
            ),
        };
        let symbol_arena = self.symbol_arena.clone();
        let compiler_options = self.compiler_options.clone();
        let globals = self.globals.clone();
        let arguments_symbol = if self.arguments_symbol == SymbolId::NONE {
            None
        } else {
            Some(self.arguments_symbol)
        };
        let require_symbol = if self.require_symbol == SymbolId::NONE {
            None
        } else {
            Some(self.require_symbol)
        };
        let mut resolver = tsc_binder::nameresolver::NameResolver {
            host: Some(self),
            for_suggestion,
            compiler_options,
            globals,
            arguments_symbol,
            require_symbol,
            get_symbol_of_declaration_hook: None,
            error_hook: None,
            lookup_hook: None,
            symbol_referenced: None,
            set_requires_scope_change_cache: None,
            get_requires_scope_change_cache: None,
            on_property_with_invalid_initializer: None,
            on_failed_to_resolve_symbol: None,
            on_successfully_resolved_symbol: None,
        };
        resolver.resolve(
            location,
            name,
            meaning,
            name_not_found_message,
            is_use,
            exclude_globals,
            &nodes,
            symbol_arena.as_ref(),
        )
    }

    // The `createNameResolver`/`createNameResolverForSuggestion` hook table —
    // Go stores `binder.NameResolver` values whose `func` fields point back
    // into `*Checker`; the `NameResolverHost` trait is the port's mechanism
    // for that (self-referential closures can't be stored on the struct).
    pub(crate) fn as_name_resolver_host(
        &mut self,
    ) -> &mut dyn tsc_binder::nameresolver::NameResolverHost {
        self
    }

    /// `(c *Checker) evaluateEntity` (checker.go).
    pub fn evaluate_entity(
        &mut self,
        expr: NodeId,
        location: Option<NodeId>,
        _nodes: &[ast::Node],
    ) -> evaluator::Result {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((expr).file_index());
        match nodes[expr].kind {
            ast::Kind::Identifier | ast::Kind::PropertyAccessExpression => {
                let symbol = self.resolve_entity_name(
                    Some(expr),
                    ast::SymbolFlags::VALUE,
                    true,  /*ignoreErrors*/
                    false, /*dontResolveAlias*/
                    None,
                );
                let Some(symbol) = symbol else {
                    return evaluator::new_result(None, false, false, false);
                };
                if nodes[expr].kind == ast::Kind::Identifier {
                    let text = nodes[expr].text(&nodes).into_owned();
                    if ast::is_infinity_or_na_n_string(&text)
                        && Some(symbol)
                            == self.get_global_symbol(
                                &text,
                                ast::SymbolFlags::VALUE,
                                None, /*diagnostic*/
                            )
                    {
                        // Technically we resolved a global lib file here, but the decision to treat this as numeric
                        // is more predicated on the fact that the single-file resolution *didn't* resolve to a
                        // different meaning of `Infinity` or `NaN`. Transpilers handle this no problem.
                        return evaluator::new_result(
                            Some(evaluator::Value::Number(tsc_jsnum::from_string(&text))),
                            false,
                            false,
                            false,
                        );
                    }
                }
                if self
                    .sym(symbol)
                    .flags
                    .intersects(ast::SymbolFlags::ENUM_MEMBER)
                {
                    if let Some(location) = location {
                        return self.evaluate_enum_member(expr, symbol, location);
                    }
                    let declaration = self.sym(symbol).value_declaration;
                    return declaration
                        .map(|d| self.get_enum_member_value(d))
                        .unwrap_or_else(|| evaluator::new_result(None, false, false, false));
                }
                if self.is_constant_variable(symbol) {
                    let declaration = self.sym(symbol).value_declaration;
                    if let Some(declaration) = declaration {
                        let __program = self.program.clone().expect("program");
                        let decl_nodes = __program.nodes((declaration).file_index());
                        if ast::is_variable_declaration(&decl_nodes[declaration])
                            && decl_nodes[declaration].type_().is_none()
                            && decl_nodes[declaration]
                                .as_variable_declaration()
                                .initializer
                                .is_some()
                            && (location.is_none()
                                || declaration != location.unwrap()
                                    && self.is_block_scoped_name_declared_before_use(
                                        declaration,
                                        location.unwrap(),
                                    ))
                        {
                            let initializer = decl_nodes[declaration]
                                .as_variable_declaration()
                                .initializer
                                .unwrap();
                            let result =
                                self.evaluate_call(initializer, Some(declaration), &decl_nodes);
                            if let Some(location) = location {
                                let loc_file = ast::get_source_file_of_node(Some(location), &nodes);
                                let decl_file =
                                    ast::get_source_file_of_node(Some(declaration), &decl_nodes);
                                if loc_file != decl_file {
                                    return evaluator::new_result(result.value, false, true, true);
                                }
                            }
                            return evaluator::new_result(
                                result.value,
                                result.is_syntactically_string,
                                result.resolved_other_files,
                                true, /*hasExternalReferences*/
                            );
                        }
                    }
                }
                evaluator::new_result(None, false, false, false)
            }
            ast::Kind::ElementAccessExpression => {
                let root = nodes[expr].as_element_access_expression().expression;
                let argument = nodes[expr]
                    .as_element_access_expression()
                    .argument_expression;
                if let (Some(root), Some(argument)) = (root, argument) {
                    if ast::is_entity_name_expression(&nodes[root], &nodes)
                        && ast::is_string_literal_like(&nodes[argument])
                    {
                        let root_symbol = self.resolve_entity_name(
                            Some(root),
                            ast::SymbolFlags::VALUE,
                            true,  /*ignoreErrors*/
                            false, /*dontResolveAlias*/
                            None,
                        );
                        if let Some(root_symbol) = root_symbol
                            && self
                                .sym(root_symbol)
                                .flags
                                .intersects(ast::SymbolFlags::ENUM)
                        {
                            let name = nodes[argument].text(&nodes).into_owned();
                            let member = self.sym(root_symbol).exports.get(&name).copied();
                            if let Some(member) = member {
                                if let Some(location) = location {
                                    return self.evaluate_enum_member(expr, member, location);
                                }
                                let declaration = self.sym(member).value_declaration;
                                return declaration
                                    .map(|d| self.get_enum_member_value(d))
                                    .unwrap_or_else(|| {
                                        evaluator::new_result(None, false, false, false)
                                    });
                            }
                        }
                    }
                }
                evaluator::new_result(None, false, false, false)
            }
            kind => panic!("Unhandled case in evaluateEntity: {kind:?}"),
        }
    }

    /// `program.nodes(...)` — the per-file node arena for `NodeId` derefs
    /// (the `Program` trait's port-added accessor).
    ///
    /// Returns a `Ref` over the shared `Rc<ArenaCell>` arena. The
    /// guard borrows `*self` — where the arena must stay live across a
    /// `&mut self` call, clone the program handle into a local first:
    /// `let program = self.program.clone().unwrap(); let nodes = program.nodes(i);`.
    pub fn program_nodes(&self, node: NodeId) -> std::rc::Rc<Vec<ast::Node>> {
        self.program
            .as_ref()
            .expect("program")
            .nodes(node.file_index())
    }

    /// `program_nodes` that falls back to the caller's checked-out working
    /// buffer when `node`'s arena is the buffer under construction — see
    /// [`crate::printer_util::arena_view`].
    pub fn program_nodes_live<'x>(
        &self,
        node: NodeId,
        live: &'x [ast::Node],
    ) -> crate::printer_util::ArenaView<'x> {
        crate::printer_util::resolve_arena_for(
            self.program.as_ref().expect("program"),
            live,
            node,
        )
    }

    /// `program.nodes_handle(...)` — the `Rc<ArenaCell>` handle for the
    /// file containing `node` — for long-lived arena aliases (`FlowState`).
    pub fn program_nodes_handle(&self, node: NodeId) -> Rc<tsc_ast::ast::ArenaCell> {
        self.program
            .as_ref()
            .expect("program")
            .nodes_handle(node.file_index())
    }

    /// `program.nodes_mut(...)` — mutable arena access for synthetic-node
    /// creation (Go mutates the shared `*ast.Node` graph freely). Returns a
    /// copy-on-write `ArenaMut` — see `checker_types::Program::nodes_mut`.
    pub fn program_nodes_mut(&self, file_index: u32) -> tsc_ast::ast::ArenaMut {
        self.program
            .as_ref()
            .expect("program")
            .nodes_mut(file_index)
    }

    /// `self.types.clone()` — clones the `Arc`-backed arena handle. The
    /// returned arena owns its `Arc`, so `get`/`get_mut` guards borrow the
    /// clone (a temporary or local) rather than `*self`. This breaks the
    /// `self.types_handle().get(..)`-across-`&mut self`-call borrow conflict; Go has
    /// no such constraint. Guards still share the underlying `RwLock` —
    /// do not hold a read guard across `get_mut`/`alloc` on the same arena.
    /// PORT: `pub` so `tsc-testrunner`'s union-ordering check can take an
    /// arena handle without borrowing the `Checker` across calls.
    pub fn types_handle(&self) -> crate::types::TypeArena {
        self.types.clone()
    }

    /// Writes `node` back into the file arena that owns `id`.
    pub fn set_program_node(&self, id: NodeId, node: ast::Node) {
        self.program_nodes_mut(id.file_index())[id] = node;
    }

    /// `(c *Checker) callLikeExpressionMayHaveTypeArguments`
    /// (utilities.go:1132).
    pub fn call_like_expression_may_have_type_arguments(&self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        ast::is_call_or_new_expression(&nodes[node])
            || ast::is_tagged_template_expression(&nodes[node])
            || ast::is_jsx_opening_like_element(&nodes[node])
    }

    /// `NewDiagnosticForNode` (checker/utilities.go). Needs the per-file
    /// node arena, so it's a `Checker` method in the port.
    pub fn new_diagnostic_for_node<T: std::fmt::Display>(
        &self,
        node: Option<NodeId>,
        message: &'static tsc_diagnostics::Message,
        args: &[T],
    ) -> ast::diagnostic::DiagnosticRef {
        let mut file = None;
        let mut loc = tsc_core::text::TextRange::default();
        if let Some(node) = node {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            if let Some(source_file) = ast::get_source_file_of_node(Some(node), &nodes) {
                let sf = nodes[source_file].as_source_file();
                loc = tsc_scanner::scanner::get_error_range_for_node(sf, node, &nodes);
                file = Some(ast::diagnostic::DiagnosticFile::from_node(
                    source_file,
                    &nodes,
                ));
            }
        }
        ast::diagnostic::new_diagnostic(file, loc, message, args)
    }

    /// `ast.SymbolName(symbol)` — the port's `symbol::symbol_name` needs
    /// the value declaration's node arena.
    pub fn symbol_display_name(&self, symbol: SymbolId) -> String {
        let arena = self.symbol_arena.borrow();
        let sym = &arena[symbol.index()];
        match sym.value_declaration {
            Some(d) => {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((d).file_index());
                ast::symbol::symbol_name(sym, &nodes).into_owned()
            }
            None => sym.name.clone(),
        }
    }

    /// `(c *Checker) compareSymbolsWorker` (utilities.go).
    pub fn compare_symbols_worker(&self, s1: Option<SymbolId>, s2: Option<SymbolId>) -> i32 {
        if s1 == s2 {
            return 0;
        }
        let Some(s1) = s1 else { return 1 };
        let Some(s2) = s2 else { return -1 };
        let (d1, d2, n1, n2) = {
            let arena = self.symbol_arena.borrow();
            let s1 = &arena[s1.index()];
            let s2 = &arena[s2.index()];
            (
                s1.declarations.clone(),
                s2.declarations.clone(),
                s1.name.clone(),
                s2.name.clone(),
            )
        };
        if !d1.is_empty() && !d2.is_empty() {
            let r = self.compare_nodes(Some(d1[0]), Some(d2[0]));
            if r != 0 {
                return r;
            }
        } else if !d1.is_empty() {
            return -1;
        } else if !d2.is_empty() {
            return 1;
        }
        let r = n1.cmp(&n2) as i32;
        if r != 0 {
            return r;
        }
        // Fall back to symbol IDs — a last resort for symbols with no
        // declaration and duplicate names.
        s1.0 as i32 - s2.0 as i32
    }

    /// `(c *Checker) compareSymbolChainsWorker` (symbolaccessibility.go).
    pub fn compare_symbol_chains_worker(&self, a: &[SymbolId], b: &[SymbolId]) -> i32 {
        let chain_len = a.len() as i32 - b.len() as i32;
        if chain_len != 0 {
            return chain_len;
        }
        for (&a, &b) in a.iter().zip(b.iter()) {
            let comparison = self.compare_symbols_worker(Some(a), Some(b));
            if comparison != 0 {
                return comparison;
            }
        }
        0
    }

    /// `(c *Checker) compareNodes` (utilities.go) — order by containing file
    /// index, then source position.
    pub fn compare_nodes(&self, n1: Option<NodeId>, n2: Option<NodeId>) -> i32 {
        if n1 == n2 {
            return 0;
        }
        let Some(n1) = n1 else { return 1 };
        let Some(n2) = n2 else { return -1 };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((n1).file_index());
        let s1 = ast::get_source_file_of_node(Some(n1), &nodes);
        let __program = self.program.clone().expect("program");
        let nodes2 = __program.nodes((n2).file_index());
        let s2 = ast::get_source_file_of_node(Some(n2), &nodes2);
        if s1 != s2 {
            let f1 = s1
                .and_then(|s| self.file_index_map.get(&s).copied())
                .unwrap_or(0) as i32;
            let f2 = s2
                .and_then(|s| self.file_index_map.get(&s).copied())
                .unwrap_or(0) as i32;
            // Order by index of file in the containing program
            return f1 - f2;
        }
        // In the same file, order by source position
        nodes[n1].pos() - nodes[n2].pos()
    }

    /// `(c *Checker) symbolReferenced` (checker.go).
    pub fn symbol_referenced(&mut self, symbol: SymbolId, meaning: ast::SymbolFlags) {
        self.symbol_reference_links
            .get(symbol)
            .reference_kinds
            .insert(meaning);
    }

    /// `(c *Checker) getRequiresScopeChangeCache` (checker.go).
    /// PORT: `&mut self` — `LinkStore::get` inserts the default entry like
    /// Go's map access.
    pub fn get_requires_scope_change_cache(
        &mut self,
        node: NodeId,
    ) -> tsc_core::tristate::Tristate {
        self.node_links.get(node).declaration_requires_scope_change
    }

    /// `(c *Checker) setRequiresScopeChangeCache` (checker.go).
    pub fn set_requires_scope_change_cache(
        &mut self,
        node: NodeId,
        value: tsc_core::tristate::Tristate,
    ) {
        self.node_links.get(node).declaration_requires_scope_change = value;
    }

    // ======== Type/symbol constructors ========

    /// `(c *Checker) newSymbol` (checker.go).
    pub fn new_symbol(&mut self, flags: ast::SymbolFlags, name: &str) -> SymbolId {
        self.symbol_count += 1;
        let mut arena = self.symbol_arena.borrow_mut();
        let id = SymbolId(arena.len() as u32);
        arena.push(ast::Symbol {
            flags: flags | ast::SymbolFlags::TRANSIENT,
            name: name.to_string(),
            ..Default::default()
        });
        id
    }

    /// `(c *Checker) newSymbolEx` (checker.go).
    pub fn new_symbol_ex(
        &mut self,
        flags: ast::SymbolFlags,
        name: &str,
        check_flags: ast::checkflags::CheckFlags,
    ) -> SymbolId {
        let result = self.new_symbol(flags, name);
        self.symbol_arena.borrow_mut()[result.index()].check_flags = check_flags;
        result
    }

    /// `(c *Checker) newParameter` (checker.go).
    pub fn new_parameter(&mut self, name: &str, t: TypeId) -> SymbolId {
        let symbol = self.new_symbol(ast::SymbolFlags::FUNCTION_SCOPED_VARIABLE, name);
        self.value_symbol_links.get(symbol).resolved_type = Some(t);
        symbol
    }

    /// `(c *Checker) newProperty` (checker.go).
    pub fn new_property(&mut self, name: &str, t: TypeId) -> SymbolId {
        let symbol = self.new_symbol(ast::SymbolFlags::PROPERTY, name);
        self.value_symbol_links.get(symbol).resolved_type = Some(t);
        symbol
    }

    /// `(c *Checker) newType` (checker.go).
    pub fn new_type(
        &mut self,
        flags: TypeFlags,
        object_flags: ObjectFlags,
        data: TypeData,
    ) -> TypeId {
        self.type_count += 1;
        let __arena_id = self.types.clone();
        let id = __arena_id.alloc(Type {
            flags,
            object_flags: object_flags
                & !(ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES_COMPUTED
                    | ObjectFlags::COULD_CONTAIN_TYPE_VARIABLES
                    | ObjectFlags::MEMBERS_RESOLVED),
            // `t.id = TypeId(c.TypeCount)` — Go ids are 1-based and equal the
            // arena index (element 0 is a tombstone).
            id: TypeId::NONE,
            checker_shard: self.id as u16,
            data,
            ..Default::default()
        });
        self.types_handle().get_mut(id).id = id;
        self.trace_record_type(id);
        id
    }

    /// `(c *Checker) newIntrinsicType` (checker.go).
    pub fn new_intrinsic_type(&mut self, flags: TypeFlags, intrinsic_name: &str) -> TypeId {
        self.new_intrinsic_type_ex(flags, intrinsic_name, ObjectFlags::NONE)
    }

    /// `(c *Checker) newIntrinsicTypeEx` (checker.go).
    pub fn new_intrinsic_type_ex(
        &mut self,
        flags: TypeFlags,
        intrinsic_name: &str,
        object_flags: ObjectFlags,
    ) -> TypeId {
        self.new_type(
            flags,
            object_flags,
            TypeData::Intrinsic(crate::types::IntrinsicType {
                intrinsic_name: intrinsic_name.to_string(),
            }),
        )
    }

    /// `(c *Checker) createWideningType` (checker.go).
    pub fn create_widening_type(&mut self, non_widening_type: TypeId) -> TypeId {
        if self.strict_null_checks {
            return non_widening_type;
        }
        let (flags, intrinsic_name) = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(non_widening_type);
            (ty.flags, ty.as_intrinsic_type().intrinsic_name.clone())
        };
        let t = self.new_intrinsic_type(flags, &intrinsic_name);
        self.types_handle()
            .get_mut(t)
            .object_flags
            .insert(ObjectFlags::CONTAINS_WIDENING_TYPE);
        t
    }

    /// `(c *Checker) createUnknownUnionType` (checker.go).
    pub fn create_unknown_union_type(&mut self) -> TypeId {
        if self.strict_null_checks {
            return self.get_union_type(&[
                self.undefined_type,
                self.null_type,
                self.unknown_empty_object_type,
            ]);
        }
        self.unknown_type
    }

    /// `(c *Checker) newLiteralType` (checker.go).
    pub fn new_literal_type(
        &mut self,
        flags: TypeFlags,
        value: Option<evaluator::Value>,
        regular_type: Option<TypeId>,
    ) -> TypeId {
        let t = self.new_type(
            flags,
            ObjectFlags::NONE,
            TypeData::Literal(crate::types::LiteralType {
                value,
                fresh_type: None,
                regular_type: None,
            }),
        );
        let regular = regular_type.unwrap_or(t);
        if let TypeData::Literal(d) = &mut self.types_handle().get_mut(t).data {
            d.regular_type = Some(regular);
        }
        t
    }

    /// `(c *Checker) newUniqueESSymbolType` (checker.go).
    pub fn new_unique_es_symbol_type(&mut self, symbol: Option<SymbolId>, name: &str) -> TypeId {
        let t = self.new_type(
            TypeFlags::UNIQUE_ES_SYMBOL,
            ObjectFlags::NONE,
            TypeData::UniqueESSymbol(crate::types::UniqueESSymbolType {
                name: name.to_string(),
            }),
        );
        self.types_handle().get_mut(t).symbol = symbol;
        t
    }

    /// `(c *Checker) newObjectType` (checker.go).
    pub fn new_object_type(
        &mut self,
        object_flags: ObjectFlags,
        symbol: Option<SymbolId>,
    ) -> TypeId {
        let data = if object_flags.intersects(ObjectFlags::CLASS_OR_INTERFACE) {
            TypeData::InterfaceType(crate::types::InterfaceType::default())
        } else if object_flags.intersects(ObjectFlags::TUPLE) {
            TypeData::Tuple(crate::types::TupleType::default())
        } else if object_flags.intersects(ObjectFlags::REFERENCE) {
            TypeData::TypeReference(crate::types::TypeReference::default())
        } else if object_flags.intersects(ObjectFlags::MAPPED) {
            TypeData::Mapped(crate::types::MappedType::default())
        } else if object_flags.intersects(ObjectFlags::REVERSE_MAPPED) {
            TypeData::ReverseMapped(crate::types::ReverseMappedType::default())
        } else if object_flags.intersects(ObjectFlags::EVOLVING_ARRAY) {
            TypeData::EvolvingArray(crate::types::EvolvingArrayType::default())
        } else if object_flags.intersects(ObjectFlags::INSTANTIATION_EXPRESSION_TYPE) {
            TypeData::InstantiationExpression(crate::types::InstantiationExpressionType::default())
        } else if object_flags.intersects(ObjectFlags::ANONYMOUS) {
            TypeData::Object(crate::types::ObjectType::default())
        } else {
            panic!("Unhandled case in newObjectType")
        };
        let t = self.new_type(TypeFlags::OBJECT, object_flags, data);
        self.types_handle().get_mut(t).symbol = symbol;
        t
    }

    /// `(c *Checker) newAnonymousType` (checker.go). `members` is the
    /// SymbolTable value (empty for Go's nil).
    pub fn new_anonymous_type(
        &mut self,
        symbol: Option<SymbolId>,
        members: SymbolTable,
        call_signatures: &[SignatureId],
        construct_signatures: &[SignatureId],
        index_infos: &[IndexInfoId],
    ) -> TypeId {
        let t = self.new_object_type(ObjectFlags::ANONYMOUS, symbol);
        self.set_structured_type_members(
            t,
            members,
            call_signatures,
            construct_signatures,
            index_infos,
        );
        t
    }

    /// `(c *Checker) setStructuredTypeMembers` (checker.go). `indexInfos
    /// []*IndexInfo` → `&[IndexInfoId]` — cloned out of `index_info_arena`
    /// into the inline `Vec<IndexInfo>` (the port's `*IndexInfo` storage
    /// choice).
    pub fn set_structured_type_members(
        &mut self,
        t: TypeId,
        members: SymbolTable,
        call_signatures: &[SignatureId],
        construct_signatures: &[SignatureId],
        index_infos: &[IndexInfoId],
    ) {
        self.types_handle()
            .get_mut(t)
            .object_flags
            .insert(ObjectFlags::MEMBERS_RESOLVED);
        let __arena_symbol = self.types.clone();
        let symbol = __arena_symbol.get(t).symbol;
        let properties = self.get_named_members(&members, symbol);
        let (signatures, call_signature_count) = if !call_signatures.is_empty() {
            let mut sigs = call_signatures.to_vec();
            sigs.extend_from_slice(construct_signatures);
            (sigs, call_signatures.len())
        } else if !construct_signatures.is_empty() {
            (construct_signatures.to_vec(), 0)
        } else {
            (Vec::new(), 0)
        };
        let index_infos: Vec<IndexInfo> = index_infos
            .iter()
            .map(|&id| self.index_info_arena.get(id).clone())
            .collect();
        if let Some(data) = self.types_handle().get_mut(t).data.as_structured_type_mut() {
            data.members = members;
            data.properties = properties;
            data.signatures = signatures;
            data.call_signature_count = call_signature_count;
            data.index_infos = index_infos;
        }
    }

    /// `(c *Checker) getNamedMembers` (checker.go) — PORT(partial): the
    /// empty-table fast path is faithful; the class/interface member
    /// ordering logic lands with checker.go.
    pub fn get_named_members(
        &mut self,
        members: &SymbolTable,
        container: Option<SymbolId>,
    ) -> Vec<SymbolId> {
        crate::checker_c::get_named_members(self, members, container)
    }

    /// `(c *Checker) newTypeParameter` (checker.go).
    pub fn new_type_parameter(&mut self, symbol: Option<SymbolId>) -> TypeId {
        let t = self.new_type(
            TypeFlags::TYPE_PARAMETER,
            ObjectFlags::NONE,
            TypeData::TypeParameter(TypeParameter::default()),
        );
        self.types_handle().get_mut(t).symbol = symbol;
        t
    }

    /// `(c *Checker) getPropagatingFlagsOfTypes` (checker.go).
    pub fn get_propagating_flags_of_types(
        &self,
        types: &[TypeId],
        exclude_kinds: TypeFlags,
    ) -> ObjectFlags {
        let mut result = ObjectFlags::NONE;
        for &t in types {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(t);
            if !ty.flags.intersects(exclude_kinds) {
                result |= ty.object_flags;
            }
        }
        result & ObjectFlags::PROPAGATING_FLAGS
    }

    /// `(c *Checker) newUnionType` (checker.go) — the raw constructor (not
    /// `get_union_type`'s normalization).
    pub fn new_union_type(&mut self, object_flags: ObjectFlags, types: Vec<TypeId>) -> TypeId {
        self.new_type(
            TypeFlags::UNION,
            object_flags,
            TypeData::Union(crate::types::UnionType {
                union_or_intersection: crate::types::UnionOrIntersectionType {
                    types,
                    ..Default::default()
                },
                ..Default::default()
            }),
        )
    }

    /// `(c *Checker) newIntersectionType` (checker.go).
    pub fn new_intersection_type(
        &mut self,
        object_flags: ObjectFlags,
        types: Vec<TypeId>,
    ) -> TypeId {
        self.new_type(
            TypeFlags::INTERSECTION,
            object_flags,
            TypeData::Intersection(crate::types::IntersectionType {
                union_or_intersection: crate::types::UnionOrIntersectionType {
                    types,
                    ..Default::default()
                },
                ..Default::default()
            }),
        )
    }

    /// `(c *Checker) newIndexedAccessType` (checker.go).
    pub fn new_indexed_access_type(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
        access_flags: crate::types::AccessFlags,
    ) -> TypeId {
        self.new_type(
            TypeFlags::INDEXED_ACCESS,
            ObjectFlags::NONE,
            TypeData::IndexedAccess(crate::types::IndexedAccessType {
                object_type: Some(object_type),
                index_type: Some(index_type),
                access_flags,
                ..Default::default()
            }),
        )
    }

    /// `(c *Checker) newIndexType` (checker.go).
    pub fn new_index_type(
        &mut self,
        target: TypeId,
        index_flags: crate::types::IndexFlags,
    ) -> TypeId {
        self.new_type(
            TypeFlags::INDEX,
            ObjectFlags::NONE,
            TypeData::Index(crate::types::IndexType {
                target: Some(target),
                index_flags,
                ..Default::default()
            }),
        )
    }

    /// `(c *Checker) newTemplateLiteralType` (checker.go).
    pub fn new_template_literal_type(&mut self, texts: Vec<String>, types: Vec<TypeId>) -> TypeId {
        self.new_type(
            TypeFlags::TEMPLATE_LITERAL,
            ObjectFlags::NONE,
            TypeData::TemplateLiteral(crate::types::TemplateLiteralType {
                texts,
                types,
                ..Default::default()
            }),
        )
    }

    /// `(c *Checker) newStringMappingType` (checker.go).
    pub fn new_string_mapping_type(&mut self, symbol: Option<SymbolId>, target: TypeId) -> TypeId {
        let t = self.new_type(
            TypeFlags::STRING_MAPPING,
            ObjectFlags::NONE,
            TypeData::StringMapping(crate::types::StringMappingType {
                target: Some(target),
                ..Default::default()
            }),
        );
        self.types_handle().get_mut(t).symbol = symbol;
        t
    }

    /// `(c *Checker) newSubstitutionType` (checker.go).
    pub fn new_substitution_type(&mut self, base_type: TypeId, constraint: TypeId) -> TypeId {
        self.new_type(
            TypeFlags::SUBSTITUTION,
            ObjectFlags::NONE,
            TypeData::Substitution(crate::types::SubstitutionType {
                base_type: Some(base_type),
                constraint: Some(constraint),
                ..Default::default()
            }),
        )
    }

    /// `(c *Checker) newSignature` (checker.go).
    #[allow(clippy::too_many_arguments)]
    pub fn new_signature(
        &mut self,
        flags: crate::types::SignatureFlags,
        declaration: Option<NodeId>,
        type_parameters: Vec<TypeId>,
        this_parameter: Option<SymbolId>,
        parameters: Vec<SymbolId>,
        resolved_return_type: Option<TypeId>,
        resolved_type_predicate: Option<Box<TypePredicate>>,
        min_argument_count: i32,
    ) -> SignatureId {
        self.signature_count += 1;
        self.signature_arena.alloc(Signature {
            // `sig.id = SignatureId(c.SignatureCount)` — Go ids are 1-based
            // and equal the arena index (element 0 is a tombstone).
            id: SignatureId(self.signature_count),
            flags,
            min_argument_count,
            resolved_min_argument_count: -1,
            declaration,
            type_parameters,
            parameters,
            this_parameter,
            resolved_return_type,
            resolved_type_predicate,
            ..Default::default()
        })
    }

    /// `(c *Checker) newIndexInfo` (checker.go).
    pub fn new_index_info(
        &mut self,
        key_type: TypeId,
        value_type: TypeId,
        is_readonly: bool,
        declaration: Option<NodeId>,
        components: Vec<NodeId>,
    ) -> IndexInfoId {
        self.index_info_arena.alloc(IndexInfo {
            key_type: Some(key_type),
            value_type: Some(value_type),
            is_readonly,
            declaration,
            components,
            ..Default::default()
        })
    }

    /// `(c *Checker) getRegularTypeOfLiteralType` (checker.go).
    pub fn get_regular_type_of_literal_type(&mut self, t: TypeId) -> TypeId {
        let __arena_flags = self.types.clone();
        let flags = __arena_flags.get(t).flags;
        if flags.intersects(TypeFlags::FRESHABLE) {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(t);
            return ty.as_literal_type().regular_type.unwrap_or(t);
        }
        if flags.intersects(TypeFlags::UNION) {
            if let Some(regular) = self.types_handle().get(t).as_union_type().regular_type {
                return regular;
            }
            let mapped = self.map_type(
                t,
                Rc::new(|c: &mut Checker, s: TypeId| c.get_regular_type_of_literal_type(s)),
            );
            if let TypeData::Union(d) = &mut self.types_handle().get_mut(t).data {
                d.regular_type = Some(mapped);
            }
            return mapped;
        }
        t
    }

    /// `(c *Checker) getFreshTypeOfLiteralType` (checker.go).
    pub fn get_fresh_type_of_literal_type(&mut self, t: TypeId) -> TypeId {
        if self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::FRESHABLE)
        {
            let (flags, value, fresh_type) = {
                let __arena_ty = self.types.clone();
                let ty = __arena_ty.get(t);
                let d = ty.as_literal_type();
                (ty.flags, d.value.clone(), d.fresh_type)
            };
            if let Some(fresh) = fresh_type {
                return fresh;
            }
            let f = self.new_literal_type(flags, value, Some(t));
            let __arena_sym = self.types.clone();
            let sym = __arena_sym.get(t).symbol;
            self.types_handle().get_mut(f).symbol = sym;
            if let TypeData::Literal(fd) = &mut self.types_handle().get_mut(f).data {
                fd.fresh_type = Some(f);
            }
            if let TypeData::Literal(d) = &mut self.types_handle().get_mut(t).data {
                d.fresh_type = Some(f);
            }
            return f;
        }
        t
    }

    /// `(c *Checker) getStringLiteralType` (checker.go).
    pub fn get_string_literal_type(&mut self, value: &str) -> TypeId {
        if let Some(&t) = self.string_literal_types.get(value) {
            return t;
        }
        let t = self.new_literal_type(
            TypeFlags::STRING_LITERAL,
            Some(evaluator::Value::String(value.to_string())),
            None,
        );
        self.string_literal_types.insert(value.to_string(), t);
        t
    }

    /// `(c *Checker) getNumberLiteralType` (checker.go). NaN cannot be used
    /// as a Go map key (`NaN != NaN` in IEEE 754), so Go caches the NaN type
    /// separately — `nan_type` mirrors that.
    pub fn get_number_literal_type(&mut self, value: tsc_jsnum::Number) -> TypeId {
        if value.is_nan() {
            if self.nan_type.is_none() {
                self.nan_type = Some(self.new_literal_type(
                    TypeFlags::NUMBER_LITERAL,
                    Some(evaluator::Value::Number(value)),
                    None,
                ));
            }
            return self.nan_type.unwrap();
        }
        if let Some(&t) = self.number_literal_types.get(&NumberLiteralKey(value)) {
            return t;
        }
        let t = self.new_literal_type(
            TypeFlags::NUMBER_LITERAL,
            Some(evaluator::Value::Number(value)),
            None,
        );
        self.number_literal_types.insert(NumberLiteralKey(value), t);
        t
    }

    /// `(c *Checker) getBigIntLiteralType` (checker.go).
    pub fn get_big_int_literal_type(&mut self, value: PseudoBigInt) -> TypeId {
        if let Some(&t) = self.bigint_literal_types.get(&value) {
            return t;
        }
        let t = self.new_literal_type(
            TypeFlags::BIG_INT_LITERAL,
            Some(evaluator::Value::PseudoBigInt(value.clone())),
            None,
        );
        self.bigint_literal_types.insert(value, t);
        t
    }

    /// `(c *Checker) parseBigIntLiteralType` (checker.go) — `text` is a
    /// valid bigint string excluding the trailing `n` (but including a
    /// possible `-` prefix); use `isValidBigIntString` before calling.
    pub fn parse_big_int_literal_type(&mut self, text: &str) -> TypeId {
        self.get_big_int_literal_type(tsc_jsnum::parse_valid_big_int(text))
    }

    /// `(c *Checker) tryCreateTypeReference` (checker.go).
    pub fn try_create_type_reference(
        &mut self,
        target: TypeId,
        type_arguments: &[TypeId],
    ) -> TypeId {
        if !type_arguments.is_empty() && target == self.empty_generic_type {
            return self.unknown_type;
        }
        self.create_type_reference(target, type_arguments)
    }

    /// `(c *Checker) createTypeReference` (checker.go).
    pub fn create_type_reference(&mut self, target: TypeId, type_arguments: &[TypeId]) -> TypeId {
        self.create_type_reference_ex(target, type_arguments, ObjectFlags::NONE)
    }

    /// `(c *Checker) createTypeReferenceEx` (checker.go).
    pub fn create_type_reference_ex(
        &mut self,
        target: TypeId,
        type_arguments: &[TypeId],
        object_flags: ObjectFlags,
    ) -> TypeId {
        let id = crate::checker_types::get_type_list_key(type_arguments);
        if let Some(&t) = self
            .types_handle()
            .get(target)
            .as_interface_type()
            .expect("createTypeReferenceEx: target is not an interface type")
            .type_reference
            .object_type
            .instantiations
            .get(&id)
        {
            return t;
        }
        let __arena_symbol = self.types.clone();
        let symbol = __arena_symbol.get(target).symbol;
        let propagating = self.get_propagating_flags_of_types(type_arguments, TypeFlags::NONE);
        let t = self.new_object_type(ObjectFlags::REFERENCE | object_flags | propagating, symbol);
        if let TypeData::TypeReference(d) = &mut self.types_handle().get_mut(t).data {
            d.object_type.target = Some(target);
            d.resolved_type_arguments = type_arguments.to_vec();
        }
        self.types_handle()
            .get_mut(target)
            .data
            .as_interface_type_mut()
            .expect("createTypeReferenceEx: target is not an interface type")
            .type_reference
            .object_type
            .instantiations
            .insert(id, t);
        t
    }

    /// `(c *Checker) cloneTypeReference` (checker.go).
    pub fn clone_type_reference(&mut self, source: TypeId) -> TypeId {
        let (symbol, object_flags, target, resolved_type_arguments) = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(source);
            let r = ty.as_type_reference();
            (
                ty.symbol,
                ty.object_flags,
                r.object_type.target,
                r.resolved_type_arguments.clone(),
            )
        };
        let t = self.new_object_type(ObjectFlags::REFERENCE, symbol);
        self.types_handle().get_mut(t).object_flags = object_flags & !ObjectFlags::MEMBERS_RESOLVED;
        if let TypeData::TypeReference(d) = &mut self.types_handle().get_mut(t).data {
            d.object_type.target = target;
            d.resolved_type_arguments = resolved_type_arguments;
        }
        t
    }

    /// `(c *Checker) createTypeFromGenericGlobalType` (checker.go).
    pub fn create_type_from_generic_global_type(
        &mut self,
        generic_global_type: TypeId,
        type_arguments: &[TypeId],
    ) -> TypeId {
        if generic_global_type != self.empty_generic_type {
            return self.create_type_reference(generic_global_type, type_arguments);
        }
        self.empty_object_type
    }

    /// `(c *Checker) getGlobalStrictFunctionType` (checker.go).
    pub fn get_global_strict_function_type(&mut self, name: &str) -> TypeId {
        if self.strict_bind_call_apply {
            return self.get_global_type(name, 0, true);
        }
        self.global_function_type
    }

    /// `(c *Checker) getGlobalImportMetaExpressionType` (checker.go) —
    /// creates the synthetic `ImportMetaExpression { meta: MetaProperty }`
    /// type on first use.
    pub fn get_global_import_meta_expression_type(&mut self) -> TypeId {
        if self.deferred_global_import_meta_expression_type.is_none() {
            let symbol = self.new_symbol(ast::SymbolFlags::NONE, "ImportMetaExpression");
            let thunk = self
                .get_global_import_meta_type
                .clone()
                .expect("getGlobalImportMetaType not initialized");
            let import_meta_type = thunk(self);
            let meta_property_symbol = self.new_symbol_ex(
                ast::SymbolFlags::PROPERTY,
                "meta",
                ast::checkflags::CheckFlags::READONLY,
            );
            self.symbol_arena.borrow_mut()[meta_property_symbol.index()].parent = Some(symbol);
            self.value_symbol_links
                .get(meta_property_symbol)
                .resolved_type = Some(import_meta_type);
            let members = create_symbol_table(&[meta_property_symbol], &self.symbol_arena);
            self.symbol_arena.borrow_mut()[symbol.index()].members = members.clone();
            self.deferred_global_import_meta_expression_type =
                Some(self.new_anonymous_type(Some(symbol), members, &[], &[], &[]));
        }
        self.deferred_global_import_meta_expression_type.unwrap()
    }

    /// `(c *Checker) createArrayType` (checker.go).
    pub fn create_array_type(&mut self, element_type: TypeId) -> TypeId {
        self.create_array_type_ex(element_type, false)
    }

    /// `(c *Checker) createArrayTypeEx` (checker.go).
    pub fn create_array_type_ex(&mut self, element_type: TypeId, readonly: bool) -> TypeId {
        let global = if readonly {
            self.global_readonly_array_type
        } else {
            self.global_array_type
        };
        self.create_type_from_generic_global_type(global, &[element_type])
    }

    // ======== Deferred helpers reached by the constructor sequence ========

    /// `(c *Checker) getUnionType` (checker.go).
    pub fn get_union_type(&mut self, types: &[TypeId]) -> TypeId {
        self.get_union_type_ex(types, UnionReduction::LITERAL, None, None)
    }

    /// `(c *Checker) getTemplateLiteralType` (checker.go:29682).
    pub fn get_template_literal_type(&mut self, texts: &[String], types: &[TypeId]) -> TypeId {
        let union_index = types.iter().position(|&t| {
            self.types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::NEVER | TypeFlags::UNION)
        });
        if let Some(union_index) = union_index {
            if !self.check_cross_product_union(types) {
                return self.error_type;
            }
            let texts2 = texts.to_vec();
            let types2 = types.to_vec();
            return self.map_type(
                types[union_index],
                Rc::new(move |c: &mut Checker, t2| {
                    let types3 = tsc_core::core::replace_element(&types2, union_index, t2);
                    c.get_template_literal_type(&texts2, &types3)
                }),
            );
        }
        if types.contains(&self.wildcard_type) {
            return self.wildcard_type;
        }
        let mut state = TemplateLiteralSpanState {
            new_types: Vec::new(),
            new_texts: Vec::new(),
            sb: texts[0].clone(),
            text_length: 0,
            too_large: false,
        };
        if !self.template_literal_add_spans(texts, types, &mut state) {
            if state.too_large {
                self.error(
                    self.current_node,
                    &tsc_diagnostics::Type_instantiation_is_excessively_deep_and_possibly_infinite,
                    &[],
                );
                return self.error_type;
            }
            return self.string_type;
        }
        if state.new_types.is_empty() {
            return self.get_string_literal_type(&String::from_utf8_lossy(
                &tsc_stringutil::combine_surrogate_pairs(state.sb.as_bytes()),
            ));
        }
        state.new_texts.push(
            String::from_utf8_lossy(&tsc_stringutil::combine_surrogate_pairs(
                state.sb.as_bytes(),
            ))
            .into_owned(),
        );
        if state.new_texts.iter().all(|t| t.is_empty()) {
            if state.new_types.iter().all(|&t| {
                self.types_handle()
                    .get(t)
                    .flags
                    .intersects(TypeFlags::STRING)
            }) {
                return self.string_type;
            }
            // Normalize `${Mapping<xxx>}` into Mapping<xxx>
            if state.new_types.len() == 1 && self.is_pattern_literal_type(state.new_types[0]) {
                return state.new_types[0];
            }
        }
        let key = crate::checker_types::get_template_type_key(&state.new_texts, &state.new_types);
        if let Some(&cached) = self.template_literal_types.get(&key) {
            return cached;
        }
        let ty = self.new_template_literal_type(state.new_texts, state.new_types);
        self.template_literal_types.insert(key, ty);
        ty
    }

    /// `addSpans` inner function of `getTemplateLiteralType` (checker.go:29704).
    /// Appends placeholder types to `state.new_types`/`state.new_texts` and
    /// merges literal and nested-template segments into `state.sb`. Returns
    /// false when a constituent cannot be folded into the template (callers
    /// then produce `stringType` or, when `state.too_large`, an error).
    fn template_literal_add_spans(
        &mut self,
        texts: &[String],
        types: &[TypeId],
        state: &mut TemplateLiteralSpanState,
    ) -> bool {
        for (i, &t) in types.iter().enumerate() {
            let flags = self.types_handle().get(t).flags;
            if flags.intersects(TypeFlags::LITERAL | TypeFlags::NULL | TypeFlags::UNDEFINED) {
                let s = self.get_template_string_for_type(t);
                state.sb.push_str(&s);
                state.sb.push_str(&texts[i + 1]);
            } else if flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
                let (t_texts, t_types) = {
                    let arena = self.types.clone();
                    let g = arena.get(t);
                    let tl = g.as_template_literal_type();
                    (tl.texts.clone(), tl.types.clone())
                };
                state.sb.push_str(&t_texts[0]);
                if !self.template_literal_add_spans(&t_texts, &t_types, state) {
                    return false;
                }
                state.sb.push_str(&texts[i + 1]);
            } else if self.is_generic_index_type(t) || self.is_pattern_literal_placeholder_type(t) {
                state.new_types.push(t);
                state.new_texts.push(
                    String::from_utf8_lossy(&tsc_stringutil::combine_surrogate_pairs(
                        state.sb.as_bytes(),
                    ))
                    .into_owned(),
                );
                state.text_length += state.sb.len();
                state.sb.clear();
                state.sb.push_str(&texts[i + 1]);
            } else {
                return false;
            }
            if state.text_length + state.sb.len()
                > crate::checker_d::MAX_TEMPLATE_LITERAL_TYPE_LENGTH
                || state.new_types.len() > crate::checker_d::MAX_TEMPLATE_LITERAL_TYPE_SPANS
            {
                state.too_large = true;
                return false;
            }
        }
        true
    }

    /// `(c *Checker) getTypeArguments` (checker.go) — delegates to the free
    /// function in `checker_c.rs`.
    pub fn get_type_arguments(&mut self, t: TypeId) -> Vec<TypeId> {
        crate::checker_c::get_type_arguments(self, t)
    }

    /// `(c *Checker) mapType` (checker.go).
    pub fn map_type(&mut self, t: TypeId, f: Rc<dyn Fn(&mut Checker, TypeId) -> TypeId>) -> TypeId {
        self.map_type_ex(t, f, false)
            .expect("mapType: mapTypeEx returned no type")
    }

    /// `(c *Checker) getDeclaredTypeOfSymbol` (checker.go) — delegates to the
    /// free function in `checker_c.rs`.
    pub fn get_declared_type_of_symbol(&mut self, symbol: SymbolId) -> TypeId {
        crate::checker_c::get_declared_type_of_symbol(self, symbol)
    }

    /// `(c *Checker) getAwaitedTypeEx` (checker.go:31806) — implemented in
    /// `checker_d.rs`.

    /// `(c *Checker) IsEmptyAnonymousObjectType` (checker.go).
    pub fn is_empty_anonymous_object_type(&mut self, t: TypeId) -> bool {
        let ty = self.types.clone();
        let ty = ty.get(t);
        if !ty.object_flags.intersects(ObjectFlags::ANONYMOUS) {
            return false;
        }
        let Some(symbol) = ty.symbol else {
            return false;
        };
        if !self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::TYPE_LITERAL)
        {
            return false;
        }
        if !self.get_members_of_symbol(symbol).is_empty() {
            return false;
        }
        if ty.object_flags.intersects(ObjectFlags::MEMBERS_RESOLVED) {
            return self.is_empty_resolved_type(t);
        }
        true
    }

    /// `(c *Checker) couldContainTypeVariablesWorker` (checker.go) —
    /// delegates to the free function in `checker_c.rs`.
    pub fn could_contain_type_variables_worker(&mut self, t: TypeId) -> bool {
        crate::checker_c::could_contain_type_variables_worker(self, t)
    }

    /// `(c *Checker) isStringIndexSignatureOnlyTypeWorker` (checker.go).
    pub fn is_string_index_signature_only_type_worker(&mut self, t: TypeId) -> bool {
        let flags = self.types.clone().get(t).flags;
        if flags.intersects(TypeFlags::OBJECT)
            && !self.is_generic_mapped_type(t)
            && self.get_properties_of_type(t).is_empty()
            && self.get_index_infos_of_type(t).len() == 1
            && self.get_index_info_of_type(t, self.string_type).is_some()
        {
            return true;
        }
        // PORT: Go calls `core.Every(t.Types(), ...)` directly here — it must
        // iterate BOTH union and intersection constituents. Routing through
        // `every_type` (union-only) recurses on the intersection itself.
        if !flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
            return false;
        }
        let __arena_types = self.types.clone();
        let types = __arena_types.get(t).types().to_vec();
        types.iter().all(|&u| {
            let thunk = self
                .is_string_index_signature_only_type
                .clone()
                .expect("isStringIndexSignatureOnlyType not initialized");
            thunk(self, u)
        })
    }

    /// `(c *Checker) markNodeAssignmentsWorker` (flow.go) — implemented in
    /// `crate::flow`.

    /// `(c *Checker) compareTypesAssignableWorker` (relater.go) —
    /// implemented in `crate::relater`.

    /// `(c *Checker) getUniqueLiteralTypeForTypeParameter` (checker.go).
    pub fn get_unique_literal_type_for_type_parameter(&mut self, t: TypeId) -> TypeId {
        if self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::TYPE_PARAMETER)
        {
            return self.unique_literal_type;
        }
        t
    }

    /// `(c *Checker) reportUnreliableWorker` (checker.go).
    pub fn report_unreliable_worker(&mut self, t: TypeId) -> TypeId {
        if t == self.marker_super_type || t == self.marker_sub_type || t == self.marker_other_type {
            self.reliability_flags |= RelationComparisonResult::REPORTS_UNRELIABLE;
        }
        t
    }

    /// `(c *Checker) reportUnmeasurableWorker` (checker.go).
    pub fn report_unmeasurable_worker(&mut self, t: TypeId) -> TypeId {
        if t == self.marker_super_type || t == self.marker_sub_type || t == self.marker_other_type {
            self.reliability_flags |= RelationComparisonResult::REPORTS_UNMEASURABLE;
        }
        t
    }

    /// `(c *Checker) restrictiveMapperWorker` (checker.go).
    pub fn restrictive_mapper_worker(&mut self, t: TypeId) -> TypeId {
        if self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::TYPE_PARAMETER)
        {
            return self.get_restrictive_type_parameter(t);
        }
        t
    }

    /// `(c *Checker) getRestrictiveTypeParameter` (checker.go).
    pub fn get_restrictive_type_parameter(&mut self, t: TypeId) -> TypeId {
        let (constraint, symbol) = {
            let arena = self.types.clone();
            let ty = arena.get(t);
            (ty.as_type_parameter().constraint, ty.symbol)
        };
        if constraint.is_none() && self.get_constraint_declaration(t).is_none()
            || constraint == Some(self.no_constraint_type)
        {
            return t;
        }
        let key = CachedTypeKey {
            kind: CachedTypeKind::RestrictiveTypeParameter,
            type_id: self.types_handle().get(t).id,
        };
        if let Some(&cached) = self.cached_types.get(&key) {
            return cached;
        }
        let result = self.new_type_parameter(symbol);
        self.types_handle()
            .get_mut(result)
            .as_type_parameter_mut()
            .constraint = Some(self.no_constraint_type);
        self.cached_types.insert(key, result);
        result
    }

    /// `(c *Checker) permissiveMapperWorker` (checker.go).
    pub fn permissive_mapper_worker(&mut self, t: TypeId) -> TypeId {
        if self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::TYPE_PARAMETER)
        {
            return self.wildcard_type;
        }
        t
    }
}

// ======== get_global_* thunk accessors ========

// Go's `c.getGlobalX()` lazy getters are stored as `Option<Rc<*Thunk>>` fields
// populated by `new_checker`; these methods invoke the stored thunk. Method and
// field share a name deliberately — Rust resolves `self.f()` to the method and
// `self.f` (no parens) to the field.

impl Checker {
    /// `(c *Checker) get_global_es_symbol_type` — invokes the `get_global_es_symbol_type` thunk field.
    pub(crate) fn get_global_es_symbol_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_es_symbol_type
            .clone()
            .expect("get_global_es_symbol_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_big_int_type` — invokes the `get_global_big_int_type` thunk field.
    pub(crate) fn get_global_big_int_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_big_int_type
            .clone()
            .expect("get_global_big_int_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_import_meta_type` — invokes the `get_global_import_meta_type` thunk field.
    pub(crate) fn get_global_import_meta_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_import_meta_type
            .clone()
            .expect("get_global_import_meta_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_import_attributes_type_checked` — invokes the `get_global_import_attributes_type_checked` thunk field.
    pub(crate) fn get_global_import_attributes_type_checked(&mut self) -> TypeId {
        let thunk = self
            .get_global_import_attributes_type_checked
            .clone()
            .expect("get_global_import_attributes_type_checked");
        thunk(self)
    }

    /// `(c *Checker) get_global_disposable_type` — invokes the `get_global_disposable_type` thunk field.
    pub(crate) fn get_global_disposable_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_disposable_type
            .clone()
            .expect("get_global_disposable_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_async_disposable_type` — invokes the `get_global_async_disposable_type` thunk field.
    pub(crate) fn get_global_async_disposable_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_async_disposable_type
            .clone()
            .expect("get_global_async_disposable_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_nan_symbol_or_nil` — invokes the `get_global_nan_symbol_or_nil` thunk field.
    pub(crate) fn get_global_nan_symbol_or_nil(&mut self) -> Option<SymbolId> {
        let thunk = self
            .get_global_nan_symbol_or_nil
            .clone()
            .expect("get_global_nan_symbol_or_nil");
        thunk(self)
    }

    /// `(c *Checker) get_global_record_symbol` — invokes the `get_global_record_symbol` thunk field.
    pub(crate) fn get_global_record_symbol(&mut self) -> Option<SymbolId> {
        let thunk = self
            .get_global_record_symbol
            .clone()
            .expect("get_global_record_symbol");
        thunk(self)
    }

    /// `(c *Checker) get_global_es_symbol_constructor_symbol_or_nil` — invokes the `get_global_es_symbol_constructor_symbol_or_nil` thunk field.
    pub(crate) fn get_global_es_symbol_constructor_symbol_or_nil(&mut self) -> Option<SymbolId> {
        let thunk = self
            .get_global_es_symbol_constructor_symbol_or_nil
            .clone()
            .expect("get_global_es_symbol_constructor_symbol_or_nil");
        thunk(self)
    }

    /// `(c *Checker) get_global_es_symbol_constructor_type_symbol_or_nil` — invokes the `get_global_es_symbol_constructor_type_symbol_or_nil` thunk field.
    pub(crate) fn get_global_es_symbol_constructor_type_symbol_or_nil(
        &mut self,
    ) -> Option<SymbolId> {
        let thunk = self
            .get_global_es_symbol_constructor_type_symbol_or_nil
            .clone()
            .expect("get_global_es_symbol_constructor_type_symbol_or_nil");
        thunk(self)
    }

    /// `(c *Checker) get_global_import_call_options_type_checked` — invokes the `get_global_import_call_options_type_checked` thunk field.
    pub(crate) fn get_global_import_call_options_type_checked(&mut self) -> TypeId {
        let thunk = self
            .get_global_import_call_options_type_checked
            .clone()
            .expect("get_global_import_call_options_type_checked");
        thunk(self)
    }

    /// `(c *Checker) get_global_promise_type` — invokes the `get_global_promise_type` thunk field.
    pub(crate) fn get_global_promise_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_promise_type
            .clone()
            .expect("get_global_promise_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_promise_type_checked` — invokes the `get_global_promise_type_checked` thunk field.
    pub(crate) fn get_global_promise_type_checked(&mut self) -> TypeId {
        let thunk = self
            .get_global_promise_type_checked
            .clone()
            .expect("get_global_promise_type_checked");
        thunk(self)
    }

    /// `(c *Checker) get_global_promise_like_type` — invokes the `get_global_promise_like_type` thunk field.
    pub(crate) fn get_global_promise_like_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_promise_like_type
            .clone()
            .expect("get_global_promise_like_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_abstract_module_source_type` — invokes the `get_global_abstract_module_source_type` thunk field.
    pub(crate) fn get_global_abstract_module_source_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_abstract_module_source_type
            .clone()
            .expect("get_global_abstract_module_source_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_promise_constructor_symbol` — invokes the `get_global_promise_constructor_symbol` thunk field.
    pub(crate) fn get_global_promise_constructor_symbol(&mut self) -> Option<SymbolId> {
        let thunk = self
            .get_global_promise_constructor_symbol
            .clone()
            .expect("get_global_promise_constructor_symbol");
        thunk(self)
    }

    /// `(c *Checker) get_global_promise_constructor_symbol_or_nil` — invokes the `get_global_promise_constructor_symbol_or_nil` thunk field.
    pub(crate) fn get_global_promise_constructor_symbol_or_nil(&mut self) -> Option<SymbolId> {
        let thunk = self
            .get_global_promise_constructor_symbol_or_nil
            .clone()
            .expect("get_global_promise_constructor_symbol_or_nil");
        thunk(self)
    }

    /// `(c *Checker) get_global_omit_symbol` — invokes the `get_global_omit_symbol` thunk field.
    pub(crate) fn get_global_omit_symbol(&mut self) -> Option<SymbolId> {
        let thunk = self
            .get_global_omit_symbol
            .clone()
            .expect("get_global_omit_symbol");
        thunk(self)
    }

    /// `(c *Checker) get_global_no_infer_symbol_or_nil` — invokes the `get_global_no_infer_symbol_or_nil` thunk field.
    pub(crate) fn get_global_no_infer_symbol_or_nil(&mut self) -> Option<SymbolId> {
        let thunk = self
            .get_global_no_infer_symbol_or_nil
            .clone()
            .expect("get_global_no_infer_symbol_or_nil");
        thunk(self)
    }

    /// `(c *Checker) get_global_iterator_type` — invokes the `get_global_iterator_type` thunk field.
    pub(crate) fn get_global_iterator_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_iterator_type
            .clone()
            .expect("get_global_iterator_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_iterable_type` — invokes the `get_global_iterable_type` thunk field.
    pub(crate) fn get_global_iterable_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_iterable_type
            .clone()
            .expect("get_global_iterable_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_iterable_type_checked` — invokes the `get_global_iterable_type_checked` thunk field.
    pub(crate) fn get_global_iterable_type_checked(&mut self) -> TypeId {
        let thunk = self
            .get_global_iterable_type_checked
            .clone()
            .expect("get_global_iterable_type_checked");
        thunk(self)
    }

    /// `(c *Checker) get_global_iterable_iterator_type` — invokes the `get_global_iterable_iterator_type` thunk field.
    pub(crate) fn get_global_iterable_iterator_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_iterable_iterator_type
            .clone()
            .expect("get_global_iterable_iterator_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_iterable_iterator_type_checked` — invokes the `get_global_iterable_iterator_type_checked` thunk field.
    pub(crate) fn get_global_iterable_iterator_type_checked(&mut self) -> TypeId {
        let thunk = self
            .get_global_iterable_iterator_type_checked
            .clone()
            .expect("get_global_iterable_iterator_type_checked");
        thunk(self)
    }

    /// `(c *Checker) get_global_iterator_object_type` — invokes the `get_global_iterator_object_type` thunk field.
    pub(crate) fn get_global_iterator_object_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_iterator_object_type
            .clone()
            .expect("get_global_iterator_object_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_generator_type` — invokes the `get_global_generator_type` thunk field.
    pub(crate) fn get_global_generator_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_generator_type
            .clone()
            .expect("get_global_generator_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_async_iterator_type` — invokes the `get_global_async_iterator_type` thunk field.
    pub(crate) fn get_global_async_iterator_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_async_iterator_type
            .clone()
            .expect("get_global_async_iterator_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_async_iterable_type` — invokes the `get_global_async_iterable_type` thunk field.
    pub(crate) fn get_global_async_iterable_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_async_iterable_type
            .clone()
            .expect("get_global_async_iterable_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_async_iterable_type_checked` — invokes the `get_global_async_iterable_type_checked` thunk field.
    pub(crate) fn get_global_async_iterable_type_checked(&mut self) -> TypeId {
        let thunk = self
            .get_global_async_iterable_type_checked
            .clone()
            .expect("get_global_async_iterable_type_checked");
        thunk(self)
    }

    /// `(c *Checker) get_global_async_iterable_iterator_type` — invokes the `get_global_async_iterable_iterator_type` thunk field.
    pub(crate) fn get_global_async_iterable_iterator_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_async_iterable_iterator_type
            .clone()
            .expect("get_global_async_iterable_iterator_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_async_iterable_iterator_type_checked` — invokes the `get_global_async_iterable_iterator_type_checked` thunk field.
    pub(crate) fn get_global_async_iterable_iterator_type_checked(&mut self) -> TypeId {
        let thunk = self
            .get_global_async_iterable_iterator_type_checked
            .clone()
            .expect("get_global_async_iterable_iterator_type_checked");
        thunk(self)
    }

    /// `(c *Checker) get_global_async_iterator_object_type` — invokes the `get_global_async_iterator_object_type` thunk field.
    pub(crate) fn get_global_async_iterator_object_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_async_iterator_object_type
            .clone()
            .expect("get_global_async_iterator_object_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_async_generator_type` — invokes the `get_global_async_generator_type` thunk field.
    pub(crate) fn get_global_async_generator_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_async_generator_type
            .clone()
            .expect("get_global_async_generator_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_iterator_yield_result_type` — invokes the `get_global_iterator_yield_result_type` thunk field.
    pub(crate) fn get_global_iterator_yield_result_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_iterator_yield_result_type
            .clone()
            .expect("get_global_iterator_yield_result_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_iterator_return_result_type` — invokes the `get_global_iterator_return_result_type` thunk field.
    pub(crate) fn get_global_iterator_return_result_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_iterator_return_result_type
            .clone()
            .expect("get_global_iterator_return_result_type");
        thunk(self)
    }

    /// `(c *Checker) get_global_class_accessor_decorator_contxt_type` — invokes the `get_global_class_accessor_decorator_contxt_type` thunk field.
    pub(crate) fn get_global_class_accessor_decorator_contxt_type(&mut self) -> TypeId {
        let thunk = self
            .get_global_class_accessor_decorator_contxt_type
            .clone()
            .expect("get_global_class_accessor_decorator_contxt_type");
        thunk(self)
    }
}

/// `binder::NameResolverHost` implementation — the Go `NameResolver` hook
/// table for `createNameResolver`/`createNameResolverForSuggestion`, routed
/// to `Checker` methods.
impl tsc_binder::nameresolver::NameResolverHost for Checker {
    fn nr_get_symbol_of_declaration(
        &mut self,
        node: NodeId,
        _nodes: &[ast::Node],
    ) -> Option<SymbolId> {
        self.get_symbol_of_declaration(node)
    }

    fn nr_error(
        &mut self,
        location: Option<NodeId>,
        message: &'static tsc_diagnostics::Message,
        args: Vec<String>,
    ) {
        self.error(location, message, &args);
    }

    /// `Lookup` — `getSymbol` normally, `getSuggestionForSymbolNameLookup`
    /// for the suggestion resolver.
    fn nr_lookup(
        &mut self,
        symbols: &SymbolTable,
        name: &str,
        meaning: ast::SymbolFlags,
        suggestion: bool,
    ) -> Option<SymbolId> {
        if suggestion {
            self.get_suggestion_for_symbol_name_lookup(symbols, name, meaning)
        } else {
            self.get_symbol(symbols, name, meaning)
        }
    }

    fn nr_symbol_referenced(&mut self, symbol: SymbolId, meaning: ast::SymbolFlags) {
        self.symbol_referenced(symbol, meaning);
    }

    fn nr_set_requires_scope_change_cache(
        &mut self,
        node: NodeId,
        value: tsc_core::tristate::Tristate,
    ) {
        self.set_requires_scope_change_cache(node, value);
    }

    fn nr_get_requires_scope_change_cache(&mut self, node: NodeId) -> tsc_core::tristate::Tristate {
        self.get_requires_scope_change_cache(node)
    }

    fn nr_on_property_with_invalid_initializer(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
        property_with_invalid_initializer: NodeId,
        result: Option<SymbolId>,
    ) -> bool {
        self.check_and_report_error_for_invalid_initializer(
            error_location,
            name,
            property_with_invalid_initializer,
            result,
        )
    }

    fn nr_on_failed_to_resolve_symbol(
        &mut self,
        error_location: Option<NodeId>,
        name: &str,
        meaning: ast::SymbolFlags,
        name_not_found_message: &'static tsc_diagnostics::Message,
    ) {
        self.on_failed_to_resolve_symbol(
            error_location,
            name,
            meaning,
            Some(name_not_found_message),
        );
    }

    fn nr_on_successfully_resolved_symbol(
        &mut self,
        error_location: Option<NodeId>,
        result: SymbolId,
        meaning: ast::SymbolFlags,
        last_location: Option<NodeId>,
        associated_declaration_for_containing_initializer_or_binding_name: Option<NodeId>,
        within_deferred_context: bool,
    ) {
        self.on_successfully_resolved_symbol(
            error_location,
            result,
            meaning,
            last_location,
            associated_declaration_for_containing_initializer_or_binding_name,
            within_deferred_context,
        );
    }

    /// `GetDeclarationOfKind(symbol, kind) != nil` — the symbol's
    /// declarations may live in another file's arena (merged symbols); each
    /// is resolved through the arena that actually owns it.
    fn nr_has_declaration_of_kind(
        &mut self,
        symbol: tsc_ast::ids::SymbolId,
        kind: ast::Kind,
        work: &[ast::Node],
    ) -> bool {
        let declarations = self.symbol_arena.borrow()[symbol.index()].declarations.clone();
        let program = self.program.clone().expect("program");
        declarations.iter().any(|&d| {
            crate::printer_util::resolve_arena_for(&program, work, d)[d].kind == kind
        })
    }
}
