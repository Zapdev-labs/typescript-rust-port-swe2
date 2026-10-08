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
use tsc_ast::{self as ast, FlowNodeId, NodeId, SymbolId, SymbolTable};
use tsc_collections::OrderedSet;
use tsc_core::context::Context;
use tsc_core::linkstore::LinkStore;
use tsc_core::options_generated::{ModuleKind, ModuleResolutionKind, ScriptTarget};
use tsc_core::options_generated::CompilerOptions;
use tsc_evaluator as evaluator;
use tsc_jsnum::PseudoBigInt;
use tsc_scanner::scanner::Scanner;
use tsc_tracing as tracing;

use crate::checker_types::{
    AssignmentReducedKey, CachedSignatureKey, CachedTypeKey, ContextualInfo,
    DeferredDiagnosticCallback, DiscriminatedContextualTypeKey, EvaluatorThunk, FlowLoopInfo,
    FlowLoopKey, InstantiationExpressionKey, IterationTypes, IterationTypesKey, IterationTypesResolver,
    NameResolverThunk, NarrowedTypeKey, NodeBoolThunk, NonExistentPropertyKey, NumberLiteralKey,
    PropertiesTypesKey, ReverseMappedTypeKey, StringMappingKey, SubstitutionTypeKey,
    SymbolChainComparerThunk, SymbolComparerThunk, ThisAssignmentDeclarationKind, TypeBoolThunk,
    TypeResolution, TypeThunk, UnionOfUnionKey, VarianceStackEntry,
};
use crate::emitresolver::EmitResolverLinks;
use crate::flagdef::flag_type;
use crate::flow::{FlowState, SharedFlow};
use crate::inference::InferenceState;
use crate::links::{NodeLinkStore, SymbolArenaLinkStore};
use crate::mapper::{TypeMapperArena, TypeMapperId};
use crate::nodebuilder::NodeBuilder;
use crate::relater::{ExpandingFlags, RelationComparisonResult, Relater, SharedRelation};
use crate::symbolaccessibility::{ExternalModuleContainerIndex, SymbolTableId};
use crate::tracer::Tracer;
use crate::types::{
    AliasSymbolLinks, AssertionLinks, ArrayLiteralLinks, ComputedNameNodeLinks,
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
    /// `globals`.
    pub globals: SymbolTable,
    /// `evaluate` — `evaluator.Evaluator` (see `EvaluatorThunk` for the
    /// `&mut Checker` receiver addition).
    pub evaluate: Option<Box<EvaluatorThunk<'static>>>,
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
    pub this_expando_locations: FxHashMap<SymbolId, NodeId>,
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
    /// `diagnostics`.
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
    pub enum_relation: FxHashMap<EnumLiteralKey, RelationComparisonResult>,
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
    pub get_global_non_nullable_type_alias_or_nil: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
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
    pub get_global_es_symbol_constructor_symbol_or_nil: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
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
    pub get_global_promise_constructor_symbol: Option<Rc<crate::checker_types::SymbolThunk<'static>>>,
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
    pub type_to_string_nodebuilder: Option<Box<NodeBuilder>>,
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
            globals: SymbolTable::new(),
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
fn count_global_symbols(files: &[NodeId], program: &Rc<dyn crate::checker_types::Program>) -> usize {
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
        c.can_collect_symbol_alias_accessibility_data =
            c.compiler_options.verbatim_module_syntax.is_false_or_unknown();
        c.array_variances = vec![VarianceFlags::COVARIANT];
        c.globals = SymbolTable::with_size_hint(count_global_symbols(&c.files, &program));
        // PORT: Go `evaluator.NewEvaluator(c.evaluateEntity,
        // ast.OEKParentheses)` — the outer evaluator walk is deferred until
        // `new_evaluator` gains a checker-parameterized entry point; the thunk
        // defers to `evaluate_entity` at call time.
        c.evaluate = Some(Box::new(|c: &mut Checker, expr, location, nodes| {
            c.evaluate_entity(expr, location, nodes)
        }));
        c.undefined_symbol = c.new_symbol(ast::SymbolFlags::PROPERTY, "undefined");
        c.arguments_symbol = c.new_symbol(ast::SymbolFlags::PROPERTY, "arguments");
        c.require_symbol = c.new_symbol(ast::SymbolFlags::PROPERTY, "require");
        c.unknown_symbol = c.new_symbol(ast::SymbolFlags::PROPERTY, "unknown");
        c.global_this_symbol =
            c.new_symbol_ex(ast::SymbolFlags::MODULE, "globalThis", ast::checkflags::CheckFlags::READONLY);
        // `c.globalThisSymbol.Exports = c.globals` — Go shares the map header
        // (later `c.globals` inserts show through `exports`); the port's
        // `SymbolTable` is a value. PORT(divergence): wave-2 may need
        // `Rc<RefCell<SymbolTable>>` for full sharing semantics.
        let globals = c.globals.clone();
        c.symbol_arena.borrow_mut()[c.global_this_symbol.index()].exports = globals;
        let name = c.symbol_arena.borrow()[c.global_this_symbol.index()].name.clone();
        c.globals.set(name, c.global_this_symbol);
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
        if let TypeData::Literal(d) = &mut c.types.get_mut(c.regular_false_type).data {
            d.fresh_type = Some(c.false_type);
        }
        if let TypeData::Literal(d) = &mut c.types.get_mut(c.false_type).data {
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
        if let TypeData::Literal(d) = &mut c.types.get_mut(c.regular_true_type).data {
            d.fresh_type = Some(c.true_type);
        }
        if let TypeData::Literal(d) = &mut c.types.get_mut(c.true_type).data {
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
        c.report_unreliable_mapper = crate::mapper::new_function_type_mapper(&mut c, |c, t| {
            c.report_unreliable_worker(t)
        });
        c.report_unmeasurable_mapper = crate::mapper::new_function_type_mapper(&mut c, |c, t| {
            c.report_unmeasurable_worker(t)
        });
        c.restrictive_mapper = crate::mapper::new_function_type_mapper(&mut c, |c, t| {
            c.restrictive_mapper_worker(t)
        });
        c.permissive_mapper = crate::mapper::new_function_type_mapper(&mut c, |c, t| {
            c.permissive_mapper_worker(t)
        });
        c.empty_object_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.empty_jsx_object_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.empty_fresh_jsx_object_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        let type_literal_symbol =
            c.new_symbol(ast::SymbolFlags::TYPE_LITERAL, ast::symbol::INTERNAL_SYMBOL_NAME_TYPE);
        c.empty_type_literal_type =
            c.new_anonymous_type(Some(type_literal_symbol), SymbolTable::new(), &[], &[], &[]);
        c.unknown_empty_object_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.unknown_union_type = c.create_unknown_union_type();
        c.empty_generic_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        // `c.emptyGenericType.AsObjectType().instantiations = make(map)` — the
        // port's field is already an empty map.
        c.any_function_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.types
            .get_mut(c.any_function_type)
            .object_flags
            .insert(ObjectFlags::NON_INFERRABLE_TYPE);
        c.no_constraint_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.circular_constraint_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.resolving_default_type = c.new_anonymous_type(None, SymbolTable::new(), &[], &[], &[]);
        c.marker_super_type = c.new_type_parameter(None);
        c.marker_sub_type = c.new_type_parameter(None);
        if let TypeData::TypeParameter(d) = &mut c.types.get_mut(c.marker_sub_type).data {
            d.constraint = Some(c.marker_super_type);
        }
        c.marker_other_type = c.new_type_parameter(None);
        c.marker_super_type_for_check = c.new_type_parameter(None);
        c.marker_sub_type_for_check = c.new_type_parameter(None);
        if let TypeData::TypeParameter(d) = &mut c.types.get_mut(c.marker_sub_type_for_check).data {
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
            "string", "number", "bigint", "boolean", "symbol", "undefined", "object", "function",
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
        c.get_global_promise_type_checked =
            Some(c.get_global_type_resolver("Promise", 1, true));
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
        c.get_global_iterable_type_checked =
            Some(c.get_global_type_resolver("Iterable", 3, true));
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
                    arena[symbol.index()].declarations.iter().copied().find(|&d| {
                        let nodes = self.program_nodes(d);
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
                let type_parameter_count =
                    self.types.get(t).as_interface_type().expect("interface type").all_type_parameters.len();
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
            let nodes = self.program_nodes(declaration);
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
        let resolve = self.resolve_name.clone().expect("resolveName not initialized");
        resolve(self, None, name, meaning, diagnostic, false, false)
    }

    /// `(c *Checker) initializeClosures` (checker.go).
    pub fn initialize_closures(&mut self) {
        self.is_primitive_or_object_or_empty_type = Some(Rc::new(|c: &mut Checker, t: TypeId| {
            c.types
                .get(t)
                .flags
                .intersects(TypeFlags::PRIMITIVE | TypeFlags::NON_PRIMITIVE)
                || c.is_empty_anonymous_object_type(t)
        }));
        self.contains_missing_type = Some(Rc::new(|c: &mut Checker, t: TypeId| {
            if t == c.missing_type {
                return true;
            }
            let ty = c.types.get(t);
            ty.flags.intersects(TypeFlags::UNION) && ty.types().first() == Some(&c.missing_type)
        }));
        self.could_contain_type_variables = Some(Rc::new(|c: &mut Checker, t: TypeId| {
            c.could_contain_type_variables_worker(t)
        }));
        self.is_string_index_signature_only_type =
            Some(Rc::new(|c: &mut Checker, t: TypeId| {
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
                )
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
        // Initialize global symbol table
        let mut ambient_module_symbols: Vec<SymbolId> = Vec::new();
        let mut augmentations: Vec<Vec<NodeId>> = Vec::new();
        let files = self.files.clone();
        for file in &files {
            let nodes = self.program.as_ref().expect("program").nodes(file.file_index());
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
                gather_pattern_ambient_modules(&nodes[*file], &mut self.pattern_ambient_modules);
                augmentations.push(nodes[*file].as_source_file().module_augmentations.to_vec());
                if let Some(_file_symbol) = file_node.symbol() {
                    // Merge in UMD exports with first-in-wins semantics
                    // (see #9771)
                    for (name, &symbol) in nodes[*file].as_source_file().global_exports.entries() {
                        if self.globals.get(name).is_none() {
                            self.globals.set(name.clone(), symbol);
                        }
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
                let nodes = self
                    .program
                    .as_ref()
                    .expect("program")
                    .nodes(augmentation.file_index());
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
        self.global_callable_function_type = self.get_global_strict_function_type("CallableFunction");
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
                let nodes = self
                    .program
                    .as_ref()
                    .expect("program")
                    .nodes(augmentation.file_index());
                let parent = nodes[augmentation].parent.unwrap_or(NodeId::NONE);
                if !ast::is_global_scope_augmentation(&nodes[parent]) {
                    self.merge_module_augmentation(augmentation);
                }
            }
        }
    }

    /// `(c *Checker) mergeGlobalSymbol` (checker.go).
    pub fn merge_global_symbol(&mut self, symbol: SymbolId) {
        let name = self.symbol_arena.borrow()[symbol.index()].name.clone();
        let global_symbol = self.globals.get(&name).copied();
        let merged = match global_symbol {
            Some(global_symbol) => self.merge_symbol(global_symbol, symbol, false),
            None => self.get_merged_symbol(symbol),
        };
        self.globals.set(name, merged);
    }

    /// `(c *Checker) mergeSymbol` — PORT(deferred): symbol merging lands
    /// with checker.go.
    pub fn merge_symbol(
        &mut self,
        target: SymbolId,
        source: SymbolId,
        unidirectional: bool,
    ) -> SymbolId {
        let _ = (target, source, unidirectional);
        unimplemented!("PORT(deferred): mergeSymbol lands with checker.go")
    }

    /// `(c *Checker) getMergedSymbol` — PORT(deferred).
    pub fn get_merged_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        let _ = symbol;
        unimplemented!("PORT(deferred): getMergedSymbol lands with checker.go")
    }

    /// `(c *Checker) mergeModuleAugmentation` — PORT(deferred).
    pub fn merge_module_augmentation(&mut self, module_name: NodeId) {
        let _ = module_name;
        unimplemented!("PORT(deferred): mergeModuleAugmentation lands with checker.go")
    }

    /// `(c *Checker) mergePatternAmbientModules` — PORT(deferred).
    pub fn merge_pattern_ambient_modules(&mut self) {
        unimplemented!("PORT(deferred): mergePatternAmbientModules lands with checker.go")
    }

    /// `(c *Checker) addUndefinedToGlobalsOrErrorOnRedeclaration`
    /// (checker.go).
    pub fn add_undefined_to_globals_or_error_on_redeclaration(&mut self) {
        let name = self.symbol_arena.borrow()[self.undefined_symbol.index()]
            .name
            .clone();
        let target_symbol = self.globals.get(&name).copied();
        if let Some(target_symbol) = target_symbol {
            let declarations = self.symbol_arena.borrow()[target_symbol.index()]
                .declarations
                .clone();
            for declaration in declarations {
                let nodes = self.program_nodes(declaration);
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
            self.globals.set(name, self.undefined_symbol);
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
        Rc::new(|c: &mut Checker, location, name, meaning, message, is_use, exclude_globals| {
            c.resolve_name_via_binder(location, name, meaning, message, is_use, exclude_globals)
        })
    }

    /// `(c *Checker) createNameResolverForSuggestion` — PORT(deferred): same
    /// hook limitation as `create_name_resolver`.
    pub fn create_name_resolver_for_suggestion(&self) -> Rc<NameResolverThunk<'static>> {
        Rc::new(|c: &mut Checker, location, name, meaning, message, is_use, exclude_globals| {
            c.resolve_name_for_suggestion_via_binder(
                location,
                name,
                meaning,
                message,
                is_use,
                exclude_globals,
            )
        })
    }

    /// `binder::NameResolver::Resolve` wired for `resolve_name` —
    /// PORT(deferred): needs `&mut Checker`-aware name-resolver hooks.
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
        let _ = (location, name, meaning, name_not_found_message, is_use, exclude_globals);
        unimplemented!("PORT(deferred): resolve_name_via_binder lands with createNameResolver")
    }

    /// `binder::NameResolver::Resolve` (suggestion variant) — PORT(deferred).
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
        let _ = (location, name, meaning, name_not_found_message, is_use, exclude_globals);
        unimplemented!(
            "PORT(deferred): resolve_name_for_suggestion_via_binder lands with createNameResolverForSuggestion"
        )
    }

    /// `(c *Checker) evaluateEntity` (checker.go) — PORT(deferred):
    /// `resolveEntityName`/`evaluateEnumMember` land with checker.go.
    pub fn evaluate_entity(
        &mut self,
        expr: NodeId,
        location: Option<NodeId>,
        _nodes: &[ast::Node],
    ) -> evaluator::Result {
        let _ = (expr, location);
        unimplemented!("PORT(deferred): evaluateEntity lands with checker.go")
    }

    /// `program.nodes(...)` — the per-file node arena for `NodeId` derefs
    /// (the `Program` trait's port-added accessor).
    pub fn program_nodes(&self, node: NodeId) -> Rc<Vec<ast::Node>> {
        self.program.as_ref().expect("program").nodes(node.file_index())
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
            let nodes = self.program_nodes(node);
            if let Some(source_file) = ast::get_source_file_of_node(Some(node), &nodes) {
                let sf = nodes[source_file].as_source_file();
                loc = tsc_scanner::scanner::get_error_range_for_node(sf, node, &nodes);
                file = Some(ast::diagnostic::DiagnosticFile::from_node(source_file, &nodes));
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
                let nodes = self.program_nodes(d);
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
        let nodes = self.program_nodes(n1);
        let s1 = ast::get_source_file_of_node(Some(n1), &nodes);
        let nodes2 = self.program_nodes(n2);
        let s2 = ast::get_source_file_of_node(Some(n2), &nodes2);
        if s1 != s2 {
            let f1 = s1.and_then(|s| self.file_index_map.get(&s).copied()).unwrap_or(0) as i32;
            let f2 = s2.and_then(|s| self.file_index_map.get(&s).copied()).unwrap_or(0) as i32;
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
    pub fn new_type(&mut self, flags: TypeFlags, object_flags: ObjectFlags, data: TypeData) -> TypeId {
        self.type_count += 1;
        let id = self.types.alloc(Type {
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
        self.types.get_mut(id).id = id;
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
            let ty = self.types.get(non_widening_type);
            (ty.flags, ty.as_intrinsic_type().intrinsic_name.clone())
        };
        let t = self.new_intrinsic_type(flags, &intrinsic_name);
        self.types
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
        if let TypeData::Literal(d) = &mut self.types.get_mut(t).data {
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
        self.types.get_mut(t).symbol = symbol;
        t
    }

    /// `(c *Checker) newObjectType` (checker.go).
    pub fn new_object_type(&mut self, object_flags: ObjectFlags, symbol: Option<SymbolId>) -> TypeId {
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
        self.types.get_mut(t).symbol = symbol;
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
        self.types
            .get_mut(t)
            .object_flags
            .insert(ObjectFlags::MEMBERS_RESOLVED);
        let symbol = self.types.get(t).symbol;
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
        if let Some(data) = self.types.get_mut(t).data.as_structured_type_mut() {
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
        &self,
        members: &SymbolTable,
        container: Option<SymbolId>,
    ) -> Vec<SymbolId> {
        if members.is_empty() {
            return Vec::new();
        }
        let _ = container;
        unimplemented!("PORT(deferred): getNamedMembers' class/interface ordering lands with checker.go")
    }

    /// `(c *Checker) newTypeParameter` (checker.go).
    pub fn new_type_parameter(&mut self, symbol: Option<SymbolId>) -> TypeId {
        let t = self.new_type(
            TypeFlags::TYPE_PARAMETER,
            ObjectFlags::NONE,
            TypeData::TypeParameter(TypeParameter::default()),
        );
        self.types.get_mut(t).symbol = symbol;
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
            let ty = self.types.get(t);
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
    pub fn new_intersection_type(&mut self, object_flags: ObjectFlags, types: Vec<TypeId>) -> TypeId {
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
    pub fn new_index_type(&mut self, target: TypeId, index_flags: crate::types::IndexFlags) -> TypeId {
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
        self.types.get_mut(t).symbol = symbol;
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
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::FRESHABLE) {
            let ty = self.types.get(t);
            return ty.as_literal_type().regular_type.unwrap_or(t);
        }
        if flags.intersects(TypeFlags::UNION) {
            if let Some(regular) = self.types.get(t).as_union_type().regular_type {
                return regular;
            }
            let mapped = self.map_type(t, Rc::new(|c: &mut Checker, s: TypeId| {
                c.get_regular_type_of_literal_type(s)
            }));
            if let TypeData::Union(d) = &mut self.types.get_mut(t).data {
                d.regular_type = Some(mapped);
            }
            return mapped;
        }
        t
    }

    /// `(c *Checker) getFreshTypeOfLiteralType` (checker.go).
    pub fn get_fresh_type_of_literal_type(&mut self, t: TypeId) -> TypeId {
        if self.types.get(t).flags.intersects(TypeFlags::FRESHABLE) {
            let (flags, value, fresh_type) = {
                let ty = self.types.get(t);
                let d = ty.as_literal_type();
                (ty.flags, d.value.clone(), d.fresh_type)
            };
            if let Some(fresh) = fresh_type {
                return fresh;
            }
            let f = self.new_literal_type(flags, value, Some(t));
            let sym = self.types.get(t).symbol;
            self.types.get_mut(f).symbol = sym;
            if let TypeData::Literal(fd) = &mut self.types.get_mut(f).data {
                fd.fresh_type = Some(f);
            }
            if let TypeData::Literal(d) = &mut self.types.get_mut(t).data {
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
    pub fn try_create_type_reference(&mut self, target: TypeId, type_arguments: &[TypeId]) -> TypeId {
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
            .types
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
        let symbol = self.types.get(target).symbol;
        let propagating = self.get_propagating_flags_of_types(type_arguments, TypeFlags::NONE);
        let t = self.new_object_type(
            ObjectFlags::REFERENCE | object_flags | propagating,
            symbol,
        );
        if let TypeData::TypeReference(d) = &mut self.types.get_mut(t).data {
            d.object_type.target = Some(target);
            d.resolved_type_arguments = type_arguments.to_vec();
        }
        self.types
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
            let ty = self.types.get(source);
            let r = ty.as_type_reference();
            (
                ty.symbol,
                ty.object_flags,
                r.object_type.target,
                r.resolved_type_arguments.clone(),
            )
        };
        let t = self.new_object_type(ObjectFlags::REFERENCE, symbol);
        self.types.get_mut(t).object_flags = object_flags & !ObjectFlags::MEMBERS_RESOLVED;
        if let TypeData::TypeReference(d) = &mut self.types.get_mut(t).data {
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
            let meta_property_symbol =
                self.new_symbol_ex(ast::SymbolFlags::PROPERTY, "meta", ast::checkflags::CheckFlags::READONLY);
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

    /// `(c *Checker) getUnionType` (checker.go) — PORT(deferred): union
    /// creation/reduction machinery.
    pub fn get_union_type(&mut self, types: &[TypeId]) -> TypeId {
        let _ = types;
        unimplemented!("PORT(deferred): getUnionType lands with checker.go")
    }

    /// `(c *Checker) getTemplateLiteralType` (checker.go) — PORT(deferred).
    pub fn get_template_literal_type(&mut self, texts: &[String], types: &[TypeId]) -> TypeId {
        let _ = (texts, types);
        unimplemented!("PORT(deferred): getTemplateLiteralType lands with checker.go")
    }

    /// `(c *Checker) getTypeArguments` (checker.go) — PORT(deferred): needed
    /// by `checker_types::is_type_reference_with_generic_arguments`.
    pub fn get_type_arguments(&mut self, t: TypeId) -> Vec<TypeId> {
        let _ = t;
        unimplemented!("PORT(deferred): getTypeArguments lands with checker.go")
    }

    /// `(c *Checker) mapType` (checker.go) — PORT(deferred).
    pub fn map_type(&mut self, t: TypeId, f: Rc<dyn Fn(&mut Checker, TypeId) -> TypeId>) -> TypeId {
        let _ = (t, f);
        unimplemented!("PORT(deferred): mapType lands with checker.go")
    }

    /// `(c *Checker) getDeclaredTypeOfSymbol` (checker.go) — PORT(deferred).
    pub fn get_declared_type_of_symbol(&mut self, symbol: SymbolId) -> TypeId {
        let _ = symbol;
        unimplemented!("PORT(deferred): getDeclaredTypeOfSymbol lands with checker.go")
    }

    /// `(c *Checker) getAwaitedTypeEx` (checker.go) — PORT(deferred): the
    /// async `resolve_iteration_type` thunk routes here.
    pub fn get_awaited_type_ex(
        &mut self,
        t: TypeId,
        error_node: Option<NodeId>,
        message: Option<&'static tsc_diagnostics::Message>,
    ) -> TypeId {
        let _ = (t, error_node, message);
        unimplemented!("PORT(deferred): getAwaitedTypeEx lands with checker.go")
    }

    /// `(c *Checker) IsEmptyAnonymousObjectType` (checker.go) —
    /// PORT(deferred).
    pub fn is_empty_anonymous_object_type(&mut self, t: TypeId) -> bool {
        let _ = t;
        unimplemented!("PORT(deferred): IsEmptyAnonymousObjectType lands with checker.go")
    }

    /// `(c *Checker) couldContainTypeVariablesWorker` (checker.go) —
    /// PORT(deferred).
    pub fn could_contain_type_variables_worker(&mut self, t: TypeId) -> bool {
        let _ = t;
        unimplemented!("PORT(deferred): couldContainTypeVariablesWorker lands with checker.go")
    }

    /// `(c *Checker) isStringIndexSignatureOnlyTypeWorker` (checker.go) —
    /// PORT(deferred).
    pub fn is_string_index_signature_only_type_worker(&mut self, t: TypeId) -> bool {
        let _ = t;
        unimplemented!("PORT(deferred): isStringIndexSignatureOnlyTypeWorker lands with checker.go")
    }

    /// `(c *Checker) markNodeAssignmentsWorker` (flow.go) — PORT(deferred).
    pub fn mark_node_assignments_worker(&mut self, node: NodeId) -> bool {
        let _ = node;
        unimplemented!("PORT(deferred): markNodeAssignmentsWorker lands with flow.go")
    }

    /// `(c *Checker) compareTypesAssignableWorker` (relater.go) —
    /// PORT(deferred).
    pub fn compare_types_assignable_worker(
        &mut self,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
    ) -> crate::types::Ternary {
        let _ = (source, target, report_errors);
        unimplemented!("PORT(deferred): compareTypesAssignableWorker lands with relater.go")
    }

    /// `(c *Checker) getUniqueLiteralTypeForTypeParameter` (checker.go).
    pub fn get_unique_literal_type_for_type_parameter(&mut self, t: TypeId) -> TypeId {
        if self.types.get(t).flags.intersects(TypeFlags::TYPE_PARAMETER) {
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
        if self.types.get(t).flags.intersects(TypeFlags::TYPE_PARAMETER) {
            return self.get_restrictive_type_parameter(t);
        }
        t
    }

    /// `(c *Checker) getRestrictiveTypeParameter` (checker.go) —
    /// PORT(deferred).
    pub fn get_restrictive_type_parameter(&mut self, t: TypeId) -> TypeId {
        let _ = t;
        unimplemented!("PORT(deferred): getRestrictiveTypeParameter lands with checker.go")
    }

    /// `(c *Checker) permissiveMapperWorker` (checker.go).
    pub fn permissive_mapper_worker(&mut self, t: TypeId) -> TypeId {
        if self.types.get(t).flags.intersects(TypeFlags::TYPE_PARAMETER) {
            return self.wildcard_type;
        }
        t
    }
}
