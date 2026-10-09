// Ported from tsc/internal/checker/checker.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the auxiliary (non-`Checker`)
// declarations of checker.go plus the `Program`/`Host` interfaces.
//
// Scope: every `type` declaration in checker.go outside `type Checker
// struct` and `func NewChecker` lives here (or in the sibling files noted
// below), preserving Go declaration order. `CheckMode` and the
// `InferenceFlags`/`InferenceContext`/`InferenceInfo`/`InferencePriority`/
// `IntraExpressionInferenceSite`/`InferenceContextInfo`/`WideningKind`/
// `EnumLiteralKey`/`RecursionId` types were already ported for the
// foundation phase and stay in `checker_core.rs`.
//
// Sibling-owner files introduced for types declared in other Go files that
// `Checker` fields reference:
//   - `relater.rs`    — relater.go (`Relation`, `Relater`, `ErrorChain`, ...)
//   - `flow.rs`       — flow.go (`FlowType`, `SharedFlow`, `FlowState`, ...)
//   - `inference.rs`  — inference.go (`InferenceKey`, `InferenceState`)
//   - `emitresolver.rs` — emitresolver.go (`EmitResolverLinks` + link structs)
//   - `symbolaccessibility.rs` — symbolaccessibility.go (`SymbolTableId`,
//     `ExternalModuleContainerIndex`)
//   - `nodebuilder.rs` — nodebuilder.go (`NodeBuilder`, `VerbosityContext`)
//
// Pointer conversions: `*Type` → `TypeId`, `*Signature` → `SignatureId`,
// `*TypeMapper` → `TypeMapperId`, `*IndexInfo` → `IndexInfoId`,
// `*ast.Node`/`ast.NodeId` → `NodeId`, `*ast.Symbol`/`ast.SymbolId` →
// `SymbolId`, `*ast.FlowNode` → `FlowNodeId`.
//
// Function-typed fields: Go closures capture the checker; here every thunk
// takes `&mut Checker` explicitly and is stored behind `Rc` so a caller can
// clone the `Rc`, drop the field borrow, then invoke with `&mut self` —
// the same pattern `TypeMapperArena` uses for `FunctionTypeMapper`.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::LazyLock;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, FlowNodeId, HasFileName, NodeId, SymbolId};
use tsc_core::options_generated::CompilerOptions;
use tsc_module::{ModeAwareCache, ResolvedModule};
use tsc_tsoptions::parsedcommandline::{ParsedCommandLine, SourceOutputAndProjectReference};
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};
use xxhash_rust::xxh3::xxh3_128;

use crate::checker_core::{CacheHashKey, CheckMode, Checker};
use crate::flagdef::flag_type;
use crate::types::{
    ElementFlags, SignatureId, TupleElementInfo, TypeAlias, TypeArena, TypeFlags, TypeId,
};

// TypeSystemEntity / TypeSystemPropertyName / TypeResolution

/// `type TypeSystemEntity any` (checker.go) — the entity whose resolution is
/// tracked by `pushTypeResolution`. Go stores `*ast.Symbol | *Type |
// *Signature | *ast.Node` in an `any`; the port is a kind-tagged union so
/// resolution entries stay `Eq + Hash` like Go's pointer key.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TypeSystemEntity {
    /// `*ast.Node` — a declaration.
    Node(NodeId),
    /// `*ast.Symbol`.
    Symbol(SymbolId),
    /// `*Type`.
    Type(TypeId),
    /// `*Signature`.
    Signature(SignatureId),
}

impl Default for TypeSystemEntity {
    /// Go's zero value is `nil`; `NodeId::NONE` is the port's nil node.
    fn default() -> Self {
        TypeSystemEntity::Node(NodeId::NONE)
    }
}

/// `type TypeSystemPropertyName int32` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum TypeSystemPropertyName {
    /// `TypeSystemPropertyNameType`
    #[default]
    Type = 0,
    /// `TypeSystemPropertyNameResolvedBaseConstructorType`
    ResolvedBaseConstructorType = 1,
    /// `TypeSystemPropertyNameDeclaredType`
    DeclaredType = 2,
    /// `TypeSystemPropertyNameResolvedReturnType`
    ResolvedReturnType = 3,
    /// `TypeSystemPropertyNameResolvedBaseConstraint`
    ResolvedBaseConstraint = 4,
    /// `TypeSystemPropertyNameResolvedTypeArguments`
    ResolvedTypeArguments = 5,
    /// `TypeSystemPropertyNameResolvedBaseTypes`
    ResolvedBaseTypes = 6,
    /// `TypeSystemPropertyNameWriteType`
    WriteType = 7,
    /// `TypeSystemPropertyNameInitializerIsUndefined`
    InitializerIsUndefined = 8,
    /// `TypeSystemPropertyNameAliasTarget`
    AliasTarget = 9,
}

/// `type TypeResolution struct` (checker.go).
#[derive(Clone, Copy, Default)]
pub struct TypeResolution {
    /// `target`.
    pub target: TypeSystemEntity,
    /// `propertyName`.
    pub property_name: TypeSystemPropertyName,
    /// `result`.
    pub result: bool,
}

// ContextualInfo

/// `type ContextualInfo struct` (checker.go).
#[derive(Clone, Copy, Default)]
pub struct ContextualInfo {
    /// `node`.
    pub node: Option<NodeId>,
    /// `t`.
    pub t: Option<TypeId>,
    /// `isCache`.
    pub is_cache: bool,
}

// EnumRelationKey

/// `type EnumRelationKey struct` (checker.go). `ast.SymbolId` is already the
/// port's `SymbolId`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct EnumRelationKey {
    /// `sourceId`.
    pub source_id: SymbolId,
    /// `targetId`.
    pub target_id: SymbolId,
}

// NumberLiteralKey — `map[jsnum.Number]*Type` key (checker.go
// `numberLiteralTypes`).

/// `map[jsnum.Number]*Type` key. Go float64 map keys compare with `==`
/// (`-0 == +0`) and hash by bit pattern; `NaN` keys never match — the Go
/// checker keeps `nanType` separately for exactly that reason.
#[derive(Clone, Copy, Debug)]
pub struct NumberLiteralKey(pub tsc_jsnum::Number);

impl PartialEq for NumberLiteralKey {
    /// Go `n == m` on float64 keys.
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl Eq for NumberLiteralKey {}

impl std::hash::Hash for NumberLiteralKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        // `-0` and `+0` must hash identically since `-0 == +0` in Go.
        state.write_u64(if self.0.0 == 0.0 {
            0
        } else {
            self.0.0.to_bits()
        });
    }
}

// CachedTypeKind / CachedTypeKey

/// `type CachedTypeKind int32` (checker.go — Go names it `CachedTypeKind`
/// under a `// TypeCacheKind` comment).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum CachedTypeKind {
    /// `CachedTypeKindLiteralUnionBaseType`
    #[default]
    LiteralUnionBaseType = 0,
    /// `CachedTypeKindIndexType`
    IndexType = 1,
    /// `CachedTypeKindStringIndexType`
    StringIndexType = 2,
    /// `CachedTypeKindEquivalentBaseType`
    EquivalentBaseType = 3,
    /// `CachedTypeKindApparentType`
    ApparentType = 4,
    /// `CachedTypeKindAwaitedType`
    AwaitedType = 5,
    /// `CachedTypeKindEvolvingArrayType`
    EvolvingArrayType = 6,
    /// `CachedTypeKindArrayLiteralType`
    ArrayLiteralType = 7,
    /// `CachedTypeKindPermissiveInstantiation`
    PermissiveInstantiation = 8,
    /// `CachedTypeKindRestrictiveInstantiation`
    RestrictiveInstantiation = 9,
    /// `CachedTypeKindRestrictiveTypeParameter`
    RestrictiveTypeParameter = 10,
    /// `CachedTypeKindIndexedAccessForReading`
    IndexedAccessForReading = 11,
    /// `CachedTypeKindIndexedAccessForWriting`
    IndexedAccessForWriting = 12,
    /// `CachedTypeKindWidened`
    Widened = 13,
    /// `CachedTypeKindRegularObjectLiteral`
    RegularObjectLiteral = 14,
    /// `CachedTypeKindPromisedTypeOfPromise`
    PromisedTypeOfPromise = 15,
    /// `CachedTypeKindDefaultOnlyType`
    DefaultOnlyType = 16,
    /// `CachedTypeKindSyntheticType`
    SyntheticType = 17,
    /// `CachedTypeKindDecoratorContext`
    DecoratorContext = 18,
    /// `CachedTypeKindDecoratorContextStatic`
    DecoratorContextStatic = 19,
    /// `CachedTypeKindDecoratorContextPrivate`
    DecoratorContextPrivate = 20,
    /// `CachedTypeKindDecoratorContextPrivateStatic`
    DecoratorContextPrivateStatic = 21,
}

/// `type CachedTypeKey struct` (checker.go). `typeId TypeId` is already the
/// port's `TypeId`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct CachedTypeKey {
    /// `kind`.
    pub kind: CachedTypeKind,
    /// `typeId`.
    pub type_id: TypeId,
}

// NarrowedTypeKey

/// `type NarrowedTypeKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NarrowedTypeKey {
    /// `t`.
    pub t: TypeId,
    /// `candidate`.
    pub candidate: TypeId,
    /// `assumeTrue`.
    pub assume_true: bool,
    /// `checkDerived`.
    pub check_derived: bool,
}

// UnionOfUnionKey

/// `type UnionOfUnionKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct UnionOfUnionKey {
    /// `id1`.
    pub id1: TypeId,
    /// `id2`.
    pub id2: TypeId,
    /// `r`.
    pub r: UnionReduction,
    /// `a`.
    pub a: CacheHashKey,
}

// CachedSignatureKey + SignatureKey* sentinels

/// `type CachedSignatureKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct CachedSignatureKey {
    /// `sig`.
    pub sig: Option<SignatureId>,
    /// `key` — type list key or one of the special keys below.
    pub key: CacheHashKey,
}

/// `xxh3.Hash128(b)` — Go's `xxh3.Uint128` is `{Lo, Hi}` uint64 halves;
/// `xxhash_rust` returns the same digest as a `u128`.
pub fn hash128(bytes: &[u8]) -> CacheHashKey {
    let h = xxh3_128(bytes);
    ast::Uint128 {
        lo: h as u64,
        hi: (h >> 64) as u64,
    }
}

/// `xxh3.HashString128(s)` — same digest as `hash128` on the string's bytes.
pub fn hash_string_128(s: &str) -> CacheHashKey {
    hash128(s.as_bytes())
}

/// `var SignatureKeyErased = CacheHashKey(xxh3.HashString128("-"))`.
pub static SIGNATURE_KEY_ERASED: LazyLock<CacheHashKey> = LazyLock::new(|| hash_string_128("-"));
/// `var SignatureKeyCanonical = CacheHashKey(xxh3.HashString128("*"))`.
pub static SIGNATURE_KEY_CANONICAL: LazyLock<CacheHashKey> = LazyLock::new(|| hash_string_128("*"));
/// `var SignatureKeyBase = CacheHashKey(xxh3.HashString128("#"))`.
pub static SIGNATURE_KEY_BASE: LazyLock<CacheHashKey> = LazyLock::new(|| hash_string_128("#"));
/// `var SignatureKeyInner = CacheHashKey(xxh3.HashString128("<"))`.
pub static SIGNATURE_KEY_INNER: LazyLock<CacheHashKey> = LazyLock::new(|| hash_string_128("<"));
/// `var SignatureKeyOuter = CacheHashKey(xxh3.HashString128(">"))`.
pub static SIGNATURE_KEY_OUTER: LazyLock<CacheHashKey> = LazyLock::new(|| hash_string_128(">"));

// StringMappingKey

/// `type StringMappingKey struct` (checker.go). `s` is never nil at key
/// construction sites, so it stays a plain `SymbolId`.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct StringMappingKey {
    /// `s`.
    pub s: SymbolId,
    /// `t`.
    pub t: TypeId,
}

// AssignmentReducedKey

/// `type AssignmentReducedKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct AssignmentReducedKey {
    /// `id1`.
    pub id1: TypeId,
    /// `id2`.
    pub id2: TypeId,
}

// DiscriminatedContextualTypeKey

/// `type DiscriminatedContextualTypeKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct DiscriminatedContextualTypeKey {
    /// `nodeId`.
    pub node_id: NodeId,
    /// `typeId`.
    pub type_id: TypeId,
}

// InstantiationExpressionKey

/// `type InstantiationExpressionKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstantiationExpressionKey {
    /// `nodeId`.
    pub node_id: NodeId,
    /// `typeId`.
    pub type_id: TypeId,
}

// SubstitutionTypeKey

/// `type SubstitutionTypeKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct SubstitutionTypeKey {
    /// `baseId`.
    pub base_id: TypeId,
    /// `constraintId`.
    pub constraint_id: TypeId,
}

// ReverseMappedTypeKey

/// `type ReverseMappedTypeKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReverseMappedTypeKey {
    /// `sourceId`.
    pub source_id: TypeId,
    /// `targetId`.
    pub target_id: TypeId,
    /// `constraintId`.
    pub constraint_id: TypeId,
}

// IterationTypesKey

/// `type IterationTypesKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct IterationTypesKey {
    /// `typeId`.
    pub type_id: TypeId,
    /// `use`.
    pub use_: IterationUse,
}

// PropertiesTypesKey

/// `type PropertiesTypesKey struct` (checker.go).
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct PropertiesTypesKey {
    /// `typeId`.
    pub type_id: TypeId,
    /// `include`.
    pub include: TypeFlags,
    /// `includeOrigin`.
    pub include_origin: bool,
}

// NonExistentPropertyKey

/// `type NonExistentPropertyKey struct` (checker.go). `propNode` and
/// `containingType` are non-nil at the only insertion site, so they stay
/// plain ids.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct NonExistentPropertyKey {
    /// `propNode`.
    pub prop_node: NodeId,
    /// `containingType`.
    pub containing_type: TypeId,
    /// `isUncheckedJS`.
    pub is_unchecked_js: bool,
}

// FlowLoopKey / FlowLoopInfo

/// `type FlowLoopKey struct` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct FlowLoopKey {
    /// `flowNode`.
    pub flow_node: FlowNodeId,
    /// `refKey`.
    pub ref_key: CacheHashKey,
}

/// `type FlowLoopInfo struct` (checker.go).
#[derive(Default)]
pub struct FlowLoopInfo {
    /// `key`.
    pub key: FlowLoopKey,
    /// `types`.
    pub types: Vec<TypeId>,
}

// DeclarationMeaning

flag_type! {
    /// `type DeclarationMeaning uint32` (checker.go).
    pub struct DeclarationMeaning(pub u32);
}

impl DeclarationMeaning {
    /// `DeclarationMeaningGetAccessor`.
    pub const GET_ACCESSOR: DeclarationMeaning = DeclarationMeaning(1 << 0);
    /// `DeclarationMeaningSetAccessor`.
    pub const SET_ACCESSOR: DeclarationMeaning = DeclarationMeaning(1 << 1);
    /// `DeclarationMeaningPropertyAssignment`.
    pub const PROPERTY_ASSIGNMENT: DeclarationMeaning = DeclarationMeaning(1 << 2);
    /// `DeclarationMeaningMethod`.
    pub const METHOD: DeclarationMeaning = DeclarationMeaning(1 << 3);
    /// `DeclarationMeaningPrivateStatic`.
    pub const PRIVATE_STATIC: DeclarationMeaning = DeclarationMeaning(1 << 4);
    /// `DeclarationMeaningGetOrSetAccessor`.
    pub const GET_OR_SET_ACCESSOR: DeclarationMeaning =
        DeclarationMeaning(Self::GET_ACCESSOR.0 | Self::SET_ACCESSOR.0);
    /// `DeclarationMeaningPropertyAssignmentOrMethod`.
    pub const PROPERTY_ASSIGNMENT_OR_METHOD: DeclarationMeaning =
        DeclarationMeaning(Self::PROPERTY_ASSIGNMENT.0 | Self::METHOD.0);
}

// DeclarationSpaces

flag_type! {
    /// `type DeclarationSpaces int32` (checker.go).
    pub struct DeclarationSpaces(pub i32);
}

impl DeclarationSpaces {
    /// `DeclarationSpacesExportValue`.
    pub const EXPORT_VALUE: DeclarationSpaces = DeclarationSpaces(1 << 0);
    /// `DeclarationSpacesExportType`.
    pub const EXPORT_TYPE: DeclarationSpaces = DeclarationSpaces(1 << 1);
    /// `DeclarationSpacesExportNamespace`.
    pub const EXPORT_NAMESPACE: DeclarationSpaces = DeclarationSpaces(1 << 2);
}

// IntrinsicTypeKind

/// `type IntrinsicTypeKind int32` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum IntrinsicTypeKind {
    /// `IntrinsicTypeKindUnknown`
    #[default]
    Unknown = 0,
    /// `IntrinsicTypeKindUppercase`
    Uppercase = 1,
    /// `IntrinsicTypeKindLowercase`
    Lowercase = 2,
    /// `IntrinsicTypeKindCapitalize`
    Capitalize = 3,
    /// `IntrinsicTypeKindUncapitalize`
    Uncapitalize = 4,
    /// `IntrinsicTypeKindNoInfer`
    NoInfer = 5,
}

/// `var intrinsicTypeKinds map[string]IntrinsicTypeKind` (checker.go).
pub fn intrinsic_type_kind(name: &str) -> Option<IntrinsicTypeKind> {
    match name {
        "Uppercase" => Some(IntrinsicTypeKind::Uppercase),
        "Lowercase" => Some(IntrinsicTypeKind::Lowercase),
        "Capitalize" => Some(IntrinsicTypeKind::Capitalize),
        "Uncapitalize" => Some(IntrinsicTypeKind::Uncapitalize),
        "NoInfer" => Some(IntrinsicTypeKind::NoInfer),
        _ => None,
    }
}

// MappedTypeModifiers

flag_type! {
    /// `type MappedTypeModifiers uint32` (checker.go).
    pub struct MappedTypeModifiers(pub u32);
}

impl MappedTypeModifiers {
    /// `MappedTypeModifiersIncludeReadonly`.
    pub const INCLUDE_READONLY: MappedTypeModifiers = MappedTypeModifiers(1 << 0);
    /// `MappedTypeModifiersExcludeReadonly`.
    pub const EXCLUDE_READONLY: MappedTypeModifiers = MappedTypeModifiers(1 << 1);
    /// `MappedTypeModifiersIncludeOptional`.
    pub const INCLUDE_OPTIONAL: MappedTypeModifiers = MappedTypeModifiers(1 << 2);
    /// `MappedTypeModifiersExcludeOptional`.
    pub const EXCLUDE_OPTIONAL: MappedTypeModifiers = MappedTypeModifiers(1 << 3);
}

// MappedTypeNameTypeKind

/// `type MappedTypeNameTypeKind int32` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum MappedTypeNameTypeKind {
    /// `MappedTypeNameTypeKindNone`
    #[default]
    None = 0,
    /// `MappedTypeNameTypeKindFiltering`
    Filtering = 1,
    /// `MappedTypeNameTypeKindRemapping`
    Remapping = 2,
}

// ReferenceHint

/// `type ReferenceHint int32` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum ReferenceHint {
    /// `ReferenceHintUnspecified`
    #[default]
    Unspecified = 0,
    /// `ReferenceHintIdentifier`
    Identifier = 1,
    /// `ReferenceHintProperty`
    Property = 2,
    /// `ReferenceHintExportAssignment`
    ExportAssignment = 3,
    /// `ReferenceHintJsx`
    Jsx = 4,
    /// `ReferenceHintExportImportEquals`
    ExportImportEquals = 5,
    /// `ReferenceHintExportSpecifier`
    ExportSpecifier = 6,
    /// `ReferenceHintDecorator`
    Decorator = 7,
}

// TypeFacts

flag_type! {
    /// `type TypeFacts uint32` (checker.go).
    pub struct TypeFacts(pub u32);
}

impl TypeFacts {
    /// `TypeFactsTypeofEQString`.
    pub const TYPEOF_EQ_STRING: TypeFacts = TypeFacts(1 << 0);
    /// `TypeFactsTypeofEQNumber`.
    pub const TYPEOF_EQ_NUMBER: TypeFacts = TypeFacts(1 << 1);
    /// `TypeFactsTypeofEQBigInt`.
    pub const TYPEOF_EQ_BIG_INT: TypeFacts = TypeFacts(1 << 2);
    /// `TypeFactsTypeofEQBoolean`.
    pub const TYPEOF_EQ_BOOLEAN: TypeFacts = TypeFacts(1 << 3);
    /// `TypeFactsTypeofEQSymbol`.
    pub const TYPEOF_EQ_SYMBOL: TypeFacts = TypeFacts(1 << 4);
    /// `TypeFactsTypeofEQObject`.
    pub const TYPEOF_EQ_OBJECT: TypeFacts = TypeFacts(1 << 5);
    /// `TypeFactsTypeofEQFunction`.
    pub const TYPEOF_EQ_FUNCTION: TypeFacts = TypeFacts(1 << 6);
    /// `TypeFactsTypeofEQHostObject`.
    pub const TYPEOF_EQ_HOST_OBJECT: TypeFacts = TypeFacts(1 << 7);
    /// `TypeFactsTypeofNEString`.
    pub const TYPEOF_NE_STRING: TypeFacts = TypeFacts(1 << 8);
    /// `TypeFactsTypeofNENumber`.
    pub const TYPEOF_NE_NUMBER: TypeFacts = TypeFacts(1 << 9);
    /// `TypeFactsTypeofNEBigInt`.
    pub const TYPEOF_NE_BIG_INT: TypeFacts = TypeFacts(1 << 10);
    /// `TypeFactsTypeofNEBoolean`.
    pub const TYPEOF_NE_BOOLEAN: TypeFacts = TypeFacts(1 << 11);
    /// `TypeFactsTypeofNESymbol`.
    pub const TYPEOF_NE_SYMBOL: TypeFacts = TypeFacts(1 << 12);
    /// `TypeFactsTypeofNEObject`.
    pub const TYPEOF_NE_OBJECT: TypeFacts = TypeFacts(1 << 13);
    /// `TypeFactsTypeofNEFunction`.
    pub const TYPEOF_NE_FUNCTION: TypeFacts = TypeFacts(1 << 14);
    /// `TypeFactsTypeofNEHostObject`.
    pub const TYPEOF_NE_HOST_OBJECT: TypeFacts = TypeFacts(1 << 15);
    /// `TypeFactsEQUndefined`.
    pub const EQ_UNDEFINED: TypeFacts = TypeFacts(1 << 16);
    /// `TypeFactsEQNull`.
    pub const EQ_NULL: TypeFacts = TypeFacts(1 << 17);
    /// `TypeFactsEQUndefinedOrNull`.
    pub const EQ_UNDEFINED_OR_NULL: TypeFacts = TypeFacts(1 << 18);
    /// `TypeFactsNEUndefined`.
    pub const NE_UNDEFINED: TypeFacts = TypeFacts(1 << 19);
    /// `TypeFactsNENull`.
    pub const NE_NULL: TypeFacts = TypeFacts(1 << 20);
    /// `TypeFactsNEUndefinedOrNull`.
    pub const NE_UNDEFINED_OR_NULL: TypeFacts = TypeFacts(1 << 21);
    /// `TypeFactsTruthy`.
    pub const TRUTHY: TypeFacts = TypeFacts(1 << 22);
    /// `TypeFactsFalsy`.
    pub const FALSY: TypeFacts = TypeFacts(1 << 23);
    /// `TypeFactsIsUndefined`.
    pub const IS_UNDEFINED: TypeFacts = TypeFacts(1 << 24);
    /// `TypeFactsIsNull`.
    pub const IS_NULL: TypeFacts = TypeFacts(1 << 25);
    /// `TypeFactsIsUndefinedOrNull`.
    pub const IS_UNDEFINED_OR_NULL: TypeFacts = TypeFacts(Self::IS_UNDEFINED.0 | Self::IS_NULL.0);
    /// `TypeFactsAll`.
    pub const ALL: TypeFacts = TypeFacts((1 << 27) - 1);

    // The following members encode facts about particular kinds of types for use in the getTypeFacts function.
    // The presence of a particular fact means that the given test is true for some (and possibly all) values
    // of that kind of type.

    /// `TypeFactsBaseStringStrictFacts`.
    pub const BASE_STRING_STRICT_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_EQ_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_OBJECT.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::TYPEOF_NE_HOST_OBJECT.0
            | Self::NE_UNDEFINED.0
            | Self::NE_NULL.0
            | Self::NE_UNDEFINED_OR_NULL.0,
    );
    /// `TypeFactsBaseStringFacts`.
    pub const BASE_STRING_FACTS: TypeFacts = TypeFacts(
        Self::BASE_STRING_STRICT_FACTS.0
            | Self::EQ_UNDEFINED.0
            | Self::EQ_NULL.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::FALSY.0,
    );
    /// `TypeFactsStringStrictFacts`.
    pub const STRING_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_STRING_STRICT_FACTS.0 | Self::TRUTHY.0 | Self::FALSY.0);
    /// `TypeFactsStringFacts`.
    pub const STRING_FACTS: TypeFacts = TypeFacts(Self::BASE_STRING_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsEmptyStringStrictFacts`.
    pub const EMPTY_STRING_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_STRING_STRICT_FACTS.0 | Self::FALSY.0);
    /// `TypeFactsEmptyStringFacts`.
    pub const EMPTY_STRING_FACTS: TypeFacts = Self::BASE_STRING_FACTS;
    /// `TypeFactsNonEmptyStringStrictFacts`.
    pub const NON_EMPTY_STRING_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_STRING_STRICT_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsNonEmptyStringFacts`.
    pub const NON_EMPTY_STRING_FACTS: TypeFacts =
        TypeFacts(Self::BASE_STRING_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsBaseNumberStrictFacts`.
    pub const BASE_NUMBER_STRICT_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_EQ_NUMBER.0
            | Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_OBJECT.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::TYPEOF_NE_HOST_OBJECT.0
            | Self::NE_UNDEFINED.0
            | Self::NE_NULL.0
            | Self::NE_UNDEFINED_OR_NULL.0,
    );
    /// `TypeFactsBaseNumberFacts`.
    pub const BASE_NUMBER_FACTS: TypeFacts = TypeFacts(
        Self::BASE_NUMBER_STRICT_FACTS.0
            | Self::EQ_UNDEFINED.0
            | Self::EQ_NULL.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::FALSY.0,
    );
    /// `TypeFactsNumberStrictFacts`.
    pub const NUMBER_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_NUMBER_STRICT_FACTS.0 | Self::TRUTHY.0 | Self::FALSY.0);
    /// `TypeFactsNumberFacts`.
    pub const NUMBER_FACTS: TypeFacts = TypeFacts(Self::BASE_NUMBER_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsZeroNumberStrictFacts`.
    pub const ZERO_NUMBER_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_NUMBER_STRICT_FACTS.0 | Self::FALSY.0);
    /// `TypeFactsZeroNumberFacts`.
    pub const ZERO_NUMBER_FACTS: TypeFacts = Self::BASE_NUMBER_FACTS;
    /// `TypeFactsNonZeroNumberStrictFacts`.
    pub const NON_ZERO_NUMBER_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_NUMBER_STRICT_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsNonZeroNumberFacts`.
    pub const NON_ZERO_NUMBER_FACTS: TypeFacts =
        TypeFacts(Self::BASE_NUMBER_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsBaseBigIntStrictFacts`.
    pub const BASE_BIG_INT_STRICT_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_EQ_BIG_INT.0
            | Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_OBJECT.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::TYPEOF_NE_HOST_OBJECT.0
            | Self::NE_UNDEFINED.0
            | Self::NE_NULL.0
            | Self::NE_UNDEFINED_OR_NULL.0,
    );
    /// `TypeFactsBaseBigIntFacts`.
    pub const BASE_BIG_INT_FACTS: TypeFacts = TypeFacts(
        Self::BASE_BIG_INT_STRICT_FACTS.0
            | Self::EQ_UNDEFINED.0
            | Self::EQ_NULL.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::FALSY.0,
    );
    /// `TypeFactsBigIntStrictFacts`.
    pub const BIG_INT_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_BIG_INT_STRICT_FACTS.0 | Self::TRUTHY.0 | Self::FALSY.0);
    /// `TypeFactsBigIntFacts`.
    pub const BIG_INT_FACTS: TypeFacts = TypeFacts(Self::BASE_BIG_INT_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsZeroBigIntStrictFacts`.
    pub const ZERO_BIG_INT_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_BIG_INT_STRICT_FACTS.0 | Self::FALSY.0);
    /// `TypeFactsZeroBigIntFacts`.
    pub const ZERO_BIG_INT_FACTS: TypeFacts = Self::BASE_BIG_INT_FACTS;
    /// `TypeFactsNonZeroBigIntStrictFacts`.
    pub const NON_ZERO_BIG_INT_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_BIG_INT_STRICT_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsNonZeroBigIntFacts`.
    pub const NON_ZERO_BIG_INT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_BIG_INT_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsBaseBooleanStrictFacts`.
    pub const BASE_BOOLEAN_STRICT_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_EQ_BOOLEAN.0
            | Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_OBJECT.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::TYPEOF_NE_HOST_OBJECT.0
            | Self::NE_UNDEFINED.0
            | Self::NE_NULL.0
            | Self::NE_UNDEFINED_OR_NULL.0,
    );
    /// `TypeFactsBaseBooleanFacts`.
    pub const BASE_BOOLEAN_FACTS: TypeFacts = TypeFacts(
        Self::BASE_BOOLEAN_STRICT_FACTS.0
            | Self::EQ_UNDEFINED.0
            | Self::EQ_NULL.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::FALSY.0,
    );
    /// `TypeFactsBooleanStrictFacts`.
    pub const BOOLEAN_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_BOOLEAN_STRICT_FACTS.0 | Self::TRUTHY.0 | Self::FALSY.0);
    /// `TypeFactsBooleanFacts`.
    pub const BOOLEAN_FACTS: TypeFacts = TypeFacts(Self::BASE_BOOLEAN_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsFalseStrictFacts`.
    pub const FALSE_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_BOOLEAN_STRICT_FACTS.0 | Self::FALSY.0);
    /// `TypeFactsFalseFacts`.
    pub const FALSE_FACTS: TypeFacts = Self::BASE_BOOLEAN_FACTS;
    /// `TypeFactsTrueStrictFacts`.
    pub const TRUE_STRICT_FACTS: TypeFacts =
        TypeFacts(Self::BASE_BOOLEAN_STRICT_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsTrueFacts`.
    pub const TRUE_FACTS: TypeFacts = TypeFacts(Self::BASE_BOOLEAN_FACTS.0 | Self::TRUTHY.0);
    /// `TypeFactsSymbolStrictFacts`.
    pub const SYMBOL_STRICT_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_EQ_SYMBOL.0
            | Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_OBJECT.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::NE_UNDEFINED.0
            | Self::NE_NULL.0
            | Self::NE_UNDEFINED_OR_NULL.0
            | Self::TRUTHY.0,
    );
    /// `TypeFactsSymbolFacts`.
    pub const SYMBOL_FACTS: TypeFacts = TypeFacts(
        Self::SYMBOL_STRICT_FACTS.0
            | Self::EQ_UNDEFINED.0
            | Self::EQ_NULL.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::FALSY.0,
    );
    /// `TypeFactsObjectStrictFacts`.
    pub const OBJECT_STRICT_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_EQ_OBJECT.0
            | Self::TYPEOF_EQ_HOST_OBJECT.0
            | Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::NE_UNDEFINED.0
            | Self::NE_NULL.0
            | Self::NE_UNDEFINED_OR_NULL.0
            | Self::TRUTHY.0,
    );
    /// `TypeFactsObjectFacts`.
    pub const OBJECT_FACTS: TypeFacts = TypeFacts(
        Self::OBJECT_STRICT_FACTS.0
            | Self::EQ_UNDEFINED.0
            | Self::EQ_NULL.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::FALSY.0,
    );
    /// `TypeFactsFunctionStrictFacts`.
    pub const FUNCTION_STRICT_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_EQ_FUNCTION.0
            | Self::TYPEOF_EQ_HOST_OBJECT.0
            | Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_OBJECT.0
            | Self::NE_UNDEFINED.0
            | Self::NE_NULL.0
            | Self::NE_UNDEFINED_OR_NULL.0
            | Self::TRUTHY.0,
    );
    /// `TypeFactsFunctionFacts`.
    pub const FUNCTION_FACTS: TypeFacts = TypeFacts(
        Self::FUNCTION_STRICT_FACTS.0
            | Self::EQ_UNDEFINED.0
            | Self::EQ_NULL.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::FALSY.0,
    );
    /// `TypeFactsVoidFacts`.
    pub const VOID_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_OBJECT.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::TYPEOF_NE_HOST_OBJECT.0
            | Self::EQ_UNDEFINED.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::NE_NULL.0
            | Self::FALSY.0,
    );
    /// `TypeFactsUndefinedFacts`.
    pub const UNDEFINED_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_OBJECT.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::TYPEOF_NE_HOST_OBJECT.0
            | Self::EQ_UNDEFINED.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::NE_NULL.0
            | Self::FALSY.0
            | Self::IS_UNDEFINED.0,
    );
    /// `TypeFactsNullFacts`.
    pub const NULL_FACTS: TypeFacts = TypeFacts(
        Self::TYPEOF_EQ_OBJECT.0
            | Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::TYPEOF_NE_HOST_OBJECT.0
            | Self::EQ_NULL.0
            | Self::EQ_UNDEFINED_OR_NULL.0
            | Self::NE_UNDEFINED.0
            | Self::FALSY.0
            | Self::IS_NULL.0,
    );
    /// `TypeFactsEmptyObjectStrictFacts`.
    pub const EMPTY_OBJECT_STRICT_FACTS: TypeFacts = TypeFacts(
        Self::ALL.0
            & !(Self::EQ_UNDEFINED.0
                | Self::EQ_NULL.0
                | Self::EQ_UNDEFINED_OR_NULL.0
                | Self::IS_UNDEFINED_OR_NULL.0),
    );
    /// `TypeFactsEmptyObjectFacts`.
    pub const EMPTY_OBJECT_FACTS: TypeFacts =
        TypeFacts(Self::ALL.0 & !Self::IS_UNDEFINED_OR_NULL.0);
    /// `TypeFactsUnknownFacts`.
    pub const UNKNOWN_FACTS: TypeFacts = TypeFacts(Self::ALL.0 & !Self::IS_UNDEFINED_OR_NULL.0);
    /// `TypeFactsAllTypeofNE`.
    pub const ALL_TYPEOF_NE: TypeFacts = TypeFacts(
        Self::TYPEOF_NE_STRING.0
            | Self::TYPEOF_NE_NUMBER.0
            | Self::TYPEOF_NE_BIG_INT.0
            | Self::TYPEOF_NE_BOOLEAN.0
            | Self::TYPEOF_NE_SYMBOL.0
            | Self::TYPEOF_NE_OBJECT.0
            | Self::TYPEOF_NE_FUNCTION.0
            | Self::NE_UNDEFINED.0,
    );

    // Masks

    /// `TypeFactsOrFactsMask`.
    pub const OR_FACTS_MASK: TypeFacts =
        TypeFacts(Self::TYPEOF_EQ_FUNCTION.0 | Self::TYPEOF_NE_OBJECT.0);
    /// `TypeFactsAndFactsMask`.
    pub const AND_FACTS_MASK: TypeFacts = TypeFacts(Self::ALL.0 & !Self::OR_FACTS_MASK.0);
}

// IterationUse

flag_type! {
    /// `type IterationUse uint32` (checker.go).
    pub struct IterationUse(pub u32);
}

impl IterationUse {
    /// `IterationUseAllowsSyncIterablesFlag`.
    pub const ALLOWS_SYNC_ITERABLES_FLAG: IterationUse = IterationUse(1 << 0);
    /// `IterationUseAllowsAsyncIterablesFlag`.
    pub const ALLOWS_ASYNC_ITERABLES_FLAG: IterationUse = IterationUse(1 << 1);
    /// `IterationUseAllowsStringInputFlag`.
    pub const ALLOWS_STRING_INPUT_FLAG: IterationUse = IterationUse(1 << 2);
    /// `IterationUseForOfFlag`.
    pub const FOR_OF_FLAG: IterationUse = IterationUse(1 << 3);
    /// `IterationUseYieldStarFlag`.
    pub const YIELD_STAR_FLAG: IterationUse = IterationUse(1 << 4);
    /// `IterationUseSpreadFlag`.
    pub const SPREAD_FLAG: IterationUse = IterationUse(1 << 5);
    /// `IterationUseDestructuringFlag`.
    pub const DESTRUCTURING_FLAG: IterationUse = IterationUse(1 << 6);
    /// `IterationUsePossiblyOutOfBounds`.
    pub const POSSIBLY_OUT_OF_BOUNDS: IterationUse = IterationUse(1 << 7);
    /// `IterationUseElement` — spread, destructuring, array element
    /// assignment.
    pub const ELEMENT: IterationUse = Self::ALLOWS_SYNC_ITERABLES_FLAG;
    /// `IterationUseSpread`.
    pub const SPREAD: IterationUse =
        IterationUse(Self::ALLOWS_SYNC_ITERABLES_FLAG.0 | Self::SPREAD_FLAG.0);
    /// `IterationUseDestructuring`.
    pub const DESTRUCTURING: IterationUse =
        IterationUse(Self::ALLOWS_SYNC_ITERABLES_FLAG.0 | Self::DESTRUCTURING_FLAG.0);
    /// `IterationUseForOf`.
    pub const FOR_OF: IterationUse = IterationUse(
        Self::ALLOWS_SYNC_ITERABLES_FLAG.0 | Self::ALLOWS_STRING_INPUT_FLAG.0 | Self::FOR_OF_FLAG.0,
    );
    /// `IterationUseForAwaitOf`.
    pub const FOR_AWAIT_OF: IterationUse = IterationUse(
        Self::ALLOWS_SYNC_ITERABLES_FLAG.0
            | Self::ALLOWS_ASYNC_ITERABLES_FLAG.0
            | Self::ALLOWS_STRING_INPUT_FLAG.0
            | Self::FOR_OF_FLAG.0,
    );
    /// `IterationUseYieldStar`.
    pub const YIELD_STAR: IterationUse =
        IterationUse(Self::ALLOWS_SYNC_ITERABLES_FLAG.0 | Self::YIELD_STAR_FLAG.0);
    /// `IterationUseAsyncYieldStar`.
    pub const ASYNC_YIELD_STAR: IterationUse = IterationUse(
        Self::ALLOWS_SYNC_ITERABLES_FLAG.0
            | Self::ALLOWS_ASYNC_ITERABLES_FLAG.0
            | Self::YIELD_STAR_FLAG.0,
    );
    /// `IterationUseGeneratorReturnType`.
    pub const GENERATOR_RETURN_TYPE: IterationUse = Self::ALLOWS_SYNC_ITERABLES_FLAG;
    /// `IterationUseAsyncGeneratorReturnType`.
    pub const ASYNC_GENERATOR_RETURN_TYPE: IterationUse = Self::ALLOWS_ASYNC_ITERABLES_FLAG;
    /// `IterationUseCacheFlags`.
    pub const CACHE_FLAGS: IterationUse = IterationUse(
        Self::ALLOWS_SYNC_ITERABLES_FLAG.0
            | Self::ALLOWS_ASYNC_ITERABLES_FLAG.0
            | Self::FOR_OF_FLAG.0,
    );
}

// IterationTypes

/// `type IterationTypes struct` (checker.go).
#[derive(Clone, Copy, Default)]
pub struct IterationTypes {
    /// `yieldType`.
    pub yield_type: Option<TypeId>,
    /// `returnType`.
    pub return_type: Option<TypeId>,
    /// `nextType`.
    pub next_type: Option<TypeId>,
}

// IterationTypeKind

/// `type IterationTypeKind int32` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum IterationTypeKind {
    /// `IterationTypeKindYield`
    #[default]
    Yield = 0,
    /// `IterationTypeKindReturn`
    Return = 1,
    /// `IterationTypeKindNext`
    Next = 2,
}

// Function-field thunk aliases (see file header).

/// `func() *Type` — the `getGlobalXType` / resolver thunks.
pub type TypeThunk<'a> = dyn Fn(&mut Checker) -> TypeId + 'a;
/// `func() *ast.Symbol` — the `getGlobalXSymbol` / alias / value resolvers.
pub type SymbolThunk<'a> = dyn Fn(&mut Checker) -> Option<SymbolId> + 'a;
/// `func() []*Type` — `getGlobalBuiltinIteratorTypes`.
pub type TypeListThunk<'a> = dyn Fn(&mut Checker) -> Vec<TypeId> + 'a;
/// `func(t *Type, errorNode *ast.Node) *Type` — `resolveIterationType`.
pub type ResolveIterationTypeThunk<'a> =
    dyn Fn(&mut Checker, TypeId, Option<NodeId>) -> TypeId + 'a;
/// `func(location *ast.Node, name string, meaning ast.SymbolFlags,
/// nameNotFoundMessage *diagnostics.Message, isUse bool, excludeGlobals
/// bool) *ast.Symbol` — `resolveName` / `resolveNameForSymbolSuggestion`.
pub type NameResolverThunk<'a> = dyn Fn(
        &mut Checker,
        Option<NodeId>,
        &str,
        ast::SymbolFlags,
        Option<&'static tsc_diagnostics::Message>,
        bool,
        bool,
    ) -> Option<SymbolId>
    + 'a;
/// `evaluator.Evaluator` — `func(expr, location *ast.Node) evaluator.Result`.
/// PORT: gains `&mut Checker` and the `nodes` arena (Go derefs `*ast.Node`
/// freely); `evaluateEntity` is deferred.
pub type EvaluatorThunk<'a> =
    dyn Fn(&mut Checker, NodeId, Option<NodeId>, &[ast::Node]) -> tsc_evaluator::Result + 'a;
/// `func(*ast.Symbol, *ast.Symbol) int` — `compareSymbols`.
pub type SymbolComparerThunk<'a> =
    dyn Fn(&mut Checker, Option<SymbolId>, Option<SymbolId>) -> i32 + 'a;
/// `func([]*ast.Symbol, []*ast.Symbol) int` — `compareSymbolChains`.
/// PORT: chain elements are `SymbolId` (non-nil in practice — Go chains are
/// populated symbol lists; compare via `compareSymbols` handles nil anyway).
pub type SymbolChainComparerThunk<'a> = dyn Fn(&mut Checker, &[SymbolId], &[SymbolId]) -> i32 + 'a;
/// `func(*Type) bool` — `isPrimitiveOrObjectOrEmptyType`,
/// `containsMissingType`, `couldContainTypeVariables`,
/// `isStringIndexSignatureOnlyType`.
pub type TypeBoolThunk<'a> = dyn Fn(&mut Checker, TypeId) -> bool + 'a;
/// `func(*ast.Node) bool` — `markNodeAssignments`.
pub type NodeBoolThunk<'a> = dyn Fn(&mut Checker, NodeId) -> bool + 'a;
/// `func()` — `deferredDiagnosticCallbacks` element.
pub type DeferredDiagnosticCallback<'a> = Box<dyn FnOnce(&mut Checker) + 'a>;

// IterationTypesResolver

/// `type IterationTypesResolver struct` (checker.go). Go function fields
/// capture the checker; here they are `Rc` thunks taking `&mut Checker`
/// (see file header). `Clone` lets callers copy the resolver bag out of the
/// checker so `&mut Checker` methods can run without aliasing it.
#[derive(Clone)]
pub struct IterationTypesResolver {
    /// `iteratorSymbolName`.
    pub iterator_symbol_name: String,
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
    /// `getGlobalBuiltinIteratorTypes`.
    pub get_global_builtin_iterator_types: Option<Rc<TypeListThunk<'static>>>,
    /// `resolveIterationType`.
    pub resolve_iteration_type: Option<Rc<ResolveIterationTypeThunk<'static>>>,
    /// `mustHaveANextMethodDiagnostic`.
    pub must_have_a_next_method_diagnostic: Option<&'static tsc_diagnostics::Message>,
    /// `mustBeAMethodDiagnostic`.
    pub must_be_a_method_diagnostic: Option<&'static tsc_diagnostics::Message>,
    /// `mustHaveAValueDiagnostic`.
    pub must_have_a_value_diagnostic: Option<&'static tsc_diagnostics::Message>,
}

// WideningContext

/// `type WideningContext struct` (checker.go). `parent`/`childContexts` form
/// a pointer graph in Go — `Rc<RefCell>` mirrors the shared mutation.
pub struct WideningContext {
    /// `parent` — parent context.
    pub parent: Option<Rc<RefCell<WideningContext>>>,
    /// `propertyName` — name of property in parent.
    pub property_name: String,
    /// `siblings` — types of siblings.
    pub siblings: Vec<TypeId>,
    /// `resolvedProperties` — properties occurring in sibling object
    /// literals.
    pub resolved_properties: Vec<SymbolId>,
    /// `childContexts`.
    pub child_contexts: FxHashMap<String, Rc<RefCell<WideningContext>>>,
    /// `widenedTypes`.
    pub widened_types: FxHashMap<TypeId, TypeId>,
}

// VarianceStackEntry

/// `type VarianceStackEntry struct` (checker.go).
#[derive(Default)]
pub struct VarianceStackEntry {
    /// `symbol`.
    pub symbol: Option<SymbolId>,
    /// `typeParameters`.
    pub type_parameters: Vec<TypeId>,
}

/// `const maxSerializationLevel = 2` (checker.go).
pub const MAX_SERIALIZATION_LEVEL: i32 = 2;

// UnionReduction

/// `type UnionReduction int32` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum UnionReduction {
    /// `UnionReductionNone`
    #[default]
    None = 0,
    /// `UnionReductionLiteral`
    Literal = 1,
    /// `UnionReductionSubtype`
    Subtype = 2,
}

impl UnionReduction {
    /// `UnionReductionNone` — Go-style const alias used by ported call sites.
    pub const NONE: UnionReduction = UnionReduction::None;
    /// `UnionReductionLiteral` — Go-style const alias.
    pub const LITERAL: UnionReduction = UnionReduction::Literal;
    /// `UnionReductionSubtype` — Go-style const alias.
    pub const SUBTYPE: UnionReduction = UnionReduction::Subtype;
}

// IntersectionFlags

flag_type! {
    /// `type IntersectionFlags uint32` (checker.go).
    pub struct IntersectionFlags(pub u32);
}

impl IntersectionFlags {
    /// `IntersectionFlagsNoSupertypeReduction`.
    pub const NO_SUPERTYPE_REDUCTION: IntersectionFlags = IntersectionFlags(1 << 0);
    /// `IntersectionFlagsNoConstraintReduction`.
    pub const NO_CONSTRAINT_REDUCTION: IntersectionFlags = IntersectionFlags(1 << 1);
}

// thisAssignmentDeclarationKind

/// `type thisAssignmentDeclarationKind int32` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum ThisAssignmentDeclarationKind {
    /// `thisAssignmentDeclarationNone` — not (all) this.property
    /// assignments.
    #[default]
    None = 0,
    /// `thisAssignmentDeclarationTyped` — typed; use the type annotation.
    Typed = 1,
    /// `thisAssignmentDeclarationConstructor` — at least one in the
    /// constructor; use control flow.
    Constructor = 2,
    /// `thisAssignmentDeclarationMethod` — methods only; look in base
    /// first, and if not found, union all declaration types plus
    /// undefined.
    Method = 3,
}

// InheritanceInfo

/// `type InheritanceInfo struct` (checker.go).
#[derive(Clone, Copy, Default)]
pub struct InheritanceInfo {
    /// `prop`.
    pub prop: Option<SymbolId>,
    /// `containingType`.
    pub containing_type: Option<TypeId>,
}

// UnusedKind

/// `type UnusedKind int32` (checker.go).
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum UnusedKind {
    /// `UnusedKindLocal`
    #[default]
    Local = 0,
    /// `UnusedKindParameter`
    Parameter = 1,
}

// constructorAccessibilityError

/// `type constructorAccessibilityError struct` (checker.go).
#[derive(Clone, Copy, Default)]
pub struct ConstructorAccessibilityError {
    /// `kind`.
    pub kind: ast::ModifierFlags,
    /// `declaringClass`.
    pub declaring_class: Option<TypeId>,
}

// CallState

/// `type CallState struct` (checker.go).
#[derive(Default)]
pub struct CallState {
    /// `node`.
    pub node: Option<NodeId>,
    /// `typeArguments`.
    pub type_arguments: Vec<NodeId>,
    /// `args`.
    pub args: Vec<NodeId>,
    /// `candidates`.
    pub candidates: Vec<SignatureId>,
    /// `argCheckMode`.
    pub arg_check_mode: CheckMode,
    /// `isSingleNonGenericCandidate`.
    pub is_single_non_generic_candidate: bool,
    /// `signatureHelpTrailingComma`.
    pub signature_help_trailing_comma: bool,
    /// `recursiveResolution`.
    pub recursive_resolution: bool,
    /// `candidatesForArgumentError`.
    pub candidates_for_argument_error: Vec<SignatureId>,
    /// `candidateForArgumentArityError`.
    pub candidate_for_argument_arity_error: Option<SignatureId>,
    /// `candidateForTypeArgumentError`.
    pub candidate_for_type_argument_error: Option<SignatureId>,
}

// PredicateSemantics

flag_type! {
    /// `type PredicateSemantics uint32` (checker.go).
    pub struct PredicateSemantics(pub u32);
}

impl PredicateSemantics {
    /// `PredicateSemanticsAlways`.
    pub const ALWAYS: PredicateSemantics = PredicateSemantics(1 << 0);
    /// `PredicateSemanticsNever`.
    pub const NEVER: PredicateSemantics = PredicateSemantics(1 << 1);
    /// `PredicateSemanticsSometimes`.
    pub const SOMETIMES: PredicateSemantics = PredicateSemantics(Self::ALWAYS.0 | Self::NEVER.0);
}

// ExportCollision / ExportCollisionTable

/// `type ExportCollision struct` (checker.go).
#[derive(Default)]
pub struct ExportCollision {
    /// `specifierText`.
    pub specifier_text: String,
    /// `exportsWithDuplicate`.
    pub exports_with_duplicate: Vec<NodeId>,
}

/// `type ExportCollisionTable = map[string]*ExportCollision` (checker.go).
/// PORT: `*ExportCollision` → the map owns the value (only ever mutated
/// through the map).
pub type ExportCollisionTable = FxHashMap<String, ExportCollision>;

// TupleNormalizer

/// `type TupleNormalizer struct` (checker.go) — PORT(partial): the `c
/// *Checker` back-pointer is dropped; `normalize` takes `&mut Checker` when
/// it lands (the struct is a per-operation scratch accumulator).
#[derive(Default)]
pub struct TupleNormalizer {
    /// `types`.
    pub types: Vec<TypeId>,
    /// `infos`.
    pub infos: Vec<TupleElementInfo>,
    /// `lastRequiredIndex`.
    pub last_required_index: i32,
    /// `firstRestIndex`.
    pub first_rest_index: i32,
    /// `lastOptionalOrRestIndex`.
    pub last_optional_or_rest_index: i32,
}

// ObjectLiteralDiscriminator

/// `type ObjectLiteralDiscriminator struct` (checker.go) — PORT(partial):
/// `c *Checker` is dropped (methods take `&mut Checker`); Go treats the
/// struct as the `Discriminator` closure-bag for
/// `discriminateTypeByDiscriminableItems`.
#[derive(Default)]
pub struct ObjectLiteralDiscriminator {
    /// `props`.
    pub props: Vec<NodeId>,
    /// `members`.
    pub members: Vec<SymbolId>,
}

// keyBuilder + key functions

/// `type keyBuilder struct` (checker.go) — byte-buffered xxh3 key writer.
/// PORT: `inline_buffer` is a fixed inline scratch — `Default` is implemented
/// manually because `[u8; 192]` has no `Default` impl.
pub struct KeyBuilder {
    /// `inlineLength`.
    inline_length: usize,
    /// `overflowBuffer`.
    overflow_buffer: Vec<u8>,
    /// `inlineBuffer`.
    inline_buffer: [u8; 192],
}

impl Default for KeyBuilder {
    fn default() -> Self {
        Self {
            inline_length: 0,
            overflow_buffer: Vec::new(),
            inline_buffer: [0; 192],
        }
    }
}

impl KeyBuilder {
    /// `(b *keyBuilder) hash`.
    pub fn hash(&self) -> CacheHashKey {
        if self.overflow_buffer.is_empty() {
            return hash128(&self.inline_buffer[..self.inline_length]);
        }
        let mut bytes = self.overflow_buffer.clone();
        bytes.extend_from_slice(&self.inline_buffer[..self.inline_length]);
        hash128(&bytes)
    }

    /// `(b *keyBuilder) spill` — moves the buffered bytes onto the end of
    /// `overflow_buffer`, so the key's byte stream stays `overflow_buffer`
    /// followed by `inline_buffer`.
    fn spill(&mut self) {
        self.overflow_buffer
            .extend_from_slice(&self.inline_buffer[..self.inline_length]);
        self.inline_length = 0;
    }

    /// `(b *keyBuilder) writeByte`.
    pub fn write_byte(&mut self, c: u8) {
        if self.inline_length == self.inline_buffer.len() {
            self.spill();
        }
        self.inline_buffer[self.inline_length] = c;
        self.inline_length += 1;
    }

    /// `(b *keyBuilder) writeString`.
    pub fn write_string(&mut self, s: &str) {
        if self.inline_length + s.len() > self.inline_buffer.len() {
            self.spill();
            if s.len() > self.inline_buffer.len() {
                self.overflow_buffer.extend_from_slice(s.as_bytes());
                return;
            }
        }
        self.inline_buffer[self.inline_length..self.inline_length + s.len()]
            .copy_from_slice(s.as_bytes());
        self.inline_length += s.len();
    }

    /// `(b *keyBuilder) writeUint32`.
    pub fn write_u32(&mut self, v: u32) {
        if self.inline_length + 4 > self.inline_buffer.len() {
            self.spill();
        }
        self.inline_buffer[self.inline_length..self.inline_length + 4]
            .copy_from_slice(&v.to_le_bytes());
        self.inline_length += 4;
    }

    /// `(b *keyBuilder) writeUint64`.
    pub fn write_u64(&mut self, v: u64) {
        if self.inline_length + 8 > self.inline_buffer.len() {
            self.spill();
        }
        self.inline_buffer[self.inline_length..self.inline_length + 8]
            .copy_from_slice(&v.to_le_bytes());
        self.inline_length += 8;
    }

    /// `(b *keyBuilder) writeInt`.
    pub fn write_int(&mut self, value: i64) {
        self.write_u64(value as u64);
    }

    /// `(b *keyBuilder) writeSymbol` — `ast.GetSymbolId(s)` is the port's
    /// `SymbolId` itself.
    pub fn write_symbol(&mut self, s: SymbolId) {
        self.write_u64(s.0 as u64);
    }

    /// `(b *keyBuilder) writeType` — `uint32(t.id)`; the port's `TypeId` IS
    /// the id (arena index == sequential id).
    pub fn write_type(&mut self, t: TypeId) {
        self.write_u32(t.0);
    }

    /// `(b *keyBuilder) writeTypes`.
    pub fn write_types(&mut self, types: &[TypeId]) {
        self.write_int(types.len() as i64);
        for &t in types {
            self.write_type(t);
        }
    }

    /// `(b *keyBuilder) writeAlias`.
    pub fn write_alias(&mut self, alias: Option<&TypeAlias>) {
        if let Some(alias) = alias {
            self.write_byte(1);
            self.write_symbol(alias.symbol.unwrap_or_default());
            self.write_types(&alias.type_arguments);
        } else {
            self.write_byte(0);
        }
    }

    /// `(b *keyBuilder) writeNodeId`.
    pub fn write_node_id(&mut self, id: NodeId) {
        self.write_u64(id.0);
    }

    /// `(b *keyBuilder) writeNode`.
    pub fn write_node(&mut self, node: Option<NodeId>) {
        if let Some(node) = node {
            self.write_node_id(node);
        }
    }
}

/// `getTypeListKey(types)` (checker.go).
pub fn get_type_list_key(types: &[TypeId]) -> CacheHashKey {
    let mut b = KeyBuilder::default();
    b.write_types(types);
    b.hash()
}

/// `getAliasKey(alias)` (checker.go).
pub fn get_alias_key(alias: Option<&TypeAlias>) -> CacheHashKey {
    let mut b = KeyBuilder::default();
    b.write_alias(alias);
    b.hash()
}

/// `getUnionKey(types, origin, alias)` (checker.go).
///
/// PORT: takes the type arena for the `origin.Types()` dereference (Go
/// reads `origin.flags`/`origin.Types()` off the heap object).
pub fn get_union_key(
    arena: &TypeArena,
    types: &[TypeId],
    origin: Option<TypeId>,
    alias: Option<&TypeAlias>,
) -> CacheHashKey {
    let mut b = KeyBuilder::default();
    match origin {
        None => b.write_types(types),
        Some(origin) => {
            let origin_flags = arena.get(origin).flags;
            if origin_flags.intersects(TypeFlags::UNION) {
                b.write_byte(b'|');
                let origin_types = arena.get(origin).types().to_vec();
                b.write_types(&origin_types);
            } else if origin_flags.intersects(TypeFlags::INTERSECTION) {
                b.write_byte(b'&');
                let origin_types = arena.get(origin).types().to_vec();
                b.write_types(&origin_types);
            } else if origin_flags.intersects(TypeFlags::INDEX) {
                // origin type id alone is insufficient, as `keyof x` may
                // resolve to multiple WIP values while `x` is still
                // resolving
                b.write_byte(b'#');
                b.write_type(origin);
                b.write_byte(b'|');
                b.write_types(types);
            } else {
                panic!("Unhandled case in getUnionKey")
            }
        }
    }
    b.write_alias(alias);
    b.hash()
}

/// `getIntersectionKey(types, flags, alias)` (checker.go).
pub fn get_intersection_key(
    types: &[TypeId],
    flags: IntersectionFlags,
    alias: Option<&TypeAlias>,
) -> CacheHashKey {
    let mut b = KeyBuilder::default();
    b.write_types(types);
    if !flags.intersects(IntersectionFlags::NO_CONSTRAINT_REDUCTION) {
        b.write_alias(alias);
    } else {
        b.write_byte(b'*');
    }
    b.hash()
}

/// `getTupleKey(elementInfos, readonly)` (checker.go).
pub fn get_tuple_key(element_infos: &[TupleElementInfo], readonly: bool) -> CacheHashKey {
    let mut b = KeyBuilder::default();
    for e in element_infos {
        if e.flags.intersects(ElementFlags::REQUIRED) {
            b.write_byte(b'#');
        } else if e.flags.intersects(ElementFlags::OPTIONAL) {
            b.write_byte(b'?');
        } else if e.flags.intersects(ElementFlags::REST) {
            b.write_byte(b'.');
        } else {
            b.write_byte(b'*');
        }
        if e.labeled_declaration.is_some() {
            b.write_node(e.labeled_declaration);
        }
    }
    if readonly {
        b.write_byte(b'!');
    }
    b.hash()
}

/// `getTypeAliasInstantiationKey(typeArguments, alias)` (checker.go).
pub fn get_type_alias_instantiation_key(
    type_arguments: &[TypeId],
    alias: Option<&TypeAlias>,
) -> CacheHashKey {
    get_type_instantiation_key(type_arguments, alias, false)
}

/// `getTypeInstantiationKey(typeArguments, alias, singleSignature)`
/// (checker.go).
pub fn get_type_instantiation_key(
    type_arguments: &[TypeId],
    alias: Option<&TypeAlias>,
    single_signature: bool,
) -> CacheHashKey {
    let mut b = KeyBuilder::default();
    b.write_types(type_arguments);
    b.write_alias(alias);
    if single_signature {
        b.write_byte(b'!');
    }
    b.hash()
}

/// `getIndexedAccessKey(objectType, indexType, accessFlags, alias)`
/// (checker.go).
pub fn get_indexed_access_key(
    object_type: TypeId,
    index_type: TypeId,
    access_flags: crate::types::AccessFlags,
    alias: Option<&TypeAlias>,
) -> CacheHashKey {
    let mut b = KeyBuilder::default();
    b.write_type(object_type);
    b.write_type(index_type);
    b.write_u32(access_flags.0);
    b.write_alias(alias);
    b.hash()
}

/// `getTemplateTypeKey(texts, types)` (checker.go).
pub fn get_template_type_key(texts: &[String], types: &[TypeId]) -> CacheHashKey {
    let mut b = KeyBuilder::default();
    b.write_types(types);
    b.write_byte(b'|');
    for s in texts {
        b.write_int(s.len() as i64);
    }
    b.write_byte(b'|');
    for s in texts {
        b.write_string(s);
    }
    b.hash()
}

/// `isNonDeferredTypeReference` (checker.go) — free helper.
pub fn is_non_deferred_type_reference(types: &TypeArena, t: TypeId) -> bool {
    let ty = types.get(t);
    ty.object_flags
        .intersects(crate::types::ObjectFlags::REFERENCE)
        && ty
            .data
            .as_type_reference()
            .is_some_and(|r| r.node.is_none())
}

/// `isTypeReferenceWithGenericArguments` (checker.go) — free helper.
///
/// PORT: `t.checker.getTypeArguments(t)` is the deferred
/// `Checker::get_type_arguments`; takes `&mut Checker` for it.
pub fn is_type_reference_with_generic_arguments(c: &mut Checker, t: TypeId) -> bool {
    is_non_deferred_type_reference(&c.types, t)
        && c.get_type_arguments(t).iter().any(|&u| {
            let is_type_parameter = c.types.get(u).flags.intersects(TypeFlags::TYPE_PARAMETER);
            is_type_parameter || is_type_reference_with_generic_arguments(c, u)
        })
}

// Program / Host

/// `type Host interface` (checker.go) — `modulespecifiers.
/// ModuleSpecifierGenerationHost`. The Rust trait is a marker over the
/// already-ported modulespecifiers trait; `Program` extends it.
pub trait Host: tsc_modulespecifiers::ModuleSpecifierGenerationHost {}

/// `type Program interface` (checker.go) — the checker's view of the
/// program. PORT(partial): method signatures mirror the Go interface, with
/// `*ast.SourceFile`/`ast.HasFileName`/`*tsoptions.ParsedCommandLine`
/// mapped per file conventions. `Program::nodes` is a port addition (the
/// Go interface hides arenas behind `*ast.Node`; here the per-file
/// `Vec<ast::Node>` arenas must be reachable for `NodeId` derefs — wave-2
/// may fold this into a richer program crate).
pub trait Program: Host {
    /// `Options()`.
    fn options(&self) -> Rc<CompilerOptions>;
    /// `SourceFiles()` — `[]*ast.SourceFile` → source-file `NodeId`s.
    fn source_files(&self) -> Vec<NodeId>;
    /// `BindSourceFiles()`.
    fn bind_source_files(&self);
    /// `FileExists(fileName)`.
    fn file_exists(&self, file_name: &RootedFilePath) -> bool;
    /// `GetSourceFileForResolvedModule(resolved)`.
    fn get_source_file_for_resolved_module(&self, resolved: &ResolvedModule) -> Option<NodeId>;
    /// `GetEmitModuleFormatOfFile(sourceFile)`.
    fn get_emit_module_format_of_file(
        &self,
        source_file: &dyn HasFileName,
    ) -> tsc_core::options_generated::ModuleKind;
    /// `GetEmitSyntaxForUsageLocation(sourceFile, usageLocation)` —
    /// `*ast.StringLiteralLike` → `NodeId`.
    fn get_emit_syntax_for_usage_location(
        &self,
        source_file: &dyn HasFileName,
        usage_location: NodeId,
    ) -> tsc_core::compileroptions::ResolutionMode;
    /// `GetImpliedNodeFormatForEmit(sourceFile)`.
    fn get_implied_node_format_for_emit(
        &self,
        source_file: &dyn HasFileName,
    ) -> tsc_core::options_generated::ModuleKind;
    /// `GetResolvedModule(currentSourceFile, moduleReference, mode)`.
    fn get_resolved_module(
        &self,
        current_source_file: &dyn HasFileName,
        module_reference: &str,
        mode: tsc_core::compileroptions::ResolutionMode,
    ) -> Option<ResolvedModule>;
    /// `GetResolvedModules()` —
    /// `map[tspath.PathKey]module.ModeAwareCache[*module.ResolvedModule]`.
    fn get_resolved_modules(&self) -> &FxHashMap<PathKey, ModeAwareCache<Option<ResolvedModule>>>;
    /// `GetPackagesMap()`.
    fn get_packages_map(&self) -> FxHashMap<String, bool>;
    /// `GetSourceFileMetaData(path)`.
    fn get_source_file_meta_data(&self, path: &PathKey) -> ast::SourceFileMetaData;
    /// `GetJSXRuntimeImportSpecifier(path)` — `(moduleReference, specifier)`.
    fn get_jsx_runtime_import_specifier(&self, path: &PathKey) -> (String, Option<NodeId>);
    /// `GetImportHelpersImportSpecifier(path)`.
    fn get_import_helpers_import_specifier(&self, path: &PathKey) -> Option<NodeId>;
    /// `SourceFileMayBeEmitted(sourceFile, forceDtsEmit)`.
    fn source_file_may_be_emitted(&self, source_file: NodeId, force_dts_emit: bool) -> bool;
    /// `IsSourceFileDefaultLibrary(path)`.
    fn is_source_file_default_library(&self, path: &PathKey) -> bool;
    /// `GetProjectReferenceFromOutputDts(path)`.
    fn get_project_reference_from_output_dts(
        &self,
        path: &PathKey,
    ) -> Option<std::sync::Arc<SourceOutputAndProjectReference>>;
    /// `GetRedirectForResolution(file)`.
    fn get_redirect_for_resolution(
        &self,
        file: &dyn HasFileName,
    ) -> Option<std::sync::Arc<ParsedCommandLine>>;
    /// `CommonSourceDirectory()` — already required by `OutputPathsHost`;
    /// redeclared to mirror the Go interface 1:1.
    fn common_source_directory(&self) -> RootedDirectoryPath;
    /// PORT(addition): the per-file `Vec<ast::Node>` arena indexed by
    /// `NodeId::file_index` — not part of Go's `Program` interface (Go
    /// derefs `*ast.Node` directly).
    fn nodes(&self, file_index: u32) -> Rc<Vec<ast::Node>>;
    /// `nodes_mut` — mutable arena access for synthetic-node creation
    /// (factory-created synthetic expressions, flow nodes).
    fn nodes_mut(&self, file_index: u32) -> std::cell::RefMut<'_, Vec<ast::Node>>;
}
