// Ported from tsc/internal/checker/types.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The core type lattice: `Type`, `TypeFlags`, `ObjectFlags`, the `TypeData`
// payload family, the `*Links` records, `Signature`, `TypePredicate` and
// `IndexInfo`.
//
// PORT notes (see SPEC.md §5.3/§5.4 for the arena rationale):
//
// - `*Type` becomes `TypeId`, an index into `TypeArena`
//   (`RwLock<Vec<Type>>`). Go's pointer-identity comparisons (`t == s`,
//   `map[*Type]*Type`) become `TypeId` equality/`HashMap<TypeId, _>` —
//   TypeIds are per-checker-shard, matching Go where two checkers' `*Type`
//   pointers never collide. `Type.checker *Checker` becomes
//   `checker_shard: u16`; code that read `t.checker.X` takes the checker as
//   an explicit parameter instead (§5.4 "t.checker eradication").
//   `TypeArena` wraps the Vec in `RwLock` because `tracing::TracedType` is
//   `Send + Sync` and the tracer's recorded-type adapters must keep reading
//   lazily-resolved fields after the checker hands them out. Accessors take
//   short-lived guards (`arena.get(id)`); write sites must not hold a read
//   guard across a `get_mut`/`alloc` (same-thread RwLock recursion deadlocks)
//   — compute into locals, then store.
// - `*Signature` → `SignatureId` into `SignatureArena` (`Vec<Signature>`).
//   `*TypeMapper` → `TypeMapperId` into `TypeMapperArena` (mapper.rs).
//   `*InferenceContext` → `InferenceContextId` into `Vec<InferenceContext>`
//   (checker_core.rs).
// - `TypeData interface` → a `TypeData` enum. Go's struct embedding chain
//   (`InterfaceType{TypeReference{ObjectType{StructuredType{ConstrainedType}}}}`)
//   becomes nested named fields (`type_reference.object_type.structured_type
//   .constrained_type`), so `as_constrained_type()`/`as_structured_type()`/
//   `as_object_type()`/`as_type_reference()`/`as_interface_type()`/
//   `as_union_or_intersection_type()` return `Option<&T>` views matching
//   Go's nil-able `TypeBase` fallback.
// - `*ast.Symbol` → `SymbolId`, `*ast.Node` → `NodeId` (`Option<_>` for
//   nil-able fields), `ast.SymbolTable` → `tsc_ast::SymbolTable`
//   (insertion-ordered), Go `map[K]V` scratch lookups → `FxHashMap`.
// - `LiteralType.value any` (string | jsnum.Number | bool | PseudoBigInt |
//   nil) → `Option<tsc_evaluator::Value>` — the evaluator's `any`-analogue
//   enum covers exactly those alternatives.

use std::fmt;
use std::sync::{Arc, RwLock, RwLockReadGuard, RwLockWriteGuard};

use rustc_hash::FxHashMap;
use tsc_ast::symbolflags::SymbolFlags;
use tsc_ast::{NodeId, SymbolId, SymbolTable};
use tsc_collections::OrderedSet;
use tsc_core::options_generated::ScriptTarget;
use tsc_core::tristate::Tristate;
use tsc_evaluator as evaluator;

use crate::flagdef::flag_type;
use crate::mapper::TypeMapperId;

// Re-exported so `crate::types::UnionReduction` resolves (the enum is
// defined in checker_types.rs alongside the other checker.go port types).
pub use crate::checker_types::UnionReduction;

// ParseFlags

flag_type! {
    /// `type ParseFlags uint32`.
    pub struct ParseFlags(pub u32);
}

impl ParseFlags {
    /// `ParseFlagsYield`
    pub const YIELD: ParseFlags = ParseFlags(1 << 0);
    /// `ParseFlagsAwait`
    pub const AWAIT: ParseFlags = ParseFlags(1 << 1);
    /// `ParseFlagsType`
    pub const TYPE: ParseFlags = ParseFlags(1 << 2);
    /// `ParseFlagsIgnoreMissingOpenBrace`
    pub const IGNORE_MISSING_OPEN_BRACE: ParseFlags = ParseFlags(1 << 4);
    /// `ParseFlagsJSDoc`
    pub const JSDOC: ParseFlags = ParseFlags(1 << 5);
}

/// `type SignatureKind int32`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum SignatureKind {
    /// `SignatureKindCall`
    #[default]
    Call = 0,
    /// `SignatureKindConstruct`
    Construct = 1,
}

/// `type IndexKind int32`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum IndexKind {
    /// `IndexKindString`
    #[default]
    String = 0,
    /// `IndexKindNumber`
    Number = 1,
}

/// `type MemberOverrideStatus int32`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum MemberOverrideStatus {
    /// `MemberOverrideStatusNone`
    #[default]
    None = 0,
    /// `MemberOverrideStatusNeedsOverride`
    NeedsOverride = 1,
    /// `MemberOverrideStatusHasInvalidOverride`
    HasInvalidOverride = 2,
}

flag_type! {
    /// `type ContextFlags uint32`.
    pub struct ContextFlags(pub u32);
}

impl ContextFlags {
    /// `ContextFlagsSignature` — obtaining contextual signature.
    pub const SIGNATURE: ContextFlags = ContextFlags(1 << 0);
    /// `ContextFlagsNoConstraints` — don't obtain type variable constraints.
    pub const NO_CONSTRAINTS: ContextFlags = ContextFlags(1 << 1);
    /// `ContextFlagsIgnoreNodeInferences` — ignore inference to current node
    /// and parent nodes out to the containing call for, for example,
    /// completions.
    pub const IGNORE_NODE_INFERENCES: ContextFlags = ContextFlags(1 << 2);
    /// `ContextFlagsSkipBindingPatterns` — ignore contextual types applied by
    /// binding patterns.
    pub const SKIP_BINDING_PATTERNS: ContextFlags = ContextFlags(1 << 3);
}

flag_type! {
    /// `type TypeFormatFlags uint32`.
    pub struct TypeFormatFlags(pub u32);
}

impl TypeFormatFlags {
    /// `TypeFormatFlagsNoTruncation` — don't truncate typeToString result.
    pub const NO_TRUNCATION: TypeFormatFlags = TypeFormatFlags(1 << 0);
    /// `TypeFormatFlagsWriteArrayAsGenericType` — write `Array<T>` instead `T[]`.
    pub const WRITE_ARRAY_AS_GENERIC_TYPE: TypeFormatFlags = TypeFormatFlags(1 << 1);
    /// `TypeFormatFlagsGenerateNamesForShadowedTypeParams` — when a type
    /// parameter T is shadowing another T, generate a name for it so it can
    /// still be referenced.
    pub const GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS: TypeFormatFlags = TypeFormatFlags(1 << 2);
    /// `TypeFormatFlagsUseStructuralFallback` — when an alias cannot be named
    /// by its symbol, rather than report an error, fallback to a structural
    /// printout if possible.
    pub const USE_STRUCTURAL_FALLBACK: TypeFormatFlags = TypeFormatFlags(1 << 3);
    // hole because there's a hole in node builder flags
    /// `TypeFormatFlagsWriteTypeArgumentsOfSignature` — write the type
    /// arguments instead of type parameters of the signature.
    pub const WRITE_TYPE_ARGUMENTS_OF_SIGNATURE: TypeFormatFlags = TypeFormatFlags(1 << 5);
    /// `TypeFormatFlagsUseFullyQualifiedType` — write out the fully qualified
    /// type name (eg. `Module.Type`, instead of `Type`).
    pub const USE_FULLY_QUALIFIED_TYPE: TypeFormatFlags = TypeFormatFlags(1 << 6);
    // hole because `UseOnlyExternalAliasing` is here in node builder flags, but
    // functions which take old flags use `SymbolFormatFlags` instead
    /// `TypeFormatFlagsSuppressAnyReturnType` — if the return type is
    /// any-like, don't offer a return type.
    pub const SUPPRESS_ANY_RETURN_TYPE: TypeFormatFlags = TypeFormatFlags(1 << 8);
    // hole because `WriteTypeParametersInQualifiedName` is here in node builder
    // flags, but functions which take old flags use `SymbolFormatFlags` for
    // this instead
    /// `TypeFormatFlagsMultilineObjectLiterals` — always print object literals
    /// across multiple lines (only used to map into node builder flags).
    pub const MULTILINE_OBJECT_LITERALS: TypeFormatFlags = TypeFormatFlags(1 << 10);
    /// `TypeFormatFlagsWriteClassExpressionAsTypeLiteral` — write a type
    /// literal instead of `(Anonymous class)`.
    pub const WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL: TypeFormatFlags = TypeFormatFlags(1 << 11);
    /// `TypeFormatFlagsUseTypeOfFunction` — write `typeof` instead of function
    /// type literal.
    pub const USE_TYPE_OF_FUNCTION: TypeFormatFlags = TypeFormatFlags(1 << 12);
    /// `TypeFormatFlagsOmitParameterModifiers` — omit modifiers on parameters.
    pub const OMIT_PARAMETER_MODIFIERS: TypeFormatFlags = TypeFormatFlags(1 << 13);
    /// `TypeFormatFlagsUseAliasDefinedOutsideCurrentScope` — for a
    /// `type T = ...` defined in a different file, write `T` instead of its
    /// value, even though `T` can't be accessed in the current scope.
    pub const USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE: TypeFormatFlags = TypeFormatFlags(1 << 14);
    /// `TypeFormatFlagsUseSingleQuotesForStringLiteralType` — use single
    /// quotes for string literal type.
    pub const USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE: TypeFormatFlags = TypeFormatFlags(1 << 28);
    /// `TypeFormatFlagsNoTypeReduction` — don't call getReducedType.
    pub const NO_TYPE_REDUCTION: TypeFormatFlags = TypeFormatFlags(1 << 29);
    /// `TypeFormatFlagsUseInstantiationExpressions` — use instantiation
    /// expressions for qualified instantiated names like `Foo<string>.Bar`.
    pub const USE_INSTANTIATION_EXPRESSIONS: TypeFormatFlags = TypeFormatFlags(1 << 30);
    /// `TypeFormatFlagsOmitThisParameter`.
    pub const OMIT_THIS_PARAMETER: TypeFormatFlags = TypeFormatFlags(1 << 25);
    /// `TypeFormatFlagsWriteCallStyleSignature` — write construct signatures
    /// as call style signatures.
    pub const WRITE_CALL_STYLE_SIGNATURE: TypeFormatFlags = TypeFormatFlags(1 << 27);

    // Error Handling
    /// `TypeFormatFlagsAllowUniqueESSymbolType` — bit 20 aligns with the same
    /// bit in `NodeBuilderFlags`.
    pub const ALLOW_UNIQUE_ES_SYMBOL_TYPE: TypeFormatFlags = TypeFormatFlags(1 << 20);

    // TypeFormatFlags exclusive
    /// `TypeFormatFlagsAddUndefined` — add undefined to types of initialized,
    /// non-optional parameters.
    pub const ADD_UNDEFINED: TypeFormatFlags = TypeFormatFlags(1 << 17);
    /// `TypeFormatFlagsWriteArrowStyleSignature` — write arrow style signature.
    pub const WRITE_ARROW_STYLE_SIGNATURE: TypeFormatFlags = TypeFormatFlags(1 << 18);

    // State
    /// `TypeFormatFlagsInArrayType` — writing an array element type.
    pub const IN_ARRAY_TYPE: TypeFormatFlags = TypeFormatFlags(1 << 19);
    /// `TypeFormatFlagsInElementType` — writing an array or union element type.
    pub const IN_ELEMENT_TYPE: TypeFormatFlags = TypeFormatFlags(1 << 21);
    /// `TypeFormatFlagsInFirstTypeArgument` — writing first type argument of
    /// the instantiated type.
    pub const IN_FIRST_TYPE_ARGUMENT: TypeFormatFlags = TypeFormatFlags(1 << 22);
    /// `TypeFormatFlagsInTypeAlias` — writing type in type alias declaration.
    pub const IN_TYPE_ALIAS: TypeFormatFlags = TypeFormatFlags(1 << 23);

    /// `TypeFormatFlagsNodeBuilderFlagsMask`.
    pub const NODE_BUILDER_FLAGS_MASK: TypeFormatFlags = TypeFormatFlags(
        Self::NO_TRUNCATION.0
            | Self::WRITE_ARRAY_AS_GENERIC_TYPE.0
            | Self::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS.0
            | Self::USE_STRUCTURAL_FALLBACK.0
            | Self::WRITE_TYPE_ARGUMENTS_OF_SIGNATURE.0
            | Self::USE_FULLY_QUALIFIED_TYPE.0
            | Self::SUPPRESS_ANY_RETURN_TYPE.0
            | Self::MULTILINE_OBJECT_LITERALS.0
            | Self::WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL.0
            | Self::USE_TYPE_OF_FUNCTION.0
            | Self::OMIT_PARAMETER_MODIFIERS.0
            | Self::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE.0
            | Self::ALLOW_UNIQUE_ES_SYMBOL_TYPE.0
            | Self::IN_TYPE_ALIAS.0
            | Self::USE_INSTANTIATION_EXPRESSIONS.0
            | Self::USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE.0
            | Self::NO_TYPE_REDUCTION.0
            | Self::OMIT_THIS_PARAMETER.0,
    );
}

flag_type! {
    /// `type SymbolFormatFlags uint32`.
    pub struct SymbolFormatFlags(pub u32);
}

impl SymbolFormatFlags {
    /// `SymbolFormatFlagsWriteTypeParametersOrArguments` — write symbols's
    /// type argument if it is instantiated symbol, eg. `class C<T> { p: T }`
    /// shows `p` as `C<T>.p` for `var a: C<number>; var p = a.p`.
    pub const WRITE_TYPE_PARAMETERS_OR_ARGUMENTS: SymbolFormatFlags = SymbolFormatFlags(1 << 0);
    /// `SymbolFormatFlagsUseOnlyExternalAliasing` — use only external alias
    /// information to get the symbol name in the given context, eg.
    /// `module m { export class c { } } import x = m.c;` uses `m.c` instead
    /// of alias symbol `x`.
    pub const USE_ONLY_EXTERNAL_ALIASING: SymbolFormatFlags = SymbolFormatFlags(1 << 1);
    /// `SymbolFormatFlagsAllowAnyNodeKind` — build symbol name using any
    /// nodes needed, instead of just components of an entity name.
    pub const ALLOW_ANY_NODE_KIND: SymbolFormatFlags = SymbolFormatFlags(1 << 2);
    /// `SymbolFormatFlagsUseAliasDefinedOutsideCurrentScope` — prefer aliases
    /// which are not directly visible.
    pub const USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE: SymbolFormatFlags =
        SymbolFormatFlags(1 << 3);
    /// `SymbolFormatFlagsWriteComputedProps` (`/** @internal */`) —
    /// `{ [E.A]: 1 }`.
    pub const WRITE_COMPUTED_PROPS: SymbolFormatFlags = SymbolFormatFlags(1 << 4);
    /// `SymbolFormatFlagsDoNotIncludeSymbolChain` (`/** @internal */`) — skip
    /// building an accessible symbol chain.
    pub const DO_NOT_INCLUDE_SYMBOL_CHAIN: SymbolFormatFlags = SymbolFormatFlags(1 << 5);
}

flag_type! {
    /// `type ExternalEmitHelpers uint32`.
    pub struct ExternalEmitHelpers(pub u32);
}

impl ExternalEmitHelpers {
    /// `ExternalEmitHelpersRest` — `__rest` (ESNext object rest transform).
    pub const REST: ExternalEmitHelpers = ExternalEmitHelpers(1 << 0);
    /// `ExternalEmitHelpersDecorate` — `__decorate` (decorators transform).
    pub const DECORATE: ExternalEmitHelpers = ExternalEmitHelpers(1 << 1);
    /// `ExternalEmitHelpersMetadata` — `__metadata` (decorators transform).
    pub const METADATA: ExternalEmitHelpers = ExternalEmitHelpers(1 << 2);
    /// `ExternalEmitHelpersParam` — `__param` (decorators transform).
    pub const PARAM: ExternalEmitHelpers = ExternalEmitHelpers(1 << 3);
    /// `ExternalEmitHelpersAwaiter` — `__awaiter` (ES2017 async transform).
    pub const AWAITER: ExternalEmitHelpers = ExternalEmitHelpers(1 << 4);
    /// `ExternalEmitHelpersAwait` — `__await` (ES2017 async generator
    /// transform).
    pub const AWAIT: ExternalEmitHelpers = ExternalEmitHelpers(1 << 5);
    /// `ExternalEmitHelpersAsyncGenerator` — `__asyncGenerator` (ES2017 async
    /// generator transform).
    pub const ASYNC_GENERATOR: ExternalEmitHelpers = ExternalEmitHelpers(1 << 6);
    /// `ExternalEmitHelpersAsyncDelegator` — `__asyncDelegator` (ES2017 async
    /// generator yield* transform).
    pub const ASYNC_DELEGATOR: ExternalEmitHelpers = ExternalEmitHelpers(1 << 7);
    /// `ExternalEmitHelpersAsyncValues` — `__asyncValues` (ES2017
    /// for..await..of transform).
    pub const ASYNC_VALUES: ExternalEmitHelpers = ExternalEmitHelpers(1 << 8);
    /// `ExternalEmitHelpersExportStar` — `__exportStar` (CommonJS/AMD/UMD
    /// module transform).
    pub const EXPORT_STAR: ExternalEmitHelpers = ExternalEmitHelpers(1 << 9);
    /// `ExternalEmitHelpersImportStar` — `__importStar` (module transform).
    pub const IMPORT_STAR: ExternalEmitHelpers = ExternalEmitHelpers(1 << 10);
    /// `ExternalEmitHelpersImportDefault` — `__importDefault` (module
    /// transform).
    pub const IMPORT_DEFAULT: ExternalEmitHelpers = ExternalEmitHelpers(1 << 11);
    /// `ExternalEmitHelpersMakeTemplateObject` — `__makeTemplateObject`
    /// (template string array objects).
    pub const MAKE_TEMPLATE_OBJECT: ExternalEmitHelpers = ExternalEmitHelpers(1 << 12);
    /// `ExternalEmitHelpersClassPrivateFieldGet` — `__classPrivateFieldGet`.
    pub const CLASS_PRIVATE_FIELD_GET: ExternalEmitHelpers = ExternalEmitHelpers(1 << 13);
    /// `ExternalEmitHelpersClassPrivateFieldSet` — `__classPrivateFieldSet`.
    pub const CLASS_PRIVATE_FIELD_SET: ExternalEmitHelpers = ExternalEmitHelpers(1 << 14);
    /// `ExternalEmitHelpersClassPrivateFieldIn` — `__classPrivateFieldIn`.
    pub const CLASS_PRIVATE_FIELD_IN: ExternalEmitHelpers = ExternalEmitHelpers(1 << 15);
    /// `ExternalEmitHelpersSetFunctionName` — `__setFunctionName` (class
    /// fields, decorators).
    pub const SET_FUNCTION_NAME: ExternalEmitHelpers = ExternalEmitHelpers(1 << 16);
    /// `ExternalEmitHelpersPropKey` — `__propKey` (decorators).
    pub const PROP_KEY: ExternalEmitHelpers = ExternalEmitHelpers(1 << 17);
    /// `ExternalEmitHelpersAddDisposableResourceAndDisposeResources` —
    /// `__addDisposableResource`/`__disposeResources` (ESNext).
    pub const ADD_DISPOSABLE_RESOURCE_AND_DISPOSE_RESOURCES: ExternalEmitHelpers =
        ExternalEmitHelpers(1 << 18);
    /// `ExternalEmitHelpersRewriteRelativeImportExtension` —
    /// `__rewriteRelativeImportExtension` (--rewriteRelativeImportExtensions).
    pub const REWRITE_RELATIVE_IMPORT_EXTENSION: ExternalEmitHelpers = ExternalEmitHelpers(1 << 19);
    /// `ExternalEmitHelpersESDecorateAndRunInitializers` — `__esDecorate` and
    /// `__runInitializers` (ECMAScript decorators).
    pub const ES_DECORATE_AND_RUN_INITIALIZERS: ExternalEmitHelpers = Self::DECORATE;

    /// `ExternalEmitHelpersFirstEmitHelper`.
    pub const FIRST_EMIT_HELPER: ExternalEmitHelpers = Self::REST;
    /// `ExternalEmitHelpersLastEmitHelper`.
    pub const LAST_EMIT_HELPER: ExternalEmitHelpers = Self::REWRITE_RELATIVE_IMPORT_EXTENSION;

    /// `ExternalEmitHelpersForAwaitOfIncludes` — helpers included by ES2017
    /// for..await..of.
    pub const FOR_AWAIT_OF_INCLUDES: ExternalEmitHelpers = Self::ASYNC_VALUES;

    /// `ExternalEmitHelpersAsyncGeneratorIncludes` — helpers included by
    /// ES2017 async generators.
    pub const ASYNC_GENERATOR_INCLUDES: ExternalEmitHelpers =
        ExternalEmitHelpers(Self::AWAIT.0 | Self::ASYNC_GENERATOR.0);

    /// `ExternalEmitHelpersAsyncDelegatorIncludes` — helpers included by
    /// yield* in ES2017 async generators.
    pub const ASYNC_DELEGATOR_INCLUDES: ExternalEmitHelpers =
        ExternalEmitHelpers(Self::AWAIT.0 | Self::ASYNC_DELEGATOR.0 | Self::ASYNC_VALUES.0);
}

/// `externalHelpersModuleNameText`.
pub const EXTERNAL_HELPERS_MODULE_NAME_TEXT: &str = "tslib";

// Ids

/// `type TypeId uint32` — Go's numeric type ids ARE the port's arena indices
/// (SPEC §5.4). `TypeId` equality is per-checker-shard, like Go's `*Type`
/// pointer identity within a checker's heap.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct TypeId(pub u32);

impl TypeId {
    /// `TypeId(0)` — Go types get ids starting at 1 via a counter; index 0
    /// of the arena is reserved so `TypeId::NONE` can never collide.
    pub const NONE: TypeId = TypeId(u32::MAX);

    /// Whether this id is `TypeId::NONE`.
    #[inline]
    pub const fn is_none(self) -> bool {
        self.0 == Self::NONE.0
    }

    /// Whether this id is not `TypeId::NONE`.
    #[inline]
    pub const fn is_some(self) -> bool {
        !self.is_none()
    }

    /// The arena index of this id.
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Debug for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TypeId({})", self.0)
    }
}

/// `type SignatureId uint32` — index into `SignatureArena`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct SignatureId(pub u32);

impl SignatureId {
    /// The absent value.
    pub const NONE: SignatureId = SignatureId(u32::MAX);

    /// Whether this id is `SignatureId::NONE`.
    #[inline]
    pub const fn is_none(self) -> bool {
        self.0 == Self::NONE.0
    }

    /// Whether this id is not `SignatureId::NONE`.
    #[inline]
    pub const fn is_some(self) -> bool {
        !self.is_none()
    }

    /// The arena index of this id.
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Debug for SignatureId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SignatureId({})", self.0)
    }
}

// Links for referenced symbols

/// `type SymbolReferenceLinks struct`.
#[derive(Default)]
pub struct SymbolReferenceLinks {
    /// `referenceKinds` — flags for the meanings of the symbol that were
    /// referenced.
    pub reference_kinds: SymbolFlags,
}

// Links for value symbols

/// `type ValueSymbolLinks struct`.
#[derive(Default)]
pub struct ValueSymbolLinks {
    /// `resolvedType` — type of value symbol.
    pub resolved_type: Option<TypeId>,
    /// `writeType`.
    pub write_type: Option<TypeId>,
    /// `target`.
    pub target: Option<SymbolId>,
    /// `mapper`.
    pub mapper: Option<TypeMapperId>,
    /// `nameType`.
    pub name_type: Option<TypeId>,
    /// `containingType` — mapped type for mapped type property, containing
    /// union or intersection type for synthetic property.
    pub containing_type: Option<TypeId>,
    /// `functionOrConstructorChecked`.
    pub function_or_constructor_checked: bool,
}

// Additional links for mapped symbols

/// `type MappedSymbolLinks struct`.
#[derive(Default)]
pub struct MappedSymbolLinks {
    /// `keyType` — key type for mapped type member.
    pub key_type: Option<TypeId>,
    /// `syntheticOrigin` — for a property on a mapped or spread type, points
    /// back to the original property.
    pub synthetic_origin: Option<SymbolId>,
}

// Additional links for deferred type symbols

/// `type DeferredSymbolLinks struct`.
#[derive(Default)]
pub struct DeferredSymbolLinks {
    /// `parent` — source union/intersection of a deferred type.
    pub parent: Option<TypeId>,
    /// `constituents` — calculated list of constituents for a deferred type.
    pub constituents: Vec<TypeId>,
    /// `writeConstituents` — constituents of a deferred `writeType`.
    pub write_constituents: Vec<TypeId>,
}

// Links for alias symbols

/// `type AliasSymbolLinks struct`.
#[derive(Default)]
pub struct AliasSymbolLinks {
    /// `immediateTarget` — immediate target of an alias. May be another
    /// alias. Do not access directly, use `checker.getImmediateAliasedSymbol`
    /// instead.
    pub immediate_target: Option<SymbolId>,
    /// `aliasTarget` — resolved (non-alias) target of an alias.
    pub alias_target: Option<SymbolId>,
    /// `referenced` — true if alias symbol has been referenced as a value
    /// that can be emitted.
    pub referenced: bool,
    /// `typeOnlyDeclaration` — first resolved alias declaration that makes
    /// the symbol only usable in type constructs.
    pub type_only_declaration: Option<NodeId>,
}

// Links for module symbols

/// `type ModuleSymbolLinks struct`.
#[derive(Default)]
pub struct ModuleSymbolLinks {
    /// `resolvedExports` — resolved exports of module or combined early- and
    /// late-bound static members of a class.
    pub resolved_exports: SymbolTable,
    /// `typeOnlyExportStarMap` — set on a module symbol when some of its
    /// exports were resolved through a `export type * from "mod"`
    /// declaration.
    ///
    /// PORT: `map[string]*ast.Node` → `OrderedMap<String, NodeId>` — Go map
    /// iteration order is random, but the port prefers insertion-ordered
    /// maps anywhere order could conceivably reach output (SPEC §5.2).
    pub type_only_export_star_map: tsc_ast::SymbolTable,
    /// `exportsChecked`.
    pub exports_checked: bool,
}

/// `type ReverseMappedSymbolLinks struct`.
#[derive(Default)]
pub struct ReverseMappedSymbolLinks {
    /// `propertyType`.
    pub property_type: Option<TypeId>,
    /// `mappedType` — references a mapped type.
    pub mapped_type: Option<TypeId>,
    /// `constraintType` — references an index type.
    pub constraint_type: Option<TypeId>,
}

// Links for late-bound symbols

/// `type LateBoundLinks struct`.
#[derive(Default)]
pub struct LateBoundLinks {
    /// `lateSymbol`.
    pub late_symbol: Option<SymbolId>,
}

// Links for export type symbols

/// `type ExportTypeLinks struct`.
#[derive(Default)]
pub struct ExportTypeLinks {
    /// `target` — target symbol.
    pub target: Option<SymbolId>,
    /// `originatingImport` — import declaration which produced the symbol,
    /// present if the symbol is marked as uncallable but had call signatures
    /// in `resolveESModuleSymbol`.
    pub originating_import: Option<NodeId>,
}

// Links for type aliases

/// `type TypeAliasLinks struct`.
#[derive(Default)]
pub struct TypeAliasLinks {
    /// `declaredType`.
    pub declared_type: Option<TypeId>,
    /// `typeParameters` — type parameters of type alias (empty if
    /// non-generic).
    pub type_parameters: Vec<TypeId>,
    /// `instantiations` — instantiations of generic type alias (empty if
    /// non-generic).
    pub instantiations: FxHashMap<crate::checker_core::CacheHashKey, TypeId>,
    /// `isConstructorDeclaredProperty`.
    pub is_constructor_declared_property: bool,
}

// Links for declared types (type parameters, class types, interface types,
// enums)

/// `type DeclaredTypeLinks struct`.
#[derive(Default)]
pub struct DeclaredTypeLinks {
    /// `declaredType`.
    pub declared_type: Option<TypeId>,
    /// `interfaceChecked`.
    pub interface_checked: bool,
    /// `indexSignaturesChecked`.
    pub index_signatures_checked: bool,
    /// `typeParametersChecked`.
    pub type_parameters_checked: bool,
    /// `enumChecked`.
    pub enum_checked: bool,
}

// Links for switch clauses

/// `type ExhaustiveState byte`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum ExhaustiveState {
    /// `ExhaustiveStateUnknown` — exhaustive state not computed.
    #[default]
    Unknown = 0,
    /// `ExhaustiveStateComputing` — exhaustive state computation in progress.
    Computing = 1,
    /// `ExhaustiveStateFalse` — switch statement is not exhaustive.
    False = 2,
    /// `ExhaustiveStateTrue` — switch statement is exhaustive.
    True = 3,
}

/// `type SwitchStatementLinks struct`.
#[derive(Default)]
pub struct SwitchStatementLinks {
    /// `exhaustiveState` — switch statement exhaustiveness.
    pub exhaustive_state: ExhaustiveState,
    /// `switchTypesComputed`.
    pub switch_types_computed: bool,
    /// `witnessesComputed`.
    pub witnesses_computed: bool,
    /// `switchTypes`.
    pub switch_types: Vec<TypeId>,
    /// `witnesses` — `Option` mirrors Go's nil `[]string` (a computed-but-
    /// invalid switch stores nil, distinct from "not computed" which is
    /// tracked by `witnesses_computed`).
    pub witnesses: Option<Vec<String>>,
}

/// `type ArrayLiteralLinks struct`.
#[derive(Default)]
pub struct ArrayLiteralLinks {
    /// `indicesComputed`.
    pub indices_computed: bool,
    /// `firstSpreadIndex` — index of first spread expression (or -1 if none).
    pub first_spread_index: i32,
    /// `lastSpreadIndex` — index of last spread expression (or -1 if none).
    pub last_spread_index: i32,
}

// Links for late-binding containers

/// `type MembersOrExportsResolutionKind int`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum MembersOrExportsResolutionKind {
    /// `MembersOrExportsResolutionKindResolvedExports`
    #[default]
    ResolvedExports = 0,
    /// `MembersOrExportsResolutionKindResolvedMembers`
    ResolvedMembers = 1,
}

/// `type MembersAndExportsLinks [2]ast.SymbolTable` — indexed by
/// `MembersOrExportsResolutionKind`.
#[derive(Default)]
pub struct MembersAndExportsLinks(pub [SymbolTable; 2]);

// Links for synthetic spread properties

/// `type SpreadLinks struct`.
#[derive(Default)]
pub struct SpreadLinks {
    /// `leftSpread` — left source for synthetic spread property.
    pub left_spread: Option<SymbolId>,
    /// `rightSpread` — right source for synthetic spread property.
    pub right_spread: Option<SymbolId>,
}

// Links for variances of type aliases and interface types

/// `type VarianceLinks struct`.
#[derive(Default)]
pub struct VarianceLinks {
    /// `variances`.
    pub variances: Vec<VarianceFlags>,
}

flag_type! {
    /// `type VarianceFlags uint32`.
    pub struct VarianceFlags(pub u32);
}

impl VarianceFlags {
    /// `VarianceFlagsInvariant` — neither covariant nor contravariant.
    pub const INVARIANT: VarianceFlags = VarianceFlags(0);
    /// `VarianceFlagsCovariant` — covariant.
    pub const COVARIANT: VarianceFlags = VarianceFlags(1 << 0);
    /// `VarianceFlagsContravariant` — contravariant.
    pub const CONTRAVARIANT: VarianceFlags = VarianceFlags(1 << 1);
    /// `VarianceFlagsBivariant` — both covariant and contravariant.
    pub const BIVARIANT: VarianceFlags = VarianceFlags(Self::COVARIANT.0 | Self::CONTRAVARIANT.0);
    /// `VarianceFlagsIndependent` — unwitnessed type parameter.
    pub const INDEPENDENT: VarianceFlags = VarianceFlags(1 << 2);
    /// `VarianceFlagsVarianceMask` — mask containing all measured variances
    /// without the unmeasurable flag.
    pub const VARIANCE_MASK: VarianceFlags = VarianceFlags(
        Self::INVARIANT.0 | Self::COVARIANT.0 | Self::CONTRAVARIANT.0 | Self::INDEPENDENT.0,
    );
    /// `VarianceFlagsUnmeasurable` — variance result is unusable:
    /// relationship relies on structural comparisons which are not reflected
    /// in generic relationships.
    pub const UNMEASURABLE: VarianceFlags = VarianceFlags(1 << 3);
    /// `VarianceFlagsUnreliable` — variance result is unreliable: checking
    /// may produce false negatives, but not false positives.
    pub const UNRELIABLE: VarianceFlags = VarianceFlags(1 << 4);
    /// `VarianceFlagsAllowsStructuralFallback`.
    pub const ALLOWS_STRUCTURAL_FALLBACK: VarianceFlags =
        VarianceFlags(Self::UNMEASURABLE.0 | Self::UNRELIABLE.0);
}

/// `type MarkedAssignmentSymbolLinks struct`.
#[derive(Default)]
pub struct MarkedAssignmentSymbolLinks {
    /// `lastAssignmentPos`.
    pub last_assignment_pos: i32,
    /// `hasDefiniteAssignment` — symbol is definitely assigned somewhere.
    pub has_definite_assignment: bool,
}

/// `type accessibleChainCacheKey struct`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct AccessibleChainCacheKey {
    /// `useOnlyExternalAliasing`.
    pub use_only_external_aliasing: bool,
    /// `location` — `NodeId::NONE` mirrors Go's nil `*ast.Node` key member.
    pub location: NodeId,
    /// `meaning`.
    pub meaning: SymbolFlags,
}

/// `type ContainingSymbolLinks struct`.
#[derive(Default)]
pub struct ContainingSymbolLinks {
    /// `extendedContainersByFile` — symbols of nodes which logically contain
    /// this one, cached by file the request is made within.
    pub extended_containers_by_file: FxHashMap<NodeId, Vec<SymbolId>>,
    /// `extendedContainers` — containers (other than the parent) which this
    /// symbol is aliased in.
    pub extended_containers: Option<Vec<SymbolId>>,
    /// `accessibleChainCache`.
    pub accessible_chain_cache: FxHashMap<AccessibleChainCacheKey, Vec<SymbolId>>,
}

flag_type! {
    /// `type AccessFlags uint32`.
    pub struct AccessFlags(pub u32);
}

impl AccessFlags {
    /// `AccessFlagsIncludeUndefined`.
    pub const INCLUDE_UNDEFINED: AccessFlags = AccessFlags(1 << 0);
    /// `AccessFlagsNoIndexSignatures`.
    pub const NO_INDEX_SIGNATURES: AccessFlags = AccessFlags(1 << 1);
    /// `AccessFlagsWriting`.
    pub const WRITING: AccessFlags = AccessFlags(1 << 2);
    /// `AccessFlagsCacheSymbol`.
    pub const CACHE_SYMBOL: AccessFlags = AccessFlags(1 << 3);
    /// `AccessFlagsAllowMissing`.
    pub const ALLOW_MISSING: AccessFlags = AccessFlags(1 << 4);
    /// `AccessFlagsExpressionPosition`.
    pub const EXPRESSION_POSITION: AccessFlags = AccessFlags(1 << 5);
    /// `AccessFlagsReportDeprecated`.
    pub const REPORT_DEPRECATED: AccessFlags = AccessFlags(1 << 6);
    /// `AccessFlagsSuppressNoImplicitAnyError`.
    pub const SUPPRESS_NO_IMPLICIT_ANY_ERROR: AccessFlags = AccessFlags(1 << 7);
    /// `AccessFlagsContextual`.
    pub const CONTEXTUAL: AccessFlags = AccessFlags(1 << 8);
    /// `AccessFlagsPersistent`.
    pub const PERSISTENT: AccessFlags = Self::INCLUDE_UNDEFINED;
}

flag_type! {
    /// `type NodeCheckFlags uint32`.
    pub struct NodeCheckFlags(pub u32);
}

impl NodeCheckFlags {
    /// `NodeCheckFlagsTypeChecked` — node has been type checked.
    pub const TYPE_CHECKED: NodeCheckFlags = NodeCheckFlags(1 << 0);
    /// `NodeCheckFlagsContextChecked` — contextual types have been assigned.
    pub const CONTEXT_CHECKED: NodeCheckFlags = NodeCheckFlags(1 << 6);
    /// `NodeCheckFlagsEnumValuesComputed` — values for enum members have been
    /// computed, and any errors have been reported for them.
    pub const ENUM_VALUES_COMPUTED: NodeCheckFlags = NodeCheckFlags(1 << 10);
    /// `NodeCheckFlagsAssignmentsMarked` — parameter assignments have been
    /// marked.
    pub const ASSIGNMENTS_MARKED: NodeCheckFlags = NodeCheckFlags(1 << 17);
    /// `NodeCheckFlagsContainsClassWithPrivateIdentifiers` — marked on all
    /// block-scoped containers containing a class with private identifiers.
    pub const CONTAINS_CLASS_WITH_PRIVATE_IDENTIFIERS: NodeCheckFlags = NodeCheckFlags(1 << 20);
    /// `NodeCheckFlagsContainsSuperPropertyInStaticInitializer` — marked on
    /// all block-scoped containers containing a static initializer with
    /// `super.x` or `super[x]`.
    pub const CONTAINS_SUPER_PROPERTY_IN_STATIC_INITIALIZER: NodeCheckFlags =
        NodeCheckFlags(1 << 21);
    /// `NodeCheckFlagsInCheckIdentifier`.
    pub const IN_CHECK_IDENTIFIER: NodeCheckFlags = NodeCheckFlags(1 << 22);
    /// `NodeCheckFlagsInitializerIsUndefined`.
    pub const INITIALIZER_IS_UNDEFINED: NodeCheckFlags = NodeCheckFlags(1 << 24);
    /// `NodeCheckFlagsInitializerIsUndefinedComputed`.
    pub const INITIALIZER_IS_UNDEFINED_COMPUTED: NodeCheckFlags = NodeCheckFlags(1 << 25);
}

// Common links

/// `type NodeLinks struct`.
#[derive(Default)]
pub struct NodeLinks {
    /// `flags` — set of flags specific to Node.
    pub flags: NodeCheckFlags,
    /// `declarationRequiresScopeChange` — set by
    /// `useOuterVariableScopeInParameter` in checker when downlevel emit
    /// would change the name resolution scope inside of a parameter.
    pub declaration_requires_scope_change: Tristate,
    /// `hasReportedStatementInAmbientContext` — cache boolean if we report
    /// statements in ambient context.
    pub has_reported_statement_in_ambient_context: bool,
}

/// `type SymbolNodeLinks struct`.
#[derive(Default)]
pub struct SymbolNodeLinks {
    /// `resolvedSymbol` — resolved symbol associated with node.
    pub resolved_symbol: Option<SymbolId>,
}

/// `type TypeNodeLinks struct`.
#[derive(Default)]
pub struct TypeNodeLinks {
    /// `resolvedType` — resolved type associated with node.
    pub resolved_type: Option<TypeId>,
    /// `outerTypeParameters` — outer type parameters of anonymous object
    /// type.
    pub outer_type_parameters: Vec<TypeId>,
}

/// `type ComputedNameNodeLinks struct`.
#[derive(Default)]
pub struct ComputedNameNodeLinks {
    /// `hasName` — if the node has a computable name.
    pub has_name: Option<bool>,
    /// `name` — resolved name associated with the type of the node.
    pub name: String,
}

// Links for enum members

/// `type EnumMemberLinks struct`.
#[derive(Default)]
pub struct EnumMemberLinks {
    /// `value` — constant value of enum member.
    pub value: evaluator::Result,
}

// Links for assertion expressions

/// `type AssertionLinks struct`.
#[derive(Default)]
pub struct AssertionLinks {
    /// `exprType` — assertion expression type.
    pub expr_type: Option<TypeId>,
}

// SourceFile links

/// `type SourceFileLinks struct`.
#[derive(Default)]
pub struct SourceFileLinks {
    /// `typeChecked`.
    pub type_checked: bool,
    /// `unusedChecked`.
    pub unused_checked: bool,
    /// `externalHelpersModule`.
    pub external_helpers_module: Option<SymbolId>,
    /// `requestedExternalEmitHelpers`.
    pub requested_external_emit_helpers: ExternalEmitHelpers,
    /// `deferredNodes`.
    pub deferred_nodes: OrderedSet<NodeId>,
    /// `identifierCheckNodes`.
    pub identifier_check_nodes: Vec<NodeId>,
    /// `localJsxNamespace`.
    pub local_jsx_namespace: String,
    /// `localJsxFragmentNamespace`.
    pub local_jsx_fragment_namespace: String,
    /// `localJsxFactory`.
    pub local_jsx_factory: Option<NodeId>,
    /// `localJsxFragmentFactory`.
    pub local_jsx_fragment_factory: Option<NodeId>,
    /// `jsxFragmentType`.
    pub jsx_fragment_type: Option<TypeId>,
}

// Signature specific links

/// `type SignatureLinks struct`.
#[derive(Default)]
pub struct SignatureLinks {
    /// `resolvedSignature` — cached signature of signature node or call
    /// expression.
    pub resolved_signature: Option<SignatureId>,
    /// `effectsSignature` — signature with possible control flow effects.
    pub effects_signature: Option<SignatureId>,
    /// `decoratorSignature` — signature for decorator as if invoked by the
    /// runtime.
    pub decorator_signature: Option<SignatureId>,
}

flag_type! {
    /// `type TypeFlags uint32`.
    ///
    /// Note that for types of different kinds, the numeric values of
    /// TypeFlags determine the order computed by the CompareTypes function
    /// and therefore the order of constituent types in union types. Since
    /// union type processing often bails out early when a result is known, it
    /// is important to order TypeFlags in increasing order of potential type
    /// complexity. In particular, indexed access and conditional types should
    /// sort last as those types are potentially recursive and possibly
    /// infinite.
    pub struct TypeFlags(pub u32);
}

impl TypeFlags {
    /// `TypeFlagsAny`.
    pub const ANY: TypeFlags = TypeFlags(1 << 0);
    /// `TypeFlagsUnknown`.
    pub const UNKNOWN: TypeFlags = TypeFlags(1 << 1);
    /// `TypeFlagsUndefined`.
    pub const UNDEFINED: TypeFlags = TypeFlags(1 << 2);
    /// `TypeFlagsNull`.
    pub const NULL: TypeFlags = TypeFlags(1 << 3);
    /// `TypeFlagsVoid`.
    pub const VOID: TypeFlags = TypeFlags(1 << 4);
    /// `TypeFlagsString`.
    pub const STRING: TypeFlags = TypeFlags(1 << 5);
    /// `TypeFlagsNumber`.
    pub const NUMBER: TypeFlags = TypeFlags(1 << 6);
    /// `TypeFlagsBigInt`.
    pub const BIG_INT: TypeFlags = TypeFlags(1 << 7);
    /// `TypeFlagsBoolean`.
    pub const BOOLEAN: TypeFlags = TypeFlags(1 << 8);
    /// `TypeFlagsESSymbol` — type of symbol primitive introduced in ES6.
    pub const ES_SYMBOL: TypeFlags = TypeFlags(1 << 9);
    /// `TypeFlagsStringLiteral`.
    pub const STRING_LITERAL: TypeFlags = TypeFlags(1 << 10);
    /// `TypeFlagsNumberLiteral`.
    pub const NUMBER_LITERAL: TypeFlags = TypeFlags(1 << 11);
    /// `TypeFlagsBigIntLiteral`.
    pub const BIG_INT_LITERAL: TypeFlags = TypeFlags(1 << 12);
    /// `TypeFlagsBooleanLiteral`.
    pub const BOOLEAN_LITERAL: TypeFlags = TypeFlags(1 << 13);
    /// `TypeFlagsUniqueESSymbol` — `unique symbol`.
    pub const UNIQUE_ES_SYMBOL: TypeFlags = TypeFlags(1 << 14);
    /// `TypeFlagsEnumLiteral` — always combined with `StringLiteral`,
    /// `NumberLiteral`, or `Union`.
    pub const ENUM_LITERAL: TypeFlags = TypeFlags(1 << 15);
    /// `TypeFlagsEnum` — numeric computed enum member value (must be right
    /// after `EnumLiteral`, see `getSortOrderFlags`).
    pub const ENUM: TypeFlags = TypeFlags(1 << 16);
    /// `TypeFlagsNonPrimitive` — intrinsic object type.
    pub const NON_PRIMITIVE: TypeFlags = TypeFlags(1 << 17);
    /// `TypeFlagsNever` — never type.
    pub const NEVER: TypeFlags = TypeFlags(1 << 18);
    /// `TypeFlagsTypeParameter` — type parameter.
    pub const TYPE_PARAMETER: TypeFlags = TypeFlags(1 << 19);
    /// `TypeFlagsObject` — object type.
    pub const OBJECT: TypeFlags = TypeFlags(1 << 20);
    /// `TypeFlagsIndex` — `keyof T`.
    pub const INDEX: TypeFlags = TypeFlags(1 << 21);
    /// `TypeFlagsTemplateLiteral` — template literal type.
    pub const TEMPLATE_LITERAL: TypeFlags = TypeFlags(1 << 22);
    /// `TypeFlagsStringMapping` — `Uppercase`/`Lowercase` type.
    pub const STRING_MAPPING: TypeFlags = TypeFlags(1 << 23);
    /// `TypeFlagsSubstitution` — type parameter substitution.
    pub const SUBSTITUTION: TypeFlags = TypeFlags(1 << 24);
    /// `TypeFlagsIndexedAccess` — `T[K]`.
    pub const INDEXED_ACCESS: TypeFlags = TypeFlags(1 << 25);
    /// `TypeFlagsConditional` — `T extends U ? X : Y`.
    pub const CONDITIONAL: TypeFlags = TypeFlags(1 << 26);
    /// `TypeFlagsUnion` — union (`T | U`).
    pub const UNION: TypeFlags = TypeFlags(1 << 27);
    /// `TypeFlagsIntersection` — intersection (`T & U`).
    pub const INTERSECTION: TypeFlags = TypeFlags(1 << 28);
    /// `TypeFlagsReserved1` — used by union/intersection type construction.
    pub const RESERVED1: TypeFlags = TypeFlags(1 << 29);
    /// `TypeFlagsReserved2` — used by union/intersection type construction.
    pub const RESERVED2: TypeFlags = TypeFlags(1 << 30);
    /// `TypeFlagsReserved3`.
    pub const RESERVED3: TypeFlags = TypeFlags(1 << 31);

    /// `TypeFlagsAnyOrUnknown`.
    pub const ANY_OR_UNKNOWN: TypeFlags = TypeFlags(Self::ANY.0 | Self::UNKNOWN.0);
    /// `TypeFlagsNullable`.
    pub const NULLABLE: TypeFlags = TypeFlags(Self::UNDEFINED.0 | Self::NULL.0);
    /// `TypeFlagsLiteral`.
    pub const LITERAL: TypeFlags = TypeFlags(
        Self::STRING_LITERAL.0
            | Self::NUMBER_LITERAL.0
            | Self::BIG_INT_LITERAL.0
            | Self::BOOLEAN_LITERAL.0,
    );
    /// `TypeFlagsUnit`.
    pub const UNIT: TypeFlags =
        TypeFlags(Self::ENUM.0 | Self::LITERAL.0 | Self::UNIQUE_ES_SYMBOL.0 | Self::NULLABLE.0);
    /// `TypeFlagsFreshable`.
    pub const FRESHABLE: TypeFlags = TypeFlags(Self::ENUM.0 | Self::LITERAL.0);
    /// `TypeFlagsStringOrNumberLiteral`.
    pub const STRING_OR_NUMBER_LITERAL: TypeFlags =
        TypeFlags(Self::STRING_LITERAL.0 | Self::NUMBER_LITERAL.0);
    /// `TypeFlagsStringOrNumberLiteralOrUnique`.
    pub const STRING_OR_NUMBER_LITERAL_OR_UNIQUE: TypeFlags =
        TypeFlags(Self::STRING_LITERAL.0 | Self::NUMBER_LITERAL.0 | Self::UNIQUE_ES_SYMBOL.0);
    /// `TypeFlagsDefinitelyFalsy`.
    pub const DEFINITELY_FALSY: TypeFlags = TypeFlags(
        Self::STRING_LITERAL.0
            | Self::NUMBER_LITERAL.0
            | Self::BIG_INT_LITERAL.0
            | Self::BOOLEAN_LITERAL.0
            | Self::VOID.0
            | Self::UNDEFINED.0
            | Self::NULL.0,
    );
    /// `TypeFlagsPossiblyFalsy`.
    pub const POSSIBLY_FALSY: TypeFlags = TypeFlags(
        Self::DEFINITELY_FALSY.0
            | Self::STRING.0
            | Self::NUMBER.0
            | Self::BIG_INT.0
            | Self::BOOLEAN.0,
    );
    /// `TypeFlagsIntrinsic`.
    pub const INTRINSIC: TypeFlags = TypeFlags(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::STRING.0
            | Self::NUMBER.0
            | Self::BIG_INT.0
            | Self::ES_SYMBOL.0
            | Self::VOID.0
            | Self::UNDEFINED.0
            | Self::NULL.0
            | Self::NEVER.0
            | Self::NON_PRIMITIVE.0,
    );
    /// `TypeFlagsStringLike`.
    pub const STRING_LIKE: TypeFlags = TypeFlags(
        Self::STRING.0 | Self::STRING_LITERAL.0 | Self::TEMPLATE_LITERAL.0 | Self::STRING_MAPPING.0,
    );
    /// `TypeFlagsNumberLike`.
    pub const NUMBER_LIKE: TypeFlags =
        TypeFlags(Self::NUMBER.0 | Self::NUMBER_LITERAL.0 | Self::ENUM.0);
    /// `TypeFlagsBigIntLike`.
    pub const BIG_INT_LIKE: TypeFlags = TypeFlags(Self::BIG_INT.0 | Self::BIG_INT_LITERAL.0);
    /// `TypeFlagsBooleanLike`.
    pub const BOOLEAN_LIKE: TypeFlags = TypeFlags(Self::BOOLEAN.0 | Self::BOOLEAN_LITERAL.0);
    /// `TypeFlagsEnumLike`.
    pub const ENUM_LIKE: TypeFlags = TypeFlags(Self::ENUM.0 | Self::ENUM_LITERAL.0);
    /// `TypeFlagsESSymbolLike`.
    pub const ES_SYMBOL_LIKE: TypeFlags = TypeFlags(Self::ES_SYMBOL.0 | Self::UNIQUE_ES_SYMBOL.0);
    /// `TypeFlagsVoidLike`.
    pub const VOID_LIKE: TypeFlags = TypeFlags(Self::VOID.0 | Self::UNDEFINED.0);
    /// `TypeFlagsPrimitive`.
    pub const PRIMITIVE: TypeFlags = TypeFlags(
        Self::STRING_LIKE.0
            | Self::NUMBER_LIKE.0
            | Self::BIG_INT_LIKE.0
            | Self::BOOLEAN_LIKE.0
            | Self::ENUM_LIKE.0
            | Self::ES_SYMBOL_LIKE.0
            | Self::VOID_LIKE.0
            | Self::NULL.0,
    );
    /// `TypeFlagsDefinitelyNonNullable`.
    pub const DEFINITELY_NON_NULLABLE: TypeFlags = TypeFlags(
        Self::STRING_LIKE.0
            | Self::NUMBER_LIKE.0
            | Self::BIG_INT_LIKE.0
            | Self::BOOLEAN_LIKE.0
            | Self::ENUM_LIKE.0
            | Self::ES_SYMBOL_LIKE.0
            | Self::OBJECT.0
            | Self::NON_PRIMITIVE.0,
    );
    /// `TypeFlagsDisjointDomains`.
    pub const DISJOINT_DOMAINS: TypeFlags = TypeFlags(
        Self::NON_PRIMITIVE.0
            | Self::STRING_LIKE.0
            | Self::NUMBER_LIKE.0
            | Self::BIG_INT_LIKE.0
            | Self::BOOLEAN_LIKE.0
            | Self::ES_SYMBOL_LIKE.0
            | Self::VOID_LIKE.0
            | Self::NULL.0,
    );
    /// `TypeFlagsUnionOrIntersection`.
    pub const UNION_OR_INTERSECTION: TypeFlags = TypeFlags(Self::UNION.0 | Self::INTERSECTION.0);
    /// `TypeFlagsStructuredType`.
    pub const STRUCTURED_TYPE: TypeFlags =
        TypeFlags(Self::OBJECT.0 | Self::UNION.0 | Self::INTERSECTION.0);
    /// `TypeFlagsTypeVariable`.
    pub const TYPE_VARIABLE: TypeFlags = TypeFlags(Self::TYPE_PARAMETER.0 | Self::INDEXED_ACCESS.0);
    /// `TypeFlagsInstantiableNonPrimitive`.
    pub const INSTANTIABLE_NON_PRIMITIVE: TypeFlags =
        TypeFlags(Self::TYPE_VARIABLE.0 | Self::CONDITIONAL.0 | Self::SUBSTITUTION.0);
    /// `TypeFlagsInstantiablePrimitive`.
    pub const INSTANTIABLE_PRIMITIVE: TypeFlags =
        TypeFlags(Self::INDEX.0 | Self::TEMPLATE_LITERAL.0 | Self::STRING_MAPPING.0);
    /// `TypeFlagsInstantiable`.
    pub const INSTANTIABLE: TypeFlags =
        TypeFlags(Self::INSTANTIABLE_NON_PRIMITIVE.0 | Self::INSTANTIABLE_PRIMITIVE.0);
    /// `TypeFlagsStructuredOrInstantiable`.
    pub const STRUCTURED_OR_INSTANTIABLE: TypeFlags =
        TypeFlags(Self::STRUCTURED_TYPE.0 | Self::INSTANTIABLE.0);
    /// `TypeFlagsObjectFlagsType`.
    pub const OBJECT_FLAGS_TYPE: TypeFlags = TypeFlags(
        Self::ANY.0
            | Self::NULLABLE.0
            | Self::NEVER.0
            | Self::OBJECT.0
            | Self::UNION.0
            | Self::INTERSECTION.0,
    );
    /// `TypeFlagsSimplifiable`.
    pub const SIMPLIFIABLE: TypeFlags =
        TypeFlags(Self::INDEXED_ACCESS.0 | Self::CONDITIONAL.0 | Self::INDEX.0);
    /// `TypeFlagsSingleton`.
    pub const SINGLETON: TypeFlags = TypeFlags(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::STRING.0
            | Self::NUMBER.0
            | Self::BOOLEAN.0
            | Self::BIG_INT.0
            | Self::ES_SYMBOL.0
            | Self::VOID.0
            | Self::UNDEFINED.0
            | Self::NULL.0
            | Self::NEVER.0
            | Self::NON_PRIMITIVE.0,
    );
    /// `TypeFlagsNarrowable` — types where narrowing actually narrows. This
    /// *should* be every type other than null, undefined, void, and never.
    pub const NARROWABLE: TypeFlags = TypeFlags(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::STRUCTURED_OR_INSTANTIABLE.0
            | Self::STRING_LIKE.0
            | Self::NUMBER_LIKE.0
            | Self::BIG_INT_LIKE.0
            | Self::BOOLEAN_LIKE.0
            | Self::ES_SYMBOL.0
            | Self::UNIQUE_ES_SYMBOL.0
            | Self::NON_PRIMITIVE.0,
    );
    /// `TypeFlagsIncludesMask` — flags aggregated during union and
    /// intersection type construction.
    pub const INCLUDES_MASK: TypeFlags = TypeFlags(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::PRIMITIVE.0
            | Self::NEVER.0
            | Self::OBJECT.0
            | Self::UNION.0
            | Self::INTERSECTION.0
            | Self::NON_PRIMITIVE.0
            | Self::TEMPLATE_LITERAL.0
            | Self::STRING_MAPPING.0,
    );
    /// `TypeFlagsIncludesMissingType` — used for different purposes during
    /// union and intersection type construction.
    pub const INCLUDES_MISSING_TYPE: TypeFlags = Self::TYPE_PARAMETER;
    /// `TypeFlagsIncludesNonWideningType`.
    pub const INCLUDES_NON_WIDENING_TYPE: TypeFlags = Self::INDEX;
    /// `TypeFlagsIncludesWildcard`.
    pub const INCLUDES_WILDCARD: TypeFlags = Self::INDEXED_ACCESS;
    /// `TypeFlagsIncludesEmptyObject`.
    pub const INCLUDES_EMPTY_OBJECT: TypeFlags = Self::CONDITIONAL;
    /// `TypeFlagsIncludesInstantiable`.
    pub const INCLUDES_INSTANTIABLE: TypeFlags = Self::SUBSTITUTION;
    /// `TypeFlagsIncludesConstrainedTypeVariable`.
    pub const INCLUDES_CONSTRAINED_TYPE_VARIABLE: TypeFlags = Self::RESERVED1;
    /// `TypeFlagsIncludesError`.
    pub const INCLUDES_ERROR: TypeFlags = Self::RESERVED2;
    /// `TypeFlagsNotPrimitiveUnion`.
    pub const NOT_PRIMITIVE_UNION: TypeFlags = TypeFlags(
        Self::ANY.0
            | Self::UNKNOWN.0
            | Self::VOID.0
            | Self::NEVER.0
            | Self::OBJECT.0
            | Self::INTERSECTION.0
            | Self::INCLUDES_INSTANTIABLE.0,
    );
}

/// `typeFlagNames` — the (flag, name) table iterated by `FormatTypeFlags`.
const TYPE_FLAG_NAMES: [(TypeFlags, &str); 28] = [
    (TypeFlags::ANY, "Any"),
    (TypeFlags::UNKNOWN, "Unknown"),
    (TypeFlags::UNDEFINED, "Undefined"),
    (TypeFlags::NULL, "Null"),
    (TypeFlags::VOID, "Void"),
    (TypeFlags::STRING, "String"),
    (TypeFlags::NUMBER, "Number"),
    (TypeFlags::BIG_INT, "BigInt"),
    (TypeFlags::BOOLEAN, "Boolean"),
    (TypeFlags::ES_SYMBOL, "ESSymbol"),
    (TypeFlags::STRING_LITERAL, "StringLiteral"),
    (TypeFlags::NUMBER_LITERAL, "NumberLiteral"),
    (TypeFlags::BIG_INT_LITERAL, "BigIntLiteral"),
    (TypeFlags::BOOLEAN_LITERAL, "BooleanLiteral"),
    (TypeFlags::UNIQUE_ES_SYMBOL, "UniqueESSymbol"),
    (TypeFlags::ENUM_LITERAL, "EnumLiteral"),
    (TypeFlags::ENUM, "Enum"),
    (TypeFlags::NON_PRIMITIVE, "NonPrimitive"),
    (TypeFlags::NEVER, "Never"),
    (TypeFlags::TYPE_PARAMETER, "TypeParameter"),
    (TypeFlags::OBJECT, "Object"),
    (TypeFlags::INDEX, "Index"),
    (TypeFlags::TEMPLATE_LITERAL, "TemplateLiteral"),
    (TypeFlags::STRING_MAPPING, "StringMapping"),
    (TypeFlags::SUBSTITUTION, "Substitution"),
    (TypeFlags::INDEXED_ACCESS, "IndexedAccess"),
    (TypeFlags::CONDITIONAL, "Conditional"),
    (TypeFlags::UNION, "Union"),
];

/// `FormatTypeFlags` returns the individual flag names as a slice of strings.
pub fn format_type_flags(flags: TypeFlags) -> Vec<String> {
    // Go sizes the result with bits.OnesCount32(flags); the push loop needs
    // no pre-sizing fidelity.
    let mut result = Vec::new();
    for (flag, name) in TYPE_FLAG_NAMES {
        if flags.intersects(flag) {
            result.push(name.to_string());
        }
    }
    if result.is_empty() {
        result.push("None".to_string());
    }
    result
}

impl fmt::Display for TypeFlags {
    /// `(f TypeFlags) String` — pipe-separated flag names.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&format_type_flags(*self).join("|"))
    }
}

impl fmt::Display for VarianceFlags {
    /// `(v VarianceFlags) String`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let variance = *self & VarianceFlags::VARIANCE_MASK;
        let mut result = match variance {
            VarianceFlags::INVARIANT => "in out",
            VarianceFlags::BIVARIANT => "[bivariant]",
            VarianceFlags::CONTRAVARIANT => "in",
            VarianceFlags::COVARIANT => "out",
            VarianceFlags::INDEPENDENT => "[independent]",
            _ => "",
        }
        .to_string();
        if self.intersects(VarianceFlags::UNMEASURABLE) {
            result += " (unmeasurable)";
        } else if self.intersects(VarianceFlags::UNRELIABLE) {
            result += " (unreliable)";
        }
        f.write_str(&result)
    }
}

flag_type! {
    /// `type ObjectFlags uint32`.
    ///
    /// Types included in `TypeFlags::OBJECT_FLAGS_TYPE` have an objectFlags
    /// property. Some ObjectFlags are specific to certain types and reuse the
    /// same bit position. Those ObjectFlags require a check for a certain
    /// TypeFlags value to determine their meaning.
    pub struct ObjectFlags(pub u32);
}

impl ObjectFlags {
    /// `ObjectFlagsClass` — class.
    pub const CLASS: ObjectFlags = ObjectFlags(1 << 0);
    /// `ObjectFlagsInterface` — interface.
    pub const INTERFACE: ObjectFlags = ObjectFlags(1 << 1);
    /// `ObjectFlagsReference` — generic type reference.
    pub const REFERENCE: ObjectFlags = ObjectFlags(1 << 2);
    /// `ObjectFlagsTuple` — synthesized generic tuple type.
    pub const TUPLE: ObjectFlags = ObjectFlags(1 << 3);
    /// `ObjectFlagsAnonymous` — anonymous.
    pub const ANONYMOUS: ObjectFlags = ObjectFlags(1 << 4);
    /// `ObjectFlagsMapped` — mapped.
    pub const MAPPED: ObjectFlags = ObjectFlags(1 << 5);
    /// `ObjectFlagsInstantiated` — instantiated anonymous or mapped type.
    pub const INSTANTIATED: ObjectFlags = ObjectFlags(1 << 6);
    /// `ObjectFlagsObjectLiteral` — originates in an object literal.
    pub const OBJECT_LITERAL: ObjectFlags = ObjectFlags(1 << 7);
    /// `ObjectFlagsEvolvingArray` — evolving array type.
    pub const EVOLVING_ARRAY: ObjectFlags = ObjectFlags(1 << 8);
    /// `ObjectFlagsObjectLiteralPatternWithComputedProperties` — object
    /// literal pattern with computed properties.
    pub const OBJECT_LITERAL_PATTERN_WITH_COMPUTED_PROPERTIES: ObjectFlags = ObjectFlags(1 << 9);
    /// `ObjectFlagsReverseMapped` — object contains a property from a
    /// reverse-mapped type.
    pub const REVERSE_MAPPED: ObjectFlags = ObjectFlags(1 << 10);
    /// `ObjectFlagsJsxAttributes` — JSX attributes type.
    pub const JSX_ATTRIBUTES: ObjectFlags = ObjectFlags(1 << 11);
    /// `ObjectFlagsJSLiteral` — object type declared in JS: disables errors
    /// on read/write of nonexisting members.
    pub const JS_LITERAL: ObjectFlags = ObjectFlags(1 << 12);
    /// `ObjectFlagsFreshLiteral` — fresh object literal.
    pub const FRESH_LITERAL: ObjectFlags = ObjectFlags(1 << 13);
    /// `ObjectFlagsArrayLiteral` — originates in an array literal.
    pub const ARRAY_LITERAL: ObjectFlags = ObjectFlags(1 << 14);
    /// `ObjectFlagsPrimitiveUnion` — union of only primitive types.
    pub const PRIMITIVE_UNION: ObjectFlags = ObjectFlags(1 << 15);
    /// `ObjectFlagsContainsWideningType` — type is or contains undefined or
    /// null widening type.
    pub const CONTAINS_WIDENING_TYPE: ObjectFlags = ObjectFlags(1 << 16);
    /// `ObjectFlagsContainsObjectOrArrayLiteral` — type is or contains
    /// object literal type.
    pub const CONTAINS_OBJECT_OR_ARRAY_LITERAL: ObjectFlags = ObjectFlags(1 << 17);
    /// `ObjectFlagsNonInferrableType` — type is or contains anyFunctionType
    /// or silentNeverType.
    pub const NON_INFERRABLE_TYPE: ObjectFlags = ObjectFlags(1 << 18);
    /// `ObjectFlagsCouldContainTypeVariablesComputed` —
    /// `couldContainTypeVariables` flag has been computed.
    pub const COULD_CONTAIN_TYPE_VARIABLES_COMPUTED: ObjectFlags = ObjectFlags(1 << 19);
    /// `ObjectFlagsCouldContainTypeVariables` — type could contain a type
    /// variable.
    pub const COULD_CONTAIN_TYPE_VARIABLES: ObjectFlags = ObjectFlags(1 << 20);
    /// `ObjectFlagsMembersResolved` — members have been resolved.
    pub const MEMBERS_RESOLVED: ObjectFlags = ObjectFlags(1 << 21);

    /// `ObjectFlagsClassOrInterface`.
    pub const CLASS_OR_INTERFACE: ObjectFlags = ObjectFlags(Self::CLASS.0 | Self::INTERFACE.0);
    /// `ObjectFlagsRequiresWidening`.
    pub const REQUIRES_WIDENING: ObjectFlags =
        ObjectFlags(Self::CONTAINS_WIDENING_TYPE.0 | Self::CONTAINS_OBJECT_OR_ARRAY_LITERAL.0);
    /// `ObjectFlagsPropagatingFlags`.
    pub const PROPAGATING_FLAGS: ObjectFlags = ObjectFlags(
        Self::CONTAINS_WIDENING_TYPE.0
            | Self::CONTAINS_OBJECT_OR_ARRAY_LITERAL.0
            | Self::NON_INFERRABLE_TYPE.0,
    );
    /// `ObjectFlagsInstantiatedMapped`.
    pub const INSTANTIATED_MAPPED: ObjectFlags = ObjectFlags(Self::MAPPED.0 | Self::INSTANTIATED.0);
    /// `ObjectFlagsObjectTypeKindMask` — object flags that uniquely identify
    /// the kind of `ObjectType`.
    pub const OBJECT_TYPE_KIND_MASK: ObjectFlags = ObjectFlags(
        Self::CLASS_OR_INTERFACE.0
            | Self::REFERENCE.0
            | Self::TUPLE.0
            | Self::ANONYMOUS.0
            | Self::MAPPED.0
            | Self::REVERSE_MAPPED.0
            | Self::EVOLVING_ARRAY.0
            | Self::INSTANTIATION_EXPRESSION_TYPE.0
            | Self::SINGLE_SIGNATURE_TYPE.0,
    );

    // Flags that require TypeFlags.Object
    /// `ObjectFlagsContainsSpread` — object literal contains spread
    /// operation.
    pub const CONTAINS_SPREAD: ObjectFlags = ObjectFlags(1 << 22);
    /// `ObjectFlagsObjectRestType` — originates in object rest declaration.
    pub const OBJECT_REST_TYPE: ObjectFlags = ObjectFlags(1 << 23);
    /// `ObjectFlagsInstantiationExpressionType` — originates in
    /// instantiation expression.
    pub const INSTANTIATION_EXPRESSION_TYPE: ObjectFlags = ObjectFlags(1 << 24);
    /// `ObjectFlagsSingleSignatureType` — a single signature type extracted
    /// from a potentially broader type.
    pub const SINGLE_SIGNATURE_TYPE: ObjectFlags = ObjectFlags(1 << 25);
    /// `ObjectFlagsIsClassInstanceClone` — type is a clone of a class
    /// instance type.
    pub const IS_CLASS_INSTANCE_CLONE: ObjectFlags = ObjectFlags(1 << 26);
    // Flags that require TypeFlags.Object and ObjectFlags.Reference
    /// `ObjectFlagsIdenticalBaseTypeCalculated` — has had
    /// `getSingleBaseForNonAugmentingSubtype` invoked on it already.
    pub const IDENTICAL_BASE_TYPE_CALCULATED: ObjectFlags = ObjectFlags(1 << 27);
    /// `ObjectFlagsIdenticalBaseTypeExists` — has a defined
    /// `cachedEquivalentBaseType` member.
    pub const IDENTICAL_BASE_TYPE_EXISTS: ObjectFlags = ObjectFlags(1 << 28);
    /// `ObjectFlagsFromTypeNode` — originates in resolution of AST type node.
    pub const FROM_TYPE_NODE: ObjectFlags = ObjectFlags(1 << 29);
    // Flags that require TypeFlags.UnionOrIntersection or TypeFlags.Substitution
    /// `ObjectFlagsIsGenericTypeComputed` — `isGenericObjectType` flag has
    /// been computed.
    pub const IS_GENERIC_TYPE_COMPUTED: ObjectFlags = ObjectFlags(1 << 22);
    /// `ObjectFlagsIsGenericObjectType` — union or intersection contains
    /// generic object type.
    pub const IS_GENERIC_OBJECT_TYPE: ObjectFlags = ObjectFlags(1 << 23);
    /// `ObjectFlagsIsGenericIndexType` — union or intersection contains
    /// generic index type.
    pub const IS_GENERIC_INDEX_TYPE: ObjectFlags = ObjectFlags(1 << 24);
    /// `ObjectFlagsIsGenericType`.
    pub const IS_GENERIC_TYPE: ObjectFlags =
        ObjectFlags(Self::IS_GENERIC_OBJECT_TYPE.0 | Self::IS_GENERIC_INDEX_TYPE.0);
    // Flags that require TypeFlags.Union
    /// `ObjectFlagsContainsIntersections` — union contains intersections.
    pub const CONTAINS_INTERSECTIONS: ObjectFlags = ObjectFlags(1 << 25);
    /// `ObjectFlagsIsUnknownLikeUnionComputed` — `isUnknownLikeUnion` flag
    /// has been computed.
    pub const IS_UNKNOWN_LIKE_UNION_COMPUTED: ObjectFlags = ObjectFlags(1 << 26);
    /// `ObjectFlagsIsUnknownLikeUnion` — union of null, undefined, and empty
    /// object type.
    pub const IS_UNKNOWN_LIKE_UNION: ObjectFlags = ObjectFlags(1 << 27);
    /// `ObjectFlagsIsUniformEnumComputed` — `isUniformEnum` flag has been
    /// computed.
    pub const IS_UNIFORM_ENUM_COMPUTED: ObjectFlags = ObjectFlags(1 << 28);
    /// `ObjectFlagsIsUniformEnum` — union contains uniform literal types.
    pub const IS_UNIFORM_ENUM: ObjectFlags = ObjectFlags(1 << 29);
    // Flags that require TypeFlags.Intersection
    /// `ObjectFlagsIsNeverIntersectionComputed` — `isNeverLike` flag has been
    /// computed.
    pub const IS_NEVER_INTERSECTION_COMPUTED: ObjectFlags = ObjectFlags(1 << 25);
    /// `ObjectFlagsIsNeverIntersection` — intersection reduces to never.
    pub const IS_NEVER_INTERSECTION: ObjectFlags = ObjectFlags(1 << 26);
    /// `ObjectFlagsIsConstrainedTypeVariable` — `T & C`, where T's
    /// constraint and C are primitives, object, or `{}`.
    pub const IS_CONSTRAINED_TYPE_VARIABLE: ObjectFlags = ObjectFlags(1 << 27);
}

// TypeAlias

/// `type TypeAlias struct`. Stored inline on `Type` (`Option<TypeAlias>`)
/// rather than behind a `*TypeAlias` pointer — two small fields.
#[derive(Clone, Default)]
pub struct TypeAlias {
    /// `symbol`.
    pub symbol: Option<SymbolId>,
    /// `typeArguments`.
    pub type_arguments: Vec<TypeId>,
}

impl TypeAlias {
    /// `(a *TypeAlias) Symbol` — Go's nil-receiver form is
    /// `alias.as_ref().and_then(TypeAlias::symbol)` at call sites.
    pub fn symbol(&self) -> Option<SymbolId> {
        self.symbol
    }

    /// `(a *TypeAlias) TypeArguments`.
    pub fn type_arguments(&self) -> &[TypeId] {
        &self.type_arguments
    }
}

// Type

/// `type Type struct` — the arena element of `TypeArena`.
///
/// PORT: `checker *Checker` becomes `checker_shard` (SPEC §5.4); `data
/// TypeData` becomes the `TypeData` enum.
#[derive(Default)]
pub struct Type {
    /// `flags`.
    pub flags: TypeFlags,
    /// `objectFlags`.
    pub object_flags: ObjectFlags,
    /// `id`.
    pub id: TypeId,
    /// `symbol`.
    pub symbol: Option<SymbolId>,
    /// `alias` — Go `*TypeAlias`, stored inline.
    pub alias: Option<TypeAlias>,
    /// `checker` — PORT: the Go back-pointer to the owning checker is
    /// replaced by the shard index of the owning `TypeArena`; readers that
    /// need checker state take it as an explicit parameter.
    pub checker_shard: u16,
    /// `data` — type specific data.
    pub data: TypeData,
}

impl Type {
    /// `(t *Type) Id`.
    pub fn id(&self) -> TypeId {
        self.id
    }

    /// `(t *Type) Flags`.
    pub fn flags(&self) -> TypeFlags {
        self.flags
    }

    /// `(t *Type) ObjectFlags`.
    pub fn object_flags(&self) -> ObjectFlags {
        self.object_flags
    }

    // Casts for concrete struct types — `(t *Type) AsX()` mirroring Go's
    // `t.data.(*X)` type assertions: they panic on a mismatched kind.

    /// `AsIntrinsicType`.
    pub fn as_intrinsic_type(&self) -> &IntrinsicType {
        match &self.data {
            TypeData::Intrinsic(d) => d,
            _ => panic!("AsIntrinsicType on {:?}", self.flags),
        }
    }

    /// `AsLiteralType`.
    pub fn as_literal_type(&self) -> &LiteralType {
        match &self.data {
            TypeData::Literal(d) => d,
            _ => panic!("AsLiteralType on {:?}", self.flags),
        }
    }

    /// `AsUniqueESSymbolType`.
    pub fn as_unique_es_symbol_type(&self) -> &UniqueESSymbolType {
        match &self.data {
            TypeData::UniqueESSymbol(d) => d,
            _ => panic!("AsUniqueESSymbolType on {:?}", self.flags),
        }
    }

    /// `AsTupleType`.
    pub fn as_tuple_type(&self) -> &TupleType {
        match &self.data {
            TypeData::Tuple(d) => d,
            _ => panic!("AsTupleType on {:?}", self.flags),
        }
    }

    /// `AsInstantiationExpressionType`.
    pub fn as_instantiation_expression_type(&self) -> &InstantiationExpressionType {
        match &self.data {
            TypeData::InstantiationExpression(d) => d,
            _ => panic!("AsInstantiationExpressionType on {:?}", self.flags),
        }
    }

    /// `AsMappedType`.
    pub fn as_mapped_type(&self) -> &MappedType {
        match &self.data {
            TypeData::Mapped(d) => d,
            _ => panic!("AsMappedType on {:?}", self.flags),
        }
    }

    /// Mutable `AsMappedType`.
    pub fn as_mapped_type_mut(&mut self) -> &mut MappedType {
        match &mut self.data {
            TypeData::Mapped(d) => d,
            _ => panic!("AsMappedType on non-mapped TypeData"),
        }
    }

    /// `AsReverseMappedType`.
    pub fn as_reverse_mapped_type(&self) -> &ReverseMappedType {
        match &self.data {
            TypeData::ReverseMapped(d) => d,
            _ => panic!("AsReverseMappedType on {:?}", self.flags),
        }
    }

    /// `AsEvolvingArrayType`.
    pub fn as_evolving_array_type(&self) -> &EvolvingArrayType {
        match &self.data {
            TypeData::EvolvingArray(d) => d,
            _ => panic!("AsEvolvingArrayType on {:?}", self.flags),
        }
    }

    /// `AsTypeParameter`.
    pub fn as_type_parameter(&self) -> &TypeParameter {
        match &self.data {
            TypeData::TypeParameter(d) => d,
            _ => panic!("AsTypeParameter on {:?}", self.flags),
        }
    }

    /// `AsTypeParameter` — mutable (Go writes `t.AsTypeParameter().constraint`
    /// when cloning type parameters for elaboration).
    pub fn as_type_parameter_mut(&mut self) -> &mut TypeParameter {
        match &mut self.data {
            TypeData::TypeParameter(d) => d,
            _ => panic!("AsTypeParameter on {:?}", self.flags),
        }
    }

    /// `AsUnionType`.
    pub fn as_union_type(&self) -> &UnionType {
        match &self.data {
            TypeData::Union(d) => d,
            _ => panic!("AsUnionType on {:?}", self.flags),
        }
    }

    /// `AsIntersectionType`.
    pub fn as_intersection_type(&self) -> &IntersectionType {
        match &self.data {
            TypeData::Intersection(d) => d,
            _ => panic!("AsIntersectionType on {:?}", self.flags),
        }
    }

    /// `AsIndexType`.
    pub fn as_index_type(&self) -> &IndexType {
        match &self.data {
            TypeData::Index(d) => d,
            _ => panic!("AsIndexType on {:?}", self.flags),
        }
    }

    /// `AsIndexedAccessType`.
    pub fn as_indexed_access_type(&self) -> &IndexedAccessType {
        match &self.data {
            TypeData::IndexedAccess(d) => d,
            _ => panic!("AsIndexedAccessType on {:?}", self.flags),
        }
    }

    /// `AsTemplateLiteralType`.
    pub fn as_template_literal_type(&self) -> &TemplateLiteralType {
        match &self.data {
            TypeData::TemplateLiteral(d) => d,
            _ => panic!("AsTemplateLiteralType on {:?}", self.flags),
        }
    }

    /// `AsStringMappingType`.
    pub fn as_string_mapping_type(&self) -> &StringMappingType {
        match &self.data {
            TypeData::StringMapping(d) => d,
            _ => panic!("AsStringMappingType on {:?}", self.flags),
        }
    }

    /// `AsSubstitutionType`.
    pub fn as_substitution_type(&self) -> &SubstitutionType {
        match &self.data {
            TypeData::Substitution(d) => d,
            _ => panic!("AsSubstitutionType on {:?}", self.flags),
        }
    }

    /// `AsConditionalType`.
    pub fn as_conditional_type(&self) -> &ConditionalType {
        match &self.data {
            TypeData::Conditional(d) => d,
            _ => panic!("AsConditionalType on {:?}", self.flags),
        }
    }

    /// `AsObjectType` — concrete-cast to `ObjectType` payload; panics for
    /// non-object-family payloads like Go's `t.data.(*ObjectType)`.
    pub fn as_object_type(&self) -> &ObjectType {
        self.data
            .as_object_type()
            .expect("AsObjectType on non-object TypeData")
    }

    /// `AsTypeReference` — concrete-cast.
    pub fn as_type_reference(&self) -> &TypeReference {
        self.data
            .as_type_reference()
            .expect("AsTypeReference on non-reference TypeData")
    }

    // Casts for embedded struct types — Go's `t.data.AsX()` returning nil
    // for non-matching payloads become `Option` accessors.

    /// `(t *Type) AsConstrainedType` — `None` where Go returns nil.
    pub fn as_constrained_type(&self) -> Option<&ConstrainedType> {
        self.data.as_constrained_type()
    }

    /// `(t *Type) AsStructuredType` — `None` where Go returns nil.
    pub fn as_structured_type(&self) -> Option<&StructuredType> {
        self.data.as_structured_type()
    }

    /// `(t *Type) AsInterfaceType` — `None` where Go returns nil.
    pub fn as_interface_type(&self) -> Option<&InterfaceType> {
        self.data.as_interface_type()
    }

    /// `(t *Type) AsUnionOrIntersectionType` — `None` where Go returns nil.
    pub fn as_union_or_intersection_type(&self) -> Option<&UnionOrIntersectionType> {
        self.data.as_union_or_intersection_type()
    }

    /// `(t *Type) Distributed` — union constituents, `[]` for never, and
    /// `[t]` otherwise. `self_id` is this type's own `TypeId` for the
    /// single-element case (Go returns `[]*Type{t}`).
    pub fn distributed(&self, self_id: TypeId) -> Vec<TypeId> {
        if self.flags.intersects(TypeFlags::UNION) {
            return self.as_union_type().union_or_intersection.types.clone();
        }
        if self.flags.intersects(TypeFlags::NEVER) {
            return Vec::new();
        }
        vec![self_id]
    }

    // Common accessors

    /// `(t *Type) Target`.
    pub fn target(&self) -> Option<TypeId> {
        if self.flags.intersects(TypeFlags::OBJECT) {
            return self.as_object_type().target;
        }
        if self.flags.intersects(TypeFlags::TYPE_PARAMETER) {
            return self.as_type_parameter().target;
        }
        if self.flags.intersects(TypeFlags::INDEX) {
            return self.as_index_type().target;
        }
        if self.flags.intersects(TypeFlags::STRING_MAPPING) {
            return self.as_string_mapping_type().target;
        }
        // PORT: Go's final `t.flags&TypeFlagsObject != 0 &&
        // t.objectFlags&ObjectFlagsMapped != 0` case is unreachable — the
        // first arm catches all TypeFlagsObject types — kept for parity.
        if self.flags.intersects(TypeFlags::OBJECT)
            && self.object_flags.intersects(ObjectFlags::MAPPED)
        {
            return self.as_mapped_type().object_type.target;
        }
        panic!("Unhandled case in Type.Target")
    }

    /// `(t *Type) Mapper`.
    pub fn mapper(&self) -> Option<TypeMapperId> {
        if self.flags.intersects(TypeFlags::OBJECT) {
            return self.as_object_type().mapper;
        }
        if self.flags.intersects(TypeFlags::TYPE_PARAMETER) {
            return self.as_type_parameter().mapper;
        }
        if self.flags.intersects(TypeFlags::CONDITIONAL) {
            return self.as_conditional_type().mapper;
        }
        panic!("Unhandled case in Type.Mapper")
    }

    /// `(t *Type) Types`.
    pub fn types(&self) -> &[TypeId] {
        if self.flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
            return &self
                .as_union_or_intersection_type()
                .expect("Types on union/intersection")
                .types;
        }
        if self.flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            return &self.as_template_literal_type().types;
        }
        panic!("Unhandled case in Type.Types")
    }

    // PORT: `(t *Type) TargetInterfaceType` / `TargetTupleType` dereference
    // the type reference's *target*, a sibling arena element — they are
    // `TypeArena::{target_interface_type,target_tuple_type}` taking the
    // `TypeId`.

    /// `(t *Type) Symbol`.
    pub fn symbol(&self) -> Option<SymbolId> {
        self.symbol
    }

    /// `(t *Type) Alias`.
    pub fn alias(&self) -> Option<&TypeAlias> {
        self.alias.as_ref()
    }

    /// `(t *Type) IsUnion`.
    pub fn is_union(&self) -> bool {
        self.flags.intersects(TypeFlags::UNION)
    }

    /// `(t *Type) IsString`.
    pub fn is_string(&self) -> bool {
        self.flags.intersects(TypeFlags::STRING)
    }

    /// `(t *Type) IsIntersection`.
    pub fn is_intersection(&self) -> bool {
        self.flags.intersects(TypeFlags::INTERSECTION)
    }

    /// `(t *Type) IsStringLiteral`.
    pub fn is_string_literal(&self) -> bool {
        self.flags.intersects(TypeFlags::STRING_LITERAL)
    }

    /// `(t *Type) IsNumberLiteral`.
    pub fn is_number_literal(&self) -> bool {
        self.flags.intersects(TypeFlags::NUMBER_LITERAL)
    }

    /// `(t *Type) IsBigIntLiteral`.
    pub fn is_big_int_literal(&self) -> bool {
        self.flags.intersects(TypeFlags::BIG_INT_LITERAL)
    }

    /// `(t *Type) IsEnumLiteral`.
    pub fn is_enum_literal(&self) -> bool {
        self.flags.intersects(TypeFlags::ENUM_LITERAL)
    }

    /// `(t *Type) IsBooleanLike`.
    pub fn is_boolean_like(&self) -> bool {
        self.flags.intersects(TypeFlags::BOOLEAN_LIKE)
    }

    /// `(t *Type) IsStringLike`.
    pub fn is_string_like(&self) -> bool {
        self.flags.intersects(TypeFlags::STRING_LIKE)
    }

    /// `(t *Type) IsClass`.
    pub fn is_class(&self) -> bool {
        self.object_flags.intersects(ObjectFlags::CLASS)
    }

    /// `(t *Type) IsTypeParameter`.
    pub fn is_type_parameter(&self) -> bool {
        self.flags.intersects(TypeFlags::TYPE_PARAMETER)
    }

    /// `(t *Type) IsIndex`.
    pub fn is_index(&self) -> bool {
        self.flags.intersects(TypeFlags::INDEX)
    }

    // PORT: `(t *Type) IsTupleType` calls `isTupleType(t)` which reads the
    // *target's* flags — a sibling arena element — so it is
    // `crate::checker_core::is_tuple_type(arena, id)`.
}

// TypeData

/// `type TypeData interface` — the payload variants. `AsConstrainedType`/
/// `AsStructuredType`/`AsObjectType`/`AsTypeReference`/`AsInterfaceType`/
/// `AsUnionOrIntersectionType` become `Option` accessors; `AsType` is
/// unnecessary (the `Type` is the arena element, reached via `TypeId`).
pub enum TypeData {
    /// `*IntrinsicType`.
    Intrinsic(IntrinsicType),
    /// `*LiteralType`.
    Literal(LiteralType),
    /// `*UniqueESSymbolType`.
    UniqueESSymbol(UniqueESSymbolType),
    /// `*ObjectType` (anonymous object types — `ObjectFlagsAnonymous` and
    /// friends).
    Object(ObjectType),
    /// `*TypeReference`.
    TypeReference(TypeReference),
    /// `*InterfaceType`.
    InterfaceType(InterfaceType),
    /// `*TupleType`.
    Tuple(TupleType),
    /// `*InstantiationExpressionType`.
    InstantiationExpression(InstantiationExpressionType),
    /// `*MappedType`.
    Mapped(MappedType),
    /// `*ReverseMappedType`.
    ReverseMapped(ReverseMappedType),
    /// `*EvolvingArrayType`.
    EvolvingArray(EvolvingArrayType),
    /// `*UnionType`.
    Union(UnionType),
    /// `*IntersectionType`.
    Intersection(IntersectionType),
    /// `*TypeParameter`.
    TypeParameter(TypeParameter),
    /// `*IndexType`.
    Index(IndexType),
    /// `*IndexedAccessType`.
    IndexedAccess(IndexedAccessType),
    /// `*TemplateLiteralType`.
    TemplateLiteral(TemplateLiteralType),
    /// `*StringMappingType`.
    StringMapping(StringMappingType),
    /// `*SubstitutionType`.
    Substitution(SubstitutionType),
    /// `*ConditionalType`.
    Conditional(ConditionalType),
}

/// Go's zero `TypeData` is a nil interface; `Type::default()` uses the
/// `Intrinsic` tombstone (fields are always inspected through flag checks).
impl Default for TypeData {
    fn default() -> Self {
        TypeData::Intrinsic(IntrinsicType::default())
    }
}

impl TypeData {
    /// `TypeBase.AsConstrainedType` — Go's embedded-method dispatch; `None`
    /// for payloads whose Go base does not override it (returns nil).
    pub fn as_constrained_type(&self) -> Option<&ConstrainedType> {
        match self {
            TypeData::Object(d) => Some(&d.structured_type.constrained_type),
            TypeData::TypeReference(d) => Some(&d.object_type.structured_type.constrained_type),
            TypeData::InterfaceType(d) => Some(
                &d.type_reference
                    .object_type
                    .structured_type
                    .constrained_type,
            ),
            TypeData::Tuple(d) => Some(
                &d.interface_type
                    .type_reference
                    .object_type
                    .structured_type
                    .constrained_type,
            ),
            TypeData::InstantiationExpression(d) => {
                Some(&d.object_type.structured_type.constrained_type)
            }
            TypeData::Mapped(d) => Some(&d.object_type.structured_type.constrained_type),
            TypeData::ReverseMapped(d) => Some(&d.object_type.structured_type.constrained_type),
            TypeData::EvolvingArray(d) => Some(&d.object_type.structured_type.constrained_type),
            TypeData::Union(d) => Some(&d.union_or_intersection.structured_type.constrained_type),
            TypeData::Intersection(d) => {
                Some(&d.union_or_intersection.structured_type.constrained_type)
            }
            TypeData::TypeParameter(d) => Some(&d.constrained_type),
            TypeData::Index(d) => Some(&d.constrained_type),
            TypeData::IndexedAccess(d) => Some(&d.constrained_type),
            TypeData::TemplateLiteral(d) => Some(&d.constrained_type),
            TypeData::StringMapping(d) => Some(&d.constrained_type),
            TypeData::Substitution(d) => Some(&d.constrained_type),
            TypeData::Conditional(d) => Some(&d.constrained_type),
            // TypeBase.AsConstrainedType() returns nil.
            TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueESSymbol(_) => None,
        }
    }

    /// Mutable `AsConstrainedType`.
    pub fn as_constrained_type_mut(&mut self) -> Option<&mut ConstrainedType> {
        match self {
            TypeData::Object(d) => Some(&mut d.structured_type.constrained_type),
            TypeData::TypeReference(d) => Some(&mut d.object_type.structured_type.constrained_type),
            TypeData::InterfaceType(d) => Some(
                &mut d
                    .type_reference
                    .object_type
                    .structured_type
                    .constrained_type,
            ),
            TypeData::Tuple(d) => Some(
                &mut d
                    .interface_type
                    .type_reference
                    .object_type
                    .structured_type
                    .constrained_type,
            ),
            TypeData::InstantiationExpression(d) => {
                Some(&mut d.object_type.structured_type.constrained_type)
            }
            TypeData::Mapped(d) => Some(&mut d.object_type.structured_type.constrained_type),
            TypeData::ReverseMapped(d) => Some(&mut d.object_type.structured_type.constrained_type),
            TypeData::EvolvingArray(d) => Some(&mut d.object_type.structured_type.constrained_type),
            TypeData::Union(d) => {
                Some(&mut d.union_or_intersection.structured_type.constrained_type)
            }
            TypeData::Intersection(d) => {
                Some(&mut d.union_or_intersection.structured_type.constrained_type)
            }
            TypeData::TypeParameter(d) => Some(&mut d.constrained_type),
            TypeData::Index(d) => Some(&mut d.constrained_type),
            TypeData::IndexedAccess(d) => Some(&mut d.constrained_type),
            TypeData::TemplateLiteral(d) => Some(&mut d.constrained_type),
            TypeData::StringMapping(d) => Some(&mut d.constrained_type),
            TypeData::Substitution(d) => Some(&mut d.constrained_type),
            TypeData::Conditional(d) => Some(&mut d.constrained_type),
            TypeData::Intrinsic(_) | TypeData::Literal(_) | TypeData::UniqueESSymbol(_) => None,
        }
    }

    /// `TypeBase.AsStructuredType` — `None` where Go returns nil.
    pub fn as_structured_type(&self) -> Option<&StructuredType> {
        match self {
            TypeData::Object(d) => Some(&d.structured_type),
            TypeData::TypeReference(d) => Some(&d.object_type.structured_type),
            TypeData::InterfaceType(d) => Some(&d.type_reference.object_type.structured_type),
            TypeData::Tuple(d) => {
                Some(&d.interface_type.type_reference.object_type.structured_type)
            }
            TypeData::InstantiationExpression(d) => Some(&d.object_type.structured_type),
            TypeData::Mapped(d) => Some(&d.object_type.structured_type),
            TypeData::ReverseMapped(d) => Some(&d.object_type.structured_type),
            TypeData::EvolvingArray(d) => Some(&d.object_type.structured_type),
            TypeData::Union(d) => Some(&d.union_or_intersection.structured_type),
            TypeData::Intersection(d) => Some(&d.union_or_intersection.structured_type),
            _ => None,
        }
    }

    /// Mutable `AsStructuredType`.
    pub fn as_structured_type_mut(&mut self) -> Option<&mut StructuredType> {
        match self {
            TypeData::Object(d) => Some(&mut d.structured_type),
            TypeData::TypeReference(d) => Some(&mut d.object_type.structured_type),
            TypeData::InterfaceType(d) => Some(&mut d.type_reference.object_type.structured_type),
            TypeData::Tuple(d) => {
                Some(&mut d.interface_type.type_reference.object_type.structured_type)
            }
            TypeData::InstantiationExpression(d) => Some(&mut d.object_type.structured_type),
            TypeData::Mapped(d) => Some(&mut d.object_type.structured_type),
            TypeData::ReverseMapped(d) => Some(&mut d.object_type.structured_type),
            TypeData::EvolvingArray(d) => Some(&mut d.object_type.structured_type),
            TypeData::Union(d) => Some(&mut d.union_or_intersection.structured_type),
            TypeData::Intersection(d) => Some(&mut d.union_or_intersection.structured_type),
            _ => None,
        }
    }

    /// `TypeBase.AsObjectType` — `None` where Go returns nil.
    pub fn as_object_type(&self) -> Option<&ObjectType> {
        match self {
            TypeData::Object(d) => Some(d),
            TypeData::TypeReference(d) => Some(&d.object_type),
            TypeData::InterfaceType(d) => Some(&d.type_reference.object_type),
            TypeData::Tuple(d) => Some(&d.interface_type.type_reference.object_type),
            TypeData::InstantiationExpression(d) => Some(&d.object_type),
            TypeData::Mapped(d) => Some(&d.object_type),
            TypeData::ReverseMapped(d) => Some(&d.object_type),
            TypeData::EvolvingArray(d) => Some(&d.object_type),
            _ => None,
        }
    }

    /// Mutable `AsObjectType`.
    pub fn as_object_type_mut(&mut self) -> Option<&mut ObjectType> {
        match self {
            TypeData::Object(d) => Some(d),
            TypeData::TypeReference(d) => Some(&mut d.object_type),
            TypeData::InterfaceType(d) => Some(&mut d.type_reference.object_type),
            TypeData::Tuple(d) => Some(&mut d.interface_type.type_reference.object_type),
            TypeData::InstantiationExpression(d) => Some(&mut d.object_type),
            TypeData::Mapped(d) => Some(&mut d.object_type),
            TypeData::ReverseMapped(d) => Some(&mut d.object_type),
            TypeData::EvolvingArray(d) => Some(&mut d.object_type),
            _ => None,
        }
    }

    /// `TypeBase.AsTypeReference` — `None` where Go returns nil.
    pub fn as_type_reference(&self) -> Option<&TypeReference> {
        match self {
            TypeData::TypeReference(d) => Some(d),
            TypeData::InterfaceType(d) => Some(&d.type_reference),
            TypeData::Tuple(d) => Some(&d.interface_type.type_reference),
            _ => None,
        }
    }

    /// Mutable `AsTypeReference`.
    pub fn as_type_reference_mut(&mut self) -> Option<&mut TypeReference> {
        match self {
            TypeData::TypeReference(d) => Some(d),
            TypeData::InterfaceType(d) => Some(&mut d.type_reference),
            TypeData::Tuple(d) => Some(&mut d.interface_type.type_reference),
            _ => None,
        }
    }

    /// `TypeBase.AsInterfaceType` — `None` where Go returns nil.
    pub fn as_interface_type(&self) -> Option<&InterfaceType> {
        match self {
            TypeData::InterfaceType(d) => Some(d),
            TypeData::Tuple(d) => Some(&d.interface_type),
            _ => None,
        }
    }

    /// Mutable `AsInterfaceType`.
    pub fn as_interface_type_mut(&mut self) -> Option<&mut InterfaceType> {
        match self {
            TypeData::InterfaceType(d) => Some(d),
            TypeData::Tuple(d) => Some(&mut d.interface_type),
            _ => None,
        }
    }

    /// `TypeBase.AsUnionOrIntersectionType` — `None` where Go returns nil.
    pub fn as_union_or_intersection_type(&self) -> Option<&UnionOrIntersectionType> {
        match self {
            TypeData::Union(d) => Some(&d.union_or_intersection),
            TypeData::Intersection(d) => Some(&d.union_or_intersection),
            _ => None,
        }
    }

    /// Mutable `AsUnionOrIntersectionType`.
    pub fn as_union_or_intersection_type_mut(&mut self) -> Option<&mut UnionOrIntersectionType> {
        match self {
            TypeData::Union(d) => Some(&mut d.union_or_intersection),
            TypeData::Intersection(d) => Some(&mut d.union_or_intersection),
            _ => None,
        }
    }
}

// TypeBase — Go's embedded `Type` is the arena element itself, so there is no
// `TypeBase` payload struct; `AsType()` corresponds to dereferencing a
// `TypeId` in the `TypeArena`.

// IntrinsicTypeData

/// `type IntrinsicType struct` — the `TypeBase` embed is the enclosing
/// `Type`.
#[derive(Default)]
pub struct IntrinsicType {
    /// `intrinsicName`.
    pub intrinsic_name: String,
}

impl IntrinsicType {
    /// `(t *IntrinsicType) IntrinsicName`.
    pub fn intrinsic_name(&self) -> &str {
        &self.intrinsic_name
    }
}

// LiteralTypeData

/// `type LiteralType struct`.
#[derive(Default)]
pub struct LiteralType {
    /// `value any` — `string | jsnum.Number | bool | PseudoBigInt`; `None`
    /// is Go's nil (computed enum).
    pub value: Option<evaluator::Value>,
    /// `freshType` — fresh version of type.
    pub fresh_type: Option<TypeId>,
    /// `regularType` — regular version of type.
    pub regular_type: Option<TypeId>,
}

impl LiteralType {
    /// `(t *LiteralType) Value`.
    pub fn value(&self) -> Option<&evaluator::Value> {
        self.value.as_ref()
    }

    /// `(t *LiteralType) FreshType`.
    pub fn fresh_type(&self) -> Option<TypeId> {
        self.fresh_type
    }

    /// `(t *LiteralType) RegularType`.
    pub fn regular_type(&self) -> Option<TypeId> {
        self.regular_type
    }
}

impl fmt::Display for LiteralType {
    /// `(t *LiteralType) String` — `ValueToString(t.value)`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&crate::checker_core::value_to_string(self.value.as_ref()))
    }
}

// UniqueESSymbolTypeData

/// `type UniqueESSymbolType struct`.
#[derive(Default)]
pub struct UniqueESSymbolType {
    /// `name`.
    pub name: String,
}

// ConstrainedType (type with computed base constraint)

/// `type ConstrainedType struct`.
#[derive(Clone, Default)]
pub struct ConstrainedType {
    /// `resolvedBaseConstraint`.
    pub resolved_base_constraint: Option<TypeId>,
}

// StructuredType (base of all types with members)

/// `type StructuredType struct`.
#[derive(Default)]
pub struct StructuredType {
    /// embedded `ConstrainedType`.
    pub constrained_type: ConstrainedType,
    /// `members`.
    pub members: SymbolTable,
    /// `properties`.
    pub properties: Vec<SymbolId>,
    /// `signatures` — signatures (call + construct).
    pub signatures: Vec<SignatureId>,
    /// `callSignatureCount` — count of call signatures.
    pub call_signature_count: usize,
    /// `indexInfos`.
    pub index_infos: Vec<IndexInfo>,
    /// `objectTypeWithoutAbstractConstructSignatures`.
    pub object_type_without_abstract_construct_signatures: Option<TypeId>,
}

impl StructuredType {
    /// `(t *StructuredType) CallSignatures` — `slices.Clip` is a capacity
    /// hint only; slicing the prefix is equivalent.
    pub fn call_signatures(&self) -> &[SignatureId] {
        &self.signatures[..self.call_signature_count]
    }

    /// `(t *StructuredType) ConstructSignatures`.
    pub fn construct_signatures(&self) -> &[SignatureId] {
        &self.signatures[self.call_signature_count..]
    }

    /// `(t *StructuredType) Properties`.
    pub fn properties(&self) -> &[SymbolId] {
        &self.properties
    }
}

// Except for tuple type references and reverse mapped types, all object
// types have an associated symbol. Possible object type instances are listed
// in the following.
//
// InterfaceType:
//   ObjectFlagsClass: Originating non-generic class type
//   ObjectFlagsClass|ObjectFlagsReference: Originating generic class type
//   ObjectFlagsInterface: Originating non-generic interface type
//   ObjectFlagsInterface|ObjectFlagsReference: Originating generic interface
//     type
//
// TupleType:
//   ObjectFlagsReference|ObjectFlagsTuple: Originating generic tuple type
//     (synthesized)
//
// TypeReference:
//   ObjectFlagsReference: Instantiated generic class, interface, or tuple
//     type
//
// ObjectType:
//   ObjectFlagsAnonymous: Originating anonymous object type
//   ObjectFlagsAnonymous|ObjectFlagsInstantiated: Instantiated anonymous
//     object type
//
// MappedType:
//   ObjectFlagsMapped: Originating mapped type
//   ObjectFlagsMapped|ObjectFlagsInstantiated: Instantiated mapped type
//
// InstantiationExpressionType:
//   ObjectFlagsAnonymous|ObjectFlagsInstantiationExpression: Originating
//     instantiation expression type
//   ObjectFlagsAnonymous|ObjectFlagsInstantiated|
//     ObjectFlagsInstantiationExpression: Instantiated instantiation
//     expression type
//
// ReverseMappedType:
//   ObjectFlagsAnonymous|ObjectFlagsReverseMapped: Reverse mapped type
//
// EvolvingArrayType:
//   ObjectFlagsEvolvingArray: Evolving array type

/// `type ObjectType struct`.
#[derive(Default)]
pub struct ObjectType {
    /// embedded `StructuredType`.
    pub structured_type: StructuredType,
    /// `target` — target of instantiated type.
    pub target: Option<TypeId>,
    /// `mapper` — type mapper for instantiated type.
    pub mapper: Option<TypeMapperId>,
    /// `instantiations` — map of type instantiations.
    pub instantiations: FxHashMap<crate::checker_core::CacheHashKey, TypeId>,
}

// TypeReference (instantiation of an InterfaceType)

/// `type TypeReference struct`.
#[derive(Default)]
pub struct TypeReference {
    /// embedded `ObjectType`.
    pub object_type: ObjectType,
    /// `node` — `TypeReferenceNode | ArrayTypeNode | TupleTypeNode` when
    /// deferred, else `None`.
    pub node: Option<NodeId>,
    /// `resolvedTypeArguments`.
    pub resolved_type_arguments: Vec<TypeId>,
}

// InterfaceType (when generic, serves as reference to instantiation of
// itself)

/// `type InterfaceType struct`.
#[derive(Default)]
pub struct InterfaceType {
    /// embedded `TypeReference`.
    pub type_reference: TypeReference,
    /// `allTypeParameters` — type parameters (outer + local + thisType).
    pub all_type_parameters: Vec<TypeId>,
    /// `outerTypeParameterCount` — count of outer type parameters.
    pub outer_type_parameter_count: usize,
    /// `thisType` — the "this" type (`None` if none).
    pub this_type: Option<TypeId>,
    /// `baseTypesResolved`.
    pub base_types_resolved: bool,
    /// `declaredMembersResolved`.
    pub declared_members_resolved: bool,
    /// `resolvedBaseConstructorType`.
    pub resolved_base_constructor_type: Option<TypeId>,
    /// `resolvedBaseTypes`.
    pub resolved_base_types: Vec<TypeId>,
    /// `declaredMembers` — declared members.
    pub declared_members: SymbolTable,
    /// `declaredCallSignatures` — declared call signatures.
    pub declared_call_signatures: Vec<SignatureId>,
    /// `declaredConstructSignatures` — declared construct signatures.
    pub declared_construct_signatures: Vec<SignatureId>,
    /// `declaredIndexInfos` — declared index signatures.
    pub declared_index_infos: Vec<IndexInfo>,
}

impl InterfaceType {
    /// `(t *InterfaceType) OuterTypeParameters`.
    pub fn outer_type_parameters(&self) -> &[TypeId] {
        if self.all_type_parameters.is_empty() {
            return &[];
        }
        &self.all_type_parameters[..self.outer_type_parameter_count]
    }

    /// `(t *InterfaceType) LocalTypeParameters`.
    pub fn local_type_parameters(&self) -> &[TypeId] {
        if self.all_type_parameters.is_empty() {
            return &[];
        }
        &self.all_type_parameters
            [self.outer_type_parameter_count..self.all_type_parameters.len() - 1]
    }

    /// `(t *InterfaceType) TypeParameters`.
    pub fn type_parameters(&self) -> &[TypeId] {
        if self.all_type_parameters.is_empty() {
            return &[];
        }
        &self.all_type_parameters[..self.all_type_parameters.len() - 1]
    }

    /// `(t *InterfaceType) ThisType`.
    pub fn this_type(&self) -> Option<TypeId> {
        self.this_type
    }
}

// TupleType

flag_type! {
    /// `type ElementFlags uint32`.
    pub struct ElementFlags(pub u32);
}

impl ElementFlags {
    /// `ElementFlagsRequired` — `T`.
    pub const REQUIRED: ElementFlags = ElementFlags(1 << 0);
    /// `ElementFlagsOptional` — `T?`.
    pub const OPTIONAL: ElementFlags = ElementFlags(1 << 1);
    /// `ElementFlagsRest` — `...T[]`.
    pub const REST: ElementFlags = ElementFlags(1 << 2);
    /// `ElementFlagsVariadic` — `...T`.
    pub const VARIADIC: ElementFlags = ElementFlags(1 << 3);
    /// `ElementFlagsFixed`.
    pub const FIXED: ElementFlags = ElementFlags(Self::REQUIRED.0 | Self::OPTIONAL.0);
    /// `ElementFlagsVariable`.
    pub const VARIABLE: ElementFlags = ElementFlags(Self::REST.0 | Self::VARIADIC.0);
    /// `ElementFlagsNonRequired`.
    pub const NON_REQUIRED: ElementFlags =
        ElementFlags(Self::OPTIONAL.0 | Self::REST.0 | Self::VARIADIC.0);
    /// `ElementFlagsNonRest`.
    pub const NON_REST: ElementFlags =
        ElementFlags(Self::REQUIRED.0 | Self::OPTIONAL.0 | Self::VARIADIC.0);
}

/// `type TupleElementInfo struct`.
#[derive(Default, Clone)]
pub struct TupleElementInfo {
    /// `flags`.
    pub flags: ElementFlags,
    /// `labeledDeclaration` — `NamedTupleMember | ParameterDeclaration`.
    pub labeled_declaration: Option<NodeId>,
}

impl TupleElementInfo {
    /// `(t *TupleElementInfo) TupleElementFlags`.
    pub fn tuple_element_flags(&self) -> ElementFlags {
        self.flags
    }

    /// `(t *TupleElementInfo) LabeledDeclaration`.
    pub fn labeled_declaration(&self) -> Option<NodeId> {
        self.labeled_declaration
    }
}

/// `type TupleType struct`.
#[derive(Default)]
pub struct TupleType {
    /// embedded `InterfaceType`.
    pub interface_type: InterfaceType,
    /// `elementInfos`.
    pub element_infos: Vec<TupleElementInfo>,
    /// `minLength` — number of required or variadic elements.
    pub min_length: usize,
    /// `fixedLength` — number of initial required or optional elements.
    pub fixed_length: usize,
    /// `combinedFlags`.
    pub combined_flags: ElementFlags,
    /// `readonly`.
    pub readonly: bool,
}

impl TupleType {
    /// `(t *TupleType) FixedLength`.
    pub fn fixed_length(&self) -> usize {
        self.fixed_length
    }

    /// `(t *TupleType) IsReadonly`.
    pub fn is_readonly(&self) -> bool {
        self.readonly
    }

    /// `(t *TupleType) ElementFlags`.
    pub fn element_flags(&self) -> Vec<ElementFlags> {
        self.element_infos.iter().map(|info| info.flags).collect()
    }

    /// `(t *TupleType) ElementInfos`.
    pub fn element_infos(&self) -> &[TupleElementInfo] {
        &self.element_infos
    }
}

// InstantiationExpressionType

/// `type InstantiationExpressionType struct`.
#[derive(Default)]
pub struct InstantiationExpressionType {
    /// embedded `ObjectType`.
    pub object_type: ObjectType,
    /// `node`.
    pub node: Option<NodeId>,
}

// MappedType

/// `type MappedType struct`.
#[derive(Default)]
pub struct MappedType {
    /// embedded `ObjectType`.
    pub object_type: ObjectType,
    /// `declaration` — `*ast.MappedTypeNode`.
    pub declaration: Option<NodeId>,
    /// `typeParameter`.
    pub type_parameter: Option<TypeId>,
    /// `constraintType`.
    pub constraint_type: Option<TypeId>,
    /// `nameType`.
    pub name_type: Option<TypeId>,
    /// `templateType`.
    pub template_type: Option<TypeId>,
    /// `modifiersType`.
    pub modifiers_type: Option<TypeId>,
    /// `resolvedApparentType`.
    pub resolved_apparent_type: Option<TypeId>,
    /// `containsError`.
    pub contains_error: bool,
}

impl MappedType {
    /// `(t *MappedType) TypeParameter`.
    pub fn type_parameter(&self) -> Option<TypeId> {
        self.type_parameter
    }

    /// `(t *MappedType) ConstraintType`.
    pub fn constraint_type(&self) -> Option<TypeId> {
        self.constraint_type
    }

    /// `(t *MappedType) NameType`.
    pub fn name_type(&self) -> Option<TypeId> {
        self.name_type
    }

    /// `(t *MappedType) TemplateType`.
    pub fn template_type(&self) -> Option<TypeId> {
        self.template_type
    }

    // PORT(deferred): `(t *MappedType) ResolveComponents(c *Checker, typ)`
    // calls four `*Checker` methods (`getTypeParameterFromMappedType`,
    // `getConstraintTypeFromMappedType`, `getNameTypeFromMappedType`,
    // `getTemplateTypeFromMappedType`) — lands with the Checker struct; see
    // `Checker::resolve_mapped_type_components` in checker_core.rs.
}

// ReverseMappedType

/// `type ReverseMappedType struct`.
#[derive(Default)]
pub struct ReverseMappedType {
    /// embedded `ObjectType`.
    pub object_type: ObjectType,
    /// `source`.
    pub source: Option<TypeId>,
    /// `mappedType`.
    pub mapped_type: Option<TypeId>,
    /// `constraintType`.
    pub constraint_type: Option<TypeId>,
}

// EvolvingArrayType

/// `type EvolvingArrayType struct`.
#[derive(Default)]
pub struct EvolvingArrayType {
    /// embedded `ObjectType`.
    pub object_type: ObjectType,
    /// `elementType`.
    pub element_type: Option<TypeId>,
    /// `finalArrayType`.
    pub final_array_type: Option<TypeId>,
}

// UnionOrIntersectionTypeData

/// `type UnionOrIntersectionType struct`.
#[derive(Default)]
pub struct UnionOrIntersectionType {
    /// embedded `StructuredType`.
    pub structured_type: StructuredType,
    /// `types`.
    pub types: Vec<TypeId>,
    /// `propertyCache`.
    pub property_cache: SymbolTable,
    /// `propertyCacheWithoutFunctionPropertyAugment`.
    pub property_cache_without_function_property_augment: SymbolTable,
    /// `resolvedProperties`.
    pub resolved_properties: Vec<SymbolId>,
}

impl UnionOrIntersectionType {
    /// `(t *UnionOrIntersectionType) Types`.
    pub fn types(&self) -> &[TypeId] {
        &self.types
    }
}

// UnionType

/// `type UnionType struct`.
#[derive(Default)]
pub struct UnionType {
    /// embedded `UnionOrIntersectionType`.
    pub union_or_intersection: UnionOrIntersectionType,
    /// `resolvedReducedType`.
    pub resolved_reduced_type: Option<TypeId>,
    /// `regularType`.
    pub regular_type: Option<TypeId>,
    /// `origin` — denormalized union, intersection, or index type in which
    /// union originates.
    pub origin: Option<TypeId>,
    /// `keyPropertyName` — property with unique unit type that exists in
    /// every object/intersection in union type.
    pub key_property_name: String,
    /// `constituentMap` — constituents keyed by unit type discriminants. Go
    /// keys by `*Type` pointer; `TypeId` is the equivalent identity.
    pub constituent_map: FxHashMap<TypeId, TypeId>,
}

// IntersectionType

/// `type IntersectionType struct`.
#[derive(Default)]
pub struct IntersectionType {
    /// embedded `UnionOrIntersectionType`.
    pub union_or_intersection: UnionOrIntersectionType,
    /// `resolvedApparentType`.
    pub resolved_apparent_type: Option<TypeId>,
    /// `uniqueLiteralFilledInstantiation` — instantiation with type
    /// parameters mapped to never type.
    pub unique_literal_filled_instantiation: Option<TypeId>,
}

// TypeParameter

/// `type TypeParameter struct`.
#[derive(Default)]
pub struct TypeParameter {
    /// embedded `ConstrainedType`.
    pub constrained_type: ConstrainedType,
    /// `constraint`.
    pub constraint: Option<TypeId>,
    /// `target`.
    pub target: Option<TypeId>,
    /// `mapper`.
    pub mapper: Option<TypeMapperId>,
    /// `isThisType`.
    pub is_this_type: bool,
    /// `isDistributed`.
    pub is_distributed: bool,
    /// `resolvedDefaultType`.
    pub resolved_default_type: Option<TypeId>,
    /// `distributedType`.
    pub distributed_type: Option<TypeId>,
}

impl TypeParameter {
    /// `(t *TypeParameter) IsThisType`.
    pub fn is_this_type(&self) -> bool {
        self.is_this_type
    }
}

// IndexFlags

flag_type! {
    /// `type IndexFlags uint32`.
    pub struct IndexFlags(pub u32);
}

impl IndexFlags {
    /// `IndexFlagsStringsOnly`.
    pub const STRINGS_ONLY: IndexFlags = IndexFlags(1 << 0);
    /// `IndexFlagsNoIndexSignatures`.
    pub const NO_INDEX_SIGNATURES: IndexFlags = IndexFlags(1 << 1);
    /// `IndexFlagsNoReducibleCheck`.
    pub const NO_REDUCIBLE_CHECK: IndexFlags = IndexFlags(1 << 2);
}

// IndexType

/// `type IndexType struct`.
#[derive(Default)]
pub struct IndexType {
    /// embedded `ConstrainedType`.
    pub constrained_type: ConstrainedType,
    /// `target`.
    pub target: Option<TypeId>,
    /// `indexFlags`.
    pub index_flags: IndexFlags,
}

impl IndexType {
    /// `(t *IndexType) Target`.
    pub fn target(&self) -> Option<TypeId> {
        self.target
    }
}

// IndexedAccessType

/// `type IndexedAccessType struct`.
#[derive(Default)]
pub struct IndexedAccessType {
    /// embedded `ConstrainedType`.
    pub constrained_type: ConstrainedType,
    /// `objectType`.
    pub object_type: Option<TypeId>,
    /// `indexType`.
    pub index_type: Option<TypeId>,
    /// `accessFlags` — only includes `AccessFlags::PERSISTENT`.
    pub access_flags: AccessFlags,
}

impl IndexedAccessType {
    /// `(t *IndexedAccessType) ObjectType`.
    pub fn object_type(&self) -> Option<TypeId> {
        self.object_type
    }

    /// `(t *IndexedAccessType) IndexType`.
    pub fn index_type(&self) -> Option<TypeId> {
        self.index_type
    }
}

/// `type TemplateLiteralType struct`.
#[derive(Clone, Default)]
pub struct TemplateLiteralType {
    /// embedded `ConstrainedType`.
    pub constrained_type: ConstrainedType,
    /// `texts` — always one element longer than `types`.
    pub texts: Vec<String>,
    /// `types` — always at least one element.
    pub types: Vec<TypeId>,
}

impl TemplateLiteralType {
    /// `(t *TemplateLiteralType) Texts`.
    pub fn texts(&self) -> &[String] {
        &self.texts
    }

    /// `(t *TemplateLiteralType) Types`.
    pub fn types(&self) -> &[TypeId] {
        &self.types
    }
}

/// `type StringMappingType struct`.
#[derive(Default)]
pub struct StringMappingType {
    /// embedded `ConstrainedType`.
    pub constrained_type: ConstrainedType,
    /// `target`.
    pub target: Option<TypeId>,
}

impl StringMappingType {
    /// `(t *StringMappingType) Target`.
    pub fn target(&self) -> Option<TypeId> {
        self.target
    }
}

/// `type SubstitutionType struct`.
#[derive(Default)]
pub struct SubstitutionType {
    /// embedded `ConstrainedType`.
    pub constrained_type: ConstrainedType,
    /// `baseType` — target type.
    pub base_type: Option<TypeId>,
    /// `constraint` — constraint that target type is known to satisfy.
    pub constraint: Option<TypeId>,
}

impl SubstitutionType {
    /// `(t *SubstitutionType) BaseType`.
    pub fn base_type(&self) -> Option<TypeId> {
        self.base_type
    }

    /// `(t *SubstitutionType) SubstConstraint`.
    pub fn subst_constraint(&self) -> Option<TypeId> {
        self.constraint
    }
}

/// `type ConditionalRoot struct`. `ConditionalType.root` is `*ConditionalRoot`
/// in Go — `Option<Box<ConditionalRoot>>` here.
#[derive(Default)]
pub struct ConditionalRoot {
    /// `node` — `*ast.ConditionalTypeNode`.
    pub node: Option<NodeId>,
    /// `checkType`.
    pub check_type: Option<TypeId>,
    /// `extendsType`.
    pub extends_type: Option<TypeId>,
    /// `isDistributive`.
    pub is_distributive: bool,
    /// `inferTypeParameters`.
    pub infer_type_parameters: Vec<TypeId>,
    /// `outerTypeParameters`.
    pub outer_type_parameters: Vec<TypeId>,
    /// `instantiations`.
    pub instantiations: FxHashMap<crate::checker_core::CacheHashKey, TypeId>,
    /// `alias` — Go `*TypeAlias`, stored inline.
    pub alias: Option<TypeAlias>,
}

/// `type ConditionalType struct`.
#[derive(Default)]
pub struct ConditionalType {
    /// embedded `ConstrainedType`.
    pub constrained_type: ConstrainedType,
    /// `root`.
    pub root: Option<Box<ConditionalRoot>>,
    /// `checkType`.
    pub check_type: Option<TypeId>,
    /// `extendsType`.
    pub extends_type: Option<TypeId>,
    /// `resolvedTrueType`.
    pub resolved_true_type: Option<TypeId>,
    /// `resolvedFalseType`.
    pub resolved_false_type: Option<TypeId>,
    /// `resolvedInferredTrueType` — the `trueType` instantiated with the
    /// `combinedMapper`, if present.
    pub resolved_inferred_true_type: Option<TypeId>,
    /// `resolvedDefaultConstraint`.
    pub resolved_default_constraint: Option<TypeId>,
    /// `resolvedConstraintOfDistributive`.
    pub resolved_constraint_of_distributive: Option<TypeId>,
    /// `mapper`.
    pub mapper: Option<TypeMapperId>,
    /// `combinedMapper`.
    pub combined_mapper: Option<TypeMapperId>,
}

impl ConditionalType {
    /// `(t *ConditionalType) CheckType`.
    pub fn check_type(&self) -> Option<TypeId> {
        self.check_type
    }

    /// `(t *ConditionalType) ExtendsType`.
    pub fn extends_type(&self) -> Option<TypeId> {
        self.extends_type
    }
}

// SignatureFlags

flag_type! {
    /// `type SignatureFlags uint32`.
    pub struct SignatureFlags(pub u32);
}

impl SignatureFlags {
    // Propagating flags
    /// `SignatureFlagsHasRestParameter` — indicates last parameter is rest
    /// parameter.
    pub const HAS_REST_PARAMETER: SignatureFlags = SignatureFlags(1 << 0);
    /// `SignatureFlagsHasLiteralTypes` — indicates signature is specialized.
    pub const HAS_LITERAL_TYPES: SignatureFlags = SignatureFlags(1 << 1);
    /// `SignatureFlagsConstruct` — indicates signature is a construct
    /// signature.
    pub const CONSTRUCT: SignatureFlags = SignatureFlags(1 << 2);
    /// `SignatureFlagsAbstract` — indicates signature comes from an abstract
    /// class, abstract construct signature, or abstract constructor type.
    pub const ABSTRACT: SignatureFlags = SignatureFlags(1 << 3);
    // Non-propagating flags
    /// `SignatureFlagsIsInnerCallChain` — indicates signature comes from a
    /// CallChain nested in an outer OptionalChain.
    pub const IS_INNER_CALL_CHAIN: SignatureFlags = SignatureFlags(1 << 4);
    /// `SignatureFlagsIsOuterCallChain` — indicates signature comes from a
    /// CallChain that is the outermost chain of an optional expression.
    pub const IS_OUTER_CALL_CHAIN: SignatureFlags = SignatureFlags(1 << 5);
    /// `SignatureFlagsIsUntypedSignatureInJSFile` — indicates signature is
    /// from a js file and has no types.
    pub const IS_UNTYPED_SIGNATURE_IN_JS_FILE: SignatureFlags = SignatureFlags(1 << 6);
    /// `SignatureFlagsIsNonInferrable` — indicates signature comes from a
    /// non-inferrable type.
    pub const IS_NON_INFERRABLE: SignatureFlags = SignatureFlags(1 << 7);
    /// `SignatureFlagsIsSignatureCandidateForOverloadFailure`.
    pub const IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE: SignatureFlags = SignatureFlags(1 << 8);
    // We do not propagate `IsInnerCallChain` or `IsOuterCallChain` to
    // instantiated signatures, as that would result in us attempting to add
    // `| undefined` on each recursive call to `getReturnTypeOfSignature` when
    // instantiating the return type.
    /// `SignatureFlagsPropagatingFlags`.
    pub const PROPAGATING_FLAGS: SignatureFlags = SignatureFlags(
        Self::HAS_REST_PARAMETER.0
            | Self::HAS_LITERAL_TYPES.0
            | Self::CONSTRUCT.0
            | Self::ABSTRACT.0
            | Self::IS_UNTYPED_SIGNATURE_IN_JS_FILE.0
            | Self::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE.0,
    );
    /// `SignatureFlagsCallChainFlags`.
    pub const CALL_CHAIN_FLAGS: SignatureFlags =
        SignatureFlags(Self::IS_INNER_CALL_CHAIN.0 | Self::IS_OUTER_CALL_CHAIN.0);
}

// Signature

/// `type Signature struct` — the arena element of `SignatureArena`.
#[derive(Default)]
pub struct Signature {
    /// `id`.
    pub id: SignatureId,
    /// `flags`.
    pub flags: SignatureFlags,
    /// `minArgumentCount`.
    pub min_argument_count: i32,
    /// `resolvedMinArgumentCount`.
    pub resolved_min_argument_count: i32,
    /// `declaration`.
    pub declaration: Option<NodeId>,
    /// `typeParameters`.
    pub type_parameters: Vec<TypeId>,
    /// `parameters`.
    pub parameters: Vec<SymbolId>,
    /// `thisParameter`.
    pub this_parameter: Option<SymbolId>,
    /// `resolvedReturnType`.
    pub resolved_return_type: Option<TypeId>,
    /// `resolvedTypePredicate`.
    pub resolved_type_predicate: Option<Box<TypePredicate>>,
    /// `target`.
    pub target: Option<SignatureId>,
    /// `mapper`.
    pub mapper: Option<TypeMapperId>,
    /// `isolatedSignatureType`.
    pub isolated_signature_type: Option<TypeId>,
    /// `composite`.
    pub composite: Option<Box<CompositeSignature>>,
}

impl Signature {
    /// `(s *Signature) Id`.
    pub fn id(&self) -> SignatureId {
        self.id
    }

    /// `(s *Signature) Flags`.
    pub fn flags(&self) -> SignatureFlags {
        self.flags
    }

    /// `(s *Signature) TypeParameters`.
    pub fn type_parameters(&self) -> &[TypeId] {
        &self.type_parameters
    }

    /// `(s *Signature) Declaration`.
    pub fn declaration(&self) -> Option<NodeId> {
        self.declaration
    }

    /// `(s *Signature) Target`.
    pub fn target(&self) -> Option<SignatureId> {
        self.target
    }

    /// `(s *Signature) ThisParameter`.
    pub fn this_parameter(&self) -> Option<SymbolId> {
        self.this_parameter
    }

    /// `(s *Signature) Parameters`.
    pub fn parameters(&self) -> &[SymbolId] {
        &self.parameters
    }

    /// `(s *Signature) HasRestParameter`.
    pub fn has_rest_parameter(&self) -> bool {
        self.flags.intersects(SignatureFlags::HAS_REST_PARAMETER)
    }

    /// `(s *Signature) MinArgumentCount`.
    pub fn min_argument_count(&self) -> i32 {
        self.min_argument_count
    }
}

/// `type CompositeSignature struct`.
#[derive(Clone, Default)]
pub struct CompositeSignature {
    /// `isUnion` — true for union, false for intersection.
    pub is_union: bool,
    /// `signatures` — individual signatures.
    pub signatures: Vec<SignatureId>,
}

/// `type TypePredicateKind int32`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum TypePredicateKind {
    /// `TypePredicateKindThis`
    #[default]
    This = 0,
    /// `TypePredicateKindIdentifier`
    Identifier = 1,
    /// `TypePredicateKindAssertsThis`
    AssertsThis = 2,
    /// `TypePredicateKindAssertsIdentifier`
    AssertsIdentifier = 3,
}

/// `type TypePredicate struct`.
#[derive(Clone, Default)]
pub struct TypePredicate {
    /// `kind`.
    pub kind: TypePredicateKind,
    /// `parameterIndex`.
    pub parameter_index: i32,
    /// `parameterName`.
    pub parameter_name: String,
    /// `t`.
    pub t: Option<TypeId>,
}

impl TypePredicate {
    /// `(typePredicate *TypePredicate) Type`.
    pub fn t(&self) -> Option<TypeId> {
        self.t
    }

    /// `(typePredicate *TypePredicate) Kind`.
    pub fn kind(&self) -> TypePredicateKind {
        self.kind
    }

    /// `(typePredicate *TypePredicate) ParameterIndex`.
    pub fn parameter_index(&self) -> i32 {
        self.parameter_index
    }

    /// `(typePredicate *TypePredicate) ParameterName`.
    pub fn parameter_name(&self) -> &str {
        &self.parameter_name
    }
}

// IndexInfo

/// `type IndexInfo struct`.
/// PORT: `Clone` is needed where Go shared `*IndexInfo` values — the port
/// clones arena'd `IndexInfo`s into `StructuredType.index_infos`.
#[derive(Clone, Default)]
pub struct IndexInfo {
    /// `keyType`.
    pub key_type: Option<TypeId>,
    /// `valueType`.
    pub value_type: Option<TypeId>,
    /// `isReadonly`.
    pub is_readonly: bool,
    /// `declaration` — `IndexSignatureDeclaration`.
    pub declaration: Option<NodeId>,
    /// `indexSymbol` — synthetic property symbol for this index signature.
    pub index_symbol: Option<SymbolId>,
    /// `components` — `ElementWithComputedPropertyName`.
    pub components: Vec<NodeId>,
}

/// `IndexInfoId` — index into `Checker::index_info_arena` (Go `*IndexInfo`).
/// Go's `IndexInfo` values are arena-allocated and shared by pointer (e.g.
/// `enumNumberIndexInfo`/`anyBaseTypeIndexInfo` are compared for identity);
/// the inline `Vec<IndexInfo>` fields on structured types store copies.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[repr(transparent)]
pub struct IndexInfoId(pub u32);

impl IndexInfoId {
    /// The absent value (Go nil `*IndexInfo` where a bare id is required).
    pub const NONE: IndexInfoId = IndexInfoId(u32::MAX);

    /// The arena index of this id.
    #[inline]
    pub const fn index(self) -> usize {
        self.0 as usize
    }
}

/// `IndexInfoArena` — the port's `core.Arena[IndexInfo]`, a plain `Vec`
/// indexed by `IndexInfoId` (mirroring `SignatureArena`).
#[derive(Default)]
pub struct IndexInfoArena {
    index_infos: Vec<IndexInfo>,
}

impl IndexInfoArena {
    /// `indexInfoArena.New()` — allocate a slot, returning its `IndexInfoId`.
    pub fn alloc(&mut self, info: IndexInfo) -> IndexInfoId {
        let id = IndexInfoId(self.index_infos.len() as u32);
        self.index_infos.push(info);
        id
    }

    /// `*IndexInfo` field access.
    pub fn get(&self, id: IndexInfoId) -> &IndexInfo {
        &self.index_infos[id.index()]
    }

    /// `*IndexInfo` field write.
    pub fn get_mut(&mut self, id: IndexInfoId) -> &mut IndexInfo {
        &mut self.index_infos[id.index()]
    }
}

impl IndexInfo {
    /// `(info *IndexInfo) KeyType`.
    pub fn key_type(&self) -> Option<TypeId> {
        self.key_type
    }

    /// `(info *IndexInfo) ValueType`.
    pub fn value_type(&self) -> Option<TypeId> {
        self.value_type
    }

    /// `(info *IndexInfo) IsReadonly`.
    pub fn is_readonly(&self) -> bool {
        self.is_readonly
    }

    /// `(info *IndexInfo) Declaration`.
    pub fn declaration(&self) -> Option<NodeId> {
        self.declaration
    }
}

/// `type Ternary int8` — ternary values are defined such that `x & y` picks
/// the lesser in the order `False < Unknown < Maybe < True`, and `x | y`
/// picks the greater in the order `False < Unknown < Maybe < True`.
/// Generally, `Maybe` is used as the result of a relation that depends on
/// itself, and `Unknown` is used as the result of a variance check that
/// depends on itself. We make a distinction because we don't want to cache
/// circular variance check results.
///
/// PORT: `TernaryTrue = -1` is all-ones in two's complement — `&`/`|`
/// semantics survive verbatim on the wrapped `i8`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
#[repr(transparent)]
pub struct Ternary(pub i8);

impl Ternary {
    /// `TernaryFalse`.
    pub const FALSE: Ternary = Ternary(0);
    /// `TernaryUnknown`.
    pub const UNKNOWN: Ternary = Ternary(1);
    /// `TernaryMaybe`.
    pub const MAYBE: Ternary = Ternary(3);
    /// `TernaryTrue` — `-1`, all-ones so `&`/`|` pick the ordering Go
    /// documents.
    pub const TRUE: Ternary = Ternary(-1);

    /// Go `a && b` on `Ternary` (three-valued `min`) — same as `a & b` given
    /// the FALSE=0/MAYBE=3/TRUE=-1 encoding.
    pub fn and(self, rhs: Ternary) -> Ternary {
        self & rhs
    }

    /// Go `a || b` on `Ternary` — same as `a | b`.
    pub fn or(self, rhs: Ternary) -> Ternary {
        self | rhs
    }
}

impl core::ops::BitAnd for Ternary {
    type Output = Ternary;
    fn bitand(self, rhs: Ternary) -> Ternary {
        Ternary(self.0 & rhs.0)
    }
}

impl core::ops::BitOr for Ternary {
    type Output = Ternary;
    fn bitor(self, rhs: Ternary) -> Ternary {
        Ternary(self.0 | rhs.0)
    }
}

/// `type TypeComparer func(s *Type, t *Type, reportErrors bool) Ternary`.
///
/// PORT: Go comparers are closures capturing a checker; the port passes the
/// checker explicitly so the closure stays a plain `dyn Fn`.
pub type TypeComparer<'a> =
    dyn Fn(&mut crate::checker_core::Checker, TypeId, TypeId, bool) -> Ternary + 'a;

/// `type LanguageFeatureMinimumTargetMap struct`.
pub struct LanguageFeatureMinimumTargetMap {
    /// `Exponentiation`.
    pub exponentiation: ScriptTarget,
    /// `AsyncFunctions`.
    pub async_functions: ScriptTarget,
    /// `ForAwaitOf`.
    pub for_await_of: ScriptTarget,
    /// `AsyncGenerators`.
    pub async_generators: ScriptTarget,
    /// `AsyncIteration`.
    pub async_iteration: ScriptTarget,
    /// `ObjectSpreadRest`.
    pub object_spread_rest: ScriptTarget,
    /// `RegularExpressionFlagsDotAll`.
    pub regular_expression_flags_dot_all: ScriptTarget,
    /// `BindinglessCatch`.
    pub bindingless_catch: ScriptTarget,
    /// `BigInt`.
    pub big_int: ScriptTarget,
    /// `NullishCoalesce`.
    pub nullish_coalesce: ScriptTarget,
    /// `OptionalChaining`.
    pub optional_chaining: ScriptTarget,
    /// `LogicalAssignment`.
    pub logical_assignment: ScriptTarget,
    /// `TopLevelAwait`.
    pub top_level_await: ScriptTarget,
    /// `ClassFields`.
    pub class_fields: ScriptTarget,
    /// `PrivateNamesAndClassStaticBlocks`.
    pub private_names_and_class_static_blocks: ScriptTarget,
    /// `RegularExpressionFlagsHasIndices`.
    pub regular_expression_flags_has_indices: ScriptTarget,
    /// `ShebangComments`.
    pub shebang_comments: ScriptTarget,
    /// `UsingAndAwaitUsing`.
    pub using_and_await_using: ScriptTarget,
    /// `ClassAndClassElementDecorators`.
    pub class_and_class_element_decorators: ScriptTarget,
    /// `RegularExpressionFlagsUnicodeSets`.
    pub regular_expression_flags_unicode_sets: ScriptTarget,
}

/// `var LanguageFeatureMinimumTarget`.
pub const LANGUAGE_FEATURE_MINIMUM_TARGET: LanguageFeatureMinimumTargetMap =
    LanguageFeatureMinimumTargetMap {
        exponentiation: ScriptTarget::ES2016,
        async_functions: ScriptTarget::ES2017,
        for_await_of: ScriptTarget::ES2018,
        async_generators: ScriptTarget::ES2018,
        async_iteration: ScriptTarget::ES2018,
        object_spread_rest: ScriptTarget::ES2018,
        regular_expression_flags_dot_all: ScriptTarget::ES2018,
        bindingless_catch: ScriptTarget::ES2019,
        big_int: ScriptTarget::ES2020,
        nullish_coalesce: ScriptTarget::ES2020,
        optional_chaining: ScriptTarget::ES2020,
        logical_assignment: ScriptTarget::ES2021,
        top_level_await: ScriptTarget::ES2022,
        class_fields: ScriptTarget::ES2022,
        private_names_and_class_static_blocks: ScriptTarget::ES2022,
        regular_expression_flags_has_indices: ScriptTarget::ES2022,
        shebang_comments: ScriptTarget::ESNext,
        using_and_await_using: ScriptTarget::ESNext,
        class_and_class_element_decorators: ScriptTarget::ESNext,
        regular_expression_flags_unicode_sets: ScriptTarget::ESNext,
    };

// Aliases for types

/// `type StringLiteralType = Type` — a `*StringLiteralType` handle is a
/// `TypeId`.
pub type StringLiteralType = TypeId;

// TypeArena — the per-checker `Vec<Type>` store of SPEC §5.4.

/// `TypeArena` is the per-checker-shard arena of `Type` elements; `TypeId`
/// indexes it. `RwLock` because `tracing::TracedType` is `Send + Sync` and
/// recorded-type adapters outlive checker borrows — see the file header.
/// `HashMap`-based intern tables for literal/intrinsic/union types live on
/// the checker, not here (they're checker state in Go too).
#[derive(Clone, Default)]
pub struct TypeArena {
    /// `Arc` so `tracer.rs`'s `Send + Sync` `TracedType` adapter can hold a
    /// share of the arena post-hoc (Go's adapter holds the `*Type` heap
    /// pointer).
    types: Arc<RwLock<Vec<Type>>>,
}

/// `TypeArena::get` result — derefs to `Type`. PORT: a custom guard instead
/// of `MappedRwLockReadGuard` (`mapped_lock_guards` is unstable on stable).
pub struct TypeReadGuard<'a> {
    guard: RwLockReadGuard<'a, Vec<Type>>,
    index: usize,
}

impl std::ops::Deref for TypeReadGuard<'_> {
    type Target = Type;
    #[inline]
    fn deref(&self) -> &Type {
        &self.guard[self.index]
    }
}

/// `TypeArena::get_mut` result — derefs to `Type` (mutable).
pub struct TypeWriteGuard<'a> {
    guard: RwLockWriteGuard<'a, Vec<Type>>,
    index: usize,
}

impl std::ops::Deref for TypeWriteGuard<'_> {
    type Target = Type;
    #[inline]
    fn deref(&self) -> &Type {
        &self.guard[self.index]
    }
}

impl std::ops::DerefMut for TypeWriteGuard<'_> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Type {
        &mut self.guard[self.index]
    }
}

impl TypeArena {
    /// Allocate a type in the arena, returning its `TypeId`.
    pub fn alloc(&self, t: Type) -> TypeId {
        let mut types = self.types.write().unwrap();
        let id = TypeId(types.len() as u32);
        types.push(t);
        id
    }

    /// Read-locked access to a single type — the Go `t.field` read shape.
    /// Do not hold across `get_mut`/`alloc` (same-thread RwLock recursion
    /// deadlocks).
    pub fn get(&self, id: TypeId) -> TypeReadGuard<'_> {
        TypeReadGuard {
            guard: self.types.read().unwrap(),
            index: id.index(),
        }
    }

    /// Write-locked access to a single type — the Go `t.field = v` write
    /// shape. Compute the value before calling (a nested `get`/`get_mut` on
    /// the same arena deadlocks while the guard is held).
    pub fn get_mut(&self, id: TypeId) -> TypeWriteGuard<'_> {
        TypeWriteGuard {
            guard: self.types.write().unwrap(),
            index: id.index(),
        }
    }

    /// `len(types)`.
    pub fn len(&self) -> usize {
        self.types.read().unwrap().len()
    }

    /// `len(types) == 0`.
    pub fn is_empty(&self) -> bool {
        self.types.read().unwrap().is_empty()
    }

    /// `(t *Type) TargetInterfaceType` —
    /// `t.AsTypeReference().target.AsInterfaceType()`. PORT: returns the
    /// `TypeId` of the interface target (`Option` mirrors Go's nil-able
    /// `target`); callers re-borrow via `arena.get(id).as_interface_type()`.
    /// Panics like Go if the target is not an interface type... the Go code
    /// would panic on the nil/type-assertion paths too.
    pub fn target_interface_type(&self, t: TypeId) -> Option<TypeId> {
        let target = self.get(t).as_type_reference().object_type.target?;
        // Go asserts the target is an InterfaceType — check here so misuse
        // panics at the same point as Go's `AsInterfaceType()` on a non-nil
        // non-interface type would.
        debug_assert!(self.get(target).as_interface_type().is_some());
        Some(target)
    }

    /// `(t *Type) TargetTupleType` —
    /// `t.AsTypeReference().target.AsTupleType()`. Same arena shape as
    /// `target_interface_type`.
    pub fn target_tuple_type(&self, t: TypeId) -> Option<TypeId> {
        let target = self.get(t).as_type_reference().object_type.target?;
        debug_assert!(matches!(self.get(target).data, TypeData::Tuple(_)));
        Some(target)
    }
}

// SignatureArena — the per-checker `Vec<Signature>` store; `SignatureId`
// indexes it. Unlike `TypeArena` this is a plain Vec: signatures are only
// mutated while the checker is building them (SPEC §5.4 — the type arena's
// lock discipline doesn't apply to signature construction).

/// `SignatureArena` — arena of `Signature`, indexed by `SignatureId`.
#[derive(Default)]
pub struct SignatureArena {
    signatures: Vec<Signature>,
}

impl SignatureArena {
    /// Allocate a signature, returning its `SignatureId`.
    pub fn alloc(&mut self, s: Signature) -> SignatureId {
        let id = SignatureId(self.signatures.len() as u32);
        self.signatures.push(s);
        id
    }

    /// `*Signature` field access — the Go `s.field` read shape.
    pub fn get(&self, id: SignatureId) -> &Signature {
        &self.signatures[id.index()]
    }

    /// `*Signature` field write — the Go `s.field = v` shape.
    pub fn get_mut(&mut self, id: SignatureId) -> &mut Signature {
        &mut self.signatures[id.index()]
    }

    /// `len(signatures)`.
    pub fn len(&self) -> usize {
        self.signatures.len()
    }

    /// `len(signatures) == 0`.
    pub fn is_empty(&self) -> bool {
        self.signatures.is_empty()
    }

    /// Iterate over all signatures in arena order.
    pub fn iter(&self) -> impl Iterator<Item = (SignatureId, &Signature)> {
        self.signatures
            .iter()
            .enumerate()
            .map(|(i, s)| (SignatureId(i as u32), s))
    }
}

// ===========================================================================
// Type predicates shared with the checker (utilities.go/checker.go free fns)
// ===========================================================================

/// `IsTypeAny` (checker/utilities.go:286).
pub fn is_type_any(types: &TypeArena, t: TypeId) -> bool {
    types.get(t).flags.intersects(TypeFlags::ANY)
}

/// `(c *Checker) isErrorType` (checker.go:27172). The `c` back-pointer only
/// supplies `errorType`, which is the `TypeFlags::ANY` intrinsic named
/// `"error"` — so the `&TypeArena`-only form tests `intrinsic_name` instead
/// of pointer identity.
pub fn is_error_type(types: &TypeArena, t: TypeId) -> bool {
    let t = types.get(t);
    t.flags.intersects(TypeFlags::ANY)
        && (t.alias.is_some()
            || matches!(&t.data, crate::types::TypeData::Intrinsic(i) if i.intrinsic_name == "error"))
}

/// `isTypeUsableAsPropertyName` (checker/utilities.go:922).
pub fn is_type_usable_as_property_name(types: &TypeArena, t: TypeId) -> bool {
    types
        .get(t)
        .flags
        .intersects(TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE)
}

/// `isObjectLiteralType` (checker/utilities.go:867).
pub fn is_object_literal_type(types: &TypeArena, t: TypeId) -> bool {
    types
        .get(t)
        .object_flags
        .intersects(ObjectFlags::OBJECT_LITERAL)
}
