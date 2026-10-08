// Ported from tsc/internal/nodebuilder/types.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Exports interfaces and types defining the node builder - concrete implementations are on top of the checker, but these types and interfaces are used by the emit resolver in the printer

use tsc_ast::ids::{NodeId, SymbolId};
use tsc_ast::symbolflags::SymbolFlags;

/// `type SymbolTracker interface`.
///
/// TODO: previously all symboltracker methods were optional, but now they're required.
///
/// PORT: `*ast.Symbol` → `SymbolId`, `*ast.Node` → `NodeId` (`Option<NodeId>`
/// for `enclosingDeclaration`, which Go passes as nil), and
/// `*ast.SourceFile` → the `NodeId` of the SourceFile-kind node (the same
/// shape `get_source_file_of_node` returns). Go's implicit access to the
/// node/symbol arenas via pointers is left to implementors — the checker-side
/// trackers own that context — so no `nodes`/`symbols` arena parameters are
/// threaded through here.
pub trait SymbolTracker {
    /// `TrackSymbol(symbol *ast.Symbol, enclosingDeclaration *ast.Node, meaning ast.SymbolFlags) bool`
    fn track_symbol(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: SymbolFlags,
    ) -> bool;
    /// `ReportInaccessibleThisError()`
    fn report_inaccessible_this_error(&mut self);
    /// `ReportPrivateInBaseOfClassExpression(propertyName string)`
    fn report_private_in_base_of_class_expression(&mut self, property_name: &str);
    /// `ReportInaccessibleUniqueSymbolError()`
    fn report_inaccessible_unique_symbol_error(&mut self);
    /// `ReportCyclicStructureError()`
    fn report_cyclic_structure_error(&mut self);
    /// `ReportLikelyUnsafeImportRequiredError(specifier string, symbolName string)`
    fn report_likely_unsafe_import_required_error(&mut self, specifier: &str, symbol_name: &str);
    /// `ReportTruncationError()`
    fn report_truncation_error(&mut self);
    /// `ReportNonlocalAugmentation(containingFile *ast.SourceFile, parentSymbol *ast.Symbol, augmentingSymbol *ast.Symbol)`
    fn report_nonlocal_augmentation(
        &mut self,
        containing_file: NodeId,
        parent_symbol: SymbolId,
        augmenting_symbol: SymbolId,
    );
    /// `ReportNonSerializableProperty(propertyName string)`
    fn report_non_serializable_property(&mut self, property_name: &str);

    /// `ReportInferenceFallback(node *ast.Node)`
    fn report_inference_fallback(&mut self, node: NodeId);
    /// `PushErrorFallbackNode(node *ast.Node)`
    fn push_error_fallback_node(&mut self, node: NodeId);
    /// `PopErrorFallbackNode()`
    fn pop_error_fallback_node(&mut self);

    /// PORT: `NewSymbolTrackerImpl` in the checker peels nested
    /// `*SymbolTrackerImpl` wrappers via a `tracker.(*SymbolTrackerImpl)`
    /// loop. `dyn SymbolTracker` can't express that type assertion, so the
    /// trait exposes this hook: for a `SymbolTrackerImpl` it takes and
    /// returns `Some(self.inner)` (the wrapped tracker, itself possibly
    /// `None`); the default returns `None` for "not a `SymbolTrackerImpl`".
    #[doc(hidden)]
    fn take_symbol_tracker_impl_inner(&mut self) -> Option<Option<Box<dyn SymbolTracker>>> {
        None
    }
}

// PORT: `flag_type!` is crate-private to tsc-ast, so the same bitmask newtype
// shape is spelled out by hand here — `pub struct X(pub u32)` plus the bit
// operators used by the Go sources.

/// `type Flags uint32`.
///
/// NOTE: If modifying this enum, must modify `TypeFormatFlags` too!
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct Flags(pub u32);

impl Flags {
    /// `FlagsNone`
    pub const NONE: Flags = Flags(0);

    // Options
    /// `FlagsNoTruncation`
    pub const NO_TRUNCATION: Flags = Flags(1 << 0);
    /// `FlagsWriteArrayAsGenericType`
    pub const WRITE_ARRAY_AS_GENERIC_TYPE: Flags = Flags(1 << 1);
    /// `FlagsGenerateNamesForShadowedTypeParams`
    pub const GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS: Flags = Flags(1 << 2);
    /// `FlagsUseStructuralFallback`
    pub const USE_STRUCTURAL_FALLBACK: Flags = Flags(1 << 3);
    /// `FlagsForbidIndexedAccessSymbolReferences`
    pub const FORBID_INDEXED_ACCESS_SYMBOL_REFERENCES: Flags = Flags(1 << 4);
    /// `FlagsWriteTypeArgumentsOfSignature`
    pub const WRITE_TYPE_ARGUMENTS_OF_SIGNATURE: Flags = Flags(1 << 5);
    /// `FlagsUseFullyQualifiedType`
    pub const USE_FULLY_QUALIFIED_TYPE: Flags = Flags(1 << 6);
    /// `FlagsUseOnlyExternalAliasing`
    pub const USE_ONLY_EXTERNAL_ALIASING: Flags = Flags(1 << 7);
    /// `FlagsSuppressAnyReturnType`
    pub const SUPPRESS_ANY_RETURN_TYPE: Flags = Flags(1 << 8);
    /// `FlagsWriteTypeParametersInQualifiedName`
    pub const WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME: Flags = Flags(1 << 9);
    /// `FlagsMultilineObjectLiterals`
    pub const MULTILINE_OBJECT_LITERALS: Flags = Flags(1 << 10);
    /// `FlagsWriteClassExpressionAsTypeLiteral`
    pub const WRITE_CLASS_EXPRESSION_AS_TYPE_LITERAL: Flags = Flags(1 << 11);
    /// `FlagsUseTypeOfFunction`
    pub const USE_TYPE_OF_FUNCTION: Flags = Flags(1 << 12);
    /// `FlagsOmitParameterModifiers`
    pub const OMIT_PARAMETER_MODIFIERS: Flags = Flags(1 << 13);
    /// `FlagsUseAliasDefinedOutsideCurrentScope`
    pub const USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE: Flags = Flags(1 << 14);
    /// `FlagsUseSingleQuotesForStringLiteralType`
    pub const USE_SINGLE_QUOTES_FOR_STRING_LITERAL_TYPE: Flags = Flags(1 << 28);
    /// `FlagsNoTypeReduction`
    pub const NO_TYPE_REDUCTION: Flags = Flags(1 << 29);
    /// `FlagsUseInstantiationExpressions`
    pub const USE_INSTANTIATION_EXPRESSIONS: Flags = Flags(1 << 30);
    /// `FlagsOmitThisParameter`
    pub const OMIT_THIS_PARAMETER: Flags = Flags(1 << 25);
    /// `FlagsWriteCallStyleSignature`
    pub const WRITE_CALL_STYLE_SIGNATURE: Flags = Flags(1 << 27);

    // Error handling
    /// `FlagsAllowThisInObjectLiteral`
    pub const ALLOW_THIS_IN_OBJECT_LITERAL: Flags = Flags(1 << 15);
    /// `FlagsAllowQualifiedNameInPlaceOfIdentifier`
    pub const ALLOW_QUALIFIED_NAME_IN_PLACE_OF_IDENTIFIER: Flags = Flags(1 << 16);
    /// `FlagsAllowAnonymousIdentifier`
    pub const ALLOW_ANONYMOUS_IDENTIFIER: Flags = Flags(1 << 17);
    /// `FlagsAllowEmptyUnionOrIntersection`
    pub const ALLOW_EMPTY_UNION_OR_INTERSECTION: Flags = Flags(1 << 18);
    /// `FlagsAllowEmptyTuple`
    pub const ALLOW_EMPTY_TUPLE: Flags = Flags(1 << 19);
    /// `FlagsAllowUniqueESSymbolType`
    pub const ALLOW_UNIQUE_ES_SYMBOL_TYPE: Flags = Flags(1 << 20);
    /// `FlagsAllowEmptyIndexInfoType`
    pub const ALLOW_EMPTY_INDEX_INFO_TYPE: Flags = Flags(1 << 21);

    // Errors (cont.)
    /// `FlagsAllowNodeModulesRelativePaths`
    pub const ALLOW_NODE_MODULES_RELATIVE_PATHS: Flags = Flags(1 << 26);
    /// `FlagsIgnoreErrors`
    pub const IGNORE_ERRORS: Flags = Flags(
        Self::ALLOW_THIS_IN_OBJECT_LITERAL.0
            | Self::ALLOW_QUALIFIED_NAME_IN_PLACE_OF_IDENTIFIER.0
            | Self::ALLOW_ANONYMOUS_IDENTIFIER.0
            | Self::ALLOW_EMPTY_UNION_OR_INTERSECTION.0
            | Self::ALLOW_EMPTY_TUPLE.0
            | Self::ALLOW_EMPTY_INDEX_INFO_TYPE.0
            | Self::ALLOW_NODE_MODULES_RELATIVE_PATHS.0,
    );

    // State
    /// `FlagsInObjectTypeLiteral`
    pub const IN_OBJECT_TYPE_LITERAL: Flags = Flags(1 << 22);
    /// `FlagsInTypeAlias`
    pub const IN_TYPE_ALIAS: Flags = Flags(1 << 23);
    /// `FlagsInInitialEntityName`
    pub const IN_INITIAL_ENTITY_NAME: Flags = Flags(1 << 24);

    /// `self & flags != 0`
    #[inline]
    pub const fn intersects(self, flags: Self) -> bool {
        self.0 & flags.0 != 0
    }

    /// `self & flags == flags`
    #[inline]
    pub const fn contains(self, flags: Self) -> bool {
        self.0 & flags.0 == flags.0
    }

    /// `self | flags`
    #[inline]
    pub const fn with(self, flags: Self) -> Self {
        Self(self.0 | flags.0)
    }

    /// `self & !flags`
    #[inline]
    pub const fn without(self, flags: Self) -> Self {
        Self(self.0 & !flags.0)
    }

    /// `self |= flags`
    #[inline]
    pub fn insert(&mut self, flags: Self) {
        self.0 |= flags.0;
    }

    /// `self &= !flags`
    #[inline]
    pub fn remove(&mut self, flags: Self) {
        self.0 &= !flags.0;
    }

    /// `self == 0`
    #[inline]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The raw bit representation.
    #[inline]
    pub const fn bits(self) -> u32 {
        self.0
    }
}

impl core::ops::BitOr for Flags {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl core::ops::BitOrAssign for Flags {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl core::ops::BitAnd for Flags {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

impl core::ops::BitAndAssign for Flags {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl core::ops::Not for Flags {
    type Output = Self;
    #[inline]
    fn not(self) -> Self {
        Self(!self.0)
    }
}

impl core::fmt::Debug for Flags {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Flags({:#x})", self.0)
    }
}

/// `type InternalFlags int32` — @internal in Go.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct InternalFlags(pub i32);

impl InternalFlags {
    /// `InternalFlagsNone`
    pub const NONE: InternalFlags = InternalFlags(0);
    /// `InternalFlagsWriteComputedProps`
    pub const WRITE_COMPUTED_PROPS: InternalFlags = InternalFlags(1 << 0);
    /// `InternalFlagsNoSyntacticPrinter`
    pub const NO_SYNTACTIC_PRINTER: InternalFlags = InternalFlags(1 << 1);
    /// `InternalFlagsDoNotIncludeSymbolChain`
    pub const DO_NOT_INCLUDE_SYMBOL_CHAIN: InternalFlags = InternalFlags(1 << 2);
    /// `InternalFlagsAllowUnresolvedNames`
    pub const ALLOW_UNRESOLVED_NAMES: InternalFlags = InternalFlags(1 << 3);

    /// `self & flags != 0`
    #[inline]
    pub const fn intersects(self, flags: Self) -> bool {
        self.0 & flags.0 != 0
    }

    /// `self & flags == flags`
    #[inline]
    pub const fn contains(self, flags: Self) -> bool {
        self.0 & flags.0 == flags.0
    }

    /// `self | flags`
    #[inline]
    pub const fn with(self, flags: Self) -> Self {
        Self(self.0 | flags.0)
    }

    /// `self & !flags`
    #[inline]
    pub const fn without(self, flags: Self) -> Self {
        Self(self.0 & !flags.0)
    }

    /// `self |= flags`
    #[inline]
    pub fn insert(&mut self, flags: Self) {
        self.0 |= flags.0;
    }

    /// `self &= !flags`
    #[inline]
    pub fn remove(&mut self, flags: Self) {
        self.0 &= !flags.0;
    }

    /// `self == 0`
    #[inline]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// The raw bit representation.
    #[inline]
    pub const fn bits(self) -> i32 {
        self.0
    }
}

impl core::ops::BitOr for InternalFlags {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        Self(self.0 | rhs.0)
    }
}

impl core::ops::BitOrAssign for InternalFlags {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl core::ops::BitAnd for InternalFlags {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

impl core::ops::BitAndAssign for InternalFlags {
    #[inline]
    fn bitand_assign(&mut self, rhs: Self) {
        self.0 &= rhs.0;
    }
}

impl core::ops::Not for InternalFlags {
    type Output = Self;
    #[inline]
    fn not(self) -> Self {
        Self(!self.0)
    }
}

impl core::fmt::Debug for InternalFlags {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "InternalFlags({:#x})", self.0)
    }
}
