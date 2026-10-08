// Ported from tsc/internal/ast/checkflags.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// CheckFlags

flag_type! {
    pub struct CheckFlags(pub u32);
}

impl CheckFlags {
    /// Instantiated symbol
    pub const INSTANTIATED: CheckFlags = CheckFlags(1 << 0);
    /// Property in union or intersection type
    pub const SYNTHETIC_PROPERTY: CheckFlags = CheckFlags(1 << 1);
    /// Method in union or intersection type
    pub const SYNTHETIC_METHOD: CheckFlags = CheckFlags(1 << 2);
    /// Readonly transient symbol
    pub const READONLY: CheckFlags = CheckFlags(1 << 3);
    /// Synthetic property present in some but not all constituents
    pub const READ_PARTIAL: CheckFlags = CheckFlags(1 << 4);
    /// Synthetic property present in some but only satisfied by an index signature in others
    pub const WRITE_PARTIAL: CheckFlags = CheckFlags(1 << 5);
    /// Synthetic property with non-uniform type in constituents
    pub const HAS_NON_UNIFORM_TYPE: CheckFlags = CheckFlags(1 << 6);
    /// Synthetic property with at least one literal type in constituents
    pub const HAS_LITERAL_TYPE: CheckFlags = CheckFlags(1 << 7);
    /// Synthetic property with public constituent(s)
    pub const CONTAINS_PUBLIC: CheckFlags = CheckFlags(1 << 8);
    /// Synthetic property with protected constituent(s)
    pub const CONTAINS_PROTECTED: CheckFlags = CheckFlags(1 << 9);
    /// Synthetic property with private constituent(s)
    pub const CONTAINS_PRIVATE: CheckFlags = CheckFlags(1 << 10);
    /// Synthetic property with public set accessors(s)
    pub const CONTAINS_WRITE_PUBLIC: CheckFlags = CheckFlags(1 << 11);
    /// Synthetic property with protected set accessors(s)
    pub const CONTAINS_WRITE_PROTECTED: CheckFlags = CheckFlags(1 << 12);
    /// Synthetic property with private set accessors(s)
    pub const CONTAINS_WRITE_PRIVATE: CheckFlags = CheckFlags(1 << 13);
    /// Synthetic property with static constituent(s)
    pub const CONTAINS_STATIC: CheckFlags = CheckFlags(1 << 14);
    /// Late-bound symbol for a computed property with a dynamic name
    pub const LATE: CheckFlags = CheckFlags(1 << 15);
    /// Property of reverse-inferred homomorphic mapped type
    pub const REVERSE_MAPPED: CheckFlags = CheckFlags(1 << 16);
    /// Optional parameter
    pub const OPTIONAL_PARAMETER: CheckFlags = CheckFlags(1 << 17);
    /// Rest parameter
    pub const REST_PARAMETER: CheckFlags = CheckFlags(1 << 18);
    /// Calculation of the type of this symbol is deferred due to processing costs, should be fetched with `getTypeOfSymbolWithDeferredType`
    pub const DEFERRED_TYPE: CheckFlags = CheckFlags(1 << 19);
    /// Synthetic property with at least one never type in constituents
    pub const HAS_NEVER_TYPE: CheckFlags = CheckFlags(1 << 20);
    /// Property of mapped type
    pub const MAPPED: CheckFlags = CheckFlags(1 << 21);
    /// Strip optionality in mapped property
    pub const STRIP_OPTIONAL: CheckFlags = CheckFlags(1 << 22);
    /// Unresolved type alias symbol
    pub const UNRESOLVED: CheckFlags = CheckFlags(1 << 23);
    /// IsDiscriminant flags has been computed
    pub const IS_DISCRIMINANT_COMPUTED: CheckFlags = CheckFlags(1 << 24);
    /// Discriminant property
    pub const IS_DISCRIMINANT: CheckFlags = CheckFlags(1 << 25);
    /// Synthetic property created from index signature
    pub const INDEX_SYMBOL: CheckFlags = CheckFlags(1 << 26);

    pub const SYNTHETIC: CheckFlags =
        CheckFlags(Self::SYNTHETIC_PROPERTY.0 | Self::SYNTHETIC_METHOD.0);
    pub const NON_UNIFORM_AND_LITERAL: CheckFlags =
        CheckFlags(Self::HAS_NON_UNIFORM_TYPE.0 | Self::HAS_LITERAL_TYPE.0);
    pub const PARTIAL: CheckFlags = CheckFlags(Self::READ_PARTIAL.0 | Self::WRITE_PARTIAL.0);
}
