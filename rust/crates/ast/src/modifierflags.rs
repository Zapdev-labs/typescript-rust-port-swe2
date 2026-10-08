// Ported from tsc/internal/ast/modifierflags.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// ModifierFlags

flag_type! {
    pub struct ModifierFlags(pub u32);
}

impl ModifierFlags {
    // Syntactic/JSDoc modifiers
    pub const PUBLIC: ModifierFlags = ModifierFlags(1 << 0); // Property/Method
    pub const PRIVATE: ModifierFlags = ModifierFlags(1 << 1); // Property/Method
    pub const PROTECTED: ModifierFlags = ModifierFlags(1 << 2); // Property/Method
    pub const READONLY: ModifierFlags = ModifierFlags(1 << 3); // Property/Method
    pub const OVERRIDE: ModifierFlags = ModifierFlags(1 << 4); // Override method

    // Syntactic-only modifiers
    pub const EXPORT: ModifierFlags = ModifierFlags(1 << 5); // Declarations
    pub const ABSTRACT: ModifierFlags = ModifierFlags(1 << 6); // Class/Method/ConstructSignature
    pub const AMBIENT: ModifierFlags = ModifierFlags(1 << 7); // Declarations (declare keyword)
    pub const STATIC: ModifierFlags = ModifierFlags(1 << 8); // Property/Method
    pub const ACCESSOR: ModifierFlags = ModifierFlags(1 << 9); // Property
    pub const ASYNC: ModifierFlags = ModifierFlags(1 << 10); // Property/Method/Function
    pub const DEFAULT: ModifierFlags = ModifierFlags(1 << 11); // Function/Class (export default declaration)
    pub const CONST: ModifierFlags = ModifierFlags(1 << 12); // Const enum
    pub const IN: ModifierFlags = ModifierFlags(1 << 13); // Contravariance modifier
    pub const OUT: ModifierFlags = ModifierFlags(1 << 14); // Covariance modifier
    pub const DECORATOR: ModifierFlags = ModifierFlags(1 << 15); // Contains a decorator

    // JSDoc-only modifiers
    pub const DEPRECATED: ModifierFlags = ModifierFlags(1 << 16); // Deprecated tag

    // Cache-only JSDoc-modifiers. Should match order of Syntactic/JSDoc modifiers, above.
    /// if this value changes, `select_effective_modifier_flags` must change accordingly
    pub const JSDOC_PUBLIC: ModifierFlags = ModifierFlags(1 << 23);
    pub const JSDOC_PRIVATE: ModifierFlags = ModifierFlags(1 << 24);
    pub const JSDOC_PROTECTED: ModifierFlags = ModifierFlags(1 << 25);
    pub const JSDOC_READONLY: ModifierFlags = ModifierFlags(1 << 26);
    pub const JSDOC_OVERRIDE: ModifierFlags = ModifierFlags(1 << 27);
    /// Indicates the computed modifier flags include modifiers from JSDoc.
    pub const HAS_COMPUTED_JSDOC_MODIFIERS: ModifierFlags = ModifierFlags(1 << 28);
    /// Modifier flags have been computed
    pub const HAS_COMPUTED_FLAGS: ModifierFlags = ModifierFlags(1 << 29);

    pub const SYNTACTIC_OR_JSDOC_MODIFIERS: ModifierFlags = ModifierFlags(
        Self::PUBLIC.0 | Self::PRIVATE.0 | Self::PROTECTED.0 | Self::READONLY.0 | Self::OVERRIDE.0,
    );
    pub const SYNTACTIC_ONLY_MODIFIERS: ModifierFlags = ModifierFlags(
        Self::EXPORT.0
            | Self::AMBIENT.0
            | Self::ABSTRACT.0
            | Self::STATIC.0
            | Self::ACCESSOR.0
            | Self::ASYNC.0
            | Self::DEFAULT.0
            | Self::CONST.0
            | Self::IN.0
            | Self::OUT.0
            | Self::DECORATOR.0,
    );
    pub const SYNTACTIC_MODIFIERS: ModifierFlags =
        ModifierFlags(Self::SYNTACTIC_OR_JSDOC_MODIFIERS.0 | Self::SYNTACTIC_ONLY_MODIFIERS.0);
    pub const JSDOC_CACHE_ONLY_MODIFIERS: ModifierFlags = ModifierFlags(
        Self::JSDOC_PUBLIC.0
            | Self::JSDOC_PRIVATE.0
            | Self::JSDOC_PROTECTED.0
            | Self::JSDOC_READONLY.0
            | Self::JSDOC_OVERRIDE.0,
    );
    pub const JSDOC_ONLY_MODIFIERS: ModifierFlags = Self::DEPRECATED;
    pub const NON_CACHE_ONLY_MODIFIERS: ModifierFlags = ModifierFlags(
        Self::SYNTACTIC_OR_JSDOC_MODIFIERS.0
            | Self::SYNTACTIC_ONLY_MODIFIERS.0
            | Self::JSDOC_ONLY_MODIFIERS.0,
    );

    pub const ACCESSIBILITY_MODIFIER: ModifierFlags =
        ModifierFlags(Self::PUBLIC.0 | Self::PRIVATE.0 | Self::PROTECTED.0);

    /// Accessibility modifiers and 'readonly' can be attached to a parameter in a constructor to make it a property.
    pub const PARAMETER_PROPERTY_MODIFIER: ModifierFlags =
        ModifierFlags(Self::ACCESSIBILITY_MODIFIER.0 | Self::READONLY.0 | Self::OVERRIDE.0);
    pub const NON_PUBLIC_ACCESSIBILITY_MODIFIER: ModifierFlags =
        ModifierFlags(Self::PRIVATE.0 | Self::PROTECTED.0);

    pub const TYPE_SCRIPT_MODIFIER: ModifierFlags = ModifierFlags(
        Self::AMBIENT.0
            | Self::PUBLIC.0
            | Self::PRIVATE.0
            | Self::PROTECTED.0
            | Self::READONLY.0
            | Self::ABSTRACT.0
            | Self::CONST.0
            | Self::OVERRIDE.0
            | Self::IN.0
            | Self::OUT.0,
    );
    pub const EXPORT_DEFAULT: ModifierFlags = ModifierFlags(Self::EXPORT.0 | Self::DEFAULT.0);
    pub const ALL: ModifierFlags = ModifierFlags(
        Self::EXPORT.0
            | Self::AMBIENT.0
            | Self::PUBLIC.0
            | Self::PRIVATE.0
            | Self::PROTECTED.0
            | Self::STATIC.0
            | Self::READONLY.0
            | Self::ABSTRACT.0
            | Self::ACCESSOR.0
            | Self::ASYNC.0
            | Self::DEFAULT.0
            | Self::CONST.0
            | Self::DEPRECATED.0
            | Self::OVERRIDE.0
            | Self::IN.0
            | Self::OUT.0
            | Self::DECORATOR.0,
    );
    pub const MODIFIER: ModifierFlags = ModifierFlags(Self::ALL.0 & !Self::DECORATOR.0);
    pub const JAVA_SCRIPT: ModifierFlags = ModifierFlags(
        Self::EXPORT.0 | Self::STATIC.0 | Self::ACCESSOR.0 | Self::ASYNC.0 | Self::DEFAULT.0,
    );
}
