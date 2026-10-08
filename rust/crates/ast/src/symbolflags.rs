// Ported from tsc/internal/ast/symbolflags.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// SymbolFlags

flag_type! {
    pub struct SymbolFlags(pub u32);
}

impl SymbolFlags {
    /// Variable (var) or parameter
    pub const FUNCTION_SCOPED_VARIABLE: SymbolFlags = SymbolFlags(1 << 0);
    /// A block-scoped variable (let or const)
    pub const BLOCK_SCOPED_VARIABLE: SymbolFlags = SymbolFlags(1 << 1);
    /// Property or enum member
    pub const PROPERTY: SymbolFlags = SymbolFlags(1 << 2);
    /// Enum member
    pub const ENUM_MEMBER: SymbolFlags = SymbolFlags(1 << 3);
    /// Function
    pub const FUNCTION: SymbolFlags = SymbolFlags(1 << 4);
    /// Class
    pub const CLASS: SymbolFlags = SymbolFlags(1 << 5);
    /// Interface
    pub const INTERFACE: SymbolFlags = SymbolFlags(1 << 6);
    /// Const enum
    pub const CONST_ENUM: SymbolFlags = SymbolFlags(1 << 7);
    /// Enum
    pub const REGULAR_ENUM: SymbolFlags = SymbolFlags(1 << 8);
    /// Instantiated module
    pub const VALUE_MODULE: SymbolFlags = SymbolFlags(1 << 9);
    /// Uninstantiated module
    pub const NAMESPACE_MODULE: SymbolFlags = SymbolFlags(1 << 10);
    /// Type Literal or mapped type
    pub const TYPE_LITERAL: SymbolFlags = SymbolFlags(1 << 11);
    /// Object Literal
    pub const OBJECT_LITERAL: SymbolFlags = SymbolFlags(1 << 12);
    /// Method
    pub const METHOD: SymbolFlags = SymbolFlags(1 << 13);
    /// Constructor
    pub const CONSTRUCTOR: SymbolFlags = SymbolFlags(1 << 14);
    /// Get accessor
    pub const GET_ACCESSOR: SymbolFlags = SymbolFlags(1 << 15);
    /// Set accessor
    pub const SET_ACCESSOR: SymbolFlags = SymbolFlags(1 << 16);
    /// Call, construct, or index signature
    pub const SIGNATURE: SymbolFlags = SymbolFlags(1 << 17);
    /// Type parameter
    pub const TYPE_PARAMETER: SymbolFlags = SymbolFlags(1 << 18);
    /// Type alias
    pub const TYPE_ALIAS: SymbolFlags = SymbolFlags(1 << 19);
    /// Exported value marker (see comment in declareModuleMember in binder)
    pub const EXPORT_VALUE: SymbolFlags = SymbolFlags(1 << 20);
    /// An alias for another symbol (see comment in isAliasSymbolDeclaration in checker)
    pub const ALIAS: SymbolFlags = SymbolFlags(1 << 21);
    /// Prototype property (no source representation)
    pub const PROTOTYPE: SymbolFlags = SymbolFlags(1 << 22);
    /// Export * declaration
    pub const EXPORT_STAR: SymbolFlags = SymbolFlags(1 << 23);
    /// Optional property
    pub const OPTIONAL: SymbolFlags = SymbolFlags(1 << 24);
    /// Transient symbol (created during type check)
    pub const TRANSIENT: SymbolFlags = SymbolFlags(1 << 25);
    /// Assignment to property on function acting as declaration (eg `func.prop = 1`)
    pub const ASSIGNMENT: SymbolFlags = SymbolFlags(1 << 26);
    /// Symbol for CommonJS `module` of `module.exports`
    pub const MODULE_EXPORTS: SymbolFlags = SymbolFlags(1 << 27);
    /// Module contains only const enums or other modules with only const enums
    pub const CONST_ENUM_ONLY_MODULE: SymbolFlags = SymbolFlags(1 << 28);
    pub const REPLACEABLE_BY_METHOD: SymbolFlags = SymbolFlags(1 << 29);
    /// Flag to signal this is a global lookup
    pub const GLOBAL_LOOKUP: SymbolFlags = SymbolFlags(1 << 30);
    /// All flags except SymbolFlagsGlobalLookup
    pub const ALL: SymbolFlags = SymbolFlags((1 << 30) - 1);

    pub const ENUM: SymbolFlags = SymbolFlags(Self::REGULAR_ENUM.0 | Self::CONST_ENUM.0);
    pub const VARIABLE: SymbolFlags =
        SymbolFlags(Self::FUNCTION_SCOPED_VARIABLE.0 | Self::BLOCK_SCOPED_VARIABLE.0);
    pub const VALUE: SymbolFlags = SymbolFlags(
        Self::VARIABLE.0
            | Self::PROPERTY.0
            | Self::ENUM_MEMBER.0
            | Self::OBJECT_LITERAL.0
            | Self::FUNCTION.0
            | Self::CLASS.0
            | Self::ENUM.0
            | Self::VALUE_MODULE.0
            | Self::METHOD.0
            | Self::GET_ACCESSOR.0
            | Self::SET_ACCESSOR.0,
    );
    pub const TYPE: SymbolFlags = SymbolFlags(
        Self::CLASS.0
            | Self::INTERFACE.0
            | Self::ENUM.0
            | Self::ENUM_MEMBER.0
            | Self::TYPE_LITERAL.0
            | Self::TYPE_PARAMETER.0
            | Self::TYPE_ALIAS.0,
    );
    pub const NAMESPACE: SymbolFlags =
        SymbolFlags(Self::VALUE_MODULE.0 | Self::NAMESPACE_MODULE.0 | Self::ENUM.0);
    pub const MODULE: SymbolFlags = SymbolFlags(Self::VALUE_MODULE.0 | Self::NAMESPACE_MODULE.0);
    pub const ACCESSOR: SymbolFlags = SymbolFlags(Self::GET_ACCESSOR.0 | Self::SET_ACCESSOR.0);

    /// Variables can be redeclared, but can not redeclare a block-scoped declaration with the
    /// same name, or any other value that is not a variable, e.g. ValueModule or Class
    pub const FUNCTION_SCOPED_VARIABLE_EXCLUDES: SymbolFlags =
        Self::VALUE.without(Self::FUNCTION_SCOPED_VARIABLE);
    /// Block-scoped declarations are not allowed to be re-declared
    /// they can not merge with anything in the value space
    pub const BLOCK_SCOPED_VARIABLE_EXCLUDES: SymbolFlags = Self::VALUE;
    pub const PARAMETER_EXCLUDES: SymbolFlags = Self::VALUE;
    pub const PROPERTY_EXCLUDES: SymbolFlags =
        Self::VALUE.without(Self::PROPERTY.with(Self::ACCESSOR));
    pub const ENUM_MEMBER_EXCLUDES: SymbolFlags = Self::VALUE.with(Self::TYPE);
    pub const FUNCTION_EXCLUDES: SymbolFlags =
        Self::VALUE.without(Self::FUNCTION.with(Self::VALUE_MODULE).with(Self::CLASS));
    /// class-interface mergability done in checker.ts
    pub const CLASS_EXCLUDES: SymbolFlags = Self::VALUE.with(Self::TYPE).without(
        Self::VALUE_MODULE
            .with(Self::INTERFACE)
            .with(Self::FUNCTION),
    );
    pub const INTERFACE_EXCLUDES: SymbolFlags =
        Self::TYPE.without(Self::INTERFACE.with(Self::CLASS));
    /// regular enums merge only with regular enums and modules
    pub const REGULAR_ENUM_EXCLUDES: SymbolFlags = Self::VALUE
        .with(Self::TYPE)
        .without(Self::REGULAR_ENUM.with(Self::VALUE_MODULE));
    /// const enums merge only with const enums
    pub const CONST_ENUM_EXCLUDES: SymbolFlags =
        Self::VALUE.with(Self::TYPE).without(Self::CONST_ENUM);
    pub const VALUE_MODULE_EXCLUDES: SymbolFlags = Self::VALUE.without(
        Self::FUNCTION
            .with(Self::CLASS)
            .with(Self::REGULAR_ENUM)
            .with(Self::VALUE_MODULE),
    );
    pub const NAMESPACE_MODULE_EXCLUDES: SymbolFlags = Self::NONE;
    pub const METHOD_EXCLUDES: SymbolFlags = Self::VALUE.without(Self::METHOD);
    pub const GET_ACCESSOR_EXCLUDES: SymbolFlags =
        Self::VALUE.without(Self::SET_ACCESSOR.with(Self::PROPERTY));
    pub const SET_ACCESSOR_EXCLUDES: SymbolFlags =
        Self::VALUE.without(Self::GET_ACCESSOR.with(Self::PROPERTY));
    pub const ACCESSOR_EXCLUDES: SymbolFlags = Self::VALUE.without(Self::PROPERTY);
    pub const TYPE_PARAMETER_EXCLUDES: SymbolFlags = Self::TYPE.without(Self::TYPE_PARAMETER);
    pub const TYPE_ALIAS_EXCLUDES: SymbolFlags = Self::TYPE;
    pub const ALIAS_EXCLUDES: SymbolFlags = Self::ALIAS;
    pub const MODULE_MEMBER: SymbolFlags = SymbolFlags(
        Self::VARIABLE.0
            | Self::FUNCTION.0
            | Self::CLASS.0
            | Self::INTERFACE.0
            | Self::ENUM.0
            | Self::MODULE.0
            | Self::TYPE_ALIAS.0
            | Self::ALIAS.0,
    );
    pub const EXPORT_HAS_LOCAL: SymbolFlags =
        SymbolFlags(Self::FUNCTION.0 | Self::CLASS.0 | Self::ENUM.0 | Self::VALUE_MODULE.0);
    pub const BLOCK_SCOPED: SymbolFlags =
        SymbolFlags(Self::BLOCK_SCOPED_VARIABLE.0 | Self::CLASS.0 | Self::ENUM.0);
    pub const PROPERTY_OR_ACCESSOR: SymbolFlags = SymbolFlags(Self::PROPERTY.0 | Self::ACCESSOR.0);
    pub const CLASS_MEMBER: SymbolFlags =
        SymbolFlags(Self::METHOD.0 | Self::ACCESSOR.0 | Self::PROPERTY.0);
    pub const EXPORT_SUPPORTS_DEFAULT_MODIFIER: SymbolFlags =
        SymbolFlags(Self::CLASS.0 | Self::FUNCTION.0 | Self::INTERFACE.0);
    pub const EXPORT_DOES_NOT_SUPPORT_DEFAULT_MODIFIER: SymbolFlags =
        SymbolFlags(!Self::EXPORT_SUPPORTS_DEFAULT_MODIFIER.0);
    pub const LATE_BINDING_CONTAINER: SymbolFlags = SymbolFlags(
        Self::CLASS.0
            | Self::INTERFACE.0
            | Self::TYPE_LITERAL.0
            | Self::OBJECT_LITERAL.0
            | Self::FUNCTION.0,
    );
}
