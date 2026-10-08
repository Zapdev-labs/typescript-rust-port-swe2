// Ported from tsc/internal/printer/emitflags.go and
// tsc/internal/printer/generatedidentifierflags.go @ ec47d33c23e464a17cdf2475632cba629bee8763

/// `type EmitFlags uint32`
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct EmitFlags(pub u32);

impl EmitFlags {
    /// `EFNone`
    pub const NONE: EmitFlags = EmitFlags(0);
    /// `EFSingleLine` — The contents of this node should be emitted on a single line.
    pub const SINGLE_LINE: EmitFlags = EmitFlags(1 << 0);
    /// `EFMultiLine` — The contents of this node should be emitted on multiple lines.
    pub const MULTI_LINE: EmitFlags = EmitFlags(1 << 1);
    /// `EFNoLeadingSourceMap` — Do not emit a leading source map location for this node.
    pub const NO_LEADING_SOURCE_MAP: EmitFlags = EmitFlags(1 << 2);
    /// `EFNoTrailingSourceMap` — Do not emit a trailing source map location for this node.
    pub const NO_TRAILING_SOURCE_MAP: EmitFlags = EmitFlags(1 << 3);
    /// `EFNoNestedSourceMaps` — Do not emit source map locations for children of this node.
    pub const NO_NESTED_SOURCE_MAPS: EmitFlags = EmitFlags(1 << 4);
    /// `EFNoTokenLeadingSourceMaps` — Do not emit leading source map location for token nodes.
    pub const NO_TOKEN_LEADING_SOURCE_MAPS: EmitFlags = EmitFlags(1 << 5);
    /// `EFNoTokenTrailingSourceMaps` — Do not emit trailing source map location for token nodes.
    pub const NO_TOKEN_TRAILING_SOURCE_MAPS: EmitFlags = EmitFlags(1 << 6);
    /// `EFNoLeadingComments` — Do not emit leading comments for this node.
    pub const NO_LEADING_COMMENTS: EmitFlags = EmitFlags(1 << 7);
    /// `EFNoTrailingComments` — Do not emit trailing comments for this node.
    pub const NO_TRAILING_COMMENTS: EmitFlags = EmitFlags(1 << 8);
    /// `EFNoNestedComments` — Do not emit nested comments for children of this node.
    pub const NO_NESTED_COMMENTS: EmitFlags = EmitFlags(1 << 9);
    /// `EFHelperName` — The Identifier refers to an *unscoped* emit helper (one that is emitted at the top of the file)
    pub const HELPER_NAME: EmitFlags = EmitFlags(1 << 10);
    /// `EFExportName` — Ensure an export prefix is added for an identifier that points to an exported declaration with a local name (see SymbolFlags.ExportHasLocal).
    pub const EXPORT_NAME: EmitFlags = EmitFlags(1 << 11);
    /// `EFLocalName` — Ensure an export prefix is not added for an identifier that points to an exported declaration.
    pub const LOCAL_NAME: EmitFlags = EmitFlags(1 << 12);
    /// `EFIndented` — Adds an explicit extra indentation level for class and function bodies when printing (used to match old emitter).
    pub const INDENTED: EmitFlags = EmitFlags(1 << 13);
    /// `EFNoIndentation` — Do not indent the node.
    pub const NO_INDENTATION: EmitFlags = EmitFlags(1 << 14);
    /// `EFReuseTempVariableScope` — Reuse the existing temp variable scope during emit.
    pub const REUSE_TEMP_VARIABLE_SCOPE: EmitFlags = EmitFlags(1 << 15);
    /// `EFCustomPrologue` — Treat the statement as if it were a prologue directive (NOTE: Prologue directives are *not* transformed).
    pub const CUSTOM_PROLOGUE: EmitFlags = EmitFlags(1 << 16);
    /// `EFNoAsciiEscaping` — When synthesizing nodes that lack an original node or textSourceNode, we want to write the text on the node with ASCII escaping substitutions.
    pub const NO_ASCII_ESCAPING: EmitFlags = EmitFlags(1 << 17);
    /// `EFExternalHelpers` — This source file has external helpers
    pub const EXTERNAL_HELPERS: EmitFlags = EmitFlags(1 << 18);
    /// `EFStartOnNewLine` — Start this node on a new line
    pub const START_ON_NEW_LINE: EmitFlags = EmitFlags(1 << 19);
    /// `EFIndirectCall` — Emit CallExpression as an indirect call: `(0, f)()`
    pub const INDIRECT_CALL: EmitFlags = EmitFlags(1 << 20);
    /// `EFAsyncFunctionBody` — The node was originally an async function body.
    pub const ASYNC_FUNCTION_BODY: EmitFlags = EmitFlags(1 << 21);
    /// `EFNoLexicalArguments` — Do not capture `arguments` for this arrow function.
    pub const NO_LEXICAL_ARGUMENTS: EmitFlags = EmitFlags(1 << 22);
    /// `EFTransformPrivateStaticElements` — Indicates static private elements in a file or class should be transformed regardless of --target.
    pub const TRANSFORM_PRIVATE_STATIC_ELEMENTS: EmitFlags = EmitFlags(1 << 23);
    /// `EFNoLexicalThis` — Do not capture `this` for this node's subtree.
    pub const NO_LEXICAL_THIS: EmitFlags = EmitFlags(1 << 24);

    /// `EFNoSourceMap` — Do not emit a source map location for this node.
    pub const NO_SOURCE_MAP: EmitFlags =
        EmitFlags(Self::NO_LEADING_SOURCE_MAP.0 | Self::NO_TRAILING_SOURCE_MAP.0);
    /// `EFNoTokenSourceMaps` — Do not emit source map locations for tokens of this node.
    pub const NO_TOKEN_SOURCE_MAPS: EmitFlags =
        EmitFlags(Self::NO_TOKEN_LEADING_SOURCE_MAPS.0 | Self::NO_TOKEN_TRAILING_SOURCE_MAPS.0);
    /// `EFNoComments` — Do not emit comments for this node.
    pub const NO_COMMENTS: EmitFlags =
        EmitFlags(Self::NO_LEADING_COMMENTS.0 | Self::NO_TRAILING_COMMENTS.0);

    /// `flags.Has(flags2)` — returns a value indicating whether all flags in
    /// `other` are set on `self`.
    pub fn has(self, other: EmitFlags) -> bool {
        self.0 & other.0 == other.0
    }
}

impl std::ops::BitOr for EmitFlags {
    type Output = EmitFlags;
    fn bitor(self, rhs: EmitFlags) -> EmitFlags {
        EmitFlags(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for EmitFlags {
    fn bitor_assign(&mut self, rhs: EmitFlags) {
        self.0 |= rhs.0;
    }
}

impl std::ops::BitAnd for EmitFlags {
    type Output = EmitFlags;
    fn bitand(self, rhs: EmitFlags) -> EmitFlags {
        EmitFlags(self.0 & rhs.0)
    }
}

impl std::ops::BitAndAssign for EmitFlags {
    fn bitand_assign(&mut self, rhs: EmitFlags) {
        self.0 &= rhs.0;
    }
}

impl std::ops::Not for EmitFlags {
    type Output = EmitFlags;
    fn not(self) -> EmitFlags {
        EmitFlags(!self.0)
    }
}

/// `type GeneratedIdentifierFlags int`
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct GeneratedIdentifierFlags(pub i32);

impl GeneratedIdentifierFlags {
    // Kind

    /// `GeneratedIdentifierFlagsNone` — Not automatically generated.
    pub const NONE: GeneratedIdentifierFlags = GeneratedIdentifierFlags(0);
    /// `GeneratedIdentifierFlagsAuto` — Automatically generated identifier.
    pub const AUTO: GeneratedIdentifierFlags = GeneratedIdentifierFlags(1);
    /// `GeneratedIdentifierFlagsLoop` — Automatically generated identifier with a preference for '_i'.
    pub const LOOP: GeneratedIdentifierFlags = GeneratedIdentifierFlags(2);
    /// `GeneratedIdentifierFlagsUnique` — Unique name based on the 'text' property.
    pub const UNIQUE: GeneratedIdentifierFlags = GeneratedIdentifierFlags(3);
    /// `GeneratedIdentifierFlagsNode` — Unique name based on the node in the 'Node' property.
    pub const NODE: GeneratedIdentifierFlags = GeneratedIdentifierFlags(4);
    /// `GeneratedIdentifierFlagsKindMask` — Mask to extract the kind of identifier from its flags.
    pub const KIND_MASK: GeneratedIdentifierFlags = GeneratedIdentifierFlags(7);

    // Flags

    /// `GeneratedIdentifierFlagsReservedInNestedScopes` — Reserve the generated name in nested scopes
    pub const RESERVED_IN_NESTED_SCOPES: GeneratedIdentifierFlags = GeneratedIdentifierFlags(1 << 3);
    /// `GeneratedIdentifierFlagsOptimistic` — First instance won't use '_#' if there's no conflict
    pub const OPTIMISTIC: GeneratedIdentifierFlags = GeneratedIdentifierFlags(1 << 4);
    /// `GeneratedIdentifierFlagsFileLevel` — Use only the file identifiers list and not generated names to search for conflicts
    pub const FILE_LEVEL: GeneratedIdentifierFlags = GeneratedIdentifierFlags(1 << 5);
    /// `GeneratedIdentifierFlagsAllowNameSubstitution` — Used by `module.ts` to indicate generated nodes which can have substitutions performed upon them.
    pub const ALLOW_NAME_SUBSTITUTION: GeneratedIdentifierFlags = GeneratedIdentifierFlags(1 << 6);

    /// `(f GeneratedIdentifierFlags) Kind()`
    pub fn kind(self) -> GeneratedIdentifierFlags {
        self & Self::KIND_MASK
    }

    /// `(f GeneratedIdentifierFlags) IsAuto()`
    pub fn is_auto(self) -> bool {
        self.kind() == Self::AUTO
    }

    /// `(f GeneratedIdentifierFlags) IsLoop()`
    pub fn is_loop(self) -> bool {
        self.kind() == Self::LOOP
    }

    /// `(f GeneratedIdentifierFlags) IsUnique()`
    pub fn is_unique(self) -> bool {
        self.kind() == Self::UNIQUE
    }

    /// `(f GeneratedIdentifierFlags) IsNode()`
    pub fn is_node(self) -> bool {
        self.kind() == Self::NODE
    }

    /// `(f GeneratedIdentifierFlags) IsReservedInNestedScopes()`
    pub fn is_reserved_in_nested_scopes(self) -> bool {
        self & Self::RESERVED_IN_NESTED_SCOPES != Self::NONE
    }

    /// `(f GeneratedIdentifierFlags) IsOptimistic()`
    pub fn is_optimistic(self) -> bool {
        self & Self::OPTIMISTIC != Self::NONE
    }

    /// `(f GeneratedIdentifierFlags) IsFileLevel()`
    pub fn is_file_level(self) -> bool {
        self & Self::FILE_LEVEL != Self::NONE
    }

    /// `(f GeneratedIdentifierFlags) HasAllowNameSubstitution()`
    pub fn has_allow_name_substitution(self) -> bool {
        self & Self::ALLOW_NAME_SUBSTITUTION != Self::NONE
    }
}

impl std::ops::BitOr for GeneratedIdentifierFlags {
    type Output = GeneratedIdentifierFlags;
    fn bitor(self, rhs: GeneratedIdentifierFlags) -> GeneratedIdentifierFlags {
        GeneratedIdentifierFlags(self.0 | rhs.0)
    }
}

impl std::ops::BitOrAssign for GeneratedIdentifierFlags {
    fn bitor_assign(&mut self, rhs: GeneratedIdentifierFlags) {
        self.0 |= rhs.0;
    }
}

impl std::ops::BitAnd for GeneratedIdentifierFlags {
    type Output = GeneratedIdentifierFlags;
    fn bitand(self, rhs: GeneratedIdentifierFlags) -> GeneratedIdentifierFlags {
        GeneratedIdentifierFlags(self.0 & rhs.0)
    }
}

impl std::ops::BitAndAssign for GeneratedIdentifierFlags {
    fn bitand_assign(&mut self, rhs: GeneratedIdentifierFlags) {
        self.0 &= rhs.0;
    }
}

impl std::ops::Not for GeneratedIdentifierFlags {
    type Output = GeneratedIdentifierFlags;
    fn not(self) -> GeneratedIdentifierFlags {
        GeneratedIdentifierFlags(!self.0)
    }
}
