// Ported from tsc/internal/ast/nodeflags.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// NodeFlags

use crate::flagdef::flag_type;

flag_type! {
    pub struct NodeFlags(pub u32);
}

impl NodeFlags {
    pub const LET: NodeFlags = NodeFlags(1 << 0); // Variable declaration
    pub const CONST: NodeFlags = NodeFlags(1 << 1); // Variable declaration
    pub const USING: NodeFlags = NodeFlags(1 << 2); // Variable declaration
    pub const REPARSED: NodeFlags = NodeFlags(1 << 3); // Node was synthesized during parsing
    pub const SYNTHESIZED: NodeFlags = NodeFlags(1 << 4); // Node was synthesized during transformation
    pub const OPTIONAL_CHAIN: NodeFlags = NodeFlags(1 << 5); // Chained MemberExpression rooted to a pseudo-OptionalExpression
    pub const EXPORT_CONTEXT: NodeFlags = NodeFlags(1 << 6); // Export context (initialized by binding)
    pub const CONTAINS_THIS: NodeFlags = NodeFlags(1 << 7); // Interface contains references to "this"
    pub const HAS_IMPLICIT_RETURN: NodeFlags = NodeFlags(1 << 8); // If function implicitly returns on one of codepaths (initialized by binding)
    pub const HAS_EXPLICIT_RETURN: NodeFlags = NodeFlags(1 << 9); // If function has explicit reachable return on one of codepaths (initialized by binding)
    pub const DISALLOW_IN_CONTEXT: NodeFlags = NodeFlags(1 << 10); // If node was parsed in a context where 'in-expressions' are not allowed
    pub const YIELD_CONTEXT: NodeFlags = NodeFlags(1 << 11); // If node was parsed in the 'yield' context created when parsing a generator
    pub const DECORATOR_CONTEXT: NodeFlags = NodeFlags(1 << 12); // If node was parsed as part of a decorator
    pub const AWAIT_CONTEXT: NodeFlags = NodeFlags(1 << 13); // If node was parsed in the 'await' context created when parsing an async function
    pub const DISALLOW_CONDITIONAL_TYPES_CONTEXT: NodeFlags = NodeFlags(1 << 14); // If node was parsed in a context where conditional types are not allowed
    pub const THIS_NODE_HAS_ERROR: NodeFlags = NodeFlags(1 << 15); // If the parser encountered an error when parsing the code that created this node
    pub const JAVA_SCRIPT_FILE: NodeFlags = NodeFlags(1 << 16); // If node was parsed in a JavaScript
    pub const THIS_NODE_OR_ANY_SUB_NODES_HAS_ERROR: NodeFlags = NodeFlags(1 << 17); // If this node or any of its children had an error
    pub const HAS_ASYNC_FUNCTIONS: NodeFlags = NodeFlags(1 << 18); // If the file has async functions (initialized by binding)

    // NodeFlagsHasAggregatedChildData is deprecated. Use `subtreeFacts` instead.

    // These flags will be set when the parser encounters a dynamic import expression or 'import.meta' to avoid
    // walking the tree if the flags are not set. However, these flags are just a approximation
    // (hence why it's named "PossiblyContainsDynamicImport") because once set, the flags never get cleared.
    // During editing, if a dynamic import is removed, incremental parsing will *NOT* clear this flag.
    // This means that the tree will always be traversed during module resolution, or when looking for external module indicators.
    // However, the removal operation should not occur often and in the case of the
    // removal, it is likely that users will add the import anyway.
    // The advantage of this approach is its simplicity. For the case of batch compilation,
    // we guarantee that users won't have to pay the price of walking the tree if a dynamic import isn't used.
    pub const POSSIBLY_CONTAINS_DYNAMIC_IMPORT: NodeFlags = NodeFlags(1 << 19);
    pub const POSSIBLY_CONTAINS_IMPORT_META: NodeFlags = NodeFlags(1 << 20);

    pub const HAS_JSDOC: NodeFlags = NodeFlags(1 << 21); // If node has preceding JSDoc comment(s)
    pub const JSDOC: NodeFlags = NodeFlags(1 << 22); // If node was parsed inside jsdoc
    pub const AMBIENT: NodeFlags = NodeFlags(1 << 23); // If node was inside an ambient context -- a declaration file, or inside something with the `declare` modifier.
    pub const IN_WITH_STATEMENT: NodeFlags = NodeFlags(1 << 24); // If any ancestor of node was the `statement` of a WithStatement (not the `expression`)
    pub const JSON_FILE: NodeFlags = NodeFlags(1 << 25); // If node was parsed in a Json
    pub const POSSIBLY_CONTAINS_DEPRECATED_TAG: NodeFlags = NodeFlags(1 << 26); // Set during parse if comment text contains '@deprecated'; must confirm via JSDoc lookup
    pub const UNREACHABLE: NodeFlags = NodeFlags(1 << 27); // If node is unreachable according to the binder
    pub const REPARSER_TRANSFORMED_LITERAL: NodeFlags = NodeFlags(1 << 28); // If node was transformed during parsing, making its' naive text source not match the AST

    pub const BLOCK_SCOPED: NodeFlags = NodeFlags(Self::LET.0 | Self::CONST.0 | Self::USING.0);
    pub const CONSTANT: NodeFlags = NodeFlags(Self::CONST.0 | Self::USING.0);
    /// Variable declaration (NOTE: on a single node these flags would otherwise be mutually exclusive)
    pub const AWAIT_USING: NodeFlags = NodeFlags(Self::CONST.0 | Self::USING.0);

    pub const REACHABILITY_CHECK_FLAGS: NodeFlags =
        NodeFlags(Self::HAS_IMPLICIT_RETURN.0 | Self::HAS_EXPLICIT_RETURN.0);
    pub const REACHABILITY_AND_EMIT_FLAGS: NodeFlags =
        NodeFlags(Self::REACHABILITY_CHECK_FLAGS.0 | Self::HAS_ASYNC_FUNCTIONS.0);

    /// Parsing context flags
    pub const CONTEXT_FLAGS: NodeFlags = NodeFlags(
        Self::DISALLOW_IN_CONTEXT.0
            | Self::DISALLOW_CONDITIONAL_TYPES_CONTEXT.0
            | Self::YIELD_CONTEXT.0
            | Self::DECORATOR_CONTEXT.0
            | Self::AWAIT_CONTEXT.0
            | Self::JAVA_SCRIPT_FILE.0
            | Self::IN_WITH_STATEMENT.0
            | Self::AMBIENT.0,
    );

    /// Exclude these flags when parsing a Type
    pub const TYPE_EXCLUDES_FLAGS: NodeFlags = NodeFlags(Self::YIELD_CONTEXT.0 | Self::AWAIT_CONTEXT.0);

    /// Represents all flags that are potentially set once and
    /// never cleared on SourceFiles which get re-used in between incremental parses.
    /// See the comment above on `PossiblyContainsDynamicImport` and `PossiblyContainsImportMeta`.
    pub const PERMANENTLY_SET_INCREMENTAL_FLAGS: NodeFlags =
        NodeFlags(Self::POSSIBLY_CONTAINS_DYNAMIC_IMPORT.0 | Self::POSSIBLY_CONTAINS_IMPORT_META.0);

    // The following flags repurpose other NodeFlags as different meanings for Identifier nodes
    /// Indicates whether the identifier contains an extended unicode escape sequence
    pub const IDENTIFIER_HAS_EXTENDED_UNICODE_ESCAPE: NodeFlags = Self::CONTAINS_THIS;
    /// Indicates the identifier is the innermost name of a JSDoc namespace declaration
    pub const IDENTIFIER_IS_IN_JSDOC_NAMESPACE: NodeFlags = Self::HAS_ASYNC_FUNCTIONS;

    /// The following flag repurposes other NodeFlags for ModuleDeclaration nodes
    /// If ModuleDeclaration is a nested namespace (e.g. inner part of A.B.C)
    pub const NESTED_NAMESPACE: NodeFlags = Self::OPTIONAL_CHAIN;
}
