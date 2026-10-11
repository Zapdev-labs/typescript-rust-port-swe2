// Ported from tsc/internal/ls/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::Cell;

use tsc_ast::ast::{CommentRange, FileReference, Node, NodeFactory, NodeFactoryHooks, NodeList};
use tsc_ast::kind_generated::Kind;
use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{
    self as ast, ModifierFlags, NodeFlags, NodeId, SymbolFlags, SymbolId, outer_expression_kinds,
};
use tsc_checker::checker_core::Checker;
use tsc_checker::types::{ContextFlags, SignatureId, SignatureKind, TypeId};
use tsc_collections::Set;
use tsc_compiler::program::Program;
use tsc_core::text::{TextPos, TextRange};
use tsc_debug as debug;
use tsc_lsconv::converters::{Script, source_file_script};
use tsc_lsproto::{Position, Range};
use tsc_lsutil::userpreferences::QuotePreference;
use tsc_lsutil::userpreferences_generated::UserPreferences;
use tsc_lsutil::utilities::get_quote_preference;
use tsc_scanner::scanner::{Scanner, get_token_pos_of_node, token_to_string};
use tsc_spanmap::{Feature, Fidelity};
use tsc_tspath::{self as tspath, RootedFilePath};

use crate::languageservice::LanguageService;

/// `quoteReplacer` — `strings.NewReplacer("'", `\'`, `\"`, `"`)`.
fn quote_replacer(text: &str) -> String {
    // Go's Replacer matches left-to-right with no overlaps; the two patterns
    // are disjoint, so sequential replaces are equivalent.
    text.replace('\'', "\\'").replace("\\\"", "\"")
}

/// `IsInString`.
pub fn is_in_string(
    nodes: &mut Vec<Node>,
    source_file: NodeId,
    position: TextPos,
    previous_token: Option<NodeId>,
) -> bool {
    if let Some(previous_token) = previous_token {
        if ast::is_string_text_containing_node(&nodes[previous_token]) {
            let start = tsc_astnav::tokens::get_start_of_node(
                nodes,
                source_file,
                previous_token,
                false, /*includeJSDoc*/
            );
            let end = nodes[previous_token].end();

            // To be "in" one of these literals, the position has to be:
            //   1. entirely within the token text.
            //   2. at the end position of an unterminated token.
            //   3. at the end of a regular expression (due to trailing flags like '/foo/g').
            if start < position && position < end {
                return true;
            }

            if position == end {
                return ast::is_unterminated_literal(&nodes[previous_token]);
            }
        }
    }
    false
}

/// `isModuleSpecifierLike`.
pub(crate) fn is_module_specifier_like(node: NodeId, nodes: &[Node]) -> bool {
    if !ast::is_string_literal_like(&nodes[node]) {
        return false;
    }

    let parent = nodes[node].parent;
    if let Some(parent) = parent {
        if ast::is_require_call(
            &nodes[parent],
            false, /*requireStringLiteralLikeArgument*/
            nodes,
        ) || ast::is_import_call(&nodes[parent], nodes)
        {
            return nodes[parent].arguments().is_some_and(|a| a[0] == node);
        }
    }

    nodes[node].parent.is_some_and(|p| {
        nodes[p].kind == Kind::ExternalModuleReference
            || nodes[p].kind == Kind::ImportDeclaration
            || nodes[p].kind == Kind::JSImportDeclaration
    })
}

/// `getNonModuleSymbolOfMergedModuleSymbol`.
pub(crate) fn get_non_module_symbol_of_merged_module_symbol(
    program: &Program,
    symbol: SymbolId,
) -> Option<SymbolId> {
    let (declarations, flags) = {
        let symbols = program.symbols.borrow();
        let s = &symbols[symbol.index()];
        (s.declarations.clone(), s.flags)
    };
    if declarations.is_empty() || !flags.intersects(SymbolFlags::MODULE | SymbolFlags::TRANSIENT) {
        return None;
    }

    if let Some(decl) = declarations.iter().copied().find(|&d| {
        let nodes = program.nodes(d.file_index());
        !ast::is_source_file(&nodes[d]) && !ast::is_module_declaration(&nodes[d])
    }) {
        let nodes = program.nodes(decl.file_index());
        return nodes[decl].symbol();
    }
    None
}

/// `getLocalSymbolForExportSpecifier` — `exportSpecifier` is the
/// `*ast.ExportSpecifier` node id.
pub(crate) fn get_local_symbol_for_export_specifier(
    nodes: &[Node],
    reference_location: NodeId,
    reference_symbol: Option<SymbolId>,
    export_specifier: NodeId,
    ch: &mut Checker,
) -> Option<SymbolId> {
    if is_export_specifier_alias(nodes, reference_location, export_specifier) {
        if let Some(symbol) = ch.get_export_specifier_local_target_symbol(export_specifier) {
            return Some(symbol);
        }
    }
    reference_symbol
}

/// `isExportSpecifierAlias` — `exportSpecifier` is the specifier's `NodeId`.
pub(crate) fn is_export_specifier_alias(
    nodes: &[Node],
    reference_location: NodeId,
    export_specifier: NodeId,
) -> bool {
    let export_specifier_data = nodes[export_specifier].as_export_specifier();
    debug::assert_!(
        export_specifier_data.property_name == Some(reference_location)
            || nodes[export_specifier].name() == Some(reference_location),
        "referenceLocation is not export specifier name or property name",
    );
    if let Some(property_name) = export_specifier_data.property_name {
        // Given `export { foo as bar } [from "someModule"]`: It's an alias at `foo`, but at `bar` it's a new symbol.
        property_name == reference_location
    } else {
        // `export { foo } from "foo"` is a re-export.
        // `export { foo };` is not a re-export, it creates an alias for the local variable `foo`.
        nodes[export_specifier]
            .parent
            .and_then(|p| nodes[p].parent)
            .is_none_or(|d| nodes[d].module_specifier().is_none())
    }
}

/// `isInComment`.
pub(crate) fn is_in_comment(
    nodes: &mut Vec<Node>,
    file: NodeId,
    position: TextPos,
    token_at_position: Option<NodeId>,
) -> Option<CommentRange> {
    // PORT(sibling): `get_range_of_enclosing_comment` is ported in the
    // sibling-owned `format.rs` (Go `tsc/internal/ls/format.go`).
    let preceding_token = tsc_astnav::tokens::find_preceding_token(nodes, file, position);
    crate::format::get_range_of_enclosing_comment(
        nodes,
        file,
        position,
        preceding_token,
        token_at_position,
    )
}

/// `positionBelongsToNode`.
pub(crate) fn position_belongs_to_node(
    nodes: &mut Vec<Node>,
    candidate: NodeId,
    position: TextPos,
    file: NodeId,
) -> bool {
    tsc_lsutil::completednode::position_belongs_to_node(nodes, candidate, position, file)
}

/// `PossibleTypeArgumentInfo`.
pub(crate) struct PossibleTypeArgumentInfo {
    /// `called` — `*ast.IdentifierNode`.
    pub(crate) called: NodeId,
    /// `nTypeArguments`.
    pub(crate) n_type_arguments: i32,
}

// Get info for an expression like `f <` that may be the start of type arguments.
/// `getPossibleTypeArgumentsInfo`.
pub(crate) fn get_possible_type_arguments_info(
    nodes: &mut Vec<Node>,
    token_in: NodeId,
    source_file: NodeId,
) -> Option<PossibleTypeArgumentInfo> {
    // This is a rare case, but one that saves on a _lot_ of work if true - if the source file has _no_ `<` character,
    // then there obviously can't be any type arguments - no expensive brace-matching backwards scanning required
    if !nodes[source_file].as_source_file().text().contains('<') {
        return None;
    }

    let mut token = Some(token_in);
    // This function determines if the node could be a type argument position
    // When editing, it is common to have an incomplete type argument list (e.g. missing ">"),
    // so the tree can have any shape depending on the tokens before the current node.
    // Instead, scanning for an identifier followed by a "<" before current node
    // will typically give us better results than inspecting the tree.
    // Note that we also balance out the already provided type arguments, arrays, object literals while doing so.
    let mut remaining_less_than_tokens = 0i32;
    let mut n_type_arguments = 0i32;
    while let Some(t) = token {
        match nodes[t].kind {
            Kind::LessThanToken => {
                // Found the beginning of the generic argument expression
                token =
                    tsc_astnav::tokens::find_preceding_token(nodes, source_file, nodes[t].pos());
                if token.is_some_and(|tk| nodes[tk].kind == Kind::QuestionDotToken) {
                    token = tsc_astnav::tokens::find_preceding_token(
                        nodes,
                        source_file,
                        nodes[token.unwrap()].pos(),
                    );
                }
                let Some(tk) = token else {
                    return None;
                };
                if !ast::is_identifier(&nodes[tk]) {
                    return None;
                }
                if remaining_less_than_tokens == 0 {
                    if ast::is_declaration_name(tk, nodes) {
                        return None;
                    }
                    return Some(PossibleTypeArgumentInfo {
                        called: tk,
                        n_type_arguments,
                    });
                }
                remaining_less_than_tokens -= 1;
            }
            Kind::GreaterThanGreaterThanGreaterThanToken => {
                remaining_less_than_tokens += 3;
            }
            Kind::GreaterThanGreaterThanToken => {
                remaining_less_than_tokens += 2;
            }
            Kind::GreaterThanToken => {
                remaining_less_than_tokens += 1;
            }
            Kind::CloseBraceToken => {
                // This can be object type, skip until we find the matching open brace token
                // Skip until the matching open brace token
                token = find_preceding_matching_token(nodes, t, Kind::OpenBraceToken, source_file);
                if token.is_none() {
                    return None;
                }
            }
            Kind::CloseParenToken => {
                // This can be object type, skip until we find the matching open brace token
                // Skip until the matching open brace token
                token = find_preceding_matching_token(nodes, t, Kind::OpenParenToken, source_file);
                if token.is_none() {
                    return None;
                }
            }
            Kind::CloseBracketToken => {
                // This can be object type, skip until we find the matching open brace token
                // Skip until the matching open brace token
                token =
                    find_preceding_matching_token(nodes, t, Kind::OpenBracketToken, source_file);
                if token.is_none() {
                    return None;
                }
            }
            Kind::CommaToken => {
                // Valid tokens in a type name. Skip.
                n_type_arguments += 1;
            }
            Kind::EqualsGreaterThanToken
            | Kind::Identifier
            | Kind::StringLiteral
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::TrueKeyword
            | Kind::FalseKeyword
            | Kind::TypeOfKeyword
            | Kind::ExtendsKeyword
            | Kind::KeyOfKeyword
            | Kind::DotToken
            | Kind::BarToken
            | Kind::QuestionToken
            | Kind::ColonToken => {
                // do nothing
            }
            _ => {
                if !ast::is_type_node(&nodes[t]) {
                    // Invalid token in type
                    return None;
                }
            }
        }
        token = tsc_astnav::tokens::find_preceding_token(
            nodes,
            source_file,
            nodes[token.unwrap()].pos(),
        );
    }
    None
}

/// `isNameOfModuleDeclaration`.
pub(crate) fn is_name_of_module_declaration(node: NodeId, nodes: &[Node]) -> bool {
    if nodes[node].parent.map(|p| nodes[p].kind) != Some(Kind::ModuleDeclaration) {
        return false;
    }
    nodes[node]
        .parent
        .is_some_and(|p| nodes[p].name() == Some(node))
}

/// `isExpressionOfExternalModuleImportEqualsDeclaration`.
pub(crate) fn is_expression_of_external_module_import_equals_declaration(
    node: NodeId,
    nodes: &[Node],
) -> bool {
    let grandparent = nodes[node].parent.and_then(|p| nodes[p].parent);
    grandparent.is_some_and(|gp| {
        ast::is_external_module_import_equals_declaration(&nodes[gp], nodes)
            && ast::get_external_module_import_equals_declaration_expression(&nodes[gp], nodes)
                == Some(node)
    })
}

/// `isNamespaceReference`.
pub(crate) fn is_namespace_reference(node: NodeId, nodes: &[Node]) -> bool {
    is_qualified_name_namespace_reference(node, nodes)
        || is_property_access_namespace_reference(node, nodes)
}

/// `isQualifiedNameNamespaceReference`.
fn is_qualified_name_namespace_reference(node: NodeId, nodes: &[Node]) -> bool {
    let mut root = node;
    let mut is_last_clause = true;
    if nodes[root]
        .parent
        .is_some_and(|p| nodes[p].kind == Kind::QualifiedName)
    {
        while let Some(parent) = nodes[root].parent
            && nodes[parent].kind == Kind::QualifiedName
        {
            root = parent;
        }

        is_last_clause = nodes[root].as_qualified_name().right == Some(node);
    }

    nodes[root]
        .parent
        .is_some_and(|p| nodes[p].kind == Kind::TypeReference)
        && !is_last_clause
}

/// `isPropertyAccessNamespaceReference`.
fn is_property_access_namespace_reference(node: NodeId, nodes: &[Node]) -> bool {
    let mut root = node;
    let mut is_last_clause = true;
    if nodes[root]
        .parent
        .is_some_and(|p| nodes[p].kind == Kind::PropertyAccessExpression)
    {
        while let Some(parent) = nodes[root].parent
            && nodes[parent].kind == Kind::PropertyAccessExpression
        {
            root = parent;
        }

        is_last_clause = nodes[root].name() == Some(node);
    }

    let Some(root_parent) = nodes[root].parent else {
        return false;
    };
    if !is_last_clause
        && nodes[root_parent].kind == Kind::ExpressionWithTypeArguments
        && nodes[root_parent]
            .parent
            .is_some_and(|gp| nodes[gp].kind == Kind::HeritageClause)
    {
        let decl = nodes[root_parent].parent.and_then(|gp| nodes[gp].parent);
        let Some(decl) = decl else {
            return false;
        };
        return (nodes[decl].kind == Kind::ClassDeclaration
            && nodes[root_parent].as_heritage_clause().token == Kind::ImplementsKeyword)
            || (nodes[decl].kind == Kind::InterfaceDeclaration
                && nodes[root_parent].as_heritage_clause().token == Kind::ExtendsKeyword);
    }

    false
}

/// `isThis`.
pub(crate) fn is_this(node: NodeId, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::ThisKeyword =>
        // case ast.KindThisType: TODO: GH#9267
        {
            true
        }
        Kind::Identifier => {
            // 'this' as a parameter
            nodes[node].text(nodes).as_ref() == "this"
                && nodes[node]
                    .parent
                    .is_some_and(|p| nodes[p].kind == Kind::Parameter)
        }
        _ => false,
    }
}

/// `isTypeReference`.
pub(crate) fn is_type_reference(node: NodeId, nodes: &[Node]) -> bool {
    let mut node = node;
    if ast::is_right_side_of_qualified_name_or_property_access(node, nodes) {
        node = nodes[node].parent.expect("parent");
    }

    match nodes[node].kind {
        Kind::ThisKeyword => return !ast::is_expression_node(node, nodes),
        Kind::ThisType => return true,
        _ => {}
    }

    match nodes[node].parent.map(|p| nodes[p].kind) {
        Some(Kind::TypeReference) => true,
        Some(Kind::ImportType) => {
            !nodes[nodes[node].parent.unwrap()]
                .as_import_type_node()
                .is_type_of
        }
        Some(Kind::ExpressionWithTypeArguments) => {
            ast::is_part_of_type_node(nodes[node].parent.unwrap(), nodes)
        }
        _ => false,
    }
}

/// `isInRightSideOfInternalImportEqualsDeclaration`.
pub(crate) fn is_in_right_side_of_internal_import_equals_declaration(
    node: NodeId,
    nodes: &[Node],
) -> bool {
    if nodes[node].parent.is_none() {
        return false;
    }
    let mut node = node;
    while nodes[node]
        .parent
        .is_some_and(|p| nodes[p].kind == Kind::QualifiedName)
    {
        node = nodes[node].parent.unwrap();
    }

    nodes[node].parent.is_some_and(|p| {
        ast::is_internal_module_import_equals_declaration(&nodes[p], nodes)
            && nodes[p].as_import_equals_declaration().module_reference == Some(node)
    })
}

impl LanguageService<'_> {
    /// `createLspRangeFromNode`.
    pub(crate) fn create_lsp_range_from_node(
        &self,
        node: NodeId,
        file: NodeId,
    ) -> (Range, Fidelity) {
        let (start, end) = {
            let nodes = self.program.nodes(file.file_index());
            (
                get_token_pos_of_node(
                    node,
                    nodes[file].as_source_file(),
                    false, /*includeJSDoc*/
                    &nodes,
                ),
                nodes[node].end(),
            )
        };
        self.create_lsp_range_from_bounds(start, end, file)
    }

    /// `createLspRangeFromNodeForFeature`.
    pub(crate) fn create_lsp_range_from_node_for_feature(
        &self,
        node: NodeId,
        file: NodeId,
        feature: Feature,
    ) -> (Range, Fidelity) {
        let nodes = self.program.nodes(file.file_index());
        let script = source_file_script(file, &nodes);
        self.converters.to_lsp_range_for_feature(
            &script,
            create_range_from_node(node, file, &nodes),
            feature,
        )
    }

    /// `createLspRangeFromBounds`.
    pub(crate) fn create_lsp_range_from_bounds(
        &self,
        start: TextPos,
        end: TextPos,
        file: NodeId,
    ) -> (Range, Fidelity) {
        let nodes = self.program.nodes(file.file_index());
        let script = source_file_script(file, &nodes);
        self.converters
            .to_lsp_range(&script, TextRange::new(start, end))
    }

    /// `createLspRangeFromRange`.
    pub(crate) fn create_lsp_range_from_range(
        &self,
        text_range: TextRange,
        script: &dyn Script,
    ) -> (Range, Fidelity) {
        self.converters.to_lsp_range(script, text_range)
    }

    /// `createLspPosition`.
    pub(crate) fn create_lsp_position(
        &self,
        position: TextPos,
        file: NodeId,
    ) -> (Position, Fidelity) {
        let nodes = self.program.nodes(file.file_index());
        let script = source_file_script(file, &nodes);
        self.converters.to_lsp_position(&script, position)
    }
}

/// `createRangeFromNode`.
pub(crate) fn create_range_from_node(node: NodeId, file: NodeId, nodes: &[Node]) -> TextRange {
    TextRange::new(
        get_token_pos_of_node(
            node,
            nodes[file].as_source_file(),
            false, /*includeJSDoc*/
            nodes,
        ),
        nodes[node].end(),
    )
}

/// `quote`.
pub(crate) fn quote(
    nodes: &[Node],
    file: NodeId,
    preferences: &UserPreferences,
    text: &str,
) -> String {
    // Editors can pass in undefined or empty string - we want to infer the preference in those cases.
    let quote_preference = get_quote_preference(nodes, file, preferences);
    let mut quoted = tsc_core::core::stringify_json(text, "" /*prefix*/, "" /*indent*/)
        .unwrap_or_else(|_| text.to_string());
    if quote_preference == QuotePreference::SINGLE {
        quoted = format!(
            "'{}'",
            quote_replacer(
                std::str::from_utf8(tsc_stringutil::strip_quotes(quoted.as_bytes()))
                    .unwrap_or_default()
            )
        );
    }
    quoted
}

/// `typeKeywords` — `collections.NewSetFromItems(...)`.
fn type_keywords() -> &'static Set<Kind> {
    static TYPE_KEYWORDS: std::sync::OnceLock<Set<Kind>> = std::sync::OnceLock::new();
    TYPE_KEYWORDS.get_or_init(|| {
        tsc_collections::new_set_from_items([
            Kind::AnyKeyword,
            Kind::AssertsKeyword,
            Kind::BigIntKeyword,
            Kind::BooleanKeyword,
            Kind::FalseKeyword,
            Kind::InferKeyword,
            Kind::KeyOfKeyword,
            Kind::NeverKeyword,
            Kind::NullKeyword,
            Kind::NumberKeyword,
            Kind::ObjectKeyword,
            Kind::ReadonlyKeyword,
            Kind::StringKeyword,
            Kind::SymbolKeyword,
            Kind::TypeOfKeyword,
            Kind::TrueKeyword,
            Kind::VoidKeyword,
            Kind::UndefinedKeyword,
            Kind::UniqueKeyword,
            Kind::UnknownKeyword,
        ])
    })
}

/// `isTypeKeyword`.
pub(crate) fn is_type_keyword(kind: Kind) -> bool {
    type_keywords().has(&kind)
}

/// `isSeparator`.
pub(crate) fn is_separator(node: NodeId, candidate: Option<NodeId>, nodes: &[Node]) -> bool {
    candidate.is_some_and(|c| {
        nodes[node].parent.is_some()
            && (nodes[c].kind == Kind::CommaToken
                || (nodes[c].kind == Kind::SemicolonToken
                    && nodes[node]
                        .parent
                        .is_some_and(|p| nodes[p].kind == Kind::ObjectLiteralExpression)))
    })
}

/// `isLiteralNameOfPropertyDeclarationOrIndexAccess`.
pub(crate) fn is_literal_name_of_property_declaration_or_index_access(
    node: NodeId,
    nodes: &[Node],
) -> bool {
    // utilities
    match nodes[node].parent.map(|p| nodes[p].kind) {
        Some(
            Kind::PropertyDeclaration
            | Kind::PropertySignature
            | Kind::PropertyAssignment
            | Kind::EnumMember
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::ModuleDeclaration,
        ) => ast::get_name_of_declaration(nodes[node].parent, nodes) == Some(node),
        Some(Kind::ElementAccessExpression) => {
            let parent = nodes[node].parent.unwrap();
            nodes[parent]
                .as_element_access_expression()
                .argument_expression
                == Some(node)
        }
        Some(Kind::ComputedPropertyName) => true,
        Some(Kind::LiteralType) => nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .is_some_and(|gp| nodes[gp].kind == Kind::IndexedAccessType),
        _ => false,
    }
}

/// `isObjectBindingElementWithoutPropertyName`.
pub(crate) fn is_object_binding_element_without_property_name(
    binding_element: NodeId,
    nodes: &[Node],
) -> bool {
    nodes[binding_element].kind == Kind::BindingElement
        && nodes[binding_element]
            .parent
            .is_some_and(|p| nodes[p].kind == Kind::ObjectBindingPattern)
        && nodes[binding_element]
            .name()
            .is_some_and(|n| nodes[n].kind == Kind::Identifier)
        && nodes[binding_element].property_name().is_none()
}

/// `isRightSideOfPropertyAccess`.
pub(crate) fn is_right_side_of_property_access(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].parent.is_some_and(|p| {
        nodes[p].kind == Kind::PropertyAccessExpression && nodes[p].name() == Some(node)
    })
}

/// `isStaticSymbol`.
pub(crate) fn is_static_symbol(program: &Program, symbol: SymbolId) -> bool {
    let value_declaration = program.symbols.borrow()[symbol.index()].value_declaration;
    let Some(value_declaration) = value_declaration else {
        return false;
    };
    let nodes = program.nodes(value_declaration.file_index());
    let modifier_flags = nodes[value_declaration].modifier_flags();
    modifier_flags & ModifierFlags::STATIC != ModifierFlags::NONE
}

/// `isImplementation`.
pub(crate) fn is_implementation(node: NodeId, nodes: &[Node]) -> bool {
    if nodes[node].flags & NodeFlags::AMBIENT != NodeFlags::NONE {
        return !(nodes[node].kind == Kind::InterfaceDeclaration
            || nodes[node].kind == Kind::TypeAliasDeclaration);
    }
    if ast::is_variable_like(&nodes[node]) {
        return ast::has_initializer(&nodes[node]);
    }
    if ast::is_function_like_declaration(Some(node), nodes) {
        return nodes[node].body().is_some();
    }
    ast::is_class_like(Some(node), nodes) || ast::is_module_or_enum_declaration(&nodes[node])
}

/// `isImplementationExpression`.
pub(crate) fn is_implementation_expression(node: NodeId, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::ParenthesizedExpression => nodes[node]
            .expression()
            .is_some_and(|e| is_implementation_expression(e, nodes)),
        Kind::ArrowFunction
        | Kind::FunctionExpression
        | Kind::ObjectLiteralExpression
        | Kind::ClassExpression
        | Kind::ArrayLiteralExpression => true,
        _ => false,
    }
}

/// `isReadonlyTypeOperator`.
pub(crate) fn is_readonly_type_operator(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].kind == Kind::ReadonlyKeyword
        && nodes[node]
            .parent
            .is_some_and(|p| nodes[p].kind == Kind::TypeOperator)
        && nodes[node]
            .parent
            .is_some_and(|p| nodes[p].as_type_operator_node().operator == Kind::ReadonlyKeyword)
}

/// `isJumpStatementTarget`.
pub(crate) fn is_jump_statement_target(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].kind == Kind::Identifier
        && nodes[node]
            .parent
            .is_some_and(|p| ast::is_break_or_continue_statement(&nodes[p]))
        && nodes[node]
            .parent
            .is_some_and(|p| nodes[p].label() == Some(node))
}

/// `isLabelOfLabeledStatement`.
pub(crate) fn is_label_of_labeled_statement(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].kind == Kind::Identifier
        && nodes[node]
            .parent
            .is_some_and(|p| nodes[p].kind == Kind::LabeledStatement)
        && nodes[node]
            .parent
            .is_some_and(|p| nodes[p].label() == Some(node))
}

/// `findReferenceInPosition`.
pub(crate) fn find_reference_in_position(
    refs: &[FileReference],
    pos: TextPos,
) -> Option<FileReference> {
    refs.iter()
        .find(|r| r.text_range.contains_inclusive(pos))
        .cloned()
}

/// `getContainingNodeIfInHeritageClause`.
pub(crate) fn get_containing_node_if_in_heritage_clause(
    node: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    if nodes[node].kind == Kind::Identifier
        || nodes[node].kind == Kind::QualifiedName
        || nodes[node].kind == Kind::PropertyAccessExpression
    {
        return nodes[node]
            .parent
            .and_then(|p| get_containing_node_if_in_heritage_clause(p, nodes));
    }
    if (nodes[node].kind == Kind::ExpressionWithTypeArguments
        || nodes[node].kind == Kind::TypeReference)
        && nodes[node]
            .parent
            .is_some_and(|p| ast::is_heritage_clause(&nodes[p]))
        && nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .is_some_and(|gp| {
                ast::is_class_like(Some(gp), nodes) || nodes[gp].kind == Kind::InterfaceDeclaration
            })
    {
        return nodes[node].parent.and_then(|p| nodes[p].parent);
    }
    None
}

/// `getContainerNode`.
pub(crate) fn get_container_node(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let mut parent = nodes[node].parent;
    while let Some(p) = parent {
        match nodes[p].kind {
            Kind::SourceFile
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::FunctionDeclaration
            | Kind::FunctionExpression
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::ClassDeclaration
            | Kind::InterfaceDeclaration
            | Kind::EnumDeclaration
            | Kind::ModuleDeclaration => return Some(p),
            _ => {}
        }
        parent = nodes[p].parent;
    }
    None
}

/// `getAdjustedLocation` — `sourceFile` is nil-able in Go (`Option<NodeId>`).
pub(crate) fn get_adjusted_location(
    nodes: &mut Vec<Node>,
    node: NodeId,
    for_rename: bool,
    source_file: Option<NodeId>,
) -> Option<NodeId> {
    // todo: check if this function needs to be changed for jsdoc updates

    let parent = nodes[node].parent;
    // /**/<modifier> [|name|] ...
    // /**/<modifier> <class|interface|type|enum|module|namespace|function|get|set> [|name|] ...
    // /**/<class|interface|type|enum|module|namespace|function|get|set> [|name|] ...
    // /**/import [|name|] = ...
    //
    // NOTE: If the node is a modifier, we don't adjust its location if it is the `default` modifier as that is handled
    // specially by `getSymbolAtLocation`.
    let is_modifier = |nodes: &[Node], node: NodeId| -> bool {
        let Some(parent) = parent else {
            return false;
        };
        if ast::is_modifier(&nodes[node])
            && (for_rename || nodes[node].kind != Kind::DefaultKeyword)
        {
            return ast::can_have_modifiers(&nodes[parent])
                && nodes[parent]
                    .modifier_nodes()
                    .is_some_and(|m| m.contains(&node));
        }
        match nodes[node].kind {
            Kind::ClassKeyword => {
                ast::is_class_declaration(&nodes[parent]) || ast::is_class_expression(&nodes[node])
            }
            Kind::FunctionKeyword => {
                ast::is_function_declaration(&nodes[parent])
                    || ast::is_function_expression(&nodes[node])
            }
            Kind::InterfaceKeyword => ast::is_interface_declaration(&nodes[parent]),
            Kind::EnumKeyword => ast::is_enum_declaration(&nodes[parent]),
            Kind::TypeKeyword => ast::is_type_alias_declaration(&nodes[parent]),
            Kind::NamespaceKeyword | Kind::ModuleKeyword => {
                ast::is_module_declaration(&nodes[parent])
            }
            Kind::ImportKeyword => ast::is_import_equals_declaration(&nodes[parent]),
            Kind::GetKeyword => ast::is_get_accessor_declaration(&nodes[parent]),
            Kind::SetKeyword => ast::is_set_accessor_declaration(&nodes[parent]),
            _ => false,
        }
    };
    if is_modifier(nodes, node) {
        let source_file = source_file.or_else(|| ast::get_source_file_of_node(Some(node), nodes));
        if let Some(location) = get_adjusted_location_for_declaration(
            nodes,
            parent.expect("parent"),
            for_rename,
            source_file,
        ) {
            return Some(location);
        }
    }

    let Some(parent) = parent else {
        return Some(node);
    };

    // /**/<var|let|const> [|name|] ...
    if (nodes[node].kind == Kind::VarKeyword
        || nodes[node].kind == Kind::ConstKeyword
        || nodes[node].kind == Kind::LetKeyword)
        && ast::is_variable_declaration_list(&nodes[parent])
        && nodes[parent]
            .as_variable_declaration_list()
            .declarations
            .as_ref()
            .is_some_and(|d| d.nodes().len() == 1)
    {
        let declaration = nodes[parent]
            .as_variable_declaration_list()
            .declarations
            .as_ref()
            .unwrap()
            .nodes()[0];
        let declaration_name = nodes[declaration].as_variable_declaration().name;
        if let Some(name) = declaration_name
            && ast::is_identifier(&nodes[name])
        {
            return Some(name);
        }
    }

    if nodes[node].kind == Kind::TypeKeyword {
        // import /**/type [|name|] from ...;
        // import /**/type { [|name|] } from ...;
        // import /**/type { propertyName as [|name|] } from ...;
        // import /**/type ... from "[|module|]";
        if ast::is_import_clause(&nodes[parent]) && nodes[parent].is_type_only() {
            if let Some(location) = get_adjusted_location_for_import_declaration(
                nodes,
                nodes[parent].parent.expect("parent"),
                for_rename,
            ) {
                return Some(location);
            }
        }
        // export /**/type { [|name|] } from ...;
        // export /**/type { propertyName as [|name|] } from ...;
        // export /**/type * from "[|module|]";
        // export /**/type * as ... from "[|module|]";
        if ast::is_export_declaration(&nodes[parent]) && nodes[parent].is_type_only() {
            if let Some(location) =
                get_adjusted_location_for_export_declaration(nodes, parent, for_rename)
            {
                return Some(location);
            }
        }
    }

    // import { propertyName /**/as [|name|] } ...
    // import * /**/as [|name|] ...
    // export { propertyName /**/as [|name|] } ...
    // export * /**/as [|name|] ...
    if nodes[node].kind == Kind::AsKeyword {
        if (nodes[parent].kind == Kind::ImportSpecifier && nodes[parent].property_name().is_some())
            || (nodes[parent].kind == Kind::ExportSpecifier
                && nodes[parent].property_name().is_some())
            || nodes[parent].kind == Kind::NamespaceImport
            || nodes[parent].kind == Kind::NamespaceExport
        {
            return nodes[parent].name();
        }
        if nodes[parent].kind == Kind::ExportDeclaration {
            if let Some(export_clause) = nodes[parent].as_export_declaration().export_clause {
                if nodes[export_clause].kind == Kind::NamespaceExport {
                    return nodes[export_clause].name();
                }
            }
        }
    }

    // /**/import [|name|] from ...;
    // /**/import { [|name|] } from ...;
    // /**/import { propertyName as [|name|] } from ...;
    // /**/import ... from "[|module|]";
    // /**/import "[|module|]";
    if nodes[node].kind == Kind::ImportKeyword && nodes[parent].kind == Kind::ImportDeclaration {
        if let Some(location) =
            get_adjusted_location_for_import_declaration(nodes, parent, for_rename)
        {
            return Some(location);
        }
    }

    if nodes[node].kind == Kind::ExportKeyword {
        // /**/export { [|name|] } ...;
        // /**/export { propertyName as [|name|] } ...;
        // /**/export * from "[|module|]";
        // /**/export * as ... from "[|module|]";
        if nodes[parent].kind == Kind::ExportDeclaration {
            if let Some(location) =
                get_adjusted_location_for_export_declaration(nodes, parent, for_rename)
            {
                return Some(location);
            }
        }
        // NOTE: We don't adjust the location of the `default` keyword as that is handled specially by `getSymbolAtLocation`.
        // /**/export default [|name|];
        // /**/export = [|name|];
        if nodes[parent].kind == Kind::ExportAssignment {
            return Some(ast::skip_outer_expressions(
                nodes[parent].expression().expect("expression"),
                outer_expression_kinds::ALL,
                nodes,
            ));
        }
    }
    // import name = /**/require("[|module|]");
    if nodes[node].kind == Kind::RequireKeyword
        && nodes[parent].kind == Kind::ExternalModuleReference
    {
        return nodes[parent].expression();
    }
    // import ... /**/from "[|module|]";
    // export ... /**/from "[|module|]";
    if nodes[node].kind == Kind::FromKeyword {
        if (nodes[parent].kind == Kind::ImportDeclaration
            || nodes[parent].kind == Kind::ExportDeclaration)
            && nodes[parent].module_specifier().is_some()
        {
            return nodes[parent].module_specifier();
        }
    }
    // class ... /**/extends [|name|] ...
    // class ... /**/implements [|name|] ...
    // class ... /**/implements name1, name2 ...
    // interface ... /**/extends [|name|] ...
    // interface ... /**/extends name1, name2 ...
    if (nodes[node].kind == Kind::ExtendsKeyword || nodes[node].kind == Kind::ImplementsKeyword)
        && nodes[parent].kind == Kind::HeritageClause
        && nodes[parent].as_heritage_clause().token == nodes[node].kind
    {
        // `getAdjustedLocationForHeritageClause`.
        // /**/extends [|name|]
        // /**/implements [|name|]
        let clause = nodes[parent].as_heritage_clause();
        let location = match clause.types.as_ref().map(|t| t.nodes()) {
            Some(types) if types.len() == 1 => {
                ast::get_heritage_clause_element_name(&nodes[types[0]], nodes)
            }
            // fall through `getAdjustedLocation`
            //    /**/extends name1, name2 ...
            //    /**/implements name1, name2 ...
            _ => None,
        };
        if let Some(location) = location {
            return Some(location);
        }
    }
    if nodes[node].kind == Kind::ExtendsKeyword {
        // ... <T /**/extends [|U|]> ...
        if nodes[parent].kind == Kind::TypeParameter {
            if let Some(constraint) = nodes[parent].as_type_parameter_declaration().constraint {
                if nodes[constraint].kind == Kind::TypeReference {
                    return nodes[constraint].as_type_reference_node().type_name;
                }
            }
        }
        // ... T /**/extends [|U|] ? ...
        if nodes[parent].kind == Kind::ConditionalType {
            if let Some(extends_type) = nodes[parent].as_conditional_type_node().extends_type {
                if nodes[extends_type].kind == Kind::TypeReference {
                    return nodes[extends_type].as_type_reference_node().type_name;
                }
            }
        }
    }
    // ... T extends /**/infer [|U|] ? ...
    if nodes[node].kind == Kind::InferKeyword && nodes[parent].kind == Kind::InferType {
        return nodes[nodes[parent]
            .as_infer_type_node()
            .type_parameter
            .expect("typeParameter")]
        .name();
    }
    // { [ [|K|] /**/in keyof T]: ... }
    if nodes[node].kind == Kind::InKeyword
        && nodes[parent].kind == Kind::TypeParameter
        && nodes[parent]
            .parent
            .is_some_and(|gp| nodes[gp].kind == Kind::MappedType)
    {
        return nodes[parent].name();
    }
    // /**/keyof [|T|]
    if nodes[node].kind == Kind::KeyOfKeyword
        && nodes[parent].kind == Kind::TypeOperator
        && nodes[parent].as_type_operator_node().operator == Kind::KeyOfKeyword
    {
        if let Some(parent_type) = nodes[parent].type_() {
            if nodes[parent_type].kind == Kind::TypeReference {
                return nodes[parent_type].as_type_reference_node().type_name;
            }
        }
    }
    // /**/readonly [|name|][]
    if nodes[node].kind == Kind::ReadonlyKeyword
        && nodes[parent].kind == Kind::TypeOperator
        && nodes[parent].as_type_operator_node().operator == Kind::ReadonlyKeyword
    {
        if let Some(parent_type) = nodes[parent].type_() {
            if nodes[parent_type].kind == Kind::ArrayType {
                let element_type = nodes[parent_type].as_array_type_node().element_type;
                if let Some(element_type) = element_type {
                    if nodes[element_type].kind == Kind::TypeReference {
                        return nodes[element_type].as_type_reference_node().type_name;
                    }
                }
            }
        }
    }

    if !for_rename {
        // /**/new [|name|]
        // /**/void [|name|]
        // /**/void obj.[|name|]
        // /**/typeof [|name|]
        // /**/typeof obj.[|name|]
        // /**/await [|name|]
        // /**/await obj.[|name|]
        // /**/yield [|name|]
        // /**/yield obj.[|name|]
        // /**/delete obj.[|name|]
        if (nodes[node].kind == Kind::NewKeyword && nodes[parent].kind == Kind::NewExpression)
            || (nodes[node].kind == Kind::VoidKeyword && nodes[parent].kind == Kind::VoidExpression)
            || (nodes[node].kind == Kind::TypeOfKeyword
                && nodes[parent].kind == Kind::TypeOfExpression)
            || (nodes[node].kind == Kind::AwaitKeyword
                && nodes[parent].kind == Kind::AwaitExpression)
            || (nodes[node].kind == Kind::YieldKeyword
                && nodes[parent].kind == Kind::YieldExpression)
            || (nodes[node].kind == Kind::DeleteKeyword
                && nodes[parent].kind == Kind::DeleteExpression)
        {
            if let Some(expr) = nodes[parent].expression() {
                return Some(ast::skip_outer_expressions(
                    expr,
                    outer_expression_kinds::ALL,
                    nodes,
                ));
            }
        }

        // left /**/in [|name|]
        // left /**/instanceof [|name|]
        if (nodes[node].kind == Kind::InKeyword || nodes[node].kind == Kind::InstanceOfKeyword)
            && nodes[parent].kind == Kind::BinaryExpression
            && nodes[parent].as_binary_expression().operator_token == Some(node)
        {
            return Some(ast::skip_outer_expressions(
                nodes[parent].as_binary_expression().right.expect("right"),
                outer_expression_kinds::ALL,
                nodes,
            ));
        }

        // left /**/as [|name|]
        if nodes[node].kind == Kind::AsKeyword && nodes[parent].kind == Kind::AsExpression {
            if let Some(as_expr_type) = nodes[parent].type_() {
                if nodes[as_expr_type].kind == Kind::TypeReference {
                    return nodes[as_expr_type].as_type_reference_node().type_name;
                }
            }
        }

        // for (... /**/in [|name|])
        // for (... /**/of [|name|])
        if (nodes[node].kind == Kind::InKeyword && nodes[parent].kind == Kind::ForInStatement)
            || (nodes[node].kind == Kind::OfKeyword && nodes[parent].kind == Kind::ForOfStatement)
        {
            return Some(ast::skip_outer_expressions(
                nodes[parent].expression().expect("expression"),
                outer_expression_kinds::ALL,
                nodes,
            ));
        }
    }

    Some(node)
}

/// `getAdjustedLocationForDeclaration`.
fn get_adjusted_location_for_declaration(
    nodes: &mut Vec<Node>,
    node: NodeId,
    for_rename: bool,
    source_file: Option<NodeId>,
) -> Option<NodeId> {
    if nodes[node].name().is_some() {
        return nodes[node].name();
    }
    if for_rename {
        return None;
    }
    let source_file = source_file?;
    match nodes[node].kind {
        Kind::ClassDeclaration | Kind::FunctionDeclaration => {
            // for class and function declarations, use the `default` modifier
            // when the declaration is unnamed.
            nodes[node].modifier_nodes().and_then(|m| {
                m.iter()
                    .copied()
                    .find(|&n| nodes[n].kind == Kind::DefaultKeyword)
            })
        }
        Kind::ClassExpression => {
            // for class expressions, use the `class` keyword when the class is unnamed
            tsc_astnav::tokens::find_child_of_kind(nodes, source_file, node, Kind::ClassKeyword)
        }
        Kind::FunctionExpression => {
            // for function expressions, use the `function` keyword when the function is unnamed
            tsc_astnav::tokens::find_child_of_kind(nodes, source_file, node, Kind::FunctionKeyword)
        }
        Kind::Constructor => Some(node),
        _ => None,
    }
}

/// `getAdjustedLocationForImportDeclaration` — `node` is the
/// `*ast.ImportDeclaration` node id.
fn get_adjusted_location_for_import_declaration(
    nodes: &[Node],
    node: NodeId,
    for_rename: bool,
) -> Option<NodeId> {
    let node_data = nodes[node].as_import_declaration();
    if let Some(import_clause) = node_data.import_clause {
        let clause_name = nodes[import_clause].name();
        if let Some(name) = clause_name {
            if nodes[import_clause]
                .as_import_clause()
                .named_bindings
                .is_some()
            {
                // do not adjust if we have both a name and named bindings
                return None;
            }
            // /**/import [|name|] from ...;
            // import /**/type [|name|] from ...;
            return Some(name);
        }

        // /**/import { [|name|] } from ...;
        // /**/import { propertyName as [|name|] } from ...;
        // /**/import * as [|name|] from ...;
        // import /**/type { [|name|] } from ...;
        // import /**/type { propertyName as [|name|] } from ...;
        // import /**/type * as [|name|] from ...;
        if let Some(named_bindings) = nodes[import_clause].as_import_clause().named_bindings {
            match nodes[named_bindings].kind {
                Kind::NamedImports => {
                    // do nothing if there is more than one binding
                    let elements = nodes[named_bindings].elements().unwrap_or(&[]);
                    if elements.len() != 1 {
                        return None;
                    }
                    return nodes[elements[0]].name();
                }
                Kind::NamespaceImport => return nodes[named_bindings].name(),
                _ => {}
            }
        }
    }
    if !for_rename {
        // /**/import "[|module|]";
        // /**/import ... from "[|module|]";
        // import /**/type ... from "[|module|]";
        return node_data.module_specifier;
    }
    None
}

/// `getAdjustedLocationForExportDeclaration` — `node` is the
/// `*ast.ExportDeclaration` node id.
fn get_adjusted_location_for_export_declaration(
    nodes: &[Node],
    node: NodeId,
    for_rename: bool,
) -> Option<NodeId> {
    let node_data = nodes[node].as_export_declaration();
    if let Some(export_clause) = node_data.export_clause {
        // /**/export { [|name|] } ...
        // /**/export { propertyName as [|name|] } ...
        // /**/export * as [|name|] ...
        // export /**/type { [|name|] } from ...
        // export /**/type { propertyName as [|name|] } from ...
        // export /**/type * as [|name|] ...
        match nodes[export_clause].kind {
            Kind::NamedExports => {
                // do nothing if there is more than one binding
                let elements = nodes[export_clause].elements().unwrap_or(&[]);
                if elements.len() != 1 {
                    return None;
                }
                return nodes[elements[0]].name();
            }
            Kind::NamespaceExport => return nodes[export_clause].name(),
            _ => {}
        }
    }
    if !for_rename {
        // /**/export * from "[|module|]";
        // export /**/type * from "[|module|]";
        return node_data.module_specifier;
    }
    None
}

/// `symbolFlagsHaveMeaning`.
pub(crate) fn symbol_flags_have_meaning(flags: SymbolFlags, meaning: ast::SemanticMeaning) -> bool {
    if meaning == ast::SemanticMeaning::ALL {
        return true;
    }
    if meaning & ast::SemanticMeaning::VALUE != ast::SemanticMeaning::NONE {
        return flags.intersects(SymbolFlags::VALUE);
    }
    if meaning & ast::SemanticMeaning::TYPE != ast::SemanticMeaning::NONE {
        return flags.intersects(SymbolFlags::TYPE);
    }
    if meaning & ast::SemanticMeaning::NAMESPACE != ast::SemanticMeaning::NONE {
        return flags.intersects(SymbolFlags::NAMESPACE);
    }
    false
}

/// `getMeaningFromLocation`.
pub(crate) fn get_meaning_from_location(
    nodes: &mut Vec<Node>,
    node: NodeId,
) -> ast::SemanticMeaning {
    // todo: check if this function needs to be changed for jsdoc updates
    let node = get_adjusted_location(
        nodes,
        ast::get_reparsed_node_for_node(node, nodes),
        false, /*forRename*/
        None,
    )
    .unwrap_or(node);
    let parent = nodes[node].parent;
    if ast::is_source_file(&nodes[node]) {
        ast::SemanticMeaning::VALUE
    } else if parent.is_some_and(|p| {
        ast::node_kind_is(
            &nodes[p],
            &[
                Kind::ExportAssignment,
                Kind::ExportSpecifier,
                Kind::ExternalModuleReference,
                Kind::ImportSpecifier,
                Kind::ImportClause,
            ],
        ) || (nodes[p].kind == Kind::ImportEqualsDeclaration && Some(node) == nodes[p].name())
    }) {
        ast::SemanticMeaning::ALL
    } else if is_in_right_side_of_internal_import_equals_declaration(node, nodes) {
        //     import a = |b|; // Namespace
        //     import a = |b.c|; // Value, type, namespace
        //     import a = |b.c|.d; // Namespace
        let mut name = Some(node);
        if nodes[node].kind != Kind::QualifiedName {
            name = if nodes[node].parent.is_some_and(|p| {
                nodes[p].kind == Kind::QualifiedName
                    && nodes[p].as_qualified_name().right == Some(node)
            }) {
                nodes[node].parent
            } else {
                None
            };
        }
        if name.is_some_and(|n| {
            nodes[n]
                .parent
                .is_some_and(|p| nodes[p].kind == Kind::ImportEqualsDeclaration)
        }) {
            return ast::SemanticMeaning::ALL;
        }
        ast::SemanticMeaning::NAMESPACE
    } else if ast::is_declaration_name(node, nodes) {
        get_meaning_from_declaration(parent.map(|p| &nodes[p]).expect("parent"), nodes)
    } else if ast::is_entity_name(&nodes[node])
        && ast::is_js_doc_name_reference_context(node, nodes)
    {
        ast::SemanticMeaning::ALL
    } else if is_type_reference(node, nodes) {
        ast::SemanticMeaning::TYPE
    } else if is_namespace_reference(node, nodes) {
        ast::SemanticMeaning::NAMESPACE
    } else if parent.is_some_and(|p| ast::is_type_parameter_declaration(&nodes[p])) {
        ast::SemanticMeaning::TYPE
    } else if parent.is_some_and(|p| ast::is_literal_type_node(&nodes[p])) {
        // This might be T["name"], which is actually referencing a property and not a type. So allow both meanings.
        ast::SemanticMeaning::TYPE | ast::SemanticMeaning::VALUE
    } else {
        ast::SemanticMeaning::VALUE
    }
}

/// `getMeaningFromDeclaration`.
pub(crate) fn get_meaning_from_declaration(node: &Node, nodes: &[Node]) -> ast::SemanticMeaning {
    match node.kind {
        Kind::VariableDeclaration
        | Kind::Parameter
        | Kind::BindingElement
        | Kind::PropertyDeclaration
        | Kind::PropertySignature
        | Kind::PropertyAssignment
        | Kind::ShorthandPropertyAssignment
        | Kind::MethodDeclaration
        | Kind::MethodSignature
        | Kind::Constructor
        | Kind::GetAccessor
        | Kind::SetAccessor
        | Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::ArrowFunction
        | Kind::CatchClause
        | Kind::JsxAttribute => ast::SemanticMeaning::VALUE,

        Kind::TypeParameter
        | Kind::InterfaceDeclaration
        | Kind::TypeAliasDeclaration
        | Kind::JSTypeAliasDeclaration
        | Kind::TypeLiteral => ast::SemanticMeaning::TYPE,

        Kind::EnumMember | Kind::ClassDeclaration => {
            ast::SemanticMeaning::VALUE | ast::SemanticMeaning::TYPE
        }

        Kind::ModuleDeclaration => {
            if ast::is_ambient_module(node, nodes) {
                ast::SemanticMeaning::NAMESPACE | ast::SemanticMeaning::VALUE
            } else if ast::get_module_instance_state(node.id, nodes)
                == ast::ModuleInstanceState::Instantiated
            {
                ast::SemanticMeaning::NAMESPACE | ast::SemanticMeaning::VALUE
            } else {
                ast::SemanticMeaning::NAMESPACE
            }
        }

        Kind::EnumDeclaration
        | Kind::NamedImports
        | Kind::ImportSpecifier
        | Kind::ImportEqualsDeclaration
        | Kind::ImportDeclaration
        | Kind::JSImportDeclaration
        | Kind::ExportAssignment
        | Kind::ExportDeclaration => ast::SemanticMeaning::ALL,

        // An external module can be a Value
        Kind::SourceFile => ast::SemanticMeaning::NAMESPACE | ast::SemanticMeaning::VALUE,

        _ => ast::SemanticMeaning::ALL,
    }
}

/// `getIntersectingMeaningFromDeclarations`.
pub(crate) fn get_intersecting_meaning_from_declarations(
    nodes: &mut Vec<Node>,
    program: &Program,
    node: Option<NodeId>,
    symbol: SymbolId,
    default_meaning: ast::SemanticMeaning,
) -> ast::SemanticMeaning {
    let Some(node) = node else {
        return default_meaning;
    };

    let meaning = get_meaning_from_location(nodes, node);
    let declarations = program.symbols.borrow()[symbol.index()]
        .declarations
        .clone();
    if declarations.is_empty() {
        return meaning;
    }

    let mut last_iteration_meaning = meaning;

    let iteration = |m: ast::SemanticMeaning| -> ast::SemanticMeaning {
        let mut m = m;
        for &declaration in &declarations {
            let decl_nodes = program.nodes(declaration.file_index());
            let declaration_meaning =
                get_meaning_from_declaration(&decl_nodes[declaration], &decl_nodes);

            if declaration_meaning & m != ast::SemanticMeaning::NONE {
                m |= declaration_meaning;
            }
        }
        m
    };
    let mut meaning = iteration(meaning);

    while meaning != last_iteration_meaning {
        // The result is order-sensitive, for instance if initialMeaning == Namespace, and declarations = [class, instantiated module]
        // we need to consider both as the initialMeaning intersects with the module in the namespace space, and the module
        // intersects with the class in the value space.
        // To achieve that we will keep iterating until the result stabilizes.

        // Remember the last meaning
        last_iteration_meaning = meaning;
        meaning = iteration(meaning);
    }

    meaning
}

// Returns the node in an `extends` or `implements` clause of a class or interface.
/// `getAllSuperTypeNodes`.
pub(crate) fn get_all_super_type_nodes(node: &Node, nodes: &[Node]) -> Vec<NodeId> {
    if ast::is_interface_declaration(node) {
        return ast::get_heritage_elements(node, Kind::ExtendsKeyword, nodes)
            .map(|e| e.to_vec())
            .unwrap_or_default();
    }
    if ast::is_class_like(Some(node.id), nodes) {
        let mut result = tsc_core::core::single_element_slice(
            ast::get_class_extends_heritage_element(node, nodes),
        );
        if let Some(elements) = ast::get_implements_heritage_clause_elements(node, nodes) {
            result.extend_from_slice(elements);
        }
        return result;
    }
    Vec::new()
}

/// `getParentSymbolsOfPropertyAccess`.
pub(crate) fn get_parent_symbols_of_property_access(
    location: NodeId,
    symbol: SymbolId,
    ch: &mut Checker,
) -> Vec<SymbolId> {
    let (is_right_side, lhs_expr) = {
        let program = ch.program.clone().expect("program");
        let nodes = program.nodes(location.file_index());
        (
            is_right_side_of_property_access(location, &nodes),
            nodes[location].parent.and_then(|p| nodes[p].expression()),
        )
    };
    if !is_right_side {
        return Vec::new();
    }
    let symbol_parent = ch.symbol_arena.borrow()[symbol.index()].parent;
    let Some(lhs_expr) = lhs_expr else {
        return Vec::new();
    };
    // PORT: Go's `lhsType == nil` check is unreachable — `get_type_at_location`
    // always returns a type (errorType at worst).
    let lhs_type = ch.get_type_at_location(lhs_expr);
    let possible_symbols: Vec<TypeId> = {
        let (is_union_or_intersection, types, lhs_symbol) = {
            let ty = ch.types.get(lhs_type);
            (
                ty.flags() & tsc_checker::types::TypeFlags::UNION_OR_INTERSECTION
                    != tsc_checker::types::TypeFlags::NONE,
                ty.types().to_vec(),
                ty.symbol,
            )
        };
        if is_union_or_intersection {
            types
        } else if lhs_symbol != symbol_parent {
            vec![lhs_type]
        } else {
            Vec::new()
        }
    };
    tsc_core::core::map_non_nil(&possible_symbols, |t| {
        let sym = ch.types.get(*t).symbol;
        sym.filter(|s| {
            ch.symbol_arena.borrow()[s.index()].flags
                & (SymbolFlags::CLASS | SymbolFlags::INTERFACE)
                != SymbolFlags::NONE
        })
    })
}

// Find symbol of the given property-name and add the symbol to the given result array
// @param symbol a symbol to start searching for the given propertyName
// @param propertyName a name of property to search for
// @param cb a cache of symbol from previous iterations of calling this function to prevent infinite revisiting of the same symbol.
//
//	The value of previousIterationSymbol is undefined when the function is first called.
/// `getPropertySymbolsFromBaseTypes`.
pub(crate) fn get_property_symbols_from_base_types(
    symbol: SymbolId,
    property_name: &str,
    checker: &mut Checker,
    cb: &mut dyn FnMut(SymbolId) -> Option<SymbolId>,
) -> Option<SymbolId> {
    fn recur(
        symbol: SymbolId,
        seen: &mut Set<SymbolId>,
        property_name: &str,
        checker: &mut Checker,
        cb: &mut dyn FnMut(SymbolId) -> Option<SymbolId>,
    ) -> Option<SymbolId> {
        // Use `addToSeen` to ensure we don't infinitely recurse in this situation:
        //      interface C extends C {
        //          /*findRef*/propName: string;
        //      }
        let flags = checker.symbol_arena.borrow()[symbol.index()].flags;
        if flags & (SymbolFlags::CLASS | SymbolFlags::INTERFACE) == SymbolFlags::NONE
            || !seen.add_if_absent(symbol)
        {
            return None;
        }
        let declarations = checker.symbol_arena.borrow()[symbol.index()]
            .declarations
            .clone();
        for declaration in declarations {
            let super_type_nodes = {
                let program = checker.program.clone().expect("program");
                let nodes = program.nodes(declaration.file_index());
                get_all_super_type_nodes(&nodes[declaration], &nodes)
            };
            for type_reference in super_type_nodes {
                let property_type = checker.get_type_at_location(type_reference);
                let property_symbol = if checker.types.get(property_type).symbol.is_some() {
                    // Visit the typeReference as well to see if it directly or indirectly uses that property
                    checker.get_property_of_type(property_type, property_name)
                } else {
                    None
                };
                if let Some(property_symbol) = property_symbol {
                    for root_symbol in checker.get_root_symbols(property_symbol) {
                        if let Some(result) = cb(root_symbol) {
                            return Some(result);
                        }
                    }
                }
                let property_type_symbol = checker.types.get(property_type).symbol;
                if let Some(property_type_symbol) = property_type_symbol {
                    if let Some(result) =
                        recur(property_type_symbol, seen, property_name, checker, cb)
                    {
                        return Some(result);
                    }
                }
            }
        }
        None
    }
    let mut seen = Set::new();
    recur(symbol, &mut seen, property_name, checker, cb)
}

/// `getPropertySymbolFromBindingElement`.
pub(crate) fn get_property_symbol_from_binding_element(
    checker: &mut Checker,
    binding_element: NodeId,
) -> Option<SymbolId> {
    let (parent, name_text) = {
        let program = checker.program.clone().expect("program");
        let nodes = program.nodes(binding_element.file_index());
        (
            nodes[binding_element].parent,
            nodes[binding_element]
                .name()
                .map(|n| nodes[n].text(&nodes).into_owned()),
        )
    };
    let type_of_pattern = checker.get_type_at_location(parent?);
    checker.get_property_of_type(type_of_pattern, &name_text?)
}

/// `getPropertySymbolOfObjectBindingPatternWithoutPropertyName`.
pub(crate) fn get_property_symbol_of_object_binding_pattern_without_property_name(
    symbol: SymbolId,
    checker: &mut Checker,
) -> Option<SymbolId> {
    let declarations = checker.symbol_arena.borrow()[symbol.index()]
        .declarations
        .clone();
    let binding_element = declarations.iter().copied().find(|&d| {
        let program = checker.program.clone().expect("program");
        let nodes = program.nodes(d.file_index());
        nodes[d].kind == Kind::BindingElement
    });
    if let Some(binding_element) = binding_element {
        let is_without_property_name = {
            let program = checker.program.clone().expect("program");
            let nodes = program.nodes(binding_element.file_index());
            is_object_binding_element_without_property_name(binding_element, &nodes)
        };
        if is_without_property_name {
            return get_property_symbol_from_binding_element(checker, binding_element);
        }
    }
    None
}

/// `getTargetLabel`.
pub(crate) fn get_target_label(
    nodes: &[Node],
    mut reference_node: Option<NodeId>,
    label_name: &str,
) -> Option<NodeId> {
    // todo: rewrite as `ast.FindAncestor`
    while let Some(n) = reference_node {
        if nodes[n].kind == Kind::LabeledStatement
            && nodes[n]
                .label()
                .is_some_and(|l| nodes[l].text(nodes).as_ref() == label_name)
        {
            return nodes[n].label();
        }
        reference_node = nodes[n].parent;
    }
    None
}

/// `skipConstraint`.
pub(crate) fn skip_constraint(t: TypeId, type_checker: &mut Checker) -> TypeId {
    if type_checker.types.get(t).is_type_parameter() {
        if let Some(c) = type_checker.get_base_constraint_of_type(t) {
            return c;
        }
    }
    t
}

/// `caseClauseTrackerState` — the sole `caseClauseTracker` implementation,
/// flattened into the interface (PORT: one impl only).
///
/// `existingNumbers` is a `Vec` rather than `Set` — `jsnum.Number` is f64-backed
/// and not `Hash`; `Vec::contains` uses `PartialEq`, matching Go's map-key `==`
/// for JS numbers (NaN never equals).
#[derive(Default)]
pub(crate) struct CaseClauseTracker {
    /// `existingStrings`.
    existing_strings: Set<String>,
    /// `existingNumbers`.
    existing_numbers: Vec<tsc_jsnum::Number>,
    /// `existingBigInts`.
    existing_big_ints: Set<tsc_jsnum::PseudoBigInt>,
}

/// `trackerAddValue` — `string | jsnum.Number`.
#[derive(Clone)]
pub(crate) enum TrackerAddValue {
    /// `string`.
    Str(String),
    /// `jsnum.Number`.
    Number(tsc_jsnum::Number),
}

/// `trackerHasValue` — `string | jsnum.Number | jsnum.PseudoBigInt`.
#[derive(Clone)]
pub(crate) enum TrackerHasValue {
    /// `string`.
    Str(String),
    /// `jsnum.Number`.
    Number(tsc_jsnum::Number),
    /// `jsnum.PseudoBigInt`.
    PseudoBigInt(tsc_jsnum::PseudoBigInt),
}

impl CaseClauseTracker {
    /// `addValue`.
    pub(crate) fn add_value(&mut self, value: TrackerAddValue) {
        match value {
            TrackerAddValue::Str(v) => {
                self.existing_strings.add(v);
            }
            TrackerAddValue::Number(v) => {
                if !self.existing_numbers.contains(&v) {
                    self.existing_numbers.push(v);
                }
            }
        }
    }

    /// `hasValue`.
    pub(crate) fn has_value(&self, value: TrackerHasValue) -> bool {
        match value {
            TrackerHasValue::Str(v) => self.existing_strings.has(&v),
            TrackerHasValue::Number(v) => self.existing_numbers.contains(&v),
            TrackerHasValue::PseudoBigInt(v) => self.existing_big_ints.has(&v),
        }
    }
}

/// `newCaseClauseTracker`.
pub(crate) fn new_case_clause_tracker(
    type_checker: &mut Checker,
    clauses: &[NodeId],
) -> CaseClauseTracker {
    let mut c = CaseClauseTracker::default();
    for &clause in clauses {
        let (is_default, clause_expression, expression) = {
            let program = type_checker.program.clone().expect("program");
            let nodes = program.nodes(clause.file_index());
            (
                ast::is_default_clause(&nodes[clause]),
                nodes[clause].expression(),
                nodes[clause]
                    .expression()
                    .map(|e| ast::skip_parentheses(e, &nodes)),
            )
        };
        if is_default {
            continue;
        }
        let expression = expression.expect("expression");
        let (is_literal, kind, text) = {
            let program = type_checker.program.clone().expect("program");
            let nodes = program.nodes(expression.file_index());
            (
                ast::is_literal_expression(&nodes[expression]),
                nodes[expression].kind,
                nodes[expression].text(&nodes).into_owned(),
            )
        };
        if is_literal {
            match kind {
                Kind::NoSubstitutionTemplateLiteral | Kind::StringLiteral => {
                    c.existing_strings.add(text);
                }
                Kind::NumericLiteral => {
                    let n = tsc_jsnum::from_string(&text);
                    if !c.existing_numbers.contains(&n) {
                        c.existing_numbers.push(n);
                    }
                }
                Kind::BigIntLiteral => {
                    c.existing_big_ints
                        .add(tsc_jsnum::parse_valid_big_int(&text));
                }
                _ => {}
            }
        } else {
            let symbol =
                type_checker.get_symbol_at_location_api(clause_expression.expect("expression"));
            let value_declaration = symbol
                .and_then(|s| type_checker.symbol_arena.borrow()[s.index()].value_declaration);
            let is_enum_member = value_declaration.is_some_and(|vd| {
                let program = type_checker.program.clone().expect("program");
                let nodes = program.nodes(vd.file_index());
                ast::is_enum_member(&nodes[vd])
            });
            if is_enum_member {
                let enum_value =
                    type_checker.get_constant_value(value_declaration.expect("valueDeclaration"));
                if let Some(enum_value) = enum_value {
                    // `c.addValue(enumValue)` — Go's `any` argument accepts
                    // only string|Number; other variants hit Go's `default:
                    // panic` arm.
                    match enum_value {
                        tsc_evaluator::Value::String(s) => {
                            c.add_value(TrackerAddValue::Str(s));
                        }
                        tsc_evaluator::Value::Number(n) => {
                            c.add_value(TrackerAddValue::Number(n));
                        }
                        v => panic!("Unsupported type: {v:?}"),
                    }
                }
            }
        }
    }
    c
}

/// `RangeContainsRange`.
pub fn range_contains_range(r1: &TextRange, r2: &TextRange) -> bool {
    start_end_contains_range(r1.pos(), r1.end(), r2)
}

/// `startEndContainsRange`.
pub(crate) fn start_end_contains_range(
    start: TextPos,
    end: TextPos,
    text_range: &TextRange,
) -> bool {
    start <= text_range.pos() && end >= text_range.end()
}

/// `getPossibleGenericSignatures` — `called` is `*ast.Expression`.
pub(crate) fn get_possible_generic_signatures(
    called: NodeId,
    type_argument_count: i32,
    c: &mut Checker,
) -> Vec<SignatureId> {
    let mut type_at_location = c.get_type_at_location(called);
    {
        let program = c.program.clone().expect("program");
        let nodes = program.nodes(called.file_index());
        if nodes[called]
            .parent
            .is_some_and(|p| ast::is_optional_chain(&nodes[p]))
        {
            let is_optional_chain_root = nodes[called]
                .parent
                .is_some_and(|p| ast::is_optional_chain_root(&nodes[p]));
            drop(nodes);
            type_at_location =
                remove_optionality(type_at_location, true, is_optional_chain_root, c);
        }
    }
    let is_new_expression = {
        let program = c.program.clone().expect("program");
        let nodes = program.nodes(called.file_index());
        nodes[called]
            .parent
            .is_some_and(|p| ast::is_new_expression(&nodes[p]))
    };
    let signatures = if is_new_expression {
        c.get_signatures_of_type(type_at_location, SignatureKind::Construct)
    } else {
        c.get_signatures_of_type(type_at_location, SignatureKind::Call)
    };
    signatures
        .into_iter()
        .filter(|s| {
            let sig = c.signature_arena.get(*s);
            !sig.type_parameters.is_empty()
                && sig.type_parameters.len() as i32 >= type_argument_count
        })
        .collect()
}

/// `removeOptionality`.
pub(crate) fn remove_optionality(
    t: TypeId,
    is_optional_expression: bool,
    is_optional_chain: bool,
    c: &mut Checker,
) -> TypeId {
    if is_optional_expression {
        c.get_non_nullable_type(t)
    } else if is_optional_chain {
        c.get_non_optional_type(t)
    } else {
        t
    }
}

/// `isNoSubstitutionTemplateLiteral`.
pub(crate) fn is_no_substitution_template_literal(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].kind == Kind::NoSubstitutionTemplateLiteral
}

/// `isTaggedTemplateExpression`.
pub(crate) fn is_tagged_template_expression(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].kind == Kind::TaggedTemplateExpression
}

/// `isInsideTemplateLiteral`.
pub(crate) fn is_inside_template_literal(
    nodes: &[Node],
    node: NodeId,
    position: TextPos,
    source_file: NodeId,
) -> bool {
    ast::is_template_literal_kind(nodes[node].kind)
        && (get_token_pos_of_node(node, nodes[source_file].as_source_file(), false, nodes)
            < position
            && position < nodes[node].end()
            || (ast::is_unterminated_literal(&nodes[node]) && position == nodes[node].end()))
}

// Pseudo-literals
/// `isTemplateHead`.
pub(crate) fn is_template_head(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].kind == Kind::TemplateHead
}

/// `isTemplateTail`.
pub(crate) fn is_template_tail(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].kind == Kind::TemplateTail
}

/// `findPrecedingMatchingToken`.
pub(crate) fn find_preceding_matching_token(
    nodes: &mut Vec<Node>,
    token: NodeId,
    matching_token_kind: Kind,
    source_file: NodeId,
) -> Option<NodeId> {
    let close_token_text = token_to_string(nodes[token].kind);
    let matching_token_text = token_to_string(matching_token_kind);
    // Text-scan based fast path - can be bamboozled by comments and other trivia, but often provides
    // a good, fast approximation without too much extra work in the cases where it fails.
    let text = nodes[source_file].as_source_file().text().to_string();
    let Some(best_guess_index) = text.rfind(matching_token_text) else {
        return None; // if the token text doesn't appear in the file, there can't be a match - super fast bail
    };
    // we can only use the textual result directly if we didn't have to count any close tokens within the range
    if text
        .rfind(close_token_text)
        .is_none_or(|i| i < best_guess_index)
    {
        let node_at_guess = tsc_astnav::tokens::find_preceding_token(
            nodes,
            source_file,
            (best_guess_index + 1) as i32,
        );
        if node_at_guess.is_some_and(|n| nodes[n].kind == matching_token_kind) {
            return node_at_guess;
        }
    }
    let token_kind = nodes[token].kind;
    let mut token = token;
    let mut remaining_matching_tokens = 0i32;
    loop {
        let Some(preceding) =
            tsc_astnav::tokens::find_preceding_token(nodes, source_file, nodes[token].pos())
        else {
            return None;
        };
        token = preceding;
        if nodes[token].kind == matching_token_kind {
            if remaining_matching_tokens == 0 {
                return Some(token);
            }
            remaining_matching_tokens -= 1;
        } else if nodes[token].kind == token_kind {
            remaining_matching_tokens += 1;
        }
    }
}

/// `findContainingList`.
pub(crate) fn find_containing_list(
    nodes: &mut Vec<Node>,
    node: NodeId,
    file: NodeId,
) -> Option<NodeList> {
    // The node might be a list element (nonsynthetic) or a comma (synthetic). Either way, it will
    // be parented by the container of the SyntaxList, not the SyntaxList itself.
    let list = Cell::new(None::<NodeList>);
    let node_loc = nodes[node].loc;
    let visit_node =
        |_cx: &mut VisitorCx, n: NodeId, _visitor: &NodeVisitor| -> Option<NodeId> { Some(n) };
    let visit_nodes = |_cx: &mut VisitorCx,
                       node_list: Option<NodeList>,
                       _visitor: &NodeVisitor|
     -> Option<NodeList> {
        if let Some(nl) = &node_list {
            if range_contains_range(&nl.loc, &node_loc) {
                list.set(Some(nl.clone()));
            }
        }
        node_list
    };
    tsc_astnav::tokens::visit_each_child_and_jsdoc(
        nodes,
        file,
        nodes[node].parent.expect("parent"),
        Some(&visit_node),
        Some(&visit_nodes),
    );
    list.take()
}

/// `getLeadingCommentRangesOfNode` — Go returns `iter.Seq[ast.CommentRange]`;
/// the port collects (same as the scanner port does).
pub(crate) fn get_leading_comment_ranges_of_node(
    nodes: &mut Vec<Node>,
    node: NodeId,
    file: NodeId,
) -> Vec<CommentRange> {
    if nodes[node].kind == Kind::JsxText {
        return Vec::new();
    }
    let text = nodes[file].as_source_file().text().to_string();
    tsc_scanner::scanner::get_leading_comment_ranges(
        &NodeFactory::new(NodeFactoryHooks::default()),
        &text,
        nodes[node].pos(),
    )
}

// Equivalent to Strada's `node.getChildren()` for non-JSDoc nodes.
/// `getChildrenFromNonJSDocNode`.
pub(crate) fn get_children_from_non_jsdoc_node(
    nodes: &mut Vec<Node>,
    node: NodeId,
    source_file: NodeId,
) -> Vec<NodeId> {
    let mut child_nodes: Vec<NodeId> = Vec::new();
    nodes[node].for_each_child(nodes, &mut |child| {
        child_nodes.push(child);
        false
    });

    // If the node has no children, don't scan for tokens.
    // This prevents creating tokens for leaf nodes' own text.
    if child_nodes.is_empty() {
        return Vec::new();
    }

    // PORT: the scanner borrows the source text, so clone it — the same
    // pattern `astnav` uses (`NavCtx::text`).
    let (text, language_variant) = {
        let sf = nodes[source_file].as_source_file();
        (sf.text().to_string(), sf.language_variant)
    };
    let mut scanner = Scanner::new();
    scanner.set_text(&text);
    scanner.set_language_variant(language_variant);
    let mut pos = nodes[node].pos();
    scanner.reset_pos(pos as usize);
    scanner.scan();

    let mut children: Vec<NodeId> = Vec::new();
    for &child in &child_nodes {
        while pos < nodes[child].pos() {
            let token = scanner.token();
            let token_full_start = scanner.token_full_start() as TextPos;
            let token_end = scanner.token_end() as TextPos;
            let token_flags = scanner.token_flags();
            children.push(ast::get_or_create_token(
                nodes,
                source_file,
                token,
                token_full_start,
                token_end,
                node,
                token_flags,
            ));
            pos = token_end;
            scanner.scan();
        }
        children.push(child);
        pos = nodes[child].end();
    }
    while pos < nodes[node].end() {
        let token = scanner.token();
        let token_full_start = scanner.token_full_start() as TextPos;
        let token_end = scanner.token_end() as TextPos;
        let token_flags = scanner.token_flags();
        children.push(ast::get_or_create_token(
            nodes,
            source_file,
            token,
            token_full_start,
            token_end,
            node,
            token_flags,
        ));
        pos = token_end;
        scanner.scan();
    }
    children
}

// Returns the containing object literal property declaration given a possible name node, e.g. "a" in x = { "a": 1 }
/// `getContainingObjectLiteralElement`.
pub(crate) fn get_containing_object_literal_element(
    node: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    let element = get_containing_object_literal_element_worker(node, nodes);
    if element.is_some_and(|e| {
        ast::is_object_literal_expression(&nodes[nodes[e].parent.unwrap_or(e)])
            || ast::is_jsx_attributes(&nodes[nodes[e].parent.unwrap_or(e)])
    }) {
        return element;
    }
    None
}

/// `getContainingObjectLiteralElementWorker`.
fn get_containing_object_literal_element_worker(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    match nodes[node].kind {
        Kind::StringLiteral | Kind::NoSubstitutionTemplateLiteral | Kind::NumericLiteral => {
            if nodes[node]
                .parent
                .is_some_and(|p| nodes[p].kind == Kind::ComputedPropertyName)
            {
                let grandparent = nodes[node].parent.and_then(|p| nodes[p].parent);
                if grandparent.is_some_and(|gp| is_object_literal_or_jsx_element(gp, nodes)) {
                    return grandparent;
                }
                return None;
            }
            // fallthrough — handled below
            fallthrough_literal_name(node, nodes)
        }
        Kind::Identifier | Kind::JsxNamespacedName => fallthrough_literal_name(node, nodes),
        _ => None,
    }
}

/// The shared tail of `getContainingObjectLiteralElementWorker`'s
/// `fallthrough` into the Identifier/JsxNamespacedName case.
fn fallthrough_literal_name(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    if let Some(parent) = nodes[node].parent {
        if is_object_literal_or_jsx_element(parent, nodes) {
            let grandparent = nodes[parent].parent;
            if grandparent.is_some_and(|gp| {
                nodes[gp].kind == Kind::ObjectLiteralExpression
                    || nodes[gp].kind == Kind::JsxAttributes
            }) && nodes[parent].name() == Some(node)
            {
                return Some(parent);
            }
        }
    }
    None
}

/// `isObjectLiteralOrJsxElement`.
pub(crate) fn is_object_literal_or_jsx_element(node: NodeId, nodes: &[Node]) -> bool {
    ast::is_object_literal_element(&nodes[node])
        || ast::is_jsx_attribute(&nodes[node])
        || ast::is_jsx_spread_attribute(&nodes[node])
}

// Return a function that returns true if the given node has not been seen
/// `nodeSeenTracker`.
pub(crate) fn node_seen_tracker() -> impl FnMut(NodeId) -> bool {
    let mut seen = Set::new();
    move |node| seen.add_if_absent(node)
}

// FindAllReferences.toContextSpan
/// `toContextRange`.
pub(crate) fn to_context_range(
    text_range: TextRange,
    context_file: NodeId,
    context: Option<NodeId>,
    nodes: &[Node],
) -> Option<TextRange> {
    let Some(context) = context else {
        return Some(text_range);
    };
    // !!! isContextWithStartAndEndNode
    // PORT(sibling): `get_range_of_node` is owned by findallreferences.rs —
    // Go signature `(node, sourceFile, endNode)`.
    let context_range =
        crate::findallreferences::get_range_of_node(context, Some(context_file), None, nodes);
    if context_range.pos() != text_range.pos() || context_range.end() != text_range.end() {
        return Some(context_range);
    }
    None
}

/// `getReferenceAtPosition`.
pub(crate) fn get_reference_at_position(
    nodes: &mut Vec<Node>,
    source_file: NodeId,
    position: TextPos,
    program: &Program,
) -> Option<crate::findallreferences::RefInfo> {
    if let Some(reference_path) = find_reference_in_position(
        &nodes[source_file].as_source_file().referenced_files,
        position,
    ) {
        if let Some(file) = program.get_source_file_from_reference(source_file, &reference_path) {
            return Some(crate::findallreferences::RefInfo {
                reference: Some(reference_path),
                file_name: program_file_name(program, file),
                file: Some(file),
                unverified: false,
            });
        }
        return None;
    }

    let type_reference_directives = nodes[source_file]
        .as_source_file()
        .type_reference_directives
        .clone();
    if let Some(type_reference_directive) =
        find_reference_in_position(&type_reference_directives, position)
    {
        if let Some(reference) = program
            .get_resolved_type_reference_directive_from_type_reference_directive(
                &type_reference_directive,
                source_file,
            )
        {
            if let Some(file) = program.get_source_file(&reference.resolved_file_name) {
                return Some(crate::findallreferences::RefInfo {
                    reference: Some(type_reference_directive),
                    file_name: program_file_name(program, file),
                    file: Some(file),
                    unverified: false,
                });
            }
        }
        return None;
    }

    let lib_reference_directives = nodes[source_file]
        .as_source_file()
        .lib_reference_directives
        .clone();
    if let Some(lib_reference_directive) =
        find_reference_in_position(&lib_reference_directives, position)
    {
        if let Some(file) = program.get_lib_file_from_reference(&lib_reference_directive) {
            return Some(crate::findallreferences::RefInfo {
                reference: Some(lib_reference_directive),
                file_name: program_file_name(program, file),
                file: Some(file),
                unverified: false,
            });
        }
        return None;
    }

    if nodes[source_file].as_source_file().imports().is_empty()
        && nodes[source_file]
            .as_source_file()
            .module_augmentations
            .is_empty()
    {
        return None;
    }

    let node = tsc_astnav::tokens::get_touching_token(nodes, source_file, position)?;
    if !is_module_specifier_like(node, nodes)
        || !tspath::is_external_module_name_relative(&nodes[node].text(nodes))
    {
        return None;
    }

    if let Some(resolution) = program.get_resolved_module_from_module_specifier(source_file, node) {
        let verified_file_name = resolution.resolved_file_name.clone();
        let mut file_name = verified_file_name.clone();
        if file_name.as_string().is_empty() {
            file_name = nodes[source_file]
                .as_source_file()
                .file_name()
                .directory()
                .resolve_file(&nodes[node].text(nodes));
        }
        return Some(crate::findallreferences::RefInfo {
            file: program.get_source_file(&file_name),
            file_name,
            reference: None,
            unverified: !verified_file_name.as_string().is_empty(),
        });
    }

    None
}

fn program_file_name(program: &Program, file: NodeId) -> RootedFilePath {
    program.arena_of(file)[file]
        .as_source_file()
        .file_name()
        .clone()
}

/// `getContextualTypeFromParent` — `node` is `*ast.Expression`.
pub(crate) fn get_contextual_type_from_parent(
    node: NodeId,
    type_checker: &mut Checker,
    context_flags: ContextFlags,
) -> Option<TypeId> {
    let parent = {
        let program = type_checker.program.clone().expect("program");
        let nodes = program.nodes(node.file_index());
        nodes[node]
            .parent
            .and_then(|p| ast::walk_up_parenthesized_expressions(p, &nodes))
    };
    let parent = parent?;
    let parent_kind = {
        let program = type_checker.program.clone().expect("program");
        let nodes = program.nodes(parent.file_index());
        nodes[parent].kind
    };
    match parent_kind {
        Kind::NewExpression => type_checker.get_contextual_type_api(parent, context_flags),
        Kind::BinaryExpression => {
            let (operator_kind, left, right) = {
                let program = type_checker.program.clone().expect("program");
                let nodes = program.nodes(parent.file_index());
                let bin = nodes[parent].as_binary_expression();
                (
                    bin.operator_token.map(|t| nodes[t].kind),
                    bin.left,
                    bin.right,
                )
            };
            if operator_kind.is_some_and(|k| crate::completions::is_equality_operator_kind(k)) {
                return Some(type_checker.get_type_at_location(if Some(node) == right {
                    left.expect("left")
                } else {
                    right.expect("right")
                }));
            }
            type_checker.get_contextual_type_api(node, context_flags)
        }
        Kind::CaseClause => Some(crate::completions::get_switched_type(parent, type_checker)),
        _ => type_checker.get_contextual_type_api(node, context_flags),
    }
}

/// `getContextualTypeFromParentOrAncestorTypeNode` — `node` is
/// `*ast.Expression`.
pub(crate) fn get_contextual_type_from_parent_or_ancestor_type_node(
    node: NodeId,
    type_checker: &mut Checker,
) -> Option<TypeId> {
    {
        let program = type_checker.program.clone().expect("program");
        let nodes = program.nodes(node.file_index());
        if nodes[node].flags & NodeFlags::JSDOC != NodeFlags::NONE
            && nodes[node].flags & NodeFlags::JAVA_SCRIPT_FILE == NodeFlags::NONE
        {
            return None;
        }
    }

    if let Some(contextual_type) =
        get_contextual_type_from_parent(node, type_checker, ContextFlags::NONE)
    {
        return Some(contextual_type);
    }

    if let Some(ancestor_type_node) = get_ancestor_type_node(node, type_checker) {
        return Some(type_checker.get_type_at_location(ancestor_type_node));
    }

    None
}

/// `getAncestorTypeNode`.
pub(crate) fn get_ancestor_type_node(node: NodeId, type_checker: &mut Checker) -> Option<NodeId> {
    let program = type_checker.program.clone().expect("program");
    let nodes = program.nodes(node.file_index());
    let mut last_type_node = None;
    ast::find_ancestor(Some(node), &nodes, &mut |n, ns| {
        if ast::is_type_node(n) {
            last_type_node = Some(n.id);
        }
        !(n.parent.is_some_and(|p| ast::is_qualified_name(&ns[p]))
            || n.parent.is_some_and(|p| ast::is_type_node(&ns[p]))
            || n.parent.is_some_and(|p| ast::is_type_element(&ns[p])))
    });
    last_type_node
}

/// `isSourceFileWithGlobalExports`.
pub(crate) fn is_source_file_with_global_exports(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| {
        ast::is_source_file(&nodes[n]) && !nodes[n].as_source_file().global_exports.is_empty()
    })
}
