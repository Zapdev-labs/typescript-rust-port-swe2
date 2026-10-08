// Ported from tsc/internal/scanner/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `node *ast.Node` parameters become `(NodeId, &[Node])` arena pairs.
// - Text-returning functions return `String`/`Cow<str>`; `Cow::Borrowed`
//   covers Go's "substring of the source text" fast path.
// - `utf8.DecodeRuneInString` decoding uses `decode_rune_in_string` from
//   `scanner.rs` (the strict RFC-3629 decoder matching Go semantics).

use std::borrow::Cow;

use tsc_ast::ast_generated::{
    Identifier, SourceFile, is_identifier, is_js_doc_type_expression, is_string_literal,
};
use tsc_ast::kind_generated::Kind;
use tsc_ast::nodeflags::NodeFlags;
use tsc_ast::tokenflags::TokenFlags;
use tsc_ast::utilities::{get_source_file_of_node, is_type_node, node_is_missing};
use tsc_ast::{Node, NodeId, NodeList};
use tsc_core::core::compute_ecma_line_starts;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::NewLineKind;
use tsc_debug as debug;
use tsc_stringutil as stringutil;

use crate::scanner::{
    decode_rune_in_string, is_identifier_part_ex, is_identifier_start, skip_trivia, text_to_keyword,
};

/// `func tokenIsIdentifierOrKeyword(token ast.Kind) bool`
pub(crate) fn token_is_identifier_or_keyword(token: Kind) -> bool {
    token >= Kind::Identifier
}

/// `func IdentifierToKeywordKind(node *ast.Identifier) ast.Kind`
///
/// `Kind::Unknown` for a non-keyword text, like Go's zero value on a miss.
pub fn identifier_to_keyword_kind(node: &Identifier) -> Kind {
    text_to_keyword(node.text.as_bytes()).unwrap_or(Kind::Unknown)
}

/// `func GetSourceTextOfNodeFromSourceFile(sourceFile *ast.SourceFile, node *ast.Node, includeTrivia bool) string`
pub fn get_source_text_of_node_from_source_file<'a>(
    source_file: &'a SourceFile,
    node: NodeId,
    include_trivia: bool,
    nodes: &[Node],
) -> Cow<'a, str> {
    get_text_of_node_from_source_text(&source_file.text, node, include_trivia, nodes)
}

/// `func isJSDocTypeExpressionOrChild(node *ast.Node) bool`
pub(crate) fn is_jsdoc_type_expression_or_child(node: NodeId, nodes: &[Node]) -> bool {
    if is_js_doc_type_expression(&nodes[node]) {
        return true;
    }
    if !nodes[node]
        .flags
        .intersects(NodeFlags::JSDOC | NodeFlags::REPARSED)
    {
        return false;
    }
    let mut current = Some(node);
    while let Some(cur) = current {
        if is_type_node(&nodes[cur]) {
            return true;
        }
        current = nodes[cur].parent;
    }
    false
}

/// `func normalizeJSDocTypeSourceText(text string) string`
pub(crate) fn normalize_jsdoc_type_source_text(text: &str) -> String {
    let line_starts = compute_ecma_line_starts(text);
    if line_starts.len() == 1 {
        return strip_leading_jsdoc_comment(text).to_string();
    }

    let mut result = String::with_capacity(text.len());
    let new_line = NewLineKind::LF.get_new_line_character();
    for (i, &line_start) in line_starts.iter().enumerate() {
        if i > 0 {
            result.push_str(new_line);
        }
        let mut line_end = text.len();
        if i + 1 < line_starts.len() {
            line_end = line_starts[i + 1] as usize;
        }
        // `strings.TrimRightFunc(line, stringutil.IsLineBreak)`
        let line = text[line_start as usize..line_end]
            .trim_end_matches(|c: char| stringutil::is_line_break(c));
        result.push_str(strip_leading_jsdoc_comment(line));
    }
    result
}

/// `func stripLeadingJSDocComment(line string) string`
pub(crate) fn strip_leading_jsdoc_comment(line: &str) -> &str {
    let line = line.trim_start_matches(|c: char| stringutil::is_white_space_like(c));
    let line = line.strip_prefix('*').unwrap_or(line);
    line.trim_start_matches(|c: char| stringutil::is_white_space_like(c))
}

/// `func GetTextOfNodeFromSourceText(sourceText string, node *ast.Node, includeTrivia bool) string`
pub fn get_text_of_node_from_source_text<'a>(
    source_text: &'a str,
    node: NodeId,
    include_trivia: bool,
    nodes: &[Node],
) -> Cow<'a, str> {
    if node_is_missing(Some(node), nodes) {
        return Cow::Borrowed("");
    }
    let mut pos = nodes[node].pos();
    if !include_trivia {
        pos = skip_trivia(source_text, pos);
    }
    let text = &source_text[pos as usize..nodes[node].end() as usize];
    let text: Cow<'a, str> = if is_jsdoc_type_expression_or_child(node, nodes) {
        Cow::Owned(normalize_jsdoc_type_source_text(text))
    } else {
        Cow::Borrowed(text)
    };
    if nodes[node]
        .flags
        .intersects(NodeFlags::REPARSER_TRANSFORMED_LITERAL)
    {
        // This is similar to `getLiteralTextOfNode` in the printer, but without the context of an `emitContext` to provide overrides
        let text = text.into_owned();
        if is_string_literal(&nodes[node]) {
            if nodes[node]
                .as_string_literal()
                .literal_expression_base
                .literal_like_node_base
                .token_flags
                .intersects(TokenFlags::SINGLE_QUOTE)
            {
                return Cow::Owned(format!("'{text}'"));
            }
            return Cow::Owned(format!("\"{text}\""));
        } else if is_identifier(&nodes[node]) {
            return Cow::Owned(nodes[node].text(nodes).into_owned());
        }
        // Only the above node kinds are currently transformed into one another by the reparser, requiring the textual remapping.
        // (Any reamppings done by emit transforms are handled by `getLiteralTextOfNode` in the printer)
        // Fail on any other kinds.
        // PORT: `Node` doesn't implement tsc_debug's `KindString` trait, so
        // the macro can't take it — call the underlying function directly.
        debug::fail_bad_syntax_kind(
            nodes[node].kind_string().to_string(),
            Some("Unexpected reparser-transformed node kind".to_string()),
        );
    }
    text
}

/// `func GetTextOfNode(node *ast.Node) string`
pub fn get_text_of_node(node: NodeId, nodes: &[Node]) -> String {
    let source_file = get_source_file_of_node(Some(node), nodes);
    // Go dereferences the nil `*ast.SourceFile` here when the node has no
    // source file; `expect` preserves the panic.
    let source_file = nodes[source_file.expect("node has no source file")].as_source_file();
    get_source_text_of_node_from_source_file(source_file, node, false, nodes).into_owned()
}

/// `func GetTextOfJSDocComment(comment *ast.NodeList) string`
pub fn get_text_of_jsdoc_comment(comment: Option<&NodeList>, nodes: &[Node]) -> String {
    let Some(comment) = comment else {
        return String::new();
    };
    let mut b = String::new();
    for &n in comment.nodes.iter() {
        match nodes[n].kind {
            Kind::JSDocText => {
                b.push_str(&nodes[n].text(nodes));
            }
            Kind::JSDocLink | Kind::JSDocLinkCode | Kind::JSDocLinkPlain => {
                b.push_str(&get_text_of_node(n, nodes));
            }
            _ => {}
        }
    }
    // `strings.TrimRightFunc(b.String(), unicode.IsSpace)` — Go's
    // `unicode.IsSpace` is the Unicode White_Space property, matching
    // `char::is_whitespace`.
    b.trim_end_matches(char::is_whitespace).to_string()
}

/// `func DeclarationNameToString(name *ast.Node) string`
pub fn declaration_name_to_string(name: Option<NodeId>, nodes: &[Node]) -> String {
    let Some(name) = name else {
        return "(Missing)".to_string();
    };
    if nodes[name].pos() == nodes[name].end() {
        return "(Missing)".to_string();
    }
    get_text_of_node(name, nodes)
}

/// `func IsIdentifierText(name string, languageVariant core.LanguageVariant) bool`
pub fn is_identifier_text(name: &str, language_variant: LanguageVariant) -> bool {
    let bytes = name.as_bytes();
    let (ch, size) = decode_rune_in_string(bytes);
    if !is_identifier_start(ch) {
        return false;
    }
    let mut i = size;
    while i < bytes.len() {
        let (ch, size) = decode_rune_in_string(&bytes[i..]);
        if !is_identifier_part_ex(ch, language_variant) {
            return false;
        }
        i += size;
    }
    true
}

/// `func IsIntrinsicJsxName(name string) bool`
pub fn is_intrinsic_jsx_name(name: &str) -> bool {
    !name.is_empty() && (name.as_bytes()[0].is_ascii_lowercase() || name.contains('-'))
}
