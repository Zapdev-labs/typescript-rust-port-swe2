// Ported from tsc/internal/printer/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Cow;
use std::fmt::Write;

use tsc_ast::{self as ast, CommentRange, Kind, Node, NodeId};
use tsc_core::core::UTF16Offset;
use tsc_core::text::{TextPos, TextRange};
use tsc_scanner::scanner::SkipTriviaOptions;
use tsc_stringutil as stringutil;

use crate::emit_context::Shared;
use crate::text_writer::get_default_indent_size;

/// `type getLiteralTextFlags int`
pub(crate) type GetLiteralTextFlags = i32;

pub(crate) const GET_LITERAL_TEXT_FLAGS_NONE: GetLiteralTextFlags = 0;
pub(crate) const GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE: GetLiteralTextFlags = 1 << 0;
pub(crate) const GET_LITERAL_TEXT_FLAGS_JSX_ATTRIBUTE_ESCAPE: GetLiteralTextFlags = 1 << 1;
pub(crate) const GET_LITERAL_TEXT_FLAGS_TERMINATE_UNTERMINATED_LITERALS: GetLiteralTextFlags =
    1 << 2;
pub(crate) const GET_LITERAL_TEXT_FLAGS_ALLOW_NUMERIC_SEPARATOR: GetLiteralTextFlags = 1 << 3;

/// `type QuoteChar rune`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum QuoteChar {
    /// `QuoteCharSingleQuote`
    SingleQuote,
    /// `QuoteCharDoubleQuote`
    DoubleQuote,
    /// `QuoteCharBacktick`
    Backtick,
}

impl QuoteChar {
    pub(crate) fn char(self) -> char {
        match self {
            QuoteChar::SingleQuote => '\'',
            QuoteChar::DoubleQuote => '"',
            QuoteChar::Backtick => '`',
        }
    }
}

/// `jsxEscapedCharsMap`
fn jsx_escaped_chars_map(ch: i32) -> Option<&'static str> {
    match ch {
        0x22 => Some("&quot;"),
        0x27 => Some("&apos;"),
        _ => None,
    }
}

/// `escapedCharsMap`
fn escaped_chars_map(ch: i32) -> Option<&'static str> {
    match ch {
        0x09 => Some("\\t"),
        0x0B => Some("\\v"),
        0x0C => Some("\\f"),
        0x08 => Some("\\b"),
        0x0D => Some("\\r"),
        0x0A => Some("\\n"),
        0x5C => Some("\\\\"),
        0x22 => Some("\\\""),
        0x27 => Some("\\'"),
        0x60 => Some("\\`"),
        0x24 => Some("\\$"), // when quoteChar == '`'
        0x2028 => Some("\\u2028"), // lineSeparator
        0x2029 => Some("\\u2029"), // paragraphSeparator
        0x85 => Some("\\u0085"), // nextLine
        _ => None,
    }
}

/// `encodeJsxCharacterEntity`
fn encode_jsx_character_entity(b: &mut String, char_code: i32) {
    let hex_char_code = format!("{:X}", char_code);
    b.push_str("&#x");
    b.push_str(&hex_char_code);
    b.push(';');
}

/// `encodeUtf16EscapeSequence`
fn encode_utf16_escape_sequence(b: &mut String, char_code: i32) {
    let hex_char_code = format!("{:X}", char_code as u32);
    b.push_str("\\u");
    for _ in hex_char_code.len()..4 {
        b.push('0');
    }
    b.push_str(&hex_char_code);
}

// Based heavily on the abstract 'Quote'/'QuoteJSONString' operation from ECMA-262 (24.3.2.2),
// but augmented for a few select characters (e.g. lineSeparator, paragraphSeparator, nextLine)
// Note that this doesn't actually wrap the input in double quotes.
//
/// `escapeStringWorker`
pub(crate) fn escape_string_worker(
    s: &str,
    quote_char: QuoteChar,
    flags: GetLiteralTextFlags,
    b: &mut String,
) {
    let bytes = s.as_bytes();
    let mut pos = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        let (ch, mut size) = stringutil::decode_js_string_rune(&bytes[i..]);

        let mut escape = false;
        if (0xD800..=0xDFFF).contains(&ch) {
            escape = true;
        } else if ch == 0xFFFD && size == 1 {
            // A stray byte that is not valid UTF-8 (for example, a fragment of a
            // surrogate sentinel left behind by code that sliced the string by
            // byte). Escape it as the Unicode replacement character so the output
            // is always well-formed rather than containing raw invalid bytes.
            escape = true;
        }

        // This consists of the first 19 unprintable ASCII characters, canonical escapes, lineSeparator,
        // paragraphSeparator, and nextLine. The latter three are just desirable to suppress new lines in
        // the language service. These characters should be escaped when printing, and if any characters are added,
        // `escapedCharsMap` and/or `jsxEscapedCharsMap` must be updated. Note that this *does not* include the 'delete'
        // character. There is no reason for this other than that JSON.stringify does not handle it either.
        match ch {
            0x5C /* '\\' */ => {
                if flags & GET_LITERAL_TEXT_FLAGS_JSX_ATTRIBUTE_ESCAPE == 0 {
                    escape = true;
                }
            }
            0x24 /* '$' */ => {
                if quote_char == QuoteChar::Backtick && i + 1 < bytes.len() && bytes[i + 1] == b'{' {
                    escape = true;
                }
            }
            c if c == quote_char.char() as i32 || c == 0x2028 || c == 0x2029 || c == 0x85 || c == 0x0D => {
                escape = true;
            }
            0x0A /* '\n' */ => {
                if quote_char != QuoteChar::Backtick {
                    // Template strings preserve simple LF newlines, still encode CRLF (or CR).
                    escape = true;
                }
            }
            _ => {
                if ch <= 0x1F
                    || flags & GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE == 0 && ch > 0x7F
                {
                    escape = true;
                }
            }
        }

        if escape {
            if pos < i {
                // Write string up to this point
                b.push_str(&s[pos..i]);
            }

            if flags & GET_LITERAL_TEXT_FLAGS_JSX_ATTRIBUTE_ESCAPE != 0 {
                if ch == 0 {
                    b.push_str("&#0;");
                } else if let Some(m) = jsx_escaped_chars_map(ch) {
                    b.push_str(m);
                } else {
                    encode_jsx_character_entity(b, ch);
                }
            } else if ch == 0x0D && quote_char == QuoteChar::Backtick && i + 1 < bytes.len() && bytes[i + 1] == b'\n' {
                // Template strings preserve simple LF newlines, but still must escape CRLF. Left alone, the
                // above cases for `\r` and `\n` would inadvertently escape CRLF as two independent characters.
                size += 1;
                b.push_str("\\r\\n");
            } else if ch > 0xFFFF {
                // encode as surrogate pair
                let ch = ch - 0x10000;
                encode_utf16_escape_sequence(b, ((ch & 0b11111111110000000000) >> 10) + 0xD800);
                encode_utf16_escape_sequence(b, (ch & 0b00000000001111111111) + 0xDC00);
            } else if (0xD800..=0xDFFF).contains(&ch) {
                encode_utf16_escape_sequence(b, ch);
            } else if ch == 0 {
                if i + 1 < bytes.len() && stringutil::is_digit(bytes[i + 1] as char) {
                    // If the null character is followed by digits, print as a hex escape to prevent the result from
                    // parsing as an octal (which is forbidden in strict mode)
                    b.push_str("\\x00");
                } else {
                    // Otherwise, keep printing a literal \0 for the null character
                    b.push_str("\\0");
                }
            } else if let Some(m) = escaped_chars_map(ch) {
                b.push_str(m);
            } else {
                encode_utf16_escape_sequence(b, ch);
            }
            pos = i + size;
        }

        i += size;
    }

    if pos < i {
        b.push_str(&s[pos..]);
    }
}

/// `EscapeString`
pub fn escape_string(s: &str, quote_char: QuoteChar) -> String {
    let mut b = String::with_capacity(s.len() + 2);
    escape_string_worker(
        s,
        quote_char,
        GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE,
        &mut b,
    );
    b
}

/// `escapeNonAsciiString`
pub(crate) fn escape_non_ascii_string(s: &str, quote_char: QuoteChar) -> String {
    let mut b = String::with_capacity(s.len() + 2);
    escape_string_worker(s, quote_char, GET_LITERAL_TEXT_FLAGS_NONE, &mut b);
    b
}

/// `escapeJsxAttributeString`
pub(crate) fn escape_jsx_attribute_string(s: &str, quote_char: QuoteChar) -> String {
    let mut b = String::with_capacity(s.len() + 2);
    escape_string_worker(
        s,
        quote_char,
        GET_LITERAL_TEXT_FLAGS_JSX_ATTRIBUTE_ESCAPE | GET_LITERAL_TEXT_FLAGS_NEVER_ASCII_ESCAPE,
        &mut b,
    );
    b
}

/// `canUseOriginalText`
fn can_use_original_text(nodes: &[Node], node: NodeId, flags: GetLiteralTextFlags) -> bool {
    // A synthetic node has no original text, nor does a node without a parent as we would be unable to find the
    // containing SourceFile. We also cannot use the original text if the literal was unterminated and the caller has
    // requested proper termination of unterminated literals
    if ast::node_is_synthesized(&nodes[node])
        || nodes[node].parent.is_none()
        || flags & GET_LITERAL_TEXT_FLAGS_TERMINATE_UNTERMINATED_LITERALS != 0
            && ast::is_unterminated_literal(&nodes[node])
    {
        return false;
    }

    if nodes[node].kind == Kind::NumericLiteral {
        let token_flags = nodes[node].as_numeric_literal()
            .literal_expression_base
            .literal_like_node_base
            .token_flags;
        // For a numeric literal, we cannot use the original text if the original text was an invalid literal
        if token_flags.0 & ast::TokenFlags::IS_INVALID.0 != 0 {
            return false;
        }
        // We also cannot use the original text if the literal contains numeric separators, but numeric separators
        // are not permitted
        if token_flags.0 & ast::TokenFlags::CONTAINS_SEPARATOR.0 != 0 {
            return flags & GET_LITERAL_TEXT_FLAGS_ALLOW_NUMERIC_SEPARATOR != 0;
        }
    }

    // Finally, we do not use the original text of a BigInt literal
    // TODO(rbuckton): The reason as to why we do not use the original text for bigints is not mentioned in the
    // original compiler source. It could be that this is no longer necessary, in which case bigint literals should
    // use the same code path as numeric literals, above
    nodes[node].kind != Kind::BigIntLiteral
}

/// `getLiteralText`
pub(crate) fn get_literal_text(
    nodes: &[Node],
    node: NodeId,
    source_file: Option<NodeId>,
    flags: GetLiteralTextFlags,
) -> String {
    // If we don't need to downlevel and we can reach the original source text using
    // the node's parent reference, then simply get the text as it was originally written.
    if let Some(source_file) = source_file
        && can_use_original_text(nodes, node, flags)
    {
        return tsc_scanner::utilities::get_source_text_of_node_from_source_file(
            nodes[source_file].as_source_file(),
            node,
            false, /*includeTrivia*/
            nodes,
        )
        .into_owned();
    }

    // If we can't reach the original source text, use the canonical form if it's a number,
    // or a (possibly escaped) quoted form of the original text if it's string-like.
    match nodes[node].kind {
        Kind::StringLiteral => {
            let mut b = String::new();
            let quote_char =
                if nodes[node]
                    .as_string_literal()
                    .literal_expression_base
                    .literal_like_node_base
                    .token_flags
                    .0
                    & ast::TokenFlags::SINGLE_QUOTE.0
                    != 0
                {
                    QuoteChar::SingleQuote
                } else {
                    QuoteChar::DoubleQuote
                };

            let text = nodes[node].text(nodes).into_owned();

            // Write leading quote character
            b.reserve(text.len() + 2);
            b.push(quote_char.char());

            // Write text
            escape_string_worker(&text, quote_char, flags, &mut b);

            // Write trailing quote character
            b.push(quote_char.char());
            b
        }

        Kind::NoSubstitutionTemplateLiteral
        | Kind::TemplateHead
        | Kind::TemplateMiddle
        | Kind::TemplateTail => {
            // If a NoSubstitutionTemplateLiteral appears to have a substitution in it, the original text
            // had to include a backslash: `not \${a} substitution`.
            let mut b = String::new();
            let text = nodes[node].text(nodes).into_owned();
            let raw_text = nodes[node]
                .template_literal_like_data()
                .map(|d| d.raw_text.clone())
                .unwrap_or_default();
            let raw = !raw_text.is_empty() || text.is_empty();

            let text_len = if raw { raw_text.len() } else { text.len() };

            // Write leading quote character
            match nodes[node].kind {
                Kind::NoSubstitutionTemplateLiteral => {
                    b.reserve(2 + text_len);
                    b.push('`');
                }
                Kind::TemplateHead => {
                    b.reserve(3 + text_len);
                    b.push('`');
                }
                Kind::TemplateMiddle => {
                    b.reserve(3 + text_len);
                    b.push('}');
                }
                Kind::TemplateTail => {
                    b.reserve(2 + text_len);
                    b.push('}');
                }
                _ => unreachable!(),
            }

            // Write text
            if !raw_text.is_empty() || text.is_empty() {
                // If rawText is set, it is expected to be valid.
                b.push_str(&raw_text);
            } else {
                escape_string_worker(&text, QuoteChar::Backtick, flags, &mut b);
            }

            // Write trailing quote character
            match nodes[node].kind {
                Kind::NoSubstitutionTemplateLiteral => b.push('`'),
                Kind::TemplateHead => b.push_str("${"),
                Kind::TemplateMiddle => b.push_str("${"),
                Kind::TemplateTail => b.push('`'),
                _ => unreachable!(),
            }
            b
        }

        Kind::NumericLiteral | Kind::BigIntLiteral => nodes[node].text(nodes).into_owned(),

        Kind::RegularExpressionLiteral => {
            if flags & GET_LITERAL_TEXT_FLAGS_TERMINATE_UNTERMINATED_LITERALS != 0
                && ast::is_unterminated_literal(&nodes[node])
            {
                let mut b = String::new();
                let text = nodes[node].text(nodes).into_owned();
                if text.ends_with('\\') {
                    b.reserve(2 + text.len());
                    b.push_str(&text);
                    b.push_str(" /");
                } else {
                    b.reserve(1 + text.len());
                    b.push_str(&text);
                    b.push('/');
                }
                return b;
            }
            nodes[node].text(nodes).into_owned()
        }

        _ => panic!("Unsupported LiteralLikeNode"),
    }
}

/// `isNotPrologueDirective`
pub(crate) fn is_not_prologue_directive(nodes: &[Node], node: NodeId) -> bool {
    !ast::is_prologue_directive(&nodes[node], nodes)
}

/// `RangeIsOnSingleLine`
pub(crate) fn range_is_on_single_line(
    r: TextRange,
    source_file: &ast::SourceFile,
) -> bool {
    range_start_is_on_same_line_as_range_end(r, r, source_file)
}

/// `RangeStartPositionsAreOnSameLine`
pub(crate) fn range_start_positions_are_on_same_line(
    range1: TextRange,
    range2: TextRange,
    source_file: &ast::SourceFile,
) -> bool {
    positions_are_on_same_line(
        get_start_position_of_range(range1, source_file, false /*includeComments*/),
        get_start_position_of_range(range2, source_file, false /*includeComments*/),
        source_file,
    )
}

/// `rangeEndPositionsAreOnSameLine`
pub(crate) fn range_end_positions_are_on_same_line(
    range1: TextRange,
    range2: TextRange,
    source_file: &ast::SourceFile,
) -> bool {
    positions_are_on_same_line(range1.end(), range2.end(), source_file)
}

/// `rangeStartIsOnSameLineAsRangeEnd`
pub(crate) fn range_start_is_on_same_line_as_range_end(
    range1: TextRange,
    range2: TextRange,
    source_file: &ast::SourceFile,
) -> bool {
    positions_are_on_same_line(
        get_start_position_of_range(range1, source_file, false /*includeComments*/),
        range2.end(),
        source_file,
    )
}

/// `rangeEndIsOnSameLineAsRangeStart`
pub(crate) fn range_end_is_on_same_line_as_range_start(
    range1: TextRange,
    range2: TextRange,
    source_file: &ast::SourceFile,
) -> bool {
    positions_are_on_same_line(
        range1.end(),
        get_start_position_of_range(range2, source_file, false /*includeComments*/),
        source_file,
    )
}

/// `getStartPositionOfRange`
pub(crate) fn get_start_position_of_range(
    r: TextRange,
    source_file: &ast::SourceFile,
    include_comments: bool,
) -> i32 {
    if ast::position_is_synthesized(r.pos()) {
        return -1;
    }
    tsc_scanner::scanner::skip_trivia_ex(
        source_file.text(),
        r.pos(),
        Some(&SkipTriviaOptions {
            stop_at_comments: include_comments,
            ..Default::default()
        }),
    )
}

/// `PositionsAreOnSameLine`
pub(crate) fn positions_are_on_same_line(
    pos1: i32,
    pos2: i32,
    source_file: &ast::SourceFile,
) -> bool {
    get_lines_between_positions(source_file, pos1, pos2) == 0
}

/// `GetLinesBetweenPositions`
pub(crate) fn get_lines_between_positions(
    source_file: &ast::SourceFile,
    pos1: i32,
    pos2: i32,
) -> i32 {
    if pos1 == pos2 {
        return 0;
    }
    let line_starts = tsc_ast::SourceFileLike::ecma_line_map(source_file);
    let lower = if pos1 < pos2 { pos1 } else { pos2 };
    let is_negative = lower == pos2;
    let upper = if is_negative { pos1 } else { pos2 };
    let lower_line = tsc_scanner::scanner::compute_line_of_position(line_starts, lower);
    let upper_line =
        lower_line + tsc_scanner::scanner::compute_line_of_position(&line_starts[lower_line as usize..], upper);
    if is_negative {
        lower_line - upper_line
    } else {
        upper_line - lower_line
    }
}

/// `getLinesBetweenRangeEndAndRangeStart`
pub(crate) fn get_lines_between_range_end_and_range_start(
    range1: TextRange,
    range2: TextRange,
    source_file: &ast::SourceFile,
    include_second_range_comments: bool,
) -> i32 {
    let range2_start =
        get_start_position_of_range(range2, source_file, include_second_range_comments);
    get_lines_between_positions(source_file, range1.end(), range2_start)
}

/// `getLinesBetweenPositionAndPrecedingNonWhitespaceCharacter`
pub(crate) fn get_lines_between_position_and_preceding_non_whitespace_character(
    pos: i32,
    stop_pos: i32,
    source_file: &ast::SourceFile,
    include_comments: bool,
) -> i32 {
    let start_pos = tsc_scanner::scanner::skip_trivia_ex(
        source_file.text(),
        pos,
        Some(&SkipTriviaOptions {
            stop_at_comments: include_comments,
            ..Default::default()
        }),
    );
    let prev_pos = get_previous_non_whitespace_position(start_pos, stop_pos, source_file);
    get_lines_between_positions(
        source_file,
        if prev_pos >= 0 { prev_pos } else { stop_pos },
        start_pos,
    )
}

/// `getLinesBetweenPositionAndNextNonWhitespaceCharacter`
pub(crate) fn get_lines_between_position_and_next_non_whitespace_character(
    pos: i32,
    stop_pos: i32,
    source_file: &ast::SourceFile,
    include_comments: bool,
) -> i32 {
    let next_pos = tsc_scanner::scanner::skip_trivia_ex(
        source_file.text(),
        pos,
        Some(&SkipTriviaOptions {
            stop_at_comments: include_comments,
            ..Default::default()
        }),
    );
    get_lines_between_positions(source_file, pos, if stop_pos < next_pos { stop_pos } else { next_pos })
}

/// `getPreviousNonWhitespacePosition`
fn get_previous_non_whitespace_position(
    pos: i32,
    stop_pos: i32,
    source_file: &ast::SourceFile,
) -> i32 {
    let text = source_file.text().as_bytes();
    let mut pos = pos;
    while pos >= stop_pos {
        if !stringutil::is_white_space_like(text[pos as usize] as char) {
            return pos;
        }
        pos -= 1;
    }
    -1
}

/// `siblingNodePositionsAreComparable`
///
/// PORT: takes `&Shared` (the emit-context tables) plus the arena `nodes` since
/// `MostOriginal` and `parent` lookups both need them.
pub(crate) fn sibling_node_positions_are_comparable(
    shared: &Shared,
    nodes: &[Node],
    previous_node: NodeId,
    next_node: NodeId,
) -> bool {
    if nodes[next_node].pos() < nodes[previous_node].end() {
        return false;
    }

    let previous_node = most_original_shared(shared, previous_node);
    let next_node = most_original_shared(shared, next_node);
    let parent = nodes[previous_node].parent;
    if parent.is_none() || parent != nodes[next_node].parent {
        return false;
    }

    if let Some(parent_node_array) = get_containing_node_array(nodes, previous_node) {
        let prev_node_index = parent_node_array
            .iter()
            .position(|&n| n == previous_node);
        return prev_node_index.is_some_and(|i| {
            parent_node_array
                .iter()
                .position(|&n| n == next_node)
                == Some(i + 1)
        });
    }

    false
}

/// `MostOriginal` on the shared tables.
pub(crate) fn most_original_shared(shared: &Shared, node: NodeId) -> NodeId {
    let mut node = node;
    while let Some(original) = shared.borrow().original.get(&node).copied() {
        node = original;
    }
    node
}

/// `getContainingNodeArray` — returns the containing node array's `nodes`
/// slice, or `None`.
///
/// PORT: returns `Option<&[NodeId]>` rather than `*ast.NodeList`; the callers
/// only use `.Nodes` for index lookups.
pub(crate) fn get_containing_node_array<'a>(
    nodes: &'a [Node],
    node: NodeId,
) -> Option<&'a [NodeId]> {
    let parent_id = nodes[node].parent?;
    let parent = &nodes[parent_id];

    match nodes[node].kind {
        Kind::TypeParameter => {
            if ast::is_function_like(Some(parent_id), nodes)
                || ast::is_class_like(Some(parent_id), nodes)
                || ast::is_interface_declaration(parent)
                || ast::is_type_alias_declaration(parent)
                || ast::is_js_type_alias_declaration(parent)
            {
                return parent.type_parameter_list().map(|l| l.nodes());
            } else if ast::is_infer_type_node(parent) {
                // infer type nodes have no associated type parameter list
            } else {
                panic!("Unexpected TypeParameter parent: {:?}", parent.kind);
            }
        }

        Kind::Parameter => {
            return nodes[node]
                .parent
                .and_then(|p| nodes[p].function_like_data())
                .and_then(|d| d.parameters.as_ref())
                .map(|l| l.nodes());
        }
        Kind::TemplateLiteralTypeSpan => {
            return nodes[node]
                .parent
                .map(|p| nodes[p].as_template_literal_type_node())
                .and_then(|d| d.template_spans.as_ref())
                .map(|l| l.nodes());
        }
        Kind::TemplateSpan => {
            return nodes[node]
                .parent
                .map(|p| nodes[p].as_template_expression())
                .and_then(|d| d.template_spans.as_ref())
                .map(|l| l.nodes());
        }
        Kind::Decorator => {
            if can_have_decorators(&nodes[nodes[node].parent.unwrap()])
                && let Some(modifiers) = nodes[nodes[node].parent.unwrap()].modifiers()
            {
                return Some(&modifiers.nodes);
            }
            return None;
        }
        Kind::HeritageClause => {
            if ast::is_class_like(nodes[node].parent, nodes) {
                return nodes[node]
                    .parent
                    .and_then(|p| nodes[p].class_like_data())
                    .and_then(|d| d.heritage_clauses.as_ref())
                    .map(|l| l.nodes());
            } else {
                return nodes[node]
                    .parent
                    .map(|p| nodes[p].as_interface_declaration())
                    .and_then(|d| d.heritage_clauses.as_ref())
                    .map(|l| l.nodes());
            }
        }
        _ => {}
    }

    // TODO(rbuckton)
    // if ast.IsJSDocTag(node) {
    //     if ast.IsJSDocTypeLiteral(node.parent) {
    //         return nil
    //      }
    //      return node.parent.tags
    // }

    match parent.kind {
        Kind::TypeLiteral | Kind::InterfaceDeclaration => {
            if ast::is_type_element(&nodes[node]) {
                return parent.member_list().map(|l| l.nodes());
            }
        }
        Kind::UnionType => {
            return parent.as_union_type_node().union_or_intersection_type_node_base.types.as_ref().map(|l| l.nodes());
        }
        Kind::IntersectionType => {
            return parent
                .as_intersection_type_node()
                .union_or_intersection_type_node_base
                .types
                .as_ref()
                .map(|l| l.nodes());
        }
        Kind::ArrayLiteralExpression
        | Kind::TupleType
        | Kind::NamedImports
        | Kind::NamedExports => {
            return parent.element_list().map(|l| l.nodes());
        }
        Kind::ObjectLiteralExpression | Kind::JsxAttributes => {
            return parent.property_list().map(|l| l.nodes());
        }
        Kind::CallExpression => {
            let p = parent.as_call_expression();
            if ast::is_type_node(&nodes[node]) {
                return p.type_arguments.as_ref().map(|l| l.nodes());
            } else if Some(node) != p.expression {
                return p.arguments.as_ref().map(|l| l.nodes());
            }
        }
        Kind::NewExpression => {
            let p = parent.as_new_expression();
            if ast::is_type_node(&nodes[node]) {
                return p.type_arguments.as_ref().map(|l| l.nodes());
            } else if Some(node) != p.expression {
                return p.arguments.as_ref().map(|l| l.nodes());
            }
        }
        Kind::JsxElement | Kind::JsxFragment => {
            if ast::is_jsx_child(&nodes[node]) {
                return parent.children().map(|l| l.nodes());
            }
        }
        Kind::JsxOpeningElement | Kind::JsxSelfClosingElement => {
            if ast::is_type_node(&nodes[node]) {
                return parent.type_argument_list().map(|l| l.nodes());
            }
        }
        Kind::Block | Kind::ModuleBlock | Kind::CaseClause | Kind::DefaultClause => {
            return parent.statement_list().map(|l| l.nodes());
        }
        Kind::CaseBlock => {
            return parent.as_case_block().clauses.as_ref().map(|l| l.nodes());
        }
        Kind::ClassDeclaration | Kind::ClassExpression => {
            if ast::is_class_element(&nodes[node]) {
                return parent.member_list().map(|l| l.nodes());
            }
        }
        Kind::EnumDeclaration => {
            if ast::is_enum_member(&nodes[node]) {
                return parent.member_list().map(|l| l.nodes());
            }
        }
        Kind::SourceFile => {
            if ast::is_statement(&nodes[node], nodes) {
                return parent.statement_list().map(|l| l.nodes());
            }
        }
        _ => {}
    }

    if ast::is_modifier(&nodes[node])
        && let Some(modifiers) = parent.modifiers()
    {
        return Some(&modifiers.nodes);
    }

    None
}

/// `canHaveDecorators`
fn can_have_decorators(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::Parameter
            | Kind::PropertyDeclaration
            | Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::ClassExpression
            | Kind::ClassDeclaration
    )
}

/// `originalNodesHaveSameParent`
pub(crate) fn original_nodes_have_same_parent(
    shared: &Shared,
    nodes: &[Node],
    node_a: NodeId,
    node_b: NodeId,
) -> bool {
    let node_a = most_original_shared(shared, node_a);
    if nodes[node_a].parent.is_some() {
        // For performance, do not call `MostOriginal` for `nodeB` if `nodeA` doesn't even
        // have a parent node.
        let node_b = most_original_shared(shared, node_b);
        return nodes[node_a].parent == nodes[node_b].parent;
    }
    false
}

/// `greatestEnd` — returns the largest of `end` and the ends of the provided
/// values, scanning in reverse order (matching `slices.Backward`).
///
/// PORT: Go accepts `interface{ End() int }` over `*ast.Node`, `*ast.NodeList`,
/// `*ast.ModifierList`, `*core.TextRange`, and `core.TextRange`, where `nil`
/// values are skipped. Rust callers pass `Option<i32>` ends (e.g.
/// `nodes[n].end()` wrapped in `Some`, or `None` for absent lists).
pub(crate) fn greatest_end(end: i32, ends: impl IntoIterator<Item = Option<i32>>) -> i32 {
    let ends: Vec<Option<i32>> = ends.into_iter().collect();
    let mut end = end;
    for node_end in ends.into_iter().rev().flatten() {
        if end < node_end {
            end = node_end;
        }
    }
    end
}

/// `skipSynthesizedParentheses`
pub(crate) fn skip_synthesized_parentheses(nodes: &[Node], node: NodeId) -> NodeId {
    let mut node = node;
    while nodes[node].kind == Kind::ParenthesizedExpression
        && ast::node_is_synthesized(&nodes[node])
    {
        node = nodes[node].expression().unwrap();
    }
    node
}

/// `isNewExpressionWithoutArguments`
pub(crate) fn is_new_expression_without_arguments(nodes: &[Node], node: NodeId) -> bool {
    nodes[node].kind == Kind::NewExpression && nodes[node].argument_list().is_none()
}

/// `isBinaryOperation`
pub(crate) fn is_binary_operation(nodes: &[Node], node: NodeId, token: Kind) -> bool {
    let node = ast::skip_partially_emitted_expressions(node, nodes);
    nodes[node].kind == Kind::BinaryExpression
        && nodes[node]
            .as_binary_expression()
            .operator_token
            .is_some_and(|t| nodes[t].kind == token)
}

/// `mixingBinaryOperatorsRequiresParentheses`
pub(crate) fn mixing_binary_operators_requires_parentheses(a: Kind, b: Kind) -> bool {
    if a == Kind::QuestionQuestionToken {
        return b == Kind::AmpersandAmpersandToken || b == Kind::BarBarToken;
    }
    if b == Kind::QuestionQuestionToken {
        return a == Kind::AmpersandAmpersandToken || a == Kind::BarBarToken;
    }
    false
}

/// `isImmediatelyInvokedFunctionExpressionOrArrowFunction`
pub(crate) fn is_immediately_invoked_function_expression_or_arrow_function(
    nodes: &[Node],
    node: NodeId,
) -> bool {
    let node = ast::skip_partially_emitted_expressions(node, nodes);
    if !ast::is_call_expression(&nodes[node]) {
        return false;
    }
    let Some(expr) = nodes[node].expression() else {
        return false;
    };
    let node = ast::skip_partially_emitted_expressions(expr, nodes);
    ast::is_function_expression(&nodes[node]) || ast::is_arrow_function(&nodes[node])
}

/// `hasLeadingHash`
pub(crate) fn has_leading_hash(text: &str) -> bool {
    text.starts_with('#')
}

/// `removeLeadingHash`
pub(crate) fn remove_leading_hash(text: &str) -> &str {
    text.strip_prefix('#').unwrap_or(text)
}

/// `ensureLeadingHash`
pub(crate) fn ensure_leading_hash(text: &str) -> Cow<'_, str> {
    if has_leading_hash(text) {
        Cow::Borrowed(text)
    } else {
        Cow::Owned(format!("#{}", text))
    }
}

/// `isASCIIWordCharacter`
pub(crate) fn is_ascii_word_character(ch: char) -> bool {
    stringutil::is_ascii_letter(ch) || stringutil::is_digit(ch) || ch == '_'
}

/// `makeIdentifierFromModuleName`
pub(crate) fn make_identifier_from_module_name(module_name: &str) -> String {
    let module_name = tsc_tspath::get_base_file_name(module_name);
    let mut builder = String::new();
    let bytes = module_name.as_bytes();
    let mut start = 0usize;
    let mut pos = 0usize;
    while pos < bytes.len() {
        let ch = bytes[pos] as char;
        if pos == 0 && stringutil::is_digit(ch) {
            builder.push('_');
        } else if !is_ascii_word_character(ch) {
            if start < pos {
                builder.push_str(&module_name[start..pos]);
            }
            builder.push('_');
            start = pos + 1;
        }
        pos += 1;
    }
    if start < pos {
        builder.push_str(&module_name[start..pos]);
    }
    builder
}

/// `findSpanEndWithEmitContext` — PORT: callers capture the emit context
/// handle in the closure instead.
pub(crate) fn find_span_end<T>(
    array: &[T],
    mut test: impl FnMut(&T) -> bool,
    start: usize,
) -> usize {
    let mut i = start;
    while i < array.len() && test(&array[i]) {
        i += 1;
    }
    i
}

/// `skipWhiteSpaceSingleLine`
fn skip_white_space_single_line(text: &str, pos: &mut usize) {
    while *pos < text.len() {
        let (ch, size) = decode_rune(&text[*pos..]);
        if !stringutil::is_white_space_single_line(ch) {
            break;
        }
        *pos += size;
    }
}

/// `matchWhiteSpaceSingleLine`
fn match_white_space_single_line(text: &str, pos: &mut usize) -> bool {
    let start_pos = *pos;
    skip_white_space_single_line(text, pos);
    *pos != start_pos
}

/// `matchRune`
fn match_rune(text: &str, pos: &mut usize, expected: char) -> bool {
    let (ch, size) = decode_rune(&text[*pos..]);
    if ch == expected {
        *pos += size;
        return true;
    }
    false
}

/// `matchString`
fn match_string(text: &str, pos: &mut usize, expected: &str) -> bool {
    let mut text_pos = *pos;
    let mut expected_pos = 0usize;
    while expected_pos < expected.len() {
        if text_pos >= text.len() {
            return false;
        }

        let (expected_rune, expected_size) = decode_rune(&expected[expected_pos..]);
        if !match_rune(text, &mut text_pos, expected_rune) {
            return false;
        }

        expected_pos += expected_size;
    }

    *pos = text_pos;
    true
}

/// `matchQuotedString`
fn match_quoted_string(text: &str, pos: &mut usize) -> bool {
    let mut text_pos = *pos;
    let quote_char;
    if match_rune(text, &mut text_pos, '\'') {
        quote_char = '\'';
    } else if match_rune(text, &mut text_pos, '"') {
        quote_char = '"';
    } else {
        return false;
    }
    while text_pos < text.len() {
        let (ch, size) = decode_rune(&text[text_pos..]);
        text_pos += size;
        if ch == quote_char {
            *pos = text_pos;
            return true;
        }
    }
    false
}

/// `utf8.DecodeRuneInString` — decodes a UTF-8 rune, returning the rune and
/// its byte width (invalid input yields `'\u{FFFD}'`, size 1).
fn decode_rune(s: &str) -> (char, usize) {
    match s.chars().next() {
        Some(ch) => (ch, ch.len_utf8()),
        None => ('\u{FFFD}', 0),
    }
}

// /// <reference path="..." />
// /// <reference types="..." />
// /// <reference lib="..." />
// /// <reference no-default-lib="..." />
// /// <amd-dependency path="..." />
// /// <amd-module />
/// `IsRecognizedTripleSlashComment`
pub fn is_recognized_triple_slash_comment(text: &str, comment_range: CommentRange) -> bool {
    if comment_range.kind == Kind::SingleLineCommentTrivia
        && comment_range.text_range.len() > 2
        && text.as_bytes()[comment_range.text_range.pos() as usize + 1] == b'/'
        && text.as_bytes()[comment_range.text_range.pos() as usize + 2] == b'/'
    {
        let text = &text[comment_range.text_range.pos() as usize + 3..comment_range.text_range.end() as usize];
        let mut pos = 0usize;
        skip_white_space_single_line(text, &mut pos);
        if !match_rune(text, &mut pos, '<') {
            return false;
        }
        if match_string(text, &mut pos, "reference") {
            if !match_white_space_single_line(text, &mut pos) {
                return false;
            }
            if !match_string(text, &mut pos, "path")
                && !match_string(text, &mut pos, "types")
                && !match_string(text, &mut pos, "lib")
                && !match_string(text, &mut pos, "no-default-lib")
            {
                return false;
            }
            skip_white_space_single_line(text, &mut pos);
            if !match_rune(text, &mut pos, '=') {
                return false;
            }
            skip_white_space_single_line(text, &mut pos);
            if !match_quoted_string(text, &mut pos) {
                return false;
            }
        } else if match_string(text, &mut pos, "amd-dependency") {
            if !match_white_space_single_line(text, &mut pos) {
                return false;
            }
            if !match_string(text, &mut pos, "path") {
                return false;
            }
            skip_white_space_single_line(text, &mut pos);
            if !match_rune(text, &mut pos, '=') {
                return false;
            }
            skip_white_space_single_line(text, &mut pos);
            if !match_quoted_string(text, &mut pos) {
                return false;
            }
        } else if match_string(text, &mut pos, "amd-module") {
            skip_white_space_single_line(text, &mut pos);
        } else {
            return false;
        }
        return text[pos..].contains("/>");
    }

    false
}

/// `isJSDocLikeText`
pub(crate) fn is_jsdoc_like_text(text: &str, comment: CommentRange) -> bool {
    comment.kind == Kind::MultiLineCommentTrivia
        && comment.text_range.len() >= 5
        && text.as_bytes()[comment.text_range.pos() as usize + 2] == b'*'
        && text.as_bytes()[comment.text_range.pos() as usize + 3] != b'/'
}

/// `IsPinnedComment`
pub fn is_pinned_comment(text: &str, comment: CommentRange) -> bool {
    comment.kind == Kind::MultiLineCommentTrivia
        && comment.text_range.len() > 5
        && text.as_bytes()[comment.text_range.pos() as usize + 2] == b'!'
}

/// `calculateIndent`
pub(crate) fn calculate_indent(text: &str, mut pos: usize, end: usize) -> i32 {
    let mut current_line_indent = 0i32;
    let indent_size = get_default_indent_size();
    while pos < end {
        let (ch, size) = decode_rune(&text[pos..]);
        if !stringutil::is_white_space_single_line(ch) {
            break;
        }
        if ch == '\t' {
            // Tabs = TabSize = indent size and go to next tabStop
            current_line_indent += indent_size - (current_line_indent % indent_size);
        } else {
            // Single space
            current_line_indent += 1;
        }
        pos += size;
    }

    current_line_indent
}

/// `lineCharacterCache` — provides cached line/character lookups for a source
/// file, optimized for monotonically increasing positions (e.g., during
/// source map emit).
///
/// When positions increase within the same line, only the delta between the
/// last position and the new position needs to be scanned for UTF-16 code
/// unit counts, turning what would be O(n²) into O(n) for long lines.
///
/// Character offsets are measured in UTF-16 code units per the source map
/// specification.
pub(crate) struct LineCharacterCache<'a> {
    line_map: &'a [TextPos],
    text: &'a str,
    cached_line: i32,
    cached_pos: i32,
    cached_char: UTF16Offset,
    has_cached: bool,
}

/// `newLineCharacterCache`
impl<'a> LineCharacterCache<'a> {
    pub(crate) fn new(source: &'a dyn tsc_sourcemap::Source) -> LineCharacterCache<'a> {
        LineCharacterCache {
            line_map: source.ecma_line_map(),
            text: source.text(),
            cached_line: 0,
            cached_pos: 0,
            cached_char: 0,
            has_cached: false,
        }
    }

    /// `getLineAndCharacter` — returns the 0-based line number and UTF-16 code
    /// unit offset from the start of that line for the given byte position.
    pub(crate) fn get_line_and_character(&mut self, pos: i32) -> (i32, UTF16Offset) {
        let line = tsc_scanner::scanner::compute_line_of_position(self.line_map, pos);
        let line_start = self.line_map[line as usize];
        // When pos is beyond the source text (e.g., for error-recovery tokens like
        // missing closing braces), we can't slice past the text end. Compute the
        // UTF-16 length up to EOF and add the remaining byte offset arithmetically,
        // matching TypeScript's computeLineAndCharacterOfPosition which uses
        // arithmetic (position - lineStarts[lineNumber]) and handles this implicitly.
        let end_pos = pos.min(self.text.len() as i32);
        let mut character = if self.has_cached && line == self.cached_line && end_pos >= self.cached_pos
        {
            // Incremental: only count UTF-16 code units from the last cached position.
            self.cached_char
                + tsc_core::core::utf16_len(
                    &self.text[self.cached_pos as usize..end_pos as usize],
                )
        } else {
            // Full computation from line start.
            tsc_core::core::utf16_len(&self.text[line_start as usize..end_pos as usize])
        };
        let cached_char = character;
        character += (pos - end_pos) as UTF16Offset;
        self.cached_line = line;
        self.cached_pos = end_pos;
        self.cached_char = cached_char;
        self.has_cached = true;
        (line, character)
    }
}

/// `fmt` helper kept for parity with Go's `fmt.Sprintf` usage sites.
#[allow(dead_code)]
pub(crate) fn write_fmt(b: &mut String, args: std::fmt::Arguments) {
    b.write_fmt(args).unwrap();
}

#[cfg(test)]
mod tests {
    //! Ported from tsc/internal/printer/utilities_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763.

    use super::*;
    use tsc_ast::CommentRange;
    use tsc_core::text::TextRange;

    /// `TestEscapeString`
    #[test]
    fn test_escape_string() {
        let data: &[(&str, QuoteChar, &str)] = &[
            ("", QuoteChar::DoubleQuote, ""),
            ("abc", QuoteChar::DoubleQuote, "abc"),
            ("ab\"c", QuoteChar::DoubleQuote, "ab\\\"c"),
            ("ab\tc", QuoteChar::DoubleQuote, "ab\\tc"),
            ("ab\nc", QuoteChar::DoubleQuote, "ab\\nc"),
            ("ab'c", QuoteChar::DoubleQuote, "ab'c"),
            ("ab'c", QuoteChar::SingleQuote, "ab\\'c"),
            ("ab\"c", QuoteChar::SingleQuote, "ab\"c"),
            ("ab`c", QuoteChar::Backtick, "ab\\`c"),
            ("\u{1f}", QuoteChar::Backtick, "\\u001F"),
        ];
        for (i, (s, quote_char, expected)) in data.iter().enumerate() {
            let actual = escape_string(s, *quote_char);
            assert_eq!(actual, *expected, "[{i}] escapeString({s:?}, {quote_char:?})");
        }
    }

    /// `TestEscapeNonAsciiString`
    #[test]
    fn test_escape_non_ascii_string() {
        let data: &[(&str, QuoteChar, &str)] = &[
            ("", QuoteChar::DoubleQuote, ""),
            ("abc", QuoteChar::DoubleQuote, "abc"),
            ("ab\"c", QuoteChar::DoubleQuote, "ab\\\"c"),
            ("ab\tc", QuoteChar::DoubleQuote, "ab\\tc"),
            ("ab\nc", QuoteChar::DoubleQuote, "ab\\nc"),
            ("ab'c", QuoteChar::DoubleQuote, "ab'c"),
            ("ab'c", QuoteChar::SingleQuote, "ab\\'c"),
            ("ab\"c", QuoteChar::SingleQuote, "ab\"c"),
            ("ab`c", QuoteChar::Backtick, "ab\\`c"),
            ("ab\u{8f}c", QuoteChar::DoubleQuote, "ab\\u008Fc"),
            (
                "\u{1d7d8}\u{1d7d9}",
                QuoteChar::DoubleQuote,
                "\\uD835\\uDFD8\\uD835\\uDFD9",
            ),
        ];
        for (i, (s, quote_char, expected)) in data.iter().enumerate() {
            let actual = escape_non_ascii_string(s, *quote_char);
            assert_eq!(
                actual, *expected,
                "[{i}] escapeNonAsciiString({s:?}, {quote_char:?})"
            );
        }
    }

    /// `TestEscapeJsxAttributeString`
    #[test]
    fn test_escape_jsx_attribute_string() {
        let data: &[(&str, QuoteChar, &str)] = &[
            ("", QuoteChar::DoubleQuote, ""),
            ("abc", QuoteChar::DoubleQuote, "abc"),
            ("ab\"c", QuoteChar::DoubleQuote, "ab&quot;c"),
            ("ab\tc", QuoteChar::DoubleQuote, "ab&#x9;c"),
            ("ab\nc", QuoteChar::DoubleQuote, "ab&#xA;c"),
            ("ab'c", QuoteChar::DoubleQuote, "ab'c"),
            ("ab'c", QuoteChar::SingleQuote, "ab&apos;c"),
            ("ab\"c", QuoteChar::SingleQuote, "ab\"c"),
            ("ab\u{8f}c", QuoteChar::DoubleQuote, "ab\u{8f}c"),
            ("\u{1d7d8}\u{1d7d9}", QuoteChar::DoubleQuote, "\u{1d7d8}\u{1d7d9}"),
        ];
        for (i, (s, quote_char, expected)) in data.iter().enumerate() {
            let actual = escape_jsx_attribute_string(s, *quote_char);
            assert_eq!(
                actual, *expected,
                "[{i}] escapeJsxAttributeString({s:?}, {quote_char:?})"
            );
        }
    }

    /// `TestIsRecognizedTripleSlashComment`
    #[test]
    fn test_is_recognized_triple_slash_comment() {
        // (s, comment_kind_override, expected) — None means SingleLineCommentTrivia
        // spanning the whole string, matching the Go test default.
        let data: &[(&str, Option<Kind>, bool)] = &[
            ("", Some(Kind::MultiLineCommentTrivia), false),
            ("", Some(Kind::SingleLineCommentTrivia), false),
            ("/a", None, false),
            ("//", None, false),
            ("//a", None, false),
            ("///", None, false),
            ("///a", None, false),
            ("///<reference path=\"foo\" />", None, true),
            ("///<reference types=\"foo\" />", None, true),
            ("///<reference lib=\"foo\" />", None, true),
            ("///<reference no-default-lib=\"foo\" />", None, true),
            ("///<amd-dependency path=\"foo\" />", None, true),
            ("///<amd-module />", None, true),
            ("/// <reference path=\"foo\" />", None, true),
            ("/// <reference types=\"foo\" />", None, true),
            ("/// <reference lib=\"foo\" />", None, true),
            ("/// <reference no-default-lib=\"foo\" />", None, true),
            ("/// <amd-dependency path=\"foo\" />", None, true),
            ("/// <amd-module />", None, true),
            ("/// <reference path=\"foo\"/>", None, true),
            ("/// <reference types=\"foo\"/>", None, true),
            ("/// <reference lib=\"foo\"/>", None, true),
            ("/// <reference no-default-lib=\"foo\"/>", None, true),
            ("/// <amd-dependency path=\"foo\"/>", None, true),
            ("/// <amd-module/>", None, true),
            ("/// <reference path='foo' />", None, true),
            ("/// <reference types='foo' />", None, true),
            ("/// <reference lib='foo' />", None, true),
            ("/// <reference no-default-lib='foo' />", None, true),
            ("/// <amd-dependency path='foo' />", None, true),
            ("/// <reference path=\"foo\" />  ", None, true),
            ("/// <reference types=\"foo\" />  ", None, true),
            ("/// <reference lib=\"foo\" />  ", None, true),
            ("/// <reference no-default-lib=\"foo\" />  ", None, true),
            ("/// <amd-dependency path=\"foo\" />  ", None, true),
            ("/// <amd-module />  ", None, true),
            ("/// <foo />", None, false),
            ("/// <reference />", None, false),
            ("/// <amd-dependency />", None, false),
        ];
        for (i, (s, kind, expected)) in data.iter().enumerate() {
            let comment_range = CommentRange {
                text_range: TextRange::new(0, s.len() as i32),
                kind: kind.unwrap_or(Kind::SingleLineCommentTrivia),
                has_trailing_new_line: false,
            };
            let actual = is_recognized_triple_slash_comment(s, comment_range);
            assert_eq!(actual, *expected, "[{i}] isRecognizedTripleSlashComment({s:?})");
        }
    }
}
