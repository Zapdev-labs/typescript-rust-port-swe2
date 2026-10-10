// Ported from tsc/internal/format/api.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::ast::Node;
use tsc_ast::ids::NodeId;
use tsc_ast::kind_generated::Kind;
use tsc_core::context::{Context, ContextKey};
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::text::TextRange;
use tsc_core::textchange::TextChange;
use tsc_lsutil::{FormatCodeSettings, get_default_format_code_settings};
use tsc_scanner::scanner::get_token_pos_of_node;
use tsc_stringutil::{is_line_break, is_white_space_single_line};

use crate::indent::{decode_rune_in_string, get_indentation_for_node};
use crate::scanner::new_formatting_scanner;
use crate::span::{
    FormatSpanWorker, find_enclosing_node, get_own_or_inherited_delta, get_scan_start_position,
    new_format_span_worker, prepare_range_contains_error_function,
};
use crate::util::{
    end_line_position, find_immediately_preceding_token_of_kind,
    find_outermost_node_within_list_level, get_line_start_position_for_position, line_map,
    line_of_position,
};
use std::cell::RefCell;

/// `type FormatRequestKind int`
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub enum FormatRequestKind {
    #[default]
    FormatDocument,
    FormatSelection,
    FormatOnEnter,
    FormatOnSemicolon,
    FormatOnOpeningCurlyBrace,
    FormatOnClosingCurlyBrace,
}

/// `type formatContextKey int` — Go's unexported key type constants become
/// zero-sized markers keyed by `TypeId` (PORT: see `core.ContextKey`).
struct FormatOptionsKey;
struct FormatNewlineKey;

const FORMAT_OPTIONS_KEY: ContextKey<FormatOptionsKey, FormatCodeSettings> = ContextKey::new();
const FORMAT_NEWLINE_KEY: ContextKey<FormatNewlineKey, String> = ContextKey::new();

/// `WithFormatCodeSettings`
pub fn with_format_code_settings(
    ctx: &Context,
    options: FormatCodeSettings,
    new_line: &str,
) -> Context {
    let ctx = ctx.with_value(FORMAT_OPTIONS_KEY, options);
    let ctx = ctx.with_value(FORMAT_NEWLINE_KEY, new_line.to_string());
    // In strada, the rules map was both globally cached *and* cached into the context, for some reason. We skip that here and just use the global one.
    ctx
}

/// `GetFormatCodeSettingsFromContext`
pub fn get_format_code_settings_from_context(ctx: &Context) -> FormatCodeSettings {
    if let Some(opt) = ctx.value(FORMAT_OPTIONS_KEY) {
        return opt.clone();
    }
    get_default_format_code_settings()
}

/// `GetNewLineOrDefaultFromContext` — TODO: Move into broader LS - more than
/// just the formatter uses the newline editor setting/host new line
pub fn get_new_line_or_default_from_context(ctx: &Context) -> String {
    let opt = get_format_code_settings_from_context(ctx);
    if !opt.editor_settings.new_line_character.is_empty() {
        return opt.editor_settings.new_line_character;
    }
    let host = ctx
        .value(FORMAT_NEWLINE_KEY)
        .expect("format newline context value");
    if !host.is_empty() {
        return host.clone();
    }
    "\n".to_string()
}

/// `FormatSpan`
pub fn format_span(
    ctx: &Context,
    span: TextRange,
    file: NodeId,
    kind: FormatRequestKind,
    nodes: &mut Vec<Node>,
) -> Vec<TextChange> {
    // find the smallest node that fully wraps the range and compute the initial indentation for the node
    let enclosing_node = find_enclosing_node(span, file, nodes);
    let opts = get_format_code_settings_from_context(ctx);

    let text = nodes[file].as_source_file().text.clone();
    let language_variant = nodes[file].as_source_file().language_variant;
    let s = new_formatting_scanner(
        &text,
        language_variant,
        get_scan_start_position(enclosing_node, span, file, nodes),
        span.end(),
    );
    let worker = new_format_span_worker(
        ctx.clone(),
        span,
        enclosing_node,
        get_indentation_for_node(enclosing_node, Some(&span), file, &opts, nodes),
        get_own_or_inherited_delta(Some(enclosing_node), &opts, file, nodes),
        kind,
        prepare_range_contains_error_function(nodes[file].as_source_file().diagnostics(), span),
        file,
    );
    let s = RefCell::new(s);
    let res = FormatSpanWorker::execute(&worker, &s, nodes);
    let mut s = s.into_inner();

    s.has_last_token_info = false;
    s.s.reset();

    res
}

/// `FormatNodeGivenIndentation`
pub fn format_node_given_indentation(
    ctx: &Context,
    node: NodeId,
    file: NodeId,
    language_variant: LanguageVariant,
    initial_indentation: i32,
    delta: i32,
    nodes: &mut Vec<Node>,
) -> Vec<TextChange> {
    let text_range = TextRange::new(nodes[node].pos(), nodes[node].end());
    let text = nodes[file].as_source_file().text.clone();
    let s = new_formatting_scanner(&text, language_variant, text_range.pos(), text_range.end());
    let worker = new_format_span_worker(
        ctx.clone(),
        text_range,
        node,
        initial_indentation,
        delta,
        FormatRequestKind::FormatSelection,
        Box::new(|_: TextRange| false), // assume that node does not have any errors
        file,
    );
    let s = RefCell::new(s);
    let res = FormatSpanWorker::execute(&worker, &s, nodes);
    let mut s = s.into_inner();

    s.has_last_token_info = false;
    s.s.reset();

    res
}

/// `formatNodeLines`
fn format_node_lines(
    ctx: &Context,
    source_file: NodeId,
    node: Option<NodeId>,
    request_kind: FormatRequestKind,
    nodes: &mut Vec<Node>,
) -> Vec<TextChange> {
    let Some(node) = node else {
        return Vec::new();
    };
    let token_start =
        get_token_pos_of_node(node, nodes[source_file].as_source_file(), false, nodes);
    let line_start = get_line_start_position_for_position(token_start, source_file, nodes);
    let span = TextRange::new(line_start, nodes[node].end());
    format_span(ctx, span, source_file, request_kind, nodes)
}

/// `FormatDocument`
pub fn format_document(
    ctx: &Context,
    source_file: NodeId,
    nodes: &mut Vec<Node>,
) -> Vec<TextChange> {
    format_span(
        ctx,
        TextRange::new(0, nodes[source_file].end()),
        source_file,
        FormatRequestKind::FormatDocument,
        nodes,
    )
}

/// `FormatSelection`
pub fn format_selection(
    ctx: &Context,
    source_file: NodeId,
    start: i32,
    end: i32,
    nodes: &mut Vec<Node>,
) -> Vec<TextChange> {
    format_span(
        ctx,
        TextRange::new(
            get_line_start_position_for_position(start, source_file, nodes),
            end,
        ),
        source_file,
        FormatRequestKind::FormatSelection,
        nodes,
    )
}

/// `FormatOnOpeningCurly`
pub fn format_on_opening_curly(
    ctx: &Context,
    source_file: NodeId,
    position: i32,
    nodes: &mut Vec<Node>,
) -> Vec<TextChange> {
    let Some(opening_curly) = find_immediately_preceding_token_of_kind(
        position,
        Kind::OpenBraceToken,
        source_file,
        nodes,
    ) else {
        return Vec::new();
    };
    let curly_brace_range = nodes[opening_curly].parent.unwrap();
    let outermost_node = find_outermost_node_within_list_level(Some(curly_brace_range), nodes);
    /*
     * We limit the span to end at the opening curly to handle the case where
     * the brace matched to that just typed will be incorrect after further edits.
     * For example, we could type the opening curly for the following method
     * body without brace-matching activated:
     * ```
     * class C {
     *     foo()
     * }
     * ```
     * and we wouldn't want to move the closing brace.
     */
    let text_range = TextRange::new(
        get_line_start_position_for_position(
            get_token_pos_of_node(
                outermost_node.expect("outermost node"),
                nodes[source_file].as_source_file(),
                false,
                nodes,
            ),
            source_file,
            nodes,
        ),
        position,
    );
    format_span(
        ctx,
        text_range,
        source_file,
        FormatRequestKind::FormatOnOpeningCurlyBrace,
        nodes,
    )
}

/// `FormatOnClosingCurly`
pub fn format_on_closing_curly(
    ctx: &Context,
    source_file: NodeId,
    position: i32,
    nodes: &mut Vec<Node>,
) -> Vec<TextChange> {
    let preceding_token = find_immediately_preceding_token_of_kind(
        position,
        Kind::CloseBraceToken,
        source_file,
        nodes,
    );
    format_node_lines(
        ctx,
        source_file,
        find_outermost_node_within_list_level(preceding_token, nodes),
        FormatRequestKind::FormatOnClosingCurlyBrace,
        nodes,
    )
}

/// `FormatOnSemicolon`
pub fn format_on_semicolon(
    ctx: &Context,
    source_file: NodeId,
    position: i32,
    nodes: &mut Vec<Node>,
) -> Vec<TextChange> {
    let semicolon = find_immediately_preceding_token_of_kind(
        position,
        Kind::SemicolonToken,
        source_file,
        nodes,
    );
    format_node_lines(
        ctx,
        source_file,
        find_outermost_node_within_list_level(semicolon, nodes),
        FormatRequestKind::FormatOnSemicolon,
        nodes,
    )
}

/// `FormatOnEnter`
pub fn format_on_enter(
    ctx: &Context,
    source_file: NodeId,
    position: i32,
    nodes: &mut Vec<Node>,
) -> Vec<TextChange> {
    let line = line_of_position(nodes, source_file, position);
    if line == 0 {
        return Vec::new();
    }
    // get start position for the previous line
    let start_pos = line_map(nodes, source_file)[(line - 1) as usize];
    // After the enter key, the cursor is now at a new line. The new line may or may not contain non-whitespace characters.
    // If the new line has only whitespaces, we won't want to format this line, because that would remove the indentation as
    // trailing whitespaces. So the end of the formatting span should be the later one between:
    //  1. the end of the previous line
    //  2. the last non-whitespace character in the current line
    let mut end_of_format_span = end_line_position(nodes, source_file, line);
    while end_of_format_span > start_pos {
        let (ch, s) = decode_rune_in_string(
            &nodes[source_file].as_source_file().text.as_bytes()[end_of_format_span as usize..],
        );
        if s == 0 || is_white_space_single_line(ch) {
            // on multibyte character keep backing up
            end_of_format_span -= 1;
            continue;
        }
        break;
    }

    // if the character at the end of the span is a line break, we shouldn't include it, because it indicates we don't want to
    // touch the current line at all. Also, on some OSes the line break consists of two characters (\r\n), we should test if the
    // previous character before the end of format span is line break character as well.
    let (ch, _) = decode_rune_in_string(
        &nodes[source_file].as_source_file().text.as_bytes()[end_of_format_span as usize..],
    );
    if is_line_break(ch) {
        end_of_format_span -= 1;
    }

    let span = TextRange::new(
        start_pos,
        // end value is exclusive so add 1 to the result
        end_of_format_span + 1,
    );

    format_span(
        ctx,
        span,
        source_file,
        FormatRequestKind::FormatOnEnter,
        nodes,
    )
}
