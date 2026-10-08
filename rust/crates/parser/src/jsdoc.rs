// Ported from tsc/internal/parser/jsdoc.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Go `*ast.Node` values are `NodeId`s resolved through `self.nodes`; Go nil is
// `Option<NodeId>`. `p.nodeSliceArena`/`p.stringSliceArena` are plain `Vec`s.

use tsc_ast::ast_generated::*;
use tsc_ast::diagnostic::lock_diagnostic;
use tsc_ast::utilities::node_is_missing;
use tsc_ast::{Kind, Node, NodeFlags, NodeId, NodeList};
use tsc_core::text::TextRange;
use tsc_diagnostics::{self as diagnostics, Message};
use tsc_stringutil as stringutil;

use crate::parser::{
    JSDOC_SCANNER_INFO_HAS_DEPRECATED, JSDOC_SCANNER_INFO_HAS_JSDOC,
    JSDOC_SCANNER_INFO_HAS_SEE_OR_LINK, JSDocInfo, JSDocScannerInfo, Parser,
    parsing_context::PC_JS_DOC_COMMENT,
};
use crate::utilities::{
    get_jsdoc_comment_ranges, is_jsdoc_like_text, token_is_identifier_or_keyword,
};

/// `type jsdocState int32`
type JSDocState = u8;

const JSDOC_STATE_BEGINNING_OF_LINE: JSDocState = 0;
const JSDOC_STATE_SAW_ASTERISK: JSDocState = 1;
const JSDOC_STATE_SAVING_COMMENTS: JSDocState = 2;
const JSDOC_STATE_SAVING_BACKTICKS: JSDocState = 3;

/// `type propertyLikeParse int32`
type PropertyLikeParse = u8;

const PROPERTY_LIKE_PARSE_PROPERTY: PropertyLikeParse = 1 << 0;
const PROPERTY_LIKE_PARSE_PARAMETER: PropertyLikeParse = 1 << 1;
const PROPERTY_LIKE_PARSE_CALLBACK_PARAMETER: PropertyLikeParse = 1 << 2;

/// `func parseJSDocForNode(sourceFile *ast.SourceFile, node *ast.Node) []*ast.Node`
///
/// Lazily parses JSDoc for a node in a TS file. Called on first access to
/// `Node::jsdoc` for non-JS source files.
///
/// PORT: the pooled `getParser`/`putParser` becomes a fresh `Parser` whose
/// `nodes` arena is swapped with the file's for the duration of the call, and
/// the file's text is cloned once per call (the arena borrow forbids aliasing
/// `source_text` into `nodes`). The factory's file index is pinned to the
/// file's so freshly minted `NodeId`s index this arena.
pub fn parse_jsdoc_for_node(
    nodes: &mut Vec<Node>,
    source_file: NodeId,
    node: NodeId,
) -> Vec<NodeId> {
    let (opts, script_kind, file_index, text) = {
        let sf = nodes[source_file].as_source_file();
        (
            sf.parse_options.clone(),
            sf.script_kind,
            nodes[source_file].id.file_index(),
            sf.text.clone(),
        )
    };
    let mut p = Parser::new();
    std::mem::swap(&mut p.nodes, nodes);
    p.initialize_state(opts, &text, script_kind);
    p.factory.set_file_index(file_index);
    let ranges = get_jsdoc_comment_ranges(&p.factory, Vec::new(), node, &text, &p.nodes);
    let jsdoc = if ranges.is_empty() {
        Vec::new()
    } else {
        let mut jsdoc: Vec<NodeId> = Vec::with_capacity(ranges.len());
        let mut pos = p.nodes[node].pos();
        for comment in &ranges {
            if let Some(parsed) = p.parse_jsdoc_comment(
                node,
                comment.text_range.pos(),
                comment.text_range.end(),
                pos,
            ) {
                p.nodes[parsed].parent = Some(node);
                jsdoc.push(parsed);
                pos = p.nodes[parsed].end();
            }
        }
        jsdoc
    };
    std::mem::swap(&mut p.nodes, nodes);
    jsdoc
}

impl<'a> Parser<'a> {
    /// `func (p *Parser) withJSDoc(node *ast.Node, info jsdocScannerInfo) []*ast.Node`
    pub fn with_jsdoc(&mut self, node: NodeId, info: JSDocScannerInfo) -> Vec<NodeId> {
        if !info & JSDOC_SCANNER_INFO_HAS_JSDOC != 0 {
            return Vec::new();
        }
        // For TS/TSX files, defer JSDoc parsing to first access, unless the comment
        // contains @see/@link (needed for unused-identifier checks).
        // @deprecated is detected via cheap text scan to set PossiblyContainsDeprecatedTag;
        // callers must confirm via JSDoc lookup.
        if !self.is_java_script() {
            self.nodes[node].flags |= NodeFlags::HAS_JSDOC;
            if info & JSDOC_SCANNER_INFO_HAS_DEPRECATED != 0 {
                self.nodes[node].flags |= NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG;
            }
            if !info & JSDOC_SCANNER_INFO_HAS_SEE_OR_LINK != 0 {
                return Vec::new();
            }
            // Fall through to eager parse for @see/@link
        }
        let __h0 = std::mem::take(&mut self.jsdoc_comment_ranges_space);
        let mut ranges =
            get_jsdoc_comment_ranges(&self.factory, __h0, node, self.source_text, &self.nodes);
        // Should only be called once per node
        self.has_deprecated_tag = false;
        let mut jsdoc: Vec<NodeId> = Vec::with_capacity(8);
        let mut pos = self.nodes[node].pos();
        for comment in &ranges {
            if let Some(parsed) = self.parse_jsdoc_comment(
                node,
                comment.text_range.pos(),
                comment.text_range.end(),
                pos,
            ) {
                self.nodes[parsed].parent = Some(node);
                jsdoc.push(parsed);
                pos = self.nodes[parsed].end();
            }
        }
        ranges.clear();
        self.jsdoc_comment_ranges_space = ranges;
        if !jsdoc.is_empty() {
            if !self.nodes[node].flags.intersects(NodeFlags::HAS_JSDOC) {
                self.nodes[node].flags |= NodeFlags::HAS_JSDOC;
            }
            if self.has_deprecated_tag {
                self.has_deprecated_tag = false;
                self.nodes[node].flags |= NodeFlags::POSSIBLY_CONTAINS_DEPRECATED_TAG;
            }
            if self.is_java_script() {
                self.reparse_tags(node, &jsdoc);
            }
            self.jsdoc_infos.push(JSDocInfo {
                parent: Some(node),
                js_docs: jsdoc.clone(),
            });
            return jsdoc;
        }
        Vec::new()
    }

    /// `func (p *Parser) parseJSDocTypeExpression(mayOmitBraces bool) *ast.Node`
    fn parse_jsdoc_type_expression(&mut self, may_omit_braces: bool) -> NodeId {
        let pos = self.node_pos();
        let has_brace = if may_omit_braces {
            self.parse_optional(Kind::OpenBraceToken)
        } else {
            self.parse_expected(Kind::OpenBraceToken)
        };
        let save_context_flags = self.context_flags;
        self.set_context_flags(NodeFlags::JSDOC, true);
        let t = self.parse_js_doc_type();
        self.context_flags = save_context_flags;
        if has_brace {
            self.parse_expected_jsdoc(Kind::CloseBraceToken);
        }
        let expr = self
            .factory
            .new_js_doc_type_expression(&mut self.nodes, Some(t));
        self.finish_node(expr, pos)
    }

    /// `func (p *Parser) parseJSDocNameReference() *ast.Node`
    fn parse_jsdoc_name_reference(&mut self) -> NodeId {
        let pos = self.node_pos();
        let has_brace = self.parse_optional(Kind::OpenBraceToken);
        let entity_name = self.parse_jsdoc_link_name();
        if has_brace {
            self.parse_expected_jsdoc(Kind::CloseBraceToken);
        }
        self.scanner.reset_pos(self.scanner.token_full_start());
        self.next_token_jsdoc();
        let reference = self
            .factory
            .new_js_doc_name_reference(&mut self.nodes, entity_name);
        self.finish_node(reference, pos)
    }

    /// `func (p *Parser) parseJSDocComment(parent *ast.Node, start int, end int, fullStart int) *ast.Node`
    ///
    /// Pass `end == -1` to parse the text to the end.
    pub fn parse_jsdoc_comment(
        &mut self,
        parent: NodeId,
        start: i32,
        end: i32,
        full_start: i32,
    ) -> Option<NodeId> {
        let _ = parent;
        let mut end = end;
        if end == -1 {
            end = self.source_text.len() as i32;
        }
        // Check for /** (JSDoc opening part)
        if !is_jsdoc_like_text(&self.source_text[start as usize..]) {
            // TODO: This should be a panic, unless parseSingleJSDocComment is calling this (not ported yet)
            return None;
        }

        let save_source_text = self.source_text;
        let save_token = self.token;
        let save_context_flags = self.context_flags;
        let save_parsing_contexts = self.parsing_contexts;
        let save_scanner_state = self.scanner.mark();
        let save_diagnostics_length = self.diagnostics.len();
        let save_has_parse_error = self.has_parse_error;
        let save_has_await_identifier = self.statement_has_await_identifier;

        // initial indent is start+4 to account for leading `/** `
        // + 1 because \n is one character before the first character in the line and,
        // if there is no \n before start, -1 is one index before the first character in the string
        let last_newline = self.source_text[..start as usize]
            .rfind('\n')
            .map(|i| i as i32)
            .unwrap_or(-1);
        let initial_indent = start + 4 - (last_newline + 1);
        // -2 for trailing `*/`
        self.source_text = &self.source_text[..(end - 2) as usize];
        self.scanner.set_text(self.source_text);
        // +3 for leading `/**`
        self.scanner.reset_pos((start + 3) as usize);
        self.set_context_flags(NodeFlags::JSDOC, true);
        self.parsing_contexts |= 1 << PC_JS_DOC_COMMENT;

        let comment = self.parse_jsdoc_comment_worker(start, end, full_start, initial_indent);
        // move jsdoc diagnostics to jsdocDiagnostics -- for JS files only
        if self.context_flags.intersects(NodeFlags::JAVA_SCRIPT_FILE) {
            let tail = self.diagnostics.split_off(save_diagnostics_length);
            self.jsdoc_diagnostics.extend(tail);
        }
        self.diagnostics.truncate(save_diagnostics_length);

        self.source_text = save_source_text;
        self.scanner.set_text(self.source_text);
        self.parsing_contexts = save_parsing_contexts;
        self.context_flags = save_context_flags;
        self.scanner.rewind(save_scanner_state);
        self.token = save_token;
        self.has_parse_error = save_has_parse_error;
        self.statement_has_await_identifier = save_has_await_identifier;

        Some(comment)
    }

    /// `func (p *Parser) parseJSDocCommentWorker(start int, end int, fullStart int, indent int) *ast.Node`
    ///
    /// `offset` — the offset in the containing file; `indent` — the number of
    /// spaces to consider as the margin (applies to non-first lines only).
    fn parse_jsdoc_comment_worker(
        &mut self,
        start: i32,
        end: i32,
        full_start: i32,
        indent: i32,
    ) -> NodeId {
        // Initially we can parse out a tag.  We also have seen a starting asterisk.
        // This is so that /** * @type */ doesn't parse.
        let mut tags: Vec<NodeId> = Vec::with_capacity(1);
        let mut tags_pos: i32 = -1;
        let mut tags_end: i32 = -1;
        let mut state = JSDOC_STATE_SAW_ASTERISK;
        let mut backtick_count = 0;
        let mut in_fenced_code_block = false;
        let mut comment_parts: Vec<NodeId> = Vec::with_capacity(1);
        let mut comments: Vec<String> = std::mem::take(&mut self.jsdoc_comments_space);
        let mut comments_pos: i32 = -1;
        let mut link_end = start;
        let mut margin: i32 = -1;
        let mut indent = indent;
        macro_rules! push_comment {
            ($text:expr) => {{
                if margin == -1 {
                    margin = indent;
                }
                let t: &str = $text;
                comments.push(t.to_string());
                indent += t.len() as i32;
            }};
        }

        self.next_token_jsdoc();
        while self.parse_optional_jsdoc(Kind::WhitespaceTrivia) {}
        if self.parse_optional_jsdoc(Kind::NewLineTrivia) {
            state = JSDOC_STATE_BEGINNING_OF_LINE;
            indent = 0;
        }
        'outer: loop {
            // Detect fenced code blocks by counting consecutive backtick tokens.
            // Three or more consecutive backticks toggle the fenced code block state.
            if self.token != Kind::BacktickToken && backtick_count > 0 {
                if backtick_count >= 3 {
                    in_fenced_code_block = !in_fenced_code_block;
                }
                backtick_count = 0;
            }
            match self.token {
                Kind::AtToken => {
                    if in_fenced_code_block || !self.scanner.can_follow_jsdoc_at() {
                        if in_fenced_code_block {
                            state = JSDOC_STATE_SAVING_BACKTICKS;
                        } else {
                            state = JSDOC_STATE_SAVING_COMMENTS;
                        }
                        let t = self.scanner.token_text();
                        push_comment!(t);
                    } else {
                        comments = remove_trailing_whitespace(comments);
                        if comments_pos == -1 {
                            comments_pos = self.node_pos();
                        }
                        let tag = self.parse_tag(&tags, indent);
                        if tags_pos == -1 {
                            tags_pos = self.nodes[tag].pos();
                        }
                        tags.push(tag);
                        tags_end = self.nodes[tag].end();
                        // NOTE: According to usejsdoc.org, a tag goes to end of line, except the last tag.
                        // Real-world comments may break this rule, so "BeginningOfLine" will not be a real line beginning
                        // for malformed examples like `/** @param {string} x @returns {number} the length */`
                        state = JSDOC_STATE_BEGINNING_OF_LINE;
                        margin = -1;
                    }
                }
                Kind::NewLineTrivia => {
                    let t = self.scanner.token_text();
                    comments.push(t.to_string());
                    state = JSDOC_STATE_BEGINNING_OF_LINE;
                    indent = 0;
                }
                Kind::AsteriskToken => {
                    let asterisk = self.scanner.token_text();
                    if state == JSDOC_STATE_SAW_ASTERISK {
                        // If we've already seen an asterisk, then we can no longer parse a tag on this line
                        state = JSDOC_STATE_SAVING_COMMENTS;
                        push_comment!(asterisk);
                    } else {
                        if state != JSDOC_STATE_BEGINNING_OF_LINE {
                            panic!("state must be BeginningOfLine");
                        }
                        // Ignore the first asterisk on a line
                        state = JSDOC_STATE_SAW_ASTERISK;
                        indent += asterisk.len() as i32;
                    }
                }
                Kind::WhitespaceTrivia => {
                    if state == JSDOC_STATE_SAVING_COMMENTS || state == JSDOC_STATE_SAVING_BACKTICKS
                    {
                        panic!(
                            "whitespace shouldn't come from the scanner while saving top-level comment text"
                        );
                    }
                    // only collect whitespace if we're already saving comments or have just crossed the comment indent margin
                    let whitespace = self.scanner.token_text();
                    if margin > -1 && indent + whitespace.len() as i32 > margin {
                        let mut existing_indent = margin - indent;
                        if existing_indent < 0 {
                            existing_indent += whitespace.len() as i32;
                        }
                        if existing_indent < 0 {
                            existing_indent = 0;
                        }
                        comments.push(whitespace[existing_indent as usize..].to_string());
                    }
                    indent += whitespace.len() as i32;
                }
                Kind::EndOfFile => {
                    break 'outer;
                }
                Kind::JSDocCommentTextToken => {
                    if state != JSDOC_STATE_SAVING_BACKTICKS {
                        if in_fenced_code_block {
                            state = JSDOC_STATE_SAVING_BACKTICKS;
                        } else {
                            state = JSDOC_STATE_SAVING_COMMENTS;
                        }
                    }
                    let t = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
                    push_comment!(&t);
                }
                Kind::BacktickToken => {
                    backtick_count += 1;
                    if state == JSDOC_STATE_SAVING_BACKTICKS {
                        state = JSDOC_STATE_SAVING_COMMENTS;
                    } else {
                        state = JSDOC_STATE_SAVING_BACKTICKS;
                    }
                    let t = self.scanner.token_text();
                    push_comment!(t);
                }
                Kind::OpenBraceToken if !in_fenced_code_block => {
                    state = JSDOC_STATE_SAVING_COMMENTS;
                    let comment_end = self.scanner.token_full_start() as i32;
                    let link_start = self.scanner.token_end() as i32 - 1;
                    if let Some(link) = self.parse_jsdoc_link(link_start) {
                        if link_end == start {
                            comments = remove_leading_newlines(comments);
                        }
                        let jsdoc_text_node =
                            self.factory.new_js_doc_text(&mut self.nodes, &comments);
                        let jsdoc_text =
                            self.finish_node_with_end(jsdoc_text_node, link_end, comment_end);
                        comment_parts.push(jsdoc_text);
                        comment_parts.push(link);
                        comments.clear();
                        link_end = self.scanner.token_end() as i32;
                    } else {
                        // `fallthrough` to default case
                        if state != JSDOC_STATE_SAVING_BACKTICKS {
                            state = JSDOC_STATE_SAVING_COMMENTS;
                        }
                        let t = self.scanner.token_text();
                        push_comment!(t);
                    }
                }
                _ => {
                    // Anything else is doc comment text. We just save it. Because it
                    // wasn't a tag, we can no longer parse a tag on this line until we hit the next
                    // line break.
                    if self.token == Kind::OpenBraceToken {
                        // fenced-code `{` handled above; here only when inFencedCodeBlock
                        state = JSDOC_STATE_SAVING_BACKTICKS;
                        let t = self.scanner.token_text();
                        push_comment!(t);
                    } else {
                        if state != JSDOC_STATE_SAVING_BACKTICKS {
                            if in_fenced_code_block {
                                state = JSDOC_STATE_SAVING_BACKTICKS;
                            } else {
                                state = JSDOC_STATE_SAVING_COMMENTS;
                            }
                        }
                        let t = self.scanner.token_text();
                        push_comment!(t);
                    }
                }
            }
            if state == JSDOC_STATE_SAVING_COMMENTS || state == JSDOC_STATE_SAVING_BACKTICKS {
                self.next_jsdoc_comment_text_token(state == JSDOC_STATE_SAVING_BACKTICKS);
            } else {
                self.next_token_jsdoc();
            }
        }

        self.jsdoc_comments_space = comments;
        if comments_pos == -1 {
            comments_pos = self.scanner.token_full_start() as i32;
        }

        if !self.jsdoc_comments_space.is_empty() {
            // `comments[len-1] = strings.TrimRightFunc(..., unicode.IsSpace)`
            let comments = &mut self.jsdoc_comments_space;
            let last = comments.len() - 1;
            comments[last] = comments[last].trim_end().to_string();
            let text_node = self.factory.new_js_doc_text(&mut self.nodes, comments);
            let jsdoc_text = self.finish_node_with_end(text_node, link_end, comments_pos);
            comment_parts.push(jsdoc_text);
        }

        if !comment_parts.is_empty() && !tags.is_empty() && comments_pos == -1 {
            panic!("having parsed tags implies that the end of the comment span should be set");
        }

        let mut tags_node_list = None;
        if tags_pos != -1 {
            tags_node_list = Some(self.new_node_list(TextRange::new(tags_pos, tags_end), tags));
        }

        let comment_list = self.new_node_list(TextRange::new(start, comments_pos), comment_parts);
        let jsdoc_comment =
            self.factory
                .new_js_doc(&mut self.nodes, Some(comment_list), tags_node_list);
        self.finish_node_with_end(jsdoc_comment, full_start, end)
    }

    /// `func (p *Parser) isNextNonwhitespaceTokenEndOfFile() bool`
    fn is_next_nonwhitespace_token_end_of_file(&mut self) -> bool {
        // We must use infinite lookahead, as there could be any number of newlines :(
        loop {
            self.next_token_jsdoc();
            if self.token == Kind::EndOfFile {
                return true;
            }
            if !(self.token == Kind::WhitespaceTrivia || self.token == Kind::NewLineTrivia) {
                return false;
            }
        }
    }

    /// `func (p *Parser) skipWhitespace()`
    fn skip_whitespace(&mut self) {
        if self.token == Kind::WhitespaceTrivia || self.token == Kind::NewLineTrivia {
            if self.look_ahead(Self::is_next_nonwhitespace_token_end_of_file) {
                return;
                // Don't skip whitespace prior to EoF (or end of comment) - that shouldn't be included in any node's range
            }
        }
        while self.token == Kind::WhitespaceTrivia || self.token == Kind::NewLineTrivia {
            self.next_token_jsdoc();
        }
    }

    /// `func (p *Parser) skipWhitespaceOrAsterisk() string`
    fn skip_whitespace_or_asterisk(&mut self) -> String {
        if self.token == Kind::WhitespaceTrivia || self.token == Kind::NewLineTrivia {
            if self.look_ahead(Self::is_next_nonwhitespace_token_end_of_file) {
                return String::new();
                // Don't skip whitespace prior to EoF (or end of comment) - that shouldn't be included in any node's range
            }
        }

        let mut preceding_line_break = self.scanner.has_preceding_line_break();
        let mut seen_line_break = false;
        let mut indents: Vec<String> = Vec::with_capacity(4);
        while (preceding_line_break && self.token == Kind::AsteriskToken)
            || self.token == Kind::WhitespaceTrivia
            || self.token == Kind::NewLineTrivia
        {
            indents.push(self.scanner.token_text().to_string());
            if self.token == Kind::NewLineTrivia {
                preceding_line_break = true;
                seen_line_break = true;
                indents.clear();
            } else if self.token == Kind::AsteriskToken {
                preceding_line_break = false;
            }
            self.next_token_jsdoc();
        }
        if seen_line_break {
            indents.join("")
        } else {
            String::new()
        }
    }

    /// `func (p *Parser) parseTag(tags []*ast.Node, margin int) *ast.Node`
    fn parse_tag(&mut self, tags: &[NodeId], margin: i32) -> NodeId {
        if self.token != Kind::AtToken {
            panic!("should be called only at the start of a tag");
        }
        let start = self.scanner.token_start() as i32;
        self.next_token_jsdoc();

        let tag_name = self.parse_jsdoc_identifier_name(Some(&diagnostics::Identifier_expected));
        let indent_text = self.skip_whitespace_or_asterisk();

        let tag_text = self.nodes[tag_name].text(&self.nodes).into_owned();
        let tag = match tag_text.as_str() {
            "implements" => self.parse_implements_tag(start, tag_name, margin, &indent_text),
            "augments" | "extends" => {
                self.parse_augments_tag(start, tag_name, margin, &indent_text)
            }
            "public" => {
                let comments =
                    self.parse_trailing_tag_comments(start, self.node_pos(), margin, &indent_text);
                let node =
                    self.factory
                        .new_js_doc_public_tag(&mut self.nodes, Some(tag_name), comments);
                self.finish_node(node, start)
            }
            "private" => {
                let comments =
                    self.parse_trailing_tag_comments(start, self.node_pos(), margin, &indent_text);
                let node =
                    self.factory
                        .new_js_doc_private_tag(&mut self.nodes, Some(tag_name), comments);
                self.finish_node(node, start)
            }
            "protected" => {
                let comments =
                    self.parse_trailing_tag_comments(start, self.node_pos(), margin, &indent_text);
                let node = self.factory.new_js_doc_protected_tag(
                    &mut self.nodes,
                    Some(tag_name),
                    comments,
                );
                self.finish_node(node, start)
            }
            "readonly" => {
                let comments =
                    self.parse_trailing_tag_comments(start, self.node_pos(), margin, &indent_text);
                let node =
                    self.factory
                        .new_js_doc_readonly_tag(&mut self.nodes, Some(tag_name), comments);
                self.finish_node(node, start)
            }
            "override" => {
                let comments =
                    self.parse_trailing_tag_comments(start, self.node_pos(), margin, &indent_text);
                let node =
                    self.factory
                        .new_js_doc_override_tag(&mut self.nodes, Some(tag_name), comments);
                self.finish_node(node, start)
            }
            "deprecated" => {
                self.has_deprecated_tag = true;
                let comments =
                    self.parse_trailing_tag_comments(start, self.node_pos(), margin, &indent_text);
                let node = self.factory.new_js_doc_deprecated_tag(
                    &mut self.nodes,
                    Some(tag_name),
                    comments,
                );
                self.finish_node(node, start)
            }
            "this" => self.parse_this_tag(start, tag_name, margin, &indent_text),
            "arg" | "argument" | "param" => self.parse_parameter_or_property_tag(
                start,
                tag_name,
                PROPERTY_LIKE_PARSE_PARAMETER,
                margin,
            ),
            "return" | "returns" => {
                self.parse_return_tag(tags, start, tag_name, margin, &indent_text)
            }
            "template" => self.parse_template_tag(start, tag_name, margin, &indent_text),
            "type" => self.parse_type_tag(tags, start, tag_name, margin, &indent_text),
            "typedef" => self.parse_typedef_tag(start, tag_name, margin, &indent_text),
            "callback" => self.parse_callback_tag(start, tag_name, margin, &indent_text),
            "overload" => self.parse_overload_tag(start, tag_name, margin, &indent_text),
            "satisfies" => self.parse_satisfies_tag(start, tag_name, margin, &indent_text),
            "see" => self.parse_see_tag(start, tag_name, margin, &indent_text),
            "exception" | "throws" => self.parse_throws_tag(start, tag_name, margin, &indent_text),
            "import" => self.parse_import_tag(start, tag_name, margin, &indent_text),
            _ => self.parse_unknown_tag(start, tag_name, margin, &indent_text),
        };
        tag
    }

    /// `func (p *Parser) parseTrailingTagComments(pos int, end int, margin int, indentText string) *ast.NodeList`
    fn parse_trailing_tag_comments(
        &mut self,
        pos: i32,
        end: i32,
        margin: i32,
        indent_text: &str,
    ) -> Option<NodeList> {
        // some tags, like typedef and callback, have already parsed their comments earlier
        let mut margin = margin;
        if indent_text.is_empty() {
            margin += end - pos;
        }
        let mut initial_margin = String::new();
        if margin < indent_text.len() as i32 {
            initial_margin = indent_text[margin as usize..].to_string();
        }
        self.parse_tag_comments(margin, Some(&initial_margin))
    }

    /// `func (p *Parser) parseTagComments(indent int, initialMargin *string) *ast.NodeList`
    fn parse_tag_comments(
        &mut self,
        indent: i32,
        initial_margin: Option<&str>,
    ) -> Option<NodeList> {
        let comments_pos = self.node_pos();
        let mut comments = std::mem::take(&mut self.jsdoc_tag_comments_space);
        // !!! can parseTagComments call itself?
        let mut parts = std::mem::take(&mut self.jsdoc_tag_comments_parts_space);
        let mut link_end: i32 = -1;
        let mut state = JSDOC_STATE_BEGINNING_OF_LINE;
        let mut backtick_count = 0;
        let mut in_fenced_code_block = false;
        if indent < 0 {
            panic!("indent must be a natural number");
        }
        let mut margin: i32 = -1;
        let mut indent = indent;
        macro_rules! push_comment {
            ($text:expr) => {{
                if margin == -1 {
                    margin = indent;
                }
                let t: &str = $text;
                comments.push(t.to_string());
                indent += t.len() as i32;
            }};
        }

        if let Some(initial_margin) = initial_margin {
            // jump straight to saving comments if there is some initial indentation
            if !initial_margin.is_empty() {
                push_comment!(initial_margin);
            }
            state = JSDOC_STATE_SAW_ASTERISK;
        }
        let mut tok = self.token;
        'outer: loop {
            // Detect fenced code blocks by counting consecutive backtick tokens.
            // Three or more consecutive backticks toggle the fenced code block state.
            if tok != Kind::BacktickToken && backtick_count > 0 {
                if backtick_count >= 3 {
                    in_fenced_code_block = !in_fenced_code_block;
                }
                backtick_count = 0;
            }
            match tok {
                Kind::NewLineTrivia => {
                    state = JSDOC_STATE_BEGINNING_OF_LINE;
                    // don't use pushComment here because we want to keep the margin unchanged
                    let t = self.scanner.token_text();
                    comments.push(t.to_string());
                    indent = 0;
                }
                Kind::AtToken => {
                    if !in_fenced_code_block && self.scanner.can_follow_jsdoc_at() {
                        self.scanner.reset_pos(self.scanner.token_end() - 1);
                        break 'outer;
                    }
                    if in_fenced_code_block {
                        state = JSDOC_STATE_SAVING_BACKTICKS;
                    } else {
                        state = JSDOC_STATE_SAVING_COMMENTS;
                    }
                    let t = self.scanner.token_text();
                    push_comment!(t);
                }
                Kind::EndOfFile => {
                    // Done
                    break 'outer;
                }
                Kind::WhitespaceTrivia => {
                    if state == JSDOC_STATE_SAVING_COMMENTS || state == JSDOC_STATE_SAVING_BACKTICKS
                    {
                        panic!(
                            "whitespace shouldn't come from the scanner while saving comment text"
                        );
                    }
                    let whitespace = self.scanner.token_text();
                    // if the whitespace crosses the margin, take only the whitespace that passes the margin
                    if margin > -1 && indent + whitespace.len() as i32 > margin {
                        let cut = std::cmp::max(margin - indent, 0) as usize;
                        comments.push(whitespace[cut..].to_string());
                        if in_fenced_code_block {
                            state = JSDOC_STATE_SAVING_BACKTICKS;
                        } else {
                            state = JSDOC_STATE_SAVING_COMMENTS;
                        }
                    }
                    indent += whitespace.len() as i32;
                }
                Kind::OpenBraceToken if !in_fenced_code_block => {
                    state = JSDOC_STATE_SAVING_COMMENTS;
                    let comment_end = self.scanner.token_full_start() as i32;
                    let link_start = self.scanner.token_end() as i32 - 1;
                    if let Some(link) = self.parse_jsdoc_link(link_start) {
                        let comment_start = if link_end > -1 {
                            link_end
                        } else {
                            comments_pos
                        };
                        let text_node = self.factory.new_js_doc_text(&mut self.nodes, &comments);
                        let text = self.finish_node_with_end(text_node, comment_start, comment_end);
                        parts.push(text);
                        parts.push(link);
                        comments.clear();
                        link_end = self.scanner.token_end() as i32;
                    } else {
                        let t = self.scanner.token_text();
                        push_comment!(t);
                    }
                }
                Kind::BacktickToken => {
                    backtick_count += 1;
                    if state == JSDOC_STATE_SAVING_BACKTICKS {
                        state = JSDOC_STATE_SAVING_COMMENTS;
                    } else {
                        state = JSDOC_STATE_SAVING_BACKTICKS;
                    }
                    let t = self.scanner.token_text();
                    push_comment!(t);
                }
                Kind::JSDocCommentTextToken => {
                    if state != JSDOC_STATE_SAVING_BACKTICKS {
                        if in_fenced_code_block {
                            state = JSDOC_STATE_SAVING_BACKTICKS;
                        } else {
                            state = JSDOC_STATE_SAVING_COMMENTS;
                        }
                        // leading identifiers start recording as well
                    }
                    let t = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
                    push_comment!(&t);
                }
                Kind::AsteriskToken if state == JSDOC_STATE_BEGINNING_OF_LINE => {
                    // leading asterisks start recording on the *next* (non-whitespace) token
                    state = JSDOC_STATE_SAW_ASTERISK;
                    indent += 1;
                }
                _ => {
                    // record the * as a comment (AsteriskToken falls through)
                    if state != JSDOC_STATE_SAVING_BACKTICKS {
                        if in_fenced_code_block {
                            state = JSDOC_STATE_SAVING_BACKTICKS;
                        } else {
                            state = JSDOC_STATE_SAVING_COMMENTS;
                        }
                        // leading identifiers start recording as well
                    }
                    let t = self.scanner.token_text();
                    push_comment!(t);
                }
            }
            if state == JSDOC_STATE_SAVING_COMMENTS || state == JSDOC_STATE_SAVING_BACKTICKS {
                tok = self.next_jsdoc_comment_text_token(state == JSDOC_STATE_SAVING_BACKTICKS);
            } else {
                tok = self.next_token_jsdoc();
            }
        }

        // `p.jsdocTagCommentsSpace = comments[:0]` — return the buffer for reuse.
        let mut comments = remove_trailing_whitespace(remove_leading_newlines(comments));
        if !comments.is_empty() {
            let comment_start = if link_end > -1 {
                link_end
            } else {
                comments_pos
            };
            let text_node = self.factory.new_js_doc_text(&mut self.nodes, &comments);
            let text = self.finish_node(text_node, comment_start);
            parts.push(text);
        }
        comments.clear();
        self.jsdoc_tag_comments_space = comments;

        // `p.jsdocTagCommentsPartsSpace = parts[:0]`
        if !parts.is_empty() {
            let tok_end = self.scanner.token_end() as i32;
            let result = self.new_node_list(TextRange::new(comments_pos, tok_end), parts);
            return Some(result);
        }
        self.jsdoc_tag_comments_parts_space = parts;
        None
    }

    /// `func (p *Parser) parseJSDocLink(start int) *ast.Node`
    fn parse_jsdoc_link(&mut self, start: i32) -> Option<NodeId> {
        let state = self.mark();
        let Some(link_type) = self.parse_jsdoc_link_prefix() else {
            self.rewind(state);
            return None;
        };
        self.next_token_jsdoc();
        // start at token after link, then skip any whitespace
        self.skip_whitespace();
        let name = self.parse_jsdoc_link_name();
        let mut text: Vec<String> = Vec::new();
        while self.token != Kind::CloseBraceToken
            && self.token != Kind::NewLineTrivia
            && self.token != Kind::EndOfFile
        {
            text.push(self.scanner.token_text().to_string());
            self.next_token_jsdoc(); // Couldn't this be nextTokenCommentJSDoc?
        }
        let create = match link_type.as_str() {
            "link" => self.factory.new_js_doc_link(&mut self.nodes, name, &text),
            "linkcode" => self
                .factory
                .new_js_doc_link_code(&mut self.nodes, name, &text),
            _ => self
                .factory
                .new_js_doc_link_plain(&mut self.nodes, name, &text),
        };
        let end = self.scanner.token_end() as i32;
        Some(self.finish_node_with_end(create, start, end))
    }

    /// `func (p *Parser) parseJSDocLinkName() *ast.Node`
    fn parse_jsdoc_link_name(&mut self) -> Option<NodeId> {
        if token_is_identifier_or_keyword(self.token) {
            let pos = self.node_pos();
            let mut name = self.parse_identifier_name();
            while self.parse_optional(Kind::DotToken) {
                let right = if self.token == Kind::PrivateIdentifier {
                    self.create_missing_identifier()
                } else {
                    self.parse_identifier_name()
                };
                let qn = self
                    .factory
                    .new_qualified_name(&mut self.nodes, Some(name), Some(right));
                name = self.finish_node(qn, pos);
            }
            while self.token == Kind::PrivateIdentifier {
                self.scanner.rescan_hash_token();
                self.next_token_jsdoc();
                let right = self.parse_identifier();
                let qn = self
                    .factory
                    .new_qualified_name(&mut self.nodes, Some(name), Some(right));
                name = self.finish_node(qn, pos);
            }
            return Some(name);
        }
        None
    }

    /// `func (p *Parser) parseJSDocLinkPrefix() (string, bool)`
    fn parse_jsdoc_link_prefix(&mut self) -> Option<String> {
        self.skip_whitespace_or_asterisk();
        if self.token == Kind::OpenBraceToken
            && self.next_token_jsdoc() == Kind::AtToken
            && token_is_identifier_or_keyword(self.next_token_jsdoc())
        {
            let kind = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
            if is_jsdoc_link_tag(&kind) {
                return Some(kind);
            }
        }
        None
    }

    /// `func (p *Parser) parseUnknownTag(start int, tagName *ast.IdentifierNode, indent int, indentText string) *ast.Node`
    fn parse_unknown_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        indent: i32,
        indent_text: &str,
    ) -> NodeId {
        let comments =
            self.parse_trailing_tag_comments(start, self.node_pos(), indent, indent_text);
        let tag = self
            .factory
            .new_js_doc_unknown_tag(&mut self.nodes, Some(tag_name), comments);
        self.finish_node(tag, start)
    }

    /// `func (p *Parser) tryParseTypeExpression() *ast.Node`
    fn try_parse_type_expression(&mut self) -> Option<NodeId> {
        self.skip_whitespace_or_asterisk();
        if self.token == Kind::OpenBraceToken {
            return Some(self.parse_jsdoc_type_expression(false /*mayOmitBraces*/));
        }
        None
    }

    /// `func (p *Parser) parseBracketNameInPropertyAndParamTag(target propertyLikeParse) (name *ast.EntityName, isBracketed bool)`
    fn parse_bracket_name_in_property_and_param_tag(
        &mut self,
        target: PropertyLikeParse,
    ) -> (Option<NodeId>, bool) {
        // Looking for something like '[foo]', 'foo', '[foo.bar]' or 'foo.bar'
        let is_bracketed = self.parse_optional_jsdoc(Kind::OpenBracketToken);
        if is_bracketed {
            self.skip_whitespace();
        }
        // a markdown-quoted name: `arg` is not legal jsdoc, but occurs in the wild
        let is_backquoted = self.parse_optional_jsdoc(Kind::BacktickToken);
        let diagnostic = if target == PROPERTY_LIKE_PARSE_PARAMETER {
            None
        } else {
            Some(&diagnostics::Identifier_expected)
        };
        let name = self.parse_jsdoc_entity_name(diagnostic);
        if is_backquoted {
            self.parse_expected_token_jsdoc(Kind::BacktickToken);
        }
        if is_bracketed {
            self.skip_whitespace();
            // May have an optional default, e.g. '[foo = 42]'
            if self.parse_optional_token(Kind::EqualsToken).is_some() {
                self.parse_expression();
            }

            self.parse_expected(Kind::CloseBracketToken);
        }

        (name, is_bracketed)
    }

    /// `func (p *Parser) parseParameterOrPropertyTag(start int, tagName *ast.IdentifierNode, target propertyLikeParse, indent int) *ast.Node`
    fn parse_parameter_or_property_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        target: PropertyLikeParse,
        indent: i32,
    ) -> NodeId {
        let mut type_expression = self.try_parse_type_expression();
        let mut is_name_first = type_expression.is_none();
        self.skip_whitespace_or_asterisk();

        let (name, is_bracketed) = self.parse_bracket_name_in_property_and_param_tag(target);
        let indent_text = self.skip_whitespace_or_asterisk();

        if is_name_first && self.look_ahead(|p| p.parse_jsdoc_link_prefix().is_none()) {
            type_expression = self.try_parse_type_expression();
        }

        let comment =
            self.parse_trailing_tag_comments(start, self.node_pos(), indent, &indent_text);

        let nested_type_literal =
            self.parse_nested_type_literal(type_expression, name, target, indent);
        if let Some(nested_type_literal) = nested_type_literal {
            type_expression = Some(nested_type_literal);
            is_name_first = true;
        }
        let kind = if target == PROPERTY_LIKE_PARSE_PROPERTY {
            Kind::JSDocPropertyTag
        } else {
            Kind::JSDocParameterTag
        };
        let result = self.factory.new_js_doc_parameter_or_property_tag(
            &mut self.nodes,
            kind,
            Some(tag_name),
            name,
            is_bracketed,
            type_expression,
            is_name_first,
            comment,
        );
        self.finish_node(result, start)
    }

    /// `func (p *Parser) parseNestedTypeLiteral(typeExpression *ast.Node, name *ast.EntityName, target propertyLikeParse, indent int) *ast.Node`
    fn parse_nested_type_literal(
        &mut self,
        type_expression: Option<NodeId>,
        name: Option<NodeId>,
        target: PropertyLikeParse,
        indent: i32,
    ) -> Option<NodeId> {
        if let Some(type_expression) = type_expression
            && is_object_or_object_array_type_reference(
                self.nodes[type_expression].type_(),
                &self.nodes,
            )
        {
            let pos = self.node_pos();
            let mut children: Vec<NodeId> = Vec::new();
            loop {
                let state = self.mark();
                let child = self.parse_child_parameter_or_property_tag(target, indent, name);
                match child {
                    None => {
                        self.rewind(state);
                        break;
                    }
                    Some(child) => match self.nodes[child].kind {
                        Kind::JSDocParameterTag | Kind::JSDocPropertyTag => {
                            children.push(child);
                        }
                        Kind::JSDocTemplateTag => {
                            let loc = self.nodes[child]
                                .tag_name()
                                .map(|t| self.nodes[t].loc)
                                .unwrap_or_default();
                            self.parse_error_at_range(
                                loc,
                                &diagnostics::A_JSDoc_template_tag_may_not_follow_a_typedef_callback_or_overload_tag,
                                &[],
                            );
                        }
                        _ => {}
                    },
                }
            }
            if !children.is_empty() {
                let is_array_type = self.nodes[type_expression]
                    .type_()
                    .is_some_and(|t| self.nodes[t].kind == Kind::ArrayType);
                let literal_node =
                    self.factory
                        .new_js_doc_type_literal(&mut self.nodes, &children, is_array_type);
                let literal = self.finish_node(literal_node, pos);
                let expr = self
                    .factory
                    .new_js_doc_type_expression(&mut self.nodes, Some(literal));
                return Some(self.finish_node(expr, pos));
            }
        }
        None
    }

    /// `func (p *Parser) parseReturnTag(previousTags []*ast.Node, start int, tagName *ast.IdentifierNode, indent int, indentText string) *ast.Node`
    fn parse_return_tag(
        &mut self,
        previous_tags: &[NodeId],
        start: i32,
        tag_name: NodeId,
        indent: i32,
        indent_text: &str,
    ) -> NodeId {
        if previous_tags
            .iter()
            .any(|&t| self.nodes[t].kind == Kind::JSDocReturnTag)
        {
            let pos = self.nodes[tag_name].pos();
            let end = self.scanner.token_start() as i32;
            let arg = self.nodes[tag_name].text(&self.nodes).into_owned();
            self.parse_error_at(pos, end, &diagnostics::X_0_tag_already_specified, &[arg]);
        }

        let type_expression = self.try_parse_type_expression();
        let comments =
            self.parse_trailing_tag_comments(start, self.node_pos(), indent, indent_text);
        let tag = self.factory.new_js_doc_return_tag(
            &mut self.nodes,
            Some(tag_name),
            type_expression,
            comments,
        );
        self.finish_node(tag, start)
    }

    /// `func (p *Parser) parseTypeTag(previousTags []*ast.Node, start int, tagName *ast.IdentifierNode, indent int, indentText string) *ast.Node`
    ///
    /// pass `indent == -1` to skip parsing trailing comments (as when a type
    /// tag is nested in a typedef)
    fn parse_type_tag(
        &mut self,
        previous_tags: &[NodeId],
        start: i32,
        tag_name: NodeId,
        indent: i32,
        indent_text: &str,
    ) -> NodeId {
        if previous_tags
            .iter()
            .any(|&t| self.nodes[t].kind == Kind::JSDocTypeTag)
        {
            let pos = self.nodes[tag_name].pos();
            let end = self.scanner.token_start() as i32;
            let arg = self.nodes[tag_name].text(&self.nodes).into_owned();
            self.parse_error_at(pos, end, &diagnostics::X_0_tag_already_specified, &[arg]);
        }

        let type_expression = self.parse_jsdoc_type_expression(true);
        let mut comments = None;
        if indent != -1 {
            comments =
                self.parse_trailing_tag_comments(start, self.node_pos(), indent, indent_text);
        }
        let tag = self.factory.new_js_doc_type_tag(
            &mut self.nodes,
            Some(tag_name),
            Some(type_expression),
            comments,
        );
        self.finish_node(tag, start)
    }

    /// `func (p *Parser) parseSeeTag(start int, tagName *ast.IdentifierNode, indent int, indentText string) *ast.Node`
    fn parse_see_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        indent: i32,
        indent_text: &str,
    ) -> NodeId {
        let has_name_reference = self.is_identifier()
            && !self.source_text[self.scanner.token_end()..].starts_with("://")
            || self.token == Kind::OpenBraceToken
                && self.look_ahead(Self::next_token_is_identifier_or_keyword);
        let mut name_expression = None;
        if has_name_reference {
            name_expression = Some(self.parse_jsdoc_name_reference());
        }
        let comments =
            self.parse_trailing_tag_comments(start, self.node_pos(), indent, indent_text);
        let tag = self.factory.new_js_doc_see_tag(
            &mut self.nodes,
            Some(tag_name),
            name_expression,
            comments,
        );
        self.finish_node(tag, start)
    }

    /// `func (p *Parser) parseImplementsTag(start int, tagName *ast.IdentifierNode, margin int, indentText string) *ast.Node`
    fn parse_implements_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        margin: i32,
        indent_text: &str,
    ) -> NodeId {
        let class_name = self.parse_expression_with_type_arguments_for_augments();
        let comments =
            self.parse_trailing_tag_comments(start, self.node_pos(), margin, indent_text);
        let tag = self.factory.new_js_doc_implements_tag(
            &mut self.nodes,
            Some(tag_name),
            Some(class_name),
            comments,
        );
        self.finish_node(tag, start)
    }

    /// `func (p *Parser) parseAugmentsTag(start int, tagName *ast.IdentifierNode, margin int, indentText string) *ast.Node`
    fn parse_augments_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        margin: i32,
        indent_text: &str,
    ) -> NodeId {
        let class_name = self.parse_expression_with_type_arguments_for_augments();
        let comments =
            self.parse_trailing_tag_comments(start, self.node_pos(), margin, indent_text);
        let tag = self.factory.new_js_doc_augments_tag(
            &mut self.nodes,
            Some(tag_name),
            Some(class_name),
            comments,
        );
        self.finish_node(tag, start)
    }

    /// `func (p *Parser) parseSatisfiesTag(start int, tagName *ast.IdentifierNode, margin int, indentText string) *ast.Node`
    fn parse_satisfies_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        margin: i32,
        indent_text: &str,
    ) -> NodeId {
        let type_expression = self.parse_jsdoc_type_expression(false);
        let comments =
            self.parse_trailing_tag_comments(start, self.node_pos(), margin, indent_text);
        let tag = self.factory.new_js_doc_satisfies_tag(
            &mut self.nodes,
            Some(tag_name),
            Some(type_expression),
            comments,
        );
        self.finish_node(tag, start)
    }

    /// `func (p *Parser) parseThrowsTag(start int, tagName *ast.IdentifierNode, margin int, indentText string) *ast.Node`
    fn parse_throws_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        margin: i32,
        indent_text: &str,
    ) -> NodeId {
        let type_expression = self.try_parse_type_expression();
        let comment = self.parse_trailing_tag_comments(start, self.node_pos(), margin, indent_text);
        let tag = self.factory.new_js_doc_throws_tag(
            &mut self.nodes,
            Some(tag_name),
            type_expression,
            comment,
        );
        self.finish_node(tag, start)
    }

    /// `func (p *Parser) parseImportTag(start int, tagName *ast.IdentifierNode, margin int, indentText string) *ast.Node`
    fn parse_import_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        margin: i32,
        indent_text: &str,
    ) -> NodeId {
        let after_import_tag_pos = self.scanner.token_full_start() as i32;

        let mut identifier = None;
        if self.is_identifier() {
            identifier = Some(self.parse_identifier());
        }

        let import_clause = self.try_parse_import_clause(
            identifier,
            after_import_tag_pos,
            Kind::TypeKeyword,
            true, /*skipJSDocLeadingAsterisks*/
        );
        let module_specifier = self.parse_module_specifier();
        let attributes = self.try_parse_import_attributes();

        let comments =
            self.parse_trailing_tag_comments(start, self.node_pos(), margin, indent_text);
        let tag = self.factory.new_js_doc_import_tag(
            &mut self.nodes,
            Some(tag_name),
            import_clause,
            module_specifier,
            attributes,
            comments,
        );
        self.finish_node(tag, start)
    }

    /// `func (p *Parser) parseExpressionWithTypeArgumentsForAugments() *ast.Node`
    fn parse_expression_with_type_arguments_for_augments(&mut self) -> NodeId {
        let used_brace = self.parse_optional(Kind::OpenBraceToken);
        let pos = self.node_pos();
        let expression = self.parse_property_access_entity_name_expression();
        self.scanner.set_skip_jsdoc_leading_asterisks(true);
        let type_arguments = self.parse_type_arguments();
        self.scanner.set_skip_jsdoc_leading_asterisks(false);
        let node = self.factory.new_expression_with_type_arguments(
            &mut self.nodes,
            Some(expression),
            type_arguments,
        );
        let node = self.finish_node(node, pos);
        if used_brace {
            self.skip_whitespace();
            self.parse_expected(Kind::CloseBraceToken);
        }
        node
    }

    /// `func (p *Parser) parsePropertyAccessEntityNameExpression() *ast.Node`
    fn parse_property_access_entity_name_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        let mut node = self.parse_jsdoc_identifier_name(Some(&diagnostics::Identifier_expected));
        while self.parse_optional(Kind::DotToken) {
            let name = self.parse_jsdoc_identifier_name(Some(&diagnostics::Identifier_expected));
            let pae = self.factory.new_property_access_expression(
                &mut self.nodes,
                Some(node),
                None,
                Some(name),
                NodeFlags::NONE,
            );
            node = self.finish_node(pae, pos);
        }
        node
    }

    /// `func (p *Parser) parseThisTag(start int, tagName *ast.IdentifierNode, margin int, indentText string) *ast.Node`
    fn parse_this_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        margin: i32,
        indent_text: &str,
    ) -> NodeId {
        let type_expression = self.parse_jsdoc_type_expression(true);
        self.skip_whitespace();
        let comments =
            self.parse_trailing_tag_comments(start, self.node_pos(), margin, indent_text);
        let result = self.factory.new_js_doc_this_tag(
            &mut self.nodes,
            Some(tag_name),
            Some(type_expression),
            comments,
        );
        self.finish_node(result, start)
    }

    /// `func (p *Parser) parseJSDocTypeNameWithNamespace(nested bool) *ast.Node`
    fn parse_jsdoc_type_name_with_namespace(&mut self, nested: bool) -> Option<NodeId> {
        let start = self.scanner.token_start() as i32;
        if !token_is_identifier_or_keyword(self.token) {
            return None;
        }
        let type_name_or_namespace_name = self.parse_jsdoc_identifier_name(None);
        if self.parse_optional_jsdoc(Kind::DotToken) {
            let body = self.parse_jsdoc_type_name_with_namespace(true /*nested*/);
            let jsdoc_namespace_node = self.factory.new_module_declaration(
                &mut self.nodes,
                None,                   /*modifiers*/
                Kind::NamespaceKeyword, /*keyword*/
                Some(type_name_or_namespace_name),
                None, /*attributes*/
                body,
            );
            if nested {
                self.nodes[jsdoc_namespace_node].flags |= NodeFlags::NESTED_NAMESPACE;
            }
            return Some(self.finish_node(jsdoc_namespace_node, start));
        }
        if nested {
            self.nodes[type_name_or_namespace_name].flags |=
                NodeFlags::IDENTIFIER_IS_IN_JSDOC_NAMESPACE;
        }
        Some(type_name_or_namespace_name)
    }

    /// `func (p *Parser) parseTypedefTag(start int, tagName *ast.IdentifierNode, indent int, indentText string) *ast.Node`
    fn parse_typedef_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        indent: i32,
        indent_text: &str,
    ) -> NodeId {
        let mut type_expression = self.try_parse_type_expression();
        self.skip_whitespace_or_asterisk();
        let mut full_name = self.parse_jsdoc_type_name_with_namespace(false /*nested*/);
        if full_name.is_none() {
            full_name =
                Some(self.parse_jsdoc_identifier_name(Some(&diagnostics::Identifier_expected)));
        }
        self.skip_whitespace();
        let mut comment = self.parse_tag_comments(indent, None);

        let mut end: i32 = -1;
        let mut has_children = false;
        if type_expression.is_none()
            || is_object_or_object_array_type_reference(
                self.nodes[type_expression.unwrap()].type_(),
                &self.nodes,
            )
        {
            let mut child_type_tag: Option<NodeId> = None;
            let mut jsdoc_property_tags: Vec<NodeId> = Vec::new();
            loop {
                let state = self.mark();
                let child = self.parse_child_property_tag(indent);
                let Some(child) = child else {
                    self.rewind(state);
                    break;
                };
                has_children = true;
                match self.nodes[child].kind {
                    Kind::JSDocTemplateTag => {
                        let loc = self.nodes[child]
                            .tag_name()
                            .map(|t| self.nodes[t].loc)
                            .unwrap_or_default();
                        self.parse_error_at_range(
                            loc,
                            &diagnostics::A_JSDoc_template_tag_may_not_follow_a_typedef_callback_or_overload_tag,
                            &[],
                        );
                    }
                    Kind::JSDocTypeTag => {
                        if child_type_tag.is_none() {
                            child_type_tag = Some(child);
                        } else {
                            let last_error = self.parse_error_at_current_token(
                                &diagnostics::A_JSDoc_typedef_comment_may_not_contain_multiple_type_tags,
                                &[],
                            );
                            if let Some(last_error) = last_error {
                                let related = tsc_ast::diagnostic::new_diagnostic::<String>(
                                    None,
                                    TextRange::new(0, 0),
                                    &diagnostics::The_tag_was_first_specified_here,
                                    &[],
                                );
                                lock_diagnostic(&last_error).add_related_info(Some(related));
                            }
                        }
                    }
                    _ => {
                        jsdoc_property_tags.push(child);
                    }
                }
            }
            if has_children {
                let is_array_type = type_expression.is_some_and(|te| {
                    self.nodes[te]
                        .type_()
                        .is_some_and(|t| self.nodes[t].kind == Kind::ArrayType)
                });
                let jsdoc_type_literal = self.factory.new_js_doc_type_literal(
                    &mut self.nodes,
                    &jsdoc_property_tags,
                    is_array_type,
                );
                let child_type_expression =
                    child_type_tag.and_then(|c| self.nodes[c].as_js_doc_type_tag().type_expression);
                if let Some(child_type_expression) = child_type_expression
                    && !is_object_or_object_array_type_reference(
                        self.nodes[child_type_expression].type_(),
                        &self.nodes,
                    )
                {
                    type_expression = Some(child_type_expression);
                } else {
                    // !!! This differs from Strada but prevents a crash
                    let mut pos = start;
                    if !jsdoc_property_tags.is_empty() {
                        pos = self.nodes[jsdoc_property_tags[0]].pos();
                    }
                    type_expression = Some(self.finish_node(jsdoc_type_literal, pos));
                }
                end = self.nodes[type_expression.unwrap()].end();
            }
        }

        // Only include the characters between the name end and the next token if a comment was actually parsed out - otherwise it's just whitespace
        if end == -1 {
            if has_children && type_expression.is_some() {
                end = self.nodes[type_expression.unwrap()].end();
            } else if comment.is_some() {
                end = self.node_pos();
            } else if let Some(full_name) = full_name {
                end = self.nodes[full_name].end();
            } else if let Some(type_expression) = type_expression {
                end = self.nodes[type_expression].end();
            } else {
                end = self.nodes[tag_name].end();
            }
        }

        if comment.is_none() {
            comment = self.parse_trailing_tag_comments(start, end, indent, indent_text);
        }

        let typedef_tag_node = self.factory.new_js_doc_typedef_tag(
            &mut self.nodes,
            Some(tag_name),
            type_expression,
            full_name,
            comment,
        );
        let typedef_tag = self.finish_node_with_end(typedef_tag_node, start, end);
        if let Some(type_expression) = type_expression {
            self.nodes[type_expression].parent = Some(typedef_tag); // forcibly overwrite parent potentially set by inner type expression parse
        }
        typedef_tag
    }

    /// `func (p *Parser) parseCallbackTagParameters(indent int) *ast.NodeList`
    fn parse_callback_tag_parameters(&mut self, indent: i32) -> NodeList {
        let mut parameters: Vec<NodeId> = Vec::new();
        let pos = self.node_pos();
        loop {
            let state = self.mark();
            let child = self.parse_child_parameter_or_property_tag(
                PROPERTY_LIKE_PARSE_CALLBACK_PARAMETER,
                indent,
                None,
            );
            let Some(child) = child else {
                self.rewind(state);
                break;
            };
            if self.nodes[child].kind == Kind::JSDocTemplateTag {
                let loc = self.nodes[child]
                    .tag_name()
                    .map(|t| self.nodes[t].loc)
                    .unwrap_or_default();
                self.parse_error_at_range(
                    loc,
                    &diagnostics::A_JSDoc_template_tag_may_not_follow_a_typedef_callback_or_overload_tag,
                    &[],
                );
            } else {
                parameters.push(child);
            }
        }
        let end = self.node_pos();
        self.new_node_list(TextRange::new(pos, end), parameters)
    }

    /// `func (p *Parser) parseJSDocSignature(start int, indent int) *ast.Node`
    fn parse_jsdoc_signature(&mut self, start: i32, indent: i32) -> NodeId {
        let parameters = self.parse_callback_tag_parameters(indent);
        let mut return_tag = None;
        let state = self.mark();
        if self.parse_optional_jsdoc(Kind::AtToken) {
            let tag = self.parse_tag(&[], indent);
            if self.nodes[tag].kind == Kind::JSDocReturnTag {
                return_tag = Some(tag);
            }
        }
        if return_tag.is_none() {
            self.rewind(state);
        }
        let sig =
            self.factory
                .new_js_doc_signature(&mut self.nodes, None, Some(parameters), return_tag);
        self.finish_node(sig, start)
    }

    /// `func (p *Parser) parseCallbackTag(start int, tagName *ast.IdentifierNode, indent int, indentText string) *ast.Node`
    fn parse_callback_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        indent: i32,
        indent_text: &str,
    ) -> NodeId {
        let mut full_name = self.parse_jsdoc_type_name_with_namespace(false /*nested*/);
        if full_name.is_none() {
            full_name =
                Some(self.parse_jsdoc_identifier_name(Some(&diagnostics::Identifier_expected)));
        }
        self.skip_whitespace();
        let mut comment = self.parse_tag_comments(indent, None);
        let type_expression = self.parse_jsdoc_signature(self.node_pos(), indent);
        if comment.is_none() {
            comment = self.parse_trailing_tag_comments(start, self.node_pos(), indent, indent_text);
        }
        let end = if comment.is_some() {
            self.node_pos()
        } else {
            self.nodes[type_expression].end()
        };
        let tag = self.factory.new_js_doc_callback_tag(
            &mut self.nodes,
            Some(tag_name),
            Some(type_expression),
            full_name,
            comment,
        );
        self.finish_node_with_end(tag, start, end)
    }

    /// `func (p *Parser) parseOverloadTag(start int, tagName *ast.IdentifierNode, indent int, indentText string) *ast.Node`
    fn parse_overload_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        indent: i32,
        indent_text: &str,
    ) -> NodeId {
        self.skip_whitespace();
        let mut comment = self.parse_tag_comments(indent, None);
        let type_expression = self.parse_jsdoc_signature(start, indent);
        if comment.is_none() {
            comment = self.parse_trailing_tag_comments(start, self.node_pos(), indent, indent_text);
        }
        let end = if comment.is_some() {
            self.node_pos()
        } else {
            self.nodes[type_expression].end()
        };
        let tag = self.factory.new_js_doc_overload_tag(
            &mut self.nodes,
            Some(tag_name),
            Some(type_expression),
            comment,
        );
        self.finish_node_with_end(tag, start, end)
    }

    /// `func (p *Parser) parseChildPropertyTag(indent int) *ast.Node`
    fn parse_child_property_tag(&mut self, indent: i32) -> Option<NodeId> {
        self.parse_child_parameter_or_property_tag(PROPERTY_LIKE_PARSE_PROPERTY, indent, None)
    }

    /// `func (p *Parser) parseChildParameterOrPropertyTag(target propertyLikeParse, indent int, name *ast.EntityName) *ast.Node`
    fn parse_child_parameter_or_property_tag(
        &mut self,
        target: PropertyLikeParse,
        indent: i32,
        name: Option<NodeId>,
    ) -> Option<NodeId> {
        let mut can_parse_tag = true;
        let mut seen_asterisk = false;
        loop {
            match self.next_token_jsdoc() {
                Kind::AtToken => {
                    if can_parse_tag && self.scanner.can_follow_jsdoc_at() {
                        let child = self.try_parse_child_tag(target, indent);
                        // `(child.Kind == param|prop) && (IsIdentifier(child.Name()) || !textsEqual(name, child.Name().AsQualifiedName().Left))`
                        // -> the child is a sub-property of another param — bail
                        let is_unrelated_child = child.is_some_and(|child| {
                            name.is_some_and(|name| {
                                (self.nodes[child].kind == Kind::JSDocParameterTag
                                    || self.nodes[child].kind == Kind::JSDocPropertyTag)
                                    && match self.nodes[child].name() {
                                        Some(cn) if is_identifier(&self.nodes[cn]) => true,
                                        Some(cn) if self.nodes[cn].kind == Kind::QualifiedName => {
                                            match self.nodes[cn].as_qualified_name().left {
                                                Some(left) => !texts_equal(&self.nodes, name, left),
                                                None => true,
                                            }
                                        }
                                        _ => false,
                                    }
                            })
                        });
                        if is_unrelated_child {
                            return None;
                        }
                        return child;
                    }
                    seen_asterisk = false;
                }
                Kind::NewLineTrivia => {
                    can_parse_tag = true;
                    seen_asterisk = false;
                }
                Kind::AsteriskToken => {
                    if seen_asterisk {
                        can_parse_tag = false;
                    }
                    seen_asterisk = true;
                }
                Kind::Identifier => {
                    can_parse_tag = false;
                }
                Kind::EndOfFile => {
                    return None;
                }
                _ => {}
            }
        }
    }

    /// `func (p *Parser) tryParseChildTag(target propertyLikeParse, indent int) *ast.Node`
    fn try_parse_child_tag(&mut self, target: PropertyLikeParse, indent: i32) -> Option<NodeId> {
        if self.token != Kind::AtToken {
            panic!("should only be called when at @");
        }
        let start = self.scanner.token_full_start() as i32;
        self.next_token_jsdoc();

        let tag_name = self.parse_jsdoc_identifier_name(Some(&diagnostics::Identifier_expected));
        let indent_text = self.skip_whitespace_or_asterisk();
        let t: PropertyLikeParse;
        let tag_text = self.nodes[tag_name].text(&self.nodes).into_owned();
        match tag_text.as_str() {
            "type" => {
                if target == PROPERTY_LIKE_PARSE_PROPERTY {
                    return Some(self.parse_type_tag(&[], start, tag_name, -1, ""));
                }
                return None;
            }
            "prop" | "property" => {
                t = PROPERTY_LIKE_PARSE_PROPERTY;
            }
            "arg" | "argument" | "param" => {
                t = PROPERTY_LIKE_PARSE_PARAMETER | PROPERTY_LIKE_PARSE_CALLBACK_PARAMETER;
            }
            "template" => {
                return Some(self.parse_template_tag(start, tag_name, indent, &indent_text));
            }
            "this" => {
                return Some(self.parse_this_tag(start, tag_name, indent, &indent_text));
            }
            _ => {
                return None;
            }
        }
        if (target & t) == 0 {
            return None;
        }
        Some(self.parse_parameter_or_property_tag(start, tag_name, target, indent))
    }

    /// `func (p *Parser) parseTemplateTagTypeParameter() *ast.Node`
    fn parse_template_tag_type_parameter(&mut self) -> Option<NodeId> {
        let type_parameter_pos = self.node_pos();
        let is_bracketed = self.parse_optional_jsdoc(Kind::OpenBracketToken);
        if is_bracketed {
            self.skip_whitespace();
        }

        let modifiers = self.parse_modifiers_ex(false, true /*permitConstAsModifier*/, false);
        let name = self.parse_jsdoc_identifier_name(Some(
            &diagnostics::Unexpected_token_A_type_parameter_name_was_expected_without_curly_braces,
        ));
        let mut default_type = None;
        if is_bracketed {
            self.skip_whitespace();
            self.parse_expected(Kind::EqualsToken);
            let save_context_flags = self.context_flags;
            self.set_context_flags(NodeFlags::JSDOC, true);
            default_type = Some(self.parse_js_doc_type());
            self.context_flags = save_context_flags;
            self.parse_expected(Kind::CloseBracketToken);
        }

        if node_is_missing(Some(name), &self.nodes) {
            return None;
        }
        let tp = self.factory.new_type_parameter_declaration(
            &mut self.nodes,
            modifiers,
            Some(name),
            None, /*constraint*/
            None, /*expression*/
            default_type,
        );
        Some(self.finish_node(tp, type_parameter_pos))
    }

    /// `func (p *Parser) parseTemplateTagTypeParameters() *ast.TypeParameterList`
    fn parse_template_tag_type_parameters(&mut self) -> NodeList {
        let mut type_parameters: Vec<NodeId> = Vec::new();
        loop {
            self.skip_whitespace();
            if let Some(node) = self.parse_template_tag_type_parameter() {
                type_parameters.push(node);
            }
            self.skip_whitespace_or_asterisk();
            if !self.parse_optional_jsdoc(Kind::CommaToken) {
                break;
            }
        }
        // Go returns `*ast.TypeParameterList` with unset Loc — NodeList::default.
        let mut list = NodeList::default();
        list.nodes = type_parameters.into();
        list
    }

    /// `func (p *Parser) parseTemplateTag(start int, tagName *ast.IdentifierNode, indent int, indentText string) *ast.Node`
    fn parse_template_tag(
        &mut self,
        start: i32,
        tag_name: NodeId,
        indent: i32,
        indent_text: &str,
    ) -> NodeId {
        // The template tag looks like one of the following:
        //   @template T,U,V
        //   @template {Constraint} T
        //
        // According to the [closure docs](https://github.com/google/closure-compiler/wiki/Generic-Types#multiple-bounded-template-types):
        //   > Multiple bounded generics cannot be declared on the same line. For the sake of clarity, if multiple templates share the same
        //   > type bound they must be declared on separate lines.
        //
        // TODO: Determine whether we should enforce this in the checker.
        // TODO: Consider moving the `constraint` to the first type parameter as we could then remove `getEffectiveConstraintOfTypeParameter`.
        // TODO: Consider only parsing a single type parameter if there is a constraint.
        let mut constraint = None;
        if self.token == Kind::OpenBraceToken {
            constraint = Some(self.parse_jsdoc_type_expression(false));
        }
        let type_parameters = self.parse_template_tag_type_parameters();
        let comments =
            self.parse_trailing_tag_comments(start, self.node_pos(), indent, indent_text);
        let result = self.factory.new_js_doc_template_tag(
            &mut self.nodes,
            Some(tag_name),
            constraint,
            Some(type_parameters),
            comments,
        );
        self.finish_node(result, start)
    }

    /// `func (p *Parser) parseOptionalJsdoc(t ast.Kind) bool`
    fn parse_optional_jsdoc(&mut self, t: Kind) -> bool {
        if self.token == t {
            self.next_token_jsdoc();
            return true;
        }
        false
    }

    /// `func (p *Parser) parseJSDocEntityName(diagnosticMessage *diagnostics.Message) *ast.EntityName`
    fn parse_jsdoc_entity_name(
        &mut self,
        diagnostic_message: Option<&'static Message>,
    ) -> Option<NodeId> {
        let mut entity = self.parse_jsdoc_identifier_name(diagnostic_message);
        if self.parse_optional(Kind::OpenBracketToken) {
            self.parse_expected(Kind::CloseBracketToken);
            // Note that y[] is accepted as an entity name, but the postfix brackets are not saved for checking.
            // Technically usejsdoc.org requires them for specifying a property of a type equivalent to Array<{ x: ...}>
            // but it's not worth it to enforce that restriction.
        }
        while self.parse_optional(Kind::DotToken) {
            let name = self.parse_jsdoc_identifier_name(Some(&diagnostics::Identifier_expected));
            if self.parse_optional(Kind::OpenBracketToken) {
                self.parse_expected(Kind::CloseBracketToken);
            }
            let pos = self.nodes[entity].pos();
            let qn = self
                .factory
                .new_qualified_name(&mut self.nodes, Some(entity), Some(name));
            entity = self.finish_node(qn, pos);
        }
        Some(entity)
    }

    /// `func (p *Parser) parseJSDocIdentifierName(diagnosticMessage *diagnostics.Message) *ast.IdentifierNode`
    fn parse_jsdoc_identifier_name(
        &mut self,
        diagnostic_message: Option<&'static Message>,
    ) -> NodeId {
        if !token_is_identifier_or_keyword(self.token) {
            if let Some(diagnostic_message) = diagnostic_message {
                self.parse_error_at_current_token(diagnostic_message, &[]);
            } else if crate::parser::is_reserved_word(self.token) {
                let arg = self.scanner.token_text().to_string();
                self.parse_error_at_current_token(
                    &diagnostics::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here,
                    &[arg],
                );
            }
            let pos = self.node_pos();
            let id = self.new_identifier("");
            return self.finish_node(id, pos);
        }
        let pos = self.scanner.token_start() as i32;
        let end = self.scanner.token_end() as i32;
        let text = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
        self.next_token_jsdoc();
        let id = self.new_identifier(&text);
        self.finish_node_with_end(id, pos, end)
    }
}

/// `func removeLeadingNewlines(comments []string) []string`
fn remove_leading_newlines(mut comments: Vec<String>) -> Vec<String> {
    let mut i = 0;
    while i < comments.len() && comments[i].trim_start_matches(['\r', '\n']).is_empty() {
        i += 1;
    }
    comments.drain(..i);
    comments
}

/// `func trimEnd(s string) string`
fn trim_end(s: &str) -> &str {
    s.trim_end_matches(stringutil::is_white_space_like)
}

/// `func removeTrailingWhitespace(comments []string) []string`
fn remove_trailing_whitespace(mut comments: Vec<String>) -> Vec<String> {
    let mut end = comments.len();
    for i in (0..comments.len()).rev() {
        let trimmed = trim_end(&comments[i]);
        if trimmed.is_empty() {
            end = i;
        } else {
            comments[i] = trimmed.to_string();
            break;
        }
    }
    comments.truncate(end);
    comments
}

/// `func isJSDocLinkTag(kind string) bool`
fn is_jsdoc_link_tag(kind: &str) -> bool {
    kind == "link" || kind == "linkcode" || kind == "linkplain"
}

/// `func isObjectOrObjectArrayTypeReference(node *ast.TypeNode) bool`
fn is_object_or_object_array_type_reference(node: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(node) = node else {
        return false;
    };
    match nodes[node].kind {
        Kind::ObjectKeyword => true,
        Kind::ArrayType => is_object_or_object_array_type_reference(
            nodes[node].as_array_type_node().element_type,
            nodes,
        ),
        _ => {
            if is_type_reference_node(&nodes[node]) {
                let ref_node = &nodes[node].as_type_reference_node();
                ref_node
                    .type_name
                    .is_some_and(|n| is_identifier(&nodes[n]) && nodes[n].text(nodes) == "Object")
                    && ref_node
                        .node_with_type_arguments_base
                        .type_arguments
                        .is_none()
            } else {
                false
            }
        }
    }
}

/// `func textsEqual(a *ast.EntityName, b *ast.EntityName) bool`
fn texts_equal(nodes: &[Node], a: NodeId, b: NodeId) -> bool {
    let mut a = a;
    let mut b = b;
    while !is_identifier(&nodes[a]) || !is_identifier(&nodes[b]) {
        if !is_identifier(&nodes[a])
            && !is_identifier(&nodes[b])
            && nodes[a].as_qualified_name().right.is_some()
            && nodes[b].as_qualified_name().right.is_some()
            && nodes[nodes[a].as_qualified_name().right.unwrap()].text(nodes)
                == nodes[nodes[b].as_qualified_name().right.unwrap()].text(nodes)
        {
            a = nodes[a].as_qualified_name().left.unwrap();
            b = nodes[b].as_qualified_name().left.unwrap();
        } else {
            return false;
        }
    }
    nodes[a].text(nodes) == nodes[b].text(nodes)
}
