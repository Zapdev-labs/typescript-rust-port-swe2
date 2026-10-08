// Ported from tsc/internal/parser/parser.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Pointer model: Go `*ast.Node` → `NodeId`/`Option<NodeId>` into `p.nodes`,
// `*ast.NodeList` → `Option<NodeList>`, `*ast.ModifierList` →
// `Option<ModifierList>`. The parser owns the per-file `Vec<Node>` arena;
// `parse_source_file` returns `(file, nodes)`.
//
// PORT: Go's `sync.Pool` of `*Parser` and the `nodeSliceArena`/`stringSliceArena`
// slice-allocators are allocation reuse only — plain `Vec`s keep identical
// semantics (dead arena slots from speculative parses are allowed, matching
// Go's arena-leak behaviour).
//
// PORT: the scanner's `onError` callback cannot borrow `self` in Rust, so
// scanner-reported diagnostics are buffered in `pending_scan_errors` and
// replayed through `parse_error_at_range` (dedup, `hasParseError`) after each
// scanner call — identical ordering, since parser diagnostics can never be
// issued inside a single scan.

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};

use rustc_hash::FxHashMap;
use tsc_ast::ast_generated::*;
use tsc_ast::diagnostic::{DiagnosticRef, lock_diagnostic, new_diagnostic};
use tsc_ast::precedence::{OperatorPrecedence, get_binary_operator_precedence};
use tsc_ast::utilities::*;
use tsc_ast::diagnostic::DiagnosticFile;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::{
    CommentRange, Kind, ModifierFlags, ModifierList, Node, NodeFactory, NodeId, NodeList,
    NodeFlags, TokenFlags,
};
use tsc_collections::Set;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::{ModuleKind, ScriptTarget};
use tsc_core::scriptkind::ScriptKind;
use tsc_core::text::{TextPos, TextRange};
use tsc_core::tristate::{TS_FALSE, TS_TRUE, TS_UNKNOWN, Tristate};
use tsc_core::core::{self as core};
use tsc_diagnostics::{self as diagnostics, Message};
use tsc_scanner::scanner::{self as scanner, Scanner, ScannerState};
use tsc_scanner::utilities as scanner_utils;
use tsc_stringutil as stringutil;

use crate::references::collect_external_module_references;
use crate::types::ParseFlags;
use crate::utilities::{
    get_language_variant, is_keyword_or_punctuation, token_is_identifier_or_keyword,
    token_is_identifier_or_keyword_or_greater_than,
};

/// `type ParsingContext int`
pub type ParsingContext = u8;

#[allow(dead_code)]
mod parsing_context {
    /// Elements in source file
    pub const PC_SOURCE_ELEMENTS: super::ParsingContext = 0;
    /// Statements in block
    pub const PC_BLOCK_STATEMENTS: super::ParsingContext = 1;
    /// Clauses in switch statement
    pub const PC_SWITCH_CLAUSES: super::ParsingContext = 2;
    /// Statements in switch clause
    pub const PC_SWITCH_CLAUSE_STATEMENTS: super::ParsingContext = 3;
    /// Members in interface or type literal
    pub const PC_TYPE_MEMBERS: super::ParsingContext = 4;
    /// Members in class declaration
    pub const PC_CLASS_MEMBERS: super::ParsingContext = 5;
    /// Members in enum declaration
    pub const PC_ENUM_MEMBERS: super::ParsingContext = 6;
    /// Elements in a heritage clause
    pub const PC_HERITAGE_CLAUSE_ELEMENT: super::ParsingContext = 7;
    /// Variable declarations in variable statement
    pub const PC_VARIABLE_DECLARATIONS: super::ParsingContext = 8;
    /// Binding elements in object binding list
    pub const PC_OBJECT_BINDING_ELEMENTS: super::ParsingContext = 9;
    /// Binding elements in array binding list
    pub const PC_ARRAY_BINDING_ELEMENTS: super::ParsingContext = 10;
    /// Expressions in argument list
    pub const PC_ARGUMENT_EXPRESSIONS: super::ParsingContext = 11;
    /// Members in object literal
    pub const PC_OBJECT_LITERAL_MEMBERS: super::ParsingContext = 12;
    /// Attributes in jsx element
    pub const PC_JSX_ATTRIBUTES: super::ParsingContext = 13;
    /// Things between opening and closing JSX tags
    pub const PC_JSX_CHILDREN: super::ParsingContext = 14;
    /// Members in array literal
    pub const PC_ARRAY_LITERAL_MEMBERS: super::ParsingContext = 15;
    /// Parameters in parameter list
    pub const PC_PARAMETERS: super::ParsingContext = 16;
    /// JSDoc parameters in parameter list of JSDoc function type
    pub const PC_JS_DOC_PARAMETERS: super::ParsingContext = 17;
    /// Property names in a rest type list
    pub const PC_REST_PROPERTIES: super::ParsingContext = 18;
    /// Type parameters in type parameter list
    pub const PC_TYPE_PARAMETERS: super::ParsingContext = 19;
    /// Type arguments in type argument list
    pub const PC_TYPE_ARGUMENTS: super::ParsingContext = 20;
    /// Element types in tuple element type list
    pub const PC_TUPLE_ELEMENT_TYPES: super::ParsingContext = 21;
    /// Heritage clauses for a class or interface declaration.
    pub const PC_HERITAGE_CLAUSES: super::ParsingContext = 22;
    /// Named import clause's import specifier list
    pub const PC_IMPORT_OR_EXPORT_SPECIFIERS: super::ParsingContext = 23;
    /// Import attributes
    pub const PC_IMPORT_ATTRIBUTES: super::ParsingContext = 24;
    /// Parsing via JSDocParser
    pub const PC_JS_DOC_COMMENT: super::ParsingContext = 25;
    /// Number of parsing contexts
    pub const PC_COUNT: super::ParsingContext = 26;
}
use parsing_context::*;

/// `type ParsingContexts int` — one bit per `ParsingContext`.
pub type ParsingContexts = u32;

/// `type JSDocInfo struct`
#[derive(Clone, Default)]
pub struct JSDocInfo {
    pub parent: Option<NodeId>,
    pub js_docs: Vec<NodeId>,
}

/// `type jsdocScannerInfo uint8`
pub type JSDocScannerInfo = u8;

pub const JSDOC_SCANNER_INFO_HAS_JSDOC: JSDocScannerInfo = 1;
pub const JSDOC_SCANNER_INFO_HAS_DEPRECATED: JSDocScannerInfo = 2;
pub const JSDOC_SCANNER_INFO_HAS_SEE_OR_LINK: JSDocScannerInfo = 4;

/// A scanner-reported diagnostic queued for replay (see module header).
pub struct PendingScanError {
    pub message: &'static Message,
    pub pos: usize,
    pub length: usize,
    pub args: Vec<String>,
}

/// `type Parser struct`
pub struct Parser<'a> {
    pub scanner: Scanner<'a>,
    pub factory: NodeFactory<'static>,
    /// The per-file node arena (Go: factory arenas + `*ast.Node` heap).
    pub nodes: Vec<Node>,

    pub opts: SourceFileParseOptions,
    /// Go `sourceText string` — may be temporarily truncated while parsing
    /// JSDoc comments; always a subslice of the original `&'a str`.
    pub source_text: &'a str,

    pub script_kind: ScriptKind,
    pub language_variant: LanguageVariant,
    pub diagnostics: Vec<DiagnosticRef>,
    pub js_diagnostics: Vec<DiagnosticRef>,
    pub jsdoc_diagnostics: Vec<DiagnosticRef>,

    pub token: Kind,
    pub source_flags: NodeFlags,
    pub context_flags: NodeFlags,
    pub parsing_contexts: ParsingContexts,
    pub statement_has_await_identifier: bool,
    pub has_deprecated_tag: bool,
    pub has_parse_error: bool,

    pub identifier_count: i32,
    pub not_parenthesized_arrow: Set<usize>,
    pub jsdoc_infos: Vec<JSDocInfo>,
    pub possible_await_spans: Vec<usize>,
    pub jsdoc_comments_space: Vec<String>,
    pub jsdoc_comment_ranges_space: Vec<CommentRange>,
    pub jsdoc_tag_comments_space: Vec<String>,
    pub jsdoc_tag_comments_parts_space: Vec<NodeId>,
    pub reparse_list: Vec<NodeId>,

    pub reparsed_clones: Vec<NodeId>,
    /// Reused buffer for `override_parent_in_immediate_children` (Go folds
    /// this into the `setParentFromContext` closure).
    parent_scratch: Vec<NodeId>,

    /// Buffered scanner diagnostics (see module header).
    pending_scan_errors: Rc<RefCell<Vec<PendingScanError>>>,
}

/// `type ParserState struct`
#[derive(Clone)]
pub struct ParserState {
    pub scanner_state: ScannerState,
    pub context_flags: NodeFlags,
    pub diagnostics_len: usize,
    pub js_diagnostics_len: usize,
    pub jsdoc_infos_len: usize,
    pub reparsed_clones_len: usize,
    pub statement_has_await_identifier: bool,
    pub has_parse_error: bool,
}

static VIABLE_KEYWORD_SUGGESTIONS: std::sync::LazyLock<Vec<&'static str>> =
    std::sync::LazyLock::new(scanner::get_viable_keyword_suggestions);

/// File indices packed into `NodeId::new` — one per parsed file (SPEC §5.1's
/// "global node index"; Go has raw heap pointers).
static NEXT_FILE_INDEX: AtomicU32 = AtomicU32::new(0);

/// `missingListNodes` — see `NodeList::is_missing`.
pub fn is_missing_node_list(list: Option<&NodeList>) -> bool {
    list.is_some_and(|l| l.is_missing)
}

// PORT: Go's `parserPool`/`getParser`/`putParser` are a recycling
// optimization; `Parser::new`+`initialize_state` keep identical semantics.
impl<'a> Parser<'a> {
    /// `func newParser() *Parser` — `initializeClosures` is folded in.
    pub fn new() -> Parser<'a> {
        Parser {
            scanner: Scanner::new(),
            factory: NodeFactory::default(),
            nodes: Vec::new(),
            opts: SourceFileParseOptions::default(),
            source_text: "",
            script_kind: ScriptKind::default(),
            language_variant: LanguageVariant::default(),
            diagnostics: Vec::new(),
            js_diagnostics: Vec::new(),
            jsdoc_diagnostics: Vec::new(),
            token: Kind::Unknown,
            source_flags: NodeFlags::NONE,
            context_flags: NodeFlags::NONE,
            parsing_contexts: 0,
            statement_has_await_identifier: false,
            has_deprecated_tag: false,
            has_parse_error: false,
            identifier_count: 0,
            not_parenthesized_arrow: Set::new(),
            jsdoc_infos: Vec::new(),
            possible_await_spans: Vec::new(),
            jsdoc_comments_space: Vec::new(),
            jsdoc_comment_ranges_space: Vec::new(),
            jsdoc_tag_comments_space: Vec::new(),
            jsdoc_tag_comments_parts_space: Vec::new(),
            reparse_list: Vec::new(),
            reparsed_clones: Vec::new(),
            parent_scratch: Vec::new(),
            pending_scan_errors: Rc::new(RefCell::new(Vec::new())),
        }
    }

    /// `func (p *Parser) isJavaScript() bool`
    pub fn is_java_script(&self) -> bool {
        self.script_kind == ScriptKind::Js || self.script_kind == ScriptKind::Jsx
    }

    /// `func (p *Parser) initializeState(...)`
    pub fn initialize_state(
        &mut self,
        opts: SourceFileParseOptions,
        source_text: &'a str,
        script_kind: ScriptKind,
    ) {
        if script_kind == ScriptKind::Unknown {
            panic!(
                "ScriptKind must be specified when parsing source file: {}",
                opts.file_name.as_string()
            );
        }
        // `p.scanner.Reset()` — `set_text` below resets the scanned state;
        // caches are kept.
        self.scanner.reset();
        self.factory.set_file_index(NEXT_FILE_INDEX.fetch_add(1, Ordering::Relaxed));
        self.opts = opts;
        self.source_text = source_text;
        self.script_kind = script_kind;
        self.language_variant = get_language_variant(self.script_kind);
        self.context_flags = match self.script_kind {
            ScriptKind::Js | ScriptKind::Jsx => NodeFlags::JAVA_SCRIPT_FILE,
            ScriptKind::Json => NodeFlags::JAVA_SCRIPT_FILE | NodeFlags::JSON_FILE,
            _ => NodeFlags::NONE,
        };
        self.scanner.set_text(self.source_text);
        let pending = Rc::clone(&self.pending_scan_errors);
        self.scanner.set_on_error(Some(
            move |message: &'static Message, pos: usize, length: usize, args: &[String]| {
                pending.borrow_mut().push(PendingScanError {
                    message,
                    pos,
                    length,
                    args: args.to_vec(),
                });
            },
        ));
        self.scanner.set_language_variant(self.language_variant);
    }

    /// Replays buffered scanner diagnostics through `parse_error_at_range`
    /// (Go's `scanError` fires mid-scan; replaying after each scanner call is
    /// order-equivalent).
    fn drain_scanner_errors(&mut self) {
        if self.pending_scan_errors.borrow().is_empty() {
            return;
        }
        let pending = std::mem::take(&mut *self.pending_scan_errors.borrow_mut());
        for e in pending {
            self.parse_error_at_range(
                TextRange::new(e.pos as i32, (e.pos + e.length) as i32),
                e.message,
                &e.args,
            );
        }
    }

    /// `func (p *Parser) scanError(...)`
    ///
    /// PORT: in Go this is the scanner's `onError` callback; in Rust the
    /// callback only buffers (see [`Parser::drain_scanner_errors`]).
    fn scan_error(&mut self, message: &'static Message, pos: i32, length: i32, args: &[String]) {
        self.parse_error_at_range(TextRange::new(pos, pos + length), message, args);
    }

    /// `func (p *Parser) parseErrorAt(pos int, end int, message, args...)` —
    /// returns the diagnostic (Go `*ast.Diagnostic`, nil when deduplicated).
    pub fn parse_error_at(
        &mut self,
        pos: i32,
        end: i32,
        message: &'static Message,
        args: &[String],
    ) -> Option<DiagnosticRef> {
        self.parse_error_at_range(TextRange::new(pos, end), message, args)
    }

    /// `func (p *Parser) parseErrorAtCurrentToken(message, args...)`
    pub fn parse_error_at_current_token(
        &mut self,
        message: &'static Message,
        args: &[String],
    ) -> Option<DiagnosticRef> {
        self.parse_error_at_range(self.scanner.token_range(), message, args)
    }

    /// `func (p *Parser) parseErrorAtRange(loc, message, args...)`
    pub fn parse_error_at_range(
        &mut self,
        loc: TextRange,
        message: &'static Message,
        args: &[String],
    ) -> Option<DiagnosticRef> {
        // Don't report another error if it would just be at the same location as the last error
        let mut result = None;
        if self.diagnostics.is_empty()
            || lock_diagnostic(self.diagnostics.last().unwrap()).pos() != loc.pos()
        {
            let diagnostic = new_diagnostic(None, loc, message, args);
            self.diagnostics.push(diagnostic.clone());
            result = Some(diagnostic);
        }
        self.has_parse_error = true;
        result
    }

    /// `func (p *Parser) mark() ParserState`
    pub fn mark(&self) -> ParserState {
        ParserState {
            scanner_state: self.scanner.mark(),
            context_flags: self.context_flags,
            diagnostics_len: self.diagnostics.len(),
            js_diagnostics_len: self.js_diagnostics.len(),
            jsdoc_infos_len: self.jsdoc_infos.len(),
            reparsed_clones_len: self.reparsed_clones.len(),
            statement_has_await_identifier: self.statement_has_await_identifier,
            has_parse_error: self.has_parse_error,
        }
    }

    /// `func (p *Parser) rewind(state ParserState)`
    pub fn rewind(&mut self, state: ParserState) {
        self.scanner.rewind(state.scanner_state);
        // Scanner errors queued during the speculative parse are discarded
        // along with the truncated diagnostics (Go records them into
        // `p.diagnostics` immediately; truncation drops them either way).
        self.pending_scan_errors.borrow_mut().clear();
        self.token = self.scanner.token();
        self.context_flags = state.context_flags;
        self.diagnostics.truncate(state.diagnostics_len);
        self.js_diagnostics.truncate(state.js_diagnostics_len);
        self.jsdoc_infos.truncate(state.jsdoc_infos_len);
        self.reparsed_clones.truncate(state.reparsed_clones_len);
        self.statement_has_await_identifier = state.statement_has_await_identifier;
        self.has_parse_error = state.has_parse_error;
    }

    /// `func (p *Parser) lookAhead(callback func(p *Parser) bool) bool`
    pub fn look_ahead(&mut self, callback: impl FnOnce(&mut Self) -> bool) -> bool {
        let state = self.mark();
        let result = callback(self);
        self.rewind(state);
        result
    }

    /// `func (p *Parser) nextToken() ast.Kind`
    pub fn next_token(&mut self) -> Kind {
        // if the keyword had an escape
        if is_keyword(self.token)
            && (self.scanner.has_unicode_escape() || self.scanner.has_extended_unicode_escape())
        {
            // issue a parse error for the escape
            self.parse_error_at_current_token(
                &diagnostics::Keywords_cannot_contain_escape_characters,
                &[],
            );
        }
        self.token = self.scanner.scan();
        self.drain_scanner_errors();
        self.token
    }

    /// `func (p *Parser) nextTokenWithoutCheck() ast.Kind`
    pub fn next_token_without_check(&mut self) -> Kind {
        self.token = self.scanner.scan();
        self.drain_scanner_errors();
        self.token
    }

    /// `func (p *Parser) nextTokenJSDoc() ast.Kind`
    pub fn next_token_jsdoc(&mut self) -> Kind {
        self.token = self.scanner.scan_jsdoc_token();
        self.drain_scanner_errors();
        self.token
    }

    /// `func (p *Parser) nextJSDocCommentTextToken(inBackticks bool) ast.Kind`
    pub fn next_jsdoc_comment_text_token(&mut self, in_backticks: bool) -> Kind {
        self.token = self.scanner.scan_jsdoc_comment_text_token(in_backticks);
        self.drain_scanner_errors();
        self.token
    }

    /// `func (p *Parser) nodePos() int`
    pub fn node_pos(&self) -> i32 {
        self.scanner.token_full_start() as i32
    }

    /// `func (p *Parser) hasPrecedingLineBreak() bool`
    pub fn has_preceding_line_break(&self) -> bool {
        self.scanner.has_preceding_line_break()
    }

    /// `func (p *Parser) jsdocScannerInfo() jsdocScannerInfo`
    pub fn jsdoc_scanner_info(&self) -> JSDocScannerInfo {
        if !self.scanner.has_preceding_jsdoc_comment() {
            return 0;
        }
        let mut info = JSDOC_SCANNER_INFO_HAS_JSDOC;
        if self.scanner.has_preceding_jsdoc_with_deprecated_tag() {
            info |= JSDOC_SCANNER_INFO_HAS_DEPRECATED;
        }
        if self.scanner.has_preceding_jsdoc_with_see_or_link() {
            info |= JSDOC_SCANNER_INFO_HAS_SEE_OR_LINK;
        }
        info
    }

    /// `func (p *Parser) finishNode(node *ast.Node, pos int) *ast.Node`
    pub fn finish_node(&mut self, node: NodeId, pos: i32) -> NodeId {
        self.finish_node_with_end(node, pos, self.node_pos())
    }

    /// `func (p *Parser) finishNodeWithEnd(node, pos, end)` — sets `loc`,
    /// applies `contextFlags`, propagates `hasParseError`, and assigns
    /// immediate-child parents.
    pub fn finish_node_with_end(&mut self, node: NodeId, pos: i32, end: i32) -> NodeId {
        self.nodes[node].loc = TextRange::new(pos, end);
        self.nodes[node].flags |= self.context_flags;
        if self.has_parse_error {
            self.nodes[node].flags |= NodeFlags::THIS_NODE_HAS_ERROR;
            self.has_parse_error = false;
        }
        self.override_parent_in_immediate_children(node);
        node
    }

    /// `func (p *Parser) overrideParentInImmediateChildren(node *ast.Node)`
    ///
    /// PORT: `p.currentParent`/`p.setParentFromContext` become a local
    /// child-id sweep — the visitor only carries `NodeId`s.
    fn override_parent_in_immediate_children(&mut self, node: NodeId) {
        let mut children = std::mem::take(&mut self.parent_scratch);
        {
            let children_ref = &mut children;
            self.nodes[node].for_each_child(&self.nodes, &mut |child| {
                children_ref.push(child);
                false
            });
        }
        for child in children.iter().copied() {
            self.nodes[child].parent = Some(node);
        }
        children.clear();
        self.parent_scratch = children;
    }

    /// `func (p *Parser) newNodeList(loc core.TextRange, nodes []*ast.Node) *ast.NodeList`
    pub fn new_node_list(&self, loc: TextRange, nodes: Vec<NodeId>) -> NodeList {
        let mut list = self.factory.new_node_list(nodes);
        list.loc = loc;
        list
    }

    /// `func (p *Parser) newModifierList(loc core.TextRange, nodes []*ast.Node) *ast.ModifierList`
    pub fn new_modifier_list(&self, loc: TextRange, nodes: Vec<NodeId>) -> ModifierList {
        let mut list = self.factory.new_modifier_list(&self.nodes, nodes);
        list.loc = loc;
        list
    }

    /// `func (p *Parser) createMissingList() *ast.NodeList` — the Go
    /// `missingListNodes` sentinel is `NodeList::is_missing`.
    pub fn create_missing_list(&mut self) -> NodeList {
        let mut result = self.parse_empty_node_list();
        result.is_missing = true;
        result
    }

    /// `func (p *Parser) parseEmptyNodeList() *ast.NodeList`
    pub fn parse_empty_node_list(&mut self) -> NodeList {
        let pos = self.node_pos();
        self.new_node_list(TextRange::new(pos, pos), Vec::new())
    }
}

/// Registers the lazy-JSDoc parse hook the first time a file is parsed
/// (Go: `func init() { ast.SetParseJSDocForNode(parseJSDocForNode) }`).
fn register_jsdoc_parse_hook() {
    tsc_ast::set_parse_jsdoc_for_node(crate::jsdoc::parse_jsdoc_for_node);
}

/// `func ParseSourceFile(opts, sourceText, scriptKind) *ast.SourceFile`
///
/// PORT: returns `(file, nodes)` — the `NodeId` of the `Kind::SourceFile`
/// node together with the arena that owns it (Go returns a heap pointer).
pub fn parse_source_file(
    opts: SourceFileParseOptions,
    source_text: &str,
    script_kind: ScriptKind,
) -> (NodeId, Vec<Node>) {
    register_jsdoc_parse_hook();
    let mut p = Parser::new();
    p.initialize_state(opts, source_text, script_kind);
    p.next_token();
    let file = if p.script_kind == ScriptKind::Json {
        p.parse_json_text()
    } else {
        p.parse_source_file_worker()
    };
    (file, p.nodes)
}

/// `type expressions any` in `parseJSONText` — either one `*ast.Expression`
/// or a `[]*ast.Expression` accumulated during error recovery.
enum JsonExpressions {
    Single(NodeId),
    Multiple(Vec<NodeId>),
}

impl<'a> Parser<'a> {
    /// `func (p *Parser) parseJSONText() *ast.SourceFile`
    fn parse_json_text(&mut self) -> NodeId {
        let pos = self.node_pos();
        let mut statements: NodeList;
        let eof: NodeId;

        if self.token == Kind::EndOfFile {
            statements = self.new_node_list(TextRange::new(pos, self.node_pos()), Vec::new());
            eof = self.parse_token_node();
        } else {
            let mut expressions: Option<JsonExpressions> = None;

            while self.token != Kind::EndOfFile {
                let expression: NodeId;
                match self.token {
                    Kind::OpenBracketToken => {
                        expression = self.parse_array_literal_expression();
                    }
                    Kind::TrueKeyword | Kind::FalseKeyword | Kind::NullKeyword => {
                        expression = self.parse_token_node();
                    }
                    Kind::MinusToken => {
                        if self.look_ahead(|p| {
                            p.next_token() == Kind::NumericLiteral
                                && p.next_token() != Kind::ColonToken
                        }) {
                            expression = self.parse_prefix_unary_expression();
                        } else {
                            expression = self.parse_object_literal_expression();
                        }
                    }
                    Kind::NumericLiteral | Kind::StringLiteral => {
                        if self.look_ahead(|p| p.next_token() != Kind::ColonToken) {
                            expression = self.parse_literal_expression();
                        } else {
                            expression = self.parse_object_literal_expression();
                        }
                    }
                    _ => {
                        expression = self.parse_object_literal_expression();
                    }
                }

                // Error recovery: collect multiple top-level expressions
                expressions = Some(match expressions {
                    Some(JsonExpressions::Multiple(mut es)) => {
                        es.push(expression);
                        JsonExpressions::Multiple(es)
                    }
                    Some(JsonExpressions::Single(e)) => {
                        JsonExpressions::Multiple(vec![e, expression])
                    }
                    None => {
                        if self.token != Kind::EndOfFile {
                            self.parse_error_at_current_token(
                                &diagnostics::Unexpected_token,
                                &[],
                            );
                        }
                        JsonExpressions::Single(expression)
                    }
                });
            }

            let expression: NodeId = match expressions {
                Some(JsonExpressions::Multiple(es)) => {
                    let list = self.new_node_list(TextRange::new(pos, self.node_pos()), es);
                    let array = self.factory.new_array_literal_expression(
                        &mut self.nodes,
                        Some(list),
                        false,
                    );
                    self.finish_node(array, pos)
                }
                Some(JsonExpressions::Single(e)) => e,
                None => unreachable!(),
            };
            let statement =
                self.factory.new_expression_statement(&mut self.nodes, Some(expression));
            let statement = self.finish_node(statement, pos);
            let statement_list =
                self.new_node_list(TextRange::new(pos, self.node_pos()), vec![statement]);
            statements = statement_list;
            eof = self.parse_expected_token(Kind::EndOfFile);
        }
        let sf = self.factory.new_source_file(
            &mut self.nodes,
            &self.opts.clone(),
            self.source_text,
            Some(statements),
            Some(eof),
        );
        let node = self.finish_node(sf, pos);
        if !self.nodes[node]
            .as_source_file()
            .statements
            .as_ref()
            .is_none_or(|s| s.nodes.is_empty())
        {
            let first = self.nodes[node].as_source_file().statements.as_ref().unwrap().nodes[0];
            let expr = self.nodes[first].expression().unwrap();
            self.validate_json_value(node, Some(expr));
        }
        self.finish_source_file(node, false);
        node
    }

    /// `func (p *Parser) validateJsonValue(sourceFile, valueExpression)`
    fn validate_json_value(&mut self, source_file: NodeId, value_expression: Option<NodeId>) {
        let Some(value_expression) = value_expression else {
            return;
        };
        match self.nodes[value_expression].kind {
            Kind::TrueKeyword | Kind::FalseKeyword | Kind::NullKeyword | Kind::NumericLiteral => {
                return;
            }
            Kind::StringLiteral => {
                if !is_double_quoted_string(&self.nodes[value_expression]) {
                    let span =
                        get_error_span_for_node(self.source_text, value_expression, &self.nodes);
                    let file = tsc_ast::diagnostic::DiagnosticFile::from_node(
                        source_file,
                        &self.nodes,
                    );
                    self.diagnostics.push(new_diagnostic(
                        Some(file),
                        span,
                        &diagnostics::String_literal_with_double_quotes_expected,
                        &[] as &[String],
                    ));
                }
                return;
            }
            Kind::PrefixUnaryExpression => {
                let d = self.nodes[value_expression].as_prefix_unary_expression();
                if d.operator != Kind::MinusToken
                    || self.nodes[d.operand.unwrap()].kind != Kind::NumericLiteral
                {
                    // not valid JSON syntax
                } else {
                    return;
                }
            }
            Kind::ObjectLiteralExpression => {
                self.validate_json_object_literal(source_file, value_expression);
                return;
            }
            Kind::ArrayLiteralExpression => {
                let elements: Vec<NodeId> = self.nodes[value_expression]
                    .elements()
                    .map(|e| e.to_vec())
                    .unwrap_or_default();
                for element in elements {
                    self.validate_json_value(source_file, Some(element));
                }
                return;
            }
            _ => {}
        }
        let span = get_error_span_for_node(self.source_text, value_expression, &self.nodes);
        let file = tsc_ast::diagnostic::DiagnosticFile::from_node(source_file, &self.nodes);
        self.diagnostics.push(new_diagnostic(
            Some(file),
            span,
            &diagnostics::Property_value_can_only_be_string_literal_numeric_literal_true_false_null_object_literal_or_array_literal,
            &[] as &[String],
        ));
    }

    /// `func (p *Parser) validateJsonObjectLiteral(sourceFile, node)` —
    /// validates properties of a JSON object literal.
    fn validate_json_object_literal(&mut self, source_file: NodeId, node: NodeId) {
        let properties = self.nodes[node]
            .as_object_literal_expression()
            .properties
            .as_ref()
            .map(|l| l.nodes.to_vec())
            .unwrap_or_default();
        for element in properties {
            if self.nodes[element].kind != Kind::PropertyAssignment {
                let span = get_error_span_for_node(self.source_text, element, &self.nodes);
                let file =
                    tsc_ast::diagnostic::DiagnosticFile::from_node(source_file, &self.nodes);
                self.diagnostics.push(new_diagnostic(
                    Some(file),
                    span,
                    &diagnostics::Property_assignment_expected,
                    &[] as &[String],
                ));
                continue;
            }
            if let Some(name) = self.nodes[element].name()
                && !is_double_quoted_string(&self.nodes[name])
            {
                let span = get_error_span_for_node(self.source_text, name, &self.nodes);
                let file =
                    tsc_ast::diagnostic::DiagnosticFile::from_node(source_file, &self.nodes);
                self.diagnostics.push(new_diagnostic(
                    Some(file),
                    span,
                    &diagnostics::String_literal_with_double_quotes_expected,
                    &[] as &[String],
                ));
            }
            let initializer = self.nodes[element].as_property_assignment().initializer;
            self.validate_json_value(source_file, initializer);
        }
    }

    /// `func (p *Parser) parseSourceFileWorker() *ast.SourceFile`
    fn parse_source_file_worker(&mut self) -> NodeId {
        let is_declaration_file = self.opts.file_name.is_declaration_file();
        if is_declaration_file {
            self.context_flags |= NodeFlags::AMBIENT;
        }
        let pos = self.node_pos();
        let mut statements =
            self.parse_list_index(PC_SOURCE_ELEMENTS, Self::parse_toplevel_statement);
        let end = self.node_pos();
        let end_jsdoc = self.jsdoc_scanner_info();
        let eof = self.parse_token_node();
        self.with_jsdoc(eof, end_jsdoc);
        if self.nodes[eof].kind != Kind::EndOfFile {
            panic!("Expected end of file token from scanner.");
        }
        if !self.reparse_list.is_empty() {
            statements.extend(std::mem::take(&mut self.reparse_list));
        }
        let statements_list = self.new_node_list(TextRange::new(pos, end), statements);
        let sf = self.factory.new_source_file(
            &mut self.nodes,
            &self.opts.clone(),
            self.source_text,
            Some(statements_list),
            Some(eof),
        );
        let node = self.finish_node(sf, pos);
        let mut result = node;
        self.finish_source_file(result, is_declaration_file);
        if !self.nodes[result].as_source_file().is_declaration_file
            && self.nodes[result]
                .as_source_file()
                .external_module_indicator
                .is_some()
            && !self.possible_await_spans.is_empty()
        {
            let reparsed = self.reparse_top_level_await(result);
            let reparse = self.finish_node(reparsed, pos);
            if node != reparse {
                result = reparse;
                self.finish_source_file(result, is_declaration_file);
            }
        }
        collect_external_module_references(&mut self.nodes, result);
        if is_in_js_file(Some(node), &self.nodes) {
            let diags = std::mem::take(&mut self.js_diagnostics);
            let diags = attach_file_to_diagnostics(diags, result, &self.nodes);
            self.nodes[result].as_source_file_mut().set_js_diagnostics(diags);
        }
        result
    }

    /// `func (p *Parser) finishSourceFile(result *ast.SourceFile, isDeclarationFile bool)`
    fn finish_source_file(&mut self, result: NodeId, is_declaration_file: bool) {
        self.nodes[result]
            .as_source_file_mut()
            .comment_directives = self.scanner.comment_directives().to_vec().into();
        let pragmas = get_comment_pragmas(&mut self.factory, self.source_text);
        self.nodes[result].as_source_file_mut().pragmas = pragmas.into();
        self.process_pragmas_into_fields(result);
        let diags = std::mem::take(&mut self.diagnostics);
        let diags = attach_file_to_diagnostics(diags, result, &self.nodes);
        self.nodes[result].as_source_file_mut().set_diagnostics(diags);
        let jsdoc_diags = std::mem::take(&mut self.jsdoc_diagnostics);
        let jsdoc_diags = attach_file_to_diagnostics(jsdoc_diags, result, &self.nodes);
        self.nodes[result]
            .as_source_file_mut()
            .set_jsdoc_diagnostics(jsdoc_diags);
        self.nodes[result].as_source_file_mut().is_declaration_file = is_declaration_file;
        self.nodes[result].as_source_file_mut().language_variant = self.language_variant;
        self.nodes[result].as_source_file_mut().script_kind = self.script_kind;
        self.nodes[result].flags |= self.source_flags;
        self.nodes[result].as_source_file_mut().node_count = self.factory.node_count() as i32;
        self.nodes[result].as_source_file_mut().text_count = self.factory.text_count() as i32;
        self.nodes[result]
            .as_source_file_mut()
            .identifier_count = self.identifier_count;
        let cache = self.create_jsdoc_cache();
        self.nodes[result].as_source_file_mut().set_jsdoc_cache(cache);
        // For non-JS files, enable lazy JSDoc parsing on demand
        if !self.is_java_script() {
            self.nodes[result]
                .as_source_file_mut()
                .set_has_lazy_jsdoc(true);
        }
        // `slices.SortFunc(p.reparsedClones, ast.CompareNodePositions)`
        let nodes = &self.nodes;
        self.reparsed_clones
            .sort_by(|&a, &b| compare_node_positions(&nodes[a], &nodes[b]).cmp(&0));
        self.nodes[result]
            .as_source_file_mut()
            .reparsed_clones = std::mem::take(&mut self.reparsed_clones).into();
        let opts = self.opts.external_module_indicator_options;
        tsc_ast::parseoptions::set_external_module_indicator(result, opts, &mut self.nodes);
    }

    /// `func (p *Parser) createJSDocCache() map[*ast.Node][]*ast.Node`
    fn create_jsdoc_cache(&self) -> FxHashMap<NodeId, Vec<NodeId>> {
        if self.jsdoc_infos.is_empty() {
            return FxHashMap::default();
        }
        let mut result = FxHashMap::with_capacity_and_hasher(
            self.jsdoc_infos.len(),
            rustc_hash::FxBuildHasher,
        );
        for info in &self.jsdoc_infos {
            result.insert(info.parent.unwrap(), info.js_docs.clone());
        }
        result
    }

    /// `func (p *Parser) parseToplevelStatement(i int) *ast.Node`
    fn parse_toplevel_statement(&mut self, i: usize) -> Option<NodeId> {
        self.statement_has_await_identifier = false;
        let statement = self.parse_statement();
        // Reparsed nodes (e.g. JSDoc @typedef) produced while parsing this statement are inserted
        // into the statement list before this statement, so account for them when recording the
        // statement's index for possibleAwaitSpans.
        let i = i + self.reparse_list.len();
        if self.statement_has_await_identifier
            && !self.nodes[statement]
                .flags
                .intersects(NodeFlags::AWAIT_CONTEXT)
        {
            if self.possible_await_spans.is_empty()
                || *self.possible_await_spans.last().unwrap() != i
            {
                self.possible_await_spans.push(i);
                self.possible_await_spans.push(i + 1);
            } else {
                *self.possible_await_spans.last_mut().unwrap() = i + 1;
            }
        }
        Some(statement)
    }

    /// `func (p *Parser) reparseTopLevelAwait(sourceFile *ast.SourceFile) *ast.Node`
    fn reparse_top_level_await(&mut self, source_file: NodeId) -> NodeId {
        if self.possible_await_spans.len() % 2 == 1 {
            panic!("possibleAwaitSpans malformed: odd number of indices, not paired into spans.");
        }
        let mut statements: Vec<NodeId> = Vec::new();
        let saved_parse_diagnostics = std::mem::take(&mut self.diagnostics);

        let sf_statements = self.nodes[source_file]
            .as_source_file()
            .statements
            .as_ref()
            .map(|s| s.nodes.to_vec())
            .unwrap_or_default();

        let mut after_await_statement = 0usize;
        let mut i = 0usize;
        while i < self.possible_await_spans.len() {
            let next_await_statement = self.possible_await_spans[i];
            // append all non-await statements between afterAwaitStatement and nextAwaitStatement
            let prev_statement = sf_statements[after_await_statement];
            let next_statement = sf_statements[next_await_statement];
            statements.extend_from_slice(&sf_statements[after_await_statement..next_await_statement]);

            // append all diagnostics associated with the copied range
            let prev_pos = self.nodes[prev_statement].pos();
            let next_pos = self.nodes[next_statement].pos();
            let diagnostic_start = core::find_index(&saved_parse_diagnostics, |diagnostic| {
                lock_diagnostic(diagnostic).pos() >= prev_pos
            });
            let diagnostic_end = if diagnostic_start >= 0 {
                core::find_index(
                    &saved_parse_diagnostics[diagnostic_start as usize..],
                    |diagnostic| lock_diagnostic(diagnostic).pos() >= next_pos,
                )
            } else {
                -1
            };
            if diagnostic_start >= 0 {
                if diagnostic_end >= 0 {
                    self.diagnostics.extend_from_slice(
                        &saved_parse_diagnostics[diagnostic_start as usize
                            ..(diagnostic_start + diagnostic_end) as usize],
                    );
                } else {
                    self.diagnostics
                        .extend_from_slice(&saved_parse_diagnostics[diagnostic_start as usize..]);
                }
            }

            let mut state = self.mark();
            // reparse all statements between start and pos. We skip existing diagnostics for the same range and allow the parser to generate new ones.
            self.context_flags |= NodeFlags::AWAIT_CONTEXT;
            self.scanner.reset_pos(next_pos as usize);
            self.next_token();

            after_await_statement = self.possible_await_spans[i + 1];
            while self.token != Kind::EndOfFile {
                let start_pos = self.scanner.token_full_start();
                let statement = self.parse_statement();
                statements.push(statement);
                if start_pos == self.scanner.token_full_start() {
                    self.next_token();
                }
                if after_await_statement < sf_statements.len() {
                    let last_await_statement = sf_statements[after_await_statement - 1];
                    if self.nodes[statement].end() == self.nodes[last_await_statement].end() {
                        // done reparsing this section
                        break;
                    }
                    if self.nodes[statement].end() > self.nodes[last_await_statement].end() {
                        // we ate into the next statement, so we must continue reparsing the next span
                        i += 2;
                        if i < self.possible_await_spans.len() {
                            after_await_statement = self.possible_await_spans[i + 1];
                        } else {
                            after_await_statement = sf_statements.len();
                        }
                    }
                }
            }

            // Keep diagnostics from the reparse
            state.diagnostics_len = self.diagnostics.len();
            self.rewind(state);
            i += 2;
        }

        // append all statements between pos and the end of the list
        if after_await_statement < sf_statements.len() {
            let prev_statement = sf_statements[after_await_statement];
            statements.extend_from_slice(&sf_statements[after_await_statement..]);

            // append all diagnostics associated with the copied range
            let prev_pos = self.nodes[prev_statement].pos();
            let diagnostic_start = core::find_index(&saved_parse_diagnostics, |diagnostic| {
                lock_diagnostic(diagnostic).pos() >= prev_pos
            });
            if diagnostic_start >= 0 {
                self.diagnostics
                    .extend_from_slice(&saved_parse_diagnostics[diagnostic_start as usize..]);
            }
        }

        let opts = self.nodes[source_file].as_source_file().parse_options.clone();
        let statements_loc = self.nodes[source_file]
            .as_source_file()
            .statements
            .as_ref()
            .map(|s| s.loc);
        let eof = self.nodes[source_file].as_source_file().end_of_file_token;
        let statements_list = self.new_node_list(statements_loc.unwrap_or_default(), statements.clone());
        let result = self.factory.new_source_file(
            &mut self.nodes,
            &opts,
            self.source_text,
            Some(statements_list),
            eof,
        );
        for s in statements {
            self.nodes[s].parent = Some(result); // force (re)set parent to reparsed source file
        }
        result
    }

    /// `func (p *Parser) parseListIndex(kind, parseElement) []*ast.Node`
    fn parse_list_index(
        &mut self,
        kind: ParsingContext,
        parse_element: impl Fn(&mut Self, usize) -> Option<NodeId>,
    ) -> Vec<NodeId> {
        let save_parsing_contexts = self.parsing_contexts;
        self.parsing_contexts |= 1 << kind;
        let mut outer_reparse_list = std::mem::take(&mut self.reparse_list);
        let mut list: Vec<NodeId> = Vec::with_capacity(16);
        while !self.is_list_terminator(kind) {
            if self.is_list_element(kind, false /*inErrorRecovery*/) {
                let elt = parse_element(self, list.len());
                if !self.reparse_list.is_empty() {
                    for e in self.reparse_list.drain(..) {
                        // Propagate @typedef type alias declarations outwards to a context that permits them.
                        if (is_js_type_alias_declaration(&self.nodes[e])
                            || is_js_import_declaration(&self.nodes[e]))
                            && kind != PC_SOURCE_ELEMENTS
                            && kind != PC_BLOCK_STATEMENTS
                        {
                            outer_reparse_list.push(e);
                        } else {
                            list.push(e);
                        }
                    }
                }
                if let Some(elt) = elt {
                    list.push(elt);
                }
                continue;
            }
            if self.abort_parsing_list_or_move_to_next_token(kind) {
                break;
            }
        }
        self.reparse_list = outer_reparse_list;
        self.parsing_contexts = save_parsing_contexts;
        // `p.nodeSliceArena.Clone(list)`
        list
    }

    /// `func (p *Parser) parseList(kind, parseElement) *ast.NodeList`
    fn parse_list(
        &mut self,
        kind: ParsingContext,
        parse_element: impl Fn(&mut Self) -> Option<NodeId>,
    ) -> NodeList {
        let pos = self.node_pos();
        let nodes = self.parse_list_index(kind, |p, _| parse_element(p));
        self.new_node_list(TextRange::new(pos, self.node_pos()), nodes)
    }

    /// `func (p *Parser) parseDelimitedList(kind, parseElement, expectSemi)` —
    /// a non-`None` (but possibly empty) list on success, `None` when
    /// `parseElement` returned nil.
    fn parse_delimited_list(
        &mut self,
        kind: ParsingContext,
        parse_element: impl Fn(&mut Self) -> Option<NodeId>,
        _expect_semi: bool,
    ) -> Option<NodeList> {
        let pos = self.node_pos();
        let save_parsing_contexts = self.parsing_contexts;
        self.parsing_contexts |= 1 << kind;
        let mut list: Vec<NodeId> = Vec::with_capacity(16);
        loop {
            if self.is_list_element(kind, false /*inErrorRecovery*/) {
                let start_pos = self.node_pos();
                let element = parse_element(self);
                let Some(element) = element else {
                    self.parsing_contexts = save_parsing_contexts;
                    // Return nil to indicate parseElement failed
                    return None;
                };
                list.push(element);
                if self.parse_optional(Kind::CommaToken) {
                    // No need to check for a zero length node since we know we parsed a comma
                    continue;
                }
                if self.is_list_terminator(kind) {
                    break;
                }
                // We didn't get a comma, and the list wasn't terminated, explicitly parse
                // out a comma so we give a good error message.
                if self.token != Kind::CommaToken && kind == PC_ENUM_MEMBERS {
                    self.parse_error_at_current_token(
                        &diagnostics::An_enum_member_name_must_be_followed_by_a_or,
                        &[],
                    );
                } else {
                    self.parse_expected(Kind::CommaToken);
                }
                // If the token was a semicolon, and the caller allows that, then skip it and
                // continue.  This ensures we get back on track and don't result in tons of
                // parse errors.  For example, this can happen when people do things like use
                // a semicolon to delimit object literal members.   Note: we'll have already
                // reported an error when we called parseExpected above.
                if (kind == PC_OBJECT_LITERAL_MEMBERS || kind == PC_IMPORT_ATTRIBUTES)
                    && self.token == Kind::SemicolonToken
                    && !self.has_preceding_line_break()
                {
                    self.next_token();
                }
                if start_pos == self.node_pos() {
                    // What we're parsing isn't actually remotely recognizable as a element and we've consumed no tokens whatsoever
                    // Consume a token to advance the parser in some way and avoid an infinite loop
                    // This can happen when we're speculatively parsing parenthesized expressions which we think may be arrow functions,
                    // or when a modifier keyword which is disallowed as a parameter name (ie, `static` in strict mode) is supplied
                    self.next_token();
                }
                continue;
            }
            if self.is_list_terminator(kind) {
                break;
            }
            if self.abort_parsing_list_or_move_to_next_token(kind) {
                break;
            }
        }
        self.parsing_contexts = save_parsing_contexts;
        Some(self.new_node_list(TextRange::new(pos, self.node_pos()), list))
    }

    /// `func (p *Parser) parseBracketedList(kind, parseElement, opening, closing)` —
    /// non-`None` list on success, a *missing* list when `opening` was absent,
    /// `None` when `parseElement` failed.
    fn parse_bracketed_list(
        &mut self,
        kind: ParsingContext,
        parse_element: impl Fn(&mut Self) -> Option<NodeId>,
        opening: Kind,
        closing: Kind,
    ) -> Option<NodeList> {
        if self.parse_expected(opening) {
            let result = self.parse_delimited_list(kind, parse_element, false);
            self.parse_expected(closing);
            return result;
        }
        Some(self.create_missing_list())
    }

    /// `func (p *Parser) abortParsingListOrMoveToNextToken(kind) bool`
    fn abort_parsing_list_or_move_to_next_token(&mut self, kind: ParsingContext) -> bool {
        self.parsing_context_errors(kind);
        if self.is_in_some_parsing_context() {
            return true;
        }
        self.next_token();
        false
    }

    /// `func (p *Parser) isInSomeParsingContext() bool` — true if positioned
    /// at element or terminator of the current list or any enclosing list.
    fn is_in_some_parsing_context(&mut self) -> bool {
        // We should be in at least one parsing context, be it SourceElements while parsing
        // a SourceFile, or JSDocComment when lazily parsing JSDoc.
        debug_assert!(self.parsing_contexts != 0, "Missing parsing context");
        for kind in 0..PC_COUNT {
            if self.parsing_contexts & (1 << kind) != 0
                && (self.is_list_element(kind, true /*inErrorRecovery*/)
                    || self.is_list_terminator(kind))
            {
                return true;
            }
        }
        false
    }

    /// `func (p *Parser) parsingContextErrors(context ParsingContext)`
    fn parsing_context_errors(&mut self, context: ParsingContext) {
        match context {
            PC_SOURCE_ELEMENTS => {
                if self.token == Kind::DefaultKeyword {
                    self.parse_error_at_current_token(
                        &diagnostics::X_0_expected,
                        &["export".to_string()],
                    );
                } else {
                    self.parse_error_at_current_token(
                        &diagnostics::Declaration_or_statement_expected,
                        &[],
                    );
                }
            }
            PC_BLOCK_STATEMENTS => {
                self.parse_error_at_current_token(
                    &diagnostics::Declaration_or_statement_expected,
                    &[],
                );
            }
            PC_SWITCH_CLAUSES => {
                self.parse_error_at_current_token(
                    &diagnostics::X_case_or_default_expected,
                    &[],
                );
            }
            PC_SWITCH_CLAUSE_STATEMENTS => {
                self.parse_error_at_current_token(&diagnostics::Statement_expected, &[]);
            }
            PC_REST_PROPERTIES | PC_TYPE_MEMBERS => {
                self.parse_error_at_current_token(
                    &diagnostics::Property_or_signature_expected,
                    &[],
                );
            }
            PC_CLASS_MEMBERS => {
                self.parse_error_at_current_token(
                    &diagnostics::Unexpected_token_A_constructor_method_accessor_or_property_was_expected,
                    &[],
                );
            }
            PC_ENUM_MEMBERS => {
                self.parse_error_at_current_token(&diagnostics::Enum_member_expected, &[]);
            }
            PC_HERITAGE_CLAUSE_ELEMENT => {
                self.parse_error_at_current_token(&diagnostics::Expression_expected, &[]);
            }
            PC_VARIABLE_DECLARATIONS => {
                if is_keyword(self.token) {
                    self.parse_error_at_current_token(
                        &diagnostics::X_0_is_not_allowed_as_a_variable_declaration_name,
                        &[scanner::token_to_string(self.token).to_string()],
                    );
                } else {
                    self.parse_error_at_current_token(
                        &diagnostics::Variable_declaration_expected,
                        &[],
                    );
                }
            }
            PC_OBJECT_BINDING_ELEMENTS => {
                self.parse_error_at_current_token(
                    &diagnostics::Property_destructuring_pattern_expected,
                    &[],
                );
            }
            PC_ARRAY_BINDING_ELEMENTS => {
                self.parse_error_at_current_token(
                    &diagnostics::Array_element_destructuring_pattern_expected,
                    &[],
                );
            }
            PC_ARGUMENT_EXPRESSIONS => {
                self.parse_error_at_current_token(
                    &diagnostics::Argument_expression_expected,
                    &[],
                );
            }
            PC_OBJECT_LITERAL_MEMBERS => {
                self.parse_error_at_current_token(
                    &diagnostics::Property_assignment_expected,
                    &[],
                );
            }
            PC_ARRAY_LITERAL_MEMBERS => {
                self.parse_error_at_current_token(
                    &diagnostics::Expression_or_comma_expected,
                    &[],
                );
            }
            PC_JS_DOC_PARAMETERS => {
                self.parse_error_at_current_token(
                    &diagnostics::Parameter_declaration_expected,
                    &[],
                );
            }
            PC_PARAMETERS => {
                if is_keyword(self.token) {
                    self.parse_error_at_current_token(
                        &diagnostics::X_0_is_not_allowed_as_a_parameter_name,
                        &[scanner::token_to_string(self.token).to_string()],
                    );
                } else {
                    self.parse_error_at_current_token(
                        &diagnostics::Parameter_declaration_expected,
                        &[],
                    );
                }
            }
            PC_TYPE_PARAMETERS => {
                self.parse_error_at_current_token(
                    &diagnostics::Type_parameter_declaration_expected,
                    &[],
                );
            }
            PC_TYPE_ARGUMENTS => {
                self.parse_error_at_current_token(&diagnostics::Type_argument_expected, &[]);
            }
            PC_TUPLE_ELEMENT_TYPES => {
                self.parse_error_at_current_token(&diagnostics::Type_expected, &[]);
            }
            PC_HERITAGE_CLAUSES => {
                self.parse_error_at_current_token(&diagnostics::Unexpected_token_expected, &[]);
            }
            PC_IMPORT_OR_EXPORT_SPECIFIERS => {
                if self.token == Kind::FromKeyword {
                    self.parse_error_at_current_token(
                        &diagnostics::X_0_expected,
                        &["}".to_string()],
                    );
                } else {
                    self.parse_error_at_current_token(&diagnostics::Identifier_expected, &[]);
                }
            }
            PC_JSX_ATTRIBUTES | PC_JSX_CHILDREN | PC_JS_DOC_COMMENT => {
                self.parse_error_at_current_token(&diagnostics::Identifier_expected, &[]);
            }
            PC_IMPORT_ATTRIBUTES => {
                self.parse_error_at_current_token(
                    &diagnostics::Identifier_or_string_literal_expected,
                    &[],
                );
            }
            _ => panic!("Unhandled case in parsingContextErrors"),
        }
    }

    /// `func (p *Parser) parseExpectedJSDoc(kind ast.Kind) bool`
    fn parse_expected_jsdoc(&mut self, kind: Kind) -> bool {
        if self.token == kind {
            self.next_token_jsdoc();
            return true;
        }
        if !is_keyword_or_punctuation(kind) {
            panic!("Invalid JSDoc kind: expected keyword or punctuation");
        }
        self.parse_error_at_current_token(
            &diagnostics::X_0_expected,
            &[scanner::token_to_string(kind).to_string()],
        );
        false
    }

    /// `func (p *Parser) parseExpectedMatchingBrackets(openKind, closeKind, openParsed, openPosition)`
    fn parse_expected_matching_brackets(
        &mut self,
        open_kind: Kind,
        close_kind: Kind,
        open_parsed: bool,
        open_position: i32,
    ) {
        if self.token == close_kind {
            self.next_token();
            return;
        }
        let last_error = self.parse_error_at_current_token(
            &diagnostics::X_0_expected,
            &[scanner::token_to_string(close_kind).to_string()],
        );
        if !open_parsed {
            return;
        }
        if let Some(last_error) = last_error {
            let related = new_diagnostic::<String>(
                None,
                TextRange::new(open_position, open_position),
                &diagnostics::The_parser_expected_to_find_a_1_to_match_the_0_token_here,
                &[
                    scanner::token_to_string(open_kind).to_string(),
                    scanner::token_to_string(close_kind).to_string(),
                ],
            );
            lock_diagnostic(&last_error).add_related_info(Some(related));
        }
    }

    /// `func (p *Parser) parseOptional(token ast.Kind) bool`
    fn parse_optional(&mut self, token: Kind) -> bool {
        if self.token == token {
            self.next_token();
            return true;
        }
        false
    }

    /// `func (p *Parser) parseExpected(kind ast.Kind) bool`
    fn parse_expected(&mut self, kind: Kind) -> bool {
        self.parse_expected_with_diagnostic(kind, None, true)
    }

    /// `func (p *Parser) parseExpectedWithoutAdvancing(kind ast.Kind) bool`
    fn parse_expected_without_advancing(&mut self, kind: Kind) -> bool {
        self.parse_expected_with_diagnostic(kind, None, false)
    }

    /// `func (p *Parser) parseExpectedWithDiagnostic(kind, message, shouldAdvance) bool`
    fn parse_expected_with_diagnostic(
        &mut self,
        kind: Kind,
        message: Option<&'static Message>,
        should_advance: bool,
    ) -> bool {
        if self.token == kind {
            if should_advance {
                self.next_token();
            }
            return true;
        }
        // Report specific message if provided with one.  Otherwise, report generic fallback message.
        if let Some(message) = message {
            self.parse_error_at_current_token(message, &[]);
        } else {
            self.parse_error_at_current_token(
                &diagnostics::X_0_expected,
                &[scanner::token_to_string(kind).to_string()],
            );
        }
        false
    }

    /// `func (p *Parser) parseTokenNode() *ast.Node`
    fn parse_token_node(&mut self) -> NodeId {
        let pos = self.node_pos();
        let kind = self.token;
        self.next_token();
        let token = self.factory.new_token(&mut self.nodes, kind);
        self.finish_node(token, pos)
    }

    /// `func (p *Parser) parseExpectedToken(kind ast.Kind) *ast.Node`
    fn parse_expected_token(&mut self, kind: Kind) -> NodeId {
        let token = self.parse_optional_token(kind);
        match token {
            Some(token) => token,
            None => {
                self.parse_error_at_current_token(
                    &diagnostics::X_0_expected,
                    &[scanner::token_to_string(kind).to_string()],
                );
                let token = self.factory.new_token(&mut self.nodes, kind);
                self.finish_node(token, self.node_pos())
            }
        }
    }

    /// `func (p *Parser) parseOptionalToken(kind ast.Kind) *ast.Node`
    fn parse_optional_token(&mut self, kind: Kind) -> Option<NodeId> {
        if self.token == kind {
            return Some(self.parse_token_node());
        }
        None
    }

    /// `func (p *Parser) parseExpectedTokenJSDoc(kind ast.Kind) *ast.Node`
    fn parse_expected_token_jsdoc(&mut self, kind: Kind) -> NodeId {
        let optional = self.parse_optional_token_jsdoc(kind);
        match optional {
            Some(optional) => optional,
            None => {
                if !is_keyword_or_punctuation(kind) {
                    panic!("expected keyword or punctuation");
                }
                self.parse_error_at_current_token(
                    &diagnostics::X_0_expected,
                    &[scanner::token_to_string(kind).to_string()],
                );
                let token = self.factory.new_token(&mut self.nodes, kind);
                self.finish_node(token, self.node_pos())
            }
        }
    }

    /// `func (p *Parser) parseOptionalTokenJSDoc(kind ast.Kind) *ast.Node`
    fn parse_optional_token_jsdoc(&mut self, kind: Kind) -> Option<NodeId> {
        if self.token == kind {
            return Some(self.parse_token_node());
        }
        None
    }
}

/// `func getErrorSpanForNode(sourceText string, node *ast.Node) core.TextRange`
pub fn get_error_span_for_node(source_text: &str, node: NodeId, nodes: &[Node]) -> TextRange {
    let mut pos = nodes[node].pos();
    if !node_is_missing(Some(node), nodes) {
        pos = scanner::skip_trivia(source_text, pos);
    }
    TextRange::new(pos, nodes[node].end())
}

/// `func isDoubleQuotedString(node *ast.Node) bool`
fn is_double_quoted_string(node: &Node) -> bool {
    is_string_literal(node)
        && !node
            .as_string_literal()
            .literal_expression_base
            .literal_like_node_base
            .token_flags
            .intersects(TokenFlags::SINGLE_QUOTE)
}

/// `func attachFileToDiagnostics(diagnostics []*ast.Diagnostic, file *ast.SourceFile)`
pub fn attach_file_to_diagnostics(
    diagnostics: Vec<DiagnosticRef>,
    file: NodeId,
    nodes: &[Node],
) -> Vec<DiagnosticRef> {
    let diag_file = tsc_ast::diagnostic::DiagnosticFile::from_node(file, nodes);
    for d in &diagnostics {
        let related = lock_diagnostic(d).related_information().to_vec();
        lock_diagnostic(d).set_file(Some(diag_file.clone()));
        for r in related {
            lock_diagnostic(&r).set_file(Some(diag_file.clone()));
        }
    }
    diagnostics
}

/// `func ParseIsolatedEntityName(text string) *ast.EntityName`
///
/// PORT: returns `(entity_name, nodes)` — the parsed entity name plus its
/// arena (Go returns a bare pointer into the pooled parser's arena).
pub fn parse_isolated_entity_name(text: &str) -> (Option<NodeId>, Vec<Node>) {
    register_jsdoc_parse_hook();
    let mut p = Parser::new();
    p.initialize_state(SourceFileParseOptions::default(), text, ScriptKind::Js);
    p.next_token();
    let entity_name = p.parse_entity_name(true, false, None);
    let entity_name = if p.token == Kind::EndOfFile && p.diagnostics.is_empty() {
        entity_name
    } else {
        None
    };
    (entity_name, p.nodes)
}

// ---------------------------------------------------------------------------
// Statements and declarations (Go: parser.go `parseStatement` onward)
// ---------------------------------------------------------------------------

/// `func isDeclareModifier(modifier *ast.Node) bool`
fn is_declare_modifier(modifier: &Node) -> bool {
    modifier.kind == Kind::DeclareKeyword
}

/// `func isExportModifier(modifier *ast.Node) bool`
fn is_export_modifier(modifier: &Node) -> bool {
    modifier.kind == Kind::ExportKeyword
}

/// `func isAsyncModifier(modifier *ast.Node) bool`
fn is_async_modifier(modifier: &Node) -> bool {
    modifier.kind == Kind::AsyncKeyword
}

/// `func modifierListHasAsync(modifiers *ast.ModifierList) bool`
fn modifier_list_has_async(modifiers: Option<&ModifierList>, nodes: &[Node]) -> bool {
    modifiers.is_some_and(|m| core::some(&m.nodes, |n| is_async_modifier(&nodes[*n])))
}

/// `func isTypeHeritageClause(isInterface bool, token ast.Kind) bool`
fn is_type_heritage_clause(is_interface: bool, token: Kind) -> bool {
    is_interface && token == Kind::ExtendsKeyword
        || !is_interface && token == Kind::ImplementsKeyword
}

/// `func isReservedWord(token ast.Kind) bool`
fn is_reserved_word(token: Kind) -> bool {
    Kind::FIRST_RESERVED_WORD <= token && token <= Kind::LAST_RESERVED_WORD
}

impl<'a> Parser<'a> {
    /// `func (p *Parser) parseStatement() *ast.Statement`
    fn parse_statement(&mut self) -> NodeId {
        match self.token {
            Kind::SemicolonToken => return self.parse_empty_statement(),
            Kind::OpenBraceToken => {
                return self.parse_block(false /*ignoreMissingOpenBrace*/, None);
            }
            Kind::VarKeyword => {
                return self.parse_variable_statement(
                    self.node_pos(),
                    self.jsdoc_scanner_info(),
                    None,
                );
            }
            Kind::LetKeyword => {
                if self.is_let_declaration() {
                    return self.parse_variable_statement(
                        self.node_pos(),
                        self.jsdoc_scanner_info(),
                        None,
                    );
                }
            }
            Kind::AwaitKeyword => {
                if self.is_await_using_declaration() {
                    return self.parse_variable_statement(
                        self.node_pos(),
                        self.jsdoc_scanner_info(),
                        None,
                    );
                }
            }
            Kind::UsingKeyword => {
                if self.is_using_declaration() {
                    return self.parse_variable_statement(
                        self.node_pos(),
                        self.jsdoc_scanner_info(),
                        None,
                    );
                }
            }
            Kind::FunctionKeyword => {
                return self.parse_function_declaration(
                    self.node_pos(),
                    self.jsdoc_scanner_info(),
                    None,
                );
            }
            Kind::ClassKeyword => {
                return self.parse_class_declaration(
                    self.node_pos(),
                    self.jsdoc_scanner_info(),
                    None,
                );
            }
            Kind::IfKeyword => return self.parse_if_statement(),
            Kind::DoKeyword => return self.parse_do_statement(),
            Kind::WhileKeyword => return self.parse_while_statement(),
            Kind::ForKeyword => return self.parse_for_or_for_in_or_for_of_statement(),
            Kind::ContinueKeyword => return self.parse_continue_statement(),
            Kind::BreakKeyword => return self.parse_break_statement(),
            Kind::ReturnKeyword => return self.parse_return_statement(),
            Kind::WithKeyword => return self.parse_with_statement(),
            Kind::SwitchKeyword => return self.parse_switch_statement(),
            Kind::ThrowKeyword => return self.parse_throw_statement(),
            Kind::TryKeyword | Kind::CatchKeyword | Kind::FinallyKeyword => {
                return self.parse_try_statement();
            }
            Kind::DebuggerKeyword => return self.parse_debugger_statement(),
            Kind::AtToken => return self.parse_declaration(),
            Kind::AsyncKeyword
            | Kind::InterfaceKeyword
            | Kind::TypeKeyword
            | Kind::ModuleKeyword
            | Kind::NamespaceKeyword
            | Kind::DeclareKeyword
            | Kind::ConstKeyword
            | Kind::EnumKeyword
            | Kind::ExportKeyword
            | Kind::ImportKeyword
            | Kind::PrivateKeyword
            | Kind::ProtectedKeyword
            | Kind::PublicKeyword
            | Kind::AbstractKeyword
            | Kind::AccessorKeyword
            | Kind::StaticKeyword
            | Kind::ReadonlyKeyword
            | Kind::GlobalKeyword => {
                if self.is_start_of_declaration() {
                    return self.parse_declaration();
                }
            }
            _ => {}
        }
        self.parse_expression_or_labeled_statement()
    }

    /// `func (p *Parser) parseDeclaration() *ast.Statement`
    fn parse_declaration(&mut self) -> NodeId {
        // `parseListElement` attempted to get the reused node at this position,
        // but the ambient context flag was not yet set, so the node appeared
        // not reusable in that context.
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers_ex(
            true,  /*allowDecorators*/
            false, /*permitConstAsModifier*/
            false, /*stopOnStartOfClassStaticBlock*/
        );
        let is_ambient = modifiers
            .as_ref()
            .is_some_and(|m| core::some(&m.nodes, |n| is_declare_modifier(&self.nodes[*n])));
        if is_ambient {
            let modifiers = modifiers.unwrap();
            for &m in &modifiers.nodes {
                self.nodes[m].flags |= NodeFlags::AMBIENT;
            }
            let save_context_flags = self.context_flags;
            self.set_context_flags(NodeFlags::AMBIENT, true);
            let result = self.parse_declaration_worker(pos, jsdoc, Some(modifiers));
            self.context_flags = save_context_flags;
            result
        } else {
            self.parse_declaration_worker(pos, jsdoc, modifiers)
        }
    }

    /// `func (p *Parser) parseDeclarationWorker(pos, jsdoc, modifiers)`
    fn parse_declaration_worker(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        match self.token {
            Kind::VarKeyword | Kind::LetKeyword | Kind::ConstKeyword | Kind::UsingKeyword => {
                return self.parse_variable_statement(pos, jsdoc, modifiers);
            }
            Kind::AwaitKeyword => {
                if self.is_await_using_declaration() {
                    return self.parse_variable_statement(pos, jsdoc, modifiers);
                }
            }
            Kind::FunctionKeyword => {
                return self.parse_function_declaration(pos, jsdoc, modifiers);
            }
            Kind::ClassKeyword => return self.parse_class_declaration(pos, jsdoc, modifiers),
            Kind::InterfaceKeyword => {
                return self.parse_interface_declaration(pos, jsdoc, modifiers);
            }
            Kind::TypeKeyword => {
                return self.parse_type_alias_declaration(pos, jsdoc, modifiers);
            }
            Kind::EnumKeyword => return self.parse_enum_declaration(pos, jsdoc, modifiers),
            Kind::GlobalKeyword | Kind::ModuleKeyword | Kind::NamespaceKeyword => {
                return self.parse_module_declaration(pos, jsdoc, modifiers);
            }
            Kind::ImportKeyword => {
                return self.parse_import_declaration_or_import_equals_declaration(
                    pos, jsdoc, modifiers,
                );
            }
            Kind::ExportKeyword => {
                self.next_token();
                match self.token {
                    Kind::DefaultKeyword | Kind::EqualsToken => {
                        return self.parse_export_assignment(pos, jsdoc, modifiers);
                    }
                    Kind::AsKeyword => {
                        return self.parse_namespace_export_declaration(pos, jsdoc, modifiers);
                    }
                    _ => return self.parse_export_declaration(pos, jsdoc, modifiers),
                }
            }
            _ => {}
        }
        if modifiers.is_some() {
            // We reached this point because we encountered decorators and/or modifiers and assumed a declaration
            // would follow. For recovery and error reporting purposes, return an incomplete declaration.
            let pos2 = self.node_pos();
            self.parse_error_at(pos2, pos2, &diagnostics::Declaration_expected, &[]);
            let node = self
                .factory
                .new_missing_declaration(&mut self.nodes, modifiers);
            return self.finish_node(node, pos);
        }
        panic!("Unhandled case in parseDeclarationWorker")
    }

    /// `func (p *Parser) isLetDeclaration() bool`
    fn is_let_declaration(&mut self) -> bool {
        // In ES6 'let' always starts a lexical declaration if followed by an identifier or {
        // or [.
        self.look_ahead(Self::next_token_is_binding_identifier_or_start_of_destructuring)
    }

    /// `func (p *Parser) nextTokenIsBindingIdentifierOrStartOfDestructuring() bool`
    fn next_token_is_binding_identifier_or_start_of_destructuring(&mut self) -> bool {
        self.next_token();
        self.is_binding_identifier()
            || self.token == Kind::OpenBraceToken
            || self.token == Kind::OpenBracketToken
    }

    /// `func (p *Parser) parseBlock(ignoreMissingOpenBrace, diagnosticMessage)`
    fn parse_block(
        &mut self,
        ignore_missing_open_brace: bool,
        diagnostic_message: Option<&'static Message>,
    ) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let open_brace_position = self.scanner.token_start() as i32;
        let open_brace_parsed = self.parse_expected_with_diagnostic(
            Kind::OpenBraceToken,
            diagnostic_message,
            true, /*shouldAdvance*/
        );
        let mut multiline = false;
        if open_brace_parsed || ignore_missing_open_brace {
            multiline = self.has_preceding_line_break();
            let statements = self.parse_list(PC_BLOCK_STATEMENTS, Self::parse_statement_some);
            self.parse_expected_matching_brackets(
                Kind::OpenBraceToken,
                Kind::CloseBraceToken,
                open_brace_parsed,
                open_brace_position,
            );
            let result = self.finish_node(
                self.factory
                    .new_block(&mut self.nodes, Some(statements), multiline),
                pos,
            );
            self.with_jsdoc(result, jsdoc);
            if self.token == Kind::EqualsToken {
                self.parse_error_at_current_token(&diagnostics::Declaration_or_statement_expected_This_follows_a_block_of_statements_so_if_you_intended_to_write_a_destructuring_assignment_you_might_need_to_wrap_the_whole_assignment_in_parentheses, &[]);
                self.next_token();
            }
            return result;
        }
        let result = self.finish_node(
            self.factory.new_block(
                &mut self.nodes,
                Some(self.create_missing_list()),
                multiline,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseEmptyStatement() *ast.Node`
    fn parse_empty_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::SemicolonToken);
        let result = self.finish_node(self.factory.new_empty_statement(&mut self.nodes), pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseIfStatement() *ast.Node`
    fn parse_if_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::IfKeyword);
        let open_paren_position = self.scanner.token_start() as i32;
        let open_paren_parsed = self.parse_expected(Kind::OpenParenToken);
        let expression = self.parse_expression_allow_in();
        self.parse_expected_matching_brackets(
            Kind::OpenParenToken,
            Kind::CloseParenToken,
            open_paren_parsed,
            open_paren_position,
        );
        let then_statement = self.parse_statement();
        let mut else_statement = None;
        if self.parse_optional(Kind::ElseKeyword) {
            else_statement = Some(self.parse_statement());
        }
        let result = self.finish_node(
            self.factory.new_if_statement(
                &mut self.nodes,
                Some(expression),
                Some(then_statement),
                else_statement,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseDoStatement() *ast.Node`
    fn parse_do_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::DoKeyword);
        let statement = self.parse_statement();
        self.parse_expected(Kind::WhileKeyword);
        let open_paren_position = self.scanner.token_start() as i32;
        let open_paren_parsed = self.parse_expected(Kind::OpenParenToken);
        let expression = self.parse_expression_allow_in();
        self.parse_expected_matching_brackets(
            Kind::OpenParenToken,
            Kind::CloseParenToken,
            open_paren_parsed,
            open_paren_position,
        );
        // From: https://mail.mozilla.org/pipermail/es-discuss/2011-August/016188.html
        // 157 min --- All allen at wirfs-brock.com CONF --- "do{;}while(false)false" prohibited in
        // spec but allowed in consensus reality. Approved -- this is the de-facto standard whereby
        //  do;while(0)x will have a semicolon inserted before x.
        self.parse_optional(Kind::SemicolonToken);
        let result = self.finish_node(
            self.factory
                .new_do_statement(&mut self.nodes, Some(statement), Some(expression)),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseWhileStatement() *ast.Node`
    fn parse_while_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::WhileKeyword);
        let open_paren_position = self.scanner.token_start() as i32;
        let open_paren_parsed = self.parse_expected(Kind::OpenParenToken);
        let expression = self.parse_expression_allow_in();
        self.parse_expected_matching_brackets(
            Kind::OpenParenToken,
            Kind::CloseParenToken,
            open_paren_parsed,
            open_paren_position,
        );
        let statement = self.parse_statement();
        let result = self.finish_node(
            self.factory
                .new_while_statement(&mut self.nodes, Some(expression), Some(statement)),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseForOrForInOrForOfStatement() *ast.Node`
    fn parse_for_or_for_in_or_for_of_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::ForKeyword);
        let await_token = self.parse_optional_token(Kind::AwaitKeyword);
        self.parse_expected(Kind::OpenParenToken);
        let mut initializer: Option<NodeId> = None;
        if self.token != Kind::SemicolonToken {
            if self.token == Kind::VarKeyword
                || self.token == Kind::LetKeyword
                || self.token == Kind::ConstKeyword
                || self.token == Kind::UsingKeyword
                    && self.look_ahead(
                        Self::next_token_is_binding_identifier_or_start_of_destructuring_on_same_line_disallow_of,
                    )
                // this one is meant to allow of
                || self.token == Kind::AwaitKeyword
                    && self.look_ahead(
                        Self::next_is_using_keyword_then_binding_identifier_or_start_of_object_destructuring_on_same_line,
                    )
            {
                initializer = Some(self.parse_variable_declaration_list(
                    true, /*inForStatementInitializer*/
                ));
            } else {
                initializer = Some(self.do_in_context(
                    NodeFlags::DISALLOW_IN_CONTEXT,
                    true,
                    Self::parse_expression,
                ));
            }
        }
        let result: NodeId;
        if (await_token.is_some() && self.parse_expected(Kind::OfKeyword))
            || (await_token.is_none() && self.parse_optional(Kind::OfKeyword))
        {
            let expression = self.do_in_context(
                NodeFlags::DISALLOW_IN_CONTEXT,
                false,
                Self::parse_assignment_expression_or_higher,
            );
            self.parse_expected(Kind::CloseParenToken);
            let statement = self.parse_statement();
            result = self.factory.new_for_in_or_of_statement(
                &mut self.nodes,
                Kind::ForOfStatement,
                await_token,
                initializer,
                Some(expression),
                Some(statement),
            );
        } else if self.parse_optional(Kind::InKeyword) {
            let expression = self.parse_expression_allow_in();
            self.parse_expected(Kind::CloseParenToken);
            let statement = self.parse_statement();
            result = self.factory.new_for_in_or_of_statement(
                &mut self.nodes,
                Kind::ForInStatement,
                None, /*awaitToken*/
                initializer,
                Some(expression),
                Some(statement),
            );
        } else {
            self.parse_expected(Kind::SemicolonToken);
            let mut condition = None;
            if self.token != Kind::SemicolonToken && self.token != Kind::CloseParenToken {
                condition = Some(self.parse_expression_allow_in());
            }
            self.parse_expected(Kind::SemicolonToken);
            let mut incrementor = None;
            if self.token != Kind::CloseParenToken {
                incrementor = Some(self.parse_expression_allow_in());
            }
            self.parse_expected(Kind::CloseParenToken);
            let statement = self.parse_statement();
            result = self.factory.new_for_statement(
                &mut self.nodes,
                initializer,
                condition,
                incrementor,
                Some(statement),
            );
        }
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseBreakStatement() *ast.Node`
    fn parse_break_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::BreakKeyword);
        let label = self.parse_identifier_unless_at_semicolon();
        self.parse_semicolon();
        let result = self.finish_node(
            self.factory.new_break_statement(&mut self.nodes, label),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseContinueStatement() *ast.Node`
    fn parse_continue_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::ContinueKeyword);
        let label = self.parse_identifier_unless_at_semicolon();
        self.parse_semicolon();
        let result = self.finish_node(
            self.factory.new_continue_statement(&mut self.nodes, label),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseIdentifierUnlessAtSemicolon() *ast.Node`
    fn parse_identifier_unless_at_semicolon(&mut self) -> Option<NodeId> {
        if !self.can_parse_semicolon() {
            return Some(self.parse_identifier());
        }
        None
    }

    /// `func (p *Parser) parseReturnStatement() *ast.Node`
    fn parse_return_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::ReturnKeyword);
        let mut expression = None;
        if !self.can_parse_semicolon() {
            expression = Some(self.parse_expression_allow_in());
        }
        self.parse_semicolon();
        let result = self.finish_node(
            self.factory
                .new_return_statement(&mut self.nodes, expression),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseWithStatement() *ast.Node`
    fn parse_with_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::WithKeyword);
        let open_paren_position = self.scanner.token_start() as i32;
        let open_paren_parsed = self.parse_expected(Kind::OpenParenToken);
        let expression = self.parse_expression_allow_in();
        self.parse_expected_matching_brackets(
            Kind::OpenParenToken,
            Kind::CloseParenToken,
            open_paren_parsed,
            open_paren_position,
        );
        let statement = self.do_in_context(
            NodeFlags::IN_WITH_STATEMENT,
            true,
            Self::parse_statement,
        );
        let result = self.finish_node(
            self.factory
                .new_with_statement(&mut self.nodes, Some(expression), Some(statement)),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseCaseClause() *ast.Node`
    fn parse_case_clause(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::CaseKeyword);
        let expression = self.parse_expression_allow_in();
        self.parse_expected(Kind::ColonToken);
        let statements =
            self.parse_list(PC_SWITCH_CLAUSE_STATEMENTS, Self::parse_statement_some);
        let result = self.finish_node(
            self.factory.new_case_or_default_clause(
                &mut self.nodes,
                Kind::CaseClause,
                Some(expression),
                Some(statements),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseDefaultClause() *ast.Node`
    fn parse_default_clause(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::DefaultKeyword);
        self.parse_expected(Kind::ColonToken);
        let statements =
            self.parse_list(PC_SWITCH_CLAUSE_STATEMENTS, Self::parse_statement_some);
        let result = self.finish_node(
            self.factory.new_case_or_default_clause(
                &mut self.nodes,
                Kind::DefaultClause,
                None, /*expression*/
                Some(statements),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseCaseOrDefaultClause() *ast.Node`
    fn parse_case_or_default_clause(&mut self) -> NodeId {
        if self.token == Kind::CaseKeyword {
            return self.parse_case_clause();
        }
        self.parse_default_clause()
    }

    fn parse_case_or_default_clause_some(&mut self) -> Option<NodeId> {
        Some(self.parse_case_or_default_clause())
    }

    /// `func (p *Parser) parseCaseBlock() *ast.Node`
    fn parse_case_block(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::OpenBraceToken);
        let clauses =
            self.parse_list(PC_SWITCH_CLAUSES, Self::parse_case_or_default_clause_some);
        self.parse_expected(Kind::CloseBraceToken);
        let result = self.finish_node(
            self.factory
                .new_case_block(&mut self.nodes, Some(clauses)),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseSwitchStatement() *ast.Node`
    fn parse_switch_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::SwitchKeyword);
        self.parse_expected(Kind::OpenParenToken);
        let expression = self.parse_expression_allow_in();
        self.parse_expected(Kind::CloseParenToken);
        let case_block = self.parse_case_block();
        let result = self.finish_node(
            self.factory.new_switch_statement(
                &mut self.nodes,
                Some(expression),
                Some(case_block),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseThrowStatement() *ast.Node`
    fn parse_throw_statement(&mut self) -> NodeId {
        // ThrowStatement[Yield] :
        //      throw [no LineTerminator here]Expression[In, ?Yield];
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::ThrowKeyword);
        // Because of automatic semicolon insertion, we need to report error if this
        // throw could be terminated with a semicolon.  Note: we can't call 'parseExpression'
        // directly as that might consume an expression on the following line.
        // Instead, we create a "missing" identifier, but don't report an error. The actual error
        // will be reported in the grammar walker.
        let expression = if !self.has_preceding_line_break() {
            self.parse_expression_allow_in()
        } else {
            self.create_missing_identifier()
        };
        if !self.try_parse_semicolon() {
            self.parse_error_for_missing_semicolon_after(expression);
        }
        let result = self.finish_node(
            self.factory
                .new_throw_statement(&mut self.nodes, Some(expression)),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    // TODO: Review for error recovery
    /// `func (p *Parser) parseTryStatement() *ast.Node`
    fn parse_try_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::TryKeyword);
        let try_block = self.parse_block(false /*ignoreMissingOpenBrace*/, None);
        let mut catch_clause = None;
        if self.token == Kind::CatchKeyword {
            catch_clause = Some(self.parse_catch_clause());
        }
        // If we don't have a catch clause, then we must have a finally clause.  Try to parse
        // one out no matter what.
        let mut finally_block = None;
        if catch_clause.is_none() || self.token == Kind::FinallyKeyword {
            self.parse_expected_with_diagnostic(
                Kind::FinallyKeyword,
                Some(&diagnostics::X_catch_or_finally_expected),
                true, /*shouldAdvance*/
            );
            finally_block = Some(self.parse_block(false /*ignoreMissingOpenBrace*/, None));
        }
        let result = self.finish_node(
            self.factory.new_try_statement(
                &mut self.nodes,
                Some(try_block),
                catch_clause,
                finally_block,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseCatchClause() *ast.Node`
    fn parse_catch_clause(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::CatchKeyword);
        let mut variable_declaration = None;
        if self.parse_optional(Kind::OpenParenToken) {
            variable_declaration = Some(self.parse_variable_declaration());
            self.parse_expected(Kind::CloseParenToken);
        }
        let block = self.parse_block(false /*ignoreMissingOpenBrace*/, None);
        self.finish_node(
            self.factory.new_catch_clause(
                &mut self.nodes,
                variable_declaration,
                Some(block),
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseDebuggerStatement() *ast.Node`
    fn parse_debugger_statement(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::DebuggerKeyword);
        self.parse_semicolon();
        let result =
            self.finish_node(self.factory.new_debugger_statement(&mut self.nodes), pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseExpressionOrLabeledStatement() *ast.Statement`
    fn parse_expression_or_labeled_statement(&mut self) -> NodeId {
        // Avoiding having to do the lookahead for a labeled statement by just trying to parse
        // out an expression, seeing if it is identifier and then seeing if it is followed by
        // a colon.
        let pos = self.node_pos();
        let mut jsdoc = self.jsdoc_scanner_info();
        let has_paren = self.token == Kind::OpenParenToken;
        let expression = self.parse_expression();

        if self.nodes[expression].kind == Kind::Identifier
            && self.parse_optional(Kind::ColonToken)
        {
            let statement = self.parse_statement();
            let result = self.finish_node(
                self.factory.new_labeled_statement(
                    &mut self.nodes,
                    Some(expression),
                    Some(statement),
                ),
                pos,
            );
            self.with_jsdoc(result, jsdoc);
            return result;
        }

        if !self.try_parse_semicolon() {
            self.parse_error_for_missing_semicolon_after(expression);
        }
        let result = self.finish_node(
            self.factory
                .new_expression_statement(&mut self.nodes, Some(expression)),
            pos,
        );
        if has_paren {
            jsdoc &= !JSDOC_SCANNER_INFO_HAS_JSDOC;
        }
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseVariableStatement(pos, jsdoc, modifiers)`
    fn parse_variable_statement(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let declaration_list =
            self.parse_variable_declaration_list(false /*inForStatementInitializer*/);
        self.parse_semicolon();
        let result = self.finish_node(
            self.factory.new_variable_statement(
                &mut self.nodes,
                modifiers,
                Some(declaration_list),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) parseVariableDeclarationList(inForStatementInitializer)`
    fn parse_variable_declaration_list(
        &mut self,
        in_for_statement_initializer: bool,
    ) -> NodeId {
        let pos = self.node_pos();
        let mut flags;
        match self.token {
            Kind::VarKeyword => flags = NodeFlags::NONE,
            Kind::LetKeyword => flags = NodeFlags::LET,
            Kind::ConstKeyword => flags = NodeFlags::CONST,
            Kind::UsingKeyword => flags = NodeFlags::USING,
            Kind::AwaitKeyword => {
                if !self.is_await_using_declaration() {
                    flags = NodeFlags::NONE;
                } else {
                    flags = NodeFlags::AWAIT_USING;
                    self.next_token();
                }
            }
            _ => panic!("Unhandled case in parseVariableDeclarationList"),
        }
        self.next_token();
        // The user may have written the following:
        //
        //    for (let of X) { }
        //
        // In this case, we want to parse an empty declaration list, and then parse 'of'
        // as a keyword. The reason this is not automatic is that 'of' is a valid identifier.
        // So we need to look ahead to determine if 'of' should be treated as a keyword in
        // this context.
        // The checker will then give an error that there is an empty declaration list.
        let declarations: Option<NodeList>;
        if self.token == Kind::OfKeyword
            && self.look_ahead(Self::next_is_identifier_and_close_paren)
        {
            declarations = Some(self.create_missing_list());
        } else {
            let save_context_flags = self.context_flags;
            self.set_context_flags(
                NodeFlags::DISALLOW_IN_CONTEXT,
                in_for_statement_initializer,
            );
            declarations = self.parse_delimited_list(
                PC_VARIABLE_DECLARATIONS,
                if in_for_statement_initializer {
                    Self::parse_variable_declaration_some
                } else {
                    Self::parse_variable_declaration_allow_exclamation_some
                },
                false,
            );
            self.context_flags = save_context_flags;
        }
        let result = self.finish_node(
            self.factory
                .new_variable_declaration_list(&mut self.nodes, declarations, flags),
            pos,
        );
        result
    }

    /// `func (p *Parser) nextIsIdentifierAndCloseParen() bool`
    fn next_is_identifier_and_close_paren(&mut self) -> bool {
        self.next_token_is_identifier() && self.next_token() == Kind::CloseParenToken
    }

    /// `func (p *Parser) nextTokenIsIdentifier() bool`
    fn next_token_is_identifier(&mut self) -> bool {
        self.next_token();
        self.is_identifier()
    }

    /// `func (p *Parser) parseVariableDeclaration() *ast.Node`
    fn parse_variable_declaration(&mut self) -> NodeId {
        self.parse_variable_declaration_worker(false /*allowExclamation*/)
    }

    fn parse_variable_declaration_some(&mut self) -> Option<NodeId> {
        Some(self.parse_variable_declaration())
    }

    /// `func (p *Parser) parseVariableDeclarationAllowExclamation() *ast.Node`
    fn parse_variable_declaration_allow_exclamation(&mut self) -> NodeId {
        self.parse_variable_declaration_worker(true /*allowExclamation*/)
    }

    fn parse_variable_declaration_allow_exclamation_some(&mut self) -> Option<NodeId> {
        Some(self.parse_variable_declaration_allow_exclamation())
    }

    /// `func (p *Parser) parseVariableDeclarationWorker(allowExclamation)`
    fn parse_variable_declaration_worker(&mut self, allow_exclamation: bool) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let name = self.parse_identifier_or_pattern_with_diagnostic(Some(
            &diagnostics::Private_identifiers_are_not_allowed_in_variable_declarations,
        ));
        let mut exclamation_token = None;
        if allow_exclamation
            && self.nodes[name].kind == Kind::Identifier
            && self.token == Kind::ExclamationToken
            && !self.has_preceding_line_break()
        {
            exclamation_token = Some(self.parse_token_node());
        }
        let type_node = self.parse_type_annotation();
        let mut initializer = None;
        if self.token != Kind::InKeyword && self.token != Kind::OfKeyword {
            initializer = self.parse_initializer();
        }
        let result = self.finish_node(
            self.factory.new_variable_declaration(
                &mut self.nodes,
                Some(name),
                exclamation_token,
                type_node,
                initializer,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) parseIdentifierOrPattern() *ast.Node`
    fn parse_identifier_or_pattern(&mut self) -> NodeId {
        self.parse_identifier_or_pattern_with_diagnostic(None)
    }

    /// `func (p *Parser) parseIdentifierOrPatternWithDiagnostic(...)`
    fn parse_identifier_or_pattern_with_diagnostic(
        &mut self,
        private_identifier_diagnostic_message: Option<&'static Message>,
    ) -> NodeId {
        if self.token == Kind::OpenBracketToken {
            return self.parse_array_binding_pattern();
        }
        if self.token == Kind::OpenBraceToken {
            return self.parse_object_binding_pattern();
        }
        self.parse_binding_identifier_with_diagnostic(private_identifier_diagnostic_message)
    }

    /// `func (p *Parser) parseArrayBindingPattern() *ast.Node`
    fn parse_array_binding_pattern(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::OpenBracketToken);
        let save_context_flags = self.context_flags;
        self.set_context_flags(NodeFlags::DISALLOW_IN_CONTEXT, false);
        let elements = self.parse_delimited_list(
            PC_ARRAY_BINDING_ELEMENTS,
            Self::parse_array_binding_element_some,
            false,
        );
        self.context_flags = save_context_flags;
        self.parse_expected(Kind::CloseBracketToken);
        self.finish_node(
            self.factory.new_binding_pattern(
                &mut self.nodes,
                Kind::ArrayBindingPattern,
                elements,
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseArrayBindingElement() *ast.Node`
    fn parse_array_binding_element(&mut self) -> NodeId {
        let pos = self.node_pos();
        let mut dot_dot_dot_token = None;
        let mut name = None;
        let mut initializer = None;
        if self.token != Kind::CommaToken {
            // These are all nil for a missing element
            dot_dot_dot_token = self.parse_optional_token(Kind::DotDotDotToken);
            name = Some(self.parse_identifier_or_pattern());
            initializer = self.parse_initializer();
        }
        self.finish_node(
            self.factory.new_binding_element(
                &mut self.nodes,
                dot_dot_dot_token,
                None, /*propertyName*/
                name,
                initializer,
            ),
            pos,
        )
    }

    fn parse_array_binding_element_some(&mut self) -> Option<NodeId> {
        Some(self.parse_array_binding_element())
    }

    /// `func (p *Parser) parseObjectBindingPattern() *ast.Node`
    fn parse_object_binding_pattern(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::OpenBraceToken);
        let save_context_flags = self.context_flags;
        self.set_context_flags(NodeFlags::DISALLOW_IN_CONTEXT, false);
        let elements = self.parse_delimited_list(
            PC_OBJECT_BINDING_ELEMENTS,
            Self::parse_object_binding_element_some,
            false,
        );
        self.context_flags = save_context_flags;
        self.parse_expected(Kind::CloseBraceToken);
        self.finish_node(
            self.factory.new_binding_pattern(
                &mut self.nodes,
                Kind::ObjectBindingPattern,
                elements,
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseObjectBindingElement() *ast.Node`
    fn parse_object_binding_element(&mut self) -> NodeId {
        let pos = self.node_pos();
        let dot_dot_dot_token = self.parse_optional_token(Kind::DotDotDotToken);
        let token_is_identifier = self.is_binding_identifier();
        let mut property_name = Some(self.parse_property_name());
        let name: Option<NodeId>;
        if token_is_identifier && self.token != Kind::ColonToken {
            name = property_name;
            property_name = None;
        } else {
            self.parse_expected(Kind::ColonToken);
            name = Some(self.parse_identifier_or_pattern());
        }
        let initializer = self.parse_initializer();
        self.finish_node(
            self.factory.new_binding_element(
                &mut self.nodes,
                dot_dot_dot_token,
                property_name,
                name,
                initializer,
            ),
            pos,
        )
    }

    fn parse_object_binding_element_some(&mut self) -> Option<NodeId> {
        Some(self.parse_object_binding_element())
    }

    /// `func (p *Parser) parseInitializer() *ast.Expression`
    fn parse_initializer(&mut self) -> Option<NodeId> {
        if self.parse_optional(Kind::EqualsToken) {
            return Some(self.parse_assignment_expression_or_higher());
        }
        None
    }

    /// `func (p *Parser) parseTypeAnnotation() *ast.TypeNode`
    fn parse_type_annotation(&mut self) -> Option<NodeId> {
        if self.parse_optional(Kind::ColonToken) {
            return Some(self.parse_type());
        }
        None
    }

    /// `func (p *Parser) parseFunctionDeclaration(pos, jsdoc, modifiers)`
    fn parse_function_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        self.parse_expected(Kind::FunctionKeyword);
        let asterisk_token = self.parse_optional_token(Kind::AsteriskToken);
        // We don't parse the name here in await context, instead we will report a grammar error in the checker.
        let mut name = None;
        if modifiers.is_none()
            || !modifiers
                .as_ref()
                .unwrap()
                .modifier_flags
                .intersects(ModifierFlags::DEFAULT)
            || self.is_binding_identifier()
        {
            name = Some(self.parse_binding_identifier());
        }
        let signature_flags = if asterisk_token.is_some() {
            ParseFlags::YIELD
        } else {
            ParseFlags::NONE
        } | if modifier_list_has_async(modifiers.as_ref(), &self.nodes) {
            ParseFlags::AWAIT
        } else {
            ParseFlags::NONE
        };
        let type_parameters = self.parse_type_parameters();
        let save_context_flags = self.context_flags;
        if modifiers
            .as_ref()
            .is_some_and(|m| m.modifier_flags.intersects(ModifierFlags::EXPORT))
        {
            self.set_context_flags(NodeFlags::AWAIT_CONTEXT, true);
        }
        let parameters = self.parse_parameters(signature_flags);
        let return_type = self.parse_return_type(Kind::ColonToken, false /*isType*/);
        let body = self.parse_function_block_or_semicolon(
            signature_flags,
            Some(&diagnostics::X_or_expected),
        );
        self.context_flags = save_context_flags;
        let result = self.finish_node(
            self.factory.new_function_declaration(
                &mut self.nodes,
                modifiers,
                asterisk_token,
                name,
                type_parameters,
                Some(parameters),
                return_type,
                None, /*fullSignature*/
                body,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }
}

impl<'a> Parser<'a> {
    /// `func (p *Parser) parseClassDeclaration(pos, jsdoc, modifiers)`
    fn parse_class_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        self.parse_class_declaration_or_expression(pos, jsdoc, modifiers, Kind::ClassDeclaration)
    }

    /// `func (p *Parser) parseClassExpression() *ast.Node`
    fn parse_class_expression(&mut self) -> NodeId {
        self.parse_class_declaration_or_expression(
            self.node_pos(),
            self.jsdoc_scanner_info(),
            None, /*modifiers*/
            Kind::ClassExpression,
        )
    }

    /// `func (p *Parser) parseClassDeclarationOrExpression(pos, jsdoc, modifiers, kind)`
    fn parse_class_declaration_or_expression(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
        kind: Kind,
    ) -> NodeId {
        let save_context_flags = self.context_flags;
        let save_has_await_identifier = self.statement_has_await_identifier;
        self.parse_expected(Kind::ClassKeyword);
        // We don't parse the name here in await context, instead we will report a grammar error in the checker.
        let name = self.parse_name_of_class_declaration_or_expression();
        let type_parameters = self.parse_type_parameters();
        if modifiers.is_some()
            && self.parsing_contexts & (1 << PC_SOURCE_ELEMENTS) != 0
            && self.parsing_contexts
                & ((1 << PC_BLOCK_STATEMENTS) | (1 << PC_SWITCH_CLAUSE_STATEMENTS))
                == 0
            && core::some(&modifiers.as_ref().unwrap().nodes, |n| {
                is_export_modifier(&self.nodes[*n])
            })
        {
            self.set_context_flags(NodeFlags::AWAIT_CONTEXT, true);
        }
        let heritage_clauses = self.parse_heritage_clauses(false /*isInterface*/);
        let members: Option<NodeList>;
        if self.parse_expected(Kind::OpenBraceToken) {
            // ClassTail[Yield,Await] : (Modified) See 14.5
            //      ClassHeritage[?Yield,?Await]opt { ClassBody[?Yield,?Await]opt }
            members = Some(self.parse_list(PC_CLASS_MEMBERS, Self::parse_class_element_some));
            self.parse_expected(Kind::CloseBraceToken);
        } else {
            members = Some(self.create_missing_list());
        }
        self.context_flags = save_context_flags;
        if modifiers.is_some()
            && modifiers_to_flags(&modifiers.as_ref().unwrap().nodes, &self.nodes)
                .intersects(ModifierFlags::AMBIENT)
        {
            self.statement_has_await_identifier = save_has_await_identifier;
        }
        let result = if kind == Kind::ClassDeclaration {
            self.factory.new_class_declaration(
                &mut self.nodes,
                modifiers,
                name,
                type_parameters,
                heritage_clauses.clone(),
                members,
            )
        } else {
            self.factory.new_class_expression(
                &mut self.nodes,
                modifiers,
                name,
                type_parameters,
                heritage_clauses.clone(),
                members,
            )
        };
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        if self.nodes[result]
            .flags
            .intersects(NodeFlags::JAVA_SCRIPT_FILE)
        {
            self.check_js_syntax(result);
            if let Some(heritage_clauses) = &heritage_clauses {
                for &clause in &heritage_clauses.nodes {
                    if self.nodes[clause].as_heritage_clause().token == Kind::ExtendsKeyword {
                        let types = self.nodes[clause]
                            .as_heritage_clause()
                            .types
                            .as_ref()
                            .map(|t| t.nodes.to_vec())
                            .unwrap_or_default();
                        for expr in types {
                            self.check_js_syntax(expr);
                        }
                    }
                }
            }
        }
        result
    }

    /// `func (p *Parser) parseNameOfClassDeclarationOrExpression() *ast.Node`
    fn parse_name_of_class_declaration_or_expression(&mut self) -> Option<NodeId> {
        // implements is a future reserved word so
        // 'class implements' might mean either
        // - class expression with omitted name, 'implements' starts heritage clause
        // - class with name 'implements'
        // 'isImplementsClause' helps to disambiguate between these two cases
        if self.is_binding_identifier() && !self.is_implements_clause() {
            let save_has_await_identifier = self.statement_has_await_identifier;
            let id = self.create_identifier(self.is_binding_identifier());
            self.statement_has_await_identifier = save_has_await_identifier;
            return Some(id);
        }
        None
    }

    /// `func (p *Parser) isImplementsClause() bool`
    fn is_implements_clause(&mut self) -> bool {
        self.token == Kind::ImplementsKeyword
            && self.look_ahead(Self::next_token_is_identifier_or_keyword)
    }

    /// `func (p *Parser) parseHeritageClauses(isInterface bool) *ast.NodeList`
    fn parse_heritage_clauses(&mut self, is_interface: bool) -> Option<NodeList> {
        // ClassTail[Yield,Await] : (Modified) See 14.5
        //      ClassHeritage[?Yield,?Await]opt { ClassBody[?Yield,?Await]opt }
        if self.is_heritage_clause() {
            return Some(self.parse_list(PC_HERITAGE_CLAUSES, move |p| {
                Some(p.parse_heritage_clause(is_interface))
            }));
        }
        None
    }

    /// `func (p *Parser) parseHeritageClause(isInterface bool) *ast.Node`
    fn parse_heritage_clause(&mut self, is_interface: bool) -> NodeId {
        let pos = self.node_pos();
        let kind = self.token;
        self.next_token();
        let types = if is_type_heritage_clause(is_interface, kind) {
            self.parse_delimited_list(
                PC_HERITAGE_CLAUSE_ELEMENT,
                Self::parse_type_heritage_clause_element_some,
                false,
            )
        } else {
            self.parse_delimited_list(
                PC_HERITAGE_CLAUSE_ELEMENT,
                Self::parse_expression_with_type_arguments_some,
                false,
            )
        };
        self.check_js_syntax(self.finish_node(
            self.factory
                .new_heritage_clause(&mut self.nodes, kind, types),
            pos,
        ))
    }

    /// `func (p *Parser) parseTypeHeritageClauseElement() *ast.HeritageClauseElement`
    fn parse_type_heritage_clause_element(&mut self) -> NodeId {
        let pos = self.node_pos();
        let expression_with_type_arguments = self.parse_expression_with_type_arguments();
        let e = self.nodes[expression_with_type_arguments].as_expression_with_type_arguments();
        let expression = e.expression;
        let type_arguments = e.type_arguments.clone();
        if !is_valid_heritage_type_reference_expression(expression, &self.nodes) {
            return expression_with_type_arguments;
        }
        let type_name = self.convert_entity_name_expression_to_entity_name(expression.unwrap());
        self.finish_node(
            self.factory
                .new_type_reference_node(&mut self.nodes, Some(type_name), type_arguments),
            pos,
        )
    }

    fn parse_type_heritage_clause_element_some(&mut self) -> Option<NodeId> {
        Some(self.parse_type_heritage_clause_element())
    }

    /// `func (p *Parser) convertEntityNameExpressionToEntityName(node)`
    fn convert_entity_name_expression_to_entity_name(&mut self, node: NodeId) -> NodeId {
        if is_identifier(&self.nodes[node]) {
            return node;
        }
        let (expression, name) = {
            let d = self.nodes[node].as_property_access_expression();
            (d.expression, d.name)
        };
        let left = self.convert_entity_name_expression_to_entity_name(expression.unwrap());
        let result = self
            .factory
            .new_qualified_name(&mut self.nodes, Some(left), name);
        self.finish_node_with_end(result, self.nodes[node].pos(), self.nodes[node].end())
    }

    /// `func (p *Parser) parseExpressionWithTypeArguments() *ast.Node`
    fn parse_expression_with_type_arguments(&mut self) -> NodeId {
        let pos = self.node_pos();
        let expression = self.parse_left_hand_side_expression_or_higher();
        if is_expression_with_type_arguments(&self.nodes[expression]) {
            return expression;
        }
        let type_arguments = self.parse_type_arguments();
        self.finish_node(
            self.factory.new_expression_with_type_arguments(
                &mut self.nodes,
                Some(expression),
                type_arguments,
            ),
            pos,
        )
    }

    fn parse_expression_with_type_arguments_some(&mut self) -> Option<NodeId> {
        Some(self.parse_expression_with_type_arguments())
    }

    /// `func (p *Parser) parseClassElement() *ast.Node`
    fn parse_class_element(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        if self.token == Kind::SemicolonToken {
            self.next_token();
            let result = self.finish_node(
                self.factory.new_semicolon_class_element(&mut self.nodes),
                pos,
            );
            self.with_jsdoc(result, jsdoc);
            return result;
        }
        let modifiers = self.parse_modifiers_ex(
            true, /*allowDecorators*/
            true, /*permitConstAsModifier*/
            true, /*stopOnStartOfClassStaticBlock*/
        );
        if self.token == Kind::StaticKeyword
            && self.look_ahead(Self::next_token_is_open_brace)
        {
            return self.parse_class_static_block_declaration(pos, jsdoc, modifiers);
        }
        if self.parse_contextual_modifier(Kind::GetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                Kind::GetAccessor,
                ParseFlags::NONE,
            );
        }
        if self.parse_contextual_modifier(Kind::SetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                Kind::SetAccessor,
                ParseFlags::NONE,
            );
        }
        if self.token == Kind::ConstructorKeyword || self.token == Kind::StringLiteral {
            if let Some(constructor_declaration) =
                self.try_parse_constructor_declaration(pos, jsdoc, modifiers.clone())
            {
                return constructor_declaration;
            }
        }
        if self.is_index_signature() {
            return self.check_js_syntax(self.parse_index_signature_declaration(
                pos,
                jsdoc,
                modifiers,
            ));
        }
        // It is very important that we check this *after* checking indexers because
        // the [ token can start an index signature or a computed property name
        if token_is_identifier_or_keyword(self.token)
            || self.token == Kind::StringLiteral
            || self.token == Kind::NumericLiteral
            || self.token == Kind::BigIntLiteral
            || self.token == Kind::AsteriskToken
            || self.token == Kind::OpenBracketToken
        {
            let is_ambient = modifiers
                .as_ref()
                .is_some_and(|m| core::some(&m.nodes, |n| is_declare_modifier(&self.nodes[*n])));
            if is_ambient {
                let modifiers = modifiers.unwrap();
                for &m in &modifiers.nodes {
                    self.nodes[m].flags |= NodeFlags::AMBIENT;
                }
                let save_context_flags = self.context_flags;
                self.set_context_flags(NodeFlags::AMBIENT, true);
                let result =
                    self.parse_property_or_method_declaration(pos, jsdoc, Some(modifiers));
                self.context_flags = save_context_flags;
                return result;
            } else {
                return self.parse_property_or_method_declaration(pos, jsdoc, modifiers);
            }
        }
        if let Some(modifiers) = modifiers {
            // treat this as a property declaration with a missing name.
            let pos2 = self.node_pos();
            self.parse_error_at(pos2, pos2, &diagnostics::Declaration_expected, &[]);
            let name = self.create_missing_identifier();
            return self.parse_property_declaration(
                pos,
                jsdoc,
                Some(modifiers),
                Some(name),
                None, /*questionToken*/
            );
        }
        // 'isClassMemberStart' should have hinted not to attempt parsing.
        panic!("Should not have attempted to parse class member declaration.")
    }

    fn parse_class_element_some(&mut self) -> Option<NodeId> {
        Some(self.parse_class_element())
    }

    /// `func (p *Parser) parseClassStaticBlockDeclaration(pos, jsdoc, modifiers)`
    fn parse_class_static_block_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        self.parse_expected_token(Kind::StaticKeyword);
        let body = self.parse_class_static_block_body();
        let result = self.finish_node(
            self.factory.new_class_static_block_declaration(
                &mut self.nodes,
                modifiers,
                Some(body),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseClassStaticBlockBody() *ast.Node`
    fn parse_class_static_block_body(&mut self) -> NodeId {
        let save_context_flags = self.context_flags;
        self.set_context_flags(NodeFlags::YIELD_CONTEXT, false);
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, true);
        let body = self.parse_block(
            false, /*ignoreMissingOpenBrace*/
            None,  /*diagnosticMessage*/
        );
        self.context_flags = save_context_flags;
        body
    }

    /// `func (p *Parser) tryParseConstructorDeclaration(pos, jsdoc, modifiers)`
    fn try_parse_constructor_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> Option<NodeId> {
        let state = self.mark();
        if self.token == Kind::ConstructorKeyword
            || self.token == Kind::StringLiteral
                && self.scanner.token_value() == b"constructor"
                && self.look_ahead(Self::next_token_is_open_paren)
        {
            self.next_token();
            let type_parameters = self.parse_type_parameters();
            let parameters = self.parse_parameters(ParseFlags::NONE);
            let return_type = self.parse_return_type(Kind::ColonToken, false /*isType*/);
            let body = self.parse_function_block_or_semicolon(
                ParseFlags::NONE,
                Some(&diagnostics::X_or_expected),
            );
            let result = self.finish_node(
                self.factory.new_constructor_declaration(
                    &mut self.nodes,
                    modifiers,
                    type_parameters,
                    Some(parameters),
                    return_type,
                    None, /*fullSignature*/
                    body,
                ),
                pos,
            );
            self.with_jsdoc(result, jsdoc);
            self.check_js_syntax(result);
            return Some(result);
        }
        self.rewind(state);
        None
    }

    /// `func (p *Parser) nextTokenIsOpenParen() bool`
    fn next_token_is_open_paren(&mut self) -> bool {
        self.next_token() == Kind::OpenParenToken
    }

    /// `func (p *Parser) parsePropertyOrMethodDeclaration(pos, jsdoc, modifiers)`
    fn parse_property_or_method_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let asterisk_token = self.parse_optional_token(Kind::AsteriskToken);
        let name = self.parse_property_name();
        // Note: this is not legal as per the grammar.  But we allow it in the parser and
        // report an error in the grammar checker.
        let question_token = self.parse_optional_token(Kind::QuestionToken);
        if asterisk_token.is_some()
            || self.token == Kind::OpenParenToken
            || self.token == Kind::LessThanToken
        {
            return self.parse_method_declaration(
                pos,
                jsdoc,
                modifiers,
                asterisk_token,
                Some(name),
                question_token,
                Some(&diagnostics::X_or_expected),
            );
        }
        self.parse_property_declaration(pos, jsdoc, modifiers, Some(name), question_token)
    }

    /// `func (p *Parser) parseMethodDeclaration(...)`
    fn parse_method_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
        asterisk_token: Option<NodeId>,
        name: Option<NodeId>,
        question_token: Option<NodeId>,
        diagnostic_message: Option<&'static Message>,
    ) -> NodeId {
        let signature_flags = if asterisk_token.is_some() {
            ParseFlags::YIELD
        } else {
            ParseFlags::NONE
        } | if modifier_list_has_async(modifiers.as_ref(), &self.nodes) {
            ParseFlags::AWAIT
        } else {
            ParseFlags::NONE
        };
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(signature_flags);
        let type_node = self.parse_return_type(Kind::ColonToken, false /*isType*/);
        let body = self.parse_function_block_or_semicolon(signature_flags, diagnostic_message);
        let result = self.finish_node(
            self.factory.new_method_declaration(
                &mut self.nodes,
                modifiers,
                asterisk_token,
                name,
                question_token,
                type_parameters,
                Some(parameters),
                type_node,
                None, /*fullSignature*/
                body,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) parsePropertyDeclaration(pos, jsdoc, modifiers, name, questionToken)`
    fn parse_property_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
        name: Option<NodeId>,
        question_token: Option<NodeId>,
    ) -> NodeId {
        let mut postfix_token = question_token;
        if postfix_token.is_none() && !self.has_preceding_line_break() {
            postfix_token = self.parse_optional_token(Kind::ExclamationToken);
        }
        let type_node = self.parse_type_annotation();
        let initializer = self.do_in_context(
            NodeFlags::YIELD_CONTEXT
                | NodeFlags::AWAIT_CONTEXT
                | NodeFlags::DISALLOW_IN_CONTEXT,
            false,
            Self::parse_initializer,
        );
        self.parse_semicolon_after_property_name(name.unwrap(), type_node, initializer);
        let result = self.finish_node(
            self.factory.new_property_declaration(
                &mut self.nodes,
                modifiers,
                name,
                postfix_token,
                type_node,
                initializer,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) parseSemicolonAfterPropertyName(name, typeNode, initializer)`
    fn parse_semicolon_after_property_name(
        &mut self,
        name: NodeId,
        type_node: Option<NodeId>,
        initializer: Option<NodeId>,
    ) {
        if self.token == Kind::AtToken && !self.has_preceding_line_break() {
            self.parse_error_at_current_token(&diagnostics::Decorators_must_precede_the_name_and_all_keywords_of_property_declarations, &[]);
            return;
        }
        if self.token == Kind::OpenParenToken {
            self.parse_error_at_current_token(
                &diagnostics::Cannot_start_a_function_call_in_a_type_annotation,
                &[],
            );
            self.next_token();
            return;
        }
        if type_node.is_some() && !self.can_parse_semicolon() {
            if initializer.is_some() {
                self.parse_error_at_current_token(
                    &diagnostics::X_0_expected,
                    &[scanner::token_to_string(Kind::SemicolonToken).to_string()],
                );
            } else {
                self.parse_error_at_current_token(
                    &diagnostics::Expected_for_property_initializer,
                    &[],
                );
            }
            return;
        }
        if self.try_parse_semicolon() {
            return;
        }
        if initializer.is_some() {
            self.parse_error_at_current_token(
                &diagnostics::X_0_expected,
                &[scanner::token_to_string(Kind::SemicolonToken).to_string()],
            );
            return;
        }
        self.parse_error_for_missing_semicolon_after(name);
    }

    /// `func (p *Parser) parseErrorForMissingSemicolonAfter(node)`
    fn parse_error_for_missing_semicolon_after(&mut self, node: NodeId) {
        // Tagged template literals are sometimes used in places where only simple strings are allowed, i.e.:
        //   module `M1` {
        //   ^^^^^^^^^^^ This block is parsed as a template literal like module`M1`.
        if self.nodes[node].kind == Kind::TaggedTemplateExpression {
            let template_loc = self.nodes[node].as_tagged_template_expression().template;
            let loc = self.nodes[template_loc.unwrap()].loc;
            let range = self.skip_range_trivia(loc);
            self.parse_error_at_range(range, &diagnostics::Module_declaration_names_may_only_use_or_quoted_strings, &[]);
            return;
        }
        // Otherwise, if this isn't a well-known keyword-like identifier, give the generic fallback message.
        let mut expression_text = String::new();
        if self.nodes[node].kind == Kind::Identifier {
            expression_text = self.nodes[node].text(&self.nodes).into_owned();
        }
        if expression_text.is_empty() {
            self.parse_error_at_current_token(
                &diagnostics::X_0_expected,
                &[scanner::token_to_string(Kind::SemicolonToken).to_string()],
            );
            return;
        }
        let pos = scanner::skip_trivia(self.source_text, self.nodes[node].pos());
        // Some known keywords are likely signs of syntax being used improperly.
        match expression_text.as_str() {
            "const" | "let" | "var" => {
                self.parse_error_at(
                    pos,
                    self.nodes[node].end(),
                    &diagnostics::Variable_declaration_not_allowed_at_this_location,
                    &[],
                );
                return;
            }
            "declare" => {
                // If a declared node failed to parse, it would have emitted a diagnostic already.
                return;
            }
            "interface" => {
                self.parse_error_for_invalid_name(
                    &diagnostics::Interface_name_cannot_be_0,
                    &diagnostics::Interface_must_be_given_a_name,
                    Kind::OpenBraceToken,
                );
                return;
            }
            "is" => {
                self.parse_error_at(
                    pos,
                    self.scanner.token_start() as i32,
                    &diagnostics::A_type_predicate_is_only_allowed_in_return_type_position_for_functions_and_methods,
                    &[],
                );
                return;
            }
            "module" | "namespace" => {
                self.parse_error_for_invalid_name(
                    &diagnostics::Namespace_name_cannot_be_0,
                    &diagnostics::Namespace_must_be_given_a_name,
                    Kind::OpenBraceToken,
                );
                return;
            }
            "type" => {
                self.parse_error_for_invalid_name(
                    &diagnostics::Type_alias_name_cannot_be_0,
                    &diagnostics::Type_alias_must_be_given_a_name,
                    Kind::EqualsToken,
                );
                return;
            }
            _ => {}
        }
        // The user alternatively might have misspelled or forgotten to add a space after a common keyword.
        let suggestion = core::get_spelling_suggestion_for_strings(
            &expression_text,
            VIABLE_KEYWORD_SUGGESTIONS.iter().copied(),
        )
        .map(|s| s.to_string())
        .or_else(|| {
            let s = get_space_suggestion(&expression_text);
            if s.is_empty() { None } else { Some(s) }
        });
        if let Some(suggestion) = suggestion {
            self.parse_error_at(
                pos,
                self.nodes[node].end(),
                &diagnostics::Unknown_keyword_or_identifier_Did_you_mean_0,
                &[suggestion],
            );
            return;
        }
        // Unknown tokens are handled with their own errors in the scanner
        if self.token == Kind::Unknown {
            return;
        }
        // Otherwise, we know this some kind of unknown word, not just a missing expected semicolon.
        self.parse_error_at(
            pos,
            self.nodes[node].end(),
            &diagnostics::Unexpected_keyword_or_identifier,
            &[],
        );
    }

    /// `func (p *Parser) parseErrorForInvalidName(nameDiagnostic, blankDiagnostic, tokenIfBlankName)`
    fn parse_error_for_invalid_name(
        &mut self,
        name_diagnostic: &'static Message,
        blank_diagnostic: &'static Message,
        token_if_blank_name: Kind,
    ) {
        if self.token == token_if_blank_name {
            self.parse_error_at_current_token(blank_diagnostic, &[]);
        } else {
            let value = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
            self.parse_error_at_current_token(name_diagnostic, &[value]);
        }
    }

    /// `func (p *Parser) parseInterfaceDeclaration(pos, jsdoc, modifiers)`
    fn parse_interface_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        self.parse_expected(Kind::InterfaceKeyword);
        let name = self.parse_identifier();
        let type_parameters = self.parse_type_parameters();
        let heritage_clauses = self.parse_heritage_clauses(true /*isInterface*/);
        let members = self.parse_object_type_members();
        let result = self.finish_node(
            self.factory.new_interface_declaration(
                &mut self.nodes,
                modifiers,
                Some(name),
                type_parameters,
                heritage_clauses,
                Some(members),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) parseTypeAliasDeclaration(pos, jsdoc, modifiers)`
    fn parse_type_alias_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        self.parse_expected(Kind::TypeKeyword);
        if self.has_preceding_line_break() {
            self.parse_error_at_current_token(&diagnostics::Line_break_not_permitted_here, &[]);
        }
        let name = self.parse_identifier();
        let type_parameters = self.parse_type_parameters();
        self.parse_expected(Kind::EqualsToken);
        let type_node = if self.token == Kind::IntrinsicKeyword
            && self.look_ahead(Self::next_is_not_dot)
        {
            self.parse_keyword_type_node()
        } else {
            self.parse_type()
        };
        self.parse_semicolon();
        let result = self.finish_node(
            self.factory.new_type_alias_declaration(
                &mut self.nodes,
                modifiers,
                Some(name),
                type_parameters,
                Some(type_node),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) nextIsNotDot() bool`
    fn next_is_not_dot(&mut self) -> bool {
        self.next_token() != Kind::DotToken
    }

    // In an ambient declaration, the grammar only allows integer literals as initializers.
    // In a non-ambient declaration, the grammar allows uninitialized members only in a
    // ConstantEnumMemberSection, which starts at the beginning of an enum declaration
    // or any time an integer literal initializer is encountered.
    /// `func (p *Parser) parseEnumMember() *ast.Node`
    fn parse_enum_member(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let name = self.parse_property_name();
        let initializer = self.do_in_context(
            NodeFlags::DISALLOW_IN_CONTEXT,
            false,
            Self::parse_initializer,
        );
        let result = self.finish_node(
            self.factory
                .new_enum_member(&mut self.nodes, Some(name), initializer),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    fn parse_enum_member_some(&mut self) -> Option<NodeId> {
        Some(self.parse_enum_member())
    }

    /// `func (p *Parser) parseEnumDeclaration(pos, jsdoc, modifiers)`
    fn parse_enum_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let save_has_await_identifier = self.statement_has_await_identifier;
        self.parse_expected(Kind::EnumKeyword);
        let name = self.parse_identifier();
        let members: Option<NodeList>;
        if self.parse_expected(Kind::OpenBraceToken) {
            let save_context_flags = self.context_flags;
            self.set_context_flags(NodeFlags::YIELD_CONTEXT | NodeFlags::AWAIT_CONTEXT, false);
            members = self.parse_delimited_list(
                PC_ENUM_MEMBERS,
                Self::parse_enum_member_some,
                false,
            );
            self.context_flags = save_context_flags;
            self.parse_expected(Kind::CloseBraceToken);
        } else {
            members = Some(self.create_missing_list());
        }
        let result = self.finish_node(
            self.factory.new_enum_declaration(
                &mut self.nodes,
                modifiers,
                Some(name),
                members,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        self.statement_has_await_identifier = save_has_await_identifier;
        result
    }

    /// `func (p *Parser) parseModuleDeclaration(pos, jsdoc, modifiers)`
    fn parse_module_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let mut keyword = Kind::ModuleKeyword;
        if self.token == Kind::GlobalKeyword {
            // global augmentation
            return self.parse_ambient_external_module_declaration(pos, jsdoc, modifiers);
        } else if self.parse_optional(Kind::NamespaceKeyword) {
            keyword = Kind::NamespaceKeyword;
        } else {
            self.parse_expected(Kind::ModuleKeyword);
            if self.token == Kind::StringLiteral {
                return self.parse_ambient_external_module_declaration(pos, jsdoc, modifiers);
            }
        }
        self.parse_module_or_namespace_declaration(
            pos, jsdoc, modifiers, false, /*nested*/
            keyword,
        )
    }

    /// `func (p *Parser) parseAmbientExternalModuleDeclaration(pos, jsdoc, modifiers)`
    fn parse_ambient_external_module_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let name: NodeId;
        let mut keyword = Kind::ModuleKeyword;
        let save_has_await_identifier = self.statement_has_await_identifier;
        if self.token == Kind::GlobalKeyword {
            // parse 'global' as name of global scope augmentation
            name = self.parse_identifier();
            keyword = Kind::GlobalKeyword;
        } else {
            // parse string literal
            name = self.parse_literal_expression();
        }
        let mut attributes = None;
        if keyword == Kind::ModuleKeyword && self.parse_optional(Kind::WithKeyword) {
            attributes = Some(self.parse_type_literal());
        }
        let mut body = None;
        if self.token == Kind::OpenBraceToken {
            body = Some(self.parse_module_block());
        } else {
            self.parse_semicolon();
        }
        let result = self.finish_node(
            self.factory.new_module_declaration(
                &mut self.nodes,
                modifiers,
                keyword,
                Some(name),
                attributes,
                body,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.statement_has_await_identifier = save_has_await_identifier;
        result
    }

    /// `func (p *Parser) parseModuleBlock() *ast.Node`
    fn parse_module_block(&mut self) -> NodeId {
        let pos = self.node_pos();
        let statements: Option<NodeList>;
        if self.parse_expected(Kind::OpenBraceToken) {
            statements =
                Some(self.parse_list(PC_BLOCK_STATEMENTS, Self::parse_statement_some));
            self.parse_expected(Kind::CloseBraceToken);
        } else {
            statements = Some(self.create_missing_list());
        }
        self.finish_node(
            self.factory
                .new_module_block(&mut self.nodes, statements),
            pos,
        )
    }

    /// `func (p *Parser) parseModuleOrNamespaceDeclaration(pos, jsdoc, modifiers, nested, keyword)`
    fn parse_module_or_namespace_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
        nested: bool,
        keyword: Kind,
    ) -> NodeId {
        let save_has_await_identifier = self.statement_has_await_identifier;
        let name = if nested {
            self.parse_identifier_name()
        } else {
            self.parse_identifier()
        };
        let body: NodeId;
        if self.parse_optional(Kind::DotToken) {
            let implicit_pos = self.node_pos();
            let implicit_export = self.factory.new_token(&mut self.nodes, Kind::ExportKeyword);
            self.nodes[implicit_export].loc = TextRange::new(implicit_pos, implicit_pos);
            self.nodes[implicit_export].flags = NodeFlags::REPARSED;
            let implicit_modifiers = self.new_modifier_list(
                self.nodes[implicit_export].loc,
                vec![implicit_export],
            );
            let nested_pos = self.node_pos();
            body = self.parse_module_or_namespace_declaration(
                nested_pos,
                0, /*jsdoc*/
                Some(implicit_modifiers),
                true, /*nested*/
                keyword,
            );
        } else {
            body = self.parse_module_block();
        }
        let result = self.finish_node(
            self.factory.new_module_declaration(
                &mut self.nodes,
                modifiers,
                keyword,
                Some(name),
                None,
                Some(body),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        self.statement_has_await_identifier = save_has_await_identifier;
        result
    }
}

impl<'a> Parser<'a> {
    /// `func (p *Parser) parseImportDeclarationOrImportEqualsDeclaration(pos, jsdoc, modifiers)`
    fn parse_import_declaration_or_import_equals_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        self.parse_expected(Kind::ImportKeyword);
        let after_import_pos = self.node_pos();
        // We don't parse the identifier here in await context, instead we will report a grammar error in the checker.
        let save_has_await_identifier = self.statement_has_await_identifier;
        let phase_modifier_candidate = self.current_import_phase_modifier();
        let mut identifier: Option<NodeId> = None;
        if self.is_identifier() {
            identifier = Some(self.parse_identifier());
        }
        let mut phase_modifier = Kind::Unknown;
        if let Some(id) = identifier
            && self.nodes[id].text(&self.nodes) == "type"
            && (self.token != Kind::FromKeyword
                || self.is_identifier()
                    && self.look_ahead(Self::next_token_is_from_keyword_or_equals_token))
            && (self.is_identifier()
                || self.token_after_import_definitely_produces_import_declaration())
        {
            phase_modifier = Kind::TypeKeyword;
            identifier = None;
            if self.is_identifier() {
                identifier = Some(self.parse_identifier());
            }
        } else if identifier.is_some()
            && phase_modifier_candidate != Kind::Unknown
            && self.should_parse_import_phase_modifier()
        {
            phase_modifier = phase_modifier_candidate;
            identifier = None;
            if self.is_identifier() {
                identifier = Some(self.parse_identifier());
            }
        }
        if let Some(id) = identifier
            && self.token_after_imported_identifier_allows_import_equals_declaration()
            && phase_modifier != Kind::DeferKeyword
            && phase_modifier != Kind::SourceKeyword
        {
            let import_equals = self.check_js_syntax(self.parse_import_equals_declaration(
                pos,
                jsdoc,
                modifiers,
                Some(id),
                phase_modifier == Kind::TypeKeyword,
            ));
            // Import= declaration is always parsed in an Await context, no need to reparse
            self.statement_has_await_identifier = save_has_await_identifier;
            return import_equals;
        }
        let import_clause = self.try_parse_import_clause(
            identifier,
            after_import_pos,
            phase_modifier,
            false, /*skipJSDocLeadingAsterisks*/
        );
        // import clause is always parsed in an Await context
        self.statement_has_await_identifier = save_has_await_identifier;
        let module_specifier = self.parse_module_specifier();
        let attributes = self.try_parse_import_attributes();
        self.parse_semicolon();
        let result = self.finish_node(
            self.factory.new_import_declaration(
                &mut self.nodes,
                modifiers,
                import_clause,
                module_specifier,
                attributes,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) nextTokenIsFromKeywordOrEqualsToken() bool`
    fn next_token_is_from_keyword_or_equals_token(&mut self) -> bool {
        self.next_token();
        self.token == Kind::FromKeyword || self.token == Kind::EqualsToken
    }

    /// `func (p *Parser) shouldParseImportPhaseModifier() bool`
    fn should_parse_import_phase_modifier(&mut self) -> bool {
        match self.token {
            Kind::CommaToken | Kind::EqualsToken => return false,
            Kind::FromKeyword => {
                if self.look_ahead(Self::next_token_is_token_string_literal) {
                    return false;
                }
            }
            _ => {}
        }
        true
    }

    /// `func (p *Parser) currentImportPhaseModifier() ast.Kind`
    fn current_import_phase_modifier(&mut self) -> Kind {
        match self.scanner.token_text() {
            "defer" => Kind::DeferKeyword,
            "source" => Kind::SourceKeyword,
            _ => Kind::Unknown,
        }
    }

    /// `func (p *Parser) tokenAfterImportDefinitelyProducesImportDeclaration() bool`
    fn token_after_import_definitely_produces_import_declaration(&mut self) -> bool {
        self.token == Kind::AsteriskToken || self.token == Kind::OpenBraceToken
    }

    /// `func (p *Parser) tokenAfterImportedIdentifierAllowsImportEqualsDeclaration() bool`
    fn token_after_imported_identifier_allows_import_equals_declaration(&mut self) -> bool {
        !matches!(self.token, Kind::CommaToken | Kind::FromKeyword)
    }

    /// `func (p *Parser) parseImportEqualsDeclaration(...)`
    fn parse_import_equals_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
        identifier: Option<NodeId>,
        is_type_only: bool,
    ) -> NodeId {
        self.parse_expected(Kind::EqualsToken);
        let module_reference = self.parse_module_reference();
        self.parse_semicolon();
        let result = self.finish_node(
            self.factory.new_import_equals_declaration(
                &mut self.nodes,
                modifiers,
                is_type_only,
                identifier,
                Some(module_reference),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseModuleReference() *ast.Node`
    fn parse_module_reference(&mut self) -> NodeId {
        if self.token == Kind::RequireKeyword
            && self.look_ahead(Self::next_token_is_open_paren)
        {
            return self.parse_external_module_reference();
        }
        self.parse_entity_name(
            false, /*allowReservedWords*/
            false, /*allowPrivateName*/
            None,  /*diagnosticMessage*/
        )
        .expect("parse_entity_name always returns Some")
    }

    /// `func (p *Parser) parseExternalModuleReference() *ast.Node`
    fn parse_external_module_reference(&mut self) -> NodeId {
        let save_has_await_identifier = self.statement_has_await_identifier;
        let pos = self.node_pos();
        self.parse_expected(Kind::RequireKeyword);
        self.parse_expected(Kind::OpenParenToken);
        let expression = self.parse_module_specifier();
        self.parse_expected(Kind::CloseParenToken);
        let result = self.finish_node(
            self.factory
                .new_external_module_reference(&mut self.nodes, expression),
            pos,
        );
        self.statement_has_await_identifier = save_has_await_identifier;
        result
    }

    /// `func (p *Parser) parseModuleSpecifier() *ast.Expression`
    fn parse_module_specifier(&mut self) -> Option<NodeId> {
        if self.token == Kind::StringLiteral {
            return Some(self.parse_literal_expression());
        }
        // We allow arbitrary expressions here, even though the grammar only allows string
        // literals.  We check to ensure that it is only a string literal later in the grammar
        // check pass.
        Some(self.parse_expression())
    }

    /// `func (p *Parser) tryParseImportClause(identifier, pos, phaseModifier, skipJSDocLeadingAsterisks)`
    pub fn try_parse_import_clause(
        &mut self,
        identifier: Option<NodeId>,
        pos: i32,
        phase_modifier: Kind,
        skip_jsdoc_leading_asterisks: bool,
    ) -> Option<NodeId> {
        // ImportDeclaration:
        //  import ImportClause from ModuleSpecifier ;
        //  import ModuleSpecifier;
        if identifier.is_some()
            || self.token == Kind::AsteriskToken
            || self.token == Kind::OpenBraceToken
        {
            let import_clause = self.parse_import_clause(
                identifier,
                pos,
                phase_modifier,
                skip_jsdoc_leading_asterisks,
            );
            self.parse_expected(Kind::FromKeyword);
            return Some(import_clause);
        }
        if phase_modifier == Kind::DeferKeyword || phase_modifier == Kind::SourceKeyword {
            let clause = self.factory.new_import_clause(
                &mut self.nodes,
                phase_modifier,
                None, /*name*/
                None, /*namedBindings*/
            );
            return Some(self.finish_node(clause, pos));
        }
        None
    }

    /// `func (p *Parser) parseImportClause(identifier, pos, phaseModifier, skipJSDocLeadingAsterisks)`
    pub fn parse_import_clause(
        &mut self,
        identifier: Option<NodeId>,
        pos: i32,
        phase_modifier: Kind,
        skip_jsdoc_leading_asterisks: bool,
    ) -> NodeId {
        // ImportClause:
        //  ImportedDefaultBinding
        //  NameSpaceImport
        //  NamedImports
        //  ImportedDefaultBinding, NameSpaceImport
        //  ImportedDefaultBinding, NamedImports
        // If there was no default import or if there is comma token after default import
        // parse namespace or named imports
        let mut named_bindings = None;
        let save_has_await_identifier = self.statement_has_await_identifier;
        if identifier.is_none() || self.parse_optional(Kind::CommaToken) {
            if skip_jsdoc_leading_asterisks {
                self.scanner.set_skip_jsdoc_leading_asterisks(true);
            }
            if self.token == Kind::AsteriskToken {
                named_bindings = Some(self.parse_namespace_import());
            } else {
                named_bindings = Some(self.parse_named_imports());
            }
            if skip_jsdoc_leading_asterisks {
                self.scanner.set_skip_jsdoc_leading_asterisks(false);
            }
        }
        let result = self.finish_node(
            self.factory.new_import_clause(
                &mut self.nodes,
                phase_modifier,
                identifier,
                named_bindings,
            ),
            pos,
        );
        self.statement_has_await_identifier = save_has_await_identifier;
        result
    }

    /// `func (p *Parser) parseNamespaceImport() *ast.Node`
    fn parse_namespace_import(&mut self) -> NodeId {
        // NameSpaceImport:
        //  * as ImportedBinding
        let pos = self.node_pos();
        self.parse_expected(Kind::AsteriskToken);
        self.parse_expected(Kind::AsKeyword);
        let name = self.parse_identifier();
        self.finish_node(
            self.factory
                .new_namespace_import(&mut self.nodes, Some(name)),
            pos,
        )
    }

    /// `func (p *Parser) parseNamedImports() *ast.Node`
    fn parse_named_imports(&mut self) -> NodeId {
        let pos = self.node_pos();
        // NamedImports:
        //  { }
        //  { ImportsList }
        //  { ImportsList, }
        let imports = self.parse_bracketed_list(
            PC_IMPORT_OR_EXPORT_SPECIFIERS,
            Self::parse_import_specifier_some,
            Kind::OpenBraceToken,
            Kind::CloseBraceToken,
        );
        self.finish_node(
            self.factory
                .new_named_imports(&mut self.nodes, imports),
            pos,
        )
    }

    /// `func (p *Parser) parseImportSpecifier() *ast.Node`
    fn parse_import_specifier(&mut self) -> NodeId {
        let pos = self.node_pos();
        let (is_type_only, property_name, name) =
            self.parse_import_or_export_specifier(Kind::ImportSpecifier);
        let identifier_name = if self.nodes[name].kind == Kind::Identifier {
            name
        } else {
            let loc = self.nodes[name].loc;
            let range = self.skip_range_trivia(loc);
            self.parse_error_at_range(range, &diagnostics::Identifier_expected, &[]);
            let identifier_name = self.new_identifier("");
            self.finish_node(identifier_name, self.nodes[name].pos())
        };
        let result = self.finish_node(
            self.factory.new_import_specifier(
                &mut self.nodes,
                is_type_only,
                property_name,
                Some(identifier_name),
            ),
            pos,
        );
        self.check_js_syntax(result)
    }

    fn parse_import_specifier_some(&mut self) -> Option<NodeId> {
        Some(self.parse_import_specifier())
    }

    /// `func (p *Parser) parseImportOrExportSpecifier(kind) (isTypeOnly, propertyName, name)`
    fn parse_import_or_export_specifier(
        &mut self,
        kind: Kind,
    ) -> (bool, Option<NodeId>, NodeId) {
        // ImportSpecifier:
        //   BindingIdentifier
        //   ModuleExportName as BindingIdentifier
        // ExportSpecifier:
        //   ModuleExportName
        //   ModuleExportName as ModuleExportName
        let mut can_parse_as_keyword = true;
        let disallow_keywords = kind == Kind::ImportSpecifier;
        let mut is_type_only = false;
        let mut property_name: Option<NodeId> = None;
        let (mut name, mut name_ok) = self.parse_module_export_name(disallow_keywords);
        if self.nodes[name].kind == Kind::Identifier && self.nodes[name].text(&self.nodes) == "type" {
            // If the first token of an import specifier is 'type', there are a lot of possibilities,
            // especially if we see 'as' afterwards:
            //
            // import { type } from "mod";          - isTypeOnly: false,   name: type
            // import { type as } from "mod";       - isTypeOnly: true,    name: as
            // import { type as as } from "mod";    - isTypeOnly: false,   name: as,    propertyName: type
            // import { type as as as } from "mod"; - isTypeOnly: true,    name: as,    propertyName: as
            if self.token == Kind::AsKeyword {
                // { type as ...? }
                let first_as = self.parse_identifier_name();
                if self.token == Kind::AsKeyword {
                    // { type as as ...? }
                    let second_as = self.parse_identifier_name();
                    if self.can_parse_module_export_name() {
                        // { type as as something }
                        // { type as as "something" }
                        is_type_only = true;
                        property_name = Some(first_as);
                        (name, name_ok) = self.parse_module_export_name(disallow_keywords);
                        can_parse_as_keyword = false;
                    } else {
                        // { type as as }
                        property_name = Some(name);
                        name = second_as;
                        can_parse_as_keyword = false;
                    }
                } else if self.can_parse_module_export_name() {
                    // { type as something }
                    // { type as "something" }
                    property_name = Some(name);
                    can_parse_as_keyword = false;
                    (name, name_ok) = self.parse_module_export_name(disallow_keywords);
                } else {
                    // { type as }
                    is_type_only = true;
                    name = first_as;
                }
            } else if self.can_parse_module_export_name() {
                // { type something ...? }
                // { type "something" ...? }
                is_type_only = true;
                (name, name_ok) = self.parse_module_export_name(disallow_keywords);
            }
        }
        if can_parse_as_keyword && self.token == Kind::AsKeyword {
            property_name = Some(name);
            self.parse_expected(Kind::AsKeyword);
            (name, name_ok) = self.parse_module_export_name(disallow_keywords);
        }

        if !name_ok {
            let loc = self.nodes[name].loc;
            let range = self.skip_range_trivia(loc);
            self.parse_error_at_range(range, &diagnostics::Identifier_expected, &[]);
        }

        (is_type_only, property_name, name)
    }

    /// `func (p *Parser) canParseModuleExportName() bool`
    fn can_parse_module_export_name(&mut self) -> bool {
        token_is_identifier_or_keyword(self.token) || self.token == Kind::StringLiteral
    }

    /// `func (p *Parser) parseModuleExportName(disallowKeywords) (node, nameOk)`
    fn parse_module_export_name(&mut self, disallow_keywords: bool) -> (NodeId, bool) {
        let mut name_ok = true;
        if self.token == Kind::StringLiteral {
            return (self.parse_literal_expression(), name_ok);
        }
        if disallow_keywords && is_keyword(self.token) && !self.is_identifier() {
            name_ok = false;
        }
        (self.parse_identifier_name(), name_ok)
    }

    /// `func (p *Parser) tryParseImportAttributes() *ast.Node`
    fn try_parse_import_attributes(&mut self) -> Option<NodeId> {
        if self.token == Kind::WithKeyword
            || (self.token == Kind::AssertKeyword && !self.has_preceding_line_break())
        {
            if self.token == Kind::AssertKeyword {
                self.parse_error_at_current_token(&diagnostics::Import_assertions_have_been_replaced_by_import_attributes_Use_with_instead_of_assert, &[]);
            }
            return Some(self.parse_import_attributes(self.token, false /*skipKeyword*/));
        }
        None
    }

    /// `func (p *Parser) parseExportAssignment(pos, jsdoc, modifiers)`
    fn parse_export_assignment(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let save_context_flags = self.context_flags;
        let save_has_await_identifier = self.statement_has_await_identifier;
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, true);
        let mut is_export_equals = false;
        if self.parse_optional(Kind::EqualsToken) {
            is_export_equals = true;
        } else {
            self.parse_expected(Kind::DefaultKeyword);
        }
        let expression = self.parse_assignment_expression_or_higher();
        self.parse_semicolon();
        self.context_flags = save_context_flags;
        self.statement_has_await_identifier = save_has_await_identifier;
        let result = self.finish_node(
            self.factory.new_export_assignment(
                &mut self.nodes,
                modifiers,
                is_export_equals,
                None, /*typeNode*/
                Some(expression),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) parseNamespaceExportDeclaration(pos, jsdoc, modifiers)`
    fn parse_namespace_export_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        self.parse_expected(Kind::AsKeyword);
        self.parse_expected(Kind::NamespaceKeyword);
        let save_has_await_identifier = self.statement_has_await_identifier;
        let name = self.parse_identifier();
        self.statement_has_await_identifier = save_has_await_identifier;
        self.parse_semicolon();
        // NamespaceExportDeclaration nodes cannot have decorators or modifiers, we attach them here so we can report them in the grammar checker
        let result = self.finish_node(
            self.factory.new_namespace_export_declaration(
                &mut self.nodes,
                modifiers,
                Some(name),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseExportDeclaration(pos, jsdoc, modifiers)`
    fn parse_export_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let save_context_flags = self.context_flags;
        let save_has_await_identifier = self.statement_has_await_identifier;
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, true);
        let mut export_clause = None;
        let mut module_specifier = None;
        let mut attributes = None;
        let is_type_only = self.parse_optional(Kind::TypeKeyword);
        let namespace_export_pos = self.node_pos();
        if self.parse_optional(Kind::AsteriskToken) {
            if self.parse_optional(Kind::AsKeyword) {
                export_clause = Some(self.parse_namespace_export(namespace_export_pos));
            }
            self.parse_expected(Kind::FromKeyword);
            module_specifier = self.parse_module_specifier();
        } else {
            export_clause = Some(self.parse_named_exports());
            // It is not uncommon to accidentally omit the 'from' keyword. Additionally, in editing scenarios,
            // the 'from' keyword can be parsed as a named export when the export clause is unterminated (i.e. `export { from "moduleName";`)
            // If we don't have a 'from' keyword, see if we have a string literal such that ASI won't take effect.
            if self.token == Kind::FromKeyword
                || (self.token == Kind::StringLiteral && !self.has_preceding_line_break())
            {
                self.parse_expected(Kind::FromKeyword);
                module_specifier = self.parse_module_specifier();
            }
        }
        if module_specifier.is_some()
            && (self.token == Kind::WithKeyword || self.token == Kind::AssertKeyword)
            && !self.has_preceding_line_break()
        {
            if self.token == Kind::AssertKeyword {
                self.parse_error_at_current_token(&diagnostics::Import_assertions_have_been_replaced_by_import_attributes_Use_with_instead_of_assert, &[]);
            }
            attributes = Some(self.parse_import_attributes(self.token, false /*skipKeyword*/));
        }
        self.parse_semicolon();
        self.context_flags = save_context_flags;
        self.statement_has_await_identifier = save_has_await_identifier;
        let result = self.finish_node(
            self.factory.new_export_declaration(
                &mut self.nodes,
                modifiers,
                is_type_only,
                export_clause,
                module_specifier,
                attributes,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) parseNamespaceExport(pos) *ast.Node`
    fn parse_namespace_export(&mut self, pos: i32) -> NodeId {
        let (export_name, _) = self.parse_module_export_name(false /*disallowKeywords*/);
        self.finish_node(
            self.factory
                .new_namespace_export(&mut self.nodes, Some(export_name)),
            pos,
        )
    }

    /// `func (p *Parser) parseNamedExports() *ast.Node`
    fn parse_named_exports(&mut self) -> NodeId {
        let pos = self.node_pos();
        // NamedImports:
        //  { }
        //  { ImportsList }
        //  { ImportsList, }
        let exports = self.parse_bracketed_list(
            PC_IMPORT_OR_EXPORT_SPECIFIERS,
            Self::parse_export_specifier_some,
            Kind::OpenBraceToken,
            Kind::CloseBraceToken,
        );
        self.finish_node(
            self.factory
                .new_named_exports(&mut self.nodes, exports),
            pos,
        )
    }

    /// `func (p *Parser) parseExportSpecifier() *ast.Node`
    fn parse_export_specifier(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let (is_type_only, property_name, name) =
            self.parse_import_or_export_specifier(Kind::ExportSpecifier);
        let result = self.finish_node(
            self.factory.new_export_specifier(
                &mut self.nodes,
                is_type_only,
                property_name,
                Some(name),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    fn parse_export_specifier_some(&mut self) -> Option<NodeId> {
        Some(self.parse_export_specifier())
    }
}

// ---------------------------------------------------------------------------
// Types (Go: `parseType` through `skipParameterStart`)
// ---------------------------------------------------------------------------

impl<'a> Parser<'a> {
    /// `func (p *Parser) parseType() *ast.TypeNode`
    pub fn parse_type(&mut self) -> NodeId {
        let save_context_flags = self.context_flags;
        self.set_context_flags(NodeFlags::TYPE_EXCLUDES_FLAGS, false);
        let type_node: NodeId;
        if self.is_start_of_function_type_or_constructor_type() {
            type_node = self.parse_function_or_constructor_type();
        } else {
            let pos = self.node_pos();
            let mut tn = self.parse_union_type_or_higher();
            if !self.in_disallow_conditional_types_context()
                && !self.has_preceding_line_break()
                && self.parse_optional(Kind::ExtendsKeyword)
            {
                // The type following 'extends' is not permitted to be another conditional type
                let extends_type = self.do_in_context(
                    NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                    true,
                    Self::parse_type,
                );
                self.parse_expected(Kind::QuestionToken);
                let true_type = self.do_in_context(
                    NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                    false,
                    Self::parse_type,
                );
                self.parse_expected(Kind::ColonToken);
                let false_type = self.do_in_context(
                    NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                    false,
                    Self::parse_type,
                );
                let conditional_type = self.factory.new_conditional_type_node(
                    &mut self.nodes,
                    Some(tn),
                    Some(extends_type),
                    Some(true_type),
                    Some(false_type),
                );
                tn = self.finish_node(conditional_type, pos);
            }
            type_node = tn;
        }
        self.context_flags = save_context_flags;
        type_node
    }

    /// `func (p *Parser) parseUnionTypeOrHigher() *ast.TypeNode`
    fn parse_union_type_or_higher(&mut self) -> NodeId {
        self.parse_union_or_intersection_type(
            Kind::BarToken,
            Self::parse_intersection_type_or_higher,
        )
    }

    /// `func (p *Parser) parseIntersectionTypeOrHigher() *ast.TypeNode`
    fn parse_intersection_type_or_higher(&mut self) -> NodeId {
        self.parse_union_or_intersection_type(
            Kind::AmpersandToken,
            Self::parse_type_operator_or_higher,
        )
    }

    /// `func (p *Parser) parseUnionOrIntersectionType(operator, parseConstituentType)`
    fn parse_union_or_intersection_type(
        &mut self,
        operator: Kind,
        parse_constituent_type: fn(&mut Self) -> NodeId,
    ) -> NodeId {
        let pos = self.node_pos();
        let is_union_type = operator == Kind::BarToken;
        let has_leading_operator = self.parse_optional(operator);
        let mut type_node = if has_leading_operator {
            self.parse_function_or_constructor_type_to_error(
                is_union_type,
                parse_constituent_type,
            )
        } else {
            parse_constituent_type(self)
        };
        if self.token == operator || has_leading_operator {
            let mut types = vec![type_node];
            while self.parse_optional(operator) {
                types.push(self.parse_function_or_constructor_type_to_error(
                    is_union_type,
                    parse_constituent_type,
                ));
            }
            let list =
                self.new_node_list(TextRange::new(pos, self.node_pos()), types);
            type_node = self.create_union_or_intersection_type_node(operator, Some(list));
            self.finish_node(type_node, pos);
        }
        type_node
    }

    /// `func (p *Parser) createUnionOrIntersectionTypeNode(operator, types)`
    fn create_union_or_intersection_type_node(
        &mut self,
        operator: Kind,
        types: Option<NodeList>,
    ) -> NodeId {
        match operator {
            Kind::BarToken => {
                self.factory
                    .new_union_type_node(&mut self.nodes, types)
            }
            Kind::AmpersandToken => {
                self.factory
                    .new_intersection_type_node(&mut self.nodes, types)
            }
            _ => panic!("Unhandled case in createUnionOrIntersectionType"),
        }
    }

    /// `func (p *Parser) parseTypeOperatorOrHigher() *ast.TypeNode`
    fn parse_type_operator_or_higher(&mut self) -> NodeId {
        let operator = self.token;
        match operator {
            Kind::KeyOfKeyword | Kind::UniqueKeyword | Kind::ReadonlyKeyword => {
                return self.parse_type_operator(operator);
            }
            Kind::InferKeyword => return self.parse_infer_type(),
            _ => {}
        }
        self.do_in_context(
            NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
            false,
            Self::parse_postfix_type_or_higher,
        )
    }

    /// `func (p *Parser) parseTypeOperator(operator) *ast.Node`
    fn parse_type_operator(&mut self, operator: Kind) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(operator);
        let type_node = self.parse_type_operator_or_higher();
        self.finish_node(
            self.factory
                .new_type_operator_node(&mut self.nodes, operator, Some(type_node)),
            pos,
        )
    }

    /// `func (p *Parser) parseInferType() *ast.Node`
    fn parse_infer_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::InferKeyword);
        let tp = self.parse_type_parameter_of_infer_type();
        self.finish_node(
            self.factory
                .new_infer_type_node(&mut self.nodes, Some(tp)),
            pos,
        )
    }

    /// `func (p *Parser) parseTypeParameterOfInferType() *ast.Node`
    fn parse_type_parameter_of_infer_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        let name = self.parse_identifier();
        let constraint = self.try_parse_constraint_of_infer_type();
        self.finish_node(
            self.factory.new_type_parameter_declaration(
                &mut self.nodes,
                None, /*modifiers*/
                Some(name),
                constraint,
                None, /*expression*/
                None, /*defaultType*/
            ),
            pos,
        )
    }

    /// `func (p *Parser) tryParseConstraintOfInferType() *ast.Node`
    fn try_parse_constraint_of_infer_type(&mut self) -> Option<NodeId> {
        let state = self.mark();
        if self.parse_optional(Kind::ExtendsKeyword) {
            let constraint = self.do_in_context(
                NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                true,
                Self::parse_type,
            );
            if self.in_disallow_conditional_types_context()
                || self.token != Kind::QuestionToken
            {
                return Some(constraint);
            }
        }
        self.rewind(state);
        None
    }

    /// `func (p *Parser) parsePostfixTypeOrHigher() *ast.Node`
    fn parse_postfix_type_or_higher(&mut self) -> NodeId {
        let pos = self.node_pos();
        let mut type_node = self.parse_non_array_type();
        while !self.has_preceding_line_break() {
            match self.token {
                Kind::ExclamationToken => {
                    self.next_token();
                    type_node = self.finish_node(
                        self.factory.new_js_doc_non_nullable_type(
                            &mut self.nodes,
                            Some(type_node),
                        ),
                        pos,
                    );
                }
                Kind::QuestionToken => {
                    // If next token is start of a type we have a conditional type
                    if self.look_ahead(Self::next_is_start_of_type) {
                        return type_node;
                    }
                    self.next_token();
                    type_node = self.finish_node(
                        self.factory.new_js_doc_nullable_type(
                            &mut self.nodes,
                            Some(type_node),
                        ),
                        pos,
                    );
                }
                Kind::OpenBracketToken => {
                    self.parse_expected(Kind::OpenBracketToken);
                    if self.is_start_of_type(false /*isStartOfParameter*/) {
                        let index_type = self.parse_type();
                        self.parse_expected(Kind::CloseBracketToken);
                        type_node = self.finish_node(
                            self.factory.new_indexed_access_type_node(
                                &mut self.nodes,
                                Some(type_node),
                                Some(index_type),
                            ),
                            pos,
                        );
                    } else {
                        self.parse_expected(Kind::CloseBracketToken);
                        type_node = self.finish_node(
                            self.factory.new_array_type_node(
                                &mut self.nodes,
                                Some(type_node),
                            ),
                            pos,
                        );
                    }
                }
                _ => return type_node,
            }
        }
        type_node
    }

    /// `func (p *Parser) nextIsStartOfType() bool`
    fn next_is_start_of_type(&mut self) -> bool {
        self.next_token();
        self.is_start_of_type(false /*inStartOfParameter*/)
    }

    /// `func (p *Parser) parseNonArrayType() *ast.Node`
    fn parse_non_array_type(&mut self) -> NodeId {
        match self.token {
            Kind::AnyKeyword
            | Kind::UnknownKeyword
            | Kind::StringKeyword
            | Kind::NumberKeyword
            | Kind::BigIntKeyword
            | Kind::SymbolKeyword
            | Kind::BooleanKeyword
            | Kind::UndefinedKeyword
            | Kind::NeverKeyword
            | Kind::ObjectKeyword => {
                let state = self.mark();
                let keyword_type_node = self.parse_keyword_type_node();
                // If these are followed by a dot then parse these out as a dotted type reference instead
                if self.token != Kind::DotToken {
                    return keyword_type_node;
                }
                self.rewind(state);
                self.parse_type_reference()
            }
            Kind::AsteriskEqualsToken => {
                // If there is '*=', treat it as * followed by postfix =
                self.scanner.rescan_asterisk_equals_token();
                self.token = self.scanner.token();
                self.parse_js_doc_all_type()
            }
            Kind::AsteriskToken => self.parse_js_doc_all_type(),
            Kind::QuestionQuestionToken => {
                // If there is '??', treat it as prefix-'?' in JSDoc type.
                self.scanner.rescan_question_token();
                self.token = self.scanner.token();
                self.parse_js_doc_nullable_type()
            }
            Kind::QuestionToken => self.parse_js_doc_nullable_type(),
            Kind::ExclamationToken => self.parse_js_doc_non_nullable_type(),
            Kind::NoSubstitutionTemplateLiteral
            | Kind::StringLiteral
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::TrueKeyword
            | Kind::FalseKeyword
            | Kind::NullKeyword => self.parse_literal_type_node(false /*negative*/),
            Kind::MinusToken => {
                if self.look_ahead(Self::next_token_is_numeric_or_big_int_literal) {
                    return self.parse_literal_type_node(true /*negative*/);
                }
                self.parse_type_reference()
            }
            Kind::VoidKeyword => self.parse_keyword_type_node(),
            Kind::ThisKeyword => {
                let this_keyword = self.parse_this_type_node();
                if self.token == Kind::IsKeyword && !self.has_preceding_line_break() {
                    return self.parse_this_type_predicate(this_keyword);
                }
                this_keyword
            }
            Kind::TypeOfKeyword => {
                if self.look_ahead(Self::next_is_start_of_type_of_import_type) {
                    return self.parse_import_type();
                }
                self.parse_type_query()
            }
            Kind::OpenBraceToken => {
                if self.look_ahead(Self::next_is_start_of_mapped_type) {
                    return self.parse_mapped_type();
                }
                self.parse_type_literal()
            }
            Kind::OpenBracketToken => self.parse_tuple_type(),
            Kind::OpenParenToken => self.parse_parenthesized_type(),
            Kind::ImportKeyword => self.parse_import_type(),
            Kind::AssertsKeyword => {
                if self.look_ahead(Self::next_token_is_identifier_or_keyword_on_same_line) {
                    return self.parse_asserts_type_predicate();
                }
                self.parse_type_reference()
            }
            Kind::TemplateHead => self.parse_template_type(),
            _ => self.parse_type_reference(),
        }
    }

    /// `func (p *Parser) parseKeywordTypeNode() *ast.Node`
    fn parse_keyword_type_node(&mut self) -> NodeId {
        let pos = self.node_pos();
        let result = self
            .factory
            .new_keyword_type_node(&mut self.nodes, self.token);
        self.next_token();
        self.finish_node(result, pos)
    }

    /// `func (p *Parser) parseThisTypeNode() *ast.Node`
    fn parse_this_type_node(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.next_token();
        self.finish_node(self.factory.new_this_type_node(&mut self.nodes), pos)
    }

    /// `func (p *Parser) parseThisTypePredicate(lhs) *ast.Node`
    fn parse_this_type_predicate(&mut self, lhs: NodeId) -> NodeId {
        let pos = self.nodes[lhs].pos();
        self.next_token();
        let type_node = self.parse_type();
        self.finish_node(
            self.factory.new_type_predicate_node(
                &mut self.nodes,
                None, /*assertsModifier*/
                Some(lhs),
                Some(type_node),
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseJSDocAllType() *ast.Node`
    fn parse_js_doc_all_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.next_token();
        self.finish_node(self.factory.new_js_doc_all_type(&mut self.nodes), pos)
    }

    /// `func (p *Parser) parseJSDocNonNullableType() *ast.TypeNode`
    fn parse_js_doc_non_nullable_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.next_token();
        let t = self.parse_type_operator_or_higher();
        self.finish_node(
            self.factory
                .new_js_doc_non_nullable_type(&mut self.nodes, Some(t)),
            pos,
        )
    }

    /// `func (p *Parser) parseJSDocNullableType() *ast.Node`
    fn parse_js_doc_nullable_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        // skip the ?
        self.next_token();
        let t = self.parse_type_operator_or_higher();
        self.finish_node(
            self.factory
                .new_js_doc_nullable_type(&mut self.nodes, Some(t)),
            pos,
        )
    }

    /// `func (p *Parser) parseJSDocType() *ast.TypeNode`
    pub fn parse_js_doc_type(&mut self) -> NodeId {
        self.scanner.set_skip_jsdoc_leading_asterisks(true);
        let pos = self.node_pos();
        let has_dot_dot_dot = self.parse_optional(Kind::DotDotDotToken);
        let mut t = self.parse_type_or_type_predicate();
        self.scanner.set_skip_jsdoc_leading_asterisks(false);
        if has_dot_dot_dot {
            t = self.finish_node(
                self.factory
                    .new_js_doc_variadic_type(&mut self.nodes, Some(t)),
                pos,
            );
        }
        if self.token == Kind::EqualsToken {
            self.next_token();
            return self.finish_node(
                self.factory
                    .new_js_doc_optional_type(&mut self.nodes, Some(t)),
                pos,
            );
        }
        t
    }

    /// `func (p *Parser) parseLiteralTypeNode(negative bool) *ast.Node`
    fn parse_literal_type_node(&mut self, negative: bool) -> NodeId {
        let pos = self.node_pos();
        if negative {
            self.next_token();
        }
        let mut expression = if matches!(
            self.token,
            Kind::TrueKeyword | Kind::FalseKeyword | Kind::NullKeyword
        ) {
            self.parse_keyword_expression()
        } else {
            self.parse_literal_expression()
        };
        if negative {
            expression = self.finish_node(
                self.factory.new_prefix_unary_expression(
                    &mut self.nodes,
                    Kind::MinusToken,
                    Some(expression),
                ),
                pos,
            );
        }
        self.finish_node(
            self.factory
                .new_literal_type_node(&mut self.nodes, Some(expression)),
            pos,
        )
    }

    /// `func (p *Parser) parseTypeReference() *ast.Node`
    fn parse_type_reference(&mut self) -> NodeId {
        let pos = self.node_pos();
        let entity_name = self.parse_entity_name_of_type_reference();
        let type_arguments = self.parse_type_arguments_of_type_reference();
        self.finish_node(
            self.factory.new_type_reference_node(
                &mut self.nodes,
                entity_name,
                type_arguments,
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseEntityNameOfTypeReference() *ast.Node`
    fn parse_entity_name_of_type_reference(&mut self) -> Option<NodeId> {
        self.parse_entity_name(
            true,  /*allowReservedWords*/
            false, /*allowPrivateName*/
            Some(&diagnostics::Type_expected),
        )
    }

    /// `func (p *Parser) parseEntityName(allowReservedWords, allowPrivateName, diagnosticMessage)`
    pub fn parse_entity_name(
        &mut self,
        allow_reserved_words: bool,
        allow_private_name: bool,
        diagnostic_message: Option<&'static Message>,
    ) -> Option<NodeId> {
        let pos = self.node_pos();
        let mut entity = if allow_reserved_words {
            self.parse_identifier_name_with_diagnostic(diagnostic_message)
        } else {
            self.parse_identifier_with_diagnostic(diagnostic_message, None)
        };
        while self.parse_optional(Kind::DotToken) {
            if self.token == Kind::LessThanToken {
                // The entity is part of a JSDoc-style generic. We will use the gap between `typeName` and
                // `typeArguments` to report it as a grammar error in the checker.
                break;
            }
            let right = self.parse_right_side_of_dot(
                allow_reserved_words,
                allow_private_name,
                true, /*allowUnicodeEscapeSequenceInIdentifierName*/
            );
            entity = self.finish_node(
                self.factory.new_qualified_name(
                    &mut self.nodes,
                    Some(entity),
                    Some(right),
                ),
                pos,
            );
        }
        Some(entity)
    }

    /// `func (p *Parser) parseRightSideOfDot(...)`
    fn parse_right_side_of_dot(
        &mut self,
        allow_identifier_names: bool,
        allow_private_identifiers: bool,
        allow_unicode_escape_sequence_in_identifier_name: bool,
    ) -> NodeId {
        // Technically a keyword is valid here as all identifiers and keywords are identifier names.
        // However, often we'll encounter this in error situations when the identifier or keyword
        // is actually starting another valid construct.
        //
        // So, we check for the following specific case:
        //
        //      name.
        //      identifierOrKeyword identifierNameOrKeyword
        //
        // Note: the newlines are important here.  For example, if that above code
        // were rewritten into:
        //
        //      name.identifierOrKeyword
        //      identifierNameOrKeyword
        //
        // Then we would consider it valid.  That's because ASI would take effect and
        // the code would be implicitly: "name.identifierOrKeyword; identifierNameOrKeyword".
        // In the first case though, ASI will not take effect because there is not a
        // line terminator after the identifier or keyword.
        if self.has_preceding_line_break()
            && token_is_identifier_or_keyword(self.token)
            && self.look_ahead(Self::next_token_is_identifier_or_keyword_on_same_line)
        {
            // Report that we need an identifier.  However, report it right after the dot,
            // and not on the next token.  This is because the next token might actually
            // be an identifier and the error would be quite confusing.
            let pos = self.node_pos();
            self.parse_error_at(pos, pos, &diagnostics::Identifier_expected, &[]);
            return self.create_missing_identifier();
        }
        if self.token == Kind::PrivateIdentifier {
            let node = self.parse_private_identifier();
            if allow_private_identifiers {
                return node;
            }
            let pos = self.node_pos();
            self.parse_error_at(pos, pos, &diagnostics::Identifier_expected, &[]);
            return self.create_missing_identifier();
        }
        if allow_identifier_names {
            if allow_unicode_escape_sequence_in_identifier_name {
                return self.parse_identifier_name();
            }
            return self.parse_identifier_name_error_on_unicode_escape_sequence();
        }
        let save_has_await_identifier = self.statement_has_await_identifier;
        let id = self.parse_identifier();
        self.statement_has_await_identifier = save_has_await_identifier;
        id
    }

    /// `func (p *Parser) newIdentifier(text string) *ast.Node`
    pub fn new_identifier(&mut self, text: &str) -> NodeId {
        self.identifier_count += 1;
        let id = self.factory.new_identifier(&mut self.nodes, text);
        if text == "await" {
            self.statement_has_await_identifier = true;
        }
        id
    }

    /// `func (p *Parser) createMissingIdentifier() *ast.Node`
    fn create_missing_identifier(&mut self) -> NodeId {
        let pos = self.node_pos();
        let id = self.new_identifier("");
        self.finish_node(id, pos)
    }

    /// `func (p *Parser) parsePrivateIdentifier() *ast.Node`
    fn parse_private_identifier(&mut self) -> NodeId {
        let pos = self.node_pos();
        let text = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
        self.next_token();
        self.finish_node(
            self.factory
                .new_private_identifier(&mut self.nodes, &text),
            pos,
        )
    }

    /// `func (p *Parser) reScanLessThanToken() ast.Kind`
    fn rescan_less_than_token(&mut self) -> Kind {
        self.token = self.scanner.rescan_less_than_token();
        self.token
    }

    /// `func (p *Parser) reScanGreaterThanToken() ast.Kind`
    fn rescan_greater_than_token(&mut self) -> Kind {
        self.token = self.scanner.rescan_greater_than_token();
        self.token
    }

    /// `func (p *Parser) reScanSlashToken() ast.Kind`
    fn rescan_slash_token(&mut self) -> Kind {
        self.token = self.scanner.rescan_slash_token(true);
        self.drain_scanner_errors();
        self.token
    }

    /// `func (p *Parser) reScanTemplateToken(isTaggedTemplate bool) ast.Kind`
    fn rescan_template_token(&mut self, is_tagged_template: bool) -> Kind {
        self.token = self.scanner.rescan_template_token(is_tagged_template);
        self.drain_scanner_errors();
        self.token
    }

    /// `func (p *Parser) parseTypeArgumentsOfTypeReference() *ast.NodeList`
    fn parse_type_arguments_of_type_reference(&mut self) -> Option<NodeList> {
        if !self.has_preceding_line_break()
            && self.rescan_less_than_token() == Kind::LessThanToken
        {
            return self.parse_type_arguments();
        }
        None
    }

    /// `func (p *Parser) parseTypeArguments() *ast.NodeList`
    fn parse_type_arguments(&mut self) -> Option<NodeList> {
        if self.token == Kind::LessThanToken {
            return self.parse_bracketed_list(
                PC_TYPE_ARGUMENTS,
                Self::parse_type_some,
                Kind::LessThanToken,
                Kind::GreaterThanToken,
            );
        }
        None
    }

    fn parse_type_some(&mut self) -> Option<NodeId> {
        Some(self.parse_type())
    }

    /// `func (p *Parser) nextIsStartOfTypeOfImportType() bool`
    fn next_is_start_of_type_of_import_type(&mut self) -> bool {
        self.next_token();
        self.token == Kind::ImportKeyword
    }

    /// `func (p *Parser) parseImportType() *ast.Node`
    fn parse_import_type(&mut self) -> NodeId {
        self.source_flags |= NodeFlags::POSSIBLY_CONTAINS_DYNAMIC_IMPORT;
        let pos = self.node_pos();
        let is_type_of = self.parse_optional(Kind::TypeOfKeyword);
        self.parse_expected(Kind::ImportKeyword);
        self.parse_expected(Kind::OpenParenToken);
        let type_node = self.parse_type();
        let mut attributes = None;
        if self.parse_optional(Kind::CommaToken) {
            let open_brace_position = self.scanner.token_start() as i32;
            self.parse_expected(Kind::OpenBraceToken);
            let current_token = self.token;
            if current_token == Kind::WithKeyword || current_token == Kind::AssertKeyword {
                if current_token == Kind::AssertKeyword {
                    self.parse_error_at_current_token(&diagnostics::Import_assertions_have_been_replaced_by_import_attributes_Use_with_instead_of_assert, &[]);
                }
                self.next_token();
            } else {
                self.parse_error_at_current_token(
                    &diagnostics::X_0_expected,
                    &[scanner::token_to_string(Kind::WithKeyword).to_string()],
                );
            }
            self.parse_expected(Kind::ColonToken);
            attributes =
                Some(self.parse_import_attributes(current_token, true /*skipKeyword*/));
            self.parse_optional(Kind::CommaToken);
            if !self.parse_expected(Kind::CloseBraceToken)
                && !self.diagnostics.is_empty()
            {
                let last_diagnostic = self.diagnostics.last().unwrap().clone();
                if lock_diagnostic(&last_diagnostic).code()
                    == diagnostics::X_0_expected.code()
                {
                    let related = new_diagnostic::<String>(
                        None,
                        TextRange::new(open_brace_position, open_brace_position),
                        &diagnostics::The_parser_expected_to_find_a_1_to_match_the_0_token_here,
                        &["{".to_string(), "}".to_string()],
                    );
                    lock_diagnostic(&last_diagnostic).add_related_info(Some(related));
                }
            }
        }
        self.parse_expected(Kind::CloseParenToken);
        let mut qualifier = None;
        if self.parse_optional(Kind::DotToken) {
            qualifier = self.parse_entity_name_of_type_reference();
        }
        let type_arguments = self.parse_type_arguments_of_type_reference();
        self.finish_node(
            self.factory.new_import_type_node(
                &mut self.nodes,
                is_type_of,
                Some(type_node),
                attributes,
                qualifier,
                type_arguments,
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseImportAttribute() *ast.Node`
    fn parse_import_attribute(&mut self) -> NodeId {
        let pos = self.node_pos();
        let mut name = None;
        if token_is_identifier_or_keyword(self.token) {
            name = Some(self.parse_identifier_name());
        } else if self.token == Kind::StringLiteral {
            name = Some(self.parse_literal_expression());
        }
        if name.is_some() {
            self.parse_expected(Kind::ColonToken);
        } else {
            self.parse_error_at_current_token(
                &diagnostics::Identifier_or_string_literal_expected,
                &[],
            );
        }
        let value = self.parse_assignment_expression_or_higher();
        self.finish_node(
            self.factory
                .new_import_attribute(&mut self.nodes, name, Some(value)),
            pos,
        )
    }

    fn parse_import_attribute_some(&mut self) -> Option<NodeId> {
        Some(self.parse_import_attribute())
    }

    /// `func (p *Parser) parseImportAttributes(token, skipKeyword) *ast.Node`
    fn parse_import_attributes(&mut self, token: Kind, skip_keyword: bool) -> NodeId {
        let pos = self.node_pos();
        if !skip_keyword {
            self.parse_expected(token);
        }
        let elements: NodeList;
        let mut multi_line = false;
        let open_brace_position = self.scanner.token_start() as i32;
        if self.parse_expected(Kind::OpenBraceToken) {
            multi_line = self.has_preceding_line_break();
            elements = self
                .parse_delimited_list(
                    PC_IMPORT_ATTRIBUTES,
                    Self::parse_import_attribute_some,
                    false,
                )
                .unwrap_or_else(|| self.parse_empty_node_list());
            if !self.parse_expected(Kind::CloseBraceToken)
                && !self.diagnostics.is_empty()
            {
                let last_diagnostic = self.diagnostics.last().unwrap().clone();
                if lock_diagnostic(&last_diagnostic).code()
                    == diagnostics::X_0_expected.code()
                {
                    let related = new_diagnostic::<String>(
                        None,
                        TextRange::new(open_brace_position, open_brace_position),
                        &diagnostics::The_parser_expected_to_find_a_1_to_match_the_0_token_here,
                        &["{".to_string(), "}".to_string()],
                    );
                    lock_diagnostic(&last_diagnostic).add_related_info(Some(related));
                }
            }
        } else {
            elements = self.parse_empty_node_list();
        }
        self.finish_node(
            self.factory.new_import_attributes(
                &mut self.nodes,
                token,
                Some(elements),
                multi_line,
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseTypeQuery() *ast.Node`
    fn parse_type_query(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::TypeOfKeyword);
        let entity_name = self.parse_entity_name(
            true, /*allowReservedWords*/
            true, /*allowPrivateName*/
            None,
        );
        // Make sure we perform ASI to prevent parsing the next line's type arguments as part of an instantiation expression
        let mut type_arguments = None;
        if !self.has_preceding_line_break() {
            type_arguments = self.parse_type_arguments();
        }
        self.finish_node(
            self.factory
                .new_type_query_node(&mut self.nodes, entity_name, type_arguments),
            pos,
        )
    }

    /// `func (p *Parser) nextIsStartOfMappedType() bool`
    fn next_is_start_of_mapped_type(&mut self) -> bool {
        self.next_token();
        if self.token == Kind::PlusToken || self.token == Kind::MinusToken {
            return self.next_token() == Kind::ReadonlyKeyword;
        }
        if self.token == Kind::ReadonlyKeyword {
            self.next_token();
        }
        self.token == Kind::OpenBracketToken
            && self.next_token_is_identifier()
            && self.next_token() == Kind::InKeyword
    }

    /// `func (p *Parser) parseMappedType() *ast.Node`
    fn parse_mapped_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::OpenBraceToken);
        let mut readonly_token = None; // ReadonlyKeyword | PlusToken | MinusToken
        if matches!(
            self.token,
            Kind::ReadonlyKeyword | Kind::PlusToken | Kind::MinusToken
        ) {
            readonly_token = Some(self.parse_token_node());
            if self.nodes[readonly_token.unwrap()].kind != Kind::ReadonlyKeyword {
                self.parse_expected(Kind::ReadonlyKeyword);
            }
        }
        self.parse_expected(Kind::OpenBracketToken);
        let type_parameter = self.parse_mapped_type_parameter();
        let mut name_type = None;
        if self.parse_optional(Kind::AsKeyword) {
            name_type = Some(self.parse_type());
        }
        self.parse_expected(Kind::CloseBracketToken);
        let mut question_token = None; // QuestionToken | PlusToken | MinusToken
        if matches!(
            self.token,
            Kind::QuestionToken | Kind::PlusToken | Kind::MinusToken
        ) {
            question_token = Some(self.parse_token_node());
            if self.nodes[question_token.unwrap()].kind != Kind::QuestionToken {
                self.parse_expected(Kind::QuestionToken);
            }
        }
        let type_node = self.parse_type_annotation();
        self.parse_semicolon();
        let members = self.parse_list(PC_TYPE_MEMBERS, Self::parse_type_member_some);
        self.parse_expected(Kind::CloseBraceToken);
        self.finish_node(
            self.factory.new_mapped_type_node(
                &mut self.nodes,
                readonly_token,
                Some(type_parameter),
                name_type,
                question_token,
                type_node,
                Some(members),
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseMappedTypeParameter() *ast.Node`
    fn parse_mapped_type_parameter(&mut self) -> NodeId {
        let pos = self.node_pos();
        let name = self.parse_identifier_name();
        self.parse_expected(Kind::InKeyword);
        let type_node = self.parse_type();
        self.finish_node(
            self.factory.new_type_parameter_declaration(
                &mut self.nodes,
                None, /*modifiers*/
                Some(name),
                Some(type_node),
                None, /*expression*/
                None, /*defaultType*/
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseTypeMember() *ast.Node`
    fn parse_type_member(&mut self) -> NodeId {
        if self.token == Kind::OpenParenToken || self.token == Kind::LessThanToken {
            return self.parse_signature_member(Kind::CallSignature);
        }
        if self.token == Kind::NewKeyword
            && self.look_ahead(Self::next_token_is_open_paren_or_less_than)
        {
            return self.parse_signature_member(Kind::ConstructSignature);
        }
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers();
        if self.parse_contextual_modifier(Kind::GetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                Kind::GetAccessor,
                ParseFlags::TYPE,
            );
        }
        if self.parse_contextual_modifier(Kind::SetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                Kind::SetAccessor,
                ParseFlags::TYPE,
            );
        }
        if self.is_index_signature() {
            return self.parse_index_signature_declaration(pos, jsdoc, modifiers);
        }
        self.parse_property_or_method_signature(pos, jsdoc, modifiers)
    }

    fn parse_type_member_some(&mut self) -> Option<NodeId> {
        Some(self.parse_type_member())
    }

    /// `func (p *Parser) nextTokenIsOpenParenOrLessThan() bool`
    fn next_token_is_open_paren_or_less_than(&mut self) -> bool {
        self.next_token();
        self.token == Kind::OpenParenToken || self.token == Kind::LessThanToken
    }

    /// `func (p *Parser) parseSignatureMember(kind) *ast.Node`
    fn parse_signature_member(&mut self, kind: Kind) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        if kind == Kind::ConstructSignature {
            self.parse_expected(Kind::NewKeyword);
        }
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(ParseFlags::TYPE);
        let type_node = self.parse_return_type(Kind::ColonToken /*isType*/, true);
        self.parse_type_member_semicolon();
        let result = if kind == Kind::CallSignature {
            self.factory.new_call_signature_declaration(
                &mut self.nodes,
                type_parameters,
                Some(parameters),
                type_node,
            )
        } else {
            self.factory.new_construct_signature_declaration(
                &mut self.nodes,
                type_parameters,
                Some(parameters),
                type_node,
            )
        };
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseTypeParameters() *ast.NodeList`
    fn parse_type_parameters(&mut self) -> Option<NodeList> {
        if self.token == Kind::LessThanToken {
            return self.parse_bracketed_list(
                PC_TYPE_PARAMETERS,
                Self::parse_type_parameter_some,
                Kind::LessThanToken,
                Kind::GreaterThanToken,
            );
        }
        None
    }

    /// `func (p *Parser) parseTypeParameter() *ast.Node`
    fn parse_type_parameter(&mut self) -> NodeId {
        let pos = self.node_pos();
        let modifiers = self.parse_modifiers_ex(
            false, /*allowDecorators*/
            true,  /*permitConstAsModifier*/
            false, /*stopOnStartOfClassStaticBlock*/
        );
        let name = self.parse_identifier();
        let mut constraint = None;
        let mut expression = None;
        if self.parse_optional(Kind::ExtendsKeyword) {
            // It's not uncommon for people to write improper constraints to a generic.  If the
            // user writes a constraint that is an expression and not an actual type, then parse
            // it out as an expression (so we can recover well), but report that a type is needed
            // instead.
            if self.is_start_of_type(false /*inStartOfParameter*/)
                || !self.is_start_of_expression()
            {
                constraint = Some(self.parse_type());
            } else {
                // It was not a type, and it looked like an expression.  Parse out an expression
                // here so we recover well.  Note: it is important that we call parseUnaryExpression
                // and not parseExpression here.  If the user has:
                //
                //      <T extends "">
                //
                // We do *not* want to consume the `>` as we're consuming the expression for "".
                expression = Some(self.parse_unary_expression_or_higher());
            }
        }
        let mut default_type = None;
        if self.parse_optional(Kind::EqualsToken) {
            default_type = Some(self.parse_type());
        }
        let result = self.factory.new_type_parameter_declaration(
            &mut self.nodes,
            modifiers,
            Some(name),
            constraint,
            expression,
            default_type,
        );
        self.finish_node(result, pos)
    }

    fn parse_type_parameter_some(&mut self) -> Option<NodeId> {
        Some(self.parse_type_parameter())
    }

    /// `func (p *Parser) parseParameters(flags ParseFlags) *ast.NodeList`
    pub fn parse_parameters(&mut self, flags: ParseFlags) -> NodeList {
        // FormalParameters [Yield,Await]: (modified)
        //      [empty]
        //      FormalParameterList[?Yield,Await]
        //
        // FormalParameter[Yield,Await]: (modified)
        //      BindingElement[?Yield,Await]
        //
        // BindingElement [Yield,Await]: (modified)
        //      SingleNameBinding[?Yield,?Await]
        //      BindingPattern[?Yield,?Await]Initializer [In, ?Yield,?Await] opt
        //
        // SingleNameBinding [Yield,Await]:
        //      BindingIdentifier[?Yield,?Await]Initializer [In, ?Yield,?Await] opt
        if self.parse_expected(Kind::OpenParenToken) {
            let parameters =
                self.parse_parameters_worker(flags, true /*allowAmbiguity*/);
            self.parse_expected(Kind::CloseParenToken);
            return parameters.unwrap_or_else(|| self.create_missing_list());
        }
        self.create_missing_list()
    }

    /// `func (p *Parser) parseParametersWorker(flags, allowAmbiguity) *ast.NodeList`
    fn parse_parameters_worker(
        &mut self,
        flags: ParseFlags,
        allow_ambiguity: bool,
    ) -> Option<NodeList> {
        let in_await_context =
            self.context_flags.intersects(NodeFlags::AWAIT_CONTEXT);
        let save_context_flags = self.context_flags;
        self.set_context_flags(
            NodeFlags::YIELD_CONTEXT,
            flags.intersects(ParseFlags::YIELD),
        );
        self.set_context_flags(
            NodeFlags::AWAIT_CONTEXT,
            flags.intersects(ParseFlags::AWAIT),
        );
        let parameters = self.parse_delimited_list(
            PC_PARAMETERS,
            move |p| {
                let parameter =
                    p.parse_parameter_ex(in_await_context, allow_ambiguity);
                if let Some(parameter) = parameter
                    && !flags.intersects(ParseFlags::TYPE)
                {
                    p.check_js_syntax(parameter);
                }
                parameter
            },
            false,
        );
        self.context_flags = save_context_flags;
        parameters
    }

    /// `func (p *Parser) parseParameter() *ast.Node`
    pub fn parse_parameter(&mut self) -> Option<NodeId> {
        self.parse_parameter_ex(
            false, /*inOuterAwaitContext*/
            true,  /*allowAmbiguity*/
        )
    }

    /// `func (p *Parser) parseParameterEx(inOuterAwaitContext, allowAmbiguity)`
    fn parse_parameter_ex(
        &mut self,
        in_outer_await_context: bool,
        allow_ambiguity: bool,
    ) -> Option<NodeId> {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        // FormalParameter [Yield,Await]:
        //      BindingElement[?Yield,?Await]
        // Decorators are parsed in the outer [Await] context, the rest of the parameter is parsed in the function's [Await] context.
        let save_context_flags = self.context_flags;
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, in_outer_await_context);
        let modifiers = self.parse_modifiers_ex(
            true,  /*allowDecorators*/
            false, /*permitConstAsModifier*/
            false, /*stopOnStartOfClassStaticBlock*/
        );
        self.context_flags = save_context_flags;
        if self.token == Kind::ThisKeyword {
            let name = self.create_identifier(true /*isIdentifier*/);
            let result = self.factory.new_parameter_declaration(
                &mut self.nodes,
                modifiers.clone(),
                None, /*dotDotDotToken*/
                Some(name),
                None, /*questionToken*/
                self.parse_type_annotation(),
                None, /*initializer*/
            );
            if let Some(mods) = modifiers.as_ref() {
                let loc = mods.nodes[0];
                let loc = self.nodes[loc].loc;
                self.parse_error_at_range(
                    loc,
                    &diagnostics::Neither_decorators_nor_modifiers_may_be_applied_to_this_parameters,
                    &[],
                );
            }
            let result = self.finish_node(result, pos);
            self.with_jsdoc(result, jsdoc);
            return Some(result);
        }
        let dot_dot_dot_token = self.parse_optional_token(Kind::DotDotDotToken);
        if !allow_ambiguity && !self.is_parameter_name_start() {
            return None;
        }
        let name = self.parse_name_of_parameter(modifiers.as_ref());
        let question_token = self.parse_optional_token(Kind::QuestionToken);
        let type_annotation = self.parse_type_annotation();
        let initializer = self.parse_initializer();
        let result = self.factory.new_parameter_declaration(
            &mut self.nodes,
            modifiers,
            dot_dot_dot_token,
            Some(name),
            question_token,
            type_annotation,
            initializer,
        );
        let result = self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        Some(result)
    }

    /// `func (p *Parser) isParameterNameStart() bool`
    fn is_parameter_name_start(&mut self) -> bool {
        // Be permissive about await and yield by calling isBindingIdentifier instead of isIdentifier; disallowing
        // them during a speculative parse leads to many more follow-on errors than allowing the function to parse then later
        // complaining about the use of the keywords.
        self.is_binding_identifier()
            || self.token == Kind::OpenBracketToken
            || self.token == Kind::OpenBraceToken
    }

    /// `func (p *Parser) parseNameOfParameter(modifiers) *ast.Node`
    fn parse_name_of_parameter(&mut self, modifiers: Option<&ModifierList>) -> NodeId {
        // FormalParameter [Yield,Await]:
        //      BindingElement[?Yield,?Await]
        let name = self.parse_identifier_or_pattern_with_diagnostic(Some(
            &diagnostics::Private_identifiers_cannot_be_used_as_parameters,
        ));
        if self.nodes[name].loc.len() == 0
            && modifiers.is_none()
            && self.token.is_modifier_kind()
        {
            // in cases like
            // 'use strict'
            // function foo(static)
            // isParameter('static') == true, because of isModifier('static')
            // however 'static' is not a legal identifier in a strict mode.
            // so result of this function will be Parameter (flags = 0, name = missing, type = undefined, initializer = undefined)
            // and current token will not change => parsing of the enclosing parameter list will last till the end of time (or OOM)
            // to avoid this we'll advance cursor to the next token.
            self.next_token();
        }
        name
    }

    /// `func (p *Parser) parseReturnType(returnToken, isType) *ast.TypeNode`
    fn parse_return_type(&mut self, return_token: Kind, is_type: bool) -> Option<NodeId> {
        if self.should_parse_return_type(return_token, is_type) {
            return Some(self.do_in_context(
                NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT,
                false,
                Self::parse_type_or_type_predicate,
            ));
        }
        None
    }

    /// `func (p *Parser) shouldParseReturnType(returnToken, isType) bool`
    fn should_parse_return_type(&mut self, return_token: Kind, is_type: bool) -> bool {
        if return_token == Kind::EqualsGreaterThanToken {
            self.parse_expected(return_token);
            return true;
        } else if self.parse_optional(Kind::ColonToken) {
            return true;
        } else if is_type && self.token == Kind::EqualsGreaterThanToken {
            // This is easy to get backward, especially in type contexts, so parse the type anyway
            self.parse_error_at_current_token(
                &diagnostics::X_0_expected,
                &[scanner::token_to_string(Kind::ColonToken).to_string()],
            );
            self.next_token();
            return true;
        }
        false
    }

    /// `func (p *Parser) parseTypeOrTypePredicate() *ast.TypeNode`
    fn parse_type_or_type_predicate(&mut self) -> NodeId {
        if self.is_identifier() {
            let state = self.mark();
            let pos = self.node_pos();
            let id = self.parse_identifier();
            if self.token == Kind::IsKeyword && !self.has_preceding_line_break() {
                self.next_token();
                let t = self.parse_type();
                return self.finish_node(
                    self.factory.new_type_predicate_node(
                        &mut self.nodes,
                        None, /*assertsModifier*/
                        Some(id),
                        Some(t),
                    ),
                    pos,
                );
            }
            self.rewind(state);
        }
        self.parse_type()
    }

    /// `func (p *Parser) parseTypeMemberSemicolon()`
    fn parse_type_member_semicolon(&mut self) {
        // We allow type members to be separated by commas or (possibly ASI) semicolons.
        // First check if it was a comma.  If so, we're done with the member.
        if self.parse_optional(Kind::CommaToken) {
            return;
        }
        // Didn't have a comma.  We must have a (possible ASI) semicolon.
        self.parse_semicolon();
    }

    /// `func (p *Parser) parseAccessorDeclaration(pos, jsdoc, modifiers, kind, flags)`
    fn parse_accessor_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
        kind: Kind,
        flags: ParseFlags,
    ) -> NodeId {
        let name = self.parse_property_name();
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(ParseFlags::NONE);
        let return_type = self.parse_return_type(Kind::ColonToken, false /*isType*/);
        let body = self.parse_function_block_or_semicolon(flags, None /*diagnosticMessage*/);
        // Keep track of `typeParameters` (for both) and `type` (for setters) if they were parsed those indicate grammar errors
        let result = if kind == Kind::GetAccessor {
            self.factory.new_get_accessor_declaration(
                &mut self.nodes,
                modifiers,
                Some(name),
                type_parameters,
                Some(parameters),
                return_type,
                None, /*fullSignature*/
                body,
            )
        } else {
            self.factory.new_set_accessor_declaration(
                &mut self.nodes,
                modifiers,
                Some(name),
                type_parameters,
                Some(parameters),
                return_type,
                None, /*fullSignature*/
                body,
            )
        };
        self.with_jsdoc(self.finish_node(result, pos), jsdoc);
        if !flags.intersects(ParseFlags::TYPE) {
            self.check_js_syntax(result);
        }
        result
    }

    /// `func (p *Parser) parsePropertyName() *ast.Node`
    pub fn parse_property_name(&mut self) -> NodeId {
        let save_has_await_identifier = self.statement_has_await_identifier;
        let prop = self.parse_property_name_worker(true /*allowComputedPropertyNames*/);
        self.statement_has_await_identifier = save_has_await_identifier;
        prop
    }

    /// `func (p *Parser) parsePropertyNameWorker(allowComputedPropertyNames)`
    fn parse_property_name_worker(&mut self, allow_computed_property_names: bool) -> NodeId {
        if matches!(
            self.token,
            Kind::StringLiteral | Kind::NumericLiteral | Kind::BigIntLiteral
        ) {
            return self.parse_literal_expression();
        }
        if allow_computed_property_names && self.token == Kind::OpenBracketToken {
            return self.parse_computed_property_name();
        }
        if self.token == Kind::PrivateIdentifier {
            return self.parse_private_identifier();
        }
        self.parse_identifier_name()
    }

    /// `func (p *Parser) parseComputedPropertyName() *ast.Node`
    fn parse_computed_property_name(&mut self) -> NodeId {
        // PropertyName [Yield]:
        //      LiteralPropertyName
        //      ComputedPropertyName[?Yield]
        let pos = self.node_pos();
        self.parse_expected(Kind::OpenBracketToken);
        // We parse any expression (including a comma expression). But the grammar
        // says that only an assignment expression is allowed, so the grammar checker
        // will error if it sees a comma expression.
        let expression = self.parse_expression_allow_in();
        self.parse_expected(Kind::CloseBracketToken);
        self.finish_node(
            self.factory
                .new_computed_property_name(&mut self.nodes, Some(expression)),
            pos,
        )
    }

    /// `func (p *Parser) parseFunctionBlockOrSemicolon(flags, diagnosticMessage)`
    fn parse_function_block_or_semicolon(
        &mut self,
        flags: ParseFlags,
        diagnostic_message: Option<&'static Message>,
    ) -> Option<NodeId> {
        if self.token != Kind::OpenBraceToken {
            if flags.intersects(ParseFlags::TYPE) {
                self.parse_type_member_semicolon();
                return None;
            }
            if self.can_parse_semicolon() {
                self.parse_semicolon();
                return None;
            }
        }
        Some(self.parse_function_block(flags, diagnostic_message))
    }

    /// `func (p *Parser) parseFunctionBlock(flags, diagnosticMessage) *ast.Node`
    fn parse_function_block(
        &mut self,
        flags: ParseFlags,
        diagnostic_message: Option<&'static Message>,
    ) -> NodeId {
        let save_context_flags = self.context_flags;
        let save_has_await_identifier = self.statement_has_await_identifier;
        self.set_context_flags(
            NodeFlags::YIELD_CONTEXT,
            flags.intersects(ParseFlags::YIELD),
        );
        self.set_context_flags(
            NodeFlags::AWAIT_CONTEXT,
            flags.intersects(ParseFlags::AWAIT),
        );
        // We may be in a [Decorator] context when parsing a function expression or
        // arrow function. The body of the function is not in [Decorator] context.
        self.set_context_flags(NodeFlags::DECORATOR_CONTEXT, false);
        let block = self.parse_block(
            flags.intersects(ParseFlags::IGNORE_MISSING_OPEN_BRACE),
            diagnostic_message,
        );
        self.context_flags = save_context_flags;
        self.statement_has_await_identifier = save_has_await_identifier;
        block
    }

    /// `func (p *Parser) isIndexSignature() bool`
    fn is_index_signature(&mut self) -> bool {
        self.token == Kind::OpenBracketToken
            && self.look_ahead(Self::next_is_unambiguously_index_signature)
    }

    /// `func (p *Parser) nextIsUnambiguouslyIndexSignature() bool`
    fn next_is_unambiguously_index_signature(&mut self) -> bool {
        // The only allowed sequence is:
        //
        //   [id:
        //
        // However, for error recovery, we also check the following cases:
        //
        //   [...
        //   [id,
        //   [id?,
        //   [id?:
        //   [id?]
        //   [public id
        //   [private id
        //   [protected id
        //   []
        //
        self.next_token();
        if self.token == Kind::DotDotDotToken || self.token == Kind::CloseBracketToken {
            return true;
        }
        if self.token.is_modifier_kind() {
            self.next_token();
            if self.is_identifier() {
                return true;
            }
        } else if !self.is_identifier() {
            return false;
        } else {
            // Skip the identifier
            self.next_token();
        }
        // A colon signifies a well formed indexer
        // A comma should be a badly formed indexer because comma expressions are not allowed
        // in computed properties.
        if self.token == Kind::ColonToken || self.token == Kind::CommaToken {
            return true;
        }
        // Question mark could be an indexer with an optional property,
        // or it could be a conditional expression in a computed property.
        if self.token != Kind::QuestionToken {
            return false;
        }
        // If any of the following tokens are after the question mark, it cannot
        // be a conditional expression, so treat it as an indexer.
        self.next_token();
        self.token == Kind::ColonToken
            || self.token == Kind::CommaToken
            || self.token == Kind::CloseBracketToken
    }

    /// `func (p *Parser) parseIndexSignatureDeclaration(pos, jsdoc, modifiers)`
    fn parse_index_signature_declaration(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let parameters = self.parse_bracketed_list(
            PC_PARAMETERS,
            Self::parse_parameter,
            Kind::OpenBracketToken,
            Kind::CloseBracketToken,
        );
        let type_node = self.parse_type_annotation();
        self.parse_type_member_semicolon();
        let result = self.finish_node(
            self.factory.new_index_signature_declaration(
                &mut self.nodes,
                modifiers,
                parameters,
                type_node,
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parsePropertyOrMethodSignature(pos, jsdoc, modifiers)`
    fn parse_property_or_method_signature(
        &mut self,
        pos: i32,
        jsdoc: JSDocScannerInfo,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let name = self.parse_property_name();
        let question_token = self.parse_optional_token(Kind::QuestionToken);
        let result;
        if self.token == Kind::OpenParenToken || self.token == Kind::LessThanToken {
            // Method signatures don't exist in expression contexts.  So they have neither
            // [Yield] nor [Await]
            let type_parameters = self.parse_type_parameters();
            let parameters = self.parse_parameters(ParseFlags::TYPE);
            let return_type = self.parse_return_type(Kind::ColonToken /*isType*/, true);
            result = self.factory.new_method_signature_declaration(
                &mut self.nodes,
                modifiers,
                Some(name),
                question_token,
                type_parameters,
                Some(parameters),
                return_type,
            );
        } else {
            let type_node = self.parse_type_annotation();
            // Although type literal properties cannot not have initializers, we attempt
            // to parse an initializer so we can report in the checker that an interface
            // property or type literal property cannot have an initializer.
            let mut initializer = None;
            if self.token == Kind::EqualsToken {
                initializer = self.parse_initializer();
            }
            result = self.factory.new_property_signature_declaration(
                &mut self.nodes,
                modifiers,
                Some(name),
                question_token,
                type_node,
                initializer,
            );
        }
        self.parse_type_member_semicolon();
        self.with_jsdoc(self.finish_node(result, pos), jsdoc);
        result
    }

    /// `func (p *Parser) parseTypeLiteral() *ast.Node`
    pub fn parse_type_literal(&mut self) -> NodeId {
        let pos = self.node_pos();
        let members = self.parse_object_type_members();
        self.finish_node(
            self.factory
                .new_type_literal_node(&mut self.nodes, Some(members)),
            pos,
        )
    }

    /// `func (p *Parser) parseObjectTypeMembers() *ast.NodeList`
    fn parse_object_type_members(&mut self) -> NodeList {
        if self.parse_expected(Kind::OpenBraceToken) {
            let members = self.parse_list(PC_TYPE_MEMBERS, Self::parse_type_member_some);
            self.parse_expected(Kind::CloseBraceToken);
            return members;
        }
        self.create_missing_list()
    }

    /// `func (p *Parser) parseTupleType() *ast.Node`
    fn parse_tuple_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        let elements = self.parse_bracketed_list(
            PC_TUPLE_ELEMENT_TYPES,
            Self::parse_tuple_element_name_or_tuple_element_type_some,
            Kind::OpenBracketToken,
            Kind::CloseBracketToken,
        );
        self.finish_node(
            self.factory
                .new_tuple_type_node(&mut self.nodes, elements),
            pos,
        )
    }

    /// `func (p *Parser) parseTupleElementNameOrTupleElementType() *ast.Node`
    fn parse_tuple_element_name_or_tuple_element_type(&mut self) -> NodeId {
        if self.look_ahead(Self::scan_start_of_named_tuple_element) {
            let pos = self.node_pos();
            let jsdoc = self.jsdoc_scanner_info();
            let dot_dot_dot_token = self.parse_optional_token(Kind::DotDotDotToken);
            let name = self.parse_identifier_name();
            let question_token = self.parse_optional_token(Kind::QuestionToken);
            self.parse_expected(Kind::ColonToken);
            let type_node = self.parse_tuple_element_type();
            let result = self.finish_node(
                self.factory.new_named_tuple_member(
                    &mut self.nodes,
                    dot_dot_dot_token,
                    Some(name),
                    question_token,
                    Some(type_node),
                ),
                pos,
            );
            self.with_jsdoc(result, jsdoc);
            return result;
        }
        self.parse_tuple_element_type()
    }

    fn parse_tuple_element_name_or_tuple_element_type_some(&mut self) -> Option<NodeId> {
        Some(self.parse_tuple_element_name_or_tuple_element_type())
    }

    /// `func (p *Parser) scanStartOfNamedTupleElement() bool`
    fn scan_start_of_named_tuple_element(&mut self) -> bool {
        if self.token == Kind::DotDotDotToken {
            return token_is_identifier_or_keyword(self.next_token())
                && self.next_token_is_colon_or_question_colon();
        }
        token_is_identifier_or_keyword(self.token)
            && self.next_token_is_colon_or_question_colon()
    }

    /// `func (p *Parser) nextTokenIsColonOrQuestionColon() bool`
    fn next_token_is_colon_or_question_colon(&mut self) -> bool {
        self.next_token() == Kind::ColonToken
            || (self.token == Kind::QuestionToken && self.next_token() == Kind::ColonToken)
    }

    /// `func (p *Parser) parseTupleElementType() *ast.TypeNode`
    fn parse_tuple_element_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        if self.parse_optional(Kind::DotDotDotToken) {
            let t = self.parse_type();
            return self.finish_node(
                self.factory.new_rest_type_node(&mut self.nodes, Some(t)),
                pos,
            );
        }
        let mut type_node = self.parse_type();
        if is_js_doc_nullable_type(&self.nodes[type_node]) {
            let inner = self.nodes[type_node]
                .as_js_doc_nullable_type()
                .type_;
            if let Some(inner) = inner
                && self.nodes[type_node].pos() == self.nodes[inner].pos()
            {
                let node = self
                    .factory
                    .new_optional_type_node(&mut self.nodes, Some(inner));
                self.nodes[node].flags = self.nodes[type_node].flags;
                self.nodes[node].loc = self.nodes[type_node].loc;
                self.nodes[inner].parent = Some(node);
                return node;
            }
        }
        type_node
    }

    /// `func (p *Parser) parseParenthesizedType() *ast.Node`
    fn parse_parenthesized_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::OpenParenToken);
        let type_node = self.parse_type();
        self.parse_expected(Kind::CloseParenToken);
        self.finish_node(
            self.factory
                .new_parenthesized_type_node(&mut self.nodes, Some(type_node)),
            pos,
        )
    }

    /// `func (p *Parser) parseAssertsTypePredicate() *ast.TypeNode`
    fn parse_asserts_type_predicate(&mut self) -> NodeId {
        let pos = self.node_pos();
        let asserts_modifier = self.parse_expected_token(Kind::AssertsKeyword);
        let parameter_name = if self.token == Kind::ThisKeyword {
            self.parse_this_type_node()
        } else {
            self.parse_identifier()
        };
        let mut type_node = None;
        if self.parse_optional(Kind::IsKeyword) {
            type_node = Some(self.parse_type());
        }
        self.finish_node(
            self.factory.new_type_predicate_node(
                &mut self.nodes,
                Some(asserts_modifier),
                Some(parameter_name),
                type_node,
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseTemplateType() *ast.Node`
    fn parse_template_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        let head = self.parse_template_head(false /*isTaggedTemplate*/);
        let spans = self.parse_template_type_spans();
        self.finish_node(
            self.factory.new_template_literal_type_node(
                &mut self.nodes,
                Some(head),
                Some(spans),
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseTemplateHead(isTaggedTemplate) *ast.Node`
    fn parse_template_head(&mut self, is_tagged_template: bool) -> NodeId {
        if !is_tagged_template
            && self
                .scanner
                .token_flags()
                .intersects(TokenFlags::IS_INVALID)
        {
            self.rescan_template_token(false /*isTaggedTemplate*/);
        }
        let pos = self.node_pos();
        let text = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
        let raw_text = self.get_template_literal_raw_text(2 /*endLength*/);
        let flags = self.scanner.token_flags();
        let result = self.factory.new_template_head(
            &mut self.nodes,
            &text,
            &raw_text,
            flags,
        );
        self.next_token();
        self.finish_node(result, pos)
    }

    /// `func (p *Parser) getTemplateLiteralRawText(endLength int) string`
    fn get_template_literal_raw_text(&mut self, mut end_length: usize) -> String {
        let token_text = self.scanner.token_text();
        if self
            .scanner
            .token_flags()
            .intersects(TokenFlags::UNTERMINATED)
        {
            end_length = 0;
        }
        token_text[1..token_text.len() - end_length].to_string()
    }

    /// `func (p *Parser) parseTemplateTypeSpans() *ast.NodeList`
    fn parse_template_type_spans(&mut self) -> NodeList {
        let pos = self.node_pos();
        let mut list = Vec::new();
        loop {
            let span = self.parse_template_type_span();
            let is_middle = self.nodes[span]
                .as_template_literal_type_span()
                .literal
                .is_some_and(|l| self.nodes[l].kind == Kind::TemplateMiddle);
            list.push(span);
            if !is_middle {
                break;
            }
        }
        self.new_node_list(TextRange::new(pos, self.node_pos()), list)
    }

    /// `func (p *Parser) parseTemplateTypeSpan() *ast.Node`
    fn parse_template_type_span(&mut self) -> NodeId {
        let pos = self.node_pos();
        let t = self.parse_type();
        let literal = self.parse_literal_of_template_span(false /*isTaggedTemplate*/);
        self.finish_node(
            self.factory.new_template_literal_type_span(
                &mut self.nodes,
                Some(t),
                Some(literal),
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseLiteralOfTemplateSpan(isTaggedTemplate) *ast.Node`
    fn parse_literal_of_template_span(&mut self, is_tagged_template: bool) -> NodeId {
        if self.token == Kind::CloseBraceToken {
            self.rescan_template_token(is_tagged_template);
            return self.parse_template_middle_or_tail();
        }
        self.parse_error_at_current_token(
            &diagnostics::X_0_expected,
            &[scanner::token_to_string(Kind::CloseBraceToken).to_string()],
        );
        let pos = self.node_pos();
        self.finish_node(
            self.factory.new_template_tail(
                &mut self.nodes,
                "",
                "",
                TokenFlags::NONE,
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseTemplateMiddleOrTail() *ast.Node`
    fn parse_template_middle_or_tail(&mut self) -> NodeId {
        let pos = self.node_pos();
        let text = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
        let flags = self.scanner.token_flags();
        let result = if self.token == Kind::TemplateMiddle {
            let raw_text = self.get_template_literal_raw_text(2 /*endLength*/);
            self.factory
                .new_template_middle(&mut self.nodes, &text, &raw_text, flags)
        } else {
            let raw_text = self.get_template_literal_raw_text(1 /*endLength*/);
            self.factory
                .new_template_tail(&mut self.nodes, &text, &raw_text, flags)
        };
        self.next_token();
        self.finish_node(result, pos)
    }

    /// `func (p *Parser) parseFunctionOrConstructorTypeToError(isInUnionType, parseConstituentType)`
    fn parse_function_or_constructor_type_to_error(
        &mut self,
        is_in_union_type: bool,
        parse_constituent_type: fn(&mut Self) -> NodeId,
    ) -> NodeId {
        // the function type and constructor type shorthand notation
        // are not allowed directly in unions and intersections, but we'll
        // try to parse them gracefully and issue a helpful message.
        if self.is_start_of_function_type_or_constructor_type() {
            let type_node = self.parse_function_or_constructor_type();
            let loc = self.nodes[type_node].loc;
            let diagnostic = if self.nodes[type_node].kind == Kind::FunctionType {
                if is_in_union_type {
                    &diagnostics::Function_type_notation_must_be_parenthesized_when_used_in_a_union_type
                } else {
                    &diagnostics::Function_type_notation_must_be_parenthesized_when_used_in_an_intersection_type
                }
            } else if is_in_union_type {
                &diagnostics::Constructor_type_notation_must_be_parenthesized_when_used_in_a_union_type
            } else {
                &diagnostics::Constructor_type_notation_must_be_parenthesized_when_used_in_an_intersection_type
            };
            self.parse_error_at_range(loc, diagnostic, &[]);
            return type_node;
        }
        parse_constituent_type(self)
    }

    /// `func (p *Parser) isStartOfFunctionTypeOrConstructorType() bool`
    fn is_start_of_function_type_or_constructor_type(&mut self) -> bool {
        self.token == Kind::LessThanToken
            || self.token == Kind::OpenParenToken
                && self.look_ahead(Self::next_is_unambiguously_start_of_function_type)
            || self.token == Kind::NewKeyword
            || self.token == Kind::AbstractKeyword
                && self.look_ahead(Self::next_token_is_new_keyword)
    }

    /// `func (p *Parser) parseFunctionOrConstructorType() *ast.TypeNode`
    fn parse_function_or_constructor_type(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers_for_constructor_type();
        let is_constructor_type = self.parse_optional(Kind::NewKeyword);
        tsc_debug::assert_!(modifiers.is_none() || is_constructor_type, "Per isStartOfFunctionOrConstructorType, a function type cannot have modifiers.");
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(ParseFlags::TYPE);
        let return_type =
            self.parse_return_type(Kind::EqualsGreaterThanToken, false /*isType*/);
        let result = if is_constructor_type {
            self.factory.new_constructor_type_node(
                &mut self.nodes,
                modifiers,
                type_parameters,
                Some(parameters),
                return_type,
            )
        } else {
            self.factory.new_function_type_node(
                &mut self.nodes,
                type_parameters,
                Some(parameters),
                return_type,
            )
        };
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseModifiersForConstructorType() *ast.ModifierList`
    fn parse_modifiers_for_constructor_type(&mut self) -> Option<ModifierList> {
        if self.token == Kind::AbstractKeyword {
            let pos = self.node_pos();
            let modifier = self.factory.new_token(&mut self.nodes, self.token);
            self.next_token();
            self.finish_node(modifier, pos);
            let loc = self.nodes[modifier].loc;
            return Some(self.new_modifier_list(loc, vec![modifier]));
        }
        None
    }

    /// `func (p *Parser) nextTokenIsNewKeyword() bool`
    fn next_token_is_new_keyword(&mut self) -> bool {
        self.next_token() == Kind::NewKeyword
    }

    /// `func (p *Parser) nextIsUnambiguouslyStartOfFunctionType() bool`
    fn next_is_unambiguously_start_of_function_type(&mut self) -> bool {
        self.next_token();
        if self.token == Kind::CloseParenToken || self.token == Kind::DotDotDotToken {
            // ( )
            // ( ...
            return true;
        }
        if self.skip_parameter_start() {
            // We successfully skipped modifiers (if any) and an identifier or binding pattern,
            // now see if we have something that indicates a parameter declaration
            if matches!(
                self.token,
                Kind::ColonToken | Kind::CommaToken | Kind::QuestionToken | Kind::EqualsToken
            ) {
                // ( xxx :
                // ( xxx ,
                // ( xxx ?
                // ( xxx =
                return true;
            }
            if self.token == Kind::CloseParenToken
                && self.next_token() == Kind::EqualsGreaterThanToken
            {
                // ( xxx ) =>
                return true;
            }
        }
        false
    }

    /// `func (p *Parser) skipParameterStart() bool`
    fn skip_parameter_start(&mut self) -> bool {
        if self.token.is_modifier_kind() {
            // Skip modifiers
            self.parse_modifiers();
        }
        self.parse_optional(Kind::DotDotDotToken);
        if self.is_identifier() || self.token == Kind::ThisKeyword {
            self.next_token();
            return true;
        }
        if self.token == Kind::OpenBracketToken || self.token == Kind::OpenBraceToken {
            // Return true if we can parse an array or object binding pattern with no errors
            let previous_error_count = self.diagnostics.len();
            self.parse_identifier_or_pattern();
            return previous_error_count == self.diagnostics.len();
        }
        false
    }
}

// ---------------------------------------------------------------------------
// Modifiers and decorator helpers (Go: `parseModifiers` onward)
// ---------------------------------------------------------------------------

impl<'a> Parser<'a> {
    /// `func (p *Parser) parseModifiers() *ast.ModifierList`
    pub fn parse_modifiers(&mut self) -> Option<ModifierList> {
        self.parse_modifiers_ex(false, false, false)
    }

    /// `func (p *Parser) parseModifiersEx(allowDecorators, permitConstAsModifier, stopOnStartOfClassStaticBlock)`
    pub fn parse_modifiers_ex(
        &mut self,
        allow_decorators: bool,
        permit_const_as_modifier: bool,
        stop_on_start_of_class_static_block: bool,
    ) -> Option<ModifierList> {
        let mut has_leading_modifier = false;
        let mut has_trailing_decorator = false;
        let mut has_trailing_modifier = false;
        let mut has_static_modifier = false;
        // Decorators should be contiguous in a list of modifiers but can potentially appear in two places (i.e., `[...leadingDecorators, ...leadingModifiers, ...trailingDecorators, ...trailingModifiers]`).
        // The leading modifiers *should* only contain `export` and `default` when trailingDecorators are present, but we'll handle errors for any other leading modifiers in the checker.
        // It is illegal to have both leadingDecorators and trailingDecorators, but we will report that as a grammar check in the checker.
        // parse leading decorators
        let pos = self.node_pos();
        let mut list: Vec<NodeId> = Vec::with_capacity(16);
        loop {
            if allow_decorators && self.token == Kind::AtToken && !has_trailing_modifier {
                let decorator = self.parse_decorator();
                list.push(decorator);
                if has_leading_modifier {
                    has_trailing_decorator = true;
                }
            } else {
                let modifier = self.try_parse_modifier(
                    has_static_modifier,
                    permit_const_as_modifier,
                    stop_on_start_of_class_static_block,
                );
                let Some(modifier) = modifier else {
                    break;
                };
                if self.nodes[modifier].kind == Kind::StaticKeyword {
                    has_static_modifier = true;
                }
                list.push(modifier);
                if has_trailing_decorator {
                    has_trailing_modifier = true;
                } else {
                    has_leading_modifier = true;
                }
            }
        }
        if !list.is_empty() {
            return Some(
                self.new_modifier_list(TextRange::new(pos, self.node_pos()), list),
            );
        }
        None
    }

    /// `func (p *Parser) parseDecorator() *ast.Node`
    fn parse_decorator(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::AtToken);
        let expression = self.do_in_context(
            NodeFlags::DECORATOR_CONTEXT,
            true,
            Self::parse_decorator_expression,
        );
        self.finish_node(
            self.factory
                .new_decorator(&mut self.nodes, Some(expression)),
            pos,
        )
    }

    /// `func (p *Parser) parseDecoratorExpression() *ast.Expression`
    fn parse_decorator_expression(&mut self) -> NodeId {
        if self.in_await_context() && self.token == Kind::AwaitKeyword {
            // `@await` is disallowed in an [Await] context, but can cause parsing to go off the rails
            // This simply parses the missing identifier and moves on.
            let pos = self.node_pos();
            let await_expression = self.parse_identifier_with_diagnostic(
                Some(&diagnostics::Expression_expected),
                None,
            );
            self.next_token();
            let member_expression = self.parse_member_expression_rest(
                pos,
                await_expression,
                true, /*allowOptionalChain*/
            );
            return self.parse_call_expression_rest(pos, member_expression);
        }
        self.parse_left_hand_side_expression_or_higher()
    }

    /// `func (p *Parser) tryParseModifier(hasSeenStaticModifier, permitConstAsModifier, stopOnStartOfClassStaticBlock)`
    fn try_parse_modifier(
        &mut self,
        has_seen_static_modifier: bool,
        permit_const_as_modifier: bool,
        stop_on_start_of_class_static_block: bool,
    ) -> Option<NodeId> {
        let pos = self.node_pos();
        let kind = self.token;
        if self.token == Kind::ConstKeyword && permit_const_as_modifier {
            // We need to ensure that any subsequent modifiers appear on the same line
            // so that when 'const' is a standalone declaration, we don't issue an error.
            if !self.look_ahead(Self::next_token_is_on_same_line_and_can_follow_modifier) {
                return None;
            } else {
                self.next_token();
            }
        } else if stop_on_start_of_class_static_block
            && self.token == Kind::StaticKeyword
            && self.look_ahead(Self::next_token_is_open_brace)
        {
            return None;
        } else if has_seen_static_modifier && self.token == Kind::StaticKeyword {
            return None;
        } else {
            if !self.parse_any_contextual_modifier() {
                return None;
            }
        }
        Some(self.finish_node(
            self.factory.new_token(&mut self.nodes, kind),
            pos,
        ))
    }

    /// `func (p *Parser) parseContextualModifier(t) bool`
    pub fn parse_contextual_modifier(&mut self, t: Kind) -> bool {
        let state = self.mark();
        if self.token == t && self.next_token_can_follow_modifier() {
            return true;
        }
        self.rewind(state);
        false
    }

    /// `func (p *Parser) parseAnyContextualModifier() bool`
    fn parse_any_contextual_modifier(&mut self) -> bool {
        let state = self.mark();
        if self.token.is_modifier_kind() && self.next_token_can_follow_modifier() {
            return true;
        }
        self.rewind(state);
        false
    }

    /// `func (p *Parser) nextTokenCanFollowModifier() bool`
    fn next_token_can_follow_modifier(&mut self) -> bool {
        match self.token {
            Kind::ConstKeyword => {
                // 'const' is only a modifier if followed by 'enum'.
                self.next_token() == Kind::EnumKeyword
            }
            Kind::ExportKeyword => {
                self.next_token();
                if self.token == Kind::DefaultKeyword {
                    return self.look_ahead(Self::next_token_can_follow_default_keyword);
                }
                if self.token == Kind::TypeKeyword {
                    return self.look_ahead(Self::next_token_can_follow_export_modifier);
                }
                self.can_follow_export_modifier()
            }
            Kind::DefaultKeyword => self.next_token_can_follow_default_keyword(),
            Kind::StaticKeyword => {
                self.next_token();
                self.can_follow_modifier()
            }
            Kind::GetKeyword | Kind::SetKeyword => {
                self.next_token();
                self.can_follow_get_or_set_keyword()
            }
            _ => self.next_token_is_on_same_line_and_can_follow_modifier(),
        }
    }

    /// `func (p *Parser) nextTokenCanFollowDefaultKeyword() bool`
    fn next_token_can_follow_default_keyword(&mut self) -> bool {
        match self.next_token() {
            Kind::ClassKeyword
            | Kind::FunctionKeyword
            | Kind::InterfaceKeyword
            | Kind::AtToken => return true,
            Kind::AbstractKeyword => {
                return self.look_ahead(Self::next_token_is_class_keyword_on_same_line);
            }
            Kind::AsyncKeyword => {
                return self.look_ahead(Self::next_token_is_function_keyword_on_same_line);
            }
            _ => {}
        }
        false
    }

    /// `func (p *Parser) nextTokenIsIdentifierOrKeyword() bool`
    fn next_token_is_identifier_or_keyword(&mut self) -> bool {
        token_is_identifier_or_keyword(self.next_token())
    }

    /// `func (p *Parser) nextTokenIsIdentifierOrKeywordOrGreaterThan() bool`
    fn next_token_is_identifier_or_keyword_or_greater_than(&mut self) -> bool {
        token_is_identifier_or_keyword_or_greater_than(self.next_token())
    }

    /// `func (p *Parser) nextTokenIsIdentifierOrKeywordOnSameLine() bool`
    fn next_token_is_identifier_or_keyword_on_same_line(&mut self) -> bool {
        self.next_token_is_identifier_or_keyword() && !self.has_preceding_line_break()
    }

    /// `func (p *Parser) nextTokenIsIdentifierOrKeywordOrLiteralOnSameLine() bool`
    fn next_token_is_identifier_or_keyword_or_literal_on_same_line(&mut self) -> bool {
        (self.next_token_is_identifier_or_keyword()
            || self.token == Kind::NumericLiteral
            || self.token == Kind::BigIntLiteral
            || self.token == Kind::StringLiteral)
            && !self.has_preceding_line_break()
    }

    /// `func (p *Parser) nextTokenIsClassKeywordOnSameLine() bool`
    fn next_token_is_class_keyword_on_same_line(&mut self) -> bool {
        self.next_token() == Kind::ClassKeyword && !self.has_preceding_line_break()
    }

    /// `func (p *Parser) nextTokenIsFunctionKeywordOnSameLine() bool`
    fn next_token_is_function_keyword_on_same_line(&mut self) -> bool {
        self.next_token() == Kind::FunctionKeyword && !self.has_preceding_line_break()
    }

    /// `func (p *Parser) nextTokenCanFollowExportModifier() bool`
    fn next_token_can_follow_export_modifier(&mut self) -> bool {
        self.next_token();
        self.can_follow_export_modifier()
    }

    /// `func (p *Parser) canFollowExportModifier() bool`
    fn can_follow_export_modifier(&mut self) -> bool {
        self.token == Kind::AtToken
            || self.token != Kind::AsteriskToken
                && self.token != Kind::AsKeyword
                && self.token != Kind::OpenBraceToken
                && self.can_follow_modifier()
    }

    /// `func (p *Parser) canFollowModifier() bool`
    fn can_follow_modifier(&mut self) -> bool {
        self.token == Kind::OpenBracketToken
            || self.token == Kind::OpenBraceToken
            || self.token == Kind::AsteriskToken
            || self.token == Kind::DotDotDotToken
            || self.is_literal_property_name()
    }

    /// `func (p *Parser) canFollowGetOrSetKeyword() bool`
    fn can_follow_get_or_set_keyword(&mut self) -> bool {
        self.token == Kind::OpenBracketToken || self.is_literal_property_name()
    }

    /// `func (p *Parser) nextTokenIsOnSameLineAndCanFollowModifier() bool`
    fn next_token_is_on_same_line_and_can_follow_modifier(&mut self) -> bool {
        self.next_token();
        if self.has_preceding_line_break() {
            return false;
        }
        self.can_follow_modifier()
    }

    /// `func (p *Parser) nextTokenIsOpenBrace() bool`
    fn next_token_is_open_brace(&mut self) -> bool {
        self.next_token() == Kind::OpenBraceToken
    }
}

// ---------------------------------------------------------------------------
// Expressions (Go: `parseExpression` onward)
// ---------------------------------------------------------------------------

impl<'a> Parser<'a> {
    /// `func (p *Parser) parseExpression() *ast.Expression`
    pub fn parse_expression(&mut self) -> NodeId {
        // Expression[in]:
        //      AssignmentExpression[in]
        //      Expression[in] , AssignmentExpression[in]

        // clear the decorator context when parsing Expression, as it should be unambiguous when parsing a decorator
        let save_context_flags = self.context_flags;
        self.context_flags &= !NodeFlags::DECORATOR_CONTEXT;
        let pos = self.node_pos();
        let mut expr = self.parse_assignment_expression_or_higher();
        loop {
            let operator_token = self.parse_optional_token(Kind::CommaToken);
            let Some(operator_token) = operator_token else {
                break;
            };
            let right = self.parse_assignment_expression_or_higher();
            expr = self.make_binary_expression(expr, operator_token, right, pos);
        }
        self.context_flags = save_context_flags;
        expr
    }

    /// `func (p *Parser) parseExpressionAllowIn() *ast.Expression`
    fn parse_expression_allow_in(&mut self) -> NodeId {
        self.do_in_context(NodeFlags::DISALLOW_IN_CONTEXT, false, Self::parse_expression)
    }

    /// `func (p *Parser) parseAssignmentExpressionOrHigher() *ast.Expression`
    pub fn parse_assignment_expression_or_higher(&mut self) -> NodeId {
        self.parse_assignment_expression_or_higher_worker(
            true, /*allowReturnTypeInArrowFunction*/
        )
    }

    /// `func (p *Parser) parseAssignmentExpressionOrHigherWorker(allowReturnTypeInArrowFunction)`
    fn parse_assignment_expression_or_higher_worker(
        &mut self,
        allow_return_type_in_arrow_function: bool,
    ) -> NodeId {
        //  AssignmentExpression[in,yield]:
        //      1) ConditionalExpression[?in,?yield]
        //      2) LeftHandSideExpression = AssignmentExpression[?in,?yield]
        //      3) LeftHandSideExpression AssignmentOperator AssignmentExpression[?in,?yield]
        //      4) ArrowFunctionExpression[?in,?yield]
        //      5) AsyncArrowFunctionExpression[in,yield,await]
        //      6) [+Yield] YieldExpression[?In]
        //
        // Note: for ease of implementation we treat productions '2' and '3' as the same thing.
        // (i.e. they're both BinaryExpressions with an assignment operator in it).
        // First, do the simple check if we have a YieldExpression (production '6').
        if self.is_yield_expression() {
            return self.parse_yield_expression();
        }
        // Then, check if we have an arrow function (production '4' and '5') that starts with a parenthesized
        // parameter list or is an async arrow function.
        // AsyncArrowFunctionExpression:
        //      1) async[no LineTerminator here]AsyncArrowBindingIdentifier[?Yield][no LineTerminator here]=>AsyncConciseBody[?In]
        //      2) CoverCallExpressionAndAsyncArrowHead[?Yield, ?Await][no LineTerminator here]=>AsyncConciseBody[?In]
        // Production (1) of AsyncArrowFunctionExpression is parsed in "tryParseAsyncSimpleArrowFunctionExpression".
        // And production (2) is parsed in "tryParseParenthesizedArrowFunctionExpression".
        //
        // If we do successfully parse arrow-function, we must *not* recurse for productions 1, 2 or 3. An ArrowFunction is
        // not a LeftHandSideExpression, nor does it start a ConditionalExpression.  So we are done
        // with AssignmentExpression if we see one.
        if let Some(arrow_expression) =
            self.try_parse_parenthesized_arrow_function_expression(
                allow_return_type_in_arrow_function,
            )
        {
            return arrow_expression;
        }
        if let Some(arrow_expression) =
            self.try_parse_async_simple_arrow_function_expression(
                allow_return_type_in_arrow_function,
            )
        {
            return arrow_expression;
        }
        // Now try to see if we're in production '1', '2' or '3'.  A conditional expression can
        // start with a LogicalOrExpression, while the assignment productions can only start with
        // LeftHandSideExpressions.
        //
        // So, first, we try to just parse out a BinaryExpression.  If we get something that is a
        // LeftHandSide or higher, then we can try to parse out the assignment expression part.
        // Otherwise, we try to parse out the conditional expression bit.  We want to allow any
        // binary expression here, so we pass in the 'lowest' precedence here so that it matches
        // and consumes anything.
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let expr = self.parse_binary_expression_or_higher(OperatorPrecedence::LOWEST);
        // To avoid a look-ahead, we did not handle the case of an arrow function with a single un-parenthesized
        // parameter ('x => ...') above. We handle it here by checking if the parsed expression was a single
        // identifier and the current token is an arrow.
        if self.nodes[expr].kind == Kind::Identifier
            && self.token == Kind::EqualsGreaterThanToken
        {
            return self.parse_simple_arrow_function_expression(
                pos,
                expr,
                allow_return_type_in_arrow_function,
                jsdoc,
                None, /*asyncModifier*/
            );
        }
        // Now see if we might be in cases '2' or '3'.
        // If the expression was a LHS expression, and we have an assignment operator, then
        // we're in '2' or '3'. Consume the assignment and return.
        //
        // Note: we call reScanGreaterToken so that we get an appropriately merged token
        // for cases like `> > =` becoming `>>=`
        if is_left_hand_side_expression(&self.nodes[expr], &self.nodes)
            && self.rescan_greater_than_token().is_assignment_operator()
        {
            let operator_token = self.parse_token_node();
            let right = self.parse_assignment_expression_or_higher_worker(
                allow_return_type_in_arrow_function,
            );
            return self.make_binary_expression(expr, operator_token, right, pos);
        }
        // It wasn't an assignment or a lambda.  This is a conditional expression:
        self.parse_conditional_expression_rest(expr, pos, allow_return_type_in_arrow_function)
    }

    /// `func (p *Parser) isYieldExpression() bool`
    fn is_yield_expression(&mut self) -> bool {
        if self.token == Kind::YieldKeyword {
            // If we have a 'yield' keyword, and this is a context where yield expressions are
            // allowed, then definitely parse out a yield expression.
            if self.in_yield_context() {
                return true;
            }

            // We're in a context where 'yield expr' is not allowed.  However, if we can
            // definitely tell that the user was trying to parse a 'yield expr' and not
            // just a normal expr that start with a 'yield' identifier, then parse out
            // a 'yield expr'.  We can then report an error later that they are only
            // allowed in generator expressions.
            //
            // for example, if we see 'yield(foo)', then we'll have to treat that as an
            // invocation expression of something called 'yield'.  However, if we have
            // 'yield foo' then that is not legal as a normal expression, so we can
            // definitely recognize this as a yield expression.
            //
            // for now we just check if the next token is an identifier.  More heuristics
            // can be added here later as necessary.  We just need to make sure that we
            // don't accidentally consume something legal.
            return self.look_ahead(
                Self::next_token_is_identifier_or_keyword_or_literal_on_same_line,
            );
        }
        false
    }

    /// `func (p *Parser) parseYieldExpression() *ast.Node`
    fn parse_yield_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        // YieldExpression[In] :
        //      yield
        //      yield [no LineTerminator here] [Lexical goal InputElementRegExp]AssignmentExpression[?In, Yield]
        //      yield [no LineTerminator here] * [Lexical goal InputElementRegExp]AssignmentExpression[?In, Yield]
        self.next_token();
        let result = if !self.has_preceding_line_break()
            && (self.token == Kind::AsteriskToken || self.is_start_of_expression())
        {
            let asterisk_token = self.parse_optional_token(Kind::AsteriskToken);
            let expression = self.parse_assignment_expression_or_higher();
            self.factory.new_yield_expression(
                &mut self.nodes,
                asterisk_token,
                Some(expression),
            )
        } else {
            // if the next token is not on the same line as yield.  or we don't have an '*' or
            // the start of an expression, then this is just a simple "yield" expression.
            self.factory
                .new_yield_expression(&mut self.nodes, None, None)
        };
        self.finish_node(result, pos)
    }

    /// `func (p *Parser) isParenthesizedArrowFunctionExpression() core.Tristate`
    fn is_parenthesized_arrow_function_expression(&mut self) -> Tristate {
        if self.token == Kind::OpenParenToken
            || self.token == Kind::LessThanToken
            || self.token == Kind::AsyncKeyword
        {
            let state = self.mark();
            let result = self.next_is_parenthesized_arrow_function_expression();
            self.rewind(state);
            return result;
        }
        if self.token == Kind::EqualsGreaterThanToken {
            // ERROR RECOVERY TWEAK:
            // If we see a standalone => try to parse it as an arrow function expression as that's
            // likely what the user intended to write.
            return TS_TRUE;
        }
        // Definitely not a parenthesized arrow function.
        TS_FALSE
    }

    /// `func (p *Parser) nextIsParenthesizedArrowFunctionExpression() core.Tristate`
    fn next_is_parenthesized_arrow_function_expression(&mut self) -> Tristate {
        if self.token == Kind::AsyncKeyword {
            self.next_token();
            if self.has_preceding_line_break() {
                return TS_FALSE;
            }
            if self.token != Kind::OpenParenToken && self.token != Kind::LessThanToken {
                return TS_FALSE;
            }
        }
        let first = self.token;
        let second = self.next_token();
        if first == Kind::OpenParenToken {
            if second == Kind::CloseParenToken {
                // Simple cases: "() =>", "(): ", and "() {".
                // This is an arrow function with no parameters.
                // The last one is not actually an arrow function,
                // but this is probably what the user intended.
                let third = self.next_token();
                match third {
                    Kind::EqualsGreaterThanToken
                    | Kind::ColonToken
                    | Kind::OpenBraceToken => {
                        return TS_TRUE;
                    }
                    _ => {}
                }
                return TS_FALSE;
            }
            // If encounter "([" or "({", this could be the start of a binding pattern.
            // Examples:
            //      ([ x ]) => { }
            //      ({ x }) => { }
            //      ([ x ])
            //      ({ x })
            if second == Kind::OpenBracketToken || second == Kind::OpenBraceToken {
                return TS_UNKNOWN;
            }
            // Simple case: "(..."
            // This is an arrow function with a rest parameter.
            if second == Kind::DotDotDotToken {
                return TS_TRUE;
            }
            // Check for "(xxx yyy", where xxx is a modifier and yyy is an identifier. This
            // isn't actually allowed, but we want to treat it as a lambda so we can provide
            // a good error message.
            if second.is_modifier_kind()
                && second != Kind::AsyncKeyword
                && self.look_ahead(Self::next_token_is_identifier)
            {
                if self.next_token() == Kind::AsKeyword {
                    // https://github.com/microsoft/TypeScript/issues/44466
                    return TS_FALSE;
                }
                return TS_TRUE;
            }
            // If we had "(" followed by something that's not an identifier,
            // then this definitely doesn't look like a lambda.  "this" is not
            // valid, but we want to parse it and then give a semantic error.
            if !self.is_identifier() && second != Kind::ThisKeyword {
                return TS_FALSE;
            }
            match self.next_token() {
                Kind::ColonToken => {
                    // If we have something like "(a:", then we must have a
                    // type-annotated parameter in an arrow function expression.
                    return TS_TRUE;
                }
                Kind::QuestionToken => {
                    self.next_token();
                    // If we have "(a?:" or "(a?," or "(a?=" or "(a?)" then it is definitely a lambda.
                    if self.token == Kind::ColonToken
                        || self.token == Kind::CommaToken
                        || self.token == Kind::EqualsToken
                        || self.token == Kind::CloseParenToken
                    {
                        return TS_TRUE;
                    }
                    // Otherwise it is definitely not a lambda.
                    return TS_FALSE;
                }
                Kind::CommaToken | Kind::EqualsToken | Kind::CloseParenToken => {
                    // If we have "(a," or "(a=" or "(a)" this *could* be an arrow function
                    return TS_UNKNOWN;
                }
                _ => {}
            }
            // It is definitely not an arrow function
            TS_FALSE
        } else {
            tsc_debug::assert_!(first == Kind::LessThanToken, "expected first token to be '<'");
            // If we have "<" not followed by an identifier,
            // then this definitely is not an arrow function.
            if !self.is_identifier() && self.token != Kind::ConstKeyword {
                return TS_FALSE;
            }
            // JSX overrides
            if self.language_variant == LanguageVariant::Jsx {
                let is_arrow_function_in_jsx = self.look_ahead(|p| {
                    p.parse_optional(Kind::ConstKeyword);
                    let third = p.next_token();
                    if third == Kind::ExtendsKeyword {
                        let fourth = p.next_token();
                        match fourth {
                            Kind::EqualsToken
                            | Kind::GreaterThanToken
                            | Kind::SlashToken => {
                                return false;
                            }
                            _ => {}
                        }
                        return true;
                    } else if third == Kind::CommaToken || third == Kind::EqualsToken {
                        return true;
                    }
                    false
                });
                if is_arrow_function_in_jsx {
                    return TS_TRUE;
                }
                return TS_FALSE;
            }
            // This *could* be a parenthesized arrow function.
            TS_UNKNOWN
        }
    }

    /// `func (p *Parser) tryParseParenthesizedArrowFunctionExpression(allowReturnTypeInArrowFunction)`
    fn try_parse_parenthesized_arrow_function_expression(
        &mut self,
        allow_return_type_in_arrow_function: bool,
    ) -> Option<NodeId> {
        let tristate = self.is_parenthesized_arrow_function_expression();
        if tristate == TS_FALSE {
            // It's definitely not a parenthesized arrow function expression.
            return None;
        }
        // If we definitely have an arrow function, then we can just parse one, not requiring a
        // following => or { token. Otherwise, we *might* have an arrow function.  Try to parse
        // it out, but don't allow any ambiguity, and return 'undefined' if this could be an
        // expression instead.
        if tristate == TS_TRUE {
            return self.parse_parenthesized_arrow_function_expression(
                true, /*allowAmbiguity*/
                allow_return_type_in_arrow_function,
            );
        }
        let state = self.mark();
        let result = self.parse_possible_parenthesized_arrow_function_expression(
            allow_return_type_in_arrow_function,
        );
        if result.is_none() {
            self.rewind(state);
        }
        result
    }

    /// `func (p *Parser) parseParenthesizedArrowFunctionExpression(allowAmbiguity, allowReturnTypeInArrowFunction)`
    fn parse_parenthesized_arrow_function_expression(
        &mut self,
        allow_ambiguity: bool,
        allow_return_type_in_arrow_function: bool,
    ) -> Option<NodeId> {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers_for_arrow_function();
        let is_async = modifier_list_has_async(modifiers.as_ref(), &self.nodes);
        let signature_flags = if is_async {
            ParseFlags::AWAIT
        } else {
            ParseFlags::NONE
        };
        // Arrow functions are never generators.
        //
        // If we're speculatively parsing a signature for a parenthesized arrow function, then
        // we have to have a complete parameter list.  Otherwise we might see something like
        // a => (b => c)
        // And think that "(b =>" was actually a parenthesized arrow function with a missing
        // close paren.
        let type_parameters = self.parse_type_parameters();
        let parameters: NodeList;
        if !self.parse_expected(Kind::OpenParenToken) {
            if !allow_ambiguity {
                return None;
            }
            parameters = self.create_missing_list();
        } else {
            if !allow_ambiguity {
                let maybe_parameters =
                    self.parse_parameters_worker(signature_flags, allow_ambiguity);
                parameters = maybe_parameters?;
            } else {
                parameters = self
                    .parse_parameters_worker(signature_flags, allow_ambiguity)
                    .unwrap_or_else(|| self.create_missing_list());
            }
            if !self.parse_expected(Kind::CloseParenToken) && !allow_ambiguity {
                return None;
            }
        }
        let has_return_colon = self.token == Kind::ColonToken;
        let return_type = self.parse_return_type(Kind::ColonToken /*isType*/, false);
        if return_type.is_some()
            && !allow_ambiguity
            && type_has_arrow_function_blocking_parse_error(
                return_type.unwrap(),
                &self.nodes,
            )
        {
            return None;
        }
        // Parsing a signature isn't enough.
        // Parenthesized arrow signatures often look like other valid expressions.
        // For instance:
        //  - "(x = 10)" is an assignment expression parsed as a signature with a default parameter value.
        //  - "(x,y)" is a comma expression parsed as a signature with two parameters that
        //    have no type annotations or default values.
        //  - "(a ? b : c)" is a conditional expression, etc.
        // So we parse the body as an expression and check that it conforms to the arrow function
        // grammar. If it doesn't, we have to bail out and re-parse as if it were an expression.
        if !allow_ambiguity
            && !matches!(
                self.token,
                Kind::EqualsGreaterThanToken | Kind::OpenBraceToken | Kind::ColonToken
            )
        {
            return None;
        }
        // If we have an arrow function, we need to check if the parameters are valid as
        // arrow function parameters.
        if allow_ambiguity
            && !matches!(self.token, Kind::EqualsGreaterThanToken | Kind::OpenBraceToken)
        {
            return None;
        }
        // Go on to parse the arrow function assuming no further issues.
        let last_token = self.token;
        let equals_greater_than_token =
            self.parse_expected_token(Kind::EqualsGreaterThanToken);
        let body = if last_token == Kind::EqualsGreaterThanToken
            || last_token == Kind::OpenBraceToken
        {
            self.parse_arrow_function_expression_body(
                is_async,
                allow_return_type_in_arrow_function,
            )
        } else {
            self.parse_identifier()
        };
        // Given:
        //     x ? y => ({ y }) : z => ({ z })
        // We try to parse the body of the first arrow function by looking at:
        //     ({ y }) : z => ({ z })
        // This is a valid arrow function with "z" as the return type.
        //
        // But, if we're in the true side of a conditional expression, this colon
        // terminates the expression, so we cannot allow a return type if we aren't
        // certain whether or not the preceding text was parsed as a parameter list.
        //
        // For example,
        //     a() ? (b: number, c?: string): void => d() : e
        // is determined by isParenthesizedArrowFunctionExpression to unambiguously
        // be an arrow expression, so we allow a return type.
        if !allow_return_type_in_arrow_function && has_return_colon {
            // However, if the arrow function we were able to parse is followed by another colon
            // as in:
            //     a ? (x): string => x : null
            // Then allow the arrow function, and treat the second colon as terminating
            // the conditional expression. It's okay to do this because this code would
            // be a syntax error in JavaScript (as the second colon shouldn't be there).
            if self.token != Kind::ColonToken {
                return None;
            }
        }
        let result = self.finish_node(
            self.factory.new_arrow_function(
                &mut self.nodes,
                modifiers,
                type_parameters,
                Some(parameters),
                return_type,
                None, /*fullSignature*/
                Some(equals_greater_than_token),
                Some(body),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        Some(result)
    }

    /// `func (p *Parser) parseModifiersForArrowFunction() *ast.ModifierList`
    fn parse_modifiers_for_arrow_function(&mut self) -> Option<ModifierList> {
        if self.token == Kind::AsyncKeyword {
            let pos = self.node_pos();
            self.next_token();
            let modifier = self.finish_node(
                self.factory
                    .new_token(&mut self.nodes, Kind::AsyncKeyword),
                pos,
            );
            let loc = self.nodes[modifier].loc;
            return Some(self.new_modifier_list(loc, vec![modifier]));
        }
        None
    }

    /// `func (p *Parser) parseArrowFunctionExpressionBody(isAsync, allowReturnTypeInArrowFunction)`
    fn parse_arrow_function_expression_body(
        &mut self,
        is_async: bool,
        allow_return_type_in_arrow_function: bool,
    ) -> NodeId {
        if self.token == Kind::OpenBraceToken {
            return self.parse_function_block(
                if is_async {
                    ParseFlags::AWAIT
                } else {
                    ParseFlags::NONE
                },
                None, /*diagnosticMessage*/
            );
        }
        if self.token != Kind::SemicolonToken
            && self.token != Kind::FunctionKeyword
            && self.token != Kind::ClassKeyword
            && self.is_start_of_statement()
            && !self.is_start_of_expression_statement()
        {
            // Check if we got a plain statement (i.e. no expression-statements, no function/class expressions/declarations)
            //
            // Here we try to recover from a potential error situation in the case where the
            // user meant to supply a block. For example, if the user wrote:
            //
            //  a =>
            //      let v = 0;
            //  }
            //
            // they may be missing an open brace.  Check to see if that's the case so we can
            // try to recover better.  If we don't do this, then the next close curly we see may end
            // up preemptively closing the containing construct.
            //
            // Note: even when 'IgnoreMissingOpenBrace' is passed, parseBody will still error.
            return self.parse_function_block(
                ParseFlags::IGNORE_MISSING_OPEN_BRACE
                    | if is_async {
                        ParseFlags::AWAIT
                    } else {
                        ParseFlags::NONE
                    },
                None, /*diagnosticMessage*/
            );
        }
        let save_context_flags = self.context_flags;
        self.set_context_flags(NodeFlags::AWAIT_CONTEXT, is_async);
        self.set_context_flags(NodeFlags::YIELD_CONTEXT, false);
        let node = self.parse_assignment_expression_or_higher_worker(
            allow_return_type_in_arrow_function,
        );
        self.context_flags = save_context_flags;
        node
    }

    /// `func (p *Parser) isStartOfExpressionStatement() bool`
    fn is_start_of_expression_statement(&mut self) -> bool {
        // As per the grammar, none of '{' or 'function' or 'class' can start an expression statement.
        self.token != Kind::OpenBraceToken
            && self.token != Kind::FunctionKeyword
            && self.token != Kind::ClassKeyword
            && self.token != Kind::AtToken
            && self.is_start_of_expression()
    }

    /// `func (p *Parser) parsePossibleParenthesizedArrowFunctionExpression(allowReturnTypeInArrowFunction)`
    fn parse_possible_parenthesized_arrow_function_expression(
        &mut self,
        allow_return_type_in_arrow_function: bool,
    ) -> Option<NodeId> {
        let token_pos = self.scanner.token_start();
        if self.not_parenthesized_arrow.has(&token_pos) {
            return None;
        }
        let result = self.parse_parenthesized_arrow_function_expression(
            false, /*allowAmbiguity*/
            allow_return_type_in_arrow_function,
        );
        if result.is_none() {
            self.not_parenthesized_arrow.add(token_pos);
        }
        result
    }

    /// `func (p *Parser) tryParseAsyncSimpleArrowFunctionExpression(allowReturnTypeInArrowFunction)`
    fn try_parse_async_simple_arrow_function_expression(
        &mut self,
        allow_return_type_in_arrow_function: bool,
    ) -> Option<NodeId> {
        // We do a check here so that we won't be doing unnecessarily call to "lookAhead"
        if self.token == Kind::AsyncKeyword
            && self.look_ahead(Self::next_is_un_parenthesized_async_arrow_function)
        {
            let pos = self.node_pos();
            let jsdoc = self.jsdoc_scanner_info();
            let async_modifier = self.parse_modifiers_for_arrow_function();
            let expr = self.parse_binary_expression_or_higher(OperatorPrecedence::LOWEST);
            return Some(self.parse_simple_arrow_function_expression(
                pos,
                expr,
                allow_return_type_in_arrow_function,
                jsdoc,
                async_modifier,
            ));
        }
        None
    }

    /// `func (p *Parser) nextIsUnParenthesizedAsyncArrowFunction() bool`
    fn next_is_un_parenthesized_async_arrow_function(&mut self) -> bool {
        // AsyncArrowFunctionExpression:
        //      1) async[no LineTerminator here]AsyncArrowBindingIdentifier[?Yield][no LineTerminator here]=>AsyncConciseBody[?In]
        //      2) CoverCallExpressionAndAsyncArrowHead[?Yield, ?Await][no LineTerminator here]=>AsyncConciseBody[?In]
        if self.token == Kind::AsyncKeyword {
            self.next_token();
            // If the "async" is followed by "=>" token then it is not a beginning of an async arrow-function
            // but instead a simple arrow-function which will be parsed inside "parseAssignmentExpressionOrHigher"
            if self.has_preceding_line_break()
                || self.token == Kind::EqualsGreaterThanToken
            {
                return false;
            }
            // Check for un-parenthesized AsyncArrowFunction
            if !self.is_identifier() {
                return false;
            }
            self.next_token_without_check();
            return !self.has_preceding_line_break()
                && self.token == Kind::EqualsGreaterThanToken;
        }
        false
    }

    /// `func (p *Parser) parseSimpleArrowFunctionExpression(...)`
    fn parse_simple_arrow_function_expression(
        &mut self,
        pos: i32,
        identifier: NodeId,
        allow_return_type_in_arrow_function: bool,
        jsdoc: JSDocScannerInfo,
        async_modifier: Option<ModifierList>,
    ) -> NodeId {
        tsc_debug::assert_!(self.token == Kind::EqualsGreaterThanToken, "parseSimpleArrowFunctionExpression should only have been called if we had a =>");
        let id_pos = self.nodes[identifier].pos();
        let parameter = self.finish_node(
            self.factory.new_parameter_declaration(
                &mut self.nodes,
                None, /*modifiers*/
                None, /*dotDotDotToken*/
                Some(identifier),
                None, /*questionToken*/
                None, /*typeNode*/
                None, /*initializer*/
            ),
            id_pos,
        );
        let parameters =
            self.new_node_list(self.nodes[parameter].loc, vec![parameter]);
        let equals_greater_than_token =
            self.parse_expected_token(Kind::EqualsGreaterThanToken);
        let body = self.parse_arrow_function_expression_body(
            async_modifier.is_some(), /*isAsync*/
            allow_return_type_in_arrow_function,
        );
        let result = self.finish_node(
            self.factory.new_arrow_function(
                &mut self.nodes,
                async_modifier,
                None, /*typeParameters*/
                Some(parameters),
                None, /*returnType*/
                None, /*fullSignature*/
                Some(equals_greater_than_token),
                Some(body),
            ),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseConditionalExpressionRest(leftOperand, pos, allowReturnTypeInArrowFunction)`
    fn parse_conditional_expression_rest(
        &mut self,
        left_operand: NodeId,
        pos: i32,
        allow_return_type_in_arrow_function: bool,
    ) -> NodeId {
        // Note: we are passed in an expression which was produced from parseBinaryExpressionOrHigher.
        let question_token = self.parse_optional_token(Kind::QuestionToken);
        let Some(question_token) = question_token else {
            return left_operand;
        };
        // Note: we explicitly 'allowIn' in the whenTrue part of the condition expression, and
        // we do not that for the 'whenFalse' part.
        let save_context_flags = self.context_flags;
        self.set_context_flags(NodeFlags::DISALLOW_IN_CONTEXT, false);
        let true_expression =
            self.parse_assignment_expression_or_higher_worker(false);
        self.context_flags = save_context_flags;
        let colon_token = self.parse_expected_token(Kind::ColonToken);
        let false_expression = if node_is_present(Some(colon_token), &self.nodes) {
            self.parse_assignment_expression_or_higher_worker(
                allow_return_type_in_arrow_function,
            )
        } else {
            self.create_missing_identifier()
        };
        self.finish_node(
            self.factory.new_conditional_expression(
                &mut self.nodes,
                Some(left_operand),
                Some(question_token),
                Some(true_expression),
                Some(colon_token),
                Some(false_expression),
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseBinaryExpressionOrHigher(precedence) *ast.Expression`
    fn parse_binary_expression_or_higher(&mut self, precedence: OperatorPrecedence) -> NodeId {
        let pos = self.node_pos();
        let left_operand = self.parse_unary_expression_or_higher();
        self.parse_binary_expression_rest(precedence, left_operand, pos)
    }

    /// `func (p *Parser) parseBinaryExpressionRest(precedence, leftOperand, pos)`
    fn parse_binary_expression_rest(
        &mut self,
        precedence: OperatorPrecedence,
        left_operand: NodeId,
        pos: i32,
    ) -> NodeId {
        let mut left_operand = left_operand;
        let mut last_operand = left_operand;
        loop {
            // We either have a binary operator here, or we're finished.  We call
            // reScanGreaterToken so that we merge token sequences like > and = into >=
            let operator = self.rescan_greater_than_token();
            let new_precedence = get_binary_operator_precedence(operator);
            // Check the precedence to see if we should "take" this operator
            if !should_consume_binary_operator(operator, new_precedence, precedence) {
                break;
            }
            if operator == Kind::InKeyword && self.in_disallow_in_context() {
                break;
            }
            if operator == Kind::AsKeyword || operator == Kind::SatisfiesKeyword {
                // Make sure we *do* perform ASI for constructs like this:
                //    var x = foo
                //    as (Bar)
                // This should be parsed as an initialized variable, followed
                // by a function call to 'as' with the argument 'Bar'
                if self.has_preceding_line_break() {
                    break;
                } else {
                    self.next_token();
                    // When we have 'a ## b as SomeType $$ c' or 'a ## b satisfies SomeType $$ c', where ## and $$
                    // are binary operators, we want to stop parsing when $$ would bind before ## after erasing the
                    // assertion. See https://github.com/microsoft/TypeScript/issues/63527.
                    let mut last_precedence = OperatorPrecedence::HIGHEST;
                    if is_binary_expression(&self.nodes[last_operand]) {
                        let op = self.nodes[last_operand]
                            .as_binary_expression()
                            .operator_token;
                        last_precedence =
                            get_binary_operator_precedence(self.nodes[op.unwrap()].kind);
                    }
                    let type_node = self.parse_type();
                    left_operand = if operator == Kind::SatisfiesKeyword {
                        self.make_satisfies_expression(left_operand, type_node)
                    } else {
                        self.make_as_expression(left_operand, type_node)
                    };
                    // Stop if the next operator would bind before the last operator when the assertion is erased.
                    let next_operator = self.rescan_greater_than_token();
                    let next_precedence = get_binary_operator_precedence(next_operator);
                    if should_consume_binary_operator(
                        next_operator,
                        next_precedence,
                        last_precedence,
                    ) {
                        break;
                    }
                }
            } else {
                let operator_token = self.parse_token_node();
                let right = self.parse_binary_expression_or_higher(new_precedence);
                left_operand =
                    self.make_binary_expression(left_operand, operator_token, right, pos);
                last_operand = left_operand;
            }
        }
        left_operand
    }

    /// `func (p *Parser) makeSatisfiesExpression(expression, typeNode)`
    fn make_satisfies_expression(&mut self, expression: NodeId, type_node: NodeId) -> NodeId {
        let pos = self.nodes[expression].pos();
        self.check_js_syntax(self.finish_node(
            self.factory.new_satisfies_expression(
                &mut self.nodes,
                Some(expression),
                Some(type_node),
            ),
            pos,
        ))
    }

    /// `func (p *Parser) makeAsExpression(left, right)`
    fn make_as_expression(&mut self, left: NodeId, right: NodeId) -> NodeId {
        let pos = self.nodes[left].pos();
        self.check_js_syntax(self.finish_node(
            self.factory
                .new_as_expression(&mut self.nodes, Some(left), Some(right)),
            pos,
        ))
    }

    /// `func (p *Parser) makeBinaryExpression(left, operatorToken, right, pos)`
    fn make_binary_expression(
        &mut self,
        left: NodeId,
        operator_token: NodeId,
        right: NodeId,
        pos: i32,
    ) -> NodeId {
        self.finish_node(
            self.factory.new_binary_expression(
                &mut self.nodes,
                None, /*modifiers*/
                Some(left),
                None, /*typeNode*/
                Some(operator_token),
                Some(right),
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseUnaryExpressionOrHigher() *ast.Expression`
    fn parse_unary_expression_or_higher(&mut self) -> NodeId {
        // ES7 UpdateExpression:
        //      1) LeftHandSideExpression[?Yield]
        //      2) LeftHandSideExpression[?Yield][no LineTerminator here]++
        //      3) LeftHandSideExpression[?Yield][no LineTerminator here]--
        //      4) ++UnaryExpression[?Yield]
        //      5) --UnaryExpression[?Yield]
        if self.is_update_expression() {
            let pos = self.node_pos();
            let update_expression = self.parse_update_expression();
            if self.token == Kind::AsteriskAsteriskToken {
                let prec = get_binary_operator_precedence(self.token);
                return self.parse_binary_expression_rest(prec, update_expression, pos);
            }
            return update_expression;
        }
        // ES7 UnaryExpression:
        //      1) UpdateExpression[?yield]
        //      2) delete UpdateExpression[?yield]
        //      3) void UpdateExpression[?yield]
        //      4) typeof UpdateExpression[?yield]
        //      5) + UpdateExpression[?yield]
        //      6) - UpdateExpression[?yield]
        //      7) ~ UpdateExpression[?yield]
        //      8) ! UpdateExpression[?yield]
        let unary_operator = self.token;
        let simple_unary_expression = self.parse_simple_unary_expression();
        if self.token == Kind::AsteriskAsteriskToken {
            let pos = scanner::skip_trivia(
                self.source_text,
                self.nodes[simple_unary_expression].pos(),
            );
            let end = self.nodes[simple_unary_expression].end();
            if self.nodes[simple_unary_expression].kind == Kind::TypeAssertionExpression {
                self.parse_error_at(pos, end, &diagnostics::A_type_assertion_expression_is_not_allowed_in_the_left_hand_side_of_an_exponentiation_expression_Consider_enclosing_the_expression_in_parentheses, &[]);
            } else {
                tsc_debug::assert_!(is_keyword_or_punctuation(unary_operator));
                self.parse_error_at(pos, end, &diagnostics::An_unary_expression_with_the_0_operator_is_not_allowed_in_the_left_hand_side_of_an_exponentiation_expression_Consider_enclosing_the_expression_in_parentheses, &[scanner::token_to_string(unary_operator).to_string()]);
            }
        }
        simple_unary_expression
    }

    /// `func (p *Parser) isUpdateExpression() bool`
    fn is_update_expression(&mut self) -> bool {
        match self.token {
            Kind::PlusToken
            | Kind::MinusToken
            | Kind::TildeToken
            | Kind::ExclamationToken
            | Kind::DeleteKeyword
            | Kind::TypeOfKeyword
            | Kind::VoidKeyword
            | Kind::AwaitKeyword => return false,
            Kind::LessThanToken => return self.language_variant == LanguageVariant::Jsx,
            _ => {}
        }
        true
    }

    /// `func (p *Parser) parseUpdateExpression() *ast.Expression`
    fn parse_update_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        if self.token == Kind::PlusPlusToken || self.token == Kind::MinusMinusToken {
            let operator = self.token;
            self.next_token();
            let lhs = self.parse_left_hand_side_expression_or_higher();
            return self.finish_node(
                self.factory.new_prefix_unary_expression(
                    &mut self.nodes,
                    operator,
                    Some(lhs),
                ),
                pos,
            );
        } else if self.language_variant == LanguageVariant::Jsx
            && self.token == Kind::LessThanToken
            && self.look_ahead(Self::next_token_is_identifier_or_keyword_or_greater_than)
        {
            // JSXElement is part of primaryExpression
            return self.parse_jsx_element_or_self_closing_element_or_fragment(
                true, /*inExpressionContext*/
                -1,   /*topInvalidNodePosition*/
                None, /*openingTag*/
                false, /*mustBeUnary*/
            );
        }
        let expression = self.parse_left_hand_side_expression_or_higher();
        if (self.token == Kind::PlusPlusToken || self.token == Kind::MinusMinusToken)
            && !self.has_preceding_line_break()
        {
            let operator = self.token;
            self.next_token();
            return self.finish_node(
                self.factory.new_postfix_unary_expression(
                    &mut self.nodes,
                    Some(expression),
                    operator,
                ),
                pos,
            );
        }
        expression
    }
}

/// `func shouldConsumeBinaryOperator(operator, operatorPrecedence, currentPrecedence) bool` —
/// reports whether an operator binds before the operator represented by
/// `current_precedence`. At equal precedence, only the right-associative
/// exponentiation operator binds first.
fn should_consume_binary_operator(
    operator: Kind,
    operator_precedence: OperatorPrecedence,
    current_precedence: OperatorPrecedence,
) -> bool {
    if operator_precedence > current_precedence {
        return true;
    }
    operator_precedence == current_precedence && operator == Kind::AsteriskAsteriskToken
}

/// `func typeHasArrowFunctionBlockingParseError(node *ast.TypeNode) bool` —
/// true if we should abort parsing an arrow function.
fn type_has_arrow_function_blocking_parse_error(node: NodeId, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::TypeReference => {
            node_is_missing(nodes[node].as_type_reference_node().type_name, nodes)
        }
        Kind::FunctionType | Kind::ConstructorType => {
            let parameters = nodes[node].parameter_list();
            // `node.FunctionLikeData().Parameters` / `node.Type()`
            let type_node = nodes[node].type_();
            is_missing_node_list(parameters)
                || type_node.is_some_and(|t| {
                    type_has_arrow_function_blocking_parse_error(t, nodes)
                })
        }
        Kind::ParenthesizedType => nodes[node]
            .type_()
            .is_some_and(|t| type_has_arrow_function_blocking_parse_error(t, nodes)),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// JSX (Go `parseJsxElementOrSelfClosingElementOrFragment` … `parseJsxClosingFragment`)
// ---------------------------------------------------------------------------

impl<'a> Parser<'a> {
    /// `func (p *Parser) parseJsxElementOrSelfClosingElementOrFragment(inExpressionContext, topInvalidNodePosition, openingTag, mustBeUnary)`
    fn parse_jsx_element_or_self_closing_element_or_fragment(
        &mut self,
        in_expression_context: bool,
        top_invalid_node_position: i32,
        opening_tag: Option<NodeId>,
        must_be_unary: bool,
    ) -> NodeId {
        let pos = self.node_pos();
        let opening = self.parse_jsx_opening_or_self_closing_element_or_opening_fragment(
            in_expression_context,
        );
        let result: NodeId;
        match self.nodes[opening].kind {
            Kind::JsxOpeningElement => {
                let mut children = self.parse_jsx_children(opening);
                let closing_element: NodeId;
                let last_child = children.nodes.last().copied();
                if let Some(last_child) = last_child
                    && self.nodes[last_child].kind == Kind::JsxElement
                {
                    let last_opening =
                        self.nodes[last_child].as_jsx_element().opening_element;
                    let last_closing =
                        self.nodes[last_child].as_jsx_element().closing_element;
                    if last_opening.is_some()
                        && last_closing.is_some()
                        && !tag_names_are_equivalent(
                            self.tag_name(last_opening.unwrap()),
                            self.tag_name(last_closing.unwrap()),
                            &self.nodes,
                        )
                        && tag_names_are_equivalent(
                            self.tag_name(opening),
                            self.tag_name(last_closing.unwrap()),
                            &self.nodes,
                        )
                    {
                        // when an unclosed JsxOpeningElement incorrectly parses its parent's JsxClosingElement,
                        // restructure (<div>(...<span>...</div>)) --> (<div>(...<span>...</>)</div>)
                        // (no need to error; the parent will error)
                        let end = self.children_end(last_child);
                        let missing_identifier = self.new_identifier("");
                        let missing_identifier =
                            self.finish_node_with_end(missing_identifier, end, end);
                        let new_closing_element = self
                            .factory
                            .new_jsx_closing_element(&mut self.nodes, Some(missing_identifier));
                        let new_closing_element = self.finish_node_with_end(
                            new_closing_element,
                            end,
                            end,
                        );
                        let new_last = self.factory.new_jsx_element(
                            &mut self.nodes,
                            last_opening,
                            Some(children.clone()),
                            Some(new_closing_element),
                        );
                        let new_last = self.finish_node_with_end(
                            new_last,
                            self.nodes[last_opening.unwrap()].pos(),
                            end,
                        );
                        // force reset parent pointers from discarded parse result
                        if let Some(o) = last_opening {
                            self.nodes[o].parent = Some(new_last);
                        }
                        for c in children.nodes.clone() {
                            self.nodes[c].parent = Some(new_last);
                        }
                        self.nodes[new_closing_element].parent = Some(new_last);
                        let mut new_nodes = children.nodes.clone();
                        *new_nodes.last_mut().unwrap() = new_last;
                        children = self.new_node_list(
                            TextRange::new(children.loc.pos(), self.nodes[new_last].end()),
                            new_nodes.to_vec(),
                        );
                        closing_element = last_closing.unwrap();
                        result = self.finish_node(
                            self.factory.new_jsx_element(
                                &mut self.nodes,
                                Some(opening),
                                Some(children),
                                Some(closing_element),
                            ),
                            pos,
                        );
                        self.nodes[closing_element].parent = Some(result);
                        // fallthrough handled after match
                        return self.finish_jsx(
                            result,
                            in_expression_context,
                            top_invalid_node_position,
                            must_be_unary,
                            pos,
                        );
                    }
                }
                closing_element =
                    self.parse_jsx_closing_element(opening, in_expression_context);
                if !tag_names_are_equivalent(
                    self.tag_name(opening),
                    self.tag_name(closing_element),
                    &self.nodes,
                ) {
                    if let Some(ot) = opening_tag
                        && is_jsx_opening_element(&self.nodes[ot])
                        && tag_names_are_equivalent(
                            self.tag_name(closing_element),
                            self.tag_name(ot),
                            &self.nodes,
                        )
                    {
                        // opening incorrectly matched with its parent's closing -- put error on opening
                        let loc = self.nodes[self.tag_name(opening).unwrap()].loc;
                        let arg = scanner_utils::get_text_of_node_from_source_text(
                            self.source_text,
                            self.tag_name(opening).unwrap(),
                            false,
                            &self.nodes,
                        )
                        .into_owned();
                        self.parse_error_at_range(
                            loc,
                            &diagnostics::JSX_element_0_has_no_corresponding_closing_tag,
                            &[arg],
                        );
                    } else {
                        // other opening/closing mismatches -- put error on closing
                        let loc = self.nodes[self.tag_name(closing_element).unwrap()].loc;
                        let arg = scanner_utils::get_text_of_node_from_source_text(
                            self.source_text,
                            self.tag_name(opening).unwrap(),
                            false,
                            &self.nodes,
                        )
                        .into_owned();
                        self.parse_error_at_range(
                            loc,
                            &diagnostics::Expected_corresponding_JSX_closing_tag_for_0,
                            &[arg],
                        );
                    }
                }
                result = self.finish_node(
                    self.factory.new_jsx_element(
                        &mut self.nodes,
                        Some(opening),
                        Some(children),
                        Some(closing_element),
                    ),
                    pos,
                );
                self.nodes[closing_element].parent = Some(result);
            }
            Kind::JsxOpeningFragment => {
                let children = self.parse_jsx_children(opening);
                let closing = self.parse_jsx_closing_fragment(in_expression_context);
                result = self.finish_node(
                    self.factory.new_jsx_fragment(
                        &mut self.nodes,
                        Some(opening),
                        Some(children),
                        Some(closing),
                    ),
                    pos,
                );
            }
            Kind::JsxSelfClosingElement => {
                // Nothing else to do for self-closing elements
                result = opening;
            }
            _ => panic!("Unhandled case in parseJsxElementOrSelfClosingElementOrFragment"),
        }
        self.finish_jsx(
            result,
            in_expression_context,
            top_invalid_node_position,
            must_be_unary,
            pos,
        )
    }

    /// Tail of `parseJsxElementOrSelfClosingElementOrFragment` — sibling-element recovery.
    fn finish_jsx(
        &mut self,
        result: NodeId,
        in_expression_context: bool,
        top_invalid_node_position: i32,
        must_be_unary: bool,
        pos: i32,
    ) -> NodeId {
        let mut result = result;
        if !must_be_unary && in_expression_context && self.token == Kind::LessThanToken {
            let mut top_bad_pos = top_invalid_node_position;
            if top_bad_pos < 0 {
                top_bad_pos = self.nodes[result].pos();
            }
            let invalid_element = self.parse_jsx_element_or_self_closing_element_or_fragment(
                true, /*inExpressionContext*/
                top_bad_pos,
                None,  /*openingTag*/
                false, /*mustBeUnary*/
            );
            let operator_token = self.factory.new_token(&mut self.nodes, Kind::CommaToken);
            self.nodes[operator_token].loc = TextRange::new(
                self.nodes[invalid_element].pos(),
                self.nodes[invalid_element].pos(),
            );
            let start = scanner::skip_trivia(self.source_text, top_bad_pos);
            let end = self.nodes[invalid_element].end();
            self.parse_error_at(
                start,
                end,
                &diagnostics::JSX_expressions_must_have_one_parent_element,
                &[],
            );
            result = self.finish_node(
                self.factory.new_binary_expression(
                    &mut self.nodes,
                    None, /*modifiers*/
                    Some(result),
                    None, /*typeNode*/
                    Some(operator_token),
                    Some(invalid_element),
                ),
                pos,
            );
        }
        result
    }

    /// `func (p *Parser) parseJsxChildren(openingTag) *ast.NodeList`
    fn parse_jsx_children(&mut self, opening_tag: NodeId) -> NodeList {
        let pos = self.node_pos();
        let save_parsing_contexts = self.parsing_contexts;
        self.parsing_contexts |= 1 << PC_JSX_CHILDREN;
        let mut list = Vec::new();
        loop {
            let current_token = self
                .scanner
                .scan_jsx_token_ex(true /*allowMultilineJsxText*/);
            self.drain_scanner_errors();
            let child = self.parse_jsx_child(opening_tag, current_token);
            let Some(child) = child else {
                break;
            };
            list.push(child);
            if is_jsx_opening_element(&self.nodes[opening_tag])
                && self.nodes[child].kind == Kind::JsxElement
            {
                let child_opening =
                    self.nodes[child].as_jsx_element().opening_element;
                let child_closing =
                    self.nodes[child].as_jsx_element().closing_element;
                if child_opening.is_some()
                    && child_closing.is_some()
                    && !tag_names_are_equivalent(
                        self.tag_name(child_opening.unwrap()),
                        self.tag_name(child_closing.unwrap()),
                        &self.nodes,
                    )
                    && tag_names_are_equivalent(
                        self.tag_name(opening_tag),
                        self.tag_name(child_closing.unwrap()),
                        &self.nodes,
                    )
                {
                    // stop after parsing a mismatched child like <div>...(<span></div>) in order to reattach the </div> higher
                    break;
                }
            }
        }
        self.parsing_contexts = save_parsing_contexts;
        self.new_node_list(TextRange::new(pos, self.node_pos()), list)
    }

    /// `func (p *Parser) parseJsxChild(openingTag, token) *ast.Expression`
    fn parse_jsx_child(&mut self, opening_tag: NodeId, token: Kind) -> Option<NodeId> {
        match token {
            Kind::EndOfFile => {
                // If we hit EOF, issue the error at the tag that lacks the closing element
                // rather than at the end of the file (which is useless)
                if is_jsx_opening_fragment(&self.nodes[opening_tag]) {
                    let loc = self.nodes[opening_tag].loc;
                    self.parse_error_at_range(
                        loc,
                        &diagnostics::JSX_fragment_has_no_corresponding_closing_tag,
                        &[],
                    );
                } else {
                    // We want the error span to cover only 'Foo.Bar' in < Foo.Bar >
                    // or to cover only 'Foo' in < Foo >
                    let tag = self.tag_name(opening_tag).unwrap();
                    let start = std::cmp::min(
                        scanner::skip_trivia(
                            self.source_text,
                            self.nodes[tag].pos(),
                        ),
                        self.nodes[tag].end(),
                    );
                    let arg = scanner_utils::get_text_of_node_from_source_text(
                        self.source_text,
                        tag,
                        false,
                        &self.nodes,
                    )
                    .into_owned();
                    self.parse_error_at(
                        start,
                        self.nodes[tag].end(),
                        &diagnostics::JSX_element_0_has_no_corresponding_closing_tag,
                        &[arg],
                    );
                }
                None
            }
            Kind::LessThanSlashToken | Kind::ConflictMarkerTrivia => None,
            Kind::JsxText | Kind::JsxTextAllWhiteSpaces => Some(self.parse_jsx_text()),
            Kind::OpenBraceToken => {
                Some(self.parse_jsx_expression(false /*inExpressionContext*/))
            }
            Kind::LessThanToken => {
                Some(self.parse_jsx_element_or_self_closing_element_or_fragment(
                    false, /*inExpressionContext*/
                    -1,    /*topInvalidNodePosition*/
                    Some(opening_tag),
                    false, /*mustBeUnary*/
                ))
            }
            _ => panic!("Unhandled case in parseJsxChild"),
        }
    }

    /// `func (p *Parser) parseJsxText() *ast.Node`
    fn parse_jsx_text(&mut self) -> NodeId {
        let pos = self.node_pos();
        let text = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
        let result = self.factory.new_jsx_text(
            &mut self.nodes,
            &text,
            self.token == Kind::JsxTextAllWhiteSpaces,
        );
        self.scan_jsx_text();
        self.finish_node(result, pos)
    }

    /// `func (p *Parser) parseJsxExpression(inExpressionContext) *ast.Node`
    fn parse_jsx_expression(&mut self, in_expression_context: bool) -> NodeId {
        let pos = self.node_pos();
        if !self.parse_expected(Kind::OpenBraceToken) {
            // Go returns nil; keep a missing node to preserve arena semantics.
            return self.create_missing_identifier();
        }
        let mut dot_dot_dot_token = None;
        let mut expression = None;
        if self.token != Kind::CloseBraceToken {
            if !in_expression_context {
                dot_dot_dot_token = self.parse_optional_token(Kind::DotDotDotToken);
            }
            // Only an AssignmentExpression is valid here per the JSX spec,
            // but we can unambiguously parse a comma sequence and provide
            // a better error message in grammar checking.
            expression = Some(self.parse_expression());
        }
        if in_expression_context {
            self.parse_expected(Kind::CloseBraceToken);
        } else if self.parse_expected_without_advancing(Kind::CloseBraceToken) {
            self.scan_jsx_text();
        }
        self.finish_node(
            self.factory.new_jsx_expression(
                &mut self.nodes,
                dot_dot_dot_token,
                expression,
            ),
            pos,
        )
    }

    /// `func (p *Parser) scanJsxText() ast.Kind`
    fn scan_jsx_text(&mut self) -> Kind {
        self.token = self.scanner.scan_jsx_token();
        self.drain_scanner_errors();
        self.token
    }

    /// `func (p *Parser) scanJsxIdentifier() ast.Kind`
    fn scan_jsx_identifier(&mut self) -> Kind {
        self.token = self.scanner.scan_jsx_identifier();
        self.drain_scanner_errors();
        self.token
    }

    /// `func (p *Parser) scanJsxAttributeValue() ast.Kind`
    fn scan_jsx_attribute_value(&mut self) -> Kind {
        self.token = self.scanner.scan_jsx_attribute_value();
        self.drain_scanner_errors();
        self.token
    }

    /// `func (p *Parser) parseJsxClosingElement(open, inExpressionContext) *ast.Node`
    fn parse_jsx_closing_element(
        &mut self,
        open: NodeId,
        in_expression_context: bool,
    ) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::LessThanSlashToken);
        let tag_name = self.parse_jsx_element_name();
        if self.parse_expected_with_diagnostic(
            Kind::GreaterThanToken,
            None,  /*diagnosticMessage*/
            false, /*shouldAdvance*/
        ) {
            // manually advance the scanner in order to look for jsx text inside jsx
            if in_expression_context
                || !tag_names_are_equivalent(
                    self.tag_name(open),
                    Some(tag_name),
                    &self.nodes,
                )
            {
                self.next_token();
            } else {
                self.scan_jsx_text();
            }
        }
        self.finish_node(
            self.factory
                .new_jsx_closing_element(&mut self.nodes, Some(tag_name)),
            pos,
        )
    }

    /// `func (p *Parser) parseJsxOpeningOrSelfClosingElementOrOpeningFragment(inExpressionContext)`
    fn parse_jsx_opening_or_self_closing_element_or_opening_fragment(
        &mut self,
        in_expression_context: bool,
    ) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::LessThanToken);
        if self.token == Kind::GreaterThanToken {
            // See below for explanation of scanJsxText
            self.scan_jsx_text();
            return self.finish_node(
                self.factory.new_jsx_opening_fragment(&mut self.nodes),
                pos,
            );
        }
        let tag_name = self.parse_jsx_element_name();
        let mut type_arguments = None;
        if !self.context_flags.intersects(NodeFlags::JAVA_SCRIPT_FILE) {
            type_arguments = self.parse_type_arguments();
        }
        let attributes = self.parse_jsx_attributes();
        let result = if self.token == Kind::GreaterThanToken {
            // Closing tag, so scan the immediately-following text with the JSX scanning instead
            // of regular scanning to avoid treating illegal characters (e.g. '#') as immediate
            // scanning errors
            self.scan_jsx_text();
            self.factory.new_jsx_opening_element(
                &mut self.nodes,
                Some(tag_name),
                type_arguments,
                Some(attributes),
            )
        } else {
            self.parse_expected(Kind::SlashToken);
            if self.parse_expected_without_advancing(Kind::GreaterThanToken) {
                if in_expression_context {
                    self.next_token();
                } else {
                    self.scan_jsx_text();
                }
            }
            self.factory.new_jsx_self_closing_element(
                &mut self.nodes,
                Some(tag_name),
                type_arguments,
                Some(attributes),
            )
        };
        self.finish_node(result, pos)
    }

    /// `func (p *Parser) parseJsxElementName() *ast.Expression`
    fn parse_jsx_element_name(&mut self) -> NodeId {
        let pos = self.node_pos();
        // JsxElement can have name in the form of
        //      propertyAccessExpression
        //      primaryExpression in the form of an identifier and "this" keyword
        // We can't just simply use parseLeftHandSideExpressionOrHigher because then we will start consider class,function etc as a keyword
        // We only want to consider "this" as a primaryExpression
        let initial_expression = self.parse_jsx_tag_name();
        if is_jsx_namespaced_name(&self.nodes[initial_expression]) {
            return initial_expression;
        }
        let mut expression = initial_expression;
        while self.parse_optional(Kind::DotToken) {
            let right = self.parse_right_side_of_dot(
                true,  /*allowIdentifierNames*/
                false, /*allowPrivateIdentifiers*/
                false, /*allowUnicodeEscapeSequenceInIdentifierName*/
            );
            expression = self.finish_node(
                self.factory.new_property_access_expression(
                    &mut self.nodes,
                    Some(expression),
                    None, /*questionDotToken*/
                    Some(right),
                    NodeFlags::NONE,
                ),
                pos,
            );
        }
        expression
    }

    /// `func (p *Parser) parseJsxTagName() *ast.Expression`
    fn parse_jsx_tag_name(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.scan_jsx_identifier();
        let is_this = self.token == Kind::ThisKeyword;
        let tag_name = self.parse_identifier_name_error_on_unicode_escape_sequence();
        if self.parse_optional(Kind::ColonToken) {
            self.scan_jsx_identifier();
            let right = self.parse_identifier_name_error_on_unicode_escape_sequence();
            return self.finish_node(
                self.factory.new_jsx_namespaced_name(
                    &mut self.nodes,
                    Some(tag_name),
                    Some(right),
                ),
                pos,
            );
        }
        if is_this {
            let result = self
                .factory
                .new_keyword_expression(&mut self.nodes, Kind::ThisKeyword);
            return self.finish_node(result, pos);
        }
        tag_name
    }

    /// `func (p *Parser) parseJsxAttributes() *ast.Node`
    fn parse_jsx_attributes(&mut self) -> NodeId {
        let pos = self.node_pos();
        let attributes =
            self.parse_list(PC_JSX_ATTRIBUTES, Self::parse_jsx_attribute_some);
        self.finish_node(
            self.factory
                .new_jsx_attributes(&mut self.nodes, Some(attributes)),
            pos,
        )
    }

    /// `func (p *Parser) parseJsxAttribute() *ast.Node`
    fn parse_jsx_attribute(&mut self) -> NodeId {
        if self.token == Kind::OpenBraceToken {
            return self.parse_jsx_spread_attribute();
        }
        let pos = self.node_pos();
        let name = self.parse_jsx_attribute_name();
        let initializer = self.parse_jsx_attribute_value();
        self.finish_node(
            self.factory
                .new_jsx_attribute(&mut self.nodes, Some(name), initializer),
            pos,
        )
    }

    fn parse_jsx_attribute_some(&mut self) -> Option<NodeId> {
        Some(self.parse_jsx_attribute())
    }

    /// `func (p *Parser) parseJsxSpreadAttribute() *ast.Node`
    fn parse_jsx_spread_attribute(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::OpenBraceToken);
        self.parse_expected(Kind::DotDotDotToken);
        let expression = self.parse_expression();
        self.parse_expected(Kind::CloseBraceToken);
        self.finish_node(
            self.factory
                .new_jsx_spread_attribute(&mut self.nodes, Some(expression)),
            pos,
        )
    }

    /// `func (p *Parser) parseJsxAttributeName() *ast.Node`
    fn parse_jsx_attribute_name(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.scan_jsx_identifier();
        let attr_name = self.parse_identifier_name_error_on_unicode_escape_sequence();
        if self.parse_optional(Kind::ColonToken) {
            self.scan_jsx_identifier();
            let right = self.parse_identifier_name_error_on_unicode_escape_sequence();
            return self.finish_node(
                self.factory.new_jsx_namespaced_name(
                    &mut self.nodes,
                    Some(attr_name),
                    Some(right),
                ),
                pos,
            );
        }
        attr_name
    }

    /// `func (p *Parser) parseJsxAttributeValue() *ast.Expression`
    fn parse_jsx_attribute_value(&mut self) -> Option<NodeId> {
        if self.token == Kind::EqualsToken {
            if self.scan_jsx_attribute_value() == Kind::StringLiteral {
                return Some(self.parse_literal_expression());
            }
            if self.token == Kind::OpenBraceToken {
                return Some(self.parse_jsx_expression(true /*inExpressionContext*/));
            }
            if self.token == Kind::LessThanToken {
                // An attribute value must be a single JsxAttributeValue, so don't allow the sibling-element
                // recovery to wrap it in a synthetic binary expression.
                return Some(self.parse_jsx_element_or_self_closing_element_or_fragment(
                    true, /*inExpressionContext*/
                    -1,   /*topInvalidNodePosition*/
                    None, /*openingTag*/
                    true, /*mustBeUnary*/
                ));
            }
            self.parse_error_at_current_token(&diagnostics::X_or_JSX_element_expected, &[]);
        }
        None
    }

    /// `func (p *Parser) parseJsxClosingFragment(inExpressionContext) *ast.Node`
    fn parse_jsx_closing_fragment(&mut self, in_expression_context: bool) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::LessThanSlashToken);
        if self.parse_expected_with_diagnostic(
            Kind::GreaterThanToken,
            Some(&diagnostics::Expected_corresponding_closing_tag_for_JSX_fragment),
            false, /*shouldAdvance*/
        ) {
            // manually advance the scanner in order to look for jsx text inside jsx
            if in_expression_context {
                self.next_token();
            } else {
                self.scan_jsx_text();
            }
        }
        self.finish_node(
            self.factory.new_jsx_closing_fragment(&mut self.nodes),
            pos,
        )
    }

    /// `n.TagName()` helper — `openingTag.TagName()` / `closingElement.TagName()`.
    fn tag_name(&self, node: NodeId) -> Option<NodeId> {
        self.nodes[node].tag_name()
    }

    /// `lastChild.Children().End()` — end of the children list of a JsxElement.
    fn children_end(&self, node: NodeId) -> i32 {
        self.nodes[node]
            .children()
            .map(|c| c.loc.end())
            .unwrap_or_else(|| self.nodes[node].end())
    }
}

/// `func getSpaceSuggestion(expressionText string) string`
fn get_space_suggestion(expression_text: &str) -> String {
    for keyword in VIABLE_KEYWORD_SUGGESTIONS.iter() {
        if expression_text.len() > keyword.len() + 2
            && expression_text.starts_with(keyword)
        {
            return format!("{} {}", keyword, &expression_text[keyword.len()..]);
        }
    }
    String::new()
}

/// `func isValidHeritageTypeReferenceExpression(node *ast.Node) bool`
fn is_valid_heritage_type_reference_expression(
    node: Option<NodeId>,
    nodes: &[Node],
) -> bool {
    let Some(node) = node else {
        return false;
    };
    if is_identifier(&nodes[node]) {
        return node_is_present(Some(node), nodes);
    }
    is_property_access_expression(&nodes[node])
        && !is_optional_chain(&nodes[node])
        && node_is_present(nodes[node].name(), nodes)
        && is_valid_heritage_type_reference_expression(
            nodes[node].expression(),
            nodes,
        )
}

/// `func ast.TagNamesAreEquivalent(...)` for NodeIds.
fn tag_names_are_equivalent(
    left: Option<NodeId>,
    right: Option<NodeId>,
    nodes: &[Node],
) -> bool {
    match (left, right) {
        (Some(l), Some(r)) => tsc_ast::utilities::tag_names_are_equivalent(l, r, nodes),
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Unary / LHS / member / call expressions (Go `parseSimpleUnaryExpression` …
// `parseTemplateSpan`)
// ---------------------------------------------------------------------------

impl<'a> Parser<'a> {
    /// `func (p *Parser) parseSimpleUnaryExpression() *ast.Expression`
    fn parse_simple_unary_expression(&mut self) -> NodeId {
        match self.token {
            Kind::PlusToken | Kind::MinusToken | Kind::TildeToken
            | Kind::ExclamationToken => self.parse_prefix_unary_expression(),
            Kind::DeleteKeyword => self.parse_delete_expression(),
            Kind::TypeOfKeyword => self.parse_type_of_expression(),
            Kind::VoidKeyword => self.parse_void_expression(),
            Kind::LessThanToken => {
                // Just like in parseUpdateExpression, we need to avoid parsing type assertions when
                // in JSX and we see an expression like "+ <foo> bar".
                if self.language_variant == LanguageVariant::Jsx {
                    return self.parse_jsx_element_or_self_closing_element_or_fragment(
                        true, /*inExpressionContext*/
                        -1,   /*topInvalidNodePosition*/
                        None, /*openingTag*/
                        true, /*mustBeUnary*/
                    );
                }
                // This is modified UnaryExpression grammar in TypeScript
                //  UnaryExpression (modified):
                //      < type > UnaryExpression
                self.parse_type_assertion()
            }
            Kind::AwaitKeyword => {
                if self.is_await_expression() {
                    return self.parse_await_expression();
                }
                self.parse_update_expression()
            }
            _ => self.parse_update_expression(),
        }
    }

    /// `func (p *Parser) parsePrefixUnaryExpression() *ast.Node`
    fn parse_prefix_unary_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        let operator = self.token;
        self.next_token();
        let operand = self.parse_simple_unary_expression();
        self.finish_node(
            self.factory
                .new_prefix_unary_expression(&mut self.nodes, operator, Some(operand)),
            pos,
        )
    }

    /// `func (p *Parser) parseDeleteExpression() *ast.Node`
    fn parse_delete_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.next_token();
        let operand = self.parse_simple_unary_expression();
        self.finish_node(
            self.factory
                .new_delete_expression(&mut self.nodes, Some(operand)),
            pos,
        )
    }

    /// `func (p *Parser) parseTypeOfExpression() *ast.Node`
    fn parse_type_of_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.next_token();
        let operand = self.parse_simple_unary_expression();
        self.finish_node(
            self.factory
                .new_type_of_expression(&mut self.nodes, Some(operand)),
            pos,
        )
    }

    /// `func (p *Parser) parseVoidExpression() *ast.Node`
    fn parse_void_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.next_token();
        let operand = self.parse_simple_unary_expression();
        self.finish_node(
            self.factory
                .new_void_expression(&mut self.nodes, Some(operand)),
            pos,
        )
    }

    /// `func (p *Parser) isAwaitExpression() bool`
    fn is_await_expression(&mut self) -> bool {
        if self.token == Kind::AwaitKeyword {
            if self.in_await_context() {
                return true;
            }
            // here we are using similar heuristics as 'isYieldExpression'
            return self.look_ahead(
                Self::next_token_is_identifier_or_keyword_or_literal_on_same_line,
            );
        }
        false
    }

    /// `func (p *Parser) parseAwaitExpression() *ast.Node`
    fn parse_await_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.next_token();
        let operand = self.parse_simple_unary_expression();
        self.finish_node(
            self.factory
                .new_await_expression(&mut self.nodes, Some(operand)),
            pos,
        )
    }

    /// `func (p *Parser) parseTypeAssertion() *ast.Node`
    fn parse_type_assertion(&mut self) -> NodeId {
        tsc_debug::assert_!(self.language_variant != LanguageVariant::Jsx, "Type assertions should never be parsed in JSX; they should be parsed as comparisons or JSX elements/fragments.");
        let pos = self.node_pos();
        self.parse_expected(Kind::LessThanToken);
        let type_node = self.parse_type();
        self.parse_expected(Kind::GreaterThanToken);
        let expression = self.parse_simple_unary_expression();
        self.finish_node(
            self.factory.new_type_assertion(
                &mut self.nodes,
                Some(type_node),
                Some(expression),
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseLeftHandSideExpressionOrHigher() *ast.Expression`
    fn parse_left_hand_side_expression_or_higher(&mut self) -> NodeId {
        // Original Ecma:
        // LeftHandSideExpression: See 11.2
        //      NewExpression
        //      CallExpression
        //
        // Our simplification:
        //
        // LeftHandSideExpression: See 11.2
        //      MemberExpression
        //      CallExpression
        //
        // Because of the recursion in these calls, we need to bottom out first. There are three
        // bottom out states we can run into: 1) We see 'super' which must start either of
        // the last two CallExpression productions. 2) We see 'import' which must start import call.
        // 3)we have a MemberExpression which either completes the LeftHandSideExpression,
        // or starts the beginning of the first four CallExpression productions.
        let pos = self.node_pos();
        let mut expression: NodeId;
        if self.token == Kind::ImportKeyword {
            if self.look_ahead(Self::next_token_is_open_paren_or_less_than) {
                // We don't want to eagerly consume all import keyword as import call expression so we look ahead to find "("
                // For example:
                //      var foo3 = require("subfolder
                //      import * as foo1 from "module-from-node
                // We want this import to be a statement rather than import call expression
                self.source_flags |= NodeFlags::POSSIBLY_CONTAINS_DYNAMIC_IMPORT;
                expression = self.parse_keyword_expression();
            } else if self.look_ahead(Self::next_token_is_dot) {
                // This is an 'import.*' metaproperty (i.e. 'import.meta')
                self.next_token(); // advance past the 'import'
                self.next_token(); // advance past the dot
                let name = self.parse_import_meta_property_name();
                expression = self.finish_node(
                    self.factory.new_meta_property(
                        &mut self.nodes,
                        Kind::ImportKeyword,
                        Some(name),
                    ),
                    pos,
                );
                if is_import_phase_meta_property(&self.nodes[expression], &self.nodes) {
                    if self.token == Kind::OpenParenToken
                        || self.token == Kind::LessThanToken
                    {
                        self.source_flags |=
                            NodeFlags::POSSIBLY_CONTAINS_DYNAMIC_IMPORT;
                    }
                } else {
                    self.source_flags |= NodeFlags::POSSIBLY_CONTAINS_IMPORT_META;
                }
            } else {
                expression = self.parse_member_expression_or_higher();
            }
        } else if self.token == Kind::SuperKeyword {
            expression = self.parse_super_expression();
        } else {
            expression = self.parse_member_expression_or_higher();
        }
        // Now, we *may* be complete.  However, we might have consumed the start of a
        // CallExpression or OptionalExpression.  As such, we need to consume the rest
        // of it here to be complete.
        self.parse_call_expression_rest(pos, expression)
    }

    /// `func (p *Parser) nextTokenIsDot() bool`
    fn next_token_is_dot(&mut self) -> bool {
        self.next_token() == Kind::DotToken
    }

    /// `func (p *Parser) parseImportMetaPropertyName() *ast.Node`
    fn parse_import_meta_property_name(&mut self) -> NodeId {
        if matches!(self.token, Kind::DeferKeyword | Kind::SourceKeyword)
            && self.current_import_phase_modifier() == Kind::Unknown
        {
            self.parse_error_at_current_token(
                &diagnostics::Keywords_cannot_contain_escape_characters,
                &[],
            );
        }
        self.parse_identifier_name()
    }

    /// `func (p *Parser) parseSuperExpression() *ast.Expression`
    fn parse_super_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        let mut expression = self.parse_keyword_expression();
        if self.token == Kind::LessThanToken {
            let start_pos = self.node_pos();
            let type_arguments = self.try_parse_type_arguments_in_expression();
            if let Some(type_arguments) = type_arguments {
                let end = self.node_pos();
                self.parse_error_at(
                    start_pos,
                    end,
                    &diagnostics::X_super_may_not_use_type_arguments,
                    &[],
                );
                if !self.is_template_start_of_tagged_template() {
                    expression = self.finish_node(
                        self.factory.new_expression_with_type_arguments(
                            &mut self.nodes,
                            Some(expression),
                            Some(type_arguments),
                        ),
                        pos,
                    );
                }
            }
        }
        if self.token == Kind::OpenParenToken
            || self.token == Kind::DotToken
            || self.token == Kind::OpenBracketToken
        {
            return expression;
        }
        // If we have seen "super" it must be followed by '(' or '.'.
        // If it wasn't then just try to parse out a '.' and report an error.
        self.parse_error_at_current_token(
            &diagnostics::X_super_must_be_followed_by_an_argument_list_or_member_access,
            &[],
        );
        // private names will never work with `super` (`super.#foo`), but that's a semantic error, not syntactic
        let right = self.parse_right_side_of_dot(
            true, /*allowIdentifierNames*/
            true, /*allowPrivateIdentifiers*/
            true, /*allowUnicodeEscapeSequenceInIdentifierName*/
        );
        self.finish_node(
            self.factory.new_property_access_expression(
                &mut self.nodes,
                Some(expression),
                None, /*questionDotToken*/
                Some(right),
                NodeFlags::NONE,
            ),
            pos,
        )
    }

    /// `func (p *Parser) isTemplateStartOfTaggedTemplate() bool`
    fn is_template_start_of_tagged_template(&self) -> bool {
        self.token == Kind::NoSubstitutionTemplateLiteral
            || self.token == Kind::TemplateHead
    }

    /// `func (p *Parser) tryParseTypeArgumentsInExpression() *ast.NodeList`
    fn try_parse_type_arguments_in_expression(&mut self) -> Option<NodeList> {
        // TypeArguments must not be parsed in JavaScript files to avoid ambiguity with binary operators.
        // Check the cheap preconditions before saving the parser state: unless the current token is `<`
        // (or `<<`, which reScanLessThanToken would split), there is nothing to speculatively parse and
        // the mark/rewind would be a no-op.
        if self.context_flags.intersects(NodeFlags::JAVA_SCRIPT_FILE)
            || (self.token != Kind::LessThanToken
                && self.token != Kind::LessThanLessThanToken)
        {
            return None;
        }
        let state = self.mark();
        if self.rescan_less_than_token() == Kind::LessThanToken {
            self.next_token();
            let type_arguments =
                self.parse_delimited_list(PC_TYPE_ARGUMENTS, Self::parse_type_some, false);
            // If it doesn't have the closing `>` then it's definitely not an type argument list.
            if self.rescan_greater_than_token() == Kind::GreaterThanToken {
                self.next_token();
                // We successfully parsed a type argument list. The next token determines whether we want to
                // treat it as such. If the type argument list is followed by `(` or a template literal, as in
                // `f<number>(42)`, we favor the type argument interpretation even though JavaScript would view
                // it as a relational expression.
                if self.can_follow_type_arguments_in_expression() {
                    return type_arguments;
                }
            }
        }
        self.rewind(state);
        None
    }

    /// `func (p *Parser) canFollowTypeArgumentsInExpression() bool`
    fn can_follow_type_arguments_in_expression(&mut self) -> bool {
        match self.token {
            // These tokens can follow a type argument list in a call expression:
            // foo<x>(
            // foo<T> `...`
            // foo<T> `...${100}...`
            Kind::OpenParenToken
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::TemplateHead => true,
            // A type argument list followed by `<` never makes sense, and a type argument list followed
            // by `>` is ambiguous with a (re-scanned) `>>` operator, so we disqualify both. Also, in
            // this context, `+` and `-` are unary operators, not binary operators.
            Kind::LessThanToken
            | Kind::GreaterThanToken
            | Kind::PlusToken
            | Kind::MinusToken => false,
            // We favor the type argument list interpretation when it is immediately followed by
            // a line break, a binary operator, or something that can't start an expression.
            _ => {
                self.has_preceding_line_break()
                    || self.is_binary_operator()
                    || !self.is_start_of_expression()
            }
        }
    }

    /// `func (p *Parser) parseMemberExpressionOrHigher() *ast.Node`
    fn parse_member_expression_or_higher(&mut self) -> NodeId {
        // Note: to make our lives simpler, we decompose the NewExpression productions and
        // place ObjectCreationExpression and FunctionExpression into PrimaryExpression.
        // Because CallExpression and MemberExpression are left recursive, we need to bottom out
        // of the recursion immediately.  So we parse out a primary expression to start with.
        let pos = self.node_pos();
        let expression = self.parse_primary_expression();
        self.parse_member_expression_rest(pos, expression, true /*allowOptionalChain*/)
    }

    /// `func (p *Parser) parseMemberExpressionRest(pos, expression, allowOptionalChain)`
    fn parse_member_expression_rest(
        &mut self,
        pos: i32,
        expression: NodeId,
        allow_optional_chain: bool,
    ) -> NodeId {
        let mut expression = expression;
        loop {
            let mut question_dot_token = None;
            let mut is_property_access = false;
            if allow_optional_chain
                && self.is_start_of_optional_property_or_element_access_chain()
            {
                question_dot_token =
                    Some(self.parse_expected_token(Kind::QuestionDotToken));
                is_property_access = token_is_identifier_or_keyword(self.token);
            } else {
                is_property_access = self.parse_optional(Kind::DotToken);
            }
            if is_property_access {
                expression = self.parse_property_access_expression_rest(
                    pos,
                    expression,
                    question_dot_token,
                );
                continue;
            }
            // when in the [Decorator] context, we do not parse ElementAccess as it could be part of a ComputedPropertyName
            if (question_dot_token.is_some() || !self.in_decorator_context())
                && self.parse_optional(Kind::OpenBracketToken)
            {
                expression = self.parse_element_access_expression_rest(
                    pos,
                    expression,
                    question_dot_token,
                );
                continue;
            }
            if self.is_template_start_of_tagged_template() {
                // Absorb type arguments into TemplateExpression when preceding expression is ExpressionWithTypeArguments
                if question_dot_token.is_none()
                    && is_expression_with_type_arguments(&self.nodes[expression])
                {
                    let (original_expression, original_type_arguments) = {
                        let original = self.nodes[expression]
                            .as_expression_with_type_arguments();
                        (original.expression, original.type_arguments.clone())
                    };
                    expression = self.parse_tagged_template_rest(
                        pos,
                        original_expression.unwrap(),
                        question_dot_token,
                        original_type_arguments.clone(),
                    );
                    self.unparse_expression_with_type_arguments(
                        original_expression,
                        original_type_arguments,
                        expression,
                    );
                } else {
                    expression = self.parse_tagged_template_rest(
                        pos,
                        expression,
                        question_dot_token,
                        None, /*typeArguments*/
                    );
                }
                continue;
            }
            if question_dot_token.is_none() {
                if self.token == Kind::ExclamationToken
                    && !self.has_preceding_line_break()
                {
                    self.next_token();
                    let non_null = self.finish_node(
                        self.factory.new_non_null_expression(
                            &mut self.nodes,
                            Some(expression),
                            NodeFlags::NONE,
                        ),
                        pos,
                    );
                    expression = self.check_js_syntax(non_null);
                    continue;
                }
                let type_arguments = self.try_parse_type_arguments_in_expression();
                if let Some(type_arguments) = type_arguments {
                    expression = self.finish_node(
                        self.factory.new_expression_with_type_arguments(
                            &mut self.nodes,
                            Some(expression),
                            Some(type_arguments),
                        ),
                        pos,
                    );
                    continue;
                }
            }
            return expression;
        }
    }

    /// `func (p *Parser) isStartOfOptionalPropertyOrElementAccessChain() bool`
    fn is_start_of_optional_property_or_element_access_chain(&mut self) -> bool {
        self.token == Kind::QuestionDotToken
            && self.look_ahead(
                Self::next_token_is_identifier_or_keyword_or_open_bracket_or_template,
            )
    }

    /// `func (p *Parser) nextTokenIsIdentifierOrKeywordOrOpenBracketOrTemplate() bool`
    fn next_token_is_identifier_or_keyword_or_open_bracket_or_template(
        &mut self,
    ) -> bool {
        self.next_token();
        token_is_identifier_or_keyword(self.token)
            || self.token == Kind::OpenBracketToken
            || self.is_template_start_of_tagged_template()
    }

    /// `func (p *Parser) parsePropertyAccessExpressionRest(pos, expression, questionDotToken)`
    fn parse_property_access_expression_rest(
        &mut self,
        pos: i32,
        expression: NodeId,
        question_dot_token: Option<NodeId>,
    ) -> NodeId {
        let name = self.parse_right_side_of_dot(
            true, /*allowIdentifierNames*/
            true, /*allowPrivateIdentifiers*/
            true, /*allowUnicodeEscapeSequenceInIdentifierName*/
        );
        let is_optional_chain =
            question_dot_token.is_some() || self.try_reparse_optional_chain(expression);
        let property_access = self.factory.new_property_access_expression(
            &mut self.nodes,
            Some(expression),
            question_dot_token,
            Some(name),
            if is_optional_chain {
                NodeFlags::OPTIONAL_CHAIN
            } else {
                NodeFlags::NONE
            },
        );
        if is_optional_chain && is_private_identifier(&self.nodes[name]) {
            let loc = self.skip_range_trivia(self.nodes[name].loc);
            self.parse_error_at_range(
                loc,
                &diagnostics::An_optional_chain_cannot_contain_private_identifiers,
                &[],
            );
        }
        if is_expression_with_type_arguments(&self.nodes[expression]) {
            let type_arguments = self.nodes[expression].type_argument_list();
            if let Some(type_arguments) = type_arguments {
                let loc = TextRange::new(
                    type_arguments.loc.pos() - 1,
                    scanner::skip_trivia(self.source_text, type_arguments.loc.end()) + 1,
                );
                self.parse_error_at_range(
                    loc,
                    &diagnostics::An_instantiation_expression_cannot_be_followed_by_a_property_access,
                    &[],
                );
            }
        }
        self.finish_node(property_access, pos)
    }

    /// `func (p *Parser) tryReparseOptionalChain(node *ast.Expression) bool`
    fn try_reparse_optional_chain(&mut self, node: NodeId) -> bool {
        let mut node = node;
        if self.nodes[node].flags.intersects(NodeFlags::OPTIONAL_CHAIN) {
            return true;
        }
        // check for an optional chain in a non-null expression
        if is_non_null_expression(&self.nodes[node]) {
            let mut expr = self.nodes[node].expression().unwrap();
            while is_non_null_expression(&self.nodes[expr])
                && !self.nodes[expr].flags.intersects(NodeFlags::OPTIONAL_CHAIN)
            {
                expr = self.nodes[expr].expression().unwrap();
            }
            if self.nodes[expr].flags.intersects(NodeFlags::OPTIONAL_CHAIN) {
                // this is part of an optional chain. Walk down from `node` to `expression` and set the flag.
                while is_non_null_expression(&self.nodes[node]) {
                    self.nodes[node].flags |= NodeFlags::OPTIONAL_CHAIN;
                    node = self.nodes[node].expression().unwrap();
                }
                return true;
            }
        }
        false
    }

    /// `func (p *Parser) parseElementAccessExpressionRest(pos, expression, questionDotToken)`
    fn parse_element_access_expression_rest(
        &mut self,
        pos: i32,
        expression: NodeId,
        question_dot_token: Option<NodeId>,
    ) -> NodeId {
        let mut argument_expression = self.create_missing_identifier();
        if self.token == Kind::CloseBracketToken {
            let node_pos = self.node_pos();
            self.parse_error_at(
                node_pos,
                node_pos,
                &diagnostics::An_element_access_expression_should_take_an_argument,
                &[],
            );
        } else {
            argument_expression = self.parse_expression_allow_in();
        }
        self.parse_expected(Kind::CloseBracketToken);
        let is_optional_chain =
            question_dot_token.is_some() || self.try_reparse_optional_chain(expression);
        self.finish_node(
            self.factory.new_element_access_expression(
                &mut self.nodes,
                Some(expression),
                question_dot_token,
                Some(argument_expression),
                if is_optional_chain {
                    NodeFlags::OPTIONAL_CHAIN
                } else {
                    NodeFlags::NONE
                },
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseCallExpressionRest(pos, expression) *ast.Expression`
    fn parse_call_expression_rest(&mut self, pos: i32, expression: NodeId) -> NodeId {
        let mut expression = expression;
        loop {
            expression = self.parse_member_expression_rest(
                pos,
                expression,
                true, /*allowOptionalChain*/
            );
            let mut type_arguments = None;
            let question_dot_token = self.parse_optional_token(Kind::QuestionDotToken);
            if question_dot_token.is_some() {
                type_arguments = self.try_parse_type_arguments_in_expression();
                if self.is_template_start_of_tagged_template() {
                    expression = self.parse_tagged_template_rest(
                        pos,
                        expression,
                        question_dot_token,
                        type_arguments,
                    );
                    continue;
                }
            }
            if type_arguments.is_some() || self.token == Kind::OpenParenToken {
                // Absorb type arguments into CallExpression when preceding expression is ExpressionWithTypeArguments
                if question_dot_token.is_none()
                    && self.nodes[expression].kind == Kind::ExpressionWithTypeArguments
                {
                    let (ewta_expression, ewta_type_arguments) = {
                        let ewta = self.nodes[expression]
                            .as_expression_with_type_arguments();
                        (ewta.expression, ewta.type_arguments.clone())
                    };
                    type_arguments = ewta_type_arguments;
                    expression = ewta_expression.unwrap();
                }
                let inner = expression;
                let argument_list = self.parse_argument_list();
                let is_optional_chain = question_dot_token.is_some()
                    || self.try_reparse_optional_chain(expression);
                let call = self.finish_node(
                    self.factory.new_call_expression(
                        &mut self.nodes,
                        Some(expression),
                        question_dot_token,
                        type_arguments.clone(),
                        argument_list,
                        if is_optional_chain {
                            NodeFlags::OPTIONAL_CHAIN
                        } else {
                            NodeFlags::NONE
                        },
                    ),
                    pos,
                );
                expression = self.check_js_syntax(call);
                self.unparse_expression_with_type_arguments(
                    Some(inner),
                    type_arguments,
                    expression,
                );
                continue;
            }
            if question_dot_token.is_some() {
                // We parsed `?.` but then failed to parse anything, so report a missing identifier here.
                self.parse_error_at_current_token(&diagnostics::Identifier_expected, &[]);
                let name = self.create_missing_identifier();
                expression = self.finish_node(
                    self.factory.new_property_access_expression(
                        &mut self.nodes,
                        Some(expression),
                        question_dot_token,
                        Some(name),
                        NodeFlags::OPTIONAL_CHAIN,
                    ),
                    pos,
                );
            }
            break;
        }
        expression
    }

    /// `func (p *Parser) parseArgumentList() *ast.NodeList`
    fn parse_argument_list(&mut self) -> Option<NodeList> {
        self.parse_expected(Kind::OpenParenToken);
        let result = self.parse_delimited_list(
            PC_ARGUMENT_EXPRESSIONS,
            Self::parse_argument_expression_some,
            false,
        );
        self.parse_expected(Kind::CloseParenToken);
        result
    }

    /// `func (p *Parser) parseArgumentExpression() *ast.Expression`
    fn parse_argument_expression(&mut self) -> NodeId {
        self.do_in_context(
            NodeFlags::DISALLOW_IN_CONTEXT | NodeFlags::DECORATOR_CONTEXT,
            false,
            Self::parse_argument_or_array_literal_element,
        )
    }

    fn parse_argument_expression_some(&mut self) -> Option<NodeId> {
        Some(self.parse_argument_expression())
    }

    /// `func (p *Parser) parseArgumentOrArrayLiteralElement() *ast.Expression`
    fn parse_argument_or_array_literal_element(&mut self) -> NodeId {
        match self.token {
            Kind::DotDotDotToken => self.parse_spread_element(),
            Kind::CommaToken => self.finish_node(
                self.factory.new_omitted_expression(&mut self.nodes),
                self.node_pos(),
            ),
            _ => self.parse_assignment_expression_or_higher(),
        }
    }

    /// `func (p *Parser) parseSpreadElement() *ast.Node`
    fn parse_spread_element(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::DotDotDotToken);
        let expression = self.parse_assignment_expression_or_higher();
        self.finish_node(
            self.factory
                .new_spread_element(&mut self.nodes, Some(expression)),
            pos,
        )
    }

    /// `func (p *Parser) parseTaggedTemplateRest(pos, tag, questionDotToken, typeArguments)`
    fn parse_tagged_template_rest(
        &mut self,
        pos: i32,
        tag: NodeId,
        question_dot_token: Option<NodeId>,
        type_arguments: Option<NodeList>,
    ) -> NodeId {
        let template = if self.token == Kind::NoSubstitutionTemplateLiteral {
            self.rescan_template_token(true /*isTaggedTemplate*/);
            self.parse_literal_expression()
        } else {
            self.parse_template_expression(true /*isTaggedTemplate*/)
        };
        let is_optional_chain = question_dot_token.is_some()
            || self.nodes[tag].flags.intersects(NodeFlags::OPTIONAL_CHAIN);
        let result = self.finish_node(
            self.factory.new_tagged_template_expression(
                &mut self.nodes,
                Some(tag),
                question_dot_token,
                type_arguments,
                Some(template),
                if is_optional_chain {
                    NodeFlags::OPTIONAL_CHAIN
                } else {
                    NodeFlags::NONE
                },
            ),
            pos,
        );
        self.check_js_syntax(result)
    }

    /// `func (p *Parser) parseTemplateExpression(isTaggedTemplate) *ast.Expression`
    fn parse_template_expression(&mut self, is_tagged_template: bool) -> NodeId {
        let pos = self.node_pos();
        let head = self.parse_template_head(is_tagged_template);
        let spans = self.parse_template_spans(is_tagged_template);
        self.finish_node(
            self.factory.new_template_expression(
                &mut self.nodes,
                Some(head),
                Some(spans),
            ),
            pos,
        )
    }

    /// `func (p *Parser) parseTemplateSpans(isTaggedTemplate) *ast.NodeList`
    fn parse_template_spans(&mut self, is_tagged_template: bool) -> NodeList {
        let pos = self.node_pos();
        let mut list = Vec::new();
        loop {
            let span = self.parse_template_span(is_tagged_template);
            let is_middle = self.nodes[span]
                .as_template_span()
                .literal
                .is_some_and(|l| self.nodes[l].kind == Kind::TemplateMiddle);
            list.push(span);
            if !is_middle {
                break;
            }
        }
        self.new_node_list(TextRange::new(pos, self.node_pos()), list)
    }

    /// `func (p *Parser) parseTemplateSpan(isTaggedTemplate) *ast.Node`
    fn parse_template_span(&mut self, is_tagged_template: bool) -> NodeId {
        let pos = self.node_pos();
        let expression = self.parse_expression_allow_in();
        let literal = self.parse_literal_of_template_span(is_tagged_template);
        self.finish_node(
            self.factory.new_template_span(
                &mut self.nodes,
                Some(expression),
                Some(literal),
            ),
            pos,
        )
    }
}

// ---------------------------------------------------------------------------
// Primary expressions, literals, and identifiers (Go `parsePrimaryExpression` …
// `createIdentifierWithDiagnostic`)
// ---------------------------------------------------------------------------

impl<'a> Parser<'a> {
    /// `func (p *Parser) parsePrimaryExpression() *ast.Expression`
    fn parse_primary_expression(&mut self) -> NodeId {
        match self.token {
            Kind::NoSubstitutionTemplateLiteral => {
                if self
                    .scanner
                    .token_flags()
                    .intersects(TokenFlags::IS_INVALID)
                {
                    self.rescan_template_token(false /*isTaggedTemplate*/);
                }
                self.parse_literal_expression()
            }
            Kind::NumericLiteral | Kind::BigIntLiteral | Kind::StringLiteral => {
                self.parse_literal_expression()
            }
            Kind::ThisKeyword
            | Kind::SuperKeyword
            | Kind::NullKeyword
            | Kind::TrueKeyword
            | Kind::FalseKeyword => self.parse_keyword_expression(),
            Kind::OpenParenToken => self.parse_parenthesized_expression(),
            Kind::OpenBracketToken => self.parse_array_literal_expression(),
            Kind::OpenBraceToken => self.parse_object_literal_expression(),
            Kind::AsyncKeyword => {
                // Async arrow functions are parsed earlier in parseAssignmentExpressionOrHigher.
                // If we encounter `async [no LineTerminator here] function` then this is an async
                // function; otherwise, its an identifier.
                if !self.look_ahead(Self::next_token_is_function_keyword_on_same_line) {
                    self.parse_identifier_with_diagnostic(
                        Some(&diagnostics::Expression_expected),
                        None,
                    )
                } else {
                    self.parse_function_expression()
                }
            }
            Kind::AtToken => self.parse_decorated_expression(),
            Kind::ClassKeyword => self.parse_class_expression(),
            Kind::FunctionKeyword => self.parse_function_expression(),
            Kind::NewKeyword => self.parse_new_expression_or_new_dot_target(),
            Kind::SlashToken | Kind::SlashEqualsToken => {
                if self.rescan_slash_token() == Kind::RegularExpressionLiteral {
                    return self.parse_literal_expression();
                }
                self.parse_identifier_with_diagnostic(
                    Some(&diagnostics::Expression_expected),
                    None,
                )
            }
            Kind::TemplateHead => {
                self.parse_template_expression(false /*isTaggedTemplate*/)
            }
            Kind::PrivateIdentifier => self.parse_private_identifier(),
            _ => self.parse_identifier_with_diagnostic(
                Some(&diagnostics::Expression_expected),
                None,
            ),
        }
    }

    /// `func (p *Parser) parseParenthesizedExpression() *ast.Expression`
    fn parse_parenthesized_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        self.parse_expected(Kind::OpenParenToken);
        let expression = self.parse_expression_allow_in();
        self.parse_expected(Kind::CloseParenToken);
        let result = self.finish_node(
            self.factory
                .new_parenthesized_expression(&mut self.nodes, Some(expression)),
            pos,
        );
        self.with_jsdoc(result, jsdoc);
        result
    }

    /// `func (p *Parser) parseArrayLiteralExpression() *ast.Expression`
    fn parse_array_literal_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        let open_bracket_position = self.scanner.token_start() as i32;
        let open_bracket_parsed = self.parse_expected(Kind::OpenBracketToken);
        let multi_line = self.has_preceding_line_break();
        let elements = self.parse_delimited_list(
            PC_ARRAY_LITERAL_MEMBERS,
            Self::parse_argument_or_array_literal_element_some,
            false,
        );
        self.parse_expected_matching_brackets(
            Kind::OpenBracketToken,
            Kind::CloseBracketToken,
            open_bracket_parsed,
            open_bracket_position,
        );
        self.finish_node(
            self.factory
                .new_array_literal_expression(&mut self.nodes, elements, multi_line),
            pos,
        )
    }

    fn parse_argument_or_array_literal_element_some(&mut self) -> Option<NodeId> {
        Some(self.parse_argument_or_array_literal_element())
    }

    /// `func (p *Parser) parseObjectLiteralExpression() *ast.Expression`
    fn parse_object_literal_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        let open_brace_position = self.scanner.token_start() as i32;
        let open_brace_parsed = self.parse_expected(Kind::OpenBraceToken);
        let multi_line = self.has_preceding_line_break();
        let properties = self.parse_delimited_list(
            PC_OBJECT_LITERAL_MEMBERS,
            Self::parse_object_literal_element_some,
            false,
        );
        self.parse_expected_matching_brackets(
            Kind::OpenBraceToken,
            Kind::CloseBraceToken,
            open_brace_parsed,
            open_brace_position,
        );
        self.finish_node(
            self.factory
                .new_object_literal_expression(&mut self.nodes, properties, multi_line),
            pos,
        )
    }

    /// `func (p *Parser) parseObjectLiteralElement() *ast.Node`
    fn parse_object_literal_element(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        if self.parse_optional(Kind::DotDotDotToken) {
            let expression = self.parse_assignment_expression_or_higher();
            let result = self.finish_node(
                self.factory
                    .new_spread_assignment(&mut self.nodes, Some(expression)),
                pos,
            );
            self.with_jsdoc(result, jsdoc);
            return result;
        }
        let modifiers = self.parse_modifiers_ex(
            true,  /*allowDecorators*/
            false, /*permitConstAsModifier*/
            false, /*stopOnStartOfClassStaticBlock*/
        );
        if self.parse_contextual_modifier(Kind::GetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                Kind::GetAccessor,
                ParseFlags::NONE,
            );
        }
        if self.parse_contextual_modifier(Kind::SetKeyword) {
            return self.parse_accessor_declaration(
                pos,
                jsdoc,
                modifiers,
                Kind::SetAccessor,
                ParseFlags::NONE,
            );
        }
        let asterisk_token = self.parse_optional_token(Kind::AsteriskToken);
        let token_is_identifier = self.is_identifier();
        let name = self.parse_property_name();
        // Disallowing of optional property assignments and definite assignment assertion happens in the grammar checker.
        let mut postfix_token = self.parse_optional_token(Kind::QuestionToken);
        // Decorators, Modifiers, questionToken, and exclamationToken are not supported by property assignments and are reported in the grammar checker
        if postfix_token.is_none() {
            postfix_token = self.parse_optional_token(Kind::ExclamationToken);
        }
        if asterisk_token.is_some()
            || self.token == Kind::OpenParenToken
            || self.token == Kind::LessThanToken
        {
            return self.parse_method_declaration(
                pos,
                jsdoc,
                modifiers,
                asterisk_token,
                Some(name),
                postfix_token,
                None, /*diagnosticMessage*/
            );
        }
        // check if it is short-hand property assignment or normal property assignment
        // NOTE: if token is EqualsToken it is interpreted as CoverInitializedName production
        // CoverInitializedName[Yield] :
        //     IdentifierReference[?Yield] Initializer[In, ?Yield]
        // this is necessary because ObjectLiteral productions are also used to cover grammar for ObjectAssignmentPattern
        let is_shorthand_property_assignment =
            token_is_identifier && self.token != Kind::ColonToken;
        let node = if is_shorthand_property_assignment {
            let equals_token = self.parse_optional_token(Kind::EqualsToken);
            let mut initializer = None;
            if equals_token.is_some() {
                initializer = Some(self.do_in_context(
                    NodeFlags::DISALLOW_IN_CONTEXT,
                    false,
                    Self::parse_assignment_expression_or_higher,
                ));
            }
            self.factory.new_shorthand_property_assignment(
                &mut self.nodes,
                modifiers,
                Some(name),
                postfix_token,
                None, /*typeNode*/
                equals_token,
                initializer,
            )
        } else {
            self.parse_expected(Kind::ColonToken);
            let initializer = self.do_in_context(
                NodeFlags::DISALLOW_IN_CONTEXT,
                false,
                Self::parse_assignment_expression_or_higher,
            );
            self.factory.new_property_assignment(
                &mut self.nodes,
                modifiers,
                Some(name),
                postfix_token,
                None, /*typeNode*/
                Some(initializer),
            )
        };
        self.finish_node(node, pos);
        self.with_jsdoc(node, jsdoc);
        node
    }

    fn parse_object_literal_element_some(&mut self) -> Option<NodeId> {
        Some(self.parse_object_literal_element())
    }

    /// `func (p *Parser) parseFunctionExpression() *ast.Expression`
    fn parse_function_expression(&mut self) -> NodeId {
        // GeneratorExpression:
        //      function* BindingIdentifier [Yield][opt](FormalParameters[Yield]){ GeneratorBody }
        //
        // FunctionExpression:
        //      function BindingIdentifier[opt](FormalParameters){ FunctionBody }
        let save_context_flags = self.context_flags;
        self.set_context_flags(NodeFlags::DECORATOR_CONTEXT, false);
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers();
        self.parse_expected(Kind::FunctionKeyword);
        let asterisk_token = self.parse_optional_token(Kind::AsteriskToken);
        let is_generator = asterisk_token.is_some();
        let is_async = modifier_list_has_async(modifiers.as_ref(), &self.nodes);
        let signature_flags = (if is_generator {
            ParseFlags::YIELD
        } else {
            ParseFlags::NONE
        }) | (if is_async {
            ParseFlags::AWAIT
        } else {
            ParseFlags::NONE
        });
        let name = if is_generator && is_async {
            self.do_in_context(
                NodeFlags::YIELD_CONTEXT | NodeFlags::AWAIT_CONTEXT,
                true,
                Self::parse_optional_binding_identifier,
            )
        } else if is_generator {
            self.do_in_context(
                NodeFlags::YIELD_CONTEXT,
                true,
                Self::parse_optional_binding_identifier,
            )
        } else if is_async {
            self.do_in_context(
                NodeFlags::AWAIT_CONTEXT,
                true,
                Self::parse_optional_binding_identifier,
            )
        } else {
            self.parse_optional_binding_identifier()
        };
        let type_parameters = self.parse_type_parameters();
        let parameters = self.parse_parameters(signature_flags);
        let return_type = self.parse_return_type(Kind::ColonToken, false /*isType*/);
        let body = self.parse_function_block(signature_flags, None /*diagnosticMessage*/);
        self.context_flags = save_context_flags;
        let result = self.factory.new_function_expression(
            &mut self.nodes,
            modifiers,
            asterisk_token,
            name,
            type_parameters,
            Some(parameters),
            return_type,
            None, /*fullSignature*/
            Some(body),
        );
        self.finish_node(result, pos);
        self.with_jsdoc(result, jsdoc);
        self.check_js_syntax(result);
        result
    }

    /// `func (p *Parser) parseOptionalBindingIdentifier() *ast.Node`
    fn parse_optional_binding_identifier(&mut self) -> Option<NodeId> {
        if self.is_binding_identifier() {
            return Some(self.parse_binding_identifier());
        }
        None
    }

    /// `func (p *Parser) parseDecoratedExpression() *ast.Expression`
    fn parse_decorated_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        let jsdoc = self.jsdoc_scanner_info();
        let modifiers = self.parse_modifiers_ex(
            true,  /*allowDecorators*/
            false, /*permitConstAsModifier*/
            false, /*stopOnStartOfClassStaticBlock*/
        );
        if self.token == Kind::ClassKeyword {
            return self.parse_class_declaration_or_expression(
                pos,
                jsdoc,
                modifiers,
                Kind::ClassExpression,
            );
        }
        let node_pos = self.node_pos();
        self.parse_error_at(node_pos, node_pos, &diagnostics::Expression_expected, &[]);
        self.finish_node(
            self.factory.new_missing_declaration(&mut self.nodes, modifiers),
            pos,
        )
    }

    /// `func (p *Parser) unparseExpressionWithTypeArguments(expression, typeArguments, result)`
    fn unparse_expression_with_type_arguments(
        &mut self,
        expression: Option<NodeId>,
        type_arguments: Option<NodeList>,
        result: NodeId,
    ) {
        // force overwrite the `.Parent` of the expression and type arguments to erase the fact that they may have originally been parsed as an ExpressionWithTypeArguments and be parented to such
        if let Some(expression) = expression {
            self.nodes[expression].parent = Some(result);
        }
        if let Some(type_arguments) = type_arguments {
            for a in type_arguments.nodes.iter() {
                self.nodes[*a].parent = Some(result);
            }
        }
    }

    /// `func (p *Parser) parseNewExpressionOrNewDotTarget() *ast.Node`
    fn parse_new_expression_or_new_dot_target(&mut self) -> NodeId {
        let pos = self.node_pos();
        self.parse_expected(Kind::NewKeyword);
        if self.parse_optional(Kind::DotToken) {
            let name = self.parse_identifier_name();
            return self.finish_node(
                self.factory.new_meta_property(
                    &mut self.nodes,
                    Kind::NewKeyword,
                    Some(name),
                ),
                pos,
            );
        }
        let expression_pos = self.node_pos();
        let primary = self.parse_primary_expression();
        let mut expression =
            self.parse_member_expression_rest(expression_pos, primary, false);
        let mut type_arguments = None;
        // Absorb type arguments into NewExpression when preceding expression is ExpressionWithTypeArguments
        if self.nodes[expression].kind == Kind::ExpressionWithTypeArguments {
            let (ewta_expression, ewta_type_arguments) = {
                let ewta =
                    self.nodes[expression].as_expression_with_type_arguments();
                (ewta.expression, ewta.type_arguments.clone())
            };
            type_arguments = ewta_type_arguments;
            expression = ewta_expression.unwrap();
        }
        if self.token == Kind::QuestionDotToken {
            let arg = scanner_utils::get_text_of_node_from_source_text(
                self.source_text,
                expression,
                false,
                &self.nodes,
            )
            .into_owned();
            self.parse_error_at_current_token(
                &diagnostics::Invalid_optional_chain_from_new_expression_Did_you_mean_to_call_0,
                &[arg],
            );
        }
        let mut argument_list = None;
        if self.token == Kind::OpenParenToken {
            argument_list = self.parse_argument_list();
        }
        let result = self.finish_node(
            self.factory.new_new_expression(
                &mut self.nodes,
                Some(expression),
                type_arguments.clone(),
                argument_list,
            ),
            pos,
        );
        let result = self.check_js_syntax(result);
        self.unparse_expression_with_type_arguments(
            Some(expression),
            type_arguments,
            result,
        );
        result
    }

    /// `func (p *Parser) parseKeywordExpression() *ast.Node`
    fn parse_keyword_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        let result = self
            .factory
            .new_keyword_expression(&mut self.nodes, self.token);
        self.next_token();
        self.finish_node(result, pos)
    }

    /// `func (p *Parser) parseLiteralExpression() *ast.Node`
    pub fn parse_literal_expression(&mut self) -> NodeId {
        let pos = self.node_pos();
        let text = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
        let token_flags = self.scanner.token_flags();
        let result = match self.token {
            Kind::StringLiteral => {
                self.factory
                    .new_string_literal(&mut self.nodes, &text, token_flags)
            }
            Kind::NumericLiteral => {
                self.factory
                    .new_numeric_literal(&mut self.nodes, &text, token_flags)
            }
            Kind::BigIntLiteral => {
                self.factory
                    .new_big_int_literal(&mut self.nodes, &text, token_flags)
            }
            Kind::RegularExpressionLiteral => self
                .factory
                .new_regular_expression_literal(&mut self.nodes, &text, token_flags),
            Kind::NoSubstitutionTemplateLiteral => self
                .factory
                .new_no_substitution_template_literal(
                    &mut self.nodes,
                    &text,
                    token_flags,
                ),
            _ => panic!("Unhandled case in parseLiteralExpression"),
        };
        self.next_token();
        self.finish_node(result, pos)
    }

    /// `func (p *Parser) parseIdentifierNameErrorOnUnicodeEscapeSequence() *ast.Node`
    fn parse_identifier_name_error_on_unicode_escape_sequence(&mut self) -> NodeId {
        if self.scanner.has_unicode_escape() || self.scanner.has_extended_unicode_escape()
        {
            self.parse_error_at_current_token(
                &diagnostics::Unicode_escape_sequence_cannot_appear_here,
                &[],
            );
        }
        self.create_identifier(token_is_identifier_or_keyword(self.token))
    }

    /// `func (p *Parser) parseBindingIdentifier() *ast.Node`
    fn parse_binding_identifier(&mut self) -> NodeId {
        self.parse_binding_identifier_with_diagnostic(None)
    }

    /// `func (p *Parser) parseBindingIdentifierWithDiagnostic(privateIdentifierDiagnosticMessage)`
    fn parse_binding_identifier_with_diagnostic(
        &mut self,
        private_identifier_diagnostic_message: Option<&'static Message>,
    ) -> NodeId {
        let save_has_await_identifier = self.statement_has_await_identifier;
        let id = self.create_identifier_with_diagnostic(
            self.is_binding_identifier(),
            None, /*diagnosticMessage*/
            private_identifier_diagnostic_message,
        );
        self.statement_has_await_identifier = save_has_await_identifier;
        id
    }

    /// `func (p *Parser) parseIdentifierName() *ast.Node`
    pub fn parse_identifier_name(&mut self) -> NodeId {
        self.parse_identifier_name_with_diagnostic(None)
    }

    /// `func (p *Parser) parseIdentifierNameWithDiagnostic(diagnosticMessage)`
    fn parse_identifier_name_with_diagnostic(
        &mut self,
        diagnostic_message: Option<&'static Message>,
    ) -> NodeId {
        self.create_identifier_with_diagnostic(
            token_is_identifier_or_keyword(self.token),
            diagnostic_message,
            None,
        )
    }

    /// `func (p *Parser) parseIdentifier() *ast.Node`
    pub fn parse_identifier(&mut self) -> NodeId {
        self.parse_identifier_with_diagnostic(None, None)
    }

    /// `func (p *Parser) parseIdentifierWithDiagnostic(diagnosticMessage, privateIdentifierDiagnosticMessage)`
    fn parse_identifier_with_diagnostic(
        &mut self,
        diagnostic_message: Option<&'static Message>,
        private_identifier_diagnostic_message: Option<&'static Message>,
    ) -> NodeId {
        self.create_identifier_with_diagnostic(
            self.is_identifier(),
            diagnostic_message,
            private_identifier_diagnostic_message,
        )
    }

    /// `func (p *Parser) createIdentifier(isIdentifier bool) *ast.Node`
    pub fn create_identifier(&mut self, is_identifier: bool) -> NodeId {
        self.create_identifier_with_diagnostic(is_identifier, None, None)
    }

    /// `func (p *Parser) createIdentifierWithDiagnostic(isIdentifier, diagnosticMessage, privateIdentifierDiagnosticMessage)`
    fn create_identifier_with_diagnostic(
        &mut self,
        is_identifier: bool,
        diagnostic_message: Option<&'static Message>,
        private_identifier_diagnostic_message: Option<&'static Message>,
    ) -> NodeId {
        if is_identifier {
            let pos = if self.scanner.has_preceding_jsdoc_leading_asterisks() {
                self.scanner.token_start() as i32
            } else {
                self.node_pos()
            };
            let text = String::from_utf8_lossy(self.scanner.token_value()).into_owned();
            self.next_token_without_check();
            return self.finish_node(self.new_identifier(&text), pos);
        }
        if self.token == Kind::PrivateIdentifier {
            match private_identifier_diagnostic_message {
                Some(msg) => { self.parse_error_at_current_token(msg, &[]); }
                None => {
                    self.parse_error_at_current_token(
                        &diagnostics::Private_identifiers_are_not_allowed_outside_class_bodies,
                        &[],
                    );
                }
            }
            return self.create_identifier(true /*isIdentifier*/);
        }
        // Only for end of file because the error gets reported incorrectly on embedded script tags.
        let report_at_current_position = self.token == Kind::EndOfFile;
        if let Some(msg) = diagnostic_message {
            if report_at_current_position {
                let pos = self.scanner.token_full_start() as i32;
                self.parse_error_at(pos, pos, msg, &[]);
            } else {
                self.parse_error_at_current_token(msg, &[]);
            }
        } else if is_reserved_word(self.token) {
            let text = self.scanner.token_text().to_string();
            if report_at_current_position {
                let pos = self.scanner.token_full_start() as i32;
                self.parse_error_at(
                    pos,
                    pos,
                    &diagnostics::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here,
                    &[text],
                );
            } else {
                self.parse_error_at_current_token(
                    &diagnostics::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here,
                    &[text],
                );
            }
        } else if report_at_current_position {
            let pos = self.scanner.token_full_start() as i32;
            self.parse_error_at(pos, pos, &diagnostics::Identifier_expected, &[]);
        } else {
            self.parse_error_at_current_token(&diagnostics::Identifier_expected, &[]);
        }
        self.create_missing_identifier()
    }
}

// ---------------------------------------------------------------------------
// Predicate / helper section (Go `scanTypeMemberStart` … `inAwaitContext`)
// ---------------------------------------------------------------------------

impl<'a> Parser<'a> {
    fn parse_statement_some(&mut self) -> Option<NodeId> {
        Some(self.parse_statement())
    }

    /// `func (p *Parser) nextTokenIsSlash() bool`
    fn next_token_is_slash(&mut self) -> bool {
        self.next_token() == Kind::SlashToken
    }

    /// `func (p *Parser) scanTypeMemberStart() bool`
    fn scan_type_member_start(&mut self) -> bool {
        // Return true if we have the start of a signature member
        if self.token == Kind::OpenParenToken
            || self.token == Kind::LessThanToken
            || self.token == Kind::GetKeyword
            || self.token == Kind::SetKeyword
        {
            return true;
        }
        let mut id_token = false;
        // Eat up all modifiers, but hold on to the last one in case it is actually an identifier
        while self.token.is_modifier_kind() {
            id_token = true;
            self.next_token();
        }
        // Index signatures and computed property names are type members
        if self.token == Kind::OpenBracketToken {
            return true;
        }
        // Try to get the first property-like token following all modifiers
        if self.is_literal_property_name() {
            id_token = true;
            self.next_token();
        }
        // If we were able to get any potential identifier, check that it is
        // the start of a member declaration
        if id_token {
            return self.token == Kind::OpenParenToken
                || self.token == Kind::LessThanToken
                || self.token == Kind::QuestionToken
                || self.token == Kind::ColonToken
                || self.token == Kind::CommaToken
                || self.can_parse_semicolon();
        }
        false
    }

    /// `func (p *Parser) scanClassMemberStart() bool`
    fn scan_class_member_start(&mut self) -> bool {
        let mut id_token = Kind::Unknown;
        if self.token == Kind::AtToken {
            return true;
        }
        // Eat up all modifiers, but hold on to the last one in case it is actually an identifier.
        while self.token.is_modifier_kind() {
            id_token = self.token;
            // If the idToken is a class modifier (protected, private, public, and static), it is
            // certain that we are starting to parse class member. This allows better error recovery
            if is_class_member_modifier(id_token) {
                return true;
            }
            self.next_token();
        }
        if self.token == Kind::AsteriskToken {
            return true;
        }
        // Try to get the first property-like token following all modifiers.
        // This can either be an identifier or the 'get' or 'set' keywords.
        if self.is_literal_property_name() {
            id_token = self.token;
            self.next_token();
        }
        // Index signatures and computed properties are class members; we can parse.
        if self.token == Kind::OpenBracketToken {
            return true;
        }
        // If we were able to get any potential identifier...
        if id_token != Kind::Unknown {
            // If we have a non-keyword identifier, or if we have an accessor, then it's safe to parse.
            if !is_keyword(id_token)
                || id_token == Kind::SetKeyword
                || id_token == Kind::GetKeyword
            {
                return true;
            }
            // If it *is* a keyword, but not an accessor, check a little farther along
            // to see if it should actually be parsed as a class member.
            match self.token {
                Kind::OpenParenToken         // Method declaration
                | Kind::LessThanToken        // Generic Method declaration
                | Kind::ExclamationToken     // Non-null assertion on property name
                | Kind::ColonToken           // Type Annotation for declaration
                | Kind::EqualsToken          // Initializer for declaration
                | Kind::QuestionToken => {   // Not valid, but permitted so that it gets caught later on.
                    return true;
                }
                _ => {}
            }
            // Covers
            //  - Semicolons     (declaration termination)
            //  - Closing braces (end-of-class, must be declaration)
            //  - End-of-files   (not valid, but permitted so that it gets caught later on)
            //  - Line-breaks    (enabling *automatic semicolon insertion*)
            return self.can_parse_semicolon();
        }
        false
    }

    /// `func (p *Parser) canParseSemicolon() bool`
    pub fn can_parse_semicolon(&self) -> bool {
        // If there's a real semicolon, then we can always parse it out.
        // We can parse out an optional semicolon in ASI cases in the following cases.
        self.token == Kind::SemicolonToken
            || self.token == Kind::CloseBraceToken
            || self.token == Kind::EndOfFile
            || self.has_preceding_line_break()
    }

    /// `func (p *Parser) tryParseSemicolon() bool`
    fn try_parse_semicolon(&mut self) -> bool {
        if !self.can_parse_semicolon() {
            return false;
        }
        if self.token == Kind::SemicolonToken {
            // consume the semicolon if it was explicitly provided.
            self.next_token();
        }
        true
    }

    /// `func (p *Parser) parseSemicolon() bool`
    fn parse_semicolon(&mut self) -> bool {
        self.try_parse_semicolon() || self.parse_expected(Kind::SemicolonToken)
    }

    /// `func (p *Parser) isLiteralPropertyName() bool`
    fn is_literal_property_name(&self) -> bool {
        token_is_identifier_or_keyword(self.token)
            || self.token == Kind::StringLiteral
            || self.token == Kind::NumericLiteral
            || self.token == Kind::BigIntLiteral
    }

    /// `func (p *Parser) isStartOfStatement() bool`
    fn is_start_of_statement(&mut self) -> bool {
        match self.token {
            // 'catch' and 'finally' do not actually indicate that the code is part of a statement,
            // however, we say they are here so that we may gracefully parse them and error later.
            Kind::AtToken
            | Kind::SemicolonToken
            | Kind::OpenBraceToken
            | Kind::VarKeyword
            | Kind::LetKeyword
            | Kind::UsingKeyword
            | Kind::FunctionKeyword
            | Kind::ClassKeyword
            | Kind::EnumKeyword
            | Kind::IfKeyword
            | Kind::DoKeyword
            | Kind::WhileKeyword
            | Kind::ForKeyword
            | Kind::ContinueKeyword
            | Kind::BreakKeyword
            | Kind::ReturnKeyword
            | Kind::WithKeyword
            | Kind::SwitchKeyword
            | Kind::ThrowKeyword
            | Kind::TryKeyword
            | Kind::DebuggerKeyword
            | Kind::CatchKeyword
            | Kind::FinallyKeyword => true,
            Kind::ImportKeyword => {
                self.is_start_of_declaration()
                    || self.is_next_token_open_paren_or_less_than_or_dot()
            }
            Kind::ConstKeyword | Kind::ExportKeyword => self.is_start_of_declaration(),
            Kind::AsyncKeyword
            | Kind::DeclareKeyword
            | Kind::InterfaceKeyword
            | Kind::ModuleKeyword
            | Kind::NamespaceKeyword
            | Kind::TypeKeyword
            | Kind::GlobalKeyword
            | Kind::DeferKeyword
            | Kind::SourceKeyword => {
                // When these don't start a declaration, they're an identifier in an expression statement
                true
            }
            Kind::AccessorKeyword
            | Kind::PublicKeyword
            | Kind::PrivateKeyword
            | Kind::ProtectedKeyword
            | Kind::StaticKeyword
            | Kind::ReadonlyKeyword => {
                // When these don't start a declaration, they may be the start of a class member if an identifier
                // immediately follows. Otherwise they're an identifier in an expression statement.
                self.is_start_of_declaration()
                    || !self
                        .look_ahead(Self::next_token_is_identifier_or_keyword_on_same_line)
            }
            _ => self.is_start_of_expression(),
        }
    }

    /// `func (p *Parser) isStartOfDeclaration() bool`
    fn is_start_of_declaration(&mut self) -> bool {
        self.look_ahead(Self::scan_start_of_declaration)
    }

    /// `func (p *Parser) scanStartOfDeclaration() bool`
    fn scan_start_of_declaration(&mut self) -> bool {
        loop {
            match self.token {
                Kind::VarKeyword
                | Kind::LetKeyword
                | Kind::ConstKeyword
                | Kind::FunctionKeyword
                | Kind::ClassKeyword
                | Kind::EnumKeyword => return true,
                Kind::UsingKeyword => return self.is_using_declaration(),
                Kind::AwaitKeyword => return self.is_await_using_declaration(),
                // 'declare', 'module', 'namespace', 'interface'* and 'type' are all legal JavaScript identifiers;
                // however, an identifier cannot be followed by another identifier on the same line. This is what we
                // count on to parse out the respective declarations. For instance, we exploit this to say that
                //
                //    namespace n
                //
                // can be none other than the beginning of a namespace declaration, but need to respect that JavaScript sees
                //
                //    namespace
                //    n
                //
                // as the identifier 'namespace' on one line followed by the identifier 'n' on another.
                // We need to look one token ahead to see if it permissible to try parsing a declaration.
                //
                // *Note*: 'interface' is actually a strict mode reserved word.
                Kind::InterfaceKeyword
                | Kind::TypeKeyword
                | Kind::DeferKeyword
                | Kind::SourceKeyword => {
                    return self.next_token_is_identifier_on_same_line();
                }
                Kind::ModuleKeyword | Kind::NamespaceKeyword => {
                    return self.next_token_is_identifier_or_string_literal_on_same_line();
                }
                Kind::AbstractKeyword
                | Kind::AccessorKeyword
                | Kind::AsyncKeyword
                | Kind::DeclareKeyword
                | Kind::PrivateKeyword
                | Kind::ProtectedKeyword
                | Kind::PublicKeyword
                | Kind::ReadonlyKeyword => {
                    let previous_token = self.token;
                    self.next_token();
                    // ASI takes effect for this modifier.
                    if self.has_preceding_line_break() {
                        return false;
                    }
                    if previous_token == Kind::DeclareKeyword
                        && self.token == Kind::TypeKeyword
                    {
                        // If we see 'declare type', then commit to parsing a type alias. parseTypeAliasDeclaration will
                        // report Line_break_not_permitted_here if needed.
                        return true;
                    }
                    continue;
                }
                Kind::GlobalKeyword => {
                    self.next_token();
                    return self.token == Kind::OpenBraceToken
                        || self.token == Kind::Identifier
                        || self.token == Kind::ExportKeyword;
                }
                Kind::ImportKeyword => {
                    self.next_token();
                    return self.token == Kind::DeferKeyword
                        || self.token == Kind::SourceKeyword
                        || self.token == Kind::StringLiteral
                        || self.token == Kind::AsteriskToken
                        || self.token == Kind::OpenBraceToken
                        || token_is_identifier_or_keyword(self.token);
                }
                Kind::ExportKeyword => {
                    self.next_token();
                    if self.token == Kind::EqualsToken
                        || self.token == Kind::AsteriskToken
                        || self.token == Kind::OpenBraceToken
                        || self.token == Kind::DefaultKeyword
                        || self.token == Kind::AsKeyword
                        || self.token == Kind::AtToken
                    {
                        return true;
                    }
                    if self.token == Kind::TypeKeyword {
                        self.next_token();
                        return self.token == Kind::AsteriskToken
                            || self.token == Kind::OpenBraceToken
                            || (self.is_identifier()
                                && !self.has_preceding_line_break());
                    }
                    continue;
                }
                Kind::StaticKeyword => {
                    self.next_token();
                    continue;
                }
                _ => {}
            }
            return false;
        }
    }

    /// `func (p *Parser) isStartOfExpression() bool`
    pub fn is_start_of_expression(&mut self) -> bool {
        if self.is_start_of_left_hand_side_expression() {
            return true;
        }
        match self.token {
            Kind::PlusToken
            | Kind::MinusToken
            | Kind::TildeToken
            | Kind::ExclamationToken
            | Kind::DeleteKeyword
            | Kind::TypeOfKeyword
            | Kind::VoidKeyword
            | Kind::PlusPlusToken
            | Kind::MinusMinusToken
            | Kind::LessThanToken
            | Kind::AwaitKeyword
            | Kind::YieldKeyword
            | Kind::PrivateIdentifier
            | Kind::AtToken => {
                // Yield/await always starts an expression.  Either it is an identifier (in which case
                // it is definitely an expression).  Or it's a keyword (either because we're in
                // a generator or async function, or in strict mode (or both)) and it started a yield or await expression.
                return true;
            }
            _ => {}
        }
        // Error tolerance.  If we see the start of some binary operator, we consider
        // that the start of an expression.  That way we'll parse out a missing identifier,
        // give a good message about an identifier being missing, and then consume the
        // rest of the binary expression.
        if self.is_binary_operator() {
            return true;
        }
        self.is_identifier()
    }

    /// `func (p *Parser) isStartOfLeftHandSideExpression() bool`
    fn is_start_of_left_hand_side_expression(&mut self) -> bool {
        match self.token {
            Kind::ThisKeyword
            | Kind::SuperKeyword
            | Kind::NullKeyword
            | Kind::TrueKeyword
            | Kind::FalseKeyword
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::StringLiteral
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::TemplateHead
            | Kind::OpenParenToken
            | Kind::OpenBracketToken
            | Kind::OpenBraceToken
            | Kind::FunctionKeyword
            | Kind::ClassKeyword
            | Kind::NewKeyword
            | Kind::SlashToken
            | Kind::SlashEqualsToken
            | Kind::Identifier => true,
            Kind::ImportKeyword => {
                self.is_next_token_open_paren_or_less_than_or_dot()
            }
            _ => self.is_identifier(),
        }
    }

    /// `func (p *Parser) isStartOfType(inStartOfParameter bool) bool`
    pub fn is_start_of_type(&mut self, in_start_of_parameter: bool) -> bool {
        match self.token {
            Kind::AnyKeyword
            | Kind::UnknownKeyword
            | Kind::StringKeyword
            | Kind::NumberKeyword
            | Kind::BigIntKeyword
            | Kind::BooleanKeyword
            | Kind::ReadonlyKeyword
            | Kind::SymbolKeyword
            | Kind::UniqueKeyword
            | Kind::VoidKeyword
            | Kind::UndefinedKeyword
            | Kind::NullKeyword
            | Kind::ThisKeyword
            | Kind::TypeOfKeyword
            | Kind::NeverKeyword
            | Kind::OpenBraceToken
            | Kind::OpenBracketToken
            | Kind::LessThanToken
            | Kind::BarToken
            | Kind::AmpersandToken
            | Kind::NewKeyword
            | Kind::StringLiteral
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::TrueKeyword
            | Kind::FalseKeyword
            | Kind::ObjectKeyword
            | Kind::AsteriskToken
            | Kind::QuestionToken
            | Kind::ExclamationToken
            | Kind::DotDotDotToken
            | Kind::InferKeyword
            | Kind::ImportKeyword
            | Kind::AssertsKeyword
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::TemplateHead => true,
            Kind::FunctionKeyword => !in_start_of_parameter,
            Kind::MinusToken => {
                !in_start_of_parameter
                    && self.look_ahead(Self::next_token_is_numeric_or_big_int_literal)
            }
            Kind::OpenParenToken => {
                // Only consider '(' the start of a type if followed by ')', '...', an identifier, a modifier,
                // or something that starts a type. We don't want to consider things like '(1)' a type.
                !in_start_of_parameter
                    && self.look_ahead(Self::next_is_parenthesized_or_function_type)
            }
            _ => self.is_identifier(),
        }
    }

    /// `func (p *Parser) nextTokenIsNumericOrBigIntLiteral() bool`
    fn next_token_is_numeric_or_big_int_literal(&mut self) -> bool {
        self.next_token();
        self.token == Kind::NumericLiteral || self.token == Kind::BigIntLiteral
    }

    /// `func (p *Parser) nextIsParenthesizedOrFunctionType() bool`
    fn next_is_parenthesized_or_function_type(&mut self) -> bool {
        self.next_token();
        self.token == Kind::CloseParenToken
            || self.is_start_of_parameter(false /*isJSDocParameter*/)
            || self.is_start_of_type(false /*inStartOfParameter*/)
    }

    /// `func (p *Parser) isStartOfParameter(isJSDocParameter bool) bool`
    pub fn is_start_of_parameter(&mut self, is_jsdoc_parameter: bool) -> bool {
        self.token == Kind::DotDotDotToken
            || self.is_binding_identifier_or_private_identifier_or_pattern()
            || self.token.is_modifier_kind()
            || self.token == Kind::AtToken
            || self.is_start_of_type(!is_jsdoc_parameter)
    }

    /// `func (p *Parser) isBindingIdentifierOrPrivateIdentifierOrPattern() bool`
    fn is_binding_identifier_or_private_identifier_or_pattern(&self) -> bool {
        self.token == Kind::OpenBraceToken
            || self.token == Kind::OpenBracketToken
            || self.token == Kind::PrivateIdentifier
            || self.is_binding_identifier()
    }

    /// `func (p *Parser) isNextTokenOpenParenOrLessThanOrDot() bool`
    fn is_next_token_open_paren_or_less_than_or_dot(&mut self) -> bool {
        self.look_ahead(Self::next_token_is_open_paren_or_less_than_or_dot)
    }

    /// `func (p *Parser) nextTokenIsOpenParenOrLessThanOrDot() bool`
    fn next_token_is_open_paren_or_less_than_or_dot(&mut self) -> bool {
        matches!(
            self.next_token(),
            Kind::OpenParenToken | Kind::LessThanToken | Kind::DotToken
        )
    }

    /// `func (p *Parser) nextTokenIsIdentifierOnSameLine() bool`
    fn next_token_is_identifier_on_same_line(&mut self) -> bool {
        self.next_token();
        self.is_identifier() && !self.has_preceding_line_break()
    }

    /// `func (p *Parser) nextTokenIsIdentifierOrStringLiteralOnSameLine() bool`
    fn next_token_is_identifier_or_string_literal_on_same_line(&mut self) -> bool {
        self.next_token();
        (self.is_identifier() || self.token == Kind::StringLiteral)
            && !self.has_preceding_line_break()
    }

    /// `func (p *Parser) isIdentifier() bool` — ignores strict mode flag because
    /// we will report an error in type checker instead.
    pub fn is_identifier(&self) -> bool {
        if self.token == Kind::Identifier {
            return true;
        }
        // If we have a 'yield' keyword, and we're in the [yield] context, then 'yield' is
        // considered a keyword and is not an identifier.
        // If we have a 'await' keyword, and we're in the [Await] context, then 'await' is
        // considered a keyword and is not an identifier.
        if self.token == Kind::YieldKeyword && self.in_yield_context()
            || self.token == Kind::AwaitKeyword && self.in_await_context()
        {
            return false;
        }
        self.token > Kind::LAST_RESERVED_WORD
    }

    /// `func (p *Parser) isBindingIdentifier() bool`
    fn is_binding_identifier(&self) -> bool {
        // `let await`/`let yield` in [Yield] or [Await] are allowed here and disallowed in the binder.
        self.token == Kind::Identifier || self.token > Kind::LAST_RESERVED_WORD
    }

    /// `func (p *Parser) isImportAttributeName() bool`
    fn is_import_attribute_name(&self) -> bool {
        token_is_identifier_or_keyword(self.token)
            || self.token == Kind::StringLiteral
    }

    /// `func (p *Parser) isBinaryOperator() bool`
    fn is_binary_operator(&self) -> bool {
        if self.in_disallow_in_context() && self.token == Kind::InKeyword {
            return false;
        }
        get_binary_operator_precedence(self.token) != OperatorPrecedence::INVALID
    }

    /// `func (p *Parser) isValidHeritageClauseObjectLiteral() bool`
    fn is_valid_heritage_clause_object_literal(&mut self) -> bool {
        self.look_ahead(Self::next_is_valid_heritage_clause_object_literal)
    }

    /// `func (p *Parser) nextIsValidHeritageClauseObjectLiteral() bool`
    fn next_is_valid_heritage_clause_object_literal(&mut self) -> bool {
        if self.next_token() == Kind::CloseBraceToken {
            // if we see "extends {}" then only treat the {} as what we're extending (and not
            // the class body) if we have:
            //
            //      extends {} {
            //      extends {},
            //      extends {} extends
            //      extends {} implements
            let next = self.next_token();
            return next == Kind::CommaToken
                || next == Kind::OpenBraceToken
                || next == Kind::ExtendsKeyword
                || next == Kind::ImplementsKeyword;
        }
        true
    }

    /// `func (p *Parser) isHeritageClause() bool`
    fn is_heritage_clause(&self) -> bool {
        self.token == Kind::ExtendsKeyword || self.token == Kind::ImplementsKeyword
    }

    /// `func (p *Parser) isHeritageClauseExtendsOrImplementsKeyword() bool`
    fn is_heritage_clause_extends_or_implements_keyword(&mut self) -> bool {
        self.is_heritage_clause() && self.look_ahead(Self::next_is_start_of_expression)
    }

    /// `func (p *Parser) nextIsStartOfExpression() bool`
    fn next_is_start_of_expression(&mut self) -> bool {
        self.next_token();
        self.is_start_of_expression()
    }

    /// `func (p *Parser) isUsingDeclaration() bool`
    fn is_using_declaration(&mut self) -> bool {
        // 'using' always starts a lexical declaration if followed by an identifier. We also eagerly parse
        // |ObjectBindingPattern| so that we can report a grammar error during check. We don't parse out
        // |ArrayBindingPattern| since it potentially conflicts with element access (i.e., `using[x]`).
        self.look_ahead(|p| {
            p.next_token_is_binding_identifier_or_start_of_destructuring_on_same_line(
                false, /*disallowOf*/
            )
        })
    }

    /// `func (p *Parser) nextTokenIsEqualsOrSemicolonOrColonToken() bool`
    fn next_token_is_equals_or_semicolon_or_colon_token(&mut self) -> bool {
        self.next_token();
        self.token == Kind::EqualsToken
            || self.token == Kind::SemicolonToken
            || self.token == Kind::ColonToken
    }

    /// `func (p *Parser) nextTokenIsBindingIdentifierOrStartOfDestructuringOnSameLine(disallowOf)`
    fn next_token_is_binding_identifier_or_start_of_destructuring_on_same_line(
        &mut self,
        disallow_of: bool,
    ) -> bool {
        self.next_token();
        if disallow_of && self.token == Kind::OfKeyword {
            return self.look_ahead(
                Self::next_token_is_equals_or_semicolon_or_colon_token,
            );
        }
        (self.is_binding_identifier() || self.token == Kind::OpenBraceToken)
            && !self.has_preceding_line_break()
    }

    /// `func (p *Parser) nextTokenIsBindingIdentifierOrStartOfDestructuringOnSameLineDisallowOf() bool`
    fn next_token_is_binding_identifier_or_start_of_destructuring_on_same_line_disallow_of(
        &mut self,
    ) -> bool {
        self.next_token_is_binding_identifier_or_start_of_destructuring_on_same_line(
            true, /*disallowOf*/
        )
    }

    /// `func (p *Parser) isAwaitUsingDeclaration() bool`
    fn is_await_using_declaration(&mut self) -> bool {
        self.look_ahead(
            Self::next_is_using_keyword_then_binding_identifier_or_start_of_object_destructuring_on_same_line,
        )
    }

    /// `func (p *Parser) nextIsUsingKeywordThenBindingIdentifierOrStartOfObjectDestructuringOnSameLine() bool`
    fn next_is_using_keyword_then_binding_identifier_or_start_of_object_destructuring_on_same_line(
        &mut self,
    ) -> bool {
        self.next_token() == Kind::UsingKeyword
            && self.next_token_is_binding_identifier_or_start_of_destructuring_on_same_line(
                false, /*disallowOf*/
            )
    }

    /// `func (p *Parser) nextTokenIsTokenStringLiteral() bool`
    fn next_token_is_token_string_literal(&mut self) -> bool {
        self.next_token() == Kind::StringLiteral
    }

    /// `func (p *Parser) setContextFlags(flags ast.NodeFlags, value bool)`
    fn set_context_flags(&mut self, flags: NodeFlags, value: bool) {
        if value {
            self.context_flags |= flags;
        } else {
            self.context_flags &= !flags;
        }
    }

    /// `func (p *Parser) doInContext(flags, value, f)`
    fn do_in_context<T>(
        &mut self,
        flags: NodeFlags,
        value: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let save_context_flags = self.context_flags;
        self.set_context_flags(flags, value);
        let result = f(self);
        self.context_flags = save_context_flags;
        result
    }

    /// `func (p *Parser) inYieldContext() bool`
    fn in_yield_context(&self) -> bool {
        self.context_flags.intersects(NodeFlags::YIELD_CONTEXT)
    }

    /// `func (p *Parser) inDisallowInContext() bool`
    fn in_disallow_in_context(&self) -> bool {
        self.context_flags.intersects(NodeFlags::DISALLOW_IN_CONTEXT)
    }

    /// `func (p *Parser) inDisallowConditionalTypesContext() bool`
    fn in_disallow_conditional_types_context(&self) -> bool {
        self.context_flags
            .intersects(NodeFlags::DISALLOW_CONDITIONAL_TYPES_CONTEXT)
    }

    /// `func (p *Parser) inDecoratorContext() bool`
    fn in_decorator_context(&self) -> bool {
        self.context_flags.intersects(NodeFlags::DECORATOR_CONTEXT)
    }

    /// `func (p *Parser) inAwaitContext() bool`
    pub fn in_await_context(&self) -> bool {
        self.context_flags.intersects(NodeFlags::AWAIT_CONTEXT)
    }
}

// ---------------------------------------------------------------------------
// Source-file tail: pragmas, JS grammar checks (Go `skipRangeTrivia` … EOF)
// ---------------------------------------------------------------------------

impl<'a> Parser<'a> {
    /// `func (p *Parser) skipRangeTrivia(textRange core.TextRange) core.TextRange`
    fn skip_range_trivia(&self, text_range: TextRange) -> TextRange {
        TextRange::new(
            scanner::skip_trivia(self.source_text, text_range.pos()),
            text_range.end(),
        )
    }

    /// `func (p *Parser) processPragmasIntoFields(context *ast.SourceFile)`
    fn process_pragmas_into_fields(&mut self, context: NodeId) {
        let mut context_check_js_directive =
            self.nodes[context].as_source_file().check_js_directive;
        let mut referenced_files: Vec<tsc_ast::FileReference> = Vec::new();
        let mut type_reference_directives: Vec<tsc_ast::FileReference> = Vec::new();
        let mut lib_reference_directives: Vec<tsc_ast::FileReference> = Vec::new();
        let pragmas = self.nodes[context].as_source_file().pragmas.to_vec();
        for pragma in &pragmas {
            match pragma.name.as_str() {
                "reference" => {
                    let types = pragma.args.get("types");
                    let lib = pragma.args.get("lib");
                    let path = pragma.args.get("path");
                    let resolution_mode = pragma.args.get("resolution-mode");
                    let preserve = pragma.args.get("preserve");
                    let no_default_lib = pragma.args.get("no-default-lib");
                    let preserve_flag =
                        preserve.is_some_and(|p| p.value == "true");
                    if no_default_lib.is_some_and(|d| d.value == "true") {
                        // Ignored.
                    } else if let Some(types) = types {
                        let mut parsed = ModuleKind::None;
                        if let Some(resolution_mode) = resolution_mode {
                            parsed = self.parse_resolution_mode(
                                &resolution_mode.value,
                                resolution_mode.text_range.pos(),
                                resolution_mode.text_range.end(),
                            );
                        }
                        type_reference_directives.push(tsc_ast::FileReference {
                            text_range: types.text_range,
                            file_name: types.value.clone(),
                            resolution_mode: parsed,
                            preserve: preserve_flag,
                        });
                    } else if let Some(lib) = lib {
                        lib_reference_directives.push(tsc_ast::FileReference {
                            text_range: lib.text_range,
                            file_name: lib.value.clone(),
                            resolution_mode: ModuleKind::None,
                            preserve: preserve_flag,
                        });
                    } else if let Some(path) = path {
                        referenced_files.push(tsc_ast::FileReference {
                            text_range: path.text_range,
                            file_name: path.value.clone(),
                            resolution_mode: ModuleKind::None,
                            preserve: preserve_flag,
                        });
                    } else {
                        self.parse_error_at_range(
                            pragma.comment_range.text_range,
                            &diagnostics::Invalid_reference_directive_syntax,
                            &[],
                        );
                    }
                }
                "ts-check" | "ts-nocheck" => {
                    // _last_ of either nocheck or check in a file is the "winner"
                    if context_check_js_directive.is_none()
                        || pragma.comment_range.text_range.pos()
                            > context_check_js_directive
                                .as_ref()
                                .unwrap()
                                .range
                                .text_range
                                .pos()
                    {
                        context_check_js_directive = Some(tsc_ast::CheckJsDirective {
                            enabled: pragma.name == "ts-check",
                            range: pragma.comment_range,
                        });
                    }
                }
                "jsx" | "jsxfrag" | "jsximportsource" | "jsxruntime" => {
                    // Nothing to do here
                }
                _ => panic!("Unhandled pragma kind: {}", pragma.name),
            }
        }
        let sf = self.nodes[context].as_source_file_mut();
        sf.check_js_directive = context_check_js_directive;
        sf.referenced_files = referenced_files.into();
        sf.type_reference_directives = type_reference_directives.into();
        sf.lib_reference_directives = lib_reference_directives.into();
    }

    /// `func (p *Parser) parseResolutionMode(mode string, pos, end) core.ResolutionMode`
    fn parse_resolution_mode(&mut self, mode: &str, pos: i32, end: i32) -> ModuleKind {
        if mode == "import" {
            return ModuleKind::ESNext;
        }
        if mode == "require" {
            return ModuleKind::CommonJS;
        }
        self.parse_error_at(
            pos,
            end,
            &diagnostics::X_resolution_mode_should_be_either_require_or_import,
            &[],
        );
        ModuleKind::None
    }

    /// `func (p *Parser) jsErrorAtRange(loc, message, args...)`
    fn js_error_at_range(
        &mut self,
        loc: TextRange,
        message: &'static Message,
        args: &[String],
    ) {
        let range = TextRange::new(
            scanner::skip_trivia(self.source_text, loc.pos()),
            loc.end(),
        );
        self.js_diagnostics
            .push(new_diagnostic(None, range, message, args));
    }

    /// `func (p *Parser) checkJSDecoratorSyntax(node *ast.Node)`
    fn check_js_decorator_syntax(&mut self, node: NodeId) {
        let Some(modifier_nodes) = self.nodes[node].modifier_nodes() else {
            return;
        };
        let modifiers: Vec<NodeId> = modifier_nodes.to_vec();
        if modifiers.is_empty() {
            return;
        }
        if can_have_illegal_decorators(&self.nodes[node]) {
            for modifier in &modifiers {
                if is_decorator(&self.nodes[*modifier]) {
                    let loc = self.nodes[*modifier].loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::Decorators_are_not_valid_here,
                        &[],
                    );
                    break;
                }
            }
        } else if can_have_decorators(&self.nodes[node]) {
            let decorator_index = modifiers
                .iter()
                .position(|m| is_decorator(&self.nodes[*m]))
                .map(|i| i as i32)
                .unwrap_or(-1);
            if decorator_index >= 0 && is_class_declaration(&self.nodes[node]) {
                let export_index = modifiers
                    .iter()
                    .position(|m| is_export_modifier(&self.nodes[*m]))
                    .map(|i| i as i32)
                    .unwrap_or(-1);
                if export_index >= 0 {
                    let default_index = modifiers
                        .iter()
                        .position(|m| self.nodes[*m].kind == Kind::DefaultKeyword)
                        .map(|i| i as i32)
                        .unwrap_or(-1);
                    if decorator_index > export_index
                        && default_index >= 0
                        && decorator_index < default_index
                    {
                        // Decorator between `export` and `default`
                        let loc = self.nodes[modifiers[decorator_index as usize]].loc;
                        self.js_error_at_range(
                            loc,
                            &diagnostics::Decorators_are_not_valid_here,
                            &[],
                        );
                    } else if decorator_index < export_index {
                        // Find a trailing decorator after the export keyword
                        let mut trailing_decorator_index = -1i32;
                        for i in export_index as usize..modifiers.len() {
                            if is_decorator(&self.nodes[modifiers[i]]) {
                                trailing_decorator_index = i as i32;
                                break;
                            }
                        }
                        if trailing_decorator_index >= 0 {
                            let trailing_loc =
                                self.nodes[modifiers[trailing_decorator_index as usize]]
                                    .loc;
                            let leading_loc =
                                self.nodes[modifiers[decorator_index as usize]].loc;
                            let diag = new_diagnostic::<String>(
                                None,
                                TextRange::new(
                                    scanner::skip_trivia(
                                        self.source_text,
                                        trailing_loc.pos(),
                                    ),
                                    trailing_loc.end(),
                                ),
                                &diagnostics::Decorators_may_not_appear_after_export_or_export_default_if_they_also_appear_before_export,
                                &[],
                            );
                            let related = new_diagnostic::<String>(
                                None,
                                TextRange::new(
                                    scanner::skip_trivia(
                                        self.source_text,
                                        leading_loc.pos(),
                                    ),
                                    leading_loc.end(),
                                ),
                                &diagnostics::Decorator_used_before_export_here,
                                &[],
                            );
                            lock_diagnostic(&diag).add_related_info(Some(related));
                            self.js_diagnostics.push(diag);
                        }
                    }
                }
            }
        }
    }

    /// `func (p *Parser) checkJSSyntax(node *ast.Node) *ast.Node`
    pub fn check_js_syntax(&mut self, node: NodeId) -> NodeId {
        if !self.nodes[node].flags.intersects(NodeFlags::JAVA_SCRIPT_FILE)
            || self.nodes[node]
                .flags
                .intersects(NodeFlags::JSDOC | NodeFlags::REPARSED)
        {
            return node;
        }
        match self.nodes[node].kind {
            Kind::Parameter | Kind::PropertyDeclaration | Kind::MethodDeclaration => {
                self.check_js_question_token(node);
                self.check_js_signature_or_type(node);
            }
            Kind::MethodSignature
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::FunctionExpression
            | Kind::FunctionDeclaration
            | Kind::ArrowFunction
            | Kind::VariableDeclaration
            | Kind::IndexSignature => {
                self.check_js_signature_or_type(node);
            }
            Kind::ImportDeclaration => {
                if let Some(clause) = self.nodes[node].import_clause()
                    && self.nodes[clause].is_type_only()
                {
                    let loc = self.nodes[node].loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::X_0_declarations_can_only_be_used_in_TypeScript_files,
                        &["import type".to_string()],
                    );
                }
            }
            Kind::ExportDeclaration => {
                if self.nodes[node].is_type_only() {
                    let loc = self.nodes[node].loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::X_0_declarations_can_only_be_used_in_TypeScript_files,
                        &["export type".to_string()],
                    );
                }
            }
            Kind::ImportSpecifier => {
                if self.nodes[node].is_type_only() {
                    let loc = self.nodes[node].loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::X_0_declarations_can_only_be_used_in_TypeScript_files,
                        &["import...type".to_string()],
                    );
                }
            }
            Kind::ExportSpecifier => {
                if self.nodes[node].is_type_only() {
                    let loc = self.nodes[node].loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::X_0_declarations_can_only_be_used_in_TypeScript_files,
                        &["export...type".to_string()],
                    );
                }
            }
            Kind::ImportEqualsDeclaration => {
                let loc = self.nodes[node].loc;
                self.js_error_at_range(
                    loc,
                    &diagnostics::X_import_can_only_be_used_in_TypeScript_files,
                    &[],
                );
            }
            Kind::ExportAssignment => {
                if self.nodes[node].as_export_assignment().is_export_equals {
                    let loc = self.nodes[node].loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::X_export_can_only_be_used_in_TypeScript_files,
                        &[],
                    );
                }
            }
            Kind::HeritageClause => {
                if self.nodes[node].as_heritage_clause().token
                    == Kind::ImplementsKeyword
                {
                    let loc = self.nodes[node].loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::X_implements_clauses_can_only_be_used_in_TypeScript_files,
                        &[],
                    );
                }
            }
            Kind::InterfaceDeclaration => {
                let loc = self.nodes[self.nodes[node].name().unwrap()].loc;
                self.js_error_at_range(
                    loc,
                    &diagnostics::X_0_declarations_can_only_be_used_in_TypeScript_files,
                    &["interface".to_string()],
                );
            }
            Kind::ModuleDeclaration => {
                let loc = self.nodes[self.nodes[node].name().unwrap()].loc;
                let keyword = self.nodes[node].as_module_declaration().keyword;
                self.js_error_at_range(
                    loc,
                    &diagnostics::X_0_declarations_can_only_be_used_in_TypeScript_files,
                    &[scanner::token_to_string(keyword).to_string()],
                );
            }
            Kind::TypeAliasDeclaration => {
                let loc = self.nodes[self.nodes[node].name().unwrap()].loc;
                self.js_error_at_range(
                    loc,
                    &diagnostics::Type_aliases_can_only_be_used_in_TypeScript_files,
                    &[],
                );
            }
            Kind::EnumDeclaration => {
                let loc = self.nodes[self.nodes[node].name().unwrap()].loc;
                self.js_error_at_range(
                    loc,
                    &diagnostics::X_0_declarations_can_only_be_used_in_TypeScript_files,
                    &["enum".to_string()],
                );
            }
            Kind::NonNullExpression => {
                let loc = self.nodes[node].loc;
                self.js_error_at_range(
                    loc,
                    &diagnostics::Non_null_assertions_can_only_be_used_in_TypeScript_files,
                    &[],
                );
            }
            Kind::AsExpression => {
                let loc = self.nodes[self.nodes[node].type_().unwrap()].loc;
                self.js_error_at_range(
                    loc,
                    &diagnostics::Type_assertion_expressions_can_only_be_used_in_TypeScript_files,
                    &[],
                );
            }
            Kind::SatisfiesExpression => {
                let loc = self.nodes[self.nodes[node].type_().unwrap()].loc;
                self.js_error_at_range(
                    loc,
                    &diagnostics::Type_satisfaction_expressions_can_only_be_used_in_TypeScript_files,
                    &[],
                );
            }
            _ => {}
        }
        // Check decorator placement in JS files
        self.check_js_decorator_syntax(node);
        // Check absence of type parameters, type arguments and non-JavaScript modifiers
        match self.nodes[node].kind {
            Kind::ClassDeclaration
            | Kind::ClassExpression
            | Kind::MethodDeclaration
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::FunctionExpression
            | Kind::FunctionDeclaration
            | Kind::ArrowFunction => {
                if let Some(list) = self.nodes[node].type_parameter_list()
                    && core::some(&list.nodes, |n| {
                        !self.nodes[*n].flags.intersects(NodeFlags::REPARSED)
                    })
                {
                    let loc = list.loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::Type_parameter_declarations_can_only_be_used_in_TypeScript_files,
                        &[],
                    );
                }
                self.check_js_modifier_list(node);
            }
            Kind::VariableStatement | Kind::PropertyDeclaration => {
                self.check_js_modifier_list(node);
            }
            Kind::Parameter => {
                if let Some(modifier_nodes) = self.nodes[node].modifier_nodes()
                    && core::some(&modifier_nodes.to_vec(), |m| {
                        is_modifier(&self.nodes[*m])
                    })
                {
                    let loc = self.nodes[node].modifiers().unwrap().loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::Parameter_modifiers_can_only_be_used_in_TypeScript_files,
                        &[],
                    );
                }
            }
            Kind::CallExpression
            | Kind::NewExpression
            | Kind::ExpressionWithTypeArguments
            | Kind::JsxSelfClosingElement
            | Kind::JsxOpeningElement
            | Kind::TaggedTemplateExpression => {
                if let Some(list) = self.nodes[node].type_argument_list()
                    && core::some(&list.nodes, |n| {
                        !self.nodes[*n].flags.intersects(NodeFlags::REPARSED)
                    })
                {
                    let loc = list.loc;
                    self.js_error_at_range(
                        loc,
                        &diagnostics::Type_arguments_can_only_be_used_in_TypeScript_files,
                        &[],
                    );
                }
            }
            _ => {}
        }
        node
    }

    /// First arm of `checkJSSyntax`'s first switch — the `?`/`!` token check
    /// shared by `Parameter`, `PropertyDeclaration`, and `MethodDeclaration`
    /// before falling through to the signature/type check.
    fn check_js_question_token(&mut self, node: NodeId) {
        if let Some(token) = self.nodes[node].question_token(&self.nodes)
            && !self.nodes[token].flags.intersects(NodeFlags::REPARSED)
            && self.nodes[token].kind == Kind::QuestionToken
        {
            let loc = self.nodes[token].loc;
            self.js_error_at_range(
                loc,
                &diagnostics::The_0_modifier_can_only_be_used_in_TypeScript_files,
                &["?".to_string()],
            );
        }
    }

    /// The fallthrough-shared `ast.IsFunctionLike`/`node.Type()` check.
    fn check_js_signature_or_type(&mut self, node: NodeId) {
        if is_function_like(Some(node), &self.nodes) && self.nodes[node].body().is_none()
        {
            let loc = self.nodes[node].loc;
            self.js_error_at_range(
                loc,
                &diagnostics::Signature_declarations_can_only_be_used_in_TypeScript_files,
                &[],
            );
        } else if let Some(t) = self.nodes[node].type_()
            && !self.nodes[t].flags.intersects(NodeFlags::REPARSED)
        {
            let loc = self.nodes[t].loc;
            self.js_error_at_range(
                loc,
                &diagnostics::Type_annotations_can_only_be_used_in_TypeScript_files,
                &[],
            );
        }
    }

    /// The fallthrough-shared modifier check for `VariableStatement` /
    /// `PropertyDeclaration` (and the class/function kinds above).
    fn check_js_modifier_list(&mut self, node: NodeId) {
        let Some(modifier_nodes) = self.nodes[node].modifier_nodes() else {
            return;
        };
        let modifiers: Vec<NodeId> = modifier_nodes.to_vec();
        for modifier in modifiers {
            let m = &self.nodes[modifier];
            if !m.flags.intersects(NodeFlags::REPARSED)
                && m.kind != Kind::Decorator
                && !modifier_to_flag(m.kind).intersects(ModifierFlags::JAVA_SCRIPT)
            {
                let loc = m.loc;
                self.js_error_at_range(
                    loc,
                    &diagnostics::The_0_modifier_can_only_be_used_in_TypeScript_files,
                    &[scanner::token_to_string(m.kind).to_string()],
                );
            }
        }
    }
}

/// `func getCommentPragmas(f *ast.NodeFactory, sourceText string) []ast.Pragma`
pub fn get_comment_pragmas(
    f: &NodeFactory,
    source_text: &str,
) -> Vec<tsc_ast::Pragma> {
    let mut pragmas = Vec::new();
    for comment_range in scanner::get_leading_comment_ranges(f, source_text, 0) {
        let comment =
            &source_text[comment_range.text_range.pos() as usize..comment_range.text_range.end() as usize];
        pragmas.extend(extract_pragmas(comment_range, comment));
    }
    pragmas
}

/// `func extractPragmas(commentRange ast.CommentRange, text string) []ast.Pragma`
fn extract_pragmas(
    comment_range: CommentRange,
    text: &str,
) -> Vec<tsc_ast::Pragma> {
    let bytes = text.as_bytes();
    if comment_range.kind == Kind::SingleLineCommentTrivia {
        let mut pos = 2usize;
        let triple_slash = pragma_match(text, pos, "/");
        if triple_slash {
            pos += 1;
        }
        pos = skip_blanks(text, pos);
        if triple_slash && pragma_match(text, pos, "<") {
            let tag_name = extract_name(text, pos + 1);
            if tag_name != "reference" {
                return vec![];
            }
            pos += 10;
            let mut args = tsc_collections::OrderedMap::<
                String,
                tsc_ast::PragmaArgument,
            >::default();
            loop {
                pos = skip_blanks(text, pos);
                if pragma_match(text, pos, "/>") {
                    break;
                }
                let arg_name = extract_name(text, pos);
                if arg_name.is_empty() {
                    break;
                }
                pos = skip_blanks(text, pos + arg_name.len());
                if !pragma_match(text, pos, "=") {
                    break;
                }
                pos = skip_blanks(text, pos + 1);
                let Some((value, _)) = extract_quoted_string(text, pos) else {
                    break;
                };
                args.set(
                    arg_name.clone(),
                    tsc_ast::PragmaArgument {
                        name: arg_name,
                        value: value.clone(),
                        text_range: TextRange::new(
                            comment_range.text_range.pos() + pos as i32 + 1,
                            comment_range.text_range.pos() + pos as i32 + 1 + value.len() as i32,
                        ),
                    },
                );
                pos += value.len() + 2;
            }
            return vec![tsc_ast::Pragma {
                comment_range,
                name: "reference".to_string(),
                args,
            }];
        }
        if pragma_match(text, pos, "@") {
            pos += 1;
            let pragma_name = extract_name(text, pos);
            if !(pragma_name == "ts-check" || pragma_name == "ts-nocheck") {
                return vec![];
            }
            return vec![tsc_ast::Pragma {
                comment_range,
                name: pragma_name,
                args: Default::default(),
            }];
        }
    }
    if comment_range.kind == Kind::MultiLineCommentTrivia {
        let text = text.strip_suffix("*/").unwrap_or(text);
        let mut pos = 2usize;
        let mut pragmas = Vec::new();
        loop {
            match skip_to(text, pos, "@") {
                Some(p) => pos = p,
                None => break,
            }
            // Mirrors the /@(\S+)(\s+(?:\S.*)?)?$/gm pragma regex used by TypeScript: the '@'
            // must be immediately followed by a non-whitespace pragma name, and the remainder
            // of the line is consumed as that pragma's arguments. As a consequence, only the
            // first '@'-token on a line is considered, so an unrelated '@token' earlier on the
            // line (e.g. an email address) prevents a later '@jsx' on the same line from being
            // treated as a pragma.
            let name_pos = pos + 1;
            let name_end = skip_non_blanks(text, name_pos);
            if name_end == name_pos {
                pos += 1;
                continue;
            }
            let line_end = line_end_pos(text, pos);
            let pragma_name = text[name_pos..name_end].to_lowercase();
            if pragma_name == "jsx"
                || pragma_name == "jsxfrag"
                || pragma_name == "jsximportsource"
                || pragma_name == "jsxruntime"
            {
                let start = skip_blanks(text, name_end);
                let arg_end = skip_non_blanks(text, start);
                if arg_end != start {
                    let mut args = tsc_collections::OrderedMap::<
                        String,
                        tsc_ast::PragmaArgument,
                    >::default();
                    args.set(
                        "factory".to_string(),
                        tsc_ast::PragmaArgument {
                            name: "factory".to_string(),
                            value: text[start..arg_end].to_string(),
                            text_range: TextRange::new(
                                comment_range.text_range.pos() + start as i32,
                                comment_range.text_range.pos() + arg_end as i32,
                            ),
                        },
                    );
                    pragmas.push(tsc_ast::Pragma {
                        comment_range,
                        name: pragma_name,
                        args,
                    });
                }
            }
            pos = line_end;
        }
        return pragmas;
    }
    vec![]
}

/// `func match(text string, pos int, s string) bool`
fn pragma_match(text: &str, pos: usize, s: &str) -> bool {
    text.get(pos..).is_some_and(|t| t.starts_with(s))
}

/// `func skipBlanks(text string, pos int) int`
fn skip_blanks(text: &str, mut pos: usize) -> usize {
    let bytes = text.as_bytes();
    while pos < bytes.len() && (bytes[pos] == b' ' || bytes[pos] == b'\t') {
        pos += 1;
    }
    pos
}

/// `func skipNonBlanks(text string, pos int) int`
fn skip_non_blanks(text: &str, mut pos: usize) -> usize {
    let bytes = text.as_bytes();
    while pos < bytes.len()
        && bytes[pos] != b' '
        && bytes[pos] != b'\t'
        && bytes[pos] != b'\r'
        && bytes[pos] != b'\n'
    {
        pos += 1;
    }
    pos
}

/// `func skipTo(text string, pos int, s string) int`
fn skip_to(text: &str, pos: usize, s: &str) -> Option<usize> {
    if pos >= text.len() {
        return None;
    }
    text[pos..].find(s).map(|i| pos + i)
}

/// `func lineEndPos(text string, pos int) int`
fn line_end_pos(text: &str, mut pos: usize) -> usize {
    while pos < text.len() {
        let ch = text[pos..].chars().next().unwrap();
        if stringutil::is_line_break(ch) {
            return pos;
        }
        pos += ch.len_utf8();
    }
    text.len()
}

/// `func extractName(text string, pos int) string`
fn extract_name(text: &str, mut pos: usize) -> String {
    let bytes = text.as_bytes();
    let start = pos;
    while pos < bytes.len()
        && (bytes[pos].is_ascii_uppercase()
            || bytes[pos].is_ascii_lowercase()
            || bytes[pos] == b'-')
    {
        pos += 1;
    }
    text[start..pos].to_lowercase()
}

/// `func extractQuotedString(text string, pos int) (string, bool)`
fn extract_quoted_string(text: &str, pos: usize) -> Option<(String, usize)> {
    let bytes = text.as_bytes();
    if pos == bytes.len() {
        return None;
    }
    let quote = bytes[pos];
    if quote != b'\'' && quote != b'"' {
        return None;
    }
    let mut pos = pos + 1;
    let start = pos;
    while pos < bytes.len() && bytes[pos] != quote {
        pos += 1;
    }
    if pos == bytes.len() {
        return None;
    }
    Some((text[start..pos].to_string(), pos))
}

// ---------------------------------------------------------------------------
// List predicates (Go `isListElement` / `isListTerminator`)
// ---------------------------------------------------------------------------

impl<'a> Parser<'a> {
    /// `func (p *Parser) isListElement(parsingContext ParsingContext, inErrorRecovery bool) bool`
    fn is_list_element(&mut self, parsing_context: ParsingContext, in_error_recovery: bool) -> bool {
        match parsing_context {
            PC_SOURCE_ELEMENTS | PC_BLOCK_STATEMENTS | PC_SWITCH_CLAUSE_STATEMENTS => {
                // If we're in error recovery, then we don't want to treat ';' as an empty statement.
                // The problem is that ';' can show up in far too many contexts, and if we see one
                // and assume it's a statement, then we may bail out inappropriately from whatever
                // we're parsing.  For example, if we have a semicolon in the middle of a class, then
                // we really don't want to assume the class is over and we're on a statement in the
                // outer module.  We just want to consume and move on.
                !(self.token == Kind::SemicolonToken && in_error_recovery)
                    && self.is_start_of_statement()
            }
            PC_SWITCH_CLAUSES => {
                self.token == Kind::CaseKeyword || self.token == Kind::DefaultKeyword
            }
            PC_TYPE_MEMBERS => self.look_ahead(Self::scan_type_member_start),
            PC_CLASS_MEMBERS => {
                // We allow semicolons as class elements (as specified by ES6) as long as we're
                // not in error recovery.  If we're in error recovery, we don't want an errant
                // semicolon to be treated as a class member (since they're almost always used
                // for statements.
                self.look_ahead(Self::scan_class_member_start)
                    || self.token == Kind::SemicolonToken && !in_error_recovery
            }
            PC_ENUM_MEMBERS => {
                // Include open bracket computed properties. This technically also lets in indexers,
                // which would be a candidate for improved error reporting.
                self.token == Kind::OpenBracketToken || self.is_literal_property_name()
            }
            PC_OBJECT_LITERAL_MEMBERS => match self.token {
                // Not an object literal member, but don't want to close the object (see `tests/cases/fourslash/completionsDotInObjectLiteral.ts`)
                Kind::OpenBracketToken
                | Kind::AsteriskToken
                | Kind::DotDotDotToken
                | Kind::DotToken => true,
                _ => self.is_literal_property_name(),
            },
            PC_REST_PROPERTIES => self.is_literal_property_name(),
            PC_OBJECT_BINDING_ELEMENTS => {
                self.token == Kind::OpenBracketToken
                    || self.token == Kind::DotDotDotToken
                    || self.is_literal_property_name()
            }
            PC_IMPORT_ATTRIBUTES => self.is_import_attribute_name(),
            PC_HERITAGE_CLAUSE_ELEMENT => {
                // If we see `{ ... }` then only consume it as an expression if it is followed by `,` or `{`
                // That way we won't consume the body of a class in its heritage clause.
                if self.token == Kind::OpenBraceToken {
                    return self.is_valid_heritage_clause_object_literal();
                }
                if !in_error_recovery {
                    return self.is_start_of_left_hand_side_expression()
                        && !self.is_heritage_clause_extends_or_implements_keyword();
                }
                // If we're in error recovery we tighten up what we're willing to match.
                // That way we don't treat something like "this" as a valid heritage clause
                // element during recovery.
                self.is_identifier()
                    && !self.is_heritage_clause_extends_or_implements_keyword()
            }
            PC_VARIABLE_DECLARATIONS => {
                self.is_binding_identifier_or_private_identifier_or_pattern()
            }
            PC_ARRAY_BINDING_ELEMENTS => {
                self.token == Kind::CommaToken
                    || self.token == Kind::DotDotDotToken
                    || self.is_binding_identifier_or_private_identifier_or_pattern()
            }
            PC_TYPE_PARAMETERS => {
                self.token == Kind::InKeyword
                    || self.token == Kind::ConstKeyword
                    || self.is_identifier()
            }
            PC_ARRAY_LITERAL_MEMBERS => {
                // Not an array literal member, but don't want to close the array (see `tests/cases/fourslash/completionsDotInArrayLiteralInObjectLiteral.ts`)
                if self.token == Kind::CommaToken || self.token == Kind::DotToken {
                    return true;
                }
                self.token == Kind::DotDotDotToken || self.is_start_of_expression()
            }
            PC_ARGUMENT_EXPRESSIONS => {
                self.token == Kind::DotDotDotToken || self.is_start_of_expression()
            }
            PC_PARAMETERS => self.is_start_of_parameter(false /*isJSDocParameter*/),
            PC_JS_DOC_PARAMETERS => self.is_start_of_parameter(true /*isJSDocParameter*/),
            PC_TYPE_ARGUMENTS | PC_TUPLE_ELEMENT_TYPES => {
                self.token == Kind::CommaToken
                    || self.is_start_of_type(false /*inStartOfParameter*/)
            }
            PC_HERITAGE_CLAUSES => self.is_heritage_clause(),
            PC_IMPORT_OR_EXPORT_SPECIFIERS => {
                // bail out if the next token is [FromKeyword StringLiteral].
                // That means we're in something like `import { from "mod"`. Stop here can give better error message.
                if self.token == Kind::FromKeyword
                    && self.look_ahead(Self::next_token_is_token_string_literal)
                {
                    return false;
                }
                if self.token == Kind::StringLiteral {
                    return true; // For "arbitrary module namespace identifiers"
                }
                token_is_identifier_or_keyword(self.token)
            }
            PC_JSX_ATTRIBUTES => {
                token_is_identifier_or_keyword(self.token)
                    || self.token == Kind::OpenBraceToken
            }
            PC_JSX_CHILDREN => true,
            PC_JS_DOC_COMMENT => true,
            _ => panic!("Unhandled case in isListElement"),
        }
    }

    /// `func (p *Parser) isListTerminator(kind ParsingContext) bool`
    fn is_list_terminator(&mut self, kind: ParsingContext) -> bool {
        if self.token == Kind::EndOfFile {
            return true;
        }
        match kind {
            PC_BLOCK_STATEMENTS
            | PC_SWITCH_CLAUSES
            | PC_TYPE_MEMBERS
            | PC_CLASS_MEMBERS
            | PC_ENUM_MEMBERS
            | PC_OBJECT_LITERAL_MEMBERS
            | PC_OBJECT_BINDING_ELEMENTS
            | PC_IMPORT_OR_EXPORT_SPECIFIERS
            | PC_IMPORT_ATTRIBUTES => self.token == Kind::CloseBraceToken,
            PC_SWITCH_CLAUSE_STATEMENTS => {
                self.token == Kind::CloseBraceToken
                    || self.token == Kind::CaseKeyword
                    || self.token == Kind::DefaultKeyword
            }
            PC_HERITAGE_CLAUSE_ELEMENT => {
                self.token == Kind::OpenBraceToken
                    || self.token == Kind::ExtendsKeyword
                    || self.token == Kind::ImplementsKeyword
            }
            PC_VARIABLE_DECLARATIONS => {
                // If we can consume a semicolon (either explicitly, or with ASI), then consider us done
                // with parsing the list of variable declarators.
                // In the case where we're parsing the variable declarator of a 'for-in' statement, we
                // are done if we see an 'in' keyword in front of us. Same with for-of
                // ERROR RECOVERY TWEAK:
                // For better error recovery, if we see an '=>' then we just stop immediately.  We've got an
                // arrow function here and it's going to be very unlikely that we'll resynchronize and get
                // another variable declaration.
                self.can_parse_semicolon()
                    || self.token == Kind::InKeyword
                    || self.token == Kind::OfKeyword
                    || self.token == Kind::EqualsGreaterThanToken
            }
            PC_TYPE_PARAMETERS => {
                // Tokens other than '>' are here for better error recovery
                self.token == Kind::GreaterThanToken
                    || self.token == Kind::OpenParenToken
                    || self.token == Kind::OpenBraceToken
                    || self.token == Kind::ExtendsKeyword
                    || self.token == Kind::ImplementsKeyword
            }
            PC_ARGUMENT_EXPRESSIONS => {
                // Tokens other than ')' are here for better error recovery
                self.token == Kind::CloseParenToken
                    || self.token == Kind::SemicolonToken
            }
            PC_ARRAY_LITERAL_MEMBERS | PC_TUPLE_ELEMENT_TYPES
            | PC_ARRAY_BINDING_ELEMENTS => self.token == Kind::CloseBracketToken,
            PC_JS_DOC_PARAMETERS | PC_PARAMETERS | PC_REST_PROPERTIES => {
                // Tokens other than ')' and ']' (the latter for index signatures) are here for better error recovery
                self.token == Kind::CloseParenToken || self.token == Kind::CloseBracketToken
            }
            PC_TYPE_ARGUMENTS => {
                // All other tokens should cause the type-argument to terminate except comma token
                self.token != Kind::CommaToken
            }
            PC_HERITAGE_CLAUSES => {
                self.token == Kind::OpenBraceToken || self.token == Kind::CloseBraceToken
            }
            PC_JSX_ATTRIBUTES => {
                self.token == Kind::GreaterThanToken || self.token == Kind::SlashToken
            }
            PC_JSX_CHILDREN => {
                self.token == Kind::LessThanToken
                    && self.look_ahead(Self::next_token_is_slash)
            }
            _ => false,
        }
    }
}
