// Ported from tsc/internal/format/scanner.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::FindAncestorResult;
use tsc_ast::ast::Node;
use tsc_ast::find_ancestor_or_quit;
use tsc_ast::ids::NodeId;
use tsc_ast::is_trivia;
use tsc_ast::kind_generated::Kind;
use tsc_core::text::TextRange;
use tsc_scanner::scanner::Scanner;

/// `type TextRangeWithKind struct`
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct TextRangeWithKind {
    pub loc: TextRange,
    pub kind: Kind,
}

impl TextRangeWithKind {
    /// `NewTextRangeWithKind`
    pub fn new(pos: i32, end: i32, kind: Kind) -> TextRangeWithKind {
        TextRangeWithKind {
            loc: TextRange::new(pos, end),
            kind,
        }
    }
}

/// `type tokenInfo struct`
#[derive(Clone, Default)]
pub(crate) struct TokenInfo {
    pub leading_trivia: Vec<TextRangeWithKind>,
    pub token: TextRangeWithKind,
    pub trailing_trivia: Vec<TextRangeWithKind>,
}

/// `type formattingScanner struct`
///
/// PORT: `s` is a `Scanner<'a>` borrowing the source text; the worker is
/// driven by the caller (`format_span`) rather than being stored here.
pub(crate) struct FormattingScanner<'a> {
    pub s: Scanner<'a>,
    pub start_pos: i32,
    pub end_pos: i32,
    pub saved_pos: i32,
    pub has_last_token_info: bool,
    pub last_token_info: TokenInfo,
    pub last_scan_action: ScanAction,
    pub leading_trivia: Vec<TextRangeWithKind>,
    pub trailing_trivia: Vec<TextRangeWithKind>,
    pub was_new_line: bool,
}

/// `newFormattingScanner` — the constructor half; `worker.execute` is driven
/// by the caller in `format_span`.
pub(crate) fn new_formatting_scanner<'a>(
    text: &'a str,
    language_variant: tsc_core::languagevariant::LanguageVariant,
    start_pos: i32,
    end_pos: i32,
) -> FormattingScanner<'a> {
    let mut scan = Scanner::new();
    scan.set_skip_trivia(false);
    scan.set_language_variant(language_variant);
    scan.set_text(text);
    scan.reset_token_state(start_pos as usize);

    FormattingScanner {
        s: scan,
        start_pos,
        end_pos,
        saved_pos: 0,
        has_last_token_info: false,
        last_token_info: TokenInfo::default(),
        last_scan_action: ScanAction::Scan,
        leading_trivia: Vec::new(),
        trailing_trivia: Vec::new(),
        was_new_line: true,
    }
}

impl<'a> FormattingScanner<'a> {
    /// `(s *formattingScanner) advance`
    pub fn advance(&mut self) {
        self.has_last_token_info = false;
        let is_started = self.s.token_full_start() as i32 != self.start_pos;

        if is_started {
            self.was_new_line = !self.trailing_trivia.is_empty()
                && self.trailing_trivia.last().unwrap().kind == Kind::NewLineTrivia;
        } else {
            self.s.scan();
        }

        self.leading_trivia.clear();
        self.trailing_trivia.clear();

        let mut pos = self.s.token_full_start() as i32;

        // Read leading trivia and token
        while pos < self.end_pos {
            let t = self.s.token();
            if !is_trivia(t) {
                break;
            }

            // consume leading trivia
            self.s.scan();
            let item = TextRangeWithKind::new(pos, self.s.token_full_start() as i32, t);

            pos = self.s.token_full_start() as i32;

            self.leading_trivia.push(item);
        }

        self.saved_pos = self.s.token_full_start() as i32;
    }

    /// `(s *formattingScanner) shouldRescanJsxText`
    fn should_rescan_jsx_text(&self, node: NodeId, nodes: &[Node]) -> bool {
        if tsc_ast::is_jsx_text(&nodes[node]) {
            return true;
        }
        if !tsc_ast::is_jsx_element(&nodes[node]) || !self.has_last_token_info {
            return false;
        }

        self.last_token_info.token.kind == Kind::JsxText
    }

    /// `(s *formattingScanner) readTokenInfo`
    pub fn read_token_info(&mut self, n: NodeId, nodes: &[Node]) -> TokenInfo {
        debug_assert!(self.is_on_token());

        // normally scanner returns the smallest available token
        // check the kind of context node to determine if scanner should have more greedy behavior and consume more text.

        let expected_scan_action = if should_rescan_greater_than_token(&nodes[n]) {
            ScanAction::RescanGreaterThanToken
        } else if should_rescan_slash_token(&nodes[n]) {
            ScanAction::RescanSlashToken
        } else if should_rescan_template_token(&nodes[n]) {
            ScanAction::RescanTemplateToken
        } else if should_rescan_jsx_identifier(n, nodes) {
            ScanAction::RescanJsxIdentifier
        } else if self.should_rescan_jsx_text(n, nodes) {
            ScanAction::RescanJsxText
        } else if should_rescan_jsx_attribute_value(n, nodes) {
            ScanAction::RescanJsxAttributeValue
        } else {
            ScanAction::Scan
        };

        if self.has_last_token_info && expected_scan_action == self.last_scan_action {
            // readTokenInfo was called before with the same expected scan action.
            // No need to re-scan text, return existing 'lastTokenInfo'
            // it is ok to call fixTokenKind here since it does not affect
            // what portion of text is consumed. In contrast rescanning can change it,
            // i.e. for '>=' when originally scanner eats just one character
            // and rescanning forces it to consume more.
            self.last_token_info = fix_token_kind(self.last_token_info.clone(), &nodes[n]);
            return self.last_token_info.clone();
        }

        if self.s.token_full_start() as i32 != self.saved_pos {
            // readTokenInfo was called before but scan action differs - rescan text
            self.s.reset_token_state(self.saved_pos as usize);
            self.s.scan();
        }

        let mut current_token = self.get_next_token(n, expected_scan_action, nodes);

        let token = TextRangeWithKind::new(
            self.s.token_full_start() as i32,
            self.s.token_end() as i32,
            current_token,
        );

        // consume trailing trivia
        self.trailing_trivia.clear();
        while (self.s.token_full_start() as i32) < self.end_pos {
            current_token = self.s.scan();
            if !is_trivia(current_token) {
                break;
            }
            let trivia = TextRangeWithKind::new(
                self.s.token_full_start() as i32,
                self.s.token_end() as i32,
                current_token,
            );

            self.trailing_trivia.push(trivia);

            if current_token == Kind::NewLineTrivia {
                // move past new line
                self.s.scan();
                break;
            }
        }

        self.has_last_token_info = true;
        self.last_token_info = TokenInfo {
            leading_trivia: self.leading_trivia.clone(),
            token,
            trailing_trivia: self.trailing_trivia.clone(),
        };
        self.last_token_info = fix_token_kind(self.last_token_info.clone(), &nodes[n]);

        self.last_token_info.clone()
    }

    /// `(s *formattingScanner) getNextToken`
    fn get_next_token(
        &mut self,
        n: NodeId,
        expected_scan_action: ScanAction,
        nodes: &[Node],
    ) -> Kind {
        let token = self.s.token();
        self.last_scan_action = ScanAction::Scan;
        match expected_scan_action {
            ScanAction::RescanGreaterThanToken => {
                if token == Kind::GreaterThanToken {
                    self.last_scan_action = ScanAction::RescanGreaterThanToken;
                    let new_token = self.s.rescan_greater_than_token();
                    debug_assert!(nodes[n].kind == new_token);
                    return new_token;
                }
            }
            ScanAction::RescanSlashToken => {
                if starts_with_slash_token(token) {
                    self.last_scan_action = ScanAction::RescanSlashToken;
                    let new_token = self.s.rescan_slash_token(false);
                    debug_assert!(nodes[n].kind == new_token);
                    return new_token;
                }
            }
            ScanAction::RescanTemplateToken => {
                if token == Kind::CloseBraceToken {
                    self.last_scan_action = ScanAction::RescanTemplateToken;
                    return self.s.rescan_template_token(false /*isTaggedTemplate*/);
                }
            }
            ScanAction::RescanJsxIdentifier => {
                self.last_scan_action = ScanAction::RescanJsxIdentifier;
                return self.s.scan_jsx_identifier();
            }
            ScanAction::RescanJsxText => {
                self.last_scan_action = ScanAction::RescanJsxText;
                return self.s.rescan_jsx_token(false /*allowMultilineJsxText*/);
            }
            ScanAction::RescanJsxAttributeValue => {
                self.last_scan_action = ScanAction::RescanJsxAttributeValue;
                return self.s.rescan_jsx_attribute_value();
            }
            ScanAction::Scan => {
                // no rescan needed; the token was already produced by the normal scan
            }
        }
        token
    }

    /// `(s *formattingScanner) readEOFTokenRange`
    pub fn read_eof_token_range(&self) -> TextRangeWithKind {
        debug_assert!(self.is_on_eof());
        TextRangeWithKind::new(
            self.s.token_full_start() as i32,
            self.s.token_end() as i32,
            Kind::EndOfFile,
        )
    }

    /// `(s *formattingScanner) isOnToken`
    pub fn is_on_token(&self) -> bool {
        let mut current = self.s.token();
        if self.has_last_token_info {
            current = self.last_token_info.token.kind;
        }
        current != Kind::EndOfFile && !is_trivia(current)
    }

    /// `(s *formattingScanner) isOnEOF`
    pub fn is_on_eof(&self) -> bool {
        let mut current = self.s.token();
        if self.has_last_token_info {
            current = self.last_token_info.token.kind;
        }
        current == Kind::EndOfFile
    }

    /// `(s *formattingScanner) skipToEndOf`
    pub fn skip_to_end_of(&mut self, r: &TextRange) {
        self.s.reset_token_state(r.end() as usize);
        self.saved_pos = self.s.token_full_start() as i32;
        self.last_scan_action = ScanAction::Scan;
        self.has_last_token_info = false;
        self.was_new_line = false;
        self.leading_trivia.clear();
        self.trailing_trivia.clear();
    }

    /// `(s *formattingScanner) skipToStartOf`
    pub fn skip_to_start_of(&mut self, r: &TextRange) {
        self.s.reset_token_state(r.pos() as usize);
        self.saved_pos = self.s.token_full_start() as i32;
        self.last_scan_action = ScanAction::Scan;
        self.has_last_token_info = false;
        self.was_new_line = false;
        self.leading_trivia.clear();
        self.trailing_trivia.clear();
    }

    /// `(s *formattingScanner) getCurrentLeadingTrivia`
    pub fn get_current_leading_trivia(&self) -> &[TextRangeWithKind] {
        &self.leading_trivia
    }

    /// `(s *formattingScanner) lastTrailingTriviaWasNewLine`
    pub fn last_trailing_trivia_was_new_line(&self) -> bool {
        self.was_new_line
    }

    /// `(s *formattingScanner) getTokenFullStart`
    pub fn get_token_full_start(&self) -> i32 {
        if self.has_last_token_info {
            return self.last_token_info.token.loc.pos();
        }
        self.s.token_full_start() as i32
    }

    /// `(s *formattingScanner) getStartPos` — TODO: redundant? (kept for parity)
    #[allow(dead_code)]
    pub fn get_start_pos(&self) -> i32 {
        self.get_token_full_start()
    }
}

/// `shouldRescanGreaterThanToken`
fn should_rescan_greater_than_token(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::GreaterThanEqualsToken
            | Kind::GreaterThanGreaterThanEqualsToken
            | Kind::GreaterThanGreaterThanGreaterThanEqualsToken
            | Kind::GreaterThanGreaterThanGreaterThanToken
            | Kind::GreaterThanGreaterThanToken
    )
}

/// `shouldRescanJsxIdentifier`
fn should_rescan_jsx_identifier(node: NodeId, nodes: &[Node]) -> bool {
    if let Some(parent) = nodes[node].parent {
        match nodes[parent].kind {
            Kind::JsxAttribute
            | Kind::JsxOpeningElement
            | Kind::JsxClosingElement
            | Kind::JsxSelfClosingElement
            | Kind::JsxNamespacedName => {
                // May parse an identifier like `module-layout`; that will be scanned as a keyword at first, but we should parse the whole thing to get an identifier.
                return nodes[node].kind.is_keyword_kind() || nodes[node].kind == Kind::Identifier;
            }
            Kind::PropertyAccessExpression => {
                // The leftmost name of a dotted JSX tag name (e.g. `a-b` in `<a-b.c>`) may contain hyphens, so rescan it as a JSX identifier.
                return (nodes[node].kind.is_keyword_kind()
                    || nodes[node].kind == Kind::Identifier)
                    && is_leftmost_jsx_tag_name(node, nodes);
            }
            _ => {}
        }
    }
    false
}

/// `isLeftmostJsxTagName`
fn is_leftmost_jsx_tag_name(node: NodeId, nodes: &[Node]) -> bool {
    find_ancestor_or_quit(Some(node), nodes, &mut |n: &Node, nodes: &[Node]| {
        let n_id = n.id;
        match nodes[n_id].parent {
            None => FindAncestorResult::Quit,
            Some(parent) => {
                if tsc_ast::is_jsx_tag_name(n_id, nodes) {
                    FindAncestorResult::True
                } else if tsc_ast::is_property_access_expression(&nodes[parent])
                    && nodes[parent].expression() == Some(n_id)
                {
                    FindAncestorResult::False
                } else {
                    FindAncestorResult::Quit
                }
            }
        }
    })
    .is_some()
}

/// `shouldRescanSlashToken`
fn should_rescan_slash_token(container: &Node) -> bool {
    container.kind == Kind::RegularExpressionLiteral
}

/// `shouldRescanTemplateToken`
fn should_rescan_template_token(container: &Node) -> bool {
    container.kind == Kind::TemplateMiddle || container.kind == Kind::TemplateTail
}

/// `shouldRescanJsxAttributeValue`
fn should_rescan_jsx_attribute_value(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].parent.is_some_and(|p| {
        tsc_ast::is_jsx_attribute(&nodes[p]) && nodes[p].initializer() == Some(node)
    })
}

/// `startsWithSlashToken`
fn starts_with_slash_token(t: Kind) -> bool {
    t == Kind::SlashToken || t == Kind::SlashEqualsToken
}

/// `type scanAction int`
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub(crate) enum ScanAction {
    #[default]
    Scan,
    RescanGreaterThanToken,
    RescanSlashToken,
    RescanTemplateToken,
    RescanJsxIdentifier,
    RescanJsxText,
    RescanJsxAttributeValue,
}

/// `fixTokenKind`
fn fix_token_kind(mut token_info: TokenInfo, container: &Node) -> TokenInfo {
    if container.kind.is_token_kind() && token_info.token.kind != container.kind {
        token_info.token.kind = container.kind;
    }
    token_info
}
