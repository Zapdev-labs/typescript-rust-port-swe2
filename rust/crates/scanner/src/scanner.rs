// Ported from tsc/internal/scanner/scanner.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - Go `int` positions are `usize` byte offsets inside `Scanner` (matching
//   regexp.rs); the standalone helpers that mirror Go APIs taking `pos int`
//   (e.g. `skip_trivia`, `get_token_pos_of_node`) keep `TextPos`/`i32` at
//   their boundaries. The negative-position panics in `ResetPos` /
//   `isConflictMarkerTrivia` are unrepresentable with `usize` (callers cannot
//   pass them).
// - `token_value` is `Vec<u8>` (Go `string`): cooked string/identifier values
//   may carry lone UTF-16 surrogates encoded as surrogate sentinels via
//   `stringutil::encode_js_string_rune`, which is encoded as a private-use sentinel (see stringutil::encode_js_string_rune). The same
//   convention was already established by `regexp.rs`.
// - `text` is `&'a str` (SPEC §5.6: source text is UTF-8). The invalid-UTF-8
//   `File_appears_to_be_binary` path is retained for Go parity; it is
//   unreachable on `&str` input.
// - The `on_error` callback is `Option<Box<ErrorCallback<'a>>>` — a borrowed
//   trait object would force the same lifetime onto `text`.

use rustc_hash::FxHashMap;
use tsc_ast::ast_generated::{SourceFile, is_jsx_text};
use tsc_ast::kind_generated::Kind;
use tsc_ast::nodeflags::NodeFlags;
use tsc_ast::tokenflags::TokenFlags;
use tsc_ast::utilities::{
    get_name_of_declaration, is_js_doc_node, node_is_missing, position_is_synthesized,
};
use tsc_ast::{CommentDirective, CommentDirectiveKind, CommentRange, Node, NodeFactory, NodeId};
use tsc_core::core::{UTF16Offset, if_else, utf16_len};
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::ScriptTarget;
use tsc_core::text::{TextPos, TextRange};
use tsc_debug as debug;
use tsc_diagnostics::{self as diagnostics, Message};
use tsc_jsnum as jsnum;
use tsc_stringutil as stringutil;

use crate::regexp::{RegExpParser, scan_regular_expression_flags};
use crate::utilities::token_is_identifier_or_keyword;

/// `type identifierVariant int32`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum IdentifierVariant {
    Standard,
    Jsx,
    RegExpGroupName,
}

/// `type EscapeSequenceScanningFlags int32`
pub type EscapeSequenceScanningFlags = u32;

pub const ESCAPE_SEQUENCE_SCANNING_FLAGS_STRING: EscapeSequenceScanningFlags = 1 << 0;
pub const ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_ERRORS: EscapeSequenceScanningFlags = 1 << 1;
pub const ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION: EscapeSequenceScanningFlags = 1 << 2;
pub const ESCAPE_SEQUENCE_SCANNING_FLAGS_ANNEX_B: EscapeSequenceScanningFlags = 1 << 3;
pub const ESCAPE_SEQUENCE_SCANNING_FLAGS_ANY_UNICODE_MODE: EscapeSequenceScanningFlags = 1 << 4;
pub const ESCAPE_SEQUENCE_SCANNING_FLAGS_ATOM_ESCAPE: EscapeSequenceScanningFlags = 1 << 5;
pub const ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS: EscapeSequenceScanningFlags =
    ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION | ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_ERRORS;
pub const ESCAPE_SEQUENCE_SCANNING_FLAGS_ALLOW_EXTENDED_UNICODE_ESCAPE:
    EscapeSequenceScanningFlags =
    ESCAPE_SEQUENCE_SCANNING_FLAGS_STRING | ESCAPE_SEQUENCE_SCANNING_FLAGS_ANY_UNICODE_MODE;

/// `type ErrorCallback func(diagnostic *diagnostics.Message, start, length int, args ...any)`
///
/// PORT: Go's `args ...any` becomes `&[String]` — diagnostics emitted by the
/// scanner take string or pre-stringified integer args only. (Declared here to
/// match Go, which defines it in scanner.go; `regexp.rs` re-exports it.)
pub type ErrorCallback<'a> = dyn FnMut(&'static Message, usize, usize, &[String]) + 'a;

/// `var textToKeyword` — a match stands in for the Go map (identical lookups).
pub(crate) fn text_to_keyword(text: &[u8]) -> Option<Kind> {
    Some(match text {
        b"abstract" => Kind::AbstractKeyword,
        b"accessor" => Kind::AccessorKeyword,
        b"any" => Kind::AnyKeyword,
        b"as" => Kind::AsKeyword,
        b"asserts" => Kind::AssertsKeyword,
        b"assert" => Kind::AssertKeyword,
        b"bigint" => Kind::BigIntKeyword,
        b"boolean" => Kind::BooleanKeyword,
        b"break" => Kind::BreakKeyword,
        b"case" => Kind::CaseKeyword,
        b"catch" => Kind::CatchKeyword,
        b"class" => Kind::ClassKeyword,
        b"continue" => Kind::ContinueKeyword,
        b"const" => Kind::ConstKeyword,
        b"constructor" => Kind::ConstructorKeyword,
        b"debugger" => Kind::DebuggerKeyword,
        b"declare" => Kind::DeclareKeyword,
        b"default" => Kind::DefaultKeyword,
        b"defer" => Kind::DeferKeyword,
        b"delete" => Kind::DeleteKeyword,
        b"do" => Kind::DoKeyword,
        b"else" => Kind::ElseKeyword,
        b"enum" => Kind::EnumKeyword,
        b"export" => Kind::ExportKeyword,
        b"extends" => Kind::ExtendsKeyword,
        b"false" => Kind::FalseKeyword,
        b"finally" => Kind::FinallyKeyword,
        b"for" => Kind::ForKeyword,
        b"from" => Kind::FromKeyword,
        b"function" => Kind::FunctionKeyword,
        b"get" => Kind::GetKeyword,
        b"if" => Kind::IfKeyword,
        b"immediate" => Kind::ImmediateKeyword,
        b"implements" => Kind::ImplementsKeyword,
        b"import" => Kind::ImportKeyword,
        b"in" => Kind::InKeyword,
        b"infer" => Kind::InferKeyword,
        b"instanceof" => Kind::InstanceOfKeyword,
        b"interface" => Kind::InterfaceKeyword,
        b"intrinsic" => Kind::IntrinsicKeyword,
        b"is" => Kind::IsKeyword,
        b"keyof" => Kind::KeyOfKeyword,
        b"let" => Kind::LetKeyword,
        b"module" => Kind::ModuleKeyword,
        b"namespace" => Kind::NamespaceKeyword,
        b"never" => Kind::NeverKeyword,
        b"new" => Kind::NewKeyword,
        b"null" => Kind::NullKeyword,
        b"number" => Kind::NumberKeyword,
        b"object" => Kind::ObjectKeyword,
        b"package" => Kind::PackageKeyword,
        b"private" => Kind::PrivateKeyword,
        b"protected" => Kind::ProtectedKeyword,
        b"public" => Kind::PublicKeyword,
        b"override" => Kind::OverrideKeyword,
        b"out" => Kind::OutKeyword,
        b"readonly" => Kind::ReadonlyKeyword,
        b"require" => Kind::RequireKeyword,
        b"global" => Kind::GlobalKeyword,
        b"return" => Kind::ReturnKeyword,
        b"satisfies" => Kind::SatisfiesKeyword,
        b"set" => Kind::SetKeyword,
        b"source" => Kind::SourceKeyword,
        b"static" => Kind::StaticKeyword,
        b"string" => Kind::StringKeyword,
        b"super" => Kind::SuperKeyword,
        b"switch" => Kind::SwitchKeyword,
        b"symbol" => Kind::SymbolKeyword,
        b"this" => Kind::ThisKeyword,
        b"throw" => Kind::ThrowKeyword,
        b"true" => Kind::TrueKeyword,
        b"try" => Kind::TryKeyword,
        b"type" => Kind::TypeKeyword,
        b"typeof" => Kind::TypeOfKeyword,
        b"undefined" => Kind::UndefinedKeyword,
        b"unique" => Kind::UniqueKeyword,
        b"unknown" => Kind::UnknownKeyword,
        b"using" => Kind::UsingKeyword,
        b"var" => Kind::VarKeyword,
        b"void" => Kind::VoidKeyword,
        b"while" => Kind::WhileKeyword,
        b"with" => Kind::WithKeyword,
        b"yield" => Kind::YieldKeyword,
        b"async" => Kind::AsyncKeyword,
        b"await" => Kind::AwaitKeyword,
        b"of" => Kind::OfKeyword,
        _ => return None,
    })
}

/// `var textToToken` — punctuation tokens plus `text_to_keyword`
/// (Go builds it with `maps.Copy(m, textToKeyword)`).
fn text_to_token(text: &[u8]) -> Option<Kind> {
    Some(match text {
        b"{" => Kind::OpenBraceToken,
        b"}" => Kind::CloseBraceToken,
        b"(" => Kind::OpenParenToken,
        b")" => Kind::CloseParenToken,
        b"[" => Kind::OpenBracketToken,
        b"]" => Kind::CloseBracketToken,
        b"." => Kind::DotToken,
        b"..." => Kind::DotDotDotToken,
        b";" => Kind::SemicolonToken,
        b"," => Kind::CommaToken,
        b"<" => Kind::LessThanToken,
        b">" => Kind::GreaterThanToken,
        b"<=" => Kind::LessThanEqualsToken,
        b">=" => Kind::GreaterThanEqualsToken,
        b"==" => Kind::EqualsEqualsToken,
        b"!=" => Kind::ExclamationEqualsToken,
        b"===" => Kind::EqualsEqualsEqualsToken,
        b"!==" => Kind::ExclamationEqualsEqualsToken,
        b"=>" => Kind::EqualsGreaterThanToken,
        b"+" => Kind::PlusToken,
        b"-" => Kind::MinusToken,
        b"**" => Kind::AsteriskAsteriskToken,
        b"*" => Kind::AsteriskToken,
        b"/" => Kind::SlashToken,
        b"%" => Kind::PercentToken,
        b"++" => Kind::PlusPlusToken,
        b"--" => Kind::MinusMinusToken,
        b"<<" => Kind::LessThanLessThanToken,
        b"</" => Kind::LessThanSlashToken,
        b">>" => Kind::GreaterThanGreaterThanToken,
        b">>>" => Kind::GreaterThanGreaterThanGreaterThanToken,
        b"&" => Kind::AmpersandToken,
        b"|" => Kind::BarToken,
        b"^" => Kind::CaretToken,
        b"!" => Kind::ExclamationToken,
        b"~" => Kind::TildeToken,
        b"&&" => Kind::AmpersandAmpersandToken,
        b"||" => Kind::BarBarToken,
        b"?" => Kind::QuestionToken,
        b"??" => Kind::QuestionQuestionToken,
        b"?." => Kind::QuestionDotToken,
        b":" => Kind::ColonToken,
        b"=" => Kind::EqualsToken,
        b"+=" => Kind::PlusEqualsToken,
        b"-=" => Kind::MinusEqualsToken,
        b"*=" => Kind::AsteriskEqualsToken,
        b"**=" => Kind::AsteriskAsteriskEqualsToken,
        b"/=" => Kind::SlashEqualsToken,
        b"%=" => Kind::PercentEqualsToken,
        b"<<=" => Kind::LessThanLessThanEqualsToken,
        b">>=" => Kind::GreaterThanGreaterThanEqualsToken,
        b">>>=" => Kind::GreaterThanGreaterThanGreaterThanEqualsToken,
        b"&=" => Kind::AmpersandEqualsToken,
        b"|=" => Kind::BarEqualsToken,
        b"^=" => Kind::CaretEqualsToken,
        b"||=" => Kind::BarBarEqualsToken,
        b"&&=" => Kind::AmpersandAmpersandEqualsToken,
        b"??=" => Kind::QuestionQuestionEqualsToken,
        b"@" => Kind::AtToken,
        b"#" => Kind::HashToken,
        b"`" => Kind::BacktickToken,
        _ => return text_to_keyword(text),
    })
}

/// `var tokenToText` — the inverse of `text_to_token`, built by reversal in
/// Go; here it is a match (kinds not in the map yield "" like Go's
/// zero-initialized `[KindCount]string`).
fn token_to_text(token: Kind) -> &'static str {
    match token {
        Kind::OpenBraceToken => "{",
        Kind::CloseBraceToken => "}",
        Kind::OpenParenToken => "(",
        Kind::CloseParenToken => ")",
        Kind::OpenBracketToken => "[",
        Kind::CloseBracketToken => "]",
        Kind::DotToken => ".",
        Kind::DotDotDotToken => "...",
        Kind::SemicolonToken => ";",
        Kind::CommaToken => ",",
        Kind::LessThanToken => "<",
        Kind::GreaterThanToken => ">",
        Kind::LessThanEqualsToken => "<=",
        Kind::GreaterThanEqualsToken => ">=",
        Kind::EqualsEqualsToken => "==",
        Kind::ExclamationEqualsToken => "!=",
        Kind::EqualsEqualsEqualsToken => "===",
        Kind::ExclamationEqualsEqualsToken => "!==",
        Kind::EqualsGreaterThanToken => "=>",
        Kind::PlusToken => "+",
        Kind::MinusToken => "-",
        Kind::AsteriskAsteriskToken => "**",
        Kind::AsteriskToken => "*",
        Kind::SlashToken => "/",
        Kind::PercentToken => "%",
        Kind::PlusPlusToken => "++",
        Kind::MinusMinusToken => "--",
        Kind::LessThanLessThanToken => "<<",
        Kind::LessThanSlashToken => "</",
        Kind::GreaterThanGreaterThanToken => ">>",
        Kind::GreaterThanGreaterThanGreaterThanToken => ">>>",
        Kind::AmpersandToken => "&",
        Kind::BarToken => "|",
        Kind::CaretToken => "^",
        Kind::ExclamationToken => "!",
        Kind::TildeToken => "~",
        Kind::AmpersandAmpersandToken => "&&",
        Kind::BarBarToken => "||",
        Kind::QuestionToken => "?",
        Kind::QuestionQuestionToken => "??",
        Kind::QuestionDotToken => "?.",
        Kind::ColonToken => ":",
        Kind::EqualsToken => "=",
        Kind::PlusEqualsToken => "+=",
        Kind::MinusEqualsToken => "-=",
        Kind::AsteriskEqualsToken => "*=",
        Kind::AsteriskAsteriskEqualsToken => "**=",
        Kind::SlashEqualsToken => "/=",
        Kind::PercentEqualsToken => "%=",
        Kind::LessThanLessThanEqualsToken => "<<=",
        Kind::GreaterThanGreaterThanEqualsToken => ">>=",
        Kind::GreaterThanGreaterThanGreaterThanEqualsToken => ">>>=",
        Kind::AmpersandEqualsToken => "&=",
        Kind::BarEqualsToken => "|=",
        Kind::CaretEqualsToken => "^=",
        Kind::BarBarEqualsToken => "||=",
        Kind::AmpersandAmpersandEqualsToken => "&&=",
        Kind::QuestionQuestionEqualsToken => "??=",
        Kind::AtToken => "@",
        Kind::HashToken => "#",
        Kind::BacktickToken => "`",
        Kind::AbstractKeyword => "abstract",
        Kind::AccessorKeyword => "accessor",
        Kind::AnyKeyword => "any",
        Kind::AsKeyword => "as",
        Kind::AssertsKeyword => "asserts",
        Kind::AssertKeyword => "assert",
        Kind::BigIntKeyword => "bigint",
        Kind::BooleanKeyword => "boolean",
        Kind::BreakKeyword => "break",
        Kind::CaseKeyword => "case",
        Kind::CatchKeyword => "catch",
        Kind::ClassKeyword => "class",
        Kind::ContinueKeyword => "continue",
        Kind::ConstKeyword => "const",
        Kind::ConstructorKeyword => "constructor",
        Kind::DebuggerKeyword => "debugger",
        Kind::DeclareKeyword => "declare",
        Kind::DefaultKeyword => "default",
        Kind::DeferKeyword => "defer",
        Kind::DeleteKeyword => "delete",
        Kind::DoKeyword => "do",
        Kind::ElseKeyword => "else",
        Kind::EnumKeyword => "enum",
        Kind::ExportKeyword => "export",
        Kind::ExtendsKeyword => "extends",
        Kind::FalseKeyword => "false",
        Kind::FinallyKeyword => "finally",
        Kind::ForKeyword => "for",
        Kind::FromKeyword => "from",
        Kind::FunctionKeyword => "function",
        Kind::GetKeyword => "get",
        Kind::IfKeyword => "if",
        Kind::ImmediateKeyword => "immediate",
        Kind::ImplementsKeyword => "implements",
        Kind::ImportKeyword => "import",
        Kind::InKeyword => "in",
        Kind::InferKeyword => "infer",
        Kind::InstanceOfKeyword => "instanceof",
        Kind::InterfaceKeyword => "interface",
        Kind::IntrinsicKeyword => "intrinsic",
        Kind::IsKeyword => "is",
        Kind::KeyOfKeyword => "keyof",
        Kind::LetKeyword => "let",
        Kind::ModuleKeyword => "module",
        Kind::NamespaceKeyword => "namespace",
        Kind::NeverKeyword => "never",
        Kind::NewKeyword => "new",
        Kind::NullKeyword => "null",
        Kind::NumberKeyword => "number",
        Kind::ObjectKeyword => "object",
        Kind::PackageKeyword => "package",
        Kind::PrivateKeyword => "private",
        Kind::ProtectedKeyword => "protected",
        Kind::PublicKeyword => "public",
        Kind::OverrideKeyword => "override",
        Kind::OutKeyword => "out",
        Kind::ReadonlyKeyword => "readonly",
        Kind::RequireKeyword => "require",
        Kind::GlobalKeyword => "global",
        Kind::ReturnKeyword => "return",
        Kind::SatisfiesKeyword => "satisfies",
        Kind::SetKeyword => "set",
        Kind::SourceKeyword => "source",
        Kind::StaticKeyword => "static",
        Kind::StringKeyword => "string",
        Kind::SuperKeyword => "super",
        Kind::SwitchKeyword => "switch",
        Kind::SymbolKeyword => "symbol",
        Kind::ThisKeyword => "this",
        Kind::ThrowKeyword => "throw",
        Kind::TrueKeyword => "true",
        Kind::TryKeyword => "try",
        Kind::TypeKeyword => "type",
        Kind::TypeOfKeyword => "typeof",
        Kind::UndefinedKeyword => "undefined",
        Kind::UniqueKeyword => "unique",
        Kind::UnknownKeyword => "unknown",
        Kind::UsingKeyword => "using",
        Kind::VarKeyword => "var",
        Kind::VoidKeyword => "void",
        Kind::WhileKeyword => "while",
        Kind::WithKeyword => "with",
        Kind::YieldKeyword => "yield",
        Kind::AsyncKeyword => "async",
        Kind::AwaitKeyword => "await",
        Kind::OfKeyword => "of",
        _ => "",
    }
}

/// `type ScannerState struct` — the rewindable scanner state embedded in
/// `Scanner` in Go; here `mark`/`rewind` copy it in and out by value.
#[derive(Clone, Default)]
pub struct ScannerState {
    pos: usize,
    full_start_pos: usize,
    token_start: usize,
    token: Kind,
    token_value: Vec<u8>,
    token_flags: TokenFlags,
    comment_directives: Vec<CommentDirective>,
    /// Leading asterisks to skip when scanning types inside JSDoc. Should be 0 outside JSDoc
    skip_jsdoc_leading_asterisks: i32,
}

/// `type Scanner struct`
pub struct Scanner<'a> {
    text: &'a str,
    end: usize,
    language_variant: LanguageVariant,
    script_target: ScriptTarget,
    on_error: Option<Box<ErrorCallback<'a>>>,
    skip_trivia: bool,
    // ==== embedded ScannerState ====
    pos: usize,
    full_start_pos: usize,
    token_start: usize,
    token: Kind,
    token_value: Vec<u8>,
    token_flags: TokenFlags,
    comment_directives: Vec<CommentDirective>,
    skip_jsdoc_leading_asterisks: i32,
    // ==============================
    number_cache: FxHashMap<Vec<u8>, Vec<u8>>,
    hex_number_cache: FxHashMap<Vec<u8>, Vec<u8>>,
    hex_digit_cache: FxHashMap<Vec<u8>, Vec<u8>>,
}

/// `func defaultScanner() Scanner`
fn default_scanner<'a>() -> Scanner<'a> {
    Scanner {
        text: "",
        end: 0,
        language_variant: LanguageVariant::default(),
        script_target: ScriptTarget::default(),
        on_error: None,
        skip_trivia: true,
        pos: 0,
        full_start_pos: 0,
        token_start: 0,
        token: Kind::default(),
        token_value: Vec::new(),
        token_flags: TokenFlags::NONE,
        comment_directives: Vec::new(),
        skip_jsdoc_leading_asterisks: 0,
        number_cache: FxHashMap::default(),
        hex_number_cache: FxHashMap::default(),
        hex_digit_cache: FxHashMap::default(),
    }
}

impl<'a> Scanner<'a> {
    /// `func NewScanner() *Scanner`
    pub fn new() -> Self {
        default_scanner()
    }

    /// `func (s *Scanner) Reset()` — keeps the caches' allocations like Go's
    /// `clear`.
    pub fn reset(&mut self) {
        self.number_cache.clear();
        self.hex_number_cache.clear();
        self.hex_digit_cache.clear();
        let number_cache = std::mem::take(&mut self.number_cache);
        let hex_number_cache = std::mem::take(&mut self.hex_number_cache);
        let hex_digit_cache = std::mem::take(&mut self.hex_digit_cache);
        *self = default_scanner();
        self.number_cache = number_cache;
        self.hex_number_cache = hex_number_cache;
        self.hex_digit_cache = hex_digit_cache;
    }

    /// `func (s *Scanner) Text() string`
    pub fn text(&self) -> &'a str {
        self.text
    }

    /// `func (s *Scanner) Token() ast.Kind`
    pub fn token(&self) -> Kind {
        self.token
    }

    /// `func (s *Scanner) TokenFlags() ast.TokenFlags`
    pub fn token_flags(&self) -> TokenFlags {
        self.token_flags
    }

    /// `func (s *Scanner) TokenFullStart() int`
    pub fn token_full_start(&self) -> usize {
        self.full_start_pos
    }

    /// `func (s *Scanner) TokenStart() int`
    pub fn token_start(&self) -> usize {
        self.token_start
    }

    /// `func (s *Scanner) TokenEnd() int`
    pub fn token_end(&self) -> usize {
        self.pos
    }

    /// `func (s *Scanner) TokenText() string`
    pub fn token_text(&self) -> &'a str {
        &self.text[self.token_start..self.pos]
    }

    /// `func (s *Scanner) TokenValue() string`
    ///
    /// PORT: returns bytes — cooked values may contain surrogate sentinel bytes
    /// for lone surrogates (see file header).
    pub fn token_value(&self) -> &[u8] {
        &self.token_value
    }

    /// `func (s *Scanner) TokenRange() core.TextRange`
    pub fn token_range(&self) -> TextRange {
        TextRange::new(self.token_start as i32, self.pos as i32)
    }

    /// `func (s *Scanner) CommentDirectives() []ast.CommentDirective`
    pub fn comment_directives(&self) -> &[CommentDirective] {
        &self.comment_directives
    }

    /// `func (s *Scanner) Mark() ScannerState`
    pub fn mark(&self) -> ScannerState {
        ScannerState {
            pos: self.pos,
            full_start_pos: self.full_start_pos,
            token_start: self.token_start,
            token: self.token,
            token_value: self.token_value.clone(),
            token_flags: self.token_flags,
            comment_directives: self.comment_directives.clone(),
            skip_jsdoc_leading_asterisks: self.skip_jsdoc_leading_asterisks,
        }
    }

    /// `func (s *Scanner) Rewind(state ScannerState)`
    pub fn rewind(&mut self, state: ScannerState) {
        self.pos = state.pos;
        self.full_start_pos = state.full_start_pos;
        self.token_start = state.token_start;
        self.token = state.token;
        self.token_value = state.token_value;
        self.token_flags = state.token_flags;
        self.comment_directives = state.comment_directives;
        self.skip_jsdoc_leading_asterisks = state.skip_jsdoc_leading_asterisks;
    }

    /// `func (s *Scanner) ResetPos(pos int)`
    ///
    /// PORT: Go panics on `pos < 0`; `usize` cannot express it.
    pub fn reset_pos(&mut self, pos: usize) {
        self.pos = pos;
        self.full_start_pos = pos;
        self.token_start = pos;
    }

    /// `func (s *Scanner) ResetTokenState(pos int)`
    pub fn reset_token_state(&mut self, pos: usize) {
        self.reset_pos(pos);
        self.token = Kind::Unknown;
        self.token_value.clear();
        self.token_flags = TokenFlags::NONE;
    }

    /// `func (scanner *Scanner) SetSkipJSDocLeadingAsterisks(skip bool)`
    pub fn set_skip_jsdoc_leading_asterisks(&mut self, skip: bool) {
        if skip {
            self.skip_jsdoc_leading_asterisks += 1;
        } else {
            self.skip_jsdoc_leading_asterisks -= 1;
        }
    }

    /// `func (scanner *Scanner) SetSkipTrivia(skip bool)`
    pub fn set_skip_trivia(&mut self, skip: bool) {
        self.skip_trivia = skip;
    }

    /// `func (s *Scanner) HasUnicodeEscape() bool`
    pub fn has_unicode_escape(&self) -> bool {
        self.token_flags.intersects(TokenFlags::UNICODE_ESCAPE)
    }

    /// `func (s *Scanner) HasExtendedUnicodeEscape() bool`
    pub fn has_extended_unicode_escape(&self) -> bool {
        self.token_flags
            .intersects(TokenFlags::EXTENDED_UNICODE_ESCAPE)
    }

    /// `func (s *Scanner) HasPrecedingLineBreak() bool`
    pub fn has_preceding_line_break(&self) -> bool {
        self.token_flags
            .intersects(TokenFlags::PRECEDING_LINE_BREAK)
    }

    /// `func (s *Scanner) HasPrecedingJSDocComment() bool`
    pub fn has_preceding_jsdoc_comment(&self) -> bool {
        self.token_flags
            .intersects(TokenFlags::PRECEDING_JSDOC_COMMENT)
    }

    /// `func (s *Scanner) HasPrecedingJSDocLeadingAsterisks() bool`
    pub fn has_preceding_jsdoc_leading_asterisks(&self) -> bool {
        self.token_flags
            .intersects(TokenFlags::PRECEDING_JSDOC_LEADING_ASTERISKS)
    }

    /// `func (s *Scanner) HasPrecedingJSDocWithDeprecatedTag() bool`
    pub fn has_preceding_jsdoc_with_deprecated_tag(&self) -> bool {
        self.token_flags
            .intersects(TokenFlags::PRECEDING_JSDOC_WITH_DEPRECATED)
    }

    /// `func (s *Scanner) HasPrecedingJSDocWithSeeOrLink() bool`
    pub fn has_preceding_jsdoc_with_see_or_link(&self) -> bool {
        self.token_flags
            .intersects(TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK)
    }

    /// `func (s *Scanner) scanJSDocCommentForTags` — scans a JSDoc comment for
    /// @deprecated, @see, and @link tags, setting the appropriate token flags.
    /// Called during scanning when a JSDoc comment is detected.
    fn scan_jsdoc_comment_for_tags(&mut self, mut comment_text: &'a str) {
        loop {
            let Some(i) = comment_text.find('@') else {
                return;
            };
            comment_text = &comment_text[i + 1..];
            if !self
                .token_flags
                .intersects(TokenFlags::PRECEDING_JSDOC_WITH_DEPRECATED)
                && has_jsdoc_tag(comment_text, &["deprecated"])
            {
                self.token_flags |= TokenFlags::PRECEDING_JSDOC_WITH_DEPRECATED;
            }
            if !self
                .token_flags
                .intersects(TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK)
                && has_jsdoc_tag(comment_text, &["see", "link", "linkcode", "linkplain"])
            {
                self.token_flags |= TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK;
            }
            if self.token_flags.contains(
                TokenFlags::PRECEDING_JSDOC_WITH_DEPRECATED
                    | TokenFlags::PRECEDING_JSDOC_WITH_SEE_OR_LINK,
            ) {
                return;
            }
        }
    }

    /// `func (s *Scanner) SetText(text string)`
    pub fn set_text(&mut self, text: &'a str) {
        self.text = text;
        self.end = text.len();
        // `s.ScannerState = ScannerState{}`
        self.pos = 0;
        self.full_start_pos = 0;
        self.token_start = 0;
        self.token = Kind::default();
        self.token_value = Vec::new();
        self.token_flags = TokenFlags::NONE;
        self.comment_directives = Vec::new();
        self.skip_jsdoc_leading_asterisks = 0;
    }

    /// `func (s *Scanner) SetOnError(errorCallback ErrorCallback)`
    pub fn set_on_error<F>(&mut self, error_callback: Option<F>)
    where
        F: FnMut(&'static Message, usize, usize, &[String]) + 'a,
    {
        self.on_error = error_callback.map(|f| -> Box<ErrorCallback<'a>> { Box::new(f) });
    }

    /// `func (s *Scanner) SetLanguageVariant(languageVariant core.LanguageVariant)`
    pub fn set_language_variant(&mut self, language_variant: LanguageVariant) {
        self.language_variant = language_variant;
    }

    /// `func (s *Scanner) SetScriptTarget(scriptTarget core.ScriptTarget)`
    pub fn set_script_target(&mut self, script_target: ScriptTarget) {
        self.script_target = script_target;
    }

    /// `func (s *Scanner) languageVersion() core.ScriptTarget`
    fn language_version(&self) -> ScriptTarget {
        if self.script_target == ScriptTarget::None {
            return ScriptTarget::LATEST;
        }
        self.script_target
    }

    /// `func (s *Scanner) error(diagnostic *diagnostics.Message)`
    fn error(&mut self, diagnostic: &'static Message) {
        self.error_at(diagnostic, self.pos, 0, &[]);
    }

    /// `func (s *Scanner) errorAt(diagnostic, pos, length, args...)`
    fn error_at(
        &mut self,
        diagnostic: &'static Message,
        pos: usize,
        length: usize,
        args: &[String],
    ) {
        if let Some(on_error) = self.on_error.as_deref_mut() {
            on_error(diagnostic, pos, length, args);
        }
    }

    // NOTE: even though this returns a rune, it only decodes the current byte.
    // It must be checked against utf8.RuneSelf to verify that a call to charAndSize
    // is not needed.
    /// `func (s *Scanner) char() rune`
    fn char(&self) -> i32 {
        if self.pos < self.end {
            return i32::from(self.text.as_bytes()[self.pos]);
        }
        -1
    }

    /// Byte view of `char()` for match sites; `None` is Go's -1.
    fn byte(&self) -> Option<u8> {
        if self.pos < self.end {
            Some(self.text.as_bytes()[self.pos])
        } else {
            None
        }
    }

    // NOTE: this returns a rune, but only decodes the byte at the offset.
    /// `func (s *Scanner) charAt(offset int) rune`
    fn char_at(&self, offset: usize) -> i32 {
        if self.pos + offset < self.end {
            return i32::from(self.text.as_bytes()[self.pos + offset]);
        }
        -1
    }

    /// `func (s *Scanner) charAndSize() (rune, int)` — full UTF-8 decode at
    /// the current position; `(RuneError, 0)` at end of text.
    fn char_and_size(&self) -> (i32, usize) {
        let bytes = self.text.as_bytes();
        if self.pos < bytes.len() {
            let b = bytes[self.pos];
            if b < 0x80 {
                return (i32::from(b), 1);
            }
            return decode_rune_in_string(&bytes[self.pos..]);
        }
        (RUNE_ERROR, 0)
    }

    /// `func (s *Scanner) scanASCIIWhile` — advances pos over the longest run
    /// of ASCII bytes for which `pred` holds; stops at end-of-text, the first
    /// non-ASCII byte, or the first byte where `pred` is false.
    fn scan_ascii_while(&mut self, pred: impl Fn(u8) -> bool) {
        let bytes = self.text.as_bytes();
        while self.pos < self.end {
            let b = bytes[self.pos];
            if b >= 0x80 || !pred(b) {
                break;
            }
            self.pos += 1;
        }
    }

    /// `func (s *Scanner) Scan() ast.Kind`
    pub fn scan(&mut self) -> Kind {
        self.full_start_pos = self.pos;
        self.token_flags = TokenFlags::NONE;
        loop {
            let ch = self.char();
            self.token_start = self.pos;

            match self.byte() {
                Some(b'\t' | b'\x0b' | b'\x0c' | b' ') => {
                    self.pos += 1;
                    if self.skip_trivia {
                        continue;
                    }
                    loop {
                        let (ch, size) = self.char_and_size();
                        if !is_white_space_single_line_rune(ch) {
                            break;
                        }
                        self.pos += size;
                    }
                    self.token = Kind::WhitespaceTrivia;
                }
                Some(b'\n' | b'\r') => {
                    self.token_flags |= TokenFlags::PRECEDING_LINE_BREAK;
                    if self.skip_trivia {
                        self.pos += 1;
                        self.scan_ascii_while(|b| b == b' ' || (b'\t'..=b'\r').contains(&b));
                        continue;
                    }
                    if self.byte() == Some(b'\r') && self.char_at(1) == i32::from(b'\n') {
                        self.pos += 2;
                    } else {
                        self.pos += 1;
                    }
                    self.token = Kind::NewLineTrivia;
                }
                Some(b'!') => {
                    if self.char_at(1) == i32::from(b'=') {
                        if self.char_at(2) == i32::from(b'=') {
                            self.pos += 3;
                            self.token = Kind::ExclamationEqualsEqualsToken;
                        } else {
                            self.pos += 2;
                            self.token = Kind::ExclamationEqualsToken;
                        }
                    } else {
                        self.pos += 1;
                        self.token = Kind::ExclamationToken;
                    }
                }
                Some(b'"' | b'\'') => {
                    self.token_value = self.scan_string(false /*jsxAttributeString*/);
                    self.token = Kind::StringLiteral;
                }
                Some(b'`') => {
                    self.token = self.scan_template_and_set_token_value(
                        false, /*shouldEmitInvalidEscapeError*/
                    );
                }
                Some(b'%') => {
                    if self.char_at(1) == i32::from(b'=') {
                        self.pos += 2;
                        self.token = Kind::PercentEqualsToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::PercentToken;
                    }
                }
                Some(b'&') => {
                    let next = self.char_at(1);
                    if next == i32::from(b'&') {
                        if self.char_at(2) == i32::from(b'=') {
                            self.pos += 3;
                            self.token = Kind::AmpersandAmpersandEqualsToken;
                        } else {
                            self.pos += 2;
                            self.token = Kind::AmpersandAmpersandToken;
                        }
                    } else if next == i32::from(b'=') {
                        self.pos += 2;
                        self.token = Kind::AmpersandEqualsToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::AmpersandToken;
                    }
                }
                Some(b'(') => {
                    self.pos += 1;
                    self.token = Kind::OpenParenToken;
                }
                Some(b')') => {
                    self.pos += 1;
                    self.token = Kind::CloseParenToken;
                }
                Some(b'*') => {
                    let next = self.char_at(1);
                    if next == i32::from(b'=') {
                        self.pos += 2;
                        self.token = Kind::AsteriskEqualsToken;
                    } else if next == i32::from(b'*') {
                        if self.char_at(2) == i32::from(b'=') {
                            self.pos += 3;
                            self.token = Kind::AsteriskAsteriskEqualsToken;
                        } else {
                            self.pos += 2;
                            self.token = Kind::AsteriskAsteriskToken;
                        }
                    } else {
                        self.pos += 1;
                        if self.skip_jsdoc_leading_asterisks != 0
                            && !self
                                .token_flags
                                .intersects(TokenFlags::PRECEDING_JSDOC_LEADING_ASTERISKS)
                            && self
                                .token_flags
                                .intersects(TokenFlags::PRECEDING_LINE_BREAK)
                        {
                            self.token_flags |= TokenFlags::PRECEDING_JSDOC_LEADING_ASTERISKS;
                            continue;
                        }
                        self.token = Kind::AsteriskToken;
                    }
                }
                Some(b'+') => {
                    let next = self.char_at(1);
                    if next == i32::from(b'=') {
                        self.pos += 2;
                        self.token = Kind::PlusEqualsToken;
                    } else if next == i32::from(b'+') {
                        self.pos += 2;
                        self.token = Kind::PlusPlusToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::PlusToken;
                    }
                }
                Some(b',') => {
                    self.pos += 1;
                    self.token = Kind::CommaToken;
                }
                Some(b'-') => {
                    let next = self.char_at(1);
                    if next == i32::from(b'=') {
                        self.pos += 2;
                        self.token = Kind::MinusEqualsToken;
                    } else if next == i32::from(b'-') {
                        self.pos += 2;
                        self.token = Kind::MinusMinusToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::MinusToken;
                    }
                }
                Some(b'.') => {
                    let next = self.char_at(1);
                    if is_digit(next) {
                        self.token = self.scan_number();
                    } else if next == i32::from(b'.') && self.char_at(2) == i32::from(b'.') {
                        self.pos += 3;
                        self.token = Kind::DotDotDotToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::DotToken;
                    }
                }
                Some(b'/') => {
                    // Single-line comment
                    if self.char_at(1) == i32::from(b'/') {
                        self.pos += 2;

                        loop {
                            self.scan_ascii_while(|b| b != b'\n' && b != b'\r');
                            let (ch1, size) = self.char_and_size();
                            if size == 0 || is_line_break_rune(ch1) {
                                break;
                            }
                            self.pos += size;
                        }

                        self.process_comment_directive(self.token_start, self.pos, false);

                        if self.skip_trivia {
                            continue;
                        }
                        self.token = Kind::SingleLineCommentTrivia;
                        return self.token;
                    }
                    // Multi-line comment
                    if self.char_at(1) == i32::from(b'*') {
                        self.pos += 2;
                        let is_jsdoc =
                            self.char() == i32::from(b'*') && self.char_at(1) != i32::from(b'/');

                        let mut comment_closed = false;
                        let mut last_line_start = self.token_start;
                        loop {
                            self.scan_ascii_while(|b| b != b'*' && b != b'\n' && b != b'\r');
                            let (ch1, size) = self.char_and_size();
                            if size == 0 {
                                break;
                            }

                            if ch1 == i32::from(b'*') && self.char_at(1) == i32::from(b'/') {
                                self.pos += 2;
                                comment_closed = true;
                                break;
                            }

                            self.pos += size;

                            if is_line_break_rune(ch1) {
                                last_line_start = self.pos;
                                self.token_flags |= TokenFlags::PRECEDING_LINE_BREAK;
                            }
                        }

                        if is_jsdoc {
                            self.token_flags |= TokenFlags::PRECEDING_JSDOC_COMMENT;
                            let comment_text = &self.text[self.token_start..self.pos];
                            self.scan_jsdoc_comment_for_tags(comment_text);
                        }

                        self.process_comment_directive(last_line_start, self.pos, true);

                        if !comment_closed {
                            self.error(&diagnostics::Asterisk_Slash_expected);
                        }

                        if self.skip_trivia {
                            continue;
                        }

                        if !comment_closed {
                            self.token_flags |= TokenFlags::UNTERMINATED;
                        }
                        self.token = Kind::MultiLineCommentTrivia;
                        return self.token;
                    }
                    if self.char_at(1) == i32::from(b'=') {
                        self.pos += 2;
                        self.token = Kind::SlashEqualsToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::SlashToken;
                    }
                }
                Some(b'0') => {
                    if matches!(self.char_at(1), c if c == i32::from(b'X') || c == i32::from(b'x'))
                    {
                        let start = self.pos;
                        self.pos += 2;
                        let mut digits = self.scan_hex_digits(1, true, true);
                        if digits.is_empty() {
                            self.error(&diagnostics::Hexadecimal_digit_expected);
                            digits = b"0".to_vec();
                        }
                        if let Some(cached) = self.hex_number_cache.get(&digits) {
                            self.token_value = cached.clone();
                        } else {
                            let raw_text = &self.text.as_bytes()[start..self.pos];
                            if raw_text.starts_with(b"0x") && &raw_text[2..] == digits.as_slice() {
                                self.token_value = raw_text.to_vec();
                            } else {
                                let mut v = b"0x".to_vec();
                                v.extend_from_slice(&digits);
                                self.token_value = v;
                            }
                            self.hex_number_cache
                                .insert(digits, self.token_value.clone());
                        }
                        self.token_flags |= TokenFlags::HEX_SPECIFIER;
                        self.token = self.scan_big_int_suffix();
                    } else if matches!(self.char_at(1), c if c == i32::from(b'B')
                        || c == i32::from(b'b'))
                    {
                        self.pos += 2;
                        let mut digits = self.scan_binary_or_octal_digits(2);
                        if digits.is_empty() {
                            self.error(&diagnostics::Binary_digit_expected);
                            digits = b"0".to_vec();
                        }
                        let mut v = b"0b".to_vec();
                        v.extend_from_slice(&digits);
                        self.token_value = v;
                        self.token_flags |= TokenFlags::BINARY_SPECIFIER;
                        self.token = self.scan_big_int_suffix();
                    } else if matches!(self.char_at(1), c if c == i32::from(b'O')
                        || c == i32::from(b'o'))
                    {
                        self.pos += 2;
                        let mut digits = self.scan_binary_or_octal_digits(8);
                        if digits.is_empty() {
                            self.error(&diagnostics::Octal_digit_expected);
                            digits = b"0".to_vec();
                        }
                        let mut v = b"0o".to_vec();
                        v.extend_from_slice(&digits);
                        self.token_value = v;
                        self.token_flags |= TokenFlags::OCTAL_SPECIFIER;
                        self.token = self.scan_big_int_suffix();
                    } else {
                        // Go `fallthrough` into the decimal-digit case.
                        self.token = self.scan_number();
                    }
                }
                Some(b'1'..=b'9') => {
                    self.token = self.scan_number();
                }
                Some(b':') => {
                    self.pos += 1;
                    self.token = Kind::ColonToken;
                }
                Some(b';') => {
                    self.pos += 1;
                    self.token = Kind::SemicolonToken;
                }
                Some(b'<') => {
                    if self.char_at(1) == i32::from(b'<')
                        && is_conflict_marker_trivia(self.text, self.pos)
                    {
                        let text = self.text;
                        let on_error = self.on_error.as_deref_mut();
                        self.pos = scan_conflict_marker_trivia(text, self.pos, on_error);
                        if self.skip_trivia {
                            continue;
                        } else {
                            self.token = Kind::ConflictMarkerTrivia;
                            return self.token;
                        }
                    }
                    if self.char_at(1) == i32::from(b'<') {
                        if self.char_at(2) == i32::from(b'=') {
                            self.pos += 3;
                            self.token = Kind::LessThanLessThanEqualsToken;
                        } else {
                            self.pos += 2;
                            self.token = Kind::LessThanLessThanToken;
                        }
                    } else if self.char_at(1) == i32::from(b'=') {
                        self.pos += 2;
                        self.token = Kind::LessThanEqualsToken;
                    } else if self.language_variant == LanguageVariant::Jsx
                        && self.char_at(1) == i32::from(b'/')
                        && self.char_at(2) != i32::from(b'*')
                    {
                        self.pos += 2;
                        self.token = Kind::LessThanSlashToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::LessThanToken;
                    }
                }
                Some(b'=') => {
                    if self.char_at(1) == i32::from(b'=')
                        && is_conflict_marker_trivia(self.text, self.pos)
                    {
                        let text = self.text;
                        let on_error = self.on_error.as_deref_mut();
                        self.pos = scan_conflict_marker_trivia(text, self.pos, on_error);
                        if self.skip_trivia {
                            continue;
                        } else {
                            self.token = Kind::ConflictMarkerTrivia;
                            return self.token;
                        }
                    }
                    if self.char_at(1) == i32::from(b'=') {
                        if self.char_at(2) == i32::from(b'=') {
                            self.pos += 3;
                            self.token = Kind::EqualsEqualsEqualsToken;
                        } else {
                            self.pos += 2;
                            self.token = Kind::EqualsEqualsToken;
                        }
                    } else if self.char_at(1) == i32::from(b'>') {
                        self.pos += 2;
                        self.token = Kind::EqualsGreaterThanToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::EqualsToken;
                    }
                }
                Some(b'>') => {
                    if self.char_at(1) == i32::from(b'>')
                        && is_conflict_marker_trivia(self.text, self.pos)
                    {
                        let text = self.text;
                        let on_error = self.on_error.as_deref_mut();
                        self.pos = scan_conflict_marker_trivia(text, self.pos, on_error);
                        if self.skip_trivia {
                            continue;
                        } else {
                            self.token = Kind::ConflictMarkerTrivia;
                            return self.token;
                        }
                    }
                    self.pos += 1;
                    self.token = Kind::GreaterThanToken;
                }
                Some(b'?') => {
                    if self.char_at(1) == i32::from(b'.') && !is_digit(self.char_at(2)) {
                        self.pos += 2;
                        self.token = Kind::QuestionDotToken;
                    } else if self.char_at(1) == i32::from(b'?') {
                        if self.char_at(2) == i32::from(b'=') {
                            self.pos += 3;
                            self.token = Kind::QuestionQuestionEqualsToken;
                        } else {
                            self.pos += 2;
                            self.token = Kind::QuestionQuestionToken;
                        }
                    } else {
                        self.pos += 1;
                        self.token = Kind::QuestionToken;
                    }
                }
                Some(b'[') => {
                    self.pos += 1;
                    self.token = Kind::OpenBracketToken;
                }
                Some(b']') => {
                    self.pos += 1;
                    self.token = Kind::CloseBracketToken;
                }
                Some(b'^') => {
                    if self.char_at(1) == i32::from(b'=') {
                        self.pos += 2;
                        self.token = Kind::CaretEqualsToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::CaretToken;
                    }
                }
                Some(b'{') => {
                    self.pos += 1;
                    self.token = Kind::OpenBraceToken;
                }
                Some(b'|') => {
                    if self.char_at(1) == i32::from(b'|')
                        && is_conflict_marker_trivia(self.text, self.pos)
                    {
                        let text = self.text;
                        let on_error = self.on_error.as_deref_mut();
                        self.pos = scan_conflict_marker_trivia(text, self.pos, on_error);
                        if self.skip_trivia {
                            continue;
                        } else {
                            self.token = Kind::ConflictMarkerTrivia;
                            return self.token;
                        }
                    }
                    if self.char_at(1) == i32::from(b'|') {
                        if self.char_at(2) == i32::from(b'=') {
                            self.pos += 3;
                            self.token = Kind::BarBarEqualsToken;
                        } else {
                            self.pos += 2;
                            self.token = Kind::BarBarToken;
                        }
                    } else if self.char_at(1) == i32::from(b'=') {
                        self.pos += 2;
                        self.token = Kind::BarEqualsToken;
                    } else {
                        self.pos += 1;
                        self.token = Kind::BarToken;
                    }
                }
                Some(b'}') => {
                    self.pos += 1;
                    self.token = Kind::CloseBraceToken;
                }
                Some(b'~') => {
                    self.pos += 1;
                    self.token = Kind::TildeToken;
                }
                Some(b'@') => {
                    self.pos += 1;
                    self.token = Kind::AtToken;
                }
                Some(b'\\') => {
                    if self.scan_identifier(0, IdentifierVariant::Standard) {
                        self.token = get_identifier_token(&self.token_value);
                    } else {
                        self.scan_invalid_character();
                    }
                }
                Some(b'#') => {
                    if self.char_at(1) == i32::from(b'!') {
                        if self.pos == 0 {
                            self.pos += 2;
                            loop {
                                let (ch, size) = self.char_and_size();
                                if size == 0 || is_line_break_rune(ch) {
                                    break;
                                }
                                self.pos += size;
                            }
                            continue;
                        }
                        self.error_at(
                            &diagnostics::X_can_only_be_used_at_the_start_of_a_file,
                            self.pos,
                            2,
                            &[],
                        );
                        self.pos += 2;
                        self.token = Kind::Unknown;
                    } else {
                        if !self.scan_identifier(1, IdentifierVariant::Standard) {
                            self.error_at(&diagnostics::Invalid_character, self.pos - 1, 1, &[]);
                            self.token_value = b"#".to_vec();
                        }
                        self.token = Kind::PrivateIdentifier;
                    }
                }
                _ => {
                    if ch < 0 {
                        self.token = Kind::EndOfFile;
                        return self.token;
                    }
                    if self.scan_identifier(0, IdentifierVariant::Standard) {
                        self.token = get_identifier_token(&self.token_value);
                        return self.token;
                    }
                    let (ch, size) = self.char_and_size();
                    if ch == RUNE_ERROR {
                        self.error_at(&diagnostics::File_appears_to_be_binary, 0, 0, &[]);
                        self.pos = self.text.len();
                        self.token = Kind::NonTextFileMarkerTrivia;
                        return self.token;
                    }
                    if is_white_space_single_line_rune(ch) {
                        self.pos += size;

                        // If we get here and it's not 0x0085 (nextLine), then we're handling non-ASCII whitespace.
                        // Handle skipTrivia like we do in the space case above.
                        if ch == 0x0085 || self.skip_trivia {
                            continue;
                        }

                        loop {
                            let (ch, size) = self.char_and_size();
                            if !is_white_space_single_line_rune(ch) {
                                break;
                            }
                            self.pos += size;
                        }
                        self.token = Kind::WhitespaceTrivia;
                        return self.token;
                    }
                    if is_line_break_rune(ch) {
                        self.token_flags |= TokenFlags::PRECEDING_LINE_BREAK;
                        self.pos += size;
                        continue;
                    }
                    self.scan_invalid_character();
                }
            }
            return self.token;
        }
    }

    /// `func (s *Scanner) processCommentDirective`
    fn process_comment_directive(&mut self, start: usize, end: usize, multiline: bool) {
        // Skip starting slashes and whitespace
        let text = self.text.as_bytes();
        let mut pos = start;
        if multiline {
            // Skip whitespace
            while pos < end && (text[pos] == b' ' || text[pos] == b'\t') {
                pos += 1;
            }
            // Skip combinations of / and *
            while pos < end && (text[pos] == b'/' || text[pos] == b'*') {
                pos += 1;
            }
        } else {
            // Skip opening //
            pos += 2;
            // Skip another / if present
            while pos < end && text[pos] == b'/' {
                pos += 1;
            }
        }
        // Skip whitespace
        while pos < end && (text[pos] == b' ' || text[pos] == b'\t') {
            pos += 1;
        }
        // Directive must start with '@'
        if !(pos < end && text[pos] == b'@') {
            return;
        }
        pos += 1;
        let kind = if text[pos..].starts_with(b"ts-expect-error") {
            CommentDirectiveKind::ExpectError
        } else if text[pos..].starts_with(b"ts-ignore") {
            CommentDirectiveKind::Ignore
        } else {
            return;
        };
        self.comment_directives.push(CommentDirective {
            loc: TextRange::new(start as i32, end as i32),
            kind,
        });
    }

    /// `func (s *Scanner) ReScanLessThanToken() ast.Kind`
    pub fn rescan_less_than_token(&mut self) -> Kind {
        if self.token == Kind::LessThanLessThanToken {
            self.pos = self.token_start + 1;
            self.token = Kind::LessThanToken;
        }
        self.token
    }

    /// `func (s *Scanner) ReScanGreaterThanToken() ast.Kind`
    pub fn rescan_greater_than_token(&mut self) -> Kind {
        if self.token == Kind::GreaterThanToken {
            self.rescan_greater_than_token_inner();
        }
        self.token
    }

    /// `func (s *Scanner) reScanGreaterThanTokenInner()`
    fn rescan_greater_than_token_inner(&mut self) {
        self.pos = self.token_start + 1;
        if self.char() == i32::from(b'>') {
            if self.char_at(1) == i32::from(b'>') {
                if self.char_at(2) == i32::from(b'=') {
                    self.pos += 3;
                    self.token = Kind::GreaterThanGreaterThanGreaterThanEqualsToken;
                } else {
                    self.pos += 2;
                    self.token = Kind::GreaterThanGreaterThanGreaterThanToken;
                }
            } else if self.char_at(1) == i32::from(b'=') {
                self.pos += 2;
                self.token = Kind::GreaterThanGreaterThanEqualsToken;
            } else {
                self.pos += 1;
                self.token = Kind::GreaterThanGreaterThanToken;
            }
        } else if self.char() == i32::from(b'=') {
            self.pos += 1;
            self.token = Kind::GreaterThanEqualsToken;
        }
    }

    /// `func (s *Scanner) ReScanTemplateToken(isTaggedTemplate bool) ast.Kind`
    pub fn rescan_template_token(&mut self, is_tagged_template: bool) -> Kind {
        self.pos = self.token_start;
        self.token = self.scan_template_and_set_token_value(!is_tagged_template);
        self.token
    }

    /// `func (s *Scanner) ReScanAsteriskEqualsToken() ast.Kind`
    pub fn rescan_asterisk_equals_token(&mut self) -> Kind {
        if self.token != Kind::AsteriskEqualsToken {
            panic!("'ReScanAsteriskEqualsToken' should only be called on a '*='");
        }
        self.pos = self.token_start + 1;
        self.token = Kind::EqualsToken;
        self.token
    }

    /// `func (s *Scanner) ReScanSlashToken(reportErrors ...bool) ast.Kind`
    ///
    /// PORT: Go's variadic `reportErrors ...bool` (first element wins, default
    /// false) becomes a plain `should_report_errors: bool`.
    pub fn rescan_slash_token(&mut self, should_report_errors: bool) -> Kind {
        if self.token == Kind::SlashToken || self.token == Kind::SlashEqualsToken {
            let bytes = self.text.as_bytes();
            // Quickly get to the end of regex such that we know the flags
            let start_of_reg_exp_body = self.token_start + 1;
            let mut p = start_of_reg_exp_body;
            let mut in_escape = false;
            let mut named_capture_groups = false;
            // Although nested character classes are allowed in Unicode Sets mode,
            // an unescaped slash is nevertheless invalid even in a character class in any Unicode mode.
            // This is indicated by Section 12.9.5 Regular Expression Literals of the specification,
            // where nested character classes are not considered at all. (A `[` RegularExpressionClassChar
            // does nothing in a RegularExpressionClass, and a `]` always closes the class.)
            // Additionally, parsing nested character classes will misinterpret regexes like `/[[]/`
            // as unterminated, consuming characters beyond the slash. (This even applies to `/[[]/v`,
            // which should be parsed as a well-terminated regex with an incomplete character class.)
            // Thus we must not handle nested character classes in the first pass.
            let mut in_character_class = false;
            let unterminated = 'scan: loop {
                // If we reach the end of a file, or hit a newline, then this is an unterminated
                // regex. Report error and return what we have so far.
                if p >= self.end {
                    self.token_flags |= TokenFlags::UNTERMINATED;
                    break 'scan true;
                }
                let ch = i32::from(bytes[p]);
                if is_line_break_rune(ch) {
                    self.token_flags |= TokenFlags::UNTERMINATED;
                    break 'scan true;
                } else if in_escape {
                    // Parsing an escape character;
                    // reset the flag and just advance to the next char.
                    in_escape = false;
                } else if ch == i32::from(b'/') && !in_character_class {
                    // A slash within a character class is permissible,
                    // but in general it signals the end of the regexp literal.
                    break 'scan false;
                } else if ch == i32::from(b'[') {
                    in_character_class = true;
                } else if ch == i32::from(b'\\') {
                    in_escape = true;
                } else if ch == i32::from(b']') {
                    in_character_class = false;
                } else if !in_character_class
                    && ch == i32::from(b'(')
                    && p + 1 < self.end
                    && bytes[p + 1] == b'?'
                    && p + 2 < self.end
                    && bytes[p + 2] == b'<'
                    && (p + 3 >= self.end || (bytes[p + 3] != b'=' && bytes[p + 3] != b'!'))
                {
                    named_capture_groups = true;
                }
                p += 1;
            };

            let end_of_reg_exp_body = p;
            if unterminated {
                // Search for the nearest unbalanced bracket for better recovery. Since the expression is
                // invalid anyways, we take nested square brackets into consideration for the best guess.
                p = start_of_reg_exp_body;
                in_escape = false;
                let mut character_class_depth = 0;
                let mut in_decimal_quantifier = false;
                let mut group_depth = 0;
                while p < end_of_reg_exp_body {
                    let ch = i32::from(bytes[p]);
                    if in_escape {
                        in_escape = false;
                    } else if ch == i32::from(b'\\') {
                        in_escape = true;
                    } else if ch == i32::from(b'[') {
                        character_class_depth += 1;
                    } else if ch == i32::from(b']') && character_class_depth != 0 {
                        character_class_depth -= 1;
                    } else if character_class_depth == 0 {
                        if ch == i32::from(b'{') {
                            in_decimal_quantifier = true;
                        } else if ch == i32::from(b'}') && in_decimal_quantifier {
                            in_decimal_quantifier = false;
                        } else if !in_decimal_quantifier {
                            if ch == i32::from(b'(') {
                                group_depth += 1;
                            } else if ch == i32::from(b')') && group_depth != 0 {
                                group_depth -= 1;
                            } else if ch == i32::from(b')')
                                || ch == i32::from(b']')
                                || ch == i32::from(b'}')
                            {
                                // We encountered an unbalanced bracket outside a character class. Treat this position as the end of regex.
                                break;
                            }
                        }
                    }
                    p += 1;
                }
                // Whitespaces and semicolons at the end are not likely to be part of the regex
                while p > start_of_reg_exp_body {
                    let (ch, size) = decode_last_rune_in_string(&bytes[..p]);
                    if is_white_space_like_rune(ch) || ch == i32::from(b';') {
                        p -= size;
                    } else {
                        break;
                    }
                }
                self.error_at(
                    &diagnostics::Unterminated_regular_expression_literal,
                    self.token_start,
                    p - self.token_start,
                    &[],
                );
            } else {
                // Consume the slash character
                p += 1;
                let language_version = self.language_version();
                let end = self.end;
                // PORT: Go passes the scanner's `onError` directly (the Go
                // callback field and the parameter share one function type).
                // `Box<dyn FnMut + 'a>` cannot be narrowed to a shorter
                // trait-object bound under `&mut`, so the callbacks here are
                // forwarding closures capturing `self.on_error` instead.
                let (reg_exp_flags, new_p) = {
                    let mut on_error =
                        |m: &'static Message, pos: usize, len: usize, args: &[String]| {
                            if let Some(cb) = self.on_error.as_deref_mut() {
                                cb(m, pos, len, args);
                            }
                        };
                    scan_regular_expression_flags(
                        bytes,
                        p,
                        end,
                        should_report_errors,
                        language_version,
                        &mut on_error,
                    )
                };
                p = new_p;
                if should_report_errors {
                    // PORT: the Go regExpParser shares the *Scanner; here the
                    // parser holds an equivalent copy of the scanner state
                    // (see the regexp.rs file header). `token_flags` round
                    // trips so escape flags seen while parsing land on the
                    // literal token, as with Go's shared `s.tokenFlags`.
                    let mut on_error =
                        |m: &'static Message, pos: usize, len: usize, args: &[String]| {
                            if let Some(cb) = self.on_error.as_deref_mut() {
                                cb(m, pos, len, args);
                            }
                        };
                    let mut parser = RegExpParser::new(
                        bytes,
                        start_of_reg_exp_body,
                        end_of_reg_exp_body,
                        reg_exp_flags,
                        named_capture_groups,
                        self.script_target,
                        Some(&mut on_error),
                        self.token_flags,
                    );
                    parser.run();
                    self.token_flags = parser.token_flags();
                }
                self.pos = p;
            }

            self.pos = p;
            self.token_value = self.text[self.token_start..self.pos].as_bytes().to_vec();
            self.token = Kind::RegularExpressionLiteral;
        }
        self.token
    }

    /// `func (s *Scanner) ReScanJsxToken(allowMultilineJsxText bool) ast.Kind`
    pub fn rescan_jsx_token(&mut self, allow_multiline_jsx_text: bool) -> Kind {
        self.pos = self.full_start_pos;
        self.token_start = self.full_start_pos;
        self.token = self.scan_jsx_token_ex(allow_multiline_jsx_text);
        self.token
    }

    /// `func (s *Scanner) ReScanHashToken() ast.Kind`
    pub fn rescan_hash_token(&mut self) -> Kind {
        if self.token == Kind::PrivateIdentifier {
            self.pos = self.token_start + 1;
            self.token = Kind::HashToken;
        }
        self.token
    }

    /// `func (s *Scanner) ReScanQuestionToken() ast.Kind`
    pub fn rescan_question_token(&mut self) -> Kind {
        if self.token != Kind::QuestionQuestionToken {
            panic!("'reScanQuestionToken' should only be called on a '??'");
        }
        self.pos = self.token_start + 1;
        self.token = Kind::QuestionToken;
        self.token
    }

    /// `func (s *Scanner) ScanJsxToken() ast.Kind`
    pub fn scan_jsx_token(&mut self) -> Kind {
        self.scan_jsx_token_ex(true /*allowMultilineJsxText*/)
    }

    /// `func (s *Scanner) ScanJsxTokenEx(allowMultilineJsxText bool) ast.Kind`
    pub fn scan_jsx_token_ex(&mut self, allow_multiline_jsx_text: bool) -> Kind {
        self.full_start_pos = self.pos;
        self.token_start = self.pos;
        let ch = self.char();
        if ch < 0 {
            self.token = Kind::EndOfFile;
        } else if ch == i32::from(b'<') {
            if self.char_at(1) == i32::from(b'/') {
                self.pos += 2;
                self.token = Kind::LessThanSlashToken;
            } else {
                self.pos += 1;
                self.token = Kind::LessThanToken;
            }
        } else if ch == i32::from(b'{') {
            self.pos += 1;
            self.token = Kind::OpenBraceToken;
        } else {
            // First non-whitespace character on this line.
            let mut first_non_whitespace: isize = 0;
            // These initial values are special because the first line is:
            // first_non_whitespace = 0 to indicate that we want leading whitespace
            loop {
                let (ch, size) = self.char_and_size();
                if size == 0 || ch == i32::from(b'{') {
                    break;
                }
                if ch == i32::from(b'<') {
                    if is_conflict_marker_trivia(self.text, self.pos) {
                        let text = self.text;
                        let on_error = self.on_error.as_deref_mut();
                        self.pos = scan_conflict_marker_trivia(text, self.pos, on_error);
                        self.token = Kind::ConflictMarkerTrivia;
                        return self.token;
                    }
                    break;
                }
                if ch == i32::from(b'>') {
                    self.error_at(
                        &diagnostics::Unexpected_token_Did_you_mean_or_gt,
                        self.pos,
                        1,
                        &[],
                    );
                } else if ch == i32::from(b'}') {
                    self.error_at(
                        &diagnostics::Unexpected_token_Did_you_mean_or_rbrace,
                        self.pos,
                        1,
                        &[],
                    );
                }
                // FirstNonWhitespace is 0, then we only see whitespaces so far. If we see a linebreak, we want to ignore that whitespaces.
                // i.e (- : whitespace)
                //      <div>----
                //      </div> becomes <div></div>
                //
                //      <div>----</div> becomes <div>----</div>
                if is_line_break_rune(ch) && first_non_whitespace == 0 {
                    first_non_whitespace = -1;
                } else if !allow_multiline_jsx_text
                    && is_line_break_rune(ch)
                    && first_non_whitespace > 0
                {
                    // Stop JsxText on each line during formatting. This allows the formatter to
                    // indent each line correctly.
                    break;
                } else if !is_white_space_like_rune(ch) {
                    first_non_whitespace = self.pos as isize;
                }
                self.pos += size;
            }
            self.token_value = self.text[self.full_start_pos..self.pos].as_bytes().to_vec();
            self.token = Kind::JsxText;
            if first_non_whitespace == -1 {
                self.token = Kind::JsxTextAllWhiteSpaces;
            }
        }
        self.token
    }

    /// `func (s *Scanner) ScanJsxIdentifier() ast.Kind` — scans a JSX
    /// identifier; these differ from normal identifiers in that they allow
    /// dashes.
    pub fn scan_jsx_identifier(&mut self) -> Kind {
        if token_is_identifier_or_keyword(self.token) {
            // An identifier or keyword has already been parsed - check for a `-` or a single instance of `:` and then append it and
            // everything after it to the token
            // Do note that this means that `scanJsxIdentifier` effectively _mutates_ the visible token without advancing to a new token
            // Any caller should be expecting this behavior and should only read the pos or token value after calling it.
            // Here scanIdentifierParts is reused to ensure Unicode escapes are handled.
            let parts = self.scan_identifier_parts(IdentifierVariant::Jsx);
            self.token_value.extend_from_slice(&parts);
            self.token = get_identifier_token(&self.token_value);
        }
        self.token
    }

    /// `func (s *Scanner) ScanJsxAttributeValue() ast.Kind`
    pub fn scan_jsx_attribute_value(&mut self) -> Kind {
        self.full_start_pos = self.pos;
        // Skip whitespace between '=' and the value so tokenStart lands on the
        // opening quote, not on trivia.
        loop {
            let (ch, size) = self.char_and_size();
            if !(size > 0 && is_white_space_like_rune(ch)) {
                break;
            }
            self.pos += size;
        }
        self.token_start = self.pos;
        match self.byte() {
            Some(b'"' | b'\'') => {
                self.token_value = self.scan_string(true /*jsxAttributeString*/);
                self.token = Kind::StringLiteral;
                self.token
            }
            _ => {
                // If this scans anything other than `{`, it's a parse error.
                self.scan()
            }
        }
    }

    /// `func (s *Scanner) ReScanJsxAttributeValue() ast.Kind`
    pub fn rescan_jsx_attribute_value(&mut self) -> Kind {
        self.pos = self.full_start_pos;
        self.token_start = self.full_start_pos;
        self.scan_jsx_attribute_value()
    }

    /// `func (s *Scanner) ScanJSDocCommentTextToken(inBackticks bool) ast.Kind`
    ///
    /// In addition to the usual JSDoc Kinds, can also return
    /// `Kind::JSDocCommentTextToken`.
    pub fn scan_jsdoc_comment_text_token(&mut self, in_backticks: bool) -> Kind {
        self.full_start_pos = self.pos;
        self.token_flags = TokenFlags::NONE;
        if self.pos >= self.text.len() {
            self.token = Kind::EndOfFile;
            return self.token;
        }
        self.token_start = self.pos;
        loop {
            let (ch, size) = self.char_and_size();
            if !(self.pos < self.text.len() && !is_line_break_rune(ch) && ch != i32::from(b'`')) {
                break;
            }
            if !in_backticks {
                if ch == i32::from(b'{') {
                    break;
                } else if ch == i32::from(b'@') {
                    // @ doesn't start a new tag inside ``, and elsewhere, only after whitespace and before identifier
                    let (previous, _) =
                        decode_last_rune_in_string(&self.text.as_bytes()[..self.pos]);
                    if is_white_space_single_line_rune(previous) {
                        let (next, _) =
                            decode_rune_in_string(&self.text.as_bytes()[self.pos + size..]);
                        if is_identifier_start(next) {
                            break;
                        }
                    }
                }
            }
            self.pos += size;
        }
        if self.pos == self.token_start {
            return self.scan_jsdoc_token();
        }
        self.token_value = self.text[self.token_start..self.pos].as_bytes().to_vec();
        self.token = Kind::JSDocCommentTextToken;
        self.token
    }

    /// `func (s *Scanner) CanFollowJSDocAt() bool` — peek at the character at
    /// the current scanner position (expected to be right after '@') and
    /// return true if a JSDoc tag can follow. Identifier starts indicate a tag
    /// name. Whitespace, newlines, and EOF are also accepted to support
    /// incomplete tags for code completion.
    pub fn can_follow_jsdoc_at(&self) -> bool {
        if self.pos >= self.text.len() {
            return true;
        }
        let (ch, _) = decode_rune_in_string(&self.text.as_bytes()[self.pos..]);
        is_identifier_start(ch) || is_white_space_single_line_rune(ch) || is_line_break_rune(ch)
    }

    /// `func (s *Scanner) ScanJSDocToken() ast.Kind`
    pub fn scan_jsdoc_token(&mut self) -> Kind {
        self.full_start_pos = self.pos;
        self.token_flags = TokenFlags::NONE;
        if self.pos >= self.text.len() {
            self.token = Kind::EndOfFile;
            return self.token;
        }

        self.token_start = self.pos;
        let (ch, size) = self.char_and_size();
        self.pos += size;
        match ch {
            c if c == i32::from(b'\t')
                || c == i32::from(b'\x0b')
                || c == i32::from(b'\x0c')
                || c == i32::from(b' ') =>
            {
                loop {
                    let (ch2, size2) = self.char_and_size();
                    if !(size2 > 0 && is_white_space_single_line_rune(ch2)) {
                        break;
                    }
                    self.pos += size2;
                }
                self.token = Kind::WhitespaceTrivia;
            }
            c if c == i32::from(b'@') => {
                self.token = Kind::AtToken;
            }
            c if c == i32::from(b'\r') || c == i32::from(b'\n') => {
                // `case '\r'` falls through into `case '\n'` in Go.
                if ch == i32::from(b'\r') && self.char() == i32::from(b'\n') {
                    self.pos += 1;
                }
                self.token_flags |= TokenFlags::PRECEDING_LINE_BREAK;
                self.token = Kind::NewLineTrivia;
            }
            c if c == i32::from(b'*') => {
                self.token = Kind::AsteriskToken;
            }
            c if c == i32::from(b'{') => {
                self.token = Kind::OpenBraceToken;
            }
            c if c == i32::from(b'}') => {
                self.token = Kind::CloseBraceToken;
            }
            c if c == i32::from(b'[') => {
                self.token = Kind::OpenBracketToken;
            }
            c if c == i32::from(b']') => {
                self.token = Kind::CloseBracketToken;
            }
            c if c == i32::from(b'(') => {
                self.token = Kind::OpenParenToken;
            }
            c if c == i32::from(b')') => {
                self.token = Kind::CloseParenToken;
            }
            c if c == i32::from(b'<') => {
                self.token = Kind::LessThanToken;
            }
            c if c == i32::from(b'>') => {
                self.token = Kind::GreaterThanToken;
            }
            c if c == i32::from(b'=') => {
                self.token = Kind::EqualsToken;
            }
            c if c == i32::from(b',') => {
                self.token = Kind::CommaToken;
            }
            c if c == i32::from(b'.') => {
                self.token = Kind::DotToken;
            }
            c if c == i32::from(b'`') => {
                self.token = Kind::BacktickToken;
            }
            c if c == i32::from(b'#') => {
                self.token = Kind::HashToken;
            }
            _ => {
                self.pos = self.token_start;
                if self.scan_identifier(0, IdentifierVariant::Jsx) {
                    self.token = get_identifier_token(&self.token_value);
                    return self.token;
                }
                self.pos = self.token_start + size;
                self.token = Kind::Unknown;
            }
        }
        self.token
    }

    /// `func (s *Scanner) scanIdentifier`
    fn scan_identifier(&mut self, prefix_length: usize, variant: IdentifierVariant) -> bool {
        let start = self.pos;
        self.pos += prefix_length;
        let identifier_start = self.pos;
        let ch = self.char();
        // Fast path for simple ASCII identifiers
        if variant != IdentifierVariant::Jsx
            && (is_ascii_letter(ch) || ch == i32::from(b'_') || ch == i32::from(b'$'))
        {
            self.pos += 1;
            self.scan_ascii_while(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'$');
            let ch = self.char();
            if ch < RUNE_SELF && ch != i32::from(b'\\') {
                self.token_value = self.text[start..self.pos].as_bytes().to_vec();
                return true;
            }
            self.pos = identifier_start;
        }
        let (mut ch, mut size) = self.char_and_size();
        if is_identifier_start(ch) {
            let language_variant = if variant == IdentifierVariant::Jsx {
                LanguageVariant::Jsx
            } else {
                LanguageVariant::Standard
            };
            loop {
                self.pos += size;
                let next = self.char_and_size();
                (ch, size) = next;
                if !is_identifier_part_ex(ch, language_variant) {
                    break;
                }
            }
            self.token_value = self.text[start..self.pos].as_bytes().to_vec();
            if ch == i32::from(b'\\') {
                let parts = self.scan_identifier_parts(variant);
                self.token_value.extend_from_slice(&parts);
            }
            return true;
        }
        let escaped = if ch == i32::from(b'\\') {
            self.scan_identifier_escape(
                is_identifier_start,
                variant == IdentifierVariant::RegExpGroupName,
            )
        } else {
            None
        };
        if let Some(escaped) = escaped {
            self.token_value = self.text[start..identifier_start].as_bytes().to_vec();
            self.token_value
                .extend_from_slice(&stringutil::encode_js_string_rune(escaped));
            let parts = self.scan_identifier_parts(variant);
            self.token_value.extend_from_slice(&parts);
            return true;
        }
        false
    }

    /// `func (s *Scanner) scanIdentifierParts`
    fn scan_identifier_parts(&mut self, variant: IdentifierVariant) -> Vec<u8> {
        let mut sb = Vec::new();
        let mut start = self.pos;
        let language_variant = if variant == IdentifierVariant::Jsx {
            LanguageVariant::Jsx
        } else {
            LanguageVariant::Standard
        };
        loop {
            let (ch, size) = self.char_and_size();
            if is_identifier_part_ex(ch, language_variant) {
                self.pos += size;
                continue;
            }
            if ch == i32::from(b'\\') {
                let escape_start = self.pos;
                if let Some(escaped) = self.scan_identifier_escape(
                    |ch| is_identifier_part_ex(ch, language_variant),
                    variant == IdentifierVariant::RegExpGroupName,
                ) {
                    sb.extend_from_slice(&self.text.as_bytes()[start..escape_start]);
                    sb.extend_from_slice(&stringutil::encode_js_string_rune(escaped));
                    start = self.pos;
                    continue;
                }
            }
            break;
        }
        sb.extend_from_slice(&self.text.as_bytes()[start..self.pos]);
        sb
    }

    /// `func (s *Scanner) scanIdentifierEscape`
    ///
    /// Go returns `(rune, bool)`; `None` is `(0, false)`.
    fn scan_identifier_escape(
        &mut self,
        is_valid: impl Fn(i32) -> bool,
        allow_surrogate_pair_escape: bool,
    ) -> Option<i32> {
        let escaped = self.peek_unicode_escape();
        if escaped >= 0 && is_valid(escaped) {
            return Some(self.scan_unicode_escape(true));
        }
        if allow_surrogate_pair_escape
            && self.char_at(2) != i32::from(b'{')
            && stringutil::is_high_surrogate(escaped)
        {
            // Unlike normal identifiers, group names in regular expressions, whether in Unicode mode or not,
            // accept \u HexLeadSurrogate \u HexTrailSurrogate as part of RegExpIdentifierName.
            // See https://github.com/tc39/ecma262/pull/1869 for the change.
            let saved_pos = self.pos;
            let saved_token_flags = self.token_flags;
            self.scan_unicode_escape(false);
            // scanLowSurrogateEscape also accepts the braced form used in string literals,
            // but RegExpIdentifierName does not allow it.
            let code_point = if self.char_at(2) != i32::from(b'{') {
                self.scan_low_surrogate_escape(escaped)
            } else {
                None
            };
            if let Some(code_point) = code_point.filter(|&cp| is_valid(cp)) {
                return Some(code_point);
            }
            self.pos = saved_pos;
            self.token_flags = saved_token_flags;
        }
        None
    }

    /// `func (s *Scanner) scanString`
    fn scan_string(&mut self, jsx_attribute_string: bool) -> Vec<u8> {
        let quote = self.char();
        if quote == i32::from(b'\'') {
            self.token_flags |= TokenFlags::SINGLE_QUOTE;
        }
        self.pos += 1;
        // Fast path for simple strings without escape sequences.
        let quote_byte = quote as u8;
        let str_len = self.text.as_bytes()[self.pos..]
            .iter()
            .position(|&b| b == quote_byte);
        match str_len {
            Some(0) => {
                self.pos += 1;
                return Vec::new();
            }
            Some(len) => {
                let str_ = &self.text.as_bytes()[self.pos..self.pos + len];
                if jsx_attribute_string
                    || (!str_.contains(&b'\\') && !str_.contains(&b'\r') && !str_.contains(&b'\n'))
                {
                    self.pos += len + 1;
                    return str_.to_vec();
                }
            }
            None => {}
        }
        let mut sb = Vec::new();
        let mut start = self.pos;
        loop {
            let ch = self.char();
            if ch < 0 {
                sb.extend_from_slice(&self.text.as_bytes()[start..self.pos]);
                self.token_flags |= TokenFlags::UNTERMINATED;
                self.error(&diagnostics::Unterminated_string_literal);
                break;
            }
            if ch == quote {
                sb.extend_from_slice(&self.text.as_bytes()[start..self.pos]);
                self.pos += 1;
                break;
            }
            if ch == i32::from(b'\\') && !jsx_attribute_string {
                sb.extend_from_slice(&self.text.as_bytes()[start..self.pos]);
                let esc = self.scan_escape_sequence(
                    ESCAPE_SEQUENCE_SCANNING_FLAGS_STRING
                        | ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_ERRORS,
                );
                sb.extend_from_slice(&esc);
                start = self.pos;
                continue;
            }
            if (ch == i32::from(b'\n') || ch == i32::from(b'\r')) && !jsx_attribute_string {
                sb.extend_from_slice(&self.text.as_bytes()[start..self.pos]);
                self.token_flags |= TokenFlags::UNTERMINATED;
                self.error(&diagnostics::Unterminated_string_literal);
                break;
            }
            self.pos += 1;
        }
        sb
    }

    /// `func (s *Scanner) scanTemplateAndSetTokenValue`
    fn scan_template_and_set_token_value(
        &mut self,
        should_emit_invalid_escape_error: bool,
    ) -> Kind {
        let started_with_backtick = self.byte() == Some(b'`');
        self.pos += 1;
        let mut start = self.pos;
        let mut parts: Vec<Vec<u8>> = Vec::with_capacity(4);
        let token;
        loop {
            self.scan_ascii_while(|b| b != b'`' && b != b'$' && b != b'\\' && b != b'\r');
            let ch = self.char();
            if ch < 0 || ch == i32::from(b'`') {
                parts.push(self.text[start..self.pos].as_bytes().to_vec());
                if ch == i32::from(b'`') {
                    self.pos += 1;
                } else {
                    self.token_flags |= TokenFlags::UNTERMINATED;
                    self.error(&diagnostics::Unterminated_template_literal);
                }
                token = if_else(
                    started_with_backtick,
                    Kind::NoSubstitutionTemplateLiteral,
                    Kind::TemplateTail,
                );
                break;
            }
            if ch == i32::from(b'$') && self.char_at(1) == i32::from(b'{') {
                parts.push(self.text[start..self.pos].as_bytes().to_vec());
                self.pos += 2;
                token = if_else(
                    started_with_backtick,
                    Kind::TemplateHead,
                    Kind::TemplateMiddle,
                );
                break;
            }
            if ch == i32::from(b'\\') {
                parts.push(self.text[start..self.pos].as_bytes().to_vec());
                parts.push(self.scan_escape_sequence(
                    ESCAPE_SEQUENCE_SCANNING_FLAGS_STRING
                        | if_else(
                            should_emit_invalid_escape_error,
                            ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_ERRORS,
                            0,
                        ),
                ));
                start = self.pos;
                continue;
            }
            // Speculated ECMAScript 6 Spec 11.8.6.1:
            // <CR><LF> and <CR> LineTerminatorSequences are normalized to <LF> for Template Values
            if ch == i32::from(b'\r') {
                parts.push(self.text[start..self.pos].as_bytes().to_vec());
                self.pos += 1;
                if self.char() == i32::from(b'\n') {
                    self.pos += 1;
                }
                parts.push(b"\n".to_vec());
                start = self.pos;
                continue;
            }
            self.pos += 1;
        }
        self.token_value = parts.concat();
        token
    }

    /// `func (s *Scanner) scanEscapeSequence`
    fn scan_escape_sequence(&mut self, flags: EscapeSequenceScanningFlags) -> Vec<u8> {
        let start = self.pos;
        self.pos += 1;
        let ch = self.char();
        if ch < 0 {
            self.error(&diagnostics::Unexpected_end_of_text);
            return Vec::new();
        }
        self.pos += 1;
        match ch {
            c if c == i32::from(b'0') && !is_digit(self.char()) => {
                // Although '0' preceding any digit is treated as LegacyOctalEscapeSequence,
                // '\08' should separately be interpreted as '\0' + '8'.
                vec![0x00]
            }
            c if (i32::from(b'0')..=i32::from(b'7')).contains(&c) => {
                // PORT: Go's `case '0'` falls through into '1'-'3', which falls
                // through into '4'-'7' — flattened here. '0'-'3' may consume a
                // second octal digit; '0'-'7' may then consume one more.
                if c <= i32::from(b'3') && is_octal_digit(self.char()) {
                    self.pos += 1;
                }
                if is_octal_digit(self.char()) {
                    self.pos += 1;
                }
                self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS) != 0 {
                    let code = i64::from_str_radix(
                        std::str::from_utf8(&self.text.as_bytes()[start + 1..self.pos])
                            .unwrap_or(""),
                        8,
                    )
                    .unwrap_or(i64::MAX);
                    if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION) != 0
                        && (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ATOM_ESCAPE) == 0
                        && c != i32::from(b'0')
                    {
                        self.error_at(&diagnostics::Octal_escape_sequences_and_backreferences_are_not_allowed_in_a_character_class_If_this_was_intended_as_an_escape_sequence_use_the_syntax_0_instead, start, self.pos - start, &[format!("\\x{code:02x}")]);
                    } else {
                        self.error_at(
                            &diagnostics::Octal_escape_sequences_are_not_allowed_Use_the_syntax_0,
                            start,
                            self.pos - start,
                            &[format!("\\x{code:02x}")],
                        );
                    }
                    return stringutil::encode_js_string_rune(code as i32);
                }
                self.text.as_bytes()[start..self.pos].to_vec()
            }
            c if c == i32::from(b'8') || c == i32::from(b'9') => {
                // the invalid '\8' and '\9'
                self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS) != 0 {
                    if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION) != 0
                        && (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ATOM_ESCAPE) == 0
                    {
                        self.error_at(&diagnostics::Decimal_escape_sequences_and_backreferences_are_not_allowed_in_a_character_class, start, self.pos - start, &[]);
                    } else {
                        self.error_at(
                            &diagnostics::Escape_sequence_0_is_not_allowed,
                            start,
                            self.pos - start,
                            &[
                                String::from_utf8_lossy(&self.text.as_bytes()[start..self.pos])
                                    .into_owned(),
                            ],
                        );
                    }
                    return stringutil::encode_js_string_rune(ch);
                }
                self.text.as_bytes()[start..self.pos].to_vec()
            }
            c if c == i32::from(b'b') => b"\x08".to_vec(),
            c if c == i32::from(b't') => b"\t".to_vec(),
            c if c == i32::from(b'n') => b"\n".to_vec(),
            c if c == i32::from(b'v') => b"\x0b".to_vec(),
            c if c == i32::from(b'f') => b"\x0c".to_vec(),
            c if c == i32::from(b'r') => b"\r".to_vec(),
            c if c == i32::from(b'\'') => b"'".to_vec(),
            c if c == i32::from(b'"') => b"\"".to_vec(),
            c if c == i32::from(b'u') => {
                // '\uDDDD' and '\u{DDDDDD}'
                let extended = self.byte() == Some(b'{');
                self.pos -= 2;
                let code_point = self.scan_unicode_escape(
                    (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS) != 0,
                );
                if extended {
                    if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ALLOW_EXTENDED_UNICODE_ESCAPE) == 0 {
                        self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                        if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS)
                            != 0
                        {
                            self.error_at(&diagnostics::Unicode_escape_sequences_are_only_available_when_the_Unicode_u_flag_or_the_Unicode_Sets_v_flag_is_set, start, self.pos - start, &[]);
                        }
                    }
                    if code_point < 0 {
                        return self.text.as_bytes()[start..self.pos].to_vec();
                    }
                    // In string literals, a high surrogate \u{...} followed by a low
                    // surrogate escape forms a single code point, exactly as adjacent
                    // UTF-16 code units would in a JavaScript string.
                    let combined = if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION)
                        == 0
                        && stringutil::is_high_surrogate(code_point)
                    {
                        self.scan_low_surrogate_escape(code_point)
                    } else {
                        None
                    };
                    if let Some(combined) = combined {
                        return stringutil::encode_js_string_rune(combined);
                    }
                    return stringutil::encode_js_string_rune(code_point);
                }
                if code_point < 0 {
                    return self.text.as_bytes()[start..self.pos].to_vec();
                } else if stringutil::is_high_surrogate(code_point) {
                    if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION) == 0 {
                        // Combine \uHigh followed by any low surrogate escape (\uLow or
                        // \u{Low}) into a single code point in string literals, matching
                        // how adjacent UTF-16 code units pair in a JavaScript string.
                        if let Some(combined) = self.scan_low_surrogate_escape(code_point) {
                            return stringutil::encode_js_string_rune(combined);
                        }
                    } else if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ANY_UNICODE_MODE) != 0
                        && self.char() == i32::from(b'\\')
                        && self.char_at(1) == i32::from(b'u')
                        && self.char_at(2) != i32::from(b'{')
                    {
                        // In regex AnyUnicodeMode, combine \uHigh\uLow so scanClassRanges
                        // can compare the pair numerically. In non-unicode regex mode they
                        // are separate atoms, and extended \u{...} escapes never combine.
                        let saved_pos = self.pos;
                        let next_code_point = self.scan_unicode_escape(
                            (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS)
                                != 0,
                        );
                        if stringutil::is_low_surrogate(next_code_point) {
                            return stringutil::encode_js_string_rune(
                                stringutil::surrogate_pair_to_code_point(
                                    code_point,
                                    next_code_point,
                                ),
                            );
                        }
                        self.pos = saved_pos;
                    }
                }
                // Lone surrogate: encode as a surrogate sentinel so it survives losslessly. In a
                // non-unicode regex this also lets scanClassRanges compare it numerically.
                stringutil::encode_js_string_rune(code_point)
            }
            c if c == i32::from(b'x') => {
                // '\xDD'
                while self.pos < start + 4 {
                    if !is_hex_digit(self.char()) {
                        self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                        if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REPORT_INVALID_ESCAPE_ERRORS)
                            != 0
                        {
                            self.error(&diagnostics::Hexadecimal_digit_expected);
                        }
                        return self.text.as_bytes()[start..self.pos].to_vec();
                    }
                    self.pos += 1;
                }
                self.token_flags |= TokenFlags::HEX_ESCAPE;
                let escaped_value = i64::from_str_radix(
                    std::str::from_utf8(&self.text.as_bytes()[start + 2..self.pos]).unwrap_or(""),
                    16,
                )
                .unwrap_or(i64::MAX);
                stringutil::encode_js_string_rune(escaped_value as i32)
            }
            c if c == i32::from(b'\r') || c == i32::from(b'\n') => {
                // when encountering a LineContinuation (i.e. a backslash and a line terminator sequence),
                // the line terminator is interpreted to be "the empty code unit sequence".
                // PORT: Go's `case '\r'` falls through into `case '\n'`.
                if ch == i32::from(b'\r') && self.byte() == Some(b'\n') {
                    self.pos += 1;
                }
                Vec::new()
            }
            _ => {
                // ch was read as a single byte; for multi-byte UTF-8 characters,
                // we need to decode the full rune and advance past all its bytes.
                let mut ch = ch;
                if ch >= RUNE_SELF {
                    self.pos -= 1; // back up past the single-byte advance
                    let (decoded, size) = decode_rune_in_string(&self.text.as_bytes()[self.pos..]);
                    ch = decoded;
                    self.pos += size;
                }
                // LineContinuation: a backslash followed by a line terminator is "the empty code unit sequence".
                if ch == 0x2028 || ch == 0x2029 {
                    return Vec::new();
                }
                if (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ANY_UNICODE_MODE) != 0
                    || ((flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_REGULAR_EXPRESSION) != 0
                        && (flags & ESCAPE_SEQUENCE_SCANNING_FLAGS_ANNEX_B) == 0
                        && is_identifier_part(ch))
                {
                    self.error_at(
                        &diagnostics::This_character_cannot_be_escaped_in_a_regular_expression,
                        start,
                        self.pos - start,
                        &[],
                    );
                }
                stringutil::encode_js_string_rune(ch)
            }
        }
    }

    /// `func (s *Scanner) scanUnicodeEscape` — known to be at `\u`.
    fn scan_unicode_escape(&mut self, should_emit_invalid_escape_error: bool) -> i32 {
        self.pos += 2;
        let start = self.pos;
        let extended = self.byte() == Some(b'{');
        let hex_digits = if extended {
            self.pos += 1;
            self.scan_hex_digits(1, true, false)
        } else {
            self.token_flags |= TokenFlags::UNICODE_ESCAPE;
            self.scan_hex_digits(4, false, false)
        };
        if hex_digits.is_empty() {
            self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
            if should_emit_invalid_escape_error {
                self.error(&diagnostics::Hexadecimal_digit_expected);
            }
            return -1;
        }
        // Go: `strconv.ParseInt(hexDigits, 16, 32)` — the error is ignored;
        // on overflow ParseInt yields the clamped max.
        let hex_value = i64::from_str_radix(std::str::from_utf8(&hex_digits).unwrap_or(""), 16)
            .unwrap_or(i64::MAX);
        if extended {
            let mut is_invalid_extended_escape = false;
            if hex_value > 0x10FFFF {
                if should_emit_invalid_escape_error {
                    self.error_at(&diagnostics::An_extended_Unicode_escape_value_must_be_between_0x0_and_0x10FFFF_inclusive, start + 1, self.pos - start - 1, &[]);
                }
                is_invalid_extended_escape = true;
            }
            if self.pos >= self.end {
                if should_emit_invalid_escape_error {
                    self.error(&diagnostics::Unexpected_end_of_text);
                }
                is_invalid_extended_escape = true;
            } else if self.byte() == Some(b'}') {
                self.pos += 1;
            } else {
                if should_emit_invalid_escape_error {
                    self.error(&diagnostics::Unterminated_Unicode_escape_sequence);
                }
                is_invalid_extended_escape = true;
            }
            if is_invalid_extended_escape {
                self.token_flags |= TokenFlags::CONTAINS_INVALID_ESCAPE;
                return -1;
            }
            self.token_flags |= TokenFlags::EXTENDED_UNICODE_ESCAPE;
        }
        hex_value as i32
    }

    /// `func (s *Scanner) scanLowSurrogateEscape` — attempts to consume a
    /// low-surrogate Unicode escape (either '\uLow' or '\u{Low}') immediately
    /// following an already-scanned high surrogate and combine them into a
    /// single supplementary code point. On success returns the combined code
    /// point; otherwise restores the scanner position and returns `None`.
    fn scan_low_surrogate_escape(&mut self, high: i32) -> Option<i32> {
        if self.char() != i32::from(b'\\') || self.char_at(1) != i32::from(b'u') {
            return None;
        }
        let saved_pos = self.pos;
        let saved_token_flags = self.token_flags;
        // Speculatively scan the escape with diagnostics suppressed: if it isn't a
        // low surrogate we rewind below, and the caller re-scans the same escape and
        // reports any error then, so reporting here would duplicate diagnostics.
        let low = self.scan_unicode_escape(false);
        if stringutil::is_low_surrogate(low) {
            return Some(stringutil::surrogate_pair_to_code_point(high, low));
        }
        self.pos = saved_pos;
        self.token_flags = saved_token_flags;
        None
    }

    /// `func (s *Scanner) peekUnicodeEscape` — current character is known to
    /// be a backslash. Check for Unicode escape of the form '\uXXXX' or
    /// '\u{XXXXXX}' and return the code point value if valid, otherwise -1.
    fn peek_unicode_escape(&mut self) -> i32 {
        if self.char_at(1) == i32::from(b'u') {
            let save_pos = self.pos;
            let save_token_flags = self.token_flags;
            let code_point = self.scan_unicode_escape(false);
            self.pos = save_pos;
            self.token_flags = save_token_flags;
            return code_point;
        }
        -1
    }

    /// `func (s *Scanner) scanNumber() ast.Kind`
    fn scan_number(&mut self) -> Kind {
        let mut start = self.pos;
        let fixed_part: Vec<u8>;
        if self.char() == i32::from(b'0') {
            self.pos += 1;
            if self.char() == i32::from(b'_') {
                self.token_flags |=
                    TokenFlags::CONTAINS_SEPARATOR | TokenFlags::CONTAINS_INVALID_SEPARATOR;
                self.error_at(
                    &diagnostics::Numeric_separators_are_not_allowed_here,
                    self.pos,
                    1,
                    &[],
                );
                self.pos = start;
                fixed_part = self.scan_number_fragment();
            } else {
                let (digits, is_octal) = self.scan_digits();
                if digits.is_empty() {
                    fixed_part = b"0".to_vec();
                } else if !is_octal {
                    self.token_flags |= TokenFlags::CONTAINS_LEADING_ZERO;
                    fixed_part = digits.as_bytes().to_vec();
                } else {
                    let val = i64::from_str_radix(digits, 8).unwrap_or(i64::MAX);
                    self.token_value = val.to_string().into_bytes();
                    self.token_flags |= TokenFlags::OCTAL;
                    let with_minus = self.token == Kind::MinusToken;
                    let literal = format!("{}0o{:o}", if_else(with_minus, "-", ""), val);
                    if with_minus {
                        start -= 1;
                    }
                    self.error_at(
                        &diagnostics::Octal_literals_are_not_allowed_Use_the_syntax_0,
                        start,
                        self.pos - start,
                        &[literal],
                    );
                    return Kind::NumericLiteral;
                }
            }
        } else {
            fixed_part = self.scan_number_fragment();
        }
        let fixed_part_end = self.pos;
        let mut fractional_part: Vec<u8> = Vec::new();
        let mut exponent_preamble: Vec<u8> = Vec::new();
        let mut exponent_part: Vec<u8> = Vec::new();
        if self.char() == i32::from(b'.') {
            self.pos += 1;
            fractional_part = self.scan_number_fragment();
        }
        let mut end = self.pos;
        if self.char() == i32::from(b'E') || self.char() == i32::from(b'e') {
            self.pos += 1;
            self.token_flags |= TokenFlags::SCIENTIFIC;
            if self.char() == i32::from(b'+') || self.char() == i32::from(b'-') {
                self.pos += 1;
            }
            let start_numeric_part = self.pos;
            exponent_part = self.scan_number_fragment();
            if exponent_part.is_empty() {
                self.error(&diagnostics::Digit_expected);
            } else {
                exponent_preamble = self.text.as_bytes()[end..start_numeric_part].to_vec();
                end = self.pos;
            }
        }
        if self.token_flags.intersects(TokenFlags::CONTAINS_SEPARATOR) {
            self.token_value = fixed_part;
            if !fractional_part.is_empty() {
                self.token_value.push(b'.');
                self.token_value.extend_from_slice(&fractional_part);
            }
            if !exponent_part.is_empty() {
                self.token_value.extend_from_slice(&exponent_preamble);
                self.token_value.extend_from_slice(&exponent_part);
            }
        } else {
            self.token_value = self.text.as_bytes()[start..end].to_vec();
        }
        if self
            .token_flags
            .intersects(TokenFlags::CONTAINS_LEADING_ZERO)
        {
            self.error_at(
                &diagnostics::Decimals_with_leading_zeros_are_not_allowed,
                start,
                self.pos - start,
                &[],
            );
            self.token_value =
                jsnum::from_string(std::str::from_utf8(&self.token_value).unwrap_or(""))
                    .string()
                    .into_bytes();
            return Kind::NumericLiteral;
        }
        let result;
        if fixed_part_end == self.pos {
            result = self.scan_big_int_suffix();
        } else {
            self.token_value =
                jsnum::from_string(std::str::from_utf8(&self.token_value).unwrap_or(""))
                    .string()
                    .into_bytes();
            result = Kind::NumericLiteral;
        }
        let (ch, _) = self.char_and_size();
        if is_identifier_start(ch) {
            let id_start = self.pos;
            let id = self.scan_identifier_parts(IdentifierVariant::Standard);
            if result != Kind::BigIntLiteral
                && id.len() == 1
                && self.text.as_bytes()[id_start] == b'n'
            {
                if self.token_flags.intersects(TokenFlags::SCIENTIFIC) {
                    self.error_at(
                        &diagnostics::A_bigint_literal_cannot_use_exponential_notation,
                        start,
                        self.pos - start,
                        &[],
                    );
                    return result;
                }
                if fixed_part_end < id_start {
                    self.error_at(
                        &diagnostics::A_bigint_literal_must_be_an_integer,
                        start,
                        self.pos - start,
                        &[],
                    );
                    return result;
                }
            }
            self.error_at(
                &diagnostics::An_identifier_or_keyword_cannot_immediately_follow_a_numeric_literal,
                id_start,
                self.pos - id_start,
                &[],
            );
            self.pos = id_start;
        }
        result
    }

    /// `func (s *Scanner) scanNumberFragment() string`
    fn scan_number_fragment(&mut self) -> Vec<u8> {
        let mut start = self.pos;
        let mut allow_separator = false;
        let mut is_previous_token_separator = false;
        let mut result: Vec<u8> = Vec::new();
        loop {
            let before = self.pos;
            self.scan_ascii_while(|b| b.is_ascii_digit());
            if self.pos > before {
                allow_separator = true;
                is_previous_token_separator = false;
            }
            if self.char() == i32::from(b'_') {
                self.token_flags |= TokenFlags::CONTAINS_SEPARATOR;
                if allow_separator {
                    allow_separator = false;
                    is_previous_token_separator = true;
                    result.extend_from_slice(&self.text.as_bytes()[start..self.pos]);
                } else {
                    self.token_flags |= TokenFlags::CONTAINS_INVALID_SEPARATOR;
                    if is_previous_token_separator {
                        self.error_at(
                            &diagnostics::Multiple_consecutive_numeric_separators_are_not_permitted,
                            self.pos,
                            1,
                            &[],
                        );
                    } else {
                        self.error_at(
                            &diagnostics::Numeric_separators_are_not_allowed_here,
                            self.pos,
                            1,
                            &[],
                        );
                    }
                }
                self.pos += 1;
                start = self.pos;
                continue;
            }
            break;
        }
        if is_previous_token_separator {
            self.token_flags |= TokenFlags::CONTAINS_INVALID_SEPARATOR;
            self.error_at(
                &diagnostics::Numeric_separators_are_not_allowed_here,
                self.pos - 1,
                1,
                &[],
            );
        }
        if result.is_empty() {
            return self.text.as_bytes()[start..self.pos].to_vec();
        }
        result.extend_from_slice(&self.text.as_bytes()[start..self.pos]);
        result
    }

    /// `func (s *Scanner) scanDigits() (string, bool)`
    fn scan_digits(&mut self) -> (&'a str, bool) {
        let start = self.pos;
        let mut is_octal = true;
        while is_digit(self.char()) {
            if !is_octal_digit(self.char()) {
                is_octal = false;
            }
            self.pos += 1;
        }
        (&self.text[start..self.pos], is_octal)
    }

    /// `func (s *Scanner) scanHexDigits(minCount int, scanAsManyAsPossible bool, canHaveSeparators bool) string`
    fn scan_hex_digits(
        &mut self,
        min_count: usize,
        scan_as_many_as_possible: bool,
        can_have_separators: bool,
    ) -> Vec<u8> {
        let mut digit_count = 0;
        let start = self.pos;
        let mut allow_separator = false;
        let mut is_previous_token_separator = false;
        while digit_count < min_count || scan_as_many_as_possible {
            let ch = self.char();
            if is_hex_digit(ch) {
                allow_separator = can_have_separators;
                is_previous_token_separator = false;
                digit_count += 1;
            } else if can_have_separators && ch == i32::from(b'_') {
                self.token_flags |= TokenFlags::CONTAINS_SEPARATOR;
                if allow_separator {
                    allow_separator = false;
                    is_previous_token_separator = true;
                } else if is_previous_token_separator {
                    self.error_at(
                        &diagnostics::Multiple_consecutive_numeric_separators_are_not_permitted,
                        self.pos,
                        1,
                        &[],
                    );
                } else {
                    self.error_at(
                        &diagnostics::Numeric_separators_are_not_allowed_here,
                        self.pos,
                        1,
                        &[],
                    );
                }
            } else {
                break;
            }
            self.pos += 1;
        }
        if is_previous_token_separator {
            self.error_at(
                &diagnostics::Numeric_separators_are_not_allowed_here,
                self.pos - 1,
                1,
                &[],
            );
        }
        if digit_count < min_count {
            return Vec::new();
        }
        let digits = &self.text.as_bytes()[start..self.pos];
        if let Some(cached) = self.hex_digit_cache.get(digits) {
            return cached.clone();
        }
        let original = digits.to_vec();
        let mut digits = original.clone();
        if self.token_flags.intersects(TokenFlags::CONTAINS_SEPARATOR) {
            digits.retain(|&b| b != b'_');
        }
        digits.make_ascii_lowercase(); // standardize hex literals to lowercase
        self.hex_digit_cache.insert(original, digits.clone());
        digits
    }

    /// `func (s *Scanner) scanBinaryOrOctalDigits(base int32) string`
    fn scan_binary_or_octal_digits(&mut self, base: i32) -> Vec<u8> {
        let mut sb = Vec::new();
        let mut allow_separator = false;
        let mut is_previous_token_separator = false;
        loop {
            let ch = self.char();
            if is_digit(ch) && ch - i32::from(b'0') < base {
                sb.push(ch as u8);
                allow_separator = true;
                is_previous_token_separator = false;
            } else if ch == i32::from(b'_') {
                self.token_flags |= TokenFlags::CONTAINS_SEPARATOR;
                if allow_separator {
                    allow_separator = false;
                    is_previous_token_separator = true;
                } else if is_previous_token_separator {
                    self.error_at(
                        &diagnostics::Multiple_consecutive_numeric_separators_are_not_permitted,
                        self.pos,
                        1,
                        &[],
                    );
                } else {
                    self.error_at(
                        &diagnostics::Numeric_separators_are_not_allowed_here,
                        self.pos,
                        1,
                        &[],
                    );
                }
            } else {
                break;
            }
            self.pos += 1;
        }
        if is_previous_token_separator {
            self.error_at(
                &diagnostics::Numeric_separators_are_not_allowed_here,
                self.pos - 1,
                1,
                &[],
            );
        }
        sb
    }

    /// `func (s *Scanner) scanBigIntSuffix() ast.Kind`
    fn scan_big_int_suffix(&mut self) -> Kind {
        if self.char() == i32::from(b'n') {
            self.token_value.push(b'n');
            if self
                .token_flags
                .intersects(TokenFlags::BINARY_OR_OCTAL_SPECIFIER)
            {
                let s = String::from_utf8_lossy(&self.token_value).into_owned();
                self.token_value = format!("{}n", jsnum::parse_pseudo_big_int(&s)).into_bytes();
            }
            self.pos += 1;
            return Kind::BigIntLiteral;
        }
        if let Some(cached) = self.number_cache.get(&self.token_value) {
            self.token_value = cached.clone();
        } else {
            let token_value =
                jsnum::from_string(std::str::from_utf8(&self.token_value).unwrap_or("")).string();
            // Go interns the normalized text in `s.numberCache`; key is the raw
            // token value, value is the normalized form.
            self.number_cache
                .insert(self.token_value.clone(), token_value.clone().into_bytes());
            self.token_value = token_value.into_bytes();
        }
        Kind::NumericLiteral
    }

    /// `func (s *Scanner) scanInvalidCharacter()`
    fn scan_invalid_character(&mut self) {
        let (_, size) = self.char_and_size();
        self.error_at(&diagnostics::Invalid_character, self.pos, size, &[]);
        self.pos += size;
        self.token = Kind::Unknown;
    }
}

impl Default for Scanner<'_> {
    /// `defaultScanner()` — `Scanner::new()`.
    fn default() -> Self {
        default_scanner()
    }
}

/// `hasJSDocTag` — reports whether text starts with one of the given tag names
/// followed by a valid JSDoc tag terminator (whitespace, '}', '*', or
/// end-of-string).
fn has_jsdoc_tag(text: &str, tags: &[&str]) -> bool {
    for tag in tags {
        if !text.starts_with(tag) {
            continue;
        }
        if text.len() == tag.len() {
            return true;
        }
        match text.as_bytes()[tag.len()] {
            b' ' | b'\t' | b'\n' | b'\r' | b'}' | b'*' => return true,
            _ => {}
        }
    }
    false
}

/// `func GetIdentifierToken(str string) ast.Kind`
pub fn get_identifier_token(str_: &[u8]) -> Kind {
    if str_.len() >= 2 && str_.len() <= 12 && str_[0].is_ascii_lowercase() {
        if let Some(keyword) = text_to_keyword(str_) {
            return keyword;
        }
    }
    Kind::Identifier
}

/// `func IsValidIdentifier(s string) bool`
pub fn is_valid_identifier(s: &str) -> bool {
    if s.is_empty() {
        return false;
    }
    for (i, ch) in s.char_indices() {
        if (i == 0 && !is_identifier_start(ch as i32)) || (i != 0 && !is_identifier_part(ch as i32))
        {
            return false;
        }
    }
    true
}

/// `func isWordCharacter(ch rune) bool` — Section 6.1.4
pub(crate) fn is_word_character(ch: i32) -> bool {
    is_ascii_letter(ch) || is_digit(ch) || ch == i32::from(b'_')
}

/// `func IsIdentifierStart(ch rune) bool`
pub fn is_identifier_start(ch: i32) -> bool {
    is_ascii_letter(ch)
        || ch == i32::from(b'_')
        || ch == i32::from(b'$')
        || ch >= RUNE_SELF
            && u32::try_from(ch)
                .ok()
                .and_then(char::from_u32)
                .is_some_and(stringutil::is_unicode_identifier_start)
}

/// `func IsIdentifierPart(ch rune) bool`
pub fn is_identifier_part(ch: i32) -> bool {
    is_identifier_part_ex(ch, LanguageVariant::Standard)
}

/// `func IsIdentifierPartEx(ch rune, languageVariant core.LanguageVariant) bool`
pub fn is_identifier_part_ex(ch: i32, language_variant: LanguageVariant) -> bool {
    is_word_character(ch)
        || ch == i32::from(b'$')
        || ch >= RUNE_SELF
            && u32::try_from(ch)
                .ok()
                .and_then(char::from_u32)
                .is_some_and(stringutil::is_unicode_identifier_part)
        || language_variant == LanguageVariant::Jsx && ch == i32::from(b'-') // ":" is part of JSXNamespacedName, but not JSXIdentifier.
}

/// `func TokenToString(token ast.Kind) string`
pub fn token_to_string(token: Kind) -> &'static str {
    token_to_text(token)
}

/// `func StringToToken(s string) ast.Kind` — `Kind::Unknown` for a miss, like
/// Go's zero value on map lookup.
pub fn string_to_token(s: &str) -> Kind {
    text_to_token(s.as_bytes()).unwrap_or(Kind::Unknown)
}

/// `func GetViableKeywordSuggestions() []string`
///
/// PORT: Go iterates a map (nondeterministic order); the list here is in the
/// declared order of `textToKeyword`.
pub fn get_viable_keyword_suggestions() -> Vec<&'static str> {
    const KEYWORDS: &[&str] = &[
        "abstract",
        "accessor",
        "any",
        "asserts",
        "assert",
        "bigint",
        "boolean",
        "break",
        "case",
        "catch",
        "class",
        "continue",
        "const",
        "constructor",
        "debugger",
        "declare",
        "default",
        "defer",
        "delete",
        "do",
        "else",
        "enum",
        "export",
        "extends",
        "false",
        "finally",
        "for",
        "from",
        "function",
        "get",
        "if",
        "immediate",
        "implements",
        "import",
        "in",
        "infer",
        "instanceof",
        "interface",
        "intrinsic",
        "is",
        "keyof",
        "let",
        "module",
        "namespace",
        "never",
        "new",
        "null",
        "number",
        "object",
        "package",
        "private",
        "protected",
        "public",
        "override",
        "out",
        "readonly",
        "require",
        "global",
        "return",
        "satisfies",
        "set",
        "source",
        "static",
        "string",
        "super",
        "switch",
        "symbol",
        "this",
        "throw",
        "true",
        "try",
        "type",
        "typeof",
        "undefined",
        "unique",
        "unknown",
        "using",
        "var",
        "void",
        "while",
        "with",
        "yield",
        "async",
        "await",
        "of",
    ];
    KEYWORDS
        .iter()
        .copied()
        .filter(|text| text.len() > 2)
        .collect()
}

/// `func couldStartTrivia(text string, pos int) bool` — keep in sync with
/// `skip_trivia`.
pub fn could_start_trivia(text: &str, pos: usize) -> bool {
    match text.as_bytes()[pos] {
        // Characters that could start normal trivia
        b'\r' | b'\n' | b'\t' | b'\x0b' | b'\x0c' | b' ' | b'/' |
        // Characters that could start conflict marker trivia
        b'<' | b'|' | b'=' | b'>' => true,
        b'#' => {
            // Only if its the beginning can we have #! trivia
            pos == 0
        }
        ch => ch > MAX_ASCII_CHARACTER,
    }
}

/// `type SkipTriviaOptions struct`
#[derive(Clone, Copy, Default)]
pub struct SkipTriviaOptions {
    pub stop_after_line_break: bool,
    pub stop_at_comments: bool,
    pub in_jsdoc: bool,
}

/// `func SkipTrivia(text string, pos int) int`
pub fn skip_trivia(text: &str, pos: TextPos) -> TextPos {
    skip_trivia_ex(text, pos, None)
}

/// `func SkipTriviaEx(text string, pos int, options *SkipTriviaOptions) int`
pub fn skip_trivia_ex(text: &str, pos: TextPos, options: Option<&SkipTriviaOptions>) -> TextPos {
    if position_is_synthesized(pos) {
        return pos;
    }
    let options = options.copied().unwrap_or_default();

    let text_len = text.len();
    let mut pos = pos as usize; // pos >= 0 after the synthesized check
    let mut can_consume_star = false;
    // Keep in sync with couldStartTrivia
    loop {
        if pos >= text_len {
            return pos as TextPos;
        }
        let (ch, size) = decode_rune_in_string(&text.as_bytes()[pos..]);
        match u8::try_from(ch) {
            Ok(b'\r' | b'\n') => {
                if ch == i32::from(b'\r') && pos + 1 < text_len && text.as_bytes()[pos + 1] == b'\n'
                {
                    pos += 1;
                }
                pos += 1;
                if options.stop_after_line_break {
                    return pos as TextPos;
                }
                can_consume_star = options.in_jsdoc;
                continue;
            }
            Ok(b'\t' | b'\x0b' | b'\x0c' | b' ') => {
                pos += 1;
                continue;
            }
            Ok(b'/') => {
                if options.stop_at_comments {
                    return pos as TextPos;
                }
                if pos + 1 < text_len {
                    if text.as_bytes()[pos + 1] == b'/' {
                        pos += 2;
                        while pos < text_len {
                            let (ch, size) = decode_rune_in_string(&text.as_bytes()[pos..]);
                            if is_line_break_rune(ch) {
                                break;
                            }
                            pos += size;
                        }
                        can_consume_star = false;
                        continue;
                    }
                    if text.as_bytes()[pos + 1] == b'*' {
                        pos += 2;
                        while pos < text_len {
                            if text.as_bytes()[pos] == b'*'
                                && pos + 1 < text_len
                                && text.as_bytes()[pos + 1] == b'/'
                            {
                                pos += 2;
                                break;
                            }
                            let (_, size) = decode_rune_in_string(&text.as_bytes()[pos..]);
                            pos += size;
                        }
                        can_consume_star = false;
                        continue;
                    }
                }
                return pos as TextPos;
            }
            Ok(b'<' | b'|' | b'=' | b'>') => {
                if is_conflict_marker_trivia(text, pos) {
                    pos = scan_conflict_marker_trivia(text, pos, None);
                    can_consume_star = false;
                    continue;
                }
                return pos as TextPos;
            }
            Ok(b'#') => {
                if pos == 0 && is_shebang_trivia(text, pos) {
                    pos = scan_shebang_trivia(text, pos);
                    can_consume_star = false;
                    continue;
                }
                return pos as TextPos;
            }
            Ok(b'*') => {
                if can_consume_star {
                    pos += 1;
                    can_consume_star = false;
                    continue;
                }
                return pos as TextPos;
            }
            _ => {
                if ch > i32::from(MAX_ASCII_CHARACTER) && is_white_space_like_rune(ch) {
                    pos += size;
                    continue;
                }
                return pos as TextPos;
            }
        }
    }
}

// All conflict markers consist of the same character repeated seven times.  If it is
// a <<<<<<< or >>>>>>> marker then it is also followed by a space.
const MERGE_CONFLICT_MARKER_LENGTH: usize = "<<<<<<<".len();
const MAX_ASCII_CHARACTER: u8 = 127;

/// `func isConflictMarkerTrivia(text string, pos int) bool`
pub(crate) fn is_conflict_marker_trivia(text: &str, pos: usize) -> bool {
    // PORT: Go panics on `pos < 0`; `usize` cannot express it.

    // Fast reject: a conflict marker is the same byte repeated seven times. If the
    // second byte differs (the overwhelmingly common case for `<`, `>`, `=`, `|`
    // tokens), it cannot be a marker, so skip the line-start check entirely.
    let bytes = text.as_bytes();
    if pos + 1 >= bytes.len() || bytes[pos + 1] != bytes[pos] {
        return false;
    }

    // Conflict markers must be at the start of a line.
    let mut at_line_start = pos == 0 || is_line_break_rune(i32::from(bytes[pos - 1]));
    if !at_line_start && pos >= 2 {
        let (prev, _) = decode_last_rune_in_string(&bytes[..pos - 2]);
        at_line_start = is_line_break_rune(prev);
    }
    if at_line_start {
        let ch = bytes[pos];

        if pos + MERGE_CONFLICT_MARKER_LENGTH < bytes.len() {
            for i in 0..MERGE_CONFLICT_MARKER_LENGTH {
                if bytes[pos + i] != ch {
                    return false;
                }
            }

            return ch == b'=' || bytes[pos + MERGE_CONFLICT_MARKER_LENGTH] == b' ';
        }
    }

    false
}

/// `func scanConflictMarkerTrivia(text string, pos int, reportError func(...)) int`
fn scan_conflict_marker_trivia(
    text: &str,
    mut pos: usize,
    report_error: Option<&mut ErrorCallback<'_>>,
) -> usize {
    if let Some(report_error) = report_error {
        report_error(
            &diagnostics::Merge_conflict_marker_encountered,
            pos,
            MERGE_CONFLICT_MARKER_LENGTH,
            &[],
        );
    }
    let (mut ch, mut size) = decode_rune_in_string(&text.as_bytes()[pos..]);
    let length = text.len();

    if ch == i32::from(b'<') || ch == i32::from(b'>') {
        while pos < length && !is_line_break_rune(ch) {
            pos += size;
            (ch, size) = decode_rune_in_string(&text.as_bytes()[pos.min(length)..]);
        }
    } else {
        if ch != i32::from(b'|') && ch != i32::from(b'=') {
            panic!("Assertion failed: ch must be either '|' or '='");
        }
        // Consume everything from the start of a ||||||| or ======= marker to the start
        // of the next ======= or >>>>>>> marker.
        while pos < length {
            let current_char = text.as_bytes()[pos];
            if (current_char == b'=' || current_char == b'>')
                && i32::from(current_char) != ch
                && is_conflict_marker_trivia(text, pos)
            {
                break;
            }

            pos += 1;
        }
    }

    pos
}

/// `func isShebangTrivia(text string, pos int) bool`
fn is_shebang_trivia(text: &str, pos: usize) -> bool {
    if text.len() < 2 {
        return false;
    }
    // Go: `panic("Shebangs check must only be done at the start of the file")`.
    assert!(
        pos == 0,
        "Shebangs check must only be done at the start of the file"
    );
    text.as_bytes()[0] == b'#' && text.as_bytes()[1] == b'!'
}

/// `func scanShebangTrivia(text string, pos int) int`
fn scan_shebang_trivia(text: &str, mut pos: usize) -> usize {
    pos += 2;
    while pos < text.len() {
        let (ch, size) = decode_rune_in_string(&text.as_bytes()[pos..]);
        if is_line_break_rune(ch) {
            break;
        }
        pos += size;
    }
    pos
}

/// `func GetShebang(text string) string`
pub fn get_shebang(text: &str) -> &str {
    if !is_shebang_trivia(text, 0) {
        return "";
    }

    let end = scan_shebang_trivia(text, 0);
    &text[..end]
}

/// `func GetScannerForSourceFile(sourceFile *ast.SourceFile, pos int) *Scanner`
pub fn get_scanner_for_source_file<'a>(source_file: &'a SourceFile, pos: usize) -> Scanner<'a> {
    let mut s = Scanner::<'a>::new();
    s.text = &source_file.text;
    s.pos = pos;
    s.end = s.text.len();
    s.language_variant = source_file.language_variant;
    s.scan();
    s
}

/// `func ScanTokenAtPosition(sourceFile *ast.SourceFile, pos int) ast.Kind`
pub fn scan_token_at_position(source_file: &SourceFile, pos: usize) -> Kind {
    let s = get_scanner_for_source_file(source_file, pos);
    s.token
}

/// `func GetRangeOfTokenAtPosition(sourceFile *ast.SourceFile, pos int) core.TextRange`
pub fn get_range_of_token_at_position(source_file: &SourceFile, pos: usize) -> TextRange {
    let s = get_scanner_for_source_file(source_file, pos);
    TextRange::new(s.token_start as i32, s.pos as i32)
}

/// `func GetTokenPosOfNode(node *ast.Node, sourceFile *ast.SourceFile, includeJSDoc bool) int`
pub fn get_token_pos_of_node(
    node: NodeId,
    source_file: &SourceFile,
    include_jsdoc: bool,
    nodes: &[Node],
) -> TextPos {
    // With nodes that have no width (i.e. 'Missing' nodes), we actually *don't*
    // want to skip trivia because this will launch us forward to the next token.
    if node_is_missing(Some(node), nodes) {
        return nodes[node].pos();
    }
    if is_js_doc_node(&nodes[node]) || nodes[node].kind == Kind::JsxText {
        // JsxText cannot actually contain comments, even though the scanner will think it sees comments
        return skip_trivia_ex(
            &source_file.text,
            nodes[node].pos(),
            Some(&SkipTriviaOptions {
                stop_at_comments: true,
                ..Default::default()
            }),
        );
    }
    // PORT(deferred): `node.JSDoc(sourceFile)` / `node.EagerJSDoc` (lazy JSDoc
    // resolution + jsdocCache) is not yet ported in tsc-ast, so the
    // `includeJSDoc` JSDoc-hop branch cannot be evaluated.
    let _ = include_jsdoc;
    skip_trivia_ex(
        &source_file.text,
        nodes[node].pos(),
        Some(&SkipTriviaOptions {
            in_jsdoc: nodes[node].flags.intersects(NodeFlags::JSDOC),
            ..Default::default()
        }),
    )
}

/// `func getErrorRangeForArrowFunction(sourceFile *ast.SourceFile, node *ast.Node) core.TextRange`
fn get_error_range_for_arrow_function(
    source_file: &SourceFile,
    node: NodeId,
    nodes: &[Node],
) -> TextRange {
    let pos = skip_trivia(&source_file.text, nodes[node].pos());
    if let Some(body) = nodes[node].body() {
        if nodes[body].kind == Kind::Block {
            let start_line = get_ecma_line_of_position(source_file, nodes[body].pos());
            let end_line = get_ecma_line_of_position(source_file, nodes[body].end());
            if start_line < end_line {
                // The arrow function spans multiple lines, make the error span be the first line, inclusive.
                return TextRange::new(
                    pos,
                    get_ecma_end_line_position(source_file, start_line) + 1,
                );
            }
        }
    }
    TextRange::new(pos, nodes[node].end())
}

/// `func findOriginatingJSDocSatisfiesTag(sourceFile *ast.SourceFile, node *ast.Node) *ast.Node`
fn find_originating_jsdoc_satisfies_tag(
    source_file: &SourceFile,
    node: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    let _ = source_file;
    let target_type = nodes[node].as_satisfies_expression().type_.unwrap();
    if !nodes[target_type].flags.intersects(NodeFlags::REPARSED) {
        return None;
    }
    let mut current = nodes[node].parent;
    while let Some(cur) = current {
        if !nodes[cur].flags.intersects(NodeFlags::HAS_JSDOC) {
            current = nodes[cur].parent;
            continue;
        }
        let mut first_satisfies_tag: Option<NodeId> = None;
        for js_doc in tsc_ast::eager_js_doc(nodes, cur, None) {
            if let Some(tags) = nodes[js_doc].as_js_doc().tags.clone() {
                for &tag in &tags.nodes {
                    if nodes[tag].kind != Kind::JSDocSatisfiesTag {
                        continue;
                    }
                    if first_satisfies_tag.is_none() {
                        first_satisfies_tag = Some(tag);
                    }
                    if let Some(type_expr) =
                        nodes[tag].as_js_doc_satisfies_tag().type_expression
                    {
                        if let Some(t) = nodes[type_expr].type_() {
                            if nodes[t].loc == nodes[target_type].loc {
                                return Some(tag);
                            }
                        }
                    }
                }
            }
        }
        return first_satisfies_tag;
    }
    None
}

/// `func GetErrorRangeForNode(sourceFile *ast.SourceFile, node *ast.Node) core.TextRange`
pub fn get_error_range_for_node(
    source_file: &SourceFile,
    node: NodeId,
    nodes: &[Node],
) -> TextRange {
    let mut error_node = Some(node);
    match nodes[node].kind {
        Kind::SourceFile => {
            let pos = skip_trivia(&source_file.text, 0);
            if pos as usize == source_file.text.len() {
                return TextRange::new(0, 0);
            }
            return get_range_of_token_at_position(source_file, pos as usize);
        }
        // This list is a work in progress. Add missing node kinds to improve their error spans
        Kind::FunctionDeclaration | Kind::MethodDeclaration
            if !nodes[node].flags.intersects(NodeFlags::REPARSED) =>
        {
            error_node = get_name_of_declaration(Some(node), nodes);
        }
        Kind::FunctionDeclaration | Kind::MethodDeclaration => {}
        Kind::VariableDeclaration
        | Kind::BindingElement
        | Kind::ClassDeclaration
        | Kind::InterfaceDeclaration
        | Kind::ModuleDeclaration
        | Kind::EnumDeclaration
        | Kind::EnumMember
        | Kind::FunctionExpression
        | Kind::GetAccessor
        | Kind::SetAccessor
        | Kind::TypeAliasDeclaration
        | Kind::JSTypeAliasDeclaration
        | Kind::PropertyDeclaration
        | Kind::PropertySignature
        | Kind::NamespaceImport => {
            error_node = get_name_of_declaration(Some(node), nodes);
        }
        Kind::ClassExpression => {
            error_node = nodes[node].name();
        }
        Kind::ArrowFunction => {
            return get_error_range_for_arrow_function(source_file, node, nodes);
        }
        Kind::CaseClause | Kind::DefaultClause => {
            let start = skip_trivia(&source_file.text, nodes[node].pos());
            let mut end = nodes[node].end();
            if let Some(statements) = nodes[node].statements() {
                if !statements.is_empty() {
                    end = nodes[statements[0]].pos();
                }
            }
            return TextRange::new(start, end);
        }
        Kind::ReturnStatement | Kind::YieldExpression => {
            let pos = skip_trivia(&source_file.text, nodes[node].pos());
            return get_range_of_token_at_position(source_file, pos as usize);
        }
        Kind::SatisfiesExpression => {
            if let Some(js_doc_satisfies_tag) =
                find_originating_jsdoc_satisfies_tag(source_file, node, nodes)
            {
                let tag_name = nodes[js_doc_satisfies_tag].tag_name().unwrap();
                let pos = skip_trivia(&source_file.text, nodes[tag_name].pos());
                return get_range_of_token_at_position(source_file, pos as usize);
            }
            let expr = nodes[node].as_satisfies_expression().expression.unwrap();
            let pos = skip_trivia(&source_file.text, nodes[expr].end());
            return get_range_of_token_at_position(source_file, pos as usize);
        }
        Kind::Constructor => {
            if nodes[node].flags.intersects(NodeFlags::REPARSED) {
                // error_node stays node
            } else {
                let mut scanner =
                    get_scanner_for_source_file(source_file, nodes[node].pos() as usize);
                let start = scanner.token_start();
                while scanner.token() != Kind::ConstructorKeyword
                    && scanner.token() != Kind::StringLiteral
                    && scanner.token() != Kind::EndOfFile
                {
                    scanner.scan();
                }
                return TextRange::new(start as i32, scanner.token_end() as i32);
            }
        }
        _ => {}
    }
    let Some(error_node) = error_node else {
        // If we don't have a better node, then just set the error on the first token of
        // construct.
        return get_range_of_token_at_position(source_file, nodes[node].pos() as usize);
    };
    let mut pos = nodes[error_node].pos();
    if !node_is_missing(Some(error_node), nodes) && !is_jsx_text(&nodes[error_node]) {
        pos = skip_trivia(&source_file.text, pos);
    }
    TextRange::new(pos, nodes[error_node].end())
}

/// `func ComputeLineOfPosition(lineStarts []core.TextPos, pos int) int`
pub fn compute_line_of_position(line_starts: &[TextPos], pos: i32) -> i32 {
    let mut low = 0i32;
    let mut high = line_starts.len() as i32 - 1;
    while low <= high {
        let middle = low + ((high - low) >> 1);
        let value = line_starts[middle as usize];
        if value < pos {
            low = middle + 1;
        } else if value > pos {
            high = middle - 1;
        } else {
            return middle;
        }
    }
    low - 1
}

/// `type SourceFileLike interface { Text() string; ECMALineMap() []core.TextPos }`
///
/// PORT: Go's `ECMALineMap` is a lazily computed cache on `SourceFile`; the
/// Rust `SourceFile` has no cache field, so `ecma_line_map` recomputes via
/// `core::compute_ecma_line_starts` on each call.
pub trait SourceFileLike {
    fn text(&self) -> &str;
    fn ecma_line_map(&self) -> Vec<TextPos>;
}

impl SourceFileLike for SourceFile {
    fn text(&self) -> &str {
        &self.text
    }
    fn ecma_line_map(&self) -> Vec<TextPos> {
        tsc_core::core::compute_ecma_line_starts(&self.text)
    }
}

/// `func GetECMALineStarts(sourceFile ast.SourceFileLike) []core.TextPos`
pub fn get_ecma_line_starts(source_file: &impl SourceFileLike) -> Vec<TextPos> {
    source_file.ecma_line_map()
}

/// `func GetECMALineOfPosition(sourceFile ast.SourceFileLike, pos int) int`
pub fn get_ecma_line_of_position(source_file: &impl SourceFileLike, pos: i32) -> i32 {
    let line_map = get_ecma_line_starts(source_file);
    compute_line_of_position(&line_map, pos)
}

/// `GetECMALineAndUTF16CharacterOfPosition` returns the 0-based line number and
/// the UTF-16 code unit offset from the start of that line for the given byte
/// position. Uses ECMAScript line separators (LF, CR, CRLF, LS, PS).
pub fn get_ecma_line_and_utf16_character_of_position(
    source_file: &impl SourceFileLike,
    pos: i32,
) -> (i32, UTF16Offset) {
    let line_map = get_ecma_line_starts(source_file);
    let line = compute_line_of_position(&line_map, pos);
    let character = utf16_len(&source_file.text()[line_map[line as usize] as usize..pos as usize]);
    (line, character)
}

/// `GetECMALineAndByteOffsetOfPosition` returns the 0-based line number and the
/// raw UTF-8 byte offset from the start of that line for the given byte
/// position. Uses ECMAScript line separators (LF, CR, CRLF, LS, PS).
/// Unlike `get_ecma_line_and_utf16_character_of_position`, the offset is in
/// bytes, not UTF-16 code units.
pub fn get_ecma_line_and_byte_offset_of_position(
    source_file: &impl SourceFileLike,
    pos: i32,
) -> (i32, i32) {
    let line_map = get_ecma_line_starts(source_file);
    let line = compute_line_of_position(&line_map, pos);
    let byte_offset = pos - line_map[line as usize];
    (line, byte_offset)
}

/// `func GetECMAEndLinePosition(sourceFile *ast.SourceFile, line int) int`
///
/// PORT: takes `&impl SourceFileLike` — the Go implementation only calls
/// `Text()`/`ECMALineMap()` on it.
pub fn get_ecma_end_line_position(source_file: &impl SourceFileLike, line: i32) -> i32 {
    let mut pos = get_ecma_line_starts(source_file)[line as usize] as usize;
    let bytes = source_file.text().as_bytes();
    loop {
        let (ch, size) = decode_rune_in_string(&bytes[pos..]);
        if size == 0 || is_line_break_rune(ch) {
            return pos as i32 - 1;
        }
        pos += size;
    }
}

/// `GetECMAPositionOfLineAndUTF16Character` converts a 0-based line number and
/// UTF-16 code unit character offset back to an absolute byte position in the
/// source text. Uses ECMAScript line separators.
pub fn get_ecma_position_of_line_and_utf16_character(
    source_file: &impl SourceFileLike,
    line: i32,
    character: UTF16Offset,
) -> i32 {
    let line_starts = get_ecma_line_starts(source_file);
    compute_position_of_line_and_utf16_character(
        &line_starts,
        line,
        character,
        source_file.text(),
        false,
    )
}

/// `GetECMAPositionOfLineAndByteOffset` converts a 0-based line number and byte
/// offset from line start back to an absolute byte position in the source text.
/// Uses ECMAScript line separators.
pub fn get_ecma_position_of_line_and_byte_offset(
    source_file: &impl SourceFileLike,
    line: i32,
    byte_offset: i32,
) -> i32 {
    compute_position_of_line_and_byte_offset(&get_ecma_line_starts(source_file), line, byte_offset)
}

/// `ComputePositionOfLineAndByteOffset` computes a byte position from a line
/// and raw byte offset from the line start. This is a simple addition with
/// validation.
pub fn compute_position_of_line_and_byte_offset(
    line_starts: &[TextPos],
    line: i32,
    byte_offset: i32,
) -> i32 {
    if line < 0 || line >= line_starts.len() as i32 {
        panic!(
            "Bad line number. Line: {}, lineStarts.length: {}.",
            line,
            line_starts.len()
        );
    }
    line_starts[line as usize] + byte_offset
}

/// `ComputePositionOfLineAndUTF16Character` converts a line and UTF-16
/// character offset back to a byte position. The character parameter is
/// measured in UTF-16 code units. It scans from the line start to correctly
/// handle multi-byte characters. When `allow_edits` is true, out-of-range
/// values are clamped instead of panicking.
pub fn compute_position_of_line_and_utf16_character(
    line_starts: &[TextPos],
    mut line: i32,
    character: UTF16Offset,
    text: &str,
    allow_edits: bool,
) -> i32 {
    if line < 0 || line >= line_starts.len() as i32 {
        if allow_edits {
            // Clamp line to nearest allowable value
            if line < 0 {
                line = 0;
            } else {
                line = line_starts.len() as i32 - 1;
            }
        } else {
            panic!(
                "Bad line number. Line: {}, lineStarts.length: {}.",
                line,
                line_starts.len()
            );
        }
    }

    let line_start = line_starts[line as usize];

    if character > 0 {
        // UTF-16 character offset: scan from line start counting UTF-16 code units.
        let mut line_end = text.len();
        if line + 1 < line_starts.len() as i32 {
            line_end = line_starts[(line + 1) as usize] as usize;
        }
        let mut utf16_count: UTF16Offset = 0;
        let mut pos = line_start as usize;
        while pos < line_end {
            if utf16_count >= character {
                break;
            }
            let (r, size) = decode_rune_in_string(&text.as_bytes()[pos..]);
            utf16_count += utf16_rune_len(r);
            pos += size;
        }
        if !allow_edits {
            if pos == line_end && utf16_count < character {
                panic!("Bad UTF-16 character offset. Line: {line}, character: {character}.");
            }
            debug::assert_!(pos <= text.len());
            return pos as i32;
        }
        if pos > text.len() {
            return text.len() as i32;
        }
        return pos as i32;
    }

    // Character is 0: line start position.
    let res = line_start;

    if allow_edits {
        if res > text.len() as i32 {
            return text.len() as i32;
        }
        return res;
    }
    debug::assert_!(res <= text.len() as i32); // Allow single character overflow for trailing newline
    res
}

/// `func GetLeadingCommentRanges(f *ast.NodeFactory, text string, pos int) iter.Seq[ast.CommentRange]`
///
/// PORT: Go's `iter.Seq` yield-iterator becomes collect-then-iterate `Vec`.
pub fn get_leading_comment_ranges(f: &NodeFactory, text: &str, pos: i32) -> Vec<CommentRange> {
    iterate_comment_ranges(f, text, pos, false)
}

/// `func GetTrailingCommentRanges(f *ast.NodeFactory, text string, pos int) iter.Seq[ast.CommentRange]`
pub fn get_trailing_comment_ranges(f: &NodeFactory, text: &str, pos: i32) -> Vec<CommentRange> {
    iterate_comment_ranges(f, text, pos, true)
}

/// `iterateCommentRanges` — returns each comment range following the provided
/// position. Single-line comment ranges include the leading double-slash
/// characters but not the ending line break. Multi-line comment ranges include
/// the leading slash-asterisk and trailing asterisk-slash characters.
fn iterate_comment_ranges(
    f: &NodeFactory,
    text: &str,
    pos: i32,
    trailing: bool,
) -> Vec<CommentRange> {
    let mut result = Vec::new();
    let mut pending_pos = 0i32;
    let mut pending_end = 0i32;
    let mut pending_kind = Kind::Unknown;
    let mut pending_has_trailing_new_line = false;
    let mut has_pending_comment_range = false;
    let mut collecting = trailing;
    let mut pos = pos;
    if pos == 0 {
        collecting = true;
        if is_shebang_trivia(text, pos as usize) {
            pos = scan_shebang_trivia(text, pos as usize) as i32;
        }
    }
    'scan: while pos >= 0 && (pos as usize) < text.len() {
        let (ch, size) = decode_rune_in_string(&text.as_bytes()[pos as usize..]);
        match u8::try_from(ch) {
            Ok(b'\r' | b'\n') => {
                if ch == i32::from(b'\r')
                    && pos + 1 < text.len() as i32
                    && text.as_bytes()[(pos + 1) as usize] == b'\n'
                {
                    pos += 1;
                }
                pos += 1;
                if trailing {
                    break 'scan;
                }

                collecting = true;
                if has_pending_comment_range {
                    pending_has_trailing_new_line = true;
                }

                continue;
            }
            Ok(b'\t' | b'\x0b' | b'\x0c' | b' ') => {
                pos += 1;
                continue;
            }
            Ok(b'/') => {
                let next_char = text
                    .as_bytes()
                    .get((pos + 1) as usize)
                    .copied()
                    .unwrap_or(0);
                let mut has_trailing_new_line = false;
                if next_char == b'/' || next_char == b'*' {
                    let kind = if next_char == b'/' {
                        Kind::SingleLineCommentTrivia
                    } else {
                        Kind::MultiLineCommentTrivia
                    };

                    let start_pos = pos;
                    pos += 2;
                    if next_char == b'/' {
                        while (pos as usize) < text.len() {
                            let (c, s) = decode_rune_in_string(&text.as_bytes()[pos as usize..]);
                            if is_line_break_rune(c) {
                                has_trailing_new_line = true;
                                break;
                            }
                            pos += s as i32;
                        }
                    } else if let Some(i) = find_subslice(&text.as_bytes()[pos as usize..], b"*/") {
                        pos += (i + 2) as i32;
                    } else {
                        pos = text.len() as i32;
                    }

                    if collecting {
                        if has_pending_comment_range {
                            result.push(f.new_comment_range(
                                pending_kind,
                                pending_pos,
                                pending_end,
                                pending_has_trailing_new_line,
                            ));
                        }

                        pending_pos = start_pos;
                        pending_end = pos;
                        pending_kind = kind;
                        pending_has_trailing_new_line = has_trailing_new_line;
                        has_pending_comment_range = true;
                    }

                    continue;
                }
                break 'scan;
            }
            _ => {
                if ch > i32::from(MAX_ASCII_CHARACTER) && is_white_space_like_rune(ch) {
                    if has_pending_comment_range && is_line_break_rune(ch) {
                        pending_has_trailing_new_line = true;
                    }
                    pos += size as i32;
                    continue;
                }
                break 'scan;
            }
        }
    }

    if has_pending_comment_range {
        result.push(f.new_comment_range(
            pending_kind,
            pending_pos,
            pending_end,
            pending_has_trailing_new_line,
        ));
    }
    result
}

/// `strings.Index(text[pos:], "*/")` — byte-substring search.
fn find_subslice(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    haystack.windows(needle.len()).position(|w| w == needle)
}

// =============================================================================
// Shared low-level helpers (Go rune/`unicode/utf8` shims + `stringutil` on
// i32 runes). Also used by `regexp.rs`.
// =============================================================================

pub(crate) const RUNE_ERROR: i32 = 0xFFFD; // utf8.RuneError — U+FFFD
pub(crate) const RUNE_SELF: i32 = 0x80; // utf8.RuneSelf

/// `stringutil.IsASCIILetter` on a Go rune (byte or decoded code point; -1 = EOF).
pub(crate) fn is_ascii_letter(ch: i32) -> bool {
    matches!(u8::try_from(ch), Ok(b'a'..=b'z' | b'A'..=b'Z'))
}

/// `stringutil.IsDigit` on a Go rune.
pub(crate) fn is_digit(ch: i32) -> bool {
    matches!(u8::try_from(ch), Ok(b'0'..=b'9'))
}

/// `stringutil.IsOctalDigit` on a Go rune.
pub(crate) fn is_octal_digit(ch: i32) -> bool {
    matches!(u8::try_from(ch), Ok(b'0'..=b'7'))
}

/// `stringutil.IsHexDigit` on a Go rune.
pub(crate) fn is_hex_digit(ch: i32) -> bool {
    matches!(
        u8::try_from(ch),
        Ok(b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F')
    )
}

/// `stringutil.IsLineBreak` on a Go rune (-1 / out-of-range → false).
pub(crate) fn is_line_break_rune(ch: i32) -> bool {
    matches!(ch, 0x0A | 0x0D | 0x2028 | 0x2029)
}

/// `stringutil.IsWhiteSpaceSingleLine` on a Go rune.
pub(crate) fn is_white_space_single_line_rune(ch: i32) -> bool {
    u32::try_from(ch)
        .ok()
        .and_then(char::from_u32)
        .is_some_and(stringutil::is_white_space_single_line)
}

/// `stringutil.IsWhiteSpaceLike` on a Go rune.
pub(crate) fn is_white_space_like_rune(ch: i32) -> bool {
    u32::try_from(ch)
        .ok()
        .and_then(char::from_u32)
        .is_some_and(stringutil::is_white_space_like)
}

/// `utf16.RuneLen` — 1 for values below 0x10000, 2 for non-BMP code points,
/// -1 for out-of-range values.
pub(crate) fn utf16_rune_len(ch: i32) -> i32 {
    if !(0..=0x10FFFF).contains(&ch) {
        -1
    } else if ch < 0x10000 {
        1
    } else {
        2
    }
}

/// Go `string(ch)` where a rune becomes a diagnostic arg — the UTF-8 encoding
/// of the code point; invalid runes give U+FFFD like Go.
pub(crate) fn rune_to_string(ch: i32) -> String {
    char::from_u32(ch as u32).unwrap_or('\u{FFFD}').to_string()
}

/// PORT: mirrors Go's utf8.DecodeRuneInString (RFC 3629-strict decoding):
/// empty input -> (RuneError, 0); invalid encoding -> (RuneError, 1);
/// otherwise the decoded rune and its width in bytes. (The decoder in
/// tsc-stringutil is crate-private, so a local copy lives here.)
pub(crate) fn decode_rune_in_string(s: &[u8]) -> (i32, usize) {
    if s.is_empty() {
        return (RUNE_ERROR, 0);
    }
    let p0 = s[0];
    if p0 < 0x80 {
        return (i32::from(p0), 1);
    }
    // (size, accept range for the first continuation byte)
    let (size, lo, hi): (usize, u8, u8) = match p0 {
        0xC2..=0xDF => (2, 0x80, 0xBF),
        0xE0 => (3, 0xA0, 0xBF),
        0xE1..=0xEC => (3, 0x80, 0xBF),
        0xED => (3, 0x80, 0x9F),
        0xEE..=0xEF => (3, 0x80, 0xBF),
        0xF0 => (4, 0x90, 0xBF),
        0xF1..=0xF3 => (4, 0x80, 0xBF),
        0xF4 => (4, 0x80, 0x8F),
        _ => return (RUNE_ERROR, 1),
    };
    if s.len() < size {
        return (RUNE_ERROR, 1);
    }
    let b1 = s[1];
    if !(lo..=hi).contains(&b1) {
        return (RUNE_ERROR, 1);
    }
    let mut r = match size {
        2 => u32::from(p0 & 0x1F),
        3 => u32::from(p0 & 0x0F),
        _ => u32::from(p0 & 0x07),
    };
    r = (r << 6) | u32::from(b1 & 0x3F);
    for &b in &s[2..size] {
        if !(0x80..=0xBF).contains(&b) {
            return (RUNE_ERROR, 1);
        }
        r = (r << 6) | u32::from(b & 0x3F);
    }
    // The accept ranges above exclude surrogates and out-of-range code points.
    (char::from_u32(r).map_or(RUNE_ERROR, |c| c as i32), size)
}

/// PORT: mirrors Go's utf8.DecodeLastRuneInString (RFC 3629-strict decoding):
/// empty input -> (RuneError, 0); invalid encoding -> (RuneError, 1);
/// otherwise the last decoded rune and its width.
pub(crate) fn decode_last_rune_in_string(s: &[u8]) -> (i32, usize) {
    const UTF_MAX: usize = 4;
    let end = s.len();
    if end == 0 {
        return (RUNE_ERROR, 0);
    }
    let mut start = end - 1;
    let r = i32::from(s[start]);
    if r < RUNE_SELF {
        return (r, 1);
    }
    // Guard against O(n^2) behavior when traversing backwards through strings
    // with long sequences of invalid UTF-8 (same as Go).
    let lim = end.saturating_sub(UTF_MAX);
    while start > lim {
        start -= 1;
        if s[start] & 0xC0 != 0x80 {
            // utf8.RuneStart
            break;
        }
    }
    // Go: `if start < 0 { start = 0 }` — unreachable with usize, the loop above
    // bottoms out at 0.
    let (r, size) = decode_rune_in_string(&s[start..end]);
    if start + size != end {
        return (RUNE_ERROR, 1);
    }
    (r, size)
}

#[cfg(test)]
mod tests;
