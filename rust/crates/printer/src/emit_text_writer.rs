// Ported from tsc/internal/printer/emittextwriter.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::SymbolId;
use tsc_core::core::UTF16Offset;

/// `type EmitTextWriter interface` — externally opaque interface for printing text.
///
/// PORT: `*ast.Symbol` became `SymbolId`; the symbol arena is not consulted
/// by any writer implementation, matching Go where writers ignore the
/// argument.
///
/// PORT: Go probes writers with type assertions (`interface{ Grow(n int) }`);
/// the trait instead exposes `grow`/`as_any_mut`/`into_any` hooks so callers
/// can reach the same capabilities and recover concrete writer types (used to
/// unwrap `TrailingSemicolonDeferringWriter` and `ChangeTrackerWriter`).
pub trait EmitTextWriter {
    /// `Write(s string)`
    fn write(&mut self, s: &str);
    /// `WriteTrailingSemicolon(text string)`
    fn write_trailing_semicolon(&mut self, text: &str);
    /// `WriteComment(text string)`
    fn write_comment(&mut self, text: &str);
    /// `WriteKeyword(text string)`
    fn write_keyword(&mut self, text: &str);
    /// `WriteOperator(text string)`
    fn write_operator(&mut self, text: &str);
    /// `WritePunctuation(text string)`
    fn write_punctuation(&mut self, text: &str);
    /// `WriteSpace(text string)`
    fn write_space(&mut self, text: &str);
    /// `WriteStringLiteral(text string)`
    fn write_string_literal(&mut self, text: &str);
    /// `WriteParameter(text string)`
    fn write_parameter(&mut self, text: &str);
    /// `WriteProperty(text string)`
    fn write_property(&mut self, text: &str);
    /// `WriteSymbol(text string, symbol *ast.Symbol)`
    fn write_symbol(&mut self, text: &str, symbol: SymbolId);
    /// `WriteLine()`
    fn write_line(&mut self);
    /// `WriteLineForce(force bool)`
    fn write_line_force(&mut self, force: bool);
    /// `IncreaseIndent()`
    fn increase_indent(&mut self);
    /// `DecreaseIndent()`
    fn decrease_indent(&mut self);
    /// `Clear()`
    fn clear(&mut self);
    /// `String() string`
    fn get_text(&self) -> String;
    /// `RawWrite(s string)`
    fn raw_write(&mut self, s: &str);
    /// `WriteLiteral(s string)`
    fn write_literal(&mut self, s: &str);
    /// `GetTextPos() int`
    fn get_text_pos(&self) -> i32;
    /// `GetLine() int`
    fn get_line(&self) -> i32;
    /// `GetColumn() core.UTF16Offset`
    fn get_column(&self) -> UTF16Offset;
    /// `GetIndent() int`
    fn get_indent(&self) -> i32;
    /// `IsAtStartOfLine() bool`
    fn is_at_start_of_line(&self) -> bool;
    /// `HasTrailingComment() bool`
    fn has_trailing_comment(&self) -> bool;
    /// `HasTrailingWhitespace() bool`
    fn has_trailing_whitespace(&self) -> bool;

    /// `interface{ Grow(n int) }` — capacity hint used by `Printer.Write`.
    /// The default is a no-op; `TextWriter` forwards to its buffer.
    fn grow(&mut self, _n: usize) {}

    /// Enables recovering the concrete writer from a `Box<dyn EmitTextWriter>`.
    /// Writers borrowing another writer (e.g. the semicolon-deferring writer)
    /// are not `'static` and cannot be recovered this way.
    fn into_any(self: Box<Self>) -> Box<dyn std::any::Any>
    where
        Self: 'static + Sized,
    {
        self
    }

    /// Enables inspecting the concrete writer through a `&mut dyn EmitTextWriter`.
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any
    where
        Self: 'static + Sized,
    {
        self
    }
}
