// Ported from tsc/internal/printer/singlelinestringwriter.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::SymbolId;
use tsc_core::core::UTF16Offset;
use tsc_stringutil::is_white_space_like;

use crate::emit_text_writer::EmitTextWriter;

/// `type singleLineStringWriter struct`
///
/// PORT: Go pools instances via `sync.Pool`; Rust callers keep a value and
/// `clear()` it between uses, which is equivalent.
#[derive(Default)]
pub struct SingleLineStringWriter {
    builder: String,
    last_written: String,
}

/// `GetSingleLineStringWriter()` — returns a cleared writer. The Go API also
/// returns a release func that returns the writer to a pool; pooling is a
/// Go-runtime optimization that does not apply here.
pub fn get_single_line_string_writer() -> SingleLineStringWriter {
    SingleLineStringWriter::default()
}

impl SingleLineStringWriter {
    fn write_raw(&mut self, s: &str) {
        self.last_written = s.to_string();
        self.builder.push_str(s);
    }
}

impl EmitTextWriter for SingleLineStringWriter {
    fn clear(&mut self) {
        self.last_written.clear();
        self.builder.clear();
    }

    fn decrease_indent(&mut self) {
        // Do Nothing
    }

    fn get_column(&self) -> UTF16Offset {
        0
    }

    fn get_indent(&self) -> i32 {
        0
    }

    fn get_line(&self) -> i32 {
        0
    }

    fn get_text(&self) -> String {
        self.builder.clone()
    }

    fn get_text_pos(&self) -> i32 {
        self.builder.len() as i32
    }

    fn has_trailing_comment(&self) -> bool {
        false
    }

    fn has_trailing_whitespace(&self) -> bool {
        if self.builder.is_empty() {
            return false;
        }
        match self.last_written.chars().next_back() {
            None => false,
            Some(ch) => is_white_space_like(ch),
        }
    }

    fn increase_indent(&mut self) {
        // Do Nothing
    }

    fn is_at_start_of_line(&self) -> bool {
        false
    }

    fn raw_write(&mut self, s: &str) {
        self.write_raw(s);
    }

    fn write(&mut self, s: &str) {
        self.write_raw(s);
    }

    fn write_comment(&mut self, text: &str) {
        self.write_raw(text);
    }

    fn write_keyword(&mut self, text: &str) {
        self.write_raw(text);
    }

    fn write_line(&mut self) {
        self.write_raw(" ");
    }

    fn write_line_force(&mut self, _force: bool) {
        self.write_raw(" ");
    }

    fn write_literal(&mut self, s: &str) {
        self.write_raw(s);
    }

    fn write_operator(&mut self, text: &str) {
        self.write_raw(text);
    }

    fn write_parameter(&mut self, text: &str) {
        self.write_raw(text);
    }

    fn write_property(&mut self, text: &str) {
        self.write_raw(text);
    }

    fn write_punctuation(&mut self, text: &str) {
        self.write_raw(text);
    }

    fn write_space(&mut self, text: &str) {
        self.write_raw(text);
    }

    fn write_string_literal(&mut self, text: &str) {
        self.write_raw(text);
    }

    fn write_symbol(&mut self, text: &str, _symbol: SymbolId) {
        self.write_raw(text);
    }

    fn write_trailing_semicolon(&mut self, text: &str) {
        self.write_raw(text);
    }

    fn into_any(self: Box<Self>) -> Box<dyn std::any::Any> {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}
