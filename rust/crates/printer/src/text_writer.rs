// Ported from tsc/internal/printer/textwriter.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::SymbolId;
use tsc_core::core::{self, UTF16Offset};
use tsc_stringutil::is_white_space_like;

use crate::emit_text_writer::EmitTextWriter;

/// `type textWriter struct`
pub struct TextWriter {
    new_line: String,
    indent_size: i32,
    builder: String,
    last_written: String,
    indent: i32,
    line_start: bool,
    line_count: i32,
    line_pos: usize,
    has_trailing_comment_state: bool,
}

impl TextWriter {
    /// `NewTextWriter(newLine, indentSize)` — returns the concrete writer.
    /// (Go returns `EmitTextWriter`.)
    pub fn new(new_line: &str, indent_size: i32) -> TextWriter {
        let indent_size = if indent_size <= 0 { 4 } else { indent_size };
        let mut w = TextWriter {
            new_line: new_line.to_string(),
            indent_size,
            builder: String::new(),
            last_written: String::new(),
            indent: 0,
            line_start: false,
            line_count: 0,
            line_pos: 0,
            has_trailing_comment_state: false,
        };
        w.clear();
        w
    }

    /// `(w *textWriter) updateLineCountAndPosFor(s)`
    fn update_line_count_and_pos_for(&mut self, s: &str) {
        let mut count = 0i32;
        let mut last_line_start = 0i32;

        for line_start in core::compute_ecma_line_starts_seq(s) {
            count += 1;
            last_line_start = line_start;
        }

        if count > 1 {
            self.line_count += count - 1;
            let cur_len = self.builder.len();
            self.line_pos = cur_len - s.len() + last_line_start as usize;
            self.line_start = (self.line_pos as i64 - cur_len as i64) == 0;
            return;
        }
        self.line_start = false;
    }

    /// `(w *textWriter) writeText(s)`
    fn write_text(&mut self, s: &str) {
        if !s.is_empty() {
            if self.line_start {
                self.builder
                    .push_str(&get_indent_string(self.indent, self.indent_size));
                self.line_start = false;
            }
            self.builder.push_str(s);
            self.last_written = s.to_string();
            self.update_line_count_and_pos_for(s);
        }
    }

    /// `(w *textWriter) writeLineRaw()`
    fn write_line_raw(&mut self) {
        self.builder.push_str(&self.new_line.clone());
        self.last_written = self.new_line.clone();
        self.line_count += 1;
        self.line_pos = self.builder.len();
        self.line_start = true;
        self.has_trailing_comment_state = false;
    }
}

/// `defaultIndentSize` — the default indent size (4 spaces) used when no
/// specific indent size is configured.
pub const DEFAULT_INDENT_SIZE: i32 = 4;

/// `GetDefaultIndentSize()`
pub fn get_default_indent_size() -> i32 {
    DEFAULT_INDENT_SIZE
}

/// `getIndentString(indent, indentSize)`
pub fn get_indent_string(indent: i32, indent_size: i32) -> String {
    if indent == 0 {
        return String::new();
    }
    // TODO: This is cached in tsc - should it be cached here?
    " ".repeat((indent * indent_size) as usize)
}

impl EmitTextWriter for TextWriter {
    fn clear(&mut self) {
        let new_line = std::mem::take(&mut self.new_line);
        let indent_size = self.indent_size;
        *self = TextWriter {
            new_line,
            indent_size,
            builder: String::new(),
            last_written: String::new(),
            indent: 0,
            line_start: true,
            line_count: 0,
            line_pos: 0,
            has_trailing_comment_state: false,
        };
    }

    fn grow(&mut self, n: usize) {
        self.builder.reserve(n);
    }

    fn decrease_indent(&mut self) {
        self.indent -= 1;
    }

    /// `GetColumn` — column position measured in UTF-16 code units
    /// for source map compatibility.
    fn get_column(&self) -> UTF16Offset {
        if self.line_start {
            return self.indent * self.indent_size;
        }
        // Count UTF-16 code units from the last line start.
        // For ASCII-only output (the common case), this equals the byte count.
        core::utf16_len(&self.builder[self.line_pos..])
    }

    fn get_indent(&self) -> i32 {
        self.indent
    }

    fn get_line(&self) -> i32 {
        self.line_count
    }

    fn get_text(&self) -> String {
        self.builder.clone()
    }

    fn get_text_pos(&self) -> i32 {
        self.builder.len() as i32
    }

    fn has_trailing_comment(&self) -> bool {
        self.has_trailing_comment_state
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
        self.indent += 1;
    }

    fn is_at_start_of_line(&self) -> bool {
        self.line_start
    }

    fn raw_write(&mut self, s: &str) {
        if !s.is_empty() {
            self.builder.push_str(s);
            self.last_written = s.to_string();
            self.has_trailing_comment_state = false;
        }
        self.update_line_count_and_pos_for(s);
    }

    fn write(&mut self, s: &str) {
        if !s.is_empty() {
            self.has_trailing_comment_state = false;
        }
        self.write_text(s);
    }

    fn write_comment(&mut self, text: &str) {
        if !text.is_empty() {
            self.has_trailing_comment_state = true;
        }
        self.write_text(text);
    }

    fn write_keyword(&mut self, text: &str) {
        self.write(text);
    }

    fn write_line(&mut self) {
        if !self.line_start {
            self.write_line_raw();
        }
    }

    fn write_line_force(&mut self, force: bool) {
        if !self.line_start || force {
            self.write_line_raw();
        }
    }

    fn write_literal(&mut self, s: &str) {
        self.write(s);
    }

    fn write_operator(&mut self, text: &str) {
        self.write(text);
    }

    fn write_parameter(&mut self, text: &str) {
        self.write(text);
    }

    fn write_property(&mut self, text: &str) {
        self.write(text);
    }

    fn write_punctuation(&mut self, text: &str) {
        self.write(text);
    }

    fn write_space(&mut self, text: &str) {
        self.write(text);
    }

    fn write_string_literal(&mut self, text: &str) {
        self.write(text);
    }

    fn write_symbol(&mut self, text: &str, _symbol: SymbolId) {
        self.write(text);
    }

    fn write_trailing_semicolon(&mut self, text: &str) {
        self.write(text);
    }

    fn into_any(self: Box<Self>) -> Box<dyn std::any::Any> {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}
