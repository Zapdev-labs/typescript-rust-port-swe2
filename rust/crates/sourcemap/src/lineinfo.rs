// Ported from tsc/internal/sourcemap/lineinfo.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_core::core::EcmaLineStarts;
use tsc_core::text::TextPos;

/// `type ECMALineInfo struct`
///
/// PORT: `lineStarts`/`text` are exposed through accessors instead of Go's
/// package-private field access from source_mapper.go.
#[derive(Clone, Debug)]
pub struct EcmaLineInfo {
    text: String,
    line_starts: EcmaLineStarts,
}

/// `func CreateECMALineInfo(text string, lineStarts core.ECMALineStarts) *ECMALineInfo`
pub fn create_ecma_line_info(text: String, line_starts: EcmaLineStarts) -> EcmaLineInfo {
    EcmaLineInfo { text, line_starts }
}

impl EcmaLineInfo {
    /// `func (li *ECMALineInfo) LineCount() int`
    pub fn line_count(&self) -> i32 {
        self.line_starts.len() as i32
    }

    /// `func (li *ECMALineInfo) LineText(line int) string` — borrows instead of
    /// copying Go's substring.
    pub fn line_text(&self, line: i32) -> &str {
        let pos = self.line_starts[line as usize];
        let end: TextPos = if (line + 1) < self.line_starts.len() as i32 {
            self.line_starts[(line + 1) as usize]
        } else {
            self.text.len() as TextPos
        };
        &self.text[pos as usize..end as usize]
    }

    /// The `text` field — accessed by source_mapper.go's decode loop in Go.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// The `lineStarts` field — accessed by source_mapper.go's decode loop in Go.
    pub fn line_starts(&self) -> &[TextPos] {
        &self.line_starts
    }
}
