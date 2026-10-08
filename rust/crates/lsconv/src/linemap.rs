// Ported from tsc/internal/ls/lsconv/linemap.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_core::text::TextPos;

use crate::runes::{RUNE_SELF, decode_rune_in_string};

/// `type LSPLineStarts []core.TextPos`
pub type LspLineStarts = Vec<TextPos>;

/// `type LSPLineMap struct`
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct LspLineMap {
    pub line_starts: LspLineStarts,
    /// `AsciiOnly` — TODO(jakebailey): collect ascii-only info per line
    pub ascii_only: bool,
}

/// `ComputeLSPLineStarts` — like `core::compute_line_starts`, but only
/// considers `"\n"`, `"\r"`, and `"\r\n"` as line breaks, and reports when
/// the text is ASCII-only.
///
/// PORT: takes `&[u8]` — a Go `string` may hold invalid UTF-8 and this
/// function deliberately decodes it rune-by-rune.
pub fn compute_lsp_line_starts(text: &[u8]) -> LspLineMap {
    let mut line_starts: Vec<TextPos> =
        Vec::with_capacity(memchr::memchr_iter(b'\n', text).count() + 1); // `strings.Count(text, "\n") + 1`
    let mut ascii_only = true;

    let text_len: TextPos = text.len() as TextPos;
    let mut pos: TextPos = 0;
    let mut line_start: TextPos = 0;
    while pos < text_len {
        let b = text[pos as usize];
        if i32::from(b) < RUNE_SELF {
            pos += 1;
            // PORT: Go `switch` with `fallthrough` from `'\r'` to `'\n'`.
            if b == b'\r' {
                if pos < text_len && text[pos as usize] == b'\n' {
                    pos += 1;
                }
                line_starts.push(line_start);
                line_start = pos;
            } else if b == b'\n' {
                line_starts.push(line_start);
                line_start = pos;
            }
        } else {
            let (_, size) = decode_rune_in_string(&text[pos as usize..]);
            pos += size as TextPos;
            ascii_only = false;
        }
    }
    line_starts.push(line_start);

    LspLineMap {
        line_starts,
        ascii_only,
    }
}

impl LspLineMap {
    /// `ComputeIndexOfLineStart` — port of
    /// `computeLineOfPosition(lineStarts: readonly number[], position: number, lowerBound?: number): number`.
    pub fn compute_index_of_line_start(&self, target_pos: TextPos) -> i32 {
        // `slices.BinarySearchFunc` = first index where
        // `line_starts[i] >= target_pos`, plus whether it is equal.
        let mut line_number = self
            .line_starts
            .partition_point(|&start| start < target_pos);
        let found =
            line_number < self.line_starts.len() && self.line_starts[line_number] == target_pos;
        if !found && line_number > 0 {
            // If the actual position was not found, the binary search returns where the target line start would be inserted
            // if the target was in the slice.
            // e.g. if the line starts at [5, 10, 23, 80] and the position requested was 20
            // then the search will return (3, false).
            //
            // We want the index of the previous line start, so we subtract 1.
            line_number -= 1;
        }
        line_number as i32
    }
}
