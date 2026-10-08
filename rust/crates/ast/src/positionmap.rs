// Ported from tsc/internal/ast/positionmap.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Go `int` offsets become `usize` (offsets are non-negative byte/code-unit
// positions; `usize` is the natural index type and matches Go's 64-bit `int`
// range on 64-bit targets). `text` is `&[u8]` rather than `&str` because JS
// source text can contain the lone-surrogate CESU-8/WTF-8 sentinel written by
// `stringutil.EncodeJSStringRune`, which is not valid UTF-8.

use tsc_stringutil::decode_js_string_rune;

/// `PositionMap` provides bidirectional mapping between UTF-8 byte offsets (used by Go)
/// and UTF-16 code unit offsets (used by JavaScript/TypeScript).
///
/// For ASCII-only text, the two are identical. For text containing non-ASCII characters,
/// the offsets diverge because multi-byte UTF-8 sequences map to different numbers of
/// UTF-16 code units:
///   - U+0000..U+007F:   1 byte  in UTF-8, 1 code unit  in UTF-16
///   - U+0080..U+07FF:   2 bytes in UTF-8, 1 code unit  in UTF-16
///   - U+0800..U+FFFF:   3 bytes in UTF-8, 1 code unit  in UTF-16
///   - U+10000..U+10FFFF: 4 bytes in UTF-8, 2 code units in UTF-16 (surrogate pair)
#[derive(Clone, Default)]
pub struct PositionMap {
    /// `asciiOnly` is true if the text contains only ASCII characters,
    /// meaning UTF-8 byte offsets and UTF-16 code unit offsets are identical.
    ascii_only: bool,
    /// For each multi-byte character, we store:
    ///   - the UTF-8 byte offset of the character
    ///   - the cumulative delta (utf8Offset - utf16Offset) at that character
    /// This allows O(log n) conversion in either direction.
    ///
    /// `entries[i].utf8_pos` is the byte offset of the i-th multi-byte character.
    /// `entries[i].delta` is the total (utf8 - utf16) difference accumulated
    /// through and including the i-th multi-byte character.
    entries: Vec<PositionMapEntry>,
}

#[derive(Clone, Copy, Default)]
struct PositionMapEntry {
    utf8_pos: usize, // UTF-8 byte offset AFTER this multi-byte character
    delta: usize,    // cumulative (utf8 - utf16) offset difference after this character
}

/// `ComputePositionMap` builds a PositionMap for the given text.
pub fn compute_position_map(text: &[u8]) -> PositionMap {
    let mut pm = PositionMap::default();
    let mut delta = 0;
    let mut i = 0;
    while i < text.len() {
        let b = text[i];
        if b < 0x80 {
            // utf8.RuneSelf
            i += 1;
            continue;
        }
        let (r, size) = decode_js_string_rune(&text[i..]);
        let utf16_size = if r >= 0x10000 { 2 } else { 1 };
        delta += size - utf16_size;
        pm.entries.push(PositionMapEntry {
            utf8_pos: i + size,
            delta,
        });
        i += size;
    }
    pm.ascii_only = pm.entries.is_empty();
    pm
}

impl PositionMap {
    /// `IsAsciiOnly` returns true if the text is ASCII-only,
    /// meaning UTF-8 and UTF-16 offsets are identical.
    pub fn is_ascii_only(&self) -> bool {
        self.ascii_only
    }

    /// `UTF8ToUTF16` converts a UTF-8 byte offset to a UTF-16 code unit offset.
    pub fn utf8_to_utf16(&self, utf8_offset: usize) -> usize {
        if self.ascii_only {
            return utf8_offset;
        }
        // Binary search: find the last entry where utf8Pos <= utf8Offset
        let (mut lo, mut hi) = (0, self.entries.len());
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            if self.entries[mid].utf8_pos <= utf8_offset {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo == 0 {
            // Before any multi-byte character
            return utf8_offset;
        }
        utf8_offset - self.entries[lo - 1].delta
    }

    /// `UTF16ToUTF8` converts a UTF-16 code unit offset to a UTF-8 byte offset.
    pub fn utf16_to_utf8(&self, utf16_offset: usize) -> usize {
        if self.ascii_only {
            return utf16_offset;
        }
        // We need the last entry where (utf8Pos - delta) <= utf16Offset.
        // (utf8Pos - delta) is the UTF-16 offset of that entry's character.
        let (mut lo, mut hi) = (0, self.entries.len());
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let utf16_pos = self.entries[mid].utf8_pos - self.entries[mid].delta;
            if utf16_pos <= utf16_offset {
                lo = mid + 1;
            } else {
                hi = mid;
            }
        }
        if lo == 0 {
            return utf16_offset;
        }
        utf16_offset + self.entries[lo - 1].delta
    }
}

