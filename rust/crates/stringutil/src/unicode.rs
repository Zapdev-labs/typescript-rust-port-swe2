// Ported from tsc/internal/stringutil @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: no tsc/internal counterpart — this module ports the exact pieces of the
// Go standard library that package stringutil relies on: unicode.RangeTable/Is,
// unicode.ToLower/ToUpper/SimpleFold, unicode/utf8, unicode/utf16, and
// strings.EqualFold/ToLower. Data tables marked "(Go unicode/tables.go)" are
// copied verbatim from the Go toolchain source.

/// unicode.ReplacementChar / utf8.RuneError
pub(crate) const REPLACEMENT_CHAR: i32 = 0xFFFD;
/// unicode.MaxASCII
const MAX_ASCII: i32 = 0x7F;
/// unicode.MaxLatin1
const MAX_LATIN1: i32 = 0xFF;

// Range16 represents of a range of 16-bit Unicode code points. The range runs from Lo to Hi
// inclusive and has the specified stride. Lo and Hi must always be >= 1<<16.
// (unicode.Range16 — see the Go source for the full doc comment.)
pub(crate) struct Range16 {
    pub lo: u16,
    pub hi: u16,
    pub stride: u16,
}

// Range32 represents of a range of Unicode code points and is used when one or
// more of the values will not fit in 16 bits. The range runs from Lo to Hi
// inclusive and has the specified stride. Lo and Hi must always be >= 1<<16.
// (unicode.Range32)
pub(crate) struct Range32 {
    pub lo: u32,
    pub hi: u32,
    pub stride: u32,
}

// RangeTable defines a set of Unicode code points by listing the ranges of
// code points to include in the set. The ranges are listed in two slices
// to save space: a slice of 16-bit ranges and a slice of 32-bit ranges.
// The two slices must be in sorted order and non-overlapping.
// Also, R32 should contain only values >= 0x10000 (1<<16).
// (unicode.RangeTable)
pub(crate) struct RangeTable {
    pub r16: &'static [Range16],
    pub r32: &'static [Range32],
    pub latin_offset: usize, // number of entries in R16 with Hi <= MaxLatin1
}

// linearMax is the maximum size table for linear search for non-Latin1 rune.
// Derived by running 'go test -calibrate'.
const LINEAR_MAX: usize = 18;

// is16 reports whether r is in the sorted slice of 16-bit ranges.
fn is16(ranges: &[Range16], r: u16) -> bool {
    if ranges.len() <= LINEAR_MAX || r <= MAX_LATIN1 as u16 {
        for range_ in ranges {
            if r < range_.lo {
                return false;
            }
            if r <= range_.hi {
                return range_.stride == 1 || (r - range_.lo) % range_.stride == 0;
            }
        }
        return false;
    }

    // binary search over ranges
    let mut lo = 0;
    let mut hi = ranges.len();
    while lo < hi {
        let m = lo + (hi - lo) / 2;
        let range_ = &ranges[m];
        if range_.lo <= r && r <= range_.hi {
            return range_.stride == 1 || (r - range_.lo) % range_.stride == 0;
        }
        if r < range_.lo {
            hi = m;
        } else {
            lo = m + 1;
        }
    }
    false
}

// is32 reports whether r is in the sorted slice of 32-bit ranges.
fn is32(ranges: &[Range32], r: u32) -> bool {
    if ranges.len() <= LINEAR_MAX {
        for range_ in ranges {
            if r < range_.lo {
                return false;
            }
            if r <= range_.hi {
                return range_.stride == 1 || (r - range_.lo) % range_.stride == 0;
            }
        }
        return false;
    }

    // binary search over ranges
    let mut lo = 0;
    let mut hi = ranges.len();
    while lo < hi {
        let m = lo + (hi - lo) / 2;
        let range_ = &ranges[m];
        if range_.lo <= r && r <= range_.hi {
            return range_.stride == 1 || (r - range_.lo) % range_.stride == 0;
        }
        if r < range_.lo {
            hi = m;
        } else {
            lo = m + 1;
        }
    }
    false
}

// Is reports whether the rune is in the specified table of ranges.
// (unicode.Is)
pub(crate) fn is(range_tab: &RangeTable, r: i32) -> bool {
    let r16 = range_tab.r16;
    // Compare as uint32 to correctly handle negative runes.
    if !r16.is_empty() && (r as u32) <= r16[r16.len() - 1].hi as u32 {
        return is16(r16, r as u16);
    }
    let r32 = range_tab.r32;
    if !r32.is_empty() && r >= r32[0].lo as i32 {
        return is32(r32, r as u32);
    }
    false
}

// ToLower maps the rune to lower case.
// (unicode.ToLower)
pub(crate) fn to_lower(r: i32) -> i32 {
    if r <= MAX_ASCII {
        if (0x41..=0x5A).contains(&r) {
            return r + 0x20;
        }
        return r;
    }
    to_lower_case_range(r)
}

// ToUpper maps the rune to upper case.
// (unicode.ToUpper)
pub(crate) fn to_upper(r: i32) -> i32 {
    if r <= MAX_ASCII {
        if (0x61..=0x7A).contains(&r) {
            return r - 0x20;
        }
        return r;
    }
    to_upper_case_range(r)
}

// PORT: Go's unicode.ToLower/ToUpper run convertCase over the generated
// CaseRanges table (UnicodeData simple case mappings). We do not vendor
// CaseRanges; the pinned generated special-casing table in js_case_generated.rs
// contains every simple one-rune mapping for Unicode 15.1.0 — verified
// exhaustively identical to Go's CaseRanges results for all runes
// 0..=0x10FFFF except where a *full* mapping is multi-rune (CaseRanges has no
// multi-rune entries). Those reduce to their simple mappings here:
//   - lower: U+0130 is the only rune with a multi-rune full lowercase
//     ("i\u{0307}"); its simple lowercase is 'i'.
//   - upper: multi-rune full uppercase maps to self, except the Greek
//     iota-subscript composites in SIMPLE_UPPER, whose simple uppercase is the
//     corresponding titlecase-like form (U+1F80..1F87 → U+1F88..1F8F, etc.).

fn to_lower_case_range(r: i32) -> i32 {
    match crate::js_case_generated::special_casing_mapping(r) {
        Some(mapping) => {
            let mut chars = mapping.lower.chars();
            match (chars.next(), chars.next()) {
                (Some(c), None) => c as i32,
                _ => {
                    debug_assert_eq!(r, 0x130, "only U+0130 has a multi-rune lower");
                    0x69 // 'i'
                }
            }
        }
        None => r,
    }
}

// SIMPLE_UPPER — the CaseRanges simple uppercase for runes whose full
// uppercase is multi-rune (verified vs Go's unicode package).
#[rustfmt::skip]
const SIMPLE_UPPER: &[(u32, u32)] = &[
    (0x1F80, 0x1F88), (0x1F81, 0x1F89), (0x1F82, 0x1F8A), (0x1F83, 0x1F8B),
    (0x1F84, 0x1F8C), (0x1F85, 0x1F8D), (0x1F86, 0x1F8E), (0x1F87, 0x1F8F),
    (0x1F90, 0x1F98), (0x1F91, 0x1F99), (0x1F92, 0x1F9A), (0x1F93, 0x1F9B),
    (0x1F94, 0x1F9C), (0x1F95, 0x1F9D), (0x1F96, 0x1F9E), (0x1F97, 0x1F9F),
    (0x1FA0, 0x1FA8), (0x1FA1, 0x1FA9), (0x1FA2, 0x1FAA), (0x1FA3, 0x1FAB),
    (0x1FA4, 0x1FAC), (0x1FA5, 0x1FAD), (0x1FA6, 0x1FAE), (0x1FA7, 0x1FAF),
    (0x1FB3, 0x1FBC), (0x1FC3, 0x1FCC), (0x1FF3, 0x1FFC),
];

fn to_upper_case_range(r: i32) -> i32 {
    match crate::js_case_generated::special_casing_mapping(r) {
        Some(mapping) => {
            let mut chars = mapping.upper.chars();
            match (chars.next(), chars.next()) {
                (Some(c), None) => c as i32,
                _ => SIMPLE_UPPER
                    .binary_search_by_key(&(r as u32), |&(from, _)| from)
                    .map(|idx| SIMPLE_UPPER[idx].1 as i32)
                    .unwrap_or(r),
            }
        }
        None => r,
    }
}

// SimpleFold iterates over Unicode code points equivalent under
// the Unicode-defined simple case folding. Among the code points
// equivalent to rune (including rune itself), SimpleFold returns the
// smallest rune > r if one exists, or else the smallest rune >= 0.
// If r is not a valid Unicode code point, SimpleFold(r) returns r.
//
// For example:
//
//	SimpleFold('A') = 'a'
//	SimpleFold('a') = 'A'
//
//	SimpleFold('K') = 'k'
//	SimpleFold('k') = '\u{212A}' (Kelvin symbol, K)
//	SimpleFold('\u{212A}') = 'K'
//
//	SimpleFold('1') = '1'
//
//	SimpleFold(-2) = -2
//
// (unicode.SimpleFold)
pub(crate) fn simple_fold(r: i32) -> i32 {
    if !(0..=utf8::MAX_RUNE).contains(&r) {
        return r;
    }

    if (r as usize) < ASCII_FOLD.len() {
        return ASCII_FOLD[r as usize];
    }

    // Consult caseOrbit table for special cases.
    if let Ok(m) = CASE_ORBIT.binary_search_by_key(&r, |&(from, _)| from) {
        return CASE_ORBIT[m].1;
    }

    // No folding specified. This is a one- or two-element
    // equivalence class containing rune and ToLower(rune)
    // and ToUpper(rune) if they are different from rune.
    // (Go consults CaseRanges directly; to_lower/to_upper are the
    // same mappings — see the PORT comment at to_lower.)
    let l = to_lower(r);
    if l != r {
        return l;
    }
    to_upper(r)
}

// asciiFold (Go unicode/tables.go)
#[rustfmt::skip]
const ASCII_FOLD: [i32; 0x80] = [
    0x0000, 0x0001, 0x0002, 0x0003, 0x0004, 0x0005, 0x0006, 0x0007,
    0x0008, 0x0009, 0x000A, 0x000B, 0x000C, 0x000D, 0x000E, 0x000F,
    0x0010, 0x0011, 0x0012, 0x0013, 0x0014, 0x0015, 0x0016, 0x0017,
    0x0018, 0x0019, 0x001A, 0x001B, 0x001C, 0x001D, 0x001E, 0x001F,
    0x0020, 0x0021, 0x0022, 0x0023, 0x0024, 0x0025, 0x0026, 0x0027,
    0x0028, 0x0029, 0x002A, 0x002B, 0x002C, 0x002D, 0x002E, 0x002F,
    0x0030, 0x0031, 0x0032, 0x0033, 0x0034, 0x0035, 0x0036, 0x0037,
    0x0038, 0x0039, 0x003A, 0x003B, 0x003C, 0x003D, 0x003E, 0x003F,
    0x0040, 0x0061, 0x0062, 0x0063, 0x0064, 0x0065, 0x0066, 0x0067,
    0x0068, 0x0069, 0x006A, 0x006B, 0x006C, 0x006D, 0x006E, 0x006F,
    0x0070, 0x0071, 0x0072, 0x0073, 0x0074, 0x0075, 0x0076, 0x0077,
    0x0078, 0x0079, 0x007A, 0x005B, 0x005C, 0x005D, 0x005E, 0x005F,
    0x0060, 0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0x0046, 0x0047,
    0x0048, 0x0049, 0x004A, 0x212A, 0x004C, 0x004D, 0x004E, 0x004F,
    0x0050, 0x0051, 0x0052, 0x017F, 0x0054, 0x0055, 0x0056, 0x0057,
    0x0058, 0x0059, 0x005A, 0x007B, 0x007C, 0x007D, 0x007E, 0x007F,
];

// caseOrbit (Go unicode/tables.go); foldPair{From, To}
#[rustfmt::skip]
const CASE_ORBIT: &[(i32, i32)] = &[
    (0x004B, 0x006B), (0x0053, 0x0073), (0x006B, 0x212A), (0x0073, 0x017F),
    (0x00B5, 0x039C), (0x00C5, 0x00E5), (0x00DF, 0x1E9E), (0x00E5, 0x212B),
    (0x0130, 0x0130), (0x0131, 0x0131), (0x017F, 0x0053), (0x01C4, 0x01C5),
    (0x01C5, 0x01C6), (0x01C6, 0x01C4), (0x01C7, 0x01C8), (0x01C8, 0x01C9),
    (0x01C9, 0x01C7), (0x01CA, 0x01CB), (0x01CB, 0x01CC), (0x01CC, 0x01CA),
    (0x01F1, 0x01F2), (0x01F2, 0x01F3), (0x01F3, 0x01F1), (0x0345, 0x0399),
    (0x0392, 0x03B2), (0x0395, 0x03B5), (0x0398, 0x03B8), (0x0399, 0x03B9),
    (0x039A, 0x03BA), (0x039C, 0x03BC), (0x03A0, 0x03C0), (0x03A1, 0x03C1),
    (0x03A3, 0x03C2), (0x03A6, 0x03C6), (0x03A9, 0x03C9), (0x03B2, 0x03D0),
    (0x03B5, 0x03F5), (0x03B8, 0x03D1), (0x03B9, 0x1FBE), (0x03BA, 0x03F0),
    (0x03BC, 0x00B5), (0x03C0, 0x03D6), (0x03C1, 0x03F1), (0x03C2, 0x03C3),
    (0x03C3, 0x03A3), (0x03C6, 0x03D5), (0x03C9, 0x2126), (0x03D0, 0x0392),
    (0x03D1, 0x03F4), (0x03D5, 0x03A6), (0x03D6, 0x03A0), (0x03F0, 0x039A),
    (0x03F1, 0x03A1), (0x03F4, 0x0398), (0x03F5, 0x0395), (0x0412, 0x0432),
    (0x0414, 0x0434), (0x041E, 0x043E), (0x0421, 0x0441), (0x0422, 0x0442),
    (0x042A, 0x044A), (0x0432, 0x1C80), (0x0434, 0x1C81), (0x043E, 0x1C82),
    (0x0441, 0x1C83), (0x0442, 0x1C84), (0x044A, 0x1C86), (0x0462, 0x0463),
    (0x0463, 0x1C87), (0x1C80, 0x0412), (0x1C81, 0x0414), (0x1C82, 0x041E),
    (0x1C83, 0x0421), (0x1C84, 0x1C85), (0x1C85, 0x0422), (0x1C86, 0x042A),
    (0x1C87, 0x0462), (0x1C88, 0xA64A), (0x1E60, 0x1E61), (0x1E61, 0x1E9B),
    (0x1E9B, 0x1E60), (0x1E9E, 0x00DF), (0x1FBE, 0x0345), (0x2126, 0x03A9),
    (0x212A, 0x004B), (0x212B, 0x00C5), (0xA64A, 0xA64B), (0xA64B, 0x1C88),
];

// EqualFold reports whether s and t, interpreted as UTF-8 strings,
// are equal under simple Unicode case-folding, which is a more general
// form of case-insensitivity.
//
// (strings.EqualFold)
pub(crate) fn equal_fold(s: &[u8], t: &[u8]) -> bool {
    // ASCII fast path
    let mut i = 0;
    let n = s.len().min(t.len());
    let mut has_unicode = false;
    while i < n {
        let sr = s[i];
        let tr = t[i];
        if sr | tr >= utf8::RUNE_SELF as u8 {
            has_unicode = true;
            break;
        }

        // Easy case.
        if tr == sr {
            i += 1;
            continue;
        }

        // Make sr < tr to simplify what follows.
        let (sr, tr) = if tr < sr { (tr, sr) } else { (sr, tr) };

        // ASCII only, sr/tr must be upper/lower case
        if (0x41..=0x5A).contains(&sr) && tr == sr + (0x61 - 0x41) {
            i += 1;
            continue;
        }
        return false;
    }
    if !has_unicode {
        // Check if we've exhausted both strings.
        return s.len() == t.len();
    }

    // hasUnicode:
    let mut s = &s[i..];
    let mut t = &t[i..];
    while !s.is_empty() {
        let (sr, ssize) = utf8::decode_rune_in_string(s);
        s = &s[ssize..];

        // If t is exhausted the strings are not equal.
        if t.is_empty() {
            return false;
        }

        // Extract first rune from second string.
        let (tr, tsize) = utf8::decode_rune_in_string(t);
        t = &t[tsize..];

        // If they match, keep going; if not, return false.

        // Easy case.
        if tr == sr {
            continue;
        }

        // Make sr < tr to simplify what follows.
        let (sr, tr) = if tr < sr { (tr, sr) } else { (sr, tr) };

        // Fast check for ASCII.
        if tr < utf8::RUNE_SELF {
            // ASCII only, sr/tr must be upper/lower case
            if (0x41..=0x5A).contains(&sr) && tr == sr + (0x61 - 0x41) {
                continue;
            }
            return false;
        }

        // General case. SimpleFold(x) returns the next equivalent rune > x
        // or wraps around to smaller values.
        let mut r = simple_fold(sr);
        while r != sr && r < tr {
            r = simple_fold(r);
        }
        if r == tr {
            continue;
        }
        return false;
    }

    // First string is empty, so check if the second one is also empty.
    t.is_empty()
}

// ToLower returns a copy of the string s with all Unicode letters mapped to
// their lower case.
//
// (strings.ToLower; produces the mapped bytes rather than a copy only when
// something changed — the content is identical either way.)
pub(crate) fn strings_to_lower(s: &[u8]) -> Vec<u8> {
    let mut is_ascii = true;
    let mut has_upper = false;
    for i in 0..s.len() {
        let c = s[i];
        if c >= utf8::RUNE_SELF as u8 {
            is_ascii = false;
            break;
        }
        has_upper = has_upper || (0x41 <= c && c <= 0x5A);
    }

    if is_ascii {
        // optimize for ASCII-only strings.
        if !has_upper {
            return s.to_vec();
        }
        let mut b = s.to_vec();
        for c in b.iter_mut() {
            if (0x41..=0x5A).contains(c) {
                *c += 0x61 - 0x41;
            }
        }
        return b;
    }

    // Map(unicode.ToLower, s)
    let mut b = Vec::with_capacity(s.len());
    let mut i = 0;
    while i < s.len() {
        let (c, size) = utf8::decode_rune_in_string(&s[i..]);
        let r = to_lower(c);
        if r == c && !(c == utf8::RUNE_ERROR && size == 1) {
            // Unchanged rune — copy the original bytes. A genuine encoded
            // U+FFFD (size 3) is copied too; an invalid byte (RuneError,
            // size 1) is replaced by WriteRune(FFFD) as in strings.Map.
            b.extend_from_slice(&s[i..i + size]);
        } else {
            utf8::append_rune(&mut b, r);
        }
        i += size;
    }
    b
}

pub(crate) mod utf16 {
    // unicode/utf16 — UTF-16 sequence encoding/decoding.

    use super::utf8::{MAX_RUNE, RUNE_ERROR};

    // 0xd800-0xdc00 encodes the high 10 bits of a pair.
    // 0xdc00-0xe000 encodes the low 10 bits of a pair.
    // the value is those 20 bits plus 0x10000.
    const SURR1: i32 = 0xd800;
    const SURR2: i32 = 0xdc00;
    const SURR3: i32 = 0xe000;

    const SURR_SELF: i32 = 0x10000;

    // IsSurrogate reports whether the specified Unicode code point
    // can appear in a surrogate pair.
    pub(crate) fn is_surrogate(r: i32) -> bool {
        (SURR1..SURR3).contains(&r)
    }

    // DecodeRune returns the UTF-16 decoding of a surrogate pair.
    // If the pair is not a valid UTF-16 surrogate pair, DecodeRune returns
    // the Unicode replacement code point U+FFFD.
    pub(crate) fn decode_rune(r1: i32, r2: i32) -> i32 {
        if (SURR1..SURR2).contains(&r1) && (SURR2..SURR3).contains(&r2) {
            return (r1 - SURR1) << 10 | (r2 - SURR2) + SURR_SELF;
        }
        RUNE_ERROR
    }

    // EncodeRune returns the UTF-16 surrogate pair r1, r2 for the given rune.
    // If the rune is not a valid Unicode code point or does not need encoding,
    // EncodeRune returns U+FFFD, U+FFFD.
    pub(crate) fn encode_rune(r: i32) -> (i32, i32) {
        if !(SURR_SELF..=MAX_RUNE).contains(&r) {
            return (RUNE_ERROR, RUNE_ERROR);
        }
        let r = r - SURR_SELF;
        (SURR1 + ((r >> 10) & 0x3ff), SURR2 + (r & 0x3ff))
    }
}

pub(crate) mod utf8 {
    // unicode/utf8 — UTF-8 rune encoding/decoding.

    pub(crate) const RUNE_ERROR: i32 = 0xFFFD; // the "error" Rune or "Unicode replacement character"
    pub(crate) const RUNE_SELF: i32 = 0x80; // characters below RuneSelf are represented as themselves in a single byte.
    pub(crate) const MAX_RUNE: i32 = 0x10FFFF; // Maximum valid Unicode code point.
    pub(crate) const UTF_MAX: usize = 4; // maximum number of bytes of a UTF-8 encoded Unicode character.

    const SURROGATE_MIN: u32 = 0xD800;
    const SURROGATE_MAX: u32 = 0xDFFF;

    const TX: u8 = 0b10000000;
    const T2: u8 = 0b11000000;
    const T3: u8 = 0b11100000;
    const T4: u8 = 0b11110000;

    const MASKX: u8 = 0b00111111;
    const MASK2: u8 = 0b00011111;
    const MASK3: u8 = 0b00001111;
    const MASK4: u8 = 0b00000111;

    const RUNE1_MAX: u32 = (1 << 7) - 1;
    const RUNE2_MAX: u32 = (1 << 11) - 1;
    const RUNE3_MAX: u32 = (1 << 16) - 1;

    // The default lowest and highest continuation byte.
    const LOCB: u8 = 0b10000000;
    const HICB: u8 = 0b10111111;

    // These names of these constants are chosen to give nice alignment in the
    // table below. The first nibble is an index into acceptRanges or F for
    // special one-byte cases. The second nibble is the Rune length or the
    // Status for the special one-byte case.
    const XX: u8 = 0xF1; // invalid: size 1
    const AS: u8 = 0xF0; // ASCII: size 1
    const S1: u8 = 0x02; // accept 0, size 2
    const S2: u8 = 0x13; // accept 1, size 3
    const S3: u8 = 0x03; // accept 0, size 3
    const S4: u8 = 0x23; // accept 2, size 3
    const S5: u8 = 0x34; // accept 3, size 4
    const S6: u8 = 0x04; // accept 0, size 4
    const S7: u8 = 0x44; // accept 4, size 4

    const RUNE_ERROR_BYTE0: u8 = T3 | (RUNE_ERROR >> 12) as u8;
    const RUNE_ERROR_BYTE1: u8 = TX | ((RUNE_ERROR >> 6) as u8) & MASKX;
    const RUNE_ERROR_BYTE2: u8 = TX | (RUNE_ERROR as u8) & MASKX;

    // first is information about the first byte in a UTF-8 sequence.
    #[rustfmt::skip]
    const FIRST: [u8; 256] = [
        //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
        AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, // 0x00-0x0F
        AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, // 0x10-0x1F
        AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, // 0x20-0x2F
        AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, // 0x30-0x3F
        AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, // 0x40-0x4F
        AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, // 0x50-0x5F
        AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, // 0x60-0x6F
        AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, AS, // 0x70-0x7F
        //   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
        XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, // 0x80-0x8F
        XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, // 0x90-0x9F
        XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, // 0xA0-0xAF
        XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, // 0xB0-0xBF
        XX, XX, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, // 0xC0-0xCF
        S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, S1, // 0xD0-0xDF
        S2, S3, S3, S3, S3, S3, S3, S3, S3, S3, S3, S3, S3, S4, S3, S3, // 0xE0-0xEF
        S5, S6, S6, S6, S7, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, XX, // 0xF0-0xFF
    ];

    // acceptRange gives the range of valid values for the second byte in a UTF-8
    // sequence.
    type AcceptRange = (u8, u8);

    // acceptRanges has size 16 to avoid bounds checks in the code that uses it.
    #[rustfmt::skip]
    const ACCEPT_RANGES: [AcceptRange; 16] = [
        (LOCB, HICB),
        (0xA0, HICB),
        (LOCB, 0x9F),
        (0x90, HICB),
        (LOCB, 0x8F),
        (0x00, 0x00),
        (0x00, 0x00),
        (0x00, 0x00),
        (0x00, 0x00),
        (0x00, 0x00),
        (0x00, 0x00),
        (0x00, 0x00),
        (0x00, 0x00),
        (0x00, 0x00),
        (0x00, 0x00),
        (0x00, 0x00),
    ];

    // DecodeRuneInString is like DecodeRune but its input is a string. If s is
    // empty it returns (RuneError, 0). Otherwise, if the encoding is invalid, it
    // returns (RuneError, 1). Both are impossible results for correct, non-empty
    // UTF-8.
    //
    // An encoding is invalid if it is incorrect UTF-8, encodes a rune that is
    // out of range, or is not the shortest possible UTF-8 encoding for the
    // value. No other validation is performed.
    pub(crate) fn decode_rune_in_string(s: &[u8]) -> (i32, usize) {
        // Inlineable fast path for ASCII characters; see #48195.
        if !s.is_empty() && s[0] < RUNE_SELF as u8 {
            (s[0] as i32, 1)
        } else {
            decode_rune_in_string_slow(s)
        }
    }

    fn decode_rune_in_string_slow(s: &[u8]) -> (i32, usize) {
        let n = s.len();
        if n < 1 {
            return (RUNE_ERROR, 0);
        }
        let s0 = s[0];
        let x = FIRST[s0 as usize];
        if x >= AS {
            // The following code simulates an additional check for x == XX and
            // handling the ASCII and invalid cases accordingly. This mask-and-or
            // approach prevents an additional branch.
            let mask = (x as i32) << 31 >> 31; // Create 0x0000 or 0xFFFF.
            return ((s0 as i32) & !mask | RUNE_ERROR & mask, 1);
        }
        let sz = (x & 7) as usize;
        let accept = ACCEPT_RANGES[(x >> 4) as usize];
        if n < sz {
            return (RUNE_ERROR, 1);
        }
        let s1 = s[1];
        if s1 < accept.0 || accept.1 < s1 {
            return (RUNE_ERROR, 1);
        }
        if sz <= 2 {
            // <= instead of == to help the compiler eliminate some bounds checks
            return (((s0 & MASK2) as i32) << 6 | (s1 & MASKX) as i32, 2);
        }
        let s2 = s[2];
        if !(LOCB..=HICB).contains(&s2) {
            return (RUNE_ERROR, 1);
        }
        if sz <= 3 {
            return (
                ((s0 & MASK3) as i32) << 12 | ((s1 & MASKX) as i32) << 6 | (s2 & MASKX) as i32,
                3,
            );
        }
        let s3 = s[3];
        if !(LOCB..=HICB).contains(&s3) {
            return (RUNE_ERROR, 1);
        }
        (
            ((s0 & MASK4) as i32) << 18
                | ((s1 & MASKX) as i32) << 12
                | ((s2 & MASKX) as i32) << 6
                | (s3 & MASKX) as i32,
            4,
        )
    }

    // DecodeLastRuneInString is like DecodeLastRune but its input is a string. If
    // s is empty it returns (RuneError, 0). Otherwise, if the encoding is invalid, it
    // returns (RuneError, 1). Both are impossible results for correct, non-empty
    // UTF-8.
    //
    // An encoding is invalid if it is incorrect UTF-8, encodes a rune that is
    // out of range, or is not the shortest possible UTF-8 encoding for the
    // value. No other validation is performed.
    pub(crate) fn decode_last_rune_in_string(s: &[u8]) -> (i32, usize) {
        let end = s.len();
        if end == 0 {
            return (RUNE_ERROR, 0);
        }
        let mut start = (end - 1) as isize;
        let r = s[start as usize] as i32;
        if r < RUNE_SELF {
            return (r, 1);
        }
        // guard against O(n^2) behavior when traversing
        // backwards through strings with long sequences of
        // invalid UTF-8.
        let lim = end.saturating_sub(UTF_MAX) as isize;
        start -= 1;
        while start >= lim {
            if rune_start(s[start as usize]) {
                break;
            }
            start -= 1;
        }
        if start < 0 {
            start = 0;
        }
        let start = start as usize;
        let (r, size) = decode_rune_in_string(&s[start..end]);
        if start + size != end {
            return (RUNE_ERROR, 1);
        }
        (r, size)
    }

    // RuneStart reports whether the byte could be the first byte of an encoded,
    // possibly invalid rune. Second and subsequent bytes always have the top two
    // bits set to 10.
    fn rune_start(b: u8) -> bool {
        b & 0xC0 != 0x80
    }

    // AppendRune appends the UTF-8 encoding of r to the end of p and
    // returns the extended buffer. If the rune is out of range,
    // it appends the encoding of RuneError.
    // (utf8.AppendRune / strings.Builder.WriteRune)
    pub(crate) fn append_rune(p: &mut Vec<u8>, r: i32) {
        // This function is inlineable for fast handling of ASCII.
        if (r as u32) <= RUNE1_MAX {
            p.push(r as u8);
            return;
        }
        append_rune_non_ascii(p, r);
    }

    fn append_rune_non_ascii(p: &mut Vec<u8>, r: i32) {
        // Negative values are erroneous. Making it unsigned addresses the problem.
        let i = r as u32;
        if i <= RUNE2_MAX {
            p.extend_from_slice(&[T2 | (r >> 6) as u8, TX | (r as u8) & MASKX]);
        } else if i < SURROGATE_MIN || (SURROGATE_MAX < i && i <= RUNE3_MAX) {
            p.extend_from_slice(&[
                T3 | (r >> 12) as u8,
                TX | ((r >> 6) as u8) & MASKX,
                TX | (r as u8) & MASKX,
            ]);
        } else if i > RUNE3_MAX && i <= MAX_RUNE as u32 {
            p.extend_from_slice(&[
                T4 | (r >> 18) as u8,
                TX | ((r >> 12) as u8) & MASKX,
                TX | ((r >> 6) as u8) & MASKX,
                TX | (r as u8) & MASKX,
            ]);
        } else {
            p.extend_from_slice(&[RUNE_ERROR_BYTE0, RUNE_ERROR_BYTE1, RUNE_ERROR_BYTE2]);
        }
    }
}
