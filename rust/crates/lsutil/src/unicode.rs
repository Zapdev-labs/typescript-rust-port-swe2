// PORT: no tsc/internal counterpart — this module ports the exact pieces of
// the Go standard library that package lsutil relies on:
// unicode.RangeTable/Is, unicode.IsUpper, unicode.ToUpper/ToLower (incl.
// `to`/`convertCase` over `unicode.CaseRanges`), unicode.Is(unicode.Mn),
// strings.ToLower, and (via unicode-normalization) unicode/norm.NFD.
// The category tables in `unicode_categories_generated.rs` and the case
// mappings in `case_ranges_generated.rs` are generated verbatim from the Go
// toolchain source (unicode/tables.go, unicode/casetables.go).
//
// tsc-stringutil has the same private Go-stdlib port (`pub(crate)`); rather
// than widening that crate's surface, lsutil keeps its own copy because only
// lsutil needs Mn categories and the CaseRanges-backed simple case mapping.

use crate::case_ranges_generated::CASE_RANGES;
use crate::unicode_categories_generated::{MN, UPPER};

/// unicode.MaxASCII
const MAX_ASCII: i32 = 0x7F;
/// unicode.MaxLatin1
const MAX_LATIN1: i32 = 0xFF;
/// unicode.MaxRune
const MAX_RUNE: i32 = 0x10FFFF;
/// unicode.ReplacementChar
#[allow(dead_code)]
pub(crate) const REPLACEMENT_CHAR: i32 = 0xFFFD;

/// unicode.UpperCase / unicode.LowerCase / unicode.TitleCase indices into
/// `CaseRange.Delta`.
const UPPER_CASE: usize = 0;
const LOWER_CASE: usize = 1;

/// `Range16` — unicode.Range16.
pub(crate) struct Range16 {
    pub lo: u16,
    pub hi: u16,
    pub stride: u16,
}

/// `Range32` — unicode.Range32.
pub(crate) struct Range32 {
    pub lo: u32,
    pub hi: u32,
    pub stride: u32,
}

/// `RangeTable` — unicode.RangeTable.
pub(crate) struct RangeTable {
    pub r16: &'static [Range16],
    pub r32: &'static [Range32],
    /// number of entries in R16 with Hi <= MaxLatin1; unused — Go reads it
    /// only in `isExcludingLatin`, which the ported helpers never call (see
    /// `is_upper`). Kept for table fidelity with the generated data.
    #[allow(dead_code)]
    pub latin_offset: usize,
}

/// `CaseRange` — unicode.CaseRange (`Delta` is `d` = `[3]rune`; the sentinel
/// for "Upper-Lower pair sequence" is `MaxRune+1`, emitted by the generator
/// as `MAX_RUNE_PAIR`).
pub(crate) struct CaseRange {
    pub lo: u32,
    pub hi: u32,
    pub delta: [i32; 3],
}

/// `MAX_RUNE_PAIR` — Go's pair-sequence sentinel `MaxRune + 1` (`delta >
/// MaxRune` in `convertCase`).
pub(crate) const MAX_RUNE_PAIR: i32 = MAX_RUNE + 1;

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

// is reports whether the rune is in the specified table of ranges.
// (unicode.Is)
pub(crate) fn is(range_tab: &RangeTable, r: i32) -> bool {
    let r16 = range_tab.r16;
    // Compare as u32 to correctly handle negative runes.
    if !r16.is_empty() && (r as u32) <= r16[r16.len() - 1].hi as u32 {
        return is16(r16, r as u16);
    }
    let r32 = range_tab.r32;
    if !r32.is_empty() && r >= r32[0].lo as i32 {
        return is32(r32, r as u32);
    }
    false
}

/// `unicode.Is(unicode.Mn, r)` — `unicode.Mn` is `_Mn` (category Mark,
/// nonspacing). Used by `removeDiacritics` in organizeimports.go.
pub(crate) fn is_mn(r: i32) -> bool {
    is(&MN, r)
}

/// `unicode.IsUpper(r)`.
///
/// Go uses the `properties` Latin-1 fast path for `r <= MaxLatin1` and
/// `isExcludingLatin(Upper, r)` otherwise; both consult category `Lu`, which
/// is exactly what the generated `UPPER` table contains — so a plain `is`
/// over the whole table is equivalent.
pub(crate) fn is_upper(r: i32) -> bool {
    is(&UPPER, r)
}

// lookupCaseRange returns the CaseRange mapping for rune r or None if no
// mapping exists for r. (unicode.lookupCaseRange)
fn lookup_case_range(r: i32, case_range: &[CaseRange]) -> Option<&CaseRange> {
    // binary search over ranges
    let mut lo = 0;
    let mut hi = case_range.len();
    while lo < hi {
        let m = (lo + hi) >> 1;
        let cr = &case_range[m];
        if cr.lo as i32 <= r && r <= cr.hi as i32 {
            return Some(cr);
        }
        if r < cr.lo as i32 {
            hi = m;
        } else {
            lo = m + 1;
        }
    }
    None
}

// convertCase converts r to `_case` using CaseRange cr.
// (unicode.convertCase — `delta > MaxRune` selects the pair-sequence mapping.)
fn convert_case(_case: usize, r: i32, cr: &CaseRange) -> i32 {
    let delta = cr.delta[_case];
    if delta > MAX_RUNE {
        // In an Upper-Lower sequence, which always starts with
        // an UpperCase letter, the real deltas always look like:
        //	{0, 1, 0}    UpperCase (Lower is next)
        //	{-1, 0, -1}  LowerCase (Upper, Title are previous)
        // The characters at even offsets from the beginning of the
        // sequence are upper case; the ones at odd offsets are lower.
        // The correct mapping can be done by clearing or setting the low
        // bit in the sequence offset.
        // The constants UpperCase and TitleCase are even while LowerCase
        // is odd so we take the low bit from _case.
        return cr.lo as i32 + ((r - cr.lo as i32) & !1 | (_case as i32 & 1));
    }
    r + delta
}

// to maps the rune using the specified case mapping.
// It additionally reports whether caseRange contained a mapping for r.
// (unicode.to)
fn to(_case: usize, r: i32, case_range: &[CaseRange]) -> i32 {
    // `to` in Go checks `0 <= _case < MaxCase`; the callers below only pass
    // UPPER_CASE/LOWER_CASE.
    if let Some(cr) = lookup_case_range(r, case_range) {
        return convert_case(_case, r, cr);
    }
    r
}

// To maps the rune to the specified case. (unicode.To)
fn to_case(_case: usize, r: i32) -> i32 {
    to(_case, r, CASE_RANGES)
}

/// `unicode.ToUpper(r)`.
pub(crate) fn to_upper(r: i32) -> i32 {
    if r <= MAX_ASCII {
        if (0x61..=0x7A).contains(&r) {
            return r - 0x20;
        }
        return r;
    }
    to_case(UPPER_CASE, r)
}

/// `unicode.ToLower(r)`.
pub(crate) fn to_lower(r: i32) -> i32 {
    if r <= MAX_ASCII {
        if (0x41..=0x5A).contains(&r) {
            return r + 0x20;
        }
        return r;
    }
    to_case(LOWER_CASE, r)
}

/// `unicode.ToUpper` as a `char` convenience — the result of a Go simple
/// case mapping is always a single rune.
pub(crate) fn char_to_upper(c: char) -> char {
    char::from_u32(to_upper(c as i32) as u32).unwrap_or('\u{FFFD}')
}

/// `strings.ToLower(s)` — Go's strings.ToLower maps each rune with
/// `unicode.ToLower` (simple mapping, no expansion); Rust `&str` input is
/// always valid UTF-8, so there is no invalid-byte path.
pub(crate) fn strings_to_lower(s: &str) -> String {
    // optimize for ASCII-only strings (strings.ToLower fast path).
    if s.is_ascii() {
        return s.to_ascii_lowercase();
    }
    s.chars()
        .map(|c| {
            let r = to_lower(c as i32);
            char::from_u32(r as u32).unwrap_or('\u{FFFD}')
        })
        .collect()
}
