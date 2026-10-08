// Ported from tsc/internal/stringutil/compare.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(shim): temporary — remove once tsc-stringutil provides these functions.
// This module exists because tsc-stringutil was still being ported when
// tsc-tspath was written. When `tsc_stringutil` provides the snake_case mirrors
// of these names, delete this module and replace `use crate::stringutil_shim as
// stringutil` with `use tsc_stringutil as stringutil` in each file.
//
// Shimmed functions:
//   - equate_string_case_insensitive   (stringutil.EquateStringCaseInsensitive)
//   - equate_string_case_sensitive     (stringutil.EquateStringCaseSensitive)
//   - get_string_equality_comparer     (stringutil.GetStringEqualityComparer)
//   - compare_strings_case_insensitive (stringutil.CompareStringsCaseInsensitive)
//   - compare_strings_case_sensitive   (stringutil.CompareStringsCaseSensitive)
//   - get_string_comparer              (stringutil.GetStringComparer)

pub type Comparison = i32;

pub const COMPARISON_LESS_THAN: Comparison = -1;
pub const COMPARISON_EQUAL: Comparison = 0;
pub const COMPARISON_GREATER_THAN: Comparison = 1;

// Go's unicode.ToLower/ToUpper perform the *simple* (1:1) case mappings. Rust's
// char::to_lowercase/to_uppercase perform the *full* mappings, which can emit
// multiple chars. The only character whose full lowercase mapping is multi-char
// while lacking a simple mapping is U+0130 ('İ'); for uppercase the multi-char
// unconditional mappings (e.g. 'ß' -> "SS") differ from the simple mapping
// (U+1E9E), so first-char is NOT safe there — callers needing simple uppercase
// must not use to_uppercase().next() blindly (see equate_string_case_insensitive
// below, which compares the full mapping iterators instead).
// PORT(shim): temporary — remove once tsc-stringutil provides go_to_lower.
// Used by tspath::to_file_name_lower_case (Go unicode.ToLower, simple mapping).
pub(crate) fn go_to_lower(c: char) -> char {
    if c == '\u{0130}' {
        return c;
    }
    let mut it = c.to_lowercase();
    it.next().unwrap()
}

// Port of Go strings.EqualFold. Two runes are fold-equal iff they belong to the
// same SimpleFold orbit. For Unicode case data that is exactly equivalent to
// "same full lowercase mapping OR same full uppercase mapping": case mappings
// never cross orbits, so equal mappings imply same orbit; and same-orbit chars
// always agree on either their lower or their upper mapping (the only orbits
// where lowercase differs within the orbit are sigma/titlecase-like triples,
// which share a single-char uppercase).
fn equate_runes_case_insensitive(a: char, b: char) -> bool {
    if a == b {
        return true;
    }
    a.to_lowercase().eq(b.to_lowercase()) || a.to_uppercase().eq(b.to_uppercase())
}

// !!!
// return a == b || strings.ToUpper(a) == strings.ToUpper(b)
pub fn equate_string_case_insensitive(a: &str, b: &str) -> bool {
    // strings.EqualFold
    if a == b {
        return true;
    }
    let mut ai = a.chars();
    let mut bi = b.chars();
    loop {
        match (ai.next(), bi.next()) {
            (None, None) => return true,
            (Some(ca), Some(cb)) => {
                if !equate_runes_case_insensitive(ca, cb) {
                    return false;
                }
            }
            _ => return false,
        }
    }
}

pub fn equate_string_case_sensitive(a: &str, b: &str) -> bool {
    a == b
}

pub fn get_string_equality_comparer(ignore_case: bool) -> fn(&str, &str) -> bool {
    if ignore_case {
        equate_string_case_insensitive
    } else {
        equate_string_case_sensitive
    }
}

pub fn compare_strings_case_insensitive(a: &str, b: &str) -> Comparison {
    if a == b {
        return COMPARISON_EQUAL;
    }
    let mut ai = a.chars();
    let mut bi = b.chars();
    loop {
        match (ai.next(), bi.next()) {
            (None, None) => return COMPARISON_EQUAL,
            (None, Some(_)) => return COMPARISON_LESS_THAN,
            (Some(_), None) => return COMPARISON_GREATER_THAN,
            (Some(ca), Some(cb)) => {
                let lca = go_to_lower(ca);
                let lcb = go_to_lower(cb);
                if lca != lcb {
                    if lca < lcb {
                        return COMPARISON_LESS_THAN;
                    }
                    return COMPARISON_GREATER_THAN;
                }
            }
        }
    }
}

// strings.Compare
pub fn compare_strings_case_sensitive(a: &str, b: &str) -> Comparison {
    match a.cmp(b) {
        std::cmp::Ordering::Less => COMPARISON_LESS_THAN,
        std::cmp::Ordering::Equal => COMPARISON_EQUAL,
        std::cmp::Ordering::Greater => COMPARISON_GREATER_THAN,
    }
}

pub fn get_string_comparer(ignore_case: bool) -> fn(&str, &str) -> Comparison {
    if ignore_case {
        compare_strings_case_insensitive
    } else {
        compare_strings_case_sensitive
    }
}
