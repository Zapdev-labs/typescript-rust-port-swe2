// Ported from tsc/internal/stringutil/compare.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(shim): signature adapters — tsc-stringutil exposes these functions on
// `&[u8]` (byte-oriented, mirroring Go's []byte utilities), while tspath works
// on `&str`. These wrappers delegate to tsc_stringutil via `as_bytes()`, which
// is free and lossless for UTF-8. If tsc-stringutil later grows `&str`
// overloads, delete this module and use it directly.

pub use tsc_stringutil::Comparison;

// PORT(shim): temporary — remove once tsc-stringutil exposes a public
// `unicode::to_lower` (Go's unicode.ToLower, *simple* case mapping).
// Go's unicode.ToLower performs 1:1 simple case mappings. Rust's
// char::to_lowercase performs the *full* mappings, which can emit multiple
// chars. The only char whose full lowercase mapping is multi-char while
// lacking a simple mapping is U+0130 ('İ'), which maps to itself under the
// simple mapping; for every other char the first char of the full mapping is
// the simple mapping. Used by tspath::to_file_name_lower_case.
pub(crate) fn go_to_lower(c: char) -> char {
    if c == '\u{0130}' {
        return c;
    }
    let mut it = c.to_lowercase();
    it.next().unwrap()
}

// stringutil.EquateStringCaseInsensitive
pub fn equate_string_case_insensitive(a: &str, b: &str) -> bool {
    tsc_stringutil::equate_string_case_insensitive(a.as_bytes(), b.as_bytes())
}

// stringutil.EquateStringCaseSensitive
pub fn equate_string_case_sensitive(a: &str, b: &str) -> bool {
    tsc_stringutil::equate_string_case_sensitive(a.as_bytes(), b.as_bytes())
}

// stringutil.GetStringEqualityComparer
pub fn get_string_equality_comparer(ignore_case: bool) -> fn(&str, &str) -> bool {
    if ignore_case {
        equate_string_case_insensitive
    } else {
        equate_string_case_sensitive
    }
}

// stringutil.CompareStringsCaseInsensitive
pub fn compare_strings_case_insensitive(a: &str, b: &str) -> Comparison {
    tsc_stringutil::compare_strings_case_insensitive(a.as_bytes(), b.as_bytes())
}

// stringutil.CompareStringsCaseSensitive
pub fn compare_strings_case_sensitive(a: &str, b: &str) -> Comparison {
    tsc_stringutil::compare_strings_case_sensitive(a.as_bytes(), b.as_bytes())
}

// stringutil.GetStringComparer
pub fn get_string_comparer(ignore_case: bool) -> fn(&str, &str) -> Comparison {
    if ignore_case {
        compare_strings_case_insensitive
    } else {
        compare_strings_case_sensitive
    }
}
