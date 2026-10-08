// Ported from tsc/internal/stringutil/compare.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::unicode::{self, utf8};

pub fn equate_string_case_insensitive(a: &[u8], b: &[u8]) -> bool {
    // !!!
    // return a == b || strings.ToUpper(a) == strings.ToUpper(b)
    unicode::equal_fold(a, b)
}

pub fn equate_string_case_sensitive(a: &[u8], b: &[u8]) -> bool {
    a == b
}

pub fn get_string_equality_comparer(ignore_case: bool) -> fn(&[u8], &[u8]) -> bool {
    if ignore_case {
        equate_string_case_insensitive
    } else {
        equate_string_case_sensitive
    }
}

pub type Comparison = i32;

pub const COMPARISON_LESS_THAN: Comparison = -1;
pub const COMPARISON_EQUAL: Comparison = 0;
pub const COMPARISON_GREATER_THAN: Comparison = 1;

pub fn compare_strings_case_insensitive(a: &[u8], b: &[u8]) -> Comparison {
    if a == b {
        return COMPARISON_EQUAL;
    }
    let mut a = a;
    let mut b = b;
    loop {
        let (ca, sa) = utf8::decode_rune_in_string(a);
        let (cb, sb) = utf8::decode_rune_in_string(b);
        if sa == 0 {
            if sb == 0 {
                return COMPARISON_EQUAL;
            }
            return COMPARISON_LESS_THAN;
        }
        if sb == 0 {
            return COMPARISON_GREATER_THAN;
        }
        let lca = unicode::to_lower(ca);
        let lcb = unicode::to_lower(cb);
        if lca != lcb {
            if lca < lcb {
                return COMPARISON_LESS_THAN;
            }
            return COMPARISON_GREATER_THAN;
        }
        a = &a[sa..];
        b = &b[sb..];
    }
}

pub fn compare_strings_case_sensitive(a: &[u8], b: &[u8]) -> Comparison {
    // strings.Compare
    match a.cmp(b) {
        std::cmp::Ordering::Less => COMPARISON_LESS_THAN,
        std::cmp::Ordering::Equal => COMPARISON_EQUAL,
        std::cmp::Ordering::Greater => COMPARISON_GREATER_THAN,
    }
}

pub fn get_string_comparer(ignore_case: bool) -> fn(&[u8], &[u8]) -> Comparison {
    if ignore_case {
        compare_strings_case_insensitive
    } else {
        compare_strings_case_sensitive
    }
}

pub fn has_prefix(s: &[u8], prefix: &[u8], case_sensitive: bool) -> bool {
    if case_sensitive {
        return s.starts_with(prefix);
    }
    if prefix.len() > s.len() {
        return false;
    }
    unicode::equal_fold(&s[0..prefix.len()], prefix)
}

pub fn has_suffix(s: &[u8], suffix: &[u8], case_sensitive: bool) -> bool {
    if case_sensitive {
        return s.ends_with(suffix);
    }
    if suffix.len() > s.len() {
        return false;
    }
    unicode::equal_fold(&s[s.len() - suffix.len()..], suffix)
}

pub fn has_prefix_and_suffix_without_overlap(
    s: &[u8],
    prefix: &[u8],
    suffix: &[u8],
    case_sensitive: bool,
) -> bool {
    if prefix.len() + suffix.len() > s.len() {
        return false;
    }

    has_prefix(s, prefix, case_sensitive) && has_suffix(s, suffix, case_sensitive)
}

pub fn compare_strings_case_insensitive_then_sensitive(a: &[u8], b: &[u8]) -> Comparison {
    let cmp = compare_strings_case_insensitive(a, b);
    if cmp != COMPARISON_EQUAL {
        return cmp;
    }
    compare_strings_case_sensitive(a, b)
}

// CompareStringsCaseInsensitiveEslintCompatible performs a case-insensitive comparison
// using toLowerCase() instead of toUpperCase() for ESLint compatibility.
//
// `CompareStringsCaseInsensitive` transforms letters to uppercase for unicode reasons,
// while eslint's `sort-imports` rule transforms letters to lowercase. Which one you choose
// affects the relative order of letters and ASCII characters 91-96, of which `_` is a
// valid character in an identifier. So if we used `CompareStringsCaseInsensitive` for
// import sorting, TypeScript and eslint would disagree about the correct case-insensitive
// sort order for `__String` and `Foo`. Since eslint's whole job is to create consistency
// by enforcing nitpicky details like this, it makes way more sense for us to just adopt
// their convention so users can have auto-imports without making eslint angry.
pub fn compare_strings_case_insensitive_eslint_compatible(a: &[u8], b: &[u8]) -> Comparison {
    if a == b {
        return COMPARISON_EQUAL;
    }
    let a = unicode::strings_to_lower(a);
    let b = unicode::strings_to_lower(b);
    compare_strings_case_sensitive(&a, &b)
}
