// Ported from tsc/internal/stringutil/js_case.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::borrow::Cow;

use crate::js_case_generated::{
    self, SpecialCasingCondition, UNICODE_CASE_IGNORABLE_RANGES, UNICODE_CASED_RANGES,
};
use crate::unicode::{self, utf8};
use crate::util::{decode_js_string_rune, encode_js_string_rune, is_surrogate};

pub fn to_lower_js(str_: &[u8]) -> Cow<'_, [u8]> {
    if let Some(ascii) = to_lower_ascii(str_) {
        return ascii;
    }

    let mut builder = Vec::with_capacity(str_.len());
    // casedBefore tracks whether the most recent non-Case_Ignorable code point is
    // "cased", which is the backward half of the Final_Sigma context. We
    // accumulate it as we stream so we never have to scan (or decode) backwards.
    let mut cased_before = false;
    let mut i = 0;
    while i < str_.len() {
        let (r, size) = decode_js_string_rune(&str_[i..]);
        i += size;
        if is_surrogate(r) {
            // A lone surrogate has no case mapping; preserve it verbatim, matching
            // String.prototype.toLowerCase. EncodeJSStringRune restores the sentinel
            // bytes because WriteRune would re-encode the surrogate as U+FFFD.
            builder.extend_from_slice(&encode_js_string_rune(r));
        } else if let Some(mapping) = js_case_generated::special_casing_mapping(r) {
            if mapping.condition == SpecialCasingCondition::FinalSigma
                && is_final_sigma_context(cased_before, str_, i)
            {
                builder.extend_from_slice(mapping.conditional_lower.as_bytes());
            } else {
                builder.extend_from_slice(mapping.lower.as_bytes());
            }
        } else {
            utf8::append_rune(&mut builder, r);
        }
        if !is_unicode_case_ignorable(r) {
            cased_before = is_sigma_cased(r);
        }
    }
    Cow::Owned(builder)
}

pub fn to_upper_js(str_: &[u8]) -> Cow<'_, [u8]> {
    if let Some(ascii) = to_upper_ascii(str_) {
        return ascii;
    }

    let mut builder = Vec::with_capacity(str_.len());
    let mut i = 0;
    while i < str_.len() {
        let (r, size) = decode_js_string_rune(&str_[i..]);
        if is_surrogate(r) {
            // A lone surrogate has no case mapping; preserve it verbatim, matching
            // String.prototype.toUpperCase. Copy the sentinel bytes directly because
            // WriteRune would re-encode the surrogate as U+FFFD.
            builder.extend_from_slice(&str_[i..i + size]);
        } else if let Some(mapping) = js_case_generated::special_casing_mapping(r) {
            builder.extend_from_slice(mapping.upper.as_bytes());
        } else {
            utf8::append_rune(&mut builder, r);
        }
        i += size;
    }

    Cow::Owned(builder)
}

// PORT: Go returns (string, bool); the string is the input itself when nothing
// mapped, so Option<Cow> mirrors both the ok flag and the no-copy fast path.
fn to_lower_ascii(str_: &[u8]) -> Option<Cow<'_, [u8]>> {
    let mut needs_mapping = false;
    for &ch in str_ {
        if ch >= utf8::RUNE_SELF as u8 {
            return None;
        }
        needs_mapping = needs_mapping || ch.is_ascii_uppercase();
    }
    if !needs_mapping {
        return Some(Cow::Borrowed(str_));
    }

    let mut buf = str_.to_vec();
    for ch in buf.iter_mut() {
        if ch.is_ascii_uppercase() {
            *ch += b'a' - b'A';
        }
    }
    Some(Cow::Owned(buf))
}

fn to_upper_ascii(str_: &[u8]) -> Option<Cow<'_, [u8]>> {
    let mut needs_mapping = false;
    for &ch in str_ {
        if ch >= utf8::RUNE_SELF as u8 {
            return None;
        }
        needs_mapping = needs_mapping || ch.is_ascii_lowercase();
    }
    if !needs_mapping {
        return Some(Cow::Borrowed(str_));
    }

    let mut buf = str_.to_vec();
    for ch in buf.iter_mut() {
        if ch.is_ascii_lowercase() {
            *ch -= b'a' - b'A';
        }
    }
    Some(Cow::Owned(buf))
}

// isFinalSigmaContext reports whether a sigma at the current position is in
// Final_Sigma context: it is preceded by a cased code point and not followed by
// one. casedBefore carries the backward half (tracked incrementally by the
// caller so we never scan backwards); afterOffset is the byte offset just past
// the sigma, from which we scan forward.
//
// ECMAScript points at Unicode Default Case Conversion for toLowerCase, and
// modern V8 reaches that behavior through Intl::ConvertToLower, which uses
// ICU root-locale lowercasing for non-Latin1 strings like Greek sigma.
// We intentionally do not delegate this to golang.org/x/text/cases: x/text
// is a general Unicode casing library, but its root-locale behavior is not
// an exact match for the JS semantics exercised by String.prototype
// .toLowerCase(), especially around Final_Sigma context. TypeScript needs the
// JS behavior itself here, so we keep the context-sensitive part explicit.
// SpiderMonkey models Final_Sigma with a more explicit context walk, while
// Unicode Table 3-17 describes it in terms of Cased and Case_Ignorable.
// We model the exposed V8/ICU behavior directly here: skip Case_Ignorable code
// points and then look for a Cased code point, exactly as Unicode Table 3-17
// defines the Final_Sigma condition. The Cased property already subsumes
// lowercase, uppercase, and titlecase letters, including the
// DerivedCoreProperties Lowercase/Uppercase extras such as ª, º, and Roman
// numerals.
fn is_final_sigma_context(cased_before: bool, str_: &[u8], after_offset: usize) -> bool {
    cased_before && !has_sigma_cased_after(str_, after_offset)
}

fn has_sigma_cased_after(str_: &[u8], start: usize) -> bool {
    let mut i = start;
    while i < str_.len() {
        let (r, size) = decode_js_string_rune(&str_[i..]);
        i += size;
        if is_unicode_case_ignorable(r) {
            continue;
        }
        return is_sigma_cased(r);
    }
    false
}

fn is_sigma_cased(r: i32) -> bool {
    unicode::is(&UNICODE_CASED_RANGES, r)
}

fn is_unicode_case_ignorable(r: i32) -> bool {
    unicode::is(&UNICODE_CASE_IGNORABLE_RANGES, r)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn enc(r: i32) -> Vec<u8> {
        encode_js_string_rune(r)
    }

    fn lower(s: &[u8]) -> Vec<u8> {
        to_lower_js(s).into_owned()
    }

    fn upper(s: &[u8]) -> Vec<u8> {
        to_upper_js(s).into_owned()
    }

    #[test]
    fn test_js_casing() {
        let tests: Vec<(&str, Vec<u8>, Vec<u8>)> = vec![
            ("ascii lowercase", lower(b"HELLO"), b"hello".to_vec()),
            ("ascii uppercase", upper(b"hello"), b"HELLO".to_vec()),
            (
                "lowercase dotted i",
                lower("İSPANYOL".as_bytes()),
                "i̇spanyol".as_bytes().to_vec(),
            ),
            (
                "lowercase lone sigma",
                lower("Σ".as_bytes()),
                "σ".as_bytes().to_vec(),
            ),
            (
                "lowercase final sigma",
                lower("ΟΣ".as_bytes()),
                "ος".as_bytes().to_vec(),
            ),
            (
                "lowercase non-sigma greek",
                lower("Ω".as_bytes()),
                "ω".as_bytes().to_vec(),
            ),
            (
                "uppercase sharp s",
                upper("ßfoo".as_bytes()),
                b"SSFOO".to_vec(),
            ),
            (
                "uppercase non-ascii simple mapping",
                upper("ω".as_bytes()),
                "Ω".as_bytes().to_vec(),
            ),
            (
                "uppercase ligature",
                upper("ﬁoo".as_bytes()),
                b"FIOO".to_vec(),
            ),
            (
                "capitalize-style uppercase",
                [upper("ß".as_bytes()), b"foo".to_vec()].concat(),
                b"SSfoo".to_vec(),
            ),
            (
                "uncapitalize-style lowercase",
                [lower("İ".as_bytes()), b"foo".to_vec()].concat(),
                "i̇foo".as_bytes().to_vec(),
            ),
            (
                "lowercase final sigma after lowercase letter without uppercase mapping",
                lower("ʕΣ".as_bytes()),
                "ʕς".as_bytes().to_vec(),
            ),
            (
                "lowercase sigma after modifier letter",
                lower("ʰΣ".as_bytes()),
                "ʰσ".as_bytes().to_vec(),
            ),
            (
                "lowercase sigma after case ignorable ypogegrammeni",
                lower("ͅΣ".as_bytes()),
                "ͅσ".as_bytes().to_vec(),
            ),
            (
                "lowercase final sigma after feminine ordinal indicator",
                lower("ªΣ".as_bytes()),
                "ªς".as_bytes().to_vec(),
            ),
            (
                "lowercase final sigma after masculine ordinal indicator",
                lower("ºΣ".as_bytes()),
                "ºς".as_bytes().to_vec(),
            ),
            (
                "lowercase final sigma after roman numeral",
                lower("ⅠΣ".as_bytes()),
                "ⅰς".as_bytes().to_vec(),
            ),
            (
                "lowercase sigma after uppercase property added after unicode 15",
                lower("\u{1C89}Σ".as_bytes()),
                "\u{1C89}σ".as_bytes().to_vec(),
            ),
            (
                "lowercase sigma after uppercase property skewed from local v8 unicode data",
                lower("\u{A7CB}Σ".as_bytes()),
                "\u{A7CB}σ".as_bytes().to_vec(),
            ),
            (
                "lowercase sigma before immediate latin letter",
                lower("ΣA".as_bytes()),
                "σa".as_bytes().to_vec(),
            ),
            (
                "lowercase sigma before immediate roman numeral letter",
                lower("ΣⅠ".as_bytes()),
                "σⅰ".as_bytes().to_vec(),
            ),
            (
                "lowercase sigma before case ignorable then latin letter",
                lower("ΣͅA".as_bytes()),
                "σͅa".as_bytes().to_vec(),
            ),
            ("uppercase lone surrogate", upper(&enc(0xD800)), enc(0xD800)),
            (
                "lowercase lone surrogate",
                lower(&[b"A".as_slice(), &enc(0xD800), b"B".as_slice()].concat()),
                [b"a".as_slice(), &enc(0xD800), b"b".as_slice()].concat(),
            ),
            (
                "uppercase lone low surrogate with text",
                upper(&[&enc(0xDC00), b"x".as_slice()].concat()),
                [&enc(0xDC00), b"X".as_slice()].concat(),
            ),
            (
                "lowercase lone surrogate before sigma",
                lower(&[&enc(0xD800), "Σ".as_bytes()].concat()),
                [&enc(0xD800), "σ".as_bytes()].concat(),
            ),
        ];

        for (name, got, want) in tests {
            assert_eq!(got, want, "{name}: got {got:?}, want {want:?}");
        }
    }
}
