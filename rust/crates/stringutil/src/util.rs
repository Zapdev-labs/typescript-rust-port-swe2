// Ported from tsc/internal/stringutil/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// Package stringutil Exports common rune utilities for parsing and emitting javascript

use std::borrow::Cow;

use crate::unicode::{self, utf8, utf16};

pub fn is_white_space_like(ch: char) -> bool {
    is_white_space_single_line(ch) || is_line_break(ch)
}

pub fn is_white_space_single_line(ch: char) -> bool {
    // Note: nextLine is in the Zs space, and should be considered to be a whitespace.
    // It is explicitly not a line-break as it isn't in the exact set specified by EcmaScript.
    matches!(
        ch,
        ' ' // space
        | '\t' // tab
        | '\u{b}' // verticalTab
        | '\u{c}' // formFeed
        | '\u{85}' // nextLine
        | '\u{a0}' // nonBreakingSpace
        | '\u{1680}' // ogham
        | '\u{2000}' // enQuad
        | '\u{2001}' // emQuad
        | '\u{2002}' // enSpace
        | '\u{2003}' // emSpace
        | '\u{2004}' // threePerEmSpace
        | '\u{2005}' // fourPerEmSpace
        | '\u{2006}' // sixPerEmSpace
        | '\u{2007}' // figureSpace
        | '\u{2008}' // punctuationEmSpace
        | '\u{2009}' // thinSpace
        | '\u{200a}' // hairSpace
        | '\u{200b}' // zeroWidthSpace
        | '\u{202f}' // narrowNoBreakSpace
        | '\u{205f}' // mathematicalSpace
        | '\u{3000}' // ideographicSpace
        | '\u{feff}' // byteOrderMark
    )
}

pub fn is_line_break(ch: char) -> bool {
    // ES5 7.3:
    // The ECMAScript line terminator characters are listed in Table 3.
    //     Table 3: Line Terminator Characters
    //     Code Unit Value     Name                    Formal Name
    //     \u000A              Line Feed               <LF>
    //     \u000D              Carriage Return         <CR>
    //     \u2028              Line separator          <LS>
    //     \u2029              Paragraph separator     <PS>
    // Only the characters in Table 3 are treated as line terminators. Other new line or line
    // breaking characters are treated as white space but not as line terminators.
    matches!(
        ch,
        '\n' // lineFeed
        | '\r' // carriageReturn
        | '\u{2028}' // lineSeparator
        | '\u{2029}' // paragraphSeparator
    )
}

pub fn is_digit(ch: char) -> bool {
    ch.is_ascii_digit()
}

pub fn is_octal_digit(ch: char) -> bool {
    ('0'..='7').contains(&ch)
}

pub fn is_hex_digit(ch: char) -> bool {
    ch.is_ascii_hexdigit()
}

pub fn is_ascii_letter(ch: char) -> bool {
    ch.is_ascii_alphabetic()
}

pub fn split_lines(text: &[u8]) -> Vec<&[u8]> {
    let mut lines = Vec::with_capacity(memchr::memchr_iter(b'\n', text).count() + 1); // preallocate
    let mut start = 0;
    let mut pos = 0;
    while pos < text.len() {
        match text[pos] {
            b'\r' => {
                if pos + 1 < text.len() && text[pos + 1] == b'\n' {
                    lines.push(&text[start..pos]);
                    pos += 2;
                    start = pos;
                    continue;
                }
                // PORT: Go's `fallthrough` to the '\n' case.
                lines.push(&text[start..pos]);
                pos += 1;
                start = pos;
                continue;
            }
            b'\n' => {
                lines.push(&text[start..pos]);
                pos += 1;
                start = pos;
                continue;
            }
            _ => {}
        }
        pos += 1;
    }
    if start < text.len() {
        lines.push(&text[start..]);
    }
    lines
}

pub fn guess_indentation(lines: &[&[u8]]) -> i32 {
    const MAX_SMI_X86: i32 = 0x3fff_ffff;
    let mut indentation = MAX_SMI_X86;
    for &line in lines {
        if line.is_empty() {
            continue;
        }
        let mut i = 0;
        while i < line.len() && i < indentation as usize {
            let (ch, size) = utf8::decode_rune_in_string(&line[i..]);
            if !is_white_space_like(char::from_u32(ch as u32).unwrap_or('\u{FFFD}')) {
                break;
            }
            i += size;
        }
        if i < indentation as usize {
            indentation = i as i32;
        }
        if indentation == 0 {
            return 0;
        }
    }
    if indentation == MAX_SMI_X86 {
        return 0;
    }
    indentation
}

// https://tc39.es/ecma262/multipage/global-object.html#sec-encodeuri-uri
pub fn encode_uri(s: &[u8]) -> String {
    let mut builder = String::with_capacity(s.len());
    for i in 0..s.len() {
        let b = s[i];
        if !should_escape_for_encode_uri(b) {
            builder.push(b as char);
            continue;
        }

        for &escaped in &s[i..i + 1] {
            builder.push('%');
            builder.push(UPPERHEX[(escaped >> 4) as usize] as char);
            builder.push(UPPERHEX[(escaped & 0x0f) as usize] as char);
        }
    }
    builder
}

const UPPERHEX: &[u8; 16] = b"0123456789ABCDEF";

fn should_escape_for_encode_uri(b: u8) -> bool {
    match b {
        b'A'..=b'Z' => return false,
        b'a'..=b'z' => return false,
        b'0'..=b'9' => return false,
        _ => {}
    }

    !matches!(
        b,
        b';' | b'/'
            | b'?'
            | b':'
            | b'@'
            | b'&'
            | b'='
            | b'+'
            | b'$'
            | b','
            | b'#'
            | b'-'
            | b'_'
            | b'.'
            | b'!'
            | b'~'
            | b'*'
            | b'\''
            | b'('
            | b')'
    )
}

fn get_byte_order_mark_length(text: &[u8]) -> usize {
    if !text.is_empty() {
        let ch0 = text[0];
        if ch0 == 0xfe {
            if text.len() >= 2 && text[1] == 0xff {
                return 2; // utf16be
            }
            return 0;
        }
        if ch0 == 0xff {
            if text.len() >= 2 && text[1] == 0xfe {
                return 2; // utf16le
            }
            return 0;
        }
        if ch0 == 0xef {
            if text.len() >= 3 && text[1] == 0xbb && text[2] == 0xbf {
                return 3; // utf8
            }
            return 0;
        }
    }
    0
}

pub fn remove_byte_order_mark(text: &[u8]) -> &[u8] {
    let length = get_byte_order_mark_length(text);
    if length > 0 {
        return &text[length..];
    }
    text
}

pub fn add_utf8_byte_order_mark(text: &[u8]) -> Cow<'_, [u8]> {
    if get_byte_order_mark_length(text) == 0 {
        let mut v = Vec::with_capacity(3 + text.len());
        v.extend_from_slice(b"\xEF\xBB\xBF");
        v.extend_from_slice(text);
        return Cow::Owned(v);
    }
    Cow::Borrowed(text)
}

pub fn strip_quotes(name: &[u8]) -> &[u8] {
    if name.len() < 2 {
        return name;
    }
    let (first_char, _) = utf8::decode_rune_in_string(name);
    let (last_char, _) = utf8::decode_last_rune_in_string(name);
    if first_char == last_char
        && (first_char == '\'' as i32 || first_char == '"' as i32 || first_char == '`' as i32)
    {
        return &name[1..name.len() - 1];
    }
    name
}

pub fn unquote_string(str_: &[u8]) -> Vec<u8> {
    // strconv.Unquote is insufficient as that only handles a single character inside single quotes, as those are character literals in go
    let inner = strip_quotes(str_);
    // In strada we do str.replace(/\\./g, s => s.substring(1)) - which is to say, replace all backslash-something with just something
    // That's replicated here faithfully, but it seems wrong! This should probably be an actual unquote operation?
    // PORT: Go runs the compiled regexp `\\.` (backslash + any rune except '\n')
    // via ReplaceAllStringFunc; the regex crate is forbidden by SPEC §5.11, so
    // the equivalent left-to-right scan is spelled out.
    let mut out = Vec::with_capacity(inner.len());
    let mut i = 0;
    while i < inner.len() {
        if inner[i] == b'\\' && i + 1 < inner.len() {
            let (r, size) = utf8::decode_rune_in_string(&inner[i + 1..]);
            if r != '\n' as i32 {
                out.extend_from_slice(&inner[i + 1..i + 1 + size]);
                i += 1 + size;
                continue;
            }
        }
        out.push(inner[i]);
        i += 1;
    }
    out
}

pub fn lower_first_char(str_: &[u8]) -> Vec<u8> {
    let (char_, size) = utf8::decode_rune_in_string(str_);
    if size > 0 {
        let mut v = Vec::with_capacity(str_.len());
        utf8::append_rune(&mut v, unicode::to_lower(char_));
        v.extend_from_slice(&str_[size..]);
        return v;
    }
    str_.to_vec()
}

pub fn truncate_by_runes(str_: &[u8], max_length: i32) -> &[u8] {
    if (str_.len() as i64) < max_length as i64 {
        return str_;
    }
    if max_length <= 0 {
        return b"";
    }
    let mut rune_count: i32 = 0;
    let mut i = 0;
    while i < str_.len() {
        // PORT: `for i := range str` yields the byte offset of each rune start.
        let (_, size) = utf8::decode_rune_in_string(&str_[i..]);
        rune_count += 1;
        if rune_count > max_length {
            return &str_[..i];
        }
        i += size;
    }
    str_
}

/// SurrogateLowStart is the boundary between the high and low halves of the
/// UTF-16 surrogate range. unicode/utf16 only exposes IsSurrogate for the
/// whole range, so this split point is defined here to distinguish the two.
pub const SURROGATE_LOW_START: i32 = 0xDC00;

pub fn is_high_surrogate(ch: i32) -> bool {
    utf16::is_surrogate(ch) && ch < SURROGATE_LOW_START
}

pub fn is_low_surrogate(ch: i32) -> bool {
    utf16::is_surrogate(ch) && ch >= SURROGATE_LOW_START
}

pub fn is_surrogate(ch: i32) -> bool {
    utf16::is_surrogate(ch)
}

pub fn surrogate_pair_to_code_point(high: i32, low: i32) -> i32 {
    utf16::decode_rune(high, low)
}

pub fn code_point_to_surrogate_pair(ch: i32) -> (i32, i32) {
    utf16::encode_rune(ch)
}

// A lone surrogate (U+D800–U+DFFF) cannot be represented in valid UTF-8, so
// EncodeJSStringRune stores it as the 3-byte CESU-8/WTF-8 sentinel that UTF-8
// would use for that code point if surrogates were encodable. unicode/utf8
// and unicode/utf16 deliberately refuse to encode or decode surrogates, so
// the byte math is spelled out here.
//
// Byte layout for a code point cp in U+D000–U+DFFF (lead nibble 0xD):
//   byte0 = 0xE0 | (cp >> 12)          == 0xED
//   byte1 = 0x80 | ((cp >> 6) & 0x3F)
//   byte2 = 0x80 | (cp & 0x3F)
const SURROGATE_UTF8_LEAD: u8 = 0xED; // byte0, shared by the whole U+D000–U+DFFF block
const SURROGATE_UTF8_LEAD_BITS: i32 = 0xD000; // (surrogateUTF8Lead & 0x0F) << 12, byte0's decoded contribution
const UTF8_CONT_MARKER: u8 = 0x80; // continuation byte marker / min value (10xxxxxx)
const UTF8_CONT_MAX: u8 = 0xBF; // continuation byte max value
const UTF8_CONT_MASK: u8 = 0x3F; // data bits carried by a continuation byte

// byte1 bounds that pin the block down to the surrogate range U+D800–U+DFFF:
// 0xD800 -> 0xA0, 0xDFFF -> 0xBF.
const SURROGATE_UTF8_BYTE1_MIN: u8 = 0xA0;
const SURROGATE_UTF8_BYTE1_MAX: u8 = 0xBF;

pub fn encode_js_string_rune(ch: i32) -> Vec<u8> {
    if is_surrogate(ch) {
        return vec![
            SURROGATE_UTF8_LEAD,
            UTF8_CONT_MARKER | (((ch >> 6) & UTF8_CONT_MASK as i32) as u8),
            UTF8_CONT_MARKER | ((ch & UTF8_CONT_MASK as i32) as u8),
        ];
    }
    // string(ch) — Go writes the UTF-8 encoding of U+FFFD for out-of-range runes.
    let mut v = Vec::new();
    utf8::append_rune(&mut v, ch);
    v
}

pub fn decode_js_string_rune(s: &[u8]) -> (i32, usize) {
    if s.len() >= 3
        && s[0] == SURROGATE_UTF8_LEAD
        && (SURROGATE_UTF8_BYTE1_MIN..=SURROGATE_UTF8_BYTE1_MAX).contains(&s[1])
        && (UTF8_CONT_MARKER..=UTF8_CONT_MAX).contains(&s[2])
    {
        return (
            SURROGATE_UTF8_LEAD_BITS
                | (((s[1] & UTF8_CONT_MASK) as i32) << 6)
                | (s[2] & UTF8_CONT_MASK) as i32,
            3,
        );
    }
    utf8::decode_rune_in_string(s)
}

// CombineSurrogatePairs canonicalizes a JS-string value produced by
// concatenation, merging any adjacent high+low surrogate sentinel pair (as
// written by EncodeJSStringRune) into the single supplementary code point they
// represent. This mirrors how concatenating two UTF-16 code units forms a
// surrogate pair in a JavaScript string. It must be applied wherever separately
// scanned string values are joined, since each half is only a lone surrogate
// until it meets its partner. Strings without a lone-surrogate sentinel (the
// common case) are returned unchanged.
pub fn combine_surrogate_pairs(s: &[u8]) -> Cow<'_, [u8]> {
    if memchr::memchr(SURROGATE_UTF8_LEAD, s).is_none() {
        return Cow::Borrowed(s);
    }
    let mut b = Vec::with_capacity(s.len());
    let mut i = 0;
    while i < s.len() {
        let (r, size) = decode_js_string_rune(&s[i..]);
        if is_high_surrogate(r) {
            let (low, low_size) = decode_js_string_rune(&s[i + size..]);
            if is_low_surrogate(low) {
                utf8::append_rune(&mut b, surrogate_pair_to_code_point(r, low));
                i += size + low_size;
                continue;
            }
        }
        b.extend_from_slice(&s[i..i + size]);
        i += size;
    }
    Cow::Owned(b)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encode_uri() {
        let tests: [(&str, &str, &str); 3] = [
            ("encodes spaces as percent20", "a b", "a%20b"),
            (
                "preserves reserved uri characters",
                ";/?:@&=+$,#",
                ";/?:@&=+$,#",
            ),
            (
                "encodes brackets and unicode using utf8 bytes",
                "①Ⅻㄨㄩ U1[abc]",
                "%E2%91%A0%E2%85%AB%E3%84%A8%E3%84%A9%20U1%5Babc%5D",
            ),
        ];

        for (name, input, expected) in tests {
            let got = encode_uri(input.as_bytes());
            assert_eq!(
                got, expected,
                "{name}: EncodeURI({input:?}) = {got:?}, expected {expected:?}"
            );
        }
    }
}
