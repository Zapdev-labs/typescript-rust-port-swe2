// Ported from tsc/internal/glob/glob.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Copyright 2023 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

use std::fmt;

/// A Glob is an LSP-compliant glob pattern, as defined by the spec:
/// https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#documentFilter
///
/// NOTE: this implementation is currently only intended for testing. In order
/// to make it production ready, we'd need to:
///   - verify it against the VS Code implementation
///   - add more tests
///   - microbenchmark, likely avoiding the element interface
///   - resolve the question of what is meant by "character". If it's a UTF-16
///     code (as we suspect) it'll be a bit more work.
///
/// Quoting from the spec:
/// Glob patterns can have the following syntax:
///   - `*` to match one or more characters in a path segment
///   - `?` to match on one character in a path segment
///   - `**` to match any number of path segments, including none
///   - `{}` to group sub patterns into an OR expression. (e.g. `**/*.{ts,js}`
///     matches all TypeScript and JavaScript files)
///   - `[]` to declare a range of characters to match in a path segment
///     (e.g., `example.[0-9]` to match on `example.0`, `example.1`, …)
///   - `[!...]` to negate a range of characters to match in a path segment
///     (e.g., `example.[!0-9]` to match on `example.a`, `example.b`, but
///     not `example.0`)
///
/// Expanding on this:
///   - '/' matches one or more literal slashes.
///   - any other character matches itself literally.
// PORT: PartialEq is not in upstream (Go has no element equality); derived for
// test assertions on parse results.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Glob {
    elems: Vec<Element>, // pattern elements
}

// PORT: Go's `error` return values are sentinel errors created with errors.New;
// ported as an enum whose Display text matches each Go message.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParseError {
    /// errors.New("** may only be adjacent to '/'")
    StarStarNotAdjacentToSlash,
    /// errors.New("unmatched '{'")
    UnmatchedBrace,
    /// errBadRange = errors.New("'[' patterns must be of the form [x-y]")
    BadRange,
    /// errInvalidUTF8 = errors.New("invalid UTF-8 encoding")
    ///
    /// PORT: unreachable for `&str` input — Rust strings are always valid UTF-8;
    /// kept for parity with Go's error set since Go strings can hold arbitrary bytes.
    InvalidUtf8,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            ParseError::StarStarNotAdjacentToSlash => "** may only be adjacent to '/'",
            ParseError::UnmatchedBrace => "unmatched '{'",
            ParseError::BadRange => "'[' patterns must be of the form [x-y]",
            ParseError::InvalidUtf8 => "invalid UTF-8 encoding",
        })
    }
}

impl std::error::Error for ParseError {}

/// Parse builds a Glob for the given pattern, returning an error if the pattern
/// is invalid.
// PORT: `Match` → `matches`, `Parse` → `parse`; the recursive worker is
// `parse_nested` (Rust cannot overload the name).
pub fn parse(pattern: &str) -> Result<Glob, ParseError> {
    let (g, _) = parse_nested(pattern, false)?;
    Ok(g)
}

fn parse_nested<'a>(mut pattern: &'a str, nested: bool) -> Result<(Glob, &'a str), ParseError> {
    let mut g = Glob::default();
    while !pattern.is_empty() {
        match pattern.as_bytes()[0] {
            b'/' => {
                pattern = &pattern[1..];
                g.elems.push(Element::Slash);
            }

            b'*' => {
                if pattern.len() > 1 && pattern.as_bytes()[1] == b'*' {
                    if g.elems.last().is_some_and(|e| !matches!(e, Element::Slash))
                        || (pattern.len() > 2 && pattern.as_bytes()[2] != b'/')
                    {
                        return Err(ParseError::StarStarNotAdjacentToSlash);
                    }
                    pattern = &pattern[2..];
                    g.elems.push(Element::StarStar);
                    continue;
                }
                pattern = &pattern[1..];
                g.elems.push(Element::Star);
            }

            b'?' => {
                pattern = &pattern[1..];
                g.elems.push(Element::AnyChar);
            }

            b'{' => {
                let mut gs = Vec::new();
                while pattern.as_bytes()[0] != b'}' {
                    pattern = &pattern[1..];
                    let (group_g, pat) = parse_nested(pattern, true)?;
                    if pat.is_empty() {
                        return Err(ParseError::UnmatchedBrace);
                    }
                    pattern = pat;
                    gs.push(group_g);
                }
                pattern = &pattern[1..];
                g.elems.push(Element::Group(gs));
            }

            b'}' | b',' => {
                if nested {
                    return Ok((g, pattern));
                }
                pattern = g.parse_literal(pattern, false);
            }

            b'[' => {
                pattern = &pattern[1..];
                if pattern.is_empty() {
                    return Err(ParseError::BadRange);
                }
                let mut negate = false;
                if pattern.as_bytes()[0] == b'!' {
                    pattern = &pattern[1..];
                    negate = true;
                }
                let (low, sz) = read_range_rune(pattern.as_bytes())?;
                pattern = &pattern[sz..];
                if pattern.is_empty() || pattern.as_bytes()[0] != b'-' {
                    return Err(ParseError::BadRange);
                }
                pattern = &pattern[1..];
                let (high, sz) = read_range_rune(pattern.as_bytes())?;
                pattern = &pattern[sz..];
                if pattern.is_empty() || pattern.as_bytes()[0] != b']' {
                    return Err(ParseError::BadRange);
                }
                pattern = &pattern[1..];
                g.elems.push(Element::CharRange { negate, low, high });
            }

            _ => {
                pattern = g.parse_literal(pattern, nested);
            }
        }
    }
    Ok((g, ""))
}

/// helper for decoding a rune in range elements, e.g. [a-z]
// PORT: operates on bytes like utf8.DecodeRuneInString; for `&str` input the
// InvalidUtf8 path cannot trigger.
fn read_range_rune(input: &[u8]) -> Result<(char, usize), ParseError> {
    let (r, sz) = decode_rune_in_string(input);
    if r == RUNE_ERROR {
        // See the documentation for DecodeRuneInString.
        match sz {
            0 => return Err(ParseError::BadRange),
            1 => return Err(ParseError::InvalidUtf8),
            _ => {}
        }
    }
    Ok((r, sz))
}

const RUNE_ERROR: char = '\u{FFFD}';

// PORT: mirrors Go's utf8.DecodeRuneInString (RFC 3629-strict decoding): empty
// input -> (RuneError, 0); invalid encoding -> (RuneError, 1); otherwise the
// decoded rune and its width in bytes.
fn decode_rune_in_string(s: &[u8]) -> (char, usize) {
    if s.is_empty() {
        return (RUNE_ERROR, 0);
    }
    let p0 = s[0];
    if p0 < 0x80 {
        return (p0 as char, 1);
    }
    // (size, accept range for the first continuation byte)
    let (size, lo, hi): (usize, u8, u8) = match p0 {
        0xC2..=0xDF => (2, 0x80, 0xBF),
        0xE0 => (3, 0xA0, 0xBF),
        0xE1..=0xEC => (3, 0x80, 0xBF),
        0xED => (3, 0x80, 0x9F),
        0xEE..=0xEF => (3, 0x80, 0xBF),
        0xF0 => (4, 0x90, 0xBF),
        0xF1..=0xF3 => (4, 0x80, 0xBF),
        0xF4 => (4, 0x80, 0x8F),
        _ => return (RUNE_ERROR, 1),
    };
    if s.len() < size {
        return (RUNE_ERROR, 1);
    }
    let b1 = s[1];
    if !(lo..=hi).contains(&b1) {
        return (RUNE_ERROR, 1);
    }
    let mut r = match size {
        2 => u32::from(p0 & 0x1F),
        3 => u32::from(p0 & 0x0F),
        _ => u32::from(p0 & 0x07),
    };
    r = (r << 6) | u32::from(b1 & 0x3F);
    for &b in &s[2..size] {
        if !(0x80..=0xBF).contains(&b) {
            return (RUNE_ERROR, 1);
        }
        r = (r << 6) | u32::from(b & 0x3F);
    }
    // The accept ranges above exclude surrogates and out-of-range code points.
    (char::from_u32(r).unwrap_or(RUNE_ERROR), size)
}

impl Glob {
    fn parse_literal<'a>(&mut self, pattern: &'a str, nested: bool) -> &'a str {
        let special_chars = if nested { "*?{[/}," } else { "*?{[/" };
        let end = pattern.find(|c| special_chars.contains(c)).unwrap_or(pattern.len());
        self.elems.push(Element::Literal(pattern[..end].to_string()));
        &pattern[end..]
    }
}

impl fmt::Display for Glob {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for e in &self.elems {
            write!(f, "{e}")?;
        }
        Ok(())
    }
}

// element holds a glob pattern element, as defined below.
// element types.
#[derive(Clone, Debug, PartialEq)]
enum Element {
    Slash,          // One or more '/' separators
    Literal(String), // string literal, not containing /, *, ?, {}, or []
    Star,           // *
    AnyChar,        // ?
    StarStar,       // **
    Group(Vec<Glob>), // {foo, bar, ...} grouping
    CharRange {
        // [a-z] character range
        // PORT: `negate` is parsed but, as upstream, never consulted by Match or
        // String — bug-for-bug fidelity ([!a-z] behaves like [a-z]).
        #[allow(dead_code)]
        negate: bool,
        low: char,
        high: char,
    },
}

impl fmt::Display for Element {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Element::Slash => f.write_str("/"),
            Element::Literal(l) => f.write_str(l),
            Element::Star => f.write_str("*"),
            Element::AnyChar => f.write_str("?"),
            Element::StarStar => f.write_str("**"),
            Element::Group(gs) => {
                f.write_str("{")?;
                for (i, g) in gs.iter().enumerate() {
                    if i > 0 {
                        f.write_str(",")?;
                    }
                    write!(f, "{g}")?;
                }
                f.write_str("}")
            }
            Element::CharRange { low, high, .. } => write!(f, "[{low}-{high}]"),
        }
    }
}

impl Glob {
    /// Match reports whether the input string matches the glob pattern.
    pub fn matches(&self, input: &str) -> bool {
        match_(&self.elems, input.as_bytes())
    }
}

// PORT: operates on byte slices so that the byte-indexed backtracking over
// `segInput[i:]` (which can split a multi-byte UTF-8 sequence, exactly like Go
// string slicing) is faithful.
fn match_(mut elems: &[Element], mut input: &[u8]) -> bool {
    while !elems.is_empty() {
        let elem = &elems[0];
        elems = &elems[1..];
        match elem {
            Element::Slash => {
                if input.is_empty() || input[0] != b'/' {
                    return false;
                }
                while input[0] == b'/' {
                    input = &input[1..];
                }
            }

            Element::StarStar => {
                // Special cases:
                //  - **/a matches "a"
                //  - **/ matches everything
                //
                // Note that if ** is followed by anything, it must be '/' (this is
                // enforced by Parse).
                if !elems.is_empty() {
                    elems = &elems[1..];
                }

                // A trailing ** matches anything.
                if elems.is_empty() {
                    return true;
                }

                // Backtracking: advance pattern segments until the remaining pattern
                // elements match.
                while !input.is_empty() {
                    if match_(elems, input) {
                        return true;
                    }
                    input = split(input).1;
                }
                return false;
            }

            Element::Literal(elem) => {
                if !input.starts_with(elem.as_bytes()) {
                    return false;
                }
                input = &input[elem.len()..];
            }

            Element::Star => {
                let seg_input;
                (seg_input, input) = split(input);

                let mut elem_end = elems.len();
                for (i, e) in elems.iter().enumerate() {
                    if matches!(e, Element::Slash) {
                        elem_end = i;
                        break;
                    }
                }
                let seg_elems = &elems[..elem_end];
                elems = &elems[elem_end..];

                // A trailing * matches the entire segment.
                if seg_elems.is_empty() {
                    continue;
                }

                // Backtracking: advance characters until remaining subpattern elements
                // match.
                let mut matched = false;
                for i in 0..seg_input.len() {
                    if match_(seg_elems, &seg_input[i..]) {
                        matched = true;
                        break;
                    }
                }
                if !matched {
                    return false;
                }
            }

            Element::AnyChar => {
                if input.is_empty() || input[0] == b'/' {
                    return false;
                }
                input = &input[1..];
            }

            Element::Group(members) => {
                // Append remaining pattern elements to each group member looking for a
                // match.
                let mut branch: Vec<Element> = Vec::new();
                for m in members {
                    branch.clear();
                    branch.extend(m.elems.iter().cloned());
                    branch.extend(elems.iter().cloned());
                    if match_(&branch, input) {
                        return true;
                    }
                }
                return false;
            }

            Element::CharRange { low, high, .. } => {
                if input.is_empty() || input[0] == b'/' {
                    return false;
                }
                let (c, sz) = decode_rune_in_string(input);
                if c < *low || c > *high {
                    return false;
                }
                input = &input[sz..];
            }
        }
    }

    input.is_empty()
}

/// split returns the portion before and after the first slash
/// (or sequence of consecutive slashes). If there is no slash
/// it returns (input, nil).
fn split(input: &[u8]) -> (&[u8], &[u8]) {
    let Some(i) = input.iter().position(|&b| b == b'/') else {
        return (input, &[]);
    };
    let first = &input[..i];
    for j in i..input.len() {
        if input[j] != b'/' {
            return (first, &input[j..]);
        }
    }
    (first, &[])
}

// PORT: no glob_test.go exists upstream; this test module is ADDED, with cases
// derived from the code's own comments and observable behavior.
#[cfg(test)]
mod tests {
    use super::*;

    fn assert_parses(pattern: &str) -> Glob {
        parse(pattern).unwrap_or_else(|e| panic!("pattern {pattern:?} should parse: {e}"))
    }

    #[test]
    fn star_star_adjacency() {
        // "** may only be adjacent to '/'"
        for pattern in ["**", "a/**", "**/a", "a/**/b", "**/", "a/**/"] {
            assert_parses(pattern);
        }
        for pattern in ["a**b", "**a", "a**", "***"] {
            assert_eq!(parse(pattern), Err(ParseError::StarStarNotAdjacentToSlash));
        }
    }

    #[test]
    fn unmatched_brace() {
        // "unmatched '{'" when a nested parse reaches end of input
        assert_eq!(parse("{"), Err(ParseError::UnmatchedBrace));
        assert_eq!(parse("{a"), Err(ParseError::UnmatchedBrace));
        assert_eq!(parse("{a,"), Err(ParseError::UnmatchedBrace));
        assert_eq!(parse("{a,b"), Err(ParseError::UnmatchedBrace));
    }

    #[test]
    fn bad_range() {
        // "'[' patterns must be of the form [x-y]"
        for pattern in ["[", "[a", "[a]", "[!a]", "[a-]", "[a-z"] {
            assert_eq!(parse(pattern), Err(ParseError::BadRange));
        }
        assert_parses("[a-z]");
        assert_parses("[!a-z]");
    }

    #[test]
    fn literal_and_star_star_matches() {
        // "**/a matches "a""; "**/ matches everything"
        assert!(assert_parses("**/a").matches("a"));
        assert!(assert_parses("**/a").matches("x/y/a"));
        assert!(assert_parses("**/").matches("anything/at/all"));

        // A trailing ** matches anything.
        assert!(assert_parses("a/**").matches("a/b/c"));

        // '/' matches one or more literal slashes.
        assert!(assert_parses("a/b").matches("a//b"));
        assert!(!assert_parses("a/b").matches("ab"));
    }

    #[test]
    fn star_any_char_range_and_group() {
        // `*` matches within a path segment; `?` a single character.
        assert!(assert_parses("*.ts").matches("foo.ts"));
        assert!(!assert_parses("*.ts").matches("foo/bar.ts"));
        assert!(assert_parses("a?c").matches("abc"));
        assert!(!assert_parses("a?c").matches("ac"));

        // `[]` declares a range of characters to match in a path segment.
        assert!(assert_parses("example.[0-9]").matches("example.0"));
        assert!(!assert_parses("example.[0-9]").matches("example.a"));
        // PORT: upstream parses but ignores `!` negation — [!0-9] behaves like [0-9].
        assert!(assert_parses("example.[!0-9]").matches("example.0"));

        // `{}` groups sub patterns into an OR expression.
        let g = assert_parses("**/*.{ts,js}");
        assert!(g.matches("a/b/c.ts"));
        assert!(g.matches("a/b/c.js"));
        assert!(!g.matches("a/b/c.rs"));
    }

    #[test]
    fn display_round_trip() {
        for pattern in ["a/**/b", "*.{ts,js}", "example.[0-9]", "a?c", "x/y"] {
            assert_eq!(assert_parses(pattern).to_string(), pattern);
        }
    }
}
