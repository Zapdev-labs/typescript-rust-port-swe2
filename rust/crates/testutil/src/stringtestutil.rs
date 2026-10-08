// Ported from tsc/internal/testutil/stringtestutil/stringtestutil.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go strings are arbitrary bytes, and source text in this codebase can
// carry tsc-stringutil's CESU-8 lone-surrogate sentinels (invalid UTF-8), so
// `Dedent` operates on `&[u8]`/`Vec<u8>`. Rune-classifying helpers decode
// UTF-8 the way Go's `utf8.DecodeRune` does: an invalid encoding consumes one
// byte and classifies as non-whitespace (Go yields RuneError, which is not
// white-space-like and not unicode.IsSpace).

use tsc_stringutil as stringutil;

/// decode_rune decodes the first UTF-8 rune, mirroring Go's
/// `utf8.DecodeRuneInString`: returns (rune, width); invalid encodings
/// return (None, 1), the RuneError analog. Surrogate encodings
/// (CESU-8 sentinels) and overlongs are invalid.
fn decode_rune(bytes: &[u8]) -> (Option<char>, usize) {
    let Some(&b0) = bytes.first() else {
        return (None, 0);
    };
    if b0 < 0x80 {
        return (Some(b0 as char), 1);
    }
    let width = match b0 {
        0xC0..=0xDF => 2,
        0xE0..=0xEF => 3,
        0xF0..=0xF7 => 4,
        _ => return (None, 1),
    };
    if bytes.len() < width {
        return (None, 1);
    }
    match std::str::from_utf8(&bytes[..width]) {
        Ok(s) => match s.chars().next() {
            Some(c) if c.len_utf8() == width => (Some(c), width),
            _ => (None, 1),
        },
        Err(_) => (None, 1),
    }
}

/// strings.IndexFunc(line, !IsWhiteSpaceLike): byte index of the first rune
/// that is not white-space-like, or None.
fn first_non_whitespace_index(line: &[u8]) -> Option<usize> {
    let mut i = 0;
    while i < line.len() {
        let (r, size) = decode_rune(&line[i..]);
        match r {
            Some(c) if stringutil::is_white_space_like(c) => i += size,
            // RuneError (None) and non-whitespace runes end the scan.
            _ => return Some(i),
        }
    }
    None
}

/// strings.TrimSpace: trims leading and trailing unicode.IsSpace runes.
/// Rust `char::is_whitespace` is the Unicode White_Space property, the same
/// set Go's `unicode.IsSpace` reports.
fn trim_space(s: &[u8]) -> &[u8] {
    let mut i = 0;
    while i < s.len() {
        let (r, size) = decode_rune(&s[i..]);
        match r {
            Some(c) if c.is_whitespace() => i += size,
            _ => break,
        }
    }
    let s = &s[i..];
    let mut j = 0;
    let mut end = 0;
    while j < s.len() {
        let (r, size) = decode_rune(&s[j..]);
        match r {
            Some(c) if c.is_whitespace() => {}
            _ => end = j + size,
        }
        j += size;
    }
    &s[..end]
}

/// Dedent removes the common leading indentation (after converting leading
/// tabs to four spaces each) and drops blank lines at the start and end.
pub fn dedent(text: &[u8]) -> Vec<u8> {
    let mut lines: Vec<Vec<u8>> = text.split(|&b| b == b'\n').map(|l| l.to_vec()).collect();
    // Remove blank lines in the beginning and end
    // and convert all tabs in the beginning of line to spaces
    let mut start_line: Option<usize> = None;
    let mut last_line = 0usize;
    for (i, line) in lines.iter_mut().enumerate() {
        if let Some(first_non_white) = first_non_whitespace_index(line) {
            if first_non_white > 0 {
                // strings.ReplaceAll(line[0:firstNonWhite], "\t", "    ")
                let mut new_line = Vec::with_capacity(line.len() + first_non_white * 3);
                for &b in &line[..first_non_white] {
                    if b == b'\t' {
                        new_line.extend_from_slice(b"    ");
                    } else {
                        new_line.push(b);
                    }
                }
                new_line.extend_from_slice(&line[first_non_white..]);
                *line = new_line;
            }
        }
        if !trim_space(line).is_empty() {
            if start_line.is_none() {
                start_line = Some(i);
            }
            last_line = i;
        }
    }
    // Go: lines[startLine : lastLine+1] — a -1 start index panics, so an
    // all-blank input panics identically here.
    let lines = &mut lines[start_line.expect("dedent: text was entirely blank")..last_line + 1];
    let mut mapped_lines: Vec<&[u8]> = Vec::with_capacity(lines.len());
    for line in lines.iter() {
        if trim_space(line).is_empty() {
            mapped_lines.push(b"");
        } else {
            mapped_lines.push(line);
        }
    }
    let indentation = stringutil::guess_indentation(&mapped_lines);
    if indentation > 0 {
        let indentation = indentation as usize;
        for line in lines.iter_mut() {
            if line.len() > indentation {
                *line = line[indentation..].to_vec();
            } else {
                line.clear();
            }
        }
    }
    lines.join(&b"\n"[..])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dedent_removes_common_indentation() {
        assert_eq!(
            dedent(b"\n    foo\n      bar\n    \n"),
            b"foo\n  bar".to_vec()
        );
    }

    #[test]
    fn dedent_converts_leading_tabs_to_spaces() {
        // "\tfoo" -> "    foo", "\t\tbar" -> "        bar"; common indent 4.
        assert_eq!(dedent(b"\tfoo\n\t\tbar"), b"foo\n    bar".to_vec());
    }

    #[test]
    fn dedent_preserves_blank_lines_inside() {
        assert_eq!(dedent(b"  a\n\n  b"), b"a\n\nb".to_vec());
    }

    #[test]
    fn dedent_no_indentation() {
        assert_eq!(dedent(b"foo\nbar"), b"foo\nbar".to_vec());
    }

    #[test]
    #[should_panic]
    fn dedent_all_blank_panics() {
        // Go: lines[startLine:lastLine+1] with startLine == -1 panics.
        dedent(b"   \n\t\n");
    }

    #[test]
    fn trim_space_runes() {
        assert_eq!(trim_space("  a\u{00A0} ".as_bytes()), b"a".as_slice());
        assert_eq!(trim_space(b""), b"".as_slice());
        // Invalid byte (like a CESU-8 sentinel fragment) is not whitespace.
        assert_eq!(trim_space(&[0xEDu8, 0xA0, 0x80]), &[0xEDu8, 0xA0, 0x80][..]);
    }
}
