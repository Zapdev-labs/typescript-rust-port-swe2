// Ported from tsc/internal/testutil/tsbaseline/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: the Go `regexp` globals are inlined as plain `str` operations —
// `lineDelimiter`/`codeLinesRegexp`/`lineEndRegex` splits become
// `split_lines`-style loops, `nonWhitespace` becomes a char check, and the
// `testPath*` regexes become `replace`/`contains` passes. No `regex`
// dependency is added.

use tsc_tspath as tspath;

/// `testPathPrefixReplacer`.
const TEST_PATH_PREFIX_PAIRS: &[(&str, &str)] = &[
    ("/.ts/", ""),
    ("/.lib/", ""),
    ("/.src/", ""),
    ("bundled:///libs/", ""),
    ("file:///./ts/", "file:///"),
    ("file:///./lib/", "file:///"),
    ("file:///./src/", "file:///"),
];

/// `testPathTrailingReplacerTrailingSeparator`.
const TEST_PATH_TRAILING_PAIRS: &[(&str, &str)] = &[
    ("/.ts/", "/"),
    ("/.lib/", "/"),
    ("/.src/", "/"),
    ("bundled:///libs/", "/"),
    ("file:///./ts/", "file:///"),
    ("file:///./lib/", "file:///"),
    ("file:///./src/", "file:///"),
];

/// `strings.NewReplacer` semantics: a single left-to-right pass where, at
/// each position, the first matching old string is replaced. (Go applies
/// the same algorithm.)
fn multi_replace(text: &str, pairs: &[(&str, &str)]) -> String {
    let mut out = String::with_capacity(text.len());
    let mut i = 0;
    'outer: while i < text.len() {
        for (old, new) in pairs {
            if text[i..].starts_with(old) {
                out.push_str(new);
                i += old.len();
                continue 'outer;
            }
        }
        // Push the byte at i; pairs are all ASCII so splitting a multi-byte
        // char here cannot match later — copy the whole char.
        let ch_len = text[i..].chars().next().map(char::len_utf8).unwrap_or(1);
        out.push_str(&text[i..i + ch_len]);
        i += ch_len;
    }
    out
}

/// `removeTestPathPrefixes`.
pub(crate) fn remove_test_path_prefixes(
    text: &str,
    retain_trailing_directory_separator: bool,
) -> String {
    if retain_trailing_directory_separator {
        return multi_replace(text, TEST_PATH_TRAILING_PAIRS);
    }
    multi_replace(text, TEST_PATH_PREFIX_PAIRS)
}

/// `isDefaultLibraryFile`.
pub(crate) fn is_default_library_file(file_path: &str) -> bool {
    let file_name = tspath::get_base_file_name(file_path);
    file_name.starts_with("lib.") && file_name.ends_with(tspath::EXTENSION_DTS)
}

/// `isBuiltFile`.
pub(crate) fn is_built_file(file_path: &str) -> bool {
    file_path.starts_with("built/local/")
        || file_path.starts_with(&*tspath::ensure_trailing_directory_separator("/.ts"))
}

/// `isTsConfigFile`.
pub(crate) fn is_tsconfig_file(path: &str) -> bool {
    // !!! fix to check for just prefixes/suffixes
    path.contains("tsconfig") && path.contains("json")
}

/// `testPathCharacters` — `[\^<>:"|?*%]`.
fn replace_test_path_characters(name: &str) -> String {
    name.chars()
        .map(|c| {
            if matches!(c, '^' | '<' | '>' | ':' | '"' | '|' | '?' | '*' | '%') {
                '_'
            } else {
                c
            }
        })
        .collect()
}

/// `sanitizeTestFilePath`.
pub(crate) fn sanitize_test_file_path(name: &str) -> String {
    let path = replace_test_path_characters(name);
    let path = tspath::normalize_slashes(&path);
    let path = path.replace("../", "__dotdot/");
    let path = tspath::normalize_path(&path);
    let path = tspath::CaseSensitivity::CaseInsensitive.canonicalize(&path);
    path.trim_start_matches('/').to_string()
}

/// `ansiEscape` — `\x1b\[[0-9;]*m` ANSI escape sequence stripping.
pub(crate) fn strip_ansi_escapes(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == 0x1b && i + 1 < bytes.len() && bytes[i + 1] == b'[' {
            // scan [0-9;]* then 'm'
            let mut j = i + 2;
            while j < bytes.len() && (bytes[j].is_ascii_digit() || bytes[j] == b';') {
                j += 1;
            }
            if j < bytes.len() && bytes[j] == b'm' {
                i = j + 1;
                continue;
            }
        }
        let ch_len = text[i..].chars().next().map(char::len_utf8).unwrap_or(1);
        out.push_str(&text[i..i + ch_len]);
        i += ch_len;
    }
    out
}

/// `codeLinesRegexp` — splits on `[\r\u2028\u2029]|\r?\n`. Go's alternation
/// is leftmost-first, so `\r` matches the character class before `\r?\n`
/// can consume a CRLF — a CRLF therefore yields an empty line between the
/// two delimiters.
pub(crate) fn split_code_lines(content: &str) -> Vec<&str> {
    let mut lines = Vec::new();
    let bytes = content.as_bytes();
    let mut start = 0;
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'\n' | b'\r' => {
                lines.push(&content[start..i]);
                i += 1;
                start = i;
            }
            // U+2028 (E2 80 A8) and U+2029 (E2 80 A9)
            0xe2 if i + 2 < bytes.len()
                && bytes[i + 1] == 0x80
                && (bytes[i + 2] == 0xa8 || bytes[i + 2] == 0xa9) =>
            {
                lines.push(&content[start..i]);
                i += 3;
                start = i;
            }
            _ => {
                i += content[i..].chars().next().map(char::len_utf8).unwrap_or(1);
            }
        }
    }
    // Go's regexp.Split with n=-1 yields a trailing empty string when the
    // content ends with a delimiter.
    lines.push(&content[start..]);
    lines
}

/// `lineDelimiter` (`\r?\n`) `.ReplaceAllString(text, "")` — strips each
/// CRLF or lone LF.
pub(crate) fn strip_line_delimiters(text: &str) -> String {
    text.replace("\r\n", "").replace('\n', "")
}

/// `bracketLineRegex` — `^\s*[{|}]\s*$` (Go's character class includes a
/// literal `|`).
pub(crate) fn is_bracket_line(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.len() == 1 && matches!(trimmed.as_bytes()[0], b'{' | b'|' | b'}')
}

/// `base64.StdEncoding.EncodeToString` — minimal local copy (Go wraps the
/// payload in `url.QueryEscape`/`QueryUnescape`, which round-trips to the
/// identity).
pub(crate) fn base64_encode_chunk(s: &str) -> String {
    const ALPHABET: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let data = s.as_bytes();
    let mut out = String::with_capacity(data.len().div_ceil(3) * 4);
    for chunk in data.chunks(3) {
        let b0 = u32::from(chunk[0]);
        let b1 = u32::from(*chunk.get(1).unwrap_or(&0));
        let b2 = u32::from(*chunk.get(2).unwrap_or(&0));
        let n = (b0 << 16) | (b1 << 8) | b2;
        out.push(ALPHABET[((n >> 18) & 63) as usize] as char);
        out.push(ALPHABET[((n >> 12) & 63) as usize] as char);
        out.push(if chunk.len() > 1 {
            ALPHABET[((n >> 6) & 63) as usize] as char
        } else {
            '='
        });
        out.push(if chunk.len() > 2 {
            ALPHABET[(n & 63) as usize] as char
        } else {
            '='
        });
    }
    out
}
