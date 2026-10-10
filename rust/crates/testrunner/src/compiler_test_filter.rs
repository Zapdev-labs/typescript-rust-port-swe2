// Ported from tsc/internal/testrunner/compiler_test_filter.go @ ec47d33c23e464a17cdf2475632cba629bee8763

/// `compilerTestFileFilter` builds the file-name predicate for the
/// `-test.run`-style pattern, extracting the subtest component after the
/// first `/` and using the compiled regexp's literal prefix for matching.
pub fn compiler_test_file_filter(pattern: &str) -> Box<dyn Fn(&str) -> bool> {
    let accept_all: Box<dyn Fn(&str) -> bool> = Box::new(|_| true);
    if compiler_test_name_needs_rewrite(pattern) {
        return accept_all;
    }
    let parts = split_compiler_test_filter(pattern);
    if parts.len() < 2 {
        return accept_all;
    }
    let component = &parts[1];
    let anchored = component.starts_with('^');
    let expression = component.strip_prefix('^').unwrap_or(component);
    let Ok(prefix) = literal_prefix(expression) else {
        return accept_all;
    };
    if prefix.is_empty()
        || compiler_test_name_needs_rewrite(&prefix)
        || (!anchored && !prefix.chars().any(|c| c.is_uppercase()))
    {
        return accept_all;
    }
    Box::new(move |filename: &str| {
        if compiler_test_name_needs_rewrite(filename) {
            return true;
        }
        if anchored {
            return filename.starts_with(&prefix) || prefix.starts_with(&format!("{filename}_"));
        }
        if filename.contains(&prefix) {
            return true;
        }
        // `for index := range filename` iterates rune-boundary byte offsets.
        for (index, _) in filename.char_indices() {
            if prefix.starts_with(&format!("{}_", &filename[index..])) {
                return true;
            }
        }
        false
    })
}

/// `compilerTestNameNeedsRewrite` — `strings.ContainsFunc(name, func(r) {
/// unicode.IsSpace(r) || !strconv.IsPrint(r) })`.
fn compiler_test_name_needs_rewrite(name: &str) -> bool {
    name.chars().any(|c| c.is_whitespace() || !is_go_print(c))
}

/// `strconv.IsPrint` — categories L, M, N, P, S plus ASCII space.
///
/// PORT: Rust has no general-category query on `char`, so non-ASCII
/// printability is approximated as "not a control or known format/unassigned
/// code point". The differences (unassigned Cn code points treated as
/// printable) only matter for bizarre `-test.run` patterns or test names,
/// where the fallback is `accept_all` anyway.
fn is_go_print(c: char) -> bool {
    if c.is_ascii() {
        return (' '..='~').contains(&c);
    }
    !c.is_control() && !is_go_non_print(c)
}

/// Common non-printable (Cf format, Cn noncharacter, Co private-use, Cs
/// surrogate-range — the last is unreachable through `char`) code point
/// ranges, approximating `!unicode.IsPrint`.
fn is_go_non_print(c: char) -> bool {
    matches!(c,
        '\u{00ad}'
        | '\u{0600}'..='\u{0605}'
        | '\u{061c}'
        | '\u{06dd}'
        | '\u{070f}'
        | '\u{180e}'
        | '\u{200b}'..='\u{200f}'
        | '\u{202a}'..='\u{202e}'
        | '\u{205f}'..='\u{2064}'
        | '\u{2066}'..='\u{206f}'
        | '\u{3000}'   // handled by IsSpace anyway; kept for clarity
        | '\u{e000}'..='\u{f8ff}'
        | '\u{feff}'
        | '\u{fff9}'..='\u{fffb}'
        | '\u{fffe}'..='\u{ffff}'
    )
}

/// `splitCompilerTestFilter` splits `pattern` on `/` separators that are not
/// nested inside a `(...)` group or `[...]` character class and not escaped.
/// Returns an empty vec (Go's `nil`) on a top-level `|`.
fn split_compiler_test_filter(pattern: &str) -> Vec<String> {
    let mut parts: Vec<String> = Vec::new();
    let mut start = 0usize;
    let mut depth = 0i32;
    let mut in_class = false;
    let mut escaped = false;
    for (index, c) in pattern.char_indices() {
        if escaped {
            escaped = false;
            continue;
        }
        if c == '\\' {
            escaped = true;
            continue;
        }
        if in_class {
            if c == ']' {
                in_class = false;
            }
            continue;
        }
        match c {
            '[' => in_class = true,
            '(' => depth += 1,
            ')' => depth -= 1,
            '|' => {
                if depth == 0 {
                    return Vec::new();
                }
            }
            '/' => {
                if depth == 0 {
                    parts.push(pattern[start..index].to_string());
                    start = index + 1;
                }
            }
            _ => {}
        }
    }
    parts.push(pattern[start..].to_string());
    parts
}

/// Hand-rolled equivalent of Go's `regexp.Compile(pattern)` +
/// `(*regexp.Regexp).LiteralPrefix()` for the RE2 syntax subset that matters
/// to test filters. Returns `Err(())` when the pattern is not a compilable
/// expression; otherwise the longest literal run Go's compiled program
/// reports as its mandatory match prefix.
///
/// Semantics mirrored from the compiled program's prefix walk:
///   - capture/non-capture groups are transparent (`(ab)c` -> "abc");
///   - an alternation inside a group ends the prefix at the `(` that opened
///     the group (the alternation instruction precedes the branch runes);
///   - `?flag` groups (e.g. `(?i)`) switch runes to fold-case matching, which
///     ends the prefix;
///   - character classes contribute their literal only when the class is a
///     single rune; `.`, `^`, `$`, escapes producing classes/anchors
///     (`\d`, `\w`, `\s`, `\b`, `\p`, ...), and repeats stop the prefix.
fn literal_prefix(pattern: &str) -> Result<String, ()> {
    #[derive(Clone, Copy, PartialEq)]
    enum Mode {
        Collect,
        Stop,
    }
    let mut prefix = String::new();
    let mut mode = Mode::Collect;
    // Byte offset in `prefix` where the enclosing `(` began; used to roll
    // back when the group turns out to contain an alternation.
    let mut group_prefix_stack: Vec<usize> = Vec::new();
    let mut chars = pattern.chars().peekable();

    macro_rules! push {
        ($c:expr) => {
            if mode == Mode::Collect {
                prefix.push($c)
            }
        };
    }

    while let Some(c) = chars.next() {
        match c {
            '\\' => {
                let Some(e) = chars.next() else {
                    return Err(());
                };
                match e {
                    'x' => {
                        let Some(r) = parse_hex_escape(&mut chars) else {
                            return Err(());
                        };
                        push!(r);
                    }
                    '0'..='7' => {
                        // \0 or octal \OOO — Go accepts up to 3 octal digits.
                        let mut value = e.to_digit(8).unwrap();
                        for _ in 0..2 {
                            match chars.peek().copied() {
                                Some(d @ '0'..='7') => {
                                    value = value * 8 + d.to_digit(8).unwrap();
                                    chars.next();
                                }
                                _ => break,
                            }
                        }
                        let r = char::from_u32(value).ok_or(())?;
                        push!(r);
                    }
                    'n' => push!('\n'),
                    'r' => push!('\r'),
                    't' => push!('\t'),
                    'f' => push!('\u{0c}'),
                    'v' => push!('\u{0b}'),
                    'a' => push!('\u{07}'),
                    'Q' => {
                        // \Q ... \E literal run.
                        loop {
                            match chars.next() {
                                None => break, // unterminated \Q: Go treats as literal-to-end
                                Some('\\') if chars.peek() == Some(&'E') => {
                                    chars.next();
                                    break;
                                }
                                Some(q) => push!(q),
                            }
                        }
                    }
                    'E' => {} // stray \E: no-op
                    // Class/anchor escapes contribute nothing literal.
                    'd' | 'D' | 's' | 'S' | 'w' | 'W' | 'b' | 'B' | 'A' | 'z' | 'p' | 'P' | 'C'
                    | 'h' | 'H' | 'K' | 'G' | 'X' | 'R' | 'k' | 'N' => mode = Mode::Stop,
                    // Escaped ASCII punctuation is a literal rune.
                    e if e.is_ascii_alphanumeric() => return Err(()),
                    e => push!(e),
                }
            }
            '.' | '^' | '$' | '*' | '+' | '?' => mode = Mode::Stop,
            '|' => {
                // Alternation: the compiled program places the branch
                // instruction at the group's `(` — roll the prefix back.
                if let Some(start) = group_prefix_stack.last() {
                    prefix.truncate(*start);
                } else {
                    prefix.clear();
                }
                mode = Mode::Stop;
            }
            '(' => {
                group_prefix_stack.push(prefix.len());
                if chars.peek() == Some(&'?') {
                    chars.next();
                    match chars.peek() {
                        // (?:...), (?P<name>...) and (?<name>...) are
                        // transparent groups.
                        Some(&':') => {
                            chars.next();
                        }
                        Some(&'P') => {
                            chars.next();
                            if chars.next() != Some('<') {
                                return Err(());
                            }
                            skip_group_name(&mut chars)?;
                        }
                        Some(&'<') => {
                            chars.next();
                            match chars.peek() {
                                // (?<= / (?<! lookbehind: Go rejects.
                                Some(&'=') | Some(&'!') => return Err(()),
                                _ => skip_group_name(&mut chars)?,
                            }
                        }
                        // Bare flag group (?i) or scoped (?i:...) — either
                        // way, fold-cased runes cannot join the prefix.
                        _ => {
                            // Validate: flag chars are [imsU-], then the group
                            // must end with `)` or open a `:` scope. Go errors
                            // on anything else (e.g. `(?=` lookahead).
                            let mut saw_flag = false;
                            while let Some(&f) = chars.peek() {
                                if matches!(f, 'i' | 'm' | 's' | 'U' | '-') {
                                    saw_flag = true;
                                    chars.next();
                                } else {
                                    break;
                                }
                            }
                            if !saw_flag || !matches!(chars.peek(), Some(&':') | Some(&')')) {
                                return Err(());
                            }
                            if chars.peek() == Some(&':') {
                                chars.next();
                            }
                            mode = Mode::Stop;
                        }
                    }
                }
            }
            ')' => {
                if group_prefix_stack.pop().is_none() {
                    return Err(()); // "unexpected )"
                }
            }
            '[' => {
                if !parse_char_class(&mut chars, &mut prefix, mode == Mode::Collect)? {
                    mode = Mode::Stop;
                }
            }
            '{' => {
                // `{n[,m]}` — a repeat. An invalid spec is a literal '{'
                // under Go's Perl syntax, so only stop when it parses.
                let mut probe = chars.clone();
                let mut digits = String::new();
                let mut valid = false;
                while let Some(p) = probe.next() {
                    match p {
                        '}' => {
                            valid = digits.chars().all(|d| d.is_ascii_digit() || d == ',')
                                && digits.chars().any(|d| d.is_ascii_digit());
                            break;
                        }
                        d if d.is_ascii_digit() || d == ',' => digits.push(d),
                        _ => break,
                    }
                }
                if valid {
                    chars = probe;
                    mode = Mode::Stop;
                } else {
                    push!('{');
                }
            }
            ']' | '}' => push!(c), // literal outside class/repeat
            c => push!(c),
        }
    }
    if !group_prefix_stack.is_empty() {
        return Err(()); // unclosed group
    }
    Ok(prefix)
}

/// Parses `\xHH` or `\x{HHHHHH}` after the `x`.
fn parse_hex_escape(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Option<char> {
    if chars.peek() == Some(&'{') {
        chars.next();
        let mut value: u32 = 0;
        let mut any = false;
        for c in chars.by_ref() {
            if c == '}' {
                return if any { char::from_u32(value) } else { None };
            }
            value = value.checked_mul(16)?.checked_add(c.to_digit(16)?)?;
            any = true;
        }
        return None;
    }
    let hi = chars.next()?.to_digit(16)?;
    let lo = chars.next()?.to_digit(16)?;
    char::from_u32(hi * 16 + lo)
}

/// Consumes a group name up to `>` in `(?P<name>...)` / `(?<name>...)`.
fn skip_group_name(chars: &mut std::iter::Peekable<std::str::Chars<'_>>) -> Result<(), ()> {
    for c in chars.by_ref() {
        if c == '>' {
            return Ok(());
        }
    }
    Err(())
}

/// Scans a `[...]` class (the `[` is already consumed). Returns
/// `Ok(literal)` where `literal` is true when the class collapses to a single
/// rune (pushed onto `prefix` when `collect`); `Err(())` on an unterminated
/// class.
fn parse_char_class(
    chars: &mut std::iter::Peekable<std::str::Chars<'_>>,
    prefix: &mut String,
    collect: bool,
) -> Result<bool, ()> {
    let mut first = true; // `]` as the very first class char is literal
    let mut single: Option<char> = None;
    let mut count = 0usize;
    while let Some(c) = chars.next() {
        match c {
            '\\' => {
                chars.next().ok_or(())?;
                count += 1;
            }
            ']' if !first => {
                if count == 1 && collect {
                    if let Some(r) = single {
                        prefix.push(r);
                    }
                }
                return Ok(count == 1);
            }
            _ => {
                if count == 0 {
                    single = Some(c);
                }
                count += 1;
            }
        }
        first = false;
    }
    Err(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `TestCompilerTestFileFilter`.
    #[test]
    fn test_compiler_test_file_filter() {
        // (name, pattern, filename, included) — mirrors the Go test table.
        let tests: &[(&str, &str, &str, bool)] = &[
            ("unfiltered", "", "other.ts", true),
            ("parentOnly", "TestLocal", "other.ts", true),
            (
                "filenamePrefix",
                "TestLocal/flakyDiagnostic1038",
                "flakyDiagnostic1038.ts",
                true,
            ),
            (
                "differentFilename",
                "TestLocal/flakyDiagnostic1038",
                "other.ts",
                false,
            ),
            (
                "substring",
                "TestLocal/Diagnostic1038",
                "flakyDiagnostic1038.ts",
                true,
            ),
            (
                "anchoredPrefix",
                "TestLocal/^lowercase",
                "lowercase.ts",
                true,
            ),
            (
                "anchoredMismatch",
                "TestLocal/^lowercase",
                "other.ts",
                false,
            ),
            (
                "unanchoredLowercaseFallback",
                "TestLocal/target",
                "other.ts",
                true,
            ),
            (
                "configuration",
                "TestLocal/^Example\\.ts_target=es2020$",
                "Example.ts",
                true,
            ),
            (
                "configurationSubstring",
                "TestLocal/Example\\.ts_target=es2020$",
                "someExample.ts",
                true,
            ),
            (
                "differentConfigurationFile",
                "TestLocal/^Example\\.ts_target=es2020$",
                "other.ts",
                false,
            ),
            (
                "spaceConfigurationFallback",
                "TestLocal/Example\\.ts target=es2020/error",
                "Example.ts",
                true,
            ),
            (
                "anchoredSpaceConfigurationFallback",
                "TestLocal/^Example\\.ts target=es2020$",
                "Example.ts",
                true,
            ),
            (
                "tabConfigurationFallback",
                "TestLocal/Example\\.ts\ttarget=es2020/error",
                "Example.ts",
                true,
            ),
            (
                "unicodeSpaceFallback",
                "TestLocal/^Example\u{00a0}Name",
                "Example_Name.ts",
                true,
            ),
            (
                "nonPrintablePatternFallback",
                "TestLocal/^Example\x00Name",
                "other.ts",
                true,
            ),
            (
                "escapedWhitespacePrefixFallback",
                "TestLocal/^Example\\x20Name",
                "other.ts",
                true,
            ),
            (
                "whitespaceFilenameFallback",
                "TestLocal/^Example_Name",
                "Example Name.ts",
                true,
            ),
            (
                "nonPrintableFilenameFallback",
                "TestLocal/^Example\\x00Name",
                "Example\x00Name.ts",
                true,
            ),
            (
                "nestedSubtest",
                "TestLocal/flakyDiagnostic1038/error",
                "flakyDiagnostic1038.ts",
                true,
            ),
            (
                "caseInsensitiveFallback",
                "TestLocal/(?i)Example",
                "other.ts",
                true,
            ),
            (
                "alternationFallback",
                "TestLocal/Example|TestLocal/Other",
                "Other.ts",
                true,
            ),
            (
                "groupFallback",
                "TestLocal/(Example|Other)",
                "Other.ts",
                true,
            ),
            (
                "groupedSlash",
                "TestLocal/(Example/Other)",
                "other.ts",
                false,
            ),
            ("classSlashFallback", "TestLocal/[A/B]", "other.ts", true),
            (
                "escapedSlash",
                "TestLocal/Example\\/Other",
                "other.ts",
                false,
            ),
            ("invalidExpressionFallback", "TestLocal/(", "other.ts", true),
            ("anchoredParent", "^TestLocal$/Example", "Example.ts", true),
        ];
        for (name, pattern, filename, included) in tests {
            assert_eq!(
                compiler_test_file_filter(pattern)(filename),
                *included,
                "{name}",
            );
        }
    }
}
