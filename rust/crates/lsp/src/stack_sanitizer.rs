// Ported from tsc/internal/lsp @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `genericSecretKeywordRegex` (Go `regexp`) is a hand-rolled scan — no
//   regex dep per repo rules (same approach as `diagnostics::format`). Go's
//   `(?i)` is Unicode simple case folding; this uses ASCII
//   case-insensitivity, identical for the ASCII-only frames we emit.
// - `strings.Lines` (elements keep their trailing newline) → `str::lines`:
//   the newline only ever sits in the portion that is trimmed or dropped
//   (`line[:i]` is leading whitespace only), so the emitted text is
//   identical — including `\r`, which `lines` strips and Go's
//   `strings.TrimSpace` in `writeSanitizedModuleOrPath` strips anyway.
// - `strings.Builder` → `String`; `strings.Index`/`LastIndex` →
//   `str::find`/`rfind` (all matches here are on ASCII needles, so byte
//   indices stay on char boundaries).

// VS Code's telemetry pipeline redacts any string matching
// /(key|token|sig|secret|signature|password|passwd|pwd|android:value)[^a-zA-Z0-9]/i
// as `<REDACTED: Generic Secret>`, which trips on innocuous Go frames like
// `getSignatureHelp(`. Insert `X_X` after each trigger keyword that we know
// can appear in our sanitized output, when followed by punctuation we
// actually emit (`(`, `[`, `.`, `|`); reverse by removing the marker (replace
// `X_X` with the empty string) on the dashboard.
//
// `(?i)(key|token|signature|sig|pwd)([(\[.|])` — alternation order is
// preserved from Go even though `signature`/`sig` can never both match at
// the same position (`sig` would need punctuation at the `n`).
const GENERIC_SECRET_KEYWORDS: &[&[u8]] = &[b"key", b"token", b"signature", b"sig", b"pwd"];
const GENERIC_SECRET_PUNCT: &[u8] = &[b'(', b'[', b'.', b'|'];

fn defeat_generic_secret_regex(s: &str) -> String {
    // `genericSecretKeywordRegex.ReplaceAllString(s, "${1}X_X${2}")` —
    // leftmost-first scan: emit up to and including the matched keyword
    // (original case preserved, like `${1}`), insert `X_X`, and let the
    // punctuation flow through with the next emitted span.
    let bytes = s.as_bytes();
    let mut result = String::with_capacity(s.len() + 8);
    let mut last = 0; // start of the not-yet-emitted span
    let mut i = 0; // scan position
    while i < bytes.len() {
        let mut matched = false;
        for kw in GENERIC_SECRET_KEYWORDS {
            if i + kw.len() < bytes.len()
                && bytes[i..i + kw.len()].eq_ignore_ascii_case(kw)
                && GENERIC_SECRET_PUNCT.contains(&bytes[i + kw.len()])
            {
                // `i` is an ASCII keyword start and the match ends before
                // ASCII punctuation, so both slice ends are char boundaries.
                result.push_str(&s[last..i + kw.len()]);
                result.push_str("X_X");
                last = i + kw.len();
                i += kw.len();
                matched = true;
                break;
            }
        }
        if !matched {
            i += 1;
        }
    }
    result.push_str(&s[last..]);
    result
}

/// `func sanitizeStackTrace(stack string) string`
pub(crate) fn sanitize_stack_trace(stack: &str) -> String {
    // TODO: should we just look for the first '(' and
    // just strip everything before the prior newline?
    let Some(start_index) = stack.find("runtime/debug.Stack()") else {
        return String::new();
    };
    let stack = &stack[start_index..];

    let mut result = String::new();

    for (line_num, line) in stack.lines().enumerate() {
        if line_num > 0 {
            result.push('\n');
        }

        // Skip whitespace
        let bytes = line.as_bytes();
        let mut i = 0;
        while i < bytes.len() && (bytes[i] == b' ' || bytes[i] == b'\t') {
            i += 1;
        }

        result.push_str(&line[..i]);
        let line = &line[i..];

        match line.find("TypeScript/tsc/") {
            Some(our_module_index) => {
                write_sanitized_module_or_path(&line[our_module_index..], &mut result);
            }
            None => result.push_str("(REDACTED FRAME)"),
        }
    }

    defeat_generic_secret_regex(&result)
}

/// `func writeSanitizedModuleOrPath(line string, result *strings.Builder)`
fn write_sanitized_module_or_path(line: &str, result: &mut String) {
    // We don't expect things like \r, but it doesn't hurt to trim just in case.
    let mut line = line.trim();

    if let Some(plus_hex) = line.find(" +0x") {
        line = &line[..plus_hex];
    } else if let Some(in_goroutine) = line.rfind(" in goroutine ") {
        line = &line[..in_goroutine];
    }

    for (segment_index, segment) in line.split('/').enumerate() {
        if segment_index > 0 {
            result.push_str("|>");
        }

        // See if the string ends with ), and strip out all the arguments.
        if segment.ends_with(')') {
            let Some(open_paren_index) = segment.rfind('(') else {
                // Closing parenthesis, but no opening - bail out.
                result.push_str("???");
                continue;
            };
            result.push_str(&segment[..open_paren_index]);
            result.push_str("()");
            continue;
        }

        result.push_str(segment);
    }
}
