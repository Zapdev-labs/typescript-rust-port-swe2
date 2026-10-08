// Tests for the ported regexp engine (tsc/internal/scanner/regexp.go).
//
// scanner_test.go in the pinned Go tree has no regexp-specific tests (it only
// covers scanString/JSDoc/keyword paths owned by scanner.go), so these are new
// tests written against the Go semantics in regexp.go, asserting the emitted
// diagnostic text (with {0} placeholders unsubstituted), position, length, and
// args.

use tsc_core::options_generated::ScriptTarget;
use tsc_diagnostics::Message;

use super::{
    RegExpParser, RegularExpressionFlags, char_code_to_reg_exp_flag, scan_regular_expression_flags,
};

fn parse(
    pattern: &str,
    reg_exp_flags: RegularExpressionFlags,
    named_capture_groups: bool,
    script_target: ScriptTarget,
) -> Vec<String> {
    let text = pattern.as_bytes();
    let mut errors: Vec<String> = Vec::new();
    {
        let mut cb = |m: &'static Message, pos: usize, len: usize, args: &[String]| {
            errors.push(format!("{}@{pos}+{len}{args:?}", m.text()));
        };
        let mut parser = RegExpParser::new(
            text,
            0,
            text.len(),
            reg_exp_flags,
            named_capture_groups,
            script_target,
            Some(&mut cb),
        );
        parser.run();
    }
    errors
}

/// `/pattern/flags` — exercises the `scan_regular_expression_flags` entry plus
/// the parser over the body, mirroring `ReScanSlashToken`.
fn parse_literal(pattern: &str, flag_text: &str, script_target: ScriptTarget) -> Vec<String> {
    let text = format!("/{pattern}/{flag_text}");
    let text = text.as_bytes();
    let body_end = pattern.len() + 1;
    let mut errors: Vec<String> = Vec::new();
    {
        let mut cb = |m: &'static Message, pos: usize, len: usize, args: &[String]| {
            errors.push(format!("{}@{pos}+{len}{args:?}", m.text()));
        };
        let (flags, _p) = scan_regular_expression_flags(
            text,
            body_end + 1,
            text.len(),
            true,
            script_target,
            &mut cb,
        );
        // ReScanSlashToken's first pass for `namedCaptureGroups`.
        let mut named_capture_groups = false;
        let body = &text[1..body_end];
        let mut in_class = false;
        let mut in_escape = false;
        let mut i = 0;
        while i < body.len() {
            let ch = body[i];
            if in_escape {
                in_escape = false;
            } else if ch == b'\\' {
                in_escape = true;
            } else if ch == b'[' {
                in_class = true;
            } else if ch == b']' {
                in_class = false;
            } else if !in_class
                && ch == b'('
                && i + 2 < body.len()
                && body[i + 1] == b'?'
                && body[i + 2] == b'<'
                && (i + 3 >= body.len() || (body[i + 3] != b'=' && body[i + 3] != b'!'))
            {
                named_capture_groups = true;
            }
            i += 1;
        }
        let mut parser = RegExpParser::new(
            text,
            1,
            body_end,
            flags,
            named_capture_groups,
            script_target,
            Some(&mut cb),
        );
        parser.run();
    }
    errors
}

fn flags(s: &str) -> RegularExpressionFlags {
    let mut f = RegularExpressionFlags::NONE;
    for c in s.chars() {
        f |= char_code_to_reg_exp_flag(c as i32).unwrap();
    }
    f
}

const LATEST: ScriptTarget = ScriptTarget::LATEST;

#[test]
fn valid_patterns_have_no_errors() {
    for (pattern, f) in [
        ("abc|d*e?f+g?", ""),
        ("^\\b\\B$.", ""),
        ("(a|b)(?:c|d)(?=e)(?!f)(?<=g)(?<!h)", ""),
        ("(?<name>x)\\k<name>", ""),
        ("(a)\\1(b)(c)\\3", ""),
        ("[a-z]{2,4}", ""),
        ("[^\\d\\s\\w\\D\\S\\W]", ""),
        ("\\cA\\x41\\u0041\\n\\t\\v\\f\\r\\0", ""),
        ("(?<\\u0061>x)\\k<a>", ""), // group name via \u escape
        ("(?<\\uD840\\uDC00>x)\\k<\u{20000}>", ""), // surrogate-pair escape = literal char (U+20000, ID_Start)
        ("\\p{Script=Greek}\\p{ASCII}", "u"),
        ("\\p{gc=L}\\p{scx=Latin}", "u"),
        ("[\\uD83D\\uDE00-\\u{1F64F}]", "u"), // \uHigh\uLow combines in unicode mode
        ("\\u{1F600}", "u"),
        ("[\\q{a|bb|c}]", "v"),
        ("[\\w&&\\d]", "v"),
        ("[\\w--\\d]", "v"),
        ("[\\p{Basic_Emoji}]", "v"),
        ("(?i:x)(?im-s:x)", ""),
        ("x{0,}y{3}", ""),
    ] {
        let errors = parse(pattern, flags(f), pattern.contains("(?<"), LATEST);
        assert!(errors.is_empty(), "{pattern:?} flags={f:?}: {errors:?}");
    }
}

#[test]
fn quantifier_errors() {
    assert_eq!(
        parse("*a", flags(""), false, LATEST),
        ["There is nothing available for repetition.@0+1[]"]
    );
    // Annex B keeps `{` literal when no digits follow.
    assert!(parse("a{", flags(""), false, LATEST).is_empty());
    // Out-of-order is reported only when a '}' follows (or in unicode mode).
    assert_eq!(
        parse("a{2,1}", flags(""), false, LATEST),
        ["Numbers out of order in quantifier.@2+3[]"]
    );
    assert_eq!(
        parse("a{2,1}x", flags(""), false, LATEST),
        ["Numbers out of order in quantifier.@2+3[]"]
    );
    // Without a closing '}', Annex B treats `{...` as literal characters.
    assert!(parse("a{2,1x", flags(""), false, LATEST).is_empty());
    assert_eq!(
        parse("x{2}{3}", flags(""), false, LATEST),
        ["There is nothing available for repetition.@4+3[]"]
    );
    assert_eq!(
        parse("a{,}", flags("u"), false, LATEST),
        ["Incomplete quantifier. Digit expected.@2+0[]"]
    );
    assert_eq!(
        parse("a{3x", flags("u"), false, LATEST),
        ["'{0}' expected.@3+0[\"}\"]"]
    );
}

#[test]
fn named_group_errors() {
    assert_eq!(
        parse("\\k<a>", flags(""), false, LATEST),
        ["There is no capturing group named '{0}' in this regular expression.@3+1[\"a\"]"]
    );
    let errs = parse("(?<abce>x)\\k<abc>", flags(""), true, LATEST);
    assert_eq!(errs.len(), 2);
    assert!(errs[0].starts_with("There is no capturing group named '{0}'"));
    assert_eq!(errs[1], "Did you mean '{0}'?@13+3[\"abce\"]");
    // Same-name groups in one alternative are never allowed.
    assert_eq!(
        parse("(?<a>x)(?<a>y)", flags(""), true, LATEST),
        [
            "Named capturing groups with the same name must be mutually exclusive to each other.@10+1[]"
        ]
    );
    // Mutually exclusive alternatives: allowed at ES2025, reported below.
    assert_eq!(
        parse("(?<a>x)|(?<a>y)", flags(""), true, ScriptTarget::ES2024),
        [
            "Duplicate named capturing groups are only available when targeting '{0}' or later.@11+1[\"es2025\"]"
        ]
    );
    assert!(parse("(?<a>x)|(?<a>y)", flags(""), true, LATEST).is_empty());
    // `(?<=` and `(?<!` are lookbehind, not named groups.
    assert!(parse("(?<=a)(?<!b)", flags(""), false, LATEST).is_empty());
}

#[test]
fn group_name_version_gate() {
    assert_eq!(
        parse("(?<a>x)", flags(""), true, ScriptTarget::ES2017),
        ["Named capturing groups are only available when targeting 'ES2018' or later.@2+3[]"]
    );
}

#[test]
fn pattern_modifier_errors() {
    assert_eq!(
        parse("(?i:x)", flags(""), false, ScriptTarget::ES2024),
        [
            "Regular expression pattern modifiers are only available when targeting '{0}' or later.@2+1[\"es2025\"]"
        ]
    );
    assert!(parse("(?i:x)", flags(""), false, LATEST).is_empty());
    assert_eq!(
        parse("(?-:x)", flags(""), false, LATEST),
        ["Subpattern flags must be present when there is a minus sign.@2+1[]"]
    );
    assert_eq!(
        parse("(?ii:x)", flags(""), false, LATEST),
        ["Duplicate regular expression flag.@3+1[]"]
    );
    assert_eq!(
        parse("(?g:x)", flags(""), false, LATEST),
        ["This regular expression flag cannot be toggled within a subpattern.@2+1[]"]
    );
    assert_eq!(
        parse("(?z:x)", flags(""), false, LATEST),
        ["Unknown regular expression flag.@2+1[]"]
    );
}

#[test]
fn flag_scanning_errors() {
    assert_eq!(
        parse_literal("x", "z", LATEST),
        ["Unknown regular expression flag.@3+1[]"]
    );
    assert_eq!(
        parse_literal("x", "gg", LATEST),
        ["Duplicate regular expression flag.@4+1[]"]
    );
    assert_eq!(
        parse_literal("x", "uv", LATEST),
        ["The Unicode (u) flag and the Unicode Sets (v) flag cannot be set simultaneously.@4+1[]"]
    );
    assert_eq!(
        parse_literal("x", "d", ScriptTarget::ES2021),
        [
            "This regular expression flag is only available when targeting '{0}' or later.@3+1[\"es2022\"]"
        ]
    );
    assert_eq!(
        parse_literal("x", "dgimsuvy", LATEST),
        ["The Unicode (u) flag and the Unicode Sets (v) flag cannot be set simultaneously.@9+1[]"]
    );
}

#[test]
fn class_errors() {
    assert_eq!(
        parse("[z-a]", flags(""), false, LATEST),
        ["Range out of order in character class.@1+3[]"]
    );
    assert_eq!(
        parse("[\\d-z]", flags("u"), false, LATEST),
        ["A character class range must not be bounded by another character class.@1+2[]"]
    );
    assert_eq!(
        parse("[\\8]", flags(""), false, LATEST),
        ["Decimal escape sequences and backreferences are not allowed in a character class.@1+2[]"]
    );
    assert_eq!(
        parse("[\\1]", flags(""), false, LATEST),
        [
            "Octal escape sequences and backreferences are not allowed in a character class. If this was intended as an escape sequence, use the syntax '{0}' instead.@1+2[\"\\\\x01\"]"
        ]
    );
}

#[test]
fn class_set_expression_errors() {
    assert_eq!(
        parse("[\\w&&\\d--x]", flags("v"), false, LATEST),
        [
            "Operators must not be mixed within a character class. Wrap it in a nested class instead.@7+2[]"
        ]
    );
    assert_eq!(
        parse("[--a]", flags("v"), false, LATEST),
        ["Expected a class set operand.@1+0[]"]
    );
    // Reserved double punctuator.
    assert_eq!(
        parse("[!!]", flags("v"), false, LATEST),
        [
            "A character class must not contain a reserved double punctuator. Did you mean to escape it with backslash?@1+2[]"
        ]
    );
    // A negated class may not contain strings.
    assert_eq!(
        parse("[^\\q{ab}]", flags("v"), false, LATEST),
        [
            "Anything that would possibly match more than a single character is invalid inside a negated character class.@2+6[]"
        ]
    );
}

#[test]
fn unicode_property_errors() {
    assert_eq!(
        parse("\\p{L}", flags(""), false, LATEST),
        [
            "Unicode property value expressions are only available when the Unicode (u) flag or the Unicode Sets (v) flag is set.@0+5[]"
        ]
    );
    assert_eq!(
        parse("\\p{Nope}", flags("u"), false, LATEST),
        ["Unknown Unicode property name or value.@3+4[]"]
    );
    assert_eq!(
        parse("\\p{gc=Nope}", flags("u"), false, LATEST),
        ["Unknown Unicode property value.@6+4[]"]
    );
    assert_eq!(
        parse("\\p{bad=X}", flags("u"), false, LATEST),
        ["Unknown Unicode property name.@3+3[]"]
    );
    // Property-of-strings values need the v flag.
    assert_eq!(
        parse("\\p{Basic_Emoji}", flags("u"), false, LATEST),
        [
            "Any Unicode property that would possibly match more than a single character is only available when the Unicode Sets (v) flag is set.@3+11[]"
        ]
    );
    // ... and can't be negated.
    assert_eq!(
        parse("\\P{Basic_Emoji}", flags("v"), false, LATEST),
        [
            "Anything that would possibly match more than a single character is invalid inside a negated character class.@3+11[]"
        ]
    );
}

#[test]
fn escape_errors() {
    assert_eq!(
        parse("\\k", flags(""), true, LATEST),
        ["'\\k' must be followed by a capturing group name enclosed in angle brackets.@0+2[]"]
    );
    // Annex B: \8 is a DecimalEscape (not octal), so the backreference
    // diagnostic fires, just like \1..\9.
    assert_eq!(
        parse("\\8", flags(""), false, LATEST),
        [
            "This backreference refers to a group that does not exist. There are no capturing groups in this regular expression.@1+1[]"
        ]
    );
    // Annex B: `\c` in an atom escape falls back to a literal backslash + 'c'.
    assert!(parse("\\c", flags(""), false, LATEST).is_empty());
    assert_eq!(
        parse("\\u{1F600}", flags(""), false, LATEST),
        [
            "Unicode escape sequences are only available when the Unicode (u) flag or the Unicode Sets (v) flag is set.@0+9[]"
        ]
    );
    assert_eq!(
        parse("a\\", flags(""), false, LATEST),
        ["Undetermined character escape.@1+1[]"]
    );
}

#[test]
fn backreference_errors() {
    assert_eq!(
        parse("\\1", flags(""), false, LATEST),
        [
            "This backreference refers to a group that does not exist. There are no capturing groups in this regular expression.@1+1[]"
        ]
    );
    assert_eq!(
        parse("(a)\\2", flags(""), false, LATEST),
        [
            "This backreference refers to a group that does not exist. There are only {0} capturing groups in this regular expression.@4+1[\"1\"]"
        ]
    );
    assert!(parse("(a)\\1", flags(""), false, LATEST).is_empty());
}

#[test]
fn unexpected_chars() {
    assert_eq!(
        parse("a)", flags(""), false, LATEST),
        ["Unexpected '{0}'. Did you mean to escape it with backslash?@1+1[\")\"]"]
    );
    // Annex B silently accepts ']' and '}' outside a class.
    assert!(parse("a]b}", flags(""), false, LATEST).is_empty());
    assert_eq!(
        parse("a]", flags("u"), false, LATEST),
        ["Unexpected '{0}'. Did you mean to escape it with backslash?@1+1[\"]\"]"]
    );
}
