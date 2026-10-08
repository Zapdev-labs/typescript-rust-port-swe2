// Ported from tsc/internal/semver/version_range.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;

use crate::version::{Version, get_uint_component, qualifier_run_len, version_zero};

// https://github.com/npm/node-semver#range-grammar
//
// range-set    ::= range ( logical-or range ) *
// range        ::= hyphen | simple ( ' ' simple ) * | ''
// logical-or   ::= ( ' ' ) * '||' ( ' ' ) *
//
// PORT: `logicalOrRegExp = regexp.MustCompile(`\|\|`)` splits on the literal "||"
// (str::split("||") is equivalent), and `whitespaceRegExp = regexp.MustCompile(`\s+`)`
// is `whitespace_reg_exp_split` below — Go regexp `\s` is exactly [\t\n\f\r ].

// PORT helper: Go regexp `\s` is the ASCII class [\t\n\f\r ] (notably excluding '\v',
// unlike strings.TrimSpace/unicode whitespace).
fn is_go_regexp_space(b: u8) -> bool {
    matches!(b, b'\t' | b'\n' | b'\x0C' | b'\r' | b' ')
}

// whitespaceRegExp.Split(text, -1): the pieces between runs of `\s`, including the
// empty pieces at the edges that Go's Split produces.
fn whitespace_reg_exp_split(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut pieces = Vec::new();
    let mut start = 0;
    let mut i = 0;
    while i < bytes.len() {
        if is_go_regexp_space(bytes[i]) {
            pieces.push(&text[start..i]);
            while i < bytes.len() && is_go_regexp_space(bytes[i]) {
                i += 1;
            }
            start = i;
        } else {
            i += 1;
        }
    }
    pieces.push(&text[start..]);
    pieces
}

fn trim_go_regexp_space_start(s: &str) -> &str {
    let bytes = s.as_bytes();
    let mut i = 0;
    while i < bytes.len() && is_go_regexp_space(bytes[i]) {
        i += 1;
    }
    &s[i..]
}

// https://github.com/npm/node-semver#range-grammar
//
// partial      ::= xr ( '.' xr ( '.' xr qualifier ? )? )?
// xr           ::= 'x' | 'X' | '*' | nr
// nr           ::= '0' | ['1'-'9'] ( ['0'-'9'] ) *
// qualifier    ::= ( '-' pre )? ( '+' build )?
// pre          ::= parts
// build        ::= parts
// parts        ::= part ( '.' part ) *
// part         ::= nr | [-0-9A-Za-z]+
//
//   partialRegExp = `(?i)^([x*0]|[1-9]\d*)(?:\.([x*0]|[1-9]\d*)(?:\.([x*0]|[1-9]\d*)(?:-([a-z0-9-.]+))?(?:\+([a-z0-9-.]+))?)?)?$`
fn partial_reg_exp_match(text: &str) -> Option<[&str; 5]> {
    let (major, mut rest) = match_xr(text)?;
    let mut matched = [major, "", "", "", ""];
    if let Some(after_dot) = rest.strip_prefix('.') {
        (matched[1], rest) = match_xr(after_dot)?;
        if let Some(after_dot) = rest.strip_prefix('.') {
            (matched[2], rest) = match_xr(after_dot)?;
            if let Some(after_dash) = rest.strip_prefix('-') {
                let len = qualifier_run_len(after_dash);
                if len == 0 {
                    return None;
                }
                matched[3] = &after_dash[..len];
                rest = &after_dash[len..];
            }
            if let Some(after_plus) = rest.strip_prefix('+') {
                let len = qualifier_run_len(after_plus);
                if len == 0 {
                    return None;
                }
                matched[4] = &after_plus[..len];
                rest = &after_plus[len..];
            }
        }
    }
    if !rest.is_empty() {
        return None;
    }
    Some(matched)
}

// PORT helper: the `[x*0]|[1-9]\d*` alternation used by partialRegExp. Returns the
// matched text and the unconsumed remainder.
fn match_xr(s: &str) -> Option<(&str, &str)> {
    match s.as_bytes().first()? {
        b'x' | b'X' | b'*' | b'0' => Some((&s[..1], &s[1..])),
        b'1'..=b'9' => {
            let len = s.bytes().take_while(|b| b.is_ascii_digit()).count();
            Some((&s[..len], &s[len..]))
        }
        _ => None,
    }
}

// PORT helper: the `[a-z0-9-+.*]` operand class (case-insensitive) shared by
// hyphenRegExp and rangeRegExp — ASCII alphanumerics plus '-', '+', '.', '*'.
fn is_range_operand_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'-' || b == b'+' || b == b'.' || b == b'*'
}

// https://github.com/npm/node-semver#range-grammar
//
// hyphen       ::= partial ' - ' partial
//
//   hyphenRegExp = `(?i)^\s*([a-z0-9-+.*]+)\s+-\s+([a-z0-9-+.*]+)\s*$`
//
// PORT: the left operand class includes '-', so the greedy first group is matched
// with the same backtracking order as the regex (longest first).
fn hyphen_reg_exp_match(text: &str) -> Option<(&str, &str)> {
    let bytes = text.as_bytes();
    let mut start = 0;
    while start < bytes.len() && is_go_regexp_space(bytes[start]) {
        start += 1;
    }
    let mut end = start;
    while end < bytes.len() && is_range_operand_char(bytes[end]) {
        end += 1;
    }
    for left_end in (start + 1..=end).rev() {
        let mut i = left_end;
        // \s+
        let ws_start = i;
        while i < bytes.len() && is_go_regexp_space(bytes[i]) {
            i += 1;
        }
        if i == ws_start {
            continue;
        }
        // '-'
        if i >= bytes.len() || bytes[i] != b'-' {
            continue;
        }
        i += 1;
        // \s+
        let ws_start = i;
        while i < bytes.len() && is_go_regexp_space(bytes[i]) {
            i += 1;
        }
        if i == ws_start {
            continue;
        }
        // [a-z0-9-+.*]+
        let right_start = i;
        while i < bytes.len() && is_range_operand_char(bytes[i]) {
            i += 1;
        }
        if i == right_start {
            continue;
        }
        let right_end = i;
        // \s*$
        while i < bytes.len() && is_go_regexp_space(bytes[i]) {
            i += 1;
        }
        if i == bytes.len() {
            return Some((&text[start..left_end], &text[right_start..right_end]));
        }
    }
    None
}

// https://github.com/npm/node-semver#range-grammar
//
// simple       ::= primitive | partial | tilde | caret
// primitive    ::= ( '<' | '>' | '>=' | '<=' | '=' ) partial
// tilde        ::= '~' partial
// caret        ::= '^' partial
//
//   rangeRegExp = `(?i)^([~^<>=]|<=|>=)?\s*([a-z0-9-+.*]+)$`
//
// PORT: the alternation is tried in leftmost-first order — the single-char class
// [~^<>=], then "<=", then ">=", then the empty alternative.
fn range_reg_exp_match(text: &str) -> Option<(&str, &str)> {
    let mut operators: [&str; 4] = ["", "<=", ">=", ""];
    if let Some(&first) = text.as_bytes().first() {
        if matches!(first, b'~' | b'^' | b'<' | b'>' | b'=') {
            operators[0] = &text[..1];
        }
    }
    for operator in operators {
        if !operator.is_empty() && !text.starts_with(operator) {
            continue;
        }
        let rest = trim_go_regexp_space_start(&text[operator.len()..]);
        if !rest.is_empty() && rest.bytes().all(is_range_operand_char) {
            return Some((operator, rest));
        }
    }
    None
}

#[derive(Clone, Debug, Default)]
pub struct VersionRange {
    pub(crate) alternatives: Vec<Vec<VersionComparator>>,
}

#[derive(Clone, Debug)]
pub(crate) struct VersionComparator {
    operator: ComparatorOperator,
    operand: Version,
}

// PORT: comparatorOperator is a string type in Go; kept as &'static str constants.
type ComparatorOperator = &'static str;

const RANGE_LESS_THAN: ComparatorOperator = "<";
const RANGE_LESS_THAN_EQUAL: ComparatorOperator = "<=";
const RANGE_EQUAL: ComparatorOperator = "=";
const RANGE_GREATER_THAN_EQUAL: ComparatorOperator = ">=";
const RANGE_GREATER_THAN: ComparatorOperator = ">";

impl fmt::Display for VersionRange {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut sb = String::new();
        format_disjunction(&mut sb, &self.alternatives);
        f.write_str(&sb)
    }
}

fn format_disjunction(sb: &mut String, alternatives: &[Vec<VersionComparator>]) {
    let orig_len = sb.len();

    for (i, alternative) in alternatives.iter().enumerate() {
        if i > 0 {
            sb.push_str(" || ");
        }
        format_alternative(sb, alternative);
    }

    if sb.len() == orig_len {
        sb.push('*');
    }
}

fn format_alternative(sb: &mut String, comparators: &[VersionComparator]) {
    for (i, comparator) in comparators.iter().enumerate() {
        if i > 0 {
            sb.push(' ');
        }
        format_comparator(sb, comparator);
    }
}

fn format_comparator(sb: &mut String, comparator: &VersionComparator) {
    sb.push_str(comparator.operator);
    sb.push_str(&comparator.operand.to_string());
}

impl VersionRange {
    // PORT: Go `Test(version *Version)` — the version may be nil (it is forwarded
    // to Version.Compare which handles nil), so the parameter is Option<&Version>.
    pub fn test(&self, version: Option<&Version>) -> bool {
        test_disjunction(&self.alternatives, version)
    }
}

fn test_disjunction(alternatives: &[Vec<VersionComparator>], version: Option<&Version>) -> bool {
    // an empty disjunction is treated as "*" (all versions)
    if alternatives.is_empty() {
        return true;
    }

    for alternative in alternatives {
        if test_alternative(alternative, version) {
            return true;
        }
    }

    false
}

fn test_alternative(alternative: &[VersionComparator], version: Option<&Version>) -> bool {
    for comparator in alternative {
        if !test_comparator(comparator, version) {
            return false;
        }
    }
    true
}

fn test_comparator(comparator: &VersionComparator, version: Option<&Version>) -> bool {
    let cmp = Version::compare(version, Some(&comparator.operand));
    match comparator.operator {
        RANGE_LESS_THAN => cmp < 0,
        RANGE_LESS_THAN_EQUAL => cmp <= 0,
        RANGE_EQUAL => cmp == 0,
        RANGE_GREATER_THAN_EQUAL => cmp >= 0,
        RANGE_GREATER_THAN => cmp > 0,
        _ => panic!("Unexpected operator: {}", comparator.operator),
    }
}

pub fn try_parse_version_range(text: &str) -> (VersionRange, bool) {
    match parse_alternatives(text) {
        Some(alternatives) => (VersionRange { alternatives }, true),
        None => (
            VersionRange {
                alternatives: Vec::new(),
            },
            false,
        ),
    }
}

fn parse_alternatives(text: &str) -> Option<Vec<Vec<VersionComparator>>> {
    let mut alternatives = Vec::new();

    let text = text.trim();
    let ranges = text.split("||"); // logicalOrRegExp.Split(text, -1)
    for r in ranges {
        let r = r.trim();
        if r.is_empty() {
            continue;
        }

        let mut comparators: Vec<VersionComparator> = Vec::new();

        if let Some((left, right)) = hyphen_reg_exp_match(r) {
            let mut parsed_comparators = parse_hyphen(left, right)?;
            comparators.append(&mut parsed_comparators);
        } else {
            for simple in whitespace_reg_exp_split(r) {
                let matched = range_reg_exp_match(simple.trim())?;
                let mut parsed_comparators = parse_comparator(matched.0, matched.1)?;
                comparators.append(&mut parsed_comparators);
            }
        }

        alternatives.push(comparators);
    }

    Some(alternatives)
}

fn parse_hyphen(left: &str, right: &str) -> Option<Vec<VersionComparator>> {
    let left_result = parse_partial(left)?;
    let right_result = parse_partial(right)?;

    let mut comparators = Vec::new();
    if !is_wildcard(left_result.major_str) {
        // `MAJOR.*.*-...` gives us `>=MAJOR.0.0 ...`
        comparators.push(VersionComparator {
            operator: RANGE_GREATER_THAN_EQUAL,
            operand: left_result.version,
        });
    }

    if !is_wildcard(right_result.major_str) {
        let mut operand = right_result.version;
        let operator;

        if is_wildcard(right_result.minor_str) {
            // `...-MAJOR.*.*` gives us `... <(MAJOR+1).0.0`
            operand = operand.increment_major();
            operator = RANGE_LESS_THAN;
        } else if is_wildcard(right_result.patch_str) {
            // `...-MAJOR.MINOR.*` gives us `... <MAJOR.(MINOR+1).0`
            operand = operand.increment_minor();
            operator = RANGE_LESS_THAN;
        } else {
            // `...-MAJOR.MINOR.PATCH` gives us `... <=MAJOR.MINOR.PATCH`
            operator = RANGE_LESS_THAN_EQUAL;
        }

        comparators.push(VersionComparator { operator, operand });
    }

    Some(comparators)
}

struct PartialVersion<'a> {
    version: Version,
    major_str: &'a str,
    minor_str: &'a str,
    patch_str: &'a str,
}

// Produces a "partial" version
fn parse_partial(text: &str) -> Option<PartialVersion<'_>> {
    let matched = partial_reg_exp_match(text)?;

    let major_str = matched[0];
    let mut minor_str = matched[1];
    let mut patch_str = matched[2];
    let prerelease_str = matched[3];
    let build_str = matched[4];

    if minor_str.is_empty() {
        minor_str = "*";
    }
    if patch_str.is_empty() {
        patch_str = "*";
    }

    let mut major_numeric = 0;
    let mut minor_numeric = 0;
    let mut patch_numeric = 0;

    if !is_wildcard(major_str) {
        major_numeric = get_uint_component(major_str).ok()?;

        if !is_wildcard(minor_str) {
            minor_numeric = get_uint_component(minor_str).ok()?;

            if !is_wildcard(patch_str) {
                patch_numeric = get_uint_component(patch_str).ok()?;
            }
        }
    }

    let mut prerelease = Vec::new();
    if !prerelease_str.is_empty() {
        prerelease = prerelease_str.split('.').map(str::to_string).collect();
    }

    let mut build = Vec::new();
    if !build_str.is_empty() {
        build = build_str.split('.').map(str::to_string).collect();
    }

    let result = PartialVersion {
        version: Version {
            major: major_numeric,
            minor: minor_numeric,
            patch: patch_numeric,
            prerelease,
            build,
        },
        major_str,
        minor_str,
        patch_str,
    };

    Some(result)
}

fn parse_comparator(op: &str, text: &str) -> Option<Vec<VersionComparator>> {
    let result = parse_partial(text)?;

    let mut comparators_result: Vec<VersionComparator> = Vec::new();

    if !is_wildcard(result.major_str) {
        // PORT: Go's `operator := comparatorOperator(op)` is a runtime string; the
        // struct field stores one of the &'static constants, so `op` dispatches the
        // match and each arm re-derives the constant (`op` is exactly one of the
        // operators by the time each arm runs).
        match op {
            "~" => {
                let first = VersionComparator {
                    operator: RANGE_GREATER_THAN_EQUAL,
                    operand: result.version.clone(),
                };

                let second_version = if is_wildcard(result.minor_str) {
                    result.version.increment_major()
                } else {
                    result.version.increment_minor()
                };

                let second = VersionComparator {
                    operator: RANGE_LESS_THAN,
                    operand: second_version,
                };
                comparators_result = vec![first, second];
            }

            "^" => {
                let first = VersionComparator {
                    operator: RANGE_GREATER_THAN_EQUAL,
                    operand: result.version.clone(),
                };

                let second_version = if result.version.major > 0 || is_wildcard(result.minor_str) {
                    result.version.increment_major()
                } else if result.version.minor > 0 || is_wildcard(result.patch_str) {
                    result.version.increment_minor()
                } else {
                    result.version.increment_patch()
                };
                let second = VersionComparator {
                    operator: RANGE_LESS_THAN,
                    operand: second_version,
                };
                comparators_result = vec![first, second];
            }

            "<" | ">=" => {
                let operator: ComparatorOperator = if op == "<" {
                    RANGE_LESS_THAN
                } else {
                    RANGE_GREATER_THAN_EQUAL
                };
                let mut version = result.version.clone();
                if is_wildcard(result.minor_str) || is_wildcard(result.patch_str) {
                    version.prerelease = vec!["0".to_string()];
                }
                comparators_result = vec![VersionComparator {
                    operator,
                    operand: version,
                }];
            }

            "<=" | ">" => {
                let mut operator: ComparatorOperator = if op == "<=" {
                    RANGE_LESS_THAN_EQUAL
                } else {
                    RANGE_GREATER_THAN
                };
                let mut version = result.version.clone();
                if is_wildcard(result.minor_str) {
                    if operator == RANGE_LESS_THAN_EQUAL {
                        operator = RANGE_LESS_THAN;
                    } else {
                        operator = RANGE_GREATER_THAN_EQUAL;
                    }

                    version = version.increment_major();
                    version.prerelease = vec!["0".to_string()];
                } else if is_wildcard(result.patch_str) {
                    if operator == RANGE_LESS_THAN_EQUAL {
                        operator = RANGE_LESS_THAN;
                    } else {
                        operator = RANGE_GREATER_THAN_EQUAL;
                    }

                    version = version.increment_minor();
                    version.prerelease = vec!["0".to_string()];
                }

                comparators_result = vec![VersionComparator {
                    operator,
                    operand: version,
                }];
            }
            "=" | "" => {
                // normalize empty string to `=`
                let operator = RANGE_EQUAL;

                if is_wildcard(result.minor_str) || is_wildcard(result.patch_str) {
                    let original_version = result.version.clone();

                    let mut first_version = original_version.clone();
                    first_version.prerelease = vec!["0".to_string()];

                    let mut second_version = if is_wildcard(result.minor_str) {
                        original_version.increment_major()
                    } else {
                        original_version.increment_minor()
                    };
                    second_version.prerelease = vec!["0".to_string()];

                    comparators_result = vec![
                        VersionComparator {
                            operator: RANGE_GREATER_THAN_EQUAL,
                            operand: first_version,
                        },
                        VersionComparator {
                            operator: RANGE_LESS_THAN,
                            operand: second_version,
                        },
                    ];
                } else {
                    comparators_result = vec![VersionComparator {
                        operator,
                        operand: result.version.clone(),
                    }];
                }
            }
            _ => panic!("Unexpected operator: {}", op),
        }
    } else if op == "<" || op == ">" {
        comparators_result = vec![VersionComparator {
            // < 0.0.0-0
            operator: RANGE_LESS_THAN,
            operand: version_zero(),
        }];
    }

    Some(comparators_result)
}

fn is_wildcard(text: &str) -> bool {
    text == "*" || text == "x" || text == "X"
}
