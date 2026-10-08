// Ported from tsc/internal/semver/version.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::num::IntErrorKind;

// https://semver.org/#spec-item-2
// > A normal version number MUST take the form X.Y.Z where X, Y, and Z are non-negative
// > integers, and MUST NOT contain leading zeroes. X is the major version, Y is the minor
// > version, and Z is the patch version. Each element MUST increase numerically.
//
// NOTE: We differ here in that we allow X and X.Y, with missing parts having the default
// value of `0`.
//
// PORT: Go compiles `versionRegexp = regexp.MustCompile(`(?i)^(0|[1-9]\d*)(?:\.(0|[1-9]\d*)(?:\.(0|[1-9]\d*)(?:-([a-z0-9-.]+))?(?:\+([a-z0-9-.]+))?)?)?$`)`.
// The `regex` crate is forbidden (SPEC.md §5.11), so each pattern in this package is
// ported as an equivalent hand-rolled matcher preserving leftmost-first (backtracking
// order) semantics. `version_regexp_match` mirrors `versionRegexp.FindStringSubmatch`,
// returning capture groups 1..=5 with "" for groups that did not participate.
fn version_regexp_match(text: &str) -> Option<[&str; 5]> {
    let (major, mut rest) = match_nr(text)?;
    let mut matched = [major, "", "", "", ""];
    if let Some(after_dot) = rest.strip_prefix('.') {
        (matched[1], rest) = match_nr(after_dot)?;
        if let Some(after_dot) = rest.strip_prefix('.') {
            (matched[2], rest) = match_nr(after_dot)?;
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

// PORT helper: the `0|[1-9]\d*` alternation used by versionRegexp. Returns the
// matched text and the unconsumed remainder.
fn match_nr(s: &str) -> Option<(&str, &str)> {
    match s.as_bytes().first()? {
        b'0' => Some((&s[..1], &s[1..])),
        b'1'..=b'9' => {
            let len = s.bytes().take_while(|b| b.is_ascii_digit()).count();
            Some((&s[..len], &s[len..]))
        }
        _ => None,
    }
}

// PORT helper: the `[a-z0-9-.]+` fragment (case-insensitive) used for the
// prerelease and build groups. Returns the length of the leading run of
// ASCII alphanumerics, '-' and '.'.
pub(crate) fn qualifier_run_len(s: &str) -> usize {
    s.bytes().take_while(|b| b.is_ascii_alphanumeric() || *b == b'-' || *b == b'.').count()
}

// https://semver.org/#spec-item-9
// > A pre-release version MAY be denoted by appending a hyphen and a series of dot separated
// > identifiers immediately following the patch version. Identifiers MUST comprise only ASCII
// > alphanumerics and hyphen [0-9A-Za-z-]. Identifiers MUST NOT be empty. Numeric identifiers
// > MUST NOT include leading zeroes.
//
//   prereleaseRegexp     = `(?i)^(?:0|[1-9]\d*|[a-z-][a-z0-9-]*)(?:\.(?:0|[1-9]\d*|[a-zA-Z-][a-zA-Z0-9-]*))*$`
//   prereleasePartRegexp = `(?i)^(?:0|[1-9]\d*|[a-z-][a-z0-9-]*)$`
fn prerelease_regexp_match(s: &str) -> bool {
    // The anchored alternation of '.'-separated parts is equivalent to checking each part.
    s.split('.').all(prerelease_part_regexp_match)
}

fn prerelease_part_regexp_match(s: &str) -> bool {
    let b = s.as_bytes();
    let Some(&first) = b.first() else { return false };
    if s == "0" {
        return true;
    }
    if first.is_ascii_digit() {
        // `[1-9]\d*` — a numeric part may not start with '0' (handled above).
        return first != b'0' && b.iter().all(|b| b.is_ascii_digit());
    }
    // `[a-z-][a-z0-9-]*` under (?i)
    (first.is_ascii_alphabetic() || first == b'-')
        && b.iter().all(|b| b.is_ascii_alphanumeric() || *b == b'-')
}

// https://semver.org/#spec-item-10
// > Build metadata MAY be denoted by appending a plus sign and a series of dot separated
// > identifiers immediately following the patch or pre-release version. Identifiers MUST
// > comprise only ASCII alphanumerics and hyphen [0-9A-Za-z-]. Identifiers MUST NOT be empty.
//
//   buildRegExp     = `(?i)^[a-z0-9-]+(?:\.[a-z0-9-]+)*$`
//   buildPartRegExp = `(?i)^[a-z0-9-]+$`
fn build_reg_exp_match(s: &str) -> bool {
    s.split('.').all(build_part_reg_exp_match)
}

fn build_part_reg_exp_match(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

// https://semver.org/#spec-item-9
// > Numeric identifiers MUST NOT include leading zeroes.
//
//   numericIdentifierRegExp = `^(?:0|[1-9]\d*)$`
fn numeric_identifier_reg_exp_match(s: &str) -> bool {
    s == "0"
        || (matches!(s.as_bytes().first(), Some(b'1'..=b'9'))
            && s.bytes().all(|b| b.is_ascii_digit()))
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Version {
    pub(crate) major: u32,
    pub(crate) minor: u32,
    pub(crate) patch: u32,
    pub(crate) prerelease: Vec<String>,
    pub(crate) build: Vec<String>,
}

// var versionZero = Version{prerelease: []string{"0"}}
pub(crate) fn version_zero() -> Version {
    Version { prerelease: vec!["0".to_string()], ..Version::default() }
}

impl Version {
    pub(crate) fn increment_major(&self) -> Version {
        Version { major: self.major.wrapping_add(1), ..Version::default() }
    }

    pub(crate) fn increment_minor(&self) -> Version {
        Version { major: self.major, minor: self.minor.wrapping_add(1), ..Version::default() }
    }

    pub(crate) fn increment_patch(&self) -> Version {
        Version {
            major: self.major,
            minor: self.minor,
            patch: self.patch.wrapping_add(1),
            ..Version::default()
        }
    }
}

pub(crate) const COMPARISON_LESS_THAN: i32 = -1;
pub(crate) const COMPARISON_EQUAL_TO: i32 = 0;
pub(crate) const COMPARISON_GREATER_THAN: i32 = 1;

impl Version {
    // https://semver.org/#spec-item-11
    // > Precedence is determined by the first difference when comparing each of these
    // > identifiers from left to right as follows: Major, minor, and patch versions are
    // > always compared numerically.
    //
    // https://semver.org/#spec-item-11
    // > Precedence for two pre-release versions with the same major, minor, and patch version
    // > MUST be determined by comparing each dot separated identifier from left to right until
    // > a difference is found [...]
    //
    // https://semver.org/#spec-item-11
    // > Build metadata does not figure into precedence
    //
    // PORT: Go signature is `func (a *Version) Compare(b *Version) int` and handles nil
    // receiver/argument; ported as an associated function over `Option<&Version>` so the
    // nil cases stay explicit (a nil Version compares below any non-nil Version).
    pub fn compare(a: Option<&Version>, b: Option<&Version>) -> i32 {
        match (a, b) {
            (None, None) => return COMPARISON_EQUAL_TO,
            (None, Some(_)) => return COMPARISON_LESS_THAN,
            (Some(_), None) => return COMPARISON_GREATER_THAN,
            (Some(a), Some(b)) => {
                if std::ptr::eq(a, b) {
                    return COMPARISON_EQUAL_TO;
                }
                let r = a.major.cmp(&b.major);
                if r != Ordering::Equal {
                    return r as i32;
                }

                let r = a.minor.cmp(&b.minor);
                if r != Ordering::Equal {
                    return r as i32;
                }

                let r = a.patch.cmp(&b.patch);
                if r != Ordering::Equal {
                    return r as i32;
                }

                compare_pre_release_identifiers(&a.prerelease, &b.prerelease)
            }
        }
    }
}

fn compare_pre_release_identifiers(left: &[String], right: &[String]) -> i32 {
    // https://semver.org/#spec-item-11
    // > When major, minor, and patch are equal, a pre-release version has lower precedence
    // > than a normal version.
    if left.is_empty() {
        if right.is_empty() {
            return COMPARISON_EQUAL_TO;
        }
        return COMPARISON_GREATER_THAN;
    } else if right.is_empty() {
        return COMPARISON_LESS_THAN;
    }

    // https://semver.org/#spec-item-11
    // > Precedence for two pre-release versions with the same major, minor, and patch version
    // > MUST be determined by comparing each dot separated identifier from left to right until
    // > a difference is found [...]
    //
    // PORT: slices.CompareFunc(left, right, comparePreReleaseIdentifier).
    for (l, r) in left.iter().zip(right.iter()) {
        let c = compare_pre_release_identifier(l, r);
        if c != 0 {
            return c;
        }
    }
    left.len().cmp(&right.len()) as i32
}

fn compare_pre_release_identifier(left: &str, right: &str) -> i32 {
    // https://semver.org/#spec-item-11
    // > Precedence for two pre-release versions with the same major, minor, and patch version
    // > MUST be determined by comparing each dot separated identifier from left to right until
    // > a difference is found [...]
    let compare_result = left.cmp(right) as i32;
    if compare_result == 0 {
        return compare_result;
    }

    let left_is_numeric = numeric_identifier_reg_exp_match(left);
    let right_is_numeric = numeric_identifier_reg_exp_match(right);

    if left_is_numeric || right_is_numeric {
        // https://semver.org/#spec-item-11
        // > Numeric identifiers always have lower precedence than non-numeric identifiers.
        if !right_is_numeric {
            return COMPARISON_LESS_THAN;
        }
        if !left_is_numeric {
            return COMPARISON_GREATER_THAN;
        }

        // https://semver.org/#spec-item-11
        // > identifiers consisting of only digits are compared numerically
        let left_as_number = get_uint_component(left);
        let right_as_number = get_uint_component(right);
        match (left_as_number, right_as_number) {
            (Ok(left_as_number), Ok(right_as_number)) => {
                left_as_number.cmp(&right_as_number) as i32
            }
            _ => {
                // This should only happen in the event of an overflow.
                // If so, use the lengths or fall back to string comparison.
                let left_len = left.len();
                let right_len = right.len();
                let len_compare = left_len.cmp(&right_len) as i32;
                if len_compare == 0 {
                    compare_result
                } else {
                    len_compare
                }
            }
        }
    } else {
        // https://semver.org/#spec-item-11
        // > identifiers with letters or hyphens are compared lexically in ASCII sort order.
        compare_result
    }
}

impl fmt::Display for Version {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}.{}", self.major, self.minor, self.patch)?;
        if !self.prerelease.is_empty() {
            write!(f, "-{}", self.prerelease.join("."))?;
        }
        if !self.build.is_empty() {
            write!(f, "+{}", self.build.join("."))?;
        }
        Ok(())
    }
}

pub struct SemverParseError {
    orig_input: String,
}

impl fmt::Display for SemverParseError {
    // Go: fmt.Sprintf("Could not parse version string from %q", e.origInput)
    // PORT: Rust's `{:?}` quoting differs from Go's `%q` for control/non-ASCII
    // characters; identical for typical ASCII version strings.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Could not parse version string from {:?}", self.orig_input)
    }
}

impl Error for SemverParseError {}

// PORT: mirrors the *strconv.NumError that getUintComponent surfaces, keeping the
// Display text identical to Go's `strconv.NumError.Error()`:
// "strconv."+Func+": parsing "+Quote(Num)+": "+Err. `{:?}` has the same `%q` caveat
// as SemverParseError above.
#[derive(Debug)]
pub struct NumError {
    num: String,
    err: &'static str,
}

impl fmt::Display for NumError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "strconv.ParseUint: parsing {:?}: {}", self.num, self.err)
    }
}

impl Error for NumError {}

// PORT: Go's TryParseVersion returns `error` holding either *SemverParseError or
// *strconv.NumError; the Rust port makes that explicit with an enum.
#[derive(Debug)]
pub enum ParseError {
    Semver(SemverParseError),
    Num(NumError),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::Semver(e) => e.fmt(f),
            ParseError::Num(e) => e.fmt(f),
        }
    }
}

impl Error for ParseError {}

impl From<SemverParseError> for ParseError {
    fn from(e: SemverParseError) -> ParseError {
        ParseError::Semver(e)
    }
}

impl From<NumError> for ParseError {
    fn from(e: NumError) -> ParseError {
        ParseError::Num(e)
    }
}

impl fmt::Debug for SemverParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

pub fn try_parse_version(text: &str) -> Result<Version, ParseError> {
    let mut result = Version::default();

    let Some(matched) = version_regexp_match(text) else {
        return Err(SemverParseError { orig_input: text.to_string() }.into());
    };

    let major_str = matched[0];
    let minor_str = matched[1];
    let patch_str = matched[2];
    let prerelease_str = matched[3];
    let build_str = matched[4];

    // PORT: Go returns the partially-filled `result` alongside the error; the
    // partial value is unobservable (callers discard it on error), so the Err
    // variant carries only the error.
    result.major = get_uint_component(major_str)?;

    if !minor_str.is_empty() {
        result.minor = get_uint_component(minor_str)?;
    }

    if !patch_str.is_empty() {
        result.patch = get_uint_component(patch_str)?;
    }

    if !prerelease_str.is_empty() {
        if !prerelease_regexp_match(prerelease_str) {
            return Err(SemverParseError { orig_input: text.to_string() }.into());
        }

        result.prerelease = prerelease_str.split('.').map(str::to_string).collect();
    }
    if !build_str.is_empty() {
        if !build_reg_exp_match(build_str) {
            return Err(SemverParseError { orig_input: text.to_string() }.into());
        }

        result.build = build_str.split('.').map(str::to_string).collect();
    }

    Ok(result)
}

pub fn must_parse(text: &str) -> Version {
    match try_parse_version(text) {
        Ok(v) => v,
        Err(err) => panic!("{err}"),
    }
}

// strconv.ParseUint(text, 10, 32)
pub(crate) fn get_uint_component(text: &str) -> Result<u32, NumError> {
    text.parse::<u32>().map_err(|e| NumError {
        num: text.to_string(),
        err: match e.kind() {
            IntErrorKind::PosOverflow | IntErrorKind::NegOverflow => "value out of range",
            _ => "invalid syntax",
        },
    })
}
