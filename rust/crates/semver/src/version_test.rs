// Ported from tsc/internal/semver/version_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::version::{
    try_parse_version, Version, COMPARISON_EQUAL_TO, COMPARISON_GREATER_THAN, COMPARISON_LESS_THAN,
};

fn strs(parts: &[&str]) -> Vec<String> {
    parts.iter().map(|s| s.to_string()).collect()
}

#[test]
fn test_try_parse_semver() {
    let tests: &[(&str, Version)] = &[
        (
            "1.2.3-pre.4+build.5",
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                prerelease: strs(&["pre", "4"]),
                build: strs(&["build", "5"]),
            },
        ),
        (
            "1.2.3-pre.4",
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                prerelease: strs(&["pre", "4"]),
                build: vec![],
            },
        ),
        (
            "1.2.3+build.4",
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                prerelease: vec![],
                build: strs(&["build", "4"]),
            },
        ),
        (
            "1.2.3",
            Version { major: 1, minor: 2, patch: 3, prerelease: vec![], build: vec![] },
        ),
    ];

    for (input, expected) in tests {
        let v = try_parse_version(*input).unwrap();
        assert_version(&v, expected);
    }
}

#[test]
fn test_version_string() {
    let tests: &[(Version, &str)] = &[
        (
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                prerelease: strs(&["pre", "4"]),
                build: strs(&["build", "5"]),
            },
            "1.2.3-pre.4+build.5",
        ),
        (
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                prerelease: strs(&["pre", "4"]),
                build: strs(&["build"]),
            },
            "1.2.3-pre.4+build",
        ),
        (
            Version { major: 1, minor: 2, patch: 3, prerelease: vec![], build: strs(&["build"]) },
            "1.2.3+build",
        ),
        (
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                prerelease: strs(&["pre", "4"]),
                build: vec![],
            },
            "1.2.3-pre.4",
        ),
        (
            Version {
                major: 1,
                minor: 2,
                patch: 3,
                prerelease: vec![],
                build: strs(&["build", "4"]),
            },
            "1.2.3+build.4",
        ),
        (Version { major: 1, minor: 2, patch: 3, prerelease: vec![], build: vec![] }, "1.2.3"),
    ];

    for (input, expected) in tests {
        assert_eq!(input.to_string(), *expected);
    }
}

#[test]
fn test_version_compare() {
    let tests: &[(&str, &str, i32)] = &[
        // https://semver.org/#spec-item-11
        // > Precedence is determined by the first difference when comparing each of these
        // > identifiers from left to right as follows: Major, minor, and patch versions are
        // > always compared numerically.
        ("1.0.0", "2.0.0", COMPARISON_LESS_THAN),
        ("1.0.0", "1.1.0", COMPARISON_LESS_THAN),
        ("1.0.0", "1.0.1", COMPARISON_LESS_THAN),
        ("2.0.0", "1.0.0", COMPARISON_GREATER_THAN),
        ("1.1.0", "1.0.0", COMPARISON_GREATER_THAN),
        ("1.0.1", "1.0.0", COMPARISON_GREATER_THAN),
        ("1.0.0", "1.0.0", COMPARISON_EQUAL_TO),
        // https://semver.org/#spec-item-11
        // > When major, minor, and patch are equal, a pre-release version has lower
        // > precedence than a normal version.
        ("1.0.0", "1.0.0-pre", COMPARISON_GREATER_THAN),
        ("1.0.1-pre", "1.0.0", COMPARISON_GREATER_THAN),
        ("1.0.0-pre", "1.0.0", COMPARISON_LESS_THAN),
        // https://semver.org/#spec-item-11
        // > identifiers consisting of only digits are compared numerically
        ("1.0.0-0", "1.0.0-1", COMPARISON_LESS_THAN),
        ("1.0.0-1", "1.0.0-0", COMPARISON_GREATER_THAN),
        ("1.0.0-2", "1.0.0-10", COMPARISON_LESS_THAN),
        ("1.0.0-10", "1.0.0-2", COMPARISON_GREATER_THAN),
        ("1.0.0-0", "1.0.0-0", COMPARISON_EQUAL_TO),
        // https://semver.org/#spec-item-11
        // > identifiers with letters or hyphens are compared lexically in ASCII sort order.
        ("1.0.0-a", "1.0.0-b", COMPARISON_LESS_THAN),
        ("1.0.0-a-2", "1.0.0-a-10", COMPARISON_GREATER_THAN),
        ("1.0.0-b", "1.0.0-a", COMPARISON_GREATER_THAN),
        ("1.0.0-a", "1.0.0-a", COMPARISON_EQUAL_TO),
        ("1.0.0-A", "1.0.0-a", COMPARISON_LESS_THAN),
        // https://semver.org/#spec-item-11
        // > Numeric identifiers always have lower precedence than non-numeric identifiers.
        ("1.0.0-0", "1.0.0-alpha", COMPARISON_LESS_THAN),
        ("1.0.0-alpha", "1.0.0-0", COMPARISON_GREATER_THAN),
        ("1.0.0-0", "1.0.0-0", COMPARISON_EQUAL_TO),
        ("1.0.0-alpha", "1.0.0-alpha", COMPARISON_EQUAL_TO),
        // https://semver.org/#spec-item-11
        // > A larger set of pre-release fields has a higher precedence than a smaller set, if all
        // > of the preceding identifiers are equal.
        ("1.0.0-alpha", "1.0.0-alpha.0", COMPARISON_LESS_THAN),
        ("1.0.0-alpha.0", "1.0.0-alpha", COMPARISON_GREATER_THAN),
        // https://semver.org/#spec-item-11
        // > Precedence for two pre-release versions with the same major, minor, and patch version
        // > MUST be determined by comparing each dot separated identifier from left to right until
        // > a difference is found [...]
        ("1.0.0-a.0.b.1", "1.0.0-a.0.b.2", COMPARISON_LESS_THAN),
        ("1.0.0-a.0.b.1", "1.0.0-b.0.a.1", COMPARISON_LESS_THAN),
        ("1.0.0-a.0.b.2", "1.0.0-a.0.b.1", COMPARISON_GREATER_THAN),
        ("1.0.0-b.0.a.1", "1.0.0-a.0.b.1", COMPARISON_GREATER_THAN),
        // https://semver.org/#spec-item-11
        // > Build metadata does not figure into precedence
        ("1.0.0+build", "1.0.0", COMPARISON_EQUAL_TO),
        ("1.0.0+build.stuff", "1.0.0", COMPARISON_EQUAL_TO),
        ("1.0.0", "1.0.0+build", COMPARISON_EQUAL_TO),
        ("1.0.0+build", "1.0.0+stuff", COMPARISON_EQUAL_TO),
        // https://semver.org/#spec-item-11
        // Edge cases for numeric and lexical comparison of prerelease identifiers.
        ("1.0.0-alpha.99999", "1.0.0-alpha.100000", COMPARISON_LESS_THAN),
        ("1.0.0-alpha.beta", "1.0.0-alpha.alpha", COMPARISON_GREATER_THAN),
    ];

    for (v1_text, v2_text, want) in tests {
        let v1 = try_parse_version(*v1_text).unwrap();
        let v2 = try_parse_version(*v2_text).unwrap();
        assert_eq!(Version::compare(Some(&v1), Some(&v2)), *want);
    }
}

fn assert_version(a: &Version, b: &Version) {
    assert_eq!(a.major, b.major);
    assert_eq!(a.minor, b.minor);
    assert_eq!(a.patch, b.patch);
    assert_eq!(a.prerelease, b.prerelease);
    assert_eq!(a.build, b.build);
}
