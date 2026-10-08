// Ported from tsc/internal/tsoptions/wildcarddirectories_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;

use crate::wildcarddirectories::get_wildcard_directories;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath};

/// `TestGetWildcardDirectories_DotPrefixedIncludeWithDotDirExclude`.
///
/// https://github.com/microsoft/TypeScript/tsc/issues/3733 — "./"-prefixed
/// include specs must be fully normalized before being tested against exclude
/// patterns; otherwise the leftover literal "." path segment matches
/// dot-directory excludes like "**/.*\/", silently dropping every wildcard
/// directory (and with them, root file watching for the config).
#[test]
fn test_get_wildcard_directories_dot_prefixed_include_with_dot_dir_exclude() {
    let mut expected = HashMap::new();
    expected.insert(
        RootedDirectoryPath::from("/home/projects/monorepo/apps/web/app"),
        true,
    );
    let result = get_wildcard_directories(
        &["./app/**/*.ts".into(), "./app/**/*.tsx".into()],
        &["**/node_modules".into(), "**/.*/".into(), "./build".into()],
        &RootedDirectoryPath::from("/home/projects/monorepo/apps/web"),
        CaseSensitivity::CaseSensitive,
    );
    assert_eq!(result, Some(expected));
}

/// `TestGetWildcardDirectories_DriveRoot`.
#[test]
fn test_get_wildcard_directories_drive_root() {
    let mut expected = HashMap::new();
    expected.insert(RootedDirectoryPath::from("c:/"), false);
    let result = get_wildcard_directories(
        &["*.ts".into()],
        &[],
        &RootedDirectoryPath::from("c:/"),
        CaseSensitivity::CaseInsensitive,
    );
    assert_eq!(result, Some(expected));
}

/// `TestGetWildcardDirectories_NonASCIICharacters`.
#[test]
fn test_get_wildcard_directories_non_ascii_characters() {
    struct TestCase {
        name: &'static str,
        include: &'static [&'static str],
        exclude: &'static [&'static str],
        current_directory: &'static str,
        case_sensitivity: CaseSensitivity,
    }

    let tests = [
        TestCase {
            name: "Norwegian character æ in path",
            include: &["src/**/*.test.ts", "src/**/*.stories.ts", "src/**/*.mdx"],
            exclude: &["node_modules"],
            current_directory: "C:/Users/TobiasLægreid/dev/app/frontend/packages/react",
            case_sensitivity: CaseSensitivity::CaseInsensitive,
        },
        TestCase {
            name: "Japanese characters in path",
            include: &["src/**/*.ts"],
            exclude: &["テスト"],
            current_directory: "/Users/ユーザー/プロジェクト",
            case_sensitivity: CaseSensitivity::CaseSensitive,
        },
        TestCase {
            name: "Chinese characters in path",
            include: &["源代码/**/*.js"],
            exclude: &["节点模块"],
            current_directory: "/home/用户/项目",
            case_sensitivity: CaseSensitivity::CaseSensitive,
        },
        TestCase {
            name: "Various Unicode characters",
            include: &["src/**/*.ts"],
            exclude: &["node_modules"],
            current_directory: "/Users/Müller/café/naïve/résumé",
            case_sensitivity: CaseSensitivity::CaseInsensitive,
        },
    ];

    for test in tests {
        let include: Vec<tsc_tspath::PathPattern> =
            test.include.iter().map(|s| (*s).into()).collect();
        let exclude: Vec<tsc_tspath::PathPattern> =
            test.exclude.iter().map(|s| (*s).into()).collect();
        let result = get_wildcard_directories(
            &include,
            &exclude,
            &RootedDirectoryPath::from(test.current_directory),
            test.case_sensitivity,
        );
        assert!(result.is_some(), "{}: expected non-None result", test.name);
    }
}
