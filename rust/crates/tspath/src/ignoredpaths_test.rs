// Ported from tsc/internal/tspath/ignoredpaths_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::ignoredpaths::contains_ignored_path_str;

#[test]
fn test_contains_ignored_path() {
    let tests = [
        // node_modules dot path
        ("/project/node_modules/.pnpm/file.ts", true),
        // git directory
        ("/project/.git/hooks/pre-commit", true),
        // emacs lock file
        ("/project/src/file.ts.#", true),
        // regular file path
        ("/project/src/file.ts", false),
        // node_modules without dot
        ("/project/node_modules/lodash/index.js", false),
        // empty path
        ("", false),
        // path with multiple ignored patterns
        ("/project/node_modules/.pnpm/.git/.#file.ts", true),
        // case sensitive test — should be case sensitive
        ("/project/NODE_MODULES/.PNPM/file.ts", false),
        // path with ignored pattern in middle
        ("/project/src/node_modules/.pnpm/dist/file.js", true),
        // path with ignored pattern at end
        ("/project/src/file.ts.#", true),
    ];

    for (path, expected) in tests {
        let result = contains_ignored_path_str(path);
        assert_eq!(result, expected, "contains_ignored_path_str({path:?})");
    }
}

#[test]
fn test_ignored_paths_patterns() {
    // Test that all expected patterns are present
    let expected_patterns = ["/node_modules/.", "/.git", ".#"];

    for pattern in expected_patterns {
        let test_path = format!("/test{pattern}/file.ts");
        assert!(
            contains_ignored_path_str(&test_path),
            "Expected pattern '{pattern}' to be detected in path '{test_path}'"
        );
    }
}

#[test]
fn test_ignored_paths_edge_cases() {
    let tests = [
        // pattern at start — pattern is "/node_modules/." not "/node_modules."
        ("/node_modules./file.ts", false),
        // pattern at end
        ("/project/file.ts.#", true),
        // multiple occurrences
        ("/project/.git/node_modules./.git/file.ts", true),
        // no slashes
        ("node_modules.file.ts", false),
        // single slash
        ("/file.ts", false),
    ];

    for (path, expected) in tests {
        let result = contains_ignored_path_str(path);
        assert_eq!(result, expected, "contains_ignored_path_str({path:?})");
    }
}
