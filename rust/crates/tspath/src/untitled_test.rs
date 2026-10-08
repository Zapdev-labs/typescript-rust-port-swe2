// Ported from tsc/internal/tspath/untitled_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's file is `package tspath_test` (external test package); here it is
// a same-crate test module, but it only uses the public API either way.

use crate::{
    CaseSensitivity, RootedDirectoryPath, get_encoded_root_length, get_normalized_absolute_path,
    is_rooted_disk_path, to_rooted_path,
};

#[test]
fn test_untitled_path_handling() {
    // Test that untitled paths are treated as rooted
    let untitled_path = "^/untitled/ts-nul-authority/Untitled-2";

    // GetEncodedRootLength should return 2 for "^/"
    let root_length = get_encoded_root_length(untitled_path);
    assert_eq!(
        root_length, 2,
        "GetEncodedRootLength should return 2 for untitled paths"
    );

    // IsRootedDiskPath should return true
    let is_rooted = is_rooted_disk_path(untitled_path);
    assert!(
        is_rooted,
        "IsRootedDiskPath should return true for untitled paths"
    );

    // Rooting should not resolve untitled paths against current directory.
    let current_dir = RootedDirectoryPath::from("/home/user/project");
    let path =
        CaseSensitivity::CaseSensitive.path_key(&to_rooted_path(untitled_path, &current_dir));
    // The path should be the original untitled path
    assert_eq!(
        path.as_string(),
        "^/untitled/ts-nul-authority/Untitled-2",
        "rooting should not resolve untitled paths against current directory"
    );

    // Test GetNormalizedAbsolutePath doesn't resolve untitled paths
    let normalized = get_normalized_absolute_path(untitled_path, &current_dir);
    assert_eq!(
        normalized.as_ref(),
        "^/untitled/ts-nul-authority/Untitled-2",
        "GetNormalizedAbsolutePath should not resolve untitled paths"
    );
}

#[test]
fn test_untitled_path_edge_cases() {
    // Test edge cases
    let test_cases: &[(&str, i32, bool)] = &[
        ("^/", 2, true),                               // Minimal untitled path
        ("^/untitled/ts-nul-authority/test", 2, true), // Normal untitled path
        ("^", 0, false),                               // Just ^ is not rooted
        ("^x", 0, false),                              // ^x is not untitled
        ("^^/", 0, false),                             // ^^/ is not untitled
        ("x^/", 0, false),                             // x^/ is not untitled (doesn't start with ^)
        (
            "^/untitled/ts-nul-authority/path/with/deeper/structure",
            2,
            true,
        ), // Deeper path
    ];

    for &(path, expected, is_rooted_expected) in test_cases {
        let root_length = get_encoded_root_length(path);
        assert_eq!(
            root_length, expected,
            "GetEncodedRootLength for path {path}"
        );

        let is_rooted = is_rooted_disk_path(path);
        assert_eq!(
            is_rooted, is_rooted_expected,
            "IsRootedDiskPath for path {path}"
        );
    }
}
