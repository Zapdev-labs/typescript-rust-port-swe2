// Ported from tsc/internal/tspath/path_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go benchmarks (BenchmarkCombinePaths, BenchmarkGetNormalizedAbsolutePath,
// BenchmarkToFileNameLowerCase, BenchmarkHasRelativePathSegment,
// BenchmarkPathIsRelative) and fuzz tests (FuzzGetNormalizedAbsolutePath,
// FuzzToFileNameLowerCase, FuzzHasRelativePathSegment) have no stable-Rust cargo
// test equivalent, so they are omitted along with their helpers (shortenName,
// normalizePath_old, getNormalizedAbsolutePath_old, oldToFileNameLowerCase,
// oldHasRelativePathSegment, the regexp-based reference implementations, and the
// bench/fuzz-only test tables). No regex is used per porting rules.

use rustc_hash::FxHashSet;

use crate::path::{get_common_parents, reduce_path_components};
use crate::{
    CaseSensitivity, RootedDirectoryPath, combine_paths, get_directory_path,
    get_longest_extension_from_path, get_normalized_absolute_path, get_path_components,
    get_relative_path_to_directory_or_url, get_root_length, is_rooted_disk_path, is_url,
    normalize_path, normalize_slashes, path_is_absolute, path_is_relative,
    remove_any_file_extension, resolve_path, resolve_path_without_trailing_directory_separator,
    to_file_name_lower_case,
};

fn ss(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

#[test]
fn test_normalize_slashes() {
    assert_eq!(normalize_slashes("a").as_ref(), "a");
    assert_eq!(normalize_slashes("a/b").as_ref(), "a/b");
    assert_eq!(normalize_slashes("a\\b").as_ref(), "a/b");
    assert_eq!(normalize_slashes("\\\\server\\path").as_ref(), "//server/path");
}

#[test]
fn test_get_root_length() {
    assert_eq!(get_root_length("a"), 0);
    assert_eq!(get_root_length("/"), 1);
    assert_eq!(get_root_length("/path"), 1);
    assert_eq!(get_root_length("c:"), 2);
    assert_eq!(get_root_length("c:d"), 0);
    assert_eq!(get_root_length("c:/"), 3);
    assert_eq!(get_root_length("c:\\"), 3);
    assert_eq!(get_root_length("//server"), 8);
    assert_eq!(get_root_length("//server/share"), 9);
    assert_eq!(get_root_length("\\\\server"), 8);
    assert_eq!(get_root_length("\\\\server\\share"), 9);
    assert_eq!(get_root_length("file:///"), 8);
    assert_eq!(get_root_length("file:///path"), 8);
    assert_eq!(get_root_length("file:///c:"), 10);
    assert_eq!(get_root_length("file:///c:d"), 8);
    assert_eq!(get_root_length("file:///c:/path"), 11);
    assert_eq!(get_root_length("file:///c%3a"), 12);
    assert_eq!(get_root_length("file:///c%3ad"), 8);
    assert_eq!(get_root_length("file:///c%3a/path"), 13);
    assert_eq!(get_root_length("file:///c%3A"), 12);
    assert_eq!(get_root_length("file:///c%3Ad"), 8);
    assert_eq!(get_root_length("file:///c%3A/path"), 13);
    assert_eq!(get_root_length("file://localhost"), 16);
    assert_eq!(get_root_length("file://localhost/"), 17);
    assert_eq!(get_root_length("file://localhost/path"), 17);
    assert_eq!(get_root_length("file://localhost/c:"), 19);
    assert_eq!(get_root_length("file://localhost/c:d"), 17);
    assert_eq!(get_root_length("file://localhost/c:/path"), 20);
    assert_eq!(get_root_length("file://localhost/c%3a"), 21);
    assert_eq!(get_root_length("file://localhost/c%3ad"), 17);
    assert_eq!(get_root_length("file://localhost/c%3a/path"), 22);
    assert_eq!(get_root_length("file://localhost/c%3A"), 21);
    assert_eq!(get_root_length("file://localhost/c%3Ad"), 17);
    assert_eq!(get_root_length("file://localhost/c%3A/path"), 22);
    assert_eq!(get_root_length("file://server"), 13);
    assert_eq!(get_root_length("file://server/"), 14);
    assert_eq!(get_root_length("file://server/path"), 14);
    assert_eq!(get_root_length("file://server/c:"), 14);
    assert_eq!(get_root_length("file://server/c:d"), 14);
    assert_eq!(get_root_length("file://server/c:/d"), 14);
    assert_eq!(get_root_length("file://server/c%3a"), 14);
    assert_eq!(get_root_length("file://server/c%3ad"), 14);
    assert_eq!(get_root_length("file://server/c%3a/d"), 14);
    assert_eq!(get_root_length("file://server/c%3A"), 14);
    assert_eq!(get_root_length("file://server/c%3Ad"), 14);
    assert_eq!(get_root_length("file://server/c%3A/d"), 14);
    assert_eq!(get_root_length("http://server"), 13);
    assert_eq!(get_root_length("http://server/path"), 14);
}

#[test]
fn test_path_is_absolute() {
    // POSIX
    assert!(path_is_absolute("/path/to/file.ext"));
    // DOS
    assert!(path_is_absolute("c:/path/to/file.ext"));
    // URL
    assert!(path_is_absolute("file:///path/to/file.ext"));
    // Non-absolute
    assert!(!path_is_absolute("path/to/file.ext"));
    assert!(!path_is_absolute("./path/to/file.ext"));
}

#[test]
fn test_is_url() {
    assert!(!is_url("a"));
    assert!(!is_url("/"));
    assert!(!is_url("c:"));
    assert!(!is_url("c:d"));
    assert!(!is_url("c:/"));
    assert!(!is_url("c:\\"));
    assert!(!is_url("//server"));
    assert!(!is_url("//server/share"));
    assert!(!is_url("\\\\server"));
    assert!(!is_url("\\\\server\\share"));

    assert!(is_url("file:///path"));
    assert!(is_url("file:///c:"));
    assert!(is_url("file:///c:d"));
    assert!(is_url("file:///c:/path"));
    assert!(is_url("file://server"));
    assert!(is_url("file://server/path"));
    assert!(is_url("http://server"));
    assert!(is_url("http://server/path"));
}

#[test]
fn test_is_rooted_disk_path() {
    assert!(!is_rooted_disk_path("a"));
    assert!(is_rooted_disk_path("/"));
    assert!(is_rooted_disk_path("c:"));
    assert!(!is_rooted_disk_path("c:d"));
    assert!(is_rooted_disk_path("c:/"));
    assert!(is_rooted_disk_path("c:\\"));
    assert!(is_rooted_disk_path("//server"));
    assert!(is_rooted_disk_path("//server/share"));
    assert!(is_rooted_disk_path("\\\\server"));
    assert!(is_rooted_disk_path("\\\\server\\share"));
    assert!(!is_rooted_disk_path("file:///path"));
    assert!(!is_rooted_disk_path("file:///c:"));
    assert!(!is_rooted_disk_path("file:///c:d"));
    assert!(!is_rooted_disk_path("file:///c:/path"));
    assert!(!is_rooted_disk_path("file://server"));
    assert!(!is_rooted_disk_path("file://server/path"));
    assert!(!is_rooted_disk_path("http://server"));
    assert!(!is_rooted_disk_path("http://server/path"));
}

#[test]
fn test_get_directory_path() {
    assert_eq!(get_directory_path("").as_ref(), "");
    assert_eq!(get_directory_path("a").as_ref(), "");
    assert_eq!(get_directory_path("a/b").as_ref(), "a");
    assert_eq!(get_directory_path("/").as_ref(), "/");
    assert_eq!(get_directory_path("/a").as_ref(), "/");
    assert_eq!(get_directory_path("/a/").as_ref(), "/");
    assert_eq!(get_directory_path("/a/b").as_ref(), "/a");
    assert_eq!(get_directory_path("/a/b/").as_ref(), "/a");
    assert_eq!(get_directory_path("c:").as_ref(), "c:");
    assert_eq!(get_directory_path("c:d").as_ref(), "");
    assert_eq!(get_directory_path("c:/").as_ref(), "c:/");
    assert_eq!(get_directory_path("c:/path").as_ref(), "c:/");
    assert_eq!(get_directory_path("c:/path/").as_ref(), "c:/");
    assert_eq!(get_directory_path("//server").as_ref(), "//server");
    assert_eq!(get_directory_path("//server/").as_ref(), "//server/");
    assert_eq!(get_directory_path("//server/share").as_ref(), "//server/");
    assert_eq!(get_directory_path("//server/share/").as_ref(), "//server/");
    assert_eq!(get_directory_path("\\\\server").as_ref(), "//server");
    assert_eq!(get_directory_path("\\\\server\\").as_ref(), "//server/");
    assert_eq!(get_directory_path("\\\\server\\share").as_ref(), "//server/");
    assert_eq!(get_directory_path("\\\\server\\share\\").as_ref(), "//server/");
    assert_eq!(get_directory_path("file:///").as_ref(), "file:///");
    assert_eq!(get_directory_path("file:///path").as_ref(), "file:///");
    assert_eq!(get_directory_path("file:///path/").as_ref(), "file:///");
    assert_eq!(get_directory_path("file:///c:").as_ref(), "file:///c:");
    assert_eq!(get_directory_path("file:///c:d").as_ref(), "file:///");
    assert_eq!(get_directory_path("file:///c:/").as_ref(), "file:///c:/");
    assert_eq!(get_directory_path("file:///c:/path").as_ref(), "file:///c:/");
    assert_eq!(get_directory_path("file:///c:/path/").as_ref(), "file:///c:/");
    assert_eq!(get_directory_path("file://server").as_ref(), "file://server");
    assert_eq!(get_directory_path("file://server/").as_ref(), "file://server/");
    assert_eq!(get_directory_path("file://server/path").as_ref(), "file://server/");
    assert_eq!(get_directory_path("file://server/path/").as_ref(), "file://server/");
    assert_eq!(get_directory_path("http://server").as_ref(), "http://server");
    assert_eq!(get_directory_path("http://server/").as_ref(), "http://server/");
    assert_eq!(get_directory_path("http://server/path").as_ref(), "http://server/");
    assert_eq!(get_directory_path("http://server/path/").as_ref(), "http://server/");
}

#[test]
fn test_get_longest_extension_from_path() {
    let extensions: &[&str] = &[".z", ".y.z", ".other"];
    assert_eq!(
        get_longest_extension_from_path("/src/Component.y.z", extensions, CaseSensitivity::CaseSensitive),
        ".y.z"
    );
    assert_eq!(
        get_longest_extension_from_path("/src/Component.z", extensions, CaseSensitivity::CaseSensitive),
        ".z"
    );
    assert_eq!(
        get_longest_extension_from_path("/src/Component.y.Z", extensions, CaseSensitivity::CaseSensitive),
        ""
    );
    assert_eq!(
        get_longest_extension_from_path("/src/Component.y.Z", extensions, CaseSensitivity::CaseInsensitive),
        ".y.Z"
    );
}

#[test]
fn test_remove_any_file_extension() {
    assert_eq!(remove_any_file_extension("/src/Component.vue").as_ref(), "/src/Component");
    assert_eq!(remove_any_file_extension("/src/Component.d.ts").as_ref(), "/src/Component");
    assert_eq!(remove_any_file_extension("/src/Component").as_ref(), "/src/Component");
}

// !!!
// getBaseFileName
// getAnyExtensionFromPath

#[test]
fn test_get_path_components() {
    assert_eq!(get_path_components(""), ss(&[""]));
    assert_eq!(get_path_components("a"), ss(&["", "a"]));
    assert_eq!(get_path_components("./a"), ss(&["", ".", "a"]));
    assert_eq!(get_path_components("/"), ss(&["/"]));
    assert_eq!(get_path_components("/a"), ss(&["/", "a"]));
    assert_eq!(get_path_components("/a/"), ss(&["/", "a"]));
    assert_eq!(get_path_components("c:"), ss(&["c:"]));
    assert_eq!(get_path_components("c:d"), ss(&["", "c:d"]));
    assert_eq!(get_path_components("c:/"), ss(&["c:/"]));
    assert_eq!(get_path_components("c:/path"), ss(&["c:/", "path"]));
    assert_eq!(get_path_components("//server"), ss(&["//server"]));
    assert_eq!(get_path_components("//server/"), ss(&["//server/"]));
    assert_eq!(get_path_components("//server/share"), ss(&["//server/", "share"]));
    assert_eq!(get_path_components("file:///"), ss(&["file:///"]));
    assert_eq!(get_path_components("file:///path"), ss(&["file:///", "path"]));
    assert_eq!(get_path_components("file:///c:"), ss(&["file:///c:"]));
    assert_eq!(get_path_components("file:///c:d"), ss(&["file:///", "c:d"]));
    assert_eq!(get_path_components("file:///c:/"), ss(&["file:///c:/"]));
    assert_eq!(get_path_components("file:///c:/path"), ss(&["file:///c:/", "path"]));
    assert_eq!(get_path_components("file://server"), ss(&["file://server"]));
    assert_eq!(get_path_components("file://server/"), ss(&["file://server/"]));
    assert_eq!(get_path_components("file://server/path"), ss(&["file://server/", "path"]));
    assert_eq!(get_path_components("http://server"), ss(&["http://server"]));
    assert_eq!(get_path_components("http://server/"), ss(&["http://server/"]));
    assert_eq!(get_path_components("http://server/path"), ss(&["http://server/", "path"]));
}

#[test]
fn test_reduce_path_components() {
    assert_eq!(reduce_path_components(&ss(&[""])), ss(&[""]));
    assert_eq!(reduce_path_components(&ss(&["", "."])), ss(&[""]));
    assert_eq!(reduce_path_components(&ss(&["", ".", "a"])), ss(&["", "a"]));
    assert_eq!(reduce_path_components(&ss(&["", "a", "."])), ss(&["", "a"]));
    assert_eq!(reduce_path_components(&ss(&["", ".."])), ss(&["", ".."]));
    assert_eq!(
        reduce_path_components(&ss(&["", "..", ".."])),
        ss(&["", "..", ".."])
    );
    assert_eq!(
        reduce_path_components(&ss(&["", "..", ".", ".."])),
        ss(&["", "..", ".."])
    );
    assert_eq!(reduce_path_components(&ss(&["", "a", ".."])), ss(&[""]));
    assert_eq!(
        reduce_path_components(&ss(&["", "..", "a"])),
        ss(&["", "..", "a"])
    );
    assert_eq!(reduce_path_components(&ss(&["/"])), ss(&["/"]));
    assert_eq!(reduce_path_components(&ss(&["/", "."])), ss(&["/"]));
    assert_eq!(reduce_path_components(&ss(&["/", ".."])), ss(&["/"]));
    assert_eq!(reduce_path_components(&ss(&["/", "a", ".."])), ss(&["/"]));
}

#[test]
fn test_combine_paths() {
    // Non-rooted
    assert_eq!(combine_paths("path", &["to", "file.ext"]), "path/to/file.ext");
    assert_eq!(
        combine_paths("path", &["dir", "..", "to", "file.ext"]),
        "path/dir/../to/file.ext"
    );
    // POSIX
    assert_eq!(combine_paths("/path", &["to", "file.ext"]), "/path/to/file.ext");
    assert_eq!(combine_paths("/path", &["/to", "file.ext"]), "/to/file.ext");
    // DOS
    assert_eq!(combine_paths("c:/path", &["to", "file.ext"]), "c:/path/to/file.ext");
    assert_eq!(combine_paths("c:/path", &["c:/to", "file.ext"]), "c:/to/file.ext");
    // URL
    assert_eq!(
        combine_paths("file:///path", &["to", "file.ext"]),
        "file:///path/to/file.ext"
    );
    assert_eq!(
        combine_paths("file:///path", &["file:///to", "file.ext"]),
        "file:///to/file.ext"
    );

    assert_eq!(combine_paths("/", &["/node_modules/@types"]), "/node_modules/@types");
    assert_eq!(combine_paths("/a/..", &[""]), "/a/..");
    assert_eq!(combine_paths("/a/..", &["b"]), "/a/../b");
    assert_eq!(combine_paths("/a/..", &["b/"]), "/a/../b/");
    assert_eq!(combine_paths("/a/..", &["/"]), "/");
    assert_eq!(combine_paths("/a/..", &["/b"]), "/b");
}

#[test]
fn test_resolve_path() {
    assert_eq!(resolve_path("", &[]), "");
    assert_eq!(resolve_path(".", &[]), "");
    assert_eq!(resolve_path("./", &[]), "");
    assert_eq!(resolve_path("..", &[]), "..");
    assert_eq!(resolve_path("../", &[]), "../");
    assert_eq!(resolve_path("/", &[]), "/");
    assert_eq!(resolve_path("/.", &[]), "/");
    assert_eq!(resolve_path("/./", &[]), "/");
    assert_eq!(resolve_path("/../", &[]), "/");
    assert_eq!(resolve_path("/a", &[]), "/a");
    assert_eq!(resolve_path("/a/", &[]), "/a/");
    assert_eq!(resolve_path("/a/.", &[]), "/a");
    assert_eq!(resolve_path("/a/./", &[]), "/a/");
    assert_eq!(resolve_path("/a/./b", &[]), "/a/b");
    assert_eq!(resolve_path("/a/./b/", &[]), "/a/b/");
    assert_eq!(resolve_path("/a/..", &[]), "/");
    assert_eq!(resolve_path("/a/../", &[]), "/");
    assert_eq!(resolve_path("/a/../b", &[]), "/b");
    assert_eq!(resolve_path("/a/../b/", &[]), "/b/");
    assert_eq!(resolve_path("/a/..", &["b"]), "/b");
    assert_eq!(resolve_path("/a/..", &["/"]), "/");
    assert_eq!(resolve_path("/a/..", &["b/"]), "/b/");
    assert_eq!(resolve_path("/a/..", &["/b"]), "/b");
    assert_eq!(resolve_path("/a/.", &["b"]), "/a/b");
    assert_eq!(resolve_path("/a/.", &["."]), "/a");
    assert_eq!(resolve_path("a", &["b", "c"]), "a/b/c");
    assert_eq!(resolve_path("a", &["b", "/c"]), "/c");
    assert_eq!(resolve_path("a", &["b", "../c"]), "a/c");
}

#[test]
fn test_resolve_path_without_trailing_directory_separator() {
    assert_eq!(resolve_path_without_trailing_directory_separator("/", &[]), "/");
    assert_eq!(resolve_path_without_trailing_directory_separator("c:/", &[]), "c:/");
    assert_eq!(resolve_path_without_trailing_directory_separator("/a/", &[]), "/a");
    assert_eq!(resolve_path_without_trailing_directory_separator("a", &["b/"]), "a/b");
}

#[test]
fn test_normalize_path_drive_root() {
    assert_eq!(normalize_path("c:").as_ref(), "c:/");
}

#[test]
fn test_get_normalized_absolute_path() {
    let dir = |d: &str| RootedDirectoryPath::from(d);
    assert_eq!(get_normalized_absolute_path("/", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/.", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/./", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/../", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/a", &dir("")).as_ref(), "/a");
    assert_eq!(get_normalized_absolute_path("/a/", &dir("")).as_ref(), "/a");
    assert_eq!(get_normalized_absolute_path("/a/.", &dir("")).as_ref(), "/a");
    assert_eq!(get_normalized_absolute_path("/a/foo.", &dir("")).as_ref(), "/a/foo.");
    assert_eq!(get_normalized_absolute_path("/a/./", &dir("")).as_ref(), "/a");
    assert_eq!(get_normalized_absolute_path("/a/./b", &dir("")).as_ref(), "/a/b");
    assert_eq!(get_normalized_absolute_path("/a/./b/", &dir("")).as_ref(), "/a/b");
    assert_eq!(get_normalized_absolute_path("/a/..", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/a/../", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/a/../", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/a/../b", &dir("")).as_ref(), "/b");
    assert_eq!(get_normalized_absolute_path("/a/../b/", &dir("")).as_ref(), "/b");
    assert_eq!(get_normalized_absolute_path("/a/..", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/a/..", &dir("/")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/a/..", &dir("b/")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/a/..", &dir("/b")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("/a/.", &dir("b")).as_ref(), "/a");
    assert_eq!(get_normalized_absolute_path("/a/.", &dir(".")).as_ref(), "/a");

    // Tests as above, but with backslashes.
    assert_eq!(get_normalized_absolute_path("\\", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\.", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\.\\", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\..\\", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\a\\.\\", &dir("")).as_ref(), "/a");
    assert_eq!(get_normalized_absolute_path("\\a\\.\\b", &dir("")).as_ref(), "/a/b");
    assert_eq!(get_normalized_absolute_path("\\a\\.\\b\\", &dir("")).as_ref(), "/a/b");
    assert_eq!(get_normalized_absolute_path("\\a\\..", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\a\\..\\", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\a\\..\\", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\a\\..\\b", &dir("")).as_ref(), "/b");
    assert_eq!(get_normalized_absolute_path("\\a\\..\\b\\", &dir("")).as_ref(), "/b");
    assert_eq!(get_normalized_absolute_path("\\a\\..", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\a\\..", &dir("\\")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\a\\..", &dir("b\\")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\a\\..", &dir("\\b")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\a\\.", &dir("b")).as_ref(), "/a");
    assert_eq!(get_normalized_absolute_path("\\a\\.", &dir(".")).as_ref(), "/a");

    // Relative paths on an empty currentDirectory.
    assert_eq!(get_normalized_absolute_path("", &dir("")).as_ref(), "");
    assert_eq!(get_normalized_absolute_path(".", &dir("")).as_ref(), "");
    assert_eq!(get_normalized_absolute_path("./", &dir("")).as_ref(), "");
    // Strangely, these do not normalize to the empty string.
    assert_eq!(get_normalized_absolute_path("..", &dir("")).as_ref(), "..");
    assert_eq!(get_normalized_absolute_path("../", &dir("")).as_ref(), "..");

    // Interaction between relative paths and currentDirectory.
    assert_eq!(get_normalized_absolute_path("", &dir("/home")).as_ref(), "/home");
    assert_eq!(get_normalized_absolute_path(".", &dir("/home")).as_ref(), "/home");
    assert_eq!(get_normalized_absolute_path("./", &dir("/home")).as_ref(), "/home");
    assert_eq!(get_normalized_absolute_path("..", &dir("/home")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("../", &dir("/home")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("a", &dir("b")).as_ref(), "b/a");
    assert_eq!(get_normalized_absolute_path("a", &dir("b/c")).as_ref(), "b/c/a");

    // Base names starting or ending with a dot do not affect normalization.
    assert_eq!(get_normalized_absolute_path(".a", &dir("")).as_ref(), ".a");
    assert_eq!(get_normalized_absolute_path("..a", &dir("")).as_ref(), "..a");
    assert_eq!(get_normalized_absolute_path("a.", &dir("")).as_ref(), "a.");
    assert_eq!(get_normalized_absolute_path("a..", &dir("")).as_ref(), "a..");

    assert_eq!(get_normalized_absolute_path("/base/./.a", &dir("")).as_ref(), "/base/.a");
    assert_eq!(get_normalized_absolute_path("/base/../.a", &dir("")).as_ref(), "/.a");
    assert_eq!(get_normalized_absolute_path("/base/./..a", &dir("")).as_ref(), "/base/..a");
    assert_eq!(get_normalized_absolute_path("/base/../..a", &dir("")).as_ref(), "/..a");
    assert_eq!(get_normalized_absolute_path("/base/./..a/b", &dir("")).as_ref(), "/base/..a/b");
    assert_eq!(get_normalized_absolute_path("/base/../..a/b", &dir("")).as_ref(), "/..a/b");

    assert_eq!(get_normalized_absolute_path("/base/./a.", &dir("")).as_ref(), "/base/a.");
    assert_eq!(get_normalized_absolute_path("/base/../a.", &dir("")).as_ref(), "/a.");
    assert_eq!(get_normalized_absolute_path("/base/./a..", &dir("")).as_ref(), "/base/a..");
    assert_eq!(get_normalized_absolute_path("/base/../a..", &dir("")).as_ref(), "/a..");
    assert_eq!(get_normalized_absolute_path("/base/./a../b", &dir("")).as_ref(), "/base/a../b");
    assert_eq!(get_normalized_absolute_path("/base/../a../b", &dir("")).as_ref(), "/a../b");

    assert_eq!(get_normalized_absolute_path("a/..", &dir("")).as_ref(), "");
    assert_eq!(get_normalized_absolute_path("/a//", &dir("")).as_ref(), "/a");
    assert_eq!(get_normalized_absolute_path("//a", &dir("a")).as_ref(), "//a/");
    assert_eq!(get_normalized_absolute_path("/\\", &dir("")).as_ref(), "//");
    assert_eq!(get_normalized_absolute_path("a///", &dir("a")).as_ref(), "a/a");
    assert_eq!(get_normalized_absolute_path("/.//", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("//\\\\", &dir("")).as_ref(), "///");
    assert_eq!(get_normalized_absolute_path(".//a", &dir(".")).as_ref(), "a");
    assert_eq!(get_normalized_absolute_path("a/../..", &dir("")).as_ref(), "..");
    assert_eq!(get_normalized_absolute_path("../..", &dir("\\a")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("a:", &dir("b")).as_ref(), "a:/");
    assert_eq!(get_normalized_absolute_path("a/../..", &dir("..")).as_ref(), "../..");
    assert_eq!(get_normalized_absolute_path("a/../..", &dir("b")).as_ref(), "");
    assert_eq!(get_normalized_absolute_path("a//../..", &dir("..")).as_ref(), "../..");

    // Consecutive intermediate slashes are normalized to a single slash.
    assert_eq!(get_normalized_absolute_path("a//b", &dir("")).as_ref(), "a/b");
    assert_eq!(get_normalized_absolute_path("a///b", &dir("")).as_ref(), "a/b");
    assert_eq!(get_normalized_absolute_path("a/b//c", &dir("")).as_ref(), "a/b/c");
    assert_eq!(get_normalized_absolute_path("/a/b//c", &dir("")).as_ref(), "/a/b/c");
    assert_eq!(get_normalized_absolute_path("//a/b//c", &dir("")).as_ref(), "//a/b/c");

    // Backslashes are converted to slashes,
    // and then consecutive intermediate slashes are normalized to a single slash
    assert_eq!(get_normalized_absolute_path("a\\\\b", &dir("")).as_ref(), "a/b");
    assert_eq!(get_normalized_absolute_path("a\\\\\\b", &dir("")).as_ref(), "a/b");
    assert_eq!(get_normalized_absolute_path("a\\b\\\\c", &dir("")).as_ref(), "a/b/c");
    assert_eq!(get_normalized_absolute_path("\\a\\b\\\\c", &dir("")).as_ref(), "/a/b/c");
    assert_eq!(get_normalized_absolute_path("\\\\a\\b\\\\c", &dir("")).as_ref(), "//a/b/c");

    // The same occurs for mixed slashes.
    assert_eq!(get_normalized_absolute_path("a/\\b", &dir("")).as_ref(), "a/b");
    assert_eq!(get_normalized_absolute_path("a\\/b", &dir("")).as_ref(), "a/b");
    assert_eq!(get_normalized_absolute_path("a\\/\\b", &dir("")).as_ref(), "a/b");
    assert_eq!(get_normalized_absolute_path("a\\b//c", &dir("")).as_ref(), "a/b/c");
    assert_eq!(get_normalized_absolute_path("\\a\\b\\\\c", &dir("")).as_ref(), "/a/b/c");
    assert_eq!(get_normalized_absolute_path("\\\\a\\b\\\\c", &dir("")).as_ref(), "//a/b/c");
}

#[test]
fn test_get_relative_path_to_directory_or_url() {
    // !!!
    // Based on tests for `getRelativePathFromDirectory`.

    assert_eq!(
        get_relative_path_to_directory_or_url("/", "/", false, CaseSensitivity::CaseInsensitive),
        ""
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("/a", "/a", false, CaseSensitivity::CaseInsensitive),
        ""
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("/a/", "/a", false, CaseSensitivity::CaseInsensitive),
        ""
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("/a", "/", false, CaseSensitivity::CaseInsensitive),
        ".."
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("/a", "/b", false, CaseSensitivity::CaseInsensitive),
        "../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("/a/b", "/b", false, CaseSensitivity::CaseInsensitive),
        "../../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("/a/b/c", "/b", false, CaseSensitivity::CaseInsensitive),
        "../../../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("/a/b/c", "/b/c", false, CaseSensitivity::CaseInsensitive),
        "../../../b/c"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("/a/b/c", "/a/b", false, CaseSensitivity::CaseInsensitive),
        ".."
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("c:", "d:", false, CaseSensitivity::CaseInsensitive),
        "d:/"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///", "file:///", false, CaseSensitivity::CaseInsensitive),
        ""
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///a", "file:///a", false, CaseSensitivity::CaseInsensitive),
        ""
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///a/", "file:///a", false, CaseSensitivity::CaseInsensitive),
        ""
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///a", "file:///", false, CaseSensitivity::CaseInsensitive),
        ".."
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///a", "file:///b", false, CaseSensitivity::CaseInsensitive),
        "../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///a/b", "file:///b", false, CaseSensitivity::CaseInsensitive),
        "../../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///a/b/c", "file:///b", false, CaseSensitivity::CaseInsensitive),
        "../../../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///a/b/c", "file:///b/c", false, CaseSensitivity::CaseInsensitive),
        "../../../b/c"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///a/b/c", "file:///a/b", false, CaseSensitivity::CaseInsensitive),
        ".."
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("file:///c:", "file:///d:", false, CaseSensitivity::CaseInsensitive),
        "file:///d:/"
    );
}

#[test]
fn test_to_file_name_lower_case() {
    assert_eq!(
        to_file_name_lower_case("/user/UserName/projects/Project/file.ts").as_ref(),
        "/user/username/projects/project/file.ts"
    );
    assert_eq!(
        to_file_name_lower_case("/user/UserName/projects/projectß/file.ts").as_ref(),
        "/user/username/projects/projectß/file.ts"
    );
    assert_eq!(
        to_file_name_lower_case("/user/UserName/projects/\u{0130}project/file.ts").as_ref(),
        "/user/username/projects/\u{0130}project/file.ts"
    );
    assert_eq!(
        to_file_name_lower_case("/user/UserName/projects/\u{0131}/file.ts").as_ref(),
        "/user/username/projects/\u{0131}/file.ts"
    );
}

#[test]
fn test_case_sensitivity_trim_prefix() {
    // case-sensitive exact match
    let (suffix, ok) = CaseSensitivity::CaseSensitive.trim_prefix("/project/src/file.ts", "/project/src");
    assert!(ok);
    assert_eq!(suffix, "/file.ts");

    // case-sensitive mismatch
    let (suffix, ok) = CaseSensitivity::CaseSensitive.trim_prefix("/project/SRC/file.ts", "/project/src");
    assert!(!ok);
    assert_eq!(suffix, "/project/SRC/file.ts");

    // case-insensitive match
    let (suffix, ok) = CaseSensitivity::CaseInsensitive.trim_prefix("/project/SRC/file.ts", "/project/src");
    assert!(ok);
    assert_eq!(suffix, "/file.ts");

    // no match
    let (suffix, ok) = CaseSensitivity::CaseInsensitive.trim_prefix("/other/file.ts", "/project/src");
    assert!(!ok);
    assert_eq!(suffix, "/other/file.ts");

    // case-folding shrinks prefix byte length without changing rune count
    // Each Kelvin sign '\u212A' case-folds to the single-byte 'k', so the raw
    // (non-canonicalized) prefix is longer, in bytes, than the path it's a
    // case-insensitive prefix of, even though the path itself is longer overall
    // once its own (already-lowercase) suffix is included. Slicing path by
    // len(prefix) bytes would panic here ([10:9]); TrimPrefix must
    // clamp per-rune instead, like the reference implementation's substring
    // does.
    let (suffix, ok) = CaseSensitivity::CaseInsensitive.trim_prefix("/kkk/a.ts", "/\u{212A}\u{212A}\u{212A}");
    assert!(ok);
    assert_eq!(suffix, "/a.ts");

    // path equal to prefix
    let (suffix, ok) = CaseSensitivity::CaseSensitive.trim_prefix("/project/src", "/project/src");
    assert!(ok);
    assert_eq!(suffix, "");
}

#[test]
fn test_path_is_relative() {
    let mut path_is_relative_tests: Vec<(String, bool)> = vec![
        // relative
        (".".to_string(), true),
        ("..".to_string(), true),
        ("./".to_string(), true),
        ("../".to_string(), true),
        ("./foo/bar".to_string(), true),
        ("../foo/bar".to_string(), true),
        (format!("../{}", "foo/".repeat(100)), true),
        // non-relative
        ("".to_string(), false),
        ("foo".to_string(), false),
        ("foo/bar".to_string(), false),
        ("/foo/bar".to_string(), false),
        ("c:/foo/bar".to_string(), false),
    ];
    // Go: init() appends backslash variants of each entry.
    let backslash_variants: Vec<(String, bool)> = path_is_relative_tests
        .iter()
        .map(|(p, is_relative)| (p.replace('/', "\\"), *is_relative))
        .collect();
    path_is_relative_tests.extend(backslash_variants);

    for (p, is_relative) in &path_is_relative_tests {
        assert_eq!(path_is_relative(p), *is_relative, "PathIsRelative({p:?})");
    }
}

#[test]
fn test_get_common_parents() {
    let opts = CaseSensitivity::CaseInsensitive;

    // empty input
    let paths: &[&str] = &[];
    let (got, ignored) = get_common_parents(paths, 1, get_path_components, opts);
    assert!(ignored.is_empty());
    assert!(got.is_empty());

    // single path returns itself
    let paths: &[&str] = &["/a/b/c/d"];
    let (got, ignored) = get_common_parents(paths, 1, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&[paths[0]]);
    assert_eq!(got, expected);

    // paths shorter than minComponents are ignored
    let paths: &[&str] = &["/a/b/c/d", "/a/b/c/e", "/a/b/f/g", "/x/y"];
    let (got, ignored) = get_common_parents(paths, 4, get_path_components, opts);
    assert_eq!(ignored, FxHashSet::from_iter(["/x/y".to_string()]));
    let expected = ss(&["/a/b/c", "/a/b/f/g"]);
    assert_eq!(got, expected);

    // three paths share /a/b
    let paths: &[&str] = &["/a/b/c/d", "/a/b/c/e", "/a/b/f/g"];
    let (got, ignored) = get_common_parents(paths, 1, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&["/a/b"]);
    assert_eq!(got, expected);

    // mixed with short path collapses to root when minComponents=1
    let paths: &[&str] = &["/a/b/c/d", "/a/b/c/e", "/a/b/f/g", "/x/y/z"];
    let (got, ignored) = get_common_parents(paths, 1, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&["/"]);
    assert_eq!(got, expected);

    // mixed with short path preserves both when minComponents=3
    let paths: &[&str] = &["/a/b/c/d", "/a/b/c/e", "/a/b/f/g", "/x/y/z"];
    let (got, ignored) = get_common_parents(paths, 3, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&["/a/b", "/x/y/z"]);
    assert_eq!(got, expected);

    // different volumes are returned individually
    let paths: &[&str] = &["c:/a/b/c/d", "d:/a/b/c/d"];
    let (got, ignored) = get_common_parents(paths, 1, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&[paths[0], paths[1]]);
    assert_eq!(got, expected);

    // duplicate paths deduplicate result
    let paths: &[&str] = &["/a/b/c/d", "/a/b/c/d"];
    let (got, ignored) = get_common_parents(paths, 1, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&[paths[0]]);
    assert_eq!(got, expected);

    // paths with few components are returned as-is when minComponents met
    let paths: &[&str] = &["/a/b/c/d", "/x/y"];
    let (got, ignored) = get_common_parents(paths, 2, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&["/a/b/c/d", "/x/y"]);
    assert_eq!(got, expected);

    // minComponents=2
    let paths: &[&str] = &["/a/b/c/d", "/a/z/c/e", "/a/aaa/f/g", "/x/y/z"];
    let (got, ignored) = get_common_parents(paths, 2, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&["/a", "/x/y/z"]);
    assert_eq!(got, expected);

    // trailing separators are handled
    let paths: &[&str] = &["/a/b/", "/a/b/c"];
    let (got, ignored) = get_common_parents(paths, 1, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&["/a/b"]);
    assert_eq!(got, expected);

    // nested fan-out keeps every result
    let paths: &[&str] = &["/a/x/1/p", "/a/x/2/q", "/a/y/3/r"];
    let (got, ignored) = get_common_parents(paths, 4, get_path_components, opts);
    assert!(ignored.is_empty());
    let expected = ss(&["/a/x/1/p", "/a/x/2/q", "/a/y/3/r"]);
    assert_eq!(got, expected);
}
