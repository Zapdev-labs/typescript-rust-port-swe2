// Ported from tsc/internal/tspath/path_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go benchmarks (BenchmarkCombinePaths, BenchmarkGetNormalizedAbsolutePath,
// BenchmarkToFileNameLowerCase, BenchmarkHasRelativePathSegment,
// BenchmarkPathIsRelative) have no stable-Rust cargo test equivalent and are
// omitted, as is the shortenName helper they use for sub-benchmark names.
// The Go fuzz tests (FuzzGetNormalizedAbsolutePath, FuzzToFileNameLowerCase,
// FuzzHasRelativePathSegment) are differential tests that run each seed-corpus
// entry through the optimized implementation and an older reference
// implementation; those are ported below as regular tests over the same corpora
// (see the *_differential tests at the bottom of this file).

use rustc_hash::FxHashSet;

use crate::path::{get_common_parents, has_relative_path_segment, reduce_path_components};
use crate::stringutil_shim::go_to_lower;
use crate::{
    CaseSensitivity, RootedDirectoryPath, combine_paths, ensure_trailing_directory_separator,
    get_directory_path, get_longest_extension_from_path, get_normalized_absolute_path,
    get_normalized_path_components, get_path_components, get_path_from_path_components,
    get_relative_path_to_directory_or_url, get_root_length, has_trailing_directory_separator,
    is_rooted_disk_path, is_url, normalize_path, normalize_slashes, path_is_absolute,
    path_is_relative, remove_any_file_extension, resolve_path,
    resolve_path_without_trailing_directory_separator, to_file_name_lower_case,
    to_rooted_directory_path,
};

fn ss(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

#[test]
fn test_normalize_slashes() {
    assert_eq!(normalize_slashes("a").as_ref(), "a");
    assert_eq!(normalize_slashes("a/b").as_ref(), "a/b");
    assert_eq!(normalize_slashes("a\\b").as_ref(), "a/b");
    assert_eq!(
        normalize_slashes("\\\\server\\path").as_ref(),
        "//server/path"
    );
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
    assert_eq!(
        get_directory_path("\\\\server\\share").as_ref(),
        "//server/"
    );
    assert_eq!(
        get_directory_path("\\\\server\\share\\").as_ref(),
        "//server/"
    );
    assert_eq!(get_directory_path("file:///").as_ref(), "file:///");
    assert_eq!(get_directory_path("file:///path").as_ref(), "file:///");
    assert_eq!(get_directory_path("file:///path/").as_ref(), "file:///");
    assert_eq!(get_directory_path("file:///c:").as_ref(), "file:///c:");
    assert_eq!(get_directory_path("file:///c:d").as_ref(), "file:///");
    assert_eq!(get_directory_path("file:///c:/").as_ref(), "file:///c:/");
    assert_eq!(
        get_directory_path("file:///c:/path").as_ref(),
        "file:///c:/"
    );
    assert_eq!(
        get_directory_path("file:///c:/path/").as_ref(),
        "file:///c:/"
    );
    assert_eq!(
        get_directory_path("file://server").as_ref(),
        "file://server"
    );
    assert_eq!(
        get_directory_path("file://server/").as_ref(),
        "file://server/"
    );
    assert_eq!(
        get_directory_path("file://server/path").as_ref(),
        "file://server/"
    );
    assert_eq!(
        get_directory_path("file://server/path/").as_ref(),
        "file://server/"
    );
    assert_eq!(
        get_directory_path("http://server").as_ref(),
        "http://server"
    );
    assert_eq!(
        get_directory_path("http://server/").as_ref(),
        "http://server/"
    );
    assert_eq!(
        get_directory_path("http://server/path").as_ref(),
        "http://server/"
    );
    assert_eq!(
        get_directory_path("http://server/path/").as_ref(),
        "http://server/"
    );
}

#[test]
fn test_get_longest_extension_from_path() {
    let extensions: &[&str] = &[".z", ".y.z", ".other"];
    assert_eq!(
        get_longest_extension_from_path(
            "/src/Component.y.z",
            extensions,
            CaseSensitivity::CaseSensitive
        ),
        ".y.z"
    );
    assert_eq!(
        get_longest_extension_from_path(
            "/src/Component.z",
            extensions,
            CaseSensitivity::CaseSensitive
        ),
        ".z"
    );
    assert_eq!(
        get_longest_extension_from_path(
            "/src/Component.y.Z",
            extensions,
            CaseSensitivity::CaseSensitive
        ),
        ""
    );
    assert_eq!(
        get_longest_extension_from_path(
            "/src/Component.y.Z",
            extensions,
            CaseSensitivity::CaseInsensitive
        ),
        ".y.Z"
    );
}

#[test]
fn test_remove_any_file_extension() {
    assert_eq!(
        remove_any_file_extension("/src/Component.vue").as_ref(),
        "/src/Component"
    );
    assert_eq!(
        remove_any_file_extension("/src/Component.d.ts").as_ref(),
        "/src/Component"
    );
    assert_eq!(
        remove_any_file_extension("/src/Component").as_ref(),
        "/src/Component"
    );
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
    assert_eq!(
        get_path_components("//server/share"),
        ss(&["//server/", "share"])
    );
    assert_eq!(get_path_components("file:///"), ss(&["file:///"]));
    assert_eq!(
        get_path_components("file:///path"),
        ss(&["file:///", "path"])
    );
    assert_eq!(get_path_components("file:///c:"), ss(&["file:///c:"]));
    assert_eq!(get_path_components("file:///c:d"), ss(&["file:///", "c:d"]));
    assert_eq!(get_path_components("file:///c:/"), ss(&["file:///c:/"]));
    assert_eq!(
        get_path_components("file:///c:/path"),
        ss(&["file:///c:/", "path"])
    );
    assert_eq!(get_path_components("file://server"), ss(&["file://server"]));
    assert_eq!(
        get_path_components("file://server/"),
        ss(&["file://server/"])
    );
    assert_eq!(
        get_path_components("file://server/path"),
        ss(&["file://server/", "path"])
    );
    assert_eq!(get_path_components("http://server"), ss(&["http://server"]));
    assert_eq!(
        get_path_components("http://server/"),
        ss(&["http://server/"])
    );
    assert_eq!(
        get_path_components("http://server/path"),
        ss(&["http://server/", "path"])
    );
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
    assert_eq!(
        combine_paths("path", &["to", "file.ext"]),
        "path/to/file.ext"
    );
    assert_eq!(
        combine_paths("path", &["dir", "..", "to", "file.ext"]),
        "path/dir/../to/file.ext"
    );
    // POSIX
    assert_eq!(
        combine_paths("/path", &["to", "file.ext"]),
        "/path/to/file.ext"
    );
    assert_eq!(combine_paths("/path", &["/to", "file.ext"]), "/to/file.ext");
    // DOS
    assert_eq!(
        combine_paths("c:/path", &["to", "file.ext"]),
        "c:/path/to/file.ext"
    );
    assert_eq!(
        combine_paths("c:/path", &["c:/to", "file.ext"]),
        "c:/to/file.ext"
    );
    // URL
    assert_eq!(
        combine_paths("file:///path", &["to", "file.ext"]),
        "file:///path/to/file.ext"
    );
    assert_eq!(
        combine_paths("file:///path", &["file:///to", "file.ext"]),
        "file:///to/file.ext"
    );

    assert_eq!(
        combine_paths("/", &["/node_modules/@types"]),
        "/node_modules/@types"
    );
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
    assert_eq!(
        resolve_path_without_trailing_directory_separator("/", &[]),
        "/"
    );
    assert_eq!(
        resolve_path_without_trailing_directory_separator("c:/", &[]),
        "c:/"
    );
    assert_eq!(
        resolve_path_without_trailing_directory_separator("/a/", &[]),
        "/a"
    );
    assert_eq!(
        resolve_path_without_trailing_directory_separator("a", &["b/"]),
        "a/b"
    );
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
    assert_eq!(
        get_normalized_absolute_path("/a/.", &dir("")).as_ref(),
        "/a"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/foo.", &dir("")).as_ref(),
        "/a/foo."
    );
    assert_eq!(
        get_normalized_absolute_path("/a/./", &dir("")).as_ref(),
        "/a"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/./b", &dir("")).as_ref(),
        "/a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/./b/", &dir("")).as_ref(),
        "/a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/..", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/../", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/../", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/../b", &dir("")).as_ref(),
        "/b"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/../b/", &dir("")).as_ref(),
        "/b"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/..", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/..", &dir("/")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/..", &dir("b/")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/..", &dir("/b")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/.", &dir("b")).as_ref(),
        "/a"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/.", &dir(".")).as_ref(),
        "/a"
    );

    // Tests as above, but with backslashes.
    assert_eq!(get_normalized_absolute_path("\\", &dir("")).as_ref(), "/");
    assert_eq!(get_normalized_absolute_path("\\.", &dir("")).as_ref(), "/");
    assert_eq!(
        get_normalized_absolute_path("\\.\\", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("\\..\\", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\.\\", &dir("")).as_ref(),
        "/a"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\.\\b", &dir("")).as_ref(),
        "/a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\.\\b\\", &dir("")).as_ref(),
        "/a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\..", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\..\\", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\..\\", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\..\\b", &dir("")).as_ref(),
        "/b"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\..\\b\\", &dir("")).as_ref(),
        "/b"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\..", &dir("")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\..", &dir("\\")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\..", &dir("b\\")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\..", &dir("\\b")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\.", &dir("b")).as_ref(),
        "/a"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\.", &dir(".")).as_ref(),
        "/a"
    );

    // Relative paths on an empty currentDirectory.
    assert_eq!(get_normalized_absolute_path("", &dir("")).as_ref(), "");
    assert_eq!(get_normalized_absolute_path(".", &dir("")).as_ref(), "");
    assert_eq!(get_normalized_absolute_path("./", &dir("")).as_ref(), "");
    // Strangely, these do not normalize to the empty string.
    assert_eq!(get_normalized_absolute_path("..", &dir("")).as_ref(), "..");
    assert_eq!(get_normalized_absolute_path("../", &dir("")).as_ref(), "..");

    // Interaction between relative paths and currentDirectory.
    assert_eq!(
        get_normalized_absolute_path("", &dir("/home")).as_ref(),
        "/home"
    );
    assert_eq!(
        get_normalized_absolute_path(".", &dir("/home")).as_ref(),
        "/home"
    );
    assert_eq!(
        get_normalized_absolute_path("./", &dir("/home")).as_ref(),
        "/home"
    );
    assert_eq!(
        get_normalized_absolute_path("..", &dir("/home")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("../", &dir("/home")).as_ref(),
        "/"
    );
    assert_eq!(get_normalized_absolute_path("a", &dir("b")).as_ref(), "b/a");
    assert_eq!(
        get_normalized_absolute_path("a", &dir("b/c")).as_ref(),
        "b/c/a"
    );

    // Base names starting or ending with a dot do not affect normalization.
    assert_eq!(get_normalized_absolute_path(".a", &dir("")).as_ref(), ".a");
    assert_eq!(
        get_normalized_absolute_path("..a", &dir("")).as_ref(),
        "..a"
    );
    assert_eq!(get_normalized_absolute_path("a.", &dir("")).as_ref(), "a.");
    assert_eq!(
        get_normalized_absolute_path("a..", &dir("")).as_ref(),
        "a.."
    );

    assert_eq!(
        get_normalized_absolute_path("/base/./.a", &dir("")).as_ref(),
        "/base/.a"
    );
    assert_eq!(
        get_normalized_absolute_path("/base/../.a", &dir("")).as_ref(),
        "/.a"
    );
    assert_eq!(
        get_normalized_absolute_path("/base/./..a", &dir("")).as_ref(),
        "/base/..a"
    );
    assert_eq!(
        get_normalized_absolute_path("/base/../..a", &dir("")).as_ref(),
        "/..a"
    );
    assert_eq!(
        get_normalized_absolute_path("/base/./..a/b", &dir("")).as_ref(),
        "/base/..a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("/base/../..a/b", &dir("")).as_ref(),
        "/..a/b"
    );

    assert_eq!(
        get_normalized_absolute_path("/base/./a.", &dir("")).as_ref(),
        "/base/a."
    );
    assert_eq!(
        get_normalized_absolute_path("/base/../a.", &dir("")).as_ref(),
        "/a."
    );
    assert_eq!(
        get_normalized_absolute_path("/base/./a..", &dir("")).as_ref(),
        "/base/a.."
    );
    assert_eq!(
        get_normalized_absolute_path("/base/../a..", &dir("")).as_ref(),
        "/a.."
    );
    assert_eq!(
        get_normalized_absolute_path("/base/./a../b", &dir("")).as_ref(),
        "/base/a../b"
    );
    assert_eq!(
        get_normalized_absolute_path("/base/../a../b", &dir("")).as_ref(),
        "/a../b"
    );

    assert_eq!(get_normalized_absolute_path("a/..", &dir("")).as_ref(), "");
    assert_eq!(
        get_normalized_absolute_path("/a//", &dir("")).as_ref(),
        "/a"
    );
    assert_eq!(
        get_normalized_absolute_path("//a", &dir("a")).as_ref(),
        "//a/"
    );
    assert_eq!(get_normalized_absolute_path("/\\", &dir("")).as_ref(), "//");
    assert_eq!(
        get_normalized_absolute_path("a///", &dir("a")).as_ref(),
        "a/a"
    );
    assert_eq!(get_normalized_absolute_path("/.//", &dir("")).as_ref(), "/");
    assert_eq!(
        get_normalized_absolute_path("//\\\\", &dir("")).as_ref(),
        "///"
    );
    assert_eq!(
        get_normalized_absolute_path(".//a", &dir(".")).as_ref(),
        "a"
    );
    assert_eq!(
        get_normalized_absolute_path("a/../..", &dir("")).as_ref(),
        ".."
    );
    assert_eq!(
        get_normalized_absolute_path("../..", &dir("\\a")).as_ref(),
        "/"
    );
    assert_eq!(
        get_normalized_absolute_path("a:", &dir("b")).as_ref(),
        "a:/"
    );
    assert_eq!(
        get_normalized_absolute_path("a/../..", &dir("..")).as_ref(),
        "../.."
    );
    assert_eq!(
        get_normalized_absolute_path("a/../..", &dir("b")).as_ref(),
        ""
    );
    assert_eq!(
        get_normalized_absolute_path("a//../..", &dir("..")).as_ref(),
        "../.."
    );

    // Consecutive intermediate slashes are normalized to a single slash.
    assert_eq!(
        get_normalized_absolute_path("a//b", &dir("")).as_ref(),
        "a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("a///b", &dir("")).as_ref(),
        "a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("a/b//c", &dir("")).as_ref(),
        "a/b/c"
    );
    assert_eq!(
        get_normalized_absolute_path("/a/b//c", &dir("")).as_ref(),
        "/a/b/c"
    );
    assert_eq!(
        get_normalized_absolute_path("//a/b//c", &dir("")).as_ref(),
        "//a/b/c"
    );

    // Backslashes are converted to slashes,
    // and then consecutive intermediate slashes are normalized to a single slash
    assert_eq!(
        get_normalized_absolute_path("a\\\\b", &dir("")).as_ref(),
        "a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("a\\\\\\b", &dir("")).as_ref(),
        "a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("a\\b\\\\c", &dir("")).as_ref(),
        "a/b/c"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\b\\\\c", &dir("")).as_ref(),
        "/a/b/c"
    );
    assert_eq!(
        get_normalized_absolute_path("\\\\a\\b\\\\c", &dir("")).as_ref(),
        "//a/b/c"
    );

    // The same occurs for mixed slashes.
    assert_eq!(
        get_normalized_absolute_path("a/\\b", &dir("")).as_ref(),
        "a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("a\\/b", &dir("")).as_ref(),
        "a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("a\\/\\b", &dir("")).as_ref(),
        "a/b"
    );
    assert_eq!(
        get_normalized_absolute_path("a\\b//c", &dir("")).as_ref(),
        "a/b/c"
    );
    assert_eq!(
        get_normalized_absolute_path("\\a\\b\\\\c", &dir("")).as_ref(),
        "/a/b/c"
    );
    assert_eq!(
        get_normalized_absolute_path("\\\\a\\b\\\\c", &dir("")).as_ref(),
        "//a/b/c"
    );
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
        get_relative_path_to_directory_or_url(
            "/a/b",
            "/b",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        "../../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "/a/b/c",
            "/b",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        "../../../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "/a/b/c",
            "/b/c",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        "../../../b/c"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "/a/b/c",
            "/a/b",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        ".."
    );
    assert_eq!(
        get_relative_path_to_directory_or_url("c:", "d:", false, CaseSensitivity::CaseInsensitive),
        "d:/"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///",
            "file:///",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        ""
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///a",
            "file:///a",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        ""
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///a/",
            "file:///a",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        ""
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///a",
            "file:///",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        ".."
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///a",
            "file:///b",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        "../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///a/b",
            "file:///b",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        "../../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///a/b/c",
            "file:///b",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        "../../../b"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///a/b/c",
            "file:///b/c",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        "../../../b/c"
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///a/b/c",
            "file:///a/b",
            false,
            CaseSensitivity::CaseInsensitive
        ),
        ".."
    );
    assert_eq!(
        get_relative_path_to_directory_or_url(
            "file:///c:",
            "file:///d:",
            false,
            CaseSensitivity::CaseInsensitive
        ),
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
    let (suffix, ok) =
        CaseSensitivity::CaseSensitive.trim_prefix("/project/src/file.ts", "/project/src");
    assert!(ok);
    assert_eq!(suffix, "/file.ts");

    // case-sensitive mismatch
    let (suffix, ok) =
        CaseSensitivity::CaseSensitive.trim_prefix("/project/SRC/file.ts", "/project/src");
    assert!(!ok);
    assert_eq!(suffix, "/project/SRC/file.ts");

    // case-insensitive match
    let (suffix, ok) =
        CaseSensitivity::CaseInsensitive.trim_prefix("/project/SRC/file.ts", "/project/src");
    assert!(ok);
    assert_eq!(suffix, "/file.ts");

    // no match
    let (suffix, ok) =
        CaseSensitivity::CaseInsensitive.trim_prefix("/other/file.ts", "/project/src");
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
    let (suffix, ok) =
        CaseSensitivity::CaseInsensitive.trim_prefix("/kkk/a.ts", "/\u{212A}\u{212A}\u{212A}");
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

// ---------------------------------------------------------------------------
// Differential tests ported from the Go fuzz tests.
//
// Go's fuzz harness runs each seed-corpus entry through both the optimized
// implementation and an older reference implementation and asserts equality.
// Stable Rust has no fuzzer; we run the same old-vs-new comparison over the
// same seed corpora here.

// Go: normalizePath_old (path_test.go)
fn normalize_path_old(path: &str) -> String {
    let path = normalize_slashes(path).into_owned();
    // Most paths don't require normalization
    if !has_relative_path_segment(&path) {
        return path;
    }
    // Some paths only require cleanup of `/./` or leading `./`
    let simplified = path.replace("/./", "/");
    let simplified = simplified
        .strip_prefix("./")
        .map_or(simplified.clone(), str::to_string);
    if simplified != path && !has_relative_path_segment(&simplified) {
        return simplified;
    }
    // Other paths require full normalization
    let mut normalized =
        get_path_from_path_components(&reduce_path_components(&get_path_components(&path)));
    if !normalized.is_empty() && has_trailing_directory_separator(&path) {
        normalized = ensure_trailing_directory_separator(&normalized).into_owned();
    }
    normalized
}

// Go: getNormalizedAbsolutePath_old (path_test.go)
fn get_normalized_absolute_path_old(file_name: &str, current_directory: &str) -> String {
    get_path_from_path_components(&get_normalized_path_components(
        file_name,
        current_directory,
    ))
}

// Go: normalizedTestDirectory (path_test.go)
fn normalized_test_directory(path: &str) -> RootedDirectoryPath {
    if path.is_empty() {
        return RootedDirectoryPath::from("");
    }
    to_rooted_directory_path(path, &RootedDirectoryPath::from("/"))
}

// Go: FuzzGetNormalizedAbsolutePath, reduced to its seed corpus.
#[test]
fn test_get_normalized_absolute_path_differential() {
    // Go: getNormalizedAbsolutePathTests
    let non_normalized_inputs: &[(&str, &str)] = &[
        ("/.", ""),
        ("/./", ""),
        ("/../", ""),
        ("/a/", ""),
        ("/a/.", ""),
        ("/a/foo.", ""),
        ("/a/./", ""),
        ("/a/./b", ""),
        ("/a/./b/", ""),
        ("/a/..", ""),
        ("/a/../", ""),
        ("/a/../", ""),
        ("/a/../b", ""),
        ("/a/../b/", ""),
        ("/a/..", ""),
        ("/a/..", "/"),
        ("/a/..", "b/"),
        ("/a/..", "/b"),
        ("/a/.", "b"),
        ("/a/.", "."),
    ];
    let normalized_inputs: &[(&str, &str)] = &[
        ("/a/b", ""),
        ("/one/two/three", ""),
        ("/users/root/project/src/foo.ts", ""),
    ];
    let normalized_inputs_long: &[(&str, &str)] = &[
        ("/a/b/c/d/e/f/g/h/i/j/k/l/m/n/o/p/q/r/s/t/u/v/w/x/y/z", ""),
        (
            "/one/two/three/four/five/six/seven/eight/nine/ten/eleven/twelve/thirteen/fourteen/fifteen/sixteen/seventeen/eighteen/nineteen/twenty",
            "",
        ),
        (
            "/users/root/project/src/foo/bar/baz/qux/quux/corge/grault/garply/waldo/fred/plugh/xyzzy/thud",
            "",
        ),
        (
            "/lorem/ipsum/dolor/sit/amet/consectetur/adipiscing/elit/sed/do/eiusmod/tempor/incididunt/ut/labore/et/dolore/magna/aliqua/ut/enim/ad/minim/veniam",
            "",
        ),
    ];

    for &(p, dir) in non_normalized_inputs
        .iter()
        .chain(normalized_inputs)
        .chain(normalized_inputs_long)
    {
        let current_directory = normalized_test_directory(dir);
        assert_eq!(
            get_normalized_absolute_path(p, &current_directory).as_ref(),
            get_normalized_absolute_path_old(p, current_directory.as_string()),
            "p={p:?}, dir={dir:?}"
        );

        // normalizePath_old is not called by any Go test/fuzz function; run the
        // same old-vs-new comparison for normalize_path over the corpus inputs.
        assert_eq!(
            normalize_path(p).as_ref(),
            normalize_path_old(p),
            "normalize_path p={p:?}"
        );
    }
}

// Go: oldToFileNameLowerCase (path_test.go). The Go regexp
// `[^\x{0130}\x{0131}\x{00DF}a-z0-9\\/:\-_. ]+` matches maximal runs of chars
// outside that whitelist and replaces each run with strings.ToLower(run);
// strings.ToLower applies the simple lowercase mapping per rune, so this is
// equivalent to mapping each non-whitelisted char through go_to_lower.
fn old_to_file_name_lower_case(file_name: &str) -> String {
    file_name
        .chars()
        .map(|c| {
            if matches!(c, 'a'..='z' | '0'..='9' | '\\' | '/' | ':' | '-' | '_' | '.' | ' ')
                || c == '\u{0130}'
                || c == '\u{0131}'
                || c == '\u{00DF}'
            {
                c
            } else {
                go_to_lower(c)
            }
        })
        .collect()
}

// Go: FuzzToFileNameLowerCase, reduced to its seed corpus.
#[test]
fn test_to_file_name_lower_case_differential() {
    // Go: toFileNameLowerCaseTests
    let tests = [
        "/path/to/file.ext",
        "/PATH/TO/FILE.EXT",
        "/path/to/FILE.EXT",
        "/user/UserName/projects/Project/file.ts",
        "/user/UserName/projects/projectß/file.ts",
        "/user/UserName/projects/İproject/file.ts",
        "/user/UserName/projects/ı/file.ts",
    ];
    let long = "FoO/".repeat(100);

    for p in tests.iter().copied().chain(std::iter::once(long.as_str())) {
        assert_eq!(
            to_file_name_lower_case(p).as_ref(),
            old_to_file_name_lower_case(p),
            "p={p:?}"
        );
    }
}

// Go: oldHasRelativePathSegment (path_test.go). The Go regexp
// `//|(?:^|/)\.\.?(?:$|/)` matches a literal "//" or a "." / ".." segment.
fn old_has_relative_path_segment(p: &str) -> bool {
    p.contains("//") || p.split('/').any(|seg| seg == "." || seg == "..")
}

// Go: FuzzHasRelativePathSegment, reduced to its seed corpus.
#[test]
fn test_has_relative_path_segment_differential() {
    // Go: hasRelativePathSegmentTests (the `bench` field only selected
    // benchmark inputs; it is omitted here)
    let tests = [
        "//",
        "foo/bar/baz",
        "foo/./baz",
        "foo/../baz",
        "foo/bar/baz/.",
        "./some/path",
        "/foo//bar/",
        "/foo/./bar/../../.",
    ];
    let long = format!("{}..", "foo/".repeat(100));

    for p in tests.iter().copied().chain(std::iter::once(long.as_str())) {
        assert_eq!(
            has_relative_path_segment(p),
            old_has_relative_path_segment(p),
            "p={p:?}"
        );
    }
}
