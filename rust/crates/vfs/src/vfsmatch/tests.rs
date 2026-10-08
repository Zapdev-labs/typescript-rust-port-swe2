// Ported from tsc/internal/vfs/vfsmatch/vfsmatch_test.go
// @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Test cases modeled after TypeScript's matchFiles tests in
// tsc/testdata/fixtures/testRunner/unittests/config/matchFiles.ts

use std::sync::Arc;

use tsc_tspath::{
    CaseSensitivity, RootedDirectoryPath, rooted_directory_path_from_absolute,
    rooted_directory_path_from_normalized, to_rooted_directory_path,
};

use super::*;
use crate::vfs::Vfs;
use crate::{vfstest, wrapvfs};

// caseInsensitiveHost simulates a Windows-like file system
fn case_insensitive_host() -> Arc<dyn Vfs> {
    vfstest::from_map(
        [
            ("/dev/a.ts", ""),
            ("/dev/a.d.ts", ""),
            ("/dev/a.js", ""),
            ("/dev/b.ts", ""),
            ("/dev/b.js", ""),
            ("/dev/c.d.ts", ""),
            ("/dev/z/a.ts", ""),
            ("/dev/z/abz.ts", ""),
            ("/dev/z/aba.ts", ""),
            ("/dev/z/b.ts", ""),
            ("/dev/z/bbz.ts", ""),
            ("/dev/z/bba.ts", ""),
            ("/dev/x/a.ts", ""),
            ("/dev/x/aa.ts", ""),
            ("/dev/x/b.ts", ""),
            ("/dev/x/y/a.ts", ""),
            ("/dev/x/y/b.ts", ""),
            ("/dev/js/a.js", ""),
            ("/dev/js/b.js", ""),
            ("/dev/js/d.min.js", ""),
            ("/dev/js/ab.min.js", ""),
            ("/ext/ext.ts", ""),
            ("/ext/b/a..b.ts", ""),
        ],
        CaseSensitivity::CaseInsensitive,
    )
}

// caseSensitiveHost simulates a Unix-like case-sensitive file system
fn case_sensitive_host() -> Arc<dyn Vfs> {
    vfstest::from_map(
        [
            ("/dev/a.ts", ""),
            ("/dev/a.d.ts", ""),
            ("/dev/a.js", ""),
            ("/dev/b.ts", ""),
            ("/dev/b.js", ""),
            ("/dev/A.ts", ""),
            ("/dev/B.ts", ""),
            ("/dev/c.d.ts", ""),
            ("/dev/z/a.ts", ""),
            ("/dev/z/abz.ts", ""),
            ("/dev/z/aba.ts", ""),
            ("/dev/z/b.ts", ""),
            ("/dev/z/bbz.ts", ""),
            ("/dev/z/bba.ts", ""),
            ("/dev/x/a.ts", ""),
            ("/dev/x/b.ts", ""),
            ("/dev/x/y/a.ts", ""),
            ("/dev/x/y/b.ts", ""),
            ("/dev/q/a/c/b/d.ts", ""),
            ("/dev/js/a.js", ""),
            ("/dev/js/b.js", ""),
            ("/dev/js/d.MIN.js", ""),
        ],
        CaseSensitivity::CaseSensitive,
    )
}

// commonFoldersHost includes node_modules, bower_components, jspm_packages
fn common_folders_host() -> Arc<dyn Vfs> {
    vfstest::from_map(
        [
            ("/dev/a.ts", ""),
            ("/dev/a.d.ts", ""),
            ("/dev/a.js", ""),
            ("/dev/b.ts", ""),
            ("/dev/x/a.ts", ""),
            ("/dev/node_modules/a.ts", ""),
            ("/dev/bower_components/a.ts", ""),
            ("/dev/jspm_packages/a.ts", ""),
        ],
        CaseSensitivity::CaseInsensitive,
    )
}

// dottedFoldersHost includes files and folders starting with a dot
fn dotted_folders_host() -> Arc<dyn Vfs> {
    vfstest::from_map(
        [
            ("/dev/x/d.ts", ""),
            ("/dev/x/y/d.ts", ""),
            ("/dev/x/y/.e.ts", ""),
            ("/dev/x/.y/a.ts", ""),
            ("/dev/.z/.b.ts", ""),
            ("/dev/.z/c.ts", ""),
            ("/dev/w/.u/e.ts", ""),
            ("/dev/g.min.js/.g/g.ts", ""),
        ],
        CaseSensitivity::CaseInsensitive,
    )
}

// mixedExtensionHost has various file extensions
fn mixed_extension_host() -> Arc<dyn Vfs> {
    vfstest::from_map(
        [
            ("/dev/a.ts", ""),
            ("/dev/a.d.ts", ""),
            ("/dev/a.js", ""),
            ("/dev/b.tsx", ""),
            ("/dev/b.d.ts", ""),
            ("/dev/b.jsx", ""),
            ("/dev/c.tsx", ""),
            ("/dev/c.js", ""),
            ("/dev/d.js", ""),
            ("/dev/e.jsx", ""),
            ("/dev/f.other", ""),
        ],
        CaseSensitivity::CaseInsensitive,
    )
}

// sameNamedDeclarationsHost has files with same names but different extensions
fn same_named_declarations_host() -> Arc<dyn Vfs> {
    vfstest::from_map(
        [
            ("/dev/a.tsx", ""),
            ("/dev/a.d.ts", ""),
            ("/dev/b.tsx", ""),
            ("/dev/b.ts", ""),
            ("/dev/c.tsx", ""),
            ("/dev/m.ts", ""),
            ("/dev/m.d.ts", ""),
            ("/dev/n.tsx", ""),
            ("/dev/n.ts", ""),
            ("/dev/n.d.ts", ""),
            ("/dev/o.ts", ""),
            ("/dev/x.d.ts", ""),
        ],
        CaseSensitivity::CaseInsensitive,
    )
}

struct ReadDirCase {
    name: &'static str,
    host: fn() -> Arc<dyn Vfs>,
    current_dir: &'static str,
    path: &'static str,
    extensions: &'static [&'static str],
    excludes: &'static [&'static str],
    includes: &'static [&'static str],
    depth: i64,
    expect: fn(&[String]),
}

fn run_read_directory_case(tc: &ReadDirCase) {
    let current_dir = if tc.current_dir.is_empty() {
        "/"
    } else {
        tc.current_dir
    };
    let path = if tc.path.is_empty() { "/dev" } else { tc.path };
    let depth = if tc.depth == 0 {
        UNLIMITED_DEPTH
    } else {
        tc.depth
    };
    let host = (tc.host)();
    let base_path =
        to_rooted_directory_path(path, &rooted_directory_path_from_absolute(current_dir));
    let got: Vec<String> = match_file_names(
        &base_path,
        tc.extensions,
        tc.excludes,
        tc.includes,
        depth,
        &host,
    )
    .iter()
    .map(|f| f.as_string().to_string())
    .collect();
    (tc.expect)(&got);
}

fn assert_contains(got: &[String], want: &str) {
    assert!(got.iter().any(|g| g == want), "missing {want} in {got:?}");
}
fn assert_not_contains(got: &[String], want: &str) {
    assert!(
        !got.iter().any(|g| g == want),
        "unexpected {want} in {got:?}"
    );
}
fn assert_deep_equal(got: &[String], want: &[&str]) {
    let want: Vec<String> = want.iter().map(|s| s.to_string()).collect();
    assert_eq!(got, &want);
}

const TS_EXTS: &[&str] = &[".ts", ".tsx", ".d.ts"];

#[test]
fn test_read_directory() {
    let cases = [
        ReadDirCase {
            name: "defaults include common package folders",
            host: common_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &[],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/b.ts");
                assert_contains(got, "/dev/x/a.ts");
                assert_contains(got, "/dev/node_modules/a.ts");
                assert_contains(got, "/dev/bower_components/a.ts");
                assert_contains(got, "/dev/jspm_packages/a.ts");
            },
        },
        ReadDirCase {
            name: "literal includes without exclusions",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["a.ts", "b.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/a.ts", "/dev/b.ts"]),
        },
        ReadDirCase {
            name: "literal includes with non ts extensions excluded",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["a.js", "b.js"],
            depth: 0,
            expect: |got| assert_eq!(got.len(), 0),
        },
        ReadDirCase {
            name: "literal includes missing files excluded",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["z.ts", "x.ts"],
            depth: 0,
            expect: |got| assert_eq!(got.len(), 0),
        },
        ReadDirCase {
            name: "literal includes with literal excludes",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["b.ts"],
            includes: &["a.ts", "b.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/a.ts"]),
        },
        ReadDirCase {
            name: "literal includes with wildcard excludes",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["*.ts", "z/??z.ts", "*/b.ts"],
            includes: &["a.ts", "b.ts", "z/a.ts", "z/abz.ts", "z/aba.ts", "x/b.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/z/a.ts", "/dev/z/aba.ts"]),
        },
        ReadDirCase {
            name: "literal includes with recursive excludes",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**/b.ts"],
            includes: &["a.ts", "b.ts", "x/a.ts", "x/b.ts", "x/y/a.ts", "x/y/b.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/a.ts", "/dev/x/a.ts", "/dev/x/y/a.ts"]),
        },
        ReadDirCase {
            name: "case sensitive exclude is respected",
            host: case_sensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**/b.ts"],
            includes: &["B.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/B.ts"]),
        },
        ReadDirCase {
            name: "explicit includes keep common package folders",
            host: common_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &[
                "a.ts",
                "b.ts",
                "node_modules/a.ts",
                "bower_components/a.ts",
                "jspm_packages/a.ts",
            ],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/b.ts");
                assert_contains(got, "/dev/node_modules/a.ts");
                assert_contains(got, "/dev/bower_components/a.ts");
                assert_contains(got, "/dev/jspm_packages/a.ts");
            },
        },
        ReadDirCase {
            name: "wildcard include sorted order",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["z/*.ts", "x/*.ts"],
            depth: 0,
            expect: |got| {
                assert_deep_equal(
                    got,
                    &[
                        "/dev/z/a.ts",
                        "/dev/z/aba.ts",
                        "/dev/z/abz.ts",
                        "/dev/z/b.ts",
                        "/dev/z/bba.ts",
                        "/dev/z/bbz.ts",
                        "/dev/x/a.ts",
                        "/dev/x/aa.ts",
                        "/dev/x/b.ts",
                    ],
                )
            },
        },
        ReadDirCase {
            name: "wildcard include same named declarations excluded",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["*.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/b.ts");
                assert_contains(got, "/dev/a.d.ts");
                assert_contains(got, "/dev/c.d.ts");
            },
        },
        ReadDirCase {
            name: "wildcard star matches only ts files",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["*"],
            depth: 0,
            expect: |got| {
                for f in got {
                    assert!(
                        f.contains(".ts") || f.contains(".tsx") || f.contains(".d.ts"),
                        "unexpected file: {f}"
                    );
                }
                assert_not_contains(got, "/dev/a.js");
                assert_not_contains(got, "/dev/b.js");
            },
        },
        ReadDirCase {
            name: "wildcard question mark single character",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["x/?.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/x/a.ts", "/dev/x/b.ts"]),
        },
        ReadDirCase {
            name: "wildcard recursive directory",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/a.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/z/a.ts");
                assert_contains(got, "/dev/x/a.ts");
                assert_contains(got, "/dev/x/y/a.ts");
            },
        },
        ReadDirCase {
            name: "double asterisk matches zero-or-more directories",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["x/**/a.ts"],
            depth: 0,
            expect: |got| {
                assert_eq!(got.len(), 2);
                assert_contains(got, "/dev/x/a.ts");
                assert_contains(got, "/dev/x/y/a.ts");
            },
        },
        ReadDirCase {
            name: "wildcard multiple recursive directories",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["x/y/**/a.ts", "x/**/a.ts", "z/**/a.ts"],
            depth: 0,
            expect: |got| assert!(got.len() > 0),
        },
        ReadDirCase {
            name: "wildcard case sensitive matching",
            host: case_sensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/A.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/A.ts"]),
        },
        ReadDirCase {
            name: "wildcard missing files excluded",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["*/z.ts"],
            depth: 0,
            expect: |got| assert_eq!(got.len(), 0),
        },
        ReadDirCase {
            name: "exclude folders with wildcards",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["z", "x"],
            includes: &["**/*"],
            depth: 0,
            expect: |got| {
                for f in got {
                    assert!(
                        !f.contains("/z/") && !f.contains("/x/"),
                        "should not contain z or x: {f}"
                    );
                }
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/b.ts");
            },
        },
        ReadDirCase {
            name: "include paths outside project absolute",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["*", "/ext/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/ext/ext.ts");
            },
        },
        ReadDirCase {
            name: "include paths outside project relative",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**"],
            includes: &["*", "../ext/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/ext/ext.ts");
            },
        },
        ReadDirCase {
            name: "include files containing double dots",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**"],
            includes: &["/ext/b/a..b.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/ext/b/a..b.ts");
            },
        },
        ReadDirCase {
            name: "exclude files containing double dots",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["/ext/b/a..b.ts"],
            includes: &["/ext/**/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/ext/ext.ts");
                assert_not_contains(got, "/ext/b/a..b.ts");
            },
        },
        ReadDirCase {
            name: "common package folders implicitly excluded",
            host: common_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/a.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/x/a.ts");
                assert_not_contains(got, "/dev/node_modules/a.ts");
                assert_not_contains(got, "/dev/bower_components/a.ts");
                assert_not_contains(got, "/dev/jspm_packages/a.ts");
            },
        },
        ReadDirCase {
            name: "common package folders explicit recursive include",
            host: common_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/a.ts", "**/node_modules/a.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/node_modules/a.ts");
            },
        },
        ReadDirCase {
            name: "common package folders wildcard include",
            host: common_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["*/a.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/a.ts");
                assert_not_contains(got, "/dev/node_modules/a.ts");
            },
        },
        ReadDirCase {
            name: "common package folders explicit wildcard include",
            host: common_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["*/a.ts", "node_modules/a.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/a.ts");
                assert_contains(got, "/dev/node_modules/a.ts");
            },
        },
        ReadDirCase {
            name: "dotted folders not implicitly included",
            host: dotted_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["x/**/*", "w/*/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/d.ts");
                assert_contains(got, "/dev/x/y/d.ts");
                assert_not_contains(got, "/dev/x/.y/a.ts");
                assert_not_contains(got, "/dev/x/y/.e.ts");
                assert_not_contains(got, "/dev/w/.u/e.ts");
            },
        },
        ReadDirCase {
            name: "dotted folders explicitly included",
            host: dotted_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["x/.y/a.ts", "/dev/.z/.b.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/.y/a.ts");
                assert_contains(got, "/dev/.z/.b.ts");
            },
        },
        ReadDirCase {
            name: "dotted folders recursive wildcard matches directories",
            host: dotted_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/.*/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/.y/a.ts");
                assert_contains(got, "/dev/.z/c.ts");
                assert_contains(got, "/dev/w/.u/e.ts");
            },
        },
        ReadDirCase {
            name: "trailing recursive include returns empty",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**"],
            depth: 0,
            expect: |got| assert_eq!(got.len(), 0),
        },
        ReadDirCase {
            name: "trailing recursive exclude removes everything",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**"],
            includes: &["**/*"],
            depth: 0,
            expect: |got| assert_eq!(got.len(), 0),
        },
        ReadDirCase {
            name: "multiple recursive directory patterns in includes",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/x/**/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/a.ts");
                assert_contains(got, "/dev/x/y/a.ts");
            },
        },
        ReadDirCase {
            name: "multiple recursive directory patterns in excludes",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**/x/**"],
            includes: &["**/a.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/z/a.ts");
                assert_not_contains(got, "/dev/x/a.ts");
                assert_not_contains(got, "/dev/x/y/a.ts");
            },
        },
        ReadDirCase {
            name: "implicit globbification expands directory",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["z"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/z/a.ts");
                assert_contains(got, "/dev/z/aba.ts");
                assert_contains(got, "/dev/z/b.ts");
            },
        },
        ReadDirCase {
            name: "exclude patterns starting with starstar",
            host: case_sensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**/x"],
            includes: &[],
            depth: 0,
            expect: |got| {
                for f in got {
                    assert!(!f.contains("/x/"), "should not contain /x/: {f}");
                }
            },
        },
        ReadDirCase {
            name: "include patterns starting with starstar",
            host: case_sensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/x", "**/a/**/b"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/a.ts");
                assert_contains(got, "/dev/q/a/c/b/d.ts");
            },
        },
        ReadDirCase {
            name: "depth limit one",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &[],
            depth: 1,
            expect: |got| {
                for f in got {
                    let suffix = &f["/dev/".len()..];
                    assert!(
                        !suffix.contains('/'),
                        "depth 1 should not include nested files: {f}"
                    );
                }
            },
        },
        ReadDirCase {
            name: "depth limit two",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &[],
            depth: 2,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/z/a.ts");
                assert_not_contains(got, "/dev/x/y/a.ts");
            },
        },
        ReadDirCase {
            name: "mixed extensions only ts",
            host: mixed_extension_host,
            current_dir: "",
            path: "",
            extensions: &[".ts"],
            excludes: &[],
            includes: &[],
            depth: 0,
            expect: |got| {
                for f in got {
                    assert!(f.ends_with(".ts"), "should only have .ts files: {f}");
                }
            },
        },
        ReadDirCase {
            name: "mixed extensions ts and tsx",
            host: mixed_extension_host,
            current_dir: "",
            path: "",
            extensions: &[".ts", ".tsx"],
            excludes: &[],
            includes: &[],
            depth: 0,
            expect: |got| {
                for f in got {
                    assert!(
                        f.ends_with(".ts") || f.ends_with(".tsx"),
                        "should only have .ts or .tsx files: {f}"
                    );
                }
            },
        },
        ReadDirCase {
            name: "mixed extensions js and jsx",
            host: mixed_extension_host,
            current_dir: "",
            path: "",
            extensions: &[".js", ".jsx"],
            excludes: &[],
            includes: &[],
            depth: 0,
            expect: |got| {
                for f in got {
                    assert!(
                        f.ends_with(".js") || f.ends_with(".jsx"),
                        "should only have .js or .jsx files: {f}"
                    );
                }
            },
        },
        ReadDirCase {
            name: "min js files excluded by wildcard",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".js"],
            excludes: &[],
            includes: &["js/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/js/a.js");
                assert_contains(got, "/dev/js/b.js");
                assert_not_contains(got, "/dev/js/d.min.js");
                assert_not_contains(got, "/dev/js/ab.min.js");
            },
        },
        ReadDirCase {
            name: "min js exclusion is case-sensitive on case-sensitive FS",
            host: case_sensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".js"],
            excludes: &[],
            includes: &["js/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/js/a.js");
                assert_contains(got, "/dev/js/b.js");
                // Legacy behavior: only lowercase ".min.js" is excluded by
                // default when matching is case-sensitive.
                assert_contains(got, "/dev/js/d.MIN.js");
            },
        },
        ReadDirCase {
            name: "min js files explicitly included",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".js"],
            excludes: &[],
            includes: &["js/*.min.js"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/js/d.min.js");
                assert_contains(got, "/dev/js/ab.min.js");
            },
        },
        ReadDirCase {
            name: "min js files included when pattern mentions .min.",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".js"],
            excludes: &[],
            includes: &["js/*.min.*"],
            depth: 0,
            expect: |got| {
                assert_eq!(got.len(), 2);
                assert_contains(got, "/dev/js/d.min.js");
                assert_contains(got, "/dev/js/ab.min.js");
            },
        },
        ReadDirCase {
            name: "exclude literal node_modules folder",
            host: common_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["node_modules"],
            includes: &["**/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_not_contains(got, "/dev/node_modules/a.ts");
            },
        },
        ReadDirCase {
            name: "same named declarations include ts",
            host: same_named_declarations_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["*.ts"],
            depth: 0,
            expect: |got| assert!(got.len() > 0),
        },
        ReadDirCase {
            name: "same named declarations include tsx",
            host: same_named_declarations_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["*.tsx"],
            depth: 0,
            expect: |got| {
                for f in got {
                    assert!(f.ends_with(".tsx"), "should only have .tsx files: {f}");
                }
            },
        },
        ReadDirCase {
            name: "empty includes returns all matching files",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &[],
            depth: 0,
            expect: |got| {
                assert!(got.len() > 0);
                assert_contains(got, "/dev/a.ts");
            },
        },
        ReadDirCase {
            name: "nil extensions returns all files",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[],
            excludes: &[],
            includes: &[],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/a.js");
            },
        },
        ReadDirCase {
            name: "empty extensions slice returns all files",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[],
            excludes: &[],
            includes: &[],
            depth: 0,
            expect: |got| assert!(got.len() > 0, "expected files to be returned"),
        },
    ];

    for tc in &cases {
        run_read_directory_case(tc);
    }
}

// Helper functions (Go's contains / hasSuffix are just str::contains/ends_with).

#[test]
fn test_is_implicit_glob() {
    let tests = [
        ("foo", true),
        ("src", true),
        ("foo.ts", false),
        ("foo.", false),
        ("*", false),
        ("?", false),
        ("foo*", false),
        ("foo?", false),
        ("foo.bar", false),
        ("", true),
    ];
    for (input, expected) in tests {
        assert_eq!(is_implicit_glob(input), expected, "input: {input}");
    }
}

// Edge case tests for various pattern scenarios
fn special_regex_chars_host() -> Arc<dyn Vfs> {
    vfstest::from_map(
        [
            ("/dev/file+test.ts", ""),
            ("/dev/file[0].ts", ""),
            ("/dev/file(1).ts", ""),
            ("/dev/file$money.ts", ""),
            ("/dev/file^start.ts", ""),
            ("/dev/file|pipe.ts", ""),
            ("/dev/file#hash.ts", ""),
        ],
        CaseSensitivity::CaseInsensitive,
    )
}

fn case_mixed_files_host() -> Arc<dyn Vfs> {
    vfstest::from_map(
        [("/dev/File.ts", ""), ("/dev/FILE.ts", "")],
        CaseSensitivity::CaseSensitive,
    )
}

#[test]
fn test_read_directory_edge_cases() {
    let cases = [
        ReadDirCase {
            name: "rooted include path",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".ts"],
            excludes: &[],
            includes: &["/dev/a.ts"],
            depth: 0,
            expect: |got| assert_contains(got, "/dev/a.ts"),
        },
        ReadDirCase {
            name: "include with extension in path",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".ts"],
            excludes: &[],
            includes: &["a.ts"],
            depth: 0,
            expect: |got| assert_contains(got, "/dev/a.ts"),
        },
        ReadDirCase {
            name: "special regex characters in path",
            host: special_regex_chars_host,
            current_dir: "",
            path: "",
            extensions: &[".ts"],
            excludes: &[],
            includes: &["file+test.ts"],
            depth: 0,
            expect: |got| assert_contains(got, "/dev/file+test.ts"),
        },
        ReadDirCase {
            name: "include pattern starting with question mark",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".ts"],
            excludes: &[],
            includes: &["?.ts"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/b.ts");
            },
        },
        ReadDirCase {
            name: "include pattern starting with star",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".ts"],
            excludes: &[],
            includes: &["*b.ts"],
            depth: 0,
            expect: |got| assert_contains(got, "/dev/b.ts"),
        },
        ReadDirCase {
            name: "case insensitive file matching",
            host: case_mixed_files_host,
            current_dir: "",
            path: "",
            extensions: &[".ts"],
            excludes: &[],
            includes: &["*.ts"],
            depth: 0,
            expect: |got| assert_eq!(got.len(), 2),
        },
        ReadDirCase {
            name: "nested subdirectory base path",
            host: case_sensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".ts"],
            excludes: &[],
            includes: &["q/a/c/b/d.ts"],
            depth: 0,
            expect: |got| assert_contains(got, "/dev/q/a/c/b/d.ts"),
        },
        ReadDirCase {
            name: "current directory differs from path",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: &[".ts"],
            excludes: &[],
            includes: &["z/*.ts"],
            depth: 0,
            expect: |got| assert!(got.len() > 0),
        },
    ];

    for tc in &cases {
        run_read_directory_case(tc);
    }
}

#[test]
fn test_read_directory_empty_includes() {
    fn root_host() -> Arc<dyn Vfs> {
        vfstest::from_map([("/root/a.ts", "")], CaseSensitivity::CaseSensitive)
    }

    let cases = [ReadDirCase {
        name: "empty includes slice behavior",
        host: root_host,
        current_dir: "/",
        path: "/root",
        extensions: &[".ts"],
        excludes: &[],
        includes: &[],
        depth: 0,
        expect: |got| {
            if got.is_empty() {
                return;
            }
            assert_contains(got, "/root/a.ts");
        },
    }];

    for tc in &cases {
        run_read_directory_case(tc);
    }
}

/// TestReadDirectorySymlinkCycle tests that cyclic symlinks don't cause
/// infinite loops. The cycle is detected via realpath for cycle detection.
fn symlink_cycle_host() -> Arc<dyn Vfs> {
    vfstest::from_map(
        vec![
            ("/root/file.ts", vfstest::TestFile::from("")),
            ("/root/a/file.ts", vfstest::TestFile::from("")),
            (
                "/root/a/b",
                vfstest::TestFile::from(vfstest::symlink("/root/a")),
            ),
        ],
        CaseSensitivity::CaseSensitive,
    )
}

#[test]
fn test_read_directory_symlink_cycle() {
    let cases = [ReadDirCase {
        name: "detects and skips symlink cycles",
        host: symlink_cycle_host,
        current_dir: "/",
        path: "/root",
        extensions: &[".ts"],
        excludes: &[],
        includes: &["**/*"],
        depth: 0,
        expect: |got| {
            assert_deep_equal(got, &["/root/file.ts", "/root/a/file.ts"]);
        },
    }];

    for tc in &cases {
        run_read_directory_case(tc);
    }
}

/// Tests that verify the implementation matches the promoted TypeScript
/// baseline outputs.
#[test]
fn test_read_directory_matches_type_script_baselines() {
    fn sorted_host() -> Arc<dyn Vfs> {
        vfstest::from_map(
            [
                ("/dev/z/a.ts", ""),
                ("/dev/z/aba.ts", ""),
                ("/dev/z/abz.ts", ""),
                ("/dev/z/b.ts", ""),
                ("/dev/z/bba.ts", ""),
                ("/dev/z/bbz.ts", ""),
                ("/dev/x/a.ts", ""),
                ("/dev/x/aa.ts", ""),
                ("/dev/x/b.ts", ""),
            ],
            CaseSensitivity::CaseInsensitive,
        )
    }
    fn dotted_host() -> Arc<dyn Vfs> {
        vfstest::from_map(
            [
                ("/dev/x/d.ts", ""),
                ("/dev/x/y/d.ts", ""),
                ("/dev/x/y/.e.ts", ""),
                ("/dev/x/.y/a.ts", ""),
                ("/dev/.z/.b.ts", ""),
                ("/dev/.z/c.ts", ""),
                ("/dev/w/.u/e.ts", ""),
                ("/dev/g.min.js/.g/g.ts", ""),
            ],
            CaseSensitivity::CaseInsensitive,
        )
    }
    fn common_host() -> Arc<dyn Vfs> {
        common_folders_host()
    }
    fn js_host() -> Arc<dyn Vfs> {
        vfstest::from_map(
            [
                ("/dev/js/a.js", ""),
                ("/dev/js/b.js", ""),
                ("/dev/js/d.min.js", ""),
                ("/dev/js/ab.min.js", ""),
            ],
            CaseSensitivity::CaseInsensitive,
        )
    }

    let cases = [
        ReadDirCase {
            name: "sorted in include order then alphabetical",
            host: sorted_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["z/*.ts", "x/*.ts"],
            depth: 0,
            expect: |got| {
                assert_deep_equal(
                    got,
                    &[
                        "/dev/z/a.ts",
                        "/dev/z/aba.ts",
                        "/dev/z/abz.ts",
                        "/dev/z/b.ts",
                        "/dev/z/bba.ts",
                        "/dev/z/bbz.ts",
                        "/dev/x/a.ts",
                        "/dev/x/aa.ts",
                        "/dev/x/b.ts",
                    ],
                )
            },
        },
        ReadDirCase {
            name: "recursive wildcards match dotted directories",
            host: dotted_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/.*/*"],
            depth: 0,
            expect: |got| {
                let expected = [
                    "/dev/.z/c.ts",
                    "/dev/g.min.js/.g/g.ts",
                    "/dev/w/.u/e.ts",
                    "/dev/x/.y/a.ts",
                ];
                assert_eq!(got.len(), expected.len());
                for want in expected {
                    assert_contains(got, want);
                }
            },
        },
        ReadDirCase {
            name: "common package folders implicitly excluded with wildcard",
            host: common_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/a.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/a.ts", "/dev/x/a.ts"]),
        },
        ReadDirCase {
            name: "js wildcard excludes min js files",
            host: js_host,
            current_dir: "",
            path: "",
            extensions: &[".js"],
            excludes: &[],
            includes: &["js/*"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/js/a.js", "/dev/js/b.js"]),
        },
        ReadDirCase {
            name: "explicit min js pattern includes min files",
            host: js_host,
            current_dir: "",
            path: "",
            extensions: &[".js"],
            excludes: &[],
            includes: &["js/*.min.js"],
            depth: 0,
            expect: |got| {
                let expected = ["/dev/js/ab.min.js", "/dev/js/d.min.js"];
                assert_eq!(got.len(), expected.len());
                for want in expected {
                    assert_contains(got, want);
                }
            },
        },
        ReadDirCase {
            name: "literal excludes baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["b.ts"],
            includes: &["a.ts", "b.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/a.ts"]),
        },
        ReadDirCase {
            name: "wildcard excludes baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["*.ts", "z/??z.ts", "*/b.ts"],
            includes: &["a.ts", "b.ts", "z/a.ts", "z/abz.ts", "z/aba.ts", "x/b.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/z/a.ts", "/dev/z/aba.ts"]),
        },
        ReadDirCase {
            name: "recursive excludes baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**/b.ts"],
            includes: &["a.ts", "b.ts", "x/a.ts", "x/b.ts", "x/y/a.ts", "x/y/b.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/a.ts", "/dev/x/a.ts", "/dev/x/y/a.ts"]),
        },
        ReadDirCase {
            name: "question mark baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["x/?.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/x/a.ts", "/dev/x/b.ts"]),
        },
        ReadDirCase {
            name: "recursive directory pattern baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/a.ts"],
            depth: 0,
            expect: |got| {
                assert_deep_equal(
                    got,
                    &["/dev/a.ts", "/dev/x/a.ts", "/dev/x/y/a.ts", "/dev/z/a.ts"],
                )
            },
        },
        ReadDirCase {
            name: "case sensitive baseline",
            host: case_sensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/A.ts"],
            depth: 0,
            expect: |got| assert_deep_equal(got, &["/dev/A.ts"]),
        },
        ReadDirCase {
            name: "exclude folders baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["z", "x"],
            includes: &["**/*"],
            depth: 0,
            expect: |got| {
                for f in got {
                    assert!(
                        !f.contains("/z/") && !f.contains("/x/"),
                        "should not contain z or x: {f}"
                    );
                }
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/dev/b.ts");
            },
        },
        ReadDirCase {
            name: "implicit glob expansion baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["z"],
            depth: 0,
            expect: |got| {
                assert_deep_equal(
                    got,
                    &[
                        "/dev/z/a.ts",
                        "/dev/z/aba.ts",
                        "/dev/z/abz.ts",
                        "/dev/z/b.ts",
                        "/dev/z/bba.ts",
                        "/dev/z/bbz.ts",
                    ],
                )
            },
        },
        ReadDirCase {
            name: "trailing recursive directory baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**"],
            depth: 0,
            expect: |got| assert_eq!(got.len(), 0),
        },
        ReadDirCase {
            name: "exclude trailing recursive directory baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**"],
            includes: &["**/*"],
            depth: 0,
            expect: |got| assert_eq!(got.len(), 0),
        },
        ReadDirCase {
            name: "multiple recursive directory patterns baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/x/**/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/a.ts");
                assert_contains(got, "/dev/x/aa.ts");
                assert_contains(got, "/dev/x/b.ts");
                assert_contains(got, "/dev/x/y/a.ts");
                assert_contains(got, "/dev/x/y/b.ts");
            },
        },
        ReadDirCase {
            name: "include dirs with starstar prefix baseline",
            host: case_sensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["**/x", "**/a/**/b"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/a.ts");
                assert_contains(got, "/dev/x/b.ts");
                assert_contains(got, "/dev/q/a/c/b/d.ts");
            },
        },
        ReadDirCase {
            name: "dotted folders not implicitly included baseline",
            host: dotted_folders_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["x/**/*", "w/*/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/x/d.ts");
                assert_contains(got, "/dev/x/y/d.ts");
                assert_not_contains(got, "/dev/x/.y/a.ts");
                assert_not_contains(got, "/dev/x/y/.e.ts");
                assert_not_contains(got, "/dev/w/.u/e.ts");
            },
        },
        ReadDirCase {
            name: "include paths outside project baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &[],
            includes: &["*", "/ext/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/dev/a.ts");
                assert_contains(got, "/ext/ext.ts");
            },
        },
        ReadDirCase {
            name: "include files with double dots baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["**"],
            includes: &["/ext/b/a..b.ts"],
            depth: 0,
            expect: |got| assert_contains(got, "/ext/b/a..b.ts"),
        },
        ReadDirCase {
            name: "exclude files with double dots baseline",
            host: case_insensitive_host,
            current_dir: "",
            path: "",
            extensions: TS_EXTS,
            excludes: &["/ext/b/a..b.ts"],
            includes: &["/ext/**/*"],
            depth: 0,
            expect: |got| {
                assert_contains(got, "/ext/ext.ts");
                assert_not_contains(got, "/ext/b/a..b.ts");
            },
        },
    ];

    for tc in &cases {
        run_read_directory_case(tc);
    }
}

#[test]
fn test_read_directory_with_extended_dynamic_root() {
    let package_directory = "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg";
    let host = vfstest::from_map(
        [
            (
                format!("{package_directory}/value.d.ts"),
                vfstest::TestFile::from(""),
            ),
            (
                format!("{package_directory}/node_modules/dep/index.d.ts"),
                vfstest::TestFile::from(""),
            ),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let got = read_directory(
        &host,
        &rooted_directory_path_from_normalized(package_directory),
        &[".d.ts"],
        &[] as &[&str],
        &["**/*"],
        UNLIMITED_DEPTH,
    );
    let got: Vec<String> = got.iter().map(|f| f.as_string().to_string()).collect();
    assert_eq!(got, [format!("{package_directory}/value.d.ts")]);
}

#[test]
fn test_read_directory_dynamic_root_uses_case_sensitive_patterns() {
    let root = "^/~ts-uri~/custom/ts-nul-authority";
    let inner = vfstest::from_map(
        [
            (format!("{root}/Foo/a.ts"), vfstest::TestFile::from("")),
            (format!("{root}/foo/b.ts"), vfstest::TestFile::from("")),
        ],
        CaseSensitivity::CaseSensitive,
    );
    // caseInsensitiveMatchFS: reports CaseInsensitive but the underlying FS is
    // case-sensitive.
    let host = wrapvfs::wrap(
        inner,
        wrapvfs::Replacements {
            case_sensitivity: Some(Box::new(|| CaseSensitivity::CaseInsensitive)),
            ..Default::default()
        },
    );
    let got = read_directory(
        &host,
        &rooted_directory_path_from_normalized(&format!("{root}/")),
        &[".ts"],
        &[] as &[&str],
        &["Foo/**/*.ts"],
        UNLIMITED_DEPTH,
    );
    let got: Vec<String> = got.iter().map(|f| f.as_string().to_string()).collect();
    assert_eq!(got, [format!("{root}/Foo/a.ts")]);
}

#[test]
fn test_dynamic_absolute_glob_uses_case_sensitive_pattern() {
    let root = "^/~ts-uri~/custom/ts-nul-authority";
    let matcher = new_spec_matcher(
        &[format!("{root}/Foo/**/*.ts")],
        &RootedDirectoryPath::from("/dev"),
        Usage::Files,
        CaseSensitivity::CaseInsensitive,
    );
    let matcher = matcher.expect("matcher should not be nil");
    assert!(matcher.match_string(&format!("{root}/Foo/a.ts")));
    assert!(!matcher.match_string(&format!("{root}/foo/a.ts")));
}

#[test]
fn test_spec_matcher() {
    struct Case {
        name: &'static str,
        specs: &'static [&'static str],
        usage: Usage,
        case_sensitivity: CaseSensitivity,
        matching: &'static [&'static str],
        non_matching: &'static [&'static str],
    }

    let cases = [
        Case {
            name: "simple wildcard",
            specs: &["*.ts"],
            usage: Usage::Files,
            case_sensitivity: CaseSensitivity::CaseSensitive,
            matching: &["/project/a.ts", "/project/b.ts", "/project/foo.ts"],
            non_matching: &["/project/a.js", "/project/sub/a.ts"],
        },
        Case {
            name: "recursive wildcard",
            specs: &["**/*.ts"],
            usage: Usage::Files,
            case_sensitivity: CaseSensitivity::CaseSensitive,
            matching: &[
                "/project/a.ts",
                "/project/sub/a.ts",
                "/project/sub/deep/a.ts",
            ],
            non_matching: &["/project/a.js"],
        },
        Case {
            name: "exclude pattern",
            specs: &["node_modules"],
            usage: Usage::Exclude,
            case_sensitivity: CaseSensitivity::CaseSensitive,
            matching: &["/project/node_modules/foo"],
            non_matching: &["/project/node_modules", "/project/src"],
        },
        Case {
            name: "case insensitive",
            specs: &["*.ts"],
            usage: Usage::Files,
            case_sensitivity: CaseSensitivity::CaseInsensitive,
            matching: &["/project/A.TS", "/project/B.Ts"],
            non_matching: &["/project/a.js"],
        },
        Case {
            name: "multiple specs",
            specs: &["*.ts", "*.tsx"],
            usage: Usage::Files,
            case_sensitivity: CaseSensitivity::CaseSensitive,
            matching: &["/project/a.ts", "/project/b.tsx"],
            non_matching: &["/project/a.js"],
        },
    ];

    for tc in &cases {
        let matcher = new_spec_matcher(
            tc.specs,
            &RootedDirectoryPath::from("/project"),
            tc.usage,
            tc.case_sensitivity,
        )
        .unwrap_or_else(|| panic!("{}: matcher should not be nil", tc.name));
        for path in tc.matching {
            assert!(
                matcher.match_string(path),
                "{}: should match: {}",
                tc.name,
                path
            );
        }
        for path in tc.non_matching {
            assert!(
                !matcher.match_string(path),
                "{}: should not match: {}",
                tc.name,
                path
            );
        }
    }
}

#[test]
fn test_spec_matcher_match_string() {
    let cases: &[(&str, &[&str], Usage, &[&str], &[bool])] = &[
        (
            "simple wildcard files",
            &["*.ts"],
            Usage::Files,
            &["/project/a.ts", "/project/sub/a.ts", "/project/a.js"],
            &[true, false, false],
        ),
        (
            "recursive wildcard files",
            &["**/*.ts"],
            Usage::Files,
            &["/project/a.ts", "/project/sub/a.ts", "/project/a.js"],
            &[true, true, false],
        ),
        (
            "exclude pattern matches prefix",
            &["node_modules"],
            Usage::Exclude,
            &[
                "/project/node_modules",
                "/project/node_modules/foo",
                "/project/src",
            ],
            &[false, true, false],
        ),
    ];

    for (name, specs, usage, paths, expected) in cases {
        assert_eq!(paths.len(), expected.len());
        let m = new_spec_matcher(
            specs,
            &RootedDirectoryPath::from("/project"),
            *usage,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap_or_else(|| panic!("{name}: matcher should not be nil"));
        for (path, expected) in paths.iter().zip(expected.iter()) {
            assert_eq!(m.match_string(path), *expected, "{name}: path: {path}");
        }
    }
}

#[test]
fn test_single_spec_matcher_match_string() {
    let cases: &[(&str, &str, Usage, &[&str], &[bool])] = &[
        (
            "single spec wildcard",
            "*.ts",
            Usage::Files,
            &["/project/a.ts", "/project/sub/a.ts", "/project/a.js"],
            &[true, false, false],
        ),
        (
            "single spec trailing starstar exclude allowed",
            "**",
            Usage::Exclude,
            &["/project/a.ts", "/project/sub/a.ts"],
            &[true, true],
        ),
    ];

    for (name, spec, usage, paths, expected) in cases {
        assert_eq!(paths.len(), expected.len());
        let m = new_spec_matcher(
            &[*spec],
            &RootedDirectoryPath::from("/project"),
            *usage,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap_or_else(|| panic!("{name}: matcher should not be nil"));
        for (path, expected) in paths.iter().zip(expected.iter()) {
            assert_eq!(m.match_string(path), *expected, "{name}: path: {path}");
        }
    }
}

#[test]
fn test_spec_matchers_match_index() {
    let cases: &[(&str, &[&str], Usage, &[&str], &[i64])] = &[
        (
            "index lookup prefers first match",
            &["*.ts", "*.tsx"],
            Usage::Files,
            &["/project/a.ts", "/project/a.tsx", "/project/a.js"],
            &[0, 1, -1],
        ),
        (
            "exclude index lookup",
            &["node_modules", "bower_components"],
            Usage::Exclude,
            &[
                "/project/node_modules",
                "/project/node_modules/foo",
                "/project/bower_components",
                "/project/bower_components/bar",
                "/project/src",
            ],
            &[-1, 0, -1, 1, -1],
        ),
    ];

    for (name, specs, usage, paths, expected) in cases {
        assert_eq!(paths.len(), expected.len());
        let m = new_spec_matcher(
            specs,
            &RootedDirectoryPath::from("/project"),
            *usage,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap_or_else(|| panic!("{name}: matcher should not be nil"));
        for (path, expected) in paths.iter().zip(expected.iter()) {
            assert_eq!(m.match_index(path), *expected, "{name}: path: {path}");
        }
    }
}

#[test]
fn test_single_spec_matcher() {
    struct Case {
        name: &'static str,
        spec: &'static str,
        usage: Usage,
        expect_none: bool,
        matching: &'static [&'static str],
        non_matching: &'static [&'static str],
    }

    let cases = [
        Case {
            name: "simple spec",
            spec: "*.ts",
            usage: Usage::Files,
            expect_none: false,
            matching: &["/project/a.ts"],
            non_matching: &["/project/a.js"],
        },
        Case {
            name: "trailing ** non-exclude returns nil",
            spec: "**",
            usage: Usage::Files,
            expect_none: true,
            matching: &[],
            non_matching: &[],
        },
        Case {
            name: "trailing ** exclude works",
            spec: "**",
            usage: Usage::Exclude,
            expect_none: false,
            matching: &["/project/anything", "/project/deep/path"],
            non_matching: &[],
        },
    ];

    for tc in &cases {
        let matcher = new_spec_matcher(
            &[tc.spec],
            &RootedDirectoryPath::from("/project"),
            tc.usage,
            CaseSensitivity::CaseSensitive,
        );
        if tc.expect_none {
            assert!(matcher.is_none(), "{}: should be nil", tc.name);
            continue;
        }
        let matcher = matcher.unwrap_or_else(|| panic!("{}: matcher should not be nil", tc.name));
        for path in tc.matching {
            assert!(
                matcher.match_string(path),
                "{}: should match: {}",
                tc.name,
                path
            );
        }
        for path in tc.non_matching {
            assert!(
                !matcher.match_string(path),
                "{}: should not match: {}",
                tc.name,
                path
            );
        }
    }
}

#[test]
fn test_spec_matchers() {
    // multiple specs return correct index
    let m = new_spec_matcher(
        &["*.ts", "*.tsx", "*.js"],
        &RootedDirectoryPath::from("/project"),
        Usage::Files,
        CaseSensitivity::CaseSensitive,
    )
    .expect("matchers should not be nil");
    for (path, expected) in [
        ("/project/a.ts", 0),
        ("/project/b.tsx", 1),
        ("/project/c.js", 2),
        ("/project/d.css", -1), // no match
    ] {
        assert_eq!(m.match_index(path), expected, "path: {path}");
    }

    // empty specs returns nil
    let m = new_spec_matcher(
        &[] as &[&str],
        &RootedDirectoryPath::from("/project"),
        Usage::Files,
        CaseSensitivity::CaseSensitive,
    );
    assert!(m.is_none(), "should be nil");
}

/// Tests internal glob pattern matching logic to ensure edge cases are
/// covered that may not be hit by ReadDirectory tests.
#[test]
fn test_glob_pattern_internals() {
    // nextPathPart handles consecutive slashes
    {
        let path = "/dev//foo///bar";
        let (part, offset, ok) = next_path_part_parts(path, "", 0);
        assert!(ok);
        assert_eq!(part, "");
        assert_eq!(offset, 1);

        let (part, offset, ok) = next_path_part_parts(path, "", 1);
        assert!(ok);
        assert_eq!(part, "dev");

        let (part, offset, ok) = next_path_part_parts(path, "", offset);
        assert!(ok);
        assert_eq!(part, "foo");

        let (part, _, ok) = next_path_part_parts(path, "", offset);
        assert!(ok);
        assert_eq!(part, "bar");
    }

    // nextPathPart handles path ending with slashes
    {
        let path = "/dev/";
        let (_, offset, ok) = next_path_part_parts(path, "", 0); // root
        assert!(ok);
        let (_, offset, ok) = next_path_part_parts(path, "", offset); // dev
        assert!(ok);
        // Now at trailing slash, should return not ok
        let (_, _, ok) = next_path_part_parts(path, "", offset);
        assert!(!ok);
    }

    // nextPathPartParts handles empty prefix
    {
        let (part, offset, ok) = next_path_part_parts("", "/dev//foo", 0);
        assert!(ok);
        assert_eq!(part, "");
        assert_eq!(offset, 1);

        let (part, offset, ok) = next_path_part_parts("", "/dev//foo", offset);
        assert!(ok);
        assert_eq!(part, "dev");

        let (part, _, ok) = next_path_part_parts("", "/dev//foo", offset);
        assert!(ok);
        assert_eq!(part, "foo");
    }

    // nextPathPartParts returns not ok when only slashes remain
    {
        let prefix = "/dev/";
        let suffix = "foo";

        let (_, offset, ok) = next_path_part_parts(prefix, suffix, 0); // root
        assert!(ok);

        let (part, offset, ok) = next_path_part_parts(prefix, suffix, offset); // dev
        assert!(ok);
        assert_eq!(part, "dev");

        let (part, offset, ok) = next_path_part_parts(prefix, suffix, offset); // foo
        assert!(ok);
        assert_eq!(part, "foo");
        assert_eq!(offset, prefix.len() + suffix.len());

        let (_, _, ok) = next_path_part_parts(prefix, suffix, offset);
        assert!(!ok);
    }

    // nextPathPartParts parses from suffix region
    {
        let prefix = "/";
        let suffix = "a";

        let (part, offset, ok) = next_path_part_parts(prefix, suffix, 0); // root
        assert!(ok);
        assert_eq!(part, "");
        assert_eq!(offset, 1);

        let (part, _, ok) = next_path_part_parts(prefix, suffix, offset);
        assert!(ok);
        assert_eq!(part, "a");
    }

    // question mark segment at end of string
    {
        let p = compile_glob_pattern(
            "a?",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p.matches("/ab"));
        assert!(!p.matches("/a"));
    }

    // star segment with complex pattern
    {
        let p = compile_glob_pattern(
            "a*b*c",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p.matches("/abc"));
        assert!(p.matches("/aXbYc"));
        assert!(p.matches("/aXXXbYYYc"));
        assert!(!p.matches("/aXbY"));
    }

    // literal component with package folder in include
    {
        let host = vfstest::from_map(
            [("/dev/node_modules/pkg/index.ts", "")],
            CaseSensitivity::CaseInsensitive,
        );

        let got = match_file_names(
            &RootedDirectoryPath::from("/dev"),
            &[".ts"],
            &[] as &[&str],
            &["node_modules/pkg/index.ts"],
            UNLIMITED_DEPTH,
            &host,
        );
        let got: Vec<String> = got.iter().map(|f| f.as_string().to_string()).collect();
        assert_contains(&got, "/dev/node_modules/pkg/index.ts");
    }
}

/// Tests edge cases in the matchSegments function.
#[test]
fn test_match_segments_edge_cases() {
    // question mark before slash in string
    {
        let p = compile_glob_pattern(
            "a?b",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p.matches("/aXb"));
        assert!(!p.matches("/ab"));
        assert!(!p.matches("/aXYb"));
    }

    // star with no trailing content
    {
        let p = compile_glob_pattern(
            "a*",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p.matches("/a"));
        assert!(p.matches("/abc"));
        assert!(p.matches("/aXYZ"));
    }

    // multiple stars in pattern
    {
        let p = compile_glob_pattern(
            "*a*",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p.matches("/a"));
        assert!(p.matches("/Xa"));
        assert!(p.matches("/aX"));
        assert!(p.matches("/XaY"));
        assert!(!p.matches("/XYZ")); // no 'a'
    }

    // multiple stars requiring backtracking
    {
        // Pattern: *a*a - must find two 'a' characters
        let p1 = compile_glob_pattern(
            "*a*a",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p1.matches("/aa"));
        assert!(p1.matches("/Xaa"));
        assert!(p1.matches("/aXa"));
        assert!(p1.matches("/XaYa"));
        assert!(p1.matches("/aaaa"));
        assert!(!p1.matches("/a"));
        assert!(!p1.matches("/Xa"));
        assert!(!p1.matches("/aX"));
        assert!(!p1.matches("/XaYaZ"));

        // Pattern: *a*b*c - must find a, then b, then c in order
        let p2 = compile_glob_pattern(
            "*a*b*c",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p2.matches("/abc"));
        assert!(p2.matches("/XaYbZc"));
        assert!(p2.matches("/aXbYc"));
        assert!(p2.matches("/aaabbbccc"));
        assert!(!p2.matches("/ab"));
        assert!(!p2.matches("/ac"));
        assert!(!p2.matches("/cba"));
        assert!(!p2.matches("/abcX"));

        // Pattern: *a*a*a - must find three 'a' characters
        let p3 = compile_glob_pattern(
            "*a*a*a",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p3.matches("/aaa"));
        assert!(p3.matches("/aXaYa"));
        assert!(p3.matches("/XaYaZa"));
        assert!(!p3.matches("/aa"));
        assert!(!p3.matches("/aaX"));

        // Pattern: a*b*a - starts with a, ends with a, has b in middle
        let p4 = compile_glob_pattern(
            "a*b*a",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p4.matches("/aba"));
        assert!(p4.matches("/aXbYa"));
        assert!(p4.matches("/abba"));
        assert!(!p4.matches("/ab"));
        assert!(!p4.matches("/aba "));
        assert!(!p4.matches("/Xaba"));
    }

    // pathological pattern performance
    {
        let p = compile_glob_pattern(
            "*a*a*a*a*b",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(!p.matches("/aaaaaaaaaaaaaaaa"));
        assert!(!p.matches("/aaaaaaaaaaaaaaaaX"));
        assert!(p.matches("/aaaab"));
        assert!(p.matches("/XaYaZaWab"));
    }

    // literal segment not matching
    {
        let p = compile_glob_pattern(
            "abcdefgh.ts",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(!p.matches("/abc.ts"));
        assert!(p.matches("/abcdefgh.ts"));
    }

    // question mark matches multi-byte unicode rune
    {
        let p1 = compile_glob_pattern(
            "?.ts",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p1.matches("/a.ts"));
        assert!(p1.matches("/é.ts"));
        assert!(p1.matches("/中.ts"));
        assert!(p1.matches("/🎉.ts"));
        assert!(!p1.matches("/.ts"));
        assert!(!p1.matches("/ab.ts"));

        let p2 = compile_glob_pattern(
            "??.ts",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p2.matches("/ab.ts"));
        assert!(p2.matches("/é中.ts"));
        assert!(p2.matches("/🎉é.ts"));
        assert!(!p2.matches("/a.ts"));
        assert!(!p2.matches("/abc.ts"));
    }

    // star matches multi-byte unicode runes correctly
    {
        let p = compile_glob_pattern(
            "*é.ts",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p.matches("/é.ts"));
        assert!(p.matches("/café.ts"));
        assert!(!p.matches("/cafe.ts"));

        let p2 = compile_glob_pattern(
            "*🎉*",
            &RootedDirectoryPath::from("/"),
            Usage::Files,
            CaseSensitivity::CaseSensitive,
        )
        .unwrap();
        assert!(p2.matches("/🎉"));
        assert!(p2.matches("/a🎉b"));
        assert!(!p2.matches("/abc"));
    }
}

/// Tests handling of paths with consecutive slashes.
#[test]
fn test_read_directory_consecutive_slashes() {
    let host = vfstest::from_map(
        [("/dev/a.ts", ""), ("/dev/x/b.ts", "")],
        CaseSensitivity::CaseInsensitive,
    );

    let got = match_file_names(
        &RootedDirectoryPath::from("/dev"),
        &[".ts"],
        &[] as &[&str],
        &["**/*.ts"],
        UNLIMITED_DEPTH,
        &host,
    );
    let got: Vec<String> = got.iter().map(|f| f.as_string().to_string()).collect();
    assert!(got.len() >= 2, "should find files");
    assert_contains(&got, "/dev/a.ts");
    assert_contains(&got, "/dev/x/b.ts");
}

/// Tests literal component behavior with package folders.
#[test]
fn test_glob_pattern_literal_with_package_folders() {
    // wildcard skips package folders
    {
        let host = vfstest::from_map(
            [("/dev/a.ts", ""), ("/dev/node_modules/b.ts", "")],
            CaseSensitivity::CaseInsensitive,
        );

        let got = match_file_names(
            &RootedDirectoryPath::from("/dev"),
            &[".ts"],
            &[] as &[&str],
            &["*/*.ts"],
            UNLIMITED_DEPTH,
            &host,
        );
        let got: Vec<String> = got.iter().map(|f| f.as_string().to_string()).collect();
        assert_not_contains(&got, "/dev/node_modules/b.ts");
    }

    // explicit literal includes package folder
    {
        let host = vfstest::from_map(
            [("/dev/node_modules/b.ts", "")],
            CaseSensitivity::CaseInsensitive,
        );

        let got = match_file_names(
            &RootedDirectoryPath::from("/dev"),
            &[".ts"],
            &[] as &[&str],
            &["node_modules/b.ts"],
            UNLIMITED_DEPTH,
            &host,
        );
        let got: Vec<String> = got.iter().map(|f| f.as_string().to_string()).collect();
        assert_contains(&got, "/dev/node_modules/b.ts");
    }
}

/// Verifies that getBasePaths uses the correct case-sensitivity when
/// deduplicating base paths.
#[test]
fn test_get_base_paths_case_sensitivity() {
    // case-sensitive does not dedup differently-cased paths
    {
        let base_paths = get_base_paths(
            &RootedDirectoryPath::from("/root"),
            &["../Other/**/*.ts", "../other/**/*.ts"],
            CaseSensitivity::CaseSensitive,
        );
        let base_paths: Vec<&str> = base_paths.iter().map(|p| p.as_string()).collect();
        assert!(
            base_paths.contains(&"/Other"),
            "expected /Other in base paths: {base_paths:?}"
        );
        assert!(
            base_paths.contains(&"/other"),
            "expected /other in base paths: {base_paths:?}"
        );
    }

    // case-insensitive dedups differently-cased paths
    {
        let base_paths = get_base_paths(
            &RootedDirectoryPath::from("/root"),
            &["../Other/**/*.ts", "../other/**/*.ts"],
            CaseSensitivity::CaseInsensitive,
        );
        let count = base_paths
            .iter()
            .filter(|bp| bp.as_string() == "/Other" || bp.as_string() == "/other")
            .count();
        assert!(
            count <= 1,
            "expected at most one of /Other or /other in base paths: {base_paths:?}"
        );
    }
}
