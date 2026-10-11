// Ported from tsc/internal/module/resolver_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(deferred): `TestResolverSharedData` is not ported — it uses
// `testutil.CheckDataOnly`, a Go reflection check that `ResolutionData`
// contains only shareable value data. There is no Rust `testutil` crate and
// no runtime reflection equivalent.
//
// PORT: Go's trailing `error` return on `ResolveModuleName`/
// `ResolveModuleNameFromDirectory` is dropped in this port (see the `Resolver`
// trait), so `r, _, err := resolver.ResolveModuleName(...)` becomes a
// two-value result here.

use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime};

use tsc_collections::OrderedMap;
use tsc_core::compileroptions::{
    RESOLUTION_MODE_COMMON_JS, RESOLUTION_MODE_ESM, RESOLUTION_MODE_NONE,
};
use tsc_core::options_generated::{
    CompilerOptions, ModuleKind, ModuleResolutionKind, ScriptTarget,
};
use tsc_core::tristate::TS_TRUE;
use tsc_packagejson::InfoCache;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath};
use tsc_vfs::fs::{FileInfo, FsError};
use tsc_vfs::{Entries, Vfs};

use crate::cache::ResolverOptions;
use crate::resolver::DefaultResolver;
use crate::types::{ResolutionHost, ResolvedModule};

/// `type resolutionTestInputs struct`
struct ResolutionTestInputs {
    fs: Arc<dyn Vfs>,
    cwd: RootedDirectoryPath,
}

impl ResolutionHost for ResolutionTestInputs {
    /// `func (i *resolutionTestInputs) FS() vfs.FS`
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }
    /// `func (i *resolutionTestInputs) GetCurrentDirectory() tspath.RootedDirectoryPath`
    fn get_current_directory(&self) -> RootedDirectoryPath {
        self.cwd.clone()
    }
}

fn test_host(fs: Arc<dyn Vfs>, cwd: &str) -> Arc<dyn ResolutionHost> {
    Arc::new(ResolutionTestInputs {
        fs,
        cwd: RootedDirectoryPath::from(cwd),
    })
}

fn resolver_options(
    host: Arc<dyn ResolutionHost>,
    compiler_options: CompilerOptions,
) -> ResolverOptions {
    ResolverOptions {
        host,
        compiler_options: Arc::new(compiler_options),
        typings_location: RootedDirectoryPath::default(),
        project_name: String::new(),
        extra_extensions: Vec::new(),
        package_json_cache: None,
    }
}

fn bundler_options() -> CompilerOptions {
    CompilerOptions {
        module_resolution: ModuleResolutionKind::Bundler,
        module: ModuleKind::ESNext,
        target: ScriptTarget::ESNext,
        ..CompilerOptions::default()
    }
}

fn bundler_resolver(fs: Arc<dyn Vfs>, cwd: &str) -> DefaultResolver {
    DefaultResolver::new(resolver_options(test_host(fs, cwd), bundler_options()))
}

/// `resolved.IsResolved()` — the Option is the Go nil receiver.
fn is_resolved(resolved: &Option<ResolvedModule>) -> bool {
    resolved.as_ref().map_or(false, |r| r.is_resolved())
}

/// `type caseInsensitiveViewFS struct` — wraps a VFS to report
/// case-insensitive comparison without rewriting the underlying data.
struct CaseInsensitiveViewFs {
    inner: Arc<dyn Vfs>,
}

impl Vfs for CaseInsensitiveViewFs {
    fn case_sensitivity(&self) -> CaseSensitivity {
        CaseSensitivity::CaseInsensitive
    }
    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.inner.file_exists(path)
    }
    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.inner.read_file(path)
    }
    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.write_file(path, data)
    }
    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.append_file(path, data)
    }
    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.inner.remove(path)
    }
    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.inner.chtimes(path, a_time, m_time)
    }
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.inner.directory_exists(path)
    }
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.inner.get_accessible_entries(path)
    }
    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.inner.stat(path)
    }
    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.inner.realpath(path)
    }
}

/// Finds the first existing package.json info-cache entry, as the Go tests do
/// via `PackageJsonCacheEntries`.
fn first_existing_package_json_entry(
    resolver: &DefaultResolver,
) -> Option<Arc<tsc_packagejson::InfoCacheEntry>> {
    let mut package_json = None;
    resolver.package_json_cache_entries(|_, entry| {
        if entry.exists() {
            package_json = Some(entry);
            return false;
        }
        true
    });
    package_json
}

// Regression test for https://github.com/microsoft/TypeScript/tsc/issues/3526.
//
// Resolving a node_modules import with a trailing slash (e.g. `pkg/`) must
// produce the same result as without one.
/// `func TestResolveModuleNameTrailingSlash(t *testing.T)`
#[test]
fn test_resolve_module_name_trailing_slash() {
    let fs = tsc_vfs::vfstest::from_map(
        [
            (
                "/repo/node_modules/pkg/package.json",
                "{\"name\":\"pkg\",\"main\":\"main.js\",\"types\":\"main.d.ts\"}",
            ),
            (
                "/repo/node_modules/pkg/main.d.ts",
                "export const x: number;",
            ),
            ("/repo/node_modules/pkg/main.js", "exports.x = 1;"),
            ("/repo/src/file.ts", ""),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "/repo"),
        CompilerOptions {
            trace_resolution: TS_TRUE,
            ..bundler_options()
        },
    ));

    for name in ["pkg", "pkg/"] {
        let (r, _) = resolver.resolve_module_name(
            name,
            &RootedFilePath::from("/repo/src/file.ts"),
            RESOLUTION_MODE_ESM,
            None,
        );
        let r = r.expect("resolve_module_name returns Some");
        assert!(r.is_resolved(), "{name:?} failed to resolve");
        assert_eq!(
            r.resolved_path,
            CaseSensitivity::CaseSensitive.path_key(&r.resolved_file_name.as_path()),
            "{name} resolved path",
        );
    }
}

/// `func TestResolutionDataCaches(t *testing.T)`
#[test]
fn test_resolution_data_caches() {
    let old_host = test_host(
        tsc_vfs::vfstest::from_map(
            [
                (
                    "/src/node_modules/pkg/package.json",
                    "{\"name\":\"pkg\",\"types\":\"index.d.ts\"}",
                ),
                (
                    "/src/node_modules/pkg/index.d.ts",
                    "export const value: number;",
                ),
            ],
            CaseSensitivity::CaseSensitive,
        ),
        "/",
    );
    let new_host = test_host(
        tsc_vfs::vfstest::from_map(
            [
                (
                    "/src/node_modules/pkg/package.json",
                    "{\"name\":\"pkg\",\"types\":\"index.d.ts\"}",
                ),
                (
                    "/src/node_modules/pkg/index.d.ts",
                    "export const value: number;",
                ),
                ("/new/package.json", "{\"name\":\"new\"}"),
                (
                    "/missing-first/package.json",
                    "{\"name\":\"missing-first\"}",
                ),
            ],
            CaseSensitivity::CaseSensitive,
        ),
        "/",
    );
    let resolver = DefaultResolver::new(resolver_options(
        old_host.clone(),
        CompilerOptions {
            module: ModuleKind::NodeNext,
            ..CompilerOptions::default()
        },
    ));
    let (resolved, _) = resolver.resolve_module_name(
        "pkg",
        &RootedFilePath::from("/src/index.ts"),
        RESOLUTION_MODE_COMMON_JS,
        None,
    );
    assert!(is_resolved(&resolved));
    let (cached, _) = resolver.resolve_module_name(
        "pkg",
        &RootedFilePath::from("/src/index.ts"),
        RESOLUTION_MODE_COMMON_JS,
        None,
    );
    assert_eq!(
        cached.as_ref().unwrap().resolved_file_name,
        resolved.as_ref().unwrap().resolved_file_name
    );

    resolver.resolve_type_reference_directive(
        "missing",
        &RootedFilePath::from("/src/index.ts"),
        RESOLUTION_MODE_COMMON_JS,
        None,
    );
    let mut paths: OrderedMap<String, Option<Vec<String>>> = OrderedMap::new();
    paths.set("alias/*".to_string(), Some(vec!["./*".to_string()]));
    resolver.get_parsed_patterns_for_paths(&CompilerOptions {
        paths: Some(paths),
        ..CompilerOptions::default()
    });
    assert_eq!(resolver.module_resolution_cache.cache.size(), 1);
    assert_eq!(resolver.type_ref_directive_resolution_cache.cache.size(), 1);
    assert_eq!(resolver.parsed_patterns_for_paths.cache.size(), 1);

    let data = resolver.get_resolution_data();
    let rebound = data.new_resolver(old_host);
    assert_eq!(rebound.module_resolution_cache.cache.size(), 0);
    assert_eq!(rebound.type_ref_directive_resolution_cache.cache.size(), 0);
    assert_eq!(rebound.parsed_patterns_for_paths.cache.size(), 0);

    let clone = data.clone().new_resolver(new_host);
    assert_eq!(clone.module_resolution_cache.cache.size(), 0);
    assert_eq!(clone.type_ref_directive_resolution_cache.cache.size(), 0);
    assert_eq!(clone.parsed_patterns_for_paths.cache.size(), 0);
    // assert.Equal on *InfoCacheEntry compares pointers — Arc::ptr_eq.
    assert!(Arc::ptr_eq(
        &clone
            .get_package_scope_for_path(&RootedDirectoryPath::from("/src/node_modules/pkg"))
            .unwrap(),
        &resolver
            .get_package_scope_for_path(&RootedDirectoryPath::from("/src/node_modules/pkg"))
            .unwrap(),
    ));
    assert!(
        clone
            .get_package_scope_for_path(&RootedDirectoryPath::from("/new"))
            .unwrap()
            .exists()
    );
    // `!entry.Exists()` — a `None` (nil) entry does not exist.
    assert!(
        !resolver
            .get_package_scope_for_path(&RootedDirectoryPath::from("/new"))
            .map_or(false, |e| e.exists())
    );
    assert!(
        !resolver
            .get_package_scope_for_path(&RootedDirectoryPath::from("/missing-first"))
            .map_or(false, |e| e.exists())
    );
    assert!(
        clone
            .get_package_scope_for_path(&RootedDirectoryPath::from("/missing-first"))
            .unwrap()
            .exists()
    );
}

/// `func TestResolveDynamicModuleNameUsingRootDirs(t *testing.T)`
#[test]
fn test_resolve_dynamic_module_name_using_root_dirs() {
    struct Case {
        name: &'static str,
        target_root: &'static str,
        target_file: &'static str,
    }
    let tests = [
        Case {
            name: "dynamic roots",
            target_root: "^/~ts-uri~/custom/ts-nul-authority/generated",
            target_file: "^/~ts-uri~/custom/ts-nul-authority/generated/~ts-uri-escape~7e74732d7572692d6573636170657e66696c65~.ts",
        },
        Case {
            name: "dynamic to disk",
            target_root: "c:/generated",
            target_file: "c:/generated/~ts-uri-escape~file.ts",
        },
    ];
    for test in tests {
        let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
        let fs = tsc_vfs::vfstest::from_map(
            [
                (source_file, ""),
                (test.target_file, "export const value = 1;"),
            ],
            CaseSensitivity::CaseSensitive,
        );
        let opts = CompilerOptions {
            root_dirs: Some(vec![
                RootedDirectoryPath::from("^/~ts-uri~/custom/ts-nul-authority/src"),
                RootedDirectoryPath::from(test.target_root),
            ]),
            ..bundler_options()
        };
        let resolver = DefaultResolver::new(resolver_options(
            test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
            opts,
        ));
        let (resolved, _) = resolver.resolve_module_name(
            "./~ts-uri-escape~file",
            &tsc_tspath::rooted_file_path_from_normalized(source_file),
            RESOLUTION_MODE_ESM,
            None,
        );
        assert!(
            is_resolved(&resolved),
            "{}: expected dynamic module to resolve through rootDirs",
            test.name
        );
        assert_eq!(
            resolved.unwrap().resolved_file_name.as_string(),
            test.target_file,
            "{}: resolved file",
            test.name
        );
    }
}

/// `func TestRootDirsPreservesExceptionalDynamicSegments(t *testing.T)`
#[test]
fn test_root_dirs_preserves_exceptional_dynamic_segments() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/~ts-uri-escape~2e2e~/main.ts";
    let target_file = "^/~ts-uri~/custom/ts-nul-authority/generated/~ts-uri-escape~2e2e~/dep.ts";
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file, ""),
            (target_file, "export const value = 1;"),
            (
                "^/~ts-uri~/custom/ts-nul-authority/dep.ts",
                "export const wrong = 1;",
            ),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let opts = CompilerOptions {
        root_dirs: Some(vec![
            RootedDirectoryPath::from("^/~ts-uri~/custom/ts-nul-authority/src"),
            RootedDirectoryPath::from("^/~ts-uri~/custom/ts-nul-authority/generated"),
        ]),
        ..bundler_options()
    };
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        opts,
    ));
    let (resolved, _) = resolver.resolve_module_name(
        "./dep",
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved)
            && resolved.as_ref().unwrap().resolved_file_name.as_string() == target_file,
        "resolved file = {:?}, expected {target_file:?}",
        resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
    );
}

/// `func TestRootDirsRejectsUnrepresentableDiskSegments(t *testing.T)`
#[test]
fn test_root_dirs_rejects_unrepresentable_disk_segments() {
    for source_file in [
        "^/~ts-uri~/custom/ts-nul-authority/src/~ts-uri-escape~2e2e~/main.ts",
        "^/~ts-uri~/custom/ts-nul-authority/src/c:/main.ts",
        "^/~ts-uri~/custom/ts-nul-authority/src/^/main.ts",
    ] {
        let fs = tsc_vfs::vfstest::from_map(
            [(source_file, ""), ("c:/dep.ts", "export const wrong = 1;")],
            CaseSensitivity::CaseSensitive,
        );
        let opts = CompilerOptions {
            root_dirs: Some(vec![
                RootedDirectoryPath::from("^/~ts-uri~/custom/ts-nul-authority/src"),
                RootedDirectoryPath::from("c:/generated"),
            ]),
            ..bundler_options()
        };
        let resolver = DefaultResolver::new(resolver_options(
            test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
            opts,
        ));
        let (resolved, _) = resolver.resolve_module_name(
            "./dep",
            &tsc_tspath::rooted_file_path_from_normalized(source_file),
            RESOLUTION_MODE_ESM,
            None,
        );
        assert!(
            !is_resolved(&resolved),
            "{source_file}: unexpectedly resolved unrepresentable disk path to {:?}",
            resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
        );
    }
}

/// `func TestRootDirsEscapesRootLikeDynamicSegments(t *testing.T)`
#[test]
fn test_root_dirs_escapes_root_like_dynamic_segments() {
    for (source_file, target_file) in [
        (
            "^/~ts-uri~/custom/ts-nul-authority/src/c:/main.ts",
            "^/~ts-uri~/custom/ts-nul-authority/generated/~ts-uri-escape~633a~/dep.ts",
        ),
        (
            "^/~ts-uri~/custom/ts-nul-authority/src/^/main.ts",
            "^/~ts-uri~/custom/ts-nul-authority/generated/~ts-uri-escape~5e~/dep.ts",
        ),
    ] {
        let fs = tsc_vfs::vfstest::from_map(
            [
                (source_file, ""),
                (target_file, "export const value = 1;"),
                ("c:/dep.ts", "export const wrong = 1;"),
                ("^/dep.ts", "export const wrong = 1;"),
            ],
            CaseSensitivity::CaseSensitive,
        );
        let opts = CompilerOptions {
            root_dirs: Some(vec![
                RootedDirectoryPath::from("^/~ts-uri~/custom/ts-nul-authority/src"),
                RootedDirectoryPath::from("^/~ts-uri~/custom/ts-nul-authority/generated"),
            ]),
            ..bundler_options()
        };
        let resolver = DefaultResolver::new(resolver_options(
            test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
            opts,
        ));
        let (resolved, _) = resolver.resolve_module_name(
            "./dep",
            &tsc_tspath::rooted_file_path_from_normalized(source_file),
            RESOLUTION_MODE_ESM,
            None,
        );
        assert!(
            is_resolved(&resolved)
                && resolved.as_ref().unwrap().resolved_file_name.as_string() == target_file,
            "{source_file}: resolved file = {:?}, expected {target_file:?}",
            resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
        );
    }
}

/// `func TestRootDirsPreservesRelativeDiskSuffixes(t *testing.T)`
#[test]
fn test_root_dirs_preserves_relative_disk_suffixes() {
    for (source_file, target_root, target_file) in [
        (
            "c:/src/^/main.ts",
            "^/~ts-uri~/custom/ts-nul-authority/generated",
            "^/~ts-uri~/custom/ts-nul-authority/generated/~ts-uri-escape~5e~/dep.ts",
        ),
        (
            "c:/src/c:/main.ts",
            "d:/generated",
            "d:/generated/c:/dep.ts",
        ),
    ] {
        let fs = tsc_vfs::vfstest::from_map(
            [
                (source_file, ""),
                (target_file, "export const value = 1;"),
                ("^/dep.ts", "export const wrong = 1;"),
                ("c:/dep.ts", "export const wrong = 1;"),
            ],
            CaseSensitivity::CaseSensitive,
        );
        let opts = CompilerOptions {
            root_dirs: Some(vec![
                RootedDirectoryPath::from("c:/src"),
                RootedDirectoryPath::from(target_root),
            ]),
            ..bundler_options()
        };
        let resolver = DefaultResolver::new(resolver_options(test_host(fs, "c:/"), opts));
        let (resolved, _) = resolver.resolve_module_name(
            "./dep",
            &tsc_tspath::rooted_file_path_from_normalized(source_file),
            RESOLUTION_MODE_ESM,
            None,
        );
        assert!(
            is_resolved(&resolved)
                && resolved.as_ref().unwrap().resolved_file_name.as_string() == target_file,
            "{source_file}: resolved file = {:?}, expected {target_file:?}",
            resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
        );
    }
}

/// `func TestRootDirsPreservesRelativeDirectoryIntent(t *testing.T)`
#[test]
fn test_root_dirs_preserves_relative_directory_intent() {
    struct Case {
        name: &'static str,
        source_root: &'static str,
        source_file: &'static str,
        target_root: &'static str,
        target_file: &'static str,
    }
    let tests = [
        Case {
            name: "disk to disk",
            source_root: "c:/src",
            source_file: "c:/src/^/main.ts",
            target_root: "d:/generated",
            target_file: "d:/generated/^/pkg/index.ts",
        },
        Case {
            name: "disk to dynamic",
            source_root: "c:/src",
            source_file: "c:/src/^/main.ts",
            target_root: "^/~ts-uri~/custom/ts-nul-authority/generated",
            target_file: "^/~ts-uri~/custom/ts-nul-authority/generated/~ts-uri-escape~5e~/pkg/index.ts",
        },
        Case {
            name: "empty suffix to dynamic",
            source_root: "c:/src",
            source_file: "c:/src/main.ts",
            target_root: "^/~ts-uri~/custom/ts-nul-authority/generated",
            target_file: "^/~ts-uri~/custom/ts-nul-authority/generated/index.ts",
        },
        Case {
            name: "empty suffix to disk",
            source_root: "^/~ts-uri~/custom/ts-nul-authority/src",
            source_file: "^/~ts-uri~/custom/ts-nul-authority/src/main.ts",
            target_root: "d:/generated",
            target_file: "d:/generated/index.ts",
        },
        Case {
            name: "literal empty segment to dynamic",
            source_root: "^/~ts-uri~/custom/ts-nul-authority/src",
            source_file: "^/~ts-uri~/custom/ts-nul-authority/src/~ts-uri-escape~~/main.ts",
            target_root: "^/~ts-uri~/custom/ts-nul-authority/generated",
            target_file: "^/~ts-uri~/custom/ts-nul-authority/generated/~ts-uri-escape~~/index.ts",
        },
    ];
    for test in tests {
        let fs = tsc_vfs::vfstest::from_map(
            [
                (test.source_file, ""),
                (test.target_file, "export const value = 1;"),
                ("^/pkg/index.ts", "export const wrong = 1;"),
                ("d:/generated.ts", "export const wrong = 1;"),
            ],
            CaseSensitivity::CaseSensitive,
        );
        let opts = CompilerOptions {
            module: ModuleKind::CommonJS,
            root_dirs: Some(vec![
                RootedDirectoryPath::from(test.source_root),
                RootedDirectoryPath::from(test.target_root),
            ]),
            ..bundler_options()
        };

        let module_name = if test.name.contains("empty suffix")
            || test.name == "literal empty segment to dynamic"
        {
            "./"
        } else {
            "./pkg/"
        };
        let resolver = DefaultResolver::new(resolver_options(test_host(fs, "c:/"), opts));
        let (resolved, _) = resolver.resolve_module_name(
            module_name,
            &tsc_tspath::rooted_file_path_from_normalized(test.source_file),
            RESOLUTION_MODE_COMMON_JS,
            None,
        );
        assert!(
            is_resolved(&resolved)
                && resolved.as_ref().unwrap().resolved_file_name.as_string() == test.target_file,
            "{}: resolved file = {:?}, expected {:?}",
            test.name,
            resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
            test.target_file,
        );
    }
}

/// `func TestResolveDynamicPackageJSONPath(t *testing.T)`
#[test]
fn test_resolve_dynamic_package_json_path() {
    let fallback_file = "^/~ts-uri~/custom/ts-nul-authority/node_modules/pkg/~ts-uri-escape~7e74732d7572692d6573636170657e7479706573~.d.ts";
    let target_file = "^/~ts-uri~/custom/ts-nul-authority/node_modules/pkg/ts3.1/~ts-uri-escape~7e74732d7572692d6573636170657e7479706573~.d.ts";
    let fs = tsc_vfs::vfstest::from_map(
        [
            ("^/~ts-uri~/custom/ts-nul-authority/src/main.ts", ""),
            (
                "^/~ts-uri~/custom/ts-nul-authority/node_modules/pkg/package.json",
                "{\"name\":\"pkg\",\"types\":\"~ts-uri-escape~types.d.ts\",\"typesVersions\":{\"*\":{\"*\":[\"ts3.1/*\"]}}}",
            ),
            (fallback_file, "export const fallback: number;"),
            (target_file, "export const value: number;"),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));
    let (resolved, _) = resolver.resolve_module_name(
        "pkg",
        &RootedFilePath::from("^/~ts-uri~/custom/ts-nul-authority/src/main.ts"),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved),
        "expected dynamic package path to resolve"
    );
    let resolved = resolved.unwrap();
    assert_eq!(resolved.resolved_file_name.as_string(), target_file);
    assert!(
        resolved.extension == tsc_tspath::EXTENSION_DTS
            && resolved.resolved_file_name.is_declaration_file(),
        "resolved declaration was classified as extension {}",
        resolved.extension
    );
}

/// `func TestResolveDynamicPackageSubpathFile(t *testing.T)`
#[test]
fn test_resolve_dynamic_package_subpath_file() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let target_file = "^/~ts-uri~/custom/ts-nul-authority/node_modules/pkg/~ts-uri-escape~7e74732d7572692d6573636170657e3636366636667e~.ts";
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file, ""),
            (
                "^/~ts-uri~/custom/ts-nul-authority/node_modules/pkg/package.json",
                "{\"name\":\"pkg\"}",
            ),
            (target_file, "export const value = 1;"),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));
    let (resolved, _) = resolver.resolve_module_name(
        "pkg/~ts-uri-escape~666f6f~.ts",
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved)
            && resolved.as_ref().unwrap().resolved_file_name.as_string() == target_file,
        "resolved file = {:?}, expected {target_file:?}",
        resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
    );
}

/// `func TestResolveDynamicESMPackageIndexFromReservedDirectory(t *testing.T)`
#[test]
fn test_resolve_dynamic_esm_package_index_from_reserved_directory() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let package_name = "~ts-uri-escape~pkg.js";
    let package_directory = "^/~ts-uri~/custom/ts-nul-authority/node_modules/~ts-uri-escape~7e74732d7572692d6573636170657e706b672e6a73~";
    let target_file = format!("{package_directory}/index.js");
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file.to_string(), "".to_string()),
            (
                format!("{package_directory}/package.json"),
                format!("{{\"name\":\"{package_name}\"}}"),
            ),
            (target_file.clone(), "exports.value = 1;".to_string()),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));
    let (resolved, _) = resolver.resolve_module_name(
        package_name,
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved)
            && resolved.as_ref().unwrap().resolved_file_name.as_string() == target_file,
        "resolved file = {:?}, expected {target_file:?}",
        resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
    );
}

/// `func TestResolveDynamicDottedDirectory(t *testing.T)`
#[test]
fn test_resolve_dynamic_dotted_directory() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let target_file = "^/~ts-uri~/custom/ts-nul-authority/src/~ts-uri-escape~7e74732d7572692d6573636170657e6469722e6a73~/index.ts";
    let fs = tsc_vfs::vfstest::from_map(
        [(source_file, ""), (target_file, "export const value = 1;")],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        CompilerOptions {
            module: ModuleKind::CommonJS,
            ..bundler_options()
        },
    ));
    let (resolved, _) = resolver.resolve_module_name(
        "./~ts-uri-escape~dir.js",
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_COMMON_JS,
        None,
    );
    assert!(
        is_resolved(&resolved),
        "expected dotted dynamic directory to resolve"
    );
    assert_eq!(
        resolved.unwrap().resolved_file_name.as_string(),
        target_file
    );
}

/// `func TestResolvedModuleCarriesCaseInsensitivePath(t *testing.T)`
#[test]
fn test_resolved_module_carries_case_insensitive_path() {
    let fs = tsc_vfs::vfstest::from_map(
        [
            (
                "/Repo/node_modules/Pkg/package.json",
                "{\"name\":\"pkg\",\"types\":\"Index.d.ts\"}",
            ),
            (
                "/Repo/node_modules/Pkg/Index.d.ts",
                "export const x: number;",
            ),
            ("/Repo/src/file.ts", ""),
        ],
        CaseSensitivity::CaseInsensitive,
    );
    let resolver = bundler_resolver(fs, "/Repo");

    let (resolved, _) = resolver.resolve_module_name(
        "Pkg",
        &RootedFilePath::from("/Repo/src/file.ts"),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(is_resolved(&resolved), "expected module to resolve");
    let resolved = resolved.unwrap();
    let assert_path =
        CaseSensitivity::CaseInsensitive.path_key(&resolved.resolved_file_name.as_path());
    assert_eq!(resolved.resolved_path, assert_path);
}

/// `func TestResolvedTypeReferenceDirectiveCarriesPath(t *testing.T)`
#[test]
fn test_resolved_type_reference_directive_carries_path() {
    let fs = tsc_vfs::vfstest::from_map(
        [
            (
                "/repo/node_modules/@types/pkg/package.json",
                "{\"name\":\"@types/pkg\",\"types\":\"index.d.ts\"}",
            ),
            (
                "/repo/node_modules/@types/pkg/index.d.ts",
                "export const x: number;",
            ),
            ("/repo/src/file.ts", ""),
        ],
        CaseSensitivity::CaseInsensitive,
    );
    let resolver = bundler_resolver(fs, "/repo");

    let (resolved, _) = resolver.resolve_type_reference_directive(
        "pkg",
        &RootedFilePath::from("/repo/src/file.ts"),
        RESOLUTION_MODE_NONE,
        None,
    );
    assert!(
        resolved.is_resolved(),
        "expected type reference directive to resolve"
    );
    let expected =
        CaseSensitivity::CaseInsensitive.path_key(&resolved.resolved_file_name.as_path());
    assert_eq!(resolved.resolved_path, expected);
}

/// `func TestResolvedEntrypointCarriesPath(t *testing.T)`
#[test]
fn test_resolved_entrypoint_carries_path() {
    let fs = tsc_vfs::vfstest::from_map(
        [
            (
                "/Repo/node_modules/Pkg/package.json",
                "{\"name\":\"pkg\",\"types\":\"Index.d.ts\"}",
            ),
            (
                "/Repo/node_modules/Pkg/Index.d.ts",
                "export const x: number;",
            ),
            ("/Repo/src/file.ts", ""),
        ],
        CaseSensitivity::CaseInsensitive,
    );
    let resolver = bundler_resolver(fs, "/Repo");

    let (resolved, _) = resolver.resolve_module_name(
        "Pkg",
        &RootedFilePath::from("/Repo/src/file.ts"),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(is_resolved(&resolved), "expected module to resolve");
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints = resolver.get_entrypoints_from_package_json_info(&package_json, "Pkg", false);
    assert_eq!(entrypoints.len(), 1, "entrypoint count");
    let entrypoint = &entrypoints[0];
    let expected =
        CaseSensitivity::CaseInsensitive.path_key(&entrypoint.resolved_file_name.as_path());
    assert_eq!(entrypoint.resolved_path, expected);
}

/// `func TestDynamicExportPatternEntrypointUsesLogicalName(t *testing.T)`
#[test]
fn test_dynamic_export_pattern_entrypoint_uses_logical_name() {
    struct Case {
        name: &'static str,
        package_json: &'static str,
        import_name: &'static str,
        module_specifier: &'static str,
    }
    let tests = [
        Case {
            name: "logical wildcard match",
            package_json: "{\"name\":\"Pkg\",\"exports\":{\"./*\":\"./*.d.ts\"}}",
            import_name: "Pkg/~ts-uri-escape~value",
            module_specifier: "Pkg/~ts-uri-spec~7e74732d7572692d6573636170657e76616c7565~",
        },
        Case {
            name: "reserved target pattern",
            package_json: "{\"name\":\"Pkg\",\"exports\":{\"./*\":\"./~ts-uri-escape~*.d.ts\"}}",
            import_name: "Pkg/value",
            module_specifier: "Pkg/value",
        },
        Case {
            name: "reserved wildcard with trailer",
            package_json: "{\"name\":\"Pkg\",\"exports\":{\"./*\":\"./*-impl.d.ts\"}}",
            import_name: "Pkg/~ts-uri-escape~value",
            module_specifier: "Pkg/~ts-uri-spec~7e74732d7572692d6573636170657e76616c7565~",
        },
    ];
    for test in tests {
        let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
        let mut target_file = "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg/~ts-uri-escape~7e74732d7572692d6573636170657e76616c7565~.d.ts";
        if test.name == "reserved wildcard with trailer" {
            target_file = "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg/~ts-uri-escape~7e74732d7572692d6573636170657e76616c75652d696d706c~.d.ts";
        }
        let fs = tsc_vfs::vfstest::from_map(
            [
                (source_file, ""),
                (
                    "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg/package.json",
                    test.package_json,
                ),
                (target_file, "export const value: number;"),
            ],
            CaseSensitivity::CaseSensitive,
        );
        let resolver = DefaultResolver::new(resolver_options(
            test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
            bundler_options(),
        ));

        let (resolved, _) = resolver.resolve_module_name(
            test.import_name,
            &tsc_tspath::rooted_file_path_from_normalized(source_file),
            RESOLUTION_MODE_ESM,
            None,
        );
        assert!(
            is_resolved(&resolved),
            "{}: expected dynamic package export to resolve",
            test.name
        );
        let package_json = first_existing_package_json_entry(&resolver)
            .expect("expected package JSON cache entry");

        let entrypoints =
            resolver.get_entrypoints_from_package_json_info(&package_json, "Pkg", false);
        assert_eq!(entrypoints.len(), 1, "{}: entrypoint count", test.name);
        assert_eq!(
            entrypoints[0].module_specifier.as_string(),
            test.module_specifier,
            "{}: module specifier",
            test.name
        );
    }
}

/// `func TestGeneratedDynamicEntrypointSpecifierResolvesEncodedFile(t *testing.T)`
#[test]
fn test_generated_dynamic_entrypoint_specifier_resolves_encoded_file() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let package_file = "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg/~ts-uri-escape~7e74732d7572692d6573636170657e76616c7565~.d.ts";
    let module_specifier = "Pkg/~ts-uri-spec~7e74732d7572692d6573636170657e76616c7565~.d.ts";
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file, ""),
            (
                "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg/package.json",
                "{\"name\":\"Pkg\"}",
            ),
            (package_file, "export const value: number;"),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));

    let _ = resolver.resolve_module_name(
        "Pkg",
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints = resolver.get_entrypoints_from_package_json_info(&package_json, "Pkg", true);
    assert!(
        entrypoints.len() == 1 && entrypoints[0].module_specifier.as_string() == module_specifier,
        "entrypoints len = {}, expected specifier {module_specifier:?}",
        entrypoints.len()
    );

    let (resolved, _) = resolver.resolve_module_name(
        module_specifier,
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved)
            && resolved.as_ref().unwrap().resolved_file_name.as_string() == package_file,
        "resolved file = {:?}, expected {package_file:?}",
        resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
    );
}

/// `func TestDynamicEntrypointsEncodePhysicalPackageNameAndRootLikePath(t *testing.T)`
#[test]
fn test_dynamic_entrypoints_encode_physical_package_name_and_root_like_path() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let physical_package_name = "~ts-uri-escape~7e74732d7572692d6573636170657e706b672e6a73~";
    let source_package_name = "~ts-uri-spec~7e74732d7572692d6573636170657e706b672e6a73~";
    let package_directory =
        format!("^/~ts-uri~/custom/ts-nul-authority/node_modules/{physical_package_name}");
    let target_file = format!("{package_directory}/~ts-uri-escape~633a~/value.d.ts");
    let module_specifier = format!("{source_package_name}/~ts-uri-spec~633a~/value.d.ts");
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file.to_string(), "".to_string()),
            (
                format!("{package_directory}/package.json"),
                "{\"name\":\"~ts-uri-escape~pkg.js\"}".to_string(),
            ),
            (
                target_file.clone(),
                "export const value: number;".to_string(),
            ),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));

    let _ = resolver.resolve_module_name(
        source_package_name,
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints =
        resolver.get_entrypoints_from_package_json_info(&package_json, physical_package_name, true);
    assert!(
        entrypoints.len() == 1 && entrypoints[0].module_specifier.as_string() == module_specifier,
        "entrypoints len = {}, expected specifier {module_specifier:?}",
        entrypoints.len()
    );
    let (resolved, _) = resolver.resolve_module_name(
        &module_specifier,
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved)
            && resolved.as_ref().unwrap().resolved_file_name.as_string() == target_file,
        "generated module specifier resolved to {:?}, expected {target_file:?}",
        resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
    );
}

/// `func TestDynamicExportPatternPreservesStaticSourcePrefix(t *testing.T)`
#[test]
fn test_dynamic_export_pattern_preserves_static_source_prefix() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let package_directory = "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg";
    let target_file = format!("{package_directory}/foo.d.ts");
    let module_specifier = "Pkg/~ts-uri-escape~prefix/foo";
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file.to_string(), "".to_string()),
            (
                format!("{package_directory}/package.json"),
                "{\"name\":\"Pkg\",\"exports\":{\"./~ts-uri-escape~prefix/*\":\"./*.d.ts\"}}"
                    .to_string(),
            ),
            (
                target_file.clone(),
                "export const value: number;".to_string(),
            ),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));

    let (resolved, _) = resolver.resolve_module_name(
        module_specifier,
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved),
        "expected static reserved-prefix export to resolve"
    );
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints = resolver.get_entrypoints_from_package_json_info(&package_json, "Pkg", false);
    assert!(
        entrypoints.len() == 1 && entrypoints[0].module_specifier.as_string() == module_specifier,
        "entrypoints len = {}, expected specifier {module_specifier:?}",
        entrypoints.len()
    );
}

/// `func TestDynamicExportPatternKeepsPackageForRootLikeMatch(t *testing.T)`
#[test]
fn test_dynamic_export_pattern_keeps_package_for_root_like_match() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let package_directory = "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg";
    let target_file = format!("{package_directory}/~ts-uri-escape~633a~/value.d.ts");
    let module_specifier = "Pkg/~ts-uri-spec~633a~/value";
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file.to_string(), "".to_string()),
            (
                format!("{package_directory}/package.json"),
                "{\"name\":\"Pkg\",\"exports\":{\"./*\":\"./*.d.ts\"}}".to_string(),
            ),
            (
                target_file.clone(),
                "export const value: number;".to_string(),
            ),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));

    let (resolved, _) = resolver.resolve_module_name(
        module_specifier,
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved),
        "expected root-like dynamic export to resolve"
    );
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints = resolver.get_entrypoints_from_package_json_info(&package_json, "Pkg", false);
    assert!(
        entrypoints.len() == 1 && entrypoints[0].module_specifier.as_string() == module_specifier,
        "entrypoints len = {}, expected specifier {module_specifier:?}",
        entrypoints.len()
    );
}

/// `func TestDynamicEntrypointsPreserveCaseDistinctFiles(t *testing.T)`
#[test]
fn test_dynamic_entrypoints_preserve_case_distinct_files() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let package_directory = "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg";
    let fs: Arc<dyn Vfs> = Arc::new(CaseInsensitiveViewFs {
        inner: tsc_vfs::vfstest::from_map(
            [
                (source_file.to_string(), "".to_string()),
                (
                    format!("{package_directory}/package.json"),
                    "{\"name\":\"Pkg\",\"types\":\"Foo.d.ts\"}".to_string(),
                ),
                (
                    format!("{package_directory}/Foo.d.ts"),
                    "export const upper: number;".to_string(),
                ),
                (
                    format!("{package_directory}/foo.d.ts"),
                    "export const lower: number;".to_string(),
                ),
            ],
            CaseSensitivity::CaseSensitive,
        ),
    });
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));

    let _ = resolver.resolve_module_name(
        "Pkg",
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints = resolver.get_entrypoints_from_package_json_info(&package_json, "Pkg", true);
    assert_eq!(entrypoints.len(), 2, "entrypoint count");
}

/// `func TestDiskExportPatternKeepsReservedPrefixLiteral(t *testing.T)`
#[test]
fn test_disk_export_pattern_keeps_reserved_prefix_literal() {
    let target_file = "/repo/node_modules/pkg/~ts-uri-escape~666f6f~.d.ts";
    let fs = tsc_vfs::vfstest::from_map(
        [
            ("/repo/src/main.ts", ""),
            (
                "/repo/node_modules/pkg/package.json",
                "{\"name\":\"pkg\",\"exports\":{\"./*\":\"./*.d.ts\"}}",
            ),
            (target_file, "export const value: number;"),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = bundler_resolver(fs, "/repo");

    let (resolved, _) = resolver.resolve_module_name(
        "pkg/~ts-uri-escape~666f6f~",
        &RootedFilePath::from("/repo/src/main.ts"),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved),
        "expected disk package export to resolve"
    );
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints = resolver.get_entrypoints_from_package_json_info(&package_json, "pkg", false);
    assert!(
        entrypoints.len() == 1
            && entrypoints[0].module_specifier.as_string() == "pkg/~ts-uri-escape~666f6f~",
        "entrypoints len = {}, expected literal reserved-prefix entrypoint",
        entrypoints.len()
    );
}

/// `func TestDynamicExportPatternUnderExceptionalParent(t *testing.T)`
#[test]
fn test_dynamic_export_pattern_under_exceptional_parent() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/work/~ts-uri-escape~2e2e~/src/main.ts";
    let package_directory =
        "^/~ts-uri~/custom/ts-nul-authority/work/~ts-uri-escape~2e2e~/node_modules/Pkg";
    let target_file = format!("{package_directory}/foo.d.ts");
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file.to_string(), "".to_string()),
            (
                format!("{package_directory}/package.json"),
                "{\"name\":\"Pkg\",\"exports\":{\"./*\":\"./*.d.ts\"}}".to_string(),
            ),
            (
                target_file.clone(),
                "export const value: number;".to_string(),
            ),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));

    let (resolved, _) = resolver.resolve_module_name(
        "Pkg/foo",
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved),
        "expected dynamic package export to resolve"
    );
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints = resolver.get_entrypoints_from_package_json_info(&package_json, "Pkg", false);
    assert!(
        entrypoints.len() == 1 && entrypoints[0].module_specifier.as_string() == "Pkg/foo",
        "entrypoints len = {}, expected logical Pkg/foo entrypoint",
        entrypoints.len()
    );
}

/// `func TestDynamicExportPatternWithEmptyMatch(t *testing.T)`
#[test]
fn test_dynamic_export_pattern_with_empty_match() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let package_directory = "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg";
    let target_file = format!("{package_directory}/index.d.ts");
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file.to_string(), "".to_string()),
            (
                format!("{package_directory}/package.json"),
                "{\"name\":\"Pkg\",\"exports\":{\"./foo/*\":\"./index*.d.ts\"}}".to_string(),
            ),
            (
                target_file.clone(),
                "export const value: number;".to_string(),
            ),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));

    let (resolved, _) = resolver.resolve_module_name(
        "Pkg/foo/",
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved),
        "expected empty wildcard package export to resolve"
    );
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints = resolver.get_entrypoints_from_package_json_info(&package_json, "Pkg", false);
    assert_eq!(entrypoints.len(), 1, "entrypoint count");
    let generated = entrypoints[0].module_specifier.as_string().to_string();
    let (resolved, _) = resolver.resolve_module_name(
        &generated,
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        is_resolved(&resolved)
            && resolved.as_ref().unwrap().resolved_file_name.as_string() == target_file,
        "generated module specifier {generated:?} resolved to {:?}, expected {target_file:?}",
        resolved.as_ref().map(|r| r.resolved_file_name.as_string()),
    );
}

/// `func TestUnaddressableEmptyExportPatternIsNotAnEntrypoint(t *testing.T)`
#[test]
fn test_unaddressable_empty_export_pattern_is_not_an_entrypoint() {
    let source_file = "^/~ts-uri~/custom/ts-nul-authority/src/main.ts";
    let package_directory = "^/~ts-uri~/custom/ts-nul-authority/node_modules/Pkg";
    let fs = tsc_vfs::vfstest::from_map(
        [
            (source_file.to_string(), "".to_string()),
            (
                format!("{package_directory}/package.json"),
                "{\"name\":\"Pkg\",\"exports\":{\"./*\":\"./index*.d.ts\"}}".to_string(),
            ),
            (
                format!("{package_directory}/index.d.ts"),
                "export const value: number;".to_string(),
            ),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = DefaultResolver::new(resolver_options(
        test_host(fs, "^/~ts-uri~/custom/ts-nul-authority/"),
        bundler_options(),
    ));

    let _ = resolver.resolve_module_name(
        "Pkg",
        &tsc_tspath::rooted_file_path_from_normalized(source_file),
        RESOLUTION_MODE_ESM,
        None,
    );
    let package_json =
        first_existing_package_json_entry(&resolver).expect("expected package JSON cache entry");
    let entrypoints = resolver.get_entrypoints_from_package_json_info(&package_json, "Pkg", false);
    assert!(
        entrypoints.is_empty(),
        "expected unaddressable empty wildcard match to be omitted"
    );
}

/// `func TestResolverRejectsMismatchedPackageJsonCacheCaseSensitivity(t *testing.T)`
#[test]
fn test_resolver_rejects_mismatched_package_json_cache_case_sensitivity() {
    let fs = tsc_vfs::vfstest::from_map(
        std::iter::empty::<(&str, &str)>(),
        CaseSensitivity::CaseSensitive,
    );
    let host = test_host(fs, "/repo");
    // Go: defer recover() — expects NewResolverWithOptions to panic.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        DefaultResolver::new_with_options(
            host,
            Arc::new(CompilerOptions::default()),
            RootedDirectoryPath::default(),
            "",
            ResolverOptions {
                host: Arc::new(ResolutionTestInputs {
                    fs: tsc_vfs::vfstest::from_map(
                        std::iter::empty::<(&str, &str)>(),
                        CaseSensitivity::CaseSensitive,
                    ),
                    cwd: RootedDirectoryPath::from("/repo"),
                }),
                compiler_options: Arc::new(CompilerOptions::default()),
                typings_location: RootedDirectoryPath::default(),
                project_name: String::new(),
                extra_extensions: Vec::new(),
                package_json_cache: Some(Arc::new(InfoCache::new(
                    CaseSensitivity::CaseInsensitive,
                ))),
            },
        )
    }));
    assert!(
        result.is_err(),
        "expected mismatched package JSON cache case sensitivity to panic"
    );
}

/// `func TestResolveModuleNameBlockedByNullExport(t *testing.T)`
#[test]
fn test_resolve_module_name_blocked_by_null_export() {
    let fs = tsc_vfs::vfstest::from_map(
        [
            (
                "/repo/node_modules/pkg/package.json",
                "{\"name\":\"pkg\",\"exports\":{\".\":null}}",
            ),
            ("/repo/src/file.ts", ""),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = bundler_resolver(fs, "/repo");

    let (resolved, _) = resolver.resolve_module_name(
        "pkg",
        &RootedFilePath::from("/repo/src/file.ts"),
        RESOLUTION_MODE_ESM,
        None,
    );
    let resolved = resolved.expect("resolve_module_name returns Some");
    assert!(
        !resolved.is_resolved(),
        "expected null export to remain unresolved, got {:?}",
        resolved.resolved_file_name.as_string()
    );
    assert_eq!(
        resolved.resolved_path,
        PathKey::default(),
        "unresolved module has path"
    );
}

/// `func TestResolveModuleNameExportTargetWithTrailingSlashDoesNotResolveAsFile(t *testing.T)`
#[test]
fn test_resolve_module_name_export_target_with_trailing_slash_does_not_resolve_as_file() {
    let fs = tsc_vfs::vfstest::from_map(
        [
            (
                "/repo/node_modules/pkg/package.json",
                "{\"name\":\"pkg\",\"exports\":{\".\":\"./index.d.ts/\"}}",
            ),
            (
                "/repo/node_modules/pkg/index.d.ts",
                "export const x: number;",
            ),
            ("/repo/src/file.ts", ""),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = bundler_resolver(fs, "/repo");

    let (resolved, _) = resolver.resolve_module_name(
        "pkg",
        &RootedFilePath::from("/repo/src/file.ts"),
        RESOLUTION_MODE_ESM,
        None,
    );
    assert!(
        !is_resolved(&resolved),
        "expected directory-only export target to remain unresolved, got {:?}",
        resolved.as_ref().map(|r| r.resolved_file_name.as_string())
    );
}

/// `type blockingFS struct` — wraps a Vfs and forces `file_exists` calls for
/// `target_path` to block on `gate` until released. Each caller sends on
/// `arrived` when it reaches the gate. Used to deterministically reproduce the
/// `package.json` info-cache insert race described in
/// https://github.com/microsoft/TypeScript/tsc/issues/3526.
///
/// PORT: Go's `<-gate` waits for channel close; here `gate` is an
/// `mpsc::Receiver` whose `Sender` is dropped to release it. `Receiver` is not
/// `Sync`, so it lives behind a `Mutex` — the second waiter unblocks
/// immediately once the first releases the lock after the senders are gone.
struct BlockingFs {
    inner: Arc<dyn Vfs>,
    target_path: RootedFilePath,
    gate: Mutex<Receiver<()>>,
    arrived: Sender<()>,
}

impl Vfs for BlockingFs {
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.inner.case_sensitivity()
    }
    fn file_exists(&self, path: &RootedFilePath) -> bool {
        if *path == self.target_path {
            let _ = self.arrived.send(());
            let _ = self.gate.lock().unwrap().recv();
        }
        self.inner.file_exists(path)
    }
    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        self.inner.read_file(path)
    }
    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.write_file(path, data)
    }
    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.append_file(path, data)
    }
    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.inner.remove(path)
    }
    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.inner.chtimes(path, a_time, m_time)
    }
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.inner.directory_exists(path)
    }
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.inner.get_accessible_entries(path)
    }
    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.inner.stat(path)
    }
    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.inner.realpath(path)
    }
}

/// `func waitForSignal(t *testing.T, ch <-chan struct{}, description string)`
fn wait_for_signal(ch: &Receiver<()>, description: &str) {
    match ch.recv_timeout(Duration::from_secs(60)) {
        Ok(()) | Err(mpsc::RecvTimeoutError::Disconnected) => {}
        Err(mpsc::RecvTimeoutError::Timeout) => {
            panic!("timed out waiting for {description}")
        }
    }
}

/// `type flipFileExistsFS struct` — wraps a Vfs and returns false for the
/// first `file_exists` call to `target_path`, then true for the second. Both
/// calls signal arrival via channel then block until released via their
/// respective gates. `read_file` for the target path also signals arrival
/// then blocks, so the "file doesn't exist" store completes before the
/// "file exists" store (reproducing the `load_or_store` race).
struct FlipFileExistsFs {
    inner: Arc<dyn Vfs>,
    target_path: RootedFilePath,
    call_count: AtomicI32,
    first_arrived: Mutex<Option<Sender<()>>>,
    second_arrived: Mutex<Option<Sender<()>>>,
    first_gate: Mutex<Receiver<()>>,
    second_gate: Mutex<Receiver<()>>,
    read_arrived: Mutex<Option<Sender<()>>>,
    read_gate: Mutex<Receiver<()>>,
}

impl FlipFileExistsFs {
    fn signal(sender: &Mutex<Option<Sender<()>>>) {
        // Go `close(ch)`: signal exactly once by taking the sender.
        if let Some(tx) = sender.lock().unwrap().take() {
            let _ = tx.send(());
        }
    }
}

impl Vfs for FlipFileExistsFs {
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.inner.case_sensitivity()
    }
    fn file_exists(&self, path: &RootedFilePath) -> bool {
        if *path == self.target_path {
            let n = self.call_count.fetch_add(1, Ordering::SeqCst) + 1;
            if n == 1 {
                Self::signal(&self.first_arrived);
                let _ = self.first_gate.lock().unwrap().recv();
                return false; // first caller: simulate "file not yet visible"
            }
            if n == 2 {
                Self::signal(&self.second_arrived);
                let _ = self.second_gate.lock().unwrap().recv();
                return self.inner.file_exists(path); // second caller: file is visible
            }
        }
        self.inner.file_exists(path)
    }
    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        if *path == self.target_path {
            Self::signal(&self.read_arrived);
            let _ = self.read_gate.lock().unwrap().recv();
        }
        self.inner.read_file(path)
    }
    fn write_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.write_file(path, data)
    }
    fn append_file(&self, path: &RootedFilePath, data: &str) -> Result<(), FsError> {
        self.inner.append_file(path, data)
    }
    fn remove(&self, path: &RootedPath) -> Result<(), FsError> {
        self.inner.remove(path)
    }
    fn chtimes(
        &self,
        path: &RootedPath,
        a_time: SystemTime,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.inner.chtimes(path, a_time, m_time)
    }
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        self.inner.directory_exists(path)
    }
    fn get_accessible_entries(&self, path: &RootedDirectoryPath) -> Entries {
        self.inner.get_accessible_entries(path)
    }
    fn stat(&self, path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        self.inner.stat(path)
    }
    fn realpath(&self, path: &RootedPath) -> RootedPath {
        self.inner.realpath(path)
    }
}

struct FlipGates {
    first_arrived: Receiver<()>,
    second_arrived: Receiver<()>,
    read_arrived: Receiver<()>,
    first_gate: Sender<()>,
    second_gate: Sender<()>,
    read_gate: Sender<()>,
}

fn flip_fs(inner: Arc<dyn Vfs>, target_path: &str) -> (Arc<dyn Vfs>, FlipGates) {
    let (first_arrived_tx, first_arrived) = mpsc::channel();
    let (second_arrived_tx, second_arrived) = mpsc::channel();
    let (read_arrived_tx, read_arrived) = mpsc::channel();
    let (first_gate, first_gate_rx) = mpsc::channel();
    let (second_gate, second_gate_rx) = mpsc::channel();
    let (read_gate, read_gate_rx) = mpsc::channel();
    (
        Arc::new(FlipFileExistsFs {
            inner,
            target_path: RootedFilePath::from(target_path),
            call_count: AtomicI32::new(0),
            first_arrived: Mutex::new(Some(first_arrived_tx)),
            second_arrived: Mutex::new(Some(second_arrived_tx)),
            first_gate: Mutex::new(first_gate_rx),
            second_gate: Mutex::new(second_gate_rx),
            read_arrived: Mutex::new(Some(read_arrived_tx)),
            read_gate: Mutex::new(read_gate_rx),
        }),
        FlipGates {
            first_arrived,
            second_arrived,
            read_arrived,
            first_gate,
            second_gate,
            read_gate,
        },
    )
}

// Regression test for https://github.com/microsoft/TypeScript/tsc/issues/3526.
//
// Two threads resolve the same package via specifiers that differ only by a
// trailing slash (`pkg` and `pkg/`). A blocking FS holds both at the
// `file_exists` check for `package.json` — *after* each has confirmed a
// `package.json` info-cache miss but *before* either has stored an entry.
// When released, both proceed to `load_or_store` and one of them loses.
/// `func TestResolveModuleNameTrailingSlashRace(t *testing.T)`
#[test]
fn test_resolve_module_name_trailing_slash_race() {
    let pkg_json_path = "/repo/node_modules/pkg/package.json";
    // `types` points at a file that is not discoverable through any fallback
    // path: there is no `index.*` and no `main`. The only way to resolve `pkg`
    // (or `pkg/`) is via the package.json `types` field inside
    // `loadNodeModuleFromDirectoryWorker`, which is exactly the step that the
    // bug skips when `candidate` and `packageInfo.PackageDirectory` mismatch.
    let inner = tsc_vfs::vfstest::from_map(
        [
            (
                pkg_json_path,
                "{\"name\":\"pkg\",\"types\":\"./typings/index.d.ts\"}",
            ),
            (
                "/repo/node_modules/pkg/typings/index.d.ts",
                "export const x: number;",
            ),
            // Distinct containing files so each `resolve_module_name` call has
            // a unique module-resolution-cache key.
            ("/repo/src/a/file.ts", ""),
            ("/repo/src/b/file.ts", ""),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let (gate_tx, gate_rx) = mpsc::channel::<()>();
    let (arrived_tx, arrived_rx) = mpsc::channel::<()>();
    let fs: Arc<dyn Vfs> = Arc::new(BlockingFs {
        inner,
        target_path: RootedFilePath::from(pkg_json_path),
        gate: Mutex::new(gate_rx),
        arrived: arrived_tx,
    });
    let resolver = bundler_resolver(fs, "/repo");

    let (results_tx, results_rx) = mpsc::channel::<(&'static str, bool)>();
    std::thread::scope(|s| {
        let mut handles = Vec::new();
        for name in ["pkg", "pkg/"] {
            let containing_file = if name.ends_with('/') {
                "/repo/src/b/file.ts"
            } else {
                "/repo/src/a/file.ts"
            };
            let resolver = &resolver;
            let results_tx = results_tx.clone();
            handles.push(s.spawn(move || {
                let (r, _) = resolver.resolve_module_name(
                    name,
                    &tsc_tspath::rooted_file_path_from_normalized(containing_file),
                    RESOLUTION_MODE_ESM,
                    None,
                );
                let _ = results_tx.send((name, is_resolved(&r)));
            }));
        }

        // Wait for both threads to reach the file_exists gate, guaranteeing
        // both have observed a package.json info-cache miss.
        wait_for_signal(&arrived_rx, "first FileExists gate arrival");
        wait_for_signal(&arrived_rx, "second FileExists gate arrival");
        drop(gate_tx);

        for handle in handles {
            handle.join().unwrap();
        }
    });
    // Go: close(results)
    drop(results_tx);

    for (name, resolved) in results_rx.iter() {
        assert!(resolved, "{name:?} failed to resolve");
    }
}

// Regression test for https://github.com/microsoft/TypeScript/tsc/issues/1290.
//
// Two threads resolve `pkg/sub` concurrently. Both miss the package.json
// info-cache for the root package directory. A `FlipFileExistsFs` forces the
// first thread's `file_exists` to return false (simulating the file not yet
// being visible), so it stores a nil-contents cache entry. The second
// thread's `file_exists` returns true, but its store (`load_or_store`)
// returns the first thread's nil-contents entry. Without the `exists()`
// guard on the `typesVersions` lookup, `contents.get_version_paths`
// dereferences nil and panics. With the guard the nil-contents entry is
// safely skipped.
/// `func TestResolveSubpathNilContentsRace(t *testing.T)`
#[test]
fn test_resolve_subpath_nil_contents_race() {
    let root_pkg_json = "/repo/node_modules/pkg/package.json";
    let inner = tsc_vfs::vfstest::from_map(
        [
            (root_pkg_json, "{\"name\":\"pkg\",\"version\":\"1.0.0\"}"),
            (
                "/repo/node_modules/pkg/sub/index.d.ts",
                "export declare const sub: number;",
            ),
            ("/repo/node_modules/pkg/sub/index.js", "exports.sub = 1;"),
            ("/repo/src/a/file.ts", ""),
            ("/repo/src/b/file.ts", ""),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let (fs, gates) = flip_fs(inner, root_pkg_json);
    let resolver = bundler_resolver(fs, "/repo");

    let panicked = AtomicBool::new(false);
    let (results_tx, results_rx) = mpsc::channel::<(&'static str, bool)>();
    std::thread::scope(|s| {
        let mut handles = Vec::new();
        // Two threads both resolve "pkg/sub". Each calls
        // get_package_json_info for the root package directory, reaching
        // file_exists for root_pkg_json.
        for containing_file in ["/repo/src/a/file.ts", "/repo/src/b/file.ts"] {
            let resolver = &resolver;
            let panicked = &panicked;
            let results_tx = results_tx.clone();
            handles.push(s.spawn(move || {
                let (r, _) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    resolver.resolve_module_name(
                        "pkg/sub",
                        &tsc_tspath::rooted_file_path_from_normalized(containing_file),
                        RESOLUTION_MODE_ESM,
                        None,
                    )
                }))
                .unwrap_or_else(|_| {
                    panicked.store(true, Ordering::SeqCst);
                    (None, Vec::new())
                });
                let _ = results_tx.send((containing_file, is_resolved(&r)));
            }));
        }

        // Phase 1: Wait for both threads to reach file_exists for the root
        // package.json, guaranteeing both have observed a cache miss.
        wait_for_signal(
            &gates.first_arrived,
            "first root package.json FileExists arrival",
        );
        wait_for_signal(
            &gates.second_arrived,
            "second root package.json FileExists arrival",
        );

        // Phase 2: Release the first file_exists caller (returns false).
        // It enters the "file not found" branch and stores a nil-contents
        // entry — this is nearly instant (no read_file).
        drop(gates.first_gate);

        // Phase 3: Release the second file_exists caller (returns true).
        // It proceeds to read_file, which we gate separately to ensure the
        // first thread's nil-contents store has completed.
        drop(gates.second_gate);

        // Phase 4: Wait for the second thread to reach read_file, then
        // release. By this point the first thread has stored its
        // nil-contents entry. The second thread's `load_or_store` will
        // return that stale entry.
        wait_for_signal(&gates.read_arrived, "root package.json ReadFile arrival");
        drop(gates.read_gate);

        for handle in handles {
            handle.join().unwrap();
        }
    });
    // Go: close(results)
    drop(results_tx);

    assert!(
        !panicked.load(Ordering::SeqCst),
        "resolver panicked due to nil Contents dereference in loadModuleFromSpecificNodeModulesDirectory"
    );
    for (containing_file, resolved) in results_rx.iter() {
        assert!(resolved, "{containing_file:?} failed to resolve pkg/sub");
    }
}

/// `func TestNodeModulePackageRoot(t *testing.T)`
#[test]
fn test_node_module_package_root() {
    use crate::util::{node_module_package_root_for_directory, node_module_package_root_for_file};

    struct Case {
        name: &'static str,
        path: &'static str,
        is_folder: bool,
        want: &'static str,
    }
    let tests = [
        Case {
            name: "file in package",
            path: "/a/node_modules/b/lib/index.d.ts",
            is_folder: false,
            want: "/a/node_modules/b",
        },
        Case {
            name: "file in scoped package",
            path: "/a/node_modules/@scope/b/lib/index.d.ts",
            is_folder: false,
            want: "/a/node_modules/@scope/b",
        },
        Case {
            name: "folder subpath",
            path: "/a/node_modules/b/lib/File",
            is_folder: true,
            want: "/a/node_modules/b",
        },
        Case {
            name: "folder subpath scoped",
            path: "/a/node_modules/@scope/b/lib/File",
            is_folder: true,
            want: "/a/node_modules/@scope/b",
        },
        Case {
            name: "package root folder",
            path: "/a/node_modules/b",
            is_folder: true,
            want: "/a/node_modules/b",
        },
        Case {
            name: "scoped package root folder",
            path: "/a/node_modules/@scope/b",
            is_folder: true,
            want: "/a/node_modules/@scope/b",
        },
        Case {
            name: "package root interpreted as file",
            path: "/a/node_modules/b",
            is_folder: false,
            want: "/a/node_modules",
        },
        Case {
            name: "scoped package root interpreted as file",
            path: "/a/node_modules/@scope/b",
            is_folder: false,
            want: "/a/node_modules/@scope",
        },
        // A bare scope directory has no package name; must not panic
        // (https://github.com/microsoft/TypeScript/tsc/issues/4373).
        Case {
            name: "scope-only folder",
            path: "/a/node_modules/@scope",
            is_folder: true,
            want: "/a/node_modules/@scope",
        },
        Case {
            name: "types scope-only folder",
            path: "/a/node_modules/@types",
            is_folder: true,
            want: "/a/node_modules/@types",
        },
        Case {
            name: "not in node_modules",
            path: "/a/src/index.ts",
            is_folder: false,
            want: "",
        },
    ];

    for tt in tests {
        let got = if tt.is_folder {
            node_module_package_root_for_directory(
                &tsc_tspath::rooted_directory_path_from_normalized(tt.path),
            )
        } else {
            node_module_package_root_for_file(&tsc_tspath::rooted_file_path_from_normalized(
                tt.path,
            ))
        };
        assert_eq!(
            got.as_string(),
            tt.want,
            "nodeModulesPackageRoot({:?}, {}) [{}]",
            tt.path,
            tt.is_folder,
            tt.name
        );
    }
}

// Regression test for https://github.com/microsoft/TypeScript/tsc/issues/4478.
//
// While resolving a package with peerDependencies, two threads look up the
// peer package's package.json concurrently. A `FlipFileExistsFs` forces the
// first lookup to cache a nil-contents entry and the second lookup to receive
// that stale entry from `load_or_store`. The resolver must not dereference
// the peer package.json contents unless the entry actually exists.
/// `func TestResolvePeerDependencyNilContentsRace(t *testing.T)`
#[test]
fn test_resolve_peer_dependency_nil_contents_race() {
    let peer_pkg_json = "/repo/node_modules/peer/package.json";
    let inner = tsc_vfs::vfstest::from_map(
        [
            (
                "/repo/node_modules/pkg/package.json",
                "{\"name\":\"pkg\",\"version\":\"1.0.0\",\"types\":\"index.d.ts\",\"peerDependencies\":{\"peer\":\"*\"}}",
            ),
            (
                "/repo/node_modules/pkg/index.d.ts",
                "export declare const x: number;",
            ),
            (peer_pkg_json, "{\"name\":\"peer\",\"version\":\"2.0.0\"}"),
            ("/repo/src/a/file.ts", ""),
            ("/repo/src/b/file.ts", ""),
        ],
        CaseSensitivity::CaseSensitive,
    );
    let (fs, gates) = flip_fs(inner, peer_pkg_json);
    let resolver = bundler_resolver(fs, "/repo");

    let panicked = AtomicBool::new(false);
    let (results_tx, results_rx) = mpsc::channel::<(&'static str, bool)>();
    let mut first_result: Option<(&'static str, bool)> = None;
    std::thread::scope(|s| {
        let mut handles = Vec::new();
        for containing_file in ["/repo/src/a/file.ts", "/repo/src/b/file.ts"] {
            let resolver = &resolver;
            let panicked = &panicked;
            let results_tx = results_tx.clone();
            handles.push(s.spawn(move || {
                let (r, _) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    resolver.resolve_module_name(
                        "pkg",
                        &tsc_tspath::rooted_file_path_from_normalized(containing_file),
                        RESOLUTION_MODE_ESM,
                        None,
                    )
                }))
                .unwrap_or_else(|_| {
                    panicked.store(true, Ordering::SeqCst);
                    (None, Vec::new())
                });
                let _ = results_tx.send((containing_file, is_resolved(&r)));
            }));
        }

        wait_for_signal(
            &gates.first_arrived,
            "first peer package.json FileExists arrival",
        );
        wait_for_signal(
            &gates.second_arrived,
            "second peer package.json FileExists arrival",
        );
        drop(gates.first_gate);
        match results_rx.recv_timeout(Duration::from_secs(60)) {
            Ok(result) => first_result = Some(result),
            Err(_) => panic!("timed out waiting for first peer package.json lookup to finish"),
        }
        drop(gates.second_gate);
        wait_for_signal(&gates.read_arrived, "peer package.json ReadFile arrival");
        drop(gates.read_gate);

        for handle in handles {
            handle.join().unwrap();
        }
    });

    assert!(
        !panicked.load(Ordering::SeqCst),
        "resolver panicked due to nil Contents dereference in readPackageJsonPeerDependencies"
    );
    let (containing_file, resolved) = first_result.expect("first result");
    assert!(resolved, "{containing_file:?} failed to resolve pkg");
    drop(results_tx);
    for (containing_file, resolved) in results_rx.iter() {
        assert!(resolved, "{containing_file:?} failed to resolve pkg");
    }
}

