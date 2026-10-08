// Ported from tsc/internal/module/resolver_internal_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_core::options_generated::CompilerOptions;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath};
use tsc_vfs::Vfs;

use super::*;

/// The Go tests build a bare `&DefaultResolver{fs: fs}` struct literal; Rust
/// requires every field, so construct the equivalent all-default resolver.
fn resolver_for_fs(fs: Arc<dyn Vfs>) -> DefaultResolver {
    DefaultResolver {
        data: ResolutionData::default(),
        fs,
        base_directory: RootedDirectoryPath::default(),
        module_resolution_cache: ModuleResolutionCache::default(),
        type_ref_directive_resolution_cache: TypeRefDirectiveResolutionCache::default(),
        parsed_patterns_for_paths: ParsedPatternsCache::default(),
    }
}

/// `func TestNormalizePathForCJSResolutionPreservesDirectoryIntent(t *testing.T)`
#[test]
fn test_normalize_path_for_cjs_resolution_preserves_directory_intent() {
    struct Case {
        name: &'static str,
        containing_directory: &'static str,
        module_name: &'static str,
        path: &'static str,
        text: &'static str,
        directory_only: bool,
    }

    let tests = [
        Case { name: "file", containing_directory: "/project", module_name: "file", path: "/project/file", text: "/project/file", directory_only: false },
        Case { name: "trailing separator", containing_directory: "/project", module_name: "directory/", path: "/project/directory", text: "/project/directory/", directory_only: true },
        Case { name: "current directory", containing_directory: "/project", module_name: ".", path: "/project", text: "/project/", directory_only: true },
        Case { name: "current directory with backslash", containing_directory: "/project", module_name: ".\\", path: "/project", text: "/project/", directory_only: true },
        Case { name: "nested parent directory", containing_directory: "/project/src", module_name: "../lib/", path: "/project/lib", text: "/project/lib/", directory_only: true },
        Case { name: "nested parent directory with backslashes", containing_directory: "/project/src", module_name: "..\\lib\\", path: "/project/lib", text: "/project/lib/", directory_only: true },
        Case { name: "posix root", containing_directory: "/project", module_name: "..", path: "/", text: "/", directory_only: true },
        Case { name: "drive root", containing_directory: "c:/project", module_name: "..", path: "c:/", text: "c:/", directory_only: true },
        Case { name: "drive root without separator", containing_directory: "/project", module_name: "c:", path: "c:/", text: "c:/", directory_only: true },
        Case { name: "UNC root without separator", containing_directory: "/project", module_name: "//server", path: "//server/", text: "//server/", directory_only: true },
        Case { name: "URL root", containing_directory: "file:///project", module_name: "..", path: "file:///", text: "file:///", directory_only: true },
        Case { name: "URL authority root without separator", containing_directory: "/project", module_name: "file://server", path: "file://server/", text: "file://server/", directory_only: true },
        Case {
            name: "dynamic reserved prefix",
            containing_directory: "^/~ts-uri~/custom/ts-nul-authority/folder",
            module_name: "./~ts-uri-escape~file",
            path: "^/~ts-uri~/custom/ts-nul-authority/folder/~ts-uri-escape~7e74732d7572692d6573636170657e66696c65~",
            text: "^/~ts-uri~/custom/ts-nul-authority/folder/~ts-uri-escape~7e74732d7572692d6573636170657e66696c65~",
            directory_only: false,
        },
        Case {
            name: "dynamic reserved prefix with extension",
            containing_directory: "^/~ts-uri~/custom/ts-nul-authority/folder",
            module_name: "./~ts-uri-escape~file.ts",
            path: "^/~ts-uri~/custom/ts-nul-authority/folder/~ts-uri-escape~7e74732d7572692d6573636170657e66696c65~.ts",
            text: "^/~ts-uri~/custom/ts-nul-authority/folder/~ts-uri-escape~7e74732d7572692d6573636170657e66696c65~.ts",
            directory_only: false,
        },
        Case {
            name: "dynamic reserved directory prefix",
            containing_directory: "^/~ts-uri~/custom/ts-nul-authority/folder",
            module_name: "./~ts-uri-escape~dir/file",
            path: "^/~ts-uri~/custom/ts-nul-authority/folder/~ts-uri-escape~7e74732d7572692d6573636170657e646972~/file",
            text: "^/~ts-uri~/custom/ts-nul-authority/folder/~ts-uri-escape~7e74732d7572692d6573636170657e646972~/file",
            directory_only: false,
        },
        Case {
            name: "dynamic dotted directory intent",
            containing_directory: "^/~ts-uri~/custom/ts-nul-authority/folder",
            module_name: "./~ts-uri-escape~dir.js/",
            path: "^/~ts-uri~/custom/ts-nul-authority/folder/~ts-uri-escape~7e74732d7572692d6573636170657e6469722e6a73~",
            text: "^/~ts-uri~/custom/ts-nul-authority/folder/~ts-uri-escape~7e74732d7572692d6573636170657e6469722e6a73~/",
            directory_only: true,
        },
    ];

    for test in tests {
        let candidate = normalize_path_for_cjs_resolution(
            &tsc_tspath::rooted_directory_path_from_normalized(test.containing_directory),
            test.module_name,
        );
        assert_eq!(
            candidate.path.as_string(),
            test.path,
            "{}: path",
            test.name
        );
        assert_eq!(
            candidate.directory_only, test.directory_only,
            "{}: directoryOnly",
            test.name
        );
        assert_eq!(candidate.as_string(), test.text, "{}: AsString", test.name);
        assert_eq!(
            candidate.has_trailing_directory_separator(),
            test.directory_only,
            "{}: HasTrailingDirectorySeparator",
            test.name
        );
    }
}

/// `func TestPackageJSONPathWithTrailingSeparatorDoesNotResolveAsFile(t *testing.T)`
#[test]
fn test_package_json_path_with_trailing_separator_does_not_resolve_as_file() {
    let fs = tsc_vfs::vfstest::from_map(
        [("/project/index.d.ts", "export {};")],
        CaseSensitivity::CaseSensitive,
    );
    let resolver = resolver_for_fs(fs);
    let mut state =
        ResolutionState::bare(&resolver, Arc::new(CompilerOptions::default()));

    let candidate = resolve_resolution_candidate("/project", &["index.d.ts/"]);
    // PORT: `result.shouldContinueSearching()` is `Option::is_none()`.
    let result =
        state.load_file_name_from_package_json_field(EXTENSIONS_DECLARATION, &candidate, "./index.d.ts/");
    assert!(result.is_none(), "directory-only candidate resolved");
}

/// `func TestExtensionReplacementPreservesEmptyAndDotStems(t *testing.T)`
#[test]
fn test_extension_replacement_preserves_empty_and_dot_stems() {
    for (import_name, expected) in [
        (".js", "/project/.native.ts"),
        ("..js", "/project/..native.ts"),
        ("...js", "/project/...native.ts"),
        (".js", "/project/.native.d.ts"),
    ] {
        let fs = tsc_vfs::vfstest::from_map(
            [(expected, "export {};")],
            CaseSensitivity::CaseSensitive,
        );
        let resolver = resolver_for_fs(fs);
        let mut state = ResolutionState::bare(
            &resolver,
            Arc::new(CompilerOptions {
                module_suffixes: Some(vec![".native".to_string(), String::new()]),
                ..CompilerOptions::default()
            }),
        );
        let result = state.load_module_from_file_no_implicit_extensions(
            EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION,
            &resolve_resolution_candidate("/project", &[import_name]),
        );
        assert!(result.is_some(), "expected {expected}");
        assert_eq!(result.unwrap().path.as_string(), expected);
    }
}

/// `func TestOutputDirectoriesRemoveTrailingSeparators(t *testing.T)`
#[test]
fn test_output_directories_remove_trailing_separators() {
    let fs = tsc_vfs::vfstest::from_map(
        std::iter::empty::<(&str, &str)>(),
        CaseSensitivity::CaseSensitive,
    );
    let resolver = resolver_for_fs(fs);
    let state = ResolutionState::bare(
        &resolver,
        Arc::new(CompilerOptions {
            declaration_dir: tsc_tspath::rooted_directory_path_from_absolute("/project/types/"),
            out_dir: tsc_tspath::rooted_directory_path_from_absolute("/project/dist/"),
            ..CompilerOptions::default()
        }),
    );

    let directories = state.get_output_directories();
    assert_eq!(
        directories,
        vec![
            RootedDirectoryPath::from("/project/types"),
            RootedDirectoryPath::from("/project/dist"),
        ]
    );
}
