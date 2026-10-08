// Ported from tsc/internal/modulespecifiers/specifiers_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use tsc_ast::ids::NodeId;
use tsc_ast::utilities::HasFileName;
use tsc_core::compileroptions::{RESOLUTION_MODE_NONE, ResolutionMode};
use tsc_core::options_generated::CompilerOptions;
use tsc_json as json;
use tsc_module::ResolvedModule;
use tsc_outputpaths::OutputPathsHost;
use tsc_packagejson::{ExportsOrImports, InfoCacheEntry};
use tsc_symlinks::{KnownDirectoryLink, KnownSymlinks};
use tsc_tsoptions::parsedcommandline::SourceOutputAndProjectReference;
use tsc_tspath::{self as tspath, CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};

use crate::specifiers::{
    contains_ignored_path, get_each_file_name_of_module, is_package_main_file,
    module_specifier_contains_node_modules, process_ending,
    try_get_module_name_from_exports_or_imports,
};
use crate::types::{MatchingMode, ModuleSpecifierEnding, ModuleSpecifierGenerationHost};
use crate::util::{
    get_node_module_path_parts, is_path_relative_to_parent,
    try_get_real_file_name_for_non_js_declaration_file_name,
};

#[test]
fn test_get_node_module_path_parts() {
    struct T {
        path: &'static str,
        top_level_node_modules_search_root: &'static str,
        top_level_node_modules_directory: &'static str,
        package_root_directory: &'static str,
        package_name: &'static str,
        package_relative_path: &'static str,
        has_nested_node_modules: bool,
        is_direct_node_modules_file: bool,
    }
    let tests = [
        T {
            path: "/workspace/node_modules/pkg/lib/index.d.ts",
            top_level_node_modules_search_root: "/workspace",
            top_level_node_modules_directory: "/workspace/node_modules",
            package_root_directory: "/workspace/node_modules/pkg",
            package_name: "pkg",
            package_relative_path: "lib/index.d.ts",
            has_nested_node_modules: false,
            is_direct_node_modules_file: false,
        },
        T {
            path: "/node_modules/@scope/pkg/index.d.ts",
            top_level_node_modules_search_root: "/",
            top_level_node_modules_directory: "/node_modules",
            package_root_directory: "/node_modules/@scope/pkg",
            package_name: "@scope/pkg",
            package_relative_path: "index.d.ts",
            has_nested_node_modules: false,
            is_direct_node_modules_file: false,
        },
        T {
            path: "c:/node_modules/pkg/index.d.ts",
            top_level_node_modules_search_root: "c:/",
            top_level_node_modules_directory: "c:/node_modules",
            package_root_directory: "c:/node_modules/pkg",
            package_name: "pkg",
            package_relative_path: "index.d.ts",
            has_nested_node_modules: false,
            is_direct_node_modules_file: false,
        },
        T {
            path: "/workspace/node_modules/pkg/node_modules/@scope/dep/index.d.ts",
            top_level_node_modules_search_root: "/workspace",
            top_level_node_modules_directory: "/workspace/node_modules",
            package_root_directory: "/workspace/node_modules/pkg/node_modules/@scope/dep",
            package_name: "@scope/dep",
            package_relative_path: "index.d.ts",
            has_nested_node_modules: true,
            is_direct_node_modules_file: false,
        },
    ];

    for tt in &tests {
        let parts = get_node_module_path_parts(&tspath::rooted_file_path_from_normalized(tt.path));
        let Some(parts) = parts else {
            panic!("get_node_module_path_parts({:?}) returned None", tt.path);
        };
        assert!(
            parts.top_level_node_modules_search_root.as_string()
                == tt.top_level_node_modules_search_root
                && parts.top_level_node_modules_directory.as_string()
                    == tt.top_level_node_modules_directory
                && parts.package_root_directory.as_string() == tt.package_root_directory
                && parts.package_name == tt.package_name
                && parts.package_relative_path.as_string() == tt.package_relative_path
                && parts.has_nested_node_modules == tt.has_nested_node_modules
                && parts.is_direct_node_modules_file == tt.is_direct_node_modules_file,
            "get_node_module_path_parts({:?}) = {:?}",
            tt.path,
            parts,
        );
    }

    for path in ["/workspace/src/index.ts"] {
        let parts = get_node_module_path_parts(&tspath::rooted_file_path_from_normalized(path));
        assert!(
            parts.is_none(),
            "get_node_module_path_parts({path:?}) = {parts:?}, want None"
        );
    }

    let direct = get_node_module_path_parts(&tspath::rooted_file_path_from_normalized(
        "/workspace/node_modules/pkg",
    ));
    assert!(
        direct
            .as_ref()
            .is_some_and(|d| d.is_direct_node_modules_file && d.package_name == "pkg"),
        "get_node_module_path_parts for direct node_modules file = {direct:?}"
    );
    let direct_scoped = get_node_module_path_parts(&tspath::rooted_file_path_from_normalized(
        "/workspace/node_modules/@scope",
    ));
    assert!(
        direct_scoped
            .as_ref()
            .is_some_and(|d| d.is_direct_node_modules_file && d.package_name == "@scope"),
        "get_node_module_path_parts for direct scoped node_modules file = {direct_scoped:?}"
    );
}

// Mock host for testing
struct MockModuleSpecifierGenerationHost {
    current_dir: RootedDirectoryPath,
    content_mapper_extensions: Vec<String>,
    case_sensitivity: CaseSensitivity,
    symlink_cache: Option<KnownSymlinks>,
    existing_files: Option<HashMap<RootedFilePath, bool>>,
    file_exists_calls: RefCell<Vec<RootedFilePath>>,
}

impl Default for MockModuleSpecifierGenerationHost {
    fn default() -> Self {
        Self {
            current_dir: RootedDirectoryPath::default(),
            content_mapper_extensions: Vec::new(),
            case_sensitivity: CaseSensitivity::CaseInsensitive,
            symlink_cache: None,
            existing_files: None,
            file_exists_calls: RefCell::new(Vec::new()),
        }
    }
}

impl OutputPathsHost for MockModuleSpecifierGenerationHost {
    fn common_source_directory(&self) -> RootedDirectoryPath {
        self.current_dir.clone()
    }

    fn content_mapper_extensions(&self) -> &[String] {
        &self.content_mapper_extensions
    }

    fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }
}

impl ModuleSpecifierGenerationHost for MockModuleSpecifierGenerationHost {
    fn base_directory(&self) -> RootedDirectoryPath {
        self.current_dir.clone()
    }

    fn get_symlink_cache(&self) -> Option<&KnownSymlinks> {
        self.symlink_cache.as_ref()
    }

    fn get_global_typings_cache_location(&self) -> RootedDirectoryPath {
        RootedDirectoryPath::default()
    }

    fn get_project_reference_from_source(
        &self,
        _path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        None
    }

    fn get_redirect_targets(&self, _path: &PathKey) -> Vec<RootedFilePath> {
        Vec::new()
    }

    fn get_source_of_project_reference_if_output_included(
        &self,
        file: &dyn HasFileName,
    ) -> RootedFilePath {
        file.file_name().clone()
    }

    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.file_exists_calls.borrow_mut().push(path.clone());
        if let Some(existing) = &self.existing_files {
            return *existing.get(path).unwrap_or(&false);
        }
        true // Mock implementation
    }

    fn get_nearest_ancestor_directory_with_package_json(
        &self,
        _dirname: &RootedDirectoryPath,
    ) -> RootedDirectoryPath {
        RootedDirectoryPath::default()
    }

    fn get_package_json_info(
        &self,
        _pkg_json_path: &RootedFilePath,
    ) -> Option<Arc<InfoCacheEntry>> {
        None
    }

    fn get_default_resolution_mode_for_file(&self, _file: &dyn HasFileName) -> ResolutionMode {
        RESOLUTION_MODE_NONE
    }

    fn get_resolved_module_from_module_specifier(
        &self,
        _file: &dyn HasFileName,
        _module_specifier: NodeId,
    ) -> Option<ResolvedModule> {
        None
    }

    fn get_mode_for_usage_location(
        &self,
        _file: &dyn HasFileName,
        _module_specifier: NodeId,
    ) -> ResolutionMode {
        RESOLUTION_MODE_NONE
    }
}

#[test]
fn test_get_each_file_name_of_module() {
    struct T {
        name: &'static str,
        importing_file: &'static str,
        imported_file: &'static str,
        prefer_symlinks: bool,
        expected_count: usize,
        expected_paths: Option<Vec<&'static str>>,
    }
    let tests = [
        T {
            name: "basic file path",
            importing_file: "/project/src/main.ts",
            imported_file: "/project/lib/utils.ts",
            prefer_symlinks: false,
            expected_count: 1,
            expected_paths: Some(vec!["/project/lib/utils.ts"]),
        },
        T {
            name: "symlink preference false",
            importing_file: "/project/src/main.ts",
            imported_file: "/project/lib/utils.ts",
            prefer_symlinks: false,
            expected_count: 1,
            expected_paths: None,
        },
        T {
            name: "symlink preference true",
            importing_file: "/project/src/main.ts",
            imported_file: "/project/lib/utils.ts",
            prefer_symlinks: true,
            expected_count: 1,
            expected_paths: None,
        },
        T {
            name: "ignored path with no alternatives",
            importing_file: "/project/src/main.ts",
            imported_file: "/project/node_modules/.pnpm/file.ts",
            prefer_symlinks: false,
            expected_count: 1, // Should return 1 because there's no better option (all paths are ignored)
            expected_paths: None,
        },
    ];

    for tt in &tests {
        let host = MockModuleSpecifierGenerationHost {
            current_dir: tspath::rooted_directory_path_from_normalized("/project"),
            case_sensitivity: CaseSensitivity::CaseSensitive,
            symlink_cache: Some(KnownSymlinks::new(CaseSensitivity::CaseSensitive)),
            ..Default::default()
        };

        let result = get_each_file_name_of_module(
            &tspath::to_rooted_file_path(tt.importing_file, &host.base_directory()),
            &tspath::to_rooted_file_path(tt.imported_file, &host.base_directory()),
            &host,
            tt.prefer_symlinks,
        );

        assert_eq!(
            result.len(),
            tt.expected_count,
            "{}: expected {} paths, got {}",
            tt.name,
            tt.expected_count,
            result.len()
        );

        if let Some(expected_paths) = &tt.expected_paths {
            for (i, expected_path) in expected_paths.iter().enumerate() {
                if i >= result.len() {
                    panic!(
                        "Expected path {i}: {expected_path}, but result has only {} paths",
                        result.len()
                    );
                }
                assert_eq!(
                    result[i].file_name.as_string(),
                    *expected_path,
                    "Expected path {i} to be {expected_path}, got {:?}",
                    result[i].file_name,
                );
            }
        }

        for (i, path) in result.iter().enumerate() {
            assert!(!path.file_name.is_empty(), "Path {i} has empty FileName");
        }
    }
}

#[test]
fn test_get_each_file_name_of_module_with_symlinks() {
    let host = MockModuleSpecifierGenerationHost {
        current_dir: tspath::rooted_directory_path_from_normalized("/project"),
        case_sensitivity: CaseSensitivity::CaseSensitive,
        symlink_cache: Some(KnownSymlinks::new(CaseSensitivity::CaseSensitive)),
        ..Default::default()
    };

    let symlink_path = CaseSensitivity::CaseSensitive
        .path_key(&tspath::rooted_file_path_from_normalized("/project/symlink").as_path());
    let real_directory = KnownDirectoryLink {
        real: tspath::rooted_directory_path_from_normalized("/real/path"),
        real_path: CaseSensitivity::CaseSensitive
            .path_key(&tspath::rooted_file_path_from_normalized("/real/path").as_path()),
        ..Default::default()
    };
    host.symlink_cache.as_ref().unwrap().set_directory(
        tspath::rooted_directory_path_from_normalized("/project/symlink"),
        symlink_path,
        Some(real_directory),
    );

    let result = get_each_file_name_of_module(
        &tspath::rooted_file_path_from_normalized("/project/src/main.ts"),
        &tspath::rooted_file_path_from_normalized("/real/path/file.ts"),
        &host,
        true,
    );

    // Should find the symlink path
    let found = result
        .iter()
        .any(|path| path.file_name.as_string() == "/project/symlink/file.ts");

    assert!(
        found,
        "Expected to find symlink path /project/symlink/file.ts"
    );
}

#[test]
fn test_module_specifier_contains_node_modules() {
    let tests = [
        (
            "contains node_modules",
            "/project/node_modules/lodash/index.js",
            true,
        ),
        (
            "does not contain node_modules",
            "/project/src/utils.ts",
            false,
        ),
        (
            "node_modules in middle",
            "/project/packages/node_modules/pkg/file.js",
            true,
        ),
        ("empty path", "", false),
    ];

    for (name, path, expected) in tests {
        let result = module_specifier_contains_node_modules(&tspath::to_module_specifier(path));
        assert_eq!(
            result, expected,
            "moduleSpecifierContainsNodeModules({path:?}) for {name}"
        );
    }
}

#[test]
fn test_is_package_main_file_preserves_directory_intent() {
    let package_root = tspath::rooted_directory_path_from_normalized("/project/node_modules/pkg");

    assert!(
        !is_package_main_file(
            &tspath::rooted_file_path_from_normalized("/project/node_modules/pkg/types.d.ts"),
            &package_root,
            "./types/",
            "",
            CaseSensitivity::CaseSensitive,
        ),
        "slash-terminated package entrypoint must not match the sibling declaration file"
    );
    assert!(
        is_package_main_file(
            &tspath::rooted_file_path_from_normalized("/project/node_modules/pkg/types/index.d.ts"),
            &package_root,
            "./types/",
            "",
            CaseSensitivity::CaseSensitive,
        ),
        "slash-terminated package entrypoint should match its index declaration"
    );
    assert!(
        is_package_main_file(
            &tspath::rooted_file_path_from_normalized("/project/node_modules/pkg/types.d.ts"),
            &package_root,
            "./types",
            "",
            CaseSensitivity::CaseSensitive,
        ),
        "extensionless package entrypoint should match the declaration file"
    );
}

#[test]
fn test_contains_ignored_path() {
    let tests = [
        ("ignored path", "/project/node_modules/.pnpm/file.ts", true),
        ("not ignored path", "/project/src/file.ts", false),
    ];

    for (name, path, expected) in tests {
        let result = contains_ignored_path(&tspath::rooted_file_path_from_normalized(path));
        assert_eq!(
            result, expected,
            "contains_ignored_path({path:?}) for {name}"
        );
    }
}

#[test]
fn test_try_get_real_file_name_for_non_js_declaration_file_name() {
    let tests = [
        (
            "json declaration file",
            "/project/foo.d.json.ts",
            "/project/foo.json",
        ),
        (
            "multi-dot source extension declaration file",
            "/project/foo.module.d.css.ts",
            "/project/foo.module.css",
        ),
        ("plain dts file ignored", "/project/foo.d.ts", ""),
    ];

    for (name, file_name, expected) in tests {
        let got = try_get_real_file_name_for_non_js_declaration_file_name(file_name);
        assert_eq!(
            got, expected,
            "try_get_real_file_name_for_non_js_declaration_file_name({file_name:?}) for {name}"
        );
    }
}

#[test]
fn test_process_ending_checks_rooted_file_path() {
    let host = MockModuleSpecifierGenerationHost {
        current_dir: tspath::rooted_directory_path_from_normalized("/wrong"),
        case_sensitivity: CaseSensitivity::CaseSensitive,
        existing_files: Some(HashMap::from([(
            tspath::rooted_file_path_from_normalized("/project/src/lib.ts"),
            true,
        )])),
        ..Default::default()
    };

    let result = process_ending(
        &tspath::to_module_specifier("./lib/index.ts"),
        &tspath::rooted_file_path_from_normalized("/project/src/lib/index.ts"),
        &[ModuleSpecifierEnding::Minimal],
        &CompilerOptions::default(),
        Some(&host),
    );
    assert_eq!(result.as_string(), "./lib/index", "process_ending()");
    assert!(
        host.file_exists_calls
            .borrow()
            .contains(&tspath::rooted_file_path_from_normalized(
                "/project/src/lib.ts"
            )),
        "FileExists calls = {:?}, expected a lookup for /project/src/lib.ts",
        host.file_exists_calls.borrow(),
    );
}

#[test]
fn test_is_path_relative_to_parent() {
    let tests = [
        ("..", true),
        ("../sibling.ts", true),
        ("..foo.ts", false),
        ("child/..foo.ts", false),
    ];

    for (path, expected) in tests {
        let actual = is_path_relative_to_parent(&tspath::to_relative_path(path));
        assert_eq!(actual, expected, "is_path_relative_to_parent({path:?})");
    }
}

#[test]
fn test_try_get_module_name_from_exports_or_imports() {
    // trailing separator target
    {
        // PORT: `ExportsOrImports`' `object_kind` field is private, so the
        // fixture is decoded from JSON instead of a struct literal.
        let exports: ExportsOrImports = json::unmarshal(b"\"./dist/internal/\"", &[]).unwrap();
        let host = MockModuleSpecifierGenerationHost {
            case_sensitivity: CaseSensitivity::CaseSensitive,
            ..Default::default()
        };
        let result = try_get_module_name_from_exports_or_imports(
            &CompilerOptions::default(),
            &host,
            &tspath::rooted_file_path_from_normalized("/pkg/dist/internal/file.ts"),
            &tspath::rooted_directory_path_from_normalized("/pkg"),
            "#internal/",
            &exports,
            &[],
            MatchingMode::Directory,
            true,
            false,
        );
        assert!(
            !result.is_empty(),
            "directory target with a trailing separator should match"
        );
        let result = try_get_module_name_from_exports_or_imports(
            &CompilerOptions::default(),
            &host,
            &tspath::rooted_file_path_from_normalized("/pkg/dist/internal/file.ts"),
            &tspath::rooted_directory_path_from_normalized("/pkg"),
            "#internal",
            &exports,
            &[],
            MatchingMode::Exact,
            true,
            false,
        );
        assert!(
            result.is_empty(),
            "exact target with a trailing separator matched as {result:?}"
        );
    }

    // with exports pattern
    {
        let tests = [
            (
                "match",
                "/pkg/src/things/thing1/index.ts",
                "./src/things/thing1",
            ),
            (
                "mismatch with matching leading and trailing strings",
                "/pkg/src/things/index.ts",
                "",
            ),
        ];

        for (name, target_file_path, expected) in tests {
            let result = try_get_module_name_from_exports_or_imports(
                &CompilerOptions::default(),
                &MockModuleSpecifierGenerationHost::default(),
                &tspath::rooted_file_path_from_normalized(target_file_path),
                &tspath::rooted_directory_path_from_normalized("/pkg"),
                "./src/things/*",
                &json::unmarshal::<ExportsOrImports>(b"\"./src/things/*/index.js\"", &[]).unwrap(),
                &[],
                MatchingMode::Pattern,
                false,
                false,
            );
            assert_eq!(
                result, expected,
                "try_get_module_name_from_exports_or_imports(target_file_path = {target_file_path:?}) for {name}"
            );
        }
    }
}
