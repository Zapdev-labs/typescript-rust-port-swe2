// Ported from tsc/internal/symlinks/knownsymlinks_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `t.Parallel()` is dropped — Rust tests always run in parallel. The
// Go tests' package-private access is preserved via `pub(crate)` items.

use std::sync::Arc;

use tsc_ast::ast_generated::SourceFile;
use tsc_core::compileroptions::{RESOLUTION_MODE_NONE, ResolutionMode};
use tsc_module::{ResolvedModule, ResolvedTypeReferenceDirective};
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath,
    rooted_directory_path_from_absolute, rooted_directory_path_from_normalized,
    rooted_file_path_from_absolute, rooted_path_from_normalized, to_rooted_file_path,
};

use crate::knownsymlinks::{KnownDirectoryLink, KnownSymlinks};

#[test]
fn test_new_known_symlink() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);
    assert_eq!(
        cache.case_sensitivity,
        CaseSensitivity::CaseSensitive,
        "expected CaseSensitivity to be CaseSensitive"
    );
}

#[test]
fn test_set_directory() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);
    let symlink_path =
        CaseSensitivity::CaseSensitive.path_key(&rooted_path_from_normalized("/test/symlink"));
    let real_directory = KnownDirectoryLink {
        real: RootedDirectoryPath::from("/real/path"),
        real_path: CaseSensitivity::CaseSensitive
            .path_key(&rooted_path_from_normalized("/real/path")),
        ..Default::default()
    };

    cache.set_directory(
        RootedDirectoryPath::from("/test/symlink"),
        symlink_path.clone(),
        Some(real_directory.clone()),
    );

    // Check that directory was stored
    let Some(Some(stored)) = cache.directories().load(&symlink_path) else {
        panic!("Expected directory to be stored")
    };
    assert_eq!(
        stored.real,
        real_directory.real,
        "Expected Real to be '{}', got '{}'",
        real_directory.real.as_string(),
        stored.real.as_string()
    );
    assert_eq!(
        stored.real_path,
        real_directory.real_path,
        "Expected RealPath to be '{}', got '{}'",
        real_directory.real_path.as_string(),
        stored.real_path.as_string()
    );
    assert_eq!(
        stored.symlink,
        RootedDirectoryPath::from("/test/symlink"),
        "Expected Symlink to preserve '/test/symlink', got '{}'",
        stored.symlink.as_string()
    );

    // Check that realpath mapping was created
    let Some(set) = cache
        .directories_by_realpath()
        .load(&real_directory.real_path)
    else {
        panic!("Expected realpath mapping to be created")
    };
    assert!(!set.is_empty(), "Expected realpath mapping to be created");
    assert!(
        set.has(&RootedDirectoryPath::from("/test/symlink")),
        "Expected symlink '/test/symlink' to be in set"
    );
}

#[test]
fn test_known_directory_link_preserves_child_spelling() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseInsensitive);
    let symlink = RootedDirectoryPath::from("/Project/Node_Modules/pkg");
    let symlink_path = CaseSensitivity::CaseInsensitive.path_key(&symlink.as_path());
    cache.set_directory(
        symlink,
        symlink_path.clone(),
        Some(KnownDirectoryLink {
            real: RootedDirectoryPath::from("/Real/Package"),
            real_path: PathKey::from("/real/package"),
            ..Default::default()
        }),
    );

    let Some(Some(link)) = cache.directories().load(&symlink_path) else {
        panic!("Expected directory link")
    };
    let Some(resolved) = link.resolve_file_path(
        &RootedFilePath::from("/PROJECT/node_modules/pkg/Src/File.ts"),
        CaseSensitivity::CaseInsensitive,
    ) else {
        panic!("Expected child path to resolve through directory link")
    };
    assert_eq!(
        resolved.as_string(),
        "/Real/Package/Src/File.ts",
        "Expected child spelling to be preserved, got '{}'",
        resolved.as_string()
    );
}

#[test]
fn test_set_file() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);
    let symlink = RootedFilePath::from("/test/symlink/file.ts");
    let symlink_path = CaseSensitivity::CaseSensitive.path_key(&symlink.as_path());
    let realpath = RootedFilePath::from("/real/path/file.ts");

    cache.set_file(symlink, symlink_path.clone(), realpath.clone());

    let Some(stored) = cache.files().load(&symlink_path) else {
        panic!("Expected file to be stored")
    };
    assert_eq!(
        stored,
        realpath,
        "Expected realpath to be '{}', got '{}'",
        realpath.as_string(),
        stored.as_string()
    );
}

#[test]
fn test_process_resolution() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);

    // Test with empty paths
    cache.process_resolution(RootedFilePath::default(), RootedFilePath::default());
    cache.process_resolution(RootedFilePath::from("/original"), RootedFilePath::default());
    cache.process_resolution(RootedFilePath::default(), RootedFilePath::from("/resolved"));

    // Test with valid paths
    let original_path = RootedFilePath::from("/test/original/file.ts");
    let resolved_path = RootedFilePath::from("/test/resolved/file.ts");
    cache.process_resolution(original_path.clone(), resolved_path.clone());

    // Check that file was stored
    let symlink_path = CaseSensitivity::CaseSensitive.path_key(&original_path.as_path());
    let Some(stored) = cache.files().load(&symlink_path) else {
        panic!("Expected file to be stored")
    };
    assert_eq!(
        stored,
        resolved_path,
        "Expected resolved path to be '{}', got '{}'",
        resolved_path.as_string(),
        stored.as_string()
    );
}

#[test]
fn test_guess_directory_symlink() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);

    // (name, a, b, cwd, expected [common_resolved, common_original])
    let tests: &[(&str, &str, &str, &str, [&str; 2])] = &[
        (
            "identical paths",
            "/test/path/file.ts",
            "/test/path/file.ts",
            "/test/dir",
            ["/", "/"],
        ),
        (
            "different files same directory",
            "/test/path/file1.ts",
            "/test/path/file2.ts",
            "/test/dir",
            ["", ""],
        ),
        (
            "different directories",
            "/test/path1/file.ts",
            "/test/path2/file.ts",
            "/test/dir",
            ["/test/path1", "/test/path2"],
        ),
        (
            "node_modules paths",
            "/test/node_modules/pkg/file.ts",
            "/test/node_modules/pkg/file.ts",
            "/test/dir",
            ["/test/node_modules/pkg", "/test/node_modules/pkg"],
        ),
        (
            "scoped package paths",
            "/test/node_modules/@scope/pkg/file.ts",
            "/test/node_modules/@scope/pkg/file.ts",
            "/test/dir",
            [
                "/test/node_modules/@scope/pkg",
                "/test/node_modules/@scope/pkg",
            ],
        ),
    ];

    for (name, a, b, cwd, expected) in tests {
        let current_directory = rooted_directory_path_from_normalized(cwd);
        let (common_resolved, common_original) = cache.guess_directory_symlink_from_file_paths(
            &to_rooted_file_path(a, &current_directory),
            &to_rooted_file_path(b, &current_directory),
        );
        assert_eq!(
            common_resolved.as_string(),
            expected[0],
            "{name}: Expected commonResolved to be '{}', got '{}'",
            expected[0],
            common_resolved.as_string()
        );
        assert_eq!(
            common_original.as_string(),
            expected[1],
            "{name}: Expected commonOriginal to be '{}', got '{}'",
            expected[1],
            common_original.as_string()
        );
    }
}

#[test]
fn test_is_node_modules_or_scoped_package_directory() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);

    let tests: &[(&str, &str, bool)] = &[
        ("node_modules", "node_modules", true),
        ("scoped package", "@scope", true),
        ("regular directory", "src", false),
        ("empty string", "", false),
        // The function is case sensitive (the cache is CaseSensitive)
        ("case insensitive node_modules", "NODE_MODULES", false),
        ("case insensitive scoped", "@SCOPE", true),
    ];

    for (name, dir, expected) in tests {
        let result = cache.is_node_modules_or_scoped_package_directory(dir);
        assert_eq!(
            result, *expected,
            "{name}: Expected {expected}, got {result} for directory '{dir}'"
        );
    }
}

#[test]
fn test_set_symlinks_from_resolutions() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);

    // Mock resolution data
    let resolved_modules: &[(&str, &str, &str, ResolutionMode, PathKey)] = &[
        (
            "/test/original/file1.ts",
            "/test/resolved/file1.ts",
            "module1",
            RESOLUTION_MODE_NONE,
            CaseSensitivity::CaseSensitive
                .path_key(&rooted_path_from_normalized("/test/source.ts")),
        ),
        (
            "/test/original/file2.ts",
            "/test/resolved/file2.ts",
            "module2",
            RESOLUTION_MODE_NONE,
            CaseSensitivity::CaseSensitive
                .path_key(&rooted_path_from_normalized("/test/source.ts")),
        ),
    ];

    // Mock callbacks
    let for_each_resolved_module =
        |callback: &mut dyn FnMut(&ResolvedModule, &str, ResolutionMode, &PathKey),
         _file: Option<&SourceFile>| {
            for (original_path, resolved_path, module_name, mode, file_path) in resolved_modules {
                let resolution = ResolvedModule {
                    original_path: rooted_file_path_from_absolute(original_path),
                    resolved_file_name: rooted_file_path_from_absolute(resolved_path),
                    ..Default::default()
                };
                callback(&resolution, module_name, *mode, file_path);
            }
        };

    // No type reference directives for this test
    let for_each_resolved_type_reference_directive =
        |_callback: &mut dyn FnMut(
            &ResolvedTypeReferenceDirective,
            &str,
            ResolutionMode,
            &PathKey,
        ),
         _file: Option<&SourceFile>| {};

    cache.set_symlinks_from_resolutions(
        for_each_resolved_module,
        for_each_resolved_type_reference_directive,
    );

    // Check that files were stored
    for (original_path, resolved_path, _module_name, _mode, _file_path) in resolved_modules {
        let symlink_path =
            CaseSensitivity::CaseSensitive.path_key(&rooted_path_from_normalized(original_path));
        let Some(stored) = cache.files().load(&symlink_path) else {
            panic!("Expected file '{original_path}' to be stored")
        };
        assert_eq!(
            stored.as_string(),
            *resolved_path,
            "Expected resolved path to be '{resolved_path}', got '{}'",
            stored.as_string()
        );
    }
}

#[test]
fn test_known_symlinks_thread_safety() {
    let cache = Arc::new(KnownSymlinks::new(CaseSensitivity::CaseSensitive));

    // Test concurrent access
    let mut handles = Vec::with_capacity(10);
    for id in 0..10u8 {
        let cache = Arc::clone(&cache);
        handles.push(std::thread::spawn(move || {
            // PORT: Go's `string(rune(id))` yields the control characters
            // "\x00".."\x09" for ids 0..10; `char::from` reproduces that.
            let suffix = char::from(id).to_string();
            let symlink_path = CaseSensitivity::CaseSensitive.path_key(
                &rooted_path_from_normalized(&format!("/test/symlink{suffix}")),
            );
            let real_directory = KnownDirectoryLink {
                real: rooted_directory_path_from_absolute(&format!("/real/path{suffix}")),
                real_path: CaseSensitivity::CaseSensitive
                    .path_key(&rooted_path_from_normalized(&format!("/real/path{suffix}"))),
                ..Default::default()
            };

            cache.set_directory(
                rooted_directory_path_from_normalized(&format!("/test/symlink{suffix}")),
                symlink_path.clone(),
                Some(real_directory.clone()),
            );

            // Read back
            let Some(Some(stored)) = cache.directories().load(&symlink_path) else {
                panic!("Thread {id}: Expected directory to be stored")
            };
            assert_eq!(
                stored.real,
                real_directory.real,
                "Thread {id}: Expected Real to be '{}', got '{}'",
                real_directory.real.as_string(),
                stored.real.as_string()
            );
        }));
    }

    // Wait for all threads to complete
    for handle in handles {
        handle.join().expect("worker thread panicked");
    }

    // Verify all directories were stored
    assert_eq!(
        cache.directories().size(),
        10,
        "Expected 10 directories to be stored, got {}",
        cache.directories().size()
    );
}
