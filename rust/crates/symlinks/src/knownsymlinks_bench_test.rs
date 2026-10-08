// Ported from tsc/internal/symlinks/knownsymlinks_bench_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's `testing.B` benchmarks have no stable-Rust harness equivalent
// (`#[bench]` is nightly-only and no benchmark crate is approved). Each
// benchmark is ported as a smoke test that exercises the same code paths a
// bounded number of times instead of `b.Loop()`.

use std::sync::Arc;

use tsc_tspath::{
    CaseSensitivity, RootedDirectoryPath, RootedFilePath, rooted_file_path_from_normalized,
    rooted_path_from_normalized, to_rooted_file_path,
};

use crate::knownsymlinks::{KnownDirectoryLink, KnownSymlinks};

// BenchmarkPopulateSymlinksFromResolutions
#[test]
fn populate_symlinks_from_resolutions_smoke() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);

    let deps: Vec<(RootedFilePath, RootedFilePath)> = (0..50)
        .map(|i| {
            (
                rooted_file_path_from_normalized(&format!("/project/node_modules/pkg{i}/index.js")),
                rooted_file_path_from_normalized(&format!("/real/pkg{i}/index.js")),
            )
        })
        .collect();

    for (orig, resolved) in &deps {
        cache.process_resolution(orig.clone(), resolved.clone());
    }

    assert_eq!(cache.files().size(), deps.len());
}

// BenchmarkSetFile
#[test]
fn set_file_smoke() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);
    let symlink = "/project/file.ts";
    let path = CaseSensitivity::CaseSensitive.path_key(&rooted_path_from_normalized(symlink));

    for _ in 0..10 {
        cache.set_file(
            rooted_file_path_from_normalized(symlink),
            path.clone(),
            RootedFilePath::from("/real/file.ts"),
        );
    }

    assert_eq!(cache.files().size(), 1);
}

// BenchmarkSetDirectory
#[test]
fn set_directory_smoke() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);
    let symlink_path =
        CaseSensitivity::CaseSensitive.path_key(&rooted_path_from_normalized("/project/symlink"));
    let real_dir = KnownDirectoryLink {
        real: RootedDirectoryPath::from("/real/path"),
        real_path: CaseSensitivity::CaseSensitive
            .path_key(&rooted_path_from_normalized("/real/path")),
        ..Default::default()
    };

    for _ in 0..10 {
        cache.set_directory(
            RootedDirectoryPath::from("/project/symlink"),
            symlink_path.clone(),
            Some(real_dir.clone()),
        );
    }

    assert_eq!(cache.directories().size(), 1);
}

// BenchmarkGuessDirectorySymlink
#[test]
fn guess_directory_symlink_smoke() {
    let cache = KnownSymlinks::new(CaseSensitivity::CaseSensitive);
    let current_directory = RootedDirectoryPath::from("/project");

    for _ in 0..10 {
        let (common_resolved, common_original) = cache.guess_directory_symlink_from_file_paths(
            &to_rooted_file_path(
                "/real/node_modules/package/dist/index.js",
                &current_directory,
            ),
            &to_rooted_file_path("/project/symlink/package/dist/index.js", &current_directory),
        );
        assert_eq!(common_resolved.as_string(), "/real/node_modules/package");
        assert_eq!(common_original.as_string(), "/project/symlink/package");
    }
}

// BenchmarkConcurrentAccess
#[test]
fn concurrent_access_smoke() {
    let cache = Arc::new(KnownSymlinks::new(CaseSensitivity::CaseSensitive));

    let mut handles = Vec::new();
    for _ in 0..4 {
        let cache = Arc::clone(&cache);
        handles.push(std::thread::spawn(move || {
            for i in 0..100usize {
                let suffix = char::from(b'A' + (i % 26) as u8);
                let symlink = format!("/project/file{suffix}.ts");
                let path =
                    CaseSensitivity::CaseSensitive.path_key(&rooted_path_from_normalized(&symlink));
                cache.set_file(
                    rooted_file_path_from_normalized(&symlink),
                    path.clone(),
                    RootedFilePath::from("/real/file.ts"),
                );
                let _ = cache.files().load(&path);
            }
        }));
    }
    for handle in handles {
        handle.join().expect("worker thread panicked");
    }

    assert_eq!(cache.files().size(), 26);
}
