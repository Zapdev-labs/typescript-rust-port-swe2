// Ported from tsc/internal/packagejson/packagejson_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, rooted_directory_path_from_absolute};

use crate::{
    ContentMapperFields, Fields, InfoCache, InfoCacheEntry, PackageDirectory, PackageJson,
    expected_of, for_each_ancestor_directory_stopping_at_global_cache, parse,
};

// PORT: `packageJsonFixtures` and `BenchmarkPackageJSON` are not ported —
// they exercise Go's `testing.B` harness and the parser/vfile packages,
// which have no Rust counterpart in this crate.

/// `func TestPackageDirectory(t *testing.T)`
#[test]
fn test_package_directory() {
    let directory = PackageDirectory::new(
        rooted_directory_path_from_absolute("/package/"),
        CaseSensitivity::CaseSensitive,
    );
    assert_eq!(directory.to_string(), "/package");
    assert_eq!(directory.as_directory_path().as_string(), "/package");
    assert_eq!(directory.path_key().as_string(), "/package");
    assert_eq!(directory.parent().to_string(), "/");
    assert_eq!(directory.parent().path_key().as_string(), "/");
}

/// `func TestPackageDirectoryCacheIdentityPreservesPresentation(t *testing.T)`
#[test]
fn test_package_directory_cache_identity_preserves_presentation() {
    let cache = InfoCache::new(CaseSensitivity::CaseInsensitive);
    let upper = cache.package_directory(RootedDirectoryPath::from("/Repo/Package"));
    let lower = cache.package_directory(RootedDirectoryPath::from("/repo/package"));
    assert_eq!(upper.path_key(), lower.path_key());
    let entry = Arc::new(InfoCacheEntry {
        package_directory: upper.clone(),
        directory_exists: true,
        contents: Some(Arc::new(PackageJson::default())),
    });
    // Go `assert.Equal` compares the returned `*InfoCacheEntry` pointer.
    assert!(Arc::ptr_eq(
        &cache.set(upper.clone(), entry.clone()),
        &entry
    ));
    assert!(Arc::ptr_eq(&cache.get(&lower).unwrap(), &entry));

    let corrected = entry.with_package_directory(lower.clone());
    assert_eq!(
        corrected.package_directory.as_directory_path(),
        lower.as_directory_path()
    );
    assert_eq!(corrected.package_directory.path_key(), upper.path_key());
    assert_eq!(
        entry.package_directory.as_directory_path(),
        upper.as_directory_path()
    );
}

/// `func TestForEachAncestorDirectoryStoppingAtGlobalCache(t *testing.T)`
#[test]
fn test_for_each_ancestor_directory_stopping_at_global_cache() {
    let cache = InfoCache::new(CaseSensitivity::CaseInsensitive);
    let start = cache.package_directory(RootedDirectoryPath::from("/Repo/Project/src"));
    let mut names = Vec::new();
    let mut keys = Vec::new();
    for_each_ancestor_directory_stopping_at_global_cache(
        &RootedDirectoryPath::from("/Repo"),
        start,
        |directory| {
            names.push(directory.to_string());
            keys.push(directory.path_key().as_string().to_string());
            ((), false)
        },
    );
    assert_eq!(names, ["/Repo/Project/src", "/Repo/Project", "/Repo"]);
    assert_eq!(keys, ["/repo/project/src", "/repo/project", "/repo"]);
}

/// `func TestParse(t *testing.T)`
#[test]
fn test_parse() {
    // PORT: Go's `want` literals use embedded-group names
    // (`Fields{HeaderFields: ..., ContentMapper: ...}`); `Fields` flattens
    // them — see the struct's PORT comment in packagejson.rs.
    let tests: [(&str, &str, Fields); 3] = [
        (
            "duplicate names",
            r#"{
                "name": "test-package",
                "name": "test-package",
                "version": "1.0.0"
            }"#,
            Fields {
                name: expected_of("test-package".to_string()),
                version: expected_of("1.0.0".to_string()),
                ..Default::default()
            },
        ),
        (
            "content mapper",
            r#"{
                "name": "test-package",
                "typescript": {
                    "contentMapper": {
                        "exec": ["mapper"],
                        "dynamicConfig": true
                    }
                }
            }"#,
            Fields {
                name: expected_of("test-package".to_string()),
                content_mapper: expected_of(ContentMapperFields {
                    exec: expected_of(vec!["mapper".to_string()]),
                    dynamic_config: expected_of(true),
                    ..Default::default()
                }),
                ..Default::default()
            },
        ),
        (
            "invalid typescript field is ignored",
            r#"{
                "name": "test-package",
                "typescript": "invalid"
            }"#,
            Fields {
                name: expected_of("test-package".to_string()),
                ..Default::default()
            },
        ),
    ];

    for (name, content, want) in tests {
        let got = parse(content.as_bytes()).unwrap();
        assert_eq!(got, want, "case {name}");
    }
}
