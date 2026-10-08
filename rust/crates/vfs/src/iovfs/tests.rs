// Ported from tsc/internal/vfs/iovfs/iofs_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use super::*;
use crate::vfstest::fstest::{MapFile, MapFs};

fn map_fs() -> MapFs {
    MapFs::from_iter([
        ("foo.ts", MapFile::new(b"hello, world".to_vec())),
        (
            "dir1/file1.ts",
            MapFile::new(b"export const foo = 42;".to_vec()),
        ),
        (
            "dir1/file2.ts",
            MapFile::new(b"export const foo = 42;".to_vec()),
        ),
        (
            "dir2/file1.ts",
            MapFile::new(b"export const foo = 42;".to_vec()),
        ),
    ])
}

#[test]
fn test_read_file() {
    let fs = from(Arc::new(map_fs()), CaseSensitivity::CaseSensitive);

    let content = fs.read_file(&RootedFilePath::from("/foo.ts"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    assert!(
        fs.read_file(&RootedFilePath::from("/does/not/exist.ts"))
            .is_none()
    );
}

#[test]
fn test_file_exists() {
    let fs = from(Arc::new(map_fs()), CaseSensitivity::CaseSensitive);

    assert!(fs.file_exists(&RootedFilePath::from("/foo.ts")));
    assert!(!fs.file_exists(&RootedFilePath::from("/bar")));
}

#[test]
fn test_directory_exists() {
    let fs = from(Arc::new(map_fs()), CaseSensitivity::CaseSensitive);

    assert!(fs.directory_exists(&RootedDirectoryPath::from("/")));
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/dir1")));
    assert!(fs.directory_exists(&tsc_tspath::rooted_directory_path_from_absolute("/dir1/")));
    assert!(fs.directory_exists(&tsc_tspath::rooted_directory_path_from_absolute("/dir1/./")));
    assert!(!fs.directory_exists(&RootedDirectoryPath::from("/bar")));
}

#[test]
fn test_get_accessible_entries() {
    let fs = from(Arc::new(map_fs()), CaseSensitivity::CaseSensitive);

    let entries = fs.get_accessible_entries(&RootedDirectoryPath::from("/"));
    assert_eq!(entries.directories, ["dir1", "dir2"]);
    assert_eq!(entries.files, ["foo.ts"]);
}

#[test]
fn test_realpath() {
    let fs = from(Arc::new(map_fs()), CaseSensitivity::CaseSensitive);

    let realpath = fs.realpath(&RootedPath::from("/foo.ts"));
    assert_eq!(realpath.as_string(), "/foo.ts");
}

#[test]
fn test_case_sensitivity() {
    let fs = from(Arc::new(map_fs()), CaseSensitivity::CaseSensitive);

    assert!(fs.case_sensitivity().is_case_sensitive());
}
