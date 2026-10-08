// Ported from tsc/internal/vfs/vfstest/vfstest_test.go
// @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;
use std::time::SystemTime;

use rustc_hash::FxHashMap;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use super::fstest::{self, MapFile};
use super::{convert_map_fs, from_map, symlink};
use crate::fs::{self, Fs};
use crate::iovfs::RealpathFs;
use crate::vfs::Vfs;

fn map_file(data: &[u8], sys: Option<Arc<dyn std::any::Any + Send + Sync>>) -> MapFile {
    MapFile {
        data: Arc::from(data),
        mode: crate::fs::FileMode(0),
        mod_time: SystemTime::UNIX_EPOCH,
        sys,
    }
}

fn dir_entries_to_names(entries: Vec<Arc<dyn fs::DirEntry>>) -> Vec<String> {
    entries.iter().map(|e| e.name()).collect()
}

/// testutil.AssertPanics: runs f, requires a panic, and asserts the panic
/// message matches exactly.
fn assert_panics(f: impl FnOnce() + std::panic::UnwindSafe, expected: &str) {
    let result = catch_unwind(f);
    match result {
        Ok(()) => panic!("expected panic {expected:?}, but nothing panicked"),
        Err(payload) => {
            let msg = payload
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| payload.downcast_ref::<&str>().copied())
                .unwrap_or("<non-string panic>");
            assert_eq!(msg, expected);
        }
    }
}

fn three_file_map(case: &str) -> FxHashMap<String, MapFile> {
    let contents = b"bar";
    FxHashMap::from_iter([
        (
            format!("{case}/bar/baz"),
            map_file(contents, Some(Arc::new(1234i32))),
        ),
        (
            format!("{case}/bar2/baz2"),
            map_file(contents, Some(Arc::new(1234i32))),
        ),
        (
            format!("{case}/bar3/baz3"),
            map_file(contents, Some(Arc::new(1234i32))),
        ),
    ])
}

fn clock() -> Arc<dyn super::Clock> {
    Arc::new(super::ClockImpl {
        start: SystemTime::now(),
    })
}

#[test]
fn test_insensitive() {
    let contents: &[u8] = b"bar";

    let vfs = Arc::new(convert_map_fs(
        three_file_map("foo"),
        CaseSensitivity::CaseInsensitive,
        clock(),
    ));

    let sensitive = fs::read_file(&*vfs, "foo/bar/baz").unwrap();
    assert_eq!(&sensitive[..], contents);
    let sensitive_info = fs::stat(&*vfs, "foo/bar/baz").unwrap();
    assert_eq!(
        *sensitive_info.sys().unwrap().downcast_ref::<i32>().unwrap(),
        1234
    );
    let sensitive_realpath = vfs.realpath("foo/bar/baz").unwrap();
    assert_eq!(sensitive_realpath, "foo/bar/baz");
    let entries = fs::read_dir(&*vfs, "foo").unwrap();
    assert_eq!(dir_entries_to_names(entries), ["bar", "bar2", "bar3"]);

    let err = vfs.realpath("does/not/exist").unwrap_err();
    assert!(err.to_string().contains("file does not exist"), "got {err}");
    let err = fs::stat(&*vfs, "does/not/exist").unwrap_err();
    assert!(err.to_string().contains("file does not exist"), "got {err}");

    let vfs_fs: Arc<dyn Fs> = vfs.clone();
    fstest::test_fs(&vfs_fs, &["foo/bar/baz"]).unwrap();

    let insensitive = fs::read_file(&*vfs, "Foo/Bar/Baz").unwrap();
    assert_eq!(&insensitive[..], contents);
    let insensitive_info = fs::stat(&*vfs, "Foo/Bar/Baz").unwrap();
    assert_eq!(
        *insensitive_info
            .sys()
            .unwrap()
            .downcast_ref::<i32>()
            .unwrap(),
        1234
    );
    let insensitive_realpath = vfs.realpath("Foo/Bar/Baz").unwrap();
    assert_eq!(insensitive_realpath, "foo/bar/baz");
    let entries = fs::read_dir(&*vfs, "Foo").unwrap();
    assert_eq!(dir_entries_to_names(entries), ["bar", "bar2", "bar3"]);

    let err = vfs.realpath("Does/Not/Exist").unwrap_err();
    assert!(err.to_string().contains("file does not exist"), "got {err}");
    let err = fs::stat(&*vfs, "Does/Not/Exist").unwrap_err();
    assert!(err.to_string().contains("file does not exist"), "got {err}");

    // PORT: TestFS doesn't understand case-insensitive file systems (same as Go).
}

#[test]
fn test_insensitive_upper() {
    let contents: &[u8] = b"bar";

    let vfs = Arc::new(convert_map_fs(
        FxHashMap::from_iter([
            (
                "Foo/Bar/Baz".to_string(),
                map_file(b"bar", Some(Arc::new(1234i32))),
            ),
            (
                "Foo/Bar2/Baz2".to_string(),
                map_file(b"bar", Some(Arc::new(1234i32))),
            ),
            (
                "Foo/Bar3/Baz3".to_string(),
                map_file(b"bar", Some(Arc::new(1234i32))),
            ),
        ]),
        CaseSensitivity::CaseInsensitive,
        clock(),
    ));

    let sensitive = fs::read_file(&*vfs, "foo/bar/baz").unwrap();
    assert_eq!(&sensitive[..], contents);
    let sensitive_info = fs::stat(&*vfs, "foo/bar/baz").unwrap();
    assert_eq!(
        *sensitive_info.sys().unwrap().downcast_ref::<i32>().unwrap(),
        1234
    );
    let entries = fs::read_dir(&*vfs, "foo").unwrap();
    assert_eq!(dir_entries_to_names(entries), ["Bar", "Bar2", "Bar3"]);

    // fstest::test_fs(&vfs, &["foo/bar/baz"]) — skipped as in Go.

    let insensitive = fs::read_file(&*vfs, "Foo/Bar/Baz").unwrap();
    assert_eq!(&insensitive[..], contents);
    let insensitive_info = fs::stat(&*vfs, "Foo/Bar/Baz").unwrap();
    assert_eq!(
        *insensitive_info
            .sys()
            .unwrap()
            .downcast_ref::<i32>()
            .unwrap(),
        1234
    );
    let entries = fs::read_dir(&*vfs, "Foo").unwrap();
    assert_eq!(dir_entries_to_names(entries), ["Bar", "Bar2", "Bar3"]);

    let vfs_fs: Arc<dyn Fs> = vfs.clone();
    fstest::test_fs(&vfs_fs, &["Foo/Bar/Baz"]).unwrap();
}

#[test]
fn test_sensitive() {
    let contents: &[u8] = b"bar";

    let vfs = Arc::new(convert_map_fs(
        three_file_map("foo"),
        CaseSensitivity::CaseSensitive,
        clock(),
    ));

    let sensitive = fs::read_file(&*vfs, "foo/bar/baz").unwrap();
    assert_eq!(&sensitive[..], contents);
    let sensitive_info = fs::stat(&*vfs, "foo/bar/baz").unwrap();
    assert_eq!(
        *sensitive_info.sys().unwrap().downcast_ref::<i32>().unwrap(),
        1234
    );

    let vfs_fs: Arc<dyn Fs> = vfs.clone();
    fstest::test_fs(&vfs_fs, &["foo/bar/baz"]).unwrap();

    let err = fs::read_file(&*vfs, "Foo/Bar/Baz").unwrap_err();
    assert!(err.to_string().contains("file does not exist"), "got {err}");
}

#[test]
fn test_sensitive_duplicate_path() {
    let testfs: FxHashMap<String, MapFile> = FxHashMap::from_iter([
        ("foo".to_string(), map_file(b"bar", None)),
        ("Foo".to_string(), map_file(b"baz", None)),
    ]);

    assert_panics(
        AssertUnwindSafe(move || {
            convert_map_fs(testfs, CaseSensitivity::CaseInsensitive, clock());
        }),
        "duplicate path: \"Foo\" and \"foo\" have the same canonical path",
    );
}

#[test]
fn test_insensitive_duplicate_path() {
    let testfs: FxHashMap<String, MapFile> = FxHashMap::from_iter([
        ("foo".to_string(), map_file(b"bar", None)),
        ("Foo".to_string(), map_file(b"baz", None)),
    ]);

    convert_map_fs(testfs, CaseSensitivity::CaseSensitive, clock());
}

#[test]
fn test_writable_fs() {
    let fs: Arc<dyn Vfs> = from_map(
        std::iter::empty::<(&str, &str)>(),
        CaseSensitivity::CaseInsensitive,
    );

    fs.write_file(&RootedFilePath::from("/foo/bar/baz"), "hello, world")
        .unwrap();

    let content = fs.read_file(&RootedFilePath::from("/foo/bar/baz"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    fs.write_file(&RootedFilePath::from("/foo/bar/baz"), "goodbye, world")
        .unwrap();

    let content = fs.read_file(&RootedFilePath::from("/foo/bar/baz"));
    assert_eq!(content.as_deref(), Some("goodbye, world"));

    let err = fs
        .write_file(&RootedFilePath::from("/foo/bar/baz/oops"), "goodbye, world")
        .unwrap_err();
    assert!(
        err.to_string()
            .contains("mkdir \"foo/bar/baz\": path exists but is not a directory"),
        "got {err}"
    );
}

#[test]
fn test_writable_fs_delete() {
    let fs: Arc<dyn Vfs> = from_map(
        std::iter::empty::<(&str, &str)>(),
        CaseSensitivity::CaseInsensitive,
    );

    let _ = fs.write_file(&RootedFilePath::from("/foo/bar/file.ts"), "remove");
    assert!(fs.file_exists(&RootedFilePath::from("/foo/bar/file.ts")));
    fs.remove(&RootedPath::from("/foo/bar/file.ts")).unwrap();
    assert!(!fs.file_exists(&RootedFilePath::from("/foo/bar/file.ts")));

    let _ = fs.write_file(&RootedFilePath::from("/foo/bar/test/remove2.ts"), "remove2");
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/foo/bar/test")));
    fs.remove(&RootedPath::from("/foo/bar/test")).unwrap();
    assert!(!fs.file_exists(&RootedFilePath::from("/foo/bar/test/remove2.ts")));
    assert!(!fs.directory_exists(&RootedDirectoryPath::from("/foo/bar/test")));

    // no errors when removing file/dir that does not exist
    fs.remove(&RootedPath::from("/foo/bar/test")).unwrap();
    fs.remove(&RootedPath::from("/foo/bar/file.ts")).unwrap();

    let _ = fs.write_file(&RootedFilePath::from("/foo/barbar"), "remove2");
    let _ = fs.remove(&RootedPath::from("/foo/bar"));
    assert!(fs.file_exists(&RootedFilePath::from("/foo/barbar")));
}

#[test]
fn test_stress() {
    use std::sync::atomic::{AtomicU64, Ordering};

    let fs: Arc<dyn Vfs> = from_map(
        std::iter::empty::<(&str, &str)>(),
        CaseSensitivity::CaseInsensitive,
    );

    // PORT: math/rand/v2.Shuffle replaced by a deterministic per-thread
    // rotation; the stress property being tested is concurrent access, not
    // the shuffle quality.
    static SEED: AtomicU64 = AtomicU64::new(0);

    let threads = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4);

    let mut handles = Vec::new();
    for _ in 0..threads {
        let fs = fs.clone();
        handles.push(std::thread::spawn(move || {
            let rot = SEED.fetch_add(1, Ordering::Relaxed) as usize;
            for i in 0..10_000usize {
                match (i + rot) % 8 {
                    0 => {
                        let _ = fs
                            .write_file(&RootedFilePath::from("/foo/bar/baz.txt"), "hello, world");
                    }
                    1 => {
                        let _ = fs.read_file(&RootedFilePath::from("/foo/bar/baz.txt"));
                    }
                    2 => {
                        let _ = fs.directory_exists(&RootedDirectoryPath::from("/foo/bar"));
                    }
                    3 => {
                        let _ = fs.file_exists(&RootedFilePath::from("/foo/bar"));
                    }
                    4 => {
                        let _ = fs.file_exists(&RootedFilePath::from("/foo/bar/baz.txt"));
                    }
                    5 => {
                        let _ = fs.get_accessible_entries(&RootedDirectoryPath::from("/foo/bar"));
                    }
                    6 => {
                        let _ = fs.realpath(&RootedPath::from("/foo/bar/baz.txt"));
                    }
                    _ => {
                        let _ = fs.stat(&RootedPath::from("/foo/bar/baz.txt"));
                    }
                }
            }
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
}

#[test]
fn test_parent_dir_file() {
    let testfs: FxHashMap<String, MapFile> = FxHashMap::from_iter([
        ("foo".to_string(), map_file(b"bar", None)),
        ("foo/oops".to_string(), map_file(b"baz", None)),
    ]);

    assert_panics(
        AssertUnwindSafe(move || {
            convert_map_fs(testfs, CaseSensitivity::CaseInsensitive, clock());
        }),
        "failed to create intermediate directories for \"foo/oops\": mkdir \"foo\": path exists but is not a directory",
    );
}

#[test]
fn test_from_map_posix() {
    let fs = from_map(
        vec![
            ("/string", super::TestFile::from("hello, world")),
            ("/bytes", super::TestFile::from(b"hello, world".to_vec())),
            (
                "/mapfile",
                super::TestFile::from(map_file(b"hello, world", None)),
            ),
        ],
        CaseSensitivity::CaseInsensitive,
    );

    let content = fs.read_file(&RootedFilePath::from("/string"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    let content = fs.read_file(&RootedFilePath::from("/bytes"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    let content = fs.read_file(&RootedFilePath::from("/mapfile"));
    assert_eq!(content.as_deref(), Some("hello, world"));
}

#[test]
fn test_from_map_windows() {
    let fs = from_map(
        vec![
            ("c:/string", super::TestFile::from("hello, world")),
            ("d:/bytes", super::TestFile::from(b"hello, world".to_vec())),
            (
                "e:/mapfile",
                super::TestFile::from(map_file(b"hello, world", None)),
            ),
        ],
        CaseSensitivity::CaseInsensitive,
    );

    let content = fs.read_file(&RootedFilePath::from("c:/string"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    let content = fs.read_file(&RootedFilePath::from("d:/bytes"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    let content = fs.read_file(&RootedFilePath::from("e:/mapfile"));
    assert_eq!(content.as_deref(), Some("hello, world"));
}

#[test]
fn test_from_map_mixed() {
    assert_panics(
        AssertUnwindSafe(|| {
            from_map(
                vec![
                    ("/string", super::TestFile::from("hello, world")),
                    ("c:/bytes", super::TestFile::from(b"hello, world".to_vec())),
                ],
                CaseSensitivity::CaseInsensitive,
            );
        }),
        "mixed posix and windows paths",
    );
}

#[test]
fn test_from_map_non_rooted() {
    assert_panics(
        AssertUnwindSafe(|| {
            from_map(
                vec![("string", super::TestFile::from("hello, world"))],
                CaseSensitivity::CaseInsensitive,
            );
        }),
        "non-rooted path \"string\"",
    );
}

#[test]
fn test_from_map_non_normalized() {
    assert_panics(
        AssertUnwindSafe(|| {
            from_map(
                vec![("/string/", super::TestFile::from("hello, world"))],
                CaseSensitivity::CaseInsensitive,
            );
        }),
        "non-normalized path \"/string/\"",
    );
}

#[test]
fn test_from_map_non_normalized2() {
    assert_panics(
        AssertUnwindSafe(|| {
            from_map(
                vec![("/string/../foo", super::TestFile::from("hello, world"))],
                CaseSensitivity::CaseInsensitive,
            );
        }),
        "non-normalized path \"/string/../foo\"",
    );
}

// PORT: Go's "invalid file type int" panic is unrepresentable — the Rust API
// is statically typed through TestFile.

#[test]
fn test_vfs_test_map_fs() {
    let fs = from_map(
        [
            ("/foo.ts", "hello, world"),
            ("/dir1/file1.ts", "export const foo = 42;"),
            ("/dir1/file2.ts", "export const foo = 42;"),
            ("/dir2/file1.ts", "export const foo = 42;"),
        ],
        CaseSensitivity::CaseInsensitive,
    );

    let content = fs.read_file(&RootedFilePath::from("/foo.ts"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    assert!(
        fs.read_file(&RootedFilePath::from("/does/not/exist.ts"))
            .is_none()
    );

    let realpath = fs.realpath(&RootedPath::from("/foo.ts"));
    assert_eq!(realpath.as_string(), "/foo.ts");

    let realpath = fs.realpath(&RootedPath::from("/Foo.ts"));
    assert_eq!(realpath.as_string(), "/foo.ts");

    let realpath = fs.realpath(&RootedPath::from("/does/not/exist.ts"));
    assert_eq!(realpath.as_string(), "/does/not/exist.ts");

    assert!(fs.case_sensitivity().is_case_insensitive());
}

#[test]
fn test_vfs_test_map_fs_windows() {
    let fs = from_map(
        [
            ("c:/foo.ts", "hello, world"),
            ("c:/dir1/file1.ts", "export const foo = 42;"),
            ("c:/dir1/file2.ts", "export const foo = 42;"),
            ("c:/dir2/file1.ts", "export const foo = 42;"),
        ],
        CaseSensitivity::CaseInsensitive,
    );

    let content = fs.read_file(&RootedFilePath::from("c:/foo.ts"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    assert!(
        fs.read_file(&RootedFilePath::from("c:/does/not/exist.ts"))
            .is_none()
    );

    let realpath = fs.realpath(&RootedPath::from("c:/foo.ts"));
    assert_eq!(realpath.as_string(), "c:/foo.ts");

    let realpath = fs.realpath(&RootedPath::from("c:/Foo.ts"));
    assert_eq!(realpath.as_string(), "c:/foo.ts");

    let realpath = fs.realpath(&RootedPath::from("c:/does/not/exist.ts"));
    assert_eq!(realpath.as_string(), "c:/does/not/exist.ts");
}

#[test]
fn test_bom() {
    let expected = "hello, world";

    for little_endian in [false, true] {
        let (bom, order_name) = if little_endian {
            ([0xFF, 0xFE], "LittleEndian")
        } else {
            ([0xFE, 0xFF], "BigEndian")
        };
        let _ = order_name;

        let mut buf = bom.to_vec();
        for unit in expected.encode_utf16() {
            buf.extend_from_slice(&if little_endian {
                unit.to_le_bytes()
            } else {
                unit.to_be_bytes()
            });
        }

        let fs = from_map(
            vec![("/foo.ts", super::TestFile::from(buf))],
            CaseSensitivity::CaseSensitive,
        );

        let content = fs.read_file(&RootedFilePath::from("/foo.ts"));
        assert_eq!(content.as_deref(), Some(expected));
    }

    // UTF8
    let fs = from_map(
        vec![(
            "/foo.ts",
            super::TestFile::from(b"\xEF\xBB\xBFhello, world".to_vec()),
        )],
        CaseSensitivity::CaseSensitive,
    );

    let content = fs.read_file(&RootedFilePath::from("/foo.ts"));
    assert_eq!(content.as_deref(), Some(expected));
}

fn symlink_host() -> Arc<dyn Vfs> {
    from_map(
        vec![
            ("/foo.ts", super::TestFile::from("hello, world")),
            ("/symlink.ts", super::TestFile::from(symlink("/foo.ts"))),
            ("/some/dir/file.ts", super::TestFile::from("hello, world")),
            ("/some/dirlink", super::TestFile::from(symlink("/some/dir"))),
            ("/a", super::TestFile::from(symlink("/b"))),
            ("/b", super::TestFile::from(symlink("/c"))),
            ("/c", super::TestFile::from(symlink("/d"))),
            (
                "/d/existing.ts",
                super::TestFile::from("this is existing.ts"),
            ),
        ],
        CaseSensitivity::CaseInsensitive,
    )
}

#[test]
fn test_symlink() {
    let fs = symlink_host();

    // ReadFile
    let content = fs.read_file(&RootedFilePath::from("/symlink.ts"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    let content = fs.read_file(&RootedFilePath::from("/some/dirlink/file.ts"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    let content = fs.read_file(&RootedFilePath::from("/a/existing.ts"));
    assert_eq!(content.as_deref(), Some("this is existing.ts"));

    // Realpath
    let realpath = fs.realpath(&RootedPath::from("/symlink.ts"));
    assert_eq!(realpath.as_string(), "/foo.ts");

    let realpath = fs.realpath(&RootedPath::from("/some/dirlink"));
    assert_eq!(realpath.as_string(), "/some/dir");

    let realpath = fs.realpath(&RootedPath::from("/some/dirlink/file.ts"));
    assert_eq!(realpath.as_string(), "/some/dir/file.ts");

    // FileExists
    assert!(fs.file_exists(&RootedFilePath::from("/symlink.ts")));
    assert!(fs.file_exists(&RootedFilePath::from("/some/dirlink/file.ts")));
    assert!(fs.file_exists(&RootedFilePath::from("/a/existing.ts")));

    // DirectoryExists
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/some/dirlink")));
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/d")));
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/c")));
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/b")));
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/a")));
}

fn writable_symlink_host() -> Arc<dyn Vfs> {
    from_map(
        vec![
            ("/some/dir/other.ts", super::TestFile::from("NOTHING")),
            (
                "/other.ts",
                super::TestFile::from(symlink("/some/dir/other.ts")),
            ),
            ("/some/dirlink", super::TestFile::from(symlink("/some/dir"))),
            (
                "/brokenlink",
                super::TestFile::from(symlink("/does/not/exist")),
            ),
            ("/a", super::TestFile::from(symlink("/b"))),
            ("/b", super::TestFile::from(symlink("/c"))),
            ("/c", super::TestFile::from(symlink("/d"))),
            ("/d/existing.ts", super::TestFile::from("hello, world")),
        ],
        CaseSensitivity::CaseInsensitive,
    )
}

#[test]
fn test_writable_fs_symlink() {
    let fs = writable_symlink_host();

    fs.write_file(
        &RootedFilePath::from("/some/dirlink/file.ts"),
        "hello, world",
    )
    .unwrap();

    let content = fs.read_file(&RootedFilePath::from("/some/dirlink/file.ts"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    let content = fs.read_file(&RootedFilePath::from("/some/dir/file.ts"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    fs.write_file(
        &RootedFilePath::from("/some/dirlink/file.ts"),
        "goodbye, world",
    )
    .unwrap();

    let content = fs.read_file(&RootedFilePath::from("/some/dirlink/file.ts"));
    assert_eq!(content.as_deref(), Some("goodbye, world"));

    fs.write_file(&RootedFilePath::from("/other.ts"), "hello, world")
        .unwrap();

    let content = fs.read_file(&RootedFilePath::from("/other.ts"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    let content = fs.read_file(&RootedFilePath::from("/some/dir/other.ts"));
    assert_eq!(content.as_deref(), Some("hello, world"));

    let err = fs
        .write_file(&RootedFilePath::from("/some/dirlink"), "hello, world")
        .unwrap_err();
    assert_eq!(
        err.to_string(),
        "write \"some/dirlink\": path exists but is not a regular file"
    );

    // Can't write inside a broken dir symlink
    let err = fs
        .write_file(&RootedFilePath::from("/brokenlink/file.ts"), "hello, world")
        .unwrap_err();
    assert_eq!(
        err.to_string(),
        "broken symlink \"brokenlink\" -> \"does/not/exist\""
    );

    let err = fs
        .write_file(
            &RootedFilePath::from("/brokenlink/also/wrong/file.ts"),
            "hello, world",
        )
        .unwrap_err();
    assert_eq!(
        err.to_string(),
        "broken symlink \"brokenlink\" -> \"does/not/exist\""
    );

    // But we can write to a broken file symlink
    fs.write_file(&RootedFilePath::from("/brokenlink"), "hello, world")
        .unwrap();
    let content = fs.read_file(&RootedFilePath::from("/brokenlink"));
    assert_eq!(content.as_deref(), Some("hello, world"));
    let content = fs.read_file(&RootedFilePath::from("/does/not/exist"));
    assert_eq!(content.as_deref(), Some("hello, world"));
}

#[test]
fn test_writable_fs_symlink_chain() {
    let fs = from_map(
        vec![
            ("/a", super::TestFile::from(symlink("/b"))),
            ("/b", super::TestFile::from(symlink("/c"))),
            ("/c", super::TestFile::from(symlink("/d"))),
            ("/d/existing.ts", super::TestFile::from("hello, world")),
        ],
        CaseSensitivity::CaseInsensitive,
    );

    fs.write_file(&RootedFilePath::from("/a/foo/bar/new.ts"), "this is new.ts")
        .unwrap();
    let content = fs.read_file(&RootedFilePath::from("/a/foo/bar/new.ts"));
    assert_eq!(content.as_deref(), Some("this is new.ts"));
    let content = fs.read_file(&RootedFilePath::from("/b/foo/bar/new.ts"));
    assert_eq!(content.as_deref(), Some("this is new.ts"));
    let content = fs.read_file(&RootedFilePath::from("/d/foo/bar/new.ts"));
    assert_eq!(content.as_deref(), Some("this is new.ts"));
}

#[test]
fn test_writable_fs_symlink_chain_not_dir() {
    let fs = from_map(
        vec![
            ("/a", super::TestFile::from(symlink("/b"))),
            ("/b", super::TestFile::from(symlink("/c"))),
            ("/c", super::TestFile::from(symlink("/d"))),
            ("/d", super::TestFile::from("hello, world")),
        ],
        CaseSensitivity::CaseInsensitive,
    );

    let err = fs
        .write_file(&RootedFilePath::from("/a/foo/bar/new.ts"), "this is new.ts")
        .unwrap_err();
    assert_eq!(
        err.to_string(),
        "mkdir \"d\": path exists but is not a directory"
    );
}

#[test]
fn test_writable_fs_symlink_delete() {
    let fs = writable_symlink_host();

    fs.remove(&RootedPath::from("/a")).unwrap();
    assert!(!fs.directory_exists(&RootedDirectoryPath::from("/a")));
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/b")));
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/c")));
    assert!(fs.file_exists(&RootedFilePath::from("/d/existing.ts")));

    // symlinks should still exist even if underlying file/dir is deleted
    fs.remove(&RootedPath::from("/d")).unwrap();
    assert!(!fs.directory_exists(&RootedDirectoryPath::from("/b")));
    assert!(!fs.directory_exists(&RootedDirectoryPath::from("/c")));
    assert!(!fs.directory_exists(&RootedDirectoryPath::from("/d")));
    assert!(!fs.file_exists(&RootedFilePath::from("/d/again.ts")));
    fs.write_file(&RootedFilePath::from("/d/again.ts"), "d exists again")
        .unwrap();
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/b")));
    assert!(fs.directory_exists(&RootedDirectoryPath::from("/c")));
    let content = fs.read_file(&RootedFilePath::from("/b/again.ts"));
    assert_eq!(content.as_deref(), Some("d exists again"));

    assert!(!fs.file_exists(&RootedFilePath::from("/brokenlink")));
    assert!(!fs.directory_exists(&RootedDirectoryPath::from("/brokenlink")));
    fs.remove(&RootedPath::from("/does/not/exist")).unwrap(); // should do nothing
    assert!(!fs.file_exists(&RootedFilePath::from("/brokenlink")));
    assert!(!fs.directory_exists(&RootedDirectoryPath::from("/brokenlink")));
    fs.write_file(&RootedFilePath::from("/does/not/exist"), "hello, world")
        .unwrap();
    assert!(fs.file_exists(&RootedFilePath::from("/brokenlink")));
}
