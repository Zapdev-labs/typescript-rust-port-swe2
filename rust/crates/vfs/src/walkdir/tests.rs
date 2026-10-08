// Ported from tsc/internal/vfs/walkdir_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{Arc, Mutex};

use tsc_tspath::{CaseSensitivity, RootedPath};

use crate::fs::{FileMode, FsError, MODE_DIR, MODE_SYMLINK};
use crate::vfs::Vfs;
use crate::vfstest;
use crate::walkdir::walk_dir;
use crate::wrapvfs::{self, Replacements};

fn fs_with(paths: &[(&str, &str)]) -> Arc<dyn Vfs> {
    vfstest::from_map(
        paths.iter().map(|(p, c)| (*p, *c)).collect::<Vec<_>>(),
        CaseSensitivity::CaseSensitive,
    )
}

#[test]
fn test_walk_dir() {
    let base = fs_with(&[
        ("/root/a.ts", ""),
        ("/root/dir/b.ts", ""),
        ("/root/link/hidden.ts", ""),
        ("/target/hidden.ts", ""),
    ]);

    let file_system = wrapvfs::wrap(
        base.clone(),
        Replacements {
            get_accessible_entries: {
                let base = base.clone();
                Some(Box::new(move |path| {
                    let mut entries = base.get_accessible_entries(path);
                    entries.symlinks = None;
                    if path.as_string() == "/root" {
                        entries.files.push("C:/foreign.ts".to_string());
                    }
                    entries
                }))
            },
            realpath: Some(Box::new(|path: &RootedPath| {
                match path.as_string() {
                    "/root/link" => RootedPath::from("/target"),
                    "/root/link/hidden.ts" => RootedPath::from("/target/hidden.ts"),
                    _ => path.clone(),
                }
            })),
            ..Default::default()
        },
    );

    let paths = Mutex::new(Vec::<String>::new());
    let modes = Mutex::new(Vec::<crate::fs::FileMode>::new());
    let err = walk_dir(
        &file_system,
        &RootedPath::from("/root"),
        &mut |path, entry, err| {
            assert!(err.is_none());
            let entry = entry.unwrap();
            paths.lock().unwrap().push(path.as_string().to_string());
            modes.lock().unwrap().push(entry.type_());
            if entry.type_() & MODE_SYMLINK != FileMode(0) {
                let info = entry.info().unwrap();
                assert_eq!(info.mode(), MODE_SYMLINK);
                assert!(!info.is_dir());
            }
            Ok(())
        },
    );
    assert!(err.is_ok());
    assert_eq!(
        *paths.lock().unwrap(),
        vec!["/root", "/root/a.ts", "/root/dir", "/root/dir/b.ts", "/root/link"]
    );
    assert_eq!(
        *modes.lock().unwrap(),
        vec![MODE_DIR, FileMode(0), MODE_DIR, FileMode(0), MODE_SYMLINK]
    );
}

#[test]
fn test_walk_dir_does_not_follow_root_symlink() {
    let base = fs_with(&[("/root/link/hidden.ts", ""), ("/target/hidden.ts", "")]);

    let file_system = wrapvfs::wrap(
        base.clone(),
        Replacements {
            get_accessible_entries: {
                let base = base.clone();
                Some(Box::new(move |path| {
                    let mut entries = base.get_accessible_entries(path);
                    entries.symlinks = None;
                    entries
                }))
            },
            realpath: Some(Box::new(|path: &RootedPath| {
                if path.as_string() == "/root/link" {
                    RootedPath::from("/target")
                } else {
                    path.clone()
                }
            })),
            ..Default::default()
        },
    );

    let paths = Mutex::new(Vec::<String>::new());
    let err = walk_dir(
        &file_system,
        &RootedPath::from("/root/link"),
        &mut |path, entry, err| {
            assert!(err.is_none());
            paths.lock().unwrap().push(path.as_string().to_string());
            assert_eq!(entry.unwrap().type_(), MODE_SYMLINK);
            Ok(())
        },
    );
    assert!(err.is_ok());
    assert_eq!(*paths.lock().unwrap(), vec!["/root/link"]);
}

#[test]
fn test_walk_dir_reports_root_file_symlink() {
    let base = fs_with(&[("/target/file.ts", "")]);

    let file_system = wrapvfs::wrap(
        base.clone(),
        Replacements {
            stat: {
                let base = base.clone();
                Some(Box::new(move |path: &RootedPath| {
                    if path.as_string() == "/root/link.ts" {
                        base.stat(&RootedPath::from("/target/file.ts"))
                    } else {
                        base.stat(path)
                    }
                }))
            },
            realpath: Some(Box::new(|path: &RootedPath| {
                if path.as_string() == "/root/link.ts" {
                    RootedPath::from("/target/file.ts")
                } else {
                    path.clone()
                }
            })),
            ..Default::default()
        },
    );

    let err = walk_dir(
        &file_system,
        &RootedPath::from("/root/link.ts"),
        &mut |path, entry, err| {
            assert!(err.is_none());
            assert_eq!(path.as_string(), "/root/link.ts");
            let entry = entry.unwrap();
            assert_eq!(entry.name(), "link.ts");
            assert_eq!(entry.type_(), MODE_SYMLINK);
            Ok(())
        },
    );
    assert!(err.is_ok());
}

#[test]
fn test_walk_dir_skip_dir() {
    let file_system = fs_with(&[("/root/a/hidden.ts", ""), ("/root/b.ts", "")]);

    let paths = Mutex::new(Vec::<String>::new());
    let err = walk_dir(
        &file_system,
        &RootedPath::from("/root"),
        &mut |path, _entry, err| {
            assert!(err.is_none());
            paths.lock().unwrap().push(path.as_string().to_string());
            if path.as_string() == "/root/a" {
                return Err(FsError::SkipDir);
            }
            Ok(())
        },
    );
    assert!(err.is_ok());
    assert_eq!(
        *paths.lock().unwrap(),
        vec!["/root", "/root/a", "/root/b.ts"]
    );
}

#[test]
fn test_walk_dir_skip_all() {
    let file_system = fs_with(&[("/root/a.ts", ""), ("/root/b.ts", "")]);

    let paths = Mutex::new(Vec::<String>::new());
    let err = walk_dir(
        &file_system,
        &RootedPath::from("/root"),
        &mut |path, _entry, err| {
            assert!(err.is_none());
            paths.lock().unwrap().push(path.as_string().to_string());
            if path.as_string() == "/root/a.ts" {
                return Err(FsError::SkipAll);
            }
            Ok(())
        },
    );
    assert!(err.is_ok());
    assert_eq!(*paths.lock().unwrap(), vec!["/root", "/root/a.ts"]);
}

#[test]
fn test_walk_dir_consumes_skip_dir_for_root_file() {
    let file_system = fs_with(&[("/root.ts", "")]);
    let err = walk_dir(&file_system, &RootedPath::from("/root.ts"), &mut |_p, _e, err| {
        assert!(err.is_none());
        Err(FsError::SkipDir)
    });
    assert!(err.is_ok());
}

#[test]
fn test_walk_dir_consumes_skip_for_missing_root() {
    let file_system = fs_with(&[]);
    for sentinel_is_dir in [true, false] {
        let err = walk_dir(&file_system, &RootedPath::from("/missing"), &mut |_p, _e, err| {
            assert!(err.unwrap().is_not_exist());
            Err(if sentinel_is_dir {
                FsError::SkipDir
            } else {
                FsError::SkipAll
            })
        });
        assert!(err.is_ok());
    }
}

#[test]
fn test_walk_dir_uses_symlink_metadata_without_realpath_calls() {
    let base = fs_with(&[("/root/dir/file.ts", "")]);

    let realpath_calls = Arc::new(Mutex::new(Vec::<String>::new()));
    let file_system = wrapvfs::wrap(
        base,
        Replacements {
            realpath: {
                let realpath_calls = realpath_calls.clone();
                Some(Box::new(move |path: &RootedPath| {
                    realpath_calls
                        .lock()
                        .unwrap()
                        .push(path.as_string().to_string());
                    path.clone()
                }))
            },
            ..Default::default()
        },
    );

    let err = walk_dir(
        &file_system,
        &RootedPath::from("/root"),
        &mut |_p, _e, err| match err {
            Some(e) => Err(FsError::Message(format!("{e}"))),
            None => Ok(()),
        },
    );
    assert!(err.is_ok());
    assert!(
        !realpath_calls
            .lock()
            .unwrap()
            .contains(&"/root/dir".to_string())
    );
}
