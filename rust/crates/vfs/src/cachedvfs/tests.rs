// Ported from tsc/internal/vfs/cachedvfs/cachedvfs_test.go
// @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath};

use super::from;
use crate::vfs::Vfs;
use crate::{vfsmock, vfstest};

fn create_mock_fs() -> Arc<vfsmock::FsMock> {
    vfsmock::wrap(vfstest::from_map(
        [("/some/path/file.txt", "hello world")],
        CaseSensitivity::CaseSensitive,
    ))
}

fn file(p: &str) -> RootedFilePath {
    RootedFilePath::from(p)
}
fn dir(p: &str) -> RootedDirectoryPath {
    RootedDirectoryPath::from(p)
}
fn path(p: &str) -> RootedPath {
    RootedPath::from(p)
}

#[test]
fn test_directory_exists() {
    let underlying = create_mock_fs();
    let cached = from(underlying.clone() as Arc<dyn Vfs>);

    cached.directory_exists(&dir("/some/path"));
    assert_eq!(1, underlying.calls().directory_exists.len());

    cached.directory_exists(&dir("/some/path"));
    assert_eq!(1, underlying.calls().directory_exists.len());

    cached.clear_cache();
    cached.directory_exists(&dir("/some/path"));
    assert_eq!(2, underlying.calls().directory_exists.len());

    cached.directory_exists(&dir("/other/path"));
    assert_eq!(3, underlying.calls().directory_exists.len());

    cached.disable_and_clear_cache();
    cached.directory_exists(&dir("/some/path"));
    assert_eq!(4, underlying.calls().directory_exists.len());

    cached.directory_exists(&dir("/some/path"));
    assert_eq!(5, underlying.calls().directory_exists.len());

    cached.enable();
    cached.directory_exists(&dir("/some/path"));
    assert_eq!(6, underlying.calls().directory_exists.len());

    cached.directory_exists(&dir("/some/path"));
    assert_eq!(6, underlying.calls().directory_exists.len());
}

#[test]
fn test_file_exists() {
    let underlying = create_mock_fs();
    let cached = from(underlying.clone() as Arc<dyn Vfs>);

    cached.file_exists(&file("/some/path/file.txt"));
    assert_eq!(1, underlying.calls().file_exists.len());

    cached.file_exists(&file("/some/path/file.txt"));
    assert_eq!(1, underlying.calls().file_exists.len());

    cached.clear_cache();
    cached.file_exists(&file("/some/path/file.txt"));
    assert_eq!(2, underlying.calls().file_exists.len());

    cached.file_exists(&file("/other/path/file.txt"));
    assert_eq!(3, underlying.calls().file_exists.len());

    cached.disable_and_clear_cache();
    cached.file_exists(&file("/some/path/file.txt"));
    assert_eq!(4, underlying.calls().file_exists.len());

    cached.file_exists(&file("/some/path/file.txt"));
    assert_eq!(5, underlying.calls().file_exists.len());

    cached.enable();
    cached.file_exists(&file("/some/path/file.txt"));
    assert_eq!(6, underlying.calls().file_exists.len());

    cached.file_exists(&file("/some/path/file.txt"));
    assert_eq!(6, underlying.calls().file_exists.len());
}

#[test]
fn test_get_accessible_entries() {
    let underlying = create_mock_fs();
    let cached = from(underlying.clone() as Arc<dyn Vfs>);

    cached.get_accessible_entries(&dir("/some/path"));
    assert_eq!(1, underlying.calls().get_accessible_entries.len());

    cached.get_accessible_entries(&dir("/some/path"));
    assert_eq!(1, underlying.calls().get_accessible_entries.len());

    cached.clear_cache();
    cached.get_accessible_entries(&dir("/some/path"));
    assert_eq!(2, underlying.calls().get_accessible_entries.len());

    cached.get_accessible_entries(&dir("/other/path"));
    assert_eq!(3, underlying.calls().get_accessible_entries.len());

    cached.disable_and_clear_cache();
    cached.get_accessible_entries(&dir("/some/path"));
    assert_eq!(4, underlying.calls().get_accessible_entries.len());

    cached.get_accessible_entries(&dir("/some/path"));
    assert_eq!(5, underlying.calls().get_accessible_entries.len());

    cached.enable();
    cached.get_accessible_entries(&dir("/some/path"));
    assert_eq!(6, underlying.calls().get_accessible_entries.len());

    cached.get_accessible_entries(&dir("/some/path"));
    assert_eq!(6, underlying.calls().get_accessible_entries.len());
}

#[test]
fn test_realpath() {
    let underlying = create_mock_fs();
    let cached = from(underlying.clone() as Arc<dyn Vfs>);

    cached.realpath(&path("/some/path"));
    assert_eq!(1, underlying.calls().realpath.len());

    cached.realpath(&path("/some/path"));
    assert_eq!(1, underlying.calls().realpath.len());

    cached.clear_cache();
    cached.realpath(&path("/some/path"));
    assert_eq!(2, underlying.calls().realpath.len());

    cached.realpath(&path("/other/path"));
    assert_eq!(3, underlying.calls().realpath.len());

    cached.disable_and_clear_cache();
    cached.realpath(&path("/some/path"));
    assert_eq!(4, underlying.calls().realpath.len());

    cached.realpath(&path("/some/path"));
    assert_eq!(5, underlying.calls().realpath.len());

    cached.enable();
    cached.realpath(&path("/some/path"));
    assert_eq!(6, underlying.calls().realpath.len());

    cached.realpath(&path("/some/path"));
    assert_eq!(6, underlying.calls().realpath.len());
}

#[test]
fn test_stat() {
    let underlying = create_mock_fs();
    let cached = from(underlying.clone() as Arc<dyn Vfs>);

    cached.stat(&path("/some/path"));
    assert_eq!(1, underlying.calls().stat.len());

    cached.stat(&path("/some/path"));
    assert_eq!(1, underlying.calls().stat.len());

    cached.clear_cache();
    cached.stat(&path("/some/path"));
    assert_eq!(2, underlying.calls().stat.len());

    cached.stat(&path("/other/path"));
    assert_eq!(3, underlying.calls().stat.len());

    cached.disable_and_clear_cache();
    cached.stat(&path("/some/path"));
    assert_eq!(4, underlying.calls().stat.len());

    cached.stat(&path("/some/path"));
    assert_eq!(5, underlying.calls().stat.len());

    cached.enable();
    cached.stat(&path("/some/path"));
    assert_eq!(6, underlying.calls().stat.len());

    cached.stat(&path("/some/path"));
    assert_eq!(6, underlying.calls().stat.len());
}

#[test]
fn test_read_file() {
    let underlying = create_mock_fs();
    let cached = from(underlying.clone() as Arc<dyn Vfs>);

    cached.read_file(&file("/some/path/file.txt"));
    assert_eq!(1, underlying.calls().read_file.len());

    cached.read_file(&file("/some/path/file.txt"));
    assert_eq!(2, underlying.calls().read_file.len());

    cached.clear_cache();
    cached.read_file(&file("/some/path/file.txt"));
    assert_eq!(3, underlying.calls().read_file.len());

    cached.disable_and_clear_cache();
    cached.read_file(&file("/some/path/file.txt"));
    assert_eq!(4, underlying.calls().read_file.len());

    cached.read_file(&file("/some/path/file.txt"));
    assert_eq!(5, underlying.calls().read_file.len());

    cached.enable();
    cached.read_file(&file("/some/path/file.txt"));
    assert_eq!(6, underlying.calls().read_file.len());

    cached.read_file(&file("/some/path/file.txt"));
    assert_eq!(7, underlying.calls().read_file.len());
}

#[test]
fn test_case_sensitivity() {
    let underlying = create_mock_fs();
    let cached = from(underlying.clone() as Arc<dyn Vfs>);

    cached.case_sensitivity();
    assert_eq!(1, underlying.calls().case_sensitivity.len());

    cached.case_sensitivity();
    assert_eq!(2, underlying.calls().case_sensitivity.len());

    cached.clear_cache();
    cached.case_sensitivity();
    assert_eq!(3, underlying.calls().case_sensitivity.len());

    cached.disable_and_clear_cache();
    cached.case_sensitivity();
    assert_eq!(4, underlying.calls().case_sensitivity.len());

    cached.case_sensitivity();
    assert_eq!(5, underlying.calls().case_sensitivity.len());

    cached.enable();
    cached.case_sensitivity();
    assert_eq!(6, underlying.calls().case_sensitivity.len());

    cached.case_sensitivity();
    assert_eq!(7, underlying.calls().case_sensitivity.len());
}

#[test]
fn test_remove() {
    let underlying = create_mock_fs();
    let cached = from(underlying.clone() as Arc<dyn Vfs>);

    let _ = cached.remove(&path("/some/path/file.txt"));
    assert_eq!(1, underlying.calls().remove.len());

    let _ = cached.remove(&path("/some/path/file.txt"));
    assert_eq!(2, underlying.calls().remove.len());

    cached.clear_cache();
    let _ = cached.remove(&path("/some/path/file.txt"));
    assert_eq!(3, underlying.calls().remove.len());

    cached.disable_and_clear_cache();
    let _ = cached.remove(&path("/some/path/file.txt"));
    assert_eq!(4, underlying.calls().remove.len());

    let _ = cached.remove(&path("/some/path/file.txt"));
    assert_eq!(5, underlying.calls().remove.len());

    cached.enable();
    let _ = cached.remove(&path("/some/path/file.txt"));
    assert_eq!(6, underlying.calls().remove.len());

    let _ = cached.remove(&path("/some/path/file.txt"));
    assert_eq!(7, underlying.calls().remove.len());
}

#[test]
fn test_write_file() {
    let underlying = create_mock_fs();
    let cached = from(underlying.clone() as Arc<dyn Vfs>);

    let _ = cached.write_file(&file("/some/path/file.txt"), "new content");
    assert_eq!(1, underlying.calls().write_file.len());

    let _ = cached.write_file(&file("/some/path/file.txt"), "another content");
    assert_eq!(2, underlying.calls().write_file.len());

    cached.clear_cache();
    let _ = cached.write_file(&file("/some/path/file.txt"), "third content");
    assert_eq!(3, underlying.calls().write_file.len());

    {
        let calls = underlying.calls();
        let call = &calls.write_file[2];
        assert_eq!("/some/path/file.txt", call.path.as_string());
        assert_eq!("third content", call.data);
    }

    cached.disable_and_clear_cache();
    let _ = cached.write_file(&file("/some/path/file.txt"), "fourth content");
    assert_eq!(4, underlying.calls().write_file.len());

    let _ = cached.write_file(&file("/some/path/file.txt"), "fifth content");
    assert_eq!(5, underlying.calls().write_file.len());

    cached.enable();
    let _ = cached.write_file(&file("/some/path/file.txt"), "sixth content");
    assert_eq!(6, underlying.calls().write_file.len());

    let _ = cached.write_file(&file("/some/path/file.txt"), "seventh content");
    assert_eq!(7, underlying.calls().write_file.len());
}
