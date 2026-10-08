// Ported from tsc/internal/vfs/osvfs/{os_test.go,realpath_test.go,helpers_test.go}
// @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use tsc_tspath::{rooted_directory_path_from_absolute, rooted_file_path_from_absolute};

use super::fs;

/// mklink is the osvfs.mklink test helper (unix port).
#[cfg(unix)]
fn mklink(target: &Path, link: &Path) {
    std::os::unix::fs::symlink(target, link)
        .unwrap_or_else(|e| panic!("symlink {} -> {}: {}", link.display(), target.display(), e));
}

/// TempDir is testing.T.TempDir.
struct TempDir(PathBuf);

impl TempDir {
    fn new() -> TempDir {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let dir = std::env::temp_dir().join(format!(
            "tsc-vfs-test-{}-{}",
            std::process::id(),
            COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(&dir).unwrap();
        TempDir(dir)
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn setup_symlinks() -> (TempDir, PathBuf, PathBuf) {
    let tmp = TempDir::new();
    let target = tmp.path().join("target");
    let target_file = target.join("file");
    let link = tmp.path().join("link");
    let link_file = link.join("file");

    std::fs::create_dir_all(&target).unwrap();
    std::fs::write(&target_file, b"hello").unwrap();

    mklink(&target, &link);

    (tmp, target_file, link_file)
}

#[test]
fn test_read_file() {
    let fs = fs();

    let go_mod = Path::new(tsc_repo::paths::root_path()).join("go.mod");
    let expected = std::fs::read_to_string(&go_mod).unwrap();

    let path = rooted_file_path_from_absolute(go_mod.to_str().unwrap());
    let contents = fs.read_file(&path);
    assert_eq!(contents.as_deref(), Some(expected.as_str()));
}

#[test]
fn test_realpath() {
    let fs = fs();

    // PORT: os.UserHomeDir — $HOME on unix.
    #[cfg(unix)]
    let home = std::env::var_os("HOME").map(PathBuf::from);
    #[cfg(not(unix))]
    let home = std::env::var_os("USERPROFILE").map(PathBuf::from);
    let Some(home) = home else {
        eprintln!("skipping: no home directory");
        return;
    };

    let home_path = rooted_directory_path_from_absolute(home.to_str().unwrap());
    let expected = home_path.as_string().to_string();
    #[cfg(windows)]
    let expected = {
        // Windows drive letters can be lowercase, but realpath will always return uppercase.
        let mut e = expected;
        e.replace_range(..1, &expected[..1].to_uppercase());
        e
    };
    let realpath = fs.realpath(&home_path.as_path());
    assert_eq!(realpath.as_string(), expected);
}

#[test]
fn test_case_sensitivity() {
    let fs = fs();
    // Just check that it works.
    let _ = fs.case_sensitivity();

    if cfg!(windows) {
        assert!(fs.case_sensitivity().is_case_insensitive());
    }
    if cfg!(target_os = "linux") {
        assert!(fs.case_sensitivity().is_case_sensitive());
    }
}

#[test]
#[cfg(unix)]
fn test_symlink_realpath() {
    let (_tmp, target_file, link_file) = setup_symlinks();

    let contents = std::fs::read(&link_file).unwrap();
    assert_eq!(contents, b"hello");

    let fs = fs();
    let target_realpath =
        fs.realpath(&rooted_file_path_from_absolute(target_file.to_str().unwrap()).as_path());
    let link_realpath =
        fs.realpath(&rooted_file_path_from_absolute(link_file.to_str().unwrap()).as_path());

    assert_eq!(
        target_realpath.as_string(),
        link_realpath.as_string(),
        "expected realpath of target and link to be equal"
    );
}

#[test]
#[cfg(unix)]
fn test_get_accessible_entries() {
    let tmp = TempDir::new();
    let target = tmp.path().join("target");
    let link = tmp.path().join("link");

    std::fs::create_dir_all(&target).unwrap();
    std::fs::create_dir_all(&link).unwrap();

    let target_file1 = target.join("file1");
    let target_file2 = target.join("file2");
    std::fs::write(&target_file1, b"hello").unwrap();
    std::fs::write(&target_file2, b"world").unwrap();

    let target_dir1 = target.join("dir1");
    let target_dir2 = target.join("dir2");
    std::fs::create_dir_all(&target_dir1).unwrap();
    std::fs::create_dir_all(&target_dir2).unwrap();

    mklink(&target_file1, &link.join("file1"));
    mklink(&target_file2, &link.join("file2"));
    mklink(&target_dir1, &link.join("dir1"));
    mklink(&target_dir2, &link.join("dir2"));

    let fs = fs();

    let entries =
        fs.get_accessible_entries(&rooted_directory_path_from_absolute(link.to_str().unwrap()));

    assert_eq!(entries.directories, ["dir1", "dir2"]);
    assert_eq!(entries.files, ["file1", "file2"]);
    let symlinks = entries
        .symlinks
        .as_ref()
        .expect("expected Symlinks to be set for directory with symlinks");
    assert_eq!(symlinks.len(), 4);
    for name in ["file1", "file2", "dir1", "dir2"] {
        assert!(symlinks.contains(name), "expected {name} to be in Symlinks");
    }

    // Non-symlink directory should have empty Symlinks.
    let entries =
        fs.get_accessible_entries(&rooted_directory_path_from_absolute(target.to_str().unwrap()));
    assert_eq!(entries.directories, ["dir1", "dir2"]);
    assert_eq!(entries.files, ["file1", "file2"]);
    let symlinks = entries
        .symlinks
        .as_ref()
        .expect("expected Symlinks to be non-nil for directory without symlinks");
    assert_eq!(symlinks.len(), 0);
}
