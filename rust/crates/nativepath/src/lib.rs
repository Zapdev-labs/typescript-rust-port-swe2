// Ported from tsc/internal/nativepath @ ec47d33c23e464a17cdf2475632cba629bee8763

#[cfg(target_os = "linux")]
mod eintr_unix;

#[cfg(target_os = "linux")]
mod realpath_linux;
#[cfg(target_os = "linux")]
pub use realpath_linux::realpath;

// realpath_other.go is `//go:build !windows && !linux`; the Rust port is
// Linux-first (SPEC §7.7) so it is wired for unix-only — darwin lands here.
#[cfg(all(unix, not(target_os = "linux")))]
mod realpath_other;
#[cfg(all(unix, not(target_os = "linux")))]
pub use realpath_other::realpath;

// symlink_other.go is `//go:build !windows`.
#[cfg(unix)]
mod symlink_other;
#[cfg(unix)]
pub use symlink_other::is_symlink_or_reparse_point;

// TODO(port): windows — realpath_windows.go (GetFinalPathNameByHandle over an
// O_PATH-equivalent handle) and symlink_windows.go (GetFileAttributesEx +
// FILE_ATTRIBUTE_REPARSE_POINT) are not ported yet.

#[cfg(unix)]
use std::io;

// PORT: Go strings hold arbitrary bytes, so EvalSymlinks can return non-UTF-8
// paths; Rust String cannot — non-UTF-8 paths produce an error instead.
#[cfg(unix)]
pub(crate) fn path_to_string(path: std::path::PathBuf) -> Result<String, io::Error> {
    path.into_os_string()
        .into_string()
        .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "path is not valid UTF-8"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn realpath_resolves_current_dir() {
        // Smokes the O_PATH + /proc/self/fd path on Linux.
        let resolved = realpath(".").unwrap();
        let expected = std::env::current_dir().unwrap();
        let expected = expected.to_str().unwrap();
        assert_eq!(resolved, expected);
    }

    #[test]
    fn realpath_missing_path_errors() {
        assert!(realpath("/definitely/missing/path/xyzzy").is_err());
    }

    #[test]
    fn is_symlink_or_reparse_point_detects_symlink() {
        let dir = std::env::temp_dir().join(format!("tsc-nativepath-test-{}", std::process::id()));
        let target = dir.join("target");
        let link = dir.join("link");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(&target, "x").unwrap();
        std::os::unix::fs::symlink(&target, &link).unwrap();
        assert!(is_symlink_or_reparse_point(link.to_str().unwrap()));
        assert!(!is_symlink_or_reparse_point(target.to_str().unwrap()));
        assert!(!is_symlink_or_reparse_point(
            dir.join("missing").to_str().unwrap()
        ));
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
