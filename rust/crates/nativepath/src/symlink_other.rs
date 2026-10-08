// Ported from tsc/internal/nativepath/symlink_other.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// //go:build !windows

/// `func IsSymlinkOrReparsePoint` — os.Lstat + ModeSymlink check.
pub fn is_symlink_or_reparse_point(path: &str) -> bool {
    // os.Lstat + info.Mode()&os.ModeSymlink — std::fs::symlink_metadata does
    // not follow symlinks, matching Lstat.
    match std::fs::symlink_metadata(path) {
        Ok(info) => info.file_type().is_symlink(),
        Err(_) => false,
    }
}
