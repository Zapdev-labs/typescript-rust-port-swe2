// Ported from tsc/internal/nativepath/realpath_other.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// //go:build !windows && !linux

use std::io;

pub fn realpath(path: &str) -> Result<String, io::Error> {
    // filepath.EvalSymlinks — std::fs::canonicalize is its std equivalent.
    crate::path_to_string(std::fs::canonicalize(path)?)
}
