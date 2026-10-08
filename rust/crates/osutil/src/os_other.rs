// Ported from tsc/internal/osutil/os_other.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// //go:build !android

use std::io;

pub(crate) fn args() -> Vec<String> {
    // os.Args — PORT: Go keeps raw argv bytes; env::args() panics on invalid
    // UTF-8, so args_os + lossy conversion is used instead.
    std::env::args_os()
        .map(|arg| arg.to_string_lossy().into_owned())
        .collect()
}

pub(crate) fn executable() -> Result<String, io::Error> {
    // os.Executable()
    // PORT: Go returns a byte-string path; Rust String must be UTF-8.
    std::env::current_exe()?.into_os_string().into_string().map_err(|_| {
        io::Error::new(io::ErrorKind::InvalidData, "executable path is not valid UTF-8")
    })
}
