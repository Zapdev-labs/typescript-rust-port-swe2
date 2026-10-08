// Ported from tsc/internal/nativepath/eintr_unix.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// //go:build linux

use std::io;

pub(crate) fn ignoring_eintr<T>(mut f: impl FnMut() -> Result<T, io::Error>) -> Result<T, io::Error> {
    loop {
        match f() {
            // PORT: Go compares `err != syscall.EINTR` on the raw errno;
            // io::ErrorKind::Interrupted is the std mapping of EINTR.
            Err(err) if err.kind() == io::ErrorKind::Interrupted => continue,
            other => return other,
        }
    }
}
