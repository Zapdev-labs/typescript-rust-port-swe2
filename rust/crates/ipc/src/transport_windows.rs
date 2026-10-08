// Ported from tsc/internal/ipc/transport_windows.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// `//go:build windows` → `#[cfg(windows)]`.
//
// PORT: `winio.ListenPipe` (Windows named pipes) has no safe-std equivalent —
// creating a named pipe requires unsafe FFI or an external crate, both of
// which are off-limits (`unsafe_code = "forbid"`; SPEC §5.11 dependency
// policy). The listener constructor therefore fails with `Unsupported`,
// making `new_pipe_transport` error out at startup rather than silently
// diverging from the Go named-pipe transport. `generate_pipe_path` is ported
// verbatim. DEFERRED: a real named-pipe listener needs an approved
// windows-sys/`go-winio` analog.

use std::io;

/// `newPipeListener` — `winio.ListenPipe(path, nil)`. Unsupported in this
/// port; see the file header.
#[allow(clippy::unnecessary_wraps)]
pub(crate) fn new_pipe_listener(_path: &str) -> io::Result<std::convert::Infallible> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "ipc: named pipe transport is not supported by this port on Windows",
    ))
}

/// `GeneratePipePath` — `\\.\pipe\` + name.
pub fn generate_pipe_path(name: &str) -> String {
    format!(r"\\.\pipe\{name}")
}
