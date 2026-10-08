// Ported from tsc/internal/ipc/transport_unix.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// `//go:build !windows` → `#[cfg(unix)]`.

use std::io;
use std::os::unix::net::UnixListener;

/// `newPipeListener` — creates a Unix domain socket listener.
pub(crate) fn new_pipe_listener(path: &str) -> io::Result<UnixListener> {
    // Remove any existing socket file.
    let _ = std::fs::remove_file(path);
    UnixListener::bind(path)
}

/// `GeneratePipePath` — `path.Join(os.TempDir(), name)`.
pub fn generate_pipe_path(name: &str) -> String {
    std::env::temp_dir()
        .join(name)
        .to_string_lossy()
        .into_owned()
}
