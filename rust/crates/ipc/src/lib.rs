// tsc-ipc — port of tsc/internal/ipc @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Bidirectional JSON-RPC IPC: the `Conn` trait with sync (`SyncConn`) and
// per-request-goroutine (`AsyncConn`) implementations, a `Protocol`
// abstraction (LSP-style Content-Length framing over `tsc-jsonrpc`), pipe and
// stdio transports, and server-side per-request timing.

mod conn;
mod conn_async;
mod conn_sync;
mod protocol;
mod protocol_jsonrpc;
mod timing;
mod transport;
#[cfg(unix)]
mod transport_unix;
#[cfg(windows)]
mod transport_windows;

pub use conn::*;
pub use conn_async::*;
pub use conn_sync::*;
pub use protocol::*;
pub use protocol_jsonrpc::*;
pub use timing::{METHOD_GET_SERVER_TIMING, METHOD_RESET_SERVER_TIMING};
pub use transport::*;
#[cfg(unix)]
pub use transport_unix::generate_pipe_path;
#[cfg(windows)]
pub use transport_windows::generate_pipe_path;

#[cfg(test)]
mod conn_async_test;
#[cfg(test)]
mod conn_sync_test;
#[cfg(test)]
mod timing_test;
