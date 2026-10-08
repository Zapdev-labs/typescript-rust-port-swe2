// Ported from tsc/internal/ipc/transport.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `Accept() (io.ReadWriteCloser, error)` returns `Arc<Self::Conn>` because
//   the connection and its protocol share one stream (see `SharedIo`).
// - `io.ReadCloser`/`io.WriteCloser` → `ReadClose`/`WriteClose` (blanket
//   impls make any `Read`/`Write` usable; `close_*` mirrors `os.Stdin`/
//   `os.Stdout` semantics — borrowed fds are not closed, so `close_read` is
//   a no-op and `close_write` flushes).
// - `stdioConn`'s halves sit behind separate `Mutex`es so `&StdioConn`
//   implements `Read`/`Write` — needed for `new_async_conn` to split it like
//   Go's `rwc`.
// - `PipeTransport::close` cannot close the listener fd through safe std;
//   instead the listener is nonblocking and `accept` polls a `closed` flag
//   (≤5 ms wake-up vs Go's instant unblocking). On Unix the socket file is
//   left behind on close, exactly as Go leaves it.

use std::io;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};

use crate::IoClose;
#[cfg(unix)]
use crate::transport_unix::new_pipe_listener;
#[cfg(windows)]
use crate::transport_windows::new_pipe_listener;

/// `io.Closer` for streams — see [`IoClose`].
impl IoClose for std::net::TcpStream {
    fn close(&self) -> io::Result<()> {
        // PORT: Go closes the fd outright; `shutdown` is the safe-std
        // equivalent — blocked reads return EOF and the peer sees a close.
        self.shutdown(std::net::Shutdown::Both)
    }
}

#[cfg(unix)]
impl IoClose for std::os::unix::net::UnixStream {
    fn close(&self) -> io::Result<()> {
        self.shutdown(std::net::Shutdown::Both)
    }
}

/// `io.ReadCloser` — `Read` + `Close`.
pub trait ReadClose: io::Read + Send {
    /// `Close() error` on the read half.
    fn close_read(&mut self) -> io::Result<()>;
}

impl<T: io::Read + Send> ReadClose for T {
    fn close_read(&mut self) -> io::Result<()> {
        // PORT: dropping the value is the close; for borrowed fds like
        // `io::Stdin` closing is a no-op either way.
        Ok(())
    }
}

/// `io.WriteCloser` — `Write` + `Close`.
pub trait WriteClose: io::Write + Send {
    /// `Close() error` on the write half.
    fn close_write(&mut self) -> io::Result<()>;
}

impl<T: io::Write + Send> WriteClose for T {
    fn close_write(&mut self) -> io::Result<()> {
        // `os.Stdout.Close()` has nothing buffered in Go; flushing here is a
        // harmless superset that also drains any `BufWriter` the caller
        // wrapped around the sink.
        self.flush()
    }
}

/// `type Transport interface` — accepts connections from API clients.
pub trait Transport {
    /// The `io.ReadWriteCloser` produced by `accept`. To drive a
    /// [`crate::Conn`] it must additionally implement `Read`/`Write` through
    /// `&self` plus [`IoClose`] (std does so for `&UnixStream`, `&TcpStream`,
    /// and `&StdioConn`).
    type Conn: Send + Sync + 'static;

    /// `Accept() (io.ReadWriteCloser, error)`
    fn accept(&self) -> io::Result<Arc<Self::Conn>>;
    /// `Close() error`
    fn close(&self) -> io::Result<()>;
}

#[cfg(unix)]
type PipeListener = std::os::unix::net::UnixListener;
#[cfg(windows)]
type PipeListener = std::convert::Infallible;

/// `type PipeTransport struct` — accepts connections on a Unix domain socket
/// or Windows named pipe.
pub struct PipeTransport {
    /// `listener net.Listener` — unread on Windows, where the transport can
    /// never be constructed (see `transport_windows.rs`).
    #[cfg_attr(windows, allow(dead_code))]
    listener: PipeListener,
    /// `Close` flag — see the file header; stands in for closing the
    /// listener fd, which safe std cannot do while `accept` may block.
    #[cfg(unix)]
    closed: AtomicBool,
}

/// `NewPipeTransport` — listens on the given path. On Unix this creates a
/// Unix domain socket; on Windows a named pipe (currently unsupported — see
/// `transport_windows.rs`).
pub fn new_pipe_transport(path: &str) -> io::Result<PipeTransport> {
    let listener = new_pipe_listener(path)?;
    #[cfg(unix)]
    listener.set_nonblocking(true)?;
    Ok(PipeTransport {
        listener,
        #[cfg(unix)]
        closed: AtomicBool::new(false),
    })
}

#[cfg(unix)]
impl Transport for PipeTransport {
    type Conn = std::os::unix::net::UnixStream;

    /// `Accept`
    fn accept(&self) -> io::Result<Arc<Self::Conn>> {
        loop {
            match self.listener.accept() {
                // Accepted unix sockets are blocking even when the listener
                // is nonblocking (O_NONBLOCK is not inherited).
                Ok((stream, _)) => return Ok(Arc::new(stream)),
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    if self.closed.load(Ordering::SeqCst) {
                        // Go: `use of closed network connection`
                        // (`net.ErrClosed`, the poll.ErrNetClosing text).
                        return Err(io::Error::new(
                            io::ErrorKind::Other,
                            "use of closed network connection",
                        ));
                    }
                    std::thread::sleep(std::time::Duration::from_millis(5));
                }
                Err(e) => return Err(e),
            }
        }
    }

    /// `Close`
    fn close(&self) -> io::Result<()> {
        self.closed.store(true, Ordering::SeqCst);
        Ok(())
    }
}

#[cfg(windows)]
impl Transport for PipeTransport {
    /// Never produced — `new_pipe_transport` always fails on Windows (see
    /// `transport_windows.rs`).
    type Conn = PipeStream;

    fn accept(&self) -> io::Result<Arc<Self::Conn>> {
        unreachable!("PipeTransport cannot be constructed on Windows")
    }

    fn close(&self) -> io::Result<()> {
        unreachable!("PipeTransport cannot be constructed on Windows")
    }
}

/// Windows `Accept` connection placeholder — never constructed because named
/// pipes are unsupported in this port.
#[cfg(windows)]
pub enum PipeStream {}

impl PipeTransport {
    /// `Path()` — `t.listener.Addr().String()`.
    #[cfg(unix)]
    pub fn path(&self) -> String {
        self.listener
            .local_addr()
            .ok()
            .and_then(|a| a.as_pathname().map(|p| p.to_string_lossy().into_owned()))
            // Go's `UnixAddr.String()` prints "@" for unnamed sockets.
            .unwrap_or_else(|| "@".to_string())
    }

    /// `Path()` — unreachable: `new_pipe_transport` always fails on Windows.
    #[cfg(windows)]
    pub fn path(&self) -> String {
        unreachable!("PipeTransport cannot be constructed on Windows")
    }
}

/// `type StdioTransport struct` — wraps stdin/stdout as a single-connection
/// transport.
pub struct StdioTransport {
    /// `stdin io.ReadCloser`
    stdin: Mutex<Option<Box<dyn ReadClose>>>,
    /// `stdout io.WriteCloser`
    stdout: Mutex<Option<Box<dyn WriteClose>>>,
    /// `used bool`
    used: AtomicBool,
}

/// `NewStdioTransport(stdin, stdout)`
pub fn new_stdio_transport(
    stdin: Box<dyn ReadClose>,
    stdout: Box<dyn WriteClose>,
) -> StdioTransport {
    StdioTransport {
        stdin: Mutex::new(Some(stdin)),
        stdout: Mutex::new(Some(stdout)),
        used: AtomicBool::new(false),
    }
}

impl Transport for StdioTransport {
    type Conn = StdioConn;

    /// `Accept` — succeeds once, then returns `io.EOF`.
    fn accept(&self) -> io::Result<Arc<StdioConn>> {
        if self.used.swap(true, Ordering::SeqCst) {
            return Err(io::Error::new(io::ErrorKind::UnexpectedEof, "EOF"));
        }
        let stdin = self.stdin.lock().unwrap().take();
        let stdout = self.stdout.lock().unwrap().take();
        Ok(Arc::new(StdioConn {
            stdin: Mutex::new(stdin.expect("StdioTransport accepted twice")),
            stdout: Mutex::new(stdout.expect("StdioTransport accepted twice")),
        }))
    }

    /// `Close`
    fn close(&self) -> io::Result<()> {
        Ok(())
    }
}

/// `stdioConn` — the single connection produced by [`StdioTransport`].
/// Read and Write lock the two halves independently, like Go's embedded
/// `io.Reader`/`io.Writer`.
pub struct StdioConn {
    stdin: Mutex<Box<dyn ReadClose>>,
    stdout: Mutex<Box<dyn WriteClose>>,
}

/// `impl io.Reader` — Go embeds `io.Reader` in `stdioConn`.
impl io::Read for &StdioConn {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.stdin.lock().unwrap().read(buf)
    }
}

/// `impl io.Writer` — Go embeds `io.Writer` in `stdioConn`.
impl io::Write for &StdioConn {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.stdout.lock().unwrap().write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.stdout.lock().unwrap().flush()
    }
}

/// `func (c *stdioConn) Close() error` — closes stdin first, then stdout;
/// the first error wins.
impl IoClose for StdioConn {
    fn close(&self) -> io::Result<()> {
        let r1 = self.stdin.lock().unwrap().close_read();
        let r2 = self.stdout.lock().unwrap().close_write();
        r1.and(r2)
    }
}
