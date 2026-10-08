// Ported from tsc/internal/ipc/conn_async_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `net.Pipe()` → `UnixStream::pair()` on unix and a loopback TCP pair on
//   Windows (`&UnixStream`/`&TcpStream` both implement `Read`/`Write`).
// - `chan struct{}` used as a broadcast (`close(ch)`) → `Broadcast`
//   (`Mutex<bool>` + `Condvar`); buffered channels → `mpsc::sync_channel`.
// - `go conn.Run(ctx)` → `thread::scope` + `s.spawn` where the test joins the
//   result; `io.Copy(io.Discard, server)` and the `WithTimeout` cancel stay
//   *unscoped* `thread::spawn`s, since Go goroutines outlive the test and a
//   scoped join would deadlock waiting on the peer.
// - `t.Context()` → `Context::background()`.

use std::collections::VecDeque;
use std::io;
use std::io::{Read, Write};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex, mpsc};
use std::thread;
use std::time::Duration;

use tsc_core::context::Context;
use tsc_json as json;
use tsc_jsonrpc as jsonrpc;

use crate::{
    AsyncConn, Error, Handler, IoClose, Message, Protocol, new_async_conn, new_json_rpc_protocol,
};

/// `net.Pipe()` — an in-memory bidirectional stream pair.
#[cfg(unix)]
type PipeStream = std::os::unix::net::UnixStream;
#[cfg(unix)]
fn pipe_pair() -> (PipeStream, PipeStream) {
    PipeStream::pair().unwrap()
}

/// `net.Pipe()` on Windows — loopback TCP (named pipes need `winio`).
#[cfg(windows)]
type PipeStream = std::net::TcpStream;
#[cfg(windows)]
fn pipe_pair() -> (PipeStream, PipeStream) {
    let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
    let a = std::net::TcpStream::connect(listener.local_addr().unwrap()).unwrap();
    let (b, _) = listener.accept().unwrap();
    (a, b)
}

/// A `chan struct{}` that is `close`d to broadcast to all receivers —
/// `Mutex<bool>` + `Condvar`.
pub(crate) struct Broadcast {
    closed: Mutex<bool>,
    cv: Condvar,
}

impl Broadcast {
    pub(crate) fn new() -> Broadcast {
        Broadcast {
            closed: Mutex::new(false),
            cv: Condvar::new(),
        }
    }

    /// `close(ch)` — idempotent, like `sync.Once`-guarded closes in the Go
    /// test types.
    pub(crate) fn close(&self) {
        *self.closed.lock().unwrap() = true;
        self.cv.notify_all();
    }

    /// `<-ch` on a closed channel.
    pub(crate) fn wait(&self) {
        let mut closed = self.closed.lock().unwrap();
        while !*closed {
            closed = self.cv.wait(closed).unwrap();
        }
    }

    /// `select { case <-ch: true; default: false }`.
    pub(crate) fn is_closed(&self) -> bool {
        *self.closed.lock().unwrap()
    }
}

/// `defer func() { select { <-release: default: close(release) } }`.
struct ReleaseGuard(Arc<Broadcast>);

impl Drop for ReleaseGuard {
    fn drop(&mut self) {
        if !self.0.is_closed() {
            self.0.close();
        }
    }
}

/// `noOpHandler`
pub(crate) struct NoOpHandler;

impl Handler for NoOpHandler {
    fn handle_request(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<Option<json::Value>, Box<dyn std::error::Error + Send + Sync>> {
        Ok(None)
    }

    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

/// `queuedProtocol` — returns queued messages then `io.EOF`; writes return
/// `responseErr`.
pub(crate) struct QueuedProtocol {
    messages: Mutex<VecDeque<Message>>,
    response_err: Option<Error>,
}

impl Protocol for QueuedProtocol {
    fn read_message(&self) -> Result<Message, Error> {
        match self.messages.lock().unwrap().pop_front() {
            Some(m) => Ok(m),
            // `io.EOF`
            None => Err(io::Error::new(io::ErrorKind::UnexpectedEof, "EOF").into()),
        }
    }

    fn write_request(
        &self,
        _id: Option<&jsonrpc::ID>,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn write_notification(&self, _method: &str, _params: Option<json::Value>) -> Result<(), Error> {
        Ok(())
    }

    fn write_response(
        &self,
        _id: Option<&jsonrpc::ID>,
        _result: Option<json::Value>,
    ) -> Result<(), Error> {
        match &self.response_err {
            Some(e) => Err(e.clone()),
            None => Ok(()),
        }
    }

    fn write_error(
        &self,
        _id: Option<&jsonrpc::ID>,
        _err: &jsonrpc::ResponseError,
    ) -> Result<(), Error> {
        match &self.response_err {
            Some(e) => Err(e.clone()),
            None => Ok(()),
        }
    }
}

/// `blockingHandler` — signals `started` then blocks on `release`.
struct BlockingHandler {
    started: mpsc::SyncSender<()>,
    release: Arc<Broadcast>,
}

impl Handler for BlockingHandler {
    fn handle_request(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<Option<json::Value>, Box<dyn std::error::Error + Send + Sync>> {
        let _ = self.started.send(());
        self.release.wait();
        Ok(None)
    }

    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        let _ = self.started.send(());
        self.release.wait();
        Ok(())
    }
}

/// `contextHandler` — blocks until the context is cancelled, then returns
/// `ctx.Err()`.
struct ContextHandler;

impl Handler for ContextHandler {
    fn handle_request(
        &self,
        ctx: &Context,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<Option<json::Value>, Box<dyn std::error::Error + Send + Sync>> {
        ctx.wait_cancelled();
        Err(Box::new(Error::ContextCanceled))
    }

    fn handle_notification(
        &self,
        ctx: &Context,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        ctx.wait_cancelled();
        Err(Box::new(Error::ContextCanceled))
    }
}

/// `closeSignal` — an `io.ReadWriteCloser` whose `Close` broadcasts on a
/// channel (Go `closed chan struct{}` + `sync.Once`).
struct CloseSignalRwc {
    broadcast: Arc<Broadcast>,
}

impl CloseSignalRwc {
    fn new() -> CloseSignalRwc {
        CloseSignalRwc {
            broadcast: Arc::new(Broadcast::new()),
        }
    }
}

/// `Read` — returns `io.EOF`.
impl io::Read for &CloseSignalRwc {
    fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
        Ok(0)
    }
}

/// `Write` — discards.
impl io::Write for &CloseSignalRwc {
    fn write(&mut self, p: &[u8]) -> io::Result<usize> {
        Ok(p.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// `Close` — `c.once.Do(func() { close(c.closed) })`.
impl IoClose for CloseSignalRwc {
    fn close(&self) -> io::Result<()> {
        self.broadcast.close();
        Ok(())
    }
}

/// `failingResponseProtocol` — returns one request, then blocks on `closed`
/// and reports `io.ErrClosedPipe`; writes fail with `responseErr`.
struct FailingResponseProtocol {
    closed: Arc<Broadcast>,
    request_read: AtomicBool,
    response_err: Option<Error>,
}

impl Protocol for FailingResponseProtocol {
    fn read_message(&self) -> Result<Message, Error> {
        if !self.request_read.swap(true, Ordering::SeqCst) {
            return Ok(Message {
                id: Some(jsonrpc::new_id_int(1)),
                method: "transform".to_string(),
                ..Default::default()
            });
        }
        self.closed.wait();
        // `io.ErrClosedPipe`
        Err(io::Error::new(io::ErrorKind::BrokenPipe, "io: read/write on closed pipe").into())
    }

    fn write_request(
        &self,
        _id: Option<&jsonrpc::ID>,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<(), Error> {
        Ok(())
    }

    fn write_notification(&self, _method: &str, _params: Option<json::Value>) -> Result<(), Error> {
        Ok(())
    }

    fn write_response(
        &self,
        _id: Option<&jsonrpc::ID>,
        _result: Option<json::Value>,
    ) -> Result<(), Error> {
        match &self.response_err {
            Some(e) => Err(e.clone()),
            None => Ok(()),
        }
    }

    fn write_error(
        &self,
        _id: Option<&jsonrpc::ID>,
        _err: &jsonrpc::ResponseError,
    ) -> Result<(), Error> {
        match &self.response_err {
            Some(e) => Err(e.clone()),
            None => Ok(()),
        }
    }
}

fn request_message(method: &str) -> Message {
    Message {
        id: Some(jsonrpc::new_id_string("1")),
        method: method.to_string(),
        ..Default::default()
    }
}

fn notification_message(method: &str) -> Message {
    Message {
        method: method.to_string(),
        ..Default::default()
    }
}

/// `TestAsyncConnRunWaitsForHandlers`
#[test]
fn run_waits_for_handlers() {
    let protocol = QueuedProtocol {
        messages: Mutex::new(VecDeque::from([
            request_message("request"),
            notification_message("notification"),
        ])),
        response_err: None,
    };
    let (started_tx, started_rx) = mpsc::sync_channel(2);
    let release = Arc::new(Broadcast::new());
    let handler = BlockingHandler {
        started: started_tx,
        release: release.clone(),
    };
    let conn = AsyncConn::new_async_conn_with_protocol(None, Arc::new(protocol), Arc::new(handler));
    let ctx = Context::background();

    let (run_tx, run_rx) = mpsc::sync_channel(1);
    thread::scope(|s| {
        let conn = &conn;
        let ctx = &ctx;
        s.spawn(move || {
            let _ = run_tx.send(conn.run(ctx));
        });

        started_rx.recv().unwrap();
        started_rx.recv().unwrap();
        assert!(
            run_rx.try_recv().is_err(),
            "Run returned while handlers were active"
        );

        release.close();
        assert!(run_rx.recv().unwrap().is_ok());
    });
}

/// `TestAsyncConnRunCancelsHandlersOnEOF`
#[test]
fn run_cancels_handlers_on_eof() {
    let protocol = QueuedProtocol {
        messages: Mutex::new(VecDeque::from([request_message("request")])),
        response_err: None,
    };
    let conn =
        AsyncConn::new_async_conn_with_protocol(None, Arc::new(protocol), Arc::new(ContextHandler));
    let ctx = Context::background();

    let (run_tx, run_rx) = mpsc::sync_channel(1);
    thread::scope(|s| {
        let conn = &conn;
        let ctx = &ctx;
        s.spawn(move || {
            let _ = run_tx.send(conn.run(ctx));
        });

        match run_rx.recv_timeout(Duration::from_secs(1)) {
            Ok(r) => assert!(r.is_ok()),
            Err(_) => panic!("Run did not cancel active handlers after EOF"),
        }
    });
}

/// `TestAsyncConnResponseWriteFailureWithNilTransport`
#[test]
fn response_write_failure_with_nil_transport() {
    let response_err = Error::Message("response write failed".to_string());
    let protocol = QueuedProtocol {
        messages: Mutex::new(VecDeque::from([request_message("request")])),
        response_err: Some(response_err.clone()),
    };
    let conn =
        AsyncConn::new_async_conn_with_protocol(None, Arc::new(protocol), Arc::new(NoOpHandler));

    let err = conn.run(&Context::background()).unwrap_err();
    assert!(
        err.is(&response_err),
        "expected response write error, got {err}"
    );
}

/// `TestAsyncConnCallReturnsWhenPeerCloses`
#[test]
fn call_returns_when_peer_closes() {
    let (client, server) = pipe_pair();
    let client = Arc::new(client);
    let conn = new_async_conn(client.clone(), Arc::new(NoOpHandler));
    let ctx = Context::background();

    let (run_tx, run_rx) = mpsc::sync_channel(1);
    let (call_tx, call_rx) = mpsc::sync_channel::<Result<Option<json::Value>, Error>>(1);
    thread::scope(|s| {
        let conn = &conn;
        let ctx = &ctx;
        s.spawn(move || {
            let _ = run_tx.send(conn.run(ctx));
        });
        s.spawn(move || {
            let _ = call_tx.send(conn.call(ctx, "transform", None));
        });

        let mut buf = [0u8; 1024];
        (&server).read(&mut buf).unwrap();
        // `server.Close()`
        server.shutdown(std::net::Shutdown::Both).unwrap();
        assert!(run_rx.recv().unwrap().is_ok());
        let err = call_rx.recv().unwrap().unwrap_err();
        assert!(err.is(&Error::ConnClosed));
    });
    // `client.Close()`
    client.close().unwrap();
}

/// `TestAsyncConnCallAfterReadLoopFailureReturnsImmediately`
#[test]
fn call_after_read_loop_failure_returns_immediately() {
    let (client, server) = pipe_pair();
    let client = Arc::new(client);
    let conn = new_async_conn(client.clone(), Arc::new(NoOpHandler));
    let ctx = Context::background();

    let (run_tx, run_rx) = mpsc::sync_channel(1);
    thread::scope(|s| {
        let conn = &conn;
        let ctx = &ctx;
        s.spawn(move || {
            let _ = run_tx.send(conn.run(ctx));
        });

        let mut server_w = &server;
        server_w.write_all(b"oops\n").unwrap();
        let err = run_rx.recv().unwrap().unwrap_err();
        assert!(err.to_string().contains("invalid header"), "got {err}");

        // `go io.Copy(io.Discard, server)` — unscoped, since the Go goroutine
        // outlives the test; the drain ends when the client is closed below.
        thread::spawn(move || {
            let mut s = &server;
            let _ = io::copy(&mut s, &mut io::sink());
        });

        // `context.WithTimeout(t.Context(), time.Second)`
        let (tctx, cancel) = ctx.with_cancel();
        thread::spawn(move || {
            thread::sleep(Duration::from_secs(1));
            cancel.cancel();
        });

        let err = conn.call(&tctx, "transform", None).unwrap_err();
        assert!(
            err.is(&Error::ConnClosed),
            "expected ErrConnClosed, got {err}"
        );
        assert!(
            !tctx.is_cancelled(),
            "call waited for its context deadline: {err}"
        );
        let err = conn.notify(&tctx, "changed", None).unwrap_err();
        assert!(
            err.is(&Error::ConnClosed),
            "expected ErrConnClosed, got {err}"
        );
    });
    // `defer client.Close()` / `defer server.Close()`
    client.close().unwrap();
}

/// `TestAsyncConnTerminalErrorIncludesResponseWriteFailure`
#[test]
fn terminal_error_includes_response_write_failure() {
    let response_err = Error::Message("response write failed".to_string());
    let rwc = Arc::new(CloseSignalRwc::new());
    let protocol = FailingResponseProtocol {
        closed: rwc.broadcast.clone(),
        request_read: AtomicBool::new(false),
        response_err: Some(response_err.clone()),
    };
    let rwc_dyn: Arc<dyn IoClose> = rwc.clone();
    let conn = AsyncConn::new_async_conn_with_protocol(
        Some(rwc_dyn),
        Arc::new(protocol),
        Arc::new(NoOpHandler),
    );

    let err = conn.run(&Context::background()).unwrap_err();
    assert!(
        err.is(&response_err),
        "expected response write error, got {err}"
    );
    let err = conn
        .call(&Context::background(), "transform", None)
        .unwrap_err();
    assert!(
        err.is(&response_err),
        "expected terminal response write error, got {err}"
    );
    assert_eq!(err.to_string().matches("response write failed").count(), 1);
}

/// `TestAsyncConnRunWaitsForRequestAfterPeerCloses`
#[test]
fn run_waits_for_request_after_peer_closes() {
    let (client, server) = pipe_pair();
    let client = Arc::new(client);
    let (started_tx, started_rx) = mpsc::sync_channel(1);
    let release = Arc::new(Broadcast::new());
    // `defer func() { select { <-handler.release: default: close(...) } }`
    let _release_guard = ReleaseGuard(release.clone());
    let handler = BlockingHandler {
        started: started_tx,
        release: release.clone(),
    };
    let conn = new_async_conn(Arc::new(server), Arc::new(handler));
    let ctx = Context::background();

    let (run_tx, run_rx) = mpsc::sync_channel(1);
    thread::scope(|s| {
        let conn = &conn;
        let ctx = &ctx;
        s.spawn(move || {
            let _ = run_tx.send(conn.run(ctx));
        });

        let client_protocol = new_json_rpc_protocol(client.clone());
        client_protocol
            .write_request(Some(&jsonrpc::new_id_int(1)), "transform", None)
            .unwrap();
        match started_rx.recv_timeout(Duration::from_secs(1)) {
            Ok(()) => {}
            Err(_) => panic!("request handler did not start"),
        }
        // `client.Close()`
        client.close().unwrap();

        let handler_blocked = run_rx.recv_timeout(Duration::from_millis(100)).is_err();
        assert!(
            handler_blocked,
            "connection stopped while request handler was blocked"
        );

        release.close();
        match run_rx.recv_timeout(Duration::from_secs(1)) {
            Ok(Err(e)) => {
                assert!(
                    e.to_string().contains("ipc: failed to write response"),
                    "{e}"
                );
                let e = conn.call(ctx, "transform", None).unwrap_err();
                assert!(
                    e.to_string().contains("ipc: failed to write response"),
                    "{e}"
                );
                let e = conn.notify(ctx, "changed", None).unwrap_err();
                assert!(
                    e.to_string().contains("ipc: failed to write response"),
                    "{e}"
                );
            }
            Ok(Ok(())) => panic!("connection returned cleanly while a handler failed"),
            Err(_) => panic!("connection did not stop after request handler completed"),
        }
    });
    // `defer server.Close()` — the conn owns the server stream; dropping it
    // (and its `IoClose` on the request error path) is the close.
}
