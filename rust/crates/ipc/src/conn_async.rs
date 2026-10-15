// Ported from tsc/internal/ipc/conn_async.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `pending map[jsonrpc.ID]chan *Message` → `HashMap<PendingKey,
//   mpsc::SyncSender<Message>>`. `close(ch)` becomes dropping the sender —
//   the call side sees `RecvError` like Go's `ok == false`. `PendingKey` is
//   `(id.to_string(), id.try_int())`, injective because an `ID` is exactly a
//   (string, int32) pair in Go.
// - `handlers sync.WaitGroup` + `c.handlers.Go` → `std::thread::scope` —
//   the implicit scope join is `handlers.Wait()`.
// - `requestErrors chan error` (buffered 1) → `mpsc::sync_channel(1)`; only
//   the first terminal-cause recorder ever sends, so `send` never blocks.
// - `ctx.Done()` inside `Call`'s `select` → a `recv_timeout` poll on
//   `ctx.is_cancelled()` (the ported `Context` has no multi-wait); wake-up
//   is ≤ `CALL_POLL_INTERVAL` instead of select-instant.
// - `recover()` → `panic::catch_unwind` + `std::backtrace::Backtrace` for
//   `debug.Stack()`. The default panic hook still prints to stderr (Go's
//   recover suppresses it) — cosmetic only.

use std::backtrace::Backtrace;
use std::collections::HashMap;
use std::io;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicI64, Ordering};
use std::sync::{Arc, Mutex, mpsc};
use std::thread;
use std::time::Duration;

use tsc_core::context::Context;
use tsc_json as json;
use tsc_jsonrpc as jsonrpc;

use crate::timing::{
    METHOD_GET_SERVER_TIMING, METHOD_RESET_SERVER_TIMING, TimingCollector, new_timing_collector,
    server_timing_snapshot,
};
use crate::{Conn, Error, Handler, IoClose, Message, Protocol, marshal_params};

/// `select` wake-up granularity for `ctx.Done()` inside `call` — see header.
const CALL_POLL_INTERVAL: Duration = Duration::from_millis(10);

/// `map` key for `pending` — `jsonrpc.ID` isn't `Hash`, and its (str, int32)
/// pair maps injectively to `(Display, try_int())`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct PendingKey(String, Option<i32>);

fn pending_key(id: &jsonrpc::ID) -> PendingKey {
    PendingKey(id.to_string(), id.try_int())
}

/// The `pending` map plus the terminal-error state Go keeps under
/// `pendingMu`.
#[derive(Default)]
struct PendingState {
    /// `pending map[jsonrpc.ID]chan *Message`
    map: HashMap<PendingKey, mpsc::SyncSender<Message>>,
    /// `terminal error` — `None` before the read loop exits; set to
    /// `ConnClosed` (or `Joined(ConnClosed, cause)`) afterwards.
    terminal: Option<Arc<Error>>,
    /// `hasCause bool`
    has_cause: bool,
}

/// `type AsyncConn struct` — bidirectional JSON-RPC communication with async
/// request handling. Each incoming request is handled on its own thread,
/// allowing concurrent processing. This is the standard implementation for
/// LSP-style JSON-RPC protocols.
pub struct AsyncConn {
    /// `rwc io.ReadWriteCloser` — only `Close` is used once the protocol is
    /// built; `None` where Go callers pass nil (tests).
    rwc: Option<Arc<dyn IoClose>>,
    /// `protocol Protocol`
    protocol: Arc<dyn Protocol>,
    /// `handler Handler`
    handler: Arc<dyn Handler>,

    /// `timing *timingCollector` — accumulates wall-clock time spent handling
    /// each request; clients retrieve it via `getServerTiming`. `Mutex`
    /// replaces Go's unsynchronized pointer load.
    timing: Mutex<Option<Arc<TimingCollector>>>,

    /// `seq atomic.Int64` — for server→client requests.
    seq: AtomicI64,
    /// `pending` + `terminal` + `hasCause` under `pendingMu`.
    pending: Mutex<PendingState>,
    /// `writeMu sync.Mutex`
    write_mu: Mutex<()>,
    // `handlers sync.WaitGroup` — replaced by `thread::scope` in `run`.
}

/// `NewAsyncConn(rwc, handler)` — uses `JsonRpcProtocol` (LSP-style
/// Content-Length framing) over `rwc`.
///
/// `S` must be usable through `&self` for both `Read` and `Write` — std
/// provides `impl Read/Write for &UnixStream`/`&TcpStream`; [`crate::StdioConn`]
/// does the same via per-half mutexes.
pub fn new_async_conn<S>(rwc: Arc<S>, handler: Arc<dyn Handler>) -> AsyncConn
where
    S: IoClose + Send + Sync + 'static,
    for<'a> &'a S: io::Read + io::Write,
{
    let rwc_dyn: Arc<dyn IoClose> = rwc.clone();
    AsyncConn::new_async_conn_with_protocol(
        Some(rwc_dyn),
        Arc::new(crate::new_json_rpc_protocol(rwc)),
        handler,
    )
}

impl AsyncConn {
    /// `NewAsyncConnWithProtocol(rwc, protocol, handler)`
    pub fn new_async_conn_with_protocol(
        rwc: Option<Arc<dyn IoClose>>,
        protocol: Arc<dyn Protocol>,
        handler: Arc<dyn Handler>,
    ) -> AsyncConn {
        AsyncConn {
            rwc,
            protocol,
            handler,
            timing: Mutex::new(None),
            seq: AtomicI64::new(0),
            pending: Mutex::new(PendingState::default()),
            write_mu: Mutex::new(()),
        }
    }

    /// `SetCollectTiming` — enables or disables per-request server
    /// processing-time measurement.
    pub fn set_collect_timing(&self, enabled: bool) {
        *self.timing.lock().unwrap() = if enabled {
            Some(Arc::new(new_timing_collector()))
        } else {
            None
        };
    }

    /// The current collector — `c.timing`.
    fn timing(&self) -> Option<Arc<TimingCollector>> {
        self.timing.lock().unwrap().clone()
    }

    /// `Run` — processes messages until the context is cancelled or an
    /// error occurs.
    pub fn run(&self, ctx: &Context) -> Result<(), Error> {
        let (handler_ctx, cancel_handlers) = ctx.with_cancel();
        let (request_errors_tx, request_errors_rx) = mpsc::sync_channel::<Error>(1);
        let mut err = thread::scope(|s| {
            let res = self.read_loop(ctx, &handler_ctx, s, &request_errors_tx);
            // The deferred block, in order: `closePendingCalls(err)`,
            // `cancelHandlers()`, `handlers.Wait()` (the scope join).
            self.close_pending_calls(res.as_ref().err().cloned());
            cancel_handlers.cancel();
            res
        });
        // After `handlers.Wait()` — drain `requestErrors` and join.
        if let Ok(request_err) = request_errors_rx.try_recv() {
            err = Err(match err {
                // `errors.Join(err, requestErr)` — nil err collapses.
                Ok(()) => request_err,
                Err(e) => Error::Joined(Box::new(e), Box::new(request_err)),
            });
        }
        err
    }

    /// The `Run` read loop, inside `thread::scope` so spawned handlers are
    /// joined when it exits.
    fn read_loop<'scope>(
        &'scope self,
        ctx: &Context,
        handler_ctx: &'scope Context,
        s: &'scope thread::Scope<'scope, '_>,
        request_errors_tx: &mpsc::SyncSender<Error>,
    ) -> Result<(), Error> {
        loop {
            if ctx.is_cancelled() {
                return Err(Error::ContextCanceled);
            }

            let msg = match self.protocol.read_message() {
                Err(e) if e.is_eof() => return Ok(()),
                Err(e) => return Err(e),
                Ok(m) => m,
            };

            if msg.is_response() {
                self.handle_response(msg);
            } else if msg.is_request() {
                let handler_ctx = handler_ctx.clone();
                let tx = request_errors_tx.clone();
                s.spawn(move || {
                    if let Err(request_err) = self.handle_request(&handler_ctx, &msg) {
                        if self.record_request_error(request_err, &tx) {
                            if let Some(rwc) = &self.rwc {
                                let _ = rwc.close();
                            }
                        }
                    }
                });
            } else if msg.is_notification() {
                let handler_ctx = handler_ctx.clone();
                s.spawn(move || self.handle_notification(&handler_ctx, &msg));
            }
        }
    }

    /// `closePendingCalls` — records that the read loop has exited and
    /// unblocks requests waiting for a response.
    fn close_pending_calls(&self, run_err: Option<Error>) {
        let mut pending = self.pending.lock().unwrap();
        Self::record_terminal_error_locked(&mut pending, run_err);
        Self::close_pending_calls_locked(&mut pending);
    }

    /// `recordRequestError`
    fn record_request_error(
        &self,
        request_err: Error,
        request_errors: &mpsc::SyncSender<Error>,
    ) -> bool {
        let mut pending = self.pending.lock().unwrap();
        if !Self::record_terminal_error_locked(&mut pending, Some(request_err.clone())) {
            return false;
        }
        // Buffered 1 and only the first recorder reaches this — never blocks.
        let _ = request_errors.send(request_err);
        Self::close_pending_calls_locked(&mut pending);
        true
    }

    /// `recordTerminalErrorLocked` — returns true only when `terminal_err`
    /// was newly joined in as the terminal cause.
    fn record_terminal_error_locked(
        pending: &mut PendingState,
        terminal_err: Option<Error>,
    ) -> bool {
        // Computed ahead because assigning `pending.terminal` while the match
        // scrutinee borrows it would conflict — value semantics differ from
        // Go's interface assignment.
        let (new_terminal, newly_caused) = match &pending.terminal {
            None => match terminal_err {
                // `errors.Join(ErrConnClosed, terminalErr)`
                Some(e) => (
                    Some(Error::Joined(Box::new(Error::ConnClosed), Box::new(e))),
                    true,
                ),
                None => (Some(Error::ConnClosed), false),
            },
            Some(t) if !pending.has_cause => match terminal_err {
                // `errors.Join(c.terminal, terminalErr)`
                Some(e) => (
                    Some(Error::Joined(Box::new((**t).clone()), Box::new(e))),
                    true,
                ),
                None => (None, false),
            },
            Some(_) => (None, false),
        };
        if let Some(t) = new_terminal {
            pending.terminal = Some(Arc::new(t));
        }
        if newly_caused {
            pending.has_cause = true;
        }
        newly_caused
    }

    /// `closePendingCallsLocked` — dropping each sender closes the channel
    /// (Go: `close(ch)`), unblocking `call`'s `recv` with `RecvError`.
    fn close_pending_calls_locked(pending: &mut PendingState) {
        pending.map.clear();
    }

    /// `handleResponse` — matches a response to a pending request.
    fn handle_response(&self, msg: Message) {
        let Some(id) = msg.id.as_ref() else {
            return; // unreachable: `is_response` requires an ID
        };
        let sender = self.pending.lock().unwrap().map.remove(&pending_key(id));
        if let Some(ch) = sender {
            // `ch <- msg; close(ch)` — send errors only if the caller went
            // away; Go's buffered channel send can't fail, so ignore it.
            let _ = ch.send(msg);
            drop(ch);
        }
    }

    /// `handleRequest` — processes an incoming request.
    fn handle_request(&self, ctx: &Context, msg: &Message) -> Result<(), Error> {
        // Intercept the meta-requests for collected server timing before
        // dispatching to the handler, so they are answered directly and not
        // themselves recorded.
        match msg.method.as_str() {
            METHOD_GET_SERVER_TIMING => {
                let snap = server_timing_snapshot(self.timing().as_deref());
                let result = marshal_params(&snap).map_err(|e| {
                    Error::wrapped(
                        format!("ipc: failed to write server timing response: {e}"),
                        e,
                    )
                })?;
                let write_res = {
                    let _w = self.write_mu.lock().unwrap();
                    self.protocol
                        .write_response(msg.id.as_ref(), Some(result.into()))
                };
                write_res.map_err(|e| {
                    Error::wrapped(
                        format!("ipc: failed to write server timing response: {e}"),
                        e,
                    )
                })?;
                return Ok(());
            }
            METHOD_RESET_SERVER_TIMING => {
                if let Some(t) = self.timing() {
                    t.reset();
                }
                let write_res = {
                    let _w = self.write_mu.lock().unwrap();
                    self.protocol.write_response(msg.id.as_ref(), None)
                };
                write_res.map_err(|e| {
                    Error::wrapped(
                        format!("ipc: failed to write reset server timing response: {e}"),
                        e,
                    )
                })?;
                return Ok(());
            }
            _ => {}
        }

        let timing = self.timing();
        let start = timing.is_some().then(std::time::Instant::now);

        // `defer recover()` — a handler panic becomes an error response with
        // a stack trace, and a failed panic write becomes the return error.
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            self.handler
                .handle_request(ctx, &msg.method, msg.params.clone())
        }));

        let (result, handler_err) = match outcome {
            Ok(Ok(result)) => (result, None),
            Ok(Err(e)) => (None, Some(e.to_string())),
            Err(payload) => {
                let panic_msg = panic_payload_string(&payload);
                let stack = Backtrace::force_capture();
                let message = format!("panic: {panic_msg}\n{stack}");
                let write_err = {
                    let _w = self.write_mu.lock().unwrap();
                    self.protocol.write_error(
                        msg.id.as_ref(),
                        &jsonrpc::ResponseError {
                            code: jsonrpc::CODE_INTERNAL_ERROR,
                            message,
                            data: None,
                        },
                    )
                };
                return match write_err {
                    Ok(()) => Ok(()),
                    Err(e) => Err(Error::wrapped(
                        format!(
                            "ipc: failed to write panic error response: {e} (original panic: {panic_msg})"
                        ),
                        e,
                    )),
                };
            }
        };

        if let Some(t) = &timing {
            t.record(&msg.method, start.unwrap().elapsed());
        }

        let _w = self.write_mu.lock().unwrap();
        let write_err = match handler_err {
            Some(message) => self.protocol.write_error(
                msg.id.as_ref(),
                &jsonrpc::ResponseError {
                    code: jsonrpc::CODE_INTERNAL_ERROR,
                    message,
                    data: None,
                },
            ),
            None => self.protocol.write_response(msg.id.as_ref(), result),
        };
        drop(_w);

        write_err.map_err(|e| Error::wrapped(format!("ipc: failed to write response: {e}"), e))
    }

    /// `handleNotification`
    fn handle_notification(&self, ctx: &Context, msg: &Message) {
        let _ = self
            .handler
            .handle_notification(ctx, &msg.method, msg.params.clone());
    }

    /// `Call` — sends a request to the client and waits for a response.
    pub fn call(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<Option<json::Value>, Error> {
        // `seq.Add(1)` returns the *new* value; `fetch_add` the old — hence +1.
        let id = jsonrpc::new_id_string(&format!(
            "api{}",
            self.seq.fetch_add(1, Ordering::SeqCst) + 1
        ));

        // Register the response channel BEFORE sending the request (Go
        // ordering — avoids the response racing the map insert).
        let (tx, rx) = mpsc::sync_channel::<Message>(1);
        let key = pending_key(&id);
        {
            let mut pending = self.pending.lock().unwrap();
            if let Some(terminal) = &pending.terminal {
                let err = (**terminal).clone();
                drop(pending);
                return Err(err);
            }
            pending.map.insert(key.clone(), tx);
        }

        let result = self.call_await(ctx, method, params, &id, &rx);

        // Go `defer`: remove the pending entry and close its channel
        // (dropping the sender).
        let mut pending = self.pending.lock().unwrap();
        pending.map.remove(&key);

        result
    }

    /// The send-and-wait body of `call`, separated so the pending-entry
    /// removal mirrors Go's `defer` on every path.
    fn call_await(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<json::Value>,
        id: &jsonrpc::ID,
        rx: &mpsc::Receiver<Message>,
    ) -> Result<Option<json::Value>, Error> {
        // Send the request.
        {
            let _w = self.write_mu.lock().unwrap();
            self.protocol.write_request(Some(id), method, params)?;
        }

        loop {
            match rx.recv_timeout(CALL_POLL_INTERVAL) {
                Ok(resp) => {
                    if let Some(err) = &resp.error {
                        return Err(Error::Remote {
                            code: err.code,
                            message: err.message.clone(),
                        });
                    }
                    return Ok(resp.result);
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    // Channel closed by `close_pending_calls*` — return the
                    // terminal error (`c.terminal` is always set first).
                    let terminal = self.pending.lock().unwrap().terminal.clone();
                    return Err(terminal.map(|t| (*t).clone()).unwrap_or(Error::ConnClosed));
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    if ctx.is_cancelled() {
                        return Err(Error::ContextCanceled);
                    }
                }
            }
        }
    }

    /// `Notify` — sends a notification to the client (no response expected).
    pub fn notify(
        &self,
        _ctx: &Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<(), Error> {
        {
            let pending = self.pending.lock().unwrap();
            if let Some(terminal) = &pending.terminal {
                let err = (**terminal).clone();
                drop(pending);
                return Err(err);
            }
        }
        let _w = self.write_mu.lock().unwrap();
        self.protocol.write_notification(method, params)
    }
}

impl Conn for AsyncConn {
    fn run(&self, ctx: &Context) -> Result<(), Error> {
        self.run(ctx)
    }

    fn call(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<Option<json::Value>, Error> {
        self.call(ctx, method, params)
    }

    fn notify(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<(), Error> {
        self.notify(ctx, method, params)
    }
}

/// `%v` of a recovered panic — Go renders the panic value; Rust payloads are
/// usually `&str`/`String`. Shared by `AsyncConn`/`SyncConn`.
pub(crate) fn panic_payload_string(payload: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        // PORT: Go's `%v` prints arbitrary panic values; `{:?}` on the Any
        // is the closest available spelling.
        format!("{payload:?}")
    }
}
