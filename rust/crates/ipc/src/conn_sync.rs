// Ported from tsc/internal/ipc/conn_sync.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `mu sync.Mutex` serializing "all protocol operations" becomes
//   `Mutex<()>` — the `Protocol` itself is already internally synchronized
//   for `&self` access; the mutex is the explicit write/read pairing token
//   Go needs for `Call`'s write-then-read atomicity and for releasing the
//   protocol during nested `handleRequest` (guard drop + re-lock).
// - `recover()` → `panic::catch_unwind` + `Backtrace` for `debug.Stack()` —
//   see conn_async.rs for the same pattern.
// - `ctx.Err()` → `Context::is_cancelled()` → `Error::ContextCanceled`.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::{Arc, Mutex};

use tsc_core::context::Context;
use tsc_json as json;
use tsc_jsonrpc as jsonrpc;

use crate::conn_async::panic_payload_string;
use crate::timing::{
    METHOD_GET_SERVER_TIMING, METHOD_RESET_SERVER_TIMING, TimingCollector, new_timing_collector,
    server_timing_snapshot,
};
use crate::{Conn, Error, Handler, IoClose, Protocol, marshal_params};

/// `type SyncConn struct` — bidirectional communication with synchronous
/// request handling. Requests are handled one at a time inline, and outgoing
/// calls are serialized.
pub struct SyncConn {
    /// `rwc io.ReadWriteCloser` — stored for parity with Go; unused, as in
    /// the Go `SyncConn`.
    #[allow(dead_code)]
    rwc: Option<Arc<dyn IoClose>>,
    /// `protocol Protocol`
    protocol: Arc<dyn Protocol>,
    /// `handler Handler`
    handler: Arc<dyn Handler>,

    /// `timing *timingCollector` — see `AsyncConn::timing`.
    timing: Mutex<Option<Arc<TimingCollector>>>,

    /// `mu sync.Mutex` — serializes all protocol operations (reads and
    /// writes), so concurrent calls from handler threads (e.g., project code
    /// spawning threads that invoke filesystem callbacks) don't corrupt the
    /// stream.
    mu: Mutex<()>,
}

impl SyncConn {
    /// `NewSyncConn(rwc, protocol, handler)`
    pub fn new_sync_conn(
        rwc: Option<Arc<dyn IoClose>>,
        protocol: Arc<dyn Protocol>,
        handler: Arc<dyn Handler>,
    ) -> SyncConn {
        SyncConn {
            rwc,
            protocol,
            handler,
            timing: Mutex::new(None),
            mu: Mutex::new(()),
        }
    }

    /// `SetCollectTiming`
    pub fn set_collect_timing(&self, enabled: bool) {
        *self.timing.lock().unwrap() = if enabled {
            Some(Arc::new(new_timing_collector()))
        } else {
            None
        };
    }

    /// `Run` — processes messages until the context is cancelled or an
    /// error occurs.
    pub fn run(&self, ctx: &Context) -> Result<(), Error> {
        loop {
            if ctx.is_cancelled() {
                return Err(Error::ContextCanceled);
            }

            let read = {
                let _g = self.mu.lock().unwrap();
                self.protocol.read_message()
            };

            let msg = match read {
                Err(e) if e.is_eof() => return Ok(()),
                Err(e) => return Err(e),
                Ok(m) => m,
            };

            if msg.is_request() {
                self.handle_request(ctx, &msg)?;
            } else if msg.is_notification() {
                self.handle_notification(ctx, &msg);
            } else {
                // Responses are not expected in the main loop — they are
                // read inline by `call`.
                return Err(Error::Message(
                    "ipc: unexpected response message in sync connection".to_string(),
                ));
            }
        }
    }

    /// `handleRequest` — processes an incoming request. See
    /// [`crate::AsyncConn`] for the identical structure; `c.mu` here replaces
    /// `c.writeMu` there.
    fn handle_request(&self, ctx: &Context, msg: &crate::Message) -> Result<(), Error> {
        // Meta-requests for collected server timing — answered directly and
        // not themselves recorded.
        match msg.method.as_str() {
            METHOD_GET_SERVER_TIMING => {
                let snap = server_timing_snapshot(self.timing.lock().unwrap().as_deref());
                let result = marshal_params(&snap).map_err(|e| {
                    Error::wrapped(
                        format!("ipc: failed to write server timing response: {e}"),
                        e,
                    )
                })?;
                let write_res = {
                    let _g = self.mu.lock().unwrap();
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
                if let Some(t) = self.timing.lock().unwrap().as_ref() {
                    t.reset();
                }
                let write_res = {
                    let _g = self.mu.lock().unwrap();
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

        let timing = self.timing.lock().unwrap().clone();
        let start = timing.is_some().then(std::time::Instant::now);

        // `defer recover()` — see `AsyncConn::handle_request`.
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            self.handler
                .handle_request(ctx, &msg.method, msg.params.clone())
        }));

        let (result, handler_err) = match outcome {
            Ok(Ok(result)) => (result, None),
            Ok(Err(e)) => (None, Some(e.to_string())),
            Err(payload) => {
                let panic_msg = panic_payload_string(&payload);
                let stack = std::backtrace::Backtrace::force_capture();
                let message = format!("panic: {panic_msg}\n{stack}");
                let write_err = {
                    let _g = self.mu.lock().unwrap();
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

        let _g = self.mu.lock().unwrap();
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
        drop(_g);

        write_err.map_err(|e| Error::wrapped(format!("ipc: failed to write response: {e}"), e))
    }

    /// `handleNotification`
    fn handle_notification(&self, ctx: &Context, msg: &crate::Message) {
        let _ = self
            .handler
            .handle_notification(ctx, &msg.method, msg.params.clone());
    }

    /// `Call` — sends a request to the client and waits for a response. Safe
    /// to call from multiple threads — calls are serialized.
    pub fn call(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<Option<json::Value>, Error> {
        // Serialize all `Call` operations. This is critical because:
        // 1. The msgpack protocol uses method names as response IDs
        // 2. The handler code (project internals) may spawn threads that
        //    call filesystem callbacks concurrently
        // 3. Write/read pairs must stay atomic
        let mut guard = self.mu.lock().unwrap();

        let id = jsonrpc::new_id_string(method);

        self.protocol.write_request(Some(&id), method, params)?;

        if ctx.is_cancelled() {
            return Err(Error::ContextCanceled);
        }

        loop {
            // Read the response inline.
            let msg = self.protocol.read_message()?;

            if msg.is_response() && msg.id.as_ref().is_some_and(|id| id.to_string() == method) {
                if let Some(err) = &msg.error {
                    return Err(Error::Remote {
                        code: err.code,
                        message: err.message.clone(),
                    });
                }
                return Ok(msg.result);
            }
            if msg.is_request() {
                // A synchronous client callback may make a nested API
                // request. Release the protocol lock while handling it so
                // nested callbacks can proceed (`c.mu.Unlock()`/`Lock()`).
                drop(guard);
                let result = self.handle_request(ctx, &msg);
                guard = self.mu.lock().unwrap();
                result?;
                continue;
            }
            if msg.is_notification() {
                drop(guard);
                self.handle_notification(ctx, &msg);
                guard = self.mu.lock().unwrap();
                continue;
            }
            return Err(Error::Message(format!(
                "ipc: unexpected message while waiting for {method:?} response"
            )));
        }
    }

    /// `Notify` — sends a notification to the client (no response expected).
    pub fn notify(
        &self,
        _ctx: &Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<(), Error> {
        let _g = self.mu.lock().unwrap();
        self.protocol.write_notification(method, params)
    }
}

impl Conn for SyncConn {
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
