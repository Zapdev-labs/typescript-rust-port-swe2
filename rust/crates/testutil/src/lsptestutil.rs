// Ported from tsc/internal/testutil/lsptestutil/lspclient.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// In-process LSP client for fourslash LSP-mode tests.
//
// PORT notes:
// - `context.Context` → `tsc_core::context::Context`; `t.Context()` (the
//   implicit test context of `*testing.T`) becomes an explicit `ctx`
//   parameter on [new_lsp_client].
// - `testing.T` has no Rust equivalent (crate convention): `t.Fatalf`
//   becomes `Err(crate::Error)` and `assert.NilError` becomes `?`.
// - `io.Pipe()` → [pipe], a Mutex+Condvar byte pipe (same design as
//   `PipeEnd` in contentmappertest.rs, but unidirectional like `io.Pipe`).
// - `lsp.Reader`/`lsp.Writer` on the client side are realized directly on
//   the pipe ends via `lsproto::BaseReader`/`BaseWriter` + `tsc_json`
//   — exactly what Go's `lsp.lspReader`/`lspWriter` do internally. On the
//   server side they are created with `tsc_lsp::to_reader`/`to_writer`.
// - `errgroup` → `std::thread` + `JoinHandle`s joined by the returned
//   cleanup closure; `context.Canceled` filtering is approximated by a
//   message check (see [new_lsp_client]).
// - `map[jsonrpc.ID]chan *ResponseMessage` → a `Vec<(ID, SyncSender)>` under
//   a Mutex — `jsonrpc::ID` does not implement `Hash`, and pending maps are
//   tiny in tests, so a linear scan replaces the hash lookup.
// - `chan *ResponseMessage` (cap 1) → `mpsc::sync_channel(1)`; Go's
//   `select { case ch <- resp: / <-ctx.Done(): }` becomes a cancelled check
//   plus a `try_send` (the channel never fills — one response per ID).
//   `select { case <-ctx.Done(): / case resp := <-ch: }` in
//   [LspClient::wait_for_response] becomes a `recv_timeout` poll loop;
//   `mpsc` has no select-with-ctx equivalent.
//
// PORT(assumption): `tsc_lsp` (tsc/internal/lsp) is ported in parallel and
// is still a skeleton. This module assumes the snake_case Go API:
//   - `tsc_lsp::ServerOptions` with mutable `in_`/`out` fields matching the
//     return types of `to_reader`/`to_writer`;
//   - `tsc_lsp::to_reader(r: impl io::Read)` / `to_writer(w: impl io::Write)`;
//   - `tsc_lsp::new_server(&ServerOptions) -> Arc<tsc_lsp::Server>`;
//   - `Server::run(&self, ctx: &Context) -> Result<(), E: Display>`,
//     `Server::session()`, and
//     `Server::set_compiler_options_for_inferred_projects(&Context, &CompilerOptions)`.
// If the port lands with different shapes (e.g. `new_server` returning
// `Server` rather than `Arc<Server>`), the call sites below need adjusting.

use std::collections::VecDeque;
use std::io;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::mpsc;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

use serde::Serialize;
use serde::de::DeserializeOwned;
use tsc_core::context::{CancelFunc, Context};
use tsc_core::options_generated::CompilerOptions;
use tsc_json as json;
use tsc_jsonrpc as jsonrpc;
use tsc_lsproto as lsproto;

use crate::Error;

/// `io.Pipe` — an in-memory, blocking, unidirectional byte pipe. Writes are
/// buffered and never block (unlike Go's synchronous pipe); closing the
/// writer makes the reader see EOF once the buffer drains, and closing the
/// reader makes writers fail with `BrokenPipe`.
#[derive(Default)]
struct PipeState {
    queue: VecDeque<u8>,
    /// The writing end closed — readers see EOF after the queue drains.
    writer_closed: bool,
    /// The reading end closed — writers fail.
    reader_closed: bool,
}

struct Pipe {
    state: Mutex<PipeState>,
    cvar: Condvar,
}

impl Pipe {
    fn new() -> Arc<Pipe> {
        Arc::new(Pipe {
            state: Mutex::new(PipeState::default()),
            cvar: Condvar::new(),
        })
    }
}

/// The read half of a [pipe].
struct PipeReader(Arc<Pipe>);
/// The write half of a [pipe].
struct PipeWriter(Arc<Pipe>);

/// `io.Pipe()`.
fn pipe() -> (PipeReader, PipeWriter, Arc<Pipe>) {
    let inner = Pipe::new();
    (
        PipeReader(inner.clone()),
        PipeWriter(inner.clone()),
        inner,
    )
}

fn closed_pipe() -> io::Error {
    io::Error::new(io::ErrorKind::BrokenPipe, "io: read/write on closed pipe")
}

impl Pipe {
    /// `PipeWriter.Close` — the reader sees EOF after the queue drains.
    fn close_writer(&self) {
        {
            let mut s = self.state.lock().unwrap();
            s.writer_closed = true;
        }
        self.cvar.notify_all();
    }
}

impl Drop for PipeWriter {
    fn drop(&mut self) {
        self.0.close_writer();
    }
}

impl Drop for PipeReader {
    fn drop(&mut self) {
        let mut s = self.0.state.lock().unwrap();
        s.reader_closed = true;
    }
}

impl io::Read for PipeReader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut s = self.0.state.lock().unwrap();
        loop {
            if s.reader_closed {
                return Err(closed_pipe());
            }
            if !s.queue.is_empty() {
                let n = s.queue.len().min(buf.len());
                for slot in buf.iter_mut().take(n) {
                    *slot = s.queue.pop_front().unwrap();
                }
                return Ok(n);
            }
            if s.writer_closed {
                return Ok(0);
            }
            s = self.0.cvar.wait(s).unwrap();
        }
    }
}

impl io::Write for PipeWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        {
            let mut s = self.0.state.lock().unwrap();
            if s.writer_closed || s.reader_closed {
                return Err(closed_pipe());
            }
            s.queue.extend(buf.iter());
        }
        self.0.cvar.notify_all();
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// `clientTransport` wires a test client to a server using real LSP
/// "Content-Length"-framed JSON streamed over byte pipes, exactly like
/// communication with a real editor. This exercises the full
/// marshal/unmarshal round-trip of every protocol data structure. The two
/// directions are:
///
/// ```text
/// client --(clientOut)--> serverIn --> server
/// server --(serverOut)--> clientIn --> client
/// ```
///
/// PORT: Go stores `lsp.Reader`/`lsp.Writer` endpoints plus close funcs. The
/// client-side endpoints become the concrete `lsproto::BaseReader`/
/// `BaseWriter` halves of `client_transport()`'s return value; only the
/// close halves (pipe inners, to signal EOF to the far reader) live here.
struct ClientTransport {
    /// `closeClientOut` — closes the client->server direction.
    client_out: Arc<Pipe>,
    /// `closeServerOut` — closes the server->client direction.
    server_out: Arc<Pipe>,
}

impl ClientTransport {
    fn close_client_out(&self) {
        self.client_out.close_writer();
    }

    fn close_server_out(&self) {
        self.server_out.close_writer();
    }
}

/// `newClientTransport` — returns the client endpoint halves plus the
/// transport handle; `server_opts.in_`/`server_opts.out` receive the other
/// halves through `tsc_lsp::to_reader`/`to_writer` in [new_lsp_client].
fn client_transport() -> (
    ClientTransport,
    PipeReader, // serverIn — handed to the server via tsc_lsp::to_reader
    PipeWriter, // serverOut — handed to the server via tsc_lsp::to_writer
    lsproto::BaseReader<PipeReader>, // clientIn — framed server->client reads
    lsproto::BaseWriter<PipeWriter>, // clientOut — framed client->server writes
) {
    let (client_to_server_reader, client_to_server_writer, client_out_pipe) = pipe();
    let (server_to_client_reader, server_to_client_writer, server_out_pipe) = pipe();
    (
        ClientTransport {
            client_out: client_out_pipe,
            server_out: server_out_pipe,
        },
        client_to_server_reader,
        server_to_client_writer,
        lsproto::new_base_reader(server_to_client_reader),
        lsproto::new_base_writer(client_to_server_writer),
    )
}

/// `ServerRequestHandler` handles server-initiated requests and returns the
/// response to send back (`None` ~ Go's nil → default MethodNotFound).
pub type ServerRequestHandler =
    Arc<dyn Fn(&Context, &lsproto::RequestMessage) -> Option<lsproto::ResponseMessage> + Send + Sync>;

/// `ServerNotificationHandler` handles server-initiated notifications
/// (e.g., `$/progress`).
pub type ServerNotificationHandler = Arc<dyn Fn(&Context, &lsproto::RequestMessage) + Send + Sync>;

/// `LSPClient` provides infrastructure for communicating with an LSP server
/// in tests.
pub struct LspClient {
    /// `Server *lsp.Server`
    pub server: Arc<tsc_lsp::Server>,
    /// `inputWriter lsp.Writer` — the framed writer on the client->server
    /// pipe.
    input_writer: Mutex<lsproto::BaseWriter<PipeWriter>>,
    /// `outputReader lsp.Reader` — the framed reader on the server->client
    /// pipe. Held in a Mutex so `&LspClient` methods can read.
    output_reader: Mutex<lsproto::BaseReader<PipeReader>>,
    /// `id int32` — `AtomicI32` in place of Go's plain field; `next_id` is
    /// called from the test thread only, but `LspClient` is shared with the
    /// router thread.
    id: AtomicI32,
    ctx: Context,

    // `inputWriterMu` — folded into `input_writer`'s Mutex: it serializes
    // writes to the server. The test thread (sending requests/notifications)
    // and the message_router thread (sending responses to server-initiated
    // requests) both write to the same stream; a single message is written
    // as multiple underlying writes (header, body, flush), so concurrent
    // writers must not interleave.
    /// `onServerRequest` handles server-initiated requests (e.g.,
    /// `workspace/configuration`). If `None`, all server requests receive a
    /// MethodNotFound error.
    on_server_request: Option<ServerRequestHandler>,

    /// `OnServerNotification` handles server-initiated notifications (e.g.,
    /// `$/progress`). If `None`, notifications are ignored.
    ///
    /// PORT: Go's exported field is guarded here by a Mutex because the
    /// router thread reads it while the test thread may still set it.
    pub on_server_notification: Mutex<Option<ServerNotificationHandler>>,

    // Async message handling
    /// `pendingRequests map[jsonrpc.ID]chan *lsproto.ResponseMessage`.
    pending_requests: Mutex<Vec<(jsonrpc::ID, mpsc::SyncSender<lsproto::ResponseMessage>)>>,
}

/// `(*LSPClient).writeToServer` — writes a message to the server,
/// serializing concurrent writers (the Mutex inside `input_writer`).
///
/// PORT: `lsp.lspWriter.Write` marshals the message then frames it; this
/// does the same two steps in place.
fn write_to_server(
    input_writer: &Mutex<lsproto::BaseWriter<PipeWriter>>,
    msg: &lsproto::Message,
) -> Result<(), Error> {
    let data = json::marshal(msg, &[])
        .map_err(|e| Error::new(format!("failed to marshal message: {e}")))?;
    let mut w = input_writer.lock().unwrap();
    w.write(&data)
        .map_err(|e| Error::new(format!("failed to write message: {e}")))
}

/// `NewLSPClient` creates an LSPClient wrapping the given server and pipes.
/// The returned closure is Go's `func() error` cleanup: cancel, close the
/// client->server direction, and wait for both goroutines.
///
/// PORT: `t`/`t.Context()` becomes `ctx` — pass the test's context. The
/// server goroutine runs `server.run` and the router goroutine runs
/// [LspClient::message_router], mirroring the `errgroup`.
pub fn new_lsp_client(
    ctx: &Context,
    mut server_opts: tsc_lsp::ServerOptions,
    on_server_request: Option<ServerRequestHandler>,
) -> (Arc<LspClient>, impl FnOnce() -> Result<(), Error>) {
    let (transport, server_in, server_out, client_in, client_out) = client_transport();
    server_opts.in_ = tsc_lsp::to_reader(server_in);
    server_opts.out = tsc_lsp::to_writer(server_out);

    // PORT(assumption): `new_server` returns `Arc<Server>` (Go `*Server`,
    // matching `project::new_session -> Arc<Session>`).
    let server: Arc<tsc_lsp::Server> = tsc_lsp::new_server(&server_opts);

    let (ctx, cancel): (Context, CancelFunc) = ctx.with_cancel();
    let client = Arc::new(LspClient {
        server: server.clone(),
        input_writer: Mutex::new(client_out),
        output_reader: Mutex::new(client_in),
        id: AtomicI32::new(0),
        ctx: ctx.clone(),
        on_server_request,
        on_server_notification: Mutex::new(None),
        pending_requests: Mutex::new(Vec::new()),
    });

    // Start server goroutine — `g.Go(func() error { defer closeServerOut(); return server.Run(ctx) })`.
    let server_handle = {
        let server = server.clone();
        let ctx = ctx.clone();
        let transport_out = transport.server_out.clone();
        thread::spawn(move || {
            // PORT(assumption): `server.run(&ctx)`; the error is stringified
            // so the JoinHandle has a nameable type regardless of the
            // parallel port's error type.
            let result = server.run(&ctx);
            transport_out.close_writer();
            result.map_err(|e| e.to_string())
        })
    };

    // Start async message router — `g.Go(func() error { return client.MessageRouter(ctx) })`.
    let router_handle = {
        let client = client.clone();
        let ctx = ctx.clone();
        thread::spawn(move || client.message_router(&ctx))
    };

    let cleanup = move || -> Result<(), Error> {
        cancel.cancel();
        transport.close_client_out();

        // `g.Wait()` — join both goroutines; first error wins unless it is
        // `context.Canceled`.
        let server_result = server_handle
            .join()
            .unwrap_or_else(|p| std::panic::resume_unwind(p));
        let router_result = router_handle
            .join()
            .unwrap_or_else(|p| std::panic::resume_unwind(p));
        if let Err(e) = server_result {
            // PORT: `errors.Is(err, context.Canceled)` — the parallel port's
            // error type is unknown, so cancellation is recognized by the
            // `context canceled` message Go's error carries.
            if !e.contains("context canceled") {
                return Err(Error::new(e));
            }
        }
        router_result
    };

    (client, cleanup)
}

impl LspClient {
    /// `NextID` returns the next request ID.
    pub fn next_id(&self) -> i32 {
        self.id.fetch_add(1, Ordering::Relaxed)
    }

    /// `MessageRouter` runs in a goroutine and routes incoming messages from
    /// the server. It handles responses to client requests and
    /// server-initiated requests. It continues draining the output until it
    /// hits EOF, even after context cancellation, to prevent the server's
    /// writeLoop from blocking on a send.
    pub fn message_router(&self, ctx: &Context) -> Result<(), Error> {
        loop {
            let msg = {
                let mut reader = self.output_reader.lock().unwrap();
                match reader.read() {
                    Err(e) => {
                        // `errors.Is(err, io.EOF)`.
                        if e.is_eof() {
                            return Ok(());
                        }
                        if ctx.is_cancelled() {
                            return Ok(());
                        }
                        return Err(Error::new(format!("failed to read message: {e}")));
                    }
                    Ok(data) => match json::unmarshal::<lsproto::Message>(&data, &[]) {
                        Ok(msg) => msg,
                        Err(e) => {
                            // PORT: Go's `lspReader.Read` reports a JSON
                            // unmarshal failure through the same `err`
                            // channel as transport failures — same handling.
                            if ctx.is_cancelled() {
                                return Ok(());
                            }
                            return Err(Error::new(format!("failed to read message: {e}")));
                        }
                    },
                }
            };

            // After context cancellation, keep draining but don't process messages.
            if ctx.is_cancelled() {
                continue;
            }

            // Validate message can be marshaled — `json.MarshalWrite(io.Discard, msg)`.
            if let Err(e) = json::marshal(&msg, &[]) {
                if ctx.is_cancelled() {
                    continue;
                }
                return Err(Error::new(format!(
                    "failed to encode message as JSON: {e}"
                )));
            }

            match msg.kind {
                jsonrpc::MessageKind::Response => {
                    self.handle_response(ctx, msg.as_response());
                }
                jsonrpc::MessageKind::Request => {
                    self.handle_server_request(ctx, msg.as_request())?;
                }
                jsonrpc::MessageKind::Notification => {
                    if let Some(handler) = self.on_server_notification.lock().unwrap().clone() {
                        handler(ctx, msg.as_request());
                    }
                }
            }
        }
    }

    /// `handleResponse` routes a response message to the waiting request
    /// goroutine.
    fn handle_response(&self, ctx: &Context, resp: &lsproto::ResponseMessage) {
        let Some(id) = &resp.id else {
            return;
        };

        let resp_chan = {
            let mut pending = self.pending_requests.lock().unwrap();
            pending
                .iter()
                .position(|(k, _)| k == id)
                .map(|idx| pending.remove(idx).1)
        };

        if let Some(resp_chan) = resp_chan {
            // `select { case respChan <- resp: case <-ctx.Done(): }` — the
            // channel has capacity 1 and is consumed at most once, so the
            // send never blocks; cancellation simply skips it.
            if !ctx.is_cancelled() {
                let _ = resp_chan.try_send(resp.clone());
            }
        }
    }

    /// `handleServerRequest` handles requests initiated by the server (e.g.,
    /// `workspace/configuration`).
    fn handle_server_request(
        &self,
        ctx: &Context,
        req: &lsproto::RequestMessage,
    ) -> Result<(), Error> {
        let mut response = self
            .on_server_request
            .as_ref()
            .and_then(|handler| handler(ctx, req));

        if response.is_none() {
            // Default: unknown server request
            response = Some(lsproto::ResponseMessage {
                id: req.id.clone(),
                jsonrpc: req.jsonrpc,
                result: None,
                error: Some(jsonrpc::ResponseError {
                    code: lsproto::ErrorCode::MethodNotFound.0,
                    message: format!("Unknown method: {}", req.method.as_str()),
                    data: None,
                }),
            });
        }
        let response = response.unwrap();

        // Send response back to server
        if ctx.is_cancelled() {
            return Ok(());
        }

        if let Err(e) = write_to_server(&self.input_writer, &response.message()) {
            if ctx.is_cancelled() {
                return Ok(());
            }
            return Err(Error::new(format!(
                "failed to write server request response: {e}"
            )));
        }
        Ok(())
    }

    /// `WriteMsg` validates and sends a message to the server.
    /// This is an untyped low-level method; prefer [LspClient::send_request]
    /// and [LspClient::send_notification] for typed interactions.
    ///
    /// PORT: `assert.NilError(t, json.MarshalWrite(io.Discard, msg))` folds
    /// into the marshal inside [write_to_server]; both errors surface here.
    pub fn write_msg(&self, msg: &lsproto::Message) -> Result<(), Error> {
        write_to_server(&self.input_writer, msg)
    }

    /// `SendRequest` sends a typed request and waits for the response.
    ///
    /// PORT: Go's `(*lsproto.Message, Resp, bool)` triple is preserved; the
    /// bool is the `UnmarshalResult` success flag and `Resp: Default` stands
    /// in for `*new(Resp)`.
    pub fn send_request<Params, Resp>(
        &self,
        info: &lsproto::RequestInfo<Params, Resp>,
        params: Params,
    ) -> Result<(Option<lsproto::Message>, Resp, bool), Error>
    where
        Params: Serialize,
        Resp: DeserializeOwned + Default,
    {
        let id = self.next_id();
        let req_id = lsproto::new_id(&lsproto::IntegerOrString {
            integer: Some(id),
            string: None,
        });
        let req = info.new_request_message(Some(req_id.clone()), params);

        let Some(resp) = self.send_request_worker(req, &req_id)? else {
            return Ok((None, Resp::default(), false));
        };
        // The result arrives as a raw json.Value; decode it into Resp.
        let result = info.unmarshal_result(resp.result.as_ref());
        let ok = result.is_ok();
        Ok((Some(resp.message()), result.unwrap_or_default(), ok))
    }

    /// `SendRequestAsync` sends a typed request and returns a waiter for its
    /// response.
    pub fn send_request_async<'a, Params, Resp>(
        &'a self,
        info: &'a lsproto::RequestInfo<Params, Resp>,
        params: Params,
    ) -> Result<impl FnOnce() -> Result<(Option<lsproto::Message>, Resp, bool), Error> + 'a, Error>
    where
        Params: Serialize,
        Resp: DeserializeOwned + Default,
    {
        let id = self.next_id();
        let req_id = lsproto::new_id(&lsproto::IntegerOrString {
            integer: Some(id),
            string: None,
        });
        let req = info.new_request_message(Some(req_id.clone()), params);

        let response_chan = self.start_request_worker(req, &req_id)?;
        Ok(move || {
            let Some(resp) = self.wait_for_response(&req_id, response_chan)? else {
                return Ok((None, Resp::default(), false));
            };
            let result = info.unmarshal_result(resp.result.as_ref());
            let ok = result.is_ok();
            Ok((Some(resp.message()), result.unwrap_or_default(), ok))
        })
    }

    /// `SendRequestWorker` — the untyped version of [LspClient::send_request].
    /// Prefer `send_request` when possible. `Ok(None)` ~ Go's `false`.
    pub fn send_request_worker(
        &self,
        req: lsproto::RequestMessage,
        req_id: &jsonrpc::ID,
    ) -> Result<Option<lsproto::ResponseMessage>, Error> {
        let response_chan = self.start_request_worker(req, req_id)?;
        self.wait_for_response(req_id, response_chan)
    }

    /// `startRequestWorker` — registers the pending request channel, writes
    /// the request, and returns the receiver.
    fn start_request_worker(
        &self,
        req: lsproto::RequestMessage,
        req_id: &jsonrpc::ID,
    ) -> Result<mpsc::Receiver<lsproto::ResponseMessage>, Error> {
        let (tx, rx) = mpsc::sync_channel(1);
        self.pending_requests
            .lock()
            .unwrap()
            .push((req_id.clone(), tx));

        self.write_msg(&req.message())?;
        Ok(rx)
    }

    /// `waitForResponse` — `select { <-ctx.Done() / resp = <-responseChan }`.
    ///
    /// PORT: the test context `t.Context()` becomes the client's own
    /// cancellable ctx (a child of the caller's ctx, per [new_lsp_client]);
    /// `mpsc` has no select, so cancellation is polled on a `recv_timeout`.
    fn wait_for_response(
        &self,
        req_id: &jsonrpc::ID,
        response_chan: mpsc::Receiver<lsproto::ResponseMessage>,
    ) -> Result<Option<lsproto::ResponseMessage>, Error> {
        loop {
            if self.ctx.is_cancelled() {
                self.pending_requests
                    .lock()
                    .unwrap()
                    .retain(|(k, _)| &*k != req_id);
                return Err(Error::new("Request cancelled"));
            }
            match response_chan.recv_timeout(Duration::from_millis(10)) {
                Ok(resp) => return Ok(Some(resp)),
                Err(mpsc::RecvTimeoutError::Disconnected) => return Ok(None),
                Err(mpsc::RecvTimeoutError::Timeout) => {}
            }
        }
    }

    /// `SendNotification` sends a typed notification.
    pub fn send_notification<Params>(
        &self,
        info: &lsproto::NotificationInfo<Params>,
        params: Params,
    ) -> Result<(), Error>
    where
        Params: Serialize,
    {
        let notification = info.new_notification_message(params);
        self.write_msg(&notification.message())
    }

    /// `SetCompilerOptionsForInferredProjects`.
    ///
    /// PORT(assumption): the parallel `lsp::Server` port takes `&Context`
    /// plus `&CompilerOptions` (Go takes `*core.CompilerOptions`).
    pub fn set_compiler_options_for_inferred_projects(&self, options: &CompilerOptions) {
        self.server
            .set_compiler_options_for_inferred_projects(&self.ctx, options);
    }
}
