// Ported from tsc/internal/contentmapper/host_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `net.Pipe` → [`test_pipe`]: a buffered in-memory duplex with close
//   semantics (peer sees EOF after draining buffered data; writes to a
//   closed end fail).
// - `io.ReadWriteCloser` test doubles → [`SpawnedProcess`] impls wrapping an
//   `Arc<dyn SpawnedProcess>`; `processExitState.ExitCode() (int, bool)` →
//   `spawned_exit_code() -> Option<i64>`.
// - `stderr == io.Discard` is asserted as `stderr.is_none()` (the port's
//   "discard" representation).
// - `json.Unmarshal(params, &p)` → `params_of`; `(any, error)` responses →
//   `Option<Value>` produced via `ipc::marshal_params`.
// - `t.Context()` → `test_context()` — a `(Context, CancelFunc)` pair; tests
//   that need end-of-test cancellation call `cancel.cancel()` explicitly.
// - `chan struct{}` signaling → `mpsc::sync_channel`.
// - `errors.AsType[*T](err)` → `err.as_*_error()` helpers on `Error`.
// - The Go test asserts `assert.Equal(t, err.Error(), "...")`-equivalents
//   via `Error::to_string`/`contains`.

use std::collections::VecDeque;
use std::io;
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::sync::{Arc, Condvar, Mutex, mpsc};
use std::thread;
use std::time::Duration;

use serde::Serialize;
use serde::de::DeserializeOwned;
use tsc_ast::MappedDiagnosticDirectivePolicy;
use tsc_ast::diagnostic::lock_diagnostic;
use tsc_core::context::{CancelFunc, Context};
use tsc_core::options_generated::{CompilerOptions, JsxEmit, ScriptTarget};
use tsc_core::tristate::Tristate;
use tsc_ipc::{self as ipc, Handler, Protocol};
use tsc_json::Value;
use tsc_locale::{self as locale, Locale};
use tsc_spanmap::{Fidelity, Kind, Segment, SpanMap};
use tsc_tspath as tspath;

use crate::contentmapper::Mapper;
use crate::host::{self, Error, InitializeErrorKind, ProjectSpec, Request};
use crate::hostimpl::{
    self, CloseProjectParams, Diagnostic, DiagnosticDirectivePolicy, DiagnosticDirectives,
    InitializeParams, InitializeResult, METHOD_CLOSE_PROJECT, METHOD_INITIALIZE,
    METHOD_OPEN_PROJECT, METHOD_TRANSFORM, MappedDiagnosticDirective, OpenProjectParams,
    OpenProjectResult, OptionDiagnosticResult, PositionEncoding, SpawnedProcess, Spawner,
    SpawnerFunc, TransformParams, TransformResult, UnusedExpectDirectiveDiagnostic,
};

// ---------------------------------------------------------------------------
// net.Pipe test double
// ---------------------------------------------------------------------------

#[derive(Default)]
struct PipeChanState {
    queue: VecDeque<u8>,
    /// The writing end closed — readers see EOF once the queue drains.
    writer_closed: bool,
    /// The reading end closed — writers and this end's reads fail.
    reader_closed: bool,
}

struct PipeChan {
    state: Mutex<PipeChanState>,
    cvar: Condvar,
}

/// One end of a `net.Pipe` — `io::Read`/`io::Write`/`IoClose` for
/// `ipc::new_async_conn`, and `SpawnedProcess` for the host dial path.
struct PipeEnd {
    incoming: Arc<PipeChan>,
    outgoing: Arc<PipeChan>,
    closed: AtomicBool,
}

fn test_pipe() -> (Arc<PipeEnd>, Arc<PipeEnd>) {
    let a_to_b = Arc::new(PipeChan {
        state: Mutex::new(PipeChanState::default()),
        cvar: Condvar::new(),
    });
    let b_to_a = Arc::new(PipeChan {
        state: Mutex::new(PipeChanState::default()),
        cvar: Condvar::new(),
    });
    (
        Arc::new(PipeEnd {
            incoming: b_to_a.clone(),
            outgoing: a_to_b.clone(),
            closed: AtomicBool::new(false),
        }),
        Arc::new(PipeEnd {
            incoming: a_to_b,
            outgoing: b_to_a,
            closed: AtomicBool::new(false),
        }),
    )
}

fn closed_pipe() -> io::Error {
    io::Error::new(io::ErrorKind::BrokenPipe, "io: read/write on closed pipe")
}

impl PipeEnd {
    fn close_inner(&self) {
        if self.closed.swap(true, Ordering::SeqCst) {
            return;
        }
        {
            let mut s = self.outgoing.state.lock().unwrap();
            s.writer_closed = true;
        }
        self.outgoing.cvar.notify_all();
        {
            let mut s = self.incoming.state.lock().unwrap();
            s.reader_closed = true;
        }
        self.incoming.cvar.notify_all();
    }
}

impl Drop for PipeEnd {
    /// `defer server.Close()`
    fn drop(&mut self) {
        self.close_inner();
    }
}

impl io::Read for &PipeEnd {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut s = self.incoming.state.lock().unwrap();
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
            s = self.incoming.cvar.wait(s).unwrap();
        }
    }
}

impl io::Write for &PipeEnd {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        {
            let mut s = self.outgoing.state.lock().unwrap();
            if s.writer_closed || s.reader_closed {
                return Err(closed_pipe());
            }
            s.queue.extend(buf.iter());
        }
        self.outgoing.cvar.notify_all();
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl ipc::IoClose for PipeEnd {
    fn close(&self) -> io::Result<()> {
        self.close_inner();
        Ok(())
    }
}

impl SpawnedProcess for PipeEnd {
    fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize> {
        io::Read::read(&mut { self }, buf)
    }

    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
        io::Write::write(&mut { self }, buf)
    }

    fn spawned_close(&self) -> io::Result<()> {
        self.close_inner();
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// handler helpers
// ---------------------------------------------------------------------------

fn test_context() -> (Context, CancelFunc) {
    Context::background().with_cancel()
}

/// `json.Unmarshal(params, &p)` — the params are always present in these
/// tests; a missing value decodes like Go's unmarshal of `null` (zero
/// value).
fn params_of<T: DeserializeOwned + Default>(
    params: &Option<Value>,
) -> std::result::Result<T, Box<dyn std::error::Error + Send + Sync>> {
    Ok(ipc::unmarshal_params::<T>(params.as_ref())
        .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> { Box::new(e) })?
        .unwrap_or_default())
}

/// `return result, nil` — marshal a handler response.
fn respond<T: Serialize>(
    value: &T,
) -> std::result::Result<Option<ipc::ResponsePayload>, Box<dyn std::error::Error + Send + Sync>> {
    Ok(ipc::marshal_params(value).ok().map(ipc::ResponsePayload::Json))
}

fn raw_json(s: &str) -> Value {
    serde_json::value::RawValue::from_string(s.to_string()).unwrap()
}

/// `protocolDiagnosticDirectives` helper.
fn protocol_diagnostic_directives(
    directives: Vec<MappedDiagnosticDirective>,
    unused: Vec<UnusedExpectDirectiveDiagnostic>,
) -> Option<DiagnosticDirectives> {
    Some(DiagnosticDirectives {
        unused_expect_directive_diagnostics: Some(unused),
        directives: Some(directives),
    })
}

// ---------------------------------------------------------------------------
// fakeMapper / responseMapper / unicodeMapper / invalidDiagnosticMapper
// ---------------------------------------------------------------------------

/// `fakeMapper` — transforms content verbatim and reports one diagnostic.
struct FakeMapper;

impl Handler for FakeMapper {
    fn handle_request(
        &self,
        _ctx: &Context,
        method: &str,
        params: Option<Value>,
    ) -> std::result::Result<Option<ipc::ResponsePayload>, Box<dyn std::error::Error + Send + Sync>> {
        match method {
            METHOD_INITIALIZE => respond(&InitializeResult {
                position_encoding: PositionEncoding::UTF8,
                diagnostic_source: "vue".into(),
            }),
            METHOD_TRANSFORM => {
                let p = params_of::<TransformParams>(&params)?;
                let len = p.content.len() as i32;
                let mappings = SpanMap::new(&[Segment {
                    virtual_end: len,
                    original_end: len,
                    kind: Kind::Verbatim,
                    ..Default::default()
                }])
                .marshal()
                .unwrap();
                respond(&TransformResult {
                    mapped_output: hostimpl::MappedOutput {
                        text: p.content.clone(),
                        extension: ".ts".into(),
                        mappings: Some(
                            serde_json::value::RawValue::from_string(
                                String::from_utf8(mappings).unwrap(),
                            )
                            .unwrap(),
                        ),
                        diagnostic_directives: None,
                    },
                    diagnostics: vec![Diagnostic {
                        message_text: "boom".into(),
                        start: 0,
                        length: 3.min(len as i64),
                        code: 9999,
                    }],
                    supplemental: Vec::new(),
                })
            }
            _ => Err(format!("unexpected method {method}").into()),
        }
    }
    /// `HandleNotification` — the test protocol sends no notifications.
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

/// `responseMapper` — returns `response(p)` for transform requests.
struct ResponseMapper {
    response: Arc<dyn Fn(&TransformParams) -> Value + Send + Sync>,
}

impl Handler for ResponseMapper {
    fn handle_request(
        &self,
        _ctx: &Context,
        method: &str,
        params: Option<Value>,
    ) -> std::result::Result<Option<ipc::ResponsePayload>, Box<dyn std::error::Error + Send + Sync>> {
        match method {
            METHOD_INITIALIZE => respond(&InitializeResult {
                position_encoding: PositionEncoding::UTF8,
                diagnostic_source: "mapper".into(),
            }),
            METHOD_TRANSFORM => {
                let p = params_of::<TransformParams>(&params)?;
                Ok(Some(((self.response)(&p)).into()))
            }
            _ => Err(format!("unexpected method {method}").into()),
        }
    }
    /// `HandleNotification` — the test protocol sends no notifications.
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

/// `unicodeMapper`
struct UnicodeMapper {
    encoding: PositionEncoding,
    source: Option<String>,
}

impl Handler for UnicodeMapper {
    fn handle_request(
        &self,
        _ctx: &Context,
        method: &str,
        params: Option<Value>,
    ) -> std::result::Result<Option<ipc::ResponsePayload>, Box<dyn std::error::Error + Send + Sync>> {
        match method {
            METHOD_INITIALIZE => {
                let p = params_of::<InitializeParams>(&params)?;
                let offered = p.position_encodings.contains(&self.encoding);
                if !offered
                    && (self.encoding == PositionEncoding::UTF8
                        || self.encoding == PositionEncoding::UTF16)
                {
                    return Err(
                        format!("position encoding {:?} was not offered", self.encoding).into(),
                    );
                }
                let source = self.source.clone().unwrap_or_else(|| "mapper".into());
                respond(&InitializeResult {
                    position_encoding: self.encoding.clone(),
                    diagnostic_source: source,
                })
            }
            METHOD_TRANSFORM => {
                let p = params_of::<TransformParams>(&params)?;
                let (emoji_length, text_length): (i64, i64) =
                    if self.encoding == PositionEncoding::UTF8 {
                        (2, 3)
                    } else if self.encoding == PositionEncoding::UTF16 {
                        (1, 2)
                    } else {
                        return respond(&TransformResult {
                            mapped_output: hostimpl::MappedOutput {
                                text: p.content.clone(),
                                extension: ".ts".into(),
                                ..Default::default()
                            },
                            ..Default::default()
                        });
                    };
                // `json.Marshal([][5]int{...})`
                let tuples: Vec<(i64, i64, i64, i64, i64)> = vec![
                    (0, emoji_length, 0, emoji_length, 0),
                    (
                        emoji_length,
                        text_length - emoji_length,
                        emoji_length,
                        text_length - emoji_length,
                        0,
                    ),
                ];
                let mappings = raw_json(&serde_json::to_string(&tuples).unwrap());
                respond(&TransformResult {
                    mapped_output: hostimpl::MappedOutput {
                        text: p.content.clone(),
                        extension: ".ts".into(),
                        mappings: Some(mappings),
                        diagnostic_directives: protocol_diagnostic_directives(
                            vec![MappedDiagnosticDirective {
                                original_start: emoji_length,
                                original_length: text_length - emoji_length,
                                virtual_start: emoji_length,
                                virtual_end: text_length,
                                policy: DiagnosticDirectivePolicy::IGNORE,
                                unused_expect_directive_index: None,
                            }],
                            Vec::new(),
                        ),
                    },
                    diagnostics: vec![Diagnostic {
                        message_text: "after non-ASCII character".into(),
                        start: emoji_length,
                        length: text_length - emoji_length,
                        code: 1001,
                    }],
                    supplemental: Vec::new(),
                })
            }
            _ => Err(format!("unexpected method {method}").into()),
        }
    }
    /// `HandleNotification` — the test protocol sends no notifications.
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

/// `invalidDiagnosticMapper`
struct InvalidDiagnosticMapper {
    encoding: PositionEncoding,
}

impl Handler for InvalidDiagnosticMapper {
    fn handle_request(
        &self,
        _ctx: &Context,
        method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<Option<ipc::ResponsePayload>, Box<dyn std::error::Error + Send + Sync>> {
        match method {
            METHOD_INITIALIZE => respond(&InitializeResult {
                position_encoding: self.encoding.clone(),
                diagnostic_source: "mapper".into(),
            }),
            METHOD_TRANSFORM => respond(&TransformResult {
                mapped_output: hostimpl::MappedOutput {
                    extension: ".ts".into(),
                    ..Default::default()
                },
                diagnostics: vec![Diagnostic {
                    message_text: "invalid boundary".into(),
                    start: 1,
                    length: 0,
                    code: 1002,
                }],
                supplemental: Vec::new(),
            }),
            _ => Err(format!("unexpected method {method}").into()),
        }
    }
    /// `HandleNotification` — the test protocol sends no notifications.
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// fakeSpawner and spawned-process test doubles
// ---------------------------------------------------------------------------

/// `noOpProjectMapper` — accepts open/closeProject with no-op results for
/// handlers that don't declare `handlesProjects`.
struct NoOpProjectMapper {
    inner: Arc<dyn Handler>,
}

impl Handler for NoOpProjectMapper {
    fn handle_request(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Value>,
    ) -> std::result::Result<Option<ipc::ResponsePayload>, Box<dyn std::error::Error + Send + Sync>> {
        match method {
            METHOD_OPEN_PROJECT => respond(&OpenProjectResult::default()),
            METHOD_CLOSE_PROJECT => Ok(None),
            _ => self.inner.handle_request(ctx, method, params),
        }
    }
    /// `HandleNotification` — the test protocol sends no notifications.
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

/// `fakeSpawner` — serves each spawn request with an in-process mapper over
/// a pipe, counting spawns so tests can assert process consolidation.
/// `project_aware` models Go's `handlesProjects` marker interface (set for
/// `recordingMapper`/`blockingMapper` handlers).
#[derive(Default)]
struct FakeSpawner {
    spawns: AtomicI32,
    closes: Arc<AtomicI32>,
    handler: Mutex<Option<(Arc<dyn Handler>, bool)>>,
}

impl FakeSpawner {
    fn with_handler(handler: Arc<dyn Handler>, handles_projects: bool) -> FakeSpawner {
        FakeSpawner {
            handler: Mutex::new(Some((handler, handles_projects))),
            ..Default::default()
        }
    }
}

impl Spawner for FakeSpawner {
    fn spawn(
        &self,
        _command: &[String],
        _dir: &str,
        _stderr: Option<Box<dyn io::Write + Send>>,
    ) -> io::Result<Arc<dyn SpawnedProcess>> {
        self.spawns.fetch_add(1, Ordering::SeqCst);
        let (handler, handles_projects) = self
            .handler
            .lock()
            .unwrap()
            .clone()
            .unwrap_or((Arc::new(FakeMapper), false));
        let handler: Arc<dyn Handler> = if handles_projects {
            handler
        } else {
            Arc::new(NoOpProjectMapper { inner: handler })
        };
        let (client, server) = test_pipe();
        thread::spawn(move || {
            let conn = ipc::new_async_conn(server, handler);
            let _ = conn.run(&Context::background());
        });
        Ok(Arc::new(CountingProcess {
            inner: client,
            closes: self.closes.clone(),
            once: AtomicBool::new(false),
        }))
    }
}

/// `countingReadWriteCloser`
struct CountingProcess {
    inner: Arc<dyn SpawnedProcess>,
    closes: Arc<AtomicI32>,
    once: AtomicBool,
}

impl SpawnedProcess for CountingProcess {
    fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.inner.spawned_read(buf)
    }
    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
        self.inner.spawned_write(buf)
    }
    fn spawned_close(&self) -> io::Result<()> {
        if !self.once.swap(true, Ordering::SeqCst) {
            self.closes.fetch_add(1, Ordering::SeqCst);
        }
        self.inner.spawned_close()
    }
    fn spawned_exit_code(&self) -> Option<i64> {
        self.inner.spawned_exit_code()
    }
}

/// `exitedReadWriteCloser`
struct ExitedProcess {
    inner: Arc<dyn SpawnedProcess>,
    exit_code: i64,
}

impl SpawnedProcess for ExitedProcess {
    fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.inner.spawned_read(buf)
    }
    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
        self.inner.spawned_write(buf)
    }
    fn spawned_close(&self) -> io::Result<()> {
        self.inner.spawned_close()
    }
    /// `ExitCode() (exitCode, true)`
    fn spawned_exit_code(&self) -> Option<i64> {
        Some(self.exit_code)
    }
}

/// `exitOnCloseReadWriteCloser`
struct ExitOnCloseProcess {
    inner: Arc<dyn SpawnedProcess>,
    exited: AtomicBool,
}

impl SpawnedProcess for ExitOnCloseProcess {
    fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.inner.spawned_read(buf)
    }
    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
        self.inner.spawned_write(buf)
    }
    fn spawned_close(&self) -> io::Result<()> {
        self.exited.store(true, Ordering::SeqCst);
        self.inner.spawned_close()
    }
    /// `ExitCode() (1, exited)`
    fn spawned_exit_code(&self) -> Option<i64> {
        self.exited.load(Ordering::SeqCst).then_some(1)
    }
}

/// `closeSignalReadWriteCloser`
struct CloseSignalProcess {
    inner: Arc<dyn SpawnedProcess>,
    closed: mpsc::SyncSender<()>,
    once: AtomicBool,
}

impl SpawnedProcess for CloseSignalProcess {
    fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.inner.spawned_read(buf)
    }
    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
        self.inner.spawned_write(buf)
    }
    fn spawned_close(&self) -> io::Result<()> {
        let err = self.inner.spawned_close();
        if !self.once.swap(true, Ordering::SeqCst) {
            let _ = self.closed.send(());
        }
        err
    }
    fn spawned_exit_code(&self) -> Option<i64> {
        self.inner.spawned_exit_code()
    }
}

// ---------------------------------------------------------------------------
// recordingMapper / blockingMapper
// ---------------------------------------------------------------------------

/// `recordingMapper` — captures project configuration and lifecycle
/// requests for host protocol tests.
#[derive(Default)]
struct RecordingConfig {
    watched_files: Option<Vec<String>>,
    /// `configIdentity *string`
    config_identity: Option<String>,
    dynamic_config: bool,
    option_diagnostics: Vec<OptionDiagnosticResult>,
}

#[derive(Default)]
struct RecordingState {
    received: String,
    received_options: String,
    received_locale: String,
    project_handles: Vec<String>,
    closed_handles: Vec<String>,
    transform_handle: String,
    transform_params: String,
}

struct RecordingMapper {
    config: RecordingConfig,
    state: Mutex<RecordingState>,
}

impl RecordingMapper {
    fn new(config: RecordingConfig) -> Arc<RecordingMapper> {
        Arc::new(RecordingMapper {
            config,
            state: Mutex::new(RecordingState::default()),
        })
    }
}

impl Handler for RecordingMapper {
    /// `handlesProjects` — modeled by `FakeSpawner::with_handler(h, true)`.
    fn handle_request(
        &self,
        _ctx: &Context,
        method: &str,
        params: Option<Value>,
    ) -> std::result::Result<Option<ipc::ResponsePayload>, Box<dyn std::error::Error + Send + Sync>> {
        match method {
            METHOD_INITIALIZE => {
                let p = params_of::<InitializeParams>(&params)?;
                self.state.lock().unwrap().received_locale = p.locale;
                respond(&InitializeResult {
                    position_encoding: PositionEncoding::UTF8,
                    diagnostic_source: "mapper".into(),
                })
            }
            METHOD_OPEN_PROJECT => {
                let p = params_of::<OpenProjectParams>(&params)?;
                // `json.Marshal(p.CompilerOptions)` — the raw value verbatim.
                let raw = p.compiler_options.get().to_string();
                let options_raw = p
                    .options
                    .as_ref()
                    .map_or(String::new(), |v| v.get().to_string());
                let mut watched_files = self.config.watched_files.clone();
                let dynamic_config = self.config.dynamic_config;
                let config_identity_override = self.config.config_identity.clone();
                let option_diagnostics = self.config.option_diagnostics.clone();
                {
                    let mut state = self.state.lock().unwrap();
                    state.project_handles.push(p.project_handle.clone());
                    state.received = raw;
                    state.received_options = options_raw.clone();
                }
                if !dynamic_config
                    && watched_files.is_none()
                    && config_identity_override.is_none()
                    && option_diagnostics.is_empty()
                {
                    return respond(&OpenProjectResult::default());
                }
                if dynamic_config && watched_files.is_none() {
                    watched_files = Some(vec![tspath::combine_paths(
                        &tspath::get_directory_path(&p.config_file_name),
                        &["mapper.config.js"],
                    )]);
                }
                let mut config_identity = String::new();
                if dynamic_config {
                    config_identity = format!("config:{options_raw}");
                }
                if let Some(o) = config_identity_override {
                    config_identity = o;
                }
                respond(&OpenProjectResult {
                    config_identity,
                    watched_files,
                    option_diagnostics: Some(option_diagnostics),
                })
            }
            METHOD_CLOSE_PROJECT => {
                let p = params_of::<CloseProjectParams>(&params)?;
                self.state
                    .lock()
                    .unwrap()
                    .closed_handles
                    .push(p.project_handle);
                Ok(None)
            }
            METHOD_TRANSFORM => {
                let p = params_of::<TransformParams>(&params)?;
                {
                    let mut state = self.state.lock().unwrap();
                    state.transform_handle = p.project_handle.clone();
                    state.transform_params = params
                        .as_ref()
                        .map_or(String::new(), |v| v.get().to_string());
                }
                respond(&TransformResult {
                    mapped_output: hostimpl::MappedOutput {
                        text: p.content.clone(),
                        extension: ".ts".into(),
                        ..Default::default()
                    },
                    ..Default::default()
                })
            }
            _ => Err(format!("unexpected method {method}").into()),
        }
    }
    /// `HandleNotification` — the test protocol sends no notifications.
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

/// `blockingMapper` — blocks transform requests until `proceed` is
/// signaled; `started` is signaled on entry.
struct BlockingMapper {
    inner: RecordingMapper,
    /// `close(m.started)` — taken once, then sent.
    started: Mutex<Option<mpsc::SyncSender<()>>>,
    /// `<-m.proceed`
    proceed: Mutex<mpsc::Receiver<()>>,
}

impl BlockingMapper {
    /// Returns `(mapper, started_rx, proceed_tx)`.
    fn new() -> (
        Arc<BlockingMapper>,
        mpsc::Receiver<()>,
        mpsc::SyncSender<()>,
    ) {
        let (started_tx, started_rx) = mpsc::sync_channel(1);
        let (proceed_tx, proceed_rx) = mpsc::sync_channel(1);
        (
            Arc::new(BlockingMapper {
                inner: RecordingMapper {
                    config: RecordingConfig::default(),
                    state: Mutex::new(RecordingState::default()),
                },
                started: Mutex::new(Some(started_tx)),
                proceed: Mutex::new(proceed_rx),
            }),
            started_rx,
            proceed_tx,
        )
    }
}

impl Handler for BlockingMapper {
    fn handle_request(
        &self,
        ctx: &Context,
        method: &str,
        params: Option<Value>,
    ) -> std::result::Result<Option<ipc::ResponsePayload>, Box<dyn std::error::Error + Send + Sync>> {
        if method == METHOD_TRANSFORM {
            // `close(m.started)` then `<-m.proceed`
            if let Some(tx) = self.started.lock().unwrap().take() {
                let _ = tx.send(());
            }
            let _ = self.proceed.lock().unwrap().recv();
        }
        self.inner.handle_request(ctx, method, params)
    }
    /// `HandleNotification` — the test protocol sends no notifications.
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// tests
// ---------------------------------------------------------------------------

fn vue_mapper() -> Arc<Mapper> {
    Arc::new(Mapper {
        extensions: Some(vec![".vue".into()]),
        name: "vue".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["vue-mapper".into()]),
        ..Default::default()
    })
}

#[test]
fn test_runner_transform() {
    let (ctx, _cancel) = test_context();
    let r = hostimpl::new_host(&ctx, Arc::new(FakeSpawner::default()), Locale::default());
    let mapper = vue_mapper();
    let result = r
        .transform(
            &mapper,
            &Request {
                file_name: "/a.vue".into(),
                content: "export const x = 1;".into(),
            },
        )
        .unwrap();
    assert_eq!(result.text, "export const x = 1;");
    assert_eq!(result.virtual_extension, ".ts");
    assert!(result.mappings.is_some());
    assert_eq!(result.diagnostics.len(), 1);
    assert_eq!(lock_diagnostic(&result.diagnostics[0]).code(), 9999);
    assert_eq!(lock_diagnostic(&result.diagnostics[0]).source(), "vue");
    r.close().unwrap();
}

#[test]
fn test_host_logging() {
    let (ctx, _cancel) = test_context();
    let logs = Arc::new(Mutex::new(Vec::<String>::new()));
    let logger: hostimpl::Logger = {
        let logs = logs.clone();
        Arc::new(move |message: &str| logs.lock().unwrap().push(message.to_string()))
    };
    let spawner = SpawnerFunc(
        move |command: &[String], dir: &str, stderr: Option<Box<dyn io::Write + Send>>| {
            if let Some(mut w) = stderr {
                let _ = w.write_all(b"mapper diagnostic\n");
            }
            let _ = (command, dir);
            FakeSpawner::default().spawn(command, dir, None)
        },
    );
    let host = hostimpl::new_host_with_options(
        &ctx,
        Arc::new(spawner),
        Locale::default(),
        hostimpl::HostOptions {
            logger: Some(logger),
        },
    );
    let mapper = Arc::new(Mapper {
        package: "configured".into(),
        extensions: Some(vec![".vue".into()]),
        name: "resolved".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    host.transform(
        &mapper,
        &Request {
            file_name: "/a.vue".into(),
            content: "export const x = 1;".into(),
        },
    )
    .unwrap();

    let joined = logs.lock().unwrap().join("\n");
    assert!(
        joined.contains(
            "[content mapper: resolved] send: {\"jsonrpc\":\"2.0\",\"id\":\"api1\",\"method\":\"initialize\""
        ),
        "{joined}"
    );
    assert!(
        joined.contains(
            "[content mapper: resolved] receive: {\"jsonrpc\":\"2.0\",\"id\":\"api1\",\"result\":"
        ),
        "{joined}"
    );
    assert!(
        joined.contains("[content mapper: resolved] stderr: mapper diagnostic"),
        "{joined}"
    );
    host.close().unwrap();
}

#[test]
fn test_host_discards_stderr_without_logging() {
    let (ctx, _cancel) = test_context();
    let stderr_check = Arc::new(AtomicBool::new(false));
    let check = stderr_check.clone();
    let spawner = SpawnerFunc(
        move |command: &[String], dir: &str, stderr: Option<Box<dyn io::Write + Send>>| {
            // PORT: Go asserts `stderr == io.Discard`; `None` is the port's
            // discard representation.
            assert!(stderr.is_none());
            check.store(true, Ordering::SeqCst);
            FakeSpawner::default().spawn(command, dir, None)
        },
    );
    let host = hostimpl::new_host(&ctx, Arc::new(spawner), Locale::default());
    let mapper = Arc::new(Mapper {
        package: "configured".into(),
        extensions: Some(vec![".vue".into()]),
        name: "resolved".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    host.transform(
        &mapper,
        &Request {
            file_name: "/a.vue".into(),
            content: "export const x = 1;".into(),
        },
    )
    .unwrap();
    assert!(stderr_check.load(Ordering::SeqCst));
    host.close().unwrap();
}

#[test]
fn test_mapper_diagnostic_name() {
    let tests: [(Mapper, &str); 3] = [
        (
            Mapper {
                package: "configured".into(),
                name: "resolved".into(),
                contribution_id: "contributed".into(),
                ..Default::default()
            },
            "resolved",
        ),
        (
            Mapper {
                package: "configured".into(),
                contribution_id: "contributed".into(),
                ..Default::default()
            },
            "configured",
        ),
        (
            Mapper {
                contribution_id: "contributed".into(),
                ..Default::default()
            },
            "contributed",
        ),
    ];
    for (mapper, want) in tests {
        assert_eq!(mapper.diagnostic_name(), want);
    }
}

#[test]
fn test_runner_transform_response_validation() {
    let request = Request {
        file_name: "/a.vue".into(),
        content: "a".into(),
    };
    let mapper = Arc::new(Mapper {
        extensions: Some(vec![".vue".into()]),
        name: "mapper".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });

    // "malformed result fails the request"
    let (ctx, _cancel) = test_context();
    let host = hostimpl::new_host(
        &ctx,
        Arc::new(FakeSpawner::with_handler(
            Arc::new(ResponseMapper {
                response: Arc::new(|_p| raw_json("{\"text\":1}")),
            }),
            false,
        )),
        Locale::default(),
    );
    assert!(
        host.transform(&mapper, &request).is_err(),
        "expected malformed result to fail the request"
    );
    host.close().unwrap();
}

#[test]
fn test_host_closes_process_when_read_loop_fails() {
    let (ctx, _cancel) = test_context();
    let (closed_tx, closed_rx) = mpsc::sync_channel::<()>(1);
    let spawner = SpawnerFunc(
        move |_command: &[String], _dir: &str, _stderr: Option<Box<dyn io::Write + Send>>| {
            let (client, server) = test_pipe();
            thread::spawn(move || {
                let protocol = ipc::new_json_rpc_protocol(server.clone());
                let message = protocol.read_message().unwrap();
                assert_eq!(message.method, METHOD_INITIALIZE);
                protocol
                    .write_response(
                        message.id.as_ref(),
                        Some(ipc::ResponsePayload::Json(
                            ipc::marshal_params(&InitializeResult {
                                position_encoding: PositionEncoding::UTF8,
                                diagnostic_source: "mapper".into(),
                            })
                            .unwrap(),
                        )),
                    )
                    .unwrap();
                io::Write::write_all(&mut &*server, b"oops\n").unwrap();
                // `defer server.Close()` — PipeEnd drops here.
            });
            Ok(Arc::new(CloseSignalProcess {
                inner: client,
                closed: closed_tx.clone(),
                once: AtomicBool::new(false),
            }) as Arc<dyn SpawnedProcess>)
        },
    );
    let host = hostimpl::new_host(&ctx, Arc::new(spawner), Locale::default());
    let mapper = Arc::new(Mapper {
        name: "mapper".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    let err = host.transform(
        &mapper,
        &Request {
            file_name: "/a.vue".into(),
            content: String::new(),
        },
    );
    assert!(err.is_err());
    let process_closed = closed_rx.recv_timeout(Duration::from_secs(1)).is_ok();
    assert!(
        process_closed,
        "mapper process was not closed after its read loop failed"
    );
    host.close().unwrap();
}

#[test]
fn test_host_reports_initialization_timeout_before_closing_process() {
    let (ctx, cancel) = test_context();
    let server_ctx = ctx.clone();
    let spawner = SpawnerFunc(
        move |_command: &[String], _dir: &str, _stderr: Option<Box<dyn io::Write + Send>>| {
            let (client, server) = test_pipe();
            let server_ctx = server_ctx.clone();
            thread::spawn(move || {
                let _protocol = ipc::new_json_rpc_protocol(server.clone());
                let _ = _protocol.read_message();
                // `<-t.Context().Done()`
                server_ctx.wait_cancelled();
                // `defer server.Close()`
            });
            Ok(Arc::new(ExitOnCloseProcess {
                inner: client,
                exited: AtomicBool::new(false),
            }) as Arc<dyn SpawnedProcess>)
        },
    );
    let host = hostimpl::new_host(&ctx, Arc::new(spawner), Locale::default());
    let mapper = Arc::new(Mapper {
        name: "mapper".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    let err = host
        .transform(
            &mapper,
            &Request {
                file_name: "/a.vue".into(),
                content: String::new(),
            },
        )
        .err()
        .unwrap();
    let initialize_error = err
        .as_initialize_error()
        .unwrap_or_else(|| panic!("expected InitializeError, got {err}"));
    assert_eq!(initialize_error.kind, InitializeErrorKind::NoResponse);
    host.close().unwrap();
    cancel.cancel();
}

#[test]
fn test_host_reports_process_exit_before_initialization() {
    let (ctx, _cancel) = test_context();
    let spawner = SpawnerFunc(
        move |_command: &[String], _dir: &str, _stderr: Option<Box<dyn io::Write + Send>>| {
            let (client, server) = test_pipe();
            drop(server); // `assert.NilError(t, server.Close())`
            Ok(Arc::new(ExitedProcess {
                inner: client,
                exit_code: 42,
            }) as Arc<dyn SpawnedProcess>)
        },
    );
    let host = hostimpl::new_host(&ctx, Arc::new(spawner), Locale::default());
    let mapper = Arc::new(Mapper {
        name: "mapper".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    let err = host
        .transform(
            &mapper,
            &Request {
                file_name: "/a.vue".into(),
                content: String::new(),
            },
        )
        .err()
        .unwrap();
    let initialize_error = err
        .as_initialize_error()
        .unwrap_or_else(|| panic!("expected InitializeError, got {err}"));
    assert_eq!(initialize_error.kind, InitializeErrorKind::ProcessExit);
    assert_eq!(initialize_error.exit_code, 42);
    host.close().unwrap();
}

#[test]
fn test_runner_transform_diagnostic_directives() {
    let (ctx, _cancel) = test_context();
    let request = Request {
        file_name: "/a.vue".into(),
        content: "directive\nsource".into(),
    };
    let mapper = Arc::new(Mapper {
        extensions: Some(vec![".vue".into()]),
        name: "mapper".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    let transform = |output: hostimpl::MappedOutput| -> std::result::Result<host::Result, Error> {
        let output = Arc::new(output);
        hostimpl::new_host(
            &ctx,
            Arc::new(FakeSpawner::with_handler(
                Arc::new(ResponseMapper {
                    response: Arc::new(move |_p| {
                        ipc::marshal_params(&TransformResult {
                            mapped_output: (*output).clone(),
                            ..Default::default()
                        })
                        .unwrap()
                    }),
                }),
                false,
            )),
            Locale::default(),
        )
        .transform(&mapper, &request)
    };

    let result = transform(hostimpl::MappedOutput {
        text: "virtual source".into(),
        extension: ".ts".into(),
        diagnostic_directives: protocol_diagnostic_directives(
            vec![MappedDiagnosticDirective {
                original_start: 0,
                original_length: 9,
                virtual_start: 8,
                virtual_end: 14,
                policy: DiagnosticDirectivePolicy::EXPECT,
                unused_expect_directive_index: None,
            }],
            vec![UnusedExpectDirectiveDiagnostic {
                code: 2578,
                message_text: "Unused framework directive.".into(),
            }],
        ),
        ..Default::default()
    })
    .unwrap();
    assert_eq!(result.diagnostic_directives.len(), 1);
    let directive = &result.diagnostic_directives[0];
    assert_eq!(directive.original_range.pos(), 0);
    assert_eq!(directive.original_range.end(), 9);
    assert_eq!(directive.virtual_range.pos(), 8);
    assert_eq!(directive.virtual_range.end(), 14);
    assert_eq!(directive.policy, MappedDiagnosticDirectivePolicy::Expect);
    assert_eq!(directive.unused_code, 2578);
    assert_eq!(directive.unused_message_text, "Unused framework directive.");
    assert_eq!(directive.source, "mapper");

    let result = transform(hostimpl::MappedOutput {
        text: "virtual source".into(),
        extension: ".ts".into(),
        diagnostic_directives: protocol_diagnostic_directives(
            vec![MappedDiagnosticDirective {
                original_start: 0,
                original_length: 9,
                virtual_start: 8,
                virtual_end: 14,
                policy: DiagnosticDirectivePolicy::EXPECT,
                unused_expect_directive_index: Some(1),
            }],
            vec![
                UnusedExpectDirectiveDiagnostic {
                    code: 1,
                    message_text: "first".into(),
                },
                UnusedExpectDirectiveDiagnostic {
                    code: 2,
                    message_text: "second".into(),
                },
            ],
        ),
        ..Default::default()
    })
    .unwrap();
    assert_eq!(result.diagnostic_directives[0].unused_code, 2);
    assert_eq!(
        result.diagnostic_directives[0].unused_message_text,
        "second"
    );

    transform(hostimpl::MappedOutput {
        text: "x".into(),
        extension: ".ts".into(),
        diagnostic_directives: protocol_diagnostic_directives(
            vec![MappedDiagnosticDirective {
                original_start: -1,
                policy: DiagnosticDirectivePolicy::IGNORE,
                ..Default::default()
            }],
            vec![UnusedExpectDirectiveDiagnostic::default()],
        ),
        ..Default::default()
    })
    .unwrap();

    struct InvalidCase {
        name: &'static str,
        text: &'static str,
        directives: Vec<MappedDiagnosticDirective>,
        kind: host::DiagnosticDirectiveErrorKind,
    }
    let invalid = vec![
        InvalidCase {
            name: "invalid range",
            text: "x",
            directives: vec![MappedDiagnosticDirective {
                virtual_start: -1,
                policy: DiagnosticDirectivePolicy::IGNORE,
                ..Default::default()
            }],
            kind: host::DiagnosticDirectiveErrorKind::InvalidRange,
        },
        InvalidCase {
            name: "unknown policy",
            text: "x",
            directives: vec![MappedDiagnosticDirective {
                policy: DiagnosticDirectivePolicy(2),
                ..Default::default()
            }],
            kind: host::DiagnosticDirectiveErrorKind::InvalidPolicy,
        },
        InvalidCase {
            name: "expect requires unused diagnostic",
            text: "x",
            directives: vec![MappedDiagnosticDirective {
                policy: DiagnosticDirectivePolicy::EXPECT,
                ..Default::default()
            }],
            kind: host::DiagnosticDirectiveErrorKind::ExpectMissingUnusedDiagnostic,
        },
        InvalidCase {
            name: "multiple unused diagnostics require index",
            text: "x",
            directives: vec![MappedDiagnosticDirective {
                policy: DiagnosticDirectivePolicy::EXPECT,
                ..Default::default()
            }],
            kind: host::DiagnosticDirectiveErrorKind::ExpectMissingUnusedDiagnostic,
        },
        InvalidCase {
            name: "original range out of bounds",
            text: "x",
            directives: vec![MappedDiagnosticDirective {
                original_start: 99,
                policy: DiagnosticDirectivePolicy::EXPECT,
                ..Default::default()
            }],
            kind: host::DiagnosticDirectiveErrorKind::InvalidRange,
        },
        InvalidCase {
            name: "virtual range out of bounds",
            text: "x",
            directives: vec![MappedDiagnosticDirective {
                virtual_start: 99,
                policy: DiagnosticDirectivePolicy::IGNORE,
                ..Default::default()
            }],
            kind: host::DiagnosticDirectiveErrorKind::InvalidRange,
        },
        InvalidCase {
            name: "overlap",
            text: "abc",
            directives: vec![
                MappedDiagnosticDirective {
                    virtual_end: 2,
                    policy: DiagnosticDirectivePolicy::IGNORE,
                    ..Default::default()
                },
                MappedDiagnosticDirective {
                    virtual_start: 1,
                    virtual_end: 3,
                    policy: DiagnosticDirectivePolicy::IGNORE,
                    ..Default::default()
                },
            ],
            kind: host::DiagnosticDirectiveErrorKind::Overlap,
        },
    ];
    for test in invalid {
        let mut diagnostic_directives = DiagnosticDirectives {
            unused_expect_directive_diagnostics: None,
            directives: Some(test.directives),
        };
        if test.name == "original range out of bounds" {
            diagnostic_directives.unused_expect_directive_diagnostics =
                Some(vec![UnusedExpectDirectiveDiagnostic::default()]);
        } else if test.name == "multiple unused diagnostics require index" {
            diagnostic_directives.unused_expect_directive_diagnostics = Some(vec![
                UnusedExpectDirectiveDiagnostic::default(),
                UnusedExpectDirectiveDiagnostic::default(),
            ]);
        }
        let transform_err = transform(hostimpl::MappedOutput {
            text: test.text.into(),
            extension: ".ts".into(),
            diagnostic_directives: Some(diagnostic_directives),
            ..Default::default()
        })
        .err()
        .unwrap();
        let directive_error = transform_err
            .as_diagnostic_directive_error()
            .unwrap_or_else(|| panic!("{}: expected DiagnosticDirectiveError", test.name));
        assert_eq!(directive_error.kind, test.kind, "{}", test.name);
    }
}

#[test]
fn test_mapped_diagnostic_directive_json() {
    let tests: [(&str, MappedDiagnosticDirective, &str); 2] = [
        (
            "ignore",
            MappedDiagnosticDirective {
                virtual_start: 8,
                virtual_end: 14,
                original_start: 0,
                original_length: 9,
                policy: DiagnosticDirectivePolicy::IGNORE,
                unused_expect_directive_index: None,
            },
            "[0,9,8,14,0]",
        ),
        (
            "expect",
            MappedDiagnosticDirective {
                virtual_start: 8,
                virtual_end: 14,
                original_start: 0,
                original_length: 9,
                policy: DiagnosticDirectivePolicy::EXPECT,
                unused_expect_directive_index: None,
            },
            "[0,9,8,14,1]",
        ),
    ];
    for (name, directive, want) in tests {
        let data = tsc_json::marshal(&directive, &[]).unwrap();
        assert_eq!(String::from_utf8(data).unwrap(), want, "{name}");
        let decoded: MappedDiagnosticDirective = tsc_json::unmarshal(want.as_bytes(), &[]).unwrap();
        assert_eq!(decoded, directive, "{name}");
    }

    for data in ["[0,0,0,0]", "[0,0,0,0,0,1,2]"] {
        let err = tsc_json::unmarshal::<MappedDiagnosticDirective>(data.as_bytes(), &[])
            .err()
            .unwrap();
        assert!(
            err.to_string().contains("diagnostic directive tuple"),
            "{err}"
        );
    }

    let diagnostic_directives = DiagnosticDirectives {
        unused_expect_directive_diagnostics: Some(vec![
            UnusedExpectDirectiveDiagnostic {
                code: 1,
                message_text: "first".into(),
            },
            UnusedExpectDirectiveDiagnostic {
                code: 2,
                message_text: "second".into(),
            },
        ]),
        directives: Some(vec![MappedDiagnosticDirective {
            original_start: 2,
            original_length: 3,
            virtual_start: 5,
            virtual_end: 9,
            policy: DiagnosticDirectivePolicy::EXPECT,
            unused_expect_directive_index: Some(1),
        }]),
    };
    let data = tsc_json::marshal(&diagnostic_directives, &[]).unwrap();
    assert_eq!(
        String::from_utf8(data.clone()).unwrap(),
        "{\"unusedExpectDirectiveDiagnostics\":[{\"code\":1,\"messageText\":\"first\"},{\"code\":2,\"messageText\":\"second\"}],\"directives\":[[2,3,5,9,1,1]]}"
    );
    let decoded: DiagnosticDirectives = tsc_json::unmarshal(&data, &[]).unwrap();
    assert_eq!(decoded, diagnostic_directives);
}

#[test]
fn test_runner_transform_supplemental_outputs() {
    let (ctx, _cancel) = test_context();
    let host = hostimpl::new_host(
        &ctx,
        Arc::new(FakeSpawner::with_handler(
            Arc::new(ResponseMapper {
                response: Arc::new(|_p| {
                    ipc::marshal_params(&TransformResult {
                        mapped_output: hostimpl::MappedOutput {
                            text: "export default 1;".into(),
                            extension: ".ts".into(),
                            ..Default::default()
                        },
                        supplemental: vec![
                            hostimpl::SupplementalOutput {
                                mapped_output: hostimpl::MappedOutput {
                                    text: "declare const first: string;".into(),
                                    extension: ".ts".into(),
                                    diagnostic_directives: protocol_diagnostic_directives(
                                        vec![MappedDiagnosticDirective {
                                            virtual_end: 7,
                                            policy: DiagnosticDirectivePolicy::IGNORE,
                                            ..Default::default()
                                        }],
                                        Vec::new(),
                                    ),
                                    ..Default::default()
                                },
                            },
                            hostimpl::SupplementalOutput {
                                mapped_output: hostimpl::MappedOutput {
                                    text: "declare const second: number;".into(),
                                    extension: ".mjs".into(),
                                    ..Default::default()
                                },
                            },
                        ],
                        ..Default::default()
                    })
                    .unwrap()
                }),
            }),
            false,
        )),
        Locale::default(),
    );
    let mapper = Arc::new(Mapper {
        extensions: Some(vec![".vue".into()]),
        name: "mapper".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    let result = host
        .transform(
            &mapper,
            &Request {
                file_name: "/component.vue".into(),
                content: "component".into(),
            },
        )
        .unwrap();
    assert_eq!(result.supplemental.len(), 2);
    assert_eq!(result.supplemental[0].text, "declare const first: string;");
    assert_eq!(result.supplemental[0].virtual_extension, ".ts");
    assert!(result.supplemental[0].mappings.is_some());
    assert_eq!(result.supplemental[0].diagnostic_directives.len(), 1);
    assert_eq!(
        result.supplemental[0].diagnostic_directives[0]
            .virtual_range
            .end(),
        7
    );
    assert_eq!(result.supplemental[1].virtual_extension, ".mjs");
    assert!(result.supplemental[1].mappings.is_some());
    host.close().unwrap();
}

#[test]
fn test_runner_transform_invalid_supplemental_diagnostic_directive() {
    let (ctx, _cancel) = test_context();
    let host = hostimpl::new_host(
        &ctx,
        Arc::new(FakeSpawner::with_handler(
            Arc::new(ResponseMapper {
                response: Arc::new(|_p| {
                    ipc::marshal_params(&TransformResult {
                        mapped_output: hostimpl::MappedOutput {
                            text: "export {};".into(),
                            extension: ".ts".into(),
                            ..Default::default()
                        },
                        supplemental: vec![
                            hostimpl::SupplementalOutput {
                                mapped_output: hostimpl::MappedOutput {
                                    text: "export {};".into(),
                                    extension: ".ts".into(),
                                    ..Default::default()
                                },
                            },
                            hostimpl::SupplementalOutput {
                                mapped_output: hostimpl::MappedOutput {
                                    text: "export {};".into(),
                                    extension: ".ts".into(),
                                    diagnostic_directives: protocol_diagnostic_directives(
                                        vec![MappedDiagnosticDirective {
                                            policy: DiagnosticDirectivePolicy::EXPECT,
                                            ..Default::default()
                                        }],
                                        Vec::new(),
                                    ),
                                    ..Default::default()
                                },
                            },
                        ],
                        ..Default::default()
                    })
                    .unwrap()
                }),
            }),
            false,
        )),
        Locale::default(),
    );
    let mapper = Arc::new(Mapper {
        extensions: Some(vec![".vue".into()]),
        name: "mapper".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    let err = host
        .transform(
            &mapper,
            &Request {
                file_name: "/component.vue".into(),
                content: "component".into(),
            },
        )
        .err()
        .unwrap();
    let directive_error = err.as_diagnostic_directive_error().unwrap();
    assert_eq!(
        directive_error.kind,
        host::DiagnosticDirectiveErrorKind::ExpectMissingUnusedDiagnostic
    );
    assert_eq!(directive_error.index, 0);
    assert_eq!(directive_error.supplemental_index, 1);
    host.close().unwrap();
}

#[test]
fn test_runner_rejects_invalid_virtual_extension() {
    let (ctx, _cancel) = test_context();
    for supplemental in [false, true] {
        for extension in ["", ".coffee"] {
            let supplemental_outputs = if supplemental {
                vec![hostimpl::SupplementalOutput {
                    mapped_output: hostimpl::MappedOutput {
                        text: "export {};".into(),
                        extension: extension.into(),
                        ..Default::default()
                    },
                }]
            } else {
                Vec::new()
            };
            let canonical_extension = if supplemental { ".ts" } else { extension };
            let host = hostimpl::new_host(
                &ctx,
                Arc::new(FakeSpawner::with_handler(
                    Arc::new(ResponseMapper {
                        response: Arc::new(move |_p| {
                            ipc::marshal_params(&TransformResult {
                                mapped_output: hostimpl::MappedOutput {
                                    text: "export {};".into(),
                                    extension: canonical_extension.into(),
                                    ..Default::default()
                                },
                                supplemental: supplemental_outputs.clone(),
                                ..Default::default()
                            })
                            .unwrap()
                        }),
                    }),
                    false,
                )),
                Locale::default(),
            );
            let mapper = Arc::new(Mapper {
                extensions: Some(vec![".vue".into()]),
                name: "mapper".into(),
                exec: Some(vec!["mapper".into()]),
                ..Default::default()
            });
            let err = host
                .transform(
                    &mapper,
                    &Request {
                        file_name: "/component.vue".into(),
                        content: "component".into(),
                    },
                )
                .err()
                .unwrap();
            assert!(
                err.to_string().contains("invalid virtual extension"),
                "supplemental={supplemental}/{extension}: {err}"
            );
            host.close().unwrap();
        }
    }
}

#[test]
fn test_runner_position_encodings() {
    for encoding in [PositionEncoding::UTF8, PositionEncoding::UTF16] {
        let (ctx, _cancel) = test_context();
        let r = hostimpl::new_host(
            &ctx,
            Arc::new(FakeSpawner::with_handler(
                Arc::new(UnicodeMapper {
                    encoding: encoding.clone(),
                    source: None,
                }),
                false,
            )),
            Locale::default(),
        );
        let mapper = Arc::new(Mapper {
            name: encoding.as_str().into(),
            exec: Some(vec!["mapper".into()]),
            ..Default::default()
        });
        let result = r
            .transform(
                &mapper,
                &Request {
                    file_name: "/a.vue".into(),
                    content: "éx".into(),
                },
            )
            .unwrap();
        let segments = SpanMap::segments(result.mappings.as_deref());
        assert_eq!(segments.len(), 2);
        assert_eq!(segments[0].virtual_end, 2);
        assert_eq!(segments[0].original_end, 2);
        assert_eq!(segments[1].virtual_start, 2);
        assert_eq!(segments[1].original_start, 2);
        assert_eq!(result.text, "éx");
        assert!(
            SpanMap::validate(result.mappings.as_deref(), &result.text, "éx").is_none(),
            "expected no mapping problem"
        );
        let (mapped, fidelity) =
            SpanMap::virtual_to_original_position(result.mappings.as_deref(), 2);
        assert_eq!(mapped, 2);
        assert_eq!(fidelity, Fidelity::Exact);
        assert_eq!(lock_diagnostic(&result.diagnostics[0]).loc().pos(), 2);
        assert_eq!(lock_diagnostic(&result.diagnostics[0]).loc().end(), 3);
        assert_eq!(result.diagnostic_directives[0].original_range.pos(), 2);
        assert_eq!(result.diagnostic_directives[0].original_range.end(), 3);
        assert_eq!(result.diagnostic_directives[0].virtual_range.pos(), 2);
        assert_eq!(result.diagnostic_directives[0].virtual_range.end(), 3);
        r.close().unwrap();
    }
}

#[test]
fn test_runner_rejects_unsupported_position_encoding() {
    let (ctx, _cancel) = test_context();
    let r = hostimpl::new_host(
        &ctx,
        Arc::new(FakeSpawner::with_handler(
            Arc::new(UnicodeMapper {
                encoding: PositionEncoding("utf-32".into()),
                source: None,
            }),
            false,
        )),
        Locale::default(),
    );
    let mapper = Arc::new(Mapper {
        name: "invalid".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    let err = r
        .transform(
            &mapper,
            &Request {
                file_name: "/a.vue".into(),
                content: "x".into(),
            },
        )
        .err()
        .unwrap();
    assert!(
        err.to_string().contains("unsupported position encoding"),
        "{err}"
    );
    r.close().unwrap();
}

#[test]
fn test_runner_rejects_invalid_diagnostic_source() {
    for source in [
        "",
        " ",
        "ts",
        "TS",
        "d.ts",
        "json",
        "typescript",
        "TypeScript",
        "tsc",
        "TSC",
    ] {
        let (ctx, _cancel) = test_context();
        let handler = UnicodeMapper {
            encoding: PositionEncoding::UTF8,
            source: Some(source.to_string()),
        };
        let r = hostimpl::new_host(
            &ctx,
            Arc::new(FakeSpawner::with_handler(Arc::new(handler), false)),
            Locale::default(),
        );
        let mapper = Arc::new(Mapper {
            name: "invalid".into(),
            exec: Some(vec!["mapper".into()]),
            ..Default::default()
        });
        let err = r
            .transform(
                &mapper,
                &Request {
                    file_name: "/a.vue".into(),
                    content: "x".into(),
                },
            )
            .err()
            .unwrap();
        if source.trim().is_empty() {
            assert!(
                err.to_string()
                    .contains("diagnostic source must not be empty"),
                "{source}: {err}"
            );
        } else {
            assert!(
                err.to_string().contains("is reserved by TypeScript"),
                "{source}: {err}"
            );
        }
        r.close().unwrap();
    }
}

#[test]
fn test_runner_rejects_positions_inside_unicode_characters() {
    for (encoding, content) in [
        (PositionEncoding::UTF8, "é"),
        (PositionEncoding::UTF16, "😀"),
    ] {
        let (ctx, _cancel) = test_context();
        let r = hostimpl::new_host(
            &ctx,
            Arc::new(FakeSpawner::with_handler(
                Arc::new(InvalidDiagnosticMapper {
                    encoding: encoding.clone(),
                }),
                false,
            )),
            Locale::default(),
        );
        let mapper = Arc::new(Mapper {
            name: encoding.as_str().into(),
            exec: Some(vec!["mapper".into()]),
            ..Default::default()
        });
        let err = r
            .transform(
                &mapper,
                &Request {
                    file_name: "/a.vue".into(),
                    content: content.into(),
                },
            )
            .err()
            .unwrap();
        assert!(
            err.to_string().contains("splits a Unicode code point"),
            "{err}"
        );
        r.close().unwrap();
    }
}

#[test]
fn test_runner_consolidates_by_identity() {
    let (ctx, _cancel) = test_context();
    let spawner = Arc::new(FakeSpawner::default());
    let r = hostimpl::new_host(&ctx, spawner.clone(), Locale::default());

    // Two logically-separate mappers with the same identity share one process.
    let vue_a = Arc::new(Mapper {
        package: "a".into(),
        name: "vue".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["vue-mapper".into()]),
        ..Default::default()
    });
    let vue_b = Arc::new(Mapper {
        package: "b".into(),
        name: "vue".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["vue-mapper".into()]),
        ..Default::default()
    });
    let svelte = Arc::new(Mapper {
        name: "svelte".into(),
        version: "2.0.0".into(),
        exec: Some(vec!["svelte-mapper".into()]),
        ..Default::default()
    });
    let project = r
        .project(&ProjectSpec {
            mappers: vec![vue_a.clone(), vue_b.clone(), svelte.clone()],
            compiler_options: Some(Arc::new(CompilerOptions::default())),
            ..Default::default()
        })
        .unwrap();

    for m in [&vue_a, &vue_b, &vue_a, &svelte] {
        project
            .transform(
                m,
                &Request {
                    file_name: "/x".into(),
                    content: "y".into(),
                },
            )
            .unwrap();
    }
    assert_eq!(
        spawner.spawns.load(Ordering::SeqCst),
        2,
        "expected one process per identity"
    );
    project.close().unwrap();
    r.close().unwrap();
}

#[test]
fn test_runner_lease_lifecycle() {
    let (ctx, _cancel) = test_context();
    let spawner = Arc::new(FakeSpawner::default());
    let r = hostimpl::new_host(&ctx, spawner.clone(), Locale::default());

    let vue_a = Arc::new(Mapper {
        package: "a".into(),
        name: "vue".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["vue-mapper".into()]),
        ..Default::default()
    });
    let vue_b = Arc::new(Mapper {
        package: "b".into(),
        name: "vue".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["vue-mapper".into()]),
        ..Default::default()
    });
    let svelte = Arc::new(Mapper {
        name: "svelte".into(),
        version: "2.0.0".into(),
        exec: Some(vec!["svelte-mapper".into()]),
        ..Default::default()
    });

    let release_vue_a = r.acquire(&[vue_a.clone(), vue_a.clone()]);
    let release_vue_b = r.acquire(&[vue_b.clone()]);
    let release_svelte = r.acquire(&[svelte.clone()]);
    for mapper in [&vue_a, &svelte] {
        r.transform(
            mapper,
            &Request {
                file_name: "/x".into(),
                content: "y".into(),
            },
        )
        .unwrap();
    }
    assert_eq!(spawner.spawns.load(Ordering::SeqCst), 2);

    release_vue_a.release();
    assert_eq!(
        spawner.closes.load(Ordering::SeqCst),
        0,
        "shared vue process should remain owned"
    );
    release_svelte.release();
    assert_eq!(
        spawner.closes.load(Ordering::SeqCst),
        1,
        "final release should close the process"
    );
    release_vue_b.release();
    release_vue_b.release();
    assert_eq!(
        spawner.closes.load(Ordering::SeqCst),
        2,
        "final vue owner should close once"
    );

    let release_new = r.acquire(&[vue_a.clone()]);
    r.transform(
        &vue_a,
        &Request {
            file_name: "/x".into(),
            content: "y".into(),
        },
    )
    .unwrap();
    assert_eq!(
        spawner.spawns.load(Ordering::SeqCst),
        3,
        "reacquiring should spawn a fresh process lazily"
    );
    release_new.release();
    assert_eq!(spawner.closes.load(Ordering::SeqCst), 3);
    r.close().unwrap();
}

#[test]
fn test_project_lifecycle() {
    let (ctx, _cancel) = test_context();
    let mapper_process = RecordingMapper::new(RecordingConfig {
        dynamic_config: true,
        ..Default::default()
    });
    let spawner = Arc::new(FakeSpawner::with_handler(mapper_process.clone(), true));
    let host = hostimpl::new_host(&ctx, spawner.clone(), Locale::default());

    let static_mapper = Arc::new(Mapper {
        options: Some(raw_json("{\"mode\":\"static\"}")),
        name: "static".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    let static_project = host
        .project(&ProjectSpec {
            config_file_name: "/repo/tsconfig.json".into(),
            mappers: vec![static_mapper.clone()],
            compiler_options: Some(Arc::new(CompilerOptions::default())),
        })
        .unwrap();
    assert_eq!(
        spawner.spawns.load(Ordering::SeqCst),
        0,
        "static identity should not spawn the mapper"
    );
    let static_identities = static_project.identities().unwrap();
    assert_eq!(static_identities.len(), 1);
    static_project.close().unwrap();

    let dynamic_a = Arc::new(Mapper {
        options: Some(raw_json("{\"mode\":\"a\"}")),
        name: "dynamic".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["mapper".into()]),
        compiler_options: Some(vec!["jsx".into()]),
        dynamic_config: true,
        ..Default::default()
    });
    let dynamic_b = Arc::new(Mapper {
        options: Some(raw_json("{\"mode\":\"b\"}")),
        name: "dynamic".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["mapper".into()]),
        dynamic_config: true,
        ..Default::default()
    });
    let dynamic_a_options = Arc::new(CompilerOptions::default());
    let project_a = host
        .project(&ProjectSpec {
            config_file_name: "/repo/a/tsconfig.json".into(),
            mappers: vec![dynamic_a.clone(), dynamic_b.clone()],
            compiler_options: Some(dynamic_a_options.clone()),
        })
        .unwrap();
    let project_a_reversed = host
        .project(&ProjectSpec {
            config_file_name: "/repo/reversed/tsconfig.json".into(),
            mappers: vec![dynamic_b.clone(), dynamic_a.clone()],
            compiler_options: Some(dynamic_a_options.clone()),
        })
        .unwrap();
    let project_different_options = host
        .project(&ProjectSpec {
            config_file_name: "/repo/options/tsconfig.json".into(),
            mappers: vec![dynamic_a.clone()],
            compiler_options: Some(Arc::new(CompilerOptions {
                jsx: JsxEmit::React,
                ..Default::default()
            })),
        })
        .unwrap();
    let project_b = host
        .project(&ProjectSpec {
            config_file_name: "/repo/b/tsconfig.json".into(),
            mappers: vec![dynamic_a.clone()],
            compiler_options: Some(Arc::new(CompilerOptions::default())),
        })
        .unwrap();
    let project_a_again = host
        .project(&ProjectSpec {
            config_file_name: "/repo/a/tsconfig.json".into(),
            mappers: vec![dynamic_a.clone(), dynamic_b.clone()],
            compiler_options: Some(dynamic_a_options.clone()),
        })
        .unwrap();
    assert_eq!(
        spawner.spawns.load(Ordering::SeqCst),
        0,
        "getting dynamic projects should not start the mapper"
    );
    let project_a_identities = project_a.identities().unwrap();
    let project_a_reversed_identities = project_a_reversed.identities().unwrap();
    let project_different_option_identities = project_different_options.identities().unwrap();
    let project_b_identities = project_b.identities().unwrap();
    assert_eq!(project_a_identities.len(), 2);
    assert_eq!(project_a_reversed_identities.len(), 2);
    assert_eq!(project_a_identities[0], project_a_reversed_identities[1]);
    assert_eq!(project_a_identities[1], project_a_reversed_identities[0]);
    assert!(project_a_identities[0] != project_different_option_identities[0]);
    assert_eq!(project_b_identities.len(), 1);
    assert_eq!(
        spawner.spawns.load(Ordering::SeqCst),
        1,
        "dynamic projects should share one mapper process"
    );
    let project_a_watched_files = project_a.watched_files().unwrap();
    let project_b_watched_files = project_b.watched_files().unwrap();
    assert_eq!(project_a_watched_files.len(), 1);
    assert_eq!(project_b_watched_files.len(), 1);
    assert_eq!(
        project_a_watched_files[0].as_string(),
        "/repo/a/mapper.config.js"
    );
    assert_eq!(
        project_b_watched_files[0].as_string(),
        "/repo/b/mapper.config.js"
    );

    project_a
        .transform(
            &dynamic_b,
            &Request {
                file_name: "/repo/a/file.ext".into(),
                content: "x".into(),
            },
        )
        .unwrap();
    {
        let state = mapper_process.state.lock().unwrap();
        assert!(state.project_handles[..2].contains(&state.transform_handle));
    }

    project_a_again.close().unwrap();
    project_a.close().unwrap();
    project_a_reversed.close().unwrap();
    project_different_options.close().unwrap();
    project_b.close().unwrap();
    let timings = host.timings();
    let dynamic_timings = &timings.mappers[&dynamic_a.identity()];
    assert_eq!(dynamic_timings.spawn.count, 1);
    assert_eq!(dynamic_timings.initialize.count, 1);
    assert_eq!(dynamic_timings.open_project.count, 6);
    assert_eq!(dynamic_timings.transform.count, 1);
    assert_eq!(dynamic_timings.close_project.count, 6);
    let state = mapper_process.state.lock().unwrap();
    assert_eq!(state.project_handles.len(), 6);
    assert_eq!(state.closed_handles.len(), 6);
    drop(state);
    host.close().unwrap();
}

#[test]
fn test_project_methods_after_host_close() {
    let (ctx, _cancel) = test_context();
    let mapper_process = RecordingMapper::new(RecordingConfig {
        dynamic_config: true,
        ..Default::default()
    });
    let host = hostimpl::new_host(
        &ctx,
        Arc::new(FakeSpawner::with_handler(mapper_process, true)),
        Locale::default(),
    );
    let mapper = Arc::new(Mapper {
        name: "dynamic".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["mapper".into()]),
        dynamic_config: true,
        ..Default::default()
    });
    let project = host
        .project(&ProjectSpec {
            config_file_name: "/repo/tsconfig.json".into(),
            mappers: vec![mapper.clone()],
            compiler_options: Some(Arc::new(CompilerOptions::default())),
        })
        .unwrap();
    project
        .transform(
            &mapper,
            &Request {
                file_name: "/repo/file.ext".into(),
                content: "x".into(),
            },
        )
        .unwrap();
    let identity = project.identity(&Arc::new(Mapper::default())).unwrap();
    assert_eq!(identity, "");
    host.close().unwrap();

    project.refresh().unwrap();
    let identities = project.identities().unwrap();
    assert_eq!(identities.len(), 0);
    let identity = project.identity(&mapper).unwrap();
    assert_eq!(identity, "");
    let identity = project.identity(&Arc::new(Mapper::default())).unwrap();
    assert_eq!(identity, "");
    let watched_files = project.watched_files().unwrap();
    assert_eq!(watched_files.len(), 0);
    assert_eq!(project.diagnostics().len(), 0);
    let err = project
        .transform(
            &mapper,
            &Request {
                file_name: "/repo/file.ext".into(),
                content: "x".into(),
            },
        )
        .err()
        .unwrap();
    assert!(
        err.to_string().contains("content mapper project is closed"),
        "{err}"
    );
    project.close().unwrap();
}

#[test]
fn test_project_rejects_relative_watched_files() {
    let (ctx, _cancel) = test_context();
    let mapper_process = RecordingMapper::new(RecordingConfig {
        watched_files: Some(vec!["mapper.config.js".into()]),
        dynamic_config: true,
        ..Default::default()
    });
    let host = hostimpl::new_host(
        &ctx,
        Arc::new(FakeSpawner::with_handler(mapper_process, true)),
        Locale::default(),
    );
    let project_mapper = Arc::new(Mapper {
        package: "dynamic".into(),
        name: "dynamic".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["mapper".into()]),
        dynamic_config: true,
        ..Default::default()
    });
    let project = host
        .project(&ProjectSpec {
            config_file_name: "/repo/tsconfig.json".into(),
            mappers: vec![project_mapper.clone()],
            compiler_options: Some(Arc::new(CompilerOptions::default())),
        })
        .unwrap();
    let err = project
        .transform(
            &project_mapper,
            &Request {
                file_name: "/repo/file.ext".into(),
                content: "x".into(),
            },
        )
        .err()
        .unwrap();
    let transform_error = err.as_transform_error().unwrap();
    let _ = transform_error;
    let project_error = err.as_project_error().unwrap();
    assert_eq!(
        project_error.kind,
        host::ProjectErrorKind::NonAbsoluteWatchedFile
    );
    project.close().unwrap();
    host.close().unwrap();
}

#[test]
fn test_dynamic_project_requires_config_identity() {
    let (ctx, _cancel) = test_context();
    let mapper_process = RecordingMapper::new(RecordingConfig {
        config_identity: Some(String::new()),
        dynamic_config: true,
        ..Default::default()
    });
    let host = hostimpl::new_host(
        &ctx,
        Arc::new(FakeSpawner::with_handler(mapper_process, true)),
        Locale::default(),
    );
    let project_mapper = Arc::new(Mapper {
        package: "dynamic".into(),
        name: "dynamic".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["mapper".into()]),
        dynamic_config: true,
        ..Default::default()
    });
    let project = host
        .project(&ProjectSpec {
            config_file_name: "/repo/tsconfig.json".into(),
            mappers: vec![project_mapper.clone()],
            compiler_options: Some(Arc::new(CompilerOptions::default())),
        })
        .unwrap();
    let err = project
        .transform(
            &project_mapper,
            &Request {
                file_name: "/repo/file.ext".into(),
                content: "x".into(),
            },
        )
        .err()
        .unwrap();
    let project_error = err.as_project_error().unwrap();
    assert_eq!(
        project_error.kind,
        host::ProjectErrorKind::MissingConfigIdentity
    );
    project.close().unwrap();
    host.close().unwrap();
}

#[test]
fn test_static_mapper_rejects_dynamic_project_response_fields() {
    for (name, config, kind) in [
        (
            "config identity",
            RecordingConfig {
                config_identity: Some("dynamic".into()),
                ..Default::default()
            },
            host::ProjectErrorKind::UnexpectedConfigIdentity,
        ),
        (
            "watched files",
            RecordingConfig {
                watched_files: Some(vec!["/repo/mapper.config.js".into()]),
                ..Default::default()
            },
            host::ProjectErrorKind::UnexpectedWatchedFiles,
        ),
    ] {
        let (ctx, _cancel) = test_context();
        let host = hostimpl::new_host(
            &ctx,
            Arc::new(FakeSpawner::with_handler(
                RecordingMapper::new(config),
                true,
            )),
            Locale::default(),
        );
        let project_mapper = Arc::new(Mapper {
            name: "static".into(),
            version: "1.0.0".into(),
            exec: Some(vec!["mapper".into()]),
            ..Default::default()
        });
        let project = host
            .project(&ProjectSpec {
                config_file_name: "/repo/tsconfig.json".into(),
                mappers: vec![project_mapper.clone()],
                compiler_options: Some(Arc::new(CompilerOptions::default())),
            })
            .unwrap();
        let err = project
            .transform(
                &project_mapper,
                &Request {
                    file_name: "/repo/file.ext".into(),
                    content: "x".into(),
                },
            )
            .err()
            .unwrap();
        let project_error = err
            .as_project_error()
            .unwrap_or_else(|| panic!("{name}: expected ProjectError, got {err}"));
        assert_eq!(project_error.kind, kind, "{name}");
        project.close().unwrap();
        host.close().unwrap();
    }
}

#[test]
fn test_project_rejects_invalid_option_diagnostic_path() {
    let (ctx, _cancel) = test_context();
    let mapper_process = RecordingMapper::new(RecordingConfig {
        option_diagnostics: vec![OptionDiagnosticResult {
            path: vec![raw_json("null")],
            message_text: "Invalid option.".into(),
            code: 123,
        }],
        ..Default::default()
    });
    let host = hostimpl::new_host(
        &ctx,
        Arc::new(FakeSpawner::with_handler(mapper_process, true)),
        Locale::default(),
    );
    let project_mapper = Arc::new(Mapper {
        name: "mapper".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["mapper".into()]),
        ..Default::default()
    });
    let project = host
        .project(&ProjectSpec {
            mappers: vec![project_mapper.clone()],
            compiler_options: Some(Arc::new(CompilerOptions::default())),
            ..Default::default()
        })
        .unwrap();
    let err = project
        .transform(
            &project_mapper,
            &Request {
                file_name: "/repo/file.ext".into(),
                content: "x".into(),
            },
        )
        .err()
        .unwrap();
    let project_error = err.as_project_error().unwrap();
    assert_eq!(
        project_error.kind,
        host::ProjectErrorKind::MalformedResponse
    );
    project.close().unwrap();
    host.close().unwrap();
}

#[test]
fn test_runner_forwards_project_options() {
    let (ctx, _cancel) = test_context();
    let mapper = RecordingMapper::new(RecordingConfig::default());
    let (diagnostic_locale, ok) = locale::parse("cs-CZ");
    assert!(ok);
    let r = hostimpl::new_host(
        &ctx,
        Arc::new(FakeSpawner::with_handler(mapper.clone(), true)),
        diagnostic_locale,
    );

    let mapper_definition = Arc::new(Mapper {
        options: Some(raw_json("{\"strictTemplates\":true}")),
        name: "vue".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["vue-mapper".into()]),
        compiler_options: Some(vec!["target".into(), "jsx".into()]),
        ..Default::default()
    });
    let compiler_options = Arc::new(CompilerOptions {
        target: ScriptTarget::ES2020,
        strict: Tristate::True,
        ..Default::default()
    });
    let project = r
        .project(&ProjectSpec {
            mappers: vec![mapper_definition.clone()],
            compiler_options: Some(compiler_options.clone()),
            ..Default::default()
        })
        .unwrap();
    project
        .transform(
            &mapper_definition,
            &Request {
                file_name: "/a.vue".into(),
                content: "x".into(),
            },
        )
        .unwrap();

    let want = tsc_json::marshal(compiler_options.as_ref(), &[]).unwrap();
    let state = mapper.state.lock().unwrap();
    assert_eq!(state.received, String::from_utf8(want).unwrap());
    assert_eq!(state.received_options, "{\"strictTemplates\":true}");
    assert_eq!(state.received_locale, "cs-CZ");
    assert!(!state.transform_params.contains("\"options\""));
    assert!(!state.transform_params.contains("\"compilerOptions\""));
    drop(state);
    project.close().unwrap();
    r.close().unwrap();
}

#[test]
fn test_host_set_locale_restarts_mapper() {
    let (ctx, _cancel) = test_context();
    let mapper = RecordingMapper::new(RecordingConfig::default());
    let spawner = Arc::new(FakeSpawner::with_handler(mapper.clone(), true));
    let r = hostimpl::new_host(&ctx, spawner.clone(), Locale::default());

    let definition = Arc::new(Mapper {
        name: "vue".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["vue-mapper".into()]),
        ..Default::default()
    });
    let release = r.acquire(&[definition.clone()]);

    r.transform(
        &definition,
        &Request {
            file_name: "/a.vue".into(),
            content: "x".into(),
        },
    )
    .unwrap();
    assert_eq!(spawner.spawns.load(Ordering::SeqCst), 1);

    let (french, ok) = locale::parse("fr");
    assert!(ok);
    r.set_locale(french);
    assert_eq!(spawner.closes.load(Ordering::SeqCst), 1);

    r.transform(
        &definition,
        &Request {
            file_name: "/a.vue".into(),
            content: "x".into(),
        },
    )
    .unwrap();
    assert_eq!(spawner.spawns.load(Ordering::SeqCst), 2);
    assert_eq!(mapper.state.lock().unwrap().received_locale, "fr");
    release.release();
    r.close().unwrap();
}

#[test]
fn test_host_set_locale_waits_for_transform() {
    let (ctx, _cancel) = test_context();
    let (mapper, started_rx, proceed_tx) = BlockingMapper::new();
    let spawner = Arc::new(FakeSpawner::with_handler(mapper, true));
    let r = hostimpl::new_host(&ctx, spawner.clone(), Locale::default());
    let definition = Arc::new(Mapper {
        name: "vue".into(),
        version: "1.0.0".into(),
        exec: Some(vec!["vue-mapper".into()]),
        ..Default::default()
    });

    let (transform_done_tx, transform_done_rx) = mpsc::channel();
    {
        let r = r.clone();
        let definition = definition.clone();
        thread::spawn(move || {
            let result = r.transform(
                &definition,
                &Request {
                    file_name: "/a.vue".into(),
                    content: "x".into(),
                },
            );
            transform_done_tx.send(result.map(|_| ())).unwrap();
        });
    }
    // `<-mapper.started`
    started_rx.recv().unwrap();

    let (french, ok) = locale::parse("fr");
    assert!(ok);
    let (set_started_tx, set_started_rx) = mpsc::channel::<()>();
    let (set_done_tx, set_done_rx) = mpsc::channel::<()>();
    {
        let r = r.clone();
        thread::spawn(move || {
            // `close(setStarted)`
            set_started_tx.send(()).unwrap();
            r.set_locale(french);
            // `close(setDone)`
            set_done_tx.send(()).unwrap();
        });
    }
    set_started_rx.recv().unwrap();
    // Small scheduling margin so `set_locale` has a chance to attempt the
    // lifecycle write-lock before we sample `set_done`.
    thread::sleep(Duration::from_millis(50));
    let set_completed = set_done_rx.try_recv().is_ok();
    assert!(
        !set_completed,
        "SetLocale completed while a transform was in flight"
    );

    // `close(mapper.proceed)`
    proceed_tx.send(()).unwrap();
    transform_done_rx.recv().unwrap().unwrap();
    set_done_rx.recv().unwrap();
    assert_eq!(spawner.closes.load(Ordering::SeqCst), 1);
    r.close().unwrap();
}
