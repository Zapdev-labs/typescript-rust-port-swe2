// Ported from tsc/internal/lsp/server.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `error` -> [`Error`], a small enum carrying the distinctions Go's
//   `errors.Is`/`errors.As` checks need: `context.Canceled`, `io.EOF`,
//   `lsproto.ErrorCode` sentinels (incl. `ParamsError`),
//   `userFacingRequestFailedError`, `messageMarshalError`, `ls::Error`
//   (`ErrNeedsAutoImports`), `ipc::Error` (dynamic queue), and
//   `ErrNoProjectForUnknownScriptKind` (message-prefix match at the
//   `String`-returning session boundary).
// - `Reader`/`Writer` interfaces -> clonable `Arc<Mutex<..>>` handle structs
//   so `ServerOptions` can be borrowed by `new_server` while sharing the one
//   underlying stream end with the server (Go passes interface values).
// - Goroutines -> `std::thread`; `chan *ResponseMessage` (cap 1) ->
//   `mpsc::sync_channel(1)`; `close(ch)` -> dropping the sender.
// - `go doAsyncWork()` closures capture `SessionLanguageService` (holds
//   `Rc<Project>` -> `!Send`). `SendShared` asserts `Send` under the same
//   discipline as `tsc_project::session::SendShared`: Go shares these
//   pointers across goroutines under the session's lock regime. The
//   `LanguageService` itself is rebuilt inside the worker (it borrows the
//   snapshot and never crosses a thread boundary).
// - `map[jsonrpc.ID]...` -> `HashMap<IdKey, _>` (`ID` is not `Hash`; its
//   `(Display, try_int())` pair is injective, per `ipc::conn_async`).
// - `s.backgroundCtx` is created at construction with its own
//   `background_cancel` (the field's `Context` type is fixed by the sibling
//   logger/progress ports); `run` cancels it when the loops exit,
//   approximating the errgroup-ctx role.
// - `initComplete chan struct{}` -> an `mpsc` pair; `close(ch)` becomes one
//   `send(())` + sender drop so `init_complete().recv()` unblocks.
// - `recover()` -> `catch_unwind` + `Backtrace` (Go's `debug.Stack()` shape
//   differs; `sanitize_stack_trace` returns "" for non-Go stacks).
// - `handleInitializeAPISession`'s accept loop is Unix-shaped
//   (`PipeTransport::Conn` is `UnixStream` there; the Windows transport is
//   unconstructable upstream), so the connection half is stored as
//   `Arc<dyn IoClose>`.

use std::collections::HashMap;
use std::io;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, AtomicI32, AtomicI64, Ordering};
use std::sync::{Arc, LazyLock, Mutex, OnceLock, RwLock, mpsc};
use std::time::{Duration, Instant};

use serde::Serialize;
use serde::de::DeserializeOwned;
use serde_json::value::RawValue;
use tsc_collections::{Set, SyncSet};
use tsc_core::context::{CancelFunc, Context};
use tsc_core::options_generated::CompilerOptions;
use tsc_diagnostics as diagnostics;
use tsc_ipc as ipc;
use tsc_ipc::Transport as _;
use tsc_json as json;
use tsc_jsonrpc as jsonrpc;
use tsc_locale::Locale;
use tsc_ls as ls;
use tsc_ls::languageservice::LanguageService;
use tsc_lsconv as lsconv;
use tsc_lsproto as lsproto;
use tsc_lsutil as lsutil;
use tsc_project as project;
use tsc_project::parsecache::ParseCache;
use tsc_project::session::{
    ERR_NO_PROJECT_FOR_UNKNOWN_SCRIPT_KIND, Session, SessionInit, SessionLanguageService,
    SessionOptions,
};
use tsc_project::watch::WatcherId;
use tsc_project_logging::Logger as _;
use tsc_tspath as tspath;
use tsc_vfs::Vfs;

use crate::dynamic_queue::{DynamicQueue, new_dynamic_queue};
use crate::logger::{Logger, is_valid_log_verbosity, new_logger};
use crate::progress::{ProjectLoadingProgress, new_project_loading_progress};
use crate::stack_sanitizer::sanitize_stack_trace;

/// `sendClientRequest`'s response-channel poll granularity (`<-ctx.Done()`).
const CALL_POLL_INTERVAL: Duration = Duration::from_millis(10);

/// `sendShared<T>` asserts `Send` for `!Send` values moved onto a request
/// worker — same precedent as `tsc_project::session::SendShared`: Go's
/// goroutines share `*Snapshot`/pointer-`Project`s freely, and the values
/// moved this way are read under the same lock regime Go holds.
pub(crate) struct SendShared<T>(pub T);
impl<T> SendShared<T> {
    /// Method-call capture keeps the wrapper whole under edition-2021
    /// disjoint field capture.
    pub fn into_inner(self) -> T {
        self.0
    }
}
#[allow(unsafe_code)]
unsafe impl<T> Send for SendShared<T> {}

/// The `Reader` failure type — `lspReader.Read`'s `error` plus the
/// partially-decoded message id Go keeps on `ErrorCodeInvalidParams`.
#[derive(Debug)]
pub struct ReadError {
    /// The `lsproto.ErrorCode` the error wraps (`None` for transport EOF
    /// and other raw read failures).
    pub code: Option<lsproto::ErrorCode>,
    /// `err.Error()`.
    pub message: String,
    /// `jsonrpc.ID` of a partially decoded request.
    pub partial_id: Option<jsonrpc::ID>,
    /// `errors.Is(err, io.EOF)`.
    pub eof: bool,
}

/// `ServerError` — the server's `error` type.
#[derive(Debug)]
pub enum Error {
    /// `context.Canceled`
    Canceled,
    /// `io.EOF` — clean stream end; `handleExit`'s sentinel.
    Eof,
    /// A bare `lsproto.ErrorCode` sentinel.
    Code(lsproto::ErrorCode),
    /// `fmt.Errorf("%w: %s", code, detail)` — a wrapped error code.
    Coded(lsproto::ErrorCode, String),
    /// `userFacingRequestFailedError` — unwraps to `ErrorCodeRequestFailed`.
    UserFacing(String),
    /// `messageMarshalError` — unwraps to `ErrorCodeInternalError`.
    Marshal(String),
    /// `lspReader` failures.
    Read(ReadError),
    /// `ls::Error` passthrough (`ErrNeedsAutoImports` detection).
    Ls(ls::Error),
    /// `project.ErrNoProjectForUnknownScriptKind`.
    NoProjectForUnknownScriptKind(String),
    /// `io` failures from the transport.
    Io(io::Error),
    /// `errors.New`/`fmt.Errorf` plain messages.
    Message(String),
}

impl Error {
    /// `errors.Is(err, context.Canceled)`
    pub(crate) fn is_canceled(&self) -> bool {
        matches!(self, Error::Canceled)
    }

    /// `errors.Is(err, io.EOF)`
    pub(crate) fn is_eof(&self) -> bool {
        match self {
            Error::Eof => true,
            Error::Read(r) => r.eof,
            Error::Io(e) => e.kind() == io::ErrorKind::UnexpectedEof,
            _ => false,
        }
    }

    /// `errors.AsType[userFacingRequestFailedError](err)`
    pub(crate) fn is_user_facing(&self) -> bool {
        matches!(self, Error::UserFacing(_))
    }

    /// `errors.Is(err, ls.ErrNeedsAutoImports)`
    pub(crate) fn is_needs_auto_imports(&self) -> bool {
        match self {
            Error::Ls(e) => e.is(&ls::ERR_NEEDS_AUTO_IMPORTS),
            _ => false,
        }
    }

    /// `errors.Is(err, project.ErrNoProjectForUnknownScriptKind)`
    pub(crate) fn is_no_project_for_unknown_script_kind(&self) -> bool {
        matches!(self, Error::NoProjectForUnknownScriptKind(_))
    }

    /// `errors.AsType[lsproto.ErrorCode](err)` — the code `sendError`
    /// reports; `InternalError` when the error carries none.
    pub(crate) fn error_code(&self) -> lsproto::ErrorCode {
        match self {
            Error::Code(c) | Error::Coded(c, _) => *c,
            Error::UserFacing(_) => lsproto::ErrorCode::RequestFailed,
            Error::Read(r) => r.code.unwrap_or(lsproto::ErrorCode::InternalError),
            _ => lsproto::ErrorCode::InternalError,
        }
    }

    /// Converts a `String` error returned by `project::Session` methods.
    pub(crate) fn from_session(msg: String) -> Error {
        if msg.starts_with(ERR_NO_PROJECT_FOR_UNKNOWN_SCRIPT_KIND) {
            return Error::NoProjectForUnknownScriptKind(msg);
        }
        Error::Message(msg)
    }

    pub(crate) fn from_queue(err: ipc::Error) -> Error {
        match err {
            ipc::Error::ContextCanceled => Error::Canceled,
            other => Error::Message(other.to_string()),
        }
    }
}

impl From<ls::Error> for Error {
    fn from(e: ls::Error) -> Error {
        Error::Ls(e)
    }
}

impl From<lsproto::ParamsError> for Error {
    fn from(e: lsproto::ParamsError) -> Error {
        Error::Coded(e.code(), e.to_string())
    }
}

impl From<io::Error> for Error {
    fn from(e: io::Error) -> Error {
        if e.kind() == io::ErrorKind::UnexpectedEof {
            return Error::Eof;
        }
        Error::Io(e)
    }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Canceled => f.write_str("context canceled"),
            Error::Eof => f.write_str("EOF"),
            Error::Code(c) => write!(f, "{c}"),
            Error::Coded(c, m) => write!(f, "{c}: {m}"),
            Error::UserFacing(m) => f.write_str(m),
            Error::Marshal(m) => write!(f, "failed to marshal message: {m}"),
            Error::Read(r) => f.write_str(&r.message),
            Error::Ls(e) => write!(f, "{e}"),
            Error::NoProjectForUnknownScriptKind(m) | Error::Message(m) => f.write_str(m),
            Error::Io(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for Error {}

/// `npmInstall func(ctx, cwd, args) ([]byte, error)`.
pub type NpmInstallFn =
    Arc<dyn Fn(&Context, &str, &[String]) -> Result<Vec<u8>, Error> + Send + Sync>;

/// `watchdog`/`SetParentProcessID` hook.
pub type SetParentProcessIdFn = Box<dyn Fn(i32) + Send + Sync>;

// ---------------------------------------------------------------------------
// `ServerOptions` / transport endpoints

/// `type ServerOptions struct`.
#[derive(Default)]
pub struct ServerOptions {
    /// `In Reader`
    pub in_: Reader,
    /// `Out Writer`
    pub out: Writer,
    /// `Err io.Writer`
    pub err: Option<Arc<Mutex<Box<dyn io::Write + Send>>>>,
    /// `Cwd`
    pub cwd: tspath::RootedDirectoryPath,
    /// `FS`
    pub fs: Option<Arc<dyn Vfs>>,
    /// `DefaultLibraryPath`
    pub default_library_path: tspath::RootedDirectoryPath,
    /// `TypingsLocation`
    pub typings_location: tspath::RootedDirectoryPath,
    /// `ParseCache`
    pub parse_cache: Option<Rc<ParseCache>>,
    /// `NpmInstall`
    pub npm_install: Option<NpmInstallFn>,
    /// `Spawn` — launches a child process for content mappers; `None` when
    /// the host cannot spawn processes.
    pub spawn: Option<Arc<dyn tsc_contentmapper::Spawner>>,
    /// `ProgressDelay` — delay before showing progress UI; zero = none.
    pub progress_delay: Duration,
    /// `SetParentProcessID`
    pub set_parent_process_id: Option<SetParentProcessIdFn>,
    /// `client` — test hook replacing `self` as the `project.Client` handed
    /// to the session.
    pub client: Option<Arc<dyn project::client::Client>>,
}

/// `type Reader interface { Read() (*lsproto.Message, error) }` — a clonable
/// handle; clones share the one underlying framed reader.
#[derive(Clone)]
pub struct Reader {
    inner: Arc<Mutex<lsproto::BaseReader<Box<dyn io::Read + Send>>>>,
}

/// `type Writer interface { Write(msg *lsproto.Message) error }`.
#[derive(Clone)]
pub struct Writer {
    inner: Arc<Mutex<lsproto::BaseWriter<Box<dyn io::Write + Send>>>>,
}

impl Reader {
    /// `Read`.
    pub fn read(&self) -> Result<lsproto::Message, ReadError> {
        let data = self.inner.lock().unwrap().read().map_err(|e| ReadError {
            code: None,
            message: e.to_string(),
            partial_id: None,
            eof: e.is_eof(),
        })?;
        json::unmarshal::<lsproto::Message>(&data, &[]).map_err(|e| {
            // Go: `errors.Is(err, lsproto.ErrorCodeInvalidParams)` keeps the
            // partially decoded message for its id; the ported decoder
            // reports all failures uniformly, so recover the id best-effort.
            let partial_id = serde_json::from_slice::<serde_json::Value>(&data)
                .ok()
                .and_then(|v| v.get("id").cloned())
                .and_then(|v| serde_json::from_value::<jsonrpc::ID>(v).ok());
            ReadError {
                code: Some(lsproto::ErrorCode::InvalidRequest),
                message: e.to_string(),
                partial_id,
                eof: false,
            }
        })
    }
}

impl Default for Reader {
    /// A permanently-at-EOF reader for unset options.
    fn default() -> Self {
        to_reader(io::empty())
    }
}

impl Writer {
    /// `Write`.
    pub fn write(&self, msg: &lsproto::Message) -> Result<(), Error> {
        let data = json::marshal(msg, &[]).map_err(|e| Error::Marshal(e.to_string()))?;
        self.inner.lock().unwrap().write(&data).map_err(Error::Io)
    }
}

impl Default for Writer {
    fn default() -> Self {
        to_writer(io::sink())
    }
}

/// `func ToReader(r io.Reader) Reader`
pub fn to_reader<R: io::Read + Send + 'static>(r: R) -> Reader {
    Reader {
        inner: Arc::new(Mutex::new(lsproto::new_base_reader(Box::new(r)
            as Box<dyn io::Read + Send>))),
    }
}

/// `func ToWriter(w io.Writer) Writer`
pub fn to_writer<W: io::Write + Send + 'static>(w: W) -> Writer {
    Writer {
        inner: Arc::new(Mutex::new(lsproto::new_base_writer(Box::new(w)
            as Box<dyn io::Write + Send>))),
    }
}

// ---------------------------------------------------------------------------
// `Server`

/// `pendingClientRequest`.
struct PendingClientRequest {
    /// Stored for parity with Go; never re-read.
    #[allow(dead_code)]
    req: lsproto::RequestMessage,
    cancel: CancelFunc,
}

/// `map[jsonrpc.ID]...` key — `ID` is not `Hash`; `(Display, try_int())` is
/// injective (same trick as `ipc::conn_async::PendingKey`).
type IdKey = (String, Option<i32>);
fn id_key(id: &jsonrpc::ID) -> IdKey {
    (id.to_string(), id.try_int())
}

/// `apiSessionState`.
pub(crate) struct ApiSessionState {
    pub(crate) session: Arc<tsc_api::session::Session>,
    pub(crate) transport: Arc<ipc::PipeTransport>,
    pub(crate) cancel: CancelFunc,
    /// `done chan struct{}` — closed when the accept goroutine exits.
    pub(crate) done: Mutex<Option<mpsc::Receiver<()>>>,
    pub(crate) inner: Mutex<ApiSessionInner>,
}

#[derive(Default)]
pub(crate) struct ApiSessionInner {
    connection: Option<Arc<dyn ipc::IoClose>>,
    stopped: bool,
}

impl ApiSessionState {
    /// `attachConnection`.
    pub(crate) fn attach_connection(&self, connection: Arc<dyn ipc::IoClose>) -> bool {
        let mut inner = self.inner.lock().unwrap();
        if inner.stopped {
            let _ = connection.close();
            return false;
        }
        inner.connection = Some(connection);
        true
    }

    /// `stop`.
    pub(crate) fn stop(&self) {
        {
            let mut inner = self.inner.lock().unwrap();
            if !inner.stopped {
                inner.stopped = true;
                self.cancel.cancel();
                let _ = self.transport.close();
                if let Some(c) = inner.connection.take() {
                    let _ = c.close();
                }
            }
        }
        if let Some(done) = self.done.lock().unwrap().take() {
            let _ = done.recv();
        }
    }
}

/// `type Server struct` — the LSP server over a `project::Session`.
pub struct Server {
    pub(crate) r: Reader,
    pub(crate) w: Writer,
    /// `backgroundCtx` — cancelled when `run`'s loops exit.
    pub(crate) background_ctx: Context,
    pub(crate) background_cancel: Mutex<Option<CancelFunc>>,
    /// `stderr`.
    pub(crate) stderr: Arc<Mutex<Box<dyn io::Write + Send>>>,

    pub(crate) logger: Arc<Logger>,
    pub(crate) init_started: AtomicBool,
    pub(crate) client_seq: AtomicI32,
    pub(crate) request_queue: DynamicQueue<lsproto::RequestMessage>,
    pub(crate) outgoing_queue: DynamicQueue<lsproto::Message>,
    pub(crate) pending_client_requests: Mutex<HashMap<IdKey, PendingClientRequest>>,
    pub(crate) pending_server_requests:
        Mutex<HashMap<IdKey, mpsc::SyncSender<lsproto::ResponseMessage>>>,

    pub(crate) cwd: tspath::RootedDirectoryPath,
    pub(crate) fs: Arc<dyn Vfs>,
    pub(crate) default_library_path: tspath::RootedDirectoryPath,
    pub(crate) typings_location: tspath::RootedDirectoryPath,

    pub(crate) initialize_params: OnceLock<lsproto::InitializeParams>,
    pub(crate) initialization_options: OnceLock<lsproto::InitializationOptions>,
    pub(crate) client_capabilities: OnceLock<lsproto::ResolvedClientCapabilities>,
    pub(crate) position_encoding: OnceLock<lsproto::PositionEncodingKind>,
    pub(crate) locale: RwLock<Locale>,
    /// `initLocale` — fallback when the user's locale preference is "auto".
    pub(crate) init_locale: OnceLock<Locale>,

    pub(crate) watch_enabled: AtomicBool,
    pub(crate) telemetry_enabled: AtomicBool,
    pub(crate) watchers: SyncSet<WatcherId>,

    /// `contentMapperRegistrationMu` + `contentMapperExtensionsRegistered`.
    pub(crate) content_mapper_registration: Mutex<bool>,
    /// `builtinWatcher`.
    pub(crate) builtin_watcher: Mutex<Option<Arc<crate::lspwatcher::Watcher>>>,

    pub(crate) last_request_time_ms: AtomicI64,

    pub(crate) session: OnceLock<Arc<Session>>,

    pub(crate) api_sessions: Mutex<HashMap<String, Arc<ApiSessionState>>>,

    /// `client` — test override for the session's `project.Client`.
    pub(crate) client: Option<Arc<dyn project::client::Client>>,

    /// `initComplete` — one `()` send, then the sender drops.
    pub(crate) init_complete_tx: Mutex<Option<mpsc::SyncSender<()>>>,
    init_complete_rx: mpsc::Receiver<()>,

    /// `compilerOptionsForInferredProjects` — temporary.
    pub(crate) compiler_options_for_inferred_projects: Mutex<Option<Arc<CompilerOptions>>>,
    /// `parseCache` — `Rc` per the session port.
    pub(crate) parse_cache: Option<Rc<ParseCache>>,

    pub(crate) npm_install: Option<NpmInstallFn>,
    pub(crate) spawn: Option<Arc<dyn tsc_contentmapper::Spawner>>,

    pub(crate) cpu_profiler: tsc_pprof::CpuProfiler,

    pub(crate) progress_delay: Duration,
    pub(crate) project_progress: Mutex<Option<Arc<ProjectLoadingProgress>>>,

    pub(crate) start_watchdog: Option<SetParentProcessIdFn>,

    pub(crate) flake_logging: Mutex<lsproto::DiagnosticFlakeLogLevel>,
}

// SAFETY: Go shares `*Server` across the read/dispatch/write goroutines and
// the session's background workers; every mutable field is behind a mutex,
// atomic, `OnceLock`, or `SyncSet`, matching Go's lock regime. The `Rc`
// `parse_cache` is only read inside `handle_initialized`'s `new_session`
// call on the dispatch thread, before the session hands the cache to
// single-threaded builders — the same aliasing Go relies on (`Session`'s
// `unsafe impl Send + Sync` is the precedent).
#[allow(unsafe_code)]
unsafe impl Send for Server {}
#[allow(unsafe_code)]
unsafe impl Sync for Server {}

/// `func NewServer(opts *ServerOptions) *Server`.
pub fn new_server(opts: &ServerOptions) -> Arc<Server> {
    assert!(!opts.cwd.as_string().is_empty(), "Cwd is required");
    let (background_ctx, background_cancel) = Context::background().with_cancel();
    let (init_tx, init_rx) = mpsc::sync_channel(1);
    Arc::new_cyclic(|weak: &std::sync::Weak<Server>| Server {
        r: opts.in_.clone(),
        w: opts.out.clone(),
        background_ctx,
        background_cancel: Mutex::new(Some(background_cancel)),
        stderr: opts
            .err
            .clone()
            .unwrap_or_else(|| Arc::new(Mutex::new(Box::new(io::stderr())))),
        logger: Arc::new(new_logger(weak.clone())),
        init_started: AtomicBool::new(false),
        client_seq: AtomicI32::new(0),
        request_queue: new_dynamic_queue(),
        outgoing_queue: new_dynamic_queue(),
        pending_client_requests: Mutex::new(HashMap::new()),
        pending_server_requests: Mutex::new(HashMap::new()),
        cwd: opts.cwd.clone(),
        fs: opts.fs.clone().unwrap_or_else(tsc_vfs::osvfs::fs),
        default_library_path: opts.default_library_path.clone(),
        typings_location: opts.typings_location.clone(),
        initialize_params: OnceLock::new(),
        initialization_options: OnceLock::new(),
        client_capabilities: OnceLock::new(),
        position_encoding: OnceLock::new(),
        locale: RwLock::new(Locale::default()),
        init_locale: OnceLock::new(),
        watch_enabled: AtomicBool::new(false),
        telemetry_enabled: AtomicBool::new(false),
        watchers: SyncSet::new(),
        content_mapper_registration: Mutex::new(false),
        builtin_watcher: Mutex::new(None),
        last_request_time_ms: AtomicI64::new(0),
        session: OnceLock::new(),
        api_sessions: Mutex::new(HashMap::new()),
        client: opts.client.clone(),
        init_complete_tx: Mutex::new(Some(init_tx)),
        init_complete_rx: init_rx,
        compiler_options_for_inferred_projects: Mutex::new(None),
        parse_cache: opts.parse_cache.clone(),
        npm_install: opts.npm_install.clone(),
        spawn: opts.spawn.clone(),
        cpu_profiler: Default::default(),
        progress_delay: opts.progress_delay,
        project_progress: Mutex::new(None),
        start_watchdog: None,
        flake_logging: Mutex::new(lsproto::DiagnosticFlakeLogLevel::Off),
    })
}

impl Server {
    /// `s.initializeParams` is set.
    pub(crate) fn has_initialize_params(&self) -> bool {
        self.initialize_params.get().is_some()
    }

    /// `s.session` (`Some` after `initialized`).
    pub(crate) fn session_opt(&self) -> Option<Arc<Session>> {
        self.session.get().cloned()
    }

    /// `s.session` — must have been initialized (`session() method` for
    /// tests, `client.server.session()`).
    pub fn session(&self) -> Arc<Session> {
        self.session_opt()
            .expect("session accessed before initialized")
    }

    /// `initComplete channel` — blocks until `initialized` handling finished
    /// (`client.server.init_complete().recv()`).
    pub fn init_complete(&self) -> &mpsc::Receiver<()> {
        &self.init_complete_rx
    }

    /// `s.SetCompilerOptionsForInferredProjects` — for tests.
    pub fn set_compiler_options_for_inferred_projects(
        self: &Arc<Self>,
        ctx: &Context,
        compiler_options: &CompilerOptions,
    ) {
        if let Some(session) = self.session_opt() {
            session
                .did_change_compiler_options_for_inferred_projects(ctx, Arc::new(compiler_options.clone()));
        }
        *self.compiler_options_for_inferred_projects.lock().unwrap() =
            Some(Arc::new(compiler_options.clone()));
    }

    /// `s.GetLocale()`.
    pub(crate) fn get_locale(&self) -> Locale {
        self.locale.read().unwrap().clone()
    }

    /// `s.SetLocale(locale)`.
    pub(crate) fn set_locale(&self, locale: Locale) {
        *self.locale.write().unwrap() = locale;
    }
}

impl project::client::Client for Server {
    /// `s.WatchFiles`.
    fn watch_files(
        &self,
        ctx: &Context,
        id: &WatcherId,
        watchers: &[Arc<lsproto::FileSystemWatcher>],
    ) -> project::client::ClientResult {
        let watchers_vec: Vec<lsproto::FileSystemWatcher> =
            watchers.iter().map(|w| (**w).clone()).collect();
        if let Some(watcher) = self.builtin_watcher.lock().unwrap().clone() {
            watcher
                .watch_files(id, &watchers_vec)
                .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
                    Box::new(Error::Message(format!(
                        "failed to register file watcher: {e}"
                    )))
                })?;
            self.watchers.add(id.clone());
        } else {
            self.send_client_request(
                ctx,
                &lsproto::CLIENT_REGISTER_CAPABILITY_INFO,
                Some(lsproto::RegistrationParams {
                    registrations: Some(vec![lsproto::Registration {
                        id: id.clone(),
                        register_options: Some(
                            lsproto::RegisterOptions {
                                workspace_did_change_watched_files: Some(
                                    lsproto::DidChangeWatchedFilesRegistrationOptions {
                                        watchers: Some(watchers_vec),
                                    },
                                ),
                                ..Default::default()
                            },
                        ),
                    }]),
                }),
            )
            .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
                Box::new(Error::Message(format!("failed to register file watcher: {e}")))
            })?;
            self.watchers.add(id.clone());
        }
        Ok(())
    }

    /// `s.UnwatchFiles`.
    fn unwatch_files(&self, ctx: &Context, id: &WatcherId) -> project::client::ClientResult {
        if let Some(watcher) = self.builtin_watcher.lock().unwrap().clone() {
            if !self.watchers.has(id) {
                return Err(Box::new(Error::Message(format!(
                    "no file watcher exists with ID {id}"
                ))));
            }
            watcher
                .unwatch_files(id)
                .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
                    Box::new(Error::Message(format!(
                        "failed to unregister file watcher: {e}"
                    )))
                })?;
            self.watchers.delete(id);
            return Ok(());
        }
        if self.watchers.has(id) {
            self.send_client_request(
                ctx,
                &lsproto::CLIENT_UNREGISTER_CAPABILITY_INFO,
                Some(lsproto::UnregistrationParams {
                    unregisterations: Some(vec![lsproto::Unregistration {
                        id: id.clone(),
                        method: lsproto::Method::WorkspaceDidChangeWatchedFiles
                            .as_str()
                            .to_string(),
                    }]),
                }),
            )
            .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
                Box::new(Error::Message(format!("failed to unregister file watcher: {e}")))
            })?;
            self.watchers.delete(id);
            return Ok(());
        }
        Err(Box::new(Error::Message(format!(
            "no file watcher exists with ID {id}"
        ))))
    }

    /// `s.RegisterContentMapperExtensions`.
    fn register_content_mapper_extensions(
        &self,
        ctx: &Context,
        extensions: &[String],
    ) -> project::client::ClientResult {
        Server::register_content_mapper_extensions(self, ctx, extensions)
            .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> { Box::new(e) })
    }

    /// `s.RefreshDiagnostics`.
    fn refresh_diagnostics(&self, ctx: &Context) -> project::client::ClientResult {
        if !self
            .client_capabilities
            .get()
            .map(|c| c.workspace.diagnostics.refresh_support)
            .unwrap_or(false)
        {
            return Ok(());
        }
        if ctx.is_cancelled() {
            return Err(Box::new(Error::Canceled));
        }
        // Fire-and-forget: the client always returns null, and waiting for
        // the response can hang if the client is slow.
        self.send_client_request_fire_and_forget(
            &lsproto::WORKSPACE_DIAGNOSTIC_REFRESH_INFO,
            lsproto::NoParams {},
        )
        .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
            Box::new(Error::Message(format!("failed to refresh diagnostics: {e}")))
        })
    }

    /// `s.PublishDiagnostics`.
    fn publish_diagnostics(
        &self,
        _ctx: &Context,
        params: &lsproto::PublishDiagnosticsParams,
    ) -> project::client::ClientResult {
        self.send_notification(
            &lsproto::TEXT_DOCUMENT_PUBLISH_DIAGNOSTICS_INFO,
            Some(params.clone()),
        )
        .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> { Box::new(e) })
    }

    /// `s.RefreshInlayHints`.
    fn refresh_inlay_hints(&self, _ctx: &Context) -> project::client::ClientResult {
        if !self
            .client_capabilities
            .get()
            .map(|c| c.workspace.inlay_hint.refresh_support)
            .unwrap_or(false)
        {
            return Ok(());
        }
        self.send_client_request_fire_and_forget(
            &lsproto::WORKSPACE_INLAY_HINT_REFRESH_INFO,
            lsproto::NoParams {},
        )
        .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
            Box::new(Error::Message(format!("failed to refresh inlay hints: {e}")))
        })
    }

    /// `s.RefreshCodeLens`.
    fn refresh_code_lens(&self, _ctx: &Context) -> project::client::ClientResult {
        if !self
            .client_capabilities
            .get()
            .map(|c| c.workspace.code_lens.refresh_support)
            .unwrap_or(false)
        {
            return Ok(());
        }
        self.send_client_request_fire_and_forget(
            &lsproto::WORKSPACE_CODE_LENS_REFRESH_INFO,
            lsproto::NoParams {},
        )
        .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
            Box::new(Error::Message(format!("failed to refresh code lens: {e}")))
        })
    }

    /// `s.ProgressStart`.
    fn progress_start(&self, message: &diagnostics::Message, args: &[String]) {
        if let Some(p) = self.project_progress.lock().unwrap().clone() {
            p.start(message.clone(), args);
        }
    }

    /// `s.ProgressFinish`.
    fn progress_finish(&self, message: &diagnostics::Message, args: &[String]) {
        if let Some(p) = self.project_progress.lock().unwrap().clone() {
            p.finish(message.clone(), args);
        }
    }

    /// `s.SendTelemetry`.
    fn send_telemetry(
        &self,
        _ctx: &Context,
        telemetry: &lsproto::TelemetryEvent,
    ) -> project::client::ClientResult {
        if !self.telemetry_enabled.load(Ordering::SeqCst) {
            panic!("SendTelemetry called with telemetry disabled");
        }
        self.send_notification(&lsproto::TELEMETRY_EVENT_INFO, telemetry.clone())
            .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> { Box::new(e) })
    }

    /// `s.IsActive`.
    fn is_active(&self) -> bool {
        let last = self.last_request_time_ms.load(Ordering::SeqCst);
        last == 0 || now_millis() - last <= 60_000
    }

    /// `s.SetLocale`.
    fn set_locale(&self, locale: &str) {
        let mut new_locale = self.init_locale.get().cloned().unwrap_or_default();
        if locale != "auto" {
            let (parsed, ok) = tsc_locale::parse(locale);
            if !ok {
                return;
            }
            new_locale = parsed;
        }
        Server::set_locale(self, new_locale);
    }

    /// `s.GetLocale`.
    fn get_locale(&self) -> Locale {
        Server::get_locale(self)
    }
}

/// `s.NpmInstall`.
impl project::ata::NpmExecutor for Server {
    fn npm_install(
        &self,
        ctx: &Context,
        cwd: &tspath::RootedDirectoryPath,
        args: &[String],
    ) -> Result<Vec<u8>, Box<dyn std::error::Error + Send + Sync>> {
        match &self.npm_install {
            Some(npm_install) => npm_install(ctx, &cwd.as_string(), args)
                .map_err(|e| Box::new(e) as _),
            None => Err(Box::new(Error::Message(
                "npm install is not supported".to_string(),
            ))),
        }
    }
}

/// `s.NpmInstall` helper (`nil npmInstall` check).
#[allow(dead_code)]
fn npm_install_for(_s: &Server) {}

// ---------------------------------------------------------------------------
// Run loops

/// `AsyncWork` — Go's `func() error` run via `go ...`; the dispatch path
/// moves it to a spawned thread through [`SendShared`].
pub type AsyncWork = Box<dyn FnOnce() -> Result<(), Error>>;

/// `handler` — `func(*Server, context.Context, *lsproto.RequestMessage)
/// (func() error, error)`.
type HandlerFn =
    Box<dyn Fn(&Arc<Server>, &Context, &lsproto::RequestMessage) -> Result<Option<AsyncWork>, Error>
        + Send
        + Sync>;

type HandlerMap = HashMap<lsproto::Method, HandlerFn>;

impl Server {
    /// `s.Run(ctx)` — reads/dispatches/writes until exit or stream EOF.
    /// Returns `Err` containing `"context canceled"` for a normal `exit`
    /// notification, matching Go's `Run` (errgroup cancels the derived ctx).
    pub fn run(self: &Arc<Self>, ctx: &Context) -> Result<(), Error> {
        let (inner, cancel) = ctx.with_cancel();
        {
            let mut guard = self.background_cancel.lock().unwrap();
            if let Some(c) = guard.take() {
                *guard = Some(c);
            }
        }

        // `g.Go(func() { return s.dispatchLoop(ctx, lspExit) })`
        let dispatch_h = {
            let s = self.clone();
            let inner = inner.clone();
            let cancel = cancel.clone();
            std::thread::spawn(move || {
                let r = s.dispatch_loop(&inner, &cancel);
                if r.is_err() {
                    cancel.cancel();
                }
                r
            })
        };
        // `g.Go(func() { return s.writeLoop(ctx) })`
        let write_h = {
            let s = self.clone();
            let inner = inner.clone();
            let cancel = cancel.clone();
            std::thread::spawn(move || {
                let r = s.write_loop(&inner);
                if r.is_err() {
                    cancel.cancel();
                }
                r
            })
        };
        // `g.Go(select{ <-ctx.Done(); <-readLoopErr })` + `go s.readLoop(ctx)`
        // — the read thread stays detached, exactly as Go's blocking-read
        // goroutine is abandoned on shutdown.
        let (read_tx, read_rx) = mpsc::sync_channel::<Result<(), Error>>(1);
        {
            let s = self.clone();
            let inner = inner.clone();
            std::thread::spawn(move || {
                let _ = read_tx.send(s.read_loop(&inner));
            });
        }
        let read_wait_h = {
            let inner = inner.clone();
            std::thread::spawn(move || loop {
                if inner.is_cancelled() {
                    return Err(Error::Canceled);
                }
                match read_rx.recv_timeout(CALL_POLL_INTERVAL) {
                    Ok(r) => return r,
                    Err(mpsc::RecvTimeoutError::Timeout) => {}
                    Err(mpsc::RecvTimeoutError::Disconnected) => return Err(Error::Canceled),
                }
            })
        };

        let mut first_err: Option<Error> = None;
        for h in [dispatch_h, write_h, read_wait_h] {
            match h.join() {
                Ok(r) => {
                    if let Err(e) = r {
                        first_err = first_err.or(Some(e));
                    }
                }
                Err(payload) => {
                    first_err = first_err.or(Some(Error::Message(format!(
                        "panic: {}",
                        panic_payload_string(payload.as_ref())
                    ))));
                }
            }
        }
        if let Some(c) = self.background_cancel.lock().unwrap().take() {
            c.cancel();
        }
        if let Some(e) = first_err
            && !e.is_eof()
            && inner.is_cancelled()
        {
            return Err(e);
        }
        Ok(())
    }

    /// `s.readLoop(ctx)` — reads and enqueues/executes LSP messages.
    pub(crate) fn read_loop(self: &Arc<Self>, ctx: &Context) -> Result<(), Error> {
        loop {
            let msg = match self.r.read() {
                Ok(m) => m,
                Err(e) => {
                    if let Some(code) = e.code {
                        // `errors.Is(err, lsproto.ErrorCodeInvalidRequest)`
                        // / `InvalidParams` — Go distinguishes; the ported
                        // decoder reports InvalidRequest uniformly (see
                        // `Reader::read`). Send a response-id error when the
                        // request id could be recovered.
                        if let Err(e) =
                            self.send_error(e.partial_id.as_ref(), Error::Coded(code, e.message))
                        {
                            return Err(e);
                        }
                        continue;
                    }
                    return Err(Error::Read(e));
                }
            };

            if ctx.is_cancelled() {
                return Err(Error::Canceled);
            }

            match msg.kind {
                jsonrpc::MessageKind::Response => {
                    let resp = msg.as_response();
                    if let Some(id) = resp.id.as_ref()
                        && let Some(tx) =
                            self.pending_server_requests.lock().unwrap().get(&id_key(id))
                    {
                        let _ = tx.try_send(resp.clone());
                    }
                }
                _ => {
                    let req = msg.as_request().clone();
                    if self.initialize_params.get().is_none()
                        && req.method != lsproto::Method::Initialize
                    {
                        if let Err(e) = self.send_error(
                            req.id.as_ref(),
                            Error::Code(lsproto::ErrorCode::ServerNotInitialized),
                        ) {
                            return Err(e);
                        }
                        continue;
                    }
                    if self.request_queue.put(ctx, req).is_err() {
                        return Err(Error::Canceled);
                    }
                }
            }
        }
    }

    /// `s.dispatchLoop(ctx, lspExit)`.
    pub(crate) fn dispatch_loop(
        self: &Arc<Self>,
        ctx: &Context,
        lsp_exit: &CancelFunc,
    ) -> Result<(), Error> {
        loop {
            let req = match self.request_queue.get(ctx) {
                Ok(r) => r,
                Err(_) => return Err(Error::Canceled),
            };
            self.last_request_time_ms.store(now_millis(), Ordering::SeqCst);
            let start = Instant::now();
            let mut request_ctx = ctx.clone();
            tsc_locale::with_locale(&mut request_ctx, self.get_locale());
            let cancel = req.id.as_ref().map(|id| {
                let (id_ctx, cancel) =
                    tsc_core::context::with_request_id(&request_ctx, id.to_string()).with_cancel();
                request_ctx = id_ctx;
                self.pending_client_requests.lock().unwrap().insert(
                    id_key(id),
                    PendingClientRequest {
                        req: req.clone(),
                        cancel: cancel.clone(),
                    },
                );
                cancel
            });

            if self.logger.is_tracing() {
                let request_id = tsc_core::context::get_request_id(&request_ctx);
                self.logger.info(format_args!(
                    "handling method '{}{}'",
                    req.method,
                    if request_id.is_empty() {
                        String::new()
                    } else {
                        format!(" ({request_id})")
                    },
                ));
            }

            let req_for_error = req.clone();
            let remove_request = move |s: &Server| {
                if let Some(c) = &cancel {
                    c.cancel();
                }
                if let Some(id) = req_for_error.id.as_ref() {
                    s.pending_client_requests
                        .lock()
                        .unwrap()
                        .remove(&id_key(id));
                }
            };

            match self.handle_request_or_notification(&request_ctx, &req) {
                Err(err) => {
                    remove_request(self);
                    self.logger.info(format_args!(
                        "method '{method}' errored in {:?}: {err}",
                        start.elapsed(),
                        method = req.method
                    ));
                    self.handle_request_error(req.id.as_ref(), err, lsp_exit);
                }
                Ok(Some(work)) => {
                    let remove_request = SendShared(remove_request);
                    let s = self.clone();
                    let work = SendShared(work);
                    // `req` is also read by the post-dispatch tracing below;
                    // the spawned thread gets its own clone. `lsp_exit` is a
                    // `&CancelFunc` — clone the `Arc`-backed func so the
                    // thread closure is `'static`.
                    let req = req.clone();
                    let lsp_exit = lsp_exit.clone();
                    std::thread::spawn(move || {
                        let work = work.into_inner();
                        let remove_request = remove_request.into_inner();
                        let r = s.run_recovered(req.id.as_ref(), &req.method, work);
                        if let Err(err) = r {
                            s.handle_request_error(req.id.as_ref(), err, &lsp_exit);
                        }
                        remove_request(&s);
                    });
                }
                Ok(None) => {
                    remove_request(self);
                }
            }

            if self.logger.is_tracing() {
                let request_id = tsc_core::context::get_request_id(&request_ctx);
                self.logger.info(format_args!(
                    "handled method '{}{}' in {:?}",
                    req.method,
                    if request_id.is_empty() {
                        String::new()
                    } else {
                        format!(" ({request_id})")
                    },
                    start.elapsed(),
                ));
            }
        }
    }

    /// `handleError(err)` — error teardown inside the dispatch loop.
    pub(crate) fn handle_request_error(
        &self,
        id: Option<&jsonrpc::ID>,
        err: Error,
        lsp_exit: &CancelFunc,
    ) {
        if err.is_canceled() {
            if let Err(e) =
                self.send_error(id, Error::Code(lsproto::ErrorCode::RequestCancelled))
            {
                self.logger
                    .error(format_args!("failed to send error response: {e}"));
                lsp_exit.cancel();
            }
        } else if err.is_eof() {
            lsp_exit.cancel();
        } else if let Err(e) = self.send_error(id, err) {
            self.logger
                .error(format_args!("failed to send error response: {e}"));
            lsp_exit.cancel();
        }
    }

    /// `s.writeLoop(ctx)`.
    pub(crate) fn write_loop(self: &Arc<Self>, ctx: &Context) -> Result<(), Error> {
        loop {
            let msg = match self.outgoing_queue.get(ctx) {
                Ok(m) => m,
                Err(_) => return Err(Error::Canceled),
            };
            let mut log = self.logger.is_tracing();
            if msg.kind == jsonrpc::MessageKind::Response
                && msg.as_response().error.is_some()
            {
                log = true;
            }
            if log {
                self.logger.info(format_args!("sending response: {msg:?}"));
            }
            if let Err(err) = self.w.write(&msg) {
                // `errors.As(err, &marshalErr)` — a marshal failure of a
                // response without an error is reported as an error response.
                if let Error::Marshal(_) = err
                    && msg.kind == jsonrpc::MessageKind::Response
                    && msg.as_response().error.is_none()
                    && let Some(id) = msg.as_response().id.as_ref()
                {
                    if let Err(e) = self.send_error(Some(id), err) {
                        return Err(Error::Message(format!(
                            "failed to write message: {e}"
                        )));
                    }
                    continue;
                }
                return Err(Error::Message(format!("failed to write message: {err}")));
            }
        }
    }

    /// `s.send(msg)`.
    pub(crate) fn send(&self, msg: lsproto::Message) -> Result<(), Error> {
        self.outgoing_queue
            .put(&self.background_ctx, msg)
            .map_err(Error::from_queue)
    }

    /// `s.sendRequest(ctx, request)` — blocks until the response arrives,
    /// `ctx` is cancelled, or the queue fails.
    pub(crate) fn send_client_request<P: Serialize, R: DeserializeOwned + Default>(
        &self,
        ctx: &Context,
        info: &lsproto::RequestInfo<P, R>,
        params: P,
    ) -> Result<R, Error> {
        let id = jsonrpc::new_id_string(&format!(
            "ts{}",
            self.client_seq.fetch_add(1, Ordering::SeqCst) + 1
        ));
        let req = info.new_request_message(Some(id.clone()), params);
        let (tx, rx) = mpsc::sync_channel(1);
        self.pending_server_requests
            .lock()
            .unwrap()
            .insert(id_key(&id), tx);
        let res = (|| {
            self.send(req.message())?;
            loop {
                if ctx.is_cancelled() {
                    return Err(Error::Canceled);
                }
                match rx.recv_timeout(CALL_POLL_INTERVAL) {
                    Ok(resp) => return info.unmarshal_result(resp.result.as_ref()).map_err(|e| Error::Message(e.to_string())),
                    Err(mpsc::RecvTimeoutError::Timeout) => {}
                    Err(mpsc::RecvTimeoutError::Disconnected) => {
                        return Err(Error::Message("request channel closed".to_string()));
                    }
                }
            }
        })();
        self.pending_server_requests
            .lock()
            .unwrap()
            .remove(&id_key(&id));
        res
    }

    /// `s.sendClientRequestFireAndForget(ctx, request)` — no response
    /// tracking (client may not respond).
    pub(crate) fn send_client_request_fire_and_forget<P: Serialize, R: DeserializeOwned>(
        &self,
        info: &lsproto::RequestInfo<P, R>,
        params: P,
    ) -> Result<(), Error> {
        let id = jsonrpc::new_id_string(&format!(
            "ts{}",
            self.client_seq.fetch_add(1, Ordering::SeqCst) + 1
        ));
        let req = info.new_request_message(Some(id), params);
        self.send(req.message())
    }

    /// `s.sendNotification(ctx, notification)` — fires and forgets.
    pub(crate) fn send_notification<P: Serialize>(
        &self,
        info: &lsproto::NotificationInfo<P>,
        params: P,
    ) -> Result<(), Error> {
        let n = info.new_notification_message(params);
        self.send(n.message())
    }

    /// `s.sendResult(id, result)`.
    pub(crate) fn send_result<R: Serialize>(
        &self,
        id: Option<&jsonrpc::ID>,
        result: &R,
    ) -> Result<(), Error> {
        let data = json::marshal(result, &[]).map_err(|e| Error::Marshal(e.to_string()))?;
        let raw = RawValue::from_string(
            String::from_utf8(data).map_err(|e| Error::Marshal(e.to_string()))?,
        )
        .map_err(|e| Error::Marshal(e.to_string()))?;
        self.send(lsproto::ResponseMessage {
            id: id.cloned(),
            result: Some(raw),
            ..Default::default()
        }
        .message())
    }

    /// `s.sendError(id, err)`.
    pub(crate) fn send_error(&self, id: Option<&jsonrpc::ID>, err: Error) -> Result<(), Error> {
        if id.is_none() && err.error_code() != lsproto::ErrorCode::InvalidRequest {
            self.logger
                .error(format_args!("dropping error for message with no id: {err}"));
            return Ok(());
        }
        let code = err.error_code();
        self.send(lsproto::ResponseMessage {
            id: id.cloned(),
            error: Some(jsonrpc::ResponseError {
                code: code.0,
                message: err.to_string(),
                ..Default::default()
            }),
            ..Default::default()
        }
        .message())
    }

    /// `s.runAsyncWork` — runs `work` with `s.recover(req)` semantics
    /// (`recover` becomes a `catch_unwind` boundary).
    pub(crate) fn run_recovered(
        self: &Arc<Self>,
        id: Option<&jsonrpc::ID>,
        method: &lsproto::Method,
        work: AsyncWork,
    ) -> Result<(), Error> {
        match catch_unwind(AssertUnwindSafe(work)) {
            Ok(r) => r,
            Err(payload) => {
                // `s.recover(req)`.
                let panic_msg = panic_payload_string(payload.as_ref());
                let stack = std::backtrace::Backtrace::force_capture().to_string();
                self.logger.error(format_args!(
                    "panic handling request {method}: {panic_msg}\n{stack}"
                ));
                if let Some(id) = id {
                    let _ = self.send_error(
                        Some(id),
                        Error::Coded(
                            lsproto::ErrorCode::InternalError,
                            format!("panic handling request {method}: {panic_msg}"),
                        ),
                    );
                } else {
                    self.logger.error(format_args!(
                        "unhandled panic in notification {method} {panic_msg}"
                    ));
                }
                if self.telemetry_enabled.load(Ordering::SeqCst) {
                    let _ = self.send_notification(
                        &lsproto::TELEMETRY_EVENT_INFO,
                        lsproto::TelemetryEvent {
                            request_failure_telemetry_event: Some(
                                lsproto::RequestFailureTelemetryEvent {
                                    properties: Some(
                                        lsproto::RequestFailureTelemetryProperties {
                                            error_code: lsproto::ErrorCode::InternalError
                                                .to_string(),
                                            request_method: method.as_str().replace('/', "."),
                                            stack: sanitize_stack_trace(&stack),
                                        },
                                    ),
                                    ..Default::default()
                                },
                            ),
                            ..Default::default()
                        },
                    );
                }
                Ok(())
            }
        }
    }
}

/// `panicValue.Error()` stand-in — extracts `String`/`&str` payloads.
pub(crate) fn panic_payload_string(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<String>() {
        return s.clone();
    }
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        return s.to_string();
    }
    format!("{payload:?}")
}

fn now_millis() -> i64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as i64)
        .unwrap_or(0)
}

// ---------------------------------------------------------------------------
// Dispatch

/// `HasTextDocumentUri` params plumbing — the declared param type is
/// `Option<P>`; unwrap to reach the uri.
trait UriParam {
    fn uri(&self) -> lsproto::DocumentUri;
}
/// `lsproto.HasTextDocumentURI` impls — generated per params struct (the Go
/// marker interface has no Rust impls generated, so `text_document.uri` is
/// spelled out for each `Option<Params>` used by the LS handlers).
macro_rules! uri_param {
    ($($t:ty),* $(,)?) => {$(
        impl UriParam for Option<$t> {
            fn uri(&self) -> lsproto::DocumentUri {
                // `TextDocumentURI()` is generated per params struct
                // (`VSOnAutoInsertParams` uses `vs_text_document`).
                self.as_ref()
                    .map(|p| <$t>::text_document_uri(p))
                    .unwrap_or_default()
            }
        }
    )*};
}
uri_param!(
    lsproto::DocumentDiagnosticParams,
    lsproto::HoverParams,
    lsproto::DefinitionParams,
    lsproto::TextDocumentPositionParams,
    lsproto::TypeDefinitionParams,
    lsproto::SignatureHelpParams,
    lsproto::DocumentFormattingParams,
    lsproto::DocumentRangeFormattingParams,
    lsproto::DocumentOnTypeFormattingParams,
    lsproto::DocumentSymbolParams,
    lsproto::DocumentHighlightParams,
    lsproto::MultiDocumentHighlightParams,
    lsproto::SelectionRangeParams,
    lsproto::InlayHintParams,
    lsproto::CodeLensParams,
    lsproto::CodeActionParams,
    lsproto::CallHierarchyPrepareParams,
    lsproto::FoldingRangeParams,
    lsproto::PrepareRenameParams,
    lsproto::LinkedEditingRangeParams,
    lsproto::CompletionParams,
    lsproto::VSOnAutoInsertParams,
    lsproto::ReferenceParams,
    lsproto::ImplementationParams,
    lsproto::SemanticTokensParams,
    lsproto::SemanticTokensRangeParams,
);

impl Server {
    /// `s.handleRequestOrNotification`.
    pub(crate) fn handle_request_or_notification(
        self: &Arc<Self>,
        ctx: &Context,
        req: &lsproto::RequestMessage,
    ) -> Result<Option<AsyncWork>, Error> {
        if req.method == lsproto::Method::CancelRequest {
            let params: Option<lsproto::CancelParams> = req.unmarshal_params()?;
            if let Some(params) = params {
                self.cancel_request(&params.id);
            }
            return Ok(None);
        }
        let Some(handler) = handlers().get(&req.method) else {
            return Err(Error::Code(lsproto::ErrorCode::MethodNotFound));
        };
        match handler(self, ctx, req) {
            Err(err) => {
                // `handleContentMapperProjectFailure` — requests against a
                // file only served by an unloaded inferred project return a
                // "successful" empty response instead of an error.
                if err.is_no_project_for_unknown_script_kind()
                    && let Some(resp) = content_mapper_fallback_response(&req.method)
                {
                    self.send_result(req.id.as_ref(), &resp)?;
                    return Ok(None);
                }
                Err(err)
            }
            ok => ok,
        }
    }

    /// `s.cancelRequest(rawId)`.
    fn cancel_request(&self, raw_id: &lsproto::IntegerOrString) {
        let id = lsproto::new_id(raw_id);
        let pending = self.pending_client_requests.lock().unwrap();
        if let Some(req) = pending.get(&id_key(&id)) {
            req.cancel.cancel();
        }
    }
}

/// `contentMapperFallbackResponse` — `Result` for methods served by
/// inferred projects that failed to load for an unknown script kind.
fn content_mapper_fallback_response(method: &lsproto::Method) -> Option<Box<RawValue>> {
    let value = if *method == lsproto::Method::TextDocumentDiagnostic {
        json::marshal(
            &lsproto::RelatedFullDocumentDiagnosticReportOrUnchangedDocumentDiagnosticReport {
                full_document_diagnostic_report: Some(
                    lsproto::RelatedFullDocumentDiagnosticReport {
                        items: Some(vec![]),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            },
            &[],
        )
        .ok()?
    } else if [
        // `Method` wraps `Cow<str>` — not usable in match patterns.
        lsproto::Method::TextDocumentHover,
        lsproto::Method::TextDocumentSignatureHelp,
        lsproto::Method::TextDocumentDefinition,
        lsproto::Method::TextDocumentTypeDefinition,
        lsproto::Method::TextDocumentImplementation,
        lsproto::Method::TextDocumentReferences,
        lsproto::Method::TextDocumentDocumentHighlight,
        lsproto::Method::TextDocumentCompletion,
        lsproto::Method::TextDocumentRename,
    ]
    .contains(method)
    {
        b"null".to_vec()
    } else {
        return None;
    };
    RawValue::from_string(String::from_utf8(value).ok()?).ok()
}

// ---------------------------------------------------------------------------
// Handler registration

fn register_notification_handler<P, F>(map: &mut HandlerMap, method: lsproto::Method, f: F)
where
    P: DeserializeOwned + Default + 'static,
    F: Fn(&Arc<Server>, &Context, P) -> Result<(), Error> + Send + Sync + 'static,
{
    map.insert(
        method,
        Box::new(move |s, ctx, req| {
            if s.session_opt().is_none() && req.method != lsproto::Method::Initialized {
                return Err(Error::Code(lsproto::ErrorCode::ServerNotInitialized));
            }
            let params: P = req.unmarshal_params()?;
            f(s, ctx, params)?;
            if ctx.is_cancelled() {
                return Err(Error::Canceled);
            }
            Ok(None)
        }),
    );
}

fn register_request_handler<P, R, F>(map: &mut HandlerMap, method: lsproto::Method, f: F)
where
    P: DeserializeOwned + Default + 'static,
    R: Serialize,
    F: Fn(&Arc<Server>, &Context, P, &lsproto::RequestMessage) -> Result<R, Error>
        + Send
        + Sync
        + 'static,
{
    map.insert(
        method,
        Box::new(move |s, ctx, req| {
            if s.session_opt().is_none() && req.method != lsproto::Method::Initialize {
                return Err(Error::Code(lsproto::ErrorCode::ServerNotInitialized));
            }
            let params: P = req.unmarshal_params()?;
            let resp = f(s, ctx, params, req)?;
            if ctx.is_cancelled() {
                return Err(Error::Canceled);
            }
            s.send_result(req.id.as_ref(), &resp)?;
            Ok(None)
        }),
    );
}

fn register_ls_document_handler<P, R, F>(map: &mut HandlerMap, method: lsproto::Method, f: F)
where
    P: DeserializeOwned + Default + UriParam + 'static,
    R: Serialize,
    F: for<'h> Fn(&Arc<Server>, &Context, &LanguageService<'h>, P) -> Result<R, Error>
        + Send
        + Sync
        + 'static,
{
    // The outer handler is `Fn` (stored in the map); `f` is shared with the
    // spawned `FnOnce` work item via `Arc`.
    let f = Arc::new(f);
    map.insert(
        method,
        Box::new(move |s, ctx, req| {
            let Some(session) = s.session_opt() else {
                return Err(Error::Code(lsproto::ErrorCode::ServerNotInitialized));
            };
            let params: P = req.unmarshal_params()?;
            let sls = session
                .get_language_service(ctx, &params.uri())
                .map_err(Error::from_session)?;
            let s2 = s.clone();
            let ctx2 = ctx.clone();
            let id = req.id.clone();
            let f = f.clone();
            Ok(Some(Box::new(move || {
                let ls = sls.language_service();
                let resp = f(&s2, &ctx2, &ls, params)?;
                if let Some(session) = s2.session_opt() {
                    session.enqueue_publish_global_diagnostics();
                }
                if ctx2.is_cancelled() {
                    return Err(Error::Canceled);
                }
                s2.send_result(id.as_ref(), &resp)
            })))
        }),
    );
}

fn register_ls_auto_imports_handler<P, R, F>(
    map: &mut HandlerMap,
    method: lsproto::Method,
    f: F,
) where
    P: DeserializeOwned + Default + UriParam + Clone + 'static,
    R: Serialize,
    F: for<'h> Fn(&Arc<Server>, &Context, &LanguageService<'h>, P) -> Result<R, Error>
        + Send
        + Sync
        + 'static,
{
    // `f` is shared with the spawned `FnOnce` work item via `Arc` (see
    // `register_ls_document_handler`).
    let f = Arc::new(f);
    map.insert(
        method,
        Box::new(move |s, ctx, req| {
            let Some(session) = s.session_opt() else {
                return Err(Error::Code(lsproto::ErrorCode::ServerNotInitialized));
            };
            let params: P = req.unmarshal_params()?;
            let sls = session
                .get_language_service(ctx, &params.uri())
                .map_err(Error::from_session)?;
            let s2 = s.clone();
            let ctx2 = ctx.clone();
            let id = req.id.clone();
            let f = f.clone();
            Ok(Some(Box::new(move || {
                let ls = sls.language_service();
                let resp = match f(&s2, &ctx2, &ls, params.clone()) {
                    Err(e) if e.is_needs_auto_imports() => {
                        let sls2 = session
                            .get_language_service_with_auto_imports(
                                &ctx2,
                                &sls.snapshot,
                                &params.uri(),
                            )
                            .map_err(Error::from_session)?;
                        if ctx2.is_cancelled() {
                            return Err(Error::Canceled);
                        }
                        let ls2 = sls2.language_service();
                        match f(&s2, &ctx2, &ls2, params) {
                            Err(e) if e.is_needs_auto_imports() => {
                                // Go: `panic(info.Method + " returned
                                // ErrNeedsAutoImports even after enabling
                                // auto imports")`.
                                panic!("returned ErrNeedsAutoImports even after enabling auto imports");
                            }
                            r => r?,
                        }
                    }
                    r => r?,
                };
                if ctx2.is_cancelled() {
                    return Err(Error::Canceled);
                }
                s2.send_result(id.as_ref(), &resp)
            })))
        }),
    );
}

fn register_multi_project_handler<P, R, F>(map: &mut HandlerMap, method: lsproto::Method, f: F)
where
    P: DeserializeOwned + Default + UriParam + 'static,
    R: Serialize,
    F: for<'h> Fn(
            &LanguageService<'h>,
            &Context,
            P,
            Option<&dyn ls::findallreferences::CrossProjectOrchestrator<'h>>,
        ) -> Result<R, Error>
        + Send
        + Sync
        + 'static,
{
    // `f` is shared with the spawned `FnOnce` work item via `Arc` (see
    // `register_ls_document_handler`).
    let f = Arc::new(f);
    map.insert(
        method,
        Box::new(move |s, ctx, req| {
            let Some(session) = s.session_opt() else {
                return Err(Error::Code(lsproto::ErrorCode::ServerNotInitialized));
            };
            let params: P = req.unmarshal_params()?;
            let (sls, all_projects) = session
                .get_language_service_and_projects_for_file(ctx, &params.uri())
                .map_err(Error::from_session)?;
            let s2 = s.clone();
            let ctx2 = ctx.clone();
            let id = req.id.clone();
            let f = f.clone();
            Ok(Some(Box::new(move || {
                let ls = sls.language_service();
                let orchestrator = ServerOrchestrator {
                    server: &s2,
                    snapshot: &sls.snapshot,
                    default_project: sls.project.clone(),
                    all_projects,
                    known: std::cell::RefCell::new(HashMap::new()),
                };
                orchestrator.register_known();
                let resp = f(&ls, &ctx2, params, Some(&orchestrator))?;
                if ctx2.is_cancelled() {
                    return Err(Error::Canceled);
                }
                s2.send_result(id.as_ref(), &resp)
            })))
        }),
    );
}

// ---------------------------------------------------------------------------
// Cross-project orchestrator

/// `crossProjectProject` — `ls::Project` adapter over `Rc<project::project::Project>`.
struct LsProject(Rc<project::project::Project>);

impl ls::Project for LsProject {
    fn id(&self) -> String {
        self.0.id.0.clone()
    }
    fn get_program(&self) -> Option<Rc<tsc_compiler::program::Program>> {
        self.0.get_program().cloned()
    }
    fn has_file(&self, file_name: &tspath::RootedFilePath) -> bool {
        self.0.has_file(file_name)
    }
}

/// `type crossProjectOrchestrator struct`.
///
/// PORT: Go's orchestrator re-snapshots the session on each
/// `GetLanguageServiceForProjectWithFile` call; the Rust `LanguageService`
/// borrows its host for `'h`, so this implementation pins the request's
/// snapshot as the host while fetching the (possibly fresher) project via
/// the session — matching the "latch onto a specific snapshot" guidance
/// elsewhere in the Go source.
pub(crate) struct ServerOrchestrator<'s, 'h> {
    pub(crate) server: &'s Arc<Server>,
    pub(crate) snapshot: &'h project::snapshot::Snapshot,
    pub(crate) default_project: Rc<project::project::Project>,
    pub(crate) all_projects: Vec<Rc<project::project::Project>>,
    /// concrete `project::Project`s keyed by id for trait-object callbacks.
    pub(crate) known: std::cell::RefCell<HashMap<String, Rc<project::project::Project>>>,
}

impl ServerOrchestrator<'_, '_> {
    pub(crate) fn register_known(&self) {
        let mut known = self.known.borrow_mut();
        known.insert(self.default_project.id.0.clone(), self.default_project.clone());
        for p in &self.all_projects {
            known.insert(p.id.0.clone(), p.clone());
        }
    }

    fn wrap(&self, p: &Rc<project::project::Project>) -> Rc<dyn ls::findallreferences::Project> {
        self.known
            .borrow_mut()
            .insert(p.id.0.clone(), p.clone());
        Rc::new(LsProject(p.clone()))
    }
}

impl<'h> ls::findallreferences::CrossProjectOrchestrator<'h> for ServerOrchestrator<'_, 'h> {
    /// `GetDefaultProject`.
    fn get_default_project(&self) -> Rc<dyn ls::findallreferences::Project> {
        self.wrap(&self.default_project.clone())
    }

    /// `GetAllProjectsForInitialRequest`.
    fn get_all_projects_for_initial_request(&self) -> Vec<Rc<dyn ls::findallreferences::Project>> {
        self.all_projects
            .clone()
            .iter()
            .map(|p| self.wrap(p))
            .collect()
    }

    /// `GetLanguageServiceForProjectWithFile`.
    fn get_language_service_for_project_with_file(
        &self,
        ctx: &Context,
        project: &Rc<dyn ls::findallreferences::Project>,
        uri: &lsproto::DocumentUri,
    ) -> Option<Rc<LanguageService<'h>>> {
        let session = self.server.session_opt()?;
        let concrete = self.known.borrow().get(&project.id()).cloned()?;
        let sls = session.get_language_service_for_project_with_file(ctx, &concrete, uri)?;
        let program = sls.project.get_program().cloned()?;
        Some(Rc::new(ls::languageservice::new_language_service(
            ls::autoimport::ProjectId(Rc::from(sls.project.id.0.as_str())),
            program,
            self.snapshot,
            uri.file_name().as_string(),
        )))
    }

    /// `GetProjectsForFile`.
    fn get_projects_for_file(
        &self,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<Vec<Rc<dyn ls::findallreferences::Project>>, ls::Error> {
        let session = self
            .server
            .session_opt()
            .ok_or_else(|| ls::Error::Message("no session".to_string()))?;
        let projects = session
            .get_projects_for_file(ctx, uri)
            .map_err(ls::Error::Message)?;
        Ok(projects.iter().map(|p| self.wrap(p)).collect())
    }

    /// `GetProjectsLoadingProjectTree`.
    fn get_projects_loading_project_tree(
        &self,
        ctx: &Context,
        requested_project_trees: &Set<tspath::PathKey>,
    ) -> Vec<Rc<dyn ls::findallreferences::Project>> {
        let Some(session) = self.server.session_opt() else {
            return Vec::new();
        };
        let mut out: Vec<Rc<project::project::Project>> = Vec::new();
        session.with_snapshot_loading_project_tree(ctx, requested_project_trees, |snapshot| {
            out = snapshot.project_collection.language_service_projects();
        });
        out.iter().map(|p| self.wrap(p)).collect()
    }
}

// ---------------------------------------------------------------------------
// API sessions

impl Server {
    /// `s.generateAPIPipePath`.
    pub(crate) fn generate_api_pipe_path() -> String {
        static CTR: AtomicI64 = AtomicI64::new(0);
        ipc::generate_pipe_path(&format!(
            "tsgo-api-{}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|d| d.as_nanos())
                .unwrap_or(0),
            CTR.fetch_add(1, Ordering::Relaxed),
        ))
    }

    /// `s.removeAPISession(id)`.
    pub(crate) fn remove_api_session(&self, id: &str) {
        if let Some(state) = self.api_sessions.lock().unwrap().remove(id) {
            state.stop();
        }
    }

    /// `s.closeAPISessions`.
    pub(crate) fn close_api_sessions(&self) {
        let states: Vec<Arc<ApiSessionState>> =
            self.api_sessions.lock().unwrap().drain().map(|(_, s)| s).collect();
        for state in states {
            state.stop();
        }
    }

    /// `s.getAPISession(id)`.
    pub(crate) fn get_api_session(&self, id: &str) -> Option<Arc<ApiSessionState>> {
        self.api_sessions.lock().unwrap().get(id).cloned()
    }
}

/// `s.getAPISession`-style helper for the accept goroutine.
impl ApiSessionState {
    /// `apiCtx`-derived connection run — Go's per-accepted-connection
    /// `conn.Run(apiCtx)` call.
    #[cfg(unix)]
    fn run_connection(
        self: &Arc<Self>,
        rwc: Arc<std::os::unix::net::UnixStream>,
        ctx: &Context,
    ) {
        if !self.attach_connection(rwc.clone()) {
            return;
        }
        let conn = Arc::new(ipc::new_async_conn(
            rwc,
            self.session.clone() as Arc<dyn ipc::Handler>,
        ));
        self.session.set_connection(conn.clone());
        conn.run(ctx);
    }
}

// ---------------------------------------------------------------------------
// Configuration / content-mapper registration helpers

/// `supportedCodeActionKinds`.
pub(crate) fn supported_code_action_kinds() -> Vec<lsproto::CodeActionKind> {
    vec![
        lsproto::CodeActionKind::QuickFix,
        lsproto::CodeActionKind(std::borrow::Cow::Borrowed("source.organizeImports.ts")),
        lsproto::CodeActionKind(std::borrow::Cow::Borrowed("source.removeUnusedImports.ts")),
        lsproto::CodeActionKind(std::borrow::Cow::Borrowed("source.sortImports.ts")),
        lsproto::CodeActionKind(std::borrow::Cow::Borrowed("source.fixAll.ts")),
    ]
}

/// `fileRenameFilters`.
pub(crate) fn file_rename_filters() -> Vec<lsproto::FileOperationFilter> {
    vec![lsproto::FileOperationFilter {
        scheme: Some("file".to_string()),
        pattern: Some(lsproto::FileOperationPattern {
            glob: "**/*.{ts,tsx,js,jsx,cts,cjs,mts,mjs,json}".to_string(),
            ..Default::default()
        }),
    }]
}

/// Content-mapper dynamic-registration ids (`contentMapper*RegistrationID`).
mod content_mapper_ids {
    pub const DID_OPEN: &str = "content-mapper-did-open";
    pub const DID_CHANGE: &str = "content-mapper-did-change";
    pub const DID_CLOSE: &str = "content-mapper-did-close";
    pub const DIAGNOSTIC: &str = "content-mapper-diagnostic";
    pub const HOVER: &str = "content-mapper-hover";
    pub const SIGNATURE_HELP: &str = "content-mapper-signature-help";
    pub const DEFINITION: &str = "content-mapper-definition";
    pub const TYPE_DEFINITION: &str = "content-mapper-type-definition";
    pub const IMPLEMENTATION: &str = "content-mapper-implementation";
    pub const REFERENCES: &str = "content-mapper-references";
    pub const DOCUMENT_HIGHLIGHT: &str = "content-mapper-document-highlight";
    pub const COMPLETION: &str = "content-mapper-completion";
    pub const RENAME: &str = "content-mapper-rename";
    pub const SEMANTIC_TOKENS: &str = "content-mapper-semantic-tokens";
    pub const DOCUMENT_SYMBOL: &str = "content-mapper-document-symbol";
    pub const FOLDING_RANGE: &str = "content-mapper-folding-range";
    pub const SELECTION_RANGE: &str = "content-mapper-selection-range";
    pub const INLAY_HINT: &str = "content-mapper-inlay-hint";
    pub const CODE_LENS: &str = "content-mapper-code-lens";
    pub const CODE_ACTION: &str = "content-mapper-code-action";
    pub const FORMATTING: &str = "content-mapper-formatting";
    pub const RANGE_FORMATTING: &str = "content-mapper-range-formatting";
    pub const ON_TYPE_FORMATTING: &str = "content-mapper-on-type-formatting";
    pub const LINKED_EDITING: &str = "content-mapper-linked-editing";
    pub const CALL_HIERARCHY: &str = "content-mapper-call-hierarchy";
    pub const WILL_RENAME_FILES: &str = "content-mapper-will-rename-files";
}

impl Server {
    /// `s.supportsContentMapperRegistration`.
    pub(crate) fn supports_content_mapper_registration(&self, id: &str) -> bool {
        use content_mapper_ids::*;
        let Some(caps) = self.client_capabilities.get() else {
            return false;
        };
        let td = &caps.text_document;
        match id {
            DID_OPEN | DID_CHANGE | DID_CLOSE => td.synchronization.dynamic_registration,
            DIAGNOSTIC => td.diagnostic.dynamic_registration,
            HOVER => td.hover.dynamic_registration,
            SIGNATURE_HELP => td.signature_help.dynamic_registration,
            DEFINITION => td.definition.dynamic_registration,
            TYPE_DEFINITION => td.type_definition.dynamic_registration,
            IMPLEMENTATION => td.implementation.dynamic_registration,
            REFERENCES => td.references.dynamic_registration,
            DOCUMENT_HIGHLIGHT => td.document_highlight.dynamic_registration,
            COMPLETION => td.completion.dynamic_registration,
            RENAME => td.rename.dynamic_registration,
            SEMANTIC_TOKENS => td.semantic_tokens.dynamic_registration,
            DOCUMENT_SYMBOL => td.document_symbol.dynamic_registration,
            FOLDING_RANGE => td.folding_range.dynamic_registration,
            SELECTION_RANGE => td.selection_range.dynamic_registration,
            INLAY_HINT => td.inlay_hint.dynamic_registration,
            CODE_LENS => td.code_lens.dynamic_registration,
            CODE_ACTION => td.code_action.dynamic_registration,
            FORMATTING => td.formatting.dynamic_registration,
            RANGE_FORMATTING => td.range_formatting.dynamic_registration,
            ON_TYPE_FORMATTING => td.on_type_formatting.dynamic_registration,
            LINKED_EDITING => td.linked_editing_range.dynamic_registration,
            CALL_HIERARCHY => td.call_hierarchy.dynamic_registration,
            WILL_RENAME_FILES => {
                caps.workspace.file_operations.dynamic_registration
                    && caps.workspace.file_operations.will_rename
            }
            _ => false,
        }
    }
}

/// `handlers` — the LSP method dispatch table (`sync.OnceValue`).
pub(crate) fn handlers() -> &'static HandlerMap {
    static HANDLERS: LazyLock<HandlerMap> = LazyLock::new(|| {
        let mut m = HandlerMap::new();
        register_request_handler(&mut m, lsproto::Method::Initialize, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_initialize(ctx, p, r));
        register_notification_handler(&mut m, lsproto::Method::Initialized, |s: &Arc<Server>, ctx: &Context, p| s.handle_initialized(ctx, p));
        register_request_handler(&mut m, lsproto::Method::Shutdown, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_shutdown(ctx, p, r));
        register_notification_handler(&mut m, lsproto::Method::Exit, |s: &Arc<Server>, ctx: &Context, p| s.handle_exit(ctx, p));
        register_notification_handler(
            &mut m,
            lsproto::Method::WorkspaceDidChangeConfiguration,
            Server::handle_did_change_workspace_configuration,
        );
        register_notification_handler(&mut m, lsproto::Method::TextDocumentDidOpen, |s: &Arc<Server>, ctx: &Context, p| s.handle_did_open(ctx, p));
        register_notification_handler(&mut m, lsproto::Method::TextDocumentDidChange, |s: &Arc<Server>, ctx: &Context, p| s.handle_did_change(ctx, p));
        register_notification_handler(&mut m, lsproto::Method::TextDocumentDidSave, |s: &Arc<Server>, ctx: &Context, p| s.handle_did_save(ctx, p));
        register_notification_handler(&mut m, lsproto::Method::TextDocumentDidClose, |s: &Arc<Server>, ctx: &Context, p| s.handle_did_close(ctx, p));
        register_notification_handler(
            &mut m,
            lsproto::Method::WorkspaceDidChangeWatchedFiles,
            Server::handle_did_change_watched_files,
        );
        register_notification_handler(&mut m, lsproto::Method::SetTrace, |s: &Arc<Server>, ctx: &Context, p| s.handle_set_trace(ctx, p));
        register_notification_handler(
            &mut m,
            lsproto::Method::CustomSetLogVerbosity,
            Server::handle_set_log_verbosity,
        );
        register_request_handler(
            &mut m,
            lsproto::Method::WorkspaceWillRenameFiles,
            Server::handle_will_rename_files,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentDiagnostic,
            Server::handle_document_diagnostic,
        );
        register_ls_document_handler(&mut m, lsproto::Method::TextDocumentHover, |s: &Arc<Server>, ctx: &Context, l, p| s.handle_hover(ctx, l, p));
        register_ls_document_handler(&mut m, lsproto::Method::TextDocumentDefinition, |s: &Arc<Server>, ctx: &Context, l, p| s.handle_definition(ctx, l, p));
        register_ls_document_handler(
            &mut m,
            lsproto::Method::CustomTextDocumentSourceDefinition,
            Server::handle_source_definition,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentTypeDefinition,
            Server::handle_type_definition,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentSignatureHelp,
            Server::handle_signature_help,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentFormatting,
            Server::handle_document_format,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentRangeFormatting,
            Server::handle_document_range_format,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentOnTypeFormatting,
            Server::handle_document_on_type_format,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentDocumentSymbol,
            Server::handle_document_symbol,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentDocumentHighlight,
            Server::handle_document_highlight,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::CustomTextDocumentMultiDocumentHighlight,
            Server::handle_multi_document_highlight,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentSelectionRange,
            Server::handle_selection_range,
        );
        register_ls_document_handler(&mut m, lsproto::Method::TextDocumentInlayHint, |s: &Arc<Server>, ctx: &Context, l, p| s.handle_inlay_hint(ctx, l, p));
        register_ls_document_handler(&mut m, lsproto::Method::TextDocumentCodeLens, |s: &Arc<Server>, ctx: &Context, l, p| s.handle_code_lens(ctx, l, p));
        register_ls_document_handler(&mut m, lsproto::Method::TextDocumentCodeAction, |s: &Arc<Server>, ctx: &Context, l, p| s.handle_code_action(ctx, l, p));
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentPrepareCallHierarchy,
            Server::handle_prepare_call_hierarchy,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentFoldingRange,
            Server::handle_folding_range,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentPrepareRename,
            Server::handle_prepare_rename,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentLinkedEditingRange,
            Server::handle_linked_editing_range,
        );
        // `registerLanguageServiceWithAutoImportsRequestHandler` — the
        // second `CodeAction` registration overwrites the first, as Go's
        // map does.
        register_ls_auto_imports_handler(&mut m, lsproto::Method::TextDocumentCompletion, |s: &Arc<Server>, ctx: &Context, l, p| s.handle_completion(ctx, l, p));
        register_ls_auto_imports_handler(&mut m, lsproto::Method::TextDocumentCodeAction, |s: &Arc<Server>, ctx: &Context, l, p| s.handle_code_action(ctx, l, p));
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentVSOnAutoInsert,
            Server::handle_on_auto_insert,
        );
        register_multi_project_handler(&mut m, lsproto::Method::TextDocumentReferences, |ls, ctx, params: Option<lsproto::ReferenceParams>, o| {
            let params = params.unwrap_or_default();
            ls.provide_references(ctx, &params, o).map_err(Error::Ls)
        });
        register_multi_project_handler(&mut m, lsproto::Method::TextDocumentVSReferences, |ls, ctx, params: Option<lsproto::ReferenceParams>, o| {
            let params = params.unwrap_or_default();
            ls.provide_vs_references(ctx, &params, o).map_err(Error::Ls)
        });
        register_request_handler(&mut m, lsproto::Method::TextDocumentRename, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_rename(ctx, p, r));
        register_multi_project_handler(&mut m, lsproto::Method::TextDocumentImplementation, |ls, ctx, params: Option<lsproto::ImplementationParams>, o| {
            let params = params.unwrap_or_default();
            ls.provide_implementations(ctx, &params, o).map_err(Error::Ls)
        });
        register_request_handler(
            &mut m,
            lsproto::Method::CallHierarchyIncomingCalls,
            Server::handle_call_hierarchy_incoming_calls,
        );
        register_request_handler(
            &mut m,
            lsproto::Method::CallHierarchyOutgoingCalls,
            Server::handle_call_hierarchy_outgoing_calls,
        );
        register_request_handler(&mut m, lsproto::Method::WorkspaceSymbol, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_workspace_symbol(ctx, p, r));
        register_request_handler(
            &mut m,
            lsproto::Method::CompletionItemResolve,
            Server::handle_completion_item_resolve,
        );
        register_request_handler(&mut m, lsproto::Method::CodeLensResolve, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_code_lens_resolve(ctx, p, r));
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentSemanticTokensFull,
            Server::handle_semantic_tokens_full,
        );
        register_ls_document_handler(
            &mut m,
            lsproto::Method::TextDocumentSemanticTokensRange,
            Server::handle_semantic_tokens_range,
        );
        // Developer/debugging commands.
        register_request_handler(&mut m, lsproto::Method::CustomRunGC, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_run_gc(ctx, p, r));
        register_request_handler(&mut m, lsproto::Method::CustomSaveHeapProfile, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_save_heap_profile(ctx, p, r));
        register_request_handler(&mut m, lsproto::Method::CustomSaveAllocProfile, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_save_alloc_profile(ctx, p, r));
        register_request_handler(&mut m, lsproto::Method::CustomStartCPUProfile, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_start_cpu_profile(ctx, p, r));
        register_request_handler(&mut m, lsproto::Method::CustomStopCPUProfile, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_stop_cpu_profile(ctx, p, r));
        register_request_handler(
            &mut m,
            lsproto::Method::CustomInitializeAPISession,
            Server::handle_initialize_api_session,
        );
        register_request_handler(&mut m, lsproto::Method::CustomProjectInfo, |s: &Arc<Server>, ctx: &Context, p, r| s.handle_project_info(ctx, p, r));
        register_request_handler(
            &mut m,
            lsproto::Method::CustomSetContentMapperContributions,
            Server::handle_set_content_mapper_contributions,
        );
        m
    });
    &HANDLERS
}

impl Server {
    /// `s.RegisterContentMapperExtensions` — dynamically registers text
    /// document sync + pull diagnostics for otherwise-unsupported file
    /// extensions so the editor forwards them to the server. Called with the
    /// full desired set each time it changes; empty removes registration.
    pub(crate) fn register_content_mapper_extensions(
        &self,
        ctx: &Context,
        extensions: &[String],
    ) -> Result<(), Error> {
        if !self.caps().text_document.synchronization.dynamic_registration {
            return Ok(());
        }
        let mut registered = self.content_mapper_registration.lock().unwrap();

        if *registered {
            let mut unregistrations = content_mapper_registration_ids()
                .iter()
                .map(|(id, method)| lsproto::Unregistration {
                    id: id.to_string(),
                    method: method.to_string(),
                })
                .collect::<Vec<_>>();
            unregistrations
                .retain(|r| self.supports_content_mapper_registration(&r.id));
            self.send_client_request(
                ctx,
                &lsproto::CLIENT_UNREGISTER_CAPABILITY_INFO,
                Some(lsproto::UnregistrationParams {
                    unregisterations: Some(unregistrations),
                }),
            )
            .map_err(|e| {
                Error::Message(format!(
                    "failed to unregister content mapper text document sync: {e}"
                ))
            })?;
            *registered = false;
        }

        if extensions.is_empty() {
            return Ok(());
        }

        let filters: Vec<lsproto::TextDocumentFilterLanguageOrSchemeOrPattern> = extensions
            .iter()
            .map(|ext| lsproto::TextDocumentFilterLanguageOrSchemeOrPattern {
                pattern: Some(lsproto::TextDocumentFilterPattern {
                    pattern: lsproto::PatternOrRelativePattern {
                        pattern: Some(format!("**/*{ext}")),
                        ..Default::default()
                    },
                    ..Default::default()
                }),
                ..Default::default()
            })
            .collect();
        let selector = lsproto::DocumentSelectorOrNull {
            document_selector: Some(filters),
        };
        let rename_filters: Vec<lsproto::FileOperationFilter> = extensions
            .iter()
            .map(|ext| lsproto::FileOperationFilter {
                scheme: Some("file".to_string()),
                pattern: Some(lsproto::FileOperationPattern {
                    glob: format!("**/*{ext}"),
                    ..Default::default()
                }),
            })
            .collect();

        use content_mapper_ids as ids;
        use lsproto::RegisterOptions;
        let sel = &selector;
        let registrations = vec![
            reg(ids::DID_OPEN, RegisterOptions {
                text_document_did_open: Some(
                    lsproto::TextDocumentRegistrationOptions {
                        document_selector: sel.clone(),
                    },
                ),
                ..Default::default()
            }),
            reg(ids::DID_CHANGE, RegisterOptions {
                text_document_did_change: Some(
                    lsproto::TextDocumentChangeRegistrationOptions {
                        document_selector: sel.clone(),
                        sync_kind: lsproto::TextDocumentSyncKind::Incremental,
                    },
                ),
                ..Default::default()
            }),
            reg(ids::DID_CLOSE, RegisterOptions {
                text_document_did_close: Some(
                    lsproto::TextDocumentRegistrationOptions {
                        document_selector: sel.clone(),
                    },
                ),
                ..Default::default()
            }),
            reg(ids::DIAGNOSTIC, RegisterOptions {
                text_document_diagnostic: Some(lsproto::DiagnosticRegistrationOptions {
                    document_selector: sel.clone(),
                    identifier: Some("typescript".to_string()),
                    inter_file_dependencies: true,
                    ..Default::default()
                }),
                ..Default::default()
            }),
            reg(ids::HOVER, RegisterOptions {
                text_document_hover: Some(lsproto::HoverRegistrationOptions {
                    document_selector: sel.clone(),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            reg(ids::SIGNATURE_HELP, RegisterOptions {
                text_document_signature_help: Some(
                    lsproto::SignatureHelpRegistrationOptions {
                        document_selector: sel.clone(),
                        trigger_characters: Some(
                            ls::SIGNATURE_HELP_TRIGGER_CHARACTERS
                                .iter()
                                .map(|s| s.to_string())
                                .collect(),
                        ),
                        retrigger_characters: Some(
                            ls::SIGNATURE_HELP_RETRIGGER_CHARACTERS
                                .iter()
                                .map(|s| s.to_string())
                                .collect(),
                        ),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::DEFINITION, RegisterOptions {
                text_document_definition: Some(
                    lsproto::DefinitionRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::TYPE_DEFINITION, RegisterOptions {
                text_document_type_definition: Some(
                    lsproto::TypeDefinitionRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::IMPLEMENTATION, RegisterOptions {
                text_document_implementation: Some(
                    lsproto::ImplementationRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::REFERENCES, RegisterOptions {
                text_document_references: Some(lsproto::ReferenceRegistrationOptions {
                    document_selector: sel.clone(),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            reg(ids::DOCUMENT_HIGHLIGHT, RegisterOptions {
                text_document_document_highlight: Some(
                    lsproto::DocumentHighlightRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::COMPLETION, RegisterOptions {
                text_document_completion: Some(lsproto::CompletionRegistrationOptions {
                    document_selector: sel.clone(),
                    trigger_characters: Some(
                        ls::completion_trigger_characters()
                            .iter()
                            .map(|s| s.to_string())
                            .collect(),
                    ),
                    resolve_provider: Some(true),
                    completion_item: Some(lsproto::ServerCompletionItemOptions {
                        label_details_support: Some(true),
                    }),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            reg(ids::RENAME, RegisterOptions {
                text_document_rename: Some(lsproto::RenameRegistrationOptions {
                    document_selector: sel.clone(),
                    prepare_provider: Some(true),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            reg(ids::SEMANTIC_TOKENS, RegisterOptions {
                text_document_semantic_tokens: Some(
                    lsproto::SemanticTokensRegistrationOptions {
                        document_selector: sel.clone(),
                        legend: Some(ls::semantic_tokens_legend(
                            &self.caps().text_document.semantic_tokens,
                        )),
                        full: Some(lsproto::BooleanOrSemanticTokensFullDelta {
                            boolean: Some(true),
                            ..Default::default()
                        }),
                        range: Some(lsproto::BooleanOrEmptyObject {
                            boolean: Some(true),
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::DOCUMENT_SYMBOL, RegisterOptions {
                text_document_document_symbol: Some(
                    lsproto::DocumentSymbolRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::FOLDING_RANGE, RegisterOptions {
                text_document_folding_range: Some(
                    lsproto::FoldingRangeRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::SELECTION_RANGE, RegisterOptions {
                text_document_selection_range: Some(
                    lsproto::SelectionRangeRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::INLAY_HINT, RegisterOptions {
                text_document_inlay_hint: Some(lsproto::InlayHintRegistrationOptions {
                    document_selector: sel.clone(),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            reg(ids::CODE_LENS, RegisterOptions {
                text_document_code_lens: Some(lsproto::CodeLensRegistrationOptions {
                    document_selector: sel.clone(),
                    resolve_provider: Some(true),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            reg(ids::CODE_ACTION, RegisterOptions {
                text_document_code_action: Some(lsproto::CodeActionRegistrationOptions {
                    document_selector: sel.clone(),
                    code_action_kinds: Some(supported_code_action_kinds()),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            reg(ids::FORMATTING, RegisterOptions {
                text_document_formatting: Some(
                    lsproto::DocumentFormattingRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::RANGE_FORMATTING, RegisterOptions {
                text_document_range_formatting: Some(
                    lsproto::DocumentRangeFormattingRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::ON_TYPE_FORMATTING, RegisterOptions {
                text_document_on_type_formatting: Some(
                    lsproto::DocumentOnTypeFormattingRegistrationOptions {
                        document_selector: sel.clone(),
                        first_trigger_character: "{".to_string(),
                        more_trigger_character: Some(vec![
                            "}".to_string(),
                            ";".to_string(),
                            "\n".to_string(),
                        ]),
                    },
                ),
                ..Default::default()
            }),
            reg(ids::LINKED_EDITING, RegisterOptions {
                text_document_linked_editing_range: Some(
                    lsproto::LinkedEditingRangeRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::CALL_HIERARCHY, RegisterOptions {
                text_document_prepare_call_hierarchy: Some(
                    lsproto::CallHierarchyRegistrationOptions {
                        document_selector: sel.clone(),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
            reg(ids::WILL_RENAME_FILES, RegisterOptions {
                workspace_will_rename_files: Some(
                    lsproto::FileOperationRegistrationOptions {
                        filters: Some(rename_filters.clone()),
                    },
                ),
                ..Default::default()
            }),
        ];
        let mut registrations = registrations;
        registrations.retain(|r| self.supports_content_mapper_registration(&r.id));
        self.send_client_request(
            ctx,
            &lsproto::CLIENT_REGISTER_CAPABILITY_INFO,
            Some(lsproto::RegistrationParams {
                registrations: Some(registrations),
            }),
        )
        .map_err(|e| {
            Error::Message(format!(
                "failed to register content mapper text document sync: {e}"
            ))
        })?;
        *registered = true;
        Ok(())
    }
}

/// Builds one `Registration` entry (`{Id, RegisterOptions}`).
fn reg(id: &str, options: lsproto::RegisterOptions) -> lsproto::Registration {
    lsproto::Registration {
        id: id.to_string(),
        register_options: Some(options),
    }
}

/// `(id, method)` pairs for unregistration (`contentMapper*RegistrationID`).
fn content_mapper_registration_ids() -> [(&'static str, lsproto::Method); 26] {
    use content_mapper_ids as ids;
    [
        (ids::DID_OPEN, lsproto::Method::TextDocumentDidOpen),
        (ids::DID_CHANGE, lsproto::Method::TextDocumentDidChange),
        (ids::DID_CLOSE, lsproto::Method::TextDocumentDidClose),
        (ids::DIAGNOSTIC, lsproto::Method::TextDocumentDiagnostic),
        (ids::HOVER, lsproto::Method::TextDocumentHover),
        (ids::SIGNATURE_HELP, lsproto::Method::TextDocumentSignatureHelp),
        (ids::DEFINITION, lsproto::Method::TextDocumentDefinition),
        (ids::TYPE_DEFINITION, lsproto::Method::TextDocumentTypeDefinition),
        (ids::IMPLEMENTATION, lsproto::Method::TextDocumentImplementation),
        (ids::REFERENCES, lsproto::Method::TextDocumentReferences),
        (ids::DOCUMENT_HIGHLIGHT, lsproto::Method::TextDocumentDocumentHighlight),
        (ids::COMPLETION, lsproto::Method::TextDocumentCompletion),
        (ids::RENAME, lsproto::Method::TextDocumentRename),
        (ids::SEMANTIC_TOKENS, lsproto::Method::TextDocumentSemanticTokensFull),
        (ids::DOCUMENT_SYMBOL, lsproto::Method::TextDocumentDocumentSymbol),
        (ids::FOLDING_RANGE, lsproto::Method::TextDocumentFoldingRange),
        (ids::SELECTION_RANGE, lsproto::Method::TextDocumentSelectionRange),
        (ids::INLAY_HINT, lsproto::Method::TextDocumentInlayHint),
        (ids::CODE_LENS, lsproto::Method::TextDocumentCodeLens),
        (ids::CODE_ACTION, lsproto::Method::TextDocumentCodeAction),
        (ids::FORMATTING, lsproto::Method::TextDocumentFormatting),
        (ids::RANGE_FORMATTING, lsproto::Method::TextDocumentRangeFormatting),
        (ids::ON_TYPE_FORMATTING, lsproto::Method::TextDocumentOnTypeFormatting),
        (ids::LINKED_EDITING, lsproto::Method::TextDocumentLinkedEditingRange),
        (ids::CALL_HIERARCHY, lsproto::Method::TextDocumentPrepareCallHierarchy),
        (ids::WILL_RENAME_FILES, lsproto::Method::WorkspaceWillRenameFiles),
    ]
}
