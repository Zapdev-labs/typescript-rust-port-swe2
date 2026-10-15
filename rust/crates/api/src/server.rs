// Ported from tsc/internal/api/server.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `StdioServer` — the STDIO (or pipe) API server entry point: transport
// setup, callback-FS wrap, session construction, and the conn run loop.

use std::io;
use std::sync::Arc;

use tsc_bundled as bundled;
use tsc_contentmapper as contentmapper;
use tsc_core::context::Context;
use tsc_ipc as ipc;
use tsc_ipc::Transport as _;
use tsc_lsproto as lsproto;
use tsc_project as project;
use tsc_tspath as tspath;
use tsc_vfs::osvfs;
use tsc_vfs::Vfs;

use crate::callbackfs::{new_callback_fs, CallbackFs};
use crate::protocol_msgpack::new_message_pack_protocol;
use crate::session::{new_standalone_session, SessionOptions};

/// `StdioServerOptions` configures the STDIO-based API server.
pub struct StdioServerOptions {
    /// `In`/`Out` — the stdio halves; `run` consumes them. `None` is only
    /// valid with `pipe_path`.
    pub input: Option<Box<dyn ipc::ReadClose>>,
    pub output: Option<Box<dyn ipc::WriteClose>>,
    pub cwd: tspath::RootedDirectoryPath,
    pub default_library_path: tspath::RootedDirectoryPath,
    /// `PipePath`, if set, listens on a named pipe (Windows) or Unix domain
    /// socket instead of using `input`/`output` for communication.
    pub pipe_path: String,
    /// `Callbacks` specifies which filesystem operations should be delegated
    /// to the client (e.g., "readFile", "fileExists"). Empty means no callbacks.
    pub callbacks: Vec<String>,
    /// `UseCaseSensitiveFileNames` overrides the base filesystem's case sensitivity.
    pub use_case_sensitive_file_names: Option<bool>,
    /// `Async` enables JSON-RPC protocol with async connection handling.
    /// When false (default), uses MessagePack protocol with sync connection.
    pub async_: bool,
    /// `CollectTiming` enables per-request server processing-time measurement.
    /// When enabled, the server accumulates each request's processing time into
    /// running totals and a recent-request ring buffer. Response messages are
    /// left unchanged; the client folds this data into its own timing snapshot
    /// on demand via getServerTiming / resetServerTiming requests.
    pub collect_timing: bool,
    /// `RunExternalCode` allows configured content mappers to execute.
    pub run_external_code: bool,
    pub content_mapper_spawner: Option<Arc<dyn contentmapper::hostimpl::Spawner>>,
}

/// `StdioServer` runs an API session over STDIO using MessagePack protocol.
/// This is the entry point for the synchronous STDIO-based API used by
/// native TypeScript tooling integration.
pub struct StdioServer {
    options: StdioServerOptions,
}

/// `NewStdioServer` creates a new STDIO-based API server.
pub fn new_stdio_server(options: StdioServerOptions) -> StdioServer {
    assert!(
        !options.cwd.as_string().is_empty(),
        "StdioServerOptions.Cwd is required"
    );
    StdioServer { options }
}

/// `makeConn` — builds the protocol + conn pair over an accepted
/// read/write/close stream. `S` is `StdioConn` or the platform pipe conn;
/// both implement `IoClose` with `&S: Read + Write`.
fn make_conn<S>(
    rwc: Arc<S>,
    async_: bool,
    collect_timing: bool,
    session: Arc<crate::session::Session>,
) -> Arc<dyn ipc::Conn>
where
    S: ipc::IoClose + Send + Sync + 'static,
    for<'a> &'a S: io::Read + io::Write,
{
    if async_ {
        let protocol = ipc::new_json_rpc_protocol(rwc.clone());
        let conn = ipc::AsyncConn::new_async_conn_with_protocol(
            Some(rwc),
            Arc::new(protocol),
            session,
        );
        conn.set_collect_timing(collect_timing);
        Arc::new(conn)
    } else {
        let protocol = new_message_pack_protocol(rwc.clone());
        let conn = ipc::SyncConn::new_sync_conn(
            Some(rwc),
            Arc::new(protocol),
            session,
        );
        conn.set_collect_timing(collect_timing);
        Arc::new(conn)
    }
}

impl StdioServer {
    /// `Run` starts the server and blocks until the connection closes.
    pub fn run(&mut self, ctx: &Context) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {

        let mut fs: Arc<dyn Vfs> = bundled::wrap_fs(osvfs::fs());

        // Wrap the base FS when callbacks or an explicit case-sensitivity
        // setting are requested.
        let mut callback_fs: Option<Arc<CallbackFs>> = None;
        if !self.options.callbacks.is_empty() || self.options.use_case_sensitive_file_names.is_some()
        {
            let cb = Arc::new(new_callback_fs(
                fs.clone(),
                &self.options.callbacks,
                self.options.use_case_sensitive_file_names,
            ));
            fs = cb.clone();
            callback_fs = Some(cb);
        }

        let session_init = project::session::SessionInit {
            background_ctx: ctx.clone(),
            logger: None, // TODO: Add logging support
            fs,
            options: Arc::new(project::session::SessionOptions {
                current_directory: self.options.cwd.clone(),
                default_library_path: self.options.default_library_path.clone(),
                position_encoding: lsproto::PositionEncodingKind::UTF8,
                logging_enabled: false,
                run_external_code: self.options.run_external_code,
                ..Default::default()
            }),
            spawner: self.options.content_mapper_spawner.clone(),
            client: None,
            npm_executor: None,
            content_mapper_logger: None,
            parse_cache: None,
            content_mapped_parse_cache: None,
        };

        let session = new_standalone_session(
            &session_init,
            Some(&SessionOptions {
                // Only msgpack uses binary responses.
                use_binary_responses: !self.options.async_,
            }),
        );

        // Accept a connection from the transport and create the protocol
        // + conn pair based on async mode. Each transport yields a
        // different concrete `Conn` type, so the match keeps them
        // statically typed like Go's `transport.Accept()` branches.
        // `defer t.Close()` — the transport lives until `run` returns.
        let transport_close: Option<Box<dyn FnOnce() + Send>>;
        #[cfg(unix)]
        let conn: Arc<dyn ipc::Conn> = if !self.options.pipe_path.is_empty() {
            let transport = ipc::new_pipe_transport(&self.options.pipe_path)
                .map_err(|e| format!("failed to create pipe transport: {e}"))?;
            let rwc = transport
                .accept()
                .map_err(|e| format!("failed to accept connection: {e}"))?;
            let conn = make_conn(
                rwc,
                self.options.async_,
                self.options.collect_timing,
                session.clone(),
            );
            transport_close = Some(Box::new(move || {
                let _ = transport.close();
            }));
            conn
        } else {
            let input = self
                .options
                .input
                .take()
                .expect("StdioServerOptions.In is required without PipePath");
            let output = self
                .options
                .output
                .take()
                .expect("StdioServerOptions.Out is required without PipePath");
            let transport = ipc::new_stdio_transport(input, output);
            let rwc = transport
                .accept()
                .map_err(|e| format!("failed to accept connection: {e}"))?;
            let conn = make_conn(
                rwc,
                self.options.async_,
                self.options.collect_timing,
                session.clone(),
            );
            transport_close = Some(Box::new(move || {
                let _ = transport.close();
            }));
            conn
        };
        #[cfg(not(unix))]
        let conn: Arc<dyn ipc::Conn> = {
            let input = self
                .options
                .input
                .take()
                .expect("StdioServerOptions.In is required without PipePath");
            let output = self
                .options
                .output
                .take()
                .expect("StdioServerOptions.Out is required without PipePath");
            let transport = ipc::new_stdio_transport(input, output);
            let rwc = transport
                .accept()
                .map_err(|e| format!("failed to accept connection: {e}"))?;
            let conn = make_conn(
                rwc,
                self.options.async_,
                self.options.collect_timing,
                session.clone(),
            );
            transport_close = Some(Box::new(move || {
                let _ = transport.close();
            }));
            conn
        };

        // If callbacks are enabled, set the connection on the FS.
        if let Some(cb) = &callback_fs {
            cb.set_connection(ctx.clone(), conn.clone());
        }
        session.set_connection(conn.clone());

        let run_err = conn.run(ctx);
        if let Some(close) = transport_close {
            close();
        }
        let result = server_run_error(ctx, run_err.map_err(|e| e.to_string()));
        session.close();
        result.map_err(|e| e.into())
    }
}

/// `serverRunError` — a closed-by-context run is a clean shutdown.
fn server_run_error(ctx: &Context, err: Result<(), String>) -> Result<(), String> {
    if ctx.is_cancelled() {
        return Ok(());
    }
    err
}
