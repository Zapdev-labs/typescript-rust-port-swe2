// Ported from tsc/internal/testutil/contentmappertest/*.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// (component.go, diagnostic_code_collision.go, duplicate.go,
// duplicate_projection.go, dynamic_verbatim.go, editing.go, failing.go,
// hoisting.go, lisp.go, manifest.go, protocol.go, registry.go, spawner.go,
// supplemental.go, supplemental_diagnostics.go, supplemental_globals.go,
// supplemental_module.go, synthesizing.go, transforming.go, verbatim.go;
// mapper_test.go is ported as `mod tests` at the bottom.)
//
// PORT notes:
// - `context.Context` → `tsc_core::context::Context`.
// - `json.Value` → `tsc_json::Value` (`Box<serde_json::value::RawValue>`);
//   `json.Value(bytes)` wraps already-marshaled bytes via
//   `RawValue::from_string` ([raw_value]).
// - `HandleRequest`'s `error` result → `Box<dyn std::error::Error + Send +
//   Sync>` ([BoxedError]); `errors.New`/`fmt.Errorf` → `Err("...".into())`.
// - `testing.TB`-free handlers return `any` → `Option<Value>`; `respond`
//   marshals the result struct like the conn's `params` marshaling would.
// - `noNotifications` has no Rust equivalent (no struct embedding); each
//   handler's `impl ipc::Handler` writes the no-op `handle_notification`
//   through the `handle_notification_noop!` macro.
// - Go's `staticProjectHandler` type-asserts its inner `ipc.Handler` to
//   `projectLifecycleHandler`. `ipc::Handler` does not carry `Any` (so no
//   downcast); [handler_for_mapper] instead returns the lifecycle capability
//   alongside the handler ([SpawnedHandler::lifecycle]).
// - `net.Pipe()` → [pipe_pair], an in-memory duplex ([PipeEnd]) copied from
//   tsc-contentmapper's host tests (same Mutex+Condvar+queue design).
// - Byte-index string ops (`strings.Index`/`IndexByte`/`Contains`...) become
//   `str::find`/`contains` on `&str`/`&[u8]`; test mapper inputs are ASCII,
//   so `str` slicing matches Go's byte slicing.
// - `ProjectLifecycle`'s `atomic.Int32` fields → `AtomicI32`.
// - `Mapper.CompilerOptions []string` needs owned strings: `DeclaredOptions`
//   → [DECLARED_OPTIONS] (`LazyLock<Vec<String>>`, clone at use sites).

use std::collections::{HashMap, VecDeque};
use std::io;
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::sync::{Arc, Condvar, LazyLock, Mutex};
use std::thread;

use tsc_collections::OrderedMap;
use tsc_contentmapper::{
    CloseProjectParams, Diagnostic, DiagnosticDirectivePolicy, DiagnosticDirectives,
    InitializeResult, METHOD_CLOSE_PROJECT, METHOD_INITIALIZE, METHOD_OPEN_PROJECT,
    METHOD_TRANSFORM, MappedDiagnosticDirective, MappedOutput, OpenProjectParams,
    OpenProjectResult, OptionDiagnosticResult, PositionEncoding, SpawnedProcess, Spawner,
    SupplementalOutput, TransformParams, TransformResult, UnusedExpectDirectiveDiagnostic,
};
use tsc_core::context::Context;
use tsc_core::text::{TextPos, TextRange};
use tsc_ipc::{self as ipc, Handler};
use tsc_json::{self as json, Value};
use tsc_spanmap::{Feature, Kind, Segment, SpanMap};
use tsc_tspath::{self as tspath};

/// `Box<dyn std::error::Error + Send + Sync>` — the `HandleRequest` error
/// result (ipc::Handler's signature).
type BoxedError = Box<dyn std::error::Error + Send + Sync>;
type HandlerResult = Result<Option<ipc::ResponsePayload>, BoxedError>;

/// `json.Unmarshal(params, &p)` — absent params decode like Go's unmarshal of
/// `null` (zero value); the wire params here are always present.
fn params_of<T: serde::de::DeserializeOwned + Default>(
    params: &Option<Value>,
) -> Result<T, BoxedError> {
    Ok(ipc::unmarshal_params::<T>(params.as_ref())?.unwrap_or_default())
}

/// `return result, nil` — marshal a handler response the way the conn's
/// result marshaling would.
fn respond<T: serde::Serialize>(value: &T) -> HandlerResult {
    Ok(Some(ipc::ResponsePayload::Json(ipc::marshal_params(value)?)))
}

/// `json.Value(b)` — wraps already-marshaled JSON bytes in a raw `Value`.
/// `SpanMap::marshal` output is always valid compact JSON.
fn raw_value(bytes: Vec<u8>) -> Value {
    serde_json::value::RawValue::from_string(String::from_utf8(bytes).unwrap()).unwrap()
}

/// `json.Value("...")` — a raw `Value` from a JSON literal.
fn raw_json(s: &str) -> Value {
    serde_json::value::RawValue::from_string(s.to_string()).unwrap()
}

/// `noNotifications` — Go embeds a struct whose `HandleNotification` is a
/// no-op; Rust traits have no embedding, so each handler's `impl` gets the
/// body through this macro.
macro_rules! handle_notification_noop {
    () => {
        fn handle_notification(
            &self,
            _ctx: &Context,
            _method: &str,
            _params: Option<Value>,
        ) -> Result<(), BoxedError> {
            Ok(())
        }
    };
}

// ---------------------------------------------------------------------------
// protocol.go
// ---------------------------------------------------------------------------

fn initialize_result(source: &str) -> InitializeResult {
    InitializeResult {
        position_encoding: PositionEncoding::UTF8,
        diagnostic_source: source.to_string(),
    }
}

fn identity_mapped_output(content: &str) -> Result<MappedOutput, BoxedError> {
    let mappings = SpanMap::new(&[Segment {
        virtual_end: content.len() as TextPos,
        original_end: content.len() as TextPos,
        kind: Kind::Verbatim,
        features: Feature::All,
        ..Default::default()
    }])
    .marshal()?;
    Ok(MappedOutput {
        text: content.to_string(),
        extension: ".ts".to_string(),
        mappings: Some(raw_value(mappings)),
        ..Default::default()
    })
}

/// `projectLifecycleHandler` — the optional interface `staticProjectHandler`
/// probes for with a type assertion. Only [`Handler`] implements it.
trait ProjectLifecycleHandler: Handler {
    fn open_project(&self, params: OpenProjectParams) -> Result<(), BoxedError>;
    fn close_project(&self, params: CloseProjectParams);
}

/// `staticProjectHandler` — intercepts openProject/closeProject on the inner
/// handler's behalf and reports option diagnostics.
///
/// PORT: Go's `staticProjectHandler struct{ ipc.Handler }` embeds (promotes)
/// the inner handler's `HandleNotification`; here `lifecycle` carries the
/// asserted `projectLifecycleHandler` half explicitly, and the notification
/// method is written out.
struct StaticProjectHandler {
    handler: Arc<dyn Handler>,
    lifecycle: Option<Arc<dyn ProjectLifecycleHandler>>,
}

impl Handler for StaticProjectHandler {
    fn handle_request(&self, ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_OPEN_PROJECT => {
                let p: OpenProjectParams = params_of(&params)?;
                if let Some(handler) = &self.lifecycle {
                    handler.open_project(p.clone())?;
                }
                let mut diagnostics = None;
                if p.options.as_ref().map_or("", |v| v.get()) == r#"{"plugins":[{"name":1}]}"# {
                    diagnostics = Some(vec![OptionDiagnosticResult {
                        path: vec![
                            raw_json(r#""plugins""#),
                            raw_json("0"),
                            raw_json(r#""name""#),
                        ],
                        message_text: "Option 'name' requires a string.".to_string(),
                        code: 123,
                    }]);
                }
                respond(&OpenProjectResult {
                    option_diagnostics: diagnostics,
                    ..Default::default()
                })
            }
            METHOD_CLOSE_PROJECT => {
                let p: CloseProjectParams = params_of(&params)?;
                if let Some(handler) = &self.lifecycle {
                    handler.close_project(p);
                }
                Ok(None)
            }
            _ => self.handler.handle_request(ctx, method, params),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// registry.go
// ---------------------------------------------------------------------------

pub const TRANSFORMING_MAPPER: &str = "compiler-test-mapper";
pub const VERBATIM_MAPPER: &str = "verbatim-mapper";
pub const MODULE_VERBATIM_MAPPER: &str = "module-verbatim-mapper";
pub const DYNAMIC_VERBATIM_MAPPER: &str = "dynamic-verbatim-mapper";
pub const DIAGNOSTIC_CODE_COLLISION_MAPPER: &str = "diagnostic-code-collision-mapper";
pub const FAILING_MAPPER: &str = "failing-mapper";
pub const SYNTHESIZING_MAPPER: &str = "synthesizing-mapper";
pub const COMPONENT_MAPPER: &str = "component-mapper";
pub const DUPLICATE_MAPPER: &str = "duplicate-mapper";
pub const LISP_MAPPER: &str = "lisp-mapper";
pub const SUPPLEMENTAL_MAPPER: &str = "supplemental-mapper";
pub const SUPPLEMENTAL_DIAGNOSTICS_MAPPER: &str = "supplemental-diagnostics-mapper";
pub const SUPPLEMENTAL_GLOBALS_MAPPER: &str = "supplemental-globals-mapper";
pub const SUPPLEMENTAL_MODULE_MAPPER: &str = "supplemental-module-mapper";
pub const PREFIXED_SUPPLEMENTAL_MAPPER: &str = "prefixed-supplemental-mapper";
pub const UNMAPPED_FOLDING_MAPPER: &str = "unmapped-folding-mapper";
pub const HOISTING_MAPPER: &str = "hoisting-mapper";
pub const DUPLICATE_PROJECTION_MAPPER: &str = "duplicate-projection-mapper";

/// The result of [handler_for_mapper] — `handler` is the `ipc.Handler`; the
/// `lifecycle` half is `Some` only when the handler also implements
/// `projectLifecycleHandler` (Go's type assertion, made explicit — only
/// [`Handler`] qualifies).
struct SpawnedHandler {
    handler: Arc<dyn Handler>,
    lifecycle: Option<Arc<dyn ProjectLifecycleHandler>>,
}

fn handler_for_mapper(
    command: &[String],
    lifecycle: Option<Arc<ProjectLifecycle>>,
) -> Result<SpawnedHandler, BoxedError> {
    let Some(name) = command.first() else {
        return Err("contentmappertest: empty mapper command".into());
    };
    let spawned = match name.as_str() {
        TRANSFORMING_MAPPER => {
            let handler = Arc::new(TransformingHandler::default());
            SpawnedHandler {
                lifecycle: Some(handler.clone()),
                handler,
            }
        }
        VERBATIM_MAPPER => SpawnedHandler {
            handler: Arc::new(VerbatimHandler),
            lifecycle: None,
        },
        MODULE_VERBATIM_MAPPER => SpawnedHandler {
            handler: Arc::new(ModuleVerbatimHandler),
            lifecycle: None,
        },
        DYNAMIC_VERBATIM_MAPPER => SpawnedHandler {
            handler: Arc::new(DynamicVerbatimHandler { lifecycle }),
            lifecycle: None,
        },
        DIAGNOSTIC_CODE_COLLISION_MAPPER => SpawnedHandler {
            handler: Arc::new(DiagnosticCodeCollisionHandler),
            lifecycle: None,
        },
        FAILING_MAPPER => SpawnedHandler {
            handler: Arc::new(FailingHandler),
            lifecycle: None,
        },
        SYNTHESIZING_MAPPER => SpawnedHandler {
            handler: Arc::new(SynthesizingHandler),
            lifecycle: None,
        },
        COMPONENT_MAPPER => SpawnedHandler {
            handler: Arc::new(ComponentHandler),
            lifecycle: None,
        },
        DUPLICATE_MAPPER => SpawnedHandler {
            handler: Arc::new(DuplicateHandler),
            lifecycle: None,
        },
        LISP_MAPPER => SpawnedHandler {
            handler: Arc::new(LispHandler),
            lifecycle: None,
        },
        SUPPLEMENTAL_MAPPER => SpawnedHandler {
            handler: Arc::new(SupplementalHandler),
            lifecycle: None,
        },
        SUPPLEMENTAL_DIAGNOSTICS_MAPPER => SpawnedHandler {
            handler: Arc::new(SupplementalDiagnosticsHandler),
            lifecycle: None,
        },
        SUPPLEMENTAL_GLOBALS_MAPPER => SpawnedHandler {
            handler: Arc::new(SupplementalGlobalsHandler),
            lifecycle: None,
        },
        SUPPLEMENTAL_MODULE_MAPPER => SpawnedHandler {
            handler: Arc::new(SupplementalModuleHandler),
            lifecycle: None,
        },
        PREFIXED_SUPPLEMENTAL_MAPPER => SpawnedHandler {
            handler: Arc::new(PrefixedSupplementalHandler),
            lifecycle: None,
        },
        UNMAPPED_FOLDING_MAPPER => SpawnedHandler {
            handler: Arc::new(UnmappedFoldingHandler),
            lifecycle: None,
        },
        HOISTING_MAPPER => SpawnedHandler {
            handler: Arc::new(HoistingHandler),
            lifecycle: None,
        },
        DUPLICATE_PROJECTION_MAPPER => SpawnedHandler {
            handler: Arc::new(DuplicateProjectionHandler),
            lifecycle: None,
        },
        _ => return Err(format!("contentmappertest: unknown mapper command {command:?}").into()),
    };
    Ok(spawned)
}

// ---------------------------------------------------------------------------
// spawner.go
// ---------------------------------------------------------------------------

/// `Serve` drives the transforming mapper over the connection until it closes
/// or ctx is cancelled.
///
/// PORT: `ipc.NewAsyncConn` takes `Arc<S>` where `&S` is `Read`/`Write` — see
/// [`ipc::new_async_conn`].
pub fn serve<S>(ctx: &Context, rwc: Arc<S>) -> Result<(), ipc::Error>
where
    S: ipc::IoClose + Send + Sync + 'static,
    for<'a> &'a S: io::Read + io::Write,
{
    let handler = Arc::new(TransformingHandler::default());
    ipc::new_async_conn(
        rwc,
        Arc::new(StaticProjectHandler {
            lifecycle: Some(handler.clone()),
            handler,
        }),
    )
    .run(ctx)
}

/// `NewSpawner` returns an in-process spawner for the test mapper
/// implementations.
///
/// PORT: Go returns the `Spawner` interface — here an `Arc` trait object
/// ready for [`contentmapper::new_host`].
pub fn new_spawner() -> Arc<dyn Spawner> {
    Arc::new(TestSpawner { lifecycle: None })
}

/// `NewSpawnerWithProjectLifecycle` returns an in-process spawner that
/// records project protocol calls.
pub fn new_spawner_with_project_lifecycle(lifecycle: Arc<ProjectLifecycle>) -> Arc<dyn Spawner> {
    Arc::new(TestSpawner {
        lifecycle: Some(lifecycle),
    })
}

struct TestSpawner {
    lifecycle: Option<Arc<ProjectLifecycle>>,
}

impl Spawner for TestSpawner {
    fn spawn(
        &self,
        command: &[String],
        _dir: &str,
        _stderr: Option<Box<dyn io::Write + Send>>,
    ) -> io::Result<Arc<dyn SpawnedProcess>> {
        let spawned = handler_for_mapper(command, self.lifecycle.clone())
            .map_err(|e| io::Error::new(io::ErrorKind::Other, e.to_string()))?;
        let handler: Arc<dyn Handler> = if command[0] != DYNAMIC_VERBATIM_MAPPER {
            Arc::new(StaticProjectHandler {
                handler: spawned.handler,
                lifecycle: spawned.lifecycle,
            })
        } else {
            spawned.handler
        };
        // `client, server := net.Pipe()` + `go conn.Run(context.Background())`
        let (client, server) = pipe_pair();
        thread::spawn(move || {
            let _ = ipc::new_async_conn(server, handler).run(&Context::background());
        });
        Ok(client)
    }
}

// `net.Pipe` — an in-memory, blocking, bidirectional byte pipe. Copied from
// tsc-contentmapper's host tests (`PipeEnd`/`test_pipe`), which ported the
// same Go construct.

#[derive(Default)]
struct PipeChanState {
    queue: VecDeque<u8>,
    /// The writing end closed — readers see EOF after the queue drains.
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

fn pipe_pair() -> (Arc<PipeEnd>, Arc<PipeEnd>) {
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
        let mut end = self;
        io::Read::read(&mut end, buf)
    }

    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
        let mut end = self;
        io::Write::write(&mut end, buf)
    }

    fn spawned_close(&self) -> io::Result<()> {
        self.close_inner();
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// manifest.go
// ---------------------------------------------------------------------------

/// `PackageName`
pub const PACKAGE_NAME: &str = "mapper";

/// `PackageJSON` returns a package manifest selecting the requested mapper.
///
/// PORT: `%q` on these ASCII names equals Rust's `{:?}` escaping for `str`.
pub fn package_json(mapper: &str) -> String {
    let mut compiler_options = "";
    let mut dynamic_config = "";
    if mapper == TRANSFORMING_MAPPER {
        compiler_options = r#", "compilerOptions": ["target", "jsx"]"#;
    }
    if mapper == DYNAMIC_VERBATIM_MAPPER {
        dynamic_config = r#", "dynamicConfig": true"#;
    }
    format!(
        "{{\n\t\"name\": {PACKAGE_NAME:?},\n\t\"version\": \"1.0.0\",\n\t\"typescript\": {{ \"contentMapper\": {{ \"exec\": [{mapper:?}]{compiler_options}{dynamic_config} }} }}\n}}"
    )
}

// ---------------------------------------------------------------------------
// verbatim.go
// ---------------------------------------------------------------------------

struct VerbatimHandler;
struct ModuleVerbatimHandler;

impl Handler for VerbatimHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                let mapped_output = identity_mapped_output(&p.content)?;
                respond(&TransformResult {
                    mapped_output,
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

impl Handler for ModuleVerbatimHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                let mut mapped_output = identity_mapped_output(&p.content)?;
                mapped_output.extension = ".mts".to_string();
                respond(&TransformResult {
                    mapped_output,
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// transforming.go
// ---------------------------------------------------------------------------

const PREAMBLE: &str = "const __VERSION = \"1.0.0\";\n";

/// `var DeclaredOptions = []string{"target", "jsx"}`
///
/// PORT: `LazyLock<Vec<String>>` — clone at use sites
/// (`DECLARED_OPTIONS.clone()`).
pub static DECLARED_OPTIONS: LazyLock<Vec<String>> =
    LazyLock::new(|| vec!["target".to_string(), "jsx".to_string()]);

const DIAGNOSTIC_SOURCE: &str = "box";
const UNCLOSED_INTERPOLATION_CODE: i32 = 1000;

/// `Handler` implements the transforming content mapper protocol.
///
/// PORT: `mu sync.Mutex` guards `compiler_options` as in Go.
#[derive(Default)]
pub struct TransformingHandler {
    /// `compilerOptions map[string]*collections.OrderedMap[string, json.Value]`
    /// — `None` value is Go's nil `*OrderedMap` (a project opened with JSON
    /// `null` options).
    compiler_options: Mutex<HashMap<String, Option<OrderedMap<String, Value>>>>,
}

impl TransformingHandler {
    /// `(h *Handler) OpenProject`
    pub fn open_project(&self, p: OpenProjectParams) -> Result<(), BoxedError> {
        let options: Option<OrderedMap<String, Value>> =
            json::unmarshal(p.compiler_options.get().as_bytes(), &[])?;
        self.compiler_options
            .lock()
            .unwrap()
            .insert(p.project_handle, options);
        Ok(())
    }

    /// `(h *Handler) CloseProject`
    pub fn close_project(&self, p: CloseProjectParams) {
        self.compiler_options
            .lock()
            .unwrap()
            .remove(&p.project_handle);
    }
}

impl ProjectLifecycleHandler for TransformingHandler {
    fn open_project(&self, params: OpenProjectParams) -> Result<(), BoxedError> {
        TransformingHandler::open_project(self, params)
    }

    fn close_project(&self, params: CloseProjectParams) {
        TransformingHandler::close_project(self, params)
    }
}

impl Handler for TransformingHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result(DIAGNOSTIC_SOURCE)),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                // Go unlocks before `transform`; the guard stays held here
                // because `OrderedMap` has no `Clone` — the map is not
                // mutated during a transform, so holding it is equivalent.
                let guard = self.compiler_options.lock().unwrap();
                let Some(options) = guard.get(&p.project_handle).and_then(Option::as_ref) else {
                    return Err(format!(
                        "contentmappertest: project {:?} is not open",
                        p.project_handle
                    )
                    .into());
                };
                let (text, mappings, diagnostics, diagnostic_directives) =
                    transform(&p.content, Some(options))?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text,
                        extension: mapped_extension(&p.content),
                        mappings: Some(mappings),
                        diagnostic_directives,
                    },
                    diagnostics,
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

fn mapped_extension(content: &str) -> String {
    const PREFIX: &str = "// @box-extension:";
    if let Some((first_line, _)) = content.split_once('\n')
        && let Some(rest) = first_line.strip_prefix(PREFIX)
    {
        return rest.trim().to_string();
    }
    ".ts".to_string()
}

fn write_verbatim(
    virtual_: &mut String,
    segments: &mut Vec<Segment>,
    content: &str,
    from: usize,
    to: usize,
) {
    if to <= from {
        return;
    }
    let virtual_start = virtual_.len() as TextPos;
    virtual_.push_str(&content[from..to]);
    segments.push(Segment {
        virtual_start,
        virtual_end: virtual_.len() as TextPos,
        original_start: from as TextPos,
        original_end: to as TextPos,
        kind: Kind::Verbatim,
        features: Feature::All,
    });
}

fn write_atom(
    virtual_: &mut String,
    segments: &mut Vec<Segment>,
    value: &str,
    from: usize,
    to: usize,
) {
    let virtual_start = virtual_.len() as TextPos;
    virtual_.push_str(value);
    segments.push(Segment {
        virtual_start,
        virtual_end: virtual_.len() as TextPos,
        original_start: from as TextPos,
        original_end: to as TextPos,
        kind: Kind::Atom,
        features: Feature::All,
    });
}

fn transform(
    content: &str,
    options: Option<&OrderedMap<String, Value>>,
) -> Result<(String, Value, Vec<Diagnostic>, Option<DiagnosticDirectives>), BoxedError> {
    let mut virtual_ = String::new();
    let mut segments: Vec<Segment> = Vec::new();
    let mut diagnostics: Vec<Diagnostic> = Vec::new();

    virtual_.push_str(PREAMBLE);

    let mut pos = 0;
    while pos < content.len() {
        let Some(rel) = content[pos..].find("#{") else {
            write_verbatim(&mut virtual_, &mut segments, content, pos, content.len());
            break;
        };
        let token_start = pos + rel;

        let line_end = match content[token_start..].find('\n') {
            Some(i) => token_start + i,
            None => content.len(),
        };
        let Some(close_rel) = content[token_start..line_end].find('}') else {
            write_verbatim(&mut virtual_, &mut segments, content, pos, token_start);
            write_atom(
                &mut virtual_,
                &mut segments,
                "undefined",
                token_start,
                line_end,
            );
            diagnostics.push(Diagnostic {
                message_text: "Unclosed interpolation.".to_string(),
                start: token_start as i64,
                length: (line_end - token_start) as i64,
                code: UNCLOSED_INTERPOLATION_CODE,
            });
            pos = line_end;
            continue;
        };
        let token_end = token_start + close_rel + 1;
        let name = &content[token_start + "#{".len()..token_end - "}".len()];

        write_verbatim(&mut virtual_, &mut segments, content, pos, token_start);
        write_atom(
            &mut virtual_,
            &mut segments,
            &render_option(options, name),
            token_start,
            token_end,
        );
        pos = token_end;
    }

    let span_map = SpanMap::new(&segments);
    let mappings = span_map.marshal()?;
    Ok((
        virtual_,
        raw_value(mappings),
        diagnostics,
        diagnostic_directives(content, &span_map),
    ))
}

fn diagnostic_directives(content: &str, mappings: &SpanMap) -> Option<DiagnosticDirectives> {
    /// `wrap` — Go's variadic `unused ...` plus nil-slice `directives`/`unused`
    /// (a nil `[]T` marshals as `null` → `None`; the literal `[]T{...}` call
    /// sites are non-empty → `Some`).
    fn wrap(
        directives: Vec<MappedDiagnosticDirective>,
        unused: Vec<UnusedExpectDirectiveDiagnostic>,
    ) -> DiagnosticDirectives {
        DiagnosticDirectives {
            unused_expect_directive_diagnostics: if unused.is_empty() {
                None
            } else {
                Some(unused)
            },
            directives: if directives.is_empty() {
                None
            } else {
                Some(directives)
            },
        }
    }

    const INVALID_PREFIX: &str = "// @box-invalid-directive:";
    if let Some(rest) = content.strip_prefix(INVALID_PREFIX) {
        match rest.split('\n').next().unwrap_or("").trim() {
            "invalid-range" => {
                return Some(wrap(
                    vec![MappedDiagnosticDirective {
                        virtual_start: -1,
                        policy: DiagnosticDirectivePolicy::IGNORE,
                        ..Default::default()
                    }],
                    Vec::new(),
                ));
            }
            "original-range-out-of-bounds" => {
                return Some(wrap(
                    vec![MappedDiagnosticDirective {
                        original_start: content.len() as i64 + 1,
                        policy: DiagnosticDirectivePolicy::IGNORE,
                        ..Default::default()
                    }],
                    Vec::new(),
                ));
            }
            "virtual-range-out-of-bounds" => {
                return Some(wrap(
                    vec![MappedDiagnosticDirective {
                        virtual_start: 1 << 20,
                        virtual_end: 1 << 20,
                        policy: DiagnosticDirectivePolicy::IGNORE,
                        ..Default::default()
                    }],
                    Vec::new(),
                ));
            }
            "invalid-policy" => {
                return Some(wrap(
                    vec![MappedDiagnosticDirective {
                        policy: DiagnosticDirectivePolicy(2),
                        ..Default::default()
                    }],
                    Vec::new(),
                ));
            }
            "ignore-with-unused-diagnostic" => {
                return Some(wrap(
                    vec![MappedDiagnosticDirective {
                        policy: DiagnosticDirectivePolicy::IGNORE,
                        ..Default::default()
                    }],
                    vec![UnusedExpectDirectiveDiagnostic::default()],
                ));
            }
            "expect-without-unused-diagnostic" => {
                return Some(wrap(
                    vec![MappedDiagnosticDirective {
                        policy: DiagnosticDirectivePolicy::EXPECT,
                        ..Default::default()
                    }],
                    Vec::new(),
                ));
            }
            "invalid-unused-diagnostic-index" => {
                let index = 1;
                return Some(wrap(
                    vec![MappedDiagnosticDirective {
                        policy: DiagnosticDirectivePolicy::EXPECT,
                        unused_expect_directive_index: Some(index),
                        ..Default::default()
                    }],
                    vec![UnusedExpectDirectiveDiagnostic::default()],
                ));
            }
            "overlap" => {
                return Some(wrap(
                    vec![
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
                    Vec::new(),
                ));
            }
            _ => {}
        }
    }
    const IGNORE_PREFIX: &str = "// @box-ignore";
    const EXPECT_PREFIX: &str = "// @box-expect-error";
    let mut result: Vec<MappedDiagnosticDirective> = Vec::new();
    let mut unused_diagnostics: Vec<UnusedExpectDirectiveDiagnostic> = Vec::new();
    let mut line_start = 0;
    while line_start < content.len() {
        let line_end = match content[line_start..].find('\n') {
            None => content.len(),
            Some(i) => line_start + i,
        };
        let line = &content[line_start..line_end];
        let trimmed = line.trim();
        let mut policy = DiagnosticDirectivePolicy::default();
        let mut has_policy = false;
        let mut unused_diagnostic_index: i64 = -1;
        if trimmed == IGNORE_PREFIX {
            policy = DiagnosticDirectivePolicy::IGNORE;
            has_policy = true;
        } else if let Some(rest) = trimmed.strip_prefix(EXPECT_PREFIX)
            && let Some(message) = rest.strip_prefix(':')
        {
            policy = DiagnosticDirectivePolicy::EXPECT;
            has_policy = true;
            unused_diagnostic_index = unused_diagnostics.len() as i64;
            unused_diagnostics.push(UnusedExpectDirectiveDiagnostic {
                code: 2578,
                message_text: message.trim().to_string(),
            });
        }
        if has_policy && line_end < content.len() {
            let affected_start = line_end + 1;
            let affected_length = match content[affected_start..].find('\n') {
                None => content.len() - affected_start,
                Some(i) => i,
            };
            let virtual_spans = SpanMap::original_to_virtual_spans(
                Some(mappings),
                TextRange::new(
                    affected_start as i32,
                    (affected_start + affected_length) as i32,
                ),
                Feature::All,
            );
            if virtual_spans.len() == 1 {
                let mut directive = MappedDiagnosticDirective {
                    original_start: line_start as i64,
                    original_length: (line_end - line_start) as i64,
                    virtual_start: virtual_spans[0].span.pos() as i64,
                    virtual_end: virtual_spans[0].span.end() as i64,
                    policy,
                    unused_expect_directive_index: None,
                };
                if unused_diagnostic_index >= 0 {
                    directive.unused_expect_directive_index = Some(unused_diagnostic_index);
                }
                result.push(directive);
            }
        }
        if line_end == content.len() {
            break;
        }
        line_start = line_end + 1;
    }
    if unused_diagnostics.len() == 1 {
        for directive in &mut result {
            directive.unused_expect_directive_index = None;
        }
    }
    if result.is_empty() && unused_diagnostics.is_empty() {
        return None;
    }
    Some(wrap(result, unused_diagnostics))
}

fn render_option(options: Option<&OrderedMap<String, Value>>, name: &str) -> String {
    if let Some(options) = options
        && let Some(value) = options.get(name)
        && !value.get().is_empty()
    {
        return value.get().to_string();
    }
    "undefined".to_string()
}

// ---------------------------------------------------------------------------
// dynamic_verbatim.go
// ---------------------------------------------------------------------------

/// `ProjectLifecycle` records mapper project protocol calls.
///
/// PORT: `Opens`/`Closes` are `atomic.Int32` in Go.
#[derive(Default)]
pub struct ProjectLifecycle {
    pub opens: AtomicI32,
    pub closes: AtomicI32,
}

struct DynamicVerbatimHandler {
    lifecycle: Option<Arc<ProjectLifecycle>>,
}

impl Handler for DynamicVerbatimHandler {
    fn handle_request(&self, ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_OPEN_PROJECT => {
                if let Some(lifecycle) = &self.lifecycle {
                    lifecycle.opens.fetch_add(1, Ordering::SeqCst);
                }
                let p: OpenProjectParams = params_of(&params)?;
                let identity = format!(
                    "{}:{}",
                    p.config_file_name,
                    p.options.as_ref().map_or("", |v| v.get())
                );
                let mut diagnostics = None;
                if p.options.as_ref().map_or("", |v| v.get()) == r#"{"plugins":[{"name":1}]}"# {
                    diagnostics = Some(vec![OptionDiagnosticResult {
                        path: vec![
                            raw_json(r#""plugins""#),
                            raw_json("0"),
                            raw_json(r#""name""#),
                        ],
                        message_text: "Option 'name' requires a string.".to_string(),
                        code: 123,
                    }]);
                }
                let mut watch_directory =
                    tspath::get_directory_path(&p.config_file_name).into_owned();
                if watch_directory.is_empty() {
                    watch_directory = "/".to_string();
                }
                return respond(&OpenProjectResult {
                    config_identity: identity,
                    watched_files: Some(vec![tspath::combine_paths(
                        &watch_directory,
                        &["mapper.config.json"],
                    )]),
                    option_diagnostics: diagnostics,
                });
            }
            METHOD_CLOSE_PROJECT => {
                if let Some(lifecycle) = &self.lifecycle {
                    lifecycle.closes.fetch_add(1, Ordering::SeqCst);
                }
                return Ok(None);
            }
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                if p.project_handle.is_empty() {
                    return Err("content mapper transform requires a project handle".into());
                }
            }
            _ => {}
        }
        VerbatimHandler.handle_request(ctx, method, params)
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// diagnostic_code_collision.go
// ---------------------------------------------------------------------------

struct DiagnosticCodeCollisionHandler;

impl Handler for DiagnosticCodeCollisionHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                let mapped_output = identity_mapped_output(&p.content)?;
                let start = p.content.find("foo").map_or(-1, |i| i as i64);
                respond(&TransformResult {
                    mapped_output,
                    diagnostics: vec![Diagnostic {
                        message_text: "Mapper diagnostic with a colliding code.".to_string(),
                        start,
                        length: "foo".len() as i64,
                        code: tsc_diagnostics::Function_must_have_an_explicit_return_type_annotation_with_isolatedDeclarations
                            .code(),
                    }],
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// duplicate.go
// ---------------------------------------------------------------------------

struct DuplicateHandler;

/// `strings.Index`/`LastIndex` — Go's `-1` miss becomes a negative segment
/// offset, which is preserved here via `i64` rather than saturating to
/// `usize` (that would panic on overflow).
fn index_of(haystack: &str, needle: &str) -> i64 {
    haystack.find(needle).map_or(-1, |i| i as i64)
}

fn last_index_of(haystack: &str, needle: &str) -> i64 {
    haystack.rfind(needle).map_or(-1, |i| i as i64)
}

/// `spanmap.New([]Segment{ ... verbatim pair ... }).Marshal()` helper shared
/// by the duplicate handler's branches: maps `content` verbatim at each given
/// virtual offset.
fn verbatim_segments(
    content: &str,
    virtual_offsets: &[i64],
    features: &[Feature],
) -> Result<Vec<u8>, serde_json::Error> {
    let segments: Vec<Segment> = virtual_offsets
        .iter()
        .zip(features)
        .map(|(&start, &features)| Segment {
            virtual_start: start as TextPos,
            virtual_end: (start + content.len() as i64) as TextPos,
            original_start: 0,
            original_end: content.len() as TextPos,
            kind: Kind::Verbatim,
            features,
        })
        .collect();
    SpanMap::new(&segments).marshal()
}

impl Handler for DuplicateHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                let n = p.content.len() as i64;
                if p.file_name.contains("hover-fallback") {
                    let r#virtual = format!("// {}\nconst {} = 1;\n", p.content, p.content);
                    let first = "// ".len() as i64;
                    let second = first + n + "\nconst ".len() as i64;
                    let mappings = verbatim_segments(
                        &p.content,
                        &[first, second],
                        &[Feature::Hover, Feature::Hover],
                    )?;
                    return respond(&TransformResult {
                        mapped_output: MappedOutput {
                            text: r#virtual,
                            extension: ".ts".to_string(),
                            mappings: Some(raw_value(mappings)),
                            ..Default::default()
                        },
                        ..Default::default()
                    });
                }
                if p.file_name.contains("hover-concat") {
                    let r#virtual = format!(
                        "namespace A {{ export const {} = 1; }}\nnamespace B {{ export const {} = \"text\"; }}\n",
                        p.content, p.content
                    );
                    let first = index_of(&r#virtual, &p.content);
                    let second = last_index_of(&r#virtual, &p.content);
                    let mappings = verbatim_segments(
                        &p.content,
                        &[first, second],
                        &[Feature::Hover, Feature::Hover],
                    )?;
                    return respond(&TransformResult {
                        mapped_output: MappedOutput {
                            text: r#virtual,
                            extension: ".ts".to_string(),
                            mappings: Some(raw_value(mappings)),
                            ..Default::default()
                        },
                        ..Default::default()
                    });
                }
                if p.file_name.contains("signature-fallback") {
                    let r#virtual = format!(
                        "// {}\nfunction use(value: number): void {{}}\n{};\n",
                        p.content, p.content
                    );
                    let first = "// ".len() as i64;
                    let second = last_index_of(&r#virtual, &p.content);
                    let mappings = verbatim_segments(
                        &p.content,
                        &[first, second],
                        &[Feature::SignatureHelp, Feature::SignatureHelp],
                    )?;
                    return respond(&TransformResult {
                        mapped_output: MappedOutput {
                            text: r#virtual,
                            extension: ".ts".to_string(),
                            mappings: Some(raw_value(mappings)),
                            ..Default::default()
                        },
                        ..Default::default()
                    });
                }
                if p.file_name.contains("rename-conflict") {
                    let r#virtual = format!(
                        "export const {} = 1;\nconst object = {{ {} }};\n{};\n",
                        p.content, p.content, p.content
                    );
                    let first = index_of(&r#virtual, &p.content);
                    let second =
                        index_of(&r#virtual[(first + n) as usize..], &p.content) + first + n;
                    let third =
                        index_of(&r#virtual[(second + n) as usize..], &p.content) + second + n;
                    let mappings = verbatim_segments(
                        &p.content,
                        &[first, second, third],
                        &[Feature::Rename, Feature::Rename, Feature::Rename],
                    )?;
                    return respond(&TransformResult {
                        mapped_output: MappedOutput {
                            text: r#virtual,
                            extension: ".ts".to_string(),
                            mappings: Some(raw_value(mappings)),
                            ..Default::default()
                        },
                        ..Default::default()
                    });
                }
                let r#virtual = format!("export const {} = 1;\n{};\n", p.content, p.content);
                let first = "export const ".len() as i64;
                let second = first + n + " = 1;\n".len() as i64;
                let disabled = p.file_name.contains("disabled");
                let mut semantic_features =
                    Feature::Hover | Feature::Definition | Feature::References | Feature::Rename;
                let mut navigation_features =
                    Feature::Definition | Feature::References | Feature::Rename;
                if disabled {
                    semantic_features = Feature::None;
                    navigation_features = Feature::None;
                }
                let mappings = verbatim_segments(
                    &p.content,
                    &[first, second],
                    &[semantic_features, navigation_features],
                )?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text: r#virtual,
                        extension: ".ts".to_string(),
                        mappings: Some(raw_value(mappings)),
                        ..Default::default()
                    },
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// duplicate_projection.go
// ---------------------------------------------------------------------------

/// `duplicateProjectionHandler` emits the original content as both the
/// canonical output and a supplemental one, so a single original span has an
/// identical counterpart in two distinct virtual source files that share an
/// OriginalFileName. An edit to that span is therefore recorded once per
/// projection.
struct DuplicateProjectionHandler;

impl Handler for DuplicateProjectionHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                let canonical = identity_mapped_output(&p.content)?;
                let supplemental = identity_mapped_output(&p.content)?;
                respond(&TransformResult {
                    mapped_output: canonical,
                    supplemental: vec![SupplementalOutput {
                        mapped_output: supplemental,
                    }],
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// editing.go
// ---------------------------------------------------------------------------

struct PrefixedSupplementalHandler;

impl Handler for PrefixedSupplementalHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                const PREFIX: &str = "/* generated */\n";
                let mut features = Feature::All;
                if p.file_name.contains("folding-disabled")
                    || p.file_name.contains("codelens-disabled")
                    || p.file_name.contains("formatting-disabled")
                {
                    features = Feature::None;
                }
                let mut supplemental_text = format!("{PREFIX}{}", p.content);
                let mut segments = vec![Segment {
                    virtual_start: PREFIX.len() as TextPos,
                    virtual_end: (PREFIX.len() + p.content.len()) as TextPos,
                    original_start: 0,
                    original_end: p.content.len() as TextPos,
                    kind: Kind::Verbatim,
                    features,
                }];
                if p.file_name.contains("formatting-split") {
                    let Some(second_start) = p.content.find("function second") else {
                        return Err(
                            "contentmappertest: formatting-split input is missing function second"
                                .into(),
                        );
                    };
                    const GENERATED: &str = "const generated={x:1};\n";
                    supplemental_text = format!(
                        "{PREFIX}{}{GENERATED}{}",
                        &p.content[..second_start],
                        &p.content[second_start..]
                    );
                    segments = vec![
                        Segment {
                            virtual_start: PREFIX.len() as TextPos,
                            virtual_end: (PREFIX.len() + second_start) as TextPos,
                            original_start: 0,
                            original_end: second_start as TextPos,
                            kind: Kind::Verbatim,
                            features: Feature::All,
                        },
                        Segment {
                            virtual_start: (PREFIX.len() + second_start + GENERATED.len())
                                as TextPos,
                            virtual_end: supplemental_text.len() as TextPos,
                            original_start: second_start as TextPos,
                            original_end: p.content.len() as TextPos,
                            kind: Kind::Verbatim,
                            features: Feature::All,
                        },
                    ];
                }
                if p.file_name.contains("formatting-overlap") {
                    let second_start = p.content.find("function second");
                    let third_start = p.content.find("function third");
                    let (Some(second_start), Some(third_start)) = (second_start, third_start)
                    else {
                        return Err(
                            "contentmappertest: formatting-overlap input is missing function second or third"
                                .into(),
                        );
                    };
                    const WRAPPER_START: &str = "if (true) {\n";
                    const WRAPPER_END: &str = "}\n";
                    supplemental_text =
                        format!("{WRAPPER_START}{}{WRAPPER_END}", &p.content[second_start..]);
                    segments = vec![Segment {
                        virtual_start: WRAPPER_START.len() as TextPos,
                        virtual_end: (WRAPPER_START.len() + p.content.len() - second_start)
                            as TextPos,
                        original_start: second_start as TextPos,
                        original_end: p.content.len() as TextPos,
                        kind: Kind::Verbatim,
                        features: Feature::All,
                    }];
                    let canonical_mappings = SpanMap::new(&[Segment {
                        virtual_start: 0,
                        virtual_end: third_start as TextPos,
                        original_start: 0,
                        original_end: third_start as TextPos,
                        kind: Kind::Verbatim,
                        features: Feature::All,
                    }])
                    .marshal()?;
                    let mappings = SpanMap::new(&segments).marshal()?;
                    return respond(&TransformResult {
                        mapped_output: MappedOutput {
                            text: p.content[..third_start].to_string(),
                            extension: ".ts".to_string(),
                            mappings: Some(raw_value(canonical_mappings)),
                            ..Default::default()
                        },
                        supplemental: vec![SupplementalOutput {
                            mapped_output: MappedOutput {
                                text: supplemental_text,
                                extension: ".ts".to_string(),
                                mappings: Some(raw_value(mappings)),
                                ..Default::default()
                            },
                        }],
                        ..Default::default()
                    });
                }
                let mappings = SpanMap::new(&segments).marshal()?;
                let mut canonical = MappedOutput {
                    text: "export {};".to_string(),
                    extension: ".ts".to_string(),
                    ..Default::default()
                };
                if p.file_name.contains("folding-duplicate")
                    || p.file_name.contains("codelens-disabled")
                    || p.file_name.contains("codelens-duplicate")
                {
                    let canonical_mappings = SpanMap::new(&[Segment {
                        virtual_start: 0,
                        virtual_end: p.content.len() as TextPos,
                        original_start: 0,
                        original_end: p.content.len() as TextPos,
                        kind: Kind::Verbatim,
                        features: Feature::All,
                    }])
                    .marshal()?;
                    canonical = MappedOutput {
                        text: p.content.clone(),
                        extension: ".ts".to_string(),
                        mappings: Some(raw_value(canonical_mappings)),
                        ..Default::default()
                    };
                }
                respond(&TransformResult {
                    mapped_output: canonical,
                    supplemental: vec![SupplementalOutput {
                        mapped_output: MappedOutput {
                            text: supplemental_text,
                            extension: ".ts".to_string(),
                            mappings: Some(raw_value(mappings)),
                            ..Default::default()
                        },
                    }],
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

struct UnmappedFoldingHandler;

impl Handler for UnmappedFoldingHandler {
    fn handle_request(
        &self,
        _ctx: &Context,
        method: &str,
        _params: Option<Value>,
    ) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let mappings = SpanMap::new(&[]).marshal()?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text: "import \"a\";\nimport \"b\";\n/*\n * generated\n */\nexport {};"
                            .to_string(),
                        extension: ".ts".to_string(),
                        mappings: Some(raw_value(mappings)),
                        ..Default::default()
                    },
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// failing.go
// ---------------------------------------------------------------------------

struct FailingHandler;

impl Handler for FailingHandler {
    fn handle_request(
        &self,
        _ctx: &Context,
        method: &str,
        _params: Option<Value>,
    ) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => Err("content mapper failed to transform the file".into()),
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// hoisting.go
// ---------------------------------------------------------------------------

struct HoistingHandler;

impl Handler for HoistingHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                let (text, mappings) = transform_hoisting(&p.content)?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text,
                        extension: ".ts".to_string(),
                        mappings: Some(mappings),
                        ..Default::default()
                    },
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// `transformHoisting` emits the script body inside a render function, but lifts the leading run of import
// declarations above it, so the virtual text is laid out as:
//
//	///<reference types="svelte" />
//	;
//	import { existing } from "./dep";      <- original [importsStart, importsEnd)
//	function $$render() {
//	<whitespace before the first import>   <- original [scriptStart, importsStart)
//	<script body after the last import>    <- original [importsEnd, scriptEnd)
//	}
//
// This mirrors the layout svelte2tsx produces for a component. Hoisting splits the script into segments
// that are contiguous in the original but disjoint in the virtual text, so the original position at a
// splice point (importsStart) lies on the boundary of two verbatim segments and projects to two distinct
// exact virtual positions.
fn transform_hoisting(content: &str) -> Result<(String, Value), BoxedError> {
    let mut virtual_ = String::new();
    let mut segments: Vec<Segment> = Vec::new();

    let write_mapped = |virtual_: &mut String,
                        segments: &mut Vec<Segment>,
                        original_start: usize,
                        original_end: usize| {
        let virtual_start = virtual_.len() as TextPos;
        virtual_.push_str(&content[original_start..original_end]);
        segments.push(Segment {
            virtual_start,
            virtual_end: virtual_.len() as TextPos,
            original_start: original_start as TextPos,
            original_end: original_end as TextPos,
            kind: Kind::Verbatim,
            features: Feature::All,
        });
    };

    let (script_start, script_end) = script_range(content)?;
    let (imports_start, imports_end) = leading_import_range(content, script_start, script_end);

    virtual_.push_str("///<reference types=\"svelte\" />\n;\n");
    write_mapped(&mut virtual_, &mut segments, imports_start, imports_end);
    virtual_.push_str("\nfunction $$render() {");
    write_mapped(&mut virtual_, &mut segments, script_start, imports_start);
    write_mapped(&mut virtual_, &mut segments, imports_end, script_end);
    virtual_.push_str("\n;\nreturn { props: {} as Record<string, never> }}\n");

    let mappings = SpanMap::new(&segments).marshal()?;
    Ok((virtual_, raw_value(mappings)))
}

fn script_range(content: &str) -> Result<(usize, usize), BoxedError> {
    let Some(script_open) = content.find("<script") else {
        return Err("contentmappertest: missing <script> tag".into());
    };
    let Some(open_end_rel) = content[script_open..].find('>') else {
        return Err("contentmappertest: unclosed <script> tag".into());
    };
    let start = script_open + open_end_rel + 1;
    let Some(close_rel) = content[start..].find("</script>") else {
        return Err("contentmappertest: missing </script> tag".into());
    };
    Ok((start, start + close_rel))
}

/// `leadingImportRange` returns the range covering the run of import
/// declarations at the top of the script body, skipping the whitespace that
/// precedes them.
fn leading_import_range(content: &str, script_start: usize, script_end: usize) -> (usize, usize) {
    let bytes = content.as_bytes();
    let mut start = script_start;
    while start < script_end && is_space_byte(bytes[start]) {
        start += 1;
    }
    let mut end = start;
    while end < script_end && content[end..script_end].starts_with("import ") {
        match content[end..script_end].find('\n') {
            None => {
                end = script_end;
                break;
            }
            Some(line_end) => {
                end += line_end;
                while end < script_end && is_space_byte(bytes[end]) {
                    end += 1;
                }
            }
        }
    }
    while end > start && is_space_byte(bytes[end - 1]) {
        end -= 1;
    }
    (start, end)
}

fn is_space_byte(ch: u8) -> bool {
    ch == b' ' || ch == b'\t' || ch == b'\r' || ch == b'\n'
}

// ---------------------------------------------------------------------------
// lisp.go
// ---------------------------------------------------------------------------

struct LispHandler;

impl Handler for LispHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("lisp")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                // `strings.TrimSuffix(p.Content, "\n")` — one trailing newline only.
                if p.content.strip_suffix('\n').unwrap_or(&p.content) != "(+ 1 2 \"oops\")" {
                    return Err(format!(
                        "contentmappertest: unsupported Lisp expression {:?}",
                        p.content
                    )
                    .into());
                }
                let mappings = SpanMap::new(&[
                    Segment {
                        virtual_start: 0,
                        virtual_end: 3,
                        original_start: 1,
                        original_end: 2,
                        kind: Kind::Alias,
                        features: Feature::All,
                    },
                    Segment {
                        virtual_start: 4,
                        virtual_end: 5,
                        original_start: 3,
                        original_end: 4,
                        kind: Kind::Verbatim,
                        features: Feature::All,
                    },
                    Segment {
                        virtual_start: 7,
                        virtual_end: 8,
                        original_start: 5,
                        original_end: 6,
                        kind: Kind::Verbatim,
                        features: Feature::All,
                    },
                    Segment {
                        virtual_start: 10,
                        virtual_end: 16,
                        original_start: 7,
                        original_end: 13,
                        kind: Kind::Verbatim,
                        features: Feature::All,
                    },
                ])
                .marshal()?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text: "add(1, 2, \"oops\");".to_string(),
                        extension: ".ts".to_string(),
                        mappings: Some(raw_value(mappings)),
                        ..Default::default()
                    },
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// supplemental.go / supplemental_diagnostics.go / supplemental_globals.go /
// supplemental_module.go
// ---------------------------------------------------------------------------

struct SupplementalHandler;

impl Handler for SupplementalHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                let mapped_output = identity_mapped_output(&p.content)?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text: "export {};".to_string(),
                        extension: ".ts".to_string(),
                        ..Default::default()
                    },
                    supplemental: vec![SupplementalOutput { mapped_output }],
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

struct SupplementalDiagnosticsHandler;

impl Handler for SupplementalDiagnosticsHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                const PREFIX: &str = "missingSupplementalGlobal;\n";
                let mappings = SpanMap::new(&[Segment {
                    virtual_start: PREFIX.len() as TextPos,
                    virtual_end: (PREFIX.len() + p.content.len()) as TextPos,
                    original_end: p.content.len() as TextPos,
                    kind: Kind::Verbatim,
                    features: Feature::All,
                    ..Default::default()
                }])
                .marshal()?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text: "export {};".to_string(),
                        extension: ".ts".to_string(),
                        ..Default::default()
                    },
                    supplemental: vec![SupplementalOutput {
                        mapped_output: MappedOutput {
                            text: format!("{PREFIX}{}", p.content),
                            extension: ".ts".to_string(),
                            mappings: Some(raw_value(mappings)),
                            ..Default::default()
                        },
                    }],
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

struct SupplementalGlobalsHandler;

impl Handler for SupplementalGlobalsHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                let supplemental = if p.file_name.ends_with("/a.vue") {
                    "/// <reference path=\"./extra.d.ts\" />\ninterface Shared extends Extra { value: string }"
                } else if p.file_name.ends_with("/b.vue") {
                    "declare const shared: Shared;"
                } else {
                    return Err(format!(
                        "contentmappertest: unexpected supplemental global input {:?}",
                        p.file_name
                    )
                    .into());
                };
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text: "export default shared.value;".to_string(),
                        extension: ".ts".to_string(),
                        ..Default::default()
                    },
                    supplemental: vec![SupplementalOutput {
                        mapped_output: MappedOutput {
                            text: supplemental.to_string(),
                            extension: ".ts".to_string(),
                            ..Default::default()
                        },
                    }],
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

struct SupplementalModuleHandler;

impl Handler for SupplementalModuleHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let _p: TransformParams = params_of(&params)?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text: "export default 1;".to_string(),
                        extension: ".ts".to_string(),
                        ..Default::default()
                    },
                    supplemental: vec![SupplementalOutput {
                        mapped_output: MappedOutput {
                            text: "export const privateValue: number = \"wrong\";".to_string(),
                            extension: ".ts".to_string(),
                            ..Default::default()
                        },
                    }],
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// synthesizing.go
// ---------------------------------------------------------------------------

const SYNTHESIZED_OUTPUT: &str = "export const el = jsxRuntime(Widget);\n";

struct SynthesizingHandler;

impl Handler for SynthesizingHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let _p: TransformParams = params_of(&params)?;
                let mappings = SpanMap::new(&[]).marshal()?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text: SYNTHESIZED_OUTPUT.to_string(),
                        extension: ".ts".to_string(),
                        mappings: Some(raw_value(mappings)),
                        ..Default::default()
                    },
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

// ---------------------------------------------------------------------------
// component.go
// ---------------------------------------------------------------------------

struct ComponentHandler;

impl Handler for ComponentHandler {
    fn handle_request(&self, _ctx: &Context, method: &str, params: Option<Value>) -> HandlerResult {
        match method {
            METHOD_INITIALIZE => respond(&initialize_result("mapper")),
            METHOD_TRANSFORM => {
                let p: TransformParams = params_of(&params)?;
                let (text, mappings) = transform_component(&p.content)?;
                respond(&TransformResult {
                    mapped_output: MappedOutput {
                        text,
                        extension: ".ts".to_string(),
                        mappings: Some(mappings),
                        ..Default::default()
                    },
                    ..Default::default()
                })
            }
            _ => Err(format!("contentmappertest: unexpected method {method:?}").into()),
        }
    }

    handle_notification_noop!();
}

/// `virtual`/`segments` plus the Go closures capturing them (`writeMapped`,
/// `writeAnchored`, `writeSynthesized`) — a small writer struct since Rust
/// closures cannot share `&mut` captures.
struct ComponentWriter {
    virtual_: String,
    segments: Vec<Segment>,
}

impl ComponentWriter {
    /// `writeSynthesized`
    fn synthesized(&mut self, text: &str) {
        self.virtual_.push_str(text);
    }

    /// `writeMapped`
    fn mapped(&mut self, text: &str, original_start: usize, original_end: usize, kind: Kind) {
        let virtual_start = self.virtual_.len() as TextPos;
        self.virtual_.push_str(text);
        self.segments.push(Segment {
            virtual_start,
            virtual_end: self.virtual_.len() as TextPos,
            original_start: original_start as TextPos,
            original_end: original_end as TextPos,
            kind,
            features: Feature::All,
        });
    }

    /// `writeAnchored`
    fn anchored(&mut self, text: &str, original_position: usize, features: Feature) {
        let virtual_start = self.virtual_.len() as TextPos;
        self.virtual_.push_str(text);
        self.segments.push(Segment {
            virtual_start,
            virtual_end: self.virtual_.len() as TextPos,
            original_start: original_position as TextPos,
            original_end: original_position as TextPos,
            kind: Kind::Atom,
            features,
        });
    }
}

fn transform_component(content: &str) -> Result<(String, Value), BoxedError> {
    let mut w = ComponentWriter {
        virtual_: String::new(),
        segments: Vec::new(),
    };
    let bytes = content.as_bytes();

    if let Some(script_open) = content.find("<script") {
        let Some(open_end_rel) = content[script_open..].find('>') else {
            return Err("contentmappertest: unclosed <script> tag".into());
        };
        let script_start = script_open + open_end_rel + 1;
        let Some(close_rel) = content[script_start..].find("</script>") else {
            return Err("contentmappertest: missing </script> tag".into());
        };
        let script_end = script_start + close_rel;
        w.mapped(
            &content[script_start..script_end],
            script_start,
            script_end,
            Kind::Verbatim,
        );
    }

    w.synthesized("\nfunction __render() {\n");
    let mut search_start = 0;
    while search_start < content.len() {
        let Some(open_rel) = content[search_start..].find("{{") else {
            break;
        };
        let expr_start = search_start + open_rel + "{{".len();
        let Some(close_rel) = content[expr_start..].find("}}") else {
            return Err("contentmappertest: unclosed template expression".into());
        };
        let expr_end = expr_start + close_rel;
        w.synthesized("  void (");
        let mut pos = expr_start;
        while pos < expr_end {
            if !is_identifier_start(bytes[pos]) {
                w.synthesized(&content[pos..pos + 1]);
                pos += 1;
                continue;
            }
            let mut end = pos + 1;
            while end < expr_end && is_identifier_part(bytes[end]) {
                end += 1;
            }
            w.mapped(&content[pos..end], pos, end, Kind::Atom);
            pos = end;
        }
        w.synthesized(");\n");
        search_start = expr_end + "}}".len();
    }
    w.synthesized("}\n");
    if let Some((name_start, name_end)) = component_name_range(content) {
        w.synthesized("export class ");
        w.mapped(
            &content[name_start..name_end],
            name_start,
            name_end,
            Kind::Atom,
        );
        w.synthesized(" {}\n");
    }
    w.anchored(
        "export default {};\n",
        0,
        Feature::Definition | Feature::References,
    );

    let mappings = SpanMap::new(&w.segments).marshal()?;
    Ok((w.virtual_, raw_value(mappings)))
}

fn component_name_range(content: &str) -> Option<(usize, usize)> {
    let component_start = content.find("<component")?;
    let tag_end_rel = content[component_start..].find('>')?;
    let tag = &content[component_start..component_start + tag_end_rel];
    let name_rel = tag.find("name=\"")?;
    let start = component_start + name_rel + "name=\"".len();
    let end_rel = content[start..].find('"')?;
    Some((start, start + end_rel))
}

fn is_identifier_start(ch: u8) -> bool {
    ch == b'_' || ch == b'$' || ch.is_ascii_uppercase() || ch.is_ascii_lowercase()
}

fn is_identifier_part(ch: u8) -> bool {
    is_identifier_start(ch) || ch.is_ascii_digit()
}

// ---------------------------------------------------------------------------
// mapper_test.go — `#[cfg(test)]` port
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use std::env;
    use std::io::{Read as _, Write as _};
    use std::process::{self, Stdio};

    use tsc_contentmapper::{Mapper, ProjectSpec, Request, new_host};
    use tsc_core::options_generated::{CompilerOptions, ScriptTarget};
    use tsc_locale as locale;

    use super::*;

    // `helperEnv`, when set, makes the test binary act as the mapper
    // subprocess instead of running tests. This lets the out-of-process test
    // spawn a real subprocess (itself) that speaks the mapper protocol,
    // exercising the same handler code that the in-process spawner runs over
    // a pipe.
    const HELPER_ENV: &str = "TSGO_CONTENT_MAPPER_HELPER";

    /// `TestMain` — Go checks `helperEnv` before running tests; Rust has no
    /// TestMain, so the spawned binary runs this test instead.
    ///
    /// PORT: the helper serves the protocol on stdin/stderr — not
    /// stdin/stdout as Go's `stdio{}` does — because libtest writes
    /// "\nrunning N test(s)" to stdout before the test function runs, which
    /// would corrupt the protocol stream. The child's stdout (the harness
    /// banner plus any test output) is drained to the spawner's `stderr`
    /// log writer or discarded.
    #[test]
    fn mapper_helper() {
        if env::var(HELPER_ENV).ok().as_deref() != Some("1") {
            return;
        }
        let _ = serve(&Context::background(), Arc::new(ChildStdio));
        process::exit(0);
    }

    /// `stdio` — adapts the process's stdin/stderr to a ReadWriteCloser for
    /// the mapper server (see the PORT note on [mapper_helper]).
    struct ChildStdio;

    impl io::Read for &ChildStdio {
        fn read(&mut self, p: &mut [u8]) -> io::Result<usize> {
            io::stdin().read(p)
        }
    }

    impl io::Write for &ChildStdio {
        fn write(&mut self, p: &[u8]) -> io::Result<usize> {
            io::stderr().write(p)
        }

        fn flush(&mut self) -> io::Result<()> {
            io::stderr().flush()
        }
    }

    impl ipc::IoClose for ChildStdio {
        /// `stdio{}.Close()` — a no-op.
        fn close(&self) -> io::Result<()> {
            Ok(())
        }
    }

    fn test_mapper() -> Arc<Mapper> {
        Arc::new(Mapper {
            package: PACKAGE_NAME.to_string(),
            extensions: Some(vec![".box".to_string()]),
            name: PACKAGE_NAME.to_string(),
            version: "1.0.0".to_string(),
            exec: Some(vec![TRANSFORMING_MAPPER.to_string()]),
            compiler_options: Some(DECLARED_OPTIONS.clone()),
            package_directory: format!("/node_modules/{PACKAGE_NAME}").into(),
            ..Default::default()
        })
    }

    fn transform_request() -> Request {
        Request {
            file_name: "/app.box".into(),
            content: "export const version = #{target};\n".to_string(),
        }
    }

    /// `TestOutOfProcess` exercises the real out-of-process IPC path: it
    /// spawns the test binary as a mapper subprocess and drives it over pipes
    /// through the production content mapper host.
    #[test]
    fn test_out_of_process() {
        let ctx = Context::background();
        let host = new_host(&ctx, Arc::new(ExecSpawner), locale::DEFAULT);
        let mapper = test_mapper();
        let request = transform_request();
        let compiler_options = Arc::new(CompilerOptions {
            target: ScriptTarget::ES2020,
            ..Default::default()
        });
        let project = host
            .project(&ProjectSpec {
                config_file_name: "/tsconfig.json".into(),
                mappers: vec![mapper.clone()],
                compiler_options: Some(compiler_options),
            })
            .expect("host.Project returned no project");

        let result = project.transform(&mapper, &request).unwrap();
        assert!(
            result.text.contains("export const version = 7;"),
            "got {:?}",
            result.text
        );
        assert!(result.mappings.is_some());

        project.close().unwrap();
        host.close().unwrap();
    }

    /// `execSpawner` spawns the test binary itself as the mapper subprocess
    /// (guarded by `helperEnv`), so the test talks to a genuinely separate
    /// process over real pipes.
    struct ExecSpawner;

    impl Spawner for ExecSpawner {
        fn spawn(
            &self,
            _command: &[String],
            _dir: &str,
            stderr: Option<Box<dyn io::Write + Send>>,
        ) -> io::Result<Arc<dyn SpawnedProcess>> {
            let mut cmd = process::Command::new(env::current_exe()?);
            // `<binary> --exact <helper test> --quiet`: runs only the helper,
            // which serves the mapper protocol on stdin/stderr. libtest names
            // exclude the leading crate-name segment `module_path!()` carries.
            let helper_test = format!(
                "{}::mapper_helper",
                module_path!()
                    .strip_prefix(concat!(env!("CARGO_CRATE_NAME"), "::"))
                    .unwrap_or(module_path!())
            );
            cmd.env(HELPER_ENV, "1")
                .arg("--exact")
                .arg(helper_test)
                .arg("--quiet")
                .stdin(Stdio::piped())
                .stderr(Stdio::piped());
            if stderr.is_some() {
                // Go's `cmd.Stderr = stderr` carries mapper diagnostic output
                // to the log writer; the child's harness banner lands on its
                // stdout, so drain that channel into the writer instead.
                cmd.stdout(Stdio::piped());
            } else {
                cmd.stdout(Stdio::null());
            }
            let mut child = cmd.spawn()?;
            if let Some(mut writer) = stderr {
                let mut stdout = child.stdout.take().unwrap();
                thread::spawn(move || {
                    let _ = io::copy(&mut stdout, &mut writer);
                });
            }
            Ok(Arc::new(MapperProcess {
                stdin: Mutex::new(child.stdin.take()),
                stderr: Mutex::new(child.stderr.take().unwrap()),
                child: Mutex::new(child),
            }))
        }
    }

    /// `process` — adapts a spawned subprocess's stdio to the
    /// [`SpawnedProcess`] interface: reads come from its stderr (the protocol
    /// channel — see [mapper_helper]'s PORT note), writes go to its stdin,
    /// and `spawned_close` tears the process down.
    struct MapperProcess {
        child: Mutex<process::Child>,
        stdin: Mutex<Option<process::ChildStdin>>,
        stderr: Mutex<process::ChildStderr>,
    }

    impl SpawnedProcess for MapperProcess {
        fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize> {
            self.stderr.lock().unwrap().read(buf)
        }

        fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
            let mut stdin = self.stdin.lock().unwrap();
            let Some(stdin) = stdin.as_mut() else {
                return Err(io::Error::new(io::ErrorKind::BrokenPipe, "stdin closed"));
            };
            stdin.write(buf)
        }

        fn spawned_flush(&self) -> io::Result<()> {
            let mut stdin = self.stdin.lock().unwrap();
            if let Some(stdin) = stdin.as_mut() {
                stdin.flush()?;
            }
            Ok(())
        }

        fn spawned_close(&self) -> io::Result<()> {
            // `_ = p.stdin.Close(); _ = p.cmd.Process.Kill(); _ = p.cmd.Wait()`
            drop(self.stdin.lock().unwrap().take());
            let mut child = self.child.lock().unwrap();
            let _ = child.kill();
            let _ = child.wait();
            Ok(())
        }

        fn spawned_exit_code(&self) -> Option<i64> {
            self.child
                .lock()
                .unwrap()
                .try_wait()
                .ok()
                .flatten()
                .and_then(|status| status.code())
                .map(|code| code as i64)
        }
    }
}
