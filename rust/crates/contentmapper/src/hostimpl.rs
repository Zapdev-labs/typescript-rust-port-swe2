// Ported from tsc/internal/contentmapper/hostimpl.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `context.Context` → `tsc_core::context::Context`. Go's
//   `context.WithTimeout` becomes a `with_cancel` child plus a timer thread
//   that cancels it after `INITIALIZE_TIMEOUT` (the ported `Context` has no
//   deadline support; `DeadlineExceeded` folds into `ContextCanceled`, which
//   the Go classification treats identically — `initializeCtxErr != nil`).
// - `context.AfterFunc(ctx, f)` → a spawned thread that waits on
//   `ctx.wait_cancelled()` and runs `f` unless the `stop` flag was set first.
// - `io.ReadWriteCloser` → the [`SpawnedProcess`] trait (`&self` methods, so
//   the shared `Arc` can be read and written concurrently like Go's stream).
//   `processExitState.ExitCode() (int, bool)` → `spawned_exit_code() ->
//   Option<i64>` (`None` is Go's `false`).
// - `io.Closer` closer handles → `Arc<dyn IoClose>` (`tsc_ipc::IoClose`).
// - `stderr io.Writer` on `Spawner` → `Option<Box<dyn io::Write + Send>>`;
//   `None` is Go's `io.Discard` (nothing is written).
// - `sync.OnceFunc` release functions → [`AcquireLease`] (`release` is
//   idempotent; `Drop` releases like a Go `defer release()`).
// - `dialFunc` → `DialFn`; the Go `(conn, closer, encoding, source, err)`
//   tuple becomes `Result<DialOutcome, Error>` — a non-nil `err` always meant
//   the rest were nil/"".
// - `map[*Mapper]string` lease entries → keyed by `Arc::as_ptr` (pointer
//   identity, like Go's map key); `projectSpecKey` embeds `Arc` addresses as
//   Go's `%p` did.
// - Go's `panic` on a negative project refcount stays a `panic!`.
// - `Project` handles are `Arc<ProjectLease>`-backed `ProjectHandle`s; the
//   lease holds the host weakly so the host -> lease -> host ownership cycle
//   Go's GC would collect cannot leak in Rust.

use std::borrow::Cow;
use std::fmt;
use std::io;
use std::sync::atomic::{AtomicBool, AtomicI64, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, RwLock, Weak};
use std::thread;
use std::time::{Duration, Instant};

use rustc_hash::FxHashMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use tsc_ast as ast;
use tsc_core::context::{CancelFunc, Context};
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::TextRange;
use tsc_diagnostics::Category;
use tsc_ipc::{self as ipc, Conn, Handler, IoClose, Message, Protocol};
use tsc_json as json;
use tsc_json::Value;
use tsc_jsonrpc as jsonrpc;
use tsc_locale::Locale;
use tsc_spanmap::{self as spanmap, SpanMap};
use tsc_tspath::{self as tspath, RootedFilePath};

use crate::contentmapper::{Mapper, is_supported_virtual_extension};
use crate::host::{
    DiagnosticDirectiveError, DiagnosticDirectiveErrorKind, Error, Host, InitializeError,
    InitializeErrorKind, InvalidVirtualExtensionError, MappedResult, MapperTimings,
    OperationTiming, OptionDiagnostic, OptionPathSegment, Project, ProjectError, ProjectErrorKind,
    ProjectSpec, Request, Result, Timings, TransformErrorKind,
};
use crate::xxh3;

const INITIALIZE_TIMEOUT_SECONDS: i64 = 5;
const INITIALIZE_TIMEOUT: Duration = Duration::from_secs(INITIALIZE_TIMEOUT_SECONDS as u64);

// Content mapper protocol method names.
/// `MethodInitialize`
pub const METHOD_INITIALIZE: &str = "initialize";
/// `MethodOpenProject`
pub const METHOD_OPEN_PROJECT: &str = "openProject";
/// `MethodCloseProject`
pub const METHOD_CLOSE_PROJECT: &str = "closeProject";
/// `MethodTransform`
pub const METHOD_TRANSFORM: &str = "transform";

/// `type InitializeParams struct` — the parameter object for the initialize
/// request.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct InitializeParams {
    /// `Locale` is the BCP 47 locale to use for mapper-authored diagnostic
    /// messages, when configured.
    #[serde(rename = "locale", default, skip_serializing_if = "String::is_empty")]
    pub locale: String,
    /// `PositionEncodings` lists the coordinate spaces the host accepts.
    #[serde(rename = "positionEncodings")]
    pub position_encodings: Vec<PositionEncoding>,
}

/// `type InitializeResult struct` — the mapper's response to the initialize
/// request.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct InitializeResult {
    /// `PositionEncoding` selects the coordinate space for all mappings and
    /// diagnostics.
    #[serde(rename = "positionEncoding", default)]
    pub position_encoding: PositionEncoding,
    /// `DiagnosticSource` is the prefix used for every mapper-authored
    /// diagnostic code.
    #[serde(rename = "diagnosticSource", default)]
    pub diagnostic_source: String,
}

/// `type OpenProjectParams struct` — the parameter object for the
/// openProject request.
///
/// PORT: `Deserialize` exists for test handlers that parse their own
/// params (Go's production type is marshal-only, but `json.Unmarshal` into
/// it works there too).
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct OpenProjectParams {
    /// `ConfigFileName` is the absolute project configuration file name, or
    /// empty when there is none.
    #[serde(rename = "configFileName")]
    pub config_file_name: String,
    /// `ProjectHandle` is an opaque, process-local handle assigned by the
    /// host.
    #[serde(rename = "projectHandle")]
    pub project_handle: String,
    /// `Options` is the mapper entry's options from the project's
    /// contentMappers configuration.
    ///
    /// PORT: Go's `omitempty` on `json.Value` omits nil *and* empty values.
    #[serde(rename = "options", default, skip_serializing_if = "value_is_empty")]
    pub options: Option<Value>,
    /// `CompilerOptions` contains the project's effective compiler options.
    #[serde(rename = "compilerOptions")]
    pub compiler_options: Value,
}

fn value_is_empty(v: &Option<Value>) -> bool {
    v.as_ref().map_or(true, |v| v.get().is_empty())
}

/// `omitempty` on a Go slice omits nil *and* empty.
fn option_vec_is_empty<T>(v: &Option<Vec<T>>) -> bool {
    v.as_ref().map_or(true, Vec::is_empty)
}

/// Go `json.Unmarshal` of `null` into a slice field yields a nil slice (no
/// error); serde's `Vec` errors instead. `null_is_default` mirrors Go —
/// `null` and absent both produce the empty vec.
fn null_is_default<'de, D, T>(d: D) -> std::result::Result<T, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de> + Default,
{
    Option::<T>::deserialize(d).map(Option::unwrap_or_default)
}

/// `type OpenProjectResult struct` — the mapper's response to an openProject
/// request. `config_identity` and `watched_files` may only be returned by
/// mappers that declare dynamicConfig.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct OpenProjectResult {
    /// `ConfigIdentity` is a stable fingerprint of all dynamic configuration
    /// that can affect transforms.
    #[serde(rename = "configIdentity", default)]
    pub config_identity: String,
    /// `WatchedFiles` are absolute files whose changes may alter
    /// `config_identity` or transform output.
    #[serde(
        rename = "watchedFiles",
        default,
        skip_serializing_if = "option_vec_is_empty"
    )]
    pub watched_files: Option<Vec<String>>,
    /// `OptionDiagnostics` report invalid mapper options. Paths are relative
    /// to the mapper entry's options object.
    #[serde(
        rename = "optionDiagnostics",
        default,
        skip_serializing_if = "option_vec_is_empty"
    )]
    pub option_diagnostics: Option<Vec<OptionDiagnosticResult>>,
}

/// `type OptionDiagnosticResult struct`
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct OptionDiagnosticResult {
    /// `Path []json.Value` — Go's `null` → nil slice, so accept `null` too.
    #[serde(rename = "path", default, deserialize_with = "null_is_default")]
    pub path: Vec<Value>,
    /// `MessageText string`
    #[serde(rename = "messageText", default)]
    pub message_text: String,
    /// `Code int32`
    #[serde(rename = "code", default)]
    pub code: i32,
}

/// `type CloseProjectParams struct` — the parameter object for the
/// closeProject request.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct CloseProjectParams {
    /// `ProjectHandle string`
    #[serde(rename = "projectHandle", default)]
    pub project_handle: String,
}

/// `type PositionEncoding string` — the coordinate space a mapper uses for
/// mappings and diagnostics.
///
/// PORT: a newtype, as in Go — mappers can return unrecognized encodings
/// (the host rejects anything other than UTF-8/UTF-16 after the handshake).
/// `Cow` keeps the `UTF8`/`UTF16` associated consts constructible.
#[derive(Clone, Default, PartialEq, Eq, Hash)]
pub struct PositionEncoding(pub Cow<'static, str>);

impl PositionEncoding {
    /// `PositionEncodingUTF8`
    pub const UTF8: PositionEncoding = PositionEncoding(Cow::Borrowed("utf-8"));
    /// `PositionEncodingUTF16`
    pub const UTF16: PositionEncoding = PositionEncoding(Cow::Borrowed("utf-16"));

    /// `string(p)` — the underlying wire value.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for PositionEncoding {
    /// `string(p)`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl fmt::Debug for PositionEncoding {
    /// Go `%q` — the quoted string, as in `InitializeError`'s
    /// `unsupported position encoding "utf-32"`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.0, f)
    }
}

impl Serialize for PositionEncoding {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        self.0.serialize(s)
    }
}

impl<'de> Deserialize<'de> for PositionEncoding {
    fn deserialize<D: Deserializer<'de>>(d: D) -> std::result::Result<Self, D::Error> {
        Ok(PositionEncoding(Cow::Owned(String::deserialize(d)?)))
    }
}

/// `type TransformParams struct` — the parameter object for the transform
/// request.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct TransformParams {
    /// `FileName` is the absolute name of the content-mapped source file
    /// being transformed.
    #[serde(rename = "fileName", default)]
    pub file_name: String,
    /// `Content` is the content-mapped source file's text.
    #[serde(rename = "content", default)]
    pub content: String,
    /// `ProjectHandle` identifies the mapper project configuration opened
    /// for this transform.
    #[serde(rename = "projectHandle", default)]
    pub project_handle: String,
}

/// `type MappedOutput struct` — virtual source text and its mapping to an
/// original input.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct MappedOutput {
    /// `Text` is the virtual JavaScript or TypeScript source text.
    #[serde(rename = "text", default)]
    pub text: String,
    /// `Extension` determines the virtual source file's syntax.
    #[serde(rename = "extension", default)]
    pub extension: String,
    /// `Mappings` is the span map's tuple-array JSON (see
    /// `spanmap.Unmarshal`), expressed in the selected position encoding.
    /// Absent or empty means the output is fully synthesized.
    #[serde(rename = "mappings", default, skip_serializing_if = "value_is_empty")]
    pub mappings: Option<Value>,
    /// `DiagnosticDirectives` describe framework directives that suppress
    /// TypeScript diagnostics in virtual ranges and optionally report an
    /// error when no diagnostic is produced.
    #[serde(
        rename = "diagnosticDirectives",
        default,
        skip_serializing_if = "Option::is_none"
    )]
    pub diagnostic_directives: Option<DiagnosticDirectives>,
}

/// `type DiagnosticDirectivePolicy uint8` — the numeric policy stored in a
/// mapped diagnostic directive tuple.
///
/// PORT: a newtype (like `spanmap::Kind`) — unknown values remain
/// representable so the host can reject them with `InvalidPolicy`.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct DiagnosticDirectivePolicy(pub u8);

impl DiagnosticDirectivePolicy {
    /// `DiagnosticDirectivePolicyIgnore`
    pub const IGNORE: DiagnosticDirectivePolicy = DiagnosticDirectivePolicy(0);
    /// `DiagnosticDirectivePolicyExpect`
    pub const EXPECT: DiagnosticDirectivePolicy = DiagnosticDirectivePolicy(1);
}

impl Serialize for DiagnosticDirectivePolicy {
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        self.0.serialize(s)
    }
}

impl<'de> Deserialize<'de> for DiagnosticDirectivePolicy {
    fn deserialize<D: Deserializer<'de>>(d: D) -> std::result::Result<Self, D::Error> {
        Ok(DiagnosticDirectivePolicy(u8::deserialize(d)?))
    }
}

/// `type UnusedExpectDirectiveDiagnostic struct`
#[derive(Clone, Default, Debug, Serialize, Deserialize, PartialEq)]
pub struct UnusedExpectDirectiveDiagnostic {
    /// `Code int32`
    #[serde(rename = "code", default)]
    pub code: i32,
    /// `MessageText string`
    #[serde(rename = "messageText", default)]
    pub message_text: String,
}

/// `type DiagnosticDirectives struct` — shares unused-expect diagnostics
/// across compact directive tuples.
#[derive(Clone, Default, Debug, Serialize, Deserialize, PartialEq)]
pub struct DiagnosticDirectives {
    /// `UnusedExpectDirectiveDiagnostics` — `Option` preserves Go's
    /// nil-slice `null` wire form.
    #[serde(rename = "unusedExpectDirectiveDiagnostics", default)]
    pub unused_expect_directive_diagnostics: Option<Vec<UnusedExpectDirectiveDiagnostic>>,
    /// `Directives` — ditto.
    #[serde(rename = "directives", default)]
    pub directives: Option<Vec<MappedDiagnosticDirective>>,
}

/// `type MappedDiagnosticDirective struct` — encoded as
/// `[originalStart, originalLength, virtualStart, virtualEnd, policy,
/// unusedExpectDirectiveIndex?]`. An omitted index selects the only
/// unused-expect diagnostic and is invalid when there is not exactly one.
#[derive(Clone, Default, Debug, PartialEq)]
pub struct MappedDiagnosticDirective {
    /// `OriginalStart int`
    pub original_start: i64,
    /// `OriginalLength int`
    pub original_length: i64,
    /// `VirtualStart int`
    pub virtual_start: i64,
    /// `VirtualEnd int`
    pub virtual_end: i64,
    /// `Policy DiagnosticDirectivePolicy`
    pub policy: DiagnosticDirectivePolicy,
    /// `UnusedExpectDirectiveIndex *int`
    pub unused_expect_directive_index: Option<i64>,
}

impl Serialize for MappedDiagnosticDirective {
    /// `func (d MappedDiagnosticDirective) MarshalJSONTo`
    fn serialize<S: Serializer>(&self, s: S) -> std::result::Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;
        let mut seq = s.serialize_seq(Some(
            5 + usize::from(self.unused_expect_directive_index.is_some()),
        ))?;
        seq.serialize_element(&self.original_start)?;
        seq.serialize_element(&self.original_length)?;
        seq.serialize_element(&self.virtual_start)?;
        seq.serialize_element(&self.virtual_end)?;
        seq.serialize_element(&self.policy)?;
        if let Some(index) = self.unused_expect_directive_index {
            seq.serialize_element(&index)?;
        }
        seq.end()
    }
}

impl<'de> Deserialize<'de> for MappedDiagnosticDirective {
    /// `func (d *MappedDiagnosticDirective) UnmarshalJSONFrom` — the Go
    /// error text ("diagnostic directive tuple ...") is preserved verbatim;
    /// tests assert on it.
    fn deserialize<D: Deserializer<'de>>(d: D) -> std::result::Result<Self, D::Error> {
        let tuple = Vec::<serde_json::Value>::deserialize(d)?;
        if tuple.len() != 5 && tuple.len() != 6 {
            return Err(serde::de::Error::custom(format!(
                "diagnostic directive tuple must contain 5 or 6 elements, got {}",
                tuple.len()
            )));
        }
        let mut directive = MappedDiagnosticDirective::default();
        directive.original_start = tuple_int(&tuple[0], 0).map_err(serde::de::Error::custom)?;
        directive.original_length = tuple_int(&tuple[1], 1).map_err(serde::de::Error::custom)?;
        directive.virtual_start = tuple_int(&tuple[2], 2).map_err(serde::de::Error::custom)?;
        directive.virtual_end = tuple_int(&tuple[3], 3).map_err(serde::de::Error::custom)?;
        directive.policy = serde_json::from_value::<u8>(tuple[4].clone())
            .map(DiagnosticDirectivePolicy)
            .map_err(|e| {
                serde::de::Error::custom(format!(
                    "invalid diagnostic directive tuple element 4: {e}"
                ))
            })?;
        if tuple.len() == 6 {
            directive.unused_expect_directive_index =
                Some(tuple_int(&tuple[5], 5).map_err(serde::de::Error::custom)?);
        }
        Ok(directive)
    }
}

/// `json.Unmarshal(tuple[i], &int)` with Go's per-element error text.
/// Callers wrap the message in `serde::de::Error::custom`.
fn tuple_int(v: &serde_json::Value, i: usize) -> std::result::Result<i64, String> {
    serde_json::from_value::<i64>(v.clone())
        .map_err(|e| format!("invalid diagnostic directive tuple element {i}: {e}"))
}

/// `type SupplementalOutput struct`
///
/// PORT: `Serialize` uses `#[serde(flatten)]` like the other wire types, but
/// `Deserialize` must delegate to `MappedOutput` directly — serde's
/// `flatten` buffers the embedded content through `serde::de::Content`,
/// which cannot produce the `Box<RawValue>` in `MappedOutput::mappings`.
#[derive(Clone, Default, Debug, Serialize)]
pub struct SupplementalOutput {
    /// `MappedOutput` (embedded).
    #[serde(flatten)]
    pub mapped_output: MappedOutput,
}

impl<'de> Deserialize<'de> for SupplementalOutput {
    /// Go's `json.Unmarshal` — the wire shape is exactly `MappedOutput`'s.
    fn deserialize<D: Deserializer<'de>>(d: D) -> std::result::Result<Self, D::Error> {
        Ok(SupplementalOutput {
            mapped_output: MappedOutput::deserialize(d)?,
        })
    }
}

/// `type TransformResult struct` — the canonical output for one input file.
///
/// PORT: same `flatten`/`RawValue` constraint as [`SupplementalOutput`] —
/// the manual `Deserialize` spells the embedded `MappedOutput` fields
/// inline through a private wire struct.
#[derive(Clone, Default, Debug, Serialize)]
pub struct TransformResult {
    /// `MappedOutput` (embedded).
    #[serde(flatten)]
    pub mapped_output: MappedOutput,
    /// `Diagnostics` are mapper-authored errors expressed in original-source
    /// coordinates.
    #[serde(rename = "diagnostics", default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<Diagnostic>,
    /// `Supplemental` contains additional unnamed compiler inputs associated
    /// with this source file.
    #[serde(
        rename = "supplemental",
        default,
        skip_serializing_if = "Vec::is_empty"
    )]
    pub supplemental: Vec<SupplementalOutput>,
}

impl<'de> Deserialize<'de> for TransformResult {
    /// Go's `json.Unmarshal` into the flattened `TransformResult` shape. The
    /// private wire struct keeps `mappings`' `Box<RawValue>` on serde_json's
    /// real deserializer (see [`SupplementalOutput`]).
    fn deserialize<D: Deserializer<'de>>(d: D) -> std::result::Result<Self, D::Error> {
        #[derive(Deserialize)]
        struct Wire {
            #[serde(rename = "text", default)]
            text: String,
            #[serde(rename = "extension", default)]
            extension: String,
            #[serde(rename = "mappings", default)]
            mappings: Option<Value>,
            #[serde(rename = "diagnosticDirectives", default)]
            diagnostic_directives: Option<DiagnosticDirectives>,
            #[serde(rename = "diagnostics", default, deserialize_with = "null_is_default")]
            diagnostics: Vec<Diagnostic>,
            #[serde(rename = "supplemental", default, deserialize_with = "null_is_default")]
            supplemental: Vec<SupplementalOutput>,
        }
        let wire = Wire::deserialize(d)?;
        Ok(TransformResult {
            mapped_output: MappedOutput {
                text: wire.text,
                extension: wire.extension,
                mappings: wire.mappings,
                diagnostic_directives: wire.diagnostic_directives,
            },
            diagnostics: wire.diagnostics,
            supplemental: wire.supplemental,
        })
    }
}

/// `type Diagnostic struct` — an error reported by a mapper in
/// original-source coordinates.
#[derive(Clone, Default, Debug, Serialize, Deserialize)]
pub struct Diagnostic {
    /// `MessageText` is the diagnostic message.
    #[serde(rename = "messageText", default)]
    pub message_text: String,
    /// `Start` and `Length` locate the diagnostic in the original content
    /// using the selected position encoding.
    #[serde(rename = "start", default)]
    pub start: i64,
    /// `Length int`
    #[serde(rename = "length", default)]
    pub length: i64,
    /// `Code int32`
    #[serde(rename = "code", default)]
    pub code: i32,
}

// ---------------------------------------------------------------------------
// Spawning seam
// ---------------------------------------------------------------------------

/// `io.ReadWriteCloser` for a spawned mapper process — read is the process's
/// stdout, write is its stdin, `spawned_close` tears the process down.
/// `&self` methods let one `Arc` be read and written concurrently like Go's
/// stream.
pub trait SpawnedProcess: Send + Sync {
    /// `io.Reader`
    fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize>;
    /// `io.Writer`
    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize>;
    /// Flush — Go's `io.Writer` has no flush; pipes don't buffer, so the
    /// default is a no-op like a `net.Pipe` write.
    fn spawned_flush(&self) -> io::Result<()> {
        Ok(())
    }
    /// `io.Closer` — tears the process down.
    fn spawned_close(&self) -> io::Result<()>;
    /// `processExitState.ExitCode() (int, bool)` — `None` is Go's `false`
    /// (the process has not exited / cannot report a code).
    fn spawned_exit_code(&self) -> Option<i64> {
        None
    }
}

/// `type Spawner interface` — starts a child process, returning its stdio.
/// `stderr` is `Some` writer when logging is enabled (Go passes `io.Discard`
/// otherwise — `None` here means "discard").
///
/// This seam keeps `std::process` out of this package: production hosts
/// spawn a real process, tests supply an in-process pipe.
pub trait Spawner: Send + Sync {
    /// `Spawn(command, dir, stderr)`
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn io::Write + Send>>,
    ) -> io::Result<Arc<dyn SpawnedProcess>>;
}

/// `type SpawnerFunc func(...)` — adapts a spawn function to the `Spawner`
/// interface.
pub struct SpawnerFunc<F>(pub F);

impl<F> Spawner for SpawnerFunc<F>
where
    F: Fn(
            &[String],
            &str,
            Option<Box<dyn io::Write + Send>>,
        ) -> io::Result<Arc<dyn SpawnedProcess>>
        + Send
        + Sync,
{
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn io::Write + Send>>,
    ) -> io::Result<Arc<dyn SpawnedProcess>> {
        (self.0)(command, dir, stderr)
    }
}

/// `type SpawnerFunc func(command []string, dir string, stderr io.Writer) (io.ReadWriteCloser, error)`
///
/// PORT: a blanket impl over matching closures — Go's named func type with
/// a `Spawn` method. `Arc::new(closure)` coerces to `Arc<dyn Spawner>` at
/// `new_host` calls.
impl<F> Spawner for F
where
    F: Fn(
            &[String],
            &str,
            Option<Box<dyn io::Write + Send>>,
        ) -> io::Result<Arc<dyn SpawnedProcess>>
        + Send
        + Sync,
{
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn io::Write + Send>>,
    ) -> io::Result<Arc<dyn SpawnedProcess>> {
        self(command, dir, stderr)
    }
}

/// `type Logger func(message string)` — receives content mapper protocol and
/// process output as complete log lines.
pub type Logger = Arc<dyn Fn(&str) + Send + Sync>;

/// `type HostOptions struct` — configures optional content mapper process
/// logging.
#[derive(Clone, Default)]
pub struct HostOptions {
    /// `Logger Logger`
    pub logger: Option<Logger>,
}

/// The [`io::Read`]/[`io::Write`]/[`IoClose`] adapter that lets a spawned
/// process feed `tsc_ipc`'s protocol halves (which read through `&S`).
struct ProcessIo(Arc<dyn SpawnedProcess>);

impl io::Read for &ProcessIo {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.spawned_read(buf)
    }
}

impl io::Write for &ProcessIo {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.spawned_write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.0.spawned_flush()
    }
}

impl IoClose for ProcessIo {
    fn close(&self) -> io::Result<()> {
        self.0.spawned_close()
    }
}

/// `type loggingProtocol struct` — logs every protocol message before
/// forwarding it to the wrapped protocol.
struct LoggingProtocol {
    inner: Arc<dyn Protocol>,
    mapper_name: String,
    logger: Logger,
}

impl LoggingProtocol {
    /// `func (p *loggingProtocol) log(direction, message)`
    fn log<T: Serialize>(&self, direction: &str, message: &T) {
        match json::marshal(message, &[]) {
            Err(e) => (self.logger)(&format!(
                "[content mapper: {}] {direction}: <failed to serialize: {e}>",
                self.mapper_name
            )),
            Ok(data) => (self.logger)(&format!(
                "[content mapper: {}] {direction}: {}",
                self.mapper_name,
                String::from_utf8_lossy(&data)
            )),
        }
    }
}

impl Protocol for LoggingProtocol {
    /// `ReadMessage` — logs only successfully read messages (Go's
    /// `err == nil` check).
    fn read_message(&self) -> std::result::Result<Message, ipc::Error> {
        let message = self.inner.read_message()?;
        self.log("receive", &message);
        Ok(message)
    }

    /// `WriteRequest`
    fn write_request(
        &self,
        id: Option<&jsonrpc::ID>,
        method: &str,
        params: Option<Value>,
    ) -> std::result::Result<(), ipc::Error> {
        self.log(
            "send",
            &jsonrpc::RequestMessage::<Value> {
                jsonrpc: jsonrpc::JSONRPCVersion,
                id: id.cloned(),
                method: method.to_string(),
                params: params.clone(),
            },
        );
        self.inner.write_request(id, method, params)
    }

    /// `WriteNotification`
    fn write_notification(
        &self,
        method: &str,
        params: Option<Value>,
    ) -> std::result::Result<(), ipc::Error> {
        self.log(
            "send",
            &jsonrpc::RequestMessage::<Value> {
                jsonrpc: jsonrpc::JSONRPCVersion,
                id: None,
                method: method.to_string(),
                params: params.clone(),
            },
        );
        self.inner.write_notification(method, params)
    }

    /// `WriteResponse`
    fn write_response(
        &self,
        id: Option<&jsonrpc::ID>,
        result: Option<ipc::ResponsePayload>,
    ) -> std::result::Result<(), ipc::Error> {
        let log_result = match &result {
            // `msg.Result` logs the `any` marshaled like `json.Marshal` —
            // `[]byte` becomes a base64 string.
            Some(ipc::ResponsePayload::Binary(b)) => Some(ipc::marshal_params(
                &ipc::base64_std_encode(b),
            )?),
            Some(ipc::ResponsePayload::Json(v)) => Some(v.clone()),
            None => None,
        };
        self.log(
            "send",
            &jsonrpc::ResponseMessage::<Value> {
                jsonrpc: jsonrpc::JSONRPCVersion,
                id: id.cloned(),
                result: log_result,
                error: None,
            },
        );
        self.inner.write_response(id, result)
    }

    /// `WriteError`
    fn write_error(
        &self,
        id: Option<&jsonrpc::ID>,
        err: &jsonrpc::ResponseError,
    ) -> std::result::Result<(), ipc::Error> {
        self.log(
            "send",
            &jsonrpc::ResponseMessage::<Value> {
                jsonrpc: jsonrpc::JSONRPCVersion,
                id: id.cloned(),
                result: None,
                error: Some(err.clone()),
            },
        );
        self.inner.write_error(id, err)
    }
}

/// `type stderrLogger struct` — buffers stderr writes and logs complete
/// lines.
struct StderrLogger {
    mapper_name: String,
    logger: Logger,
    state: Mutex<StderrLoggerState>,
}

#[derive(Default)]
struct StderrLoggerState {
    pending: String,
}

impl StderrLogger {
    fn new(mapper_name: String, logger: Logger) -> Arc<StderrLogger> {
        Arc::new(StderrLogger {
            mapper_name,
            logger,
            state: Mutex::new(StderrLoggerState::default()),
        })
    }

    /// `func (w *stderrLogger) Write` — emits complete lines; partial lines
    /// stay buffered until `flush_lines`.
    fn write_lines(&self, data: &[u8]) {
        let mut lines: Vec<String> = Vec::new();
        {
            let mut state = self.state.lock().unwrap();
            state.pending.push_str(&String::from_utf8_lossy(data));
            while let Some(index) = state.pending.find('\n') {
                let line = state.pending[..index].trim_end_matches('\r').to_string();
                state.pending.drain(..index + 1);
                lines.push(line);
            }
        }
        for line in lines {
            self.log(&line);
        }
    }

    /// `func (w *stderrLogger) flush`
    fn flush_lines(&self) {
        let pending = {
            let mut state = self.state.lock().unwrap();
            std::mem::take(&mut state.pending)
        };
        if !pending.is_empty() {
            self.log(pending.trim_end_matches('\r'));
        }
    }

    /// `func (w *stderrLogger) log`
    fn log(&self, message: &str) {
        (self.logger)(&format!(
            "[content mapper: {}] stderr: {message}",
            self.mapper_name
        ));
    }
}

/// `stderrLogger` as a boxed `io::Write` for the spawner — delegates to the
/// shared logger so `LoggedProcess` can `flush_lines` on close.
struct StderrLoggerWriter(Arc<StderrLogger>);

impl io::Write for StderrLoggerWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write_lines(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// `type loggedProcess struct` — flushes the stderr logger when the process
/// is torn down.
struct LoggedProcess {
    inner: Arc<dyn SpawnedProcess>,
    stderr: Arc<StderrLogger>,
}

impl SpawnedProcess for LoggedProcess {
    fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.inner.spawned_read(buf)
    }

    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
        self.inner.spawned_write(buf)
    }

    fn spawned_flush(&self) -> io::Result<()> {
        self.inner.spawned_flush()
    }

    /// `func (p *loggedProcess) Close`
    fn spawned_close(&self) -> io::Result<()> {
        let err = self.inner.spawned_close();
        self.stderr.flush_lines();
        err
    }

    fn spawned_exit_code(&self) -> Option<i64> {
        self.inner.spawned_exit_code()
    }
}

/// `type closeOnceReadWriteCloser struct` — `close` runs once and returns
/// the first result on every call (Go's `sync.Once` + stored err).
struct CloseOnce {
    inner: Arc<dyn SpawnedProcess>,
    state: Mutex<CloseOnceState>,
}

#[derive(Default)]
struct CloseOnceState {
    closed: bool,
    /// Go stores the first close's `error` and returns it again; the error
    /// is shared as `Arc` since `io::Error` is not `Clone`.
    result: Option<Arc<io::Error>>,
}

impl SpawnedProcess for CloseOnce {
    fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.inner.spawned_read(buf)
    }

    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
        self.inner.spawned_write(buf)
    }

    fn spawned_flush(&self) -> io::Result<()> {
        self.inner.spawned_flush()
    }

    /// `func (c *closeOnceReadWriteCloser) Close`
    fn spawned_close(&self) -> io::Result<()> {
        let mut state = self.state.lock().unwrap();
        if !state.closed {
            state.closed = true;
            state.result = self.inner.spawned_close().err().map(Arc::new);
        }
        match &state.result {
            Some(e) => Err(io::Error::new(e.kind(), e.to_string())),
            None => Ok(()),
        }
    }

    /// `func (c *closeOnceReadWriteCloser) ExitCode` — delegates to the
    /// inner process if it reports one (Go's `processExitState` assertion
    /// through the wrapper chain).
    fn spawned_exit_code(&self) -> Option<i64> {
        self.inner.spawned_exit_code()
    }
}

// ---------------------------------------------------------------------------
// Timings
// ---------------------------------------------------------------------------

/// `type operationTiming struct` — atomic count + nanosecond duration.
#[derive(Default)]
struct OperationTimingCounter {
    count: AtomicU64,
    duration_nanos: AtomicI64,
}

impl OperationTimingCounter {
    /// `func (t *operationTiming) record(start)`
    fn record(&self, start: Instant) {
        self.count.fetch_add(1, Ordering::SeqCst);
        self.duration_nanos
            .fetch_add(start.elapsed().as_nanos() as i64, Ordering::SeqCst);
    }

    /// `func (t *operationTiming) snapshot`
    fn snapshot(&self) -> OperationTiming {
        OperationTiming {
            count: self.count.load(Ordering::SeqCst),
            duration: Duration::from_nanos(self.duration_nanos.load(Ordering::SeqCst).max(0) as u64),
        }
    }
}

/// `type timingCollector struct`
#[derive(Default)]
struct TimingCollector {
    state: Mutex<TimingCollectorState>,
}

#[derive(Default)]
struct TimingCollectorState {
    mappers: FxHashMap<String, Arc<MapperTimingCollector>>,
    active_requests: u64,
    request_wait_start: Option<Instant>,
    request_wait_elapsed: Duration,
}

/// `type mapperTimingCollector struct`
struct MapperTimingCollector {
    spawn: OperationTimingCounter,
    initialize: OperationTimingCounter,
    open_project: OperationTimingCounter,
    close_project: OperationTimingCounter,
    transform: OperationTimingCounter,
    /// `owner *timingCollector`
    owner: Weak<TimingCollector>,
}

impl TimingCollector {
    /// `func (t *timingCollector) mapper(identity)`
    fn mapper(self: &Arc<Self>, identity: &str) -> Arc<MapperTimingCollector> {
        let mut state = self.state.lock().unwrap();
        if let Some(timing) = state.mappers.get(identity) {
            return timing.clone();
        }
        let timing = Arc::new(MapperTimingCollector {
            spawn: OperationTimingCounter::default(),
            initialize: OperationTimingCounter::default(),
            open_project: OperationTimingCounter::default(),
            close_project: OperationTimingCounter::default(),
            transform: OperationTimingCounter::default(),
            owner: Arc::downgrade(self),
        });
        state.mappers.insert(identity.to_string(), timing.clone());
        timing
    }

    /// `func (t *timingCollector) snapshot`
    fn snapshot(&self) -> Timings {
        let (request_wait, mappers) = {
            let state = self.state.lock().unwrap();
            let mut request_wait = state.request_wait_elapsed;
            if state.active_requests != 0 {
                if let Some(start) = state.request_wait_start {
                    request_wait += start.elapsed();
                }
            }
            (request_wait, state.mappers.clone())
        };
        let mut result = Timings {
            mappers: FxHashMap::default(),
            request_wait,
        };
        result.mappers.reserve(mappers.len());
        for (identity, timing) in &mappers {
            result.mappers.insert(
                identity.clone(),
                MapperTimings {
                    spawn: timing.spawn.snapshot(),
                    initialize: timing.initialize.snapshot(),
                    open_project: timing.open_project.snapshot(),
                    close_project: timing.close_project.snapshot(),
                    transform: timing.transform.snapshot(),
                },
            );
        }
        result
    }
}

impl MapperTimingCollector {
    /// `func (t *mapperTimingCollector) startRequest`
    fn start_request(&self) -> Instant {
        if let Some(owner) = self.owner.upgrade() {
            let mut state = owner.state.lock().unwrap();
            if state.active_requests == 0 {
                state.request_wait_start = Some(Instant::now());
            }
            state.active_requests += 1;
        }
        Instant::now()
    }

    /// `func (t *mapperTimingCollector) finishRequest`
    fn finish_request(&self, operation: &OperationTimingCounter, start: Instant) {
        operation.record(start);
        if let Some(owner) = self.owner.upgrade() {
            let mut state = owner.state.lock().unwrap();
            state.active_requests -= 1;
            if state.active_requests == 0 {
                if let Some(started) = state.request_wait_start.take() {
                    state.request_wait_elapsed += started.elapsed();
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Host implementation
// ---------------------------------------------------------------------------

/// `dialFunc` — establishes a running connection to a mapper. In production
/// it spawns the mapper's process; tests substitute an in-memory connection.
type DialFn = Arc<
    dyn Fn(&Context, &Arc<Mapper>, &Locale) -> std::result::Result<DialOutcome, Error>
        + Send
        + Sync,
>;

/// The `dialFunc` result tuple — `(conn, closer, encoding, source)`.
struct DialOutcome {
    conn: Arc<dyn Conn>,
    closer: Arc<dyn IoClose>,
    position_encoding: PositionEncoding,
    diagnostic_source: String,
}

/// `type mapperConn struct` — one child process per mapper identity.
#[derive(Default)]
struct MapperConn {
    conn: Option<Arc<dyn Conn>>,
    closer: Option<Arc<dyn IoClose>>,
    /// `err`, when `Some`, records that this mapper failed to start; it is
    /// cached so we do not repeatedly try (and fail) to spawn a broken
    /// mapper.
    err: Option<Error>,
    position_encoding: PositionEncoding,
    diagnostic_source: String,
    /// `refs` is the number of active `Acquire` calls retaining this
    /// identity.
    refs: i64,
}

/// `type projectEntry struct`
struct ProjectEntry {
    mapper: Arc<Mapper>,
    spec: ProjectSpec,
    project_handle: String,
    opened: bool,
    config_identity: String,
    watched_files: Vec<RootedFilePath>,
    option_diagnostics: Vec<OptionDiagnostic>,
}

/// The `h.mu`-guarded state — `None` once the host is closed (Go's
/// `conns`/`projects`/`projectLeases == nil`).
struct HostMu {
    /// `diagnosticLocale` — written under `lifecycle_mu`'s write-lock
    /// (`SetLocale`), read under its read-lock, mirroring Go's guard
    /// discipline (the field itself lives here so `Option<HostMu>` captures
    /// all per-host state in one place).
    diagnostic_locale: Locale,
    conns: FxHashMap<String, MapperConn>,
    projects: FxHashMap<String, ProjectEntry>,
    project_leases: FxHashMap<String, Arc<ProjectLease>>,
    next_project_id: u64,
}

/// `type host struct` — manages one child process per mapper identity; the
/// production implementation of `Host`.
pub(crate) struct HostState {
    ctx: Context,
    cancel: CancelFunc,
    /// `stop func() bool` — the `context.AfterFunc` stop flag: `true` once
    /// close has started or been requested.
    stop: AtomicBool,
    dial: DialFn,
    timing: Arc<TimingCollector>,

    /// `lifecycleMu sync.RWMutex` — guards `diagnostic_locale` and makes
    /// `set_locale`/`close` wait for in-flight transforms.
    lifecycle_mu: RwLock<()>,

    /// `mu sync.Mutex` — `None` == host closed.
    mu: Mutex<Option<HostMu>>,
}

impl HostState {
    /// `func (h *host) Timings`
    fn timings(&self) -> Timings {
        self.timing.snapshot()
    }

    /// `func (h *host) SetLocale`
    fn set_locale(&self, diagnostic_locale: Locale) {
        let _lifecycle = self.lifecycle_mu.write().unwrap();
        let mut closers: Vec<Arc<dyn IoClose>> = Vec::new();
        {
            let mut mu = self.mu.lock().unwrap();
            let Some(state) = mu.as_mut() else {
                return;
            };
            if state.diagnostic_locale == diagnostic_locale {
                return;
            }
            state.diagnostic_locale = diagnostic_locale;
            for entry in state.conns.values_mut() {
                if let Some(closer) = entry.closer.take() {
                    closers.push(closer);
                }
                entry.conn = None;
                entry.err = None;
                entry.position_encoding = PositionEncoding::default();
                entry.diagnostic_source = String::new();
            }
            for project in state.projects.values_mut() {
                project.opened = false;
            }
        }
        for closer in closers {
            let _ = closer.close();
        }
    }

    /// `func (h *host) Project`
    fn project(self: &Arc<Self>, spec: &ProjectSpec) -> Option<Arc<dyn Project>> {
        let _lifecycle = self.lifecycle_mu.read().unwrap();
        let key = project_spec_key(spec);
        let mut mu = self.mu.lock().unwrap();
        let state = mu.as_mut()?;
        if let Some(lease) = state.project_leases.get(&key) {
            // `lease.retainLocked()` — a new handle on the same lease.
            lease.refs.fetch_add(1, Ordering::SeqCst);
            return Some(Arc::new(ProjectHandle {
                lease: lease.clone(),
                released: AtomicBool::new(false),
            }));
        }
        let mut entries: FxHashMap<usize, String> = FxHashMap::default();
        entries.reserve(spec.mappers.len());
        for mapper in &spec.mappers {
            let entry_key = format!("{}:{}", mapper.identity(), state.next_project_id);
            state.next_project_id += 1;
            state.projects.insert(
                entry_key.clone(),
                ProjectEntry {
                    mapper: mapper.clone(),
                    spec: spec.clone(),
                    project_handle: entry_key.clone(),
                    opened: false,
                    config_identity: String::new(),
                    watched_files: Vec::new(),
                    option_diagnostics: Vec::new(),
                },
            );
            state.conns.entry(mapper.identity()).or_default().refs += 1;
            entries.insert(Arc::as_ptr(mapper) as usize, entry_key);
        }
        let lease = Arc::new(ProjectLease {
            host: Arc::downgrade(self),
            key: key.clone(),
            mappers: spec.mappers.clone(),
            entries,
            refs: AtomicI64::new(1),
        });
        state.project_leases.insert(key, lease.clone());
        Some(Arc::new(ProjectHandle {
            lease,
            released: AtomicBool::new(false),
        }))
    }

    /// `func (h *host) Acquire` — retains the processes for the given mapper
    /// identities until the returned lease is released.
    fn acquire(self: &Arc<Self>, mappers: &[Arc<Mapper>]) -> AcquireLease {
        let mut seen: FxHashMap<String, ()> = FxHashMap::default();
        let mut identities: Vec<String> = Vec::with_capacity(mappers.len());
        {
            let mut mu = self.mu.lock().unwrap();
            if let Some(state) = mu.as_mut() {
                for mapper in mappers {
                    let identity = mapper.identity();
                    if seen.insert(identity.clone(), ()).is_some() {
                        continue;
                    }
                    identities.push(identity.clone());
                    state.conns.entry(identity).or_default().refs += 1;
                }
            }
        }
        AcquireLease {
            host: Arc::downgrade(self),
            identities,
            released: AtomicBool::new(false),
        }
    }

    /// `func (h *host) release`
    fn release(&self, identities: &[String]) {
        let mut closers: Vec<Arc<dyn IoClose>> = Vec::new();
        {
            let mut mu = self.mu.lock().unwrap();
            if let Some(state) = mu.as_mut() {
                for identity in identities {
                    let Some(entry) = state.conns.get_mut(identity) else {
                        continue;
                    };
                    entry.refs -= 1;
                    if entry.refs == 0 {
                        if let Some(closer) = entry.closer.take() {
                            closers.push(closer);
                        }
                        state.conns.remove(identity);
                    }
                }
            }
        }
        for closer in closers {
            let _ = closer.close();
        }
    }

    /// `func (h *host) transformLocked`
    fn transform_locked(
        self: &Arc<Self>,
        mapper: &Arc<Mapper>,
        request: &Request,
        project_handle: &str,
    ) -> std::result::Result<Result, Error> {
        if project_handle.is_empty() {
            return Err(Error::message("content mapper project handle is required"));
        }
        let (conn, position_encoding, diagnostic_source) = self
            .conn_for(mapper)
            .map_err(|e| Error::transform(TransformErrorKind::Initialize, e))?;
        let mapper_timing = self.timing.mapper(&mapper.identity());
        let start = mapper_timing.start_request();
        // Go marshals the params inside `conn.Call`, so a marshal failure is
        // a `TransformErrorKindRequest` like a call failure.
        let params = ipc::marshal_params(&TransformParams {
            file_name: request.file_name.as_string().to_string(),
            content: request.content.clone(),
            project_handle: project_handle.to_string(),
        })
        .map_err(|e| Error::transform(TransformErrorKind::Request, Error::Ipc(e)))?;
        let raw = conn.call(&self.ctx, METHOD_TRANSFORM, Some(params));
        mapper_timing.finish_request(&mapper_timing.transform, start);
        let raw = raw.map_err(|e| Error::transform(TransformErrorKind::Request, Error::Ipc(e)))?;
        decode_transform_result(
            raw,
            &request.content,
            &position_encoding,
            &diagnostic_source,
        )
        .map_err(|e| Error::transform(TransformErrorKind::Response, e))
    }

    /// `func (h *host) connFor` — returns the connection for a mapper's
    /// identity, spawning its process on first use. Mappers sharing an
    /// identity share a single process.
    fn conn_for(
        &self,
        mapper: &Arc<Mapper>,
    ) -> std::result::Result<(Arc<dyn Conn>, PositionEncoding, String), Error> {
        let mut mu = self.mu.lock().unwrap();
        let Some(state) = mu.as_mut() else {
            return Err(Error::message("content mapper host is closed"));
        };
        // `connForLocked` — dials while holding `h.mu`, as in Go.
        let identity = mapper.identity();
        let entry = state.conns.entry(identity.clone()).or_default();
        if entry.conn.is_none() && entry.err.is_none() {
            let locale = state.diagnostic_locale.clone();
            match (self.dial)(&self.ctx, mapper, &locale) {
                Ok(outcome) => {
                    let entry = state.conns.entry(identity.clone()).or_default();
                    entry.conn = Some(outcome.conn.clone());
                    entry.closer = Some(outcome.closer.clone());
                    entry.position_encoding = outcome.position_encoding.clone();
                    entry.diagnostic_source = outcome.diagnostic_source.clone();
                }
                Err(e) => {
                    state.conns.entry(identity.clone()).or_default().err = Some(e.clone());
                    return Err(e);
                }
            }
        }
        let entry = state.conns.get(&identity).unwrap();
        if let Some(e) = &entry.err {
            return Err(e.clone());
        }
        Ok((
            entry.conn.clone().unwrap(),
            entry.position_encoding.clone(),
            entry.diagnostic_source.clone(),
        ))
    }

    /// The `h.mu`-held half of `connFor` for callers that already hold the
    /// lock — Go's `connForLocked` (call sites use `state` pieces directly
    /// so `entry`/`conns` borrows don't collide).
    #[allow(clippy::too_many_arguments)]
    fn conn_for_locked(
        &self,
        conns: &mut FxHashMap<String, MapperConn>,
        diagnostic_locale: &Locale,
        mapper: &Arc<Mapper>,
    ) -> std::result::Result<(Arc<dyn Conn>, PositionEncoding, String), Error> {
        let identity = mapper.identity();
        let entry = conns.entry(identity.clone()).or_default();
        if entry.conn.is_none() && entry.err.is_none() {
            match (self.dial)(&self.ctx, mapper, diagnostic_locale) {
                Ok(outcome) => {
                    let entry = conns.entry(identity.clone()).or_default();
                    entry.conn = Some(outcome.conn.clone());
                    entry.closer = Some(outcome.closer.clone());
                    entry.position_encoding = outcome.position_encoding.clone();
                    entry.diagnostic_source = outcome.diagnostic_source.clone();
                }
                Err(e) => {
                    conns.entry(identity.clone()).or_default().err = Some(e.clone());
                    return Err(e);
                }
            }
        }
        let entry = conns.get(&identity).unwrap();
        if let Some(e) = &entry.err {
            return Err(e.clone());
        }
        Ok((
            entry.conn.clone().unwrap(),
            entry.position_encoding.clone(),
            entry.diagnostic_source.clone(),
        ))
    }

    /// `func (h *host) openProjectLocked` — `h.mu` is held by the caller
    /// (`state` is the guard contents). Takes the `projects` key rather
    /// than the entry so the `state.projects` borrow and the `state.conns`
    /// dial borrow don't collide (Go passes the entry under `h.mu`).
    fn open_project_locked(&self, state: &mut HostMu, key: &str) -> std::result::Result<(), Error> {
        let Some(entry) = state.projects.get_mut(key) else {
            return Ok(());
        };
        if entry.opened {
            return Ok(());
        }
        let (conn, _position_encoding, diagnostic_source) =
            self.conn_for_locked(&mut state.conns, &state.diagnostic_locale, &entry.mapper)?;
        let compiler_options = match &entry.spec.compiler_options {
            Some(options) => json::marshal(options.as_ref(), &[]).map_err(into_json_error)?,
            // `json.Marshal((*CompilerOptions)(nil))` → `null`.
            None => b"null".to_vec(),
        };
        let compiler_options = serde_json::value::RawValue::from_string(
            String::from_utf8_lossy(&compiler_options).into_owned(),
        )
        .map_err(into_json_error)?;
        let mapper_identity = entry.mapper.identity();
        let mapper_timing = self.timing.mapper(&mapper_identity);
        let start = mapper_timing.start_request();
        let raw = conn.call(
            &self.ctx,
            METHOD_OPEN_PROJECT,
            Some(
                ipc::marshal_params(&OpenProjectParams {
                    config_file_name: entry.spec.config_file_name.as_string().to_string(),
                    project_handle: entry.project_handle.clone(),
                    options: entry.mapper.options.clone(),
                    compiler_options,
                })
                .map_err(Error::Ipc)?,
            ),
        );
        mapper_timing.finish_request(&mapper_timing.open_project, start);
        let raw = raw.map_err(Error::Ipc)?;
        let result: OpenProjectResult =
            json::unmarshal(raw.as_ref().map_or(&b""[..], |v| v.get().as_bytes()), &[]).map_err(
                |_| {
                    Error::Project(ProjectError {
                        kind: ProjectErrorKind::MalformedResponse,
                    })
                },
            )?;
        if entry.mapper.dynamic_config && result.config_identity.is_empty() {
            return Err(Error::Project(ProjectError {
                kind: ProjectErrorKind::MissingConfigIdentity,
            }));
        }
        if !entry.mapper.dynamic_config && !result.config_identity.is_empty() {
            return Err(Error::Project(ProjectError {
                kind: ProjectErrorKind::UnexpectedConfigIdentity,
            }));
        }
        if !entry.mapper.dynamic_config && result.watched_files.as_ref().map_or(0, Vec::len) != 0 {
            return Err(Error::Project(ProjectError {
                kind: ProjectErrorKind::UnexpectedWatchedFiles,
            }));
        }
        entry.config_identity = result.config_identity;
        entry.watched_files = Vec::with_capacity(result.watched_files.as_ref().map_or(0, Vec::len));
        for file_name in result.watched_files.as_deref().unwrap_or(&[]) {
            let Some(typed_file_name) = tspath::try_rooted_file_path_from_absolute(file_name)
            else {
                return Err(Error::Project(ProjectError {
                    kind: ProjectErrorKind::NonAbsoluteWatchedFile,
                }));
            };
            entry.watched_files.push(typed_file_name);
        }
        entry.option_diagnostics =
            Vec::with_capacity(result.option_diagnostics.as_ref().map_or(0, Vec::len));
        for diagnostic in result.option_diagnostics.as_deref().unwrap_or(&[]) {
            let mut path = Vec::with_capacity(diagnostic.path.len());
            for raw_segment in &diagnostic.path {
                // `rawSegment.Kind()` — Go's jsontext reports a token's
                // kind byte: '"' for strings, '0' for every number.
                match raw_segment.get().as_bytes().first().copied().unwrap_or(0) {
                    b'"' => {
                        let property: String = json::unmarshal(raw_segment.get().as_bytes(), &[])
                            .map_err(|_| {
                            Error::Project(ProjectError {
                                kind: ProjectErrorKind::MalformedResponse,
                            })
                        })?;
                        path.push(OptionPathSegment {
                            property,
                            index: 0,
                            is_index: false,
                        });
                    }
                    b'0'..=b'9' | b'-' => {
                        let index: i64 = json::unmarshal(raw_segment.get().as_bytes(), &[])
                            .map_err(|_| {
                                Error::Project(ProjectError {
                                    kind: ProjectErrorKind::MalformedResponse,
                                })
                            })?;
                        if index < 0 {
                            return Err(Error::Project(ProjectError {
                                kind: ProjectErrorKind::MalformedResponse,
                            }));
                        }
                        path.push(OptionPathSegment {
                            property: String::new(),
                            index,
                            is_index: true,
                        });
                    }
                    _ => {
                        return Err(Error::Project(ProjectError {
                            kind: ProjectErrorKind::MalformedResponse,
                        }));
                    }
                }
            }
            entry.option_diagnostics.push(OptionDiagnostic {
                mapper: entry.mapper.clone(),
                path,
                source: diagnostic_source.clone(),
                code: diagnostic.code,
                message_text: diagnostic.message_text.clone(),
            });
        }
        entry.opened = true;
        Ok(())
    }

    /// `func (h *host) closeProject`
    fn close_project(
        &self,
        mapper: &Arc<Mapper>,
        conn: &Arc<dyn Conn>,
        project_handle: &str,
    ) -> std::result::Result<(), Error> {
        let mapper_timing = self.timing.mapper(&mapper.identity());
        let start = mapper_timing.start_request();
        let result = conn.call(
            &self.ctx,
            METHOD_CLOSE_PROJECT,
            Some(
                ipc::marshal_params(&CloseProjectParams {
                    project_handle: project_handle.to_string(),
                })
                .map_err(Error::Ipc)?,
            ),
        );
        mapper_timing.finish_request(&mapper_timing.close_project, start);
        result.map_err(Error::Ipc)?;
        Ok(())
    }

    /// `func (h *host) Close` — shuts down every mapper process. Safe to
    /// call more than once and invoked automatically when the context passed
    /// to `new_host` is cancelled.
    fn close_inner(&self) -> std::result::Result<(), Error> {
        let _lifecycle = self.lifecycle_mu.write().unwrap();
        // `h.stop()` — prevent the ctx-cancel callback from re-entering.
        self.stop.store(true, Ordering::SeqCst);
        self.cancel.cancel();
        let closers = {
            let mut mu = self.mu.lock().unwrap();
            match mu.take() {
                Some(state) => state
                    .conns
                    .into_values()
                    .filter_map(|entry| entry.closer)
                    .collect::<Vec<_>>(),
                None => Vec::new(),
            }
        };
        let mut result: Option<Error> = None;
        for closer in closers {
            if let Err(e) = closer.close() {
                result = Error::joined(result, Some(Error::Io(Arc::new(e))));
            }
        }
        match result {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }
}

fn into_json_error(e: serde_json::Error) -> Error {
    Error::Json(Arc::new(e))
}

/// `func projectSpecKey(spec ProjectSpec) string` — `%p` fields become the
/// `Arc` data pointers (`{:p}` formatting of `Arc::as_ptr`; `None` prints
/// `0x0`, like Go's `%p` on a nil pointer).
fn project_spec_key(spec: &ProjectSpec) -> String {
    let mut key = String::new();
    key.push_str(spec.config_file_name.as_string());
    key.push('\0');
    let options_ptr = spec
        .compiler_options
        .as_ref()
        .map_or(std::ptr::null::<CompilerOptions>(), Arc::as_ptr);
    key.push_str(&format!("{options_ptr:p}"));
    for mapper in &spec.mappers {
        key.push('\0');
        key.push_str(&format!("{:p}", Arc::as_ptr(mapper)));
    }
    key
}

/// `func combinedIdentity(mapper, configIdentity, compilerOptions) string`
fn combined_identity(
    mapper: &Arc<Mapper>,
    config_identity: &str,
    compiler_options: Option<&CompilerOptions>,
) -> String {
    let transform_identity = mapper.transform_identity(compiler_options).bytes();
    let identity = mapper.identity();
    let mut buf = Vec::with_capacity(
        identity.len()
            + mapper.options.as_ref().map_or(0, |v| v.get().len())
            + config_identity.len()
            + transform_identity.len()
            + 3,
    );
    buf.extend(identity.as_bytes());
    buf.push(0);
    if let Some(options) = &mapper.options {
        buf.extend(options.get().as_bytes());
    }
    buf.push(0);
    buf.extend(config_identity.as_bytes());
    buf.push(0);
    buf.extend(transform_identity);
    let hash = xxh3::hash_128(&buf).bytes();
    format!("{}:{}", identity, hex_encode(&hash))
}

/// `hex.EncodeToString` (lowercase).
fn hex_encode(data: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(data.len() * 2);
    for &b in data {
        out.push(HEX[(b >> 4) as usize] as char);
        out.push(HEX[(b & 0xf) as usize] as char);
    }
    out
}

// ---------------------------------------------------------------------------
// projectLease / ProjectHandle / AcquireLease
// ---------------------------------------------------------------------------

/// `type projectLease struct`
pub(crate) struct ProjectLease {
    host: Weak<HostState>,
    key: String,
    mappers: Vec<Arc<Mapper>>,
    /// `entries map[*Mapper]string` — keyed by `Arc` data pointer, like Go's
    /// `*Mapper` map keys.
    entries: FxHashMap<usize, String>,
    /// `refs int` — accessed under `host.mu` only; `AtomicI64` mirrors the
    /// lock-guarded increment/decrement.
    refs: AtomicI64,
}

/// `type retainedProject struct` — a retained handle on a `projectLease`;
/// `released` is the Go `sync.Once` on `Close`.
struct ProjectHandle {
    lease: Arc<ProjectLease>,
    released: AtomicBool,
}

impl ProjectLease {
    /// `p.host` — a dead `Weak` means the host was dropped; methods behave
    /// as they do on a closed host (`projects == nil` paths).
    fn host(&self) -> Option<Arc<HostState>> {
        self.host.upgrade()
    }

    /// `func (p *projectLease) Refresh`
    fn refresh(&self) -> std::result::Result<(), Error> {
        let Some(host) = self.host() else {
            return Ok(());
        };
        let _lifecycle = host.lifecycle_mu.read().unwrap();
        let mut mu = host.mu.lock().unwrap();
        let Some(state) = mu.as_mut() else {
            return Ok(());
        };
        let mut result: Option<Error> = None;
        for key in self.entries.values() {
            let entry = match state.projects.get_mut(key) {
                Some(entry) if entry.opened => entry,
                _ => continue,
            };
            if let Some(conn_entry) = state.conns.get(&entry.mapper.identity()) {
                if let Some(conn) = conn_entry.conn.clone() {
                    let mapper = entry.mapper.clone();
                    let handle = entry.project_handle.clone();
                    result =
                        Error::joined(result, host.close_project(&mapper, &conn, &handle).err());
                }
            }
            entry.opened = false;
        }
        match result {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }

    /// `func (p *projectLease) Identities`
    fn identities(&self) -> std::result::Result<Vec<String>, Error> {
        let Some(host) = self.host() else {
            return Ok(Vec::new());
        };
        let _lifecycle = host.lifecycle_mu.read().unwrap();
        let mut mu = host.mu.lock().unwrap();
        let Some(state) = mu.as_mut() else {
            return Ok(Vec::new());
        };
        let mut identities = Vec::with_capacity(self.entries.len());
        for mapper in &self.mappers {
            let Some(key) = self.entries.get(&(Arc::as_ptr(mapper) as usize)) else {
                continue;
            };
            if !state.projects.contains_key(key) {
                continue;
            }
            if mapper.dynamic_config {
                host.open_project_locked(state, key)?;
                let entry = &state.projects[key];
                identities.push(combined_identity(
                    mapper,
                    &entry.config_identity,
                    entry.spec.compiler_options.as_deref(),
                ));
            } else {
                let entry = &state.projects[key];
                let hash = mapper
                    .transform_identity(entry.spec.compiler_options.as_deref())
                    .bytes();
                identities.push(format!("{}:{}", mapper.identity(), hex_encode(&hash)));
            }
        }
        Ok(identities)
    }

    /// `func (p *projectLease) Identity`
    fn identity(&self, mapper: &Arc<Mapper>) -> std::result::Result<String, Error> {
        let Some(host) = self.host() else {
            return Ok(String::new());
        };
        let _lifecycle = host.lifecycle_mu.read().unwrap();
        let mut mu = host.mu.lock().unwrap();
        let Some(state) = mu.as_mut() else {
            return Ok(String::new());
        };
        let Some(key) = self.entries.get(&(Arc::as_ptr(mapper) as usize)) else {
            return Ok(String::new());
        };
        if !state.projects.contains_key(key) {
            return Ok(String::new());
        }
        if mapper.dynamic_config {
            host.open_project_locked(state, key)?;
            let entry = &state.projects[key];
            return Ok(combined_identity(
                mapper,
                &entry.config_identity,
                entry.spec.compiler_options.as_deref(),
            ));
        }
        let entry = &state.projects[key];
        let hash = mapper
            .transform_identity(entry.spec.compiler_options.as_deref())
            .bytes();
        Ok(format!("{}:{}", mapper.identity(), hex_encode(&hash)))
    }

    /// `func (p *projectLease) WatchedFiles`
    fn watched_files(&self) -> std::result::Result<Vec<RootedFilePath>, Error> {
        let Some(host) = self.host() else {
            return Ok(Vec::new());
        };
        let _lifecycle = host.lifecycle_mu.read().unwrap();
        let mut mu = host.mu.lock().unwrap();
        let Some(state) = mu.as_mut() else {
            return Ok(Vec::new());
        };
        let mut files: Vec<RootedFilePath> = Vec::new();
        for key in self.entries.values() {
            let Some(entry) = state.projects.get(key) else {
                continue;
            };
            if entry.mapper.dynamic_config {
                host.open_project_locked(state, key)?;
            }
            files.extend(state.projects[key].watched_files.iter().cloned());
        }
        // `slices.Sort` + `slices.Compact` (consecutive-dup removal).
        files.sort();
        files.dedup();
        Ok(files)
    }

    /// `func (p *projectLease) Diagnostics`
    fn diagnostics(&self) -> Vec<OptionDiagnostic> {
        let Some(host) = self.host() else {
            return Vec::new();
        };
        let _lifecycle = host.lifecycle_mu.read().unwrap();
        let mut mu = host.mu.lock().unwrap();
        let Some(state) = mu.as_mut() else {
            return Vec::new();
        };
        let mut diagnostics: Vec<OptionDiagnostic> = Vec::new();
        for mapper in &self.mappers {
            let Some(key) = self.entries.get(&(Arc::as_ptr(mapper) as usize)) else {
                continue;
            };
            let Some(entry) = state.projects.get_mut(key) else {
                continue;
            };
            if !entry.opened {
                continue;
            }
            diagnostics.extend(entry.option_diagnostics.iter().cloned());
        }
        diagnostics
    }

    /// `func (p *projectLease) Transform`
    fn transform(
        &self,
        mapper: &Arc<Mapper>,
        request: &Request,
    ) -> std::result::Result<Result, Error> {
        let Some(host) = self.host() else {
            return Err(Error::message("content mapper project is closed"));
        };
        // `lifecycleMu.RLock` is held for the whole method — `SetLocale`
        // waits for in-flight transforms.
        let _lifecycle = host.lifecycle_mu.read().unwrap();
        let handle = {
            let mut mu = host.mu.lock().unwrap();
            let Some(state) = mu.as_mut() else {
                return Err(Error::message("content mapper project is closed"));
            };
            let Some(key) = self
                .entries
                .get(&(Arc::as_ptr(mapper) as usize))
                .filter(|key| state.projects.contains_key(*key))
                .cloned()
            else {
                return Err(Error::message("content mapper project is closed"));
            };
            match host.open_project_locked(state, &key) {
                Err(e) => {
                    drop(mu);
                    if e.as_initialize_error().is_some() {
                        return Err(Error::transform(TransformErrorKind::Initialize, e));
                    }
                    return Err(Error::transform(TransformErrorKind::Project, e));
                }
                Ok(()) => state.projects[&key].project_handle.clone(),
            }
        };
        host.transform_locked(mapper, request, &handle)
    }

    /// `func (p *projectLease) release` — `self` is an `Arc` for the
    /// `projectLeases[key] == p` identity check.
    fn release(self: &Arc<Self>) -> std::result::Result<(), Error> {
        let mut result: Option<Error> = None;
        {
            let Some(host) = self.host() else {
                return Ok(());
            };
            let _lifecycle = host.lifecycle_mu.read().unwrap();
            let mut released_identities: Vec<String> = Vec::new();
            {
                let mut mu = host.mu.lock().unwrap();
                let refs = self.refs.fetch_sub(1, Ordering::SeqCst) - 1;
                if refs < 0 {
                    panic!("content mapper project reference count below zero");
                }
                if refs != 0 {
                    return Ok(());
                }
                if let Some(state) = mu.as_mut() {
                    if state
                        .project_leases
                        .get(&self.key)
                        .is_some_and(|l| Arc::ptr_eq(l, self))
                    {
                        state.project_leases.remove(&self.key);
                    }
                    for key in self.entries.values() {
                        let Some(entry) = state.projects.remove(key) else {
                            continue;
                        };
                        if entry.opened {
                            if let Some(conn_entry) = state.conns.get(&entry.mapper.identity())
                                && let Some(conn) = conn_entry.conn.clone()
                            {
                                result = Error::joined(
                                    result,
                                    host.close_project(&entry.mapper, &conn, &entry.project_handle)
                                        .err(),
                                );
                            }
                        }
                        released_identities.push(entry.mapper.identity());
                    }
                }
            }
            host.release(&released_identities);
        }
        match result {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }
}

impl Project for ProjectHandle {
    /// `Refresh()`
    fn refresh(&self) -> std::result::Result<(), Error> {
        self.lease.refresh()
    }

    /// `Identities()`
    fn identities(&self) -> std::result::Result<Vec<String>, Error> {
        self.lease.identities()
    }

    /// `Identity(mapper)`
    fn identity(&self, mapper: &Arc<Mapper>) -> std::result::Result<String, Error> {
        self.lease.identity(mapper)
    }

    /// `WatchedFiles()`
    fn watched_files(&self) -> std::result::Result<Vec<RootedFilePath>, Error> {
        self.lease.watched_files()
    }

    /// `Diagnostics()`
    fn diagnostics(&self) -> Vec<OptionDiagnostic> {
        self.lease.diagnostics()
    }

    /// `Transform(mapper, request)`
    fn transform(
        &self,
        mapper: &Arc<Mapper>,
        request: &Request,
    ) -> std::result::Result<Result, Error> {
        self.lease.transform(mapper, request)
    }

    /// `func (p *retainedProject) Close` — `released` is Go's `sync.Once`:
    /// `release` runs at most once per handle.
    fn close(&self) -> std::result::Result<(), Error> {
        if self.released.swap(true, Ordering::SeqCst) {
            return Ok(());
        }
        self.lease.release()
    }
}

impl Drop for ProjectHandle {
    /// Go callers `defer project.Close()`; a dropped handle releases like a
    /// `Close` observed at scope end.
    fn drop(&mut self) {
        let _ = self.close();
    }
}

/// The `sync.OnceFunc` returned by `Acquire` — `release` runs at most once;
/// `Drop` releases like a Go `defer release()`.
pub struct AcquireLease {
    host: Weak<HostState>,
    identities: Vec<String>,
    released: AtomicBool,
}

impl AcquireLease {
    /// The release function — `func() { h.release(identities) }`.
    pub fn release(&self) {
        if self.released.swap(true, Ordering::SeqCst) {
            return;
        }
        if let Some(host) = self.host.upgrade() {
            host.release(&self.identities);
        }
    }
}

impl Drop for AcquireLease {
    fn drop(&mut self) {
        self.release();
    }
}

// ---------------------------------------------------------------------------
// Host constructors and the production dial
// ---------------------------------------------------------------------------

/// `func NewHost(ctx, spawner, diagnosticLocale) Host` — creates a Host that
/// spawns each mapper's process via the given spawner and drives it over a
/// JSON-RPC connection. The host's lifetime is bound to `ctx`: cancelling it
/// tears every mapper process down. `close` does the same synchronously.
pub fn new_host(
    ctx: &Context,
    spawner: Arc<dyn Spawner>,
    diagnostic_locale: Locale,
) -> Arc<dyn Host> {
    new_host_with_options(ctx, spawner, diagnostic_locale, HostOptions::default())
}

/// `func NewHostWithOptions(ctx, spawner, diagnosticLocale, options) Host`
pub fn new_host_with_options(
    ctx: &Context,
    spawner: Arc<dyn Spawner>,
    diagnostic_locale: Locale,
    options: HostOptions,
) -> Arc<dyn Host> {
    let logger = options.logger;
    let timing = Arc::new(TimingCollector::default());
    let dial = new_production_dial(spawner, timing.clone(), logger);
    let state = new_with_dial(ctx, diagnostic_locale, timing, dial);
    Arc::new(HostImpl { state })
}

/// `func newWithDial(ctx, diagnosticLocale, timing, dial) *host`
fn new_with_dial(
    ctx: &Context,
    diagnostic_locale: Locale,
    timing: Arc<TimingCollector>,
    dial: DialFn,
) -> Arc<HostState> {
    let (host_ctx, cancel) = ctx.with_cancel();
    let state = Arc::new(HostState {
        ctx: host_ctx,
        cancel,
        stop: AtomicBool::new(false),
        dial,
        timing,
        lifecycle_mu: RwLock::new(()),
        mu: Mutex::new(Some(HostMu {
            diagnostic_locale,
            conns: FxHashMap::default(),
            projects: FxHashMap::default(),
            project_leases: FxHashMap::default(),
            next_project_id: 0,
        })),
    });
    // `h.stop = context.AfterFunc(ctx, func() { _ = h.Close() })`
    let weak = Arc::downgrade(&state);
    let watcher_ctx = ctx.clone();
    thread::spawn(move || {
        watcher_ctx.wait_cancelled();
        if let Some(state) = weak.upgrade() {
            if state.stop.swap(true, Ordering::SeqCst) {
                return;
            }
            let _ = state.close_inner();
        }
    });
    state
}

/// The `dialFunc` closure inside `NewHostWithOptions` — spawns the mapper,
/// wires up the JSON-RPC protocol, runs the connection loop, and performs
/// the initialize handshake under a 5-second deadline.
fn new_production_dial(
    spawner: Arc<dyn Spawner>,
    timing: Arc<TimingCollector>,
    logger: Option<Logger>,
) -> DialFn {
    Arc::new(
        move |ctx: &Context, mapper: &Arc<Mapper>, diagnostic_locale: &Locale| {
            let exec = mapper.exec.as_deref().unwrap_or(&[]);
            if exec.is_empty() {
                return Err(Error::message(format!(
                    "content mapper {:?} declares no command to run",
                    mapper.package
                )));
            }
            let mapper_timing = timing.mapper(&mapper.identity());
            let diagnostic_name = mapper.diagnostic_name();
            let spawn_start = Instant::now();
            let stderr_log = logger
                .as_ref()
                .map(|l| StderrLogger::new(diagnostic_name.clone(), l.clone()));
            let stderr: Option<Box<dyn io::Write + Send>> = stderr_log
                .as_ref()
                .map(|l| Box::new(StderrLoggerWriter(l.clone())) as Box<dyn io::Write + Send>);
            let spawned = match spawner.spawn(exec, mapper.package_directory.as_string(), stderr) {
                Ok(spawned) => spawned,
                Err(e) => {
                    mapper_timing.spawn.record(spawn_start);
                    return Err(Error::Initialize(InitializeError {
                        kind: InitializeErrorKind::ProcessStart,
                        mapper_name: diagnostic_name,
                        command: exec[0].clone(),
                        detail: e.to_string(),
                        ..Default::default()
                    }));
                }
            };
            mapper_timing.spawn.record(spawn_start);
            let mut rwc: Arc<dyn SpawnedProcess> = spawned;
            if let Some(stderr_log) = stderr_log {
                rwc = Arc::new(LoggedProcess {
                    inner: rwc,
                    stderr: stderr_log,
                });
            }
            let rwc: Arc<dyn SpawnedProcess> = Arc::new(CloseOnce {
                inner: rwc,
                state: Mutex::new(CloseOnceState::default()),
            });
            let io = Arc::new(ProcessIo(rwc.clone()));
            let json_protocol: Arc<dyn Protocol> = Arc::new(ipc::new_json_rpc_protocol(io.clone()));
            let protocol: Arc<dyn Protocol> = match &logger {
                Some(l) => Arc::new(LoggingProtocol {
                    inner: json_protocol,
                    mapper_name: diagnostic_name.clone(),
                    logger: l.clone(),
                }),
                None => json_protocol,
            };
            let conn: Arc<dyn Conn> = Arc::new(ipc::AsyncConn::new_async_conn_with_protocol(
                Some(io.clone() as Arc<dyn IoClose>),
                protocol,
                Arc::new(RejectHandler),
            ));
            {
                let conn = conn.clone();
                let io = io.clone();
                let run_ctx = ctx.clone();
                thread::spawn(move || {
                    let _ = conn.run(&run_ctx);
                    let _ = io.close();
                });
            }
            // `context.WithTimeout(ctx, initializeTimeout)` — a child ctx
            // cancelled by a timer thread after 5 seconds.
            let (initialize_ctx, initialize_cancel) = ctx.with_cancel();
            let initialize_cancel = Arc::new(initialize_cancel);
            {
                let cancel = initialize_cancel.clone();
                thread::spawn(move || {
                    thread::sleep(INITIALIZE_TIMEOUT);
                    cancel.cancel();
                });
            }
            let initialize_start = mapper_timing.start_request();
            let handshake_result = handshake(&initialize_ctx, conn.as_ref(), diagnostic_locale);
            mapper_timing.finish_request(&mapper_timing.initialize, initialize_start);
            // `initializeCtxErr := initializeCtx.Err()` — read BEFORE `cancel()`.
            let initialize_ctx_err = initialize_ctx.is_cancelled();
            initialize_cancel.cancel();
            match handshake_result {
                Err(err) => {
                    let (exit_code, exited) = match rwc.spawned_exit_code() {
                        Some(code) => (code, true),
                        None => (0, false),
                    };
                    let _ = rwc.spawned_close();
                    if let Error::Initialize(mut initialize_error) = err {
                        initialize_error.mapper_name = diagnostic_name;
                        return Err(Error::Initialize(initialize_error));
                    }
                    if exited {
                        return Err(Error::Initialize(InitializeError {
                            kind: InitializeErrorKind::ProcessExit,
                            mapper_name: diagnostic_name,
                            exit_code,
                            ..Default::default()
                        }));
                    }
                    if initialize_ctx_err || err.is_context_canceled() {
                        return Err(Error::Initialize(InitializeError {
                            kind: InitializeErrorKind::NoResponse,
                            mapper_name: diagnostic_name,
                            timeout_seconds: INITIALIZE_TIMEOUT_SECONDS,
                            ..Default::default()
                        }));
                    }
                    Err(Error::Initialize(InitializeError {
                        kind: InitializeErrorKind::Request,
                        mapper_name: diagnostic_name,
                        detail: err.to_string(),
                        ..Default::default()
                    }))
                }
                Ok((position_encoding, diagnostic_source)) => Ok(DialOutcome {
                    conn,
                    closer: io as Arc<dyn IoClose>,
                    position_encoding,
                    diagnostic_source,
                }),
            }
        },
    )
}

/// `type host struct` exposed through `Arc<dyn Host>` — `Drop` is the Rust
/// analogue of ctx-cancel teardown for a host whose owner lets go without
/// closing it.
pub(crate) struct HostImpl {
    state: Arc<HostState>,
}

impl Drop for HostImpl {
    fn drop(&mut self) {
        let _ = self.state.close_inner();
    }
}

impl Host for HostImpl {
    /// `Timings()`
    fn timings(&self) -> Timings {
        self.state.timings()
    }

    /// `Project(spec)` — `None` is Go's nil return on a closed host.
    fn project(&self, spec: &ProjectSpec) -> Option<Arc<dyn Project>> {
        self.state.project(spec)
    }

    /// `Acquire(mappers)`
    fn acquire(&self, mappers: &[Arc<Mapper>]) -> AcquireLease {
        self.state.acquire(mappers)
    }

    /// `SetLocale(locale)`
    fn set_locale(&self, locale: Locale) {
        self.state.set_locale(locale);
    }

    /// `Transform(mapper, request)` — uses a short-lived project with
    /// default compiler options, as in Go.
    fn transform(
        &self,
        mapper: &Arc<Mapper>,
        request: &Request,
    ) -> std::result::Result<Result, Error> {
        let Some(project) = self.project(&ProjectSpec {
            config_file_name: RootedFilePath::default(),
            mappers: vec![mapper.clone()],
            compiler_options: Some(Arc::new(CompilerOptions::default())),
        }) else {
            // PORT: Go returns a nil Project from a closed host and then
            // nil-dereferences it; report the closed state instead.
            return Err(Error::message("content mapper project is closed"));
        };
        // `defer project.Close()` — the close error is discarded as in Go.
        let result = project.transform(mapper, request);
        let _ = project.close();
        result
    }

    /// `Close()`
    fn close(&self) -> std::result::Result<(), Error> {
        self.state.close_inner()
    }
}

// ---------------------------------------------------------------------------
// Handshake and transform-result decoding
// ---------------------------------------------------------------------------

/// `func handshake(ctx, conn, diagnosticLocale)` — sends the initialize
/// request and validates the response.
fn handshake(
    ctx: &Context,
    conn: &dyn Conn,
    diagnostic_locale: &Locale,
) -> std::result::Result<(PositionEncoding, String), Error> {
    let raw = conn
        .call(
            ctx,
            METHOD_INITIALIZE,
            Some(
                ipc::marshal_params(&InitializeParams {
                    locale: diagnostic_locale.to_string(),
                    position_encodings: vec![PositionEncoding::UTF8, PositionEncoding::UTF16],
                })
                .map_err(Error::Ipc)?,
            ),
        )
        .map_err(Error::Ipc)?;
    let res: InitializeResult =
        json::unmarshal(raw.as_ref().map_or(&b""[..], |v| v.get().as_bytes()), &[]).map_err(
            |e| {
                Error::Initialize(InitializeError {
                    kind: InitializeErrorKind::InvalidResponse,
                    detail: e.to_string(),
                    ..Default::default()
                })
            },
        )?;
    if res.position_encoding != PositionEncoding::UTF8
        && res.position_encoding != PositionEncoding::UTF16
    {
        return Err(Error::Initialize(InitializeError {
            kind: InitializeErrorKind::PositionEncoding,
            position_encoding: res.position_encoding,
            ..Default::default()
        }));
    }
    if res.diagnostic_source.trim().is_empty() {
        return Err(Error::Initialize(InitializeError {
            kind: InitializeErrorKind::EmptyDiagnosticSource,
            ..Default::default()
        }));
    }
    if res.diagnostic_source.eq_ignore_ascii_case("typescript")
        || res.diagnostic_source.eq_ignore_ascii_case("tsc")
    {
        return Err(Error::Initialize(InitializeError {
            kind: InitializeErrorKind::ReservedDiagnosticSource,
            diagnostic_source: res.diagnostic_source,
            ..Default::default()
        }));
    }
    // `core.Flatten(tspath.AllSupportedExtensionsWithJson)`
    let native_extensions: Vec<&str> = tspath::ALL_SUPPORTED_EXTENSIONS_WITH_JSON
        .iter()
        .flat_map(|group| group.iter().copied())
        .collect();
    if native_extensions.iter().any(|extension| {
        res.diagnostic_source
            .eq_ignore_ascii_case(extension.strip_prefix('.').unwrap_or(extension))
    }) {
        return Err(Error::Initialize(InitializeError {
            kind: InitializeErrorKind::ReservedDiagnosticSource,
            diagnostic_source: res.diagnostic_source,
            ..Default::default()
        }));
    }
    Ok((res.position_encoding, res.diagnostic_source))
}

/// `type rejectHandler struct` — rejects any request initiated by the
/// mapper. The content mapper protocol is currently parent-driven only; a
/// request from the child is a protocol violation.
struct RejectHandler;

impl Handler for RejectHandler {
    /// `HandleRequest`
    fn handle_request(
        &self,
        _ctx: &Context,
        method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<
        Option<ipc::ResponsePayload>,
        Box<dyn std::error::Error + Send + Sync>,
    > {
        Err(format!("content mapper sent an unexpected request: {method}").into())
    }

    /// `HandleNotification`
    fn handle_notification(
        &self,
        _ctx: &Context,
        _method: &str,
        _params: Option<Value>,
    ) -> std::result::Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

/// `func decodeTransformResult(raw, originalText, positionEncoding, diagnosticSource)`
fn decode_transform_result(
    raw: Option<Value>,
    original_text: &str,
    position_encoding: &PositionEncoding,
    diagnostic_source: &str,
) -> std::result::Result<Result, Error> {
    let res: TransformResult =
        json::unmarshal(raw.as_ref().map_or(&b""[..], |v| v.get().as_bytes()), &[])
            .map_err(into_json_error)?;
    let (mapped, original_positions) = decode_mapped_output(
        &res.mapped_output,
        original_text,
        position_encoding,
        diagnostic_source,
    )?;
    let mut result = Result {
        text: mapped.text,
        virtual_extension: mapped.virtual_extension,
        mappings: mapped.mappings,
        diagnostic_directives: mapped.diagnostic_directives,
        ..Default::default()
    };
    for (supplemental_index, supplemental) in res.supplemental.iter().enumerate() {
        match decode_mapped_output(
            &supplemental.mapped_output,
            original_text,
            position_encoding,
            diagnostic_source,
        ) {
            Err(mut e) => {
                // `errors.AsType[*DiagnosticDirectiveError](err)` — the error
                // here is unwrapped, so a direct variant match suffices.
                if let Error::DiagnosticDirective(directive_error) = &mut e {
                    directive_error.supplemental_index = supplemental_index as i64;
                }
                return Err(e);
            }
            Ok((mapped, _)) => result.supplemental.push(mapped),
        }
    }
    for d in &res.diagnostics {
        if d.start < 0 || d.length < 0 || d.start > i64::MAX - d.length {
            return Err(Error::message(format!(
                "invalid content mapper diagnostic range [{}, {})",
                d.start,
                d.start + d.length
            )));
        }
        let start = original_positions
            .normalize(d.start)
            .map_err(|e| Error::message(format!("invalid content mapper diagnostic start: {e}")))?;
        let end = original_positions
            .normalize(d.start + d.length)
            .map_err(|e| Error::message(format!("invalid content mapper diagnostic end: {e}")))?;
        result
            .diagnostics
            .push(ast::diagnostic::new_external_diagnostic(
                None,
                TextRange::new(start, end),
                diagnostic_source.to_string(),
                Category::Error,
                d.code,
                d.message_text.clone(),
            ));
    }
    Ok(result)
}

/// `func decodeMappedOutput(output, originalText, positionEncoding, diagnosticSource)` —
/// returns the decoded output and the original-text normalizer (Go's second
/// return value, used for diagnostics).
fn decode_mapped_output<'a>(
    output: &MappedOutput,
    original_text: &'a str,
    position_encoding: &PositionEncoding,
    diagnostic_source: &str,
) -> std::result::Result<(MappedResult, PositionNormalizer<'a>), Error> {
    if !is_supported_virtual_extension(&output.extension) {
        return Err(Error::InvalidVirtualExtension(
            InvalidVirtualExtensionError {
                extension: output.extension.clone(),
            },
        ));
    }
    let mut result = MappedResult {
        text: output.text.clone(),
        virtual_extension: output.extension.clone(),
        ..Default::default()
    };
    let virtual_positions = PositionNormalizer::new(&output.text, position_encoding)?;
    let original_positions = PositionNormalizer::new(original_text, position_encoding)?;
    // A successful transform always carries a span map. Absent or empty
    // mappings describe fully synthesized output (no segment corresponds to
    // the original), so decode to an empty map rather than nil, which would
    // mean "not content-mapped".
    if output.mappings.as_ref().map_or(0, |v| v.get().len()) > 0 {
        let mappings = spanmap::unmarshal(output.mappings.as_ref().unwrap().get().as_bytes())
            .map_err(|e| Error::SpanMapUnmarshal(Arc::new(e)))?;
        result.mappings = Some(Arc::new(normalize_mappings(
            &mappings,
            &virtual_positions,
            &original_positions,
        )?));
    } else {
        result.mappings = Some(Arc::new(SpanMap::new(&[])));
    }
    result.diagnostic_directives = normalize_diagnostic_directives(
        output.diagnostic_directives.as_ref(),
        &virtual_positions,
        &original_positions,
        diagnostic_source,
    )?;
    Ok((result, original_positions))
}

/// `func normalizeDiagnosticDirectives(...)`
fn normalize_diagnostic_directives(
    diagnostic_directives: Option<&DiagnosticDirectives>,
    virtual_positions: &PositionNormalizer,
    original_positions: &PositionNormalizer,
    diagnostic_source: &str,
) -> std::result::Result<Vec<ast::MappedDiagnosticDirective>, Error> {
    let Some(diagnostic_directives) = diagnostic_directives else {
        return Ok(Vec::new());
    };
    let directives = diagnostic_directives.directives.as_deref().unwrap_or(&[]);
    let unused_diagnostics = diagnostic_directives
        .unused_expect_directive_diagnostics
        .as_deref()
        .unwrap_or(&[]);
    let mut result: Vec<ast::MappedDiagnosticDirective> = Vec::with_capacity(directives.len());
    for (i, directive) in directives.iter().enumerate() {
        let directive_error = |kind: DiagnosticDirectiveErrorKind| {
            Error::DiagnosticDirective(DiagnosticDirectiveError {
                kind,
                index: i as i64,
                supplemental_index: -1,
                policy: DiagnosticDirectivePolicy::default(),
            })
        };
        let mut normalized = ast::MappedDiagnosticDirective {
            source: diagnostic_source.to_string(),
            ..Default::default()
        };
        if directive.policy == DiagnosticDirectivePolicy::IGNORE {
            normalized.policy = ast::MappedDiagnosticDirectivePolicy::Ignore;
        } else if directive.policy == DiagnosticDirectivePolicy::EXPECT {
            let mut unused_diagnostic_index: i64 = 0;
            if let Some(index) = directive.unused_expect_directive_index {
                unused_diagnostic_index = index;
            } else if unused_diagnostics.len() != 1 {
                return Err(directive_error(
                    DiagnosticDirectiveErrorKind::ExpectMissingUnusedDiagnostic,
                ));
            }
            if unused_diagnostic_index < 0
                || unused_diagnostic_index as usize >= unused_diagnostics.len()
            {
                return Err(directive_error(
                    DiagnosticDirectiveErrorKind::InvalidUnusedDiagnosticIndex,
                ));
            }
            let unused_diagnostic = &unused_diagnostics[unused_diagnostic_index as usize];
            normalized.policy = ast::MappedDiagnosticDirectivePolicy::Expect;
            normalized.unused_code = unused_diagnostic.code;
            normalized.unused_message_text = unused_diagnostic.message_text.clone();
        } else {
            return Err(Error::DiagnosticDirective(DiagnosticDirectiveError {
                kind: DiagnosticDirectiveErrorKind::InvalidPolicy,
                index: i as i64,
                supplemental_index: -1,
                policy: directive.policy,
            }));
        }
        if directive.virtual_start < 0 || directive.virtual_end < directive.virtual_start {
            return Err(directive_error(DiagnosticDirectiveErrorKind::InvalidRange));
        }
        let Ok(virtual_start) = virtual_positions.normalize(directive.virtual_start) else {
            return Err(directive_error(DiagnosticDirectiveErrorKind::InvalidRange));
        };
        let Ok(virtual_end) = virtual_positions.normalize(directive.virtual_end) else {
            return Err(directive_error(DiagnosticDirectiveErrorKind::InvalidRange));
        };
        normalized.virtual_range = TextRange::new(virtual_start, virtual_end);
        let mut valid_original_range = directive.original_start >= 0
            && directive.original_length >= 0
            && directive.original_start <= i64::MAX - directive.original_length;
        if valid_original_range {
            let original_start = original_positions.normalize(directive.original_start);
            let original_end =
                original_positions.normalize(directive.original_start + directive.original_length);
            if let (Ok(original_start), Ok(original_end)) = (original_start, original_end) {
                normalized.original_range = TextRange::new(original_start, original_end);
            } else {
                valid_original_range = false;
            }
        }
        if normalized.policy == ast::MappedDiagnosticDirectivePolicy::Expect
            && !valid_original_range
        {
            return Err(directive_error(DiagnosticDirectiveErrorKind::InvalidRange));
        }
        result.push(normalized);
    }
    // Overlap check: sort a copy by virtual start (unstable, like Go's
    // `slices.SortFunc`), then reject any directive starting before its
    // predecessor ends — reporting the directive's original index.
    let mut sorted: Vec<(i64, &ast::MappedDiagnosticDirective)> = result
        .iter()
        .enumerate()
        .map(|(i, d)| (i as i64, d))
        .collect();
    sorted.sort_by(|a, b| {
        a.1.virtual_range
            .pos()
            .wrapping_sub(b.1.virtual_range.pos())
            .cmp(&0)
    });
    for i in 1..sorted.len() {
        if sorted[i].1.virtual_range.pos() < sorted[i - 1].1.virtual_range.end() {
            return Err(Error::DiagnosticDirective(DiagnosticDirectiveError {
                kind: DiagnosticDirectiveErrorKind::Overlap,
                index: sorted[i].0,
                supplemental_index: -1,
                policy: DiagnosticDirectivePolicy::default(),
            }));
        }
    }
    Ok(result)
}

/// `func normalizeMappings(mappings, virtualPositions, originalPositions)`
fn normalize_mappings(
    mappings: &SpanMap,
    virtual_positions: &PositionNormalizer,
    original_positions: &PositionNormalizer,
) -> std::result::Result<SpanMap, Error> {
    let mut segments = SpanMap::segments(Some(mappings));
    for (i, segment) in segments.iter_mut().enumerate() {
        segment.virtual_start = virtual_positions
            .normalize_text_pos(segment.virtual_start)
            .map_err(|e| {
                Error::message(format!(
                    "invalid content mapper mapping {i} virtual start: {e}"
                ))
            })?;
        segment.virtual_end = virtual_positions
            .normalize_text_pos(segment.virtual_end)
            .map_err(|e| {
                Error::message(format!(
                    "invalid content mapper mapping {i} virtual end: {e}"
                ))
            })?;
        segment.original_start = original_positions
            .normalize_text_pos(segment.original_start)
            .map_err(|e| {
                Error::message(format!(
                    "invalid content mapper mapping {i} original start: {e}"
                ))
            })?;
        segment.original_end = original_positions
            .normalize_text_pos(segment.original_end)
            .map_err(|e| {
                Error::message(format!(
                    "invalid content mapper mapping {i} original end: {e}"
                ))
            })?;
    }
    Ok(SpanMap::new(&segments))
}

/// `type positionNormalizer struct` — converts protocol positions (UTF-8
/// byte or UTF-16 code-unit offsets) to host byte positions.
struct PositionNormalizer<'a> {
    text: &'a str,
    encoding: PositionEncoding,
    position_map: Option<ast::positionmap::PositionMap>,
    length: i64,
}

impl<'a> PositionNormalizer<'a> {
    /// `func newPositionNormalizer(text, encoding)`
    fn new(text: &'a str, encoding: &PositionEncoding) -> std::result::Result<Self, Error> {
        let (position_map, length) = if *encoding == PositionEncoding::UTF8 {
            (None, text.len() as i64)
        } else if *encoding == PositionEncoding::UTF16 {
            let position_map = ast::positionmap::compute_position_map(text.as_bytes());
            let length = position_map.utf8_to_utf16(text.len()) as i64;
            (Some(position_map), length)
        } else {
            return Err(Error::message(format!(
                "unsupported position encoding {:?}",
                encoding.0
            )));
        };
        Ok(PositionNormalizer {
            text,
            encoding: encoding.clone(),
            position_map,
            length,
        })
    }

    /// `func (n *positionNormalizer) normalizeTextPos`
    fn normalize_text_pos(&self, position: i32) -> std::result::Result<i32, NormalizeError> {
        self.normalize(position as i64)
    }

    /// `func (n *positionNormalizer) normalize`
    fn normalize(&self, position: i64) -> std::result::Result<i32, NormalizeError> {
        if position < 0 {
            return Err(NormalizeError(format!("position {position} is negative")));
        }
        if position > self.length {
            return Err(NormalizeError(format!(
                "position {position} exceeds {} length {}",
                self.encoding, self.length
            )));
        }
        let byte_position = if self.encoding == PositionEncoding::UTF8 {
            position
        } else {
            self.position_map
                .as_ref()
                .unwrap()
                .utf16_to_utf8(position as usize) as i64
        };
        let bytes = self.text.as_bytes();
        if (byte_position as usize) < bytes.len() && (bytes[byte_position as usize] & 0xC0) == 0x80
        {
            // `!utf8.RuneStart` — the position splits a multi-byte sequence.
            return Err(NormalizeError(format!(
                "position {position} splits a Unicode code point"
            )));
        }
        Ok(byte_position as i32)
    }
}

/// The `fmt.Errorf`-produced position normalization error — a plain message
/// string, wrapped by callers.
#[derive(Debug)]
struct NormalizeError(String);

impl fmt::Display for NormalizeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for NormalizeError {}
