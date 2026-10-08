// Ported from tsc/internal/contentmapper/host.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - Go's typed `error` values collapse into the [`Error`] enum. The typed
//   structs (`TransformError`, `InitializeError`, ...) stay public as
//   variants' payloads; `errors.AsType[T]` becomes `Error::as_*`, which
//   walks the same unwrapping chain (`TransformError`'s source, `errors.Join`
//   members) `errors.As` would.
// - `Project`/`Host` Go interfaces become traits; `*Mapper` params become
//   `&Arc<Mapper>` (the Go code uses mapper pointers as map keys).
// - `Result` keeps its Go name; use `std::result::Result` spelled out where
//   the two collide.
// - `Mappings *spanmap.SpanMap` → `Option<Arc<SpanMap>>`: the normalized map
//   is shared with `ContentMapperSourceFileInfo.span_map`.

use std::fmt;
use std::io;
use std::sync::Arc;
use std::time::Duration;

use tsc_ast::{self as ast, diagnostic::DiagnosticRef};
use tsc_core::options_generated::CompilerOptions;
use tsc_json as json;
use tsc_locale::Locale;
use tsc_spanmap::SpanMap;
use tsc_tspath::{RootedDirectoryPath, RootedFilePath};

use crate::contentmapper::Mapper;

// TransformErrorKind

/// `type TransformErrorKind uint8` — identifies the stage at which a content
/// mapper transform failed.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum TransformErrorKind {
    /// `TransformErrorKindUnknown`
    #[default]
    Unknown = 0,
    /// `TransformErrorKindInitialize`
    Initialize = 1,
    /// `TransformErrorKindProject`
    Project = 2,
    /// `TransformErrorKindRequest`
    Request = 3,
    /// `TransformErrorKindResponse`
    Response = 4,
    /// `TransformErrorKindMappings`
    Mappings = 5,
}

/// `type TransformError struct` — reports a failure while preparing,
/// requesting, or decoding a transform.
///
/// PORT: `err error` becomes `Option<Box<Error>>` — Go's
/// `NewTransformError(kind, nil)` leaves it nil; the `Box` breaks the
/// `Error → TransformError → Error` size cycle.
#[derive(Clone, Default)]
pub struct TransformError {
    /// `Kind TransformErrorKind`
    pub kind: TransformErrorKind,
    /// `err error`
    pub source: Option<Box<Error>>,
}

impl TransformError {
    /// `func NewTransformError(kind, err) *TransformError`
    pub fn new(kind: TransformErrorKind, err: Option<Error>) -> TransformError {
        TransformError {
            kind,
            source: err.map(Box::new),
        }
    }
}

impl fmt::Display for TransformError {
    /// `func (e *TransformError) Error() string`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.source {
            Some(source) => write!(f, "content mapper transform failed: {source}"),
            None => write!(f, "content mapper transform failed: <nil>"),
        }
    }
}

// DiagnosticDirectiveErrorKind

/// `type DiagnosticDirectiveErrorKind uint8` — identifies why a diagnostic
/// directive was rejected.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum DiagnosticDirectiveErrorKind {
    /// `DiagnosticDirectiveErrorKindInvalidRange`
    #[default]
    InvalidRange = 0,
    /// `DiagnosticDirectiveErrorKindInvalidPolicy`
    InvalidPolicy = 1,
    /// `DiagnosticDirectiveErrorKindExpectMissingUnusedDiagnostic`
    ExpectMissingUnusedDiagnostic = 2,
    /// `DiagnosticDirectiveErrorKindInvalidUnusedDiagnosticIndex`
    InvalidUnusedDiagnosticIndex = 3,
    /// `DiagnosticDirectiveErrorKindOverlap`
    Overlap = 4,
}

/// `type DiagnosticDirectiveError struct` — reports an invalid diagnostic
/// directive in a transform response.
#[derive(Clone, Default)]
pub struct DiagnosticDirectiveError {
    /// `Kind DiagnosticDirectiveErrorKind`
    pub kind: DiagnosticDirectiveErrorKind,
    /// `Index int`
    pub index: i64,
    /// `SupplementalIndex int` — `-1` for the canonical output's directives.
    pub supplemental_index: i64,
    /// `Policy DiagnosticDirectivePolicy`
    pub policy: crate::hostimpl::DiagnosticDirectivePolicy,
}

impl fmt::Display for DiagnosticDirectiveError {
    /// `func (e *DiagnosticDirectiveError) Error() string`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid content mapper diagnostic directive {}",
            self.index
        )
    }
}

/// `type InvalidVirtualExtensionError struct` — reports an unsupported or
/// missing virtual extension on a mapped output.
#[derive(Clone, Default)]
pub struct InvalidVirtualExtensionError {
    /// `Extension string`
    pub extension: String,
}

impl fmt::Display for InvalidVirtualExtensionError {
    /// `func (e *InvalidVirtualExtensionError) Error() string`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid virtual extension {:?}", self.extension)
    }
}

// ProjectErrorKind

/// `type ProjectErrorKind uint8` — identifies why a mapper's openProject
/// response was rejected.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum ProjectErrorKind {
    /// `ProjectErrorKindMalformedResponse`
    #[default]
    MalformedResponse = 0,
    /// `ProjectErrorKindMissingConfigIdentity`
    MissingConfigIdentity = 1,
    /// `ProjectErrorKindNonAbsoluteWatchedFile`
    NonAbsoluteWatchedFile = 2,
    /// `ProjectErrorKindUnexpectedConfigIdentity`
    UnexpectedConfigIdentity = 3,
    /// `ProjectErrorKindUnexpectedWatchedFiles`
    UnexpectedWatchedFiles = 4,
}

/// `type ProjectError struct` — reports an invalid mapper openProject
/// response.
#[derive(Clone, Copy, Default)]
pub struct ProjectError {
    /// `Kind ProjectErrorKind`
    pub kind: ProjectErrorKind,
}

impl fmt::Display for ProjectError {
    /// `func (e *ProjectError) Error() string`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self.kind {
            ProjectErrorKind::MalformedResponse => {
                "content mapper returned a malformed project response"
            }
            ProjectErrorKind::MissingConfigIdentity => {
                "content mapper did not return configIdentity for dynamic configuration"
            }
            ProjectErrorKind::NonAbsoluteWatchedFile => {
                "content mapper returned a non-absolute path in watchedFiles"
            }
            ProjectErrorKind::UnexpectedConfigIdentity => {
                "content mapper returned configIdentity without declaring dynamicConfig"
            }
            ProjectErrorKind::UnexpectedWatchedFiles => {
                "content mapper returned watchedFiles without declaring dynamicConfig"
            }
        })
    }
}

// InitializeErrorKind

/// `type InitializeErrorKind uint8` — identifies why a mapper's initialize
/// response was rejected.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum InitializeErrorKind {
    /// `InitializeErrorKindProcessStart`
    #[default]
    ProcessStart = 0,
    /// `InitializeErrorKindProcessExit`
    ProcessExit = 1,
    /// `InitializeErrorKindNoResponse`
    NoResponse = 2,
    /// `InitializeErrorKindInvalidResponse`
    InvalidResponse = 3,
    /// `InitializeErrorKindRequest`
    Request = 4,
    /// `InitializeErrorKindPositionEncoding`
    PositionEncoding = 5,
    /// `InitializeErrorKindEmptyDiagnosticSource`
    EmptyDiagnosticSource = 6,
    /// `InitializeErrorKindReservedDiagnosticSource`
    ReservedDiagnosticSource = 7,
}

/// `type InitializeError struct` — reports an invalid or unsupported mapper
/// initialize response.
#[derive(Clone, Default)]
pub struct InitializeError {
    /// `Kind InitializeErrorKind`
    pub kind: InitializeErrorKind,
    /// `MapperName string`
    pub mapper_name: String,
    /// `Command string`
    pub command: String,
    /// `Detail string`
    pub detail: String,
    /// `ExitCode int`
    pub exit_code: i64,
    /// `TimeoutSeconds int`
    pub timeout_seconds: i64,
    /// `PositionEncoding PositionEncoding`
    pub position_encoding: crate::hostimpl::PositionEncoding,
    /// `DiagnosticSource string`
    pub diagnostic_source: String,
}

impl fmt::Display for InitializeError {
    /// `func (e *InitializeError) Error() string`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            InitializeErrorKind::ProcessStart => {
                write!(
                    f,
                    "could not start content mapper command {:?}: {}",
                    self.command, self.detail
                )
            }
            InitializeErrorKind::ProcessExit => write!(
                f,
                "content mapper process exited before initialization with code {}",
                self.exit_code
            ),
            InitializeErrorKind::NoResponse => {
                f.write_str("content mapper did not respond to the initialize request")
            }
            InitializeErrorKind::InvalidResponse => write!(
                f,
                "content mapper returned an invalid initialize response: {}",
                self.detail
            ),
            InitializeErrorKind::Request => {
                write!(
                    f,
                    "content mapper initialize request failed: {}",
                    self.detail
                )
            }
            InitializeErrorKind::PositionEncoding => {
                write!(
                    f,
                    "unsupported position encoding {:?}",
                    self.position_encoding
                )
            }
            InitializeErrorKind::EmptyDiagnosticSource => {
                f.write_str("diagnostic source must not be empty")
            }
            InitializeErrorKind::ReservedDiagnosticSource => write!(
                f,
                "diagnostic source {:?} is reserved by TypeScript",
                self.diagnostic_source
            ),
        }
    }
}

/// `type SupplementalFileCollisionError struct` — reports a compiler-assigned
/// supplemental filename that already exists.
#[derive(Clone, Default)]
pub struct SupplementalFileCollisionError {
    /// `FileName tspath.RootedFilePath`
    pub file_name: RootedFilePath,
}

impl fmt::Display for SupplementalFileCollisionError {
    /// `func (e *SupplementalFileCollisionError) Error() string`
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "content mapper supplemental output file {:?} already exists",
            self.file_name.as_string()
        )
    }
}

/// Every Go `error` this package produces or forwards. Go's `errors.Is`/
/// `errors.As` machinery becomes variant matching plus the `as_*`/walking
/// helpers below.
#[derive(Clone)]
pub enum Error {
    /// `ErrProjectUnavailable` — the project needed for a transform is gone
    /// (e.g. its session ended).
    ProjectUnavailable,
    /// `*InitializeError`
    Initialize(InitializeError),
    /// `*ProjectError`
    Project(ProjectError),
    /// `*TransformError`
    Transform(TransformError),
    /// `*DiagnosticDirectiveError`
    DiagnosticDirective(DiagnosticDirectiveError),
    /// `*InvalidVirtualExtensionError`
    InvalidVirtualExtension(InvalidVirtualExtensionError),
    /// `*SupplementalFileCollisionError`
    SupplementalFileCollision(SupplementalFileCollisionError),
    /// `*spanmap.MappingError` returned by `Mappings.Validate`.
    Mapping(tsc_spanmap::MappingError),
    /// `spanmap.Unmarshal` failure.
    SpanMapUnmarshal(Arc<tsc_spanmap::UnmarshalError>),
    /// `json.Marshal`/`Unmarshal` failure.
    Json(Arc<serde_json::Error>),
    /// An `ipc` call failure.
    Ipc(tsc_ipc::Error),
    /// An `io` failure (process spawn and close paths).
    Io(Arc<io::Error>),
    /// `errors.New`/`fmt.Errorf` — a plain message.
    Message(String),
    /// `errors.Join` — pairwise like Go's variadic join flattened.
    Joined(Box<Error>, Box<Error>),
}

impl Error {
    /// `errors.New(msg)` / `fmt.Errorf(msg)`
    pub(crate) fn message(msg: impl Into<String>) -> Error {
        Error::Message(msg.into())
    }

    /// `NewTransformError(kind, err)` wrapped in `Error`.
    pub(crate) fn transform(kind: TransformErrorKind, err: Error) -> Error {
        Error::Transform(TransformError::new(kind, Some(err)))
    }

    /// `errors.Join` — `None` operands collapse like nil errors in Go.
    pub(crate) fn joined(a: Option<Error>, b: Option<Error>) -> Option<Error> {
        match (a, b) {
            (Some(a), Some(b)) => Some(Error::Joined(Box::new(a), Box::new(b))),
            (Some(e), None) | (None, Some(e)) => Some(e),
            (None, None) => None,
        }
    }

    /// `errors.Is(err, ErrProjectUnavailable)`.
    pub fn is_project_unavailable(&self) -> bool {
        self.find(|e| matches!(e, Error::ProjectUnavailable).then_some(()))
            .is_some()
    }

    /// `errors.Is(err, context.Canceled)` — the only Go sentinel the
    /// classification code checks.
    pub(crate) fn is_context_canceled(&self) -> bool {
        self.find(|e| {
            matches!(e, Error::Ipc(e) if e.is(&tsc_ipc::Error::ContextCanceled)).then_some(())
        })
        .is_some()
    }

    /// `errors.AsType[*TransformError](err)` — walks `Unwrap`: a
    /// `TransformError`'s source and `errors.Join` members.
    pub fn as_transform_error(&self) -> Option<&TransformError> {
        self.find(|e| match e {
            Error::Transform(e) => Some(e),
            _ => None,
        })
    }

    /// `errors.AsType[*InitializeError](err)`.
    pub fn as_initialize_error(&self) -> Option<&InitializeError> {
        self.find(|e| match e {
            Error::Initialize(e) => Some(e),
            _ => None,
        })
    }

    /// `errors.AsType[*ProjectError](err)` — Go's
    /// `errors.AsType[*ProjectError](transformError)` unwraps the transform
    /// error to find the project error.
    pub fn as_project_error(&self) -> Option<&ProjectError> {
        self.find(|e| match e {
            Error::Project(e) => Some(e),
            _ => None,
        })
    }

    /// `errors.AsType[*DiagnosticDirectiveError](err)`.
    pub fn as_diagnostic_directive_error(&self) -> Option<&DiagnosticDirectiveError> {
        self.find(|e| match e {
            Error::DiagnosticDirective(e) => Some(e),
            _ => None,
        })
    }

    /// `errors.AsType[*InvalidVirtualExtensionError](err)`.
    pub fn as_invalid_virtual_extension_error(&self) -> Option<&InvalidVirtualExtensionError> {
        self.find(|e| match e {
            Error::InvalidVirtualExtension(e) => Some(e),
            _ => None,
        })
    }

    /// `errors.AsType[*SupplementalFileCollisionError](err)`.
    pub fn as_supplemental_file_collision_error(&self) -> Option<&SupplementalFileCollisionError> {
        self.find(|e| match e {
            Error::SupplementalFileCollision(e) => Some(e),
            _ => None,
        })
    }

    /// `errors.AsType[*spanmap.MappingError](err)`.
    pub fn as_mapping_error(&self) -> Option<&tsc_spanmap::MappingError> {
        self.find(|e| match e {
            Error::Mapping(e) => Some(e),
            _ => None,
        })
    }

    /// Depth-first chain walk over `TransformError.source` and `Joined`
    /// members — Go's `Unwrap`/`Unwrap []error` traversal.
    fn find<'a, T>(&'a self, f: impl Fn(&'a Error) -> Option<T>) -> Option<T> {
        fn walk<'a, T>(e: &'a Error, f: &dyn Fn(&'a Error) -> Option<T>) -> Option<T> {
            if let Some(t) = f(e) {
                return Some(t);
            }
            match e {
                Error::Transform(te) => te.source.as_deref().and_then(|s| walk(s, f)),
                Error::Joined(a, b) => walk(a, f).or_else(|| walk(b, f)),
                _ => None,
            }
        }
        walk(self, &f)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::ProjectUnavailable => f.write_str("content mapper project is unavailable"),
            Error::Initialize(e) => e.fmt(f),
            Error::Project(e) => e.fmt(f),
            Error::Transform(e) => e.fmt(f),
            Error::DiagnosticDirective(e) => e.fmt(f),
            Error::InvalidVirtualExtension(e) => e.fmt(f),
            Error::SupplementalFileCollision(e) => e.fmt(f),
            Error::Mapping(e) => e.fmt(f),
            Error::SpanMapUnmarshal(e) => e.fmt(f),
            Error::Json(e) => e.fmt(f),
            Error::Ipc(e) => e.fmt(f),
            Error::Io(e) => e.fmt(f),
            Error::Message(m) => f.write_str(m),
            // Go's `joinError.Error()` joins operands with '\n'.
            Error::Joined(a, b) => write!(f, "{a}\n{b}"),
        }
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Transform(e) => e
                .source
                .as_deref()
                .map(|s| s as &(dyn std::error::Error + 'static)),
            _ => None,
        }
    }
}

/// `type Result struct` — the outcome of transforming a content-mapped
/// source file into virtual TypeScript.
///
/// PORT: the name shadows `std::result::Result` inside this crate; `Result`
/// in Go is an output value, not an error carrier.
#[derive(Clone, Default)]
pub struct Result {
    /// `Text` is the virtual TypeScript source text that is parsed into the
    /// program.
    pub text: String,
    /// `VirtualExtension` determines how `text` is parsed.
    pub virtual_extension: String,
    /// `Diagnostics` are syntax errors in the original content.
    pub diagnostics: Vec<DiagnosticRef>,
    /// `Mappings` maps positions in `text` back to the original content, so
    /// that diagnostics the compiler produces against the virtual text can
    /// be reported at their original locations. A successful transform must
    /// return a non-nil map; an empty map describes fully synthesized
    /// output.
    pub mappings: Option<Arc<SpanMap>>,
    /// `DiagnosticDirectives` control TypeScript diagnostics produced in
    /// virtual ranges.
    pub diagnostic_directives: Vec<ast::MappedDiagnosticDirective>,
    /// `Supplemental` contains additional unnamed outputs associated with
    /// the canonical result.
    pub supplemental: Vec<MappedResult>,
}

impl std::fmt::Debug for Result {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Result")
            .field("text", &self.text)
            .field("virtual_extension", &self.virtual_extension)
            .field("diagnostics", &self.diagnostics.len())
            .field("supplemental", &self.supplemental.len())
            .finish_non_exhaustive()
    }
}

/// `type MappedResult struct` — one virtual source file and its mapping to
/// the original input.
#[derive(Clone, Default)]
pub struct MappedResult {
    /// `Text string`
    pub text: String,
    /// `VirtualExtension string`
    pub virtual_extension: String,
    /// `Mappings *spanmap.SpanMap`
    pub mappings: Option<Arc<SpanMap>>,
    /// `DiagnosticDirectives []ast.MappedDiagnosticDirective`
    pub diagnostic_directives: Vec<ast::MappedDiagnosticDirective>,
}

/// `type Request struct` — the inputs for transforming one content-mapped
/// source file.
#[derive(Clone, Default)]
pub struct Request {
    /// `FileName` is the content-mapped source file being transformed.
    pub file_name: RootedFilePath,
    /// `Content` is the content-mapped source file's text.
    pub content: String,
}

/// `type ProjectSpec struct` — describes the project configuration visible
/// to its content mappers.
///
/// PORT: `Mappers []*Mapper` → `Vec<Arc<Mapper>>`;
/// `CompilerOptions *core.CompilerOptions` → `Option<Arc<CompilerOptions>>`
/// (`None` is Go's nil; the `Arc` pointer also feeds `projectSpecKey` like
/// Go's `%p`).
#[derive(Clone, Default)]
pub struct ProjectSpec {
    /// `ConfigFileName` is the absolute project configuration file name, or
    /// empty for a project without one.
    pub config_file_name: RootedFilePath,
    /// `Mappers` are the resolved content mapper entries configured for the
    /// project.
    pub mappers: Vec<Arc<Mapper>>,
    /// `CompilerOptions` are the project's effective compiler options.
    pub compiler_options: Option<Arc<CompilerOptions>>,
}

/// `type OptionPathSegment struct`
#[derive(Clone, Default)]
pub struct OptionPathSegment {
    /// `Property string`
    pub property: String,
    /// `Index int`
    pub index: i64,
    /// `IsIndex bool`
    pub is_index: bool,
}

/// `type OptionDiagnostic struct`
#[derive(Clone)]
pub struct OptionDiagnostic {
    /// `Mapper *Mapper`
    pub mapper: Arc<Mapper>,
    /// `Path []OptionPathSegment`
    pub path: Vec<OptionPathSegment>,
    /// `Source string`
    pub source: String,
    /// `Code int32`
    pub code: i32,
    /// `MessageText string`
    pub message_text: String,
}

/// `type OperationTiming struct` — cumulative wall time and invocation count
/// for one mapper operation.
#[derive(Clone, Copy, Default, Debug)]
pub struct OperationTiming {
    /// `Count uint64`
    pub count: u64,
    /// `Duration time.Duration`
    pub duration: Duration,
}

/// `type MapperTimings struct` — cumulative process and protocol activity
/// for one resolved mapper identity.
#[derive(Clone, Copy, Default, Debug)]
pub struct MapperTimings {
    /// `Spawn OperationTiming`
    pub spawn: OperationTiming,
    /// `Initialize OperationTiming`
    pub initialize: OperationTiming,
    /// `OpenProject OperationTiming`
    pub open_project: OperationTiming,
    /// `CloseProject OperationTiming`
    pub close_project: OperationTiming,
    /// `Transform OperationTiming`
    pub transform: OperationTiming,
}

/// `type Timings struct` — a cumulative snapshot of content mapper process
/// and protocol activity.
#[derive(Clone, Default)]
pub struct Timings {
    /// `Mappers map[string]MapperTimings`
    pub mappers: rustc_hash::FxHashMap<String, MapperTimings>,
    /// `RequestWait time.Duration`
    pub request_wait: Duration,
}

impl Timings {
    /// `func (t Timings) Since(previous Timings) Timings` — the non-negative
    /// operation delta since `previous`.
    pub fn since(&self, previous: &Timings) -> Timings {
        let mut result = Timings {
            mappers: rustc_hash::FxHashMap::default(),
            request_wait: self.request_wait.saturating_sub(previous.request_wait),
        };
        result.mappers.reserve(self.mappers.len());
        for (identity, current) in &self.mappers {
            let before = previous.mappers.get(identity).copied().unwrap_or_default();
            result.mappers.insert(
                identity.clone(),
                MapperTimings {
                    spawn: operation_timing_since(&current.spawn, &before.spawn),
                    initialize: operation_timing_since(&current.initialize, &before.initialize),
                    open_project: operation_timing_since(
                        &current.open_project,
                        &before.open_project,
                    ),
                    close_project: operation_timing_since(
                        &current.close_project,
                        &before.close_project,
                    ),
                    transform: operation_timing_since(&current.transform, &before.transform),
                },
            );
        }
        result
    }
}

/// `func operationTimingSince(current, previous OperationTiming) OperationTiming`
fn operation_timing_since(
    current: &OperationTiming,
    previous: &OperationTiming,
) -> OperationTiming {
    OperationTiming {
        count: current.count - current.count.min(previous.count),
        duration: current.duration.saturating_sub(previous.duration),
    }
}

/// `type Project interface` — the project-scoped view of a `Host`. It owns
/// mapper configuration handles and provides the identities and watch
/// dependencies needed for caching and incremental builds. Mapper projects
/// are opened lazily when a transform is requested, or earlier when dynamic
/// configuration is needed.
///
/// PORT: implementations returned by [`Host::project`] also `release()` on
/// `Drop` like a `defer Close()`-less Go caller that forgets — the refcount
/// contract stays the same.
pub trait Project: Send + Sync {
    /// `Refresh()` — closes opened mapper projects so they are reopened on
    /// the next transform or configuration identity query.
    fn refresh(&self) -> std::result::Result<(), Error>;
    /// `Identities()` — sorted transform identities for all configured
    /// mappers. It returns an error if dynamic project configuration cannot
    /// be opened or validated.
    fn identities(&self) -> std::result::Result<Vec<String>, Error>;
    /// `Identity(mapper)` — the transform identity for `mapper`, or an
    /// empty string if `mapper` is not in this project. It returns an error
    /// if dynamic project configuration cannot be opened or validated.
    fn identity(&self, mapper: &Arc<Mapper>) -> std::result::Result<String, Error>;
    /// `WatchedFiles()` — the absolute files reported by mappers whose
    /// package.json declares dynamicConfig. It returns an error if project
    /// configuration cannot be opened or validated.
    fn watched_files(&self) -> std::result::Result<Vec<RootedFilePath>, Error>;
    /// `Diagnostics()` — option diagnostics cached by mapper projects that
    /// have already been opened.
    fn diagnostics(&self) -> Vec<OptionDiagnostic>;
    /// `Transform(mapper, request)` — transforms one content-mapped source
    /// file using `mapper` in this project's configuration.
    fn transform(
        &self,
        mapper: &Arc<Mapper>,
        request: &Request,
    ) -> std::result::Result<Result, Error>;
    /// `Close()` — releases this project reference and closes mapper project
    /// handles when no references remain. Idempotent like Go's `sync.Once`.
    fn close(&self) -> std::result::Result<(), Error>;
}

/// `type Host interface` — transforms otherwise unsupported file content
/// into virtual TypeScript during program construction, by driving the
/// configured content mappers. Create one with [`crate::new_host`];
/// [`Host::close`] tears down every mapper it spawned.
pub trait Host: Send + Sync {
    /// `Timings()` — a cumulative snapshot of mapper process and protocol
    /// activity.
    fn timings(&self) -> Timings;
    /// `Project(spec)` — a retained project-scoped view for `spec`.
    /// Equivalent specs share underlying mapper configuration state; the
    /// caller must close the returned `Project`. `None` is Go's nil return
    /// on a closed host.
    fn project(&self, spec: &ProjectSpec) -> Option<Arc<dyn Project>>;
    /// `Acquire(mappers)` — retains the processes for the given mapper
    /// identities until the returned lease is released (or dropped).
    /// Acquiring a mapper does not start its process; processes remain lazy
    /// until `Transform` is called.
    fn acquire(&self, mappers: &[Arc<Mapper>]) -> crate::hostimpl::AcquireLease;
    /// `SetLocale(locale)` — updates the locale used to initialize mapper
    /// processes. Existing processes are stopped and respawned lazily so
    /// subsequent transforms use the new locale.
    fn set_locale(&self, locale: Locale);
    /// `Transform(mapper, request)` — maps a content-mapped source file to
    /// virtual TypeScript using the given content mapper in a short-lived
    /// project with default compiler options.
    ///
    /// A non-nil error indicates the mapper itself failed to produce a
    /// result — for example the host hit a broken pipe, a process crash, or
    /// could not deserialize the mapper's response.
    fn transform(
        &self,
        mapper: &Arc<Mapper>,
        request: &Request,
    ) -> std::result::Result<Result, Error>;
    /// `Close()` — shuts down every mapper process the host spawned.
    fn close(&self) -> std::result::Result<(), Error>;
}

// Unused-import suppressions for re-exported names referenced in doc comments.
#[allow(dead_code)]
type _DocImports = (json::Value, RootedDirectoryPath, tsc_ipc::Error);
