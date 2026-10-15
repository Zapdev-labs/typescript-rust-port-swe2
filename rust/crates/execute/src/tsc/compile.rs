// Ported from tsc/internal/execute/tsc/compile.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io;
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, SystemTime};

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_collections::SyncMap;
use tsc_compiler::emit_host::EmitResult;
use tsc_contentmapper::host::Timings;
use tsc_contentmapper::hostimpl::{HostOptions, SpawnedProcess, new_host_with_options};
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_diagnostics::Message;
use tsc_locale::Locale;
use tsc_tspath::{PathKey, RootedDirectoryPath};
use tsc_vfs::vfs::Vfs;

use crate::tsc::diagnostics::DiagnosticRegistry;

/// `SharedWriter` — Go's `io.Writer` for stdout/stderr. The CLI writers are
/// shared across the watch worker thread, so writes go through a mutex. The
/// guard derefs to the boxed writer so batches of `emit!` calls take the
/// lock once per write, matching Go's per-`Fprint` interleaving.
#[derive(Clone)]
pub struct SharedWriter {
    inner: Arc<Mutex<Box<dyn io::Write + Send>>>,
}

impl SharedWriter {
    pub fn new(w: impl io::Write + Send + 'static) -> SharedWriter {
        SharedWriter {
            inner: Arc::new(Mutex::new(Box::new(w))),
        }
    }

    pub fn from_box(w: Box<dyn io::Write + Send>) -> SharedWriter {
        SharedWriter {
            inner: Arc::new(Mutex::new(w)),
        }
    }

    /// Locks the writer; the guard implements `io::Write`.
    pub fn guard(&self) -> MutexGuard<'_, Box<dyn io::Write + Send>> {
        self.inner.lock().unwrap_or_else(|e| e.into_inner())
    }

    /// `fmt.Fprint` equivalent — locks, writes the string.
    pub fn write_text(&self, s: &str) {
        use std::io::Write;
        let _ = self.guard().write_all(s.as_bytes());
    }
}

impl io::Write for SharedWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.guard().write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.guard().flush()
    }
}

/// `type System interface` — tsc/compile.go.
pub trait System: Send + Sync {
    /// `Writer() io.Writer`.
    fn writer(&self) -> SharedWriter;
    /// `ErrorWriter() io.Writer`.
    fn error_writer(&self) -> SharedWriter;
    /// `FS() vfs.FS`.
    fn fs(&self) -> Arc<dyn Vfs>;
    /// `DefaultLibraryPath() tspath.RootedDirectoryPath`.
    fn default_library_path(&self) -> RootedDirectoryPath;
    /// `GetCurrentDirectory() tspath.RootedDirectoryPath`.
    fn current_directory(&self) -> RootedDirectoryPath;
    /// `WriteOutputIsTTY() bool`.
    fn write_output_is_tty(&self) -> bool;
    /// `GetWidthOfTerminal() int`.
    fn width_of_terminal(&self) -> usize;
    /// `GetEnvironmentVariable(name string) (string, bool)` — `None` is
    /// Go's `ok == false`.
    fn environment_variable(&self, name: &str) -> Option<String>;
    /// `Spawn(command []string, dir string, stderr io.Writer) (io.ReadWriteCloser, error)`.
    ///
    /// `None` stderr is Go's `io.Discard` (see `contentmapper.Spawner`).
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn io::Write + Send>>,
    ) -> io::Result<Arc<dyn SpawnedProcess>>;
    /// `Now() time.Time`.
    fn now(&self) -> SystemTime;
    /// `SinceStart() time.Duration`.
    fn since_start(&self) -> Duration;

    /// The session's diagnostic-arena registry — Go threads
    /// `*ast.SourceFile` pointers through `*ast.Diagnostic`; in Rust the
    /// `DiagnosticFile` snapshot carries everything except the two lookups
    /// that still need the arena (`canonical_source_file`,
    /// `content_mapper`), and this registry stores them keyed by
    /// `file_index`. See `CliDiagnostic` in diagnostics.rs.
    fn diagnostic_registry(&self) -> &Arc<DiagnosticRegistry>;
}

/// `newContentMapperLogger`.
fn new_content_mapper_logger(sys: &dyn System) -> Option<tsc_contentmapper::hostimpl::Logger> {
    if sys
        .environment_variable("TS_CONTENT_MAPPER_DEBUG")
        .unwrap_or_default()
        .is_empty()
    {
        return None;
    }
    let writer = sys.error_writer();
    Some(Arc::new(move |message: &str| {
        use std::io::Write;
        let _ = writeln!(writer.guard(), "{}", message);
    }))
}

/// `type ExitStatus int`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
#[repr(i32)]
pub enum ExitStatus {
    #[default]
    Success = 0,
    DiagnosticsPresentOutputsSkipped = 1,
    DiagnosticsPresentOutputsGenerated = 2,
    InvalidProjectOutputsSkipped = 3,
    ProjectReferenceCycleOutputsSkipped = 4,
    NotImplemented = 5,
}

/// `type Watcher interface { DoCycle() }`.
pub trait Watcher {
    /// `DoCycle()`.
    fn do_cycle(&self);
}

/// `type CommandLineResult struct`.
pub struct CommandLineResult {
    pub status: ExitStatus,
    /// `Watcher Watcher` — `None` is Go's nil.
    pub watcher: Option<Arc<dyn Watcher>>,
}

/// `type CommandLineTesting interface`.
pub trait CommandLineTesting: Send + Sync {
    /// `OnEmittedFiles` — ensure all emitted files are timestamped for
    /// deterministic test baselines.
    fn on_emitted_files(&self, result: &EmitResult, mtimes_cache: &SyncMap<PathKey, SystemTime>);
    fn on_list_files_start(&self, w: &mut dyn io::Write);
    fn on_list_files_end(&self, w: &mut dyn io::Write);
    fn on_statistics_start(&self, w: &mut dyn io::Write);
    fn on_statistics_end(&self, w: &mut dyn io::Write);
    fn on_build_status_report_start(&self, w: &mut dyn io::Write);
    fn on_build_status_report_end(&self, w: &mut dyn io::Write);
    fn on_watch_status_report_start(&self);
    fn on_watch_status_report_end(&self);
    /// `GetTrace(w, locale)` — returns the trace callback.
    fn get_trace(
        &self,
        w: SharedWriter,
        locale: Locale,
    ) -> Box<dyn Fn(&'static Message, &[String]) + Send + Sync>;
    /// `OnProgram(program *incremental.Program)`.
    fn on_program(&self, program: &crate::incremental::Program);

    /// `WatchBackend()` — Go discovers this capability via the
    /// `testing.(watchmanager.CommandLineTestingWithWatchBackend)` type
    /// assertion in `createWatcher`. Rust cannot downcast `dyn
    /// CommandLineTesting`, so the optional extension is a defaulted
    /// method: `None` is Go's failed assertion; test types that supply a
    /// backend override it (typically by implementing
    /// [`tsc_watchmanager::CommandLineTestingWithWatchBackend`] and
    /// delegating).
    fn watch_backend(&self) -> Option<Arc<dyn tsc_watchmanager::WatchBackend>> {
        None
    }
}

/// `NewContentMapperHost` — creates a content mapper host when content
/// mappers are enabled via `--runExternalCode`, spawning mapper processes
/// through the system's `Spawn`. Returns `None` otherwise, in which case no
/// content-mapped files can be loaded. The caller owns the host and must
/// close it when the compilation session ends.
///
/// PORT: Go's `System` is a shared interface reference; callers hold an
/// `Arc<dyn System>` so the spawner can be stored inside the host.
pub fn new_content_mapper_host(
    ctx: &Context,
    sys: &Arc<dyn System>,
    options: &CompilerOptions,
) -> Option<Arc<dyn tsc_contentmapper::host::Host>> {
    if !options.run_external_code.is_true() {
        return None;
    }
    let (diagnostic_locale, _) = tsc_locale::parse(&options.locale);
    struct SysSpawner {
        sys: Arc<dyn System>,
    }
    impl tsc_contentmapper::hostimpl::Spawner for SysSpawner {
        fn spawn(
            &self,
            command: &[String],
            dir: &str,
            stderr: Option<Box<dyn io::Write + Send>>,
        ) -> io::Result<Arc<dyn SpawnedProcess>> {
            self.sys.spawn(command, dir, stderr)
        }
    }
    Some(new_host_with_options(
        ctx,
        Arc::new(SysSpawner { sys: sys.clone() }),
        diagnostic_locale,
        HostOptions {
            logger: new_content_mapper_logger(sys.as_ref()),
        },
    ))
}

/// `type CompileTimes struct`.
#[derive(Clone, Debug, Default)]
pub struct CompileTimes {
    pub config_time: Duration,
    pub parse_time: Duration,
    pub content_mapper_times: Timings,
    pub bind_time: Duration,
    pub check_time: Duration,
    pub total_time: Duration,
    pub emit_time: Duration,
    pub build_info_read_time: Duration,
    pub changes_compute_time: Duration,
}

/// `type CompileAndEmitResult struct`.
pub struct CompileAndEmitResult {
    pub diagnostics: Vec<DiagnosticRef>,
    pub emit_result: EmitResult,
    pub status: ExitStatus,
    /// `times *CompileTimes` — `Rc` shared with the caller, like Go's pointer.
    pub times: std::rc::Rc<std::cell::RefCell<CompileTimes>>,
}
