// Ported from tsc/internal/execute/tsctests/sys.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `testing.T` is dropped: Go's `t.Error`/`t.Run` have no equivalent here;
//   the test-facing methods return values or panic like their Go
//   counterparts, and `runner.rs` reports via `tsc_testutil::Error`.
// - `TestSys` fields that Go mutates through the shared `*TestSys` pointer
//   (`currentWrite`, `programBaselines`, `programIncludeBaselines`,
//   `tracer`, `fsDiffer`) are behind `Mutex`/`SharedBuffer` because the Rust
//   port shares `Arc<TestSys>` across the `tsc::System`/`CommandLineTesting`
//   traits and the runner's `WorkGroup` thread — `System: Send + Sync`.
// - `*strings.Builder` for `currentWrite` becomes [`SharedBuffer`] (an
//   `Arc<Mutex<Vec<u8>>>` + `io::Write`); `sys.Writer()` returns a
//   `SharedWriter` built once from it, so `w == s.Writer()` (Go interface
//   identity) ports as `SharedWriter::ptr_eq` on the stored writer.
// - `fsbaselineutil.FsDiffer` writes raw bytes; `baseline_fs_with_diff`
//   stages into a `Vec<u8>` and decodes with `from_utf8_lossy` into the
//   `String` baseline (same convention as fourslash's statebaseline).
// - `tscInput.files` is `map[string]any` in Go; the port is
//   `BTreeMap<String, vfstest::TestFile>` (strings, byte slices and
//   `vfstest::MapFile`s all convert into `TestFile`).

use std::collections::BTreeMap;
use std::io;
use std::sync::{Arc, LazyLock, Mutex};
use std::time::{Duration, SystemTime};

use rustc_hash::FxHashMap;
use tsc_collections::SyncMap;
use tsc_compiler::emit_host::EmitResult;
use tsc_core::context::Context;
use tsc_locale::Locale;
use tsc_testutil::contentmappertest;
use tsc_testutil::fsbaselineutil::{self, FsDiffer};
use tsc_testutil::harnessutil::{self, FAKE_TS_VERSION};
use tsc_testutil::stringtestutil::dedent;
use tsc_tspath::{self as tspath, CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_tsoptions::generated::declarations::{self, LIB_MAP};
use tsc_tsoptions::value::Value;
use tsc_vfs::vfs::Vfs;
use tsc_vfs::vfstest;
use tsc_watchmanager as watchmanager;

use crate::incremental::{Program, SignatureUpdateKind};
use crate::tsc::{CommandLineTesting, DiagnosticRegistry, SharedWriter, System};
use crate::tsctests::fs::TestFs;
use crate::tsctests::mock_watch_backend::MockWatchBackend;
use crate::tsctests::runner::TscInput;

/// `type FileMap map[string]any` — paths to string contents, byte slices or
/// `vfstest::MapFile` entries (e.g. `vfstest::symlink(target)`).
pub type FileMap = BTreeMap<String, vfstest::TestFile>;

/// `var tscLibPath = "/home/src/tslibs/TS/Lib"`.
pub const TSC_LIB_PATH: &str = "/home/src/tslibs/TS/Lib";

/// `var tscDefaultLibContent = stringtestutil.Dedent(...)`.
static TSC_DEFAULT_LIB_CONTENT: LazyLock<String> = LazyLock::new(|| {
    String::from_utf8(dedent(
        b"/// <reference no-default-lib=\"true\"/>\n\
          interface Boolean {}\n\
          interface Function {}\n\
          interface CallableFunction {}\n\
          interface NewableFunction {}\n\
          interface IArguments {}\n\
          interface Number { toExponential: any; }\n\
          interface Object {}\n\
          interface RegExp {}\n\
          interface String { charAt: any; }\n\
          interface Array<T> { length: number; [n: number]: T; }\n\
          interface ReadonlyArray<T> {}\n\
          interface SymbolConstructor {\n\
          \x20   (desc?: string | number): symbol;\n\
          \x20   for(name: string): symbol;\n\
          \x20   readonly toStringTag: symbol;\n\
          }\n\
          declare var Symbol: SymbolConstructor;\n\
          interface Symbol {\n\
          \x20   readonly [Symbol.toStringTag]: string;\n\
          }\n\
          declare const console: { log(msg: any): void; };\n",
    ))
    .expect("dedent produces valid utf-8")
});

/// `getTestLibPathFor`.
pub fn get_test_lib_path_for(lib_name: &str) -> String {
    let lib_file = match LIB_MAP.get(lib_name) {
        Some(Value::Str(s)) => s.clone(),
        _ => format!("lib.{lib_name}.d.ts"),
    };
    format!("{TSC_LIB_PATH}/{lib_file}")
}

/// `type TestClock struct` — the fake clock shared by the test fs and
/// `TestSys::now`/`since_start`.
pub struct TestClock {
    start: SystemTime,
    now: Mutex<Option<SystemTime>>,
}

impl TestClock {
    /// `&TestClock{start: time.Now()}`.
    pub fn new() -> TestClock {
        TestClock {
            start: SystemTime::now(),
            now: Mutex::new(None),
        }
    }

    /// `(*TestClock) Now`.
    pub fn now(&self) -> SystemTime {
        let mut now = self.now.lock().unwrap_or_else(|e| e.into_inner());
        // Simulate some time passing.
        let next = now.unwrap_or(self.start) + Duration::from_secs(1);
        *now = Some(next);
        next
    }

    /// `(*TestClock) SinceStart`.
    pub fn since_start(&self) -> Duration {
        self.now()
            .duration_since(self.start)
            .unwrap_or_default()
    }
}

impl Default for TestClock {
    fn default() -> Self {
        Self::new()
    }
}

/// `TestClock` doubles as the `vfstest.Clock`.
impl vfstest::Clock for TestClock {
    fn now(&self) -> SystemTime {
        TestClock::now(self)
    }

    fn since_start(&self) -> Duration {
        TestClock::since_start(self)
    }
}

/// `SharedBuffer` — Go's `*strings.Builder` for `currentWrite`: a shared
/// byte sink that `Writer()`/`ErrorWriter()` write through and the
/// baseline/output code reads and resets.
#[derive(Clone, Default)]
pub struct SharedBuffer {
    inner: Arc<Mutex<Vec<u8>>>,
}

impl SharedBuffer {
    pub fn new() -> SharedBuffer {
        SharedBuffer::default()
    }

    /// `strings.Builder.String` — lossy, since `io::Write` may deliver
    /// bytes (the builders only ever hold UTF-8 text in practice).
    pub fn string(&self) -> String {
        String::from_utf8_lossy(&self.inner.lock().unwrap_or_else(|e| e.into_inner())).into_owned()
    }

    /// `strings.Builder.Reset`.
    pub fn reset(&self) {
        self.inner.lock().unwrap_or_else(|e| e.into_inner()).clear();
    }

    /// `strings.Builder.WriteString`.
    pub fn write_string(&self, s: &str) {
        self.inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .extend_from_slice(s.as_bytes());
    }
}

impl io::Write for SharedBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.inner
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// `NewTscSystem`.
pub fn new_tsc_system(
    files: FileMap,
    case_sensitivity: CaseSensitivity,
    cwd: RootedDirectoryPath,
) -> TestSys {
    let clock = Arc::new(TestClock::new());
    let inner = vfstest::from_map_with_clock(files, case_sensitivity, clock.clone());
    let fs = Arc::new(TestFs::new(inner.clone()));
    let current_write = SharedBuffer::new();
    let writer = SharedWriter::new(current_write.clone());
    // `sys.fsDiffer` is wired to `sys.fs.FS` — the *inner* vfs (the
    // `iovfs.FsWithSys`), not the `TestFs` decorator (whose `as_fs_with_sys`
    // mirrors Go's failed `.(iovfs.FsWithSys)` assertion).
    let default_libs_fs = fs.clone();
    let fs_differ = FsDiffer::new(
        inner.clone(),
        Some(Box::new(move || default_libs_fs.default_libs())),
        fs.written_files.clone(),
    );
    let mock_watch_backend = crate::tsctests::mock_watch_backend::new_mock_watch_backend();
    {
        let fs_for_dir_exists = inner.clone();
        mock_watch_backend.set_directory_exists(move |path: &RootedDirectoryPath| {
            fs_for_dir_exists.directory_exists(path)
        });
        mock_watch_backend.set_case_sensitivity(case_sensitivity);
    }
    TestSys {
        current_write,
        writer,
        program_baselines: Mutex::new(String::new()),
        program_include_baselines: Mutex::new(String::new()),
        tracer: Arc::new(Mutex::new(harnessutil::new_tracer_for_baselining(
            cwd.clone(),
            case_sensitivity,
        ))),
        fs_differ: Mutex::new(fs_differ),
        for_incremental_correctness: false,
        mock_watch_backend,
        fs,
        default_library_path: RootedDirectoryPath::default(),
        cwd,
        env: FxHashMap::default(),
        output_is_tty: true,
        clock,
        diagnostic_registry: Arc::new(DiagnosticRegistry::default()),
    }
}

/// `GetFileMapWithBuild`.
pub fn get_file_map_with_build(mut files: FileMap, command_line_args: &[String]) -> FileMap {
    let input = TscInput {
        files: files.clone(),
        ..Default::default()
    };
    let sys = new_test_sys(&input, false);
    let sys_dyn: Arc<dyn System> = sys.clone();
    let testing: Arc<dyn CommandLineTesting> = sys.clone();
    crate::command_line(&Context::background(), &sys_dyn, command_line_args, Some(testing));
    sys.fs.written_files.range(|file_name: RootedFilePath| {
        if let Some(text) = sys.fs_from_file_map().read_file(&file_name) {
            files.insert(file_name.as_string().to_string(), vfstest::TestFile::from(text));
        }
        true
    });
    files
}

/// `newTestSys`.
pub fn new_test_sys(tsc_input: &TscInput, for_incremental_correctness: bool) -> Arc<TestSys> {
    let cwd = if tsc_input.cwd.is_empty() {
        "/home/src/workspaces/project".to_string()
    } else {
        tsc_input.cwd.clone()
    };
    let mut lib_path = TSC_LIB_PATH.to_string();
    if !tsc_input.windows_style_root.is_empty() {
        lib_path = format!("{}{}", tsc_input.windows_style_root, &TSC_LIB_PATH[1..]);
    }
    let case_sensitivity = if tsc_input.ignore_case {
        CaseSensitivity::CaseInsensitive
    } else {
        CaseSensitivity::CaseSensitive
    };
    let mut sys = new_tsc_system(
        tsc_input.files.clone(),
        case_sensitivity,
        tspath::rooted_directory_path_from_normalized(&cwd),
    );
    sys.default_library_path = tspath::to_rooted_directory_path(&lib_path, &sys.cwd);
    if let Some(output_is_tty) = tsc_input.output_is_tty {
        sys.output_is_tty = output_is_tty;
    }
    sys.env = tsc_input.env.clone();
    sys.for_incremental_correctness = for_incremental_correctness;

    // Ensure the default library file is present
    sys.ensure_lib_path_exists("lib.d.ts");
    for &target in TARGETS_WITH_LIBS {
        if let Some(lib_file) = declarations::target_to_lib_map(target) {
            sys.ensure_lib_path_exists(lib_file);
        }
    }
    for value in LIB_MAP.values() {
        let Value::Str(lib_file) = value else {
            unreachable!()
        };
        sys.ensure_lib_path_exists(lib_file);
    }
    Arc::new(sys)
}

/// `tsoptions.TargetToLibMap()` iterated over every `ScriptTarget` — Go
/// iterates the `map[ScriptTarget]string` (in random order); the port walks
/// the enum discriminants, which is deterministic.
const TARGETS_WITH_LIBS: &[tsc_core::options_generated::ScriptTarget] = {
    use tsc_core::options_generated::ScriptTarget::*;
    &[
        ES5, ES2015, ES2016, ES2017, ES2018, ES2019, ES2020, ES2021, ES2022, ES2023, ES2024,
        ES2025, ES2026, ESNext, JSON,
    ]
};

/// `type TestSys struct`.
pub struct TestSys {
    /// `fs` — the `*testFs` decorator over the `vfstest` fs.
    pub fs: Arc<TestFs>,
    /// `currentWrite` — the shared output buffer `Writer`/`ErrorWriter`
    /// append to (`sys.currentWrite.String()`/`Reset()` in tests).
    pub current_write: SharedBuffer,
    /// `mockWatchBackend`.
    pub mock_watch_backend: Arc<MockWatchBackend>,
    /// `forIncrementalCorrectness` — read by test `edit` closures.
    pub for_incremental_correctness: bool,
    /// `defaultLibraryPath`.
    pub default_library_path: RootedDirectoryPath,
    /// `env`.
    pub env: FxHashMap<String, String>,

    /// `programBaselines`.
    program_baselines: Mutex<String>,
    /// `programIncludeBaselines`.
    program_include_baselines: Mutex<String>,
    /// `tracer` — `Arc` so the `GetTrace` closure (which is `'static`) can
    /// hold a reference.
    tracer: Arc<Mutex<harnessutil::TracerForBaselining>>,
    /// `fsDiffer`.
    fs_differ: Mutex<FsDiffer>,
    /// The `SharedWriter` built on `current_write` once, so Go's
    /// `w == s.Writer()` pointer comparison ports as `ptr_eq` against it.
    writer: SharedWriter,
    /// `cwd`.
    cwd: RootedDirectoryPath,
    /// `outputIsTTY`.
    output_is_tty: bool,
    /// `clock`.
    clock: Arc<TestClock>,
    diagnostic_registry: Arc<DiagnosticRegistry>,
}

impl TestSys {
    /// `fsFromFileMap` — `s.fsDiffer.FS`: the inner `iovfs.FsWithSys`.
    pub fn fs_from_file_map(&self) -> Arc<dyn Vfs> {
        self.fs.inner.clone()
    }

    /// `mapFs` — `s.fsDiffer.MapFs()`.
    pub fn with_map_fs<R>(&self, f: impl FnOnce(&vfstest::MapFs) -> R) -> R {
        self.fs_differ
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .with_map_fs(f)
    }

    /// `fsDiffer` accessor (`&mut` is through the lock).
    pub fn fs_differ(&self) -> &Mutex<FsDiffer> {
        &self.fs_differ
    }

    /// `ensureLibPathExists`.
    fn ensure_lib_path_exists(&self, path: &str) {
        let file_name = self.default_library_path.resolve_file(path);
        if self.fs_from_file_map().read_file(&file_name).is_none() {
            let default_libs = self.fs.default_libs_or_init();
            default_libs.add(file_name.as_path());
            if let Err(err) = self
                .fs_from_file_map()
                .write_file(&file_name, &TSC_DEFAULT_LIB_CONTENT)
            {
                panic!("Failed to write default library file: {err}");
            }
        }
    }

    /// `writeHeaderToBaseline`.
    fn write_header_to_baseline(&self, builder: &mut String, program: &Program) {
        if !builder.is_empty() {
            builder.push('\n');
        }

        let config_file_path = &program.options().config_file_path;
        if !config_file_path.as_string().is_empty() {
            match self
                .fs()
                .case_sensitivity()
                .relative_path_from_directory(&self.cwd, config_file_path)
            {
                Some(relative_path) => builder.push_str(relative_path.as_string()),
                None => builder.push_str(config_file_path.as_string()),
            }
            builder.push_str("::\n");
        }
    }

    /// `baselinePrograms` — appends the program baselines and returns the
    /// include-reason complaints ("" when none), which Go appends to
    /// `unexpectedDiff`.
    pub(crate) fn baseline_programs(&self, baseline: &mut String, header: &str) -> String {
        {
            let mut program_baselines =
                self.program_baselines.lock().unwrap_or_else(|e| e.into_inner());
            baseline.push_str(&program_baselines);
            program_baselines.clear();
        }
        let mut result = String::new();
        let mut include_baselines = self
            .program_include_baselines
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        if !include_baselines.is_empty() {
            result += &format!(
                "\n\n{header}\n!!! Include reasons expectations don't match pls review!!!\n"
            );
            result += &include_baselines;
            include_baselines.clear();
            baseline.push_str(&result);
        }
        result
    }

    /// `serializeState`.
    pub(crate) fn serialize_state(&self, baseline: &mut String) {
        self.baseline_output(baseline);
        self.baseline_fs_with_diff(baseline);
        // todo watch
        // this.serializeWatches(baseline);
        // this.timeoutCallbacks.serialize(baseline);
        // this.immediateCallbacks.serialize(baseline);
        // this.pendingInstalls.serialize(baseline);
        // this.service?.baseline();
    }

    /// `baselineOutput`.
    fn baseline_output(&self, baseline: &mut String) {
        baseline.push_str("\nOutput::\n");
        baseline.push_str(&self.get_output(false));
    }

    /// `getOutput`.
    pub(crate) fn get_output(&self, for_comparing: bool) -> String {
        let output = self.current_write.string();
        let lines: Vec<&str> = output.split('\n').collect();
        let mut transformer = OutputSanitizer {
            for_comparing,
            lines,
            index: 0,
            output_lines: Vec::new(),
        };
        transformer.transform_lines()
    }

    /// `clearOutput`.
    pub fn clear_output(&self) {
        self.current_write.reset();
        self.tracer
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .reset();
    }

    /// `baselineFSwithDiff`.
    pub(crate) fn baseline_fs_with_diff(&self, baseline: &mut String) {
        let mut buf = Vec::new();
        self.fs_differ
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .baseline_fs_with_diff(&mut buf);
        baseline.push_str(&String::from_utf8_lossy(&buf));
    }

    /// `writeFileNoError`.
    pub fn write_file_no_error(&self, path: &str, content: &str) {
        let file_path = tspath::to_rooted_file_path(path, &self.current_directory());
        if let Err(err) = self.fs_from_file_map().write_file(&file_path, content) {
            panic!("{err}");
        }
    }

    /// `removeNoError`.
    pub fn remove_no_error(&self, path: &str) {
        let rooted = tspath::to_rooted_path(path, &self.current_directory());
        if let Err(err) = self.fs_from_file_map().remove(&rooted) {
            panic!("{err}");
        }
    }

    /// `readFileNoError`.
    pub fn read_file_no_error(&self, path: &str) -> String {
        let file_path = tspath::to_rooted_file_path(path, &self.current_directory());
        match self.fs_from_file_map().read_file(&file_path) {
            Some(content) => content,
            None => panic!("File not found: {path}"),
        }
    }

    /// `renameFileNoError`.
    pub fn rename_file_no_error(&self, old_path: &str, new_path: &str) {
        self.write_file_no_error(new_path, &self.read_file_no_error(old_path));
        self.remove_no_error(old_path);
    }

    /// `replaceFileText` — replaces the first occurrence.
    pub fn replace_file_text(&self, path: &str, old_text: &str, new_text: &str) {
        let content = self.read_file_no_error(path);
        self.write_file_no_error(path, &content.replacen(old_text, new_text, 1));
    }

    /// `replaceFileTextAll`.
    pub fn replace_file_text_all(&self, path: &str, old_text: &str, new_text: &str) {
        let content = self.read_file_no_error(path);
        self.write_file_no_error(path, &content.replace(old_text, new_text));
    }

    /// `appendFile`.
    pub fn append_file(&self, path: &str, text: &str) {
        let content = self.read_file_no_error(path);
        self.write_file_no_error(path, &(content + text));
    }

    /// `prependFile`.
    pub fn prepend_file(&self, path: &str, text: &str) {
        let content = self.read_file_no_error(path);
        self.write_file_no_error(path, &(text.to_string() + &content));
    }
}

impl System for TestSys {
    /// `Now`.
    fn now(&self) -> SystemTime {
        self.clock.now()
    }

    /// `SinceStart`.
    fn since_start(&self) -> Duration {
        self.clock.since_start()
    }

    /// `FS`.
    fn fs(&self) -> Arc<dyn Vfs> {
        self.fs.clone()
    }

    /// `DefaultLibraryPath`.
    fn default_library_path(&self) -> RootedDirectoryPath {
        self.default_library_path.clone()
    }

    /// `GetCurrentDirectory`.
    fn current_directory(&self) -> RootedDirectoryPath {
        self.cwd.clone()
    }

    /// `Writer`.
    fn writer(&self) -> SharedWriter {
        self.writer.clone()
    }

    /// `ErrorWriter`.
    fn error_writer(&self) -> SharedWriter {
        self.writer.clone()
    }

    /// `WriteOutputIsTTY`.
    fn write_output_is_tty(&self) -> bool {
        self.output_is_tty
    }

    /// `GetWidthOfTerminal`.
    fn width_of_terminal(&self) -> usize {
        if let Some(width_str) = self.environment_variable("TS_TEST_TERMINAL_WIDTH") {
            if !width_str.is_empty() {
                // `core.Must(strconv.Atoi(widthStr))`.
                return width_str.parse().expect("TS_TEST_TERMINAL_WIDTH must be an int");
            }
        }
        0
    }

    /// `GetEnvironmentVariable`.
    fn environment_variable(&self, name: &str) -> Option<String> {
        self.env.get(name).cloned()
    }

    /// `Spawn` — serves the fake content mappers in-process (see
    /// `contentmappertest`), so tests exercise the full IPC stack without
    /// spawning a subprocess.
    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn io::Write + Send>>,
    ) -> io::Result<Arc<dyn tsc_contentmapper::hostimpl::SpawnedProcess>> {
        contentmappertest::new_spawner().spawn(command, dir, stderr)
    }

    fn diagnostic_registry(&self) -> &Arc<DiagnosticRegistry> {
        &self.diagnostic_registry
    }
}

impl CommandLineTesting for TestSys {
    /// `OnEmittedFiles`.
    fn on_emitted_files(&self, result: &EmitResult, mtimes_cache: &SyncMap<PathKey, SystemTime>) {
        for file in &result.emitted_files {
            let file_name = file.as_string();
            let mod_time = self.with_map_fs(|map_fs| map_fs.get_mod_time(file_name));
            {
                let differ = self.fs_differ.lock().unwrap_or_else(|e| e.into_inner());
                if let Some(serialized_diff) = differ.serialized_diff() {
                    if let Some(diff) = serialized_diff.snap.get(file_name) {
                        // Even though written, timestamp was reverted
                        if diff.mtime == mod_time {
                            continue;
                        }
                    }
                }
            }

            // Ensure that the timestamp for emitted files is in the order
            let now = self.now();
            let path = file.as_path();
            if let Err(err) = self
                .fs_from_file_map()
                .chtimes(&path, SystemTime::UNIX_EPOCH, now)
            {
                panic!("Failed to change time for emitted file: {file_name}: {err}");
            }
            // Update the mTime cache in --b mode to store the updated timestamp so tests will behave deteministically when finding newest output
            let path_key = self.fs().case_sensitivity().path_key(&path);
            if mtimes_cache.load(&path_key).is_some() {
                mtimes_cache.store(path_key, now);
            }
        }
    }

    /// `OnListFilesStart`.
    fn on_list_files_start(&self, w: &mut dyn io::Write) {
        let _ = writeln!(w, "{LIST_FILE_START}");
    }

    /// `OnListFilesEnd`.
    fn on_list_files_end(&self, w: &mut dyn io::Write) {
        let _ = writeln!(w, "{LIST_FILE_END}");
    }

    /// `OnStatisticsStart`.
    fn on_statistics_start(&self, w: &mut dyn io::Write) {
        let _ = writeln!(w, "{STATISTICS_START}");
    }

    /// `OnStatisticsEnd`.
    fn on_statistics_end(&self, w: &mut dyn io::Write) {
        let _ = writeln!(w, "{STATISTICS_END}");
    }

    /// `OnBuildStatusReportStart`.
    fn on_build_status_report_start(&self, w: &mut dyn io::Write) {
        let _ = writeln!(w, "{BUILD_STATUS_REPORT_START}");
    }

    /// `OnBuildStatusReportEnd`.
    fn on_build_status_report_end(&self, w: &mut dyn io::Write) {
        let _ = writeln!(w, "{BUILD_STATUS_REPORT_END}");
    }

    /// `OnWatchStatusReportStart`.
    fn on_watch_status_report_start(&self) {
        self.writer()
            .write_text(&format!("{WATCH_STATUS_REPORT_START}\n"));
    }

    /// `OnWatchStatusReportEnd`.
    fn on_watch_status_report_end(&self) {
        self.writer()
            .write_text(&format!("{WATCH_STATUS_REPORT_END}\n"));
    }

    /// `GetTrace`.
    fn get_trace(
        &self,
        w: SharedWriter,
        locale: Locale,
    ) -> Box<dyn Fn(&'static tsc_diagnostics::Message, &[String]) + Send + Sync> {
        let tracer = self.tracer.clone();
        // `w == s.Writer()` — the sys writer enables package-json caching.
        let is_sys_writer = w.ptr_eq(&self.writer);
        Box::new(move |msg: &'static tsc_diagnostics::Message, args: &[String]| {
            w.write_text(&format!("{TRACE_START}\n"));
            // With tsc -b building projects in parallel we cannot serialize the package.json lookup trace
            // so trace as if it wasnt cached
            let str_ = msg.localize(&locale, args);
            let sanitized = tracer
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .sanitize_trace(&str_, is_sys_writer);
            w.write_text(&format!("{sanitized}\n"));
            w.write_text(&format!("{TRACE_END}\n"));
        })
    }

    /// `WatchBackend`.
    fn watch_backend(&self) -> Option<Arc<dyn watchmanager::WatchBackend>> {
        Some(self.mock_watch_backend.clone())
    }

    /// `OnProgram`.
    fn on_program(&self, program: &Program) {
        let mut baselines = self
            .program_baselines
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        self.write_header_to_baseline(&mut baselines, program);

        let testing_data = program.get_testing_data().expect("program testing data");
        baselines.push_str("SemanticDiagnostics::\n");
        for file in program.get_program().source_file_entries() {
            let path_key = file.path();
            if let Some(diagnostics) = testing_data
                .semantic_diagnostics_per_file
                .load(&path_key)
            {
                let old = testing_data
                    .old_program_semantic_diagnostics_per_file
                    .load(&path_key);
                if old.as_ref().is_none_or(|old| !std::rc::Rc::ptr_eq(old, &diagnostics)) {
                    baselines.push_str("*refresh*    ");
                    baselines.push_str(file.file_name().as_string());
                    baselines.push('\n');
                }
            } else {
                baselines.push_str("*not cached* ");
                baselines.push_str(file.file_name().as_string());
                baselines.push('\n');
            }
        }

        // Write signature updates
        baselines.push_str("Signatures::\n");
        for file in program.get_program().source_file_entries() {
            let kind = testing_data
                .updated_signature_kinds
                .borrow()
                .get(&file.path())
                .copied();
            match kind {
                Some(SignatureUpdateKind::ComputedDts) => {
                    baselines.push_str("(computed .d.ts) ");
                    baselines.push_str(file.file_name().as_string());
                    baselines.push('\n');
                }
                Some(SignatureUpdateKind::StoredAtEmit) => {
                    baselines.push_str("(stored at emit) ");
                    baselines.push_str(file.file_name().as_string());
                    baselines.push('\n');
                }
                Some(SignatureUpdateKind::UsedVersion) => {
                    baselines.push_str("(used version)   ");
                    baselines.push_str(file.file_name().as_string());
                    baselines.push('\n');
                }
                None => {}
            }
        }

        let mut files_without_include_reason: Vec<String> = Vec::new();
        let mut file_not_in_program_with_include_reason: Vec<String> = Vec::new();
        let program_ = program.get_program().clone();
        let include_reasons = program_.get_include_reasons();
        for file in program_.source_file_entries() {
            if !include_reasons.contains_key(&file.path()) {
                files_without_include_reason.push(file.path().as_string().to_string());
            }
        }
        for path in include_reasons.keys() {
            if program_.get_source_file_by_path(path).is_none() && !program_.is_missing_path(path) {
                file_not_in_program_with_include_reason.push(path.as_string().to_string());
            }
        }
        if !files_without_include_reason.is_empty()
            || !file_not_in_program_with_include_reason.is_empty()
        {
            let mut include_baselines = self
                .program_include_baselines
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            self.write_header_to_baseline(&mut include_baselines, program);
            include_baselines.push_str(
                "!!! Expected all files to have include reasons\nfilesWithoutIncludeReason::\n",
            );
            for file in &files_without_include_reason {
                include_baselines.push_str("  ");
                include_baselines.push_str(file);
                include_baselines.push('\n');
            }
            include_baselines.push_str("filesNotInProgramWithIncludeReason::\n");
            for file in &file_not_in_program_with_include_reason {
                include_baselines.push_str("  ");
                include_baselines.push_str(file);
                include_baselines.push('\n');
            }
        }
    }
}

/// `fmt.Fprintln` baseline sentinels.
pub(crate) const FAKE_TIME_STAMP: &str = "HH:MM:SS AM";
pub(crate) const FAKE_DURATION: &str = "d.ddds";

pub(crate) const BUILD_STARTING_AT: &str = "build starting at ";
pub(crate) const BUILD_FINISHED_IN: &str = "build finished in ";
pub(crate) const LIST_FILE_START: &str = "!!! List files start";
pub(crate) const LIST_FILE_END: &str = "!!! List files end";
pub(crate) const STATISTICS_START: &str = "!!! Statistics start";
pub(crate) const STATISTICS_END: &str = "!!! Statistics end";
pub(crate) const BUILD_STATUS_REPORT_START: &str = "!!! Build Status Report Start";
pub(crate) const BUILD_STATUS_REPORT_END: &str = "!!! Build Status Report End";
pub(crate) const WATCH_STATUS_REPORT_START: &str = "!!! Watch Status Report Start";
pub(crate) const WATCH_STATUS_REPORT_END: &str = "!!! Watch Status Report End";
pub(crate) const TRACE_START: &str = "!!! Trace start";
pub(crate) const TRACE_END: &str = "!!! Trace end";

/// `type outputSanitizer struct`.
struct OutputSanitizer<'a> {
    for_comparing: bool,
    lines: Vec<&'a str>,
    index: usize,
    output_lines: Vec<String>,
}

/// `englishVersion`/`fakeEnglishVersion`/`czechVersion`/`fakeCzechVersion`.
static ENGLISH_VERSION: LazyLock<String> = LazyLock::new(|| {
    tsc_diagnostics::Version_0.localize(&tsc_locale::DEFAULT, &[tsc_core::version::version()])
});
static FAKE_ENGLISH_VERSION: LazyLock<String> = LazyLock::new(|| {
    tsc_diagnostics::Version_0.localize(&tsc_locale::DEFAULT, &[FAKE_TS_VERSION.to_string()])
});
static CZECH_LOCALE: LazyLock<Locale> =
    LazyLock::new(|| tsc_locale::parse("cs").0);
static CZECH_VERSION: LazyLock<String> = LazyLock::new(|| {
    tsc_diagnostics::Version_0.localize(&CZECH_LOCALE, &[tsc_core::version::version()])
});
static FAKE_CZECH_VERSION: LazyLock<String> = LazyLock::new(|| {
    tsc_diagnostics::Version_0.localize(&CZECH_LOCALE, &[FAKE_TS_VERSION.to_string()])
});

impl<'a> OutputSanitizer<'a> {
    /// `addOutputLine`.
    fn add_output_line(&mut self, s: &str) {
        let mut s = s.replace(
            &format!("'{}'", tsc_core::version::version()),
            &format!("'{FAKE_TS_VERSION}'"),
        );
        s = s.replace(&*ENGLISH_VERSION, &FAKE_ENGLISH_VERSION);
        s = s.replace(&*CZECH_VERSION, &FAKE_CZECH_VERSION);
        let sanitized = fsbaselineutil::sanitize_internal_symbol_name(s.as_bytes());
        self.output_lines
            .push(String::from_utf8_lossy(&sanitized).into_owned());
    }

    /// `sanitizeBuildStatusTimeStamp`.
    fn sanitize_build_status_time_stamp(&self) -> String {
        let status_line = self.lines[self.index];
        let Some(hh_separator) = status_line.find(':') else {
            panic!("Expected timestamp");
        };
        if hh_separator < 2 {
            panic!("Expected timestamp");
        }
        // PORT: Go slices bytes; the timestamp layout is ASCII so the index
        // arithmetic lands on char boundaries.
        format!(
            "{}{}{}",
            &status_line[..hh_separator - 2],
            FAKE_TIME_STAMP,
            &status_line[hh_separator + FAKE_TIME_STAMP.len() - 2..],
        )
    }

    /// `transformLines`.
    fn transform_lines(&mut self) -> String {
        while self.index < self.lines.len() {
            let line = self.lines[self.index];
            if line.starts_with(BUILD_STARTING_AT) {
                if !self.for_comparing {
                    self.add_output_line(&format!("{BUILD_STARTING_AT}{FAKE_TIME_STAMP}"));
                }
                self.index += 1;
                continue;
            }
            if line.starts_with(BUILD_FINISHED_IN) {
                if !self.for_comparing {
                    self.add_output_line(&format!("{BUILD_FINISHED_IN}{FAKE_DURATION}"));
                }
                self.index += 1;
                continue;
            }
            if !self.add_or_skip_lines_for_comparing(LIST_FILE_START, LIST_FILE_END, false, None)
                && !self.add_or_skip_lines_for_comparing(
                    STATISTICS_START,
                    STATISTICS_END,
                    true,
                    None,
                )
                && !self.add_or_skip_lines_for_comparing(TRACE_START, TRACE_END, false, None)
                && !self.add_or_skip_lines_for_comparing(
                    BUILD_STATUS_REPORT_START,
                    BUILD_STATUS_REPORT_END,
                    false,
                    Some(Self::sanitize_build_status_time_stamp),
                )
                && !self.add_or_skip_lines_for_comparing(
                    WATCH_STATUS_REPORT_START,
                    WATCH_STATUS_REPORT_END,
                    false,
                    Some(Self::sanitize_build_status_time_stamp),
                )
            {
                self.add_output_line(line);
                self.index += 1;
            }
        }
        self.output_lines.join("\n")
    }

    /// `addOrSkipLinesForComparing`.
    fn add_or_skip_lines_for_comparing(
        &mut self,
        line_start: &str,
        line_end: &str,
        skip_even_if_not_comparing: bool,
        sanitize_first_line: Option<fn(&Self) -> String>,
    ) -> bool {
        if self.lines[self.index] != line_start {
            return false;
        }
        self.index += 1;
        let mut is_first_line = true;
        while self.index < self.lines.len() {
            if self.lines[self.index] == line_end {
                self.index += 1;
                return true;
            }
            if !self.for_comparing && !skip_even_if_not_comparing {
                let line = self.lines[self.index];
                if is_first_line && sanitize_first_line.is_some() {
                    let sanitized = sanitize_first_line.expect("checked")(self);
                    self.add_output_line(&sanitized);
                    is_first_line = false;
                } else {
                    self.add_output_line(line);
                }
            }
            self.index += 1;
        }
        panic!("Expected lineEnd{line_end} not found after {line_start}");
    }
}
