// Ported from tsc/internal/execute/watcher.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
//
// - `*collections.SyncMap[tspath.PathKey, *cachedSourceFile]` becomes a
//   `thread_local` cache. `ParsedSourceFile` owns a `Vec<Node>` whose nodes
//   contain `Rc`/`Cell` state (`SourceFileData` cells), so it is `!Send +
//   !Sync` and cannot sit inside `WatchCompilerHost` — `CompilerHost`
//   requires `Send + Sync`. Go's `sync.Map` is only accessed on the watch
//   goroutine, which a thread-local models exactly: a cache miss on a new
//   thread just reparses (still correct, only slower). Reassigning
//   `w.sourceFileCache` in Go becomes `SOURCE_FILE_CACHE.clear()`.
// - `Watcher`'s mutable fields use `Cell`/`RefCell`: `DoCycle` runs under
//   `WatchManagerLock`, so all state is single-threaded like Go's `w.mu`
//   regime (the watcher itself is `!Send` because `incremental::Program`
//   contains `Rc`s).
// - Go's `testing.(watchmanager.CommandLineTestingWithWatchBackend)` type
//   assertion becomes `CommandLineTesting::watch_backend()` — a defaulted
//   method returning `None`; implementors supplying a test backend override
//   it (see `tsc_watchmanager::CommandLineTestingWithWatchBackend`).
// - `incremental::Program` / `incremental::new_program` /
//   `incremental::read_build_info_program` are sibling-owned ports; the
//   calls below assume the natural signatures
//   `new_program(Rc<compiler::Program>, Option<Rc<Program>>, Option<Arc<dyn Host>>,
//   Arc<dyn Fn() -> SystemTime + Send + Sync>, bool) -> Rc<Program>` and
//   `read_build_info_program(&Arc<ParsedCommandLine>, reader,
//   &Arc<dyn CompilerHost>) -> Option<Rc<Program>>`.
// - `source_file_cache_load` clones the cached arena (`Vec<Node>`) — Go
//   hands the caller the shared `*ast.SourceFile` pointer, but both Go and
//   Rust callers treat the result as a fresh parse handed to the loader, so
//   a copy is semantically equivalent (only heavier).
// - `w.extendedConfigCache` is still maintained for `parseConfigFile`, but
//   hosts are built with `None` for `extended_config_cache`: the compiler
//   host field requires `Arc<dyn ExtendedConfigCache + Send + Sync>` while
//   `ExtendedConfigCacheEntry` holds `Cell`/`Rc` config ASTs
//   (`TsConfigSourceFile`), and `unsafe_code` is forbidden — so the bound is
//   unmeetable without changing `compiler::host`. PORT(deferred): project
//   references reparse extended configs instead of sharing the cache
//   (semantics preserved, memoization lost).
// - `program.GetProgram().FilesByPath()` is `&FxHashMap<PathKey, NodeId>`;
//   `*ast.SourceFile` access goes through `program.arena_of(id)`.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::io::Write as _;
use std::rc::Rc;
use std::sync::Arc;
use std::time::SystemTime;

use rustc_hash::FxHashMap;
use tsc_ast::diagnostic::new_compiler_diagnostic;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::{SourceFile, get_jsx_implicit_import_base, get_jsx_runtime_import};
use tsc_collections::{OrderedMap, Set, new_set_from_items};
use tsc_compiler::host::{BasicCompilerHost, CompilerHost, new_compiler_host};
use tsc_compiler::program::{ProgramConfig, ProgramHosts, ProgramOptions, reuse_program};
use tsc_contentmapper::ParsedSourceFile;
use tsc_contentmapper::host::{Host as ContentMapperHost, Project, ProjectSpec};
use tsc_core::context::Context;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::scriptkind::ScriptKind;
use tsc_diagnostics as diagnostics;
use tsc_fswatch::EventKind;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tsoptions::tsconfigparsing;
use tsc_tsoptions::value::Value;
use tsc_tspath::{self as tspath, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath};
use tsc_vfs::{cachedvfs, trackingvfs};
use tsc_watchmanager::{
    WatchManager, WatchManagerLock, can_watch_directory, new_dir_watch_set, new_watch_manager,
};

use crate::tsc::{
    self, CommandLineTesting, CompileAndEmitResult, CompileTimes, DiagnosticReporter,
    DiagnosticsReporter, EmitInput, ExtendedConfigCache, System, emit_files_and_report_errors,
};
use crate::tsc_main::get_trace_from_sys;

/// `cachedSourceFile`.
struct CachedSourceFile {
    file: ParsedSourceFile,
    mod_time: SystemTime,
}

// `w.sourceFileCache` — see the file header for why this is a thread-local
// rather than a `SyncMap` field on the host.
thread_local! {
    static SOURCE_FILE_CACHE: RefCell<FxHashMap<PathKey, CachedSourceFile>> =
        RefCell::new(FxHashMap::default());
}

fn source_file_cache_load(path: &PathKey) -> Option<ParsedSourceFile> {
    SOURCE_FILE_CACHE.with(|c| {
        c.borrow().get(path).map(|cached| ParsedSourceFile {
            file: cached.file.file,
            nodes: cached.file.nodes.clone(),
        })
    })
}

fn source_file_cache_mod_time(path: &PathKey) -> Option<SystemTime> {
    SOURCE_FILE_CACHE.with(|c| c.borrow().get(path).map(|cached| cached.mod_time))
}

fn source_file_cache_store(path: PathKey, file: ParsedSourceFile, mod_time: SystemTime) {
    SOURCE_FILE_CACHE.with(|c| {
        c.borrow_mut()
            .insert(path, CachedSourceFile { file, mod_time });
    });
}

fn source_file_cache_delete(path: &PathKey) {
    SOURCE_FILE_CACHE.with(|c| {
        c.borrow_mut().remove(path);
    });
}

fn source_file_cache_contains(path: &PathKey) -> bool {
    SOURCE_FILE_CACHE.with(|c| c.borrow().contains_key(path))
}

/// `w.sourceFileCache = &collections.SyncMap{}` — a fresh map.
fn source_file_cache_reset() {
    SOURCE_FILE_CACHE.with(|c| c.borrow_mut().clear());
}

/// `watchCompilerHost` — a `BasicCompilerHost` that serves unchanged source
/// files from the per-thread cache (`cachedSourceFile`).
struct WatchCompilerHost {
    /// `compiler.CompilerHost` — embedded.
    inner: BasicCompilerHost,
}

impl WatchCompilerHost {
    /// `(h *watchCompilerHost) GetSourceFile` — reparses when the VFS mtime
    /// moved past the cached entry, reusing the cached parse otherwise.
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<ParsedSourceFile> {
        let info = self.inner.fs().stat(&opts.file_name.as_path());

        if let Some(mod_time) = source_file_cache_mod_time(&opts.path_key) {
            if info.as_ref().is_some_and(|i| i.mod_time() == mod_time) {
                return source_file_cache_load(&opts.path_key);
            }
        }

        let file = self.inner.get_source_file(opts);
        match &file {
            Some(file) => {
                if let Some(info) = info {
                    source_file_cache_store(
                        opts.path_key.clone(),
                        ParsedSourceFile {
                            file: file.file,
                            nodes: file.nodes.clone(),
                        },
                        info.mod_time(),
                    );
                }
            }
            None => source_file_cache_delete(&opts.path_key),
        }
        file
    }
}

impl CompilerHost for WatchCompilerHost {
    fn fs(&self) -> &Arc<dyn tsc_vfs::Vfs> {
        self.inner.fs()
    }

    fn default_library_path(&self) -> &RootedDirectoryPath {
        self.inner.default_library_path()
    }

    fn trace(&self, msg: &'static tsc_diagnostics::Message, args: &[String]) {
        self.inner.trace(msg, args)
    }

    /// Unused through the trait — the watcher's single-file path calls the
    /// inherent [`WatchCompilerHost::get_source_file`]; the trait impl
    /// delegates for completeness.
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<ParsedSourceFile> {
        WatchCompilerHost::get_source_file(self, opts)
    }

    fn get_content_mapped_source_files(
        &self,
        parse_options: &SourceFileParseOptions,
        mapper: &Arc<tsc_contentmapper::Mapper>,
    ) -> Result<tsc_contentmapper::SourceFiles, tsc_contentmapper::Error> {
        self.inner
            .get_content_mapped_source_files(parse_options, mapper)
    }

    fn content_mapper_project(&self) -> Option<&Arc<dyn Project>> {
        self.inner.content_mapper_project()
    }

    fn get_resolved_project_reference(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<ParsedCommandLine>> {
        self.inner.get_resolved_project_reference(file_name, path)
    }
}

/// `type Watcher struct`.
pub(crate) struct Watcher {
    sys: Arc<dyn System>,
    config_file_name: Option<RootedFilePath>,
    config: RefCell<Arc<ParsedCommandLine>>,
    compiler_options_from_command_line: Option<CompilerOptions>,
    command_line_raw: Option<OrderedMap<String, Value>>,
    report_diagnostic: DiagnosticReporter,
    report_error_summary: DiagnosticsReporter,
    report_watch_status: DiagnosticReporter,
    testing: Option<Arc<dyn CommandLineTesting>>,

    // contentMapperHost transforms content-mapped files; it is created once per watch session (when
    // enabled) and reused across cycles. It closes itself when the session context is cancelled (see
    // contentmapper.New).
    content_mapper_host: RefCell<Option<Arc<dyn ContentMapperHost>>>,
    content_mapper_project: RefCell<Option<Arc<dyn Project>>>,

    program: RefCell<Option<Rc<crate::incremental::Program>>>,
    extended_config_cache: RefCell<Option<Arc<ExtendedConfigCache>>>,
    config_modified: Cell<bool>,
    config_has_errors: Cell<bool>,
    config_file_paths: RefCell<Vec<RootedFilePath>>,

    wm: Arc<WatchManager>,
    /// `seenFiles` — all build dependencies (for event filtering).
    seen_files: RefCell<Set<PathKey>>,
    config_mtimes: RefCell<HashMap<RootedFilePath, SystemTime>>,
    watch_set_dirty: Cell<bool>,
    // forceFullRebuild records a reason that requires a full NewProgram rebuild
    // (e.g. an event overflow, a mid-cycle watch failure, a newly appeared
    // project file, or a changed non-source dependency). Unlike watchSetDirty,
    // which is only raised to recheck wildcard roots and may be cleared once the
    // file set is confirmed unchanged, this flag is preserved until a full
    // rebuild actually runs so the single-file fast path cannot silently reuse a
    // stale program.
    force_full_rebuild: Cell<bool>,
    program_ready: Cell<bool>,

    // Test-only observability of which build path was taken.
    fast_path_builds: Cell<i32>,
    full_builds: Cell<i32>,
}

impl tsc::Watcher for Watcher {
    fn do_cycle(&self) {
        Watcher::do_cycle(self)
    }
}

/// `createWatcher`.
pub(crate) fn create_watcher(
    sys: &Arc<dyn System>,
    config_parse_result: Arc<ParsedCommandLine>,
    compiler_options_from_command_line: Option<&CompilerOptions>,
    command_line_raw: Option<OrderedMap<String, Value>>,
    report_diagnostic: DiagnosticReporter,
    report_error_summary: DiagnosticsReporter,
    testing: Option<Arc<dyn CommandLineTesting>>,
) -> Arc<Watcher> {
    let case_sensitivity = sys.fs().case_sensitivity();
    let fs = sys.fs();
    let wm = new_watch_manager(
        Box::new(sys.writer()),
        move |dir: &RootedDirectoryPath| fs.directory_exists(dir),
        case_sensitivity,
    );
    // PORT: Go's `testing.(CommandLineTestingWithWatchBackend)` assertion.
    if let Some(backend) = testing.as_ref().and_then(|t| t.watch_backend()) {
        wm.set_backend(backend);
    }
    let w = Arc::new(Watcher {
        sys: sys.clone(),
        config_file_name: config_parse_result
            .config_file
            .as_ref()
            .map(|cf| cf.file_name().clone()),
        config: RefCell::new(config_parse_result.clone()),
        compiler_options_from_command_line: compiler_options_from_command_line.cloned(),
        command_line_raw,
        report_diagnostic,
        report_error_summary,
        report_watch_status: tsc::create_watch_status_reporter(
            sys,
            config_parse_result.locale().clone(),
            config_parse_result.compiler_options(),
            testing.as_ref(),
        ),
        testing,
        content_mapper_host: RefCell::new(None),
        content_mapper_project: RefCell::new(None),
        program: RefCell::new(None),
        extended_config_cache: RefCell::new(None),
        config_modified: Cell::new(false),
        config_has_errors: Cell::new(false),
        config_file_paths: RefCell::new(Vec::new()),
        wm,
        seen_files: RefCell::new(Set::new()),
        config_mtimes: RefCell::new(HashMap::new()),
        watch_set_dirty: Cell::new(false),
        force_full_rebuild: Cell::new(false),
        program_ready: Cell::new(false),
        fast_path_builds: Cell::new(0),
        full_builds: Cell::new(0),
    });
    w
}

impl Watcher {
    /// `(w *Watcher) start` — creates the content mapper host/project, primes
    /// the build-info program, then runs the initial build and (outside test
    /// mode) enters the watch loop.
    pub(crate) fn start(self: &Arc<Watcher>, ctx: &Context) {
        *self.content_mapper_host.borrow_mut() = tsc::new_content_mapper_host(
            ctx,
            &self.sys,
            self.config
                .borrow()
                .compiler_options()
                .expect("compiler options"),
        );
        // `defer w.contentMapperHost.Close()` — but only when not testing
        // (the test harness owns the host lifetime).
        let _host_guard = if self.testing.is_none() {
            self.content_mapper_host.borrow().clone().map(|host| {
                crate::util::Defer::new(move || {
                    let _ = host.close();
                })
            })
        } else {
            None
        };
        let config = self.config.borrow().clone();
        self.replace_content_mapper_project(&config);

        let mut lock = self.wm.lock();
        *self.extended_config_cache.borrow_mut() = Some(Arc::new(ExtendedConfigCache::default()));
        let host: Arc<dyn CompilerHost> = Arc::new(new_compiler_host(
            self.sys.fs(),
            self.sys.default_library_path(),
            // PORT(deferred): `w.extendedConfigCache` — see the file header.
            None,
            Some(get_trace_from_sys(
                &self.sys,
                self.config.borrow().locale().clone(),
                self.testing.as_ref(),
            )),
            self.content_mapper_project.borrow().clone(),
        ));
        *self.program.borrow_mut() = crate::incremental::read_build_info_program(
            &self.config.borrow(),
            crate::incremental::new_build_info_reader(host.clone()),
            &host,
        );

        if let Some(config_file_name) = &self.config_file_name {
            let mut paths = vec![config_file_name.clone()];
            paths.extend(self.config.borrow().extended_source_files().iter().cloned());
            *self.config_file_paths.borrow_mut() = paths;
        }

        if self
            .sys
            .environment_variable("TS_WATCH_DEBUG")
            .map(|v| !v.is_empty())
            .unwrap_or(false)
        {
            *self.wm.debug_log.lock().unwrap() = Some(Box::new(self.sys.writer()));
        }

        if self.testing.is_none() {
            lock.ensure_default_backend();
        }

        (self.report_watch_status)(&new_compiler_diagnostic(
            &diagnostics::Starting_compilation_in_watch_mode,
            &[] as &[String],
        ));
        self.watch_set_dirty.set(true);
        if self.do_build(&mut lock).is_err() {
            self.wm.force_overflow();
        }
        drop(lock);

        if self.testing.is_none() {
            // The content mapper host closes itself when ctx is cancelled (see contentmapper.New).
            let w = self.clone();
            self.wm.run_loop(ctx, move || w.do_cycle());
        }
    }

    /// `(w *Watcher) replaceContentMapperProject`.
    fn replace_content_mapper_project(&self, config: &ParsedCommandLine) {
        let host = self.content_mapper_host.borrow().clone();
        let Some(host) = host else { return };
        let project = host.project(&ProjectSpec {
            config_file_name: config.config_name().clone(),
            mappers: config.content_mappers().to_vec(),
            compiler_options: config.compiler_options().cloned().map(Arc::new),
        });
        // Go closes the old project before installing the new one.
        let old = self.content_mapper_project.borrow_mut().take();
        if let Some(old) = old {
            let _ = old.close();
        }
        *self.content_mapper_project.borrow_mut() = project;
    }

    /// `(w *Watcher) contentMapperWatchedFiles`.
    fn content_mapper_watched_files(&self) -> Vec<RootedFilePath> {
        let mut files = Vec::new();
        {
            let config = self.config.borrow();
            for mapper in config.content_mappers() {
                if !mapper.package_directory.as_string().is_empty()
                    && mapper.contribution_id.is_empty()
                {
                    files.push(mapper.package_directory.resolve_file("package.json"));
                }
            }
        }
        if let Some(project) = self.content_mapper_project.borrow().clone() {
            match project.watched_files() {
                Ok(dynamic_files) => files.extend(dynamic_files),
                Err(err) => {
                    (self.report_diagnostic)(
                        &tsc_compiler::file_loader::content_mapper_project_diagnostic(&err),
                    );
                    files.sort();
                    files.dedup();
                    return files;
                }
            }
        }
        files.sort();
        files.dedup();
        files
    }

    /// `(w *Watcher) computeDesiredWatches`.
    fn compute_desired_watches(
        &self,
        seen_file_paths: &[RootedPath],
    ) -> FxHashMap<RootedDirectoryPath, bool> {
        let mut desired_dirs: FxHashMap<RootedDirectoryPath, bool> = FxHashMap::default();

        {
            let config = self.config.borrow();
            // Wildcard directories from tsconfig (recursive or non-recursive)
            if config.config_file.is_some() {
                if let Some(wildcard_directories) = config.wildcard_directories() {
                    for (dir, recursive) in wildcard_directories {
                        let real_dir = tspath::rooted_directory_path_from_path(
                            self.sys.fs().realpath(&dir.as_path()),
                        );
                        desired_dirs.insert(real_dir, *recursive);
                    }
                }
            }

            // For no-config CLI mode, ensure CWD is watched
            if config.config_file.is_none() && desired_dirs.is_empty() {
                let dir = tspath::rooted_directory_path_from_path(
                    self.sys.fs().realpath(&config.base_directory().as_path()),
                );
                desired_dirs.insert(dir, false);
            }
        }

        // Config file parent directories as non-recursive watches
        for cfg_path in self.config_file_paths.borrow().iter() {
            let real_path = self.sys.fs().realpath(&cfg_path.as_path());
            let dir = real_path.directory();
            desired_dirs.entry(dir).or_insert(false);
        }

        // For no-config CLI mode, also watch the CLI-specified files' directories
        {
            let config = self.config.borrow();
            if config.config_file.is_none() {
                for file_name in config.file_names() {
                    let real_path = self.sys.fs().realpath(&file_name.as_path());
                    let dir = real_path.directory();
                    desired_dirs.entry(dir).or_insert(false);
                }
            }
        }

        // Add parent directories for seen files not covered by existing dir watches.
        // Resolve ancestor fallbacks first so coverage checks use final dirs.
        let resolved_dirs = self.wm.resolve_desired_dirs(desired_dirs);

        let mut coverage = new_dir_watch_set(self.case_sensitivity());
        for (dir, recursive) in resolved_dirs {
            coverage.set(dir, recursive);
        }
        let program_rc = self.program.borrow().clone().expect("program set");
        let program = program_rc.get_program().clone();
        let program_files = program.files_by_path();
        let case_sensitivity = self.case_sensitivity();
        let root_files = new_set_from_items(
            self.config
                .borrow()
                .file_names()
                .iter()
                .map(|file_name| case_sensitivity.path_key(&file_name.as_path())),
        );
        for file_path in seen_file_paths {
            let dir = file_path.directory();
            if coverage.covered(&dir) {
                continue;
            }
            // Seen files mix program files with lookup locations. Only lookups keep the depth check, so an imported
            // file outside the tsconfig directory (say /shared next to /app) is still watched. A root file is not in
            // the program while it is missing, but its directory stays watched so that recreating it rebuilds.
            let p = case_sensitivity.path_key(file_path);
            let is_program_file = program_files.contains_key(&p);
            if is_program_file || root_files.has(&p) || can_watch_directory(&dir) {
                coverage.set(dir, false);
            }
        }

        // Re-resolve in case newly added dirs don't exist
        self.wm.resolve_desired_dirs(coverage.dirs())
    }

    /// `(w *Watcher) reconcileWatches`.
    fn reconcile_watches(
        &self,
        lock: &mut WatchManagerLock<'_>,
        seen_file_paths: &[RootedPath],
    ) -> Result<(), tsc_fswatch::Error> {
        let desired_dirs = self.compute_desired_watches(seen_file_paths);
        lock.reconcile_watches(desired_dirs)
    }

    fn case_sensitivity(&self) -> tspath::CaseSensitivity {
        self.sys.fs().case_sensitivity()
    }

    /// `(w *Watcher) DoCycle`.
    pub fn do_cycle(&self) {
        let mut lock = self.wm.lock();

        let (changed_paths, overflow) = self.wm.drain_events();
        let changed_paths = changed_paths.unwrap_or_default();
        let has_events = !changed_paths.is_empty() || overflow;

        if self.recheck_ts_config(self.content_mapper_manifest_changed(&changed_paths)) {
            return;
        }

        if has_events && !overflow && !self.config_modified.get() {
            // Filter fswatch events against known dependencies
            if self.is_relevant_change(&changed_paths, &lock) {
                self.evict_changed_source_files(&changed_paths);
                let case_sensitivity = self.sys.fs().case_sensitivity();
                let program_rc = self.program.borrow().clone().expect("program set");
                let program = program_rc.get_program().clone();
                let program_files = program.files_by_path();
                let content_mapper_watched_files = new_set_from_items(
                    self.content_mapper_watched_files()
                        .iter()
                        .map(|file_name| case_sensitivity.path_key(&file_name.as_path())),
                );
                let mut content_mapper_config_changed = false;
                for event_path in changed_paths.keys() {
                    if self
                        .sys
                        .fs()
                        .directory_exists(&tspath::rooted_directory_path_from_path(
                            event_path.clone(),
                        ))
                    {
                        // A watched directory changed: the wildcard file set may have
                        // changed, so reload file names on the next build.
                        self.watch_set_dirty.set(true);
                        continue;
                    }
                    let p = self.case_sensitivity().path_key(event_path);
                    if content_mapper_watched_files.has(&p) {
                        content_mapper_config_changed = true;
                        self.force_full_rebuild.set(true);
                    }
                    {
                        let config = self.config.borrow();
                        if config.config_file.is_some()
                            && config.possibly_matches_file_name(
                                &tspath::rooted_file_path_from_path(event_path.clone()),
                            )
                            && !self.seen_files.borrow().has(&p)
                        {
                            // A file that matches the project but was not previously
                            // seen appeared: a structural change that requires a full
                            // rebuild, not the single-file fast path.
                            self.watch_set_dirty.set(true);
                            self.force_full_rebuild.set(true);
                            continue;
                        }
                    }
                    if let Some(&source_file) = program_files.get(&p) {
                        let arena = program.arena_of(source_file);
                        if !arena[source_file]
                            .as_source_file()
                            .content_mapper()
                            .is_empty()
                        {
                            // Canonical mapped files must be transformed again, and supplemental paths are failed
                            // physical lookups reserved for virtual files. Neither can use single-file AST reuse.
                            self.force_full_rebuild.set(true);
                        }
                    } else if self.seen_files.borrow().has(&p) {
                        // A non-source build dependency changed. Such dependencies
                        // (e.g. package.json or a previously-missing module path) are
                        // tracked in seenFiles but are not program source files, so a
                        // missing sourceFileCache entry would not account for them.
                        // Module resolution may now differ, so the single-file fast
                        // path is unsafe; force a full rebuild.
                        self.force_full_rebuild.set(true);
                    }
                }
                if content_mapper_config_changed {
                    if let Some(project) = self.content_mapper_project.borrow().clone() {
                        if project.refresh().is_err() {
                            (self.report_diagnostic)(&new_compiler_diagnostic(
                                &diagnostics::The_content_mapper_process_could_not_be_started_or_initialized,
                                &[] as &[String],
                            ));
                            return;
                        }
                    }
                }
            } else {
                self.dlog(format_args!(
                    "[watch] DoCycle: {} event(s) not relevant to compilation, skipping rebuild\n",
                    changed_paths.len()
                ));
                if let Some(testing) = &self.testing {
                    testing.on_program(
                        self.program
                            .borrow()
                            .as_ref()
                            .expect("program set")
                            .as_ref(),
                    );
                }
                return;
            }
        } else if overflow {
            // Overflow: evict the entire source file cache and force a full rebuild.
            // The fast path must not run here: after clearing the cache a one-file
            // program would present exactly one cache miss and be misread as a
            // single-file content edit, silently reusing a stale (e.g. unresolved
            // import) program instead of rediscovering the file graph.
            source_file_cache_reset();
            self.watch_set_dirty.set(true);
            self.force_full_rebuild.set(true);
        } else if !has_events && !self.config_modified.get() {
            // No events and no config change
            self.dlog(format_args!("[watch] DoCycle: no events, skipping\n"));
            if let Some(testing) = &self.testing {
                testing.on_program(
                    self.program
                        .borrow()
                        .as_ref()
                        .expect("program set")
                        .as_ref(),
                );
            }
            return;
        }

        (self.report_watch_status)(&new_compiler_diagnostic(
            &diagnostics::File_change_detected_Starting_incremental_compilation,
            &[] as &[String],
        ));
        if self.do_build(&mut lock).is_err() {
            // Mid-cycle watch failure; force a full rebuild on the next event
            self.wm.force_overflow();
        }
    }

    /// `wm.DebugLog` write — `fmt.Fprintf(w.wm.DebugLog, ...)`.
    fn dlog(&self, args: std::fmt::Arguments) {
        if let Some(w) = self.wm.debug_log.lock().unwrap().as_mut() {
            let _ = w.write_fmt(args);
        }
    }

    /// `(w *Watcher) isRelevantChange`.
    fn is_relevant_change(
        &self,
        changed_paths: &FxHashMap<RootedPath, EventKind>,
        lock: &WatchManagerLock<'_>,
    ) -> bool {
        let case_sensitivity = self.sys.fs().case_sensitivity();
        let opts = self.case_sensitivity();
        let content_mapper_watched_files = new_set_from_items(
            self.content_mapper_watched_files()
                .iter()
                .map(|file_name| case_sensitivity.path_key(&file_name.as_path())),
        );
        for event_path in changed_paths.keys() {
            let p = opts.path_key(event_path);
            if content_mapper_watched_files.has(&p) {
                return true;
            }
            if self.seen_files.borrow().has(&p) {
                return true;
            }
            {
                let config = self.config.borrow();
                if config.config_file.is_some()
                    && config.possibly_matches_file_name(&tspath::rooted_file_path_from_path(
                        event_path.clone(),
                    ))
                {
                    return true;
                }
                if config.config_file.is_some() && config.possibly_matches_directory_name(&p) {
                    return true;
                }
            }
            if self
                .sys
                .fs()
                .directory_exists(&tspath::rooted_directory_path_from_path(event_path.clone()))
                && lock.is_path_under_watch(event_path)
            {
                return true;
            }
        }
        false
    }

    /// `(w *Watcher) doBuild` — returns `Err` when watch reconciliation fails
    /// (Go's `error` return).
    fn do_build(&self, lock: &mut WatchManagerLock<'_>) -> Result<(), tsc_fswatch::Error> {
        if self.config_modified.get() {
            source_file_cache_reset();
            self.watch_set_dirty.set(true);
        }

        let mut reloaded_file_names = false;
        if self.watch_set_dirty.get() {
            let reload = {
                let config = self.config.borrow();
                config.config_file.is_some()
                    && config
                        .wildcard_directories()
                        .is_some_and(|dirs| !dirs.is_empty())
            };
            if reload {
                let new_config = self
                    .config
                    .borrow()
                    .reload_file_names_of_parsed_command_line(&self.sys.fs());
                reloaded_file_names = true;
                if self.config.borrow().file_names() != new_config.file_names() {
                    *self.config.borrow_mut() = Arc::new(new_config);
                } else {
                    self.watch_set_dirty.set(false);
                    *self.config.borrow_mut() = Arc::new(new_config);
                }
            } else if !self.config_modified.get() {
                self.watch_set_dirty.set(false);
            }
        }

        if self.program.borrow().is_some()
            && self.program_ready.get()
            && !self.config_modified.get()
            && !self.watch_set_dirty.get()
            && !self.force_full_rebuild.get()
        {
            let cached = cachedvfs::from(self.sys.fs());
            let inner_host = new_compiler_host(
                cached.clone(),
                self.sys.default_library_path(),
                // PORT(deferred): `w.extendedConfigCache` — see the file header.
                None,
                Some(get_trace_from_sys(
                    &self.sys,
                    self.config.borrow().locale().clone(),
                    self.testing.as_ref(),
                )),
                self.content_mapper_project.borrow().clone(),
            );
            let host = Arc::new(WatchCompilerHost { inner: inner_host });

            if self.try_update_program(&host) {
                self.fast_path_builds.set(self.fast_path_builds.get() + 1);
                let result = self.compile_and_emit();
                cached.disable_and_clear_cache();

                self.update_config_mtimes();
                self.config_modified.set(false);

                self.report_error_count(result.diagnostics.len());
                if let Some(testing) = &self.testing {
                    testing.on_program(
                        self.program
                            .borrow()
                            .as_ref()
                            .expect("program set")
                            .as_ref(),
                    );
                }
                return Ok(());
            }
            cached.disable_and_clear_cache();
        }

        let cached = cachedvfs::from(self.sys.fs());
        let tfs = Arc::new(trackingvfs::Fs::new(cached.clone()));
        let inner_host = new_compiler_host(
            tfs.clone(),
            self.sys.default_library_path(),
            // PORT(deferred): `w.extendedConfigCache` — see the file header.
            None,
            Some(get_trace_from_sys(
                &self.sys,
                self.config.borrow().locale().clone(),
                self.testing.as_ref(),
            )),
            self.content_mapper_project.borrow().clone(),
        );
        let host = Arc::new(WatchCompilerHost { inner: inner_host });

        {
            let config = self.config.borrow();
            if config.config_file.is_some() {
                if let Some(wildcard_directories) = config.wildcard_directories() {
                    for dir in wildcard_directories.keys() {
                        tfs.seen_files.add(dir.as_path());
                    }
                }
                if !reloaded_file_names
                    && !self.watch_set_dirty.get()
                    && config
                        .wildcard_directories()
                        .is_some_and(|dirs| !dirs.is_empty())
                {
                    drop(config);
                    let new_config = self
                        .config
                        .borrow()
                        .reload_file_names_of_parsed_command_line(&self.sys.fs());
                    *self.config.borrow_mut() = Arc::new(new_config);
                }
            }
        }
        for path in self.config_file_paths.borrow().iter() {
            tfs.seen_files.add(path.as_path());
        }
        for path in &self.content_mapper_watched_files() {
            tfs.seen_files.add(path.as_path());
        }

        let program = tsc_compiler::program::new_program(ProgramOptions {
            config: Rc::new(ProgramConfig {
                config: self.config.borrow().clone(),
                ..Default::default()
            }),
            hosts: ProgramHosts {
                host: host.clone(),
                tracing: None,
            },
            factories: Default::default(),
        });
        let sys = self.sys.clone();
        *self.program.borrow_mut() = Some(crate::incremental::new_program(
            program,
            self.program.borrow().clone(),
            None,
            Arc::new(move || sys.now()),
            self.testing.is_some(),
        ));
        self.program_ready.set(true);
        self.full_builds.set(self.full_builds.get() + 1);

        let result = self.compile_and_emit();
        cached.disable_and_clear_cache();

        let case_sensitivity = self.sys.fs().case_sensitivity();
        let seen_slice = tfs.seen_files.to_slice();
        let mut seen_files = Set::with_size_hint(seen_slice.len());
        for p in &seen_slice {
            seen_files.add(case_sensitivity.path_key(p));
        }
        *self.seen_files.borrow_mut() = seen_files;

        self.update_config_mtimes();

        if let Err(err) = self.reconcile_watches(lock, &seen_slice) {
            let _ = writeln!(self.sys.writer().guard(), "{err}");
            return Err(err);
        }
        self.watch_set_dirty.set(false);
        self.config_modified.set(false);
        self.force_full_rebuild.set(false);

        let program_rc = self.program.borrow().clone().expect("program set");
        let program = program_rc.get_program().clone();
        let program_files = program.files_by_path();
        // `w.sourceFileCache.Range` — drop cache entries for files no longer
        // in the program.
        let stale: Vec<PathKey> = SOURCE_FILE_CACHE.with(|c| {
            c.borrow()
                .keys()
                .filter(|path| !program_files.contains_key(*path))
                .cloned()
                .collect()
        });
        for path in stale {
            source_file_cache_delete(&path);
        }

        self.report_error_count(result.diagnostics.len());

        if let Some(testing) = &self.testing {
            testing.on_program(
                self.program
                    .borrow()
                    .as_ref()
                    .expect("program set")
                    .as_ref(),
            );
        }
        Ok(())
    }

    /// `(w *Watcher) tryUpdateProgram` — the single-file fast path.
    fn try_update_program(&self, host: &Arc<WatchCompilerHost>) -> bool {
        let program_rc = self.program.borrow().clone().expect("program set");
        let old_program = program_rc.get_program().clone();

        let mut changed_path = PathKey::default();
        let mut changed_count = 0;
        for (path, &file) in old_program.files_by_path() {
            {
                let arena = old_program.arena_of(file);
                if !arena[file].as_source_file().content_mapper().is_empty() {
                    continue;
                }
            }
            if !source_file_cache_contains(path) {
                changed_path = path.clone();
                changed_count += 1;
                if changed_count > 1 {
                    return false;
                }
            }
        }
        if changed_count == 0 {
            return false;
        }

        if let Some(&old_file_id) = old_program.files_by_path().get(&changed_path) {
            let parse_options = {
                let arena = old_program.arena_of(old_file_id);
                arena[old_file_id].as_source_file().parse_options().clone()
            };
            if let Some(new_file) = host.get_source_file(&parse_options) {
                let arena = old_program.arena_of(old_file_id);
                let old_file = arena[old_file_id].as_source_file();
                if !equal_jsx_implicit_import(
                    &old_program.options(),
                    old_file,
                    new_file.source_file(),
                ) {
                    return false;
                }
            }
        }

        let host_dyn: Arc<dyn CompilerHost> = host.clone();
        let (new_program, _, reused) = reuse_program(&old_program, &changed_path, host_dyn, None);
        if reused {
            let sys = self.sys.clone();
            *self.program.borrow_mut() = Some(crate::incremental::new_program(
                new_program.expect("reused program"),
                Some(program_rc),
                None,
                Arc::new(move || sys.now()),
                self.testing.is_some(),
            ));
        }
        reused
    }

    /// `FastPathBuilds` — how many builds reused an existing program via the
    /// UpdateProgram single-file fast path (test observability).
    #[allow(dead_code)] // consumed by in-crate watch tests
    pub fn fast_path_builds(&self) -> i32 {
        self.fast_path_builds.get()
    }

    /// `FullBuilds` — how many builds constructed a full program via
    /// NewProgram (test observability).
    #[allow(dead_code)] // consumed by in-crate watch tests
    pub fn full_builds(&self) -> i32 {
        self.full_builds.get()
    }

    /// `(w *Watcher) evictChangedSourceFiles`.
    fn evict_changed_source_files(&self, changed_paths: &FxHashMap<RootedPath, EventKind>) {
        let case_sensitivity = self.sys.fs().case_sensitivity();
        for event_path in changed_paths.keys() {
            let p = case_sensitivity.path_key(event_path);
            if source_file_cache_contains(&p) {
                self.dlog(format_args!("[watch] evicting cached source file: {p:?}\n"));
                source_file_cache_delete(&p);
            }
        }
    }

    /// `(w *Watcher) compileAndEmit`.
    fn compile_and_emit(&self) -> CompileAndEmitResult {
        let program_rc = self.program.borrow().clone().expect("program set");
        let program = program_rc.get_program().clone();
        let config = self.config.borrow().clone();
        let take_nested = program_rc.clone();
        // Go's `EmitInput.ProgramLike` is `w.program`, which emit only reads
        // (for `TakeNestedEmitTime` via a downcast); the Rust `EmitInput`
        // takes the callback directly, so `program_like` is enough.
        emit_files_and_report_errors(&mut EmitInput {
            sys: &self.sys,
            program_like: &*program_rc,
            program: &program,
            config: &config,
            report_diagnostic: self.report_diagnostic.clone(),
            report_error_summary: self.report_error_summary.clone(),
            writer: self.sys.writer(),
            write_file: None,
            compile_times: Rc::new(RefCell::new(CompileTimes::default())),
            testing: self.testing.as_ref(),
            testing_mtimes_cache: None,
            tracing: None,
            // `program.(*incremental.Program).TakeNestedEmitTime` — the
            // watcher's program is always incremental.
            take_nested_emit_time: Some(Box::new(move || take_nested.take_nested_emit_time())),
        })
    }

    /// `(w *Watcher) contentMapperManifestChanged`.
    fn content_mapper_manifest_changed(
        &self,
        changed_paths: &FxHashMap<RootedPath, EventKind>,
    ) -> bool {
        let case_sensitivity = self.case_sensitivity();
        let mut changed_path_keys: Option<Set<PathKey>> = None;
        let config = self.config.borrow();
        for mapper in config.content_mappers() {
            if mapper.package_directory.as_string().is_empty() || !mapper.contribution_id.is_empty()
            {
                continue;
            }
            if changed_path_keys.is_none() {
                let mut keys = Set::with_size_hint(changed_paths.len());
                for path in changed_paths.keys() {
                    keys.add(case_sensitivity.path_key(path));
                }
                changed_path_keys = Some(keys);
            }
            let manifest_path = mapper.package_directory.resolve_file("package.json");
            if changed_path_keys
                .as_ref()
                .unwrap()
                .has(&case_sensitivity.path_key(&manifest_path.as_path()))
            {
                return true;
            }
        }
        false
    }

    /// `(w *Watcher) recheckTsConfig` — re-parses tsconfig when a config file
    /// mtime changed (or `force`); returns `true` when the cycle should be
    /// skipped (unrecoverable config errors).
    fn recheck_ts_config(&self, force: bool) -> bool {
        let Some(config_file_name) = &self.config_file_name else {
            return false;
        };

        if !force && !self.config_has_errors.get() && !self.config_file_paths.borrow().is_empty() {
            let mut changed = false;
            for path in self.config_file_paths.borrow().iter() {
                let old_mtime = self.config_mtimes.borrow().get(path).copied();
                let s = self.sys.fs().stat(&path.as_path());
                match old_mtime {
                    None => {
                        if s.is_some() {
                            changed = true;
                            break;
                        }
                    }
                    Some(old_mtime) => {
                        if s.is_none_or(|s| s.mod_time() != old_mtime) {
                            changed = true;
                            break;
                        }
                    }
                }
            }
            if !changed {
                return false;
            }
        }

        let Some(config_parse_result) = self.parse_config_file() else {
            return true;
        };
        if self.config_has_errors.get() {
            self.config_modified.set(true);
        }
        self.config_has_errors.set(false);
        {
            let mut paths = vec![config_file_name.clone()];
            paths.extend(config_parse_result.extended_source_files().iter().cloned());
            *self.config_file_paths.borrow_mut() = paths;
        }
        if !parsed_config_equals(
            self.config.borrow().parsed_config.as_ref(),
            config_parse_result.parsed_config.as_ref(),
        ) {
            self.config_modified.set(true);
        }
        self.replace_content_mapper_project(&config_parse_result);
        *self.config.borrow_mut() = Arc::new(config_parse_result);
        false
    }

    /// `(w *Watcher) parseConfigFile`.
    fn parse_config_file(&self) -> Option<ParsedCommandLine> {
        let extended_config_cache = Arc::new(ExtendedConfigCache::default());
        let result = tsconfigparsing::get_parsed_command_line_of_config_file(
            self.config_file_name.clone().expect("config file name"),
            self.compiler_options_from_command_line.as_ref(),
            self.command_line_raw.as_ref(),
            &self.sys.fs(),
            Some(&*extended_config_cache),
        );
        let config_parse_result = match result {
            Ok(config) => config,
            Err(errors) => {
                for e in &errors {
                    (self.report_diagnostic)(e);
                }
                self.config_has_errors.set(true);
                self.report_error_count(errors.len());
                return None;
            }
        };
        *self.extended_config_cache.borrow_mut() = Some(extended_config_cache);
        Some(config_parse_result)
    }

    /// The `Found_0/1_errors_Watching_for_file_changes` status line shared by
    /// `doBuild` and `parseConfigFile`.
    fn report_error_count(&self, error_count: usize) {
        if error_count == 1 {
            (self.report_watch_status)(&new_compiler_diagnostic(
                &diagnostics::Found_1_error_Watching_for_file_changes,
                &[] as &[String],
            ));
        } else {
            (self.report_watch_status)(&new_compiler_diagnostic(
                &diagnostics::Found_0_errors_Watching_for_file_changes,
                &[error_count],
            ));
        }
    }

    /// `w.configMtimes` refresh — shared by both `doBuild` paths.
    fn update_config_mtimes(&self) {
        let config_file_paths = self.config_file_paths.borrow();
        let mut mtimes = HashMap::with_capacity(config_file_paths.len());
        for cfg_path in config_file_paths.iter() {
            if let Some(s) = self.sys.fs().stat(&cfg_path.as_path()) {
                mtimes.insert(cfg_path.clone(), s.mod_time());
            }
        }
        *self.config_mtimes.borrow_mut() = mtimes;
    }
}

/// `equalJSXImplicitImport`.
fn equal_jsx_implicit_import(
    options: &CompilerOptions,
    old_file: &SourceFile,
    new_file: &SourceFile,
) -> bool {
    let is_jsx = |file: &SourceFile| matches!(file.script_kind, ScriptKind::Jsx | ScriptKind::Tsx);
    if !is_jsx(old_file) && !is_jsx(new_file) {
        return true;
    }
    let old_import = get_jsx_runtime_import(
        &get_jsx_implicit_import_base(options, Some(old_file)),
        options,
    );
    let new_import = get_jsx_runtime_import(
        &get_jsx_implicit_import_base(options, Some(new_file)),
        options,
    );
    old_import == new_import
}

/// `w.config.ParsedConfig.Equals(other.ParsedConfig)` — Go's `*ParsedOptions`
/// is nilable; `(nil).Equals`/`Equals(nil)` would panic in Go, but the
/// command-line path always has `ParsedConfig` set. `None == None` is equal.
fn parsed_config_equals(
    a: Option<&tsc_tsoptions::parsedoptions::ParsedOptions>,
    b: Option<&tsc_tsoptions::parsedoptions::ParsedOptions>,
) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => a.equals(b),
        (None, None) => true,
        _ => false,
    }
}
