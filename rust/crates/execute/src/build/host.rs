// Ported from tsc/internal/execute/build/host.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Concurrency: Go's `host` is shared by the builder goroutines and guards its
// caches with `sync.Map` + per-entry mutexes. The port is sequential — the
// orchestrator runs a work-list, not workers (see the concurrency note in
// `orchestrator.rs`) — but `BuildHost` still satisfies `CompilerHost:
// Send + Sync`, which forces the following PORT(deferred) cache changes:
//
//   - `sourceFiles`: Go caches `.d.ts`/`.json` `*ast.SourceFile` parses for
//     the duration of a build cycle. `ParsedSourceFile` owns its `Vec<Node>`
//     arena and is `!Send`, so it cannot be stored in this host — files are
//     parsed per call, matching `BasicCompilerHost`'s behaviour. The per-cycle
//     cache (and `resetCaches`'s reset of it) is deferred.
//   - `resolvedReferences`: `Arc<ParsedCommandLine>` is `!Send`/`!Sync` for the
//     same reason (it retains `TsConfigSourceFile` arenas), so config files
//     are parsed per call. Fresh parses are observationally equal to Go's
//     cache hits — parse is deterministic — but shared configs are re-parsed.
//   - `extendedConfigCache`: `ExtendedConfigCacheEntry` stores the same
//     `!Send` arenas, so `None` is passed to
//     `get_parsed_command_line_of_config_file_path` (no "extends" memoization).
//   - `mTimes` and `configTimes` hold plain values and keep Go's `SyncMap`
//     shape. `mTimes` is swapped wholesale on each watch update (Go assigns a
//     fresh `*SyncMap`), so it sits behind `Mutex<Arc<…>>`.

use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime};

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_collections::{OrderedMap, SyncMap};
use tsc_compiler::host::{BasicCompilerHost, CompilerHost};
use tsc_contentmapper::contentmapper::Mapper;
use tsc_contentmapper::host::{Error as ContentMapperError, Project};
use tsc_contentmapper::transform::{ParsedSourceFile, SourceFiles};
use tsc_diagnostics::Message;
use tsc_tsoptions::parsedbuildcommandline::ParsedBuildCommandLine;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tsoptions::tsconfigparsing::get_parsed_command_line_of_config_file_path;
use tsc_tsoptions::value::Value;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::cachedvfs;
use tsc_vfs::fs::FsError;
use tsc_vfs::vfs::Vfs;

use crate::tsc::System;

use super::uptodatestatus::ZERO_TIME;

/// `type host struct` — the orchestrator-scoped compiler host backing every
/// per-project [`super::compiler_host::BuildCompilerHost`].
pub(crate) struct BuildHost {
    /// `host compiler.CompilerHost` — the shared cached-FS compiler host.
    inner: BasicCompilerHost,
    /// The `cachedvfs::Fs` inside `inner` — kept so `resetCaches` can call
    /// `ClearCache` (Go reaches it via `h.host.FS().(*cachedvfs.FS)`).
    cached_fs: Arc<cachedvfs::Fs>,

    /// `configTimes` — per-config parse time, recorded once per path per
    /// cache lifetime (Go records it inside the `resolvedReferences` loader,
    /// which parses each config once per cycle; this records the first parse).
    config_times: SyncMap<PathKey, Duration>,

    /// `mTimes *collections.SyncMap[tspath.PathKey, time.Time]` — the Arc is
    /// replaced wholesale by `reset_mtime_cache` (Go assigns a new `SyncMap`
    /// pointer); callers that captured the previous `Arc` keep seeing the old
    /// cache, matching Go's `oldCache` hand-off in `updateWatch`.
    m_times: Mutex<Arc<SyncMap<PathKey, SystemTime>>>,

    /// `orchestrator.opts.Sys` — needed for `Now()` in the parse-timing path
    /// (Go reaches it through `h.orchestrator`; the port keeps the few values
    /// the host needs rather than a `!Send` back-pointer to the state).
    sys: Arc<dyn System>,
    /// `orchestrator.opts.Command` — `CompilerOptions` and `Raw` are the
    /// overrides folded into every resolved project reference.
    command: Arc<ParsedBuildCommandLine>,
    /// `orchestrator.caseSensitivity`.
    case_sensitivity: CaseSensitivity,
}

impl BuildHost {
    pub(crate) fn new(
        inner: BasicCompilerHost,
        cached_fs: Arc<cachedvfs::Fs>,
        sys: Arc<dyn System>,
        command: Arc<ParsedBuildCommandLine>,
        case_sensitivity: CaseSensitivity,
    ) -> BuildHost {
        BuildHost {
            inner,
            cached_fs,
            config_times: SyncMap::new(),
            m_times: Mutex::new(Arc::new(SyncMap::new())),
            sys,
            command,
            case_sensitivity,
        }
    }

    /// The shared `cachedvfs::Fs` for `Orchestrator::resetCaches`.
    pub(crate) fn cached_fs(&self) -> &Arc<cachedvfs::Fs> {
        &self.cached_fs
    }

    /// `configTimes.Load(path)` — the config-parse time recorded for `path`.
    pub(crate) fn config_time(&self, path: &PathKey) -> Duration {
        self.config_times.load(path).unwrap_or_default()
    }

    /// `o.host.mTimes` — the live mtime cache (a fresh `SyncMap` after
    /// `reset_mtime_cache`, as with Go's pointer swap).
    pub(crate) fn m_times(&self) -> Arc<SyncMap<PathKey, SystemTime>> {
        self.m_times.lock().unwrap().clone()
    }

    /// `o.host.mTimes = &collections.SyncMap[...]{}` — Go swaps in a fresh map;
    /// holders of the previous `Arc` keep the old one.
    pub(crate) fn reset_mtime_cache(&self) {
        *self.m_times.lock().unwrap() = Arc::new(SyncMap::new());
    }

    /// `(h *host) GetMTime`.
    pub(crate) fn get_mtime(&self, file: &RootedFilePath) -> SystemTime {
        self.load_or_store_mtime(file, None, true)
    }

    /// `(h *host) SetMTime`.
    pub(crate) fn set_mtime(
        &self,
        file: &RootedFilePath,
        m_time: SystemTime,
    ) -> Result<(), FsError> {
        self.fs().chtimes(&file.as_path(), ZERO_TIME, m_time)
    }

    /// `(h *host) loadOrStoreMTime` — `old_cache` is Go's `oldCache`
    /// (`updateWatch`'s pre-reset map); `store` is Go's `store` flag.
    fn load_or_store_mtime(
        &self,
        file: &RootedFilePath,
        old_cache: Option<&SyncMap<PathKey, SystemTime>>,
        store: bool,
    ) -> SystemTime {
        let path = self.case_sensitivity.path_key(&file.as_path());
        let m_times = self.m_times();
        if let Some(existing) = m_times.load(&path) {
            return existing;
        }
        let mut m_time = old_cache.and_then(|cache| cache.load(&path));
        if m_time.is_none() {
            m_time = Some(crate::incremental::get_mtime(&self.inner, file));
        }
        let m_time = m_time.unwrap_or(ZERO_TIME);
        if store {
            m_times.store(path, m_time);
        }
        m_time
    }

    /// `(h *host) storeMTime`.
    pub(crate) fn store_mtime(&self, file: &RootedFilePath, m_time: SystemTime) {
        let path = self.case_sensitivity.path_key(&file.as_path());
        self.m_times().store(path, m_time);
    }

    /// `(h *host) storeMTimeFromOldCache`.
    pub(crate) fn store_mtime_from_old_cache(
        &self,
        file: &RootedFilePath,
        old_cache: &SyncMap<PathKey, SystemTime>,
    ) {
        let path = self.case_sensitivity.path_key(&file.as_path());
        if let Some(m_time) = old_cache.load(&path) {
            self.m_times().store(path, m_time);
        }
    }

    /// `(h *host) configTimes` reset — part of `resetCaches`.
    pub(crate) fn reset_config_times(&self) {
        self.config_times.clear();
    }
}

impl CompilerHost for BuildHost {
    /// `(h *host) FS`.
    fn fs(&self) -> &Arc<dyn Vfs> {
        self.inner.fs()
    }

    /// `(h *host) DefaultLibraryPath`.
    fn default_library_path(&self) -> &RootedDirectoryPath {
        self.inner.default_library_path()
    }

    /// `(h *host) Trace` — panics like Go.
    fn trace(&self, _msg: &'static Message, _args: &[String]) {
        panic!(
            "build.Orchestrator.host does not support tracing; use a different host for tracing"
        );
    }

    /// `(h *host) GetSourceFile`.
    ///
    /// PORT(deferred): Go memoizes `.d.ts`/`.json` parses per cycle in
    /// `sourceFiles`; the arena-backed `ParsedSourceFile` is `!Send`, so the
    /// cache cannot live in this `Sync` host — every call parses fresh.
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<ParsedSourceFile> {
        self.inner.get_source_file(opts)
    }

    /// `(h *host) GetContentMappedSourceFiles` — the base host has no content
    /// mapper project (the per-task `BuildCompilerHost` does).
    fn get_content_mapped_source_files(
        &self,
        _parse_options: &SourceFileParseOptions,
        _mapper: &Arc<Mapper>,
    ) -> Result<SourceFiles, ContentMapperError> {
        Err(ContentMapperError::ProjectUnavailable)
    }

    /// `(h *host) ContentMapperProject` — panics like Go.
    fn content_mapper_project(&self) -> Option<&Arc<dyn Project>> {
        panic!(
            "build.Orchestrator.host does not support content mapper project; use an individual project's compiler host instead"
        );
    }

    /// `(h *host) GetResolvedProjectReference`.
    ///
    /// PORT(deferred): Go's `resolvedReferences` cache is keyed by `PathKey`
    /// and dedupes parses across task creation and each program's project
    /// reference resolution; `ParsedCommandLine` retains `!Send` arenas, so
    /// the cache cannot live here — every call parses fresh (the
    /// `configTimes` accounting still records the first parse per path).
    fn get_resolved_project_reference(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<ParsedCommandLine>> {
        let config_start = self.sys.now();
        // Wrap command line options in "compilerOptions" key to match
        // tsconfig.json structure.
        let mut command_line_raw: Option<OrderedMap<String, Value>> = None;
        if let Some(Value::Map(raw)) = self.command.raw.as_ref() {
            let mut wrapped = OrderedMap::new();
            wrapped.set("compilerOptions".to_string(), Value::Map(raw.clone()));
            command_line_raw = Some(wrapped);
        }
        let command_line = get_parsed_command_line_of_config_file_path(
            file_name.clone(),
            path.clone(),
            self.command.compiler_options.as_ref(),
            command_line_raw.as_ref(),
            self.fs(),
            None, // extended_config_cache — see the PORT note above.
        )
        .ok();
        let config_time = self
            .sys
            .now()
            .duration_since(config_start)
            .unwrap_or_default();
        if self.config_times.load(path).is_none() {
            self.config_times.store(path.clone(), config_time);
        }
        command_line.map(Arc::new)
    }
}

/// `var _ incremental.Host = (*host)(nil)` — the orchestrator host is the
/// incremental `Host` (mtime get/set) for `incremental::Program`.
///
/// PORT(sibling-pending): `crate::incremental` is still being ported; the
/// `Host` trait shape is assumed to be Go's
/// `{ GetMTime, SetMTime }`.
impl crate::incremental::Host for BuildHost {
    fn get_mtime(&self, file_name: &RootedFilePath) -> SystemTime {
        BuildHost::get_mtime(self, file_name)
    }

    fn set_mtime(&self, file_name: &RootedFilePath, m_time: SystemTime) -> Result<(), String> {
        BuildHost::set_mtime(self, file_name, m_time).map_err(|e| e.to_string())
    }
}
