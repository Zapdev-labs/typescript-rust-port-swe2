// Ported from tsc/internal/compiler/program.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `*ast.SourceFile`/`​*ast.Node` are `NodeId` values resolved through
// the program's per-file `Rc<ArenaCell>` arenas (`Program::nodes`/
// `arena_of`). `*tsoptions.ParsedCommandLine` is `Arc<ParsedCommandLine>`,
// `*tsoptions.SourceOutputAndProjectReference` is `Arc<...>` (tsoptions
// convention). `sync.Once`/`collections.SyncMap`/`lazyValue` fields become
// `RefCell<Option<_>>`/`OnceCell` — the port is single-threaded (see
// PORTING-NOTES). Go's shared backing array in `ReuseProgram`
// (`processedFiles: p.processedFiles`, `programDiagnostics`, etc.) becomes a
// `Clone` — the maps are never mutated after construction, so sharing was
// unobservable.
//
// PORT: Go's `error` returns/fields (`moduleResolutionError`, resolver
// `error`) are dropped — the Rust `Resolver` trait never produces one
// (see tsc-module's PORT note), so `module_resolution_error` is `None`
// unconditionally.
//
// PORT: `verifyCompilerOptions`'s `getDiagnosticsForFile`-adjacent mutation
// of `p.processedFiles.processingDiagnostics` inside `sync.Once` and
// `commonSourceDirectory` is funneled through
// `pending_processing_diagnostics`, drained by
// `IncludeProcessor::get_diagnostics` (order preserved: parse-time then
// post-parse in call order).
//
// PORT: `outputpaths.ForEachEmittedFile` takes a single `&[Node]` arena in
// this workspace, which cannot span per-file arenas, so
// `verify_compiler_options` iterates files directly and calls
// `get_output_paths_for` with each file's own arena.

use std::cell::{OnceCell, RefCell};
use std::collections::HashSet;
use std::io::Write;
use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use tsc_ast::diagnostic::{
    self, DiagnosticFile, DiagnosticRef, lock_diagnostic, new_compiler_diagnostic, new_diagnostic,
    new_external_diagnostic,
};
use tsc_ast::utilities::HasFileName;
use tsc_ast::{
    ArenaCell, ArenaMut, CheckJsDirective, CommentDirectiveKind, FileReference, Node, NodeArenaBuf,
    NodeId, SourceFileMetaData, SymbolArena, is_check_js_enabled_for_file, is_external_module,
    is_external_or_commonjs_module, is_plain_js_file, is_source_file_js, is_source_phase_import,
    is_string_literal, is_string_literal_like, new_has_file_name,
};
use tsc_checker::checker_core::Checker;
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::context::Context;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::{
    CompilerOptions, JsxEmit, ModuleKind, ModuleResolutionKind, ScriptTarget,
};
use tsc_core::scriptkind::ScriptKind;
use tsc_core::text::TextRange;
use tsc_core::tristate::{TS_TRUE, Tristate};
use tsc_diagnostics::{self as diagnostics, Category};
use tsc_locale::Locale;
use tsc_module::{
    DefaultResolver, ModeAwareCache, ModeAwareCacheKey, ResolutionData, ResolvedModule,
    ResolvedTypeReferenceDirective, Resolver, ResolverOptions,
};
use tsc_modulespecifiers::ModuleSpecifierGenerationHost;
use tsc_outputpaths::{ForceEmitPaths, OutputPathsHost};
use tsc_packagejson::InfoCacheEntry;
use tsc_symlinks::KnownSymlinks;
use tsc_tracing::{PHASE_BIND, PHASE_EMIT, PHASE_PROGRAM, Tracing, push};
use tsc_tsoptions::parsedcommandline::{ParsedCommandLine, SourceOutputAndProjectReference};
use tsc_tsoptions::tsconfigparsing::{
    create_diagnostic_at_reference_syntax, for_each_property_assignment,
    for_each_ts_config_prop_array, get_content_mapper_option_diagnostic_location,
};
use tsc_tsoptions::value::Value;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};

use crate::checker_pool::{
    CheckerPool, CheckerPoolProgram, CompilerCheckerPool, DoneFn, new_checker_pool_with_tracing,
};
use crate::emit_host::{
    BasicEmitHost, EmitOptions, EmitResult, SourceFileMayBeEmittedHost, get_source_files_to_emit,
    source_file_may_be_emitted,
};
use crate::file_include::FileIncludeReason;
use crate::file_loader::{
    LibFile, LoadedSourceFile, ProcessedFiles, RedirectsFile, get_default_resolution_mode_for_file,
    get_emit_syntax_for_usage_location_worker, get_mode_for_usage_location,
    process_all_program_files,
};
use crate::include_processor::IncludeProcessor;
use crate::processing_diagnostic::{IncludeExplainingDiagnostic, ProcessingDiagnostic};
use crate::project_reference_dts_faking_host::CompilerResolutionHost;
use crate::project_reference_file_mapper::ProjectReferenceFileMapper;

// ---------------------------------------------------------------------------
// ProgramOptions / ProgramConfig / ProgramHosts / ProgramFactories
// ---------------------------------------------------------------------------

/// `type ProgramOptions struct` — flattened `ProgramConfig` +
/// `ProgramHosts` + `ProgramFactories`.
pub struct ProgramOptions {
    pub config: Rc<ProgramConfig>,
    pub hosts: ProgramHosts,
    pub factories: ProgramFactories,
}

/// `type ProgramConfig struct`.
pub struct ProgramConfig {
    /// `Config *tsoptions.ParsedCommandLine`.
    pub config: Arc<ParsedCommandLine>,
    /// `UseSourceOfProjectReference`.
    pub use_source_of_project_reference: bool,
    /// `SingleThreaded`.
    pub single_threaded: Tristate,
    /// `TypingsLocation`.
    pub typings_location: RootedDirectoryPath,
    /// `ProjectName`.
    pub project_name: String,
    /// `SkipModuleResolution` — avoids all module and type reference
    /// resolution while still collecting import metadata needed for emit.
    pub skip_module_resolution: bool,
}

impl Default for ProgramConfig {
    fn default() -> Self {
        ProgramConfig {
            config: Arc::new(ParsedCommandLine::default()),
            use_source_of_project_reference: false,
            single_threaded: Tristate::default(),
            typings_location: RootedDirectoryPath::default(),
            project_name: String::new(),
            skip_module_resolution: false,
        }
    }
}

impl ProgramConfig {
    /// `(p *ProgramConfig) canUseProjectReferenceSource`.
    pub fn can_use_project_reference_source(&self) -> bool {
        self.use_source_of_project_reference
            && !self
                .config
                .compiler_options()
                .is_some_and(|o| o.disable_source_of_project_reference_redirect == TS_TRUE)
    }
}

/// `type ProgramHosts struct`.
#[derive(Clone)]
pub struct ProgramHosts {
    /// `Host CompilerHost`.
    pub host: Arc<dyn crate::host::CompilerHost>,
    /// `Tracing *tracing.Tracing`.
    pub tracing: Option<Arc<Tracing>>,
}

/// `type ProgramFactories struct`.
#[derive(Default)]
pub struct ProgramFactories {
    /// `CreateCheckerPool func(*Program) CheckerPool`. `Arc` (not `Box`) so
    /// `UpdateProgram` can offer the same factory to both `ReuseProgram` and
    /// the full-build fallback.
    pub create_checker_pool: Option<Arc<dyn Fn(&Rc<Program>) -> Rc<dyn CheckerPool>>>,
    /// `CreateModuleResolver func(module.ResolverOptions) module.Resolver`.
    pub create_module_resolver: Option<Arc<dyn Fn(ResolverOptions) -> Arc<dyn Resolver>>>,
}

/// `type packageNamesInfo struct`.
pub struct PackageNamesInfo {
    pub resolved: HashSet<String>,
    pub unresolved: HashSet<String>,
    pub deep_import_packages: HashSet<String>,
}

// ---------------------------------------------------------------------------
// Program
// ---------------------------------------------------------------------------

/// `type Program struct` — Go's embedded `processedFiles` lives in
/// `processed`; `Deref` forwards field access (`p.files`,
/// `p.resolved_modules`, ...) so the ported methods read like Go.
pub struct Program {
    /// `opts`.
    pub opts: Rc<ProgramConfig>,
    /// `hosts`.
    pub hosts: ProgramHosts,
    /// `resolutionData`.
    pub resolution_data: Rc<ResolutionData>,
    /// `checkerPool` — always set; used as fallback for project-system pools.
    /// Set inside `init_checker_pool`, after the `Rc<Program>` exists.
    checker_pool: RefCell<Option<Rc<dyn CheckerPool>>>,
    /// `compilerCheckerPool` — set only when the built-in compiler checker
    /// pool is in use (`create_checker_pool` was not provided).
    compiler_checker_pool: RefCell<Option<Rc<CompilerCheckerPool<Program>>>>,
    /// `includeProcessor`.
    pub include_processor: IncludeProcessor,
    /// `moduleResolutionError` — always `None`; see header PORT note.
    module_resolution_error: Option<String>,

    /// `caseSensitivity`.
    case_sensitivity: CaseSensitivity,

    /// Program-global symbol arena (SPEC §5.2 — `Program::symbols`). Go has
    /// no explicit arena: binder- and checker-allocated `*ast.Symbol`s share
    /// pointer identity on the heap. Here every `SymbolId` indexes this one
    /// `Vec<ast::Symbol>`; `Checker::symbol_arena` aliases it via `Rc`.
    pub symbols: SymbolArena,

    /// `processedFiles` (embedded in Go).
    pub processed: ProcessedFiles,

    /// `usesUriStyleNodeCoreModules` — never assigned in this revision of
    /// the Go source (always `TSUnknown`); kept for parity and `ReuseProgram`.
    uses_uri_style_node_core_modules: Tristate,

    /// `commonSourceDirectory` + `commonSourceDirectoryOnce` — `OnceCell`
    /// because `common_source_directory_ref` must yield `&` (printer host).
    common_source_directory: OnceCell<RootedDirectoryPath>,

    /// `declarationDiagnosticCache`.
    declaration_diagnostic_cache: RefCell<FxHashMap<NodeId, Rc<Vec<DiagnosticRef>>>>,

    /// `programDiagnostics`.
    program_diagnostics: RefCell<Vec<DiagnosticRef>>,
    /// `hasEmitBlockingDiagnostics`.
    has_emit_blocking_diagnostics: RefCell<HashSet<PathKey>>,
    /// `contentMapperOptionDiagnostics`.
    content_mapper_option_diagnostics: RefCell<Vec<DiagnosticRef>>,

    /// `sourceFilesToEmit` + `sourceFilesToEmitOnce`.
    source_files_to_emit: RefCell<Option<Rc<Vec<NodeId>>>>,

    /// `unresolvedImports lazyValue`.
    unresolved_imports: OnceCell<Rc<HashSet<String>>>,
    /// `knownSymlinks lazyValue`.
    known_symlinks: OnceCell<Rc<KnownSymlinks>>,
    /// `packageNames lazyValue`.
    package_names: OnceCell<Rc<PackageNamesInfo>>,
    /// `hasTSFile` + `hasTSFileOnce`.
    has_ts_file: OnceCell<bool>,
    /// `packagesMap` + `packagesMapOnce`.
    packages_map: OnceCell<Rc<FxHashMap<String, bool>>>,

    /// Post-parse additions to `processed.processing_diagnostics` (see
    /// header PORT note on the Go `sync.Once`/verify-time mutation).
    /// `pub(crate)` for `IncludeProcessor::get_diagnostics`, which drains it.
    pub(crate) pending_processing_diagnostics: RefCell<Vec<ProcessingDiagnostic>>,

    /// Cached `compiler_options_arc(opts.config)` — the checker `Program`
    /// trait returns `Rc<CompilerOptions>` by value.
    options: Rc<CompilerOptions>,

    /// `NodeId`s of `processed.files` — the `[]*ast.SourceFile` slice.
    source_file_ids: Vec<NodeId>,
    /// Lazily-built `fileIndexMap` — source-file `NodeId` → position in
    /// `source_file_ids` (program order), for `Program::file_rank`.
    file_rank_map: RefCell<Option<FxHashMap<NodeId, usize>>>,
    /// `file_index` → arena. `NodeId::file_index` is a global counter, so
    /// the table is sparse in principle but dense in practice — a Vec
    /// indexed by it replaces a hashmap probe with an array read on the
    /// very hot `nodes()`/`nodes_mut()` paths.
    arenas: Vec<Option<Rc<ArenaCell>>>,
    /// Last-resolved `(file_index, arena)` — `nodes()`/`nodes_mut()` are
    /// called per node access and overwhelmingly stay within one file, so a
    /// 1-entry cache skips the map lookup on the hot path.
    last_arena: std::cell::RefCell<Option<(u32, Rc<ArenaCell>)>>,
}

impl std::ops::Deref for Program {
    type Target = ProcessedFiles;
    fn deref(&self) -> &ProcessedFiles {
        &self.processed
    }
}

impl Program {
    // -- FileExists / BaseDirectory / host plumbing -------------------------

    /// `FileExists` — implements `checker.Program`.
    pub fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.hosts.host.fs().file_exists(path)
    }

    /// `BaseDirectory` — implements `checker.Program`.
    pub fn base_directory(&self) -> RootedDirectoryPath {
        self.opts.config.base_directory().clone()
    }

    /// Borrowed variant — the printer `EmitHost` returns `&`.
    pub fn base_directory_ref(&self) -> &RootedDirectoryPath {
        self.opts.config.base_directory()
    }

    /// `GetCurrentDirectory`.
    pub fn get_current_directory(&self) -> RootedDirectoryPath {
        self.base_directory()
    }

    /// `ContentMapperProject`.
    pub fn content_mapper_project(&self) -> Option<Arc<dyn tsc_contentmapper::Project>> {
        self.hosts.host.content_mapper_project().cloned()
    }

    /// `GetGlobalTypingsCacheLocation` — implements `checker.Program`.
    pub fn get_global_typings_cache_location(&self) -> RootedDirectoryPath {
        self.opts.typings_location.clone()
    }

    /// `GetNearestAncestorDirectoryWithPackageJson` — implements
    /// `checker.Program`.
    pub fn get_nearest_ancestor_directory_with_package_json(
        &self,
        dirname: &RootedDirectoryPath,
    ) -> RootedDirectoryPath {
        let scoped = self.new_resolver().get_package_scope_for_path(dirname);
        if let Some(scoped) = scoped {
            if scoped.exists() {
                return scoped.package_directory.as_directory_path().clone();
            }
        }
        RootedDirectoryPath::default()
    }

    /// `GetPackageJsonInfo` — implements `checker.Program`.
    pub fn get_package_json_info(
        &self,
        pkg_json_path: &RootedFilePath,
    ) -> Option<Arc<InfoCacheEntry>> {
        let directory = pkg_json_path.directory();
        let scoped = self.new_resolver().get_package_scope_for_path(&directory);
        if let Some(scoped) = scoped {
            if scoped.exists() && scoped.package_directory.as_directory_path() == &directory {
                return Some(scoped);
            }
        }
        None
    }

    /// `PackageJsonCacheEntries` — iterates all package.json cache entries.
    pub fn package_json_cache_entries(&self, f: impl FnMut(PathKey, Arc<InfoCacheEntry>) -> bool) {
        self.resolution_data.package_json_cache_entries(f);
    }

    /// `newResolver`.
    fn new_resolver(&self) -> DefaultResolver {
        let host = Arc::new(CompilerResolutionHost {
            host: self.hosts.host.clone(),
            base_directory: self.base_directory(),
        });
        self.resolution_data
            .new_resolver(self.mapper().resolution_host(host))
    }

    /// `p.projectReferenceFileMapper` — always populated by the files
    /// parser; `get_processed_files` stores `Some` unconditionally.
    fn mapper(&self) -> &Arc<ProjectReferenceFileMapper> {
        self.processed
            .project_reference_file_mapper
            .as_ref()
            .expect("project reference file mapper initialized")
    }

    /// `GetRedirectTargets` — the list of file paths that redirect to the
    /// given path (same package installed in different locations).
    pub fn get_redirect_targets(&self, path: &PathKey) -> Vec<RootedFilePath> {
        self.redirect_targets_map
            .get(path)
            .cloned()
            .unwrap_or_default()
    }

    /// `GetSourceOfProjectReferenceIfOutputIncluded` — the original file
    /// that was included in the program: the original source file name when
    /// including output of a project reference, otherwise the same name.
    /// Equivalent to `originalFileName` on `SourceFile` in Strada.
    pub fn get_source_of_project_reference_if_output_included(
        &self,
        file: &dyn HasFileName,
    ) -> RootedFilePath {
        if let Some(source) = self
            .output_file_to_project_reference_source
            .get(file.path_key())
        {
            return source.clone();
        }
        file.file_name().clone()
    }

    /// `GetProjectReferenceFromSource` — implements `checker.Program`.
    pub fn get_project_reference_from_source(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        self.mapper().get_project_reference_from_source(path)
    }

    /// Borrowed variant for `printer::EmitHost`.
    pub fn get_project_reference_from_source_ref(
        &self,
        path: &PathKey,
    ) -> Option<&SourceOutputAndProjectReference> {
        self.mapper()
            .source_to_project_reference
            .get(path)
            .map(|r| &**r)
    }

    /// `IsSourceFromProjectReference` — implements `checker.Program`.
    pub fn is_source_from_project_reference(&self, path: &PathKey) -> bool {
        self.mapper().is_source_from_project_reference(path)
    }

    /// `GetProjectReferenceFromOutputDts`.
    pub fn get_project_reference_from_output_dts(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        self.mapper().get_project_reference_from_output_dts(path)
    }

    /// `GetResolvedProjectReferenceFor` — `(config, present)`; a present
    /// `None` mirrors Go's stored nil `*ParsedCommandLine`.
    pub fn get_resolved_project_reference_for(
        &self,
        path: &PathKey,
    ) -> (Option<Arc<ParsedCommandLine>>, bool) {
        self.mapper().get_resolved_reference_for(path)
    }

    /// `GetRedirectForResolution` — implements `checker.Program`.
    pub fn get_redirect_for_resolution(
        &self,
        file: &dyn HasFileName,
    ) -> Option<Arc<ParsedCommandLine>> {
        self.mapper().get_redirect_for_resolution(file).0
    }

    /// `GetParseFileRedirect`.
    pub fn get_parse_file_redirect(&self, file_name: &RootedFilePath) -> RootedFilePath {
        self.get_parse_file_redirect_by_file_name(file_name)
    }

    /// `getParseFileRedirectByFileName`.
    fn get_parse_file_redirect_by_file_name(&self, file_name: &RootedFilePath) -> RootedFilePath {
        let (redirect, _) = self.mapper().get_parse_file_redirect(&new_has_file_name(
            file_name.clone(),
            self.case_sensitivity.path_key(&file_name.as_path()),
        ));
        redirect
    }

    /// `GetResolvedProjectReferences` — `Option` entries mirror Go nils.
    pub fn get_resolved_project_references(&self) -> Vec<Option<Arc<ParsedCommandLine>>> {
        self.mapper().get_resolved_project_references()
    }

    /// `RangeResolvedProjectReference`.
    pub fn range_resolved_project_reference(
        &self,
        f: &mut dyn FnMut(
            &PathKey,
            Option<&Arc<ParsedCommandLine>>,
            &Arc<ParsedCommandLine>,
            usize,
        ) -> bool,
    ) -> bool {
        self.mapper().range_resolved_project_reference(f)
    }

    /// `RangeResolvedProjectReferenceInChildConfig`.
    pub fn range_resolved_project_reference_in_child_config(
        &self,
        child_config: &Arc<ParsedCommandLine>,
        f: &mut dyn FnMut(
            &PathKey,
            Option<&Arc<ParsedCommandLine>>,
            &Arc<ParsedCommandLine>,
            usize,
        ) -> bool,
    ) -> bool {
        self.mapper()
            .range_resolved_project_reference_in_child_config(child_config, f)
    }

    /// `CaseSensitivity`.
    pub fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }

    /// `UseCaseSensitiveFileNames`.
    pub fn use_case_sensitive_file_names(&self) -> bool {
        self.case_sensitivity.is_case_sensitive()
    }

    /// `UsesUriStyleNodeCoreModules`.
    pub fn uses_uri_style_node_core_modules(&self) -> Tristate {
        self.uses_uri_style_node_core_modules
    }

    // -- Arena plumbing -------------------------------------------------------

    /// The arena handle owning `file`'s nodes.
    pub fn arena_handle(&self, file_index: u32) -> Rc<ArenaCell> {
        self.arena_cell(file_index)
    }

    /// `p.options`/`Options()` — inherent accessor so sibling modules can
    /// read options without importing `tsc_checker::checker_types::Program`.
    pub fn options(&self) -> Rc<CompilerOptions> {
        self.options.clone()
    }

    /// Inherent arena reads so sibling modules (emit_host, emitter,
    /// file_include) can read without the checker `Program` trait in scope.
    /// Returns a cheap `Rc` snapshot — no `RefCell` borrow is held, so a
    /// held snapshot can never block `nodes_mut`.
    fn arena_cell(&self, file_index: u32) -> Rc<ArenaCell> {
        {
            let last = self.last_arena.borrow();
            if let Some((i, cell)) = &*last {
                if *i == file_index {
                    return cell.clone();
                }
            }
        }
        let cell = self
            .arenas
            .get(file_index as usize)
            .and_then(|c| c.as_ref())
            .unwrap_or_else(|| {
                panic!(
                    "unknown file_index {file_index} (arenas: {:?})",
                    self.arenas
                        .iter()
                        .enumerate()
                        .filter(|(_, c)| c.is_some())
                        .map(|(i, _)| i as u32)
                        .collect::<Vec<_>>()
                )
            })
            .clone();
        *self.last_arena.borrow_mut() = Some((file_index, cell.clone()));
        cell
    }

    pub fn nodes(&self, file_index: u32) -> Rc<NodeArenaBuf> {
        self.arena_cell(file_index).snapshot()
    }

    /// Inherent mutable arena access via [`ArenaMut`] — the guard mutates
    /// the shared buffer in place; every live snapshot observes the writes.
    pub fn nodes_mut(&self, file_index: u32) -> ArenaMut {
        self.arena_cell(file_index).cow()
    }

    /// The shared arena cell handle — see `nodes`.
    pub fn nodes_handle(&self, file_index: u32) -> Rc<ArenaCell> {
        self.arena_handle(file_index)
    }

    /// `nodes_handle` with fallback: `NodeId::file_index` is process-global,
    /// so a synthetic arena index (or a node minted before this program's
    /// files were parsed) may not be present. Falls back to any registered
    /// arena — synthetic builder nodes only need a writable arena.
    pub fn nodes_handle_or_fallback(&self, file_index: u32) -> (u32, Rc<ArenaCell>) {
        if let Some(cell) = self.arenas.get(file_index as usize).and_then(|c| c.as_ref()) {
            return (file_index, cell.clone());
        }
        let (k, cell) = self
            .arenas
            .iter()
            .enumerate()
            .find_map(|(k, c)| c.as_ref().map(|c| (k as u32, c)))
            .expect("program has no arenas");
        (k, cell.clone())
    }

    /// Arena snapshot for a `NodeId`'s owning file.
    pub fn arena_of(&self, file: NodeId) -> Rc<NodeArenaBuf> {
        self.nodes(file.file_index())
    }

    /// `arena_checkout` — emit-time arena handoff. PORT(divergence): Go's
    /// emit mutates the shared `[]*ast.Node` graph while emit-resolver
    /// callbacks freely read it. A `RefMut` held across transformer visits
    /// would panic every such re-entrant `program.nodes()` read, so emit
    /// checks the arena out instead: the live `Vec` moves into the returned
    /// guard (transformers mutate it via `&mut`), while a clone is left in
    /// the cell for checker callbacks. On drop the guard writes the mutated
    /// `Vec` back. Checker reads during the window see pre-transform state —
    /// import-elision marking only walks original-tree nodes, so this is
    /// observationally equivalent there; if a future caller hands a
    /// synthetic `NodeId` minted during the visit to a checker callback, the
    /// clone will be too short — that's the known limitation.
    pub fn arena_checkout(&self, file_index: u32) -> ArenaCheckout {
        ArenaCheckout::new(self.arena_handle(file_index))
    }

    /// The `*ast.SourceFile`-as-`HasFileName` adapter — `fileName` +
    /// `pathKey` from the file's arena.
    pub fn file_has_file_name(&self, file: NodeId) -> tsc_ast::HasFileNameImpl {
        let nodes = self.arena_of(file);
        let sf = nodes[file].as_source_file();
        new_has_file_name(sf.file_name().clone(), sf.path_key().clone())
    }

    /// `GetSourceFileFromReference` — same behavior as `processSourceFile`
    /// without diagnostics or mutation.
    pub fn get_source_file_from_reference(
        &self,
        origin: NodeId,
        ref_: &FileReference,
    ) -> Option<NodeId> {
        // TODO: The module loader in corsa is fairly different than strada, it should probably be able to expose this functionality at some point,
        // rather than redoing the logic approximately here, since most of the related logic now lives in module.Resolver
        // Still, without the failed lookup reporting that only the loader does, this isn't terribly complicated

        let file_name = {
            let nodes = self.arena_of(origin);
            nodes[origin]
                .as_source_file()
                .file_name()
                .directory()
                .resolve_file(&ref_.file_name)
        };
        let options = self.options();
        let supported_extensions_base = tsc_tsoptions::tsconfigparsing::get_supported_extensions(
            &options,
            self.opts.config.content_mapper_extensions(),
        );
        let supported_extensions =
            tsc_tsoptions::tsconfigparsing::get_supported_extensions_with_json_if_resolve_json_module(
                Some(&options),
                &supported_extensions_base,
            );
        let allow_non_ts_extensions = options.allow_non_ts_extensions == TS_TRUE;
        if file_name.has_extension() {
            if !allow_non_ts_extensions {
                let canonical_file_name = self.case_sensitivity.path_key(&file_name.as_path());
                let supported = supported_extensions.iter().any(|exts| {
                    canonical_file_name
                        .extension_is_one_of(&exts.iter().map(|s| s.as_str()).collect::<Vec<_>>())
                });
                if !supported {
                    return None; // unsupported extensions are forced to fail
                }
            }
            return self.get_source_file_with_redirect(
                &file_name,
                self.path_key_for_file_name(&file_name),
            );
        }
        if allow_non_ts_extensions {
            let extensionless = self
                .get_source_file_with_redirect(&file_name, self.path_key_for_file_name(&file_name));
            if extensionless.is_some() {
                return extensionless;
            }
        }

        // Only try adding extensions from the first supported group (which should be .ts/.tsx/.d.ts)
        for ext in &supported_extensions[0] {
            let file_name_with_extension = file_name.append_suffix(ext);
            let result = self.get_source_file_with_redirect(
                &file_name_with_extension,
                self.path_key_for_file_name(&file_name_with_extension),
            );
            if result.is_some() {
                return result;
            }
        }
        None
    }

    // -- Construction ---------------------------------------------------------

    /// `initCheckerPool`.
    fn init_checker_pool(
        &self,
        create: Option<Arc<dyn Fn(&Rc<Program>) -> Rc<dyn CheckerPool>>>,
        this: &Rc<Program>,
    ) {
        if !self.finished_processing {
            panic!("Program must finish processing files before initializing checker pool")
        }

        if let Some(create) = create {
            *self.checker_pool.borrow_mut() = Some(create(this));
        } else {
            let pool = Rc::new(new_checker_pool_with_tracing(
                this,
                self.hosts.tracing.clone(),
            ));
            *self.checker_pool.borrow_mut() = Some(pool.clone());
            *self.compiler_checker_pool.borrow_mut() = Some(pool);
        }
    }

    /// `GetCheckerPool` — the checker pool associated with this program.
    pub fn get_checker_pool(&self) -> Rc<dyn CheckerPool> {
        self.checker_pool
            .borrow()
            .clone()
            .expect("checker pool initialized")
    }

    /// `canReplaceFileInProgram`.
    fn can_replace_file_in_program(
        &self,
        file1: &LoadedSourceFile,
        file2: &LoadedSourceFile,
    ) -> bool {
        let nodes1 = file1.nodes.snapshot();
        let nodes2 = file2.nodes.snapshot();
        let f1 = nodes1[file1.file].as_source_file();
        let f2 = nodes2[file2.file].as_source_file();
        let same_parse_options = f1.parse_options().file_name == f2.parse_options().file_name
            && f1.parse_options().path_key == f2.parse_options().path_key
            && f1.parse_options().external_module_indicator_options.jsx
                == f2.parse_options().external_module_indicator_options.jsx
            && f1.parse_options().external_module_indicator_options.force
                == f2.parse_options().external_module_indicator_options.force;
        let equal_refs = |a: &[FileReference], b: &[FileReference]| {
            a.len() == b.len()
                && a.iter()
                    .zip(b.iter())
                    .all(|(x, y)| equal_file_references(x, y))
        };
        if !same_parse_options
            || f1.script_kind != f2.script_kind
            || is_external_or_commonjs_module(nodes1[file1.file].as_source_file())
                != is_external_or_commonjs_module(nodes2[file2.file].as_source_file())
            || f1.uses_uri_style_node_core_modules != f2.uses_uri_style_node_core_modules
            || f1.imports().len() != f2.imports().len()
            || !f1
                .imports()
                .iter()
                .zip(f2.imports().iter())
                .all(|(&n1, &n2)| {
                    // `file2` was parsed by the incoming host and is not in
                    // `p.arenas`, so build `HasFileName` adapters from each
                    // file's own parse options rather than `file_has_file_name`
                    // (which looks the node up in the program arenas).
                    let has1 = tsc_ast::utilities::new_has_file_name(
                        f1.parse_options.file_name.clone(),
                        f1.parse_options.path_key.clone(),
                    );
                    let has2 = tsc_ast::utilities::new_has_file_name(
                        f2.parse_options.file_name.clone(),
                        f2.parse_options.path_key.clone(),
                    );
                    let options1 = self.compiler_options_for_file(&has1);
                    let options2 = self.compiler_options_for_file(&has2);
                    equal_module_specifiers(&nodes1[n1], &nodes2[n2], &nodes1, &nodes2)
                        && get_mode_for_usage_location(
                            has1.file_name(),
                            &self.get_source_file_meta_data(has1.path_key()),
                            n1,
                            &nodes1,
                            Some(&options1),
                        ) == get_mode_for_usage_location(
                            has2.file_name(),
                            &self.get_source_file_meta_data(has2.path_key()),
                            n2,
                            &nodes2,
                            Some(&options2),
                        )
                        && nodes1[n1]
                            .parent
                            .is_some_and(|p| is_source_phase_import(&nodes1[p], &nodes1))
                            == nodes2[n2]
                                .parent
                                .is_some_and(|p| is_source_phase_import(&nodes2[p], &nodes2))
                })
            || f1.module_augmentations.len() != f2.module_augmentations.len()
            || !f1
                .module_augmentations
                .iter()
                .zip(f2.module_augmentations.iter())
                .all(|(&n1, &n2)| {
                    equal_module_augmentation_names(&nodes1[n1], &nodes2[n2], &nodes1, &nodes2)
                })
            || f1.ambient_module_names != f2.ambient_module_names
            || !equal_refs(&f1.referenced_files, &f2.referenced_files)
            || !equal_refs(&f1.type_reference_directives, &f2.type_reference_directives)
            || !equal_refs(&f1.lib_reference_directives, &f2.lib_reference_directives)
        {
            return false;
        }
        equal_check_js_directives(
            f1.check_js_directive.as_ref(),
            f2.check_js_directive.as_ref(),
        )
    }

    /// `needsImportHelpersImportSpecifier`.
    fn needs_import_helpers_import_specifier(&self, file: &LoadedSourceFile) -> bool {
        let options_for_file = self.compiler_options_for_file_nodes(file);
        if options_for_file.import_helpers != TS_TRUE {
            return false;
        }
        let nodes = file.nodes.snapshot();
        let sf = nodes[file.file].as_source_file();
        let is_java_script_file = is_source_file_js(sf);
        let is_external_module_file = is_external_module(sf);
        if !is_java_script_file
            && (sf.is_declaration_file
                || (!options_for_file.get_isolated_modules() && !is_external_module_file))
        {
            return false;
        }
        true
    }

    /// `jsxRuntimeImportSpecifier` (the file-scanning variant).
    fn jsx_runtime_import_specifier_for(&self, file: &LoadedSourceFile) -> String {
        let nodes = file.nodes.snapshot();
        let sf = nodes[file.file].as_source_file();
        if !is_source_file_js(sf) && sf.script_kind != ScriptKind::Tsx {
            return String::new();
        }
        let file_has_name = new_has_file_name(sf.file_name().clone(), sf.path_key().clone());
        let options_for_file = self.mapper().get_compiler_options_for_file(&file_has_name);
        tsc_ast::get_jsx_runtime_import(
            &tsc_ast::get_jsx_implicit_import_base(&options_for_file, Some(sf)),
            &options_for_file,
        )
    }

    /// `projectReferenceFileMapper.getCompilerOptionsForFile` for a
    /// `LoadedSourceFile`.
    fn compiler_options_for_file_nodes(&self, file: &LoadedSourceFile) -> Arc<CompilerOptions> {
        let nodes = file.nodes.snapshot();
        let sf = nodes[file.file].as_source_file();
        let file_has_name = new_has_file_name(sf.file_name().clone(), sf.path_key().clone());
        drop(nodes);
        self.mapper().get_compiler_options_for_file(&file_has_name)
    }

    // -- Accessors ------------------------------------------------------------

    /// `SourceFiles` / `GetSourceFiles`.
    pub fn source_files(&self) -> Vec<NodeId> {
        self.source_file_ids.clone()
    }

    /// The `[]*ast.SourceFile` slice — borrowed.
    pub fn source_files_slice(&self) -> &[NodeId] {
        &self.source_file_ids
    }

    /// Per-file `(NodeId, arena)` pairs.
    pub fn source_file_entries(&self) -> Vec<LoadedSourceFile> {
        self.processed.files.clone()
    }

    /// `DuplicateSourceFiles`.
    pub fn duplicate_source_files(&self) -> &[crate::file_loader::DuplicateSourceFile] {
        &self.duplicate_source_files
    }

    /// `Options` — the `&CompilerOptions` view (the trait impl returns `Rc`).
    pub fn options_ref(&self) -> &CompilerOptions {
        &self.options
    }

    /// `Options` — `Rc` view (`checker::Program::options`).
    pub fn options_rc(&self) -> Rc<CompilerOptions> {
        self.options.clone()
    }

    /// `GetContentMapper` — the content mapper that produced the given
    /// source file, or `None` if the file was not produced by a content
    /// mapper.
    pub fn get_content_mapper(&self, file: NodeId) -> Option<Arc<tsc_contentmapper::Mapper>> {
        let nodes = self.arena_of(file);
        let sf = nodes[file].as_source_file();
        let content_mapper = sf.content_mapper().to_string();
        let file_name = sf.file_name().clone();
        drop(nodes);
        if content_mapper.is_empty() {
            return None;
        }
        let mapper = self
            .opts
            .config
            .get_content_mapper_for_file_name(&file_name)?;
        if mapper.identity() == content_mapper {
            return Some(mapper.clone());
        }
        None
    }

    /// `ContentMapperExtensions`.
    pub fn content_mapper_extensions(&self) -> &[String] {
        self.opts.config.content_mapper_extensions()
    }

    /// `CommandLine` / `config`.
    pub fn command_line(&self) -> &Arc<ParsedCommandLine> {
        &self.opts.config
    }

    /// `p.opts.Config` — used by include/file-include plumbing.
    pub fn config(&self) -> &Arc<ParsedCommandLine> {
        &self.opts.config
    }

    /// `Host`.
    pub fn host(&self) -> &Arc<dyn crate::host::CompilerHost> {
        &self.hosts.host
    }

    /// `Tracing`.
    pub fn tracing(&self) -> Option<Arc<Tracing>> {
        self.hosts.tracing.clone()
    }

    /// `GetConfigFileParsingDiagnostics`.
    pub fn get_config_file_parsing_diagnostics(&self) -> Vec<DiagnosticRef> {
        self.opts.config.get_config_file_parsing_diagnostics()
    }

    /// `GetUnresolvedImports` — cached, computed once.
    pub fn get_unresolved_imports(&self) -> Rc<HashSet<String>> {
        self.unresolved_imports
            .get_or_init(|| Rc::new(self.extract_unresolved_imports()))
            .clone()
    }

    /// `extractUnresolvedImports`.
    fn extract_unresolved_imports(&self) -> HashSet<String> {
        let mut unresolved_set = HashSet::new();
        for &source_file in &self.source_file_ids {
            for imp in self.extract_unresolved_imports_from_source_file(source_file) {
                unresolved_set.insert(imp);
            }
        }
        unresolved_set
    }

    /// `extractUnresolvedImportsFromSourceFile`.
    fn extract_unresolved_imports_from_source_file(&self, file: NodeId) -> Vec<String> {
        let mut unresolved_imports = Vec::new();
        let path_key = {
            let nodes = self.arena_of(file);
            nodes[file].as_source_file().path_key().clone()
        };
        if let Some(resolved_modules) = self.resolved_modules.get(&path_key) {
            for (cache_key, resolution) in resolved_modules {
                let resolved = resolution.as_ref().is_some_and(|r| r.is_resolved());
                if (!resolved
                    || !tsc_tspath::extension_is_one_of(
                        &resolution
                            .as_ref()
                            .map(|r| r.extension.clone())
                            .unwrap_or_default(),
                        &tsc_tspath::SUPPORTED_TS_EXTENSIONS_WITH_JSON_FLAT
                            .iter()
                            .map(|s| *s)
                            .collect::<Vec<_>>(),
                    ))
                    && !tsc_tspath::is_external_module_name_relative(&cache_key.name)
                {
                    unresolved_imports.push(cache_key.name.clone());
                }
            }
        }
        unresolved_imports
    }

    /// `SingleThreaded`.
    pub fn single_threaded(&self) -> bool {
        self.opts
            .single_threaded
            .default_if_unknown(self.options.single_threaded)
            == TS_TRUE
    }

    /// `BindSourceFiles`.
    pub fn bind_source_files(&self) {
        // PORT: sequential — `Rc`/`RefCell` arenas are not `Send`.
        // The global symbol arena is borrowed for the whole pass; per-file
        // binds append so `SymbolId`s are program-wide (SPEC §5.2).
        let mut symbols = self.symbols.clone();
        for &file in &self.source_file_ids {
            let needs_bind = {
                let nodes = self.arena_of(file);
                !nodes[file].as_source_file().is_bound()
            };
            if needs_bind {
                let trace_done = push(
                    self.hosts.tracing.as_ref(),
                    PHASE_BIND,
                    "bindSourceFile",
                    [(
                        "path".to_string(),
                        serde_json::Value::from(
                            self.arena_of(file)[file]
                                .as_source_file()
                                .path_key()
                                .as_string()
                                .to_string(),
                        ),
                    )]
                    .into_iter()
                    .collect(),
                    true,
                );
                let mut nodes = self.nodes_mut(file.file_index());
                tsc_binder::binder::bind_source_file(&mut *nodes, file, &mut symbols);
                drop(nodes);
                trace_done();
            }
        }
    }

    /// `Program::releaseCheckerPool` — PORT(addition): drops the program's
    /// pool `Rc`s. Each pooled `Checker` holds `Rc<dyn Program>` back to this
    /// program, so without this the program graph is kept alive by an `Rc`
    /// cycle even after every external reference is gone. Called from
    /// `harnessutil::CompilationResult`'s `Drop` (and any other owner that
    /// is finished with a program); checker lookups after release panic.
    pub fn release_checker_pool(&self) {
        self.compiler_checker_pool.borrow_mut().take();
        self.checker_pool.borrow_mut().take();
    }

    /// `GetTypeChecker` — the type checker associated with the program.
    pub fn get_type_checker(&self, ctx: Context) -> (Rc<RefCell<Checker>>, DoneFn) {
        if let Some(pool) = self.compiler_checker_pool.borrow().as_ref() {
            return pool.get_checker_non_exclusive();
        }
        self.get_checker_pool().get_checker(ctx, None)
    }

    /// `ForEachCheckerParallel` — sequential under the single-threaded port.
    pub fn for_each_checker_parallel(&self, cb: &mut dyn FnMut(usize, &Rc<RefCell<Checker>>)) {
        if let Some(pool) = self.compiler_checker_pool.borrow().as_ref() {
            pool.for_each_checker_parallel(cb);
        }
    }

    /// `GetTypeCheckerForFile` — the checker tasked with checking `file`.
    /// Do not mix types from different checkers.
    pub fn get_type_checker_for_file(
        &self,
        ctx: Context,
        file: NodeId,
    ) -> (Rc<RefCell<Checker>>, DoneFn) {
        if let Some(pool) = self.compiler_checker_pool.borrow().as_ref() {
            return pool.get_checker_for_file_non_exclusive(file);
        }
        self.get_checker_pool().get_checker(ctx, Some(file))
    }

    /// `GetTypeCheckerForFileExclusive` — the file's checker, held for the
    /// caller's exclusive use until `done` is called.
    pub fn get_type_checker_for_file_exclusive(
        &self,
        ctx: Context,
        file: NodeId,
    ) -> (Rc<RefCell<Checker>>, DoneFn) {
        if let Some(pool) = self.compiler_checker_pool.borrow().as_ref() {
            return pool.get_checker_for_file_exclusive(ctx, file);
        }
        self.get_checker_pool().get_checker(ctx, Some(file))
    }

    /// `GetResolvedModule`.
    pub fn get_resolved_module(
        &self,
        file: &dyn HasFileName,
        module_reference: &str,
        mode: ResolutionMode,
    ) -> Option<ResolvedModule> {
        if let Some(resolutions) = self.resolved_modules.get(file.path_key()) {
            if let Some(resolved) = resolutions.get(&ModeAwareCacheKey {
                name: module_reference.to_string(),
                mode,
            }) {
                return resolved.clone();
            }
        }
        None
    }

    /// `GetResolvedModuleFromModuleSpecifier` (`ast.HasFileName` variant).
    pub fn get_resolved_module_from_module_specifier_has(
        &self,
        file: &dyn HasFileName,
        module_specifier: NodeId,
    ) -> Option<ResolvedModule> {
        let nodes = self.arena_of(module_specifier);
        if !is_string_literal_like(&nodes[module_specifier]) {
            panic!("moduleSpecifier must be a StringLiteralLike")
        }
        if nodes[module_specifier]
            .parent
            .is_some_and(|p| is_source_phase_import(&nodes[p], &nodes))
        {
            return None;
        }
        let text = nodes[module_specifier].text(&nodes).to_string();
        drop(nodes);
        let mode = self.get_mode_for_usage_location(file, module_specifier);
        self.get_resolved_module(file, &text, mode)
    }

    /// `GetResolvedModuleFromModuleSpecifier` (`NodeId` file variant).
    pub fn get_resolved_module_from_module_specifier(
        &self,
        file: NodeId,
        module_specifier: NodeId,
    ) -> Option<ResolvedModule> {
        self.get_resolved_module_from_module_specifier_has(
            &self.file_has_file_name(file),
            module_specifier,
        )
    }

    /// `GetResolvedModules`.
    pub fn resolved_modules_map(
        &self,
    ) -> &FxHashMap<PathKey, ModeAwareCache<Option<ResolvedModule>>> {
        &self.resolved_modules
    }

    /// `ModuleResolutionError` — always `None` here (see header PORT note).
    pub fn module_resolution_error(&self) -> Option<&str> {
        self.module_resolution_error.as_deref()
    }

    /// `GetPackagesMap` — lazily cached map of package names to whether they
    /// bundle types; used by incremental diagnostic repopulation.
    pub fn packages_map(&self) -> FxHashMap<String, bool> {
        self.packages_map
            .get_or_init(|| {
                let mut packages_map = FxHashMap::default();
                for resolved_modules_in_file in self.resolved_modules.values() {
                    for m in resolved_modules_in_file.values() {
                        if let Some(m) = m {
                            if !m.package_id.name.is_empty() {
                                let entry = packages_map
                                    .entry(m.package_id.name.clone())
                                    .or_insert(false);
                                *entry = *entry || m.extension == tsc_tspath::EXTENSION_DTS;
                            }
                        }
                    }
                }
                Rc::new(packages_map)
            })
            .as_ref()
            .clone()
    }

    // -- Diagnostics collection ------------------------------------------------

    /// `collectDiagnostics` — a single file (`Some`) or all files (`None`).
    fn collect_diagnostics(
        &self,
        ctx: Context,
        source_file: Option<NodeId>,
        collect: &mut dyn FnMut(Context, NodeId) -> Vec<DiagnosticRef>,
    ) -> Vec<DiagnosticRef> {
        let result = match source_file {
            Some(file) => collect(ctx, file),
            None => {
                // PORT: sequential — `collect` runs per file inline.
                let mut result = Vec::new();
                for &file in &self.source_file_ids {
                    result.extend(collect(ctx.clone(), file));
                }
                result
            }
        };
        self.filter_and_sort_diagnostics(result)
    }

    /// `collectCheckerDiagnostics` — like `collectDiagnostics` but the
    /// callback receives the checker for each file. Files are grouped by
    /// checker under the compiler pool; external pools fall back to
    /// per-file collection.
    fn collect_checker_diagnostics(
        &self,
        ctx: Context,
        source_file: Option<NodeId>,
        collect: &mut dyn FnMut(Context, &Rc<RefCell<Checker>>, NodeId) -> Vec<DiagnosticRef>,
    ) -> Vec<DiagnosticRef> {
        if let Some(source_file) = source_file {
            if self.skip_type_checking(source_file, false) {
                return Vec::new();
            }
            let (c, done) = self.get_type_checker_for_file_exclusive(ctx.clone(), source_file);
            let result = collect(ctx, &c, source_file);
            done();
            return self.filter_and_sort_diagnostics(result);
        }
        self.filter_and_sort_diagnostics(
            self.collect_checker_diagnostics_from_files(ctx, &self.source_file_ids, collect)
                .into_iter()
                .flatten()
                .collect(),
        )
    }

    /// `collectCheckerDiagnosticsFromFiles`.
    fn collect_checker_diagnostics_from_files(
        &self,
        ctx: Context,
        source_files: &[NodeId],
        collect: &mut dyn FnMut(Context, &Rc<RefCell<Checker>>, NodeId) -> Vec<DiagnosticRef>,
    ) -> Vec<Vec<DiagnosticRef>> {
        let mut diagnostics: Vec<Vec<DiagnosticRef>> = vec![Vec::new(); source_files.len()];
        let __collect_t = std::time::Instant::now();
        if let Some(pool) = self.compiler_checker_pool.borrow().as_ref().cloned() {
            pool.for_each_checker_group_do(
                ctx.clone(),
                source_files,
                self.single_threaded(),
                &mut |c, file_index, file| {
                    let __t = std::time::Instant::now();
                    diagnostics[file_index] = collect(ctx.clone(), c, file);
                    if std::env::var("TSC_FILE_TIME").is_ok() {
                        eprintln!("[cb-inner] {:?} file_idx={}", __t.elapsed(), file_index);
                    }
                },
            );
        } else {
            for (i, &file) in source_files.iter().enumerate() {
                if self.skip_type_checking(file, false) {
                    continue;
                }
                let __ft = std::time::Instant::now();
                let (c, done) = self.get_checker_pool().get_checker(ctx.clone(), Some(file));
                if std::env::var("TSC_FILE_TIME").is_ok() {
                    eprintln!("[get-checker] {:?}", __ft.elapsed());
                }
                diagnostics[i] = collect(ctx.clone(), &c, file);
                done();
            }
        }
        if std::env::var("TSC_FILE_TIME").is_ok() {
            eprintln!("[collect-all] {:?}", __collect_t.elapsed());
        }
        diagnostics
    }

    /// `GetSyntacticDiagnostics`.
    pub fn get_syntactic_diagnostics(
        &self,
        ctx: Context,
        source_file: Option<NodeId>,
    ) -> Vec<DiagnosticRef> {
        self.collect_diagnostics(ctx, source_file, &mut |_ctx, file| {
            let nodes = self.arena_of(file);
            let sf = nodes[file].as_source_file();
            let mut diags: Vec<DiagnosticRef> = sf
                .diagnostics()
                .iter()
                .chain(sf.js_diagnostics().iter())
                .cloned()
                .collect();
            // For JS files that won't be checked by the checker (no checkJs/ts-check), we need
            // program-level syntactic checks that require compiler options. This mirrors Strada's
            // getJSSyntacticDiagnosticsForFile in program.ts.
            if is_source_file_js(sf) && !is_check_js_enabled_for_file(sf, &self.options) {
                drop(nodes);
                diags.extend(get_additional_js_syntactic_diagnostics(self, file));
            }
            diags
        })
    }

    /// `GetBindDiagnostics`.
    pub fn get_bind_diagnostics(
        &self,
        ctx: Context,
        source_file: Option<NodeId>,
    ) -> Vec<DiagnosticRef> {
        if let Some(source_file) = source_file {
            let mut nodes = self.nodes_mut(source_file.file_index());
            let mut symbols = self.symbols.clone();
            tsc_binder::binder::bind_source_file(&mut *nodes, source_file, &mut symbols);
        } else {
            self.bind_source_files();
        }
        self.collect_diagnostics(ctx, source_file, &mut |_ctx, file| {
            let nodes = self.arena_of(file);
            nodes[file].as_source_file().bind_diagnostics().to_vec()
        })
    }

    /// `GetSemanticDiagnostics`.
    pub fn get_semantic_diagnostics(
        &self,
        ctx: Context,
        source_file: Option<NodeId>,
    ) -> Vec<DiagnosticRef> {
        self.collect_checker_diagnostics(ctx, source_file, &mut |ctx, c, file| {
            self.get_semantic_diagnostics_with_checker(ctx, c, file)
        })
    }

    /// `GetSemanticDiagnosticsForIncremental` — includes newly discovered
    /// globals in each file's cached diagnostics; `noEmit` filtering is the
    /// builder's concern.
    pub fn get_semantic_diagnostics_for_incremental(
        &self,
        ctx: Context,
        source_files: &[NodeId],
    ) -> FxHashMap<NodeId, Vec<DiagnosticRef>> {
        let all_diags =
            self.collect_checker_diagnostics_from_files(ctx, source_files, &mut |ctx, c, file| {
                self.get_bind_and_check_diagnostics_with_checker(ctx, c, file, true)
            });
        let mut result =
            FxHashMap::with_capacity_and_hasher(source_files.len(), Default::default());
        for (i, diags) in all_diags.into_iter().enumerate() {
            result.insert(source_files[i], self.filter_and_sort_diagnostics(diags));
        }
        result
    }

    /// `GetSuggestionDiagnostics`.
    pub fn get_suggestion_diagnostics(
        &self,
        ctx: Context,
        source_file: Option<NodeId>,
    ) -> Vec<DiagnosticRef> {
        self.collect_checker_diagnostics(ctx, source_file, &mut |ctx, c, file| {
            self.get_suggestion_diagnostics_with_checker(ctx, c, file)
        })
    }

    /// `GetProgramDiagnostics`.
    pub fn get_program_diagnostics(&self) -> Vec<DiagnosticRef> {
        let mut all: Vec<DiagnosticRef> = self.program_diagnostics.borrow().clone();
        all.extend(self.content_mapper_diagnostics.iter().cloned());
        all.extend(
            self.content_mapper_option_diagnostics
                .borrow()
                .iter()
                .cloned(),
        );
        all.extend(
            self.include_processor
                .get_diagnostics(self)
                .get_global_diagnostics(),
        );
        sort_and_deduplicate_diagnostics(all)
    }

    /// `collectContentMapperOptionDiagnostics`.
    fn collect_content_mapper_option_diagnostics(&self) {
        let Some(project) = self.content_mapper_project() else {
            return;
        };
        let option_diagnostics = project.diagnostics();
        let mut out = self.content_mapper_option_diagnostics.borrow_mut();
        for diagnostic in &option_diagnostics {
            let (file, loc) = match get_content_mapper_option_diagnostic_location(
                Some(&self.opts.config),
                &diagnostic.mapper,
                &diagnostic.path,
            ) {
                Some((ctx, loc)) => (Some(DiagnosticFile::from_node(ctx.file, ctx.nodes)), loc),
                None => (None, TextRange::default()),
            };
            out.push(new_external_diagnostic(
                file,
                loc,
                diagnostic.source.clone(),
                Category::Error,
                diagnostic.code,
                diagnostic.message_text.clone(),
            ));
        }
    }

    /// `GetIncludeProcessorDiagnostics`.
    pub fn get_include_processor_diagnostics(&self, source_file: NodeId) -> Vec<DiagnosticRef> {
        if self.skip_type_checking(source_file, false) {
            return Vec::new();
        }
        let nodes = self.arena_of(source_file);
        let diags = self
            .include_processor
            .get_diagnostics(self)
            .get_diagnostics_for_file(&DiagnosticFile::from_node(source_file, &nodes));
        drop(nodes);
        let (filtered, _) = self.get_diagnostics_with_preceding_directives(source_file, diags);
        filtered
    }

    /// `SkipTypeChecking`.
    pub fn skip_type_checking(&self, source_file: NodeId, ignore_no_check: bool) -> bool {
        let nodes = self.arena_of(source_file);
        let sf = nodes[source_file].as_source_file();
        (!ignore_no_check && self.options.no_check == TS_TRUE)
            || self.options.skip_lib_check == TS_TRUE && sf.is_declaration_file
            || self.options.skip_default_lib_check == TS_TRUE
                && self.is_source_file_default_library(sf.path_key())
            || self.is_source_from_project_reference(sf.path_key())
            || !self.can_include_bind_and_check_diagnostics(sf)
    }

    /// `canIncludeBindAndCheckDiagnostics`.
    fn can_include_bind_and_check_diagnostics(&self, source_file: &tsc_ast::SourceFile) -> bool {
        if let Some(directive) = &source_file.check_js_directive {
            if !directive.enabled {
                return false;
            }
        }

        if source_file.script_kind == ScriptKind::Ts || source_file.script_kind == ScriptKind::Tsx {
            return true;
        }

        let is_js =
            source_file.script_kind == ScriptKind::Js || source_file.script_kind == ScriptKind::Jsx;
        let is_check_js = is_js && is_check_js_enabled_for_file(source_file, &self.options);
        let is_plain_js = is_plain_js_file(Some(source_file), self.options.check_js);

        // By default, only type-check .ts, .tsx, plain JS, and checked JS
        // - plain JS: .js files with no // ts-check and checkJs: undefined
        // - check JS: .js files with either // ts-check or checkJs: true
        is_plain_js || is_check_js
    }

    /// `getSourceFilesToEmit`.
    fn get_source_files_to_emit(
        &self,
        target_source_files: Option<Vec<NodeId>>,
        force_dts_emit: bool,
        force_js_emit: bool,
    ) -> Vec<NodeId> {
        if target_source_files.is_none() && !force_dts_emit && !force_js_emit {
            if self.source_files_to_emit.borrow().is_none() {
                *self.source_files_to_emit.borrow_mut() =
                    Some(Rc::new(get_source_files_to_emit(self, None, false, false)));
            }
            return self
                .source_files_to_emit
                .borrow()
                .as_ref()
                .unwrap()
                .as_ref()
                .clone();
        }
        get_source_files_to_emit(self, target_source_files, force_dts_emit, force_js_emit)
    }

    /// `verifyCompilerOptions`.
    fn verify_compiler_options(&self) {
        let options = self.options.clone();

        let source_file_ctx = || self.opts.config.config_file.as_ref().map(|cf| cf.as_ctx());
        let config_file_path = || -> RootedFilePath {
            source_file_ctx()
                .map(|ctx| ctx.nodes[ctx.file].as_source_file().file_name().clone())
                .unwrap_or_default()
        };

        // `getCompilerOptionsPropertySyntax` — `(name, initializer)` node ids
        // of the top-level "compilerOptions" property.
        let get_compiler_options_property_syntax =
            || -> Option<(Option<NodeId>, Option<NodeId>)> {
                for_each_ts_config_prop_array(
                    source_file_ctx(),
                    "compilerOptions",
                    &mut |property| Some((property.named_member_base.name, property.initializer)),
                )
            };

        let get_compiler_options_object_literal_syntax = || -> Option<NodeId> {
            let (_, initializer) = get_compiler_options_property_syntax()?;
            let initializer = initializer?;
            source_file_ctx().and_then(|ctx| {
                if ctx.nodes[initializer].kind == tsc_ast::Kind::ObjectLiteralExpression {
                    Some(initializer)
                } else {
                    None
                }
            })
        };

        let mut create_option_diagnostic_in_object_literal_syntax =
            |object_literal: Option<NodeId>,
             on_key: bool,
             key1: &str,
             key2: Option<&str>,
             message: &'static diagnostics::Message,
             args: &[Value]|
             -> Option<DiagnosticRef> {
                let ctx = source_file_ctx()?;
                let diag = for_each_property_assignment(
                    object_literal,
                    ctx,
                    key1,
                    &mut |property| {
                        Some(
                            tsc_tsoptions::errors::create_diagnostic_for_node_in_source_file(
                                ctx,
                                if on_key {
                                    property
                                        .named_member_base
                                        .name
                                        .unwrap_or(property.initializer.unwrap_or_default())
                                } else {
                                    property.initializer.unwrap_or_default()
                                },
                                message,
                                args,
                            ),
                        )
                    },
                    key2,
                );
                if let Some(diag) = &diag {
                    self.program_diagnostics.borrow_mut().push(diag.clone());
                }
                diag
            };

        macro_rules! create_compiler_options_diagnostic {
            ($message:expr, $args:expr) => {{
                let diag = if let Some((name, _)) = get_compiler_options_property_syntax() {
                    if let Some(ctx) = source_file_ctx() {
                        tsc_tsoptions::errors::create_diagnostic_for_node_in_source_file(
                            ctx,
                            name.unwrap_or_default(),
                            $message,
                            $args,
                        )
                    } else {
                        new_compiler_diagnostic($message, $args)
                    }
                } else {
                    new_compiler_diagnostic($message, $args)
                };
                self.program_diagnostics.borrow_mut().push(diag.clone());
                diag
            }};
        }

        macro_rules! create_diagnostic_for_option {
            ($on_key:expr, $option1:expr, $option2:expr, $message:expr, $args:expr) => {{
                let option2: Option<&str> = if ($option2).is_empty() {
                    None
                } else {
                    Some($option2)
                };
                match create_option_diagnostic_in_object_literal_syntax(
                    get_compiler_options_object_literal_syntax(),
                    $on_key,
                    $option1,
                    option2,
                    $message,
                    $args,
                ) {
                    Some(diag) => diag,
                    None => create_compiler_options_diagnostic!($message, $args),
                }
            }};
        }

        macro_rules! create_diagnostic_for_option_name {
            ($message:expr, $option1:expr, $option2:expr $(, $extra:expr)*) => {{
                let mut args: Vec<Value> = vec![
                    Value::Str($option1.to_string()),
                    Value::Str($option2.to_string()),
                ];
                $(args.push(Value::Str($extra.to_string()));)*
                create_diagnostic_for_option!(true, $option1, $option2, $message, &args)
            }};
        }

        macro_rules! create_option_value_diagnostic {
            ($option1:expr, $message:expr $(, $extra:expr)*) => {{
                let args: Vec<Value> = vec![$(Value::Str($extra.to_string()),)*];
                create_diagnostic_for_option!(false, $option1, "", $message, &args)
            }};
        }

        macro_rules! create_removed_option_diagnostic {
            ($name:expr, $value:expr, $use_instead:expr) => {{
                let (message, args): (&'static diagnostics::Message, Vec<Value>) = if ($value).is_empty() {
                    (
                        &diagnostics::Option_0_has_been_removed_Please_remove_it_from_your_configuration,
                        vec![Value::Str(($name).to_string())],
                    )
                } else {
                    (
                        &diagnostics::Option_0_1_has_been_removed_Please_remove_it_from_your_configuration,
                        vec![
                            Value::Str(($name).to_string()),
                            Value::Str(($value).to_string()),
                        ],
                    )
                };
                let diag = create_diagnostic_for_option!(
                    ($value).is_empty(),
                    $name,
                    "",
                    message,
                    &args
                );
                if !($use_instead).is_empty() {
                    lock_diagnostic(&diag).add_message_chain(Some(new_compiler_diagnostic(
                        &diagnostics::Use_0_instead,
                        &[($use_instead).to_string()],
                    )));
                }
            }};
        }

        // Removed in TS7

        if !options.base_url.is_empty() {
            // BaseUrl will have been turned absolute by this point.
            let mut use_instead = String::new();
            if !config_file_path().is_empty() {
                let mut relative = tsc_tspath::get_relative_path_from_file(
                    config_file_path().as_string(),
                    options.base_url.as_string(),
                    self.case_sensitivity,
                );
                if !(relative.starts_with("./") || relative.starts_with("../")) {
                    relative = format!("./{}", relative);
                }
                let suggestion = tsc_tspath::combine_paths(&relative, &["*"]);
                use_instead = format!(
                    "\"paths\": {{\"*\": [{}]}}",
                    serde_json::to_string(&suggestion).unwrap_or_default()
                );
            }
            create_removed_option_diagnostic!("baseUrl", "", use_instead);
        }

        if !options.out_file.is_empty() {
            create_removed_option_diagnostic!("outFile", "", "");
        }

        if options.target == ScriptTarget::ES5 {
            create_removed_option_diagnostic!("target", "ES5", "");
        }

        if options.module == ModuleKind::AMD {
            create_removed_option_diagnostic!("module", "AMD", "");
        }
        if options.module == ModuleKind::System {
            create_removed_option_diagnostic!("module", "System", "");
        }
        if options.module == ModuleKind::UMD {
            create_removed_option_diagnostic!("module", "UMD", "");
        }

        if options.module_resolution == ModuleResolutionKind::Classic {
            create_removed_option_diagnostic!("moduleResolution", "Classic", "");
        }

        if options.always_strict.is_false() {
            create_removed_option_diagnostic!("alwaysStrict", "false", "");
        }

        if options.es_module_interop.is_false() {
            create_removed_option_diagnostic!("esModuleInterop", "false", "");
        }

        if options.allow_synthetic_default_imports.is_false() {
            create_removed_option_diagnostic!("allowSyntheticDefaultImports", "false", "");
        }

        if options.module_resolution == ModuleResolutionKind::Node10 {
            create_removed_option_diagnostic!("moduleResolution", "node10", "");
        }

        if !options.downlevel_iteration.is_unknown() {
            create_removed_option_diagnostic!("downlevelIteration", "", "");
        }

        if options.strict_property_initialization == TS_TRUE
            && !options.get_strict_option_value(options.strict_null_checks)
        {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1,
                "strictPropertyInitialization",
                "strictNullChecks"
            );
        }
        if options.exact_optional_property_types == TS_TRUE
            && !options.get_strict_option_value(options.strict_null_checks)
        {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1,
                "exactOptionalPropertyTypes",
                "strictNullChecks"
            );
        }

        if options.isolated_declarations == TS_TRUE {
            if options.get_allow_js() {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_cannot_be_specified_with_option_1,
                    "allowJs",
                    "isolatedDeclarations"
                );
            }
            if !options.get_emit_declarations() {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1_or_option_2,
                    "isolatedDeclarations",
                    "declaration",
                    "composite"
                );
            }
        }

        if options.inline_source_map == TS_TRUE {
            if options.source_map == TS_TRUE {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_cannot_be_specified_with_option_1,
                    "sourceMap",
                    "inlineSourceMap"
                );
            }
            if !options.map_root.is_empty() {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_cannot_be_specified_with_option_1,
                    "mapRoot",
                    "inlineSourceMap"
                );
            }
        }

        if options.composite == TS_TRUE {
            if options.declaration.is_false() {
                create_diagnostic_for_option_name!(
                    &diagnostics::Composite_projects_may_not_disable_declaration_emit,
                    "declaration",
                    ""
                );
            }
            if options.incremental.is_false() {
                create_diagnostic_for_option_name!(
                    &diagnostics::Composite_projects_may_not_disable_incremental_compilation,
                    "declaration",
                    ""
                );
            }
        }

        if options.ts_build_info_file.is_empty()
            && options.incremental == TS_TRUE
            && options.config_file_path.is_empty()
        {
            create_compiler_options_diagnostic!(
                &diagnostics::Option_incremental_is_only_valid_with_a_known_configuration_file_like_tsconfig_json_or_when_tsBuildInfoFile_is_explicitly_provided,
                &[] as &[Value]
            );
        }

        self.verify_project_references();

        if options.composite == TS_TRUE {
            let mut root_paths: HashSet<PathKey> = HashSet::new();
            for file_name in self.opts.config.file_names() {
                root_paths.insert(self.case_sensitivity.path_key(&file_name.as_path()));
            }

            for &file in &self.source_file_ids {
                let (root_path, file_name) = {
                    let nodes = self.arena_of(file);
                    let sf = nodes[file].as_source_file();
                    let mut root_path = sf.path_key().clone();
                    let canonical = sf.canonical_source_file();
                    let file_name = sf.file_name().clone();
                    drop(nodes);
                    if let Some(canonical) = canonical {
                        // `canonical` is a NodeId in the CANONICAL file's
                        // arena — index it there, not in `file`'s arena.
                        root_path = self.arena_of(canonical)[canonical]
                            .as_source_file()
                            .path_key()
                            .clone();
                    }
                    (root_path, file_name)
                };
                if source_file_may_be_emitted(file, self, false, false)
                    && !root_paths.contains(&root_path)
                {
                    self.add_processing_diagnostic(ProcessingDiagnostic::ExplainingFileInclude(
                        Box::new(IncludeExplainingDiagnostic {
                            file: root_path.clone(),
                            diagnostic_reason: None,
                            message: &diagnostics::File_0_is_not_listed_within_the_file_list_of_project_1_Projects_must_list_all_files_or_use_an_include_pattern,
                            args: vec![
                                file_name.as_string().to_string(),
                                config_file_path().as_string().to_string(),
                            ],
                        }),
                    ));
                }
            }
        }

        let for_each_option_paths_syntax = |callback: &mut dyn FnMut(
            &tsc_ast::ast_generated::PropertyAssignment,
        )
            -> Option<DiagnosticRef>| {
            source_file_ctx().and_then(|ctx| {
                for_each_property_assignment(
                    get_compiler_options_object_literal_syntax(),
                    ctx,
                    "paths",
                    callback,
                    None,
                )
            })
        };

        // `createDiagnosticForOptionPaths`.
        macro_rules! create_diagnostic_for_option_paths {
            ($on_key:expr, $key:expr, $message:expr, $args:expr) => {{
                let ctx_opt = source_file_ctx();
                let diag = for_each_option_paths_syntax(&mut |path_prop| {
                    let initializer = path_prop.initializer?;
                    let ctx = ctx_opt?;
                    if ctx.nodes[initializer].kind == tsc_ast::Kind::ObjectLiteralExpression {
                        return create_option_diagnostic_in_object_literal_syntax(
                            Some(initializer),
                            $on_key,
                            $key,
                            None,
                            $message,
                            $args,
                        );
                    }
                    None
                });
                match diag {
                    Some(d) => d,
                    None => create_compiler_options_diagnostic!($message, $args),
                }
            }};
        }

        // `createDiagnosticForOptionPathKeyValue`.
        macro_rules! create_diagnostic_for_option_path_key_value {
            ($key:expr, $value_index:expr, $message:expr, $args:expr) => {{
                let ctx_opt = source_file_ctx();
                let diag = for_each_option_paths_syntax(&mut |path_prop| {
                    let initializer = path_prop.initializer?;
                    let ctx = ctx_opt?;
                    if ctx.nodes[initializer].kind != tsc_ast::Kind::ObjectLiteralExpression {
                        return None;
                    }
                    for_each_property_assignment(
                        Some(initializer),
                        ctx,
                        $key,
                        &mut |key_props| {
                            let arr = key_props.initializer?;
                            if ctx.nodes[arr].kind == tsc_ast::Kind::ArrayLiteralExpression {
                                let elements = ctx.nodes[arr]
                                    .as_array_literal_expression()
                                    .elements
                                    .as_ref()
                                    .map(|l| &l.nodes[..])
                                    .unwrap_or(&[]);
                                if elements.len() > $value_index {
                                    let d = tsc_tsoptions::errors::create_diagnostic_for_node_in_source_file(
                                        ctx,
                                        elements[$value_index],
                                        $message,
                                        $args,
                                    );
                                    self.program_diagnostics.borrow_mut().push(d.clone());
                                    return Some(d);
                                }
                            }
                            None
                        },
                        None,
                    )
                });
                match diag {
                    Some(d) => d,
                    None => create_compiler_options_diagnostic!($message, $args),
                }
            }};
        }

        if let Some(paths) = &options.paths {
            for (key, value) in paths.entries() {
                // !!! This code does not handle cases where where the path mappings have the wrong types,
                // as that information is mostly lost during the parsing process.
                if !has_zero_or_one_asterisk_character(key) {
                    create_diagnostic_for_option_paths!(
                        true,
                        key,
                        &diagnostics::Pattern_0_can_have_at_most_one_Asterisk_character,
                        &[Value::Str(key.clone())]
                    );
                }
                match value {
                    None => {
                        create_diagnostic_for_option_paths!(
                            false,
                            key,
                            &diagnostics::Substitutions_for_pattern_0_should_be_an_array,
                            &[Value::Str(key.clone())]
                        );
                    }
                    Some(value) if value.is_empty() => {
                        create_diagnostic_for_option_paths!(
                            false,
                            key,
                            &diagnostics::Substitutions_for_pattern_0_shouldn_t_be_an_empty_array,
                            &[Value::Str(key.clone())]
                        );
                    }
                    Some(value) => {
                        for (i, subst) in value.iter().enumerate() {
                            if !has_zero_or_one_asterisk_character(subst) {
                                create_diagnostic_for_option_path_key_value!(
                                    key,
                                    i,
                                    &diagnostics::Substitution_0_in_pattern_1_can_have_at_most_one_Asterisk_character,
                                    &[Value::Str(subst.clone()), Value::Str(key.clone())]
                                );
                            }
                            if !tsc_tspath::path_is_relative(subst)
                                && !tsc_tspath::path_is_absolute(subst)
                            {
                                create_diagnostic_for_option_path_key_value!(
                                    key,
                                    i,
                                    &diagnostics::Non_relative_paths_are_not_allowed_Did_you_forget_a_leading_Slash,
                                    &[] as &[Value]
                                );
                            }
                        }
                    }
                }
            }
        }

        if options.source_map.is_false_or_unknown()
            && options.inline_source_map.is_false_or_unknown()
        {
            if options.inline_sources == TS_TRUE {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_can_only_be_used_when_either_option_inlineSourceMap_or_option_sourceMap_is_provided,
                    "inlineSources",
                    ""
                );
            }
            if !options.source_root.is_empty() {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_can_only_be_used_when_either_option_inlineSourceMap_or_option_sourceMap_is_provided,
                    "sourceRoot",
                    ""
                );
            }
        }

        if !options.map_root.is_empty()
            && !(options.source_map == TS_TRUE || options.declaration_map == TS_TRUE)
        {
            // Error to specify --mapRoot without --sourcemap
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1_or_option_2,
                "mapRoot",
                "sourceMap",
                "declarationMap"
            );
        }

        if !options.declaration_dir.is_empty() && !options.get_emit_declarations() {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1_or_option_2,
                "declarationDir",
                "declaration",
                "composite"
            );
        }

        if options.declaration_map == TS_TRUE && !options.get_emit_declarations() {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1_or_option_2,
                "declarationMap",
                "declaration",
                "composite"
            );
        }

        if options.lib.is_some() && options.no_lib == TS_TRUE {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_with_option_1,
                "lib",
                "noLib"
            );
        }

        if options.isolated_modules == TS_TRUE || options.verbatim_module_syntax == TS_TRUE {
            if options.preserve_const_enums.is_false() {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_preserveConstEnums_cannot_be_disabled_when_0_is_enabled,
                    if options.verbatim_module_syntax == TS_TRUE {
                        "verbatimModuleSyntax"
                    } else {
                        "isolatedModules"
                    },
                    "preserveConstEnums"
                );
            }
        }

        if !options.out_dir.is_empty()
            || !options.root_dir.is_empty()
            || !options.source_root.is_empty()
            || !options.map_root.is_empty()
            || options.get_emit_declarations() && !options.declaration_dir.is_empty()
        {
            // !!! sheetal checkSourceFilesBelongToPath - for root Dir and configFile - explaining why file is in the program
            let dir = self.common_source_directory();
            if !options.out_dir.is_empty()
                && dir.is_empty()
                && self.source_file_ids.iter().any(|&f| {
                    self.arena_of(f)[f]
                        .as_source_file()
                        .file_name()
                        .root_length()
                        > 1
                })
            {
                create_diagnostic_for_option_name!(
                    &diagnostics::Cannot_find_the_common_subdirectory_path_for_the_input_files,
                    "outDir",
                    ""
                );
            }
        }

        if options.no_emit != TS_TRUE
            && options.composite != TS_TRUE
            && options.root_dir.is_empty()
            && !options.config_file_path.is_empty()
            && (!options.out_dir.is_empty()
                || options.get_emit_declarations() && !options.declaration_dir.is_empty()
                || !options.out_file.is_empty())
        {
            // Check if rootDir inferred changed and issue diagnostic
            let dir = self.common_source_directory();
            let mut emitted_files: Vec<RootedFilePath> = Vec::new();
            for &file in &self.source_file_ids {
                let nodes = self.arena_of(file);
                let sf = nodes[file].as_source_file();
                if !sf.is_declaration_file && source_file_may_be_emitted(file, self, false, false) {
                    emitted_files.push(sf.file_name().clone());
                }
            }
            let dir59 = tsc_outputpaths::get_computed_common_source_directory(
                &emitted_files,
                self.base_directory(),
                self.case_sensitivity,
            );
            if !dir59.is_empty()
                && self
                    .case_sensitivity
                    .compare_paths(&dir.as_path(), &dir59.as_path())
                    != 0
            {
                // change in layout
                let option1 = if !options.out_file.is_empty() {
                    "outFile"
                } else if !options.out_dir.is_empty() {
                    "outDir"
                } else {
                    "declarationDir"
                };
                let option2 = if options.out_file.is_empty() && !options.out_dir.is_empty() {
                    "declarationDir"
                } else {
                    ""
                };
                let mut common_source_directory = dir59.as_string().to_string();
                if let Some(relative_path) = self
                    .case_sensitivity
                    .relative_path_from_file_to_path(&options.config_file_path, &dir59.as_path())
                {
                    common_source_directory =
                        relative_path.as_module_specifier().as_string().to_string();
                }
                let diag = create_diagnostic_for_option!(
                    true,
                    option1,
                    option2,
                    &diagnostics::The_common_source_directory_of_0_is_1_The_rootDir_setting_must_be_explicitly_set_to_this_or_another_path_to_adjust_your_output_s_file_layout,
                    &[
                        Value::Str(options.config_file_path.base_name().to_string()),
                        Value::Str(common_source_directory.clone()),
                    ]
                );
                lock_diagnostic(&diag).add_message_chain(Some(new_compiler_diagnostic(
                    &diagnostics::Visit_https_Colon_Slash_Slashaka_ms_Slashts6_for_migration_information,
                    &[] as &[String],
                )));
            }
        }

        if options.check_js == TS_TRUE && !options.get_allow_js() {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1,
                "checkJs",
                "allowJs"
            );
        }

        if options.emit_declaration_only == TS_TRUE && !options.get_emit_declarations() {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1_or_option_2,
                "emitDeclarationOnly",
                "declaration",
                "composite"
            );
        }

        if options.emit_decorator_metadata == TS_TRUE
            && options.experimental_decorators.is_false_or_unknown()
        {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1,
                "emitDecoratorMetadata",
                "experimentalDecorators"
            );
        }

        if !options.jsx_factory.is_empty() {
            if !options.react_namespace.is_empty() {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_cannot_be_specified_with_option_1,
                    "reactNamespace",
                    "jsxFactory"
                );
            }
            if options.jsx == JsxEmit::ReactJSX || options.jsx == JsxEmit::ReactJSXDev {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_cannot_be_specified_when_option_jsx_is_1,
                    "jsxFactory",
                    "",
                    options.jsx.to_string()
                );
            }
            if tsc_parser::parser::parse_isolated_entity_name(&options.jsx_factory)
                .0
                .is_none()
            {
                create_option_value_diagnostic!(
                    "jsxFactory",
                    &diagnostics::Invalid_value_for_jsxFactory_0_is_not_a_valid_identifier_or_qualified_name,
                    options.jsx_factory
                );
            }
        } else if !options.react_namespace.is_empty()
            && !tsc_scanner::utilities::is_identifier_text(
                &options.react_namespace,
                LanguageVariant::Standard,
            )
        {
            create_option_value_diagnostic!(
                "reactNamespace",
                &diagnostics::Invalid_value_for_reactNamespace_0_is_not_a_valid_identifier,
                options.react_namespace
            );
        }

        if !options.jsx_fragment_factory.is_empty() {
            if options.jsx_factory.is_empty() {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_cannot_be_specified_without_specifying_option_1,
                    "jsxFragmentFactory",
                    "jsxFactory"
                );
            }
            if options.jsx == JsxEmit::ReactJSX || options.jsx == JsxEmit::ReactJSXDev {
                create_diagnostic_for_option_name!(
                    &diagnostics::Option_0_cannot_be_specified_when_option_jsx_is_1,
                    "jsxFragmentFactory",
                    "",
                    options.jsx.to_string()
                );
            }
            if tsc_parser::parser::parse_isolated_entity_name(&options.jsx_fragment_factory)
                .0
                .is_none()
            {
                create_option_value_diagnostic!(
                    "jsxFragmentFactory",
                    &diagnostics::Invalid_value_for_jsxFragmentFactory_0_is_not_a_valid_identifier_or_qualified_name,
                    options.jsx_fragment_factory
                );
            }
        }

        if !options.react_namespace.is_empty()
            && (options.jsx == JsxEmit::ReactJSX || options.jsx == JsxEmit::ReactJSXDev)
        {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_when_option_jsx_is_1,
                "reactNamespace",
                "",
                options.jsx.to_string()
            );
        }

        if !options.jsx_import_source.is_empty() && options.jsx == JsxEmit::React {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_cannot_be_specified_when_option_jsx_is_1,
                "jsxImportSource",
                "",
                options.jsx.to_string()
            );
        }

        let module_kind = options.get_emit_module_kind();

        if options.allow_importing_ts_extensions == TS_TRUE
            && !(options.no_emit == TS_TRUE
                || options.emit_declaration_only == TS_TRUE
                || options.rewrite_relative_import_extensions == TS_TRUE)
        {
            create_option_value_diagnostic!(
                "allowImportingTsExtensions",
                &diagnostics::Option_allowImportingTsExtensions_can_only_be_used_when_one_of_noEmit_emitDeclarationOnly_or_rewriteRelativeImportExtensions_is_set
            );
        }

        let module_resolution = options.get_module_resolution_kind();
        if options.resolve_package_json_exports == TS_TRUE
            && !module_resolution_supports_package_json_exports_and_imports(module_resolution)
        {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_can_only_be_used_when_moduleResolution_is_set_to_node16_nodenext_or_bundler,
                "resolvePackageJsonExports",
                ""
            );
        }
        if options.resolve_package_json_imports == TS_TRUE
            && !module_resolution_supports_package_json_exports_and_imports(module_resolution)
        {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_can_only_be_used_when_moduleResolution_is_set_to_node16_nodenext_or_bundler,
                "resolvePackageJsonImports",
                ""
            );
        }
        if options.custom_conditions.is_some()
            && !module_resolution_supports_package_json_exports_and_imports(module_resolution)
        {
            create_diagnostic_for_option_name!(
                &diagnostics::Option_0_can_only_be_used_when_moduleResolution_is_set_to_node16_nodenext_or_bundler,
                "customConditions",
                ""
            );
        }

        if module_resolution == ModuleResolutionKind::Bundler
            && !emit_module_kind_is_non_node_esm(module_kind)
            && module_kind != ModuleKind::Preserve
            && module_kind != ModuleKind::CommonJS
        {
            create_option_value_diagnostic!(
                "moduleResolution",
                &diagnostics::Option_0_can_only_be_used_when_module_is_set_to_preserve_commonjs_or_es2015_or_later,
                "bundler"
            );
        }

        if (ModuleKind::Node16..=ModuleKind::NodeNext).contains(&module_kind)
            && !(ModuleResolutionKind::Node16..=ModuleResolutionKind::NodeNext)
                .contains(&module_resolution)
        {
            let module_kind_name = module_kind.to_string();
            let module_resolution_name =
                match tsc_core::options_generated::MODULE_KIND_TO_MODULE_RESOLUTION_KIND
                    .get(&module_kind)
                {
                    Some(v) => v.to_string(),
                    None => "Node16".to_string(),
                };
            create_option_value_diagnostic!(
                "moduleResolution",
                &diagnostics::Option_moduleResolution_must_be_set_to_0_or_left_unspecified_when_option_module_is_set_to_1,
                module_resolution_name,
                module_kind_name
            );
        } else if (ModuleResolutionKind::Node16..=ModuleResolutionKind::NodeNext)
            .contains(&module_resolution)
            && !(ModuleKind::Node16..=ModuleKind::NodeNext).contains(&module_kind)
        {
            let module_resolution_name = module_resolution.to_string();
            create_option_value_diagnostic!(
                "module",
                &diagnostics::Option_module_must_be_set_to_0_when_option_moduleResolution_is_set_to_1,
                module_resolution_name,
                module_resolution_name
            );
        }

        // If the emit is enabled make sure that every output file is unique and not overwriting any of the input files
        if options.no_emit != TS_TRUE && options.suppress_output_path_check != TS_TRUE {
            let mut emit_files_seen: HashSet<PathKey> = HashSet::new();

            // Verify that all the emit files are unique and don't overwrite input files
            // (`verifyEmitFilePath` in Go).
            let mut verify_emit_file_path = |emit_file_name: &RootedFilePath| {
                if !emit_file_name.is_empty() {
                    let emit_file_path = self.path_key_for_file_name(emit_file_name);
                    // Report error if the output overwrites input file
                    if self.files_by_path.contains_key(&emit_file_path) {
                        let diag = new_compiler_diagnostic(
                            &diagnostics::Cannot_write_file_0_because_it_would_overwrite_input_file,
                            &[emit_file_name.as_string().to_string()],
                        );
                        if config_file_path().is_empty() {
                            // The program is from either an inferred project or an external project
                            lock_diagnostic(&diag).add_message_chain(Some(new_compiler_diagnostic(
                                &diagnostics::Adding_a_tsconfig_json_file_will_help_organize_projects_that_contain_both_TypeScript_and_JavaScript_files_Learn_more_at_https_Colon_Slash_Slashaka_ms_Slashtsconfig,
                                &[] as &[String],
                            )));
                        }
                        self.block_emitting_of_file(emit_file_name.clone(), diag);
                    }

                    // Report error if multiple files write into same file
                    if emit_files_seen.contains(&emit_file_path) {
                        // Already seen the same emit file - report error
                        self.block_emitting_of_file(
                            emit_file_name.clone(),
                            new_compiler_diagnostic(
                                &diagnostics::Cannot_write_file_0_because_it_would_be_overwritten_by_multiple_input_files,
                                &[emit_file_name.as_string().to_string()],
                            ),
                        );
                    } else {
                        emit_files_seen.insert(emit_file_path);
                    }
                }
            };

            // `outputpaths.ForEachEmittedFile` — per-file arenas; see header.
            for &source_file in &self.get_source_files_to_emit(None, false, false) {
                let paths = {
                    let nodes = self.arena_of(source_file);
                    tsc_outputpaths::get_output_paths_for(
                        source_file,
                        &options,
                        self,
                        ForceEmitPaths::default(),
                        &nodes,
                    )
                };
                verify_emit_file_path(paths.js_file_path());
                verify_emit_file_path(paths.source_map_file_path());
                verify_emit_file_path(paths.declaration_file_path());
                verify_emit_file_path(paths.declaration_map_path());
            }
            verify_emit_file_path(&self.opts.config.get_build_info_file_name());
        }
    }

    /// `blockEmittingOfFile`.
    fn block_emitting_of_file(&self, emit_file_name: RootedFilePath, diag: DiagnosticRef) {
        self.has_emit_blocking_diagnostics
            .borrow_mut()
            .insert(self.path_key_for_file_name(&emit_file_name));
        self.program_diagnostics.borrow_mut().push(diag);
    }

    /// `IsEmitBlocked` — implements `printer.EmitHost`.
    pub fn is_emit_blocked(&self, emit_file_name: &RootedFilePath) -> bool {
        self.has_emit_blocking_diagnostics
            .borrow()
            .contains(&self.path_key_for_file_name(emit_file_name))
    }

    /// `verifyProjectReferences`.
    fn verify_project_references(&self) {
        let build_info_file_name = if self.options.suppress_output_path_check == TS_TRUE {
            RootedFilePath::default()
        } else {
            self.opts.config.get_build_info_file_name()
        };
        let create_diagnostic_for_reference =
            |config: &ParsedCommandLine,
             index: usize,
             message: &'static diagnostics::Message,
             args: &[Value]| {
                let diag = create_diagnostic_at_reference_syntax(config, index, message, args)
                    .unwrap_or_else(|| new_compiler_diagnostic(message, args));
                self.program_diagnostics.borrow_mut().push(diag);
            };

        self.range_resolved_project_reference(&mut |_path, config, parent, index| {
            let project_refs = parent.project_references();
            if project_refs.len() <= index {
                return true;
            }
            let ref_ = &project_refs[index];
            // !!! Deprecated in 5.0 and removed since 5.5
            // verifyRemovedProjectReference(ref, parent, index);
            let Some(config) = config else {
                create_diagnostic_for_reference(
                    parent,
                    index,
                    &diagnostics::File_0_not_found,
                    &[Value::Str(ref_.original_path.clone())],
                );
                return true;
            };
            let ref_options = config.compiler_options();
            let composite_is_true = ref_options.is_some_and(|o| o.composite == TS_TRUE);
            let no_emit_is_true = ref_options.is_some_and(|o| o.no_emit == TS_TRUE);
            if !composite_is_true || no_emit_is_true {
                if !parent.file_names().is_empty() {
                    if !composite_is_true {
                        create_diagnostic_for_reference(
                            parent,
                            index,
                            &diagnostics::Referenced_project_0_must_have_setting_composite_Colon_true,
                            &[Value::Str(ref_.original_path.clone())],
                        );
                    }
                    if no_emit_is_true {
                        create_diagnostic_for_reference(
                            parent,
                            index,
                            &diagnostics::Referenced_project_0_may_not_disable_emit,
                            &[Value::Str(ref_.original_path.clone())],
                        );
                    }
                }
            }
            if !build_info_file_name.is_empty()
                && build_info_file_name == config.get_build_info_file_name()
            {
                create_diagnostic_for_reference(
                    parent,
                    index,
                    &diagnostics::Cannot_write_file_0_because_it_will_overwrite_tsbuildinfo_file_generated_by_referenced_project_1,
                    &[
                        Value::Str(build_info_file_name.as_string().to_string()),
                        Value::Str(ref_.original_path.clone()),
                    ],
                );
                self.has_emit_blocking_diagnostics
                    .borrow_mut()
                    .insert(self.path_key_for_file_name(&build_info_file_name));
            }
            true
        });
    }

    /// `GetGlobalDiagnostics`.
    pub fn get_global_diagnostics(&self, _ctx: Context) -> Vec<DiagnosticRef> {
        if self.source_file_ids.is_empty() {
            return Vec::new();
        }
        if let Some(pool) = self.compiler_checker_pool.borrow().as_ref() {
            return pool.get_global_diagnostics();
        }
        // For external pools (project system), global diagnostics are collected
        // incrementally as checkers are used, not via a bulk query.
        Vec::new()
    }

    /// `GetDeclarationDiagnostics`.
    pub fn get_declaration_diagnostics(
        &self,
        ctx: Context,
        source_file: Option<NodeId>,
    ) -> Vec<DiagnosticRef> {
        self.collect_diagnostics(ctx, source_file, &mut |ctx, file| {
            self.get_declaration_diagnostics_for_file(ctx, file)
        })
    }

    /// `getSemanticDiagnosticsWithChecker`.
    fn get_semantic_diagnostics_with_checker(
        &self,
        ctx: Context,
        c: &Rc<RefCell<Checker>>,
        source_file: NodeId,
    ) -> Vec<DiagnosticRef> {
        let __t0 = std::time::Instant::now();
        let inner = self.get_bind_and_check_diagnostics_with_checker(ctx, c, source_file, false);
        let __t1 = std::time::Instant::now();
        let mut diags = filter_no_emit_semantic_diagnostics(inner, &self.options);
        let __t2 = std::time::Instant::now();
        diags.extend(self.get_include_processor_diagnostics(source_file));
        if std::env::var("TSC_FILE_TIME").is_ok() {
            eprintln!(
                "[sem-diag] bindcheck={:?} filternoemit={:?} includeproc={:?}",
                __t1 - __t0,
                __t2 - __t1,
                __t2.elapsed()
            );
        }
        diags
    }

    /// `getBindAndCheckDiagnosticsWithChecker` — semantic diagnostics for a
    /// single file using a caller-provided checker, including bind
    /// diagnostics, checker diagnostics, and `@ts-ignore`/`@ts-expect-error`
    /// directive handling.
    fn get_bind_and_check_diagnostics_with_checker(
        &self,
        ctx: Context,
        file_checker: &Rc<RefCell<Checker>>,
        source_file: NodeId,
        include_deferred_globals: bool,
    ) -> Vec<DiagnosticRef> {
        if self.skip_type_checking(source_file, false) {
            return Vec::new();
        }
        let mut previous_globals: Vec<DiagnosticRef> = Vec::new();
        if include_deferred_globals {
            previous_globals = file_checker.borrow_mut().get_global_diagnostics();
        }

        // Checker creation forces binding, so bind diagnostics will be populated.
        let mut diags = {
            let nodes = self.arena_of(source_file);
            nodes[source_file]
                .as_source_file()
                .bind_diagnostics()
                .to_vec()
        };
        diags.extend(
            file_checker
                .borrow_mut()
                .get_diagnostics(ctx.clone(), source_file),
        );

        if include_deferred_globals {
            let checker = file_checker.borrow();
            if checker.was_canceled() {
                return Vec::new();
            }
            drop(checker);
            let current_globals = file_checker.borrow_mut().get_global_diagnostics();
            if current_globals.len() > previous_globals.len() {
                for diagnostic in &current_globals {
                    if previous_globals
                        .binary_search_by(|d| {
                            diagnostic::compare_diagnostics(d, diagnostic).cmp(&0)
                        })
                        .is_err()
                    {
                        diags.push(diagnostic.clone());
                    }
                }
            }
        }

        let (is_plain_js, is_check_js, jsdoc_diagnostics) = {
            let nodes = self.arena_of(source_file);
            let sf = nodes[source_file].as_source_file();
            let is_plain_js = is_plain_js_file(Some(sf), self.options.check_js);
            let is_js = sf.script_kind == ScriptKind::Js || sf.script_kind == ScriptKind::Jsx;
            let is_check_js = is_js && is_check_js_enabled_for_file(sf, &self.options);
            let jsdoc = sf.jsdoc_diagnostics().to_vec();
            (is_plain_js, is_check_js, jsdoc)
        };

        if is_plain_js {
            diags.retain(|d| plain_js_errors().contains(&lock_diagnostic(d).code()));
            let (filtered, _) = self.get_diagnostics_with_preceding_directives(source_file, diags);
            return apply_content_mapper_diagnostic_directives(self, source_file, filtered);
        }

        if is_check_js {
            diags.extend(jsdoc_diagnostics);
        }

        let (mut filtered, directives_by_line) =
            self.get_diagnostics_with_preceding_directives(source_file, diags);
        for directive in directives_by_line.values() {
            // Above we changed all used directive kinds to @ts-ignore, so any @ts-expect-error directives that
            // remain are unused and thus errors.
            if directive.kind == CommentDirectiveKind::ExpectError {
                let nodes = self.arena_of(source_file);
                filtered.push(new_diagnostic(
                    Some(DiagnosticFile::from_node(source_file, &nodes)),
                    directive.loc,
                    &diagnostics::Unused_ts_expect_error_directive,
                    &[] as &[String],
                ));
            }
        }
        apply_content_mapper_diagnostic_directives(self, source_file, filtered)
    }

    /// `getDiagnosticsWithPrecedingDirectives`.
    fn get_diagnostics_with_preceding_directives(
        &self,
        source_file: NodeId,
        diags: Vec<DiagnosticRef>,
    ) -> (
        Vec<DiagnosticRef>,
        std::collections::HashMap<i32, tsc_ast::CommentDirective>,
    ) {
        let nodes = self.arena_of(source_file);
        let sf = nodes[source_file].as_source_file();
        if sf.comment_directives.is_empty() {
            return (diags, std::collections::HashMap::new());
        }
        // Build map of directives by line number
        let mut directives_by_line: std::collections::HashMap<i32, tsc_ast::CommentDirective> =
            std::collections::HashMap::new();
        for directive in sf.comment_directives.iter() {
            let line = tsc_scanner::scanner::get_ecma_line_of_position(sf, directive.loc.pos());
            directives_by_line.insert(line, directive.clone());
        }
        let line_starts = tsc_scanner::scanner::get_ecma_line_starts(sf);
        let text = sf.text().to_string();
        drop(nodes);
        let mut filtered: Vec<DiagnosticRef> = Vec::with_capacity(diags.len());
        for diagnostic in diags {
            let mut ignore_diagnostic = false;
            let (file_node, pos) = {
                let d = lock_diagnostic(&diagnostic);
                (d.file().and_then(|f| f.node), d.pos())
            };
            if file_node != Some(source_file) {
                filtered.push(diagnostic);
                continue;
            }
            let start_line = tsc_scanner::scanner::compute_line_of_position(&line_starts, pos) - 1;
            for line in (0..=start_line).rev() {
                if line < 0 {
                    break;
                }
                // If line contains a @ts-ignore or @ts-expect-error directive, ignore this diagnostic and change
                // the directive kind to @ts-ignore to indicate it was used.
                if let Some(directive) = directives_by_line.get_mut(&line) {
                    ignore_diagnostic = true;
                    directive.kind = CommentDirectiveKind::Ignore;
                    break;
                }
                // Stop searching backwards when we encounter a line that isn't blank or a comment.
                if !is_comment_or_blank_line(&text, line_starts[line as usize] as usize) {
                    break;
                }
            }
            if !ignore_diagnostic {
                filtered.push(diagnostic);
            }
        }
        (filtered, directives_by_line)
    }

    /// `getDeclarationDiagnosticsForFile`.
    fn get_declaration_diagnostics_for_file(
        &self,
        ctx: Context,
        source_file: NodeId,
    ) -> Vec<DiagnosticRef> {
        {
            let nodes = self.arena_of(source_file);
            if nodes[source_file].as_source_file().is_declaration_file {
                return Vec::new();
            }
        }

        if let Some(cached) = self.declaration_diagnostic_cache.borrow().get(&source_file) {
            return cached.as_ref().clone();
        }

        let (host, done) = BasicEmitHost::new(ctx, self, source_file);
        let diagnostics = crate::emit_host::get_declaration_diagnostics(&host, source_file);
        done();
        let diagnostics = Rc::new(diagnostics);
        self.declaration_diagnostic_cache
            .borrow_mut()
            .entry(source_file)
            .or_insert_with(|| diagnostics.clone())
            .as_ref()
            .clone()
    }

    /// `getSuggestionDiagnosticsWithChecker`.
    fn get_suggestion_diagnostics_with_checker(
        &self,
        ctx: Context,
        file_checker: &Rc<RefCell<Checker>>,
        source_file: NodeId,
    ) -> Vec<DiagnosticRef> {
        if self.skip_type_checking(source_file, false) {
            return Vec::new();
        }
        file_checker
            .borrow_mut()
            .get_suggestion_diagnostics(ctx, source_file)
    }

    /// `LineCount`.
    pub fn line_count(&self) -> usize {
        let mut count = 0;
        for &file in &self.source_file_ids {
            let nodes = self.arena_of(file);
            count += nodes[file].as_source_file().ecma_line_map().len();
        }
        count
    }

    /// `IdentifierCount`.
    pub fn identifier_count(&self) -> i64 {
        let mut count: i64 = 0;
        for &file in &self.source_file_ids {
            let nodes = self.arena_of(file);
            count += nodes[file].as_source_file().identifier_count as i64;
        }
        count
    }

    /// `SymbolCount`.
    pub fn symbol_count(&self) -> u64 {
        let mut count: u64 = 0;
        for &file in &self.source_file_ids {
            let nodes = self.arena_of(file);
            count += nodes[file].as_source_file().symbol_count as u64;
        }
        self.for_each_checker_parallel(&mut |_idx, c| {
            count += c.borrow().symbol_count as u64;
        });
        count
    }

    /// `TypeCount`.
    pub fn type_count(&self) -> u64 {
        let mut count: u64 = 0;
        self.for_each_checker_parallel(&mut |_idx, c| {
            count += c.borrow().type_count as u64;
        });
        count
    }

    /// `InstantiationCount`.
    pub fn instantiation_count(&self) -> u64 {
        let mut count: u64 = 0;
        self.for_each_checker_parallel(&mut |_idx, c| {
            count += c.borrow().total_instantiation_count as u64;
        });
        count
    }

    /// `Program` — self-reference for `ProgramLike`.
    pub fn program(&self) -> &Program {
        self
    }

    /// `GetSourceFileMetaData` — implements `checker.Program`.
    pub fn get_source_file_meta_data(&self, path: &PathKey) -> SourceFileMetaData {
        self.source_file_meta_datas
            .get(path)
            .cloned()
            .unwrap_or_default()
    }

    /// `getCompilerOptionsForFile` — the file's effective compiler options
    /// (config options redirected through a project reference).
    fn compiler_options_for_file(&self, file: &dyn HasFileName) -> Arc<CompilerOptions> {
        self.mapper().get_compiler_options_for_file(file)
    }

    /// `GetEmitModuleFormatOfFile` — implements `checker.Program`.
    pub fn get_emit_module_format_of_file(&self, source_file: &dyn HasFileName) -> ModuleKind {
        tsc_ast::get_emit_module_format_of_file_worker(
            source_file.file_name(),
            &self.compiler_options_for_file(source_file),
            &self.get_source_file_meta_data(source_file.path_key()),
        )
    }

    /// `GetEmitModuleFormatOfFile` for a `&SourceFile` — the printer
    /// `EmitHost` signature.
    pub fn get_emit_module_format_of_file_for_source(
        &self,
        source_file: &tsc_ast::SourceFile,
    ) -> ModuleKind {
        let file = new_has_file_name(
            source_file.file_name().clone(),
            source_file.path_key().clone(),
        );
        self.get_emit_module_format_of_file(&file)
    }

    /// `GetEmitSyntaxForUsageLocation` — implements `checker.Program`.
    pub fn get_emit_syntax_for_usage_location(
        &self,
        source_file: &dyn HasFileName,
        location: NodeId,
    ) -> ResolutionMode {
        let nodes = self.arena_of(location);
        get_emit_syntax_for_usage_location_worker(
            source_file.file_name(),
            &self.get_source_file_meta_data(source_file.path_key()),
            location,
            &nodes,
            &self.compiler_options_for_file(source_file),
        )
    }

    /// `GetImpliedNodeFormatForEmit` — implements `checker.Program`.
    pub fn get_implied_node_format_for_emit(&self, source_file: &dyn HasFileName) -> ModuleKind {
        tsc_ast::get_implied_node_format_for_emit_worker(
            source_file.file_name(),
            self.compiler_options_for_file(source_file)
                .get_emit_module_kind(),
            &self.get_source_file_meta_data(source_file.path_key()),
        )
    }

    /// `GetModeForUsageLocation` — implements
    /// `modulespecifiers.ModuleSpecifierGenerationHost`.
    pub fn get_mode_for_usage_location(
        &self,
        source_file: &dyn HasFileName,
        location: NodeId,
    ) -> ResolutionMode {
        let nodes = self.arena_of(location);
        let options = self.compiler_options_for_file(source_file);
        get_mode_for_usage_location(
            source_file.file_name(),
            &self.get_source_file_meta_data(source_file.path_key()),
            location,
            &nodes,
            Some(&options),
        )
    }

    /// `GetModeForResolutionAtIndex`.
    pub fn get_mode_for_resolution_at_index(
        &self,
        source_file: NodeId,
        index: usize,
    ) -> ResolutionMode {
        let (imports, module_augmentations) = {
            let nodes = self.arena_of(source_file);
            let sf = nodes[source_file].as_source_file();
            (sf.imports().to_vec(), sf.module_augmentations.to_vec())
        };
        let mut index = index;
        if index < imports.len() {
            return self.get_mode_for_usage_location(
                &self.file_has_file_name(source_file),
                imports[index],
            );
        }
        index -= imports.len();
        let nodes = self.arena_of(source_file);
        for augmentation in module_augmentations {
            if nodes[augmentation].kind == tsc_ast::Kind::StringLiteral {
                if index == 0 {
                    let has_name = self.file_has_file_name(source_file);
                    drop(nodes);
                    return self.get_mode_for_usage_location(&has_name, augmentation);
                }
                index -= 1;
            }
        }
        panic!("resolution index out of range")
    }

    /// `GetDefaultResolutionModeForFile` — implements
    /// `modulespecifiers.ModuleSpecifierGenerationHost`.
    pub fn get_default_resolution_mode_for_file(
        &self,
        source_file: &dyn HasFileName,
    ) -> ResolutionMode {
        get_default_resolution_mode_for_file(
            source_file.file_name(),
            &self.get_source_file_meta_data(source_file.path_key()),
            &self.compiler_options_for_file(source_file),
        )
    }

    /// `IsSourceFileDefaultLibrary` — implements `checker.Program`.
    pub fn is_source_file_default_library(&self, path: &PathKey) -> bool {
        self.lib_files.contains_key(path)
    }

    /// `IsGlobalTypingsFile`.
    pub fn is_global_typings_file(&self, file_name: &RootedFilePath) -> bool {
        if !file_name.is_declaration_file() {
            return false;
        }
        self.case_sensitivity.contains_path(
            &self.get_global_typings_cache_location(),
            &file_name.as_path(),
        )
    }

    /// `GetDefaultLibFile`.
    pub fn get_default_lib_file(&self, path: &PathKey) -> Option<Rc<LibFile>> {
        self.lib_files.get(path).cloned()
    }

    /// `CommonSourceDirectory`.
    pub fn common_source_directory(&self) -> RootedDirectoryPath {
        self.common_source_directory_ref().clone()
    }

    /// Borrowed variant — `printer::EmitHost` returns `&`.
    pub fn common_source_directory_ref(&self) -> &RootedDirectoryPath {
        self.common_source_directory.get_or_init(|| {
            let files = || -> Vec<RootedFilePath> {
                self.source_file_ids
                    .iter()
                    .filter(|&&file| {
                        let nodes = self.arena_of(file);
                        let is_decl = nodes[file].as_source_file().is_declaration_file;
                        drop(nodes);
                        source_file_may_be_emitted(file, self, false, false) && !is_decl
                    })
                    .map(|&file| {
                        self.arena_of(file)[file]
                            .as_source_file()
                            .file_name()
                            .clone()
                    })
                    .collect()
            };
            tsc_outputpaths::get_common_source_directory(
                &self.options,
                files,
                self.base_directory(),
                self.case_sensitivity,
                Some(&|files, dir| self.check_source_files_belong_to_path(files, dir)),
            )
        })
    }

    /// `checkSourceFilesBelongToPath`.
    fn check_source_files_belong_to_path(
        &self,
        source_files: &[RootedFilePath],
        root_directory: RootedDirectoryPath,
    ) -> bool {
        let mut all_files_belong_to_path = true;
        for file in source_files {
            if !self
                .case_sensitivity
                .contains_file_path(&root_directory, file)
            {
                self.add_processing_diagnostic(ProcessingDiagnostic::ExplainingFileInclude(
                    Box::new(IncludeExplainingDiagnostic {
                        file: self.case_sensitivity.path_key(&file.as_path()),
                        diagnostic_reason: None,
                        message: &diagnostics::File_0_is_not_under_rootDir_1_rootDir_is_expected_to_contain_all_source_files,
                        args: vec![
                            file.as_string().to_string(),
                            root_directory.as_string().to_string(),
                        ],
                    }),
                ));
                all_files_belong_to_path = false;
            }
        }
        all_files_belong_to_path
    }

    /// `addProcessingDiagnostic` — Go appends to
    /// `processedFiles.processingDiagnostics`; post-parse additions go
    /// through the pending channel (see header PORT note).
    pub fn add_processing_diagnostic(&self, d: ProcessingDiagnostic) {
        self.pending_processing_diagnostics.borrow_mut().push(d);
    }

    /// Iterates `processed.processing_diagnostics` then the pending
    /// additions, in Go append order.
    pub fn for_each_processing_diagnostic(&self, f: &mut dyn FnMut(&ProcessingDiagnostic)) {
        for d in &self.processed.processing_diagnostics {
            f(d);
        }
        for d in self.pending_processing_diagnostics.borrow().iter() {
            f(d);
        }
    }

    /// `Emit`.
    pub fn emit(&self, ctx: Context, options: &mut EmitOptions<'_>) -> EmitResult {
        let trace_done = push(
            self.hosts.tracing.as_ref(),
            PHASE_EMIT,
            "emit",
            Default::default(),
            true,
        );

        if !options.force_emit && options.emit_only != crate::emit_host::EmitOnly::BuilderSignature
        {
            let result =
                handle_no_emit_options(&ctx, self, options.target_source_files.as_deref(), None);
            if result.is_some() || ctx.is_cancelled() {
                return result.unwrap_or_default();
            }
        }

        let new_line = self.options.new_line.get_new_line_character();
        let _ = new_line;
        let force_dts_emit = options.emit_only == crate::emit_host::EmitOnly::BuilderSignature
            || options.force_emit && options.emit_only == crate::emit_host::EmitOnly::Dts;
        let force_js_emit =
            options.force_emit && options.emit_only == crate::emit_host::EmitOnly::Js;
        let source_files = self.get_source_files_to_emit(
            options.target_source_files.take(),
            force_dts_emit,
            force_js_emit,
        );

        let mut emitters: Vec<crate::emitter::Emitter<'_, '_>> =
            Vec::with_capacity(source_files.len());
        for source_file in source_files {
            let mut emitter = crate::emitter::Emitter::new(
                source_file,
                options.emit_only,
                options.force_emit,
                options.write_file.take(),
                self.hosts.tracing.clone(),
            );
            options.write_file = None;
            let (host, done) = BasicEmitHost::new(ctx.clone(), self, source_file);
            emitter.set_host(host);
            emitter.compute_paths(force_dts_emit, force_js_emit, options.force_emit);
            emitter.emit();
            done();
            emitters.push(emitter);
        }

        // collect results from emit, preserving input order
        let result = combine_emit_results(emitters.iter_mut().map(|e| e.emit_result()));
        trace_done();
        result
    }

    /// `PathKeyForFileName`.
    pub fn path_key_for_file_name(&self, file_name: &RootedFilePath) -> PathKey {
        self.case_sensitivity.path_key(&file_name.as_path())
    }

    /// `GetSourceFile`.
    pub fn get_source_file(&self, file_name: &RootedFilePath) -> Option<NodeId> {
        self.get_source_file_by_path(&self.path_key_for_file_name(file_name))
    }

    /// `GetSourceFileForResolvedModule` — implements `checker.Program`.
    pub fn get_source_file_for_resolved_module(&self, resolved: &ResolvedModule) -> Option<NodeId> {
        self.get_source_file_with_redirect(
            &resolved.resolved_file_name,
            resolved.resolved_path.clone(),
        )
    }

    /// `getSourceFileWithRedirect`.
    fn get_source_file_with_redirect(
        &self,
        file_name: &RootedFilePath,
        path: PathKey,
    ) -> Option<NodeId> {
        let file = self.get_source_file_by_path(&path);
        if file.is_none() {
            let filename = self.get_parse_file_redirect_by_file_name(file_name);
            if !filename.is_empty() {
                return self.get_source_file(&filename);
            }
        }
        file
    }

    /// `FilesByPath`.
    pub fn files_by_path(&self) -> &FxHashMap<PathKey, NodeId> {
        &self.processed.files_by_path
    }

    /// `GetSourceFileByPath`.
    pub fn get_source_file_by_path(&self, path: &PathKey) -> Option<NodeId> {
        self.files_by_path.get(path).copied()
    }

    /// `HasSameFileNames` — checks for casing differences on
    /// case-insensitive file systems.
    pub fn has_same_file_names(&self, other: &Program) -> bool {
        let file_name_eq = |a: &NodeId, b: &NodeId| {
            self.arena_of(*a)[*a].as_source_file().file_name()
                == other.arena_of(*b)[*b].as_source_file().file_name()
        };
        self.files_by_path.len() == other.files_by_path.len()
            && self.files_by_path.iter().all(|(k, v)| {
                other
                    .files_by_path
                    .get(k)
                    .is_some_and(|b| file_name_eq(v, b))
            })
            && self.redirect_files_by_path.len() == other.redirect_files_by_path.len()
            && self.redirect_files_by_path.iter().all(|(k, v)| {
                other
                    .redirect_files_by_path
                    .get(k)
                    .is_some_and(|b| v.file_name == b.file_name)
            })
    }

    /// `GetIncludeReasons` — testing only.
    pub fn get_include_reasons(&self) -> &FxHashMap<PathKey, Vec<Rc<FileIncludeReason>>> {
        &self.file_include_reasons
    }

    /// `IsMissingPath` — testing only.
    pub fn is_missing_path(&self, path: &PathKey) -> bool {
        self.missing_files.contains(path)
    }

    /// `ExplainFiles`.
    pub fn explain_files(
        &self,
        w: &mut dyn Write,
        locale: &Locale,
        current_directory: RootedDirectoryPath,
    ) {
        let to_relative_file_name = |file_name: &RootedFilePath| -> String {
            if let Some(relative_path) = self
                .case_sensitivity
                .relative_path_from_directory(&current_directory, file_name)
            {
                return relative_path.as_string().to_string();
            }
            file_name.as_string().to_string()
        };
        let mut files_explained = 0usize;
        let mut explain_file =
            |file: &dyn HasFileName, files_explained: &mut usize| -> Vec<String> {
                let mut lines = Vec::new();
                lines.push(to_relative_file_name(file.file_name()));
                if let Some(reasons) = self.file_include_reasons.get(file.path_key()) {
                    for reason in reasons {
                        let d = reason.to_diagnostic(self, true, current_directory.clone());
                        lines.push(format!("   {}", lock_diagnostic(&d).localize(locale)));
                    }
                }
                for diag in self.include_processor.explain_redirect_and_implied_format(
                    self,
                    file.path_key(),
                    &mut |file_name| to_relative_file_name(file_name),
                ) {
                    lines.push(format!("   {}", lock_diagnostic(&diag).localize(locale)));
                }
                *files_explained += 1;
                lines
            };

        let mut redirect_files: Vec<Rc<RedirectsFile>> =
            self.redirect_files_by_path.values().cloned().collect();
        redirect_files.sort_by(|a, b| a.index.cmp(&b.index));

        let files = self.source_files();
        let mut source_file_index = 0usize;

        let mut output = String::new();
        for redirect_file in &redirect_files {
            // Explain all sourceFiles till we reach this redirectFile index
            while files_explained < redirect_file.index {
                for line in explain_file(
                    &self.file_has_file_name(files[source_file_index]),
                    &mut files_explained,
                ) {
                    output.push_str(&line);
                    output.push('\n');
                }
                source_file_index += 1;
            }
            for line in explain_file(&**redirect_file, &mut files_explained) {
                output.push_str(&line);
                output.push('\n');
            }
        }

        // Explain any remaining sourceFiles
        while files_explained < files.len() + redirect_files.len() {
            for line in explain_file(
                &self.file_has_file_name(files[source_file_index]),
                &mut files_explained,
            ) {
                output.push_str(&line);
                output.push('\n');
            }
            source_file_index += 1;
        }
        let _ = w.write_all(output.as_bytes());
    }

    /// `GetLibFileFromReference`.
    pub fn get_lib_file_from_reference(&self, ref_: &FileReference) -> Option<NodeId> {
        let Some(name) = tsc_tsoptions::enummaps::get_lib_file_name(&ref_.file_name) else {
            return None;
        };
        for (path, lib_file) in &self.lib_files {
            if lib_file.name == name {
                return self.files_by_path.get(path).copied();
            }
        }
        None
    }

    /// `GetResolvedTypeReferenceDirectiveFromTypeReferenceDirective`.
    pub fn get_resolved_type_reference_directive_from_type_reference_directive(
        &self,
        type_ref: &FileReference,
        source_file: NodeId,
    ) -> Option<ResolvedTypeReferenceDirective> {
        let has_name = self.file_has_file_name(source_file);
        self.get_resolved_type_reference_directive(
            &has_name,
            &type_ref.file_name,
            self.get_mode_for_type_reference_directive_in_file(type_ref, &has_name),
        )
    }

    /// `GetResolvedTypeReferenceDirective`.
    pub fn get_resolved_type_reference_directive(
        &self,
        file: &dyn HasFileName,
        type_directive_name: &str,
        mode: ResolutionMode,
    ) -> Option<ResolvedTypeReferenceDirective> {
        if let Some(resolutions) = self.type_resolutions_in_file.get(file.path_key()) {
            if let Some(resolved) = resolutions.get(&ModeAwareCacheKey {
                name: type_directive_name.to_string(),
                mode,
            }) {
                return Some(resolved.clone());
            }
        }
        None
    }

    /// `GetResolvedTypeReferenceDirectives`.
    pub fn get_resolved_type_reference_directives(
        &self,
    ) -> &FxHashMap<PathKey, ModeAwareCache<ResolvedTypeReferenceDirective>> {
        &self.type_resolutions_in_file
    }

    /// `getModeForTypeReferenceDirectiveInFile`.
    fn get_mode_for_type_reference_directive_in_file(
        &self,
        ref_: &FileReference,
        source_file: &dyn HasFileName,
    ) -> ResolutionMode {
        if ref_.resolution_mode != ResolutionMode::None {
            return ref_.resolution_mode;
        }
        self.get_default_resolution_mode_for_file(source_file)
    }

    /// `IsSourceFileFromExternalLibrary` — `*ast.SourceFile` → `NodeId`.
    pub fn is_source_file_from_external_library(&self, file: NodeId) -> bool {
        let nodes = self.arena_of(file);
        let key = nodes[file].as_source_file().path_key().clone();
        drop(nodes);
        self.is_source_file_from_external_library_by_path(&key)
    }

    /// `IsSourceFileFromExternalLibrary` by path key.
    pub fn is_source_file_from_external_library_by_path(&self, path: &PathKey) -> bool {
        self.source_files_found_searching_node_modules
            .contains(path)
    }

    /// `GetJSXRuntimeImportSpecifier` — implements `checker.Program`.
    pub fn get_jsx_runtime_import_specifier(&self, path: &PathKey) -> (String, Option<NodeId>) {
        if let Some(result) = self.jsx_runtime_import_specifiers.get(path) {
            return (result.module_reference.clone(), Some(result.specifier));
        }
        (String::new(), None)
    }

    /// `GetImportHelpersImportSpecifier` — implements `checker.Program`.
    pub fn get_import_helpers_import_specifier(&self, path: &PathKey) -> Option<NodeId> {
        self.import_helpers_import_specifiers.get(path).copied()
    }

    /// `SourceFileMayBeEmitted` — `*ast.SourceFile` → `NodeId`.
    pub fn source_file_may_be_emitted_for(
        &self,
        source_file: NodeId,
        force_dts_emit: bool,
    ) -> bool {
        source_file_may_be_emitted(source_file, self, force_dts_emit, false)
    }

    /// `ResolvedPackageNames`.
    pub fn resolved_package_names(&self) -> &HashSet<String> {
        &self.collect_package_names().resolved
    }

    /// `UnresolvedPackageNames`.
    pub fn unresolved_package_names(&self) -> &HashSet<String> {
        &self.collect_package_names().unresolved
    }

    /// `DeepImportPackageNames`.
    pub fn deep_import_package_names(&self) -> &HashSet<String> {
        &self.collect_package_names().deep_import_packages
    }

    /// `collectPackageNames`.
    fn collect_package_names(&self) -> &PackageNamesInfo {
        self.package_names.get_or_init(|| {
            let resolver = self.new_resolver();
            let mut package_names = PackageNamesInfo {
                resolved: HashSet::new(),
                unresolved: HashSet::new(),
                deep_import_packages: HashSet::new(),
            };
            for &file in &self.source_file_ids {
                let (path_key, file_name, imports) = {
                    let nodes = self.arena_of(file);
                    let sf = nodes[file].as_source_file();
                    (
                        sf.path_key().clone(),
                        sf.file_name().clone(),
                        sf.imports().to_vec(),
                    )
                };
                if self.is_source_file_default_library(&path_key)
                    || self.is_source_file_from_external_library(file)
                    || file_name.contains_lowercase_directory_sequence("/node_modules/")
                {
                    // Checking for /node_modules/ is a little imprecise, but ATA treats locally installed typings
                    // as root files, which would not pass IsSourceFileFromExternalLibrary.
                    continue;
                }
                let has_name = self.file_has_file_name(file);
                for imp in imports {
                    let (is_source_phase, imp_text) = {
                        let nodes = self.arena_of(file);
                        (
                            nodes[imp]
                                .parent
                                .is_some_and(|p| is_source_phase_import(&nodes[p], &nodes)),
                            nodes[imp].text(&nodes).to_string(),
                        )
                    };
                    if is_source_phase || tsc_tspath::is_external_module_name_relative(&imp_text) {
                        continue;
                    }
                    if let Some(resolved_modules) = self.resolved_modules.get(&path_key) {
                        let key = ModeAwareCacheKey {
                            name: imp_text.clone(),
                            mode: self.get_mode_for_usage_location(&has_name, imp),
                        };
                        if let Some(Some(resolved_module)) = resolved_modules.get(&key) {
                            if !resolved_module.is_resolved() || !resolved_module.is_external_library_import
                            {
                                if resolved_module.is_resolved() {
                                    continue;
                                }
                                package_names.unresolved.insert(imp_text);
                                continue;
                            }
                            // Priority order for getting package name:
                            // 1. PackageId.Name (requires both name and version in package.json)
                            let mut name = resolved_module.package_id.name.clone();
                            if name.is_empty() {
                                // 2. GetPackageScopeForPath - get name from package.json in the package directory
                                if let Some(package_scope) = resolver
                                    .get_package_scope_for_path(&resolved_module.resolved_file_name.directory())
                                {
                                    if package_scope.exists() {
                                        if let Some(scope_name) = package_scope
                                            .contents
                                            .as_ref()
                                            .and_then(|c| c.fields.name.get_value())
                                        {
                                            name = scope_name.clone();
                                        }
                                    }
                                }
                            }
                            if name.is_empty() {
                                // 3. GetPackageNameFromDirectory - extract from node_modules path
                                name = tsc_modulespecifiers::util::get_package_name_from_directory(
                                    &resolved_module.resolved_file_name.as_path(),
                                )
                                .to_string();
                            }
                            // 4. If all fail, don't add empty string
                            if !name.is_empty() {
                                package_names.resolved.insert(name.clone());
                                // Detect deep imports: subpath imports in packages without exports.
                                // These are imports like "lodash/fp" where the package has no exports
                                // map, so auto-import can only find them via recursive directory search.
                                let (_, rest) = tsc_module::parse_package_name(&imp_text);
                                if !rest.is_empty() {
                                    if let Some(scope) = resolver.get_package_scope_for_path(
                                        &resolved_module.resolved_file_name.directory(),
                                    ) {
                                        if scope.exists()
                                            && !scope
                                                .contents
                                                .as_ref()
                                                .is_some_and(|c| c.fields.exports.is_present())
                                        {
                                            package_names.deep_import_packages.insert(
                                                tsc_module::get_package_name_from_types_package_name(
                                                    &name,
                                                ),
                                            );
                                        }
                                    }
                                }
                            }
                            continue;
                        }
                    }
                    package_names.unresolved.insert(imp_text);
                }
            }
            Rc::new(package_names)
        })
    }

    /// `IsLibFile`.
    pub fn is_lib_file(&self, source_file: NodeId) -> bool {
        let nodes = self.arena_of(source_file);
        let key = nodes[source_file].as_source_file().path_key().clone();
        drop(nodes);
        self.lib_files.contains_key(&key)
    }

    /// `HasTSFile`.
    pub fn has_ts_file(&self) -> bool {
        *self.has_ts_file.get_or_init(|| {
            for &file in &self.source_file_ids {
                let nodes = self.arena_of(file);
                if nodes[file]
                    .as_source_file()
                    .file_name()
                    .has_implementation_ts_file_extension()
                {
                    return true;
                }
            }
            false
        })
    }

    /// `GetSymlinkCache` — lazily computes the known-symlinks map.
    fn compute_known_symlinks(&self) -> KnownSymlinks {
        let resolver = self.new_resolver();
        let known_symlinks = KnownSymlinks::new(self.case_sensitivity);

        // Resolved modules store realpath information when they're resolved inside node_modules
        if !self.resolved_modules.is_empty() || !self.type_resolutions_in_file.is_empty() {
            known_symlinks.set_symlinks_from_resolutions(
                |cb, _file| self.for_each_resolved_module(cb, None),
                |cb, _file| self.for_each_resolved_type_reference_directive(cb, None),
            );
        }

        // Check other dependencies for symlinks
        let mut seen_package_jsons: HashSet<PathKey> = HashSet::new();
        for (file_path, meta) in &self.source_file_meta_datas {
            if meta.package_json_directory.is_empty()
                || !self.source_file_may_be_emitted_for(
                    self.get_source_file_by_path(file_path)
                        .expect("metadata for file not in program"),
                    false,
                )
                || !seen_package_jsons.insert(
                    self.case_sensitivity
                        .path_key(&meta.package_json_directory.as_path()),
                )
            {
                continue;
            }
            let package_json_name = meta.package_json_directory.resolve_file("package.json");
            let Some(info) = self.get_package_json_info(&package_json_name) else {
                continue;
            };
            let Some(contents) = info.get_contents() else {
                continue;
            };

            for dep in contents.get_runtime_dependency_names().m.iter() {
                // Skip work in common case: we already saved a symlink for this package directory
                // in the node_modules adjacent to this package.json
                let possible_directory_path = self.case_sensitivity.path_key(
                    &meta
                        .package_json_directory
                        .resolve_directory(&tsc_tspath::combine_paths(
                            "node_modules",
                            &[dep.as_str()],
                        ))
                        .as_path(),
                );
                if known_symlinks.has_directory(&possible_directory_path) {
                    continue;
                }
                if !dep.starts_with("@types") {
                    let possible_types_directory_path = self.case_sensitivity.path_key(
                        &meta
                            .package_json_directory
                            .resolve_directory(&tsc_tspath::combine_paths(
                                "node_modules",
                                &[&tsc_module::get_types_package_name(dep)],
                            ))
                            .as_path(),
                    );
                    if known_symlinks.has_directory(&possible_types_directory_path) {
                        continue;
                    }
                }

                if let Some(package_resolution) = resolver.resolve_package_directory(
                    dep,
                    &package_json_name,
                    ResolutionMode::CommonJS,
                    None,
                ) {
                    if package_resolution.is_resolved()
                        && !package_resolution.original_path.is_empty()
                    {
                        known_symlinks.process_resolution(
                            tsc_tspath::rooted_directory_path_from_path(
                                package_resolution.original_path.as_path(),
                            )
                            .resolve_file("package.json"),
                            tsc_tspath::rooted_directory_path_from_path(
                                package_resolution.resolved_file_name.as_path(),
                            )
                            .resolve_file("package.json"),
                        );
                    }
                }
            }
        }
        known_symlinks
    }

    /// `GetSymlinkCache`.
    pub fn get_symlink_cache(&self) -> &KnownSymlinks {
        self.known_symlinks
            .get_or_init(|| Rc::new(self.compute_known_symlinks()))
    }

    /// `GetSymlinkCache` — `Option<&>` for the modulespecifiers host trait.
    pub fn get_symlink_cache_opt(&self) -> Option<&KnownSymlinks> {
        Some(self.get_symlink_cache())
    }

    /// `ForEachResolvedModule` — `file` is Go's nilable `*ast.SourceFile`.
    pub fn for_each_resolved_module(
        &self,
        callback: &mut dyn FnMut(&ResolvedModule, &str, ResolutionMode, &PathKey),
        file: Option<NodeId>,
    ) {
        for_each_resolution(
            &self.resolved_modules,
            callback,
            file,
            |f| self.arena_of(f)[f].as_source_file().path_key().clone(),
            |r| r.as_ref().expect("nil resolution in cache"),
        );
    }

    /// `ForEachResolvedTypeReferenceDirective`.
    pub fn for_each_resolved_type_reference_directive(
        &self,
        callback: &mut dyn FnMut(&ResolvedTypeReferenceDirective, &str, ResolutionMode, &PathKey),
        file: Option<NodeId>,
    ) {
        for_each_resolution(
            &self.type_resolutions_in_file,
            callback,
            file,
            |f| self.arena_of(f)[f].as_source_file().path_key().clone(),
            |r| r,
        );
    }
}

/// `forEachResolution` — `file` is Go's nilable `*ast.SourceFile`. `get`
/// projects the cache value to the callback arg: `resolved_modules` stores
/// `Option<ResolvedModule>` (Go `*ResolvedModule` — `None` would nil-deref
/// in Go, so `expect` is the parity behavior) while type-reference caches
/// store the directive directly.
fn for_each_resolution<V, T>(
    resolution_cache: &FxHashMap<PathKey, ModeAwareCache<V>>,
    callback: &mut dyn FnMut(&T, &str, ResolutionMode, &PathKey),
    file: Option<NodeId>,
    path_key_of: impl Fn(NodeId) -> PathKey,
    get: impl Fn(&V) -> &T,
) {
    if let Some(file) = file {
        let path_key = path_key_of(file);
        if let Some(resolutions) = resolution_cache.get(&path_key) {
            for (key, resolution) in resolutions {
                callback(get(resolution), &key.name, key.mode, &path_key);
            }
        }
    } else {
        for (file_path, resolutions) in resolution_cache {
            for (key, resolution) in resolutions {
                callback(get(resolution), &key.name, key.mode, file_path);
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Construction / reuse
// ---------------------------------------------------------------------------

/// `NewProgram`.
pub fn new_program(opts: ProgramOptions) -> Rc<Program> {
    let trace_done = push(
        opts.hosts.tracing.as_ref(),
        PHASE_PROGRAM,
        "createProgram",
        [(
            "configFilePath".to_string(),
            serde_json::Value::from(
                opts.config
                    .config
                    .compiler_options()
                    .map(|o| o.config_file_path.as_string().to_string())
                    .unwrap_or_default(),
            ),
        )]
        .into_iter()
        .collect(),
        true,
    );
    let case_sensitivity = opts.hosts.host.fs().case_sensitivity();
    let (processed, resolution_data) = process_all_program_files(&opts);
    let source_file_ids: Vec<NodeId> = processed.files.iter().map(|f| f.file).collect();
    let mut arenas: Vec<Option<Rc<ArenaCell>>> = Vec::new();
    for file in &processed.files {
        let idx = file.file.file_index() as usize;
        if idx >= arenas.len() {
            arenas.resize_with(idx + 1, || None);
        }
        arenas[idx] = Some(file.nodes.clone());
    }
    let p = Rc::new(Program {
        options: Rc::new(
            opts.config
                .config
                .compiler_options()
                .cloned()
                .unwrap_or_default(),
        ),
        opts: opts.config.clone(),
        hosts: opts.hosts.clone(),
        resolution_data,
        checker_pool: RefCell::new(None),
        compiler_checker_pool: RefCell::new(None),
        include_processor: IncludeProcessor::default(),
        module_resolution_error: None,
        case_sensitivity,
        symbols: SymbolArena::default(),
        processed,
        uses_uri_style_node_core_modules: Tristate::default(),
        common_source_directory: OnceCell::new(),
        declaration_diagnostic_cache: RefCell::new(FxHashMap::default()),
        program_diagnostics: RefCell::new(Vec::new()),
        has_emit_blocking_diagnostics: RefCell::new(HashSet::new()),
        content_mapper_option_diagnostics: RefCell::new(Vec::new()),
        source_files_to_emit: RefCell::new(None),
        unresolved_imports: OnceCell::new(),
        known_symlinks: OnceCell::new(),
        package_names: OnceCell::new(),
        has_ts_file: OnceCell::new(),
        packages_map: OnceCell::new(),
        pending_processing_diagnostics: RefCell::new(Vec::new()),
        source_file_ids,
        file_rank_map: RefCell::new(None),
        arenas,
        last_arena: std::cell::RefCell::new(None),
    });
    p.init_checker_pool(opts.factories.create_checker_pool, &p);
    p.verify_compiler_options();
    p.collect_content_mapper_option_diagnostics();
    trace_done();
    p
}

/// `UpdateProgram` — returns an updated program for which it is known that
/// only the file with the given path has changed, plus the changed file
/// (through `new_host`; `None` only if the host cannot locate the file),
/// plus whether the old program's data was reused.
pub fn update_program(
    p: &Rc<Program>,
    changed_file_path: &PathKey,
    new_host: Arc<dyn crate::host::CompilerHost>,
    create_checker_pool: Option<Arc<dyn Fn(&Rc<Program>) -> Rc<dyn CheckerPool>>>,
    create_module_resolver: Option<Arc<dyn Fn(ResolverOptions) -> Arc<dyn Resolver>>>,
) -> (Rc<Program>, Option<LoadedSourceFile>, bool) {
    // `ReuseProgram` needs `Rc<Program>` receivers; split so the fallback
    // path can move the factories.
    match reuse_program(
        p,
        changed_file_path,
        new_host.clone(),
        create_checker_pool.clone(),
    ) {
        (Some(result), new_file, true) => (result, new_file, true),
        (_, new_file, _) => (
            new_program(ProgramOptions {
                config: p.opts.clone(),
                hosts: ProgramHosts {
                    host: new_host,
                    // `ProgramConfig` carries no hosts in Go — tracing is not
                    // propagated to the fallback program.
                    tracing: None,
                },
                factories: ProgramFactories {
                    create_checker_pool,
                    create_module_resolver,
                },
            }),
            new_file,
            false,
        ),
    }
}

/// `ReuseProgram` — produces a new program by replacing only
/// `changed_file_path` in place, reusing the rest of `p`. Returns
/// `(Some(newProgram), newFile, true)` on success, `(None, newFile, false)`
/// when the file cannot be replaced in place.
pub fn reuse_program(
    p: &Rc<Program>,
    changed_file_path: &PathKey,
    new_host: Arc<dyn crate::host::CompilerHost>,
    // Go's `createModuleResolver` parameter is dead inside `ReuseProgram`
    // (only `UpdateProgram`'s fallback uses it), so it is not taken here.
    create_checker_pool: Option<Arc<dyn Fn(&Rc<Program>) -> Rc<dyn CheckerPool>>>,
) -> (Option<Rc<Program>>, Option<LoadedSourceFile>, bool) {
    let Some(&old_file_id) = p.files_by_path.get(changed_file_path) else {
        return (None, None, false);
    };
    let old_file = p
        .processed
        .files
        .iter()
        .find(|f| f.file == old_file_id)
        .cloned()
        .expect("filesByPath points at a file");
    let mut new_file: Option<LoadedSourceFile> = None;
    let mut old_supplemental_files: Vec<NodeId> = Vec::new();
    let mut new_supplemental_files: Vec<LoadedSourceFile> = Vec::new();
    {
        let nodes = old_file.nodes.snapshot();
        let old_sf = nodes[old_file.file].as_source_file();
        let has_content_mapper = !old_sf.content_mapper().is_empty();
        if has_content_mapper {
            // Content-mapped files are produced by running an external transform, which a plain reparse can't
            // reproduce. Re-run the transform through the host; any failure (or a missing file) falls back to
            // a full rebuild so the file loader's failure policy runs.
            let Some(mapper) = p
                .opts
                .config
                .get_content_mapper_for_file_name(old_sf.file_name())
            else {
                return (None, None, false);
            };
            let parse_options = old_sf.parse_options().clone();
            let supplemental = old_sf.supplemental_source_files().to_vec();
            drop(nodes);
            match new_host.get_content_mapped_source_files(&parse_options, &mapper) {
                Ok(files) => {
                    new_file = Some(LoadedSourceFile::from(files.canonical));
                    old_supplemental_files = supplemental;
                    new_supplemental_files = files
                        .supplemental
                        .into_iter()
                        .map(LoadedSourceFile::from)
                        .collect();
                }
                Err(_) => return (None, None, false),
            }
        } else {
            let parse_options = old_sf.parse_options().clone();
            drop(nodes);
            new_file = new_host
                .get_source_file(&parse_options)
                .map(LoadedSourceFile::from);
        }
    }
    let Some(new_file_value) = new_file.clone() else {
        // Go distinguishes `newFile == nil` (host miss) from other failures —
        // both bail, but the caller still gets nil back.
        return (None, None, false);
    };

    // If this file is part of a package redirect group (same package installed in multiple
    // node_modules locations), we need to rebuild the program because the redirect targets
    // might need recalculation.
    if p.redirect_files_by_path.contains_key(changed_file_path)
        || p.redirect_targets_map.contains_key(changed_file_path)
    {
        return (None, Some(new_file_value), false);
    }

    if p.module_resolution_error.is_some()
        || !p.can_replace_file_in_program(&old_file, &new_file_value)
    {
        return (None, Some(new_file_value), false);
    }
    // Cloning does not recompute synthetic helper or JSX-runtime import bookkeeping. Fall back to a full
    // build whenever either version requires those imports.
    if p.import_helpers_import_specifiers
        .contains_key(&old_file.path())
        || p.needs_import_helpers_import_specifier(&new_file_value)
    {
        return (None, Some(new_file_value), false);
    }
    if p.jsx_runtime_import_specifiers
        .contains_key(&old_file.path())
        || !p
            .jsx_runtime_import_specifier_for(&new_file_value)
            .is_empty()
    {
        return (None, Some(new_file_value), false);
    }
    if old_supplemental_files.len() != new_supplemental_files.len() {
        return (None, Some(new_file_value), false);
    }
    for (i, &old_supplemental) in old_supplemental_files.iter().enumerate() {
        let new_supplemental = &new_supplemental_files[i];
        let old_supplemental_lsf = p
            .processed
            .files
            .iter()
            .find(|f| f.file == old_supplemental)
            .cloned()
            .expect("supplemental file in program files");
        if old_supplemental_lsf.path() != new_supplemental.path()
            || !p.can_replace_file_in_program(&old_supplemental_lsf, new_supplemental)
        {
            return (None, Some(new_file_value), false);
        }
        if p.import_helpers_import_specifiers
            .contains_key(&old_supplemental_lsf.path())
            || p.needs_import_helpers_import_specifier(new_supplemental)
        {
            return (None, Some(new_file_value), false);
        }
        if p.jsx_runtime_import_specifiers
            .contains_key(&old_supplemental_lsf.path())
            || !p
                .jsx_runtime_import_specifier_for(new_supplemental)
                .is_empty()
        {
            return (None, Some(new_file_value), false);
        }
    }
    // TODO: reverify compiler options when config has changed?
    let mut processed = p.processed.clone();
    let index = processed
        .files
        .iter()
        .position(|file| file.path() == new_file_value.path())
        .expect("old file in program files");
    processed.files[index] = new_file_value.clone();
    processed
        .files_by_path
        .insert(new_file_value.path(), new_file_value.file);
    if !old_supplemental_files.is_empty() {
        for (i, &old_supplemental) in old_supplemental_files.iter().enumerate() {
            let new_supplemental = &new_supplemental_files[i];
            if let Some(supplemental_index) = processed
                .files
                .iter()
                .position(|f| f.file == old_supplemental)
            {
                processed.files[supplemental_index] = new_supplemental.clone();
                processed
                    .files_by_path
                    .insert(new_supplemental.path(), new_supplemental.file);
            }
        }
    }

    let source_file_ids: Vec<NodeId> = processed.files.iter().map(|f| f.file).collect();
    let mut arenas = p.arenas.clone();
    let mut set_arena = |file_index: u32, cell: Rc<ArenaCell>| {
        let idx = file_index as usize;
        if idx >= arenas.len() {
            arenas.resize_with(idx + 1, || None);
        }
        arenas[idx] = Some(cell);
    };
    set_arena(new_file_value.file.file_index(), new_file_value.nodes.clone());
    for supplemental in &new_supplemental_files {
        set_arena(supplemental.file.file_index(), supplemental.nodes.clone());
    }

    let result = Rc::new(Program {
        options: p.options.clone(),
        opts: p.opts.clone(),
        hosts: ProgramHosts {
            host: new_host,
            tracing: None,
        },
        resolution_data: Rc::new(p.resolution_data.as_ref().clone()),
        checker_pool: RefCell::new(None),
        compiler_checker_pool: RefCell::new(None),
        include_processor: IncludeProcessor::default(),
        module_resolution_error: None,
        case_sensitivity: p.case_sensitivity,
        // Share the global symbol arena: `SymbolId`s of unchanged files must
        // keep indexing the same `Vec`, and `Symbol` is not `Clone` (arena
        // design). The changed file's rebind appends fresh ids at the tail —
        // old-program ids stay valid (Go parity: rebinding allocates new
        // `*ast.Symbol`s while old ones remain reachable).
        symbols: p.symbols.clone(),
        processed,
        uses_uri_style_node_core_modules: p.uses_uri_style_node_core_modules,
        common_source_directory: OnceCell::new(),
        declaration_diagnostic_cache: RefCell::new(FxHashMap::default()),
        program_diagnostics: RefCell::new(p.program_diagnostics.borrow().clone()),
        has_emit_blocking_diagnostics: RefCell::new(
            p.has_emit_blocking_diagnostics.borrow().clone(),
        ),
        content_mapper_option_diagnostics: RefCell::new(
            p.content_mapper_option_diagnostics.borrow().clone(),
        ),
        source_files_to_emit: RefCell::new(None),
        unresolved_imports: OnceCell::new(),
        known_symlinks: OnceCell::new(),
        package_names: OnceCell::new(),
        has_ts_file: OnceCell::new(),
        packages_map: OnceCell::new(),
        pending_processing_diagnostics: RefCell::new(
            p.pending_processing_diagnostics.borrow().to_vec(),
        ),
        source_file_ids,
        file_rank_map: RefCell::new(None),
        arenas,
        last_arena: std::cell::RefCell::new(None),
    });
    // `tryReuse` — copy over the already-initialized lazy values.
    if let Some(v) = p.unresolved_imports.get() {
        let _ = result.unresolved_imports.set(v.clone());
    }
    if let Some(v) = p.known_symlinks.get() {
        let _ = result.known_symlinks.set(v.clone());
    }
    if let Some(v) = p.package_names.get() {
        let _ = result.package_names.set(v.clone());
    }
    // `result.initCheckerPool(createCheckerPool)`.
    result.init_checker_pool(create_checker_pool, &result);
    (Some(result), Some(new_file_value), true)
}

// ---------------------------------------------------------------------------
// Free functions (Go file order)
// ---------------------------------------------------------------------------

/// `equalModuleSpecifiers`.
fn equal_module_specifiers(n1: &Node, n2: &Node, nodes1: &[Node], nodes2: &[Node]) -> bool {
    n1.kind == n2.kind && (!is_string_literal(n1) || n1.text(nodes1) == n2.text(nodes2))
}

/// `equalModuleAugmentationNames`.
fn equal_module_augmentation_names(n1: &Node, n2: &Node, nodes1: &[Node], nodes2: &[Node]) -> bool {
    n1.kind == n2.kind && n1.text(nodes1) == n2.text(nodes2)
}

/// `equalFileReferences`.
pub fn equal_file_references(f1: &FileReference, f2: &FileReference) -> bool {
    f1.file_name == f2.file_name
        && f1.resolution_mode == f2.resolution_mode
        && f1.preserve == f2.preserve
}

/// `equalCheckJSDirectives`.
fn equal_check_js_directives(d1: Option<&CheckJsDirective>, d2: Option<&CheckJsDirective>) -> bool {
    (d1.is_none() && d2.is_none())
        || (d1.is_some() && d2.is_some() && d1.unwrap().enabled == d2.unwrap().enabled)
}

impl Program {
    /// `filterAndSortDiagnostics`.
    fn filter_and_sort_diagnostics(&self, diags: Vec<DiagnosticRef>) -> Vec<DiagnosticRef> {
        sort_and_deduplicate_diagnostics(
            diags
                .into_iter()
                .filter(|diag| {
                    let d = lock_diagnostic(diag);
                    let file = d.file();
                    if !d.reports_unnecessary() || file.is_none() || !d.source().is_empty() {
                        return true;
                    }
                    let file = file.unwrap();
                    // `file.SpanMap()` in Go is a live read off the
                    // `*SourceFile` — a `DiagnosticFile` snapshotted during
                    // parse can predate `SetContentMapperInfo`, so prefer the
                    // live node's map.
                    let span_map = file.node.and_then(|node| {
                        let nodes = self.arena_of(node);
                        nodes[node].as_source_file().span_map()
                    });
                    let span_map = span_map.as_ref().or(file.span_map.as_ref());
                    let Some(span_map) = span_map else {
                        return true;
                    };
                    let (_, fidelity) =
                        tsc_spanmap::SpanMap::virtual_to_original_span(Some(span_map), d.loc());
                    fidelity != tsc_spanmap::Fidelity::None
                })
                .collect(),
        )
    }
}

/// `filterAndSortDiagnostics` — free-fn shim for non-Program callers that
/// only have `DiagnosticFile` snapshots (no live span-map re-read).
fn filter_and_sort_diagnostics(diags: Vec<DiagnosticRef>) -> Vec<DiagnosticRef> {
    sort_and_deduplicate_diagnostics(
        diags
            .into_iter()
            .filter(|diag| {
                let d = lock_diagnostic(diag);
                let file = d.file();
                if !d.reports_unnecessary() || file.is_none() || !d.source().is_empty() {
                    return true;
                }
                let file = file.unwrap();
                let Some(span_map) = &file.span_map else {
                    return true;
                };
                let (_, fidelity) =
                    tsc_spanmap::SpanMap::virtual_to_original_span(Some(span_map), d.loc());
                fidelity != tsc_spanmap::Fidelity::None
            })
            .collect(),
    )
}

/// `SortAndDeduplicateDiagnostics`.
pub fn sort_and_deduplicate_diagnostics(mut diagnostics: Vec<DiagnosticRef>) -> Vec<DiagnosticRef> {
    diagnostics.sort_by(|a, b| diagnostic::compare_diagnostics(a, b).cmp(&0));
    compact_and_merge_related_infos(diagnostics)
}

/// `compactAndMergeRelatedInfos` — removes duplicate diagnostics and, for
/// sequences differing only by related information, creates a single
/// diagnostic with sorted, deduplicated related information.
fn compact_and_merge_related_infos(diagnostics: Vec<DiagnosticRef>) -> Vec<DiagnosticRef> {
    if diagnostics.len() < 2 {
        return diagnostics;
    }
    let mut out: Vec<DiagnosticRef> = Vec::with_capacity(diagnostics.len());
    let mut i = 0;
    while i < diagnostics.len() {
        let mut d = diagnostics[i].clone();
        let mut n = 1;
        while i + n < diagnostics.len()
            && diagnostic::equal_diagnostics_no_related_info(&d, &diagnostics[i + n])
        {
            n += 1;
        }
        if n > 1 {
            let mut related_infos: Vec<DiagnosticRef> = Vec::new();
            for k in 0..n {
                related_infos.extend(
                    lock_diagnostic(&diagnostics[i + k])
                        .related_information()
                        .to_vec(),
                );
            }
            if !related_infos.is_empty() {
                related_infos.sort_by(|a, b| diagnostic::compare_diagnostics(a, b).cmp(&0));
                related_infos.dedup_by(|a, b| diagnostic::equal_diagnostics(a, b));
                let cloned = lock_diagnostic(&d).clone_diagnostic();
                lock_diagnostic(&cloned).set_related_info(related_infos);
                d = cloned;
            }
        }
        out.push(d);
        i += n;
    }
    out
}

/// `isCommentOrBlankLine`.
fn is_comment_or_blank_line(text: &str, mut pos: usize) -> bool {
    let bytes = text.as_bytes();
    while pos < bytes.len() && (bytes[pos] == b' ' || bytes[pos] == b'\t') {
        pos += 1;
    }
    pos == bytes.len()
        || pos < bytes.len() && (bytes[pos] == b'\r' || bytes[pos] == b'\n')
        || pos + 1 < bytes.len() && bytes[pos] == b'/' && bytes[pos + 1] == b'/'
}

/// `FilterNoEmitSemanticDiagnostics`.
pub fn filter_no_emit_semantic_diagnostics(
    diagnostics: Vec<DiagnosticRef>,
    options: &CompilerOptions,
) -> Vec<DiagnosticRef> {
    if options.no_emit != TS_TRUE {
        return diagnostics;
    }
    diagnostics
        .into_iter()
        .filter(|d| !lock_diagnostic(d).skipped_on_no_emit())
        .collect()
}

/// `applyContentMapperDiagnosticDirectives`.
fn apply_content_mapper_diagnostic_directives(
    program: &Program,
    source_file: NodeId,
    diags: Vec<DiagnosticRef>,
) -> Vec<DiagnosticRef> {
    let nodes = program.arena_of(source_file);
    let directives = nodes[source_file]
        .as_source_file()
        .diagnostic_directives()
        .to_vec();
    if directives.is_empty() {
        return diags;
    }
    let mut used = vec![false; directives.len()];
    let mark_used = |diag: &DiagnosticRef, used: &mut Vec<bool>| -> bool {
        let d = lock_diagnostic(diag);
        if d.file().and_then(|f| f.node) != Some(source_file) || !d.source().is_empty() {
            return false;
        }
        for (i, directive) in directives.iter().enumerate() {
            if d.pos() >= directive.virtual_range.pos() && d.pos() < directive.virtual_range.end() {
                used[i] = true;
                return true;
            }
        }
        false
    };
    let mut filtered: Vec<DiagnosticRef> = diags
        .into_iter()
        .filter(|diag| !mark_used(diag, &mut used))
        .collect();
    for (i, directive) in directives.iter().enumerate() {
        if directive.policy == tsc_ast::MappedDiagnosticDirectivePolicy::Expect && !used[i] {
            filtered.push(new_external_diagnostic(
                Some(DiagnosticFile::from_node(source_file, &nodes)),
                directive.original_range,
                directive.source.clone(),
                Category::Error,
                directive.unused_code,
                directive.unused_message_text.clone(),
            ));
        }
    }
    filtered
}

/// `getAdditionalJSSyntacticDiagnostics` — option-dependent syntactic
/// diagnostics for JS files that aren't covered by the parser or the
/// checker. Mirrors Strada's `getJSSyntacticDiagnosticsForFile`.
fn get_additional_js_syntactic_diagnostics(program: &Program, file: NodeId) -> Vec<DiagnosticRef> {
    if program.options.experimental_decorators == TS_TRUE {
        return Vec::new();
    }
    let mut diags: Vec<DiagnosticRef> = Vec::new();
    // Parameter decorators are only valid with experimentalDecorators. Without it,
    // the checker would report this, but the checker doesn't run on unchecked JS files.
    let nodes = program.arena_of(file);
    let mut walk = |node: NodeId, nodes: &Vec<Node>, diags: &mut Vec<DiagnosticRef>| {
        walk_inner(node, nodes, file, diags);
    };
    walk(file, &nodes, &mut diags);
    fn walk_inner(node: NodeId, nodes: &Vec<Node>, file: NodeId, diags: &mut Vec<DiagnosticRef>) {
        if nodes[node]
            .subtree_facts(nodes)
            .contains(tsc_ast::SubtreeFacts::CONTAINS_DECORATORS)
            == false
        {
            return;
        }
        if nodes[node].kind == tsc_ast::Kind::Parameter && tsc_ast::has_decorators(&nodes[node]) {
            if let Some(decorator) = nodes[node]
                .modifier_nodes()
                .unwrap_or(&[])
                .iter()
                .copied()
                .find(|&m| tsc_ast::is_decorator(&nodes[m]))
            {
                diags.push(new_diagnostic(
                    Some(DiagnosticFile::from_node(file, nodes)),
                    nodes[decorator].loc,
                    &diagnostics::Decorators_are_not_valid_here,
                    &[] as &[String],
                ));
            }
        }
        nodes[node].for_each_child(nodes, &mut |child| {
            walk_inner(child, nodes, file, diags);
            false
        });
    }
    diags
}

/// `hasZeroOrOneAsteriskCharacter`.
fn has_zero_or_one_asterisk_character(str_: &str) -> bool {
    let mut seen_asterisk = false;
    for ch in str_.chars() {
        if ch == '*' {
            if !seen_asterisk {
                seen_asterisk = true;
            } else {
                // have already seen asterisk
                return false;
            }
        }
    }
    true
}

/// `moduleResolutionSupportsPackageJsonExportsAndImports`.
fn module_resolution_supports_package_json_exports_and_imports(
    module_resolution: ModuleResolutionKind,
) -> bool {
    (ModuleResolutionKind::Node16..=ModuleResolutionKind::NodeNext).contains(&module_resolution)
        || module_resolution == ModuleResolutionKind::Bundler
}

/// `emitModuleKindIsNonNodeESM`.
fn emit_module_kind_is_non_node_esm(module_kind: ModuleKind) -> bool {
    (ModuleKind::ES2015..=ModuleKind::ESNext).contains(&module_kind)
}

/// `plainJSErrors` — the lazily-initialized code set.
fn plain_js_errors() -> &'static HashSet<i32> {
    static PLAIN_JS_ERRORS: std::sync::OnceLock<HashSet<i32>> = std::sync::OnceLock::new();
    PLAIN_JS_ERRORS.get_or_init(|| {
        [
            // binder errors
            diagnostics::Cannot_redeclare_block_scoped_variable_0.code(),
            diagnostics::A_module_cannot_have_multiple_default_exports.code(),
            diagnostics::Another_export_default_is_here.code(),
            diagnostics::The_first_export_default_is_here.code(),
            diagnostics::Identifier_expected_0_is_a_reserved_word_at_the_top_level_of_a_module.code(),
            diagnostics::Identifier_expected_0_is_a_reserved_word_in_strict_mode_Modules_are_automatically_in_strict_mode.code(),
            diagnostics::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here.code(),
            diagnostics::X_constructor_is_a_reserved_word.code(),
            diagnostics::X_delete_cannot_be_called_on_an_identifier_in_strict_mode.code(),
            diagnostics::Code_contained_in_a_class_is_evaluated_in_JavaScript_s_strict_mode_which_does_not_allow_this_use_of_0_For_more_information_see_https_Colon_Slash_Slashdeveloper_mozilla_org_Slashen_US_Slashdocs_SlashWeb_SlashJavaScript_SlashReference_SlashStrict_mode.code(),
            diagnostics::Invalid_use_of_0_Modules_are_automatically_in_strict_mode.code(),
            diagnostics::Invalid_use_of_0_in_strict_mode.code(),
            diagnostics::A_label_is_not_allowed_here.code(),
            diagnostics::X_with_statements_are_not_allowed_in_strict_mode.code(),
            // grammar errors
            diagnostics::A_break_statement_can_only_be_used_within_an_enclosing_iteration_or_switch_statement.code(),
            diagnostics::A_break_statement_can_only_jump_to_a_label_of_an_enclosing_statement.code(),
            diagnostics::A_class_declaration_without_the_default_modifier_must_have_a_name.code(),
            diagnostics::A_class_member_cannot_have_the_0_keyword.code(),
            diagnostics::A_comma_expression_is_not_allowed_in_a_computed_property_name.code(),
            diagnostics::A_continue_statement_can_only_be_used_within_an_enclosing_iteration_statement.code(),
            diagnostics::A_continue_statement_can_only_jump_to_a_label_of_an_enclosing_iteration_statement.code(),
            diagnostics::A_default_clause_cannot_appear_more_than_once_in_a_switch_statement.code(),
            diagnostics::A_default_export_must_be_at_the_top_level_of_a_file_or_module_declaration.code(),
            diagnostics::A_deferred_import_must_specify_a_namespace_binding.code(),
            diagnostics::A_definite_assignment_assertion_is_not_permitted_in_this_context.code(),
            diagnostics::A_destructuring_declaration_must_have_an_initializer.code(),
            diagnostics::A_get_accessor_cannot_have_parameters.code(),
            diagnostics::A_rest_element_cannot_contain_a_binding_pattern.code(),
            diagnostics::A_rest_element_cannot_have_a_property_name.code(),
            diagnostics::A_rest_element_cannot_have_an_initializer.code(),
            diagnostics::A_rest_element_must_be_last_in_a_destructuring_pattern.code(),
            diagnostics::A_rest_parameter_cannot_have_an_initializer.code(),
            diagnostics::A_rest_parameter_must_be_last_in_a_parameter_list.code(),
            diagnostics::A_rest_parameter_or_binding_pattern_may_not_have_a_trailing_comma.code(),
            diagnostics::A_return_statement_cannot_be_used_inside_a_class_static_block.code(),
            diagnostics::A_set_accessor_cannot_have_rest_parameter.code(),
            diagnostics::A_set_accessor_must_have_exactly_one_parameter.code(),
            diagnostics::A_source_phase_import_must_specify_a_local_binding.code(),
            diagnostics::An_export_declaration_can_only_be_used_at_the_top_level_of_a_module.code(),
            diagnostics::An_export_declaration_cannot_have_modifiers.code(),
            diagnostics::An_import_declaration_can_only_be_used_at_the_top_level_of_a_module.code(),
            diagnostics::An_import_declaration_cannot_have_modifiers.code(),
            diagnostics::An_object_member_cannot_be_declared_optional.code(),
            diagnostics::Argument_of_dynamic_import_cannot_be_spread_element.code(),
            diagnostics::Cannot_assign_to_private_method_0_Private_methods_are_not_writable.code(),
            diagnostics::Cannot_redeclare_identifier_0_in_catch_clause.code(),
            diagnostics::Catch_clause_variable_cannot_have_an_initializer.code(),
            diagnostics::Class_decorators_can_t_be_used_with_static_private_identifier_Consider_removing_the_experimental_decorator.code(),
            diagnostics::Classes_can_only_extend_a_single_class.code(),
            diagnostics::Classes_may_not_have_a_field_named_constructor.code(),
            diagnostics::Did_you_mean_to_use_a_Colon_An_can_only_follow_a_property_name_when_the_containing_object_literal_is_part_of_a_destructuring_pattern.code(),
            diagnostics::Duplicate_label_0.code(),
            diagnostics::Dynamic_imports_can_only_accept_a_module_specifier_and_an_optional_set_of_attributes_as_arguments.code(),
            diagnostics::X_for_await_loops_cannot_be_used_inside_a_class_static_block.code(),
            diagnostics::JSX_attributes_must_only_be_assigned_a_non_empty_expression.code(),
            diagnostics::JSX_elements_cannot_have_multiple_attributes_with_the_same_name.code(),
            diagnostics::JSX_expressions_may_not_use_the_comma_operator_Did_you_mean_to_write_an_array.code(),
            diagnostics::JSX_property_access_expressions_cannot_include_JSX_namespace_names.code(),
            diagnostics::Jump_target_cannot_cross_function_boundary.code(),
            diagnostics::Line_terminator_not_permitted_before_arrow.code(),
            diagnostics::Modifiers_cannot_appear_here.code(),
            diagnostics::Named_and_namespace_imports_are_not_allowed_in_a_source_phase_import.code(),
            diagnostics::Only_a_single_variable_declaration_is_allowed_in_a_for_in_statement.code(),
            diagnostics::Only_a_single_variable_declaration_is_allowed_in_a_for_of_statement.code(),
            diagnostics::Optional_chaining_cannot_be_used_with_import_source.code(),
            diagnostics::Private_identifiers_are_not_allowed_outside_class_bodies.code(),
            diagnostics::Private_identifiers_are_only_allowed_in_class_bodies_and_may_only_be_used_as_part_of_a_class_member_declaration_property_access_or_on_the_left_hand_side_of_an_in_expression.code(),
            diagnostics::Property_0_is_not_accessible_outside_class_1_because_it_has_a_private_identifier.code(),
            diagnostics::Source_phase_imports_are_not_allowed_on_statements_that_compile_to_CommonJS_require_calls.code(),
            diagnostics::Source_phase_imports_are_only_supported_when_the_module_option_is_set_to_esnext_nodenext_or_preserve.code(),
            diagnostics::Tagged_template_expressions_are_not_permitted_in_an_optional_chain.code(),
            diagnostics::The_left_hand_side_of_a_for_of_statement_may_not_be_async.code(),
            diagnostics::The_variable_declaration_of_a_for_in_statement_cannot_have_an_initializer.code(),
            diagnostics::The_variable_declaration_of_a_for_of_statement_cannot_have_an_initializer.code(),
            diagnostics::Trailing_comma_not_allowed.code(),
            diagnostics::Variable_declaration_list_cannot_be_empty.code(),
            diagnostics::X_0_and_1_operations_cannot_be_mixed_without_parentheses.code(),
            diagnostics::X_0_expected.code(),
            diagnostics::X_0_is_not_a_valid_meta_property_for_keyword_import_Did_you_mean_meta_defer_or_source.code(),
            diagnostics::X_0_is_not_a_valid_meta_property_for_keyword_1_Did_you_mean_2.code(),
            diagnostics::X_0_list_cannot_be_empty.code(),
            diagnostics::X_0_modifier_already_seen.code(),
            diagnostics::X_0_modifier_cannot_appear_on_a_constructor_declaration.code(),
            diagnostics::X_0_modifier_cannot_appear_on_a_module_or_namespace_element.code(),
            diagnostics::X_0_modifier_cannot_appear_on_a_parameter.code(),
            diagnostics::X_0_modifier_cannot_appear_on_class_elements_of_this_kind.code(),
            diagnostics::X_0_modifier_cannot_be_used_here.code(),
            diagnostics::X_0_modifier_must_precede_1_modifier.code(),
            diagnostics::X_0_declarations_can_only_be_declared_inside_a_block.code(),
            diagnostics::X_0_declarations_must_be_initialized.code(),
            diagnostics::X_extends_clause_already_seen.code(),
            diagnostics::X_let_is_not_allowed_to_be_used_as_a_name_in_let_or_const_declarations.code(),
            diagnostics::Class_constructor_may_not_be_a_generator.code(),
            diagnostics::Class_constructor_may_not_be_an_accessor.code(),
            diagnostics::X_await_expressions_are_only_allowed_within_async_functions_and_at_the_top_levels_of_modules.code(),
            diagnostics::X_await_using_statements_are_only_allowed_within_async_functions_and_at_the_top_levels_of_modules.code(),
            diagnostics::Private_field_0_must_be_declared_in_an_enclosing_class.code(),
            // Type errors
            diagnostics::This_condition_will_always_return_0_since_JavaScript_compares_objects_by_reference_not_value.code(),
        ]
        .into_iter()
        .collect()
    })
}

// ---------------------------------------------------------------------------
// ProgramLike / HandleNoEmitOptions / GetDiagnosticsOfAnyProgram
// ---------------------------------------------------------------------------

/// `type ProgramLike interface`.
pub trait ProgramLike {
    /// `Options()`.
    fn options(&self) -> &CompilerOptions;
    /// `GetSourceFile(fileName)`.
    fn get_source_file(&self, file_name: &RootedFilePath) -> Option<NodeId>;
    /// `GetSourceFiles()`.
    fn get_source_files(&self) -> Vec<NodeId>;
    /// `GetConfigFileParsingDiagnostics()`.
    fn get_config_file_parsing_diagnostics(&self) -> Vec<DiagnosticRef>;
    /// `GetSyntacticDiagnostics(ctx, file)`.
    fn get_syntactic_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef>;
    /// `GetBindDiagnostics(ctx, file)`.
    fn get_bind_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef>;
    /// `GetProgramDiagnostics()`.
    fn get_program_diagnostics(&self) -> Vec<DiagnosticRef>;
    /// `GetGlobalDiagnostics(ctx)`.
    fn get_global_diagnostics(&self, ctx: Context) -> Vec<DiagnosticRef>;
    /// `GetSemanticDiagnostics(ctx, file)`.
    fn get_semantic_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef>;
    /// `GetDeclarationDiagnostics(ctx, file)`.
    fn get_declaration_diagnostics(&self, ctx: Context, file: Option<NodeId>)
    -> Vec<DiagnosticRef>;
    /// `GetSuggestionDiagnostics(ctx, file)`.
    fn get_suggestion_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef>;
    /// `Emit(ctx, options)`.
    fn emit(&self, ctx: Context, options: &mut EmitOptions<'_>) -> EmitResult;
    /// `CommonSourceDirectory()`.
    fn common_source_directory(&self) -> RootedDirectoryPath;
    /// `IsSourceFileDefaultLibrary(path)`.
    fn is_source_file_default_library(&self, path: &PathKey) -> bool;
    /// `Program()` — narrows to `*Program` for program-only state (Go's
    /// `program.Program().contentMapperDiagnostics`).
    fn program(&self) -> &Program;
    /// PORT(addition): release the checker pool's `Rc<Checker>`s so the
    /// `Program -> checkerPool -> Checker.program -> Program` `Rc` cycle
    /// breaks and the program graph drops at teardown (Go relies on GC for
    /// this). Default no-op for non-`Program` implementors.
    fn release_checker_pool(&self) {}
}

impl ProgramLike for Program {
    fn options(&self) -> &CompilerOptions {
        &self.options
    }
    fn get_source_file(&self, file_name: &RootedFilePath) -> Option<NodeId> {
        Program::get_source_file(self, file_name)
    }
    fn get_source_files(&self) -> Vec<NodeId> {
        self.source_files()
    }
    fn get_config_file_parsing_diagnostics(&self) -> Vec<DiagnosticRef> {
        Program::get_config_file_parsing_diagnostics(self)
    }
    fn get_syntactic_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef> {
        Program::get_syntactic_diagnostics(self, ctx, file)
    }
    fn get_bind_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef> {
        Program::get_bind_diagnostics(self, ctx, file)
    }
    fn get_program_diagnostics(&self) -> Vec<DiagnosticRef> {
        Program::get_program_diagnostics(self)
    }
    fn get_global_diagnostics(&self, ctx: Context) -> Vec<DiagnosticRef> {
        Program::get_global_diagnostics(self, ctx)
    }
    fn get_semantic_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef> {
        Program::get_semantic_diagnostics(self, ctx, file)
    }
    fn get_declaration_diagnostics(
        &self,
        ctx: Context,
        file: Option<NodeId>,
    ) -> Vec<DiagnosticRef> {
        Program::get_declaration_diagnostics(self, ctx, file)
    }
    fn get_suggestion_diagnostics(&self, ctx: Context, file: Option<NodeId>) -> Vec<DiagnosticRef> {
        Program::get_suggestion_diagnostics(self, ctx, file)
    }
    fn emit(&self, ctx: Context, options: &mut EmitOptions<'_>) -> EmitResult {
        Program::emit(self, ctx, options)
    }
    fn common_source_directory(&self) -> RootedDirectoryPath {
        Program::common_source_directory(self)
    }
    fn is_source_file_default_library(&self, path: &PathKey) -> bool {
        Program::is_source_file_default_library(self, path)
    }
    fn program(&self) -> &Program {
        self
    }
    fn release_checker_pool(&self) {
        Program::release_checker_pool(self)
    }
}

/// `HandleNoEmitOptions` — mirrors tsc's `handleNoEmitOptions`.
pub fn handle_no_emit_options(
    ctx: &Context,
    program: &dyn ProgramLike,
    files: Option<&[NodeId]>,
    emit_build_info: Option<&dyn Fn() -> Option<EmitResult>>,
) -> Option<EmitResult> {
    if program.options().no_emit != TS_TRUE {
        if program.options().no_emit_on_error != TS_TRUE {
            return None; // NoEmit is false and NoEmitOnError is also false, so we can proceed with normal emit
        }

        let diagnostics = get_diagnostics_of_any_program(
            ctx,
            program,
            files,
            true,
            &|p, ctx, f| p.get_bind_diagnostics(ctx, f),
            &|p, ctx, f| p.get_semantic_diagnostics(ctx, f),
        );
        if diagnostics.is_empty() {
            return None; // NoEmitOnError is enabled, but no diagnostics were found, so we can proceed with emitting
        }
        return Some(EmitResult {
            diagnostics,
            emit_skipped: true,
            ..Default::default()
        });
    }
    if files.is_some() {
        return Some(EmitResult {
            emit_skipped: true,
            ..Default::default()
        });
    }
    if let Some(emit_build_info) = emit_build_info {
        if let Some(result) = emit_build_info() {
            return Some(result);
        }
    }
    Some(EmitResult::default())
}

/// `GetDiagnosticsOfAnyProgram`.
pub fn get_diagnostics_of_any_program(
    ctx: &Context,
    program: &dyn ProgramLike,
    files: Option<&[NodeId]>,
    skip_no_emit_check_for_dts_diagnostics: bool,
    get_bind_diagnostics: &dyn Fn(&dyn ProgramLike, Context, Option<NodeId>) -> Vec<DiagnosticRef>,
    get_semantic_diagnostics: &dyn Fn(
        &dyn ProgramLike,
        Context,
        Option<NodeId>,
    ) -> Vec<DiagnosticRef>,
) -> Vec<DiagnosticRef> {
    let mut all_diagnostics = program.get_config_file_parsing_diagnostics();
    let config_file_parsing_diagnostics_length = all_diagnostics.len();

    let append_diagnostics_for_all_files = |diagnostics: &mut Vec<DiagnosticRef>,
                                            get_diagnostics: &dyn Fn(
        &dyn ProgramLike,
        Context,
        Option<NodeId>,
    ) -> Vec<DiagnosticRef>| {
        match files {
            None => diagnostics.extend(get_diagnostics(program, ctx.clone(), None)),
            Some(files) => {
                for &file in files {
                    diagnostics.extend(get_diagnostics(program, ctx.clone(), Some(file)));
                }
            }
        }
    };

    let mut syntactic_diagnostics: Vec<DiagnosticRef> = Vec::new();
    append_diagnostics_for_all_files(&mut syntactic_diagnostics, &|p, ctx, f| {
        p.get_syntactic_diagnostics(ctx, f)
    });
    if !syntactic_diagnostics.is_empty() {
        // Per-file content mapper failures are syntactic diagnostics, but the locationless diagnostic
        // that disables a repeatedly failing mapper must still be reported.
        all_diagnostics.extend(program.program().content_mapper_diagnostics.iter().cloned());
    }
    all_diagnostics.extend(syntactic_diagnostics);

    // If we didn't have any syntactic errors, then also try getting the program (options),
    // global and semantic errors.
    if all_diagnostics.len() == config_file_parsing_diagnostics_length {
        all_diagnostics.extend(program.get_program_diagnostics());

        // Do binding early so we can track the time.
        let mut unused: Vec<DiagnosticRef> = Vec::new();
        append_diagnostics_for_all_files(&mut unused, get_bind_diagnostics);

        if program.options().list_files_only.is_false_or_unknown() {
            all_diagnostics.extend(program.get_global_diagnostics(ctx.clone()));

            if all_diagnostics.len() == config_file_parsing_diagnostics_length {
                append_diagnostics_for_all_files(&mut all_diagnostics, get_semantic_diagnostics);
                // Incremental programs cache checking globals with file diagnostics;
                // a late sweep would also collect incidental signature-generation globals.
                all_diagnostics.extend(program.get_global_diagnostics(ctx.clone()));
            }

            if (skip_no_emit_check_for_dts_diagnostics || program.options().no_emit == TS_TRUE)
                && program.options().get_emit_declarations()
                && all_diagnostics.len() == config_file_parsing_diagnostics_length
            {
                append_diagnostics_for_all_files(&mut all_diagnostics, &|p, ctx, f| {
                    p.get_declaration_diagnostics(ctx, f)
                });
            }
        }
    }
    all_diagnostics
}

// ---------------------------------------------------------------------------
// Trait implementations
// ---------------------------------------------------------------------------

impl OutputPathsHost for Program {
    fn common_source_directory(&self) -> RootedDirectoryPath {
        self.common_source_directory()
    }
    fn content_mapper_extensions(&self) -> &[String] {
        self.opts.config.content_mapper_extensions()
    }
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }
}

impl ModuleSpecifierGenerationHost for Program {
    fn get_symlink_cache(&self) -> Option<&KnownSymlinks> {
        self.get_symlink_cache_opt()
    }
    fn get_global_typings_cache_location(&self) -> RootedDirectoryPath {
        self.opts.typings_location.clone()
    }
    fn base_directory(&self) -> RootedDirectoryPath {
        self.base_directory()
    }
    fn get_project_reference_from_source(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        self.mapper().get_project_reference_from_source(path)
    }
    fn get_redirect_targets(&self, path: &PathKey) -> Vec<RootedFilePath> {
        self.get_redirect_targets(path)
    }
    fn get_source_of_project_reference_if_output_included(
        &self,
        file: &dyn HasFileName,
    ) -> RootedFilePath {
        self.get_source_of_project_reference_if_output_included(file)
    }
    fn file_exists(&self, path: &RootedFilePath) -> bool {
        self.file_exists(path)
    }
    fn get_nearest_ancestor_directory_with_package_json(
        &self,
        dirname: &RootedDirectoryPath,
    ) -> RootedDirectoryPath {
        self.get_nearest_ancestor_directory_with_package_json(dirname)
    }
    fn get_package_json_info(&self, pkg_json_path: &RootedFilePath) -> Option<Arc<InfoCacheEntry>> {
        self.get_package_json_info(pkg_json_path)
    }
    fn get_default_resolution_mode_for_file(&self, file: &dyn HasFileName) -> ResolutionMode {
        self.get_default_resolution_mode_for_file(file)
    }
    fn get_resolved_module_from_module_specifier(
        &self,
        file: &dyn HasFileName,
        module_specifier: NodeId,
    ) -> Option<ResolvedModule> {
        self.get_resolved_module_from_module_specifier_has(file, module_specifier)
    }
    fn get_mode_for_usage_location(
        &self,
        file: &dyn HasFileName,
        module_specifier: NodeId,
    ) -> ResolutionMode {
        self.get_mode_for_usage_location(file, module_specifier)
    }
}

impl tsc_checker::checker_types::Host for Program {}

impl tsc_checker::checker_types::Program for Program {
    fn options(&self) -> Rc<CompilerOptions> {
        self.options.clone()
    }
    fn source_files(&self) -> Vec<NodeId> {
        self.source_files()
    }
    fn file_rank(&self, source_file: NodeId) -> Option<usize> {
        let mut cache = self.file_rank_map.borrow_mut();
        let map = cache.get_or_insert_with(|| {
            self.source_file_ids
                .iter()
                .enumerate()
                .map(|(i, &f)| (f, i))
                .collect()
        });
        map.get(&source_file).copied()
    }
    fn bind_source_files(&self) {
        self.bind_source_files();
    }
    fn symbols(&self) -> SymbolArena {
        self.symbols.clone()
    }
    fn file_exists(&self, file_name: &RootedFilePath) -> bool {
        self.file_exists(file_name)
    }
    fn get_source_file_for_resolved_module(&self, resolved: &ResolvedModule) -> Option<NodeId> {
        self.get_source_file_for_resolved_module(resolved)
    }
    fn get_emit_module_format_of_file(&self, source_file: &dyn HasFileName) -> ModuleKind {
        self.get_emit_module_format_of_file(source_file)
    }
    fn get_emit_syntax_for_usage_location(
        &self,
        source_file: &dyn HasFileName,
        usage_location: NodeId,
    ) -> ResolutionMode {
        self.get_emit_syntax_for_usage_location(source_file, usage_location)
    }
    fn get_implied_node_format_for_emit(&self, source_file: &dyn HasFileName) -> ModuleKind {
        self.get_implied_node_format_for_emit(source_file)
    }
    fn get_resolved_module(
        &self,
        current_source_file: &dyn HasFileName,
        module_reference: &str,
        mode: ResolutionMode,
    ) -> Option<ResolvedModule> {
        self.get_resolved_module(current_source_file, module_reference, mode)
    }
    fn get_resolved_modules(&self) -> &FxHashMap<PathKey, ModeAwareCache<Option<ResolvedModule>>> {
        &self.resolved_modules
    }
    fn get_packages_map(&self) -> FxHashMap<String, bool> {
        self.packages_map()
    }
    fn get_source_file_meta_data(&self, path: &PathKey) -> SourceFileMetaData {
        self.get_source_file_meta_data(path)
    }
    fn get_jsx_runtime_import_specifier(&self, path: &PathKey) -> (String, Option<NodeId>) {
        self.get_jsx_runtime_import_specifier(path)
    }
    fn get_import_helpers_import_specifier(&self, path: &PathKey) -> Option<NodeId> {
        self.get_import_helpers_import_specifier(path)
    }
    fn source_file_may_be_emitted(&self, source_file: NodeId, force_dts_emit: bool) -> bool {
        source_file_may_be_emitted(source_file, self, force_dts_emit, false)
    }
    fn is_source_file_default_library(&self, path: &PathKey) -> bool {
        self.is_source_file_default_library(path)
    }
    fn get_project_reference_from_output_dts(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        self.get_project_reference_from_output_dts(path)
    }
    fn get_redirect_for_resolution(
        &self,
        file: &dyn HasFileName,
    ) -> Option<Arc<ParsedCommandLine>> {
        self.mapper().get_redirect_for_resolution(file).0
    }
    fn common_source_directory(&self) -> RootedDirectoryPath {
        self.common_source_directory()
    }
    fn nodes(&self, file_index: u32) -> Rc<NodeArenaBuf> {
        Program::nodes(self, file_index)
    }
    fn nodes_mut(&self, file_index: u32) -> ArenaMut {
        Program::nodes_mut(self, file_index)
    }
    fn nodes_handle(&self, file_index: u32) -> Rc<ArenaCell> {
        self.arena_handle(file_index)
    }
    fn nodes_handle_or_fallback(&self, file_index: u32) -> (u32, Rc<ArenaCell>) {
        Program::nodes_handle_or_fallback(self, file_index)
    }
}

impl CheckerPoolProgram for Program {
    /// `p.SingleThreaded()`.
    fn single_threaded(&self) -> bool {
        self.single_threaded()
    }
}

impl SourceFileMayBeEmittedHost for Program {
    fn smbe_options(&self) -> &CompilerOptions {
        &self.options
    }
    fn smbe_project_reference_from_source(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        self.get_project_reference_from_source(path)
    }
    fn smbe_is_source_file_from_external_library(&self, file: NodeId) -> bool {
        self.is_source_file_from_external_library(file)
    }
    fn smbe_base_directory(&self) -> RootedDirectoryPath {
        self.base_directory()
    }
    fn smbe_case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }
    fn smbe_source_files(&self) -> Vec<NodeId> {
        self.source_files()
    }
    fn smbe_nodes(&self, file_index: u32) -> Rc<NodeArenaBuf> {
        self.nodes(file_index)
    }
}

// ---------------------------------------------------------------------------
// Include-processor helpers used by sibling modules
// ---------------------------------------------------------------------------

impl Program {
    /// `sourceFile.MetaData` accessor used by emit/include plumbing.
    pub fn source_file_meta_data_by_file(&self, file: NodeId) -> SourceFileMetaData {
        let nodes = self.arena_of(file);
        let key = nodes[file].as_source_file().path_key().clone();
        drop(nodes);
        self.get_source_file_meta_data(&key)
    }
}

/// `func CombineEmitResults` — merges per-emitter results in input order.
/// Go's `[]*EmitResult` admits nil entries; the port's emitters always
/// produce a result, so the nil check is dropped.
pub fn combine_emit_results(results: impl Iterator<Item = EmitResult>) -> EmitResult {
    let mut result = EmitResult::default();
    for emit_result in results {
        if emit_result.emit_skipped {
            result.emit_skipped = true;
        }
        result.diagnostics.extend(emit_result.diagnostics);
        result.emitted_files.extend(emit_result.emitted_files);
        result.source_maps.extend(emit_result.source_maps);
    }
    result
}

#[cfg(test)]
mod program_test;

/// Re-export — `ArenaCheckout` lives in `tsc_ast::ast` so the
/// `tsc_checker::checker_types::Program::nodes_mut` signature can name it
/// without a `tsc-checker` → `tsc-compiler` dependency.
pub use tsc_ast::ast::ArenaCheckout;
