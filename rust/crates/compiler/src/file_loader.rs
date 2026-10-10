// Ported from tsc/internal/compiler/fileloader.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `*ast.SourceFile` is `ParsedSourceFile` (`NodeId` + arena); the
// arena moves into the `Program`'s `Rc<RefCell<Vec<Node>>>` arenas when
// `processedFiles` is consumed. `collections.SyncMap`/`sync.Once`/`atomic`
// fields are `RefCell`/`Cell` — the loader is single-threaded (see
// PORTING-NOTES). `module.Resolver`'s Rust trait drops the Go `error`
// return, so `moduleResolutionError` has no counterpart. `*contentmapper.Mapper`
// identity is `Arc::as_ptr` as `usize`. `context.Context` is not modeled.

use std::cell::{Cell, RefCell};
use std::collections::HashSet;
use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::{FileReference, HasFileName, Node, NodeFactory, NodeId, SourceFileMetaData, Uint128};
use tsc_contentmapper::{
    DiagnosticDirectiveErrorKind, Error as ContentMapperError, InitializeErrorKind, Mapper,
    ProjectErrorKind, TransformErrorKind,
};
use tsc_core::compileroptions::{RESOLUTION_MODE_NONE, ResolutionMode};
use tsc_core::options_generated::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use tsc_core::scriptkind::ScriptKind as CoreScriptKind;
use tsc_core::tristate::TS_TRUE;
use tsc_diagnostics::{self as diagnostics};
use tsc_module::{
    DiagAndArgs, ModeAwareCache, ModeAwareCacheKey, ResolutionData, ResolvedModule,
    ResolvedTypeReferenceDirective, Resolver, ResolverOptions,
};
use tsc_tracing::{Tracing, push};
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath, RootedPath};

use crate::file_include::{
    AutomaticTypeDirectiveFileData, FILE_INCLUDE_KIND_AUTOMATIC_TYPE_DIRECTIVE_FILE,
    FILE_INCLUDE_KIND_IMPORT, FILE_INCLUDE_KIND_LIB_FILE, FILE_INCLUDE_KIND_REFERENCE_FILE,
    FILE_INCLUDE_KIND_ROOT_FILE, FILE_INCLUDE_KIND_TYPE_REFERENCE_DIRECTIVE, FileIncludeReason,
    ReferencedFileData,
};
use crate::files_parser::{FilesParser, ParseTask, ResolvedRef};
use crate::host::CompilerHost;
use crate::processing_diagnostic::{IncludeExplainingDiagnostic, ProcessingDiagnostic};
use crate::program::{ProgramConfig, ProgramOptions};
use crate::project_reference_dts_faking_host::CompilerResolutionHost;
use crate::project_reference_file_mapper::{
    ProjectReferenceFileMapper, ProjectReferenceFileMapperBuilder, as_resolved_project_reference,
    compiler_options_arc,
};
use crate::project_reference_parser::{
    ProjectReferenceParser, create_project_reference_parse_tasks,
};

/// `type libResolution struct`.
pub struct LibResolution {
    pub library_name: String,
    pub resolution: Option<ResolvedModule>,
    pub trace: Vec<DiagAndArgs>,
}

/// `maxContentMapperFailures`.
pub const MAX_CONTENT_MAPPER_FAILURES: i32 = 5;

/// `LoadedSourceFile` — a parsed source file whose arena is shared with the
/// program (`*ast.SourceFile` — `NodeId` + `Rc<RefCell<Vec<Node>>>`).
#[derive(Clone)]
pub struct LoadedSourceFile {
    pub file: NodeId,
    pub nodes: Rc<RefCell<Vec<Node>>>,
}

impl LoadedSourceFile {
    /// `SourceFileName()` — borrowed from the arena.
    pub fn file_name(&self) -> RootedFilePath {
        self.nodes.borrow()[self.file]
            .as_source_file()
            .file_name()
            .clone()
    }

    /// `Path()` — borrowed from the arena.
    pub fn path(&self) -> PathKey {
        self.nodes.borrow()[self.file]
            .as_source_file()
            .path_key()
            .clone()
    }
}

impl From<tsc_contentmapper::ParsedSourceFile> for LoadedSourceFile {
    fn from(f: tsc_contentmapper::ParsedSourceFile) -> Self {
        LoadedSourceFile {
            file: f.file,
            nodes: Rc::new(RefCell::new(f.nodes)),
        }
    }
}

/// `LoadedFile` — the result of `parseSourceFile`: the canonical file plus
/// its content-mapped supplementals (`file.SupplementalSourceFiles()` —
/// NodeIds in each supplemental's own arena; the arenas live here).
pub struct LoadedFile {
    pub canonical: LoadedSourceFile,
    pub supplemental: Vec<LoadedSourceFile>,
}

/// `type LibFile struct`.
#[derive(Clone)]
pub struct LibFile {
    pub name: String,
    pub path: RootedFilePath,
    pub path_key: PathKey,
    pub replaced: bool,
}

/// `type sourceFileFromReferenceDiagnostic struct`.
pub struct SourceFileFromReferenceDiagnostic {
    pub message: &'static diagnostics::Message,
    pub args: Vec<String>,
}

/// `type fileLoader struct`.
pub struct FileLoader {
    pub opts: Rc<ProgramConfig>,
    pub host: Arc<dyn CompilerHost>,
    pub tracing: Option<Arc<Tracing>>,
    pub resolver: Arc<dyn Resolver>,
    pub default_library_path: RootedDirectoryPath,
    pub case_sensitivity: tsc_tspath::CaseSensitivity,
    pub supported_extensions: Vec<Vec<String>>,
    pub supported_extensions_with_json_if_resolve_json_module: Vec<Vec<String>>,
    pub content_mapper_extensions: Vec<String>,

    pub files_parser: FilesParser,
    pub root_tasks: Vec<Rc<RefCell<ParseTask>>>,

    /// `totalFileCount`.
    pub total_file_count: Cell<i32>,
    /// `libFileCount`.
    pub lib_file_count: Cell<i32>,

    /// `factory` — `NodeFactory` is shared under a `RefCell` (Go `factoryMu`).
    pub factory: RefCell<NodeFactory<'static>>,

    pub project_references: RefCell<ProjectReferenceFileMapperBuilder>,

    /// `pathForLibFileCache`.
    pub path_for_lib_file_cache: RefCell<FxHashMap<String, Rc<LibFile>>>,
    /// `pathForLibFileResolutions`.
    pub path_for_lib_file_resolutions: RefCell<FxHashMap<PathKey, Rc<LibResolution>>>,

    /// `contentMapperMu`-guarded bookkeeping — plain `RefCell`s (single-threaded).
    pub content_mapper_failures: RefCell<FxHashMap<usize, i32>>,
    /// `contentMapperInitFailed` — `Arc::as_ptr` mapper identities.
    pub content_mapper_init_failed: RefCell<HashSet<usize>>,
    pub content_mapper_diagnostics: RefCell<Vec<DiagnosticRef>>,
}

/// `type redirectsFile struct` — a stand-in `HasFileName` for files deduplicated
/// by package redirects.
#[derive(Clone)]
pub struct RedirectsFile {
    /// `index` — position in the explained file list.
    pub index: usize,
    pub file_name: RootedFilePath,
    pub path: PathKey,
    /// `target` — the surviving file's path key.
    pub target: PathKey,
}

impl HasFileName for RedirectsFile {
    fn file_name(&self) -> &RootedFilePath {
        &self.file_name
    }
    fn path_key(&self) -> &PathKey {
        &self.path
    }
}

/// `type DuplicateSourceFile struct`.
#[derive(Clone)]
pub struct DuplicateSourceFile {
    pub parse_options: SourceFileParseOptions,
    /// `ContentMapperParseOptions` — the acquire-time options for a
    /// content-mapped parse-cache entry.
    pub content_mapper_parse_options: SourceFileParseOptions,
    pub hash: Uint128,
    pub script_kind: CoreScriptKind,
    /// `ContentMapper` is the identity of the content mapper that produced
    /// this file, or "" if the file is not content-mapped.
    pub content_mapper: String,
    /// `IsContentMapperFailureStub` — the file is an empty placeholder from a
    /// failed transform.
    pub is_content_mapper_failure_stub: bool,
}

/// `type processedFiles struct` — the output of the files parser, consumed by
/// `Program` (Go embeds it in `Program` and `filesParser.getProcessedFiles`
// returns it).
#[derive(Default, Clone)]
pub struct ProcessedFiles {
    pub files: Vec<LoadedSourceFile>,
    /// `duplicateSourceFiles` — parsed files dropped from the final program;
    /// kept so their parse-cache acquires could be balanced on dispose
    /// (parse caches are not yet ported — see PORTING-NOTES).
    pub duplicate_source_files: Vec<DuplicateSourceFile>,
    pub files_by_path: FxHashMap<PathKey, NodeId>,
    pub project_reference_file_mapper: Option<Arc<ProjectReferenceFileMapper>>,
    pub missing_files: HashSet<PathKey>,
    pub resolved_modules: FxHashMap<PathKey, ModeAwareCache<Option<ResolvedModule>>>,
    pub type_resolutions_in_file:
        FxHashMap<PathKey, ModeAwareCache<ResolvedTypeReferenceDirective>>,
    pub source_file_meta_datas: FxHashMap<PathKey, SourceFileMetaData>,
    pub jsx_runtime_import_specifiers: FxHashMap<PathKey, JsxRuntimeImportSpecifier>,
    pub import_helpers_import_specifiers: FxHashMap<PathKey, NodeId>,
    pub lib_files: FxHashMap<PathKey, Rc<LibFile>>,
    /// `sourceFilesFoundSearchingNodeModules`.
    pub source_files_found_searching_node_modules: HashSet<PathKey>,
    /// `fileIncludeData` — flattened into these two fields (the struct lives
    /// in include_processor.rs).
    pub file_include_reasons: FxHashMap<PathKey, Vec<Rc<FileIncludeReason>>>,
    pub processing_diagnostics: Vec<ProcessingDiagnostic>,
    /// `outputFileToProjectReferenceSource` — output path → project-reference
    /// source file (only populated when NOT using source of project
    /// reference).
    pub output_file_to_project_reference_source: FxHashMap<PathKey, RootedFilePath>,
    /// `redirectTargetsMap` — redirect target path → file names redirecting to
    /// it (same package, different install location).
    pub redirect_targets_map: FxHashMap<PathKey, Vec<RootedFilePath>>,
    /// `redirectFilesByPath` — `filesByPath` for redirect files.
    pub redirect_files_by_path: FxHashMap<PathKey, Rc<RedirectsFile>>,
    /// `contentMapperDiagnostics` — program-level diagnostics reported when a
    /// content mapper fails fatally (once per mapper).
    pub content_mapper_diagnostics: Vec<DiagnosticRef>,
    pub finished_processing: bool,
}

/// `type jsxRuntimeImportSpecifier struct`.
#[derive(Clone)]
pub struct JsxRuntimeImportSpecifier {
    pub module_reference: String,
    /// `specifier *ast.StringLiteralNode` — a synthetic `NodeId` in the
    /// file's arena.
    pub specifier: NodeId,
}

/// `processAllProgramFiles`.
pub fn process_all_program_files(opts: &ProgramOptions) -> (ProcessedFiles, Rc<ResolutionData>) {
    let compiler_options = opts
        .config
        .config
        .compiler_options()
        .cloned()
        .map(Arc::new)
        .unwrap_or_default();
    let root_files = opts.config.config.file_names().to_vec();
    let supported_extensions = tsc_tsoptions::tsconfigparsing::get_supported_extensions(
        &compiler_options,
        opts.config.config.content_mapper_extensions(),
    );
    let supported_extensions_with_json_if_resolve_json_module =
        tsc_tsoptions::tsconfigparsing::get_supported_extensions_with_json_if_resolve_json_module(
            Some(&compiler_options),
            &supported_extensions,
        );
    let max_node_module_js_depth = compiler_options.max_node_module_js_depth.unwrap_or(0);
    let mut loader = FileLoader {
        opts: opts.config.clone(),
        host: opts.hosts.host.clone(),
        tracing: opts.hosts.tracing.clone(),
        resolver: Arc::new(tsc_module::DefaultResolver::new(ResolverOptions {
            host: compiler_resolution_host(opts),
            compiler_options: compiler_options.clone(),
            typings_location: opts.config.typings_location.clone(),
            project_name: opts.config.project_name.clone(),
            extra_extensions: opts.config.config.content_mapper_extensions().to_vec(),
            package_json_cache: None,
        })),
        default_library_path: opts.hosts.host.default_library_path().clone(),
        case_sensitivity: opts.hosts.host.fs().case_sensitivity(),
        files_parser: FilesParser {
            max_depth: max_node_module_js_depth as usize,
            ..Default::default()
        },
        root_tasks: Vec::with_capacity(
            root_files.len() + compiler_options.lib.as_ref().map_or(0, |l| l.len()),
        ),
        supported_extensions,
        supported_extensions_with_json_if_resolve_json_module,
        content_mapper_extensions: opts.config.config.content_mapper_extensions().to_vec(),
        total_file_count: Cell::new(0),
        lib_file_count: Cell::new(0),
        factory: RefCell::new(NodeFactory::default()),
        project_references: RefCell::new(ProjectReferenceFileMapperBuilder {
            mapper: Arc::new(ProjectReferenceFileMapper {
                config: opts.config.config.clone(),
                use_source_of_project_reference: opts.config.can_use_project_reference_source(),
                dts_directories: tsc_collections::SyncSet::new(),
                config_to_project_reference: FxHashMap::default(),
                references_in_config_file: FxHashMap::default(),
                source_to_project_reference: FxHashMap::default(),
                output_dts_to_project_reference: FxHashMap::default(),
                realpath_dts_to_source: tsc_collections::SyncMap::default(),
            }),
            host: compiler_resolution_host(opts),
        }),
        path_for_lib_file_cache: RefCell::new(FxHashMap::default()),
        path_for_lib_file_resolutions: RefCell::new(FxHashMap::default()),
        content_mapper_failures: RefCell::new(FxHashMap::default()),
        content_mapper_init_failed: RefCell::new(HashSet::new()),
        content_mapper_diagnostics: RefCell::new(Vec::new()),
    };
    loader.add_project_reference_tasks();
    // `loader.projectReferences.host` may have been replaced by the
    // dts-faking host during project-reference parsing.
    let resolution_host = loader.project_references.borrow().host.clone();
    let resolver_options = ResolverOptions {
        host: resolution_host,
        compiler_options,
        typings_location: opts.config.typings_location.clone(),
        project_name: opts.config.project_name.clone(),
        extra_extensions: opts.config.config.content_mapper_extensions().to_vec(),
        package_json_cache: None,
    };
    loader.resolver = match &opts.factories.create_module_resolver {
        Some(create) => create(resolver_options),
        None => Arc::new(tsc_module::DefaultResolver::new(resolver_options)),
    };
    let _trace = push(
        loader.tracing.as_ref(),
        tsc_tracing::PHASE_PROGRAM,
        "processRootFiles",
        [(
            "count".to_string(),
            serde_json::Value::from(root_files.len()),
        )]
        .into_iter()
        .collect(),
        false,
    );
    let root_file_count = opts.config.config.file_names().len();
    for index in 0..root_file_count {
        let root_file = opts.config.config.file_names()[index].clone();
        let reference_text = opts
            .config
            .config
            .root_file_name_for_diagnostic(index)
            .to_string();
        loader.add_root_file_task(
            root_file,
            &reference_text,
            None,
            Rc::new(FileIncludeReason {
                kind: FILE_INCLUDE_KIND_ROOT_FILE,
                index,
                ..Default::default()
            }),
        );
    }
    // `len(rootFiles) > 0 && compilerOptions.NoLib.IsFalseOrUnknown()`
    if root_file_count > 0
        && opts
            .config
            .config
            .compiler_options()
            .map(|o| o.no_lib)
            .unwrap_or_default()
            .is_false_or_unknown()
    {
        let options = opts
            .config
            .config
            .compiler_options()
            .cloned()
            .unwrap_or_default();
        if options.lib.is_none() {
            let name = tsc_tsoptions::enummaps::get_default_lib_file_name(&options);
            let lib_file = loader.path_for_lib_file(name);
            let path = lib_file.path.clone();
            loader.add_root_task(
                path,
                Some(lib_file),
                Rc::new(FileIncludeReason {
                    kind: FILE_INCLUDE_KIND_LIB_FILE,
                    is_default_lib: true,
                    ..Default::default()
                }),
            );
        } else {
            for (index, lib) in options.lib.as_ref().unwrap().iter().enumerate() {
                if let Some(name) = tsc_tsoptions::enummaps::get_lib_file_name(lib) {
                    let lib_file = loader.path_for_lib_file(&name);
                    let path = lib_file.path.clone();
                    loader.add_root_task(
                        path,
                        Some(lib_file),
                        Rc::new(FileIncludeReason {
                            kind: FILE_INCLUDE_KIND_LIB_FILE,
                            index,
                            ..Default::default()
                        }),
                    );
                }
                // !!! error on unknown name
            }
        }
    }

    if root_file_count > 0 && !opts.config.skip_module_resolution {
        loader.add_automatic_type_directive_tasks();
    }

    loader.parse_root_tasks();
    let resolution_data = Rc::new(loader.resolver.get_resolution_data().clone());
    (loader.get_processed_files(), resolution_data)
}

fn compiler_resolution_host(opts: &ProgramOptions) -> Arc<CompilerResolutionHost> {
    Arc::new(CompilerResolutionHost {
        host: opts.hosts.host.clone(),
        base_directory: opts.config.config.base_directory().clone(),
    })
}

impl FileLoader {
    /// `(p *fileLoader) toPath`.
    pub fn to_path(&self, file: &RootedPath) -> PathKey {
        self.case_sensitivity.path_key(file)
    }

    /// `(p *fileLoader) addRootTask`.
    fn add_root_task(
        &mut self,
        file_name: RootedFilePath,
        lib_file: Option<Rc<LibFile>>,
        include_reason: Rc<FileIncludeReason>,
    ) {
        let options = self
            .opts
            .config
            .compiler_options()
            .cloned()
            .unwrap_or_default();
        if options.allow_non_ts_extensions == TS_TRUE || file_name.has_extension() {
            self.root_tasks.push(Rc::new(RefCell::new(ParseTask {
                normalized_file_path: file_name.clone(),
                path: self.to_path(&file_name.as_path()),
                lib_file,
                include_reason: Some(include_reason),
                ..Default::default()
            })));
        }
    }

    /// `(p *fileLoader) addRootFileTask`.
    fn add_root_file_task(
        &mut self,
        file_name: RootedFilePath,
        reference_text: &str,
        lib_file: Option<Rc<LibFile>>,
        include_reason: Rc<FileIncludeReason>,
    ) {
        let (resolved_file, resolved_path, diagnostic) =
            self.get_source_file_from_reference(&file_name, reference_text);
        let mut root_task = ParseTask {
            normalized_file_path: resolved_file,
            path: resolved_path,
            lib_file,
            include_reason: Some(include_reason),
            ..Default::default()
        };
        if let Some(diagnostic) = diagnostic {
            root_task.normalized_file_path = file_name.clone();
            root_task.path = self.to_path(&file_name.as_path());
            root_task.failed_lookup = true;
            root_task
                .processing_diagnostics
                .push(ProcessingDiagnostic::ExplainingFileInclude(Box::new(
                    IncludeExplainingDiagnostic {
                        file: PathKey::default(),
                        diagnostic_reason: root_task.include_reason.clone(),
                        message: diagnostic.message,
                        args: diagnostic.args,
                    },
                )));
        }
        self.root_tasks.push(Rc::new(RefCell::new(root_task)));
    }

    /// `(p *fileLoader) addAutomaticTypeDirectiveTasks`.
    fn add_automatic_type_directive_tasks(&mut self) {
        let containing_file_name = self
            .opts
            .config
            .base_directory()
            .resolve_file(tsc_module::INFERRED_TYPES_CONTAINING_FILE);
        self.root_tasks.push(Rc::new(RefCell::new(ParseTask {
            normalized_file_path: containing_file_name.clone(),
            path: self.to_path(&containing_file_name.as_path()),
            is_for_automatic_type_directive: true,
            ..Default::default()
        })));
    }

    /// `(p *fileLoader) resolveAutomaticTypeDirectives`.
    pub(crate) fn resolve_automatic_type_directives(
        &self,
        containing_file_name: &RootedFilePath,
    ) -> (
        Vec<ResolvedRef>,
        ModeAwareCache<ResolvedTypeReferenceDirective>,
        Vec<DiagAndArgs>,
        Vec<ProcessingDiagnostic>,
    ) {
        let options = self
            .opts
            .config
            .compiler_options()
            .cloned()
            .unwrap_or_default();
        let automatic_type_directive_names = tsc_module::get_automatic_type_directive_names(
            &options,
            self.opts.config.base_directory().clone(),
            self.host.fs(),
        );
        let mut to_parse = Vec::new();
        let mut type_resolutions_in_file = ModeAwareCache::default();
        let mut type_resolutions_trace = Vec::new();
        let mut p_diagnostics = Vec::new();
        if !automatic_type_directive_names.is_empty() {
            to_parse.reserve(automatic_type_directive_names.len());
            type_resolutions_in_file.reserve(automatic_type_directive_names.len());
            for name in automatic_type_directive_names {
                // Under node16/nodenext module resolution, load `types`/ata include names as cjs resolution results by passing an `undefined` mode.
                // Under bundler module resolution, this also triggers the "import" condition to be used.
                let resolution_mode = RESOLUTION_MODE_NONE;
                let (resolved, trace) = self.resolver.resolve_type_reference_directive(
                    &name,
                    containing_file_name,
                    resolution_mode,
                    None,
                );
                let trace_done = if self.tracing.is_some() {
                    Some(push(
                        self.tracing.as_ref(),
                        tsc_tracing::PHASE_PROGRAM,
                        "processTypeReferenceDirective",
                        [
                            (
                                "directive".to_string(),
                                serde_json::Value::from(name.clone()),
                            ),
                            (
                                "hasResolved".to_string(),
                                serde_json::Value::from(resolved.is_resolved()),
                            ),
                            (
                                "refKind".to_string(),
                                serde_json::Value::from(
                                    FILE_INCLUDE_KIND_AUTOMATIC_TYPE_DIRECTIVE_FILE.0,
                                ),
                            ),
                        ]
                        .into_iter()
                        .collect(),
                        false,
                    ))
                } else {
                    None
                };
                type_resolutions_in_file.insert(
                    ModeAwareCacheKey {
                        name: name.clone(),
                        mode: resolution_mode,
                    },
                    resolved.clone(),
                );
                type_resolutions_trace.extend(trace);
                if resolved.is_resolved() {
                    to_parse.push(ResolvedRef {
                        file_name: resolved.resolved_file_name.clone(),
                        path: resolved.resolved_path.clone(),
                        increase_depth: resolved.is_external_library_import,
                        elide_on_depth: false,
                        include_reason: Some(Rc::new(FileIncludeReason {
                            kind: FILE_INCLUDE_KIND_AUTOMATIC_TYPE_DIRECTIVE_FILE,
                            automatic_type_directive: Some(Box::new(
                                AutomaticTypeDirectiveFileData {
                                    type_reference: name.clone(),
                                    package_id: resolved.package_id.clone(),
                                },
                            )),
                            ..Default::default()
                        })),
                        package_id: resolved.package_id,
                    });
                } else {
                    p_diagnostics.push(ProcessingDiagnostic::ExplainingFileInclude(Box::new(
                        IncludeExplainingDiagnostic {
                            file: PathKey::default(),
                            diagnostic_reason: Some(Rc::new(FileIncludeReason {
                                kind: FILE_INCLUDE_KIND_AUTOMATIC_TYPE_DIRECTIVE_FILE,
                                automatic_type_directive: Some(Box::new(
                                    AutomaticTypeDirectiveFileData {
                                        type_reference: name.clone(),
                                        ..Default::default()
                                    },
                                )),
                                ..Default::default()
                            })),
                            message: &diagnostics::Cannot_find_type_definition_file_for_0,
                            args: vec![name.clone()],
                        },
                    )));
                }
                if let Some(done) = trace_done {
                    done();
                }
            }
        }
        (
            to_parse,
            type_resolutions_in_file,
            type_resolutions_trace,
            p_diagnostics,
        )
    }

    /// `(p *fileLoader) addProjectReferenceTasks`.
    fn add_project_reference_tasks(&mut self) {
        let project_references = self.opts.config.resolved_project_reference_paths().clone();
        if project_references.is_empty() {
            return;
        }
        let root_tasks = create_project_reference_parse_tasks(&project_references);
        let parser = ProjectReferenceParser {
            tasks_by_file_name: RefCell::new(FxHashMap::default()),
        };
        parser.parse(self, root_tasks);
    }

    /// `(p *fileLoader) sortLibs` — stable order in `files` mirrors Go's
    /// `sort.SliceStable`, which only shuffles lib files among themselves.
    pub(crate) fn sort_libs(&self, lib_files: &mut Vec<LoadedSourceFile>) {
        lib_files.sort_by_key(|f| self.get_default_lib_file_priority(f));
    }

    /// `(p *fileLoader) getDefaultLibFilePriority`.
    fn get_default_lib_file_priority(&self, a: &LoadedSourceFile) -> i32 {
        let file_name = a.file_name();
        if let Some(relative) = file_name.relative_to(&self.default_library_path) {
            if !relative.as_string().is_empty() {
                let basename = relative.base_name();
                if basename == "lib.d.ts" || basename == "lib.es6.d.ts" {
                    return 0;
                }
                let name = basename
                    .trim_start_matches("lib.")
                    .trim_end_matches(".d.ts");
                if let Some(index) = tsc_tsoptions::enummaps::libs()
                    .iter()
                    .position(|l| l == name)
                {
                    return index as i32 + 1;
                }
            }
        }
        tsc_tsoptions::enummaps::libs().len() as i32 + 2
    }

    /// `(p *fileLoader) loadSourceFileMetaData`.
    pub fn load_source_file_meta_data(&self, file_name: &RootedFilePath) -> SourceFileMetaData {
        if self.opts.skip_module_resolution {
            return SourceFileMetaData {
                implied_node_format: tsc_ast::get_implied_node_format_for_file(file_name, ""),
                ..Default::default()
            };
        }

        let resolver = self
            .resolver
            .get_resolution_data()
            .new_resolver(self.project_references.borrow().host.clone());
        let package_json_scope = resolver.get_package_scope_for_path(&file_name.directory());
        let options = self
            .opts
            .config
            .compiler_options()
            .cloned()
            .unwrap_or_default();
        let module_resolution_kind = options.get_module_resolution_kind();

        let mut package_json_type = String::new();
        let mut package_json_directory = RootedDirectoryPath::default();
        if let Some(scope) = &package_json_scope {
            if scope.exists() {
                package_json_directory = scope.package_directory.as_directory_path().clone();
                if let Some(contents) = &scope.contents {
                    if let Some(value) = contents.type_.get_value() {
                        if !file_name.extension_is_one_of(&[
                            tsc_tspath::EXTENSION_MTS,
                            tsc_tspath::EXTENSION_CTS,
                            tsc_tspath::EXTENSION_MJS,
                            tsc_tspath::EXTENSION_CJS,
                        ]) && (ModuleResolutionKind::Node16..=ModuleResolutionKind::NodeNext)
                            .contains(&module_resolution_kind)
                            || file_name.contains_lowercase_directory_sequence("/node_modules/")
                        {
                            package_json_type = value.clone();
                        }
                    }
                }
            }
        }

        let implied_node_format =
            tsc_ast::get_implied_node_format_for_file(file_name, &package_json_type);
        SourceFileMetaData {
            package_json_type,
            package_json_directory,
            implied_node_format,
        }
    }

    /// `(p *fileLoader) parseSourceFile` — returns the canonical file plus
    /// its content-mapped supplementals (which `load` iterates as
    /// `file.SupplementalSourceFiles()`).
    pub fn parse_source_file(&self, t: &ParseTask) -> Option<LoadedFile> {
        let _trace = push(
            self.tracing.as_ref(),
            tsc_tracing::PHASE_PARSE,
            "createSourceFile",
            [(
                "path".to_string(),
                serde_json::Value::from(t.normalized_file_path.as_string().to_string()),
            )]
            .into_iter()
            .collect(),
            true,
        );
        let has_file_name =
            tsc_ast::new_has_file_name(t.normalized_file_path.clone(), t.path.clone());
        let options = self
            .project_references
            .borrow()
            .get_compiler_options_for_file(&has_file_name);
        let parse_options = SourceFileParseOptions {
            file_name: t.normalized_file_path.clone(),
            path_key: t.path.clone(),
            external_module_indicator_options:
                tsc_ast::parseoptions::get_external_module_indicator_options(
                    &t.normalized_file_path,
                    &options,
                    &t.metadata,
                ),
        };
        if t.normalized_file_path.extension_is_one_of(
            &self
                .content_mapper_extensions
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
        ) {
            return self.parse_content_mapped_file(&parse_options);
        }
        self.host
            .get_source_file(&parse_options)
            .map(|f| LoadedFile {
                canonical: f.into(),
                supplemental: Vec::new(),
            })
    }

    /// `(p *fileLoader) parseContentMappedFile`.
    fn parse_content_mapped_file(&self, opts: &SourceFileParseOptions) -> Option<LoadedFile> {
        let mapper = self
            .opts
            .config
            .get_content_mapper_for_file_name(&opts.file_name)?
            .clone();
        let label = mapper.diagnostic_name();
        let transform_identity = self.get_content_mapper_transform_identity(&mapper);
        if self.content_mapper_unavailable(&mapper) {
            // The mapper failed initialization or exceeded its failure budget; add the file empty without re-reporting.
            return Some(self.empty_content_mapped_file(
                opts,
                &mapper.identity(),
                &transform_identity,
            ));
        }
        match self.host.get_content_mapped_source_files(opts, &mapper) {
            Err(err) => {
                let source_file =
                    self.empty_content_mapped_file(opts, &mapper.identity(), &transform_identity);
                if err
                    .as_transform_error()
                    .is_some_and(|te| te.kind == TransformErrorKind::Initialize)
                {
                    self.record_content_mapper_initialization_failure(&mapper, &label, &err);
                    return Some(source_file);
                }
                if self.record_content_mapper_failure(&mapper, &label) {
                    let diagnostic = if let Some(problem) = err.as_mapping_error() {
                        content_mapper_mapping_diagnostic(&source_file.canonical, &label, problem)
                    } else {
                        content_mapper_transform_diagnostic(&source_file.canonical, &label, &err)
                    };
                    let mut nodes = source_file.canonical.nodes.borrow_mut();
                    let file = source_file.canonical.file;
                    let mut diags = nodes[file].as_source_file().diagnostics().to_vec();
                    diags.push(diagnostic);
                    nodes[file].as_source_file_mut().set_diagnostics(diags);
                }
                Some(source_file)
            }
            Ok(files) => Some(LoadedFile {
                canonical: files.canonical.into(),
                supplemental: files.supplemental.into_iter().map(Into::into).collect(),
            }),
        }
    }

    /// `(p *fileLoader) getContentMapperTransformIdentity`.
    fn get_content_mapper_transform_identity(&self, mapper: &Arc<Mapper>) -> String {
        if let Some(project) = self.host.content_mapper_project() {
            if let Ok(identity) = project.identity(mapper) {
                return identity;
            }
        }
        let options = self
            .opts
            .config
            .compiler_options()
            .cloned()
            .unwrap_or_default();
        // Go: `fmt.Sprintf("%x", mapper.TransformIdentity(...).Bytes())`.
        mapper
            .transform_identity(Some(&options))
            .bytes()
            .iter()
            .map(|b| format!("{b:02x}"))
            .collect()
    }

    /// `(p *fileLoader) emptyContentMappedFile`.
    fn empty_content_mapped_file(
        &self,
        opts: &SourceFileParseOptions,
        mapper_identity: &str,
        transform_identity: &str,
    ) -> LoadedFile {
        let content = self
            .host
            .fs()
            .read_file(&opts.file_name)
            .unwrap_or_default();
        let (file, mut nodes) = tsc_parser::parse_source_file(opts.clone(), "", CoreScriptKind::Ts);
        nodes[file].as_source_file_mut().set_content_mapper_info(
            tsc_ast::ContentMapperSourceFileInfo {
                content_mapper: mapper_identity.to_string(),
                transform_identity: transform_identity.to_string(),
                parse_options: opts.clone(),
                virtual_file_name: opts.file_name.append_suffix(tsc_tspath::EXTENSION_TS),
                original_text: content,
                ..Default::default()
            },
        );
        LoadedFile {
            canonical: LoadedSourceFile {
                file,
                nodes: Rc::new(RefCell::new(nodes)),
            },
            supplemental: Vec::new(),
        }
    }

    /// `contentMapperUnavailable` — whether the mapper failed initialization
    /// or exceeded its failure budget.
    fn content_mapper_unavailable(&self, mapper: &Arc<Mapper>) -> bool {
        let key = Arc::as_ptr(mapper) as usize;
        self.content_mapper_init_failed.borrow().contains(&key)
            || self
                .content_mapper_failures
                .borrow()
                .get(&key)
                .copied()
                .unwrap_or(0)
                >= MAX_CONTENT_MAPPER_FAILURES
    }

    /// `(p *fileLoader) recordContentMapperInitializationFailure`.
    fn record_content_mapper_initialization_failure(
        &self,
        mapper: &Arc<Mapper>,
        label: &str,
        err: &ContentMapperError,
    ) {
        let key = Arc::as_ptr(mapper) as usize;
        if !self.content_mapper_init_failed.borrow_mut().insert(key) {
            return;
        }
        self.content_mapper_diagnostics
            .borrow_mut()
            .push(content_mapper_initialization_diagnostic(label, err));
    }

    /// `(p *fileLoader) recordContentMapperFailure` — returns whether the
    /// failure should be reported for this file.
    fn record_content_mapper_failure(&self, mapper: &Arc<Mapper>, label: &str) -> bool {
        let key = Arc::as_ptr(mapper) as usize;
        let mut failures = self.content_mapper_failures.borrow_mut();
        let count = failures.entry(key).or_insert(0);
        if *count >= MAX_CONTENT_MAPPER_FAILURES {
            return false;
        }
        *count += 1;
        if *count >= MAX_CONTENT_MAPPER_FAILURES {
            drop(failures);
            self.content_mapper_diagnostics.borrow_mut().push(
                tsc_ast::diagnostic::new_compiler_diagnostic(
                    &diagnostics::The_content_mapper_0_failed_1_times_and_will_not_be_used,
                    &[
                        tsc_tsoptions::value::Value::Str(label.to_string()),
                        tsc_tsoptions::value::Value::Int(MAX_CONTENT_MAPPER_FAILURES as i64),
                    ],
                ),
            );
        }
        true
    }

    /// `(p *fileLoader) isSupportedExtension`.
    pub fn is_supported_extension(&self, canonical_file_name: &PathKey) -> bool {
        self.supported_extensions_with_json_if_resolve_json_module
            .iter()
            .any(|group| {
                canonical_file_name
                    .extension_is_one_of(&group.iter().map(String::as_str).collect::<Vec<_>>())
            })
    }

    /// `(p *fileLoader) getSourceFileFromReference`.
    fn get_source_file_from_reference(
        &self,
        file_name: &RootedFilePath,
        reference_text: &str,
    ) -> (
        RootedFilePath,
        PathKey,
        Option<SourceFileFromReferenceDiagnostic>,
    ) {
        let options = self
            .opts
            .config
            .compiler_options()
            .cloned()
            .unwrap_or_default();
        let allow_non_ts_extensions = options.allow_non_ts_extensions == TS_TRUE;
        let diagnostic_file_name = tsc_tspath::normalize_slashes(reference_text).to_string();

        if file_name.has_extension() {
            let canonical_file_name = self.to_path(&file_name.as_path());
            if !allow_non_ts_extensions && !self.is_supported_extension(&canonical_file_name) {
                if canonical_file_name.has_js_file_extension() {
                    return (
                        RootedFilePath::default(),
                        PathKey::default(),
                        Some(SourceFileFromReferenceDiagnostic {
                            message: &diagnostics::File_0_is_a_JavaScript_file_Did_you_mean_to_enable_the_allowJs_option,
                            args: vec![diagnostic_file_name],
                        }),
                    );
                }
                return (
                    RootedFilePath::default(),
                    PathKey::default(),
                    Some(SourceFileFromReferenceDiagnostic {
                        message: &diagnostics::File_0_has_an_unsupported_extension_The_only_supported_extensions_are_1,
                        args: vec![
                            diagnostic_file_name,
                            format!(
                                "'{}'",
                                self.supported_extensions
                                    .iter()
                                    .flatten()
                                    .cloned()
                                    .collect::<Vec<_>>()
                                    .join("', '")
                            ),
                        ],
                    }),
                );
            }

            if !self.host.fs().file_exists(file_name) {
                return (
                    RootedFilePath::default(),
                    PathKey::default(),
                    Some(SourceFileFromReferenceDiagnostic {
                        message: &diagnostics::File_0_not_found,
                        args: vec![diagnostic_file_name],
                    }),
                );
            }
            return (file_name.clone(), canonical_file_name, None);
        }

        if allow_non_ts_extensions && self.host.fs().file_exists(file_name) {
            return (file_name.clone(), self.to_path(&file_name.as_path()), None);
        }

        if allow_non_ts_extensions {
            return (
                RootedFilePath::default(),
                PathKey::default(),
                Some(SourceFileFromReferenceDiagnostic {
                    message: &diagnostics::File_0_not_found,
                    args: vec![diagnostic_file_name],
                }),
            );
        }

        for ext in &self.supported_extensions[0] {
            let candidate = file_name.append_suffix(ext);
            if self.host.fs().file_exists(&candidate) {
                return (candidate.clone(), self.to_path(&candidate.as_path()), None);
            }
        }

        (
            RootedFilePath::default(),
            PathKey::default(),
            Some(SourceFileFromReferenceDiagnostic {
                message: &diagnostics::Could_not_resolve_the_path_0_with_the_extensions_Colon_1,
                args: vec![
                    diagnostic_file_name,
                    format!(
                        "'{}'",
                        self.supported_extensions
                            .iter()
                            .flatten()
                            .cloned()
                            .collect::<Vec<_>>()
                            .join("', '")
                    ),
                ],
            }),
        )
    }

    /// `(p *fileLoader) resolveTripleslashPathReference`.
    pub fn resolve_tripleslash_path_reference(
        &self,
        module_name: &str,
        containing_file: &RootedFilePath,
        index: usize,
    ) -> (Option<ResolvedRef>, Option<ProcessingDiagnostic>) {
        let normalized_file_name = containing_file.directory().resolve_file(module_name);
        let containing_path = self.to_path(&containing_file.as_path());
        let include_reason = Rc::new(FileIncludeReason {
            kind: FILE_INCLUDE_KIND_REFERENCE_FILE,
            referenced_file: Some(Box::new(ReferencedFileData {
                file: containing_path.clone(),
                index: index as isize,
                synthetic: None,
            })),
            ..Default::default()
        });

        let (resolved_file_name, resolved_path, diagnostic) =
            self.get_source_file_from_reference(&normalized_file_name, module_name);
        if let Some(diagnostic) = diagnostic {
            return (
                None,
                Some(ProcessingDiagnostic::ExplainingFileInclude(Box::new(
                    IncludeExplainingDiagnostic {
                        file: PathKey::default(),
                        diagnostic_reason: Some(include_reason),
                        message: diagnostic.message,
                        args: diagnostic.args,
                    },
                ))),
            );
        }
        if containing_path == resolved_path {
            return (
                None,
                Some(ProcessingDiagnostic::ExplainingFileInclude(Box::new(
                    IncludeExplainingDiagnostic {
                        file: PathKey::default(),
                        diagnostic_reason: Some(include_reason),
                        message: &diagnostics::A_file_cannot_have_a_reference_to_itself,
                        args: vec![],
                    },
                ))),
            );
        }

        (
            Some(ResolvedRef {
                file_name: resolved_file_name,
                path: resolved_path,
                include_reason: Some(include_reason),
                ..Default::default()
            }),
            None,
        )
    }

    /// `(p *fileLoader) resolveTypeReferenceDirectives`.
    pub fn resolve_type_reference_directives(&self, t: &RefCell<ParseTask>) {
        let (file, nodes) = {
            let t = t.borrow();
            match &t.file {
                Some(f) => (f.file, f.nodes.clone()),
                None => return,
            }
        };
        let nodes = nodes.borrow();
        let sf = nodes[file].as_source_file();
        if sf.type_reference_directives.is_empty() {
            return;
        }
        let _trace = push(
            self.tracing.as_ref(),
            tsc_tracing::PHASE_PROGRAM,
            "resolveTypeReferenceDirectiveNamesWorker",
            [(
                "containingFileName".to_string(),
                serde_json::Value::from(sf.file_name().as_string().to_string()),
            )]
            .into_iter()
            .collect(),
            false,
        );
        let meta = t.borrow().metadata.clone();
        let type_reference_directives: Vec<FileReference> = sf.type_reference_directives.to_vec();
        let t_path = t.borrow().path.clone();
        let file_has_file_name =
            tsc_ast::new_has_file_name(sf.file_name().clone(), sf.path_key().clone());
        drop(nodes);

        let mut type_resolutions_in_file = ModeAwareCache::with_capacity_and_hasher(
            type_reference_directives.len(),
            Default::default(),
        );
        let mut type_resolutions_trace: Vec<DiagAndArgs> = Vec::new();
        for (index, ref_) in type_reference_directives.iter().enumerate() {
            let (redirect, file_name) = self
                .project_references
                .borrow()
                .get_redirect_for_resolution(&file_has_file_name);
            let redirect_adapter = redirect.as_ref().map(|r| as_resolved_project_reference(r));
            let options_for_file = tsc_module::get_compiler_options_with_redirect(
                &compiler_options_arc(&self.opts.config),
                redirect_adapter
                    .as_ref()
                    .map(|r| r as &dyn tsc_module::ResolvedProjectReference),
            );
            let resolution_mode = get_mode_for_type_reference_directive_in_file(
                ref_,
                file_has_file_name.file_name(),
                &meta,
                &options_for_file,
            );
            let (resolved, trace) = self.resolver.resolve_type_reference_directive(
                &ref_.file_name,
                &file_name,
                resolution_mode,
                redirect_adapter
                    .as_ref()
                    .map(|r| r as &dyn tsc_module::ResolvedProjectReference),
            );
            let trace_done = if self.tracing.is_some() {
                Some(push(
                    self.tracing.as_ref(),
                    tsc_tracing::PHASE_PROGRAM,
                    "processTypeReferenceDirective",
                    [
                        (
                            "directive".to_string(),
                            serde_json::Value::from(ref_.file_name.clone()),
                        ),
                        (
                            "hasResolved".to_string(),
                            serde_json::Value::from(resolved.is_resolved()),
                        ),
                        (
                            "refKind".to_string(),
                            serde_json::Value::from(FILE_INCLUDE_KIND_TYPE_REFERENCE_DIRECTIVE.0),
                        ),
                        (
                            "refPath".to_string(),
                            serde_json::Value::from(t_path.as_string().to_string()),
                        ),
                    ]
                    .into_iter()
                    .collect(),
                    false,
                ))
            } else {
                None
            };
            type_resolutions_in_file.insert(
                ModeAwareCacheKey {
                    name: ref_.file_name.clone(),
                    mode: resolution_mode,
                },
                resolved.clone(),
            );
            let include_reason = Rc::new(FileIncludeReason {
                kind: FILE_INCLUDE_KIND_TYPE_REFERENCE_DIRECTIVE,
                referenced_file: Some(Box::new(ReferencedFileData {
                    file: t_path.clone(),
                    index: index as isize,
                    synthetic: None,
                })),
                ..Default::default()
            });
            type_resolutions_trace.extend(trace);

            if resolved.is_resolved() {
                ParseTask::add_sub_task(
                    t,
                    ResolvedRef {
                        file_name: resolved.resolved_file_name.clone(),
                        path: resolved.resolved_path.clone(),
                        increase_depth: resolved.is_external_library_import,
                        elide_on_depth: false,
                        include_reason: Some(include_reason),
                        package_id: resolved.package_id,
                    },
                    None,
                );
            } else {
                t.borrow_mut()
                    .processing_diagnostics
                    .push(ProcessingDiagnostic::UnknownReference(include_reason));
            }
            if let Some(done) = trace_done {
                done();
            }
        }

        let mut t = t.borrow_mut();
        t.type_resolutions_in_file = type_resolutions_in_file;
        t.type_resolutions_trace = type_resolutions_trace;
    }

    /// `(p *fileLoader) resolveImportsAndModuleAugmentations`.
    pub fn resolve_imports_and_module_augmentations(&self, t: &RefCell<ParseTask>) {
        let (file, nodes_rc) = {
            let t = t.borrow();
            match &t.file {
                Some(f) => (f.file, f.nodes.clone()),
                None => return,
            }
        };
        let _trace = push(
            self.tracing.as_ref(),
            tsc_tracing::PHASE_PROGRAM,
            "resolveModuleNamesWorker",
            [(
                "containingFileName".to_string(),
                serde_json::Value::from(
                    nodes_rc.borrow()[file]
                        .as_source_file()
                        .file_name()
                        .as_string()
                        .to_string(),
                ),
            )]
            .into_iter()
            .collect(),
            false,
        );
        let meta = t.borrow().metadata.clone();
        let t_path = t.borrow().path.clone();

        let (
            imports,
            module_augmentations,
            is_java_script_file,
            is_external_module_file,
            is_declaration_file,
            script_kind,
            file_name_of_file,
            path_key_of_file,
        ) = {
            let nodes = nodes_rc.borrow();
            let sf = nodes[file].as_source_file();
            (
                sf.imports().to_vec(),
                sf.module_augmentations.to_vec(),
                tsc_ast::is_source_file_js(sf),
                tsc_ast::is_external_module(sf),
                sf.is_declaration_file,
                sf.script_kind,
                sf.file_name().clone(),
                sf.path_key().clone(),
            )
        };

        let mut module_names: Vec<NodeId> =
            Vec::with_capacity(imports.len() + module_augmentations.len() + 2);

        let file_has_file_name =
            tsc_ast::new_has_file_name(file_name_of_file.clone(), path_key_of_file);
        let (redirect, file_name) = self
            .project_references
            .borrow()
            .get_redirect_for_resolution(&file_has_file_name);
        let redirect_adapter = redirect.as_ref().map(|r| as_resolved_project_reference(r));
        let options_for_file = tsc_module::get_compiler_options_with_redirect(
            &compiler_options_arc(&self.opts.config),
            redirect_adapter
                .as_ref()
                .map(|r| r as &dyn tsc_module::ResolvedProjectReference),
        );
        if is_java_script_file
            || (!is_declaration_file
                && (options_for_file.get_isolated_modules() || is_external_module_file))
        {
            if options_for_file.import_helpers == TS_TRUE {
                let specifier = self.create_synthetic_import(
                    EXTERNAL_HELPERS_MODULE_NAME_TEXT,
                    file,
                    &nodes_rc,
                );
                module_names.push(specifier);
                t.borrow_mut().import_helpers_import_specifier = Some(specifier);
            }
        }

        if is_java_script_file || script_kind == CoreScriptKind::Tsx {
            let nodes = nodes_rc.borrow();
            let jsx_import = tsc_ast::get_jsx_runtime_import(
                &tsc_ast::get_jsx_implicit_import_base(
                    &options_for_file,
                    Some(nodes[file].as_source_file()),
                ),
                &options_for_file,
            );
            drop(nodes);
            if !jsx_import.is_empty() {
                let specifier = self.create_synthetic_import(&jsx_import, file, &nodes_rc);
                module_names.push(specifier);
                t.borrow_mut().jsx_runtime_import_specifier = Some(JsxRuntimeImportSpecifier {
                    module_reference: jsx_import,
                    specifier,
                });
            }
        }

        let imports_start = module_names.len();

        module_names.extend(imports.iter().copied());
        for &imp in &module_augmentations {
            let nodes = nodes_rc.borrow();
            if nodes[imp].kind == tsc_ast::Kind::StringLiteral {
                module_names.push(imp);
            }
            // Do nothing if it's an Identifier; we don't need to do module resolution for `declare global`.
        }

        if self.opts.skip_module_resolution {
            return;
        }

        if !module_names.is_empty() {
            let mut resolutions_in_file =
                ModeAwareCache::with_capacity_and_hasher(module_names.len(), Default::default());
            let mut resolutions_trace: Vec<DiagAndArgs> = Vec::new();

            for (index, &entry) in module_names.iter().enumerate() {
                let (module_name, is_source_phase) = {
                    let nodes = nodes_rc.borrow();
                    let text = nodes[entry].text(&nodes[..]).into_owned();
                    let phase = nodes[entry]
                        .parent
                        .is_some_and(|p| tsc_ast::is_source_phase_import(&nodes[p], &nodes[..]));
                    (text, phase)
                };
                if module_name.is_empty() || is_source_phase {
                    continue;
                }

                let mode = get_mode_for_usage_location(
                    &file_name_of_file,
                    &meta,
                    entry,
                    &nodes_rc.borrow()[..],
                    Some(&options_for_file),
                );
                let (resolved_module, trace) = self.resolver.resolve_module_name(
                    &module_name,
                    &file_name,
                    mode,
                    redirect_adapter
                        .as_ref()
                        .map(|r| r as &dyn tsc_module::ResolvedProjectReference),
                );
                let resolved_module = resolved_module.unwrap_or_default();
                resolutions_in_file.insert(
                    ModeAwareCacheKey {
                        name: module_name.clone(),
                        mode,
                    },
                    Some(resolved_module.clone()),
                );
                resolutions_trace.extend(trace);

                if !resolved_module.is_resolved() {
                    continue;
                }

                let resolved_file_name = resolved_module.resolved_file_name.clone();
                let is_from_node_modules_search = resolved_module.is_external_library_import;
                // Don't treat redirected files as JS files.
                let is_js_file = !resolved_module.resolved_using_extra_extensions
                    && !resolved_file_name
                        .extension_is_one_of(&tsc_tspath::SUPPORTED_TS_EXTENSIONS_WITH_JSON_FLAT)
                    && self
                        .project_references
                        .borrow()
                        .get_redirect_parsed_command_line_for_resolution(
                            &tsc_ast::new_has_file_name(
                                resolved_file_name.clone(),
                                resolved_module.resolved_path.clone(),
                            ),
                        )
                        .is_none();
                let is_js_file_from_node_modules = is_from_node_modules_search
                    && is_js_file
                    && resolved_file_name.contains_lowercase_directory_sequence("/node_modules/");

                // add file to program only if:
                // - resolution was successful
                // - noResolve is falsy
                // - module name comes from the list of imports
                // - it's not a top level JavaScript module that exceeded the search max

                let import_index = index as isize - imports_start as isize;

                let should_add_file = {
                    let nodes = nodes_rc.borrow();
                    let file_sf = nodes[file].as_source_file();
                    !module_name.is_empty()
                        && tsc_module::get_resolution_diagnostic(
                            &options_for_file,
                            &resolved_module,
                            file_sf,
                        )
                        .is_none()
                        && options_for_file.no_resolve != TS_TRUE
                        && !(is_js_file && !options_for_file.get_allow_js())
                        && (import_index < 0
                            || ((import_index as usize) < imports.len()
                                && (tsc_ast::is_in_js_file(
                                    Some(imports[import_index as usize]),
                                    &nodes[..],
                                ) || !nodes[imports[import_index as usize]]
                                    .flags
                                    .intersects(tsc_ast::NodeFlags::JSDOC))))
                };

                if should_add_file {
                    ParseTask::add_sub_task(
                        t,
                        ResolvedRef {
                            file_name: resolved_file_name.clone(),
                            path: resolved_module.resolved_path.clone(),
                            increase_depth: resolved_module.is_external_library_import,
                            elide_on_depth: is_js_file_from_node_modules,
                            include_reason: Some(Rc::new(FileIncludeReason {
                                kind: FILE_INCLUDE_KIND_IMPORT,
                                referenced_file: Some(Box::new(ReferencedFileData {
                                    file: t_path.clone(),
                                    index: import_index,
                                    synthetic: if import_index < 0 { Some(entry) } else { None },
                                })),
                                ..Default::default()
                            })),
                            package_id: resolved_module.package_id,
                        },
                        None,
                    );
                }
            }

            let mut t = t.borrow_mut();
            t.resolutions_in_file = resolutions_in_file;
            t.resolutions_trace = resolutions_trace;
        }
    }

    /// `(p *fileLoader) createSyntheticImport` — mints a synthetic import
    /// specifier in `file`'s arena (the `nodes` handle).
    fn create_synthetic_import(
        &self,
        text: &str,
        file: NodeId,
        nodes: &Rc<RefCell<Vec<Node>>>,
    ) -> NodeId {
        let mut nodes = nodes.borrow_mut();
        let mut factory = self.factory.borrow_mut();
        factory.set_file_index(file.file_index());
        let external_helpers_module_reference =
            factory.new_string_literal(&mut nodes, text, tsc_ast::TokenFlags::NONE);
        let import_decl = factory.new_import_declaration(
            &mut nodes,
            None,
            None,
            Some(external_helpers_module_reference),
            None,
        );
        nodes[external_helpers_module_reference].parent = Some(import_decl);
        nodes[import_decl].parent = Some(file);
        external_helpers_module_reference
    }

    /// `(p *fileLoader) pathForLibFile`.
    pub fn path_for_lib_file(&self, name: &str) -> Rc<LibFile> {
        if let Some(cached) = self.path_for_lib_file_cache.borrow().get(name) {
            return cached.clone();
        }

        let mut path = self.default_library_path.resolve_file(name);
        let mut path_key = self.to_path(&path.as_path());
        let mut replaced = false;
        let options = self
            .opts
            .config
            .compiler_options()
            .cloned()
            .unwrap_or_default();
        if !self.opts.skip_module_resolution
            && options.lib_replacement == TS_TRUE
            && name != "lib.d.ts"
        {
            let library_name = get_library_name_from_lib_file_name(name);
            let resolve_from =
                get_inferred_library_name_resolve_from(self.opts.config.base_directory(), name);
            let (resolution, trace) = self.resolve_library(&library_name, &resolve_from);
            if let Some(resolution) = &resolution {
                if resolution.is_resolved() {
                    path = resolution.resolved_file_name.clone();
                    path_key = resolution.resolved_path.clone();
                    replaced = true;
                }
            }
            self.path_for_lib_file_resolutions
                .borrow_mut()
                .entry(self.to_path(&resolve_from.as_path()))
                .or_insert_with(|| {
                    Rc::new(LibResolution {
                        library_name,
                        resolution,
                        trace,
                    })
                });
        }

        let mut cache = self.path_for_lib_file_cache.borrow_mut();
        cache
            .entry(name.to_string())
            .or_insert_with(|| {
                Rc::new(LibFile {
                    name: name.to_string(),
                    path,
                    path_key,
                    replaced,
                })
            })
            .clone()
    }

    /// `(p *fileLoader) resolveLibrary`.
    fn resolve_library(
        &self,
        library_name: &str,
        resolve_from: &RootedFilePath,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>) {
        let _trace = push(
            self.tracing.as_ref(),
            tsc_tracing::PHASE_PROGRAM,
            "resolveLibrary",
            [(
                "resolveFrom".to_string(),
                serde_json::Value::from(resolve_from.as_string().to_string()),
            )]
            .into_iter()
            .collect(),
            false,
        );
        // `core.ModuleKindCommonJS` — a `ResolutionMode` alias.
        self.resolver
            .resolve_module_name(library_name, resolve_from, ModuleKind::CommonJS, None)
    }

    /// `(filesParser) parse` — runs the load loop over `rootTasks`
    /// (`loader.filesParser.parse(loader, loader.rootTasks)`). Go keeps
    /// `rootTasks` on the loader for `getProcessedFiles`, so the `Rc` list
    /// is cloned, not consumed.
    fn parse_root_tasks(&mut self) {
        let tasks = self.root_tasks.clone();
        self.files_parser.parse(self, tasks, 0);
    }

    /// `(filesParser) getProcessedFiles`.
    fn get_processed_files(&mut self) -> ProcessedFiles {
        self.files_parser.get_processed_files(self)
    }
}

const EXTERNAL_HELPERS_MODULE_NAME_TEXT: &str = "tslib"; // TODO(jakebailey): dedupe

/// `getLibraryNameFromLibFileName`.
fn get_library_name_from_lib_file_name(lib_file_name: &str) -> String {
    // Support resolving to lib.dom.d.ts -> @typescript/lib-dom, and
    //                      lib.dom.iterable.d.ts -> @typescript/lib-dom/iterable
    //                      lib.es2015.symbol.wellknown.d.ts -> @typescript/lib-es2015/symbol-wellknown
    let components: Vec<&str> = lib_file_name.split('.').collect();
    let mut path = String::from("@typescript/lib-");
    if components.len() > 1 {
        path.push_str(components[1]);
    }
    let mut i = 2;
    while i < components.len() && !components[i].is_empty() && components[i] != "d" {
        if i == 2 {
            path.push('/');
        } else {
            path.push('-');
        }
        path.push_str(components[i]);
        i += 1;
    }
    path
}

/// `getInferredLibraryNameResolveFrom`.
fn get_inferred_library_name_resolve_from(
    base_directory: &RootedDirectoryPath,
    lib_file_name: &str,
) -> RootedFilePath {
    base_directory.resolve_file(&format!("__lib_node_modules_lookup_{lib_file_name}__.ts"))
}

/// `getModeForTypeReferenceDirectiveInFile` (fileloader.go).
pub fn get_mode_for_type_reference_directive_in_file(
    ref_: &FileReference,
    file_name: &RootedFilePath,
    meta: &SourceFileMetaData,
    options: &CompilerOptions,
) -> ResolutionMode {
    if ref_.resolution_mode != RESOLUTION_MODE_NONE {
        ref_.resolution_mode
    } else {
        get_default_resolution_mode_for_file(file_name, meta, options)
    }
}

/// `getDefaultResolutionModeForFile` (fileloader.go).
pub fn get_default_resolution_mode_for_file(
    file_name: &RootedFilePath,
    meta: &SourceFileMetaData,
    options: &CompilerOptions,
) -> ResolutionMode {
    if import_syntax_affects_module_resolution(options) {
        tsc_ast::get_implied_node_format_for_emit_worker(
            file_name,
            options.get_emit_module_kind(),
            meta,
        )
    } else {
        RESOLUTION_MODE_NONE
    }
}

/// `getModeForUsageLocation` (fileloader.go).
pub fn get_mode_for_usage_location(
    file_name: &RootedFilePath,
    meta: &SourceFileMetaData,
    usage: NodeId,
    nodes: &[Node],
    options: Option<&CompilerOptions>,
) -> ResolutionMode {
    let usage_node = &nodes[usage];
    let parent = usage_node.parent;
    if let Some(parent_id) = parent {
        let parent_node = &nodes[parent_id];
        if tsc_ast::is_import_declaration(parent_node)
            || parent_node.kind == tsc_ast::Kind::JSImportDeclaration
            || tsc_ast::is_export_declaration(parent_node)
            || parent_node.kind == tsc_ast::Kind::JSDocImportTag
        {
            let is_type_only = tsc_ast::is_exclusively_type_only_import_or_export(parent_id, nodes);
            if is_type_only {
                let attributes = match parent_node.kind {
                    tsc_ast::Kind::ImportDeclaration | tsc_ast::Kind::JSImportDeclaration => {
                        parent_node.as_import_declaration().attributes
                    }
                    tsc_ast::Kind::ExportDeclaration => {
                        parent_node.as_export_declaration().attributes
                    }
                    tsc_ast::Kind::JSDocImportTag => parent_node.as_js_doc_import_tag().attributes,
                    _ => None,
                };
                let (override_mode, ok) =
                    tsc_ast::import_attributes_resolution_mode_override(attributes, None, nodes);
                if ok {
                    return override_mode;
                }
            }
        }
        if tsc_ast::is_literal_type_node(parent_node)
            && parent_node
                .parent
                .is_some_and(|pp| tsc_ast::is_import_type_node(&nodes[pp]))
        {
            let import_type = parent_node.parent.unwrap();
            let attributes = nodes[import_type].as_import_type_node().attributes;
            let (override_mode, ok) =
                tsc_ast::import_attributes_resolution_mode_override(attributes, None, nodes);
            if ok {
                return override_mode;
            }
        }
    }

    if let Some(options) = options {
        if import_syntax_affects_module_resolution(options) {
            return get_emit_syntax_for_usage_location_worker(
                file_name, meta, usage, nodes, options,
            );
        }
    }

    RESOLUTION_MODE_NONE
}

/// `importSyntaxAffectsModuleResolution`.
fn import_syntax_affects_module_resolution(options: &CompilerOptions) -> bool {
    let module_resolution = options.get_module_resolution_kind();
    (ModuleResolutionKind::Node16..=ModuleResolutionKind::NodeNext).contains(&module_resolution)
        || options.get_resolve_package_json_exports()
        || options.get_resolve_package_json_imports()
}

/// `getEmitSyntaxForUsageLocationWorker` (fileloader.go).
pub fn get_emit_syntax_for_usage_location_worker(
    file_name: &RootedFilePath,
    meta: &SourceFileMetaData,
    usage: NodeId,
    nodes: &[Node],
    options: &CompilerOptions,
) -> ResolutionMode {
    let parent = nodes[usage].parent;
    if let Some(parent_id) = parent {
        let parent_node = &nodes[parent_id];
        if tsc_ast::is_require_call(parent_node, false, nodes)
            || (tsc_ast::is_external_module_reference(parent_node)
                && parent_node
                    .parent
                    .is_some_and(|pp| tsc_ast::is_import_equals_declaration(&nodes[pp])))
        {
            return ModuleKind::CommonJS;
        }
    }
    let file_emit_mode = tsc_ast::get_emit_module_format_of_file_worker(file_name, options, meta);
    if let Some(parent_id) = parent {
        if let Some(call) = tsc_ast::walk_up_parenthesized_expressions(parent_id, nodes) {
            if tsc_ast::is_import_call(&nodes[call], nodes) {
                if tsc_ast::is_source_phase_import_call(&nodes[call], nodes) {
                    return ModuleKind::ESNext;
                }
                if tsc_ast::should_transform_import_call(file_name, options, file_emit_mode) {
                    return ModuleKind::CommonJS;
                }
                return ModuleKind::ESNext;
            }
        }
    }
    // If we're in --module preserve on an input file, we know that an import
    // is an import. But if this is a declaration file, we'd prefer to use the
    // impliedNodeFormat. Since we want things to be consistent between the two,
    // we need to issue errors when the user writes ESM syntax in a definitely-CJS
    // file, until/unless declaration emit can indicate a true ESM import. On the
    // other hand, writing CJS syntax in a definitely-ESM file is fine, since declaration
    // emit preserves the CJS syntax.
    if file_emit_mode == ModuleKind::CommonJS {
        ModuleKind::CommonJS
    } else if file_emit_mode.is_non_node_esm() || file_emit_mode == ModuleKind::Preserve {
        ModuleKind::ESNext
    } else {
        ModuleKind::None
    }
}

/// `contentMapperTransformDiagnostic`.
fn content_mapper_transform_diagnostic(
    file: &LoadedSourceFile,
    label: &str,
    err: &ContentMapperError,
) -> DiagnosticRef {
    if let Some(collision) = err.as_supplemental_file_collision_error() {
        return content_mapper_transform_diagnostic_chain(
            file,
            label,
            &diagnostics::Content_mapper_supplemental_output_file_0_conflicts_with_an_existing_file,
            &[tsc_tsoptions::value::Value::Str(
                collision.file_name.as_string().to_string(),
            )],
        );
    }
    if let Some(transform_error) = err.as_transform_error() {
        match transform_error.kind {
            TransformErrorKind::Initialize => {
                if let Some(initialize_error) = err.as_initialize_error() {
                    match initialize_error.kind {
                        InitializeErrorKind::PositionEncoding => {
                            return content_mapper_transform_diagnostic_chain(
                                file,
                                label,
                                &diagnostics::The_content_mapper_selected_unsupported_position_encoding_0,
                                &[tsc_tsoptions::value::Value::Str(
                                    initialize_error.position_encoding.to_string(),
                                )],
                            );
                        }
                        InitializeErrorKind::EmptyDiagnosticSource => {
                            return content_mapper_transform_diagnostic_chain(
                                file,
                                label,
                                &diagnostics::The_content_mapper_diagnostic_source_must_not_be_empty,
                                &[],
                            );
                        }
                        InitializeErrorKind::ReservedDiagnosticSource => {
                            return content_mapper_transform_diagnostic_chain(
                                file,
                                label,
                                &diagnostics::The_content_mapper_diagnostic_source_0_is_reserved_by_TypeScript,
                                &[tsc_tsoptions::value::Value::Str(
                                    initialize_error.diagnostic_source.clone(),
                                )],
                            );
                        }
                        _ => {}
                    }
                }
                return content_mapper_transform_diagnostic_chain(
                    file,
                    label,
                    &diagnostics::The_content_mapper_process_could_not_be_started_or_initialized,
                    &[],
                );
            }
            TransformErrorKind::Project => {
                return content_mapper_transform_diagnostic_chain(
                    file,
                    label,
                    content_mapper_project_error_diagnostic(err),
                    &[],
                );
            }
            TransformErrorKind::Request => {
                return content_mapper_transform_diagnostic_chain(
                    file,
                    label,
                    &diagnostics::The_content_mapper_process_failed_while_handling_the_transform_request,
                    &[],
                );
            }
            TransformErrorKind::Response => {
                if let Some(extension_error) = err.as_invalid_virtual_extension_error() {
                    return content_mapper_transform_diagnostic_chain(
                        file,
                        label,
                        &diagnostics::The_content_mapper_returned_an_output_with_unsupported_virtual_extension_0,
                        &[tsc_tsoptions::value::Value::Str(
                            extension_error.extension.clone(),
                        )],
                    );
                }
                if let Some(directive_error) = err.as_diagnostic_directive_error() {
                    let detail = match directive_error.kind {
                        DiagnosticDirectiveErrorKind::InvalidRange => {
                            Some(tsc_ast::diagnostic::new_compiler_diagnostic(
                                &diagnostics::Diagnostic_directive_0_returned_by_the_content_mapper_has_an_invalid_range,
                                &[tsc_tsoptions::value::Value::Int(
                                    directive_error.index as i64,
                                )],
                            ))
                        }
                        DiagnosticDirectiveErrorKind::InvalidPolicy => {
                            Some(tsc_ast::diagnostic::new_compiler_diagnostic(
                                &diagnostics::The_content_mapper_returned_a_diagnostic_directive_with_invalid_policy_0,
                                &[tsc_tsoptions::value::Value::Str(
                                    directive_error.policy.0.to_string(),
                                )],
                            ))
                        }
                        DiagnosticDirectiveErrorKind::ExpectMissingUnusedDiagnostic => {
                            Some(tsc_ast::diagnostic::new_compiler_diagnostic(
                                &diagnostics::Diagnostic_directive_0_returned_by_the_content_mapper_must_specify_unusedExpectDirectiveIndex_when_there_is_not_exactly_one_unusedExpectDirectiveDiagnostics_entry,
                                &[tsc_tsoptions::value::Value::Int(
                                    directive_error.index as i64,
                                )],
                            ))
                        }
                        DiagnosticDirectiveErrorKind::InvalidUnusedDiagnosticIndex => {
                            Some(tsc_ast::diagnostic::new_compiler_diagnostic(
                                &diagnostics::Diagnostic_directive_0_returned_by_the_content_mapper_has_an_invalid_unusedExpectDirectiveIndex,
                                &[tsc_tsoptions::value::Value::Int(
                                    directive_error.index as i64,
                                )],
                            ))
                        }
                        DiagnosticDirectiveErrorKind::Overlap => {
                            Some(tsc_ast::diagnostic::new_compiler_diagnostic(
                                &diagnostics::The_content_mapper_returned_diagnostic_directives_with_overlapping_virtual_ranges,
                                &[] as &[tsc_tsoptions::value::Value],
                            ))
                        }
                        _ => None,
                    };
                    if let Some(mut detail) = detail {
                        if directive_error.supplemental_index >= 0 {
                            detail = tsc_ast::diagnostic::new_diagnostic_chain(
                                Some(&detail),
                                &diagnostics::The_invalid_diagnostic_directive_is_in_supplemental_output_0_returned_by_the_content_mapper,
                                &[tsc_tsoptions::value::Value::Int(
                                    directive_error.supplemental_index as i64,
                                )],
                            );
                        }
                        return content_mapper_transform_diagnostic_with_detail(
                            file, label, detail,
                        );
                    }
                }
                return content_mapper_transform_diagnostic_chain(
                    file,
                    label,
                    &diagnostics::The_content_mapper_returned_an_invalid_transform_response,
                    &[],
                );
            }
            TransformErrorKind::Mappings => {
                return tsc_ast::diagnostic::new_diagnostic(
                    Some(tsc_ast::diagnostic::DiagnosticFile::from_node(
                        file.file, &file.nodes.borrow(),
                    )),
                    tsc_core::text::TextRange::new(0, 0),
                    &diagnostics::The_content_mapper_0_did_not_provide_the_required_position_mappings,
                    &[tsc_tsoptions::value::Value::Str(label.to_string())],
                );
            }
            _ => {}
        }
    }
    tsc_ast::diagnostic::new_diagnostic(
        Some(tsc_ast::diagnostic::DiagnosticFile::from_node(
            file.file,
            &file.nodes.borrow(),
        )),
        tsc_core::text::TextRange::new(0, 0),
        &diagnostics::The_content_mapper_0_failed_to_transform_this_file,
        &[tsc_tsoptions::value::Value::Str(label.to_string())],
    )
}

/// `ContentMapperProjectErrorDiagnostic`.
pub fn content_mapper_project_error_diagnostic(
    err: &ContentMapperError,
) -> &'static diagnostics::Message {
    if let Some(project_error) = err.as_project_error() {
        match project_error.kind {
            ProjectErrorKind::MalformedResponse => {
                return &diagnostics::The_content_mapper_returned_a_project_response_that_could_not_be_decoded;
            }
            ProjectErrorKind::MissingConfigIdentity => {
                return &diagnostics::The_content_mapper_did_not_return_configIdentity_which_is_required_when_the_content_mapper_has_dynamicConfig_Colon_true_in_its_package_json;
            }
            ProjectErrorKind::NonAbsoluteWatchedFile => {
                return &diagnostics::The_content_mapper_returned_a_non_absolute_path_in_watchedFiles;
            }
            ProjectErrorKind::UnexpectedConfigIdentity => {
                return &diagnostics::The_content_mapper_returned_configIdentity_which_is_only_allowed_when_it_declares_dynamicConfig_Colon_true_in_its_package_json;
            }
            ProjectErrorKind::UnexpectedWatchedFiles => {
                return &diagnostics::The_content_mapper_returned_watchedFiles_which_is_only_allowed_when_it_declares_dynamicConfig_Colon_true_in_its_package_json;
            }
            _ => {}
        }
    }
    &diagnostics::The_content_mapper_process_failed_while_handling_the_project_request
}

fn content_mapper_transform_diagnostic_chain(
    file: &LoadedSourceFile,
    label: &str,
    message: &'static diagnostics::Message,
    args: &[tsc_tsoptions::value::Value],
) -> DiagnosticRef {
    content_mapper_transform_diagnostic_with_detail(
        file,
        label,
        tsc_ast::diagnostic::new_compiler_diagnostic(message, args),
    )
}

fn content_mapper_transform_diagnostic_with_detail(
    file: &LoadedSourceFile,
    label: &str,
    detail: DiagnosticRef,
) -> DiagnosticRef {
    let diag = tsc_ast::diagnostic::new_diagnostic(
        Some(tsc_ast::diagnostic::DiagnosticFile::from_node(
            file.file,
            &file.nodes.borrow(),
        )),
        tsc_core::text::TextRange::new(0, 0),
        &diagnostics::The_content_mapper_0_failed_to_transform_this_file,
        &[tsc_tsoptions::value::Value::Str(label.to_string())],
    );
    tsc_ast::diagnostic::lock_diagnostic(&diag).add_message_chain(Some(detail.clone()));
    diag
}

/// `contentMapperMappingDiagnostic`.
fn content_mapper_mapping_diagnostic(
    file: &LoadedSourceFile,
    label: &str,
    problem: &tsc_spanmap::MappingError,
) -> DiagnosticRef {
    let loc = tsc_core::text::TextRange::new(0, 0);
    let file_ = Some(tsc_ast::diagnostic::DiagnosticFile::from_node(
        file.file,
        &file.nodes.borrow(),
    ));
    let l = tsc_tsoptions::value::Value::Str(label.to_string());
    use tsc_spanmap::MappingErrorKind as K;
    if problem.kind == K::Overlap {
        tsc_ast::diagnostic::new_diagnostic(
            file_,
            loc,
            &diagnostics::The_content_mapper_0_produced_overlapping_or_out_of_order_position_mappings_near_virtual_offset_1,
            &[l, tsc_tsoptions::value::Value::Int(problem.virtual_pos as i64)],
        )
    } else if problem.kind == K::OutOfBounds {
        tsc_ast::diagnostic::new_diagnostic(
            file_,
            loc,
            &diagnostics::The_content_mapper_0_produced_a_position_mapping_that_points_outside_the_original_content_original_offset_1,
            &[l, tsc_tsoptions::value::Value::Int(problem.original_pos as i64)],
        )
    } else if problem.kind == K::VerbatimMismatch {
        tsc_ast::diagnostic::new_diagnostic(
            file_,
            loc,
            &diagnostics::The_content_mapper_0_produced_a_verbatim_mapping_that_does_not_match_the_original_content_virtual_offset_1_original_offset_2,
            &[
                l,
                tsc_tsoptions::value::Value::Int(problem.virtual_pos as i64),
                tsc_tsoptions::value::Value::Int(problem.original_pos as i64),
            ],
        )
    } else if problem.kind == K::Kind {
        tsc_ast::diagnostic::new_diagnostic(
            file_,
            loc,
            &diagnostics::The_content_mapper_0_produced_a_position_mapping_with_an_invalid_kind_near_virtual_offset_1,
            &[l, tsc_tsoptions::value::Value::Int(problem.virtual_pos as i64)],
        )
    } else if problem.kind == K::Feature {
        tsc_ast::diagnostic::new_diagnostic(
            file_,
            loc,
            &diagnostics::The_content_mapper_0_produced_invalid_mapping_features_near_original_offset_1,
            &[l, tsc_tsoptions::value::Value::Int(problem.original_pos as i64)],
        )
    } else {
        tsc_ast::diagnostic::new_diagnostic(
            file_,
            loc,
            &diagnostics::The_content_mapper_0_did_not_provide_the_required_position_mappings,
            &[l],
        )
    }
}

/// `ContentMapperInitializationDiagnostic` — a fileless diagnostic for a
/// mapper initialization failure.
pub fn content_mapper_initialization_diagnostic(
    label: &str,
    err: &ContentMapperError,
) -> DiagnosticRef {
    let mut label = label.to_string();
    if let Some(initialize_error) = err.as_initialize_error() {
        if label.is_empty() {
            label = initialize_error.mapper_name.clone();
        }
    }
    let diagnostic = tsc_ast::diagnostic::new_compiler_diagnostic(
        &diagnostics::The_content_mapper_0_could_not_be_initialized,
        &[tsc_tsoptions::value::Value::Str(label)],
    );
    if let Some(initialize_error) = err.as_initialize_error() {
        let chain = |m: &'static diagnostics::Message, args: &[tsc_tsoptions::value::Value]| {
            let d = tsc_ast::diagnostic::new_compiler_diagnostic(m, args);
            tsc_ast::diagnostic::lock_diagnostic(&diagnostic).add_message_chain(Some(d));
            diagnostic.clone()
        };
        match initialize_error.kind {
            InitializeErrorKind::ProcessStart => {
                return chain(
                    &diagnostics::The_content_mapper_command_0_could_not_be_started_Colon_1,
                    &[
                        tsc_tsoptions::value::Value::Str(initialize_error.command.clone()),
                        tsc_tsoptions::value::Value::Str(initialize_error.detail.clone()),
                    ],
                );
            }
            InitializeErrorKind::ProcessExit => {
                return chain(
                    &diagnostics::The_content_mapper_process_exited_before_responding_to_the_initialize_request_exit_code_0,
                    &[tsc_tsoptions::value::Value::Int(initialize_error.exit_code as i64)],
                );
            }
            InitializeErrorKind::NoResponse => {
                return chain(
                    &diagnostics::The_content_mapper_did_not_respond_to_the_initialize_request_within_0_seconds,
                    &[tsc_tsoptions::value::Value::Int(initialize_error.timeout_seconds as i64)],
                );
            }
            InitializeErrorKind::InvalidResponse => {
                return chain(
                    &diagnostics::The_content_mapper_returned_an_initialize_response_that_could_not_be_decoded_Colon_0,
                    &[tsc_tsoptions::value::Value::Str(initialize_error.detail.clone())],
                );
            }
            InitializeErrorKind::Request => {
                return chain(
                    &diagnostics::The_content_mapper_s_initialize_request_failed_Colon_0,
                    &[tsc_tsoptions::value::Value::Str(
                        initialize_error.detail.clone(),
                    )],
                );
            }
            InitializeErrorKind::PositionEncoding => {
                return chain(
                    &diagnostics::The_content_mapper_selected_unsupported_position_encoding_0,
                    &[tsc_tsoptions::value::Value::Str(
                        initialize_error.position_encoding.to_string(),
                    )],
                );
            }
            InitializeErrorKind::EmptyDiagnosticSource => {
                return chain(
                    &diagnostics::The_content_mapper_diagnostic_source_must_not_be_empty,
                    &[],
                );
            }
            InitializeErrorKind::ReservedDiagnosticSource => {
                return chain(
                    &diagnostics::The_content_mapper_diagnostic_source_0_is_reserved_by_TypeScript,
                    &[tsc_tsoptions::value::Value::Str(
                        initialize_error.diagnostic_source.clone(),
                    )],
                );
            }
            _ => {}
        }
    }
    tsc_ast::diagnostic::lock_diagnostic(&diagnostic).add_message_chain(Some(
        tsc_ast::diagnostic::new_compiler_diagnostic(
            &diagnostics::The_content_mapper_process_could_not_be_started_or_initialized,
            &[] as &[tsc_tsoptions::value::Value],
        ),
    ));
    diagnostic
}

/// `ContentMapperProjectDiagnostic` — a fileless diagnostic for project
/// setup or mapper initialization.
pub fn content_mapper_project_diagnostic(err: &ContentMapperError) -> DiagnosticRef {
    if err.as_initialize_error().is_some() {
        return content_mapper_initialization_diagnostic("", err);
    }
    tsc_ast::diagnostic::new_compiler_diagnostic(
        content_mapper_project_error_diagnostic(err),
        &[] as &[tsc_tsoptions::value::Value],
    )
}
