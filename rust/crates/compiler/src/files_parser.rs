// Ported from tsc/internal/compiler/filesparser.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go parallelizes `filesParser.start` through a `core.WorkGroup` and
// guards `parseTaskData` with a `sync.Mutex`. The Rust port is intentionally
// single-threaded (see PORTING-NOTES): `WorkGroup::queue` requires `Send`
// closures and `Rc`/`RefCell`/`Node` arenas are not `Send`. Work items are
// deferred on a `VecDeque` and drained after `start` returns, which preserves
// Go's semantics exactly: in Go, `w.start` calls made while holding
// `data.mu` merely queue the closures, so recursively revisiting the same
// `taskDataByPath` entry can never lock the same mutex twice on one thread.
// `*ast.SourceFile` task results are `LoadedSourceFile` (`NodeId` + shared
// arena handle); `*parseTask` is `Rc<RefCell<ParseTask>>` and
// `*parseTaskData` is `Rc<RefCell<ParseTaskData>>` — Go's `seen` map keys
// become `Rc::as_ptr` identities.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;

use rustc_hash::FxHashMap;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::utilities::HasFileName;
use tsc_ast::{NodeId, SourceFileMetaData};
use tsc_core::options_generated::ModuleKind;
use tsc_core::tristate::TS_TRUE;
use tsc_diagnostics as diagnostics;
use tsc_module::{
    DiagAndArgs, ModeAwareCache, ModeAwareCacheKey, PackageId, ResolvedModule,
    ResolvedTypeReferenceDirective,
};
use tsc_tracing::push;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::file_include::{
    FILE_INCLUDE_KIND_CONTENT_MAPPER_SUPPLEMENTAL, FILE_INCLUDE_KIND_LIB_REFERENCE_DIRECTIVE,
    FileIncludeReason, ReferencedFileData,
};
use crate::file_loader::{
    DuplicateSourceFile, FileLoader, JsxRuntimeImportSpecifier, LibFile, LoadedFile,
    LoadedSourceFile, ProcessedFiles, RedirectsFile,
};
use crate::include_processor::FileIncludeData;
use crate::processing_diagnostic::{IncludeExplainingDiagnostic, ProcessingDiagnostic};

/// `type parseTask struct`.
#[derive(Default)]
pub struct ParseTask {
    pub normalized_file_path: RootedFilePath,
    pub path: PathKey,
    /// `file *ast.SourceFile` — the parsed canonical file (content-mapped
    /// supplementals spawn sibling tasks, so only the canonical `NodeId` +
    /// arena handle live here).
    pub file: Option<LoadedSourceFile>,
    pub lib_file: Option<Rc<LibFile>>,
    pub redirected_parse_task: Option<Rc<RefCell<ParseTask>>>,
    pub sub_tasks: Vec<Rc<RefCell<ParseTask>>>,
    pub loaded: bool,
    pub started_sub_tasks: bool,
    pub is_for_automatic_type_directive: bool,
    pub is_content_mapper_supplemental: bool,
    pub failed_lookup: bool,
    pub include_reason: Option<Rc<FileIncludeReason>>,
    pub package_id: PackageId,

    pub metadata: SourceFileMetaData,
    pub resolutions_in_file: ModeAwareCache<Option<ResolvedModule>>,
    pub resolutions_trace: Vec<DiagAndArgs>,
    pub type_resolutions_in_file: ModeAwareCache<ResolvedTypeReferenceDirective>,
    pub type_resolutions_trace: Vec<DiagAndArgs>,
    pub resolution_diagnostics: Vec<DiagnosticRef>,
    pub processing_diagnostics: Vec<ProcessingDiagnostic>,
    pub import_helpers_import_specifier: Option<NodeId>,
    pub jsx_runtime_import_specifier: Option<JsxRuntimeImportSpecifier>,

    pub increase_depth: bool,
    pub elide_on_depth: bool,

    pub loaded_task: Option<Rc<RefCell<ParseTask>>>,
    pub all_include_reasons: Vec<Rc<FileIncludeReason>>,
}

impl HasFileName for ParseTask {
    /// `(t *parseTask) FileName`.
    fn file_name(&self) -> &RootedFilePath {
        &self.normalized_file_path
    }
    /// `(t *parseTask) PathKey`.
    fn path_key(&self) -> &PathKey {
        &self.path
    }
}

/// `type resolvedRef struct`.
#[derive(Default)]
pub struct ResolvedRef {
    pub file_name: RootedFilePath,
    pub path: PathKey,
    pub increase_depth: bool,
    pub elide_on_depth: bool,
    pub include_reason: Option<Rc<FileIncludeReason>>,
    pub package_id: PackageId,
}

impl ParseTask {
    /// `(t *parseTask) addSubTask`.
    /// PORT: takes `&RefCell` rather than `&Rc<RefCell>` so the file loader's
    /// `&RefCell<ParseTask>` task references can queue subtasks too (Go's
    /// `t.addSubTask` has no ownership requirement).
    pub(crate) fn add_sub_task(
        task: &RefCell<ParseTask>,
        ref_: ResolvedRef,
        lib_file: Option<Rc<LibFile>>,
    ) {
        task.borrow_mut()
            .sub_tasks
            .push(Rc::new(RefCell::new(ParseTask {
                normalized_file_path: ref_.file_name,
                path: ref_.path,
                lib_file,
                increase_depth: ref_.increase_depth,
                elide_on_depth: ref_.elide_on_depth,
                include_reason: ref_.include_reason,
                package_id: ref_.package_id,
                ..Default::default()
            })));
    }

    /// `(t *parseTask) redirect`.
    fn redirect(task: &Rc<RefCell<ParseTask>>, file_name: RootedFilePath, path: PathKey) {
        let (lib_file, include_reason) = {
            let t = task.borrow();
            (t.lib_file.clone(), t.include_reason.clone())
        };
        let redirected = Rc::new(RefCell::new(ParseTask {
            normalized_file_path: file_name,
            path,
            lib_file,
            include_reason,
            ..Default::default()
        }));
        // increaseDepth and elideOnDepth are not copied to redirects, otherwise
        // their depth would be double counted.
        let mut t = task.borrow_mut();
        t.redirected_parse_task = Some(redirected.clone());
        t.sub_tasks = vec![redirected];
    }

    /// `(t *parseTask) load`.
    pub fn load(task: &Rc<RefCell<ParseTask>>, loader: &FileLoader) {
        task.borrow_mut().loaded = true;
        if task.borrow().is_for_automatic_type_directive {
            Self::load_automatic_type_directives(task, loader);
            return;
        }
        if task.borrow().failed_lookup {
            // The root file name did not resolve to a supported extension; the task
            // exists only to carry its processing diagnostic, so nothing is parsed.
            return;
        }
        let trace_done = push(
            loader.tracing.as_ref(),
            tsc_tracing::PHASE_PROGRAM,
            "findSourceFile",
            [(
                "fileName".to_string(),
                serde_json::Value::from(task.borrow().normalized_file_path.as_string().to_string()),
            )]
            .into_iter()
            .collect(),
            false,
        );

        enum Flow {
            Continue,
            Return,
        }
        let flow = (|| {
            let (redirect, redirect_path) = {
                let t = task.borrow();
                loader
                    .project_references
                    .borrow()
                    .get_parse_file_redirect(&*t as &dyn HasFileName)
            };
            if !redirect.as_string().is_empty() {
                Self::redirect(task, redirect, redirect_path);
                return Flow::Return;
            }

            {
                let (is_supplemental, has_extension) = {
                    let t = task.borrow();
                    (
                        t.is_content_mapper_supplemental,
                        t.normalized_file_path.has_extension(),
                    )
                };
                if !is_supplemental && has_extension {
                    let compiler_options = loader
                        .opts
                        .config
                        .compiler_options()
                        .cloned()
                        .unwrap_or_default();
                    let allow_non_ts_extensions =
                        compiler_options.allow_non_ts_extensions.is_true();
                    if !allow_non_ts_extensions {
                        let canonical_file_name = task.borrow().path.clone();
                        if !loader.is_supported_extension(&canonical_file_name) {
                            if canonical_file_name.has_js_file_extension() {
                                let (reason, file_name) = {
                                    let t = task.borrow();
                                    (
                                        t.include_reason.clone(),
                                        t.normalized_file_path.as_string().to_string(),
                                    )
                                };
                                task.borrow_mut().processing_diagnostics.push(
                                    ProcessingDiagnostic::ExplainingFileInclude(Box::new(
                                        IncludeExplainingDiagnostic {
                                            file: PathKey::default(),
                                            diagnostic_reason: reason,
                                            message: &diagnostics::File_0_is_a_JavaScript_file_Did_you_mean_to_enable_the_allowJs_option,
                                            args: vec![file_name],
                                        },
                                    )),
                                );
                            } else {
                                let (reason, file_name) = {
                                    let t = task.borrow();
                                    (
                                        t.include_reason.clone(),
                                        t.normalized_file_path.as_string().to_string(),
                                    )
                                };
                                task.borrow_mut().processing_diagnostics.push(
                                    ProcessingDiagnostic::ExplainingFileInclude(Box::new(
                                        IncludeExplainingDiagnostic {
                                            file: PathKey::default(),
                                            diagnostic_reason: reason,
                                            message: &diagnostics::File_0_has_an_unsupported_extension_The_only_supported_extensions_are_1,
                                            args: vec![
                                                file_name,
                                                format!(
                                                    "'{}'",
                                                    loader
                                                        .supported_extensions
                                                        .iter()
                                                        .flatten()
                                                        .cloned()
                                                        .collect::<Vec<_>>()
                                                        .join("', '")
                                                ),
                                            ],
                                        },
                                    )),
                                );
                            }
                            return Flow::Return;
                        }
                    }
                }
            }
            Flow::Continue
        })();
        if matches!(flow, Flow::Return) {
            trace_done();
            return;
        }

        loader
            .total_file_count
            .set(loader.total_file_count.get() + 1);
        {
            let mut t = task.borrow_mut();
            if t.lib_file.is_some() {
                loader.lib_file_count.set(loader.lib_file_count.get() + 1);
                // Default lib files are all scripts; we can safely skip looking up
                // their package.json to avoid adding spurious lookups to file watcher
                // tracking.
                t.metadata = SourceFileMetaData {
                    implied_node_format: ModuleKind::CommonJS,
                    ..Default::default()
                };
            } else {
                let metadata = loader.load_source_file_meta_data(&t.normalized_file_path);
                t.metadata = metadata;
            }
        }

        let loaded_file = match task.borrow().file.clone() {
            Some(f) => Some(LoadedFile {
                canonical: f,
                supplemental: Vec::new(),
            }),
            None => loader.parse_source_file(&task.borrow()),
        };
        let Some(loaded_file) = loaded_file else {
            trace_done();
            return;
        };

        task.borrow_mut().file = Some(loaded_file.canonical.clone());
        let supplementals = loaded_file.supplemental;

        let canonical = task.borrow().file.clone().unwrap();
        let nodes = canonical.nodes.snapshot();
        let sf = nodes[canonical.file].as_source_file();
        let virtual_file_name = sf.virtual_file_name();
        if !virtual_file_name.as_string().is_empty() {
            let mut t = task.borrow_mut();
            let package_json_type = t.metadata.package_json_type.clone();
            t.metadata.implied_node_format =
                tsc_ast::get_implied_node_format_for_file(&virtual_file_name, &package_json_type);
        }
        let referenced_files = sf.referenced_files.to_vec();
        let lib_reference_directives = sf.lib_reference_directives.to_vec();
        let file_name = sf.file_name().clone();
        drop(nodes);

        let compiler_options = loader
            .opts
            .config
            .compiler_options()
            .cloned()
            .unwrap_or_default();
        if !compiler_options.no_resolve.is_true() && !loader.opts.skip_module_resolution {
            for (index, ref_) in referenced_files.iter().enumerate() {
                let (resolved_ref, processing_diagnostic) =
                    loader.resolve_tripleslash_path_reference(&ref_.file_name, &file_name, index);
                if let Some(processing_diagnostic) = processing_diagnostic {
                    task.borrow_mut()
                        .processing_diagnostics
                        .push(processing_diagnostic);
                    continue;
                }
                Self::add_sub_task(task, resolved_ref.unwrap(), None);
            }

            loader.resolve_type_reference_directives(task);
        }

        if compiler_options.no_lib != TS_TRUE && !loader.opts.skip_module_resolution {
            let task_path = task.borrow().path.clone();
            for (index, lib) in lib_reference_directives.iter().enumerate() {
                let include_reason = Rc::new(FileIncludeReason {
                    kind: FILE_INCLUDE_KIND_LIB_REFERENCE_DIRECTIVE,
                    referenced_file: Some(Box::new(ReferencedFileData {
                        file: task_path.clone(),
                        index: index as isize,
                        synthetic: None,
                    })),
                    ..Default::default()
                });
                if let Some(name) =
                    tsc_tsoptions::enummaps::get_lib_file_name(lib.file_name.as_str())
                {
                    let lib_file = loader.path_for_lib_file(&name);
                    Self::add_sub_task(
                        task,
                        ResolvedRef {
                            file_name: lib_file.path.clone(),
                            path: lib_file.path_key.clone(),
                            include_reason: Some(include_reason),
                            ..Default::default()
                        },
                        Some(lib_file),
                    );
                } else {
                    task.borrow_mut()
                        .processing_diagnostics
                        .push(ProcessingDiagnostic::UnknownReference(include_reason));
                }
            }
        }

        loader.resolve_imports_and_module_augmentations(task);
        for supplemental in supplementals {
            let supplemental_file_name = supplemental.file_name();
            let supplemental_path = loader
                .case_sensitivity
                .path_key(&supplemental_file_name.as_path());
            let canonical_source_file = task.borrow().path.clone();
            task.borrow_mut()
                .sub_tasks
                .push(Rc::new(RefCell::new(ParseTask {
                    normalized_file_path: supplemental_file_name,
                    path: supplemental_path,
                    file: Some(supplemental),
                    is_content_mapper_supplemental: true,
                    include_reason: Some(Rc::new(FileIncludeReason {
                        kind: FILE_INCLUDE_KIND_CONTENT_MAPPER_SUPPLEMENTAL,
                        canonical_source_file,
                        ..Default::default()
                    })),
                    ..Default::default()
                })));
        }
        trace_done();
    }

    /// `(t *parseTask) loadAutomaticTypeDirectives`.
    fn load_automatic_type_directives(task: &Rc<RefCell<ParseTask>>, loader: &FileLoader) {
        let trace_done = push(
            loader.tracing.as_ref(),
            tsc_tracing::PHASE_PROGRAM,
            "processTypeReferences",
            Default::default(),
            false,
        );
        let (to_parse_type_refs, type_resolutions_in_file, type_resolutions_trace, p_diagnostics) = {
            let file_name = task.borrow().normalized_file_path.clone();
            loader.resolve_automatic_type_directives(&file_name)
        };
        {
            let mut t = task.borrow_mut();
            t.type_resolutions_in_file = type_resolutions_in_file;
            t.type_resolutions_trace = type_resolutions_trace;
            t.processing_diagnostics.extend(p_diagnostics);
        }
        for type_resolution in to_parse_type_refs {
            Self::add_sub_task(task, type_resolution, None);
        }
        trace_done();
    }
}

/// `type parseTaskData struct`.
#[derive(Default)]
pub struct ParseTaskData {
    /// map of tasks by file casing
    pub tasks: FxHashMap<RootedFilePath, Rc<RefCell<ParseTask>>>,
    pub lowest_depth: usize,
    pub started_sub_tasks: bool,
    pub package_id: PackageId,
}

impl ParseTaskData {
    /// `getParseTaskData`.
    fn new(task: Rc<RefCell<ParseTask>>) -> Self {
        let mut tasks = FxHashMap::default();
        let key = task.borrow().normalized_file_path.clone();
        tasks.insert(key, task);
        ParseTaskData {
            tasks,
            lowest_depth: usize::MAX,
            started_sub_tasks: false,
            package_id: PackageId::default(),
        }
    }
}

/// `type filesParser struct`. The `wg core.WorkGroup` becomes an in-scope
/// deferred `VecDeque` — see the header PORT note.
#[derive(Default)]
pub struct FilesParser {
    pub task_data_by_path: RefCell<FxHashMap<PathKey, Rc<RefCell<ParseTaskData>>>>,
    pub max_depth: usize,
}

/// Deferred `wg.Queue` item. `Box<dyn FnOnce>` so `start` jobs queued while a
/// `ParseTaskData` is borrowed run only after the borrow is released —
/// mirroring Go where the lock is held while queuing and the queued closure
/// blocks on another goroutine.
type Job<'a> = Box<dyn FnOnce() + 'a>;

impl FilesParser {
    /// `(w *filesParser) parse`.
    pub fn parse(&self, loader: &FileLoader, tasks: Vec<Rc<RefCell<ParseTask>>>, depth: usize) {
        // `Rc` so queued `start` jobs can re-enqueue without capturing a
        // `&queue` borrow that would make the queue self-referential.
        let queue = Rc::new(RefCell::new(VecDeque::<Job>::new()));
        self.start(loader, &tasks, depth, &queue);
        // `wg.RunAndWait` — the block scopes the `RefMut` to the pop so
        // `job()` may re-enqueue through `queue.borrow_mut()`.
        while let Some(job) = { queue.borrow_mut().pop_front() } {
            job();
        }
    }

    /// `(w *filesParser) start`.
    fn start<'a>(
        &'a self,
        loader: &'a FileLoader,
        tasks: &[Rc<RefCell<ParseTask>>],
        depth: usize,
        queue: &Rc<RefCell<VecDeque<Job<'a>>>>,
    ) {
        let tasks: Rc<Vec<Rc<RefCell<ParseTask>>>> = Rc::new(tasks.to_vec());
        for (i, task) in tasks.iter().enumerate() {
            let task = task.clone();
            assert!(
                !task.borrow().path.as_string().is_empty(),
                "parse task must have a path key: {}",
                task.borrow().normalized_file_path.as_string()
            );
            let candidate = Rc::new(RefCell::new(ParseTaskData::new(task.clone())));
            let (data, loaded) = {
                let mut map = self.task_data_by_path.borrow_mut();
                let path = task.borrow().path.clone();
                match map.entry(path) {
                    std::collections::hash_map::Entry::Occupied(e) => (e.get().clone(), true),
                    std::collections::hash_map::Entry::Vacant(e) => {
                        (e.insert(candidate).clone(), false)
                    }
                }
            };

            let tasks_ref = tasks.clone();
            let queue_ref = queue.clone();
            queue.borrow_mut().push_back(Box::new(move || {
                let mut start_subtasks = false;
                {
                    let mut data_b = data.borrow_mut();
                    if loaded {
                        let key = task.borrow().normalized_file_path.clone();
                        if let Some(existing_task) = data_b.tasks.get(&key) {
                            tasks_ref[i].borrow_mut().loaded_task = Some(existing_task.clone());
                        } else {
                            data_b.tasks.insert(key, task.clone());
                            // This is new task for file name - so load subtasks
                            // if there was loading for any other casing
                            start_subtasks = data_b.started_sub_tasks;
                        }
                    }

                    // Propagate packageId to data if we have one and data doesn't yet
                    let task_package_id = task.borrow().package_id.clone();
                    if data_b.package_id.name.is_empty() && !task_package_id.name.is_empty() {
                        data_b.package_id = task_package_id;
                    }

                    let current_depth = if task.borrow().increase_depth {
                        depth + 1
                    } else {
                        depth
                    };
                    let lowered = current_depth < data_b.lowest_depth;
                    if lowered {
                        // If we're seeing this task at a lower depth than before,
                        // reprocess its subtasks to ensure they are loaded.
                        data_b.lowest_depth = current_depth;
                        start_subtasks = true;
                        data_b.started_sub_tasks = true;
                    }

                    if task.borrow().elide_on_depth && current_depth > self.max_depth {
                        return;
                    }

                    let task_list: Vec<Rc<RefCell<ParseTask>>> =
                        data_b.tasks.values().cloned().collect();
                    for task_by_file_name in task_list {
                        let mut load_sub_tasks = start_subtasks;
                        if !task_by_file_name.borrow().loaded {
                            ParseTask::load(&task_by_file_name, loader);
                            if task_by_file_name.borrow().redirected_parse_task.is_some() {
                                // Always load redirected task
                                load_sub_tasks = true;
                                data_b.started_sub_tasks = true;
                            }
                        }
                        if load_sub_tasks
                            && (lowered || !task_by_file_name.borrow().started_sub_tasks)
                        {
                            task_by_file_name.borrow_mut().started_sub_tasks = true;
                            let sub_tasks = task_by_file_name.borrow().sub_tasks.clone();
                            let lowest_depth = data_b.lowest_depth;
                            self.start(loader, &sub_tasks, lowest_depth, &queue_ref);
                        }
                    }
                }
            }));
        }
    }

    /// `(w *filesParser) addIncludeReason`.
    fn add_include_reason(
        &self,
        include_processor: &mut FileIncludeData,
        task: &Rc<RefCell<ParseTask>>,
        reason: Option<&Rc<FileIncludeReason>>,
    ) {
        if let Some(redirected) = task.borrow().redirected_parse_task.clone() {
            self.add_include_reason(include_processor, &redirected, reason);
        } else if task.borrow().loaded {
            include_processor
                .file_include_reasons
                .entry(task.borrow().path.clone())
                .or_default()
                .push(reason.cloned().unwrap_or_default());
        }
    }

    /// `(w *filesParser) getProcessedFiles`.
    pub fn get_processed_files(&self, loader: &FileLoader) -> ProcessedFiles {
        let total_file_count = loader.total_file_count.get() as usize;
        let lib_file_count = loader.lib_file_count.get() as usize;

        let mut missing_files: HashSet<PathKey> = HashSet::new();
        let mut duplicate_source_files: Vec<DuplicateSourceFile> = Vec::new();
        let mut files: Vec<LoadedSourceFile> =
            Vec::with_capacity(total_file_count - lib_file_count);
        // totalFileCount here since we append files to it later to construct the final list
        let mut lib_files: Vec<LoadedSourceFile> = Vec::with_capacity(total_file_count);

        let mut files_by_path: FxHashMap<PathKey, NodeId> =
            FxHashMap::with_capacity_and_hasher(total_file_count, Default::default());
        // stores 'filename -> file association' ignoring case
        // used to track cases when two file names differ only in casing
        let mut tasks_seen_by_name_ignore_case: Option<HashMap<PathKey, Rc<RefCell<ParseTask>>>> =
            if loader.case_sensitivity.is_case_sensitive() {
                Some(HashMap::with_capacity(total_file_count))
            } else {
                None
            };

        let mut include_data = FileIncludeData {
            file_include_reasons: FxHashMap::with_capacity_and_hasher(
                total_file_count,
                Default::default(),
            ),
            ..Default::default()
        };
        let mut output_file_to_project_reference_source: FxHashMap<PathKey, RootedFilePath> =
            FxHashMap::default();
        let can_use_project_reference_source = loader.opts.can_use_project_reference_source();
        let mut resolved_modules: FxHashMap<PathKey, ModeAwareCache<Option<ResolvedModule>>> =
            FxHashMap::with_capacity_and_hasher(total_file_count + 1, Default::default());
        let mut type_resolutions_in_file: FxHashMap<
            PathKey,
            ModeAwareCache<ResolvedTypeReferenceDirective>,
        > = FxHashMap::with_capacity_and_hasher(total_file_count, Default::default());
        let mut source_file_meta_datas: FxHashMap<PathKey, SourceFileMetaData> =
            FxHashMap::with_capacity_and_hasher(total_file_count, Default::default());
        let mut jsx_runtime_import_specifiers: FxHashMap<PathKey, JsxRuntimeImportSpecifier> =
            FxHashMap::default();
        let mut import_helpers_import_specifiers: FxHashMap<PathKey, NodeId> = FxHashMap::default();
        let mut source_files_found_searching_node_modules: HashSet<PathKey> = HashSet::new();
        let mut lib_files_map: FxHashMap<PathKey, Rc<LibFile>> =
            FxHashMap::with_capacity_and_hasher(lib_file_count, Default::default());

        let mut redirect_targets_map: FxHashMap<PathKey, Vec<RootedFilePath>> =
            FxHashMap::default();
        let mut redirect_files_by_path: FxHashMap<PathKey, Rc<RedirectsFile>> =
            FxHashMap::default();
        let deduplicate_packages = !loader
            .opts
            .config
            .compiler_options()
            .map(|o| o.deduplicate_packages)
            .unwrap_or_default()
            .is_false();
        // `packageIdToSourceFile` — `NodeId` + the file's `PathKey` (Go reads
        // `packageIdFile.PathKey()` for redirect targets).
        let mut package_id_to_source_file: FxHashMap<PackageId, (NodeId, PathKey)> =
            FxHashMap::default();

        // recordedDuplicates tracks, per task data, the set of file-name casings that
        // have already been recorded in duplicateSourceFiles (see Go comment).
        let mut recorded_duplicates: HashMap<usize, HashSet<RootedFilePath>> = HashMap::new();

        #[allow(clippy::too_many_arguments)]
        fn collect_files(
            parser: &FilesParser,
            loader: &FileLoader,
            tasks: &[Rc<RefCell<ParseTask>>],
            seen: &mut HashMap<usize, RootedFilePath>,
            recorded_duplicates: &mut HashMap<usize, HashSet<RootedFilePath>>,
            missing_files: &mut HashSet<PathKey>,
            duplicate_source_files: &mut Vec<DuplicateSourceFile>,
            files: &mut Vec<LoadedSourceFile>,
            lib_files: &mut Vec<LoadedSourceFile>,
            files_by_path: &mut FxHashMap<PathKey, NodeId>,
            tasks_seen_by_name_ignore_case: &mut Option<HashMap<PathKey, Rc<RefCell<ParseTask>>>>,
            include_data: &mut FileIncludeData,
            output_file_to_project_reference_source: &mut FxHashMap<PathKey, RootedFilePath>,
            resolved_modules: &mut FxHashMap<PathKey, ModeAwareCache<Option<ResolvedModule>>>,
            type_resolutions_in_file: &mut FxHashMap<
                PathKey,
                ModeAwareCache<ResolvedTypeReferenceDirective>,
            >,
            source_file_meta_datas: &mut FxHashMap<PathKey, SourceFileMetaData>,
            jsx_runtime_import_specifiers: &mut FxHashMap<PathKey, JsxRuntimeImportSpecifier>,
            import_helpers_import_specifiers: &mut FxHashMap<PathKey, NodeId>,
            source_files_found_searching_node_modules: &mut HashSet<PathKey>,
            lib_files_map: &mut FxHashMap<PathKey, Rc<LibFile>>,
            redirect_targets_map: &mut FxHashMap<PathKey, Vec<RootedFilePath>>,
            redirect_files_by_path: &mut FxHashMap<PathKey, Rc<RedirectsFile>>,
            package_id_to_source_file: &mut FxHashMap<PackageId, (NodeId, PathKey)>,
            deduplicate_packages: bool,
            can_use_project_reference_source: bool,
        ) {
            for task in tasks {
                let mut task = task.clone();
                let include_reason = task.borrow().include_reason.clone();
                // Exclude automatic type directive tasks from include reason
                // processing, as these are internal implementation details and
                // should not contribute to the reasons for including files.
                if task.borrow().redirected_parse_task.is_none()
                    && !task.borrow().is_for_automatic_type_directive
                {
                    let loaded_task = { task.borrow().loaded_task.clone() };
                    if let Some(loaded_task) = loaded_task {
                        task = loaded_task;
                    }
                    parser.add_include_reason(include_data, &task, include_reason.as_ref());
                }
                let data = parser
                    .task_data_by_path
                    .borrow()
                    .get(&task.borrow().path)
                    .cloned();
                if !task.borrow().loaded {
                    continue;
                }
                let Some(data) = data else {
                    continue;
                };
                let data_key = Rc::as_ptr(&data) as usize;

                // ensure we only walk each task once
                if let Some(checked_name) = seen.get(&data_key) {
                    let checked_name = checked_name.clone();
                    let (normalized_file_path, file) = {
                        let t = task.borrow();
                        (t.normalized_file_path.clone(), t.file.clone())
                    };
                    if let Some(file) = &file {
                        if checked_name != normalized_file_path {
                            let dups = recorded_duplicates.entry(data_key).or_default();
                            if dups.insert(normalized_file_path.clone()) {
                                let nodes = file.nodes.snapshot();
                                let sf = nodes[file.file].as_source_file();
                                duplicate_source_files.push(DuplicateSourceFile {
                                    parse_options: sf.parse_options.clone(),
                                    content_mapper_parse_options: sf.content_mapper_parse_options(),
                                    hash: sf.hash,
                                    script_kind: sf.script_kind,
                                    content_mapper: sf.content_mapper().to_string(),
                                    is_content_mapper_failure_stub: sf
                                        .is_content_mapper_failure_stub(),
                                });
                            }
                        }
                    }
                    if !loader
                        .opts
                        .config
                        .compiler_options()
                        .map(|o| o.force_consistent_casing_in_file_names)
                        .unwrap_or_default()
                        .is_false()
                    {
                        // Check if it differs only in drive letters its ok to
                        // ignore that error:
                        let checked_absolute_path = checked_name.without_root().to_string();
                        let input_absolute_path = normalized_file_path.without_root().to_string();
                        if checked_absolute_path != input_absolute_path {
                            include_data.add_processing_diagnostics_for_file_casing(
                                task.borrow().path.clone(),
                                checked_name.as_string().to_string(),
                                normalized_file_path.as_string().to_string(),
                                include_reason.clone().unwrap_or_default(),
                            );
                        }
                    }
                    continue;
                } else {
                    seen.insert(data_key, task.borrow().normalized_file_path.clone());
                }

                if let Some(seen_map) = tasks_seen_by_name_ignore_case.as_mut() {
                    let path_lower_case = task.borrow().path.case_insensitive_key();
                    if let Some(task_by_ignore_case) = seen_map.get(&path_lower_case) {
                        let existing = task_by_ignore_case.borrow();
                        include_data.add_processing_diagnostics_for_file_casing(
                            existing.path.clone(),
                            existing.normalized_file_path.as_string().to_string(),
                            task.borrow().normalized_file_path.as_string().to_string(),
                            include_reason.clone().unwrap_or_default(),
                        );
                    } else {
                        seen_map.insert(path_lower_case, task.clone());
                    }
                }

                {
                    let t = task.borrow();
                    for trace in &t.type_resolutions_trace {
                        loader.host.trace(trace.message, &trace.args);
                    }
                    for trace in &t.resolutions_trace {
                        loader.host.trace(trace.message, &trace.args);
                    }
                }

                let file = task.borrow().file.clone();
                let package_id = data.borrow().package_id.clone();
                if deduplicate_packages && !package_id.name.is_empty() {
                    if let Some(&(package_id_file, ref target_path_key)) =
                        package_id_to_source_file.get(&package_id)
                    {
                        let target_path_key = target_path_key.clone();
                        if let Some(file) = &file {
                            // Package deduplication keeps the first package instance
                            // in the program, but we still parsed this file and
                            // acquired it through the host, so snapshot disposal must
                            // release that extra owner.
                            let nodes = file.nodes.snapshot();
                            let sf = nodes[file.file].as_source_file();
                            duplicate_source_files.push(DuplicateSourceFile {
                                parse_options: sf.parse_options.clone(),
                                content_mapper_parse_options: sf.content_mapper_parse_options(),
                                hash: sf.hash,
                                script_kind: sf.script_kind,
                                content_mapper: sf.content_mapper().to_string(),
                                is_content_mapper_failure_stub: sf.is_content_mapper_failure_stub(),
                            });
                        }
                        redirect_targets_map
                            .entry(target_path_key.clone())
                            .or_default()
                            .push(task.borrow().normalized_file_path.clone());
                        let index = files.len() + redirect_files_by_path.len();
                        let t = task.borrow();
                        redirect_files_by_path.insert(
                            t.path.clone(),
                            Rc::new(RedirectsFile {
                                index,
                                file_name: t.normalized_file_path.clone(),
                                path: t.path.clone(),
                                target: target_path_key,
                            }),
                        );
                        files_by_path.insert(t.path.clone(), package_id_file);
                        if data.borrow().lowest_depth > 0 {
                            source_files_found_searching_node_modules.insert(t.path.clone());
                        }
                        continue;
                    } else if let Some(file) = &file {
                        let file_path_key = file.path();
                        package_id_to_source_file.insert(package_id, (file.file, file_path_key));
                    }
                }

                let sub_tasks = task.borrow().sub_tasks.clone();
                if !sub_tasks.is_empty() {
                    collect_files(
                        parser,
                        loader,
                        &sub_tasks,
                        seen,
                        recorded_duplicates,
                        missing_files,
                        duplicate_source_files,
                        files,
                        lib_files,
                        files_by_path,
                        tasks_seen_by_name_ignore_case,
                        include_data,
                        output_file_to_project_reference_source,
                        resolved_modules,
                        type_resolutions_in_file,
                        source_file_meta_datas,
                        jsx_runtime_import_specifiers,
                        import_helpers_import_specifiers,
                        source_files_found_searching_node_modules,
                        lib_files_map,
                        redirect_targets_map,
                        redirect_files_by_path,
                        package_id_to_source_file,
                        deduplicate_packages,
                        can_use_project_reference_source,
                    );
                }

                // Exclude automatic type directive tasks from include reason
                // processing, as these are internal implementation details and
                // should not contribute to the reasons for including files.
                if task.borrow().redirected_parse_task.is_some() {
                    if !can_use_project_reference_source {
                        let t = task.borrow();
                        output_file_to_project_reference_source.insert(
                            t.redirected_parse_task
                                .as_ref()
                                .unwrap()
                                .borrow()
                                .path
                                .clone(),
                            t.normalized_file_path.clone(),
                        );
                    }
                    continue;
                }

                if task.borrow().is_for_automatic_type_directive {
                    let mut t = task.borrow_mut();
                    type_resolutions_in_file.insert(
                        t.path.clone(),
                        std::mem::take(&mut t.type_resolutions_in_file),
                    );
                    include_data
                        .processing_diagnostics
                        .append(&mut t.processing_diagnostics);
                    continue;
                }

                let path = task.borrow().path.clone();
                {
                    let mut t = task.borrow_mut();
                    include_data
                        .processing_diagnostics
                        .append(&mut t.processing_diagnostics);
                }

                let Some(file) = file else {
                    missing_files.insert(path);
                    continue;
                };

                {
                    let t = task.borrow();
                    if t.lib_file.is_some() {
                        lib_files.push(file.clone());
                        lib_files_map.insert(path.clone(), t.lib_file.clone().unwrap());
                    } else {
                        files.push(file.clone());
                    }
                    files_by_path.insert(path.clone(), file.file);
                    resolved_modules.insert(path.clone(), t.resolutions_in_file.clone());
                    type_resolutions_in_file
                        .insert(path.clone(), t.type_resolutions_in_file.clone());
                    source_file_meta_datas.insert(path.clone(), t.metadata.clone());

                    if let Some(jsx_spec) = t.jsx_runtime_import_specifier.as_ref() {
                        jsx_runtime_import_specifiers.insert(
                            path.clone(),
                            JsxRuntimeImportSpecifier {
                                module_reference: jsx_spec.module_reference.clone(),
                                specifier: jsx_spec.specifier,
                            },
                        );
                    }
                    if let Some(specifier) = t.import_helpers_import_specifier {
                        import_helpers_import_specifiers.insert(path.clone(), specifier);
                    }
                }
                if data.borrow().lowest_depth > 0 {
                    source_files_found_searching_node_modules.insert(path.clone());
                }
            }
        }

        collect_files(
            self,
            loader,
            &loader.root_tasks,
            &mut HashMap::with_capacity(total_file_count),
            &mut recorded_duplicates,
            &mut missing_files,
            &mut duplicate_source_files,
            &mut files,
            &mut lib_files,
            &mut files_by_path,
            &mut tasks_seen_by_name_ignore_case,
            &mut include_data,
            &mut output_file_to_project_reference_source,
            &mut resolved_modules,
            &mut type_resolutions_in_file,
            &mut source_file_meta_datas,
            &mut jsx_runtime_import_specifiers,
            &mut import_helpers_import_specifiers,
            &mut source_files_found_searching_node_modules,
            &mut lib_files_map,
            &mut redirect_targets_map,
            &mut redirect_files_by_path,
            &mut package_id_to_source_file,
            deduplicate_packages,
            can_use_project_reference_source,
        );
        loader.sort_libs(&mut lib_files);

        let mut all_files = lib_files;
        let lib_file_count_final = all_files.len();
        all_files.extend(files);
        for redirect_file in redirect_files_by_path.values_mut() {
            // `Rc<RedirectsFile>` — index adjusted after libs are prepended.
            if let Some(rf) = Rc::get_mut(redirect_file) {
                rf.index += lib_file_count_final;
            }
        }

        let mut lib_keys: Vec<PathKey> = loader
            .path_for_lib_file_resolutions
            .borrow()
            .keys()
            .cloned()
            .collect();
        lib_keys.sort();
        for key in lib_keys {
            let value = loader
                .path_for_lib_file_resolutions
                .borrow()
                .get(&key)
                .cloned()
                .unwrap();
            let mut cache = ModeAwareCache::default();
            cache.insert(
                ModeAwareCacheKey {
                    name: value.library_name.clone(),
                    mode: ModuleKind::CommonJS,
                },
                value.resolution.clone(),
            );
            resolved_modules.insert(key, cache);
            for trace in &value.trace {
                loader.host.trace(trace.message, &trace.args);
            }
        }

        ProcessedFiles {
            finished_processing: true,
            files: all_files,
            duplicate_source_files,
            files_by_path,
            project_reference_file_mapper: Some(loader.project_references.borrow().mapper.clone()),
            resolved_modules,
            type_resolutions_in_file,
            source_file_meta_datas,
            jsx_runtime_import_specifiers,
            import_helpers_import_specifiers,
            source_files_found_searching_node_modules,
            lib_files: lib_files_map,
            missing_files,
            file_include_reasons: include_data.file_include_reasons,
            processing_diagnostics: include_data.processing_diagnostics,
            output_file_to_project_reference_source,
            redirect_targets_map,
            redirect_files_by_path,
            content_mapper_diagnostics: loader.content_mapper_diagnostics.borrow().clone(),
        }
    }
}
