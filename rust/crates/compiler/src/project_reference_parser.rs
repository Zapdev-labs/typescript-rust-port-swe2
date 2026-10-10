// Ported from tsc/internal/compiler/projectreferenceparser.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `*projectReferenceParseTask` is `Rc<RefCell<ProjectReferenceParseTask>>`
// (dedup shares tasks; `seen` uses `Rc::as_ptr` identity). The `wg` work group
// runs inline — the port is single-threaded (see PORTING-NOTES). Go's
// `initMapper` assigns freshly-built maps onto the loader's shared
// `*projectReferenceFileMapper`; here the finished maps are moved into a new
// `Arc<ProjectReferenceFileMapper>` that replaces `builder.mapper`, preserving
// the Go invariant that the dts-faking host and the loader see the same
// mapper (`mapper.resolution_host` wraps that same `Arc`).

use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use tsc_tracing::push;
use tsc_tsoptions::parsedcommandline::{ParsedCommandLine, SourceOutputAndProjectReference};
use tsc_tspath::{PathKey, RootedFilePath};

use crate::file_loader::FileLoader;
use crate::project_reference_file_mapper::ProjectReferenceFileMapper;

/// `type projectReferenceParseTask struct`.
pub struct ProjectReferenceParseTask {
    pub config_name: RootedFilePath,
    /// `resolved *tsoptions.ParsedCommandLine` — `None` for unresolved refs.
    pub resolved: Option<Arc<ParsedCommandLine>>,
    pub sub_tasks: Vec<Rc<RefCell<ProjectReferenceParseTask>>>,
}

impl ProjectReferenceParseTask {
    /// `(t *projectReferenceParseTask) parse`.
    fn parse(
        task: &Rc<RefCell<ProjectReferenceParseTask>>,
        _parser: &ProjectReferenceParser,
        loader: &FileLoader,
    ) {
        let config_name = task.borrow().config_name.clone();
        let trace_done = push(
            loader.tracing.as_ref(),
            tsc_tracing::PHASE_PARSE,
            "parseJsonSourceFileConfigFileContent",
            [(
                "path".to_string(),
                serde_json::Value::from(config_name.as_string().to_string()),
            )]
            .into_iter()
            .collect(),
            false,
        );
        let resolved = loader.host.get_resolved_project_reference(
            &config_name,
            &loader.to_path(&config_name.as_path()),
        );
        task.borrow_mut().resolved = resolved;
        let resolved = match &task.borrow().resolved {
            Some(r) => r.clone(),
            None => {
                trace_done();
                return;
            }
        };
        resolved.parse_input_output_names();
        let sub_references = resolved.resolved_project_reference_paths();
        if !sub_references.is_empty() {
            task.borrow_mut().sub_tasks =
                create_project_reference_parse_tasks(sub_references);
        }
        trace_done();
    }
}

/// `createProjectReferenceParseTasks`.
pub fn create_project_reference_parse_tasks(
    project_references: &[RootedFilePath],
) -> Vec<Rc<RefCell<ProjectReferenceParseTask>>> {
    project_references
        .iter()
        .map(|config_name| {
            Rc::new(RefCell::new(ProjectReferenceParseTask {
                config_name: config_name.clone(),
                resolved: None,
                sub_tasks: Vec::new(),
            }))
        })
        .collect()
}

/// `type projectReferenceParser struct` — `loader`/`wg` are passed through
/// `parse`/`start` instead of stored.
pub struct ProjectReferenceParser {
    /// `tasksByFileName` — `RefCell` instead of `collections.SyncMap`
    /// (single-threaded).
    pub tasks_by_file_name: RefCell<FxHashMap<PathKey, Rc<RefCell<ProjectReferenceParseTask>>>>,
}

impl ProjectReferenceParser {
    /// `(p *projectReferenceParser) parse`.
    pub fn parse(&self, loader: &FileLoader, mut tasks: Vec<Rc<RefCell<ProjectReferenceParseTask>>>) {
        self.start(loader, &mut tasks);
        self.init_mapper(loader, &tasks);
    }

    /// `(p *projectReferenceParser) start` — Go queues `task.parse` +
    /// `start(subTasks)` per unseen task; sequential recursion is equivalent.
    fn start(&self, loader: &FileLoader, tasks: &mut [Rc<RefCell<ProjectReferenceParseTask>>]) {
        for task in tasks.iter_mut() {
            let path = loader.to_path(&task.borrow().config_name.as_path());
            let loaded = {
                let mut by_name = self.tasks_by_file_name.borrow_mut();
                if let Some(loaded_task) = by_name.get(&path) {
                    Some(loaded_task.clone())
                } else {
                    by_name.insert(path, task.clone());
                    None
                }
            };
            if let Some(loaded_task) = loaded {
                // dedup tasks to ensure correct file order, regardless of
                // which task would be started first
                *task = loaded_task;
            } else {
                ProjectReferenceParseTask::parse(task, self, loader);
                let mut sub_tasks = task.borrow().sub_tasks.clone();
                self.start(loader, &mut sub_tasks);
                task.borrow_mut().sub_tasks = sub_tasks;
            }
        }
    }

    /// `(p *projectReferenceParser) initMapper`.
    fn init_mapper(&self, loader: &FileLoader, tasks: &[Rc<RefCell<ProjectReferenceParseTask>>]) {
        let total_references = self.tasks_by_file_name.borrow().len() + 1;
        let mut config_to_project_reference: FxHashMap<
            PathKey,
            Option<Arc<ParsedCommandLine>>,
        > = FxHashMap::with_capacity_and_hasher(total_references, Default::default());
        let mut references_in_config_file: FxHashMap<PathKey, Vec<PathKey>> =
            FxHashMap::with_capacity_and_hasher(total_references, Default::default());
        let mut source_to_project_reference: FxHashMap<
            PathKey,
            Arc<SourceOutputAndProjectReference>,
        > = FxHashMap::default();
        let mut output_dts_to_project_reference: FxHashMap<
            PathKey,
            Arc<SourceOutputAndProjectReference>,
        > = FxHashMap::default();
        let dts_directories = tsc_collections::SyncSet::new();

        let old_mapper = loader.project_references.borrow().mapper.clone();
        let root_config_path = old_mapper.root_config_path();
        let mut seen = HashSet::new();
        let root_refs = self.init_mapper_worker(
            loader,
            tasks,
            &mut seen,
            &old_mapper,
            &mut config_to_project_reference,
            &mut references_in_config_file,
            &mut source_to_project_reference,
            &mut output_dts_to_project_reference,
            &dts_directories,
        );
        references_in_config_file.insert(root_config_path, root_refs);

        // Go assigns the maps on the shared `*projectReferenceFileMapper`;
        // here the fully-built replacement `Arc` is installed and the
        // resolution host wraps it (see the header PORT note).
        let new_mapper = Arc::new(ProjectReferenceFileMapper {
            config: old_mapper.config.clone(),
            use_source_of_project_reference: old_mapper.use_source_of_project_reference,
            dts_directories,
            config_to_project_reference,
            references_in_config_file,
            source_to_project_reference,
            output_dts_to_project_reference,
            // `realpathDtsToSource` is still empty here — it is populated
            // later, during file loading — but share the instance anyway so
            // any earlier `resolveSymlink` writes survive.
            realpath_dts_to_source: tsc_collections::SyncMap::default(),
        });
        {
            let mut builder = loader.project_references.borrow_mut();
            builder.mapper = new_mapper.clone();
            builder.host = new_mapper.resolution_host(builder.host.clone());
        }
    }

    /// `(p *projectReferenceParser) initMapperWorker`.
    #[allow(clippy::too_many_arguments)]
    fn init_mapper_worker(
        &self,
        loader: &FileLoader,
        tasks: &[Rc<RefCell<ProjectReferenceParseTask>>],
        seen: &mut HashSet<usize>,
        old_mapper: &Arc<ProjectReferenceFileMapper>,
        config_to_project_reference: &mut FxHashMap<PathKey, Option<Arc<ParsedCommandLine>>>,
        references_in_config_file: &mut FxHashMap<PathKey, Vec<PathKey>>,
        source_to_project_reference: &mut FxHashMap<PathKey, Arc<SourceOutputAndProjectReference>>,
        output_dts_to_project_reference: &mut FxHashMap<
            PathKey,
            Arc<SourceOutputAndProjectReference>,
        >,
        dts_directories: &tsc_collections::SyncSet<PathKey>,
    ) -> Vec<PathKey> {
        if tasks.is_empty() {
            return Vec::new();
        }
        let mut results = Vec::with_capacity(tasks.len());
        for task in tasks {
            let path = loader.to_path(&task.borrow().config_name.as_path());
            results.push(path.clone());
            // ensure we only walk each task once
            if !seen.insert(Rc::as_ptr(task) as usize) {
                continue;
            }
            let resolved = task.borrow().resolved.clone();
            config_to_project_reference.insert(path.clone(), resolved.clone());
            let same_config_file = match (&old_mapper.config.config_file, &resolved) {
                (Some(config_file), Some(resolved)) => match &resolved.config_file {
                    Some(resolved_config_file) => Arc::ptr_eq(config_file, resolved_config_file),
                    None => false,
                },
                (None, Some(_)) => false,
                (_, None) => true,
            };
            if let Some(resolved) = &resolved {
                if !same_config_file {
                    // Map current task's files first, before recursing into
                    // subtasks. This matches TypeScript's behavior where child
                    // project references overwrite parent entries when a file
                    // belongs to multiple projects.
                    if let Some(map) = resolved.source_to_project_reference() {
                        source_to_project_reference.extend(map.iter().map(|(k, v)| (k.clone(), v.clone())));
                    }
                    if let Some(map) = resolved.output_dts_to_project_reference() {
                        output_dts_to_project_reference
                            .extend(map.iter().map(|(k, v)| (k.clone(), v.clone())));
                    }
                    if old_mapper.use_source_of_project_reference {
                        if let Some(options) = resolved.compiler_options() {
                            let mut decl_dir = options.declaration_dir.clone();
                            if decl_dir.as_string().is_empty() {
                                decl_dir = options.out_dir.clone();
                            }
                            if !decl_dir.as_string().is_empty() {
                                dts_directories
                                    .add(loader.to_path(&decl_dir.as_path()));
                            }
                        }
                    }
                }
            }
            let mut sub_tasks = task.borrow().sub_tasks.clone();
            let references_in_config = self.init_mapper_worker(
                loader,
                &mut sub_tasks,
                seen,
                old_mapper,
                config_to_project_reference,
                references_in_config_file,
                source_to_project_reference,
                output_dts_to_project_reference,
                dts_directories,
            );
            references_in_config_file.insert(path, references_in_config);
        }
        results
    }
}
