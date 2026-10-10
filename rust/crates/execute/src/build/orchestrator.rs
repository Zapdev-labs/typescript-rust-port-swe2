// Ported from tsc/internal/execute/build/orchestrator.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Concurrency — the deliberate structural divergence of this port:
//
// Go runs each build on a pool of `builders` goroutines (default 4, or 1 for
// `--singleThreaded`) coordinated by `BuildTask.done`/`built` channels and a
// reporter goroutine, and parses config files on a `core.WorkGroup`. The Rust
// compiler stack is single-threaded — `Program`, `ParsedCommandLine`,
// `ParsedSourceFile` and friends are `Rc`/arena-backed and not `Send`/`Sync`,
// so build tasks cannot move between threads — so this port runs a sequential
// work-list instead: `create_build_tasks` recurses instead of queueing,
// `range_tasks` iterates in `order`, `waitOnUpstream`/`close(done)` collapse
// to no-ops (the schedule order is topological and every upstream task
// completes before its downstream runs), and task results are reported in
// `Order()` after the pass. `schedule_order` is still computed and exported
// for parity with `Orchestrator.ScheduleOrder`.
//
// Interior mutability (`RefCell<OrchestratorState>` inside `Orchestrator`,
// `Rc<RefCell<BuildInfoEntry>>` on tasks) replaces Go's mutex/`atomic`
// fields; the watch side still uses the thread-safe `WatchManager` since
// watcher callbacks arrive on backend threads.

use std::cell::RefCell;
use std::io::Write;
use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_ast::diagnostic::{DiagnosticRef, new_compiler_diagnostic};
use tsc_compiler::host::{CompilerHost, new_compiler_host};
use tsc_contentmapper::host::Host as ContentMapperHost;
use tsc_core::context::Context;
use tsc_core::core::if_else;
use tsc_core::options_generated::{BuildOptions, CompilerOptions};
use tsc_core::projectreference::resolve_config_file_name_of_project_reference;
use tsc_fswatch::EventKind;
use tsc_tsoptions::parsedbuildcommandline::ParsedBuildCommandLine;
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath,
    rooted_directory_path_from_path, to_rooted_path,
};
use tsc_vfs::cachedvfs;
use tsc_vfs::vfs::Vfs;
use tsc_watchmanager::{
    DirWatchSet, WatchManager, WatchManagerLock, can_watch_directory, new_dir_watch_set,
    new_watch_manager,
};

use crate::tsc::{
    CommandLineResult, CommandLineTesting, DiagnosticReporter, DiagnosticsReporter, ExitStatus,
    SharedWriter, Statistics, System, Watcher, create_builder_status_reporter,
    create_diagnostic_reporter, create_report_error_summary, create_watch_status_reporter,
};

use super::buildtask::{BuildTask, TaskBuffer, TaskId, TaskResult, UpstreamTask};
use super::host::BuildHost;

/// `type Options struct`.
pub struct Options {
    pub sys: Arc<dyn System>,
    pub command: Arc<ParsedBuildCommandLine>,
    /// `Testing tsc.CommandLineTesting` — `None` is Go's nil.
    pub testing: Option<Arc<dyn CommandLineTesting>>,
}

/// `type OrchestratorResult struct`.
pub struct OrchestratorResult {
    pub result: CommandLineResult,
    pub errors: Vec<DiagnosticRef>,
    pub statistics: Statistics,
    pub files_to_delete: Vec<RootedFilePath>,
}

impl Default for OrchestratorResult {
    fn default() -> OrchestratorResult {
        OrchestratorResult {
            result: CommandLineResult {
                status: ExitStatus::Success,
                watcher: None,
            },
            errors: Vec::new(),
            statistics: Statistics::default(),
            files_to_delete: Vec::new(),
        }
    }
}

/// `tasks`/`oldTasks` — Go stores `*BuildTask` values in a
/// `SyncMap[PathKey, *BuildTask]`; the port keeps them in a `Vec` (the `Rc`
/// inside `BuildTask` is `!Send`) indexed by [`TaskId`], plus a `PathKey`
/// index for Go's `tasks.Load`.
pub(crate) struct OrchestratorState {
    /// `opts`.
    pub(crate) opts: Options,
    /// `currentDirectory`.
    pub(crate) current_directory: RootedDirectoryPath,
    /// `caseSensitivity`.
    pub(crate) case_sensitivity: CaseSensitivity,
    /// `host`.
    pub(crate) host: Arc<BuildHost>,
    /// `contentMapperHost` — created once per `start` call when content
    /// mappers are enabled.
    pub(crate) content_mapper_host: Option<Arc<dyn ContentMapperHost>>,

    // order generation result
    pub(crate) tasks: Vec<BuildTask>,
    /// `tasks` index — Go's `SyncMap` key → position in `self.tasks`.
    pub(crate) tasks_by_path: FxHashMap<PathKey, TaskId>,
    /// `order`.
    pub(crate) order: Vec<TaskId>,
    /// `errors` — circularity errors from graph generation.
    pub(crate) errors: Vec<DiagnosticRef>,
    /// `graphGenerated`.
    pub(crate) graph_generated: bool,

    /// `errorSummaryReporter`.
    pub(crate) error_summary_reporter: Option<DiagnosticsReporter>,
    /// `watchStatusReporter`.
    pub(crate) watch_status_reporter: Option<DiagnosticReporter>,

    /// `scheduleOrder`.
    pub(crate) schedule_order: Vec<TaskId>,
}

impl OrchestratorState {
    /// `o.opts.Command.BuildOptions` — Go's nil-able pointer panics on
    /// absent options just like `expect`.
    pub(crate) fn build_options(&self) -> &BuildOptions {
        self.opts
            .command
            .build_options
            .as_ref()
            .expect("build options")
    }

    /// `o.opts.Command.CompilerOptions`.
    pub(crate) fn command_compiler_options(&self) -> &CompilerOptions {
        self.opts
            .command
            .compiler_options
            .as_ref()
            .expect("compiler options")
    }

    /// `o.opts.Command.Locale()`.
    pub(crate) fn command_locale(&self) -> tsc_locale::Locale {
        self.opts.command.locale().clone()
    }

    /// `(o *Orchestrator) relativeFileName`.
    pub(crate) fn relative_file_name(&self, file_name: &RootedFilePath) -> String {
        self.relative_path(&file_name.as_path())
    }

    /// `(o *Orchestrator) relativePath`.
    pub(crate) fn relative_path(&self, path: &RootedPath) -> String {
        if let Some(relative) = self
            .case_sensitivity
            .relative_path_from_path(&self.current_directory, path)
        {
            return relative.as_string().to_string();
        }
        path.as_string().to_string()
    }

    /// `(o *Orchestrator) getTask`.
    pub(crate) fn get_task(&self, path: &PathKey) -> TaskId {
        *self
            .tasks_by_path
            .get(path)
            .unwrap_or_else(|| panic!("No build task found for {}", path.as_string()))
    }

    /// `(o *Orchestrator) createBuildTasks` — Go queues each config on a
    /// `core.WorkGroup`; the port recurses sequentially (see the banner).
    /// `is_initial_cycle` is Go's `oldTasks == nil`.
    fn create_build_tasks(
        &mut self,
        old_tasks: &mut FxHashMap<PathKey, BuildTask>,
        is_initial_cycle: bool,
        configs: &[RootedFilePath],
    ) {
        for config in configs {
            let path = self.case_sensitivity.path_key(&config.as_path());
            let mut task = None;
            let mut build_info = None;
            if let Some(existing) = old_tasks.get_mut(&path) {
                if !existing.dirty {
                    // Reuse existing task if config is same — move it out of
                    // the old set so the post-generation cleanup does not
                    // close its content mapper project.
                    task = old_tasks.remove(&path);
                } else {
                    if let Some(project) = existing.content_mapper_project.take() {
                        let _ = project.close();
                    }
                    build_info = Some(existing.build_info_entry.clone());
                }
            }
            let mut task = task.unwrap_or_else(|| {
                let mut task = BuildTask::new(config.clone(), path.clone(), is_initial_cycle);
                task.build_info_entry = build_info.unwrap_or_default();
                task
            });
            // Go's `tasks.LoadOrStore` dedupe: shared subprojects already
            // inserted by an earlier config are skipped.
            if self.tasks_by_path.contains_key(&path) {
                continue;
            }
            task.resolved = self.host.get_resolved_project_reference(config, &path);
            task.up_stream.clear();
            let sub_configs = task
                .resolved
                .as_ref()
                .map(|resolved| resolved.resolved_project_reference_paths().clone())
                .unwrap_or_default();
            self.tasks_by_path.insert(path, self.tasks.len());
            self.tasks.push(task);
            self.create_build_tasks(old_tasks, is_initial_cycle, &sub_configs);
        }
    }

    /// `(o *Orchestrator) setupBuildTask`.
    #[allow(clippy::too_many_arguments)]
    fn setup_build_task(
        &mut self,
        config_name: &RootedFilePath,
        down_stream: Option<TaskId>,
        in_circular_context: bool,
        completed: &mut FxHashSet<PathKey>,
        analyzing: &mut FxHashSet<PathKey>,
        circularity_stack: &mut Vec<String>,
    ) -> Option<TaskId> {
        let path = self.case_sensitivity.path_key(&config_name.as_path());
        let task_id = self.get_task(&path);
        if !completed.contains(&path) {
            if analyzing.contains(&path) {
                if !in_circular_context {
                    self.errors.push(new_compiler_diagnostic(
                        &tsc_diagnostics::Project_references_may_not_form_a_circular_graph_Cycle_detected_Colon_0,
                        &[circularity_stack.join("\n")],
                    ));
                }
                return None;
            }
            analyzing.insert(path.clone());
            circularity_stack.push(config_name.as_string().to_string());
            if let Some(resolved) = self.tasks[task_id].resolved.clone() {
                for (index, sub_reference) in resolved
                    .resolved_project_reference_paths()
                    .iter()
                    .enumerate()
                {
                    let upstream = self.setup_build_task(
                        sub_reference,
                        Some(task_id),
                        in_circular_context || resolved.project_references()[index].circular,
                        completed,
                        analyzing,
                        circularity_stack,
                    );
                    if let Some(upstream) = upstream {
                        self.tasks[task_id].up_stream.push(UpstreamTask {
                            task: upstream,
                            ref_index: index,
                        });
                    }
                }
            }
            circularity_stack.pop();
            completed.insert(path);
            // `task.built`/`task.done = make(chan)` — channels dropped in the
            // sequential port.
            self.order.push(task_id);
        }
        if self.command_compiler_options().watch.is_true() {
            if let Some(down_stream) = down_stream {
                self.tasks[task_id].down_stream.push(down_stream);
            }
        }
        Some(task_id)
    }

    /// `(o *Orchestrator) GenerateGraphReusingOldTasks`.
    fn generate_graph_reusing_old_tasks(&mut self) {
        let old_tasks: FxHashMap<PathKey, BuildTask> = std::mem::take(&mut self.tasks)
            .into_iter()
            .map(|task| (task.path.clone(), task))
            .collect();
        self.tasks_by_path.clear();
        self.order.clear();
        self.errors.clear();
        self.generate_graph(Some(old_tasks));
    }

    /// `(o *Orchestrator) GenerateGraph` — `old_tasks` is Go's `oldTasks`
    /// (`None` is Go's nil map; `generate_graph_reusing_old_tasks` re-keys
    /// the previous `tasks` by path).
    fn generate_graph(&mut self, old_tasks: Option<FxHashMap<PathKey, BuildTask>>) {
        let is_initial_cycle = old_tasks.is_none();
        let mut old_tasks = old_tasks.unwrap_or_default();
        let projects = self.opts.command.resolved_project_paths().clone();
        // Parse all config files — sequentially (see the banner).
        self.create_build_tasks(&mut old_tasks, is_initial_cycle, &projects);

        // Generate the graph.
        let mut completed = FxHashSet::default();
        let mut analyzing = FxHashSet::default();
        let mut circularity_stack = Vec::new();
        for project in &projects {
            self.setup_build_task(
                project,
                None,
                false,
                &mut completed,
                &mut analyzing,
                &mut circularity_stack,
            );
        }
        self.schedule_order = self.compute_schedule_order();
        // Old tasks still in `old_tasks` were not reused — release their
        // content mapper projects (Go's `oldTasks.Range` cleanup checks
        // pointer identity against the new map; since reused tasks were
        // removed above, anything left is un-reused).
        for (_, mut old_task) in old_tasks {
            if let Some(project) = old_task.content_mapper_project.take() {
                let _ = project.close();
            }
        }
        self.graph_generated = true;
    }

    /// `(o *Orchestrator) computeScheduleOrder` — stable depth sort; Rust's
    /// `sort_by_key` is stable like Go's `slices.SortStableFunc`.
    fn compute_schedule_order(&self) -> Vec<TaskId> {
        let mut entries: Vec<(TaskId, usize)> = Vec::with_capacity(self.order.len());
        let mut depths: FxHashMap<TaskId, usize> = FxHashMap::default();
        for &task_id in &self.order {
            let mut depth = 0;
            for upstream in &self.tasks[task_id].up_stream {
                depth = depth.max(depths[&upstream.task] + 1);
            }
            depths.insert(task_id, depth);
            entries.push((task_id, depth));
        }
        entries.sort_by_key(|&(_, depth)| depth);
        entries.into_iter().map(|(task, _)| task).collect()
    }

    /// `(o *Orchestrator) recheckAllProjects`.
    fn recheck_all_projects(&mut self, project: &str) {
        if !self.graph_generated {
            return;
        }
        let Some(order) = self.get_build_order_for(project) else {
            return;
        };
        for task_id in order {
            self.tasks[task_id].reset_status();
            self.tasks[task_id].reset_config();
        }
        self.host.reset_mtime_cache();
        self.reset_caches();
    }

    /// `(o *Orchestrator) getBuildOrderFor` — `None` is Go's `ok == false`.
    fn get_build_order_for(&self, project: &str) -> Option<Vec<TaskId>> {
        if project.is_empty() {
            return Some(self.order.clone());
        }

        let config = resolve_config_file_name_of_project_reference(&to_rooted_path(
            project,
            &self.current_directory,
        ));
        let target = *self
            .tasks_by_path
            .get(&self.case_sensitivity.path_key(&config.as_path()))?;

        fn add_project_and_references(
            state: &OrchestratorState,
            task_id: TaskId,
            projects: &mut FxHashSet<PathKey>,
        ) {
            if !projects.insert(state.tasks[task_id].path.clone()) {
                return;
            }
            for upstream in &state.tasks[task_id].up_stream {
                add_project_and_references(state, upstream.task, projects);
            }
        }
        let mut projects = FxHashSet::default();
        add_project_and_references(self, target, &mut projects);

        Some(
            self.order
                .iter()
                .copied()
                .filter(|task_id| projects.contains(&self.tasks[*task_id].path))
                .collect(),
        )
    }

    /// `(o *Orchestrator) cleanProjectOutput` — returns Go's `deleted`.
    fn clean_project_output(
        &mut self,
        output_file: &RootedFilePath,
        inputs: &FxHashSet<PathKey>,
        dry: bool,
        files_to_delete: &mut Vec<RootedFilePath>,
        report_diagnostic: &DiagnosticReporter,
    ) -> bool {
        if output_file.as_string().is_empty()
            || inputs.contains(&self.case_sensitivity.path_key(&output_file.as_path()))
            || !self.host.fs().file_exists(output_file)
        {
            return false;
        }
        files_to_delete.push(output_file.clone());
        if dry {
            return false;
        }
        if self.host.fs().remove(&output_file.as_path()).is_err() {
            report_diagnostic(&new_compiler_diagnostic(
                &tsc_diagnostics::Failed_to_delete_file_0,
                &[output_file.as_string().to_string()],
            ));
            return false;
        }
        true
    }

    /// `(o *Orchestrator) updateWatch`.
    fn update_watch(&mut self) {
        let old_cache = self.host.m_times();
        self.host.reset_mtime_cache();
        for task_id in self.order.clone() {
            self.task_update_watch(task_id, &old_cache);
        }
    }

    /// `(o *Orchestrator) resetCaches` — `extendedConfigCache` and
    /// `sourceFiles` resets are deferred (see the PORT notes in `host.rs` —
    /// both caches hold `!Send` arenas and are not instantiated).
    fn reset_caches(&mut self) {
        // Clean out all the caches.
        self.host.cached_fs().clear_cache();
        self.host.reset_config_times();
    }

    /// `(o *Orchestrator) packageJsonLookupChanged`.
    fn package_json_lookup_changed(
        &self,
        package_json: &RootedFilePath,
        changed_paths: &FxHashMap<PathKey, EventKind>,
    ) -> bool {
        let package_json_path = self.case_sensitivity.path_key(&package_json.as_path());
        if changed_paths.contains_key(&package_json_path) {
            return true;
        }
        for (changed_path, kind) in changed_paths {
            if *kind == EventKind::Delete && changed_path.contains_path(&package_json_path) {
                return true;
            }
        }
        false
    }

    /// `(o *Orchestrator) checkTasksForEventChanges` — `needs_config_update`
    /// / `needs_update` are Go's `*atomic.Bool`s.
    fn check_tasks_for_event_changes(
        &mut self,
        changed_paths: &FxHashMap<RootedPath, EventKind>,
        needs_config_update: &mut bool,
        needs_update: &mut bool,
        lock: &WatchManagerLock<'_>,
    ) {
        let mut normalized_paths: FxHashMap<PathKey, EventKind> =
            FxHashMap::with_capacity_and_hasher(changed_paths.len(), Default::default());
        for (event_path, kind) in changed_paths {
            normalized_paths.insert(self.case_sensitivity.path_key(event_path), *kind);
        }

        for task_id in self.order.clone() {
            let path = self.tasks[task_id].path.clone();

            if normalized_paths.contains_key(&path) {
                self.tasks[task_id].reset_config();
                *needs_config_update = true;
                *needs_update = true;
                continue;
            }

            let Some(resolved) = self.tasks[task_id].resolved.clone() else {
                continue;
            };

            let mut config_changed = false;
            for file in resolved.extended_source_files() {
                let fp = self.case_sensitivity.path_key(&file.as_path());
                if normalized_paths.contains_key(&fp) {
                    self.tasks[task_id].reset_config();
                    *needs_config_update = true;
                    *needs_update = true;
                    config_changed = true;
                    break;
                }
            }
            if config_changed {
                continue;
            }
            for mapper in resolved.content_mappers() {
                if mapper.package_directory.as_string().is_empty()
                    || !mapper.contribution_id.is_empty()
                {
                    continue;
                }
                let manifest_path = self.case_sensitivity.path_key(
                    &mapper
                        .package_directory
                        .resolve_file("package.json")
                        .as_path(),
                );
                if normalized_paths.contains_key(&manifest_path) {
                    self.tasks[task_id].reset_config();
                    *needs_config_update = true;
                    *needs_update = true;
                    config_changed = true;
                    break;
                }
            }
            if config_changed {
                continue;
            }

            let mut root_changed = false;
            if let Some(project) = self.tasks[task_id].content_mapper_project.clone() {
                match project.watched_files() {
                    Err(err) => {
                        self.tasks[task_id].content_mapper_project_err = Some(Arc::new(err));
                        self.tasks[task_id].reset_status();
                        *needs_update = true;
                        root_changed = true;
                    }
                    Ok(watched_files) => {
                        for file_name in watched_files {
                            if normalized_paths
                                .contains_key(&self.case_sensitivity.path_key(&file_name.as_path()))
                            {
                                self.tasks[task_id].refresh_content_mapper_project();
                                self.tasks[task_id].reset_status();
                                *needs_update = true;
                                root_changed = true;
                                break;
                            }
                        }
                    }
                }
            }
            let file_names = resolved.file_names();
            let mut roots: FxHashSet<PathKey> =
                FxHashSet::with_capacity_and_hasher(file_names.len(), Default::default());
            for file in file_names {
                let fp = self.case_sensitivity.path_key(&file.as_path());
                roots.insert(fp.clone());
                if !root_changed && normalized_paths.contains_key(&fp) {
                    self.tasks[task_id].reset_status();
                    *needs_update = true;
                    root_changed = true;
                }
            }

            if !root_changed {
                let build_info = self.tasks[task_id]
                    .build_info_entry
                    .borrow()
                    .as_ref()
                    .and_then(|entry| entry.build_info.clone());
                if let Some(build_info) = build_info {
                    let build_info_dir = self.tasks[task_id]
                        .build_info_entry
                        .borrow()
                        .as_ref()
                        .expect("buildInfoEntry")
                        .file_name
                        .directory();
                    for file_name in &build_info.file_names {
                        let fp = self.case_sensitivity.path_key(
                            &crate::incremental::build_info::resolve_build_info_file_name(
                                file_name,
                                &build_info_dir,
                                self.host.default_library_path(),
                            )
                            .as_path(),
                        );
                        if roots.contains(&fp) {
                            continue;
                        }
                        if normalized_paths.contains_key(&fp) {
                            self.tasks[task_id].reset_status();
                            *needs_update = true;
                            break;
                        }
                    }
                    for package_json in build_info.get_package_jsons(&build_info_dir) {
                        if self.package_json_lookup_changed(&package_json, &normalized_paths) {
                            self.tasks[task_id].reset_status();
                            *needs_update = true;
                            break;
                        }
                    }
                    for package_json in build_info.get_missing_package_jsons(&build_info_dir) {
                        if self.package_json_lookup_changed(&package_json, &normalized_paths) {
                            self.tasks[task_id].reset_status();
                            *needs_update = true;
                            break;
                        }
                    }
                }
                for package_json in self.tasks[task_id].package_jsons.clone() {
                    if self.package_json_lookup_changed(&package_json, &normalized_paths) {
                        self.tasks[task_id].reset_status();
                        *needs_update = true;
                        break;
                    }
                }
            }

            // `task.built`/`task.done = make(chan)` — channels dropped in the
            // sequential port.

            let new_config = resolved.reload_file_names_of_parsed_command_line(self.host.fs());
            if resolved.file_names() != new_config.file_names() {
                // Go stores `newConfig` in `host.resolvedReferences` — that
                // cache is deferred (`!Send`; see `host.rs`), so the fresh
                // parse is only stored on the task.
                self.tasks[task_id].resolved = Some(Arc::new(new_config));
                self.tasks[task_id].reset_status();
                *needs_update = true;
            }
        }

        if !*needs_update {
            for event_path in changed_paths.keys() {
                if self
                    .host
                    .fs()
                    .directory_exists(&rooted_directory_path_from_path(event_path.clone()))
                {
                    if lock.is_path_under_watch(event_path) {
                        for task_id in self.order.clone() {
                            self.tasks[task_id].reset_status();
                            // `task.built`/`task.done` — channels dropped.
                        }
                        *needs_update = true;
                        break;
                    }
                }
            }
        }
    }

    /// `(o *Orchestrator) addWatchDir`.
    fn add_watch_dir(&self, desired_dirs: &mut DirWatchSet, dir: &RootedDirectoryPath) {
        if !desired_dirs.covered(dir) && can_watch_directory(dir) {
            desired_dirs.set(dir.clone(), false);
        }
    }

    /// `(o *Orchestrator) addProgramFileWatchDir` — watches a program file's
    /// directory at any depth, unlike `add_watch_dir` which guards lookup
    /// locations against watching something as generic as / or /home.
    fn add_program_file_watch_dir(&self, desired_dirs: &mut DirWatchSet, dir: RootedDirectoryPath) {
        if !desired_dirs.covered(&dir) {
            desired_dirs.set(dir, false);
        }
    }

    /// `(o *Orchestrator) addPackageJsonWatchDirs`.
    fn add_package_json_watch_dirs(
        &self,
        desired_dirs: &mut DirWatchSet,
        package_json: &RootedFilePath,
    ) {
        let dir = package_json.directory();
        let mut dirs = vec![dir.clone()];
        let mut found_node_modules = false;
        let mut current = dir.clone();
        loop {
            let parent = current.as_path().directory();
            if parent.as_string().is_empty() || parent == current {
                break;
            }
            dirs.push(parent.clone());
            if parent.base_name() == "node_modules" {
                found_node_modules = true;
                let grandparent = parent.as_path().directory();
                if !grandparent.as_string().is_empty() && grandparent != parent {
                    dirs.push(grandparent);
                }
                break;
            }
            current = parent;
        }

        if !found_node_modules {
            self.add_watch_dir(desired_dirs, &dir);
            return;
        }
        for dir in dirs {
            self.add_watch_dir(desired_dirs, &dir);
        }
    }

    /// `(o *Orchestrator) computeDesiredWatches` — `&mut self` because Go
    /// assigns `task.contentMapperProjectErr` inside the loop.
    fn compute_desired_watches(
        &mut self,
        wm: &WatchManager,
    ) -> FxHashMap<RootedDirectoryPath, bool> {
        let mut desired_dirs = new_dir_watch_set(self.case_sensitivity);

        for task_id in self.order.clone() {
            // Watch config file directory.
            let config_dir = self.tasks[task_id].config.directory();
            let real_config_dir =
                rooted_directory_path_from_path(self.host.fs().realpath(&config_dir.as_path()));
            desired_dirs.set(real_config_dir, false);

            let Some(resolved) = self.tasks[task_id].resolved.clone() else {
                continue;
            };

            // Extended config file directories.
            for cfg_path in resolved.extended_source_files() {
                let real_path = self.host.fs().realpath(&cfg_path.as_path());
                desired_dirs.set(real_path.directory(), false);
            }

            // Wildcard directories from tsconfig.
            if let Some(wildcard_directories) = resolved.wildcard_directories() {
                for (dir, recursive) in wildcard_directories {
                    let real_dir =
                        rooted_directory_path_from_path(self.host.fs().realpath(&dir.as_path()));
                    desired_dirs.set(real_dir, *recursive);
                }
            }

            // Input file directories not already covered.
            for file_name in resolved.file_names() {
                self.add_program_file_watch_dir(&mut desired_dirs, file_name.directory());
                for mapper in resolved.content_mappers() {
                    if mapper.package_directory.as_string().is_empty()
                        || !mapper.contribution_id.is_empty()
                    {
                        continue;
                    }
                    let dir = &mapper.package_directory;
                    if !desired_dirs.covered(dir) && can_watch_directory(dir) {
                        desired_dirs.set(dir.clone(), false);
                    }
                }
            }
            if let Some(project) = self.tasks[task_id].content_mapper_project.clone() {
                match project.watched_files() {
                    Err(err) => {
                        // `task.contentMapperProjectErr = err`.
                        self.tasks[task_id].content_mapper_project_err = Some(Arc::new(err));
                    }
                    Ok(watched_files) => {
                        for file_name in watched_files {
                            let dir = self.host.fs().realpath(&file_name.as_path()).directory();
                            if !desired_dirs.covered(&dir) && can_watch_directory(&dir) {
                                desired_dirs.set(dir, false);
                            }
                        }
                    }
                }
            }

            // Non-root dependency directories from buildinfo (e.g.
            // node_modules .d.ts files).
            let build_info_entry = self.tasks[task_id].build_info_entry.clone();
            let build_info = build_info_entry
                .borrow()
                .as_ref()
                .and_then(|entry| entry.build_info.clone());
            if let Some(build_info) = build_info {
                let build_info_dir = build_info_entry
                    .borrow()
                    .as_ref()
                    .expect("buildInfoEntry")
                    .file_name
                    .directory();
                let roots: FxHashSet<PathKey> = resolved
                    .file_names()
                    .iter()
                    .map(|file_name| self.case_sensitivity.path_key(&file_name.as_path()))
                    .collect();
                for file_name in &build_info.file_names {
                    let abs_path = self.host.fs().realpath(
                        &crate::incremental::build_info::resolve_build_info_file_name(
                            file_name,
                            &build_info_dir,
                            self.host.default_library_path(),
                        )
                        .as_path(),
                    );
                    let fp = self.case_sensitivity.path_key(&abs_path);
                    if roots.contains(&fp) {
                        continue;
                    }
                    self.add_program_file_watch_dir(&mut desired_dirs, abs_path.directory());
                }
                for package_json in build_info.get_package_jsons(&build_info_dir) {
                    self.add_package_json_watch_dirs(&mut desired_dirs, &package_json);
                }
                for package_json in build_info.get_missing_package_jsons(&build_info_dir) {
                    self.add_package_json_watch_dirs(&mut desired_dirs, &package_json);
                }
            }
            for package_json in self.tasks[task_id].package_jsons.clone() {
                self.add_package_json_watch_dirs(&mut desired_dirs, &package_json);
            }
        }

        wm.resolve_desired_dirs(desired_dirs.dirs())
    }

    /// `(o *Orchestrator) getWriter`.
    fn get_writer(&self, task: Option<TaskId>) -> SharedWriter {
        match task {
            None => self.opts.sys.writer(),
            Some(task_id) => SharedWriter::new(
                self.tasks[task_id]
                    .result
                    .as_ref()
                    .expect("task result")
                    .builder
                    .clone(),
            ),
        }
    }

    /// `(o *Orchestrator) createBuilderStatusReporter`.
    fn create_builder_status_reporter_for(&self, task: Option<TaskId>) -> DiagnosticReporter {
        create_builder_status_reporter(
            &self.opts.sys,
            self.get_writer(task),
            self.command_locale(),
            self.opts.command.compiler_options.as_ref(),
            self.opts.testing.as_ref(),
        )
    }

    /// `(o *Orchestrator) createDiagnosticReporter`.
    fn create_diagnostic_reporter_for(&self, task: Option<TaskId>) -> DiagnosticReporter {
        create_diagnostic_reporter(
            &self.opts.sys,
            self.get_writer(task),
            self.command_locale(),
            self.opts.command.compiler_options.as_ref(),
        )
    }

    /// `(o *Orchestrator) buildOrCleanProject` — `close(task.built)` is a
    /// no-op in the sequential port.
    fn build_or_clean_project(&mut self, task_id: TaskId) {
        let builder = TaskBuffer::default();
        self.tasks[task_id].result = Some(TaskResult::new(
            builder,
            self.create_builder_status_reporter_for(Some(task_id)),
            self.create_diagnostic_reporter_for(Some(task_id)),
        ));
        if !self.build_options().clean.is_true() {
            self.build_project(task_id);
        } else {
            self.clean_project(task_id);
        }
        if self.opts.testing.is_none() {
            // The program is only needed by `Testing::on_program` at report
            // time; drop it now so a task that has finished but is not yet
            // reported does not keep its program alive.
            if let Some(result) = &mut self.tasks[task_id].result {
                result.program = None;
            }
        }
    }

    /// `(o *Orchestrator) buildOrClean`.
    fn build_or_clean(&mut self) -> CommandLineResult {
        let order = self.order.clone();
        self.build_or_clean_order(&order).result
    }

    /// `(o *Orchestrator) buildOrCleanOrder` — Go reports from a goroutine
    /// waiting on each task's `built` channel; sequentially, tasks are run in
    /// `order` first and reported in `order` afterwards.
    fn build_or_clean_order(&mut self, order: &[TaskId]) -> OrchestratorResult {
        if !self.build_options().clean.is_true() && self.build_options().verbose.is_true() {
            let reporter = self.create_builder_status_reporter_for(None);
            let list = order
                .iter()
                .map(|&task_id| {
                    format!(
                        "\r\n    * {}",
                        self.relative_file_name(&self.tasks[task_id].config)
                    )
                })
                .collect::<String>();
            reporter(&new_compiler_diagnostic(
                &tsc_diagnostics::Projects_in_this_build_Colon_0,
                &[list],
            ));
        }
        let mut build_result = OrchestratorResult::default();
        if self.errors.is_empty() {
            build_result.statistics.projects = order.len() as i32;
            for &task_id in order {
                self.build_or_clean_project(task_id);
            }
            // Results are reported in Order() — sequentially this is a
            // second pass over the same slice.
            for &task_id in order {
                self.task_report(task_id, &mut build_result);
            }
        } else {
            // Circularity errors prevent any project from being built.
            build_result.result.status = ExitStatus::ProjectReferenceCycleOutputsSkipped;
            let report_diagnostic = self.create_diagnostic_reporter_for(None);
            for err in self.errors.clone() {
                report_diagnostic(&err);
            }
            build_result.errors = self.errors.clone();
        }
        self.report_result(&mut build_result, true);
        build_result
    }

    /// `(b *OrchestratorResult) report`/`reportWithFilesToDelete`.
    fn report_result(&self, result: &mut OrchestratorResult, report_files_to_delete: bool) {
        if self.command_compiler_options().watch.is_true() {
            if let Some(reporter) = &self.watch_status_reporter {
                reporter(&new_compiler_diagnostic(
                    if_else(
                        result.errors.len() == 1,
                        &tsc_diagnostics::Found_1_error_Watching_for_file_changes,
                        &tsc_diagnostics::Found_0_errors_Watching_for_file_changes,
                    ),
                    &[result.errors.len().to_string()],
                ));
            }
        } else if let Some(reporter) = &self.error_summary_reporter {
            reporter(&result.errors);
        }
        if report_files_to_delete && !result.files_to_delete.is_empty() {
            let reporter = self.create_builder_status_reporter_for(None);
            reporter(&new_compiler_diagnostic(
                &tsc_diagnostics::A_non_dry_build_would_delete_the_following_files_Colon_0,
                &[result
                    .files_to_delete
                    .iter()
                    .map(|f| format!("\r\n * {}", f.as_string()))
                    .collect::<String>()],
            ));
        }
        if !self.command_compiler_options().diagnostics.is_true()
            && !self
                .command_compiler_options()
                .extended_diagnostics
                .is_true()
        {
            return;
        }
        result
            .statistics
            .set_total_time(self.opts.sys.since_start());
        result.statistics.report(
            &mut *self.opts.sys.writer().guard(),
            self.opts.testing.as_ref(),
        );
    }

    /// `(o *Orchestrator) clean`.
    fn clean(&mut self, project: &str, only_references: bool) -> OrchestratorResult {
        if !self.graph_generated {
            self.generate_graph(None);
        }
        if !self.errors.is_empty() {
            let mut result = OrchestratorResult {
                result: CommandLineResult {
                    status: ExitStatus::ProjectReferenceCycleOutputsSkipped,
                    watcher: None,
                },
                errors: self.errors.clone(),
                ..Default::default()
            };
            self.report_result(&mut result, true);
            return result;
        }

        let Some(mut order) = self.get_build_order_for(project) else {
            return OrchestratorResult {
                result: CommandLineResult {
                    status: ExitStatus::InvalidProjectOutputsSkipped,
                    watcher: None,
                },
                ..Default::default()
            };
        };
        if only_references {
            order.pop();
        }

        let mut result = OrchestratorResult::default();
        result.statistics.projects = order.len() as i32;
        let dry = self.build_options().dry.is_true();
        let report_diagnostic = self.create_diagnostic_reporter_for(None);
        for task_id in order {
            let Some(resolved) = self.tasks[task_id].resolved.clone() else {
                let diagnostic = new_compiler_diagnostic(
                    &tsc_diagnostics::File_0_not_found,
                    &[self.tasks[task_id].config.as_string().to_string()],
                );
                report_diagnostic(&diagnostic);
                result.errors.push(diagnostic);
                continue;
            };

            let inputs: FxHashSet<PathKey> = resolved
                .file_names()
                .iter()
                .map(|file_name| self.case_sensitivity.path_key(&file_name.as_path()))
                .collect();
            let mut deleted = false;
            for output_file in resolved.get_output_file_names() {
                deleted = self.clean_project_output(
                    &output_file,
                    &inputs,
                    dry,
                    &mut result.files_to_delete,
                    &report_diagnostic,
                ) || deleted;
            }
            deleted = self.clean_project_output(
                &resolved.get_build_info_file_name(),
                &inputs,
                dry,
                &mut result.files_to_delete,
                &report_diagnostic,
            ) || deleted;
            if deleted {
                self.tasks[task_id].reset_status();
                *self.tasks[task_id].build_info_entry.borrow_mut() = None;
            }
        }

        self.report_result(&mut result, dry);
        result
    }

    /// `(o *Orchestrator) DoCycle` — must be called under the
    /// [`WatchManagerLock`].
    fn do_cycle(&mut self, wm: &Arc<WatchManager>, lock: &mut WatchManagerLock<'_>) {
        let (changed_paths, overflow) = wm.drain_events();
        let has_events = changed_paths
            .as_ref()
            .is_some_and(|paths| !paths.is_empty())
            || overflow;

        if !has_events {
            if let Some(writer) = wm.debug_log.lock().unwrap().as_mut() {
                let _ = writeln!(writer, "[watch] DoCycle: no events, skipping");
            }
            return;
        }

        let mut needs_config_update = false;
        let mut needs_update = false;

        if overflow {
            // Overflow: reset all tasks to force a full rebuild.
            for task_id in self.order.clone() {
                self.tasks[task_id].reset_config();
            }
            needs_config_update = true;
            needs_update = true;
        } else {
            // Event-driven: check only tasks affected by changed paths.
            self.check_tasks_for_event_changes(
                changed_paths.as_ref().expect("changed_paths"),
                &mut needs_config_update,
                &mut needs_update,
                lock,
            );
        }

        if !needs_update {
            self.reset_caches();
            return;
        }

        if let Some(reporter) = &self.watch_status_reporter {
            reporter(&new_compiler_diagnostic(
                &tsc_diagnostics::File_change_detected_Starting_incremental_compilation,
                &[] as &[String],
            ));
        }
        if needs_config_update {
            // Generate new tasks.
            self.generate_graph_reusing_old_tasks();
        }

        self.build_or_clean();
        self.update_watch();
        let desired_dirs = self.compute_desired_watches(wm);
        if let Err(err) = lock.reconcile_watches(desired_dirs) {
            let writer = self.opts.sys.writer();
            let _ = writeln!(writer.guard(), "{err}");
            // Mark overflow so the next event triggers a full rebuild.
            wm.force_overflow();
        }
        self.reset_caches();
    }
}

/// `type Orchestrator struct`.
///
/// Go's `*Orchestrator` is shared with watchers (`result.Result.Watcher = o`)
/// and `DoCycle` runs on the watch loop — the port keeps the mutable state in
/// a `RefCell` so `Watcher::do_cycle(&self)` can borrow it, and the
/// `WatchManager` outside it (it is internally synchronized).
pub struct Orchestrator {
    state: RefCell<OrchestratorState>,
    /// `wm`.
    wm: Arc<WatchManager>,
}

impl Orchestrator {
    /// `o.opts.Sys` reach-through for `start`'s watch check without a second
    /// borrow.
    fn is_watch(&self) -> bool {
        self.state
            .borrow()
            .command_compiler_options()
            .watch
            .is_true()
    }
}

impl Orchestrator {
    /// `(o *Orchestrator) Order`.
    pub fn order(&self) -> Vec<RootedFilePath> {
        let state = self.state.borrow();
        state
            .order
            .iter()
            .map(|&task_id| state.tasks[task_id].config.clone())
            .collect()
    }

    /// `(o *Orchestrator) ScheduleOrder` — the build order stably sorted by
    /// dependency depth.
    pub fn schedule_order(&self) -> Vec<String> {
        let state = self.state.borrow();
        state
            .schedule_order
            .iter()
            .map(|&task_id| state.tasks[task_id].config.as_string().to_string())
            .collect()
    }

    /// `(o *Orchestrator) Upstream`.
    pub fn upstream(&self, config_name: &str) -> Vec<String> {
        let state = self.state.borrow();
        let path = state
            .case_sensitivity
            .path_key(&to_rooted_path(config_name, &state.current_directory));
        let task_id = state.get_task(&path);
        state.tasks[task_id]
            .up_stream
            .iter()
            .map(|upstream| state.tasks[upstream.task].config.as_string().to_string())
            .collect()
    }

    /// `(o *Orchestrator) Downstream`.
    pub fn downstream(&self, config_name: &str) -> Vec<String> {
        let state = self.state.borrow();
        let path = state
            .case_sensitivity
            .path_key(&to_rooted_path(config_name, &state.current_directory));
        let task_id = state.get_task(&path);
        state.tasks[task_id]
            .down_stream
            .iter()
            .map(|&task_id| state.tasks[task_id].config.as_string().to_string())
            .collect()
    }

    /// `(o *Orchestrator) Start` — the `tsc -b` entrypoint.
    pub fn start(self: &Arc<Self>, ctx: &Context) -> CommandLineResult {
        self.start_inner(ctx, "", false).result
    }

    /// `(o *Orchestrator) Build` — orchestrator.Build() entrypoint for api.
    pub fn build(self: &Arc<Self>, ctx: &Context, project: &str) -> OrchestratorResult {
        self.state.borrow_mut().recheck_all_projects(project);
        self.start_inner(ctx, project, false)
    }

    /// `(o *Orchestrator) BuildReferences`.
    pub fn build_references(self: &Arc<Self>, ctx: &Context, project: &str) -> OrchestratorResult {
        self.state.borrow_mut().recheck_all_projects(project);
        self.start_inner(ctx, project, true)
    }

    /// `(o *Orchestrator) Clean`.
    pub fn clean(&self, project: &str) -> OrchestratorResult {
        self.state.borrow_mut().clean(project, false)
    }

    /// `(o *Orchestrator) CleanReferences`.
    pub fn clean_references(&self, project: &str) -> OrchestratorResult {
        self.state.borrow_mut().clean(project, true)
    }

    /// `(o *Orchestrator) start`.
    fn start_inner(
        self: &Arc<Self>,
        ctx: &Context,
        project: &str,
        only_references: bool,
    ) -> OrchestratorResult {
        let (mut result, content_mapper_host_to_close) = {
            let mut state = self.state.borrow_mut();
            state.content_mapper_host = crate::tsc::new_content_mapper_host(
                ctx,
                &state.opts.sys,
                state.command_compiler_options(),
            );
            // Go `defer o.contentMapperHost.Close()` — fires after `Watch`'s
            // run loop returns, i.e. when `start` returns.
            let close_after = state.content_mapper_host.is_some()
                && (!state.command_compiler_options().watch.is_true()
                    || state.opts.testing.is_none());
            let host_to_close = if_else(close_after, state.content_mapper_host.clone(), None);
            if state.command_compiler_options().watch.is_true() {
                if let Some(reporter) = &state.watch_status_reporter {
                    reporter(&new_compiler_diagnostic(
                        &tsc_diagnostics::Starting_compilation_in_watch_mode,
                        &[] as &[String],
                    ));
                }
            }
            if state.graph_generated {
                state.generate_graph_reusing_old_tasks();
            } else {
                state.generate_graph(None);
            }
            let Some(order) = state.get_build_order_for(project) else {
                if let Some(host) = host_to_close {
                    let _ = host.close();
                }
                return OrchestratorResult {
                    result: CommandLineResult {
                        status: ExitStatus::InvalidProjectOutputsSkipped,
                        watcher: None,
                    },
                    ..Default::default()
                };
            };
            let mut order = order;
            if only_references && state.errors.is_empty() {
                if project.is_empty() {
                    if let Some(host) = host_to_close {
                        let _ = host.close();
                    }
                    return OrchestratorResult {
                        result: CommandLineResult {
                            status: ExitStatus::InvalidProjectOutputsSkipped,
                            watcher: None,
                        },
                        ..Default::default()
                    };
                }
                order.pop();
            }
            (state.build_or_clean_order(&order), host_to_close)
        };
        if self.is_watch() {
            self.watch(ctx);
            // `result.Result.Watcher = o`.
            let watcher: Arc<dyn Watcher> = self.clone();
            result.result.watcher = Some(watcher);
        }
        if let Some(host) = content_mapper_host_to_close {
            let _ = host.close();
        }
        result
    }

    /// `(o *Orchestrator) Watch` — the initial `updateWatch`/reconcile pass
    /// runs under the watch-manager lock; `run_loop` runs outside it (Go's
    /// `wm.RunLoop(ctx, o.DoCycle)` after `Unlock`).
    fn watch(self: &Arc<Self>, ctx: &Context) {
        {
            let mut lock = self.wm.lock();
            let mut state = self.state.borrow_mut();

            if state.opts.testing.is_none() {
                if let Some(value) = state.opts.sys.environment_variable("TS_WATCH_DEBUG") {
                    if !value.is_empty() {
                        *self.wm.debug_log.lock().unwrap() =
                            Some(Box::new(state.opts.sys.writer()));
                    }
                }
                lock.ensure_default_backend();
            }

            state.update_watch();
            let desired_dirs = state.compute_desired_watches(&self.wm);
            if let Err(err) = lock.reconcile_watches(desired_dirs) {
                let writer = state.opts.sys.writer();
                let _ = writeln!(writer.guard(), "{err}");
                self.wm.force_overflow();
            }
            state.reset_caches();
        }

        if self.state.borrow().opts.testing.is_none() {
            let this = self.clone();
            self.wm.run_loop(ctx, move || this.do_cycle());
        }
    }
}

/// `var _ tsc.Watcher = (*Orchestrator)(nil)`.
impl Watcher for Orchestrator {
    /// `(o *Orchestrator) DoCycle`.
    fn do_cycle(&self) {
        let mut lock = self.wm.lock();
        let mut state = self.state.borrow_mut();
        state.do_cycle(&self.wm, &mut lock);
    }
}

/// `NewOrchestrator`.
pub fn new_orchestrator(opts: Options) -> Arc<Orchestrator> {
    let current_directory = opts.sys.current_directory();
    let fs = opts.sys.fs();
    let case_sensitivity = fs.case_sensitivity();
    let dir_exists_fs = fs.clone();
    let wm = new_watch_manager(
        Box::new(opts.sys.writer()),
        move |dir: &RootedDirectoryPath| dir_exists_fs.directory_exists(dir),
        case_sensitivity,
    );
    // `compiler.NewCachedFSCompilerHost` — keep a handle to the cached FS
    // for `resetCaches`'s `ClearCache` (Go downcasts `h.host.FS()`).
    let cached_fs = cachedvfs::from(fs);
    let compiler_host_vfs: Arc<dyn Vfs> = cached_fs.clone();
    let host = Arc::new(BuildHost::new(
        new_compiler_host(
            compiler_host_vfs,
            opts.sys.default_library_path(),
            None,
            None,
            None,
        ),
        cached_fs,
        opts.sys.clone(),
        opts.command.clone(),
        case_sensitivity,
    ));
    let (watch_status_reporter, error_summary_reporter) = if opts
        .command
        .compiler_options
        .as_ref()
        .expect("compiler options")
        .watch
        .is_true()
    {
        let reporter = create_watch_status_reporter(
            &opts.sys,
            opts.command.locale().clone(),
            opts.command.compiler_options.as_ref(),
            opts.testing.as_ref(),
        );
        if let Some(backend) = opts.testing.as_ref().and_then(|t| t.watch_backend()) {
            wm.set_backend(backend);
        }
        (Some(reporter), None)
    } else {
        (
            None,
            Some(create_report_error_summary(
                &opts.sys,
                opts.command.locale().clone(),
                opts.command.compiler_options.as_ref(),
            )),
        )
    };
    Arc::new(Orchestrator {
        state: RefCell::new(OrchestratorState {
            opts,
            current_directory,
            case_sensitivity,
            host,
            content_mapper_host: None,
            tasks: Vec::new(),
            tasks_by_path: FxHashMap::default(),
            order: Vec::new(),
            errors: Vec::new(),
            graph_generated: false,
            error_summary_reporter,
            watch_status_reporter,
            schedule_order: Vec::new(),
        }),
        wm,
    })
}
