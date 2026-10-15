// Ported from tsc/internal/project/projectcollection.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `ProjectCollection` carries the Go struct's fields plus the read-only
// accessors the snapshot layer calls (`projects`, `synthetic_projects`,
// `get_default_project`, `get_language_service_projects_containing_file`,
// `get_project`). Mutation happens on
// `projectcollectionbuilder.rs`'s builder; `shallow_clone` + `finalize`
// produce the next collection.

use std::rc::Rc;
use std::sync::{Arc, OnceLock};

use rustc_hash::FxHashMap;
use tsc_collections::{Set, SyncSet};
use tsc_tspath::{CaseSensitivity, PathKey, RootedFilePath};

use crate::configfileregistry::ConfigFileRegistry;
use crate::project::{
    ConfiguredProjectId, Id, Project, configured_project_id_from_path_key,
};

/// `apiOpenedFile` tracks a file kept open by API clients along with its
/// ref count.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ApiOpenedFile {
    pub file_name: RootedFilePath,
    pub ref_count: i32,
}

/// `APIState` tracks the projects and files that API clients have
/// explicitly opened. Opens and closes are ref-counted so multiple API
/// clients don't clobber each other, and it is carried across snapshots so
/// API-opened resources stay loaded.
#[derive(Clone, Default)]
pub struct ApiState {
    /// `openProjects` — the ref-counted set of projects to keep open for
    /// API clients, keyed by config file path. The value is the number of
    /// outstanding API opens.
    pub open_projects: FxHashMap<PathKey, i32>,
    /// `openFiles` — the ref-counted set of files to keep open for API
    /// clients, keyed by file path. Files with no configured project are
    /// loaded into the inferred project.
    pub open_files: FxHashMap<PathKey, ApiOpenedFile>,
}

impl ApiState {
    /// `s.clone()` — `maps.Clone` of both fields; `Clone::clone` on the
    /// hash maps already produces deep value copies.
    pub fn clone_state(&self) -> ApiState {
        self.clone()
    }

    /// `s.equals(other)` — `maps.Equal` of both fields.
    pub fn equals(&self, other: &ApiState) -> bool {
        self.open_projects == other.open_projects && self.open_files == other.open_files
    }
}

/// `openFilePaths` — the set of open file paths from the snapshot's
/// overlays.
pub fn open_file_paths(
    overlays: &FxHashMap<PathKey, Arc<crate::overlayfs::Overlay>>,
) -> Set<PathKey> {
    let mut open_files = Set::new();
    for path in overlays.keys() {
        open_files.add(path.clone());
    }
    open_files
}

/// `ProjectCollection`.
///
/// PORT: `*Project` becomes `Rc<Project>` (projects are shared between
/// consecutive immutable snapshots on a single thread — see the PORT note
/// in `checkerpool.rs`).
pub struct ProjectCollection {
    pub case_sensitivity: CaseSensitivity,
    pub config_file_registry: Option<ConfigFileRegistry>,
    /// `fileDefaultProjects` maps file paths to the ID of the default
    /// project for that file — quick lookups for only the associations
    /// discovered during the latest snapshot update.
    pub file_default_projects: FxHashMap<PathKey, Id>,
    /// `configuredProjects` — loaded projects associated with a tsconfig
    /// file, keyed by the config file path.
    pub configured_projects: FxHashMap<ConfiguredProjectId, Rc<Project>>,
    /// `syntheticProjects` — synthetic projects created explicitly through
    /// the API.
    pub synthetic_projects: FxHashMap<crate::project::SyntheticProjectId, Rc<Project>>,
    /// `openFiles` — the set of open file paths associated with the
    /// snapshot that owns this project collection.
    pub open_files: Set<PathKey>,
    /// `inferredProject` — fallback project used when no configured
    /// project can be found for an open file.
    pub inferred_project: Option<Rc<Project>>,
    /// `apiState` tracks the projects and files that API clients have
    /// explicitly opened so they are kept loaded across snapshots.
    pub api_state: ApiState,

    /// `openConfiguredProjectsOnce` — `pub(crate)` so `snapshothost.rs`
    /// can construct the empty collection for the root snapshot.
    pub(crate) open_configured_projects: OnceLock<Set<ConfiguredProjectId>>,
}

impl ProjectCollection {
    /// `ConfigFileRegistry()`.
    pub fn config_file_registry(&self) -> Option<&ConfigFileRegistry> {
        self.config_file_registry.as_ref()
    }

    /// `ConfiguredProject`.
    pub fn configured_project(&self, path: &PathKey) -> Option<&Rc<Project>> {
        self.configured_projects
            .get(&configured_project_id_from_path_key(path))
    }

    /// `GetProject`.
    pub fn get_project(&self, id: &Id) -> Option<&Rc<Project>> {
        if id.inferred().is_some() {
            return self.inferred_project.as_ref();
        }
        if let Some(synthetic_id) = id.synthetic() {
            return self.synthetic_projects.get(&synthetic_id);
        }
        if let Some(configured_id) = id.configured() {
            return self.configured_projects.get(&configured_id);
        }
        None
    }

    /// `fillConfiguredProjects` — configured projects in stable (ID) order.
    fn fill_configured_projects(&self, projects: &mut Vec<Rc<Project>>) {
        projects.extend(self.configured_projects.values().cloned());
        projects.sort_by(|a, b| a.id.cmp(&b.id));
    }

    /// `ConfiguredProjects` returns all configured projects in a stable
    /// order.
    pub fn configured_projects(&self) -> Vec<Rc<Project>> {
        let mut projects = Vec::with_capacity(self.configured_projects.len());
        self.fill_configured_projects(&mut projects);
        projects
    }

    /// `SyntheticProjects` returns all synthetic projects in a stable
    /// order.
    pub fn synthetic_projects(&self) -> Vec<Rc<Project>> {
        let mut projects: Vec<Rc<Project>> = self.synthetic_projects.values().cloned().collect();
        projects.sort_by(|a, b| a.id.cmp(&b.id));
        projects
    }

    /// `ProjectsByID` returns all projects keyed by project ID in stable
    /// order.
    pub fn projects_by_id(&self) -> Vec<(Id, Rc<Project>)> {
        let mut projects =
            Vec::with_capacity(self.configured_projects.len() + self.synthetic_projects.len() + 1);
        for project in self.configured_projects() {
            projects.push((project.id.clone(), project));
        }
        for project in self.synthetic_projects() {
            projects.push((project.id.clone(), project));
        }
        if let Some(inferred) = &self.inferred_project {
            projects.push((inferred.id.clone(), inferred.clone()));
        }
        projects
    }

    /// `Projects` returns all configured, synthetic, and inferred projects
    /// in a stable order.
    pub fn projects(&self) -> Vec<Rc<Project>> {
        let mut projects = Vec::with_capacity(
            self.configured_projects.len()
                + self.synthetic_projects.len()
                + usize::from(self.inferred_project.is_some()),
        );
        self.fill_configured_projects(&mut projects);
        projects.extend(self.synthetic_projects());
        if let Some(inferred) = &self.inferred_project {
            projects.push(inferred.clone());
        }
        projects
    }

    /// `LanguageServiceProjects` returns configured and inferred projects
    /// in stable order. Synthetic projects are accessed explicitly through
    /// the API and do not participate in cross-project language service
    /// operations.
    pub fn language_service_projects(&self) -> Vec<Rc<Project>> {
        let mut projects =
            Vec::with_capacity(self.configured_projects.len() + 1);
        self.fill_configured_projects(&mut projects);
        if let Some(inferred) = &self.inferred_project {
            projects.push(inferred.clone());
        }
        projects
    }

    /// `InferredProject`.
    pub fn inferred_project(&self) -> Option<&Rc<Project>> {
        self.inferred_project.as_ref()
    }

    /// `GetLanguageServiceProjectsContainingFile` does not consider
    /// synthetic projects (ones created by API via `createProgram`).
    ///
    /// PORT: Go returns `[]ls.Project`; until the `tsc-ls` sibling crate
    /// compiles, `Rc<Project>` stands in for the `ls.Project` interface.
    pub fn get_language_service_projects_containing_file(
        &self,
        path: &PathKey,
    ) -> Vec<Rc<Project>> {
        let mut projects = Vec::new();
        for project in self.configured_projects() {
            if project.contains_file(path) {
                projects.push(project);
            }
        }
        if let Some(inferred) = &self.inferred_project {
            if inferred.contains_file(path) {
                projects.push(inferred.clone());
            }
        }
        projects
    }

    /// `GetOpenConfiguredProjects` returns configured projects containing
    /// at least one open file.
    pub fn get_open_configured_projects(&self) -> &Set<ConfiguredProjectId> {
        self.open_configured_projects.get_or_init(|| {
            let mut open_projects = Set::new();
            for path in self.open_files.keys() {
                if let Some(project_id) = self.file_default_projects.get(path) {
                    if let Some(configured_id) = project_id.configured() {
                        if self.configured_projects.contains_key(&configured_id) {
                            open_projects.add(configured_id);
                            continue;
                        }
                    }
                }
                for project in self.configured_projects.values() {
                    if project.contains_file(path) {
                        if let Some(configured_id) = project.id.configured() {
                            open_projects.add(configured_id);
                        }
                    }
                }
            }
            open_projects
        })
    }

    /// `GetDefaultProject` — the project a language-service request for
    /// `path` should be routed to.
    pub fn get_default_project(&self, path: &PathKey) -> Option<Rc<Project>> {
        if let Some(result) = self.file_default_projects.get(path) {
            if result.inferred().is_some() {
                return self.inferred_project.clone();
            }
            let configured_id = result.configured()?;
            return self.configured_projects.get(&configured_id).cloned();
        }

        let mut containing_projects: Vec<Rc<Project>> = Vec::new();
        let mut first_configured_project: Option<Rc<Project>> = None;
        let mut first_non_source_of_project_reference_redirect: Option<Rc<Project>> = None;
        let mut multiple_direct_inclusions = false;

        for p in self.configured_projects() {
            if p.contains_file(path) {
                containing_projects.push(p.clone());
                if !multiple_direct_inclusions && !p.is_source_from_project_reference(path) {
                    if first_non_source_of_project_reference_redirect.is_none() {
                        first_non_source_of_project_reference_redirect = Some(p.clone());
                    } else {
                        multiple_direct_inclusions = true;
                    }
                }
                if first_configured_project.is_none() {
                    first_configured_project = Some(p);
                }
            }
        }

        if containing_projects.len() == 1 {
            return containing_projects.into_iter().next();
        }
        if containing_projects.is_empty() {
            if let Some(inferred) = &self.inferred_project {
                if inferred.contains_file(path) {
                    return Some(inferred.clone());
                }
            }
            return None;
        }
        if !multiple_direct_inclusions {
            if let Some(project) = first_non_source_of_project_reference_redirect {
                // Multiple projects include the file, but only one is a
                // direct inclusion.
                return Some(project);
            }
            // Multiple projects include the file, and none are direct
            // inclusions.
            return first_configured_project;
        }
        // Multiple projects include the file directly.
        if let Some(default_project) = self.find_default_configured_project(path) {
            return Some(default_project);
        }
        first_configured_project
    }

    /// `findDefaultConfiguredProject`.
    fn find_default_configured_project(&self, path: &PathKey) -> Option<Rc<Project>> {
        let registry = self.config_file_registry.as_ref()?;
        let config_file_name = registry.get_config_file_name(path);
        if !config_file_name.is_empty() {
            return self.find_default_configured_project_worker(
                path,
                &config_file_name,
                None,
                None,
            );
        }
        None
    }

    /// `findDefaultConfiguredProjectWorker`.
    ///
    /// PORT: Go's `core.BreadthFirstSearchParallelEx` spawns goroutines
    /// per level; `Rc<Project>` is `!Send`, so the identical level-order
    /// search runs sequentially here (`visit`/`neighbors` are pure, so
    /// parallelization cannot change the outcome).
    fn find_default_configured_project_worker(
        &self,
        path: &PathKey,
        config_file_name: &RootedFilePath,
        visited: Option<&SyncSet<usize>>,
        mut fallback: Option<Rc<Project>>,
    ) -> Option<Rc<Project>> {
        let registry = self.config_file_registry.as_ref()?;
        let config_file_path = self.case_sensitivity.path_key(&config_file_name.as_path());
        let project = self
            .configured_projects
            .get(&configured_project_id_from_path_key(&config_file_path))?
            .clone();
        let owned_visited;
        let visited = match visited {
            Some(v) => v,
            None => {
                owned_visited = SyncSet::new();
                &owned_visited
            }
        };

        // Single-threaded equivalent of `BreadthFirstSearchParallelEx`:
        // `path` in the result is the found node followed by its parents,
        // so `path[0]` is the project `visit` accepted.
        let ptr_key = |p: &Rc<Project>| Rc::as_ptr(p) as usize;
        let mut arena: Vec<(Rc<Project>, Option<usize>)> = vec![(project, None)];
        let mut level: Vec<usize> = vec![0];
        let mut result: Option<usize> = None;
        let mut fallback_job: Option<usize> = None;
        'levels: while !level.is_empty() {
            let mut next_keys = Set::new();
            let mut next_jobs: Vec<usize> = Vec::new();
            for (i, &j) in level.iter().enumerate() {
                let _ = i;
                if !visited.add_if_absent(ptr_key(&arena[j].0)) {
                    continue;
                }
                let (is_result, stop) = {
                    let p = &arena[j].0;
                    (
                        p.contains_file(path),
                        !p.is_source_from_project_reference(path),
                    )
                };
                if is_result && stop {
                    result = Some(j);
                    break 'levels;
                }
                if is_result && fallback_job.is_none() {
                    fallback_job = Some(j);
                }
                // neighbors: referenced projects (loaded only).
                let neighbors: Vec<Rc<Project>> = {
                    let p = &arena[j].0;
                    match &p.command_line {
                        None => Vec::new(),
                        Some(command_line) => command_line
                            .resolved_project_reference_paths()
                            .iter()
                            .filter_map(|config_file_name| {
                                self.configured_projects
                                    .get(&configured_project_id_from_path_key(
                                        &self
                                            .case_sensitivity
                                            .path_key(&config_file_name.as_path()),
                                    ))
                                    .cloned()
                            })
                            .collect(),
                    }
                };
                for child in neighbors {
                    let key = ptr_key(&child);
                    if !next_keys.has(&key) {
                        next_keys.add(key);
                        arena.push((child, Some(j)));
                        next_jobs.push(arena.len() - 1);
                    }
                }
            }
            level = next_jobs;
        }

        // `search.Path[0]` — the found node is first in the parent chain.
        if let Some(found) = result {
            return Some(arena[found].0.clone());
        }
        if let Some(found) = fallback_job {
            if fallback.is_none() {
                // We found a project that contains the file, but it is a
                // source from a project reference; record it as a fallback.
                fallback = Some(arena[found].0.clone());
            }
        }

        // Look for tsconfig.json files higher up the directory tree and do
        // the same. This handles the common case where a higher-level
        // "solution" tsconfig.json contains all projects in a workspace.
        if let Some(config) = registry.get_config(path) {
            if config
                .compiler_options()
                .is_some_and(|o| o.disable_solution_searching.is_true())
            {
                return fallback;
            }
        }
        let ancestor_config_name =
            registry.get_ancestor_config_file_name(path, config_file_name);
        if !ancestor_config_name.is_empty() {
            return self.find_default_configured_project_worker(
                path,
                &ancestor_config_name,
                Some(visited),
                fallback,
            );
        }
        fallback
    }

    /// `clone` creates a shallow copy of the project collection.
    ///
    /// PORT: Go's field-copy clone keeps the `sync.Once` state; `OnceLock`
    /// cannot be copied, so the clone recomputes `openConfiguredProjects`
    /// (the value is deterministic).
    pub fn shallow_clone(&self) -> ProjectCollection {
        ProjectCollection {
            case_sensitivity: self.case_sensitivity,
            config_file_registry: self.config_file_registry.clone(),
            configured_projects: self.configured_projects.clone(),
            synthetic_projects: self.synthetic_projects.clone(),
            open_files: self.open_files.clone(),
            inferred_project: self.inferred_project.clone(),
            file_default_projects: self.file_default_projects.clone(),
            api_state: self.api_state.clone(),
            open_configured_projects: OnceLock::new(),
        }
    }
}
