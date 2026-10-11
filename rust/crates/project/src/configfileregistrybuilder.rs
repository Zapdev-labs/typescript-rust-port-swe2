// Ported from tsc/internal/project/configfileregistrybuilder.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cell::Cell;
use std::collections::BTreeSet;
use std::rc::Rc;
use std::sync::{Arc, Mutex, Weak};

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_collections::Set;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::TS_TRUE;
use tsc_dirty::{Map as DirtyMap, SyncMap as DirtySyncMap, SyncMapEntry};
use tsc_project_logging::{LogTree, Logger};
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tsoptions::tsconfigparsing::{
    ExtendedConfigCache as ExtendedConfigCacheTrait, ExtendedConfigCacheEntry,
    get_parsed_command_line_of_config_file_path,
};
use tsc_tspath::{
    PathKey, RootedDirectoryPath, RootedFilePath, RootedPath, contains_ignored_path,
    rooted_directory_path_from_path, rooted_file_path_from_path,
};
use tsc_vfs::Vfs;

use crate::configfileregistry::{
    ConfigFileEntry, ConfigFileNames, ConfigFileRegistry, ConfiguredContentMappers,
    collect_configured_content_mappers, new_config_file_entry, new_extended_config_file_entry,
};
use crate::extendedconfigcache::{ExtendedConfigCache, ExtendedConfigParseArgs};
use crate::filechange::FileChangeSummary;
use crate::project::{Id, PendingReload};
use crate::projectcollectionbuilder::ProjectLoadKind;
use crate::session::SessionOptions;
use crate::overlayfs::FileHandleSource;
use crate::snapshotfs::{FileSource, SourceFs, new_source_fs};
use crate::watch::{
    MIN_WATCH_LOCATION_DEPTH, PatternsAndIgnored, get_path_components_for_watching,
    get_recursive_glob_pattern,
};

/// `configFileRegistryBuilder` tracks changes made on top of a previous
/// configFileRegistry, producing a new clone with `finalize()` after
/// all changes have been made.
pub struct ConfigFileRegistryBuilder {
    pub(crate) has_relative_pattern_capability: bool,
    pub(crate) fs: Arc<SourceFs>,
    /// `isOpenFile` — `Box<dyn Fn>` is Go's `func` field.
    pub(crate) is_open_file: Box<dyn Fn(&PathKey) -> bool>,
    /// `extendedConfigCache` — `Rc` because Go's `*ExtendedConfigCache`
    /// pointer is shared between the snapshot host (owner tracking) and
    /// each builder (the cache itself is `!Clone`).
    pub(crate) extended_config_cache: Rc<ExtendedConfigCache>,
    pub(crate) snapshot_id: u64,
    pub(crate) session_options: Arc<SessionOptions>,
    pub(crate) custom_config_file_name: String,

    pub(crate) base: ConfigFileRegistry,
    pub(crate) configs: DirtySyncMap<PathKey, ConfigFileEntry>,
    pub(crate) config_file_names: DirtyMap<PathKey, ConfigFileNames>,
    pub(crate) custom_config_file_name_changed: bool,
    /// `contentMappersMu`/`allConfiguredContentMappers`.
    all_configured_content_mappers: Mutex<Option<ConfiguredContentMappers>>,
    /// `Weak` self-handle — `GetExtendedConfig` passes the builder itself as
    /// `ExtendedConfigParseArgs.Cache` (Go `Cache: c`).
    me: Weak<Self>,
}

/// `newConfigFileRegistryBuilder`. Returns `Arc` because the builder passes
/// itself as an `ExtendedConfigCache` (Go `Cache: c` / `var _
/// tsoptions.ExtendedConfigCache = (*configFileRegistryBuilder)(nil)`).
///
/// PORT: `fs` is the `*snapshotFsBuilder` (an `Arc<dyn FileSource>` here);
/// `isOpenFile` is `func(tspath.PathKey) bool`.
pub fn new_config_file_registry_builder(
    has_relative_pattern_capability: bool,
    fs: Arc<dyn FileSource>,
    is_open_file: Box<dyn Fn(&PathKey) -> bool>,
    old_config_file_registry: &ConfigFileRegistry,
    extended_config_cache: Rc<ExtendedConfigCache>,
    snapshot_id: u64,
    session_options: Arc<SessionOptions>,
    custom_config_file_name: String,
    _logger: &LogTree,
) -> Arc<ConfigFileRegistryBuilder> {
    Arc::new_cyclic(|me| ConfigFileRegistryBuilder {
        has_relative_pattern_capability,
        fs: Arc::new(new_source_fs(false, fs)),
        is_open_file,
        base: old_config_file_registry.clone(),
        session_options,
        extended_config_cache,
        snapshot_id,
        custom_config_file_name_changed: custom_config_file_name
            != old_config_file_registry.custom_config_file_name,
        all_configured_content_mappers: Mutex::new(Some(
            old_config_file_registry.content_mappers(),
        )),
        custom_config_file_name,
        configs: DirtySyncMap::new(Some(old_config_file_registry.configs.clone())),
        config_file_names: DirtyMap::new(Some(
            old_config_file_registry.config_file_names.clone(),
        )),
        me: me.clone(),
    })
}

impl ConfigFileRegistryBuilder {
    /// `Finalize` creates a new configFileRegistry based on the changes made
    /// in the builder. If no changes were made, it returns the original base
    /// registry.
    pub fn finalize(&self) -> ConfigFileRegistry {
        let mut changed = false;
        let mut new_registry = self.base.clone();
        macro_rules! ensure_cloned {
            () => {
                if !changed {
                    new_registry = self.base.clone();
                    changed = true;
                }
            };
        }
        // Go's `ensureCloned` starts from `c.base` (no clone) and clones on
        // first use; since `new_registry` is already a clone this degenerates
        // to a flag.
        let _ = &mut changed;

        if let (Some(configs), true) = self.configs.finalize() {
            ensure_cloned!();
            new_registry.configs = configs;
            new_registry.all_configured_content_mappers = Some(self.content_mappers());
        }

        if let (Some(config_file_names), true) = self.config_file_names.finalize() {
            ensure_cloned!();
            new_registry.config_file_names = config_file_names;
        }

        if self.custom_config_file_name_changed {
            ensure_cloned!();
            new_registry.custom_config_file_name = self.custom_config_file_name.clone();
        }

        let _ = changed;
        new_registry
    }

    fn content_mappers(&self) -> ConfiguredContentMappers {
        let mut cached = self.all_configured_content_mappers.lock().unwrap();
        if cached.is_none() {
            let mut command_lines: Vec<Arc<ParsedCommandLine>> = Vec::new();
            self.configs.range(|entry| {
                if let Some(value) = entry.value() {
                    if let Some(command_line) = &value.command_line {
                        command_lines.push(command_line.clone());
                    }
                }
                true
            });
            *cached = Some(collect_configured_content_mappers(&command_lines));
        }
        cached.clone().unwrap()
    }

    fn invalidate_content_mappers(&self) {
        *self.all_configured_content_mappers.lock().unwrap() = None;
    }

    /// `findOrAcquireConfigForFile`.
    pub fn find_or_acquire_config_for_file(
        self: &Arc<Self>,
        config_file_name: &RootedFilePath,
        config_file_path: &PathKey,
        file_path: &PathKey,
        load_kind: ProjectLoadKind,
        logger: &LogTree,
    ) -> Option<Arc<ParsedCommandLine>> {
        match load_kind {
            ProjectLoadKind::Find => {
                if let Some(entry) = self.configs.load(config_file_path) {
                    return entry.value().and_then(|e| e.command_line.clone());
                }
                None
            }
            ProjectLoadKind::Create => self.acquire_config_for_file(
                config_file_name,
                config_file_path,
                file_path,
                logger,
            ),
        }
    }

    /// `reloadIfNeeded` updates the command line of the config file entry
    /// based on its pending reload state. Must only be called from within the
    /// `change` of a dirty map entry (the entry is a copy-on-write clone).
    fn reload_if_needed(
        self: &Arc<Self>,
        entry: &mut ConfigFileEntry,
        file_name: &RootedFilePath,
        path: &PathKey,
        logger: &LogTree,
    ) -> bool {
        let old_command_line = entry.command_line.clone();
        match entry.pending_reload {
            PendingReload::FileNames => {
                logger.log(format_args!(
                    "Reloading file names for config: {}",
                    file_name.as_string()
                ));
                entry.command_line = entry.command_line.as_ref().map(|cl| {
                    Arc::new(cl.reload_file_names_of_parsed_command_line(
                        &(self.fs.clone() as Arc<dyn Vfs>),
                    ))
                });
            }
            PendingReload::Full => {
                logger.log(format_args!(
                    "Loading config file: {}",
                    file_name.as_string()
                ));
                // When the workspace is trusted, enable external content
                // mappers so a config's contentMappers pass the
                // runExternalCode gate and register, as they would with the
                // CLI flag.
                let existing_options;
                let existing_options = if self.session_options.run_external_code {
                    existing_options = CompilerOptions {
                        run_external_code: TS_TRUE,
                        ..Default::default()
                    };
                    Some(&existing_options)
                } else {
                    None
                };
                entry.command_line = get_parsed_command_line_of_config_file_path(
                    file_name.clone(),
                    path.clone(),
                    existing_options,
                    None, /* optionsRaw */
                    &(self.fs.clone() as Arc<dyn Vfs>),
                    Some(self.as_ref() as &dyn ExtendedConfigCacheTrait),
                )
                .ok()
                .map(Arc::new);
                self.update_extending_configs(
                    path,
                    entry.command_line.as_ref(),
                    old_command_line.as_ref(),
                );
                self.update_root_files_watch(file_name, entry);
                logger.log(format_args!("Finished loading config file"));
            }
            _ => return false,
        }
        entry.pending_reload = PendingReload::None;
        !option_arc_ptr_eq(&old_command_line, &entry.command_line)
    }

    /// `updateExtendingConfigs`.
    fn update_extending_configs(
        &self,
        extending_config_path: &PathKey,
        new_command_line: Option<&Arc<ParsedCommandLine>>,
        old_command_line: Option<&Arc<ParsedCommandLine>>,
    ) {
        let mut new_extended_config_paths: Set<PathKey> = Set::new();
        let case_sensitivity = self.fs.case_sensitivity();
        if let Some(new_command_line) = new_command_line {
            for extended_config in new_command_line.extended_source_files() {
                let extended_config_path =
                    case_sensitivity.path_key(&extended_config.as_path());
                new_extended_config_paths.add(extended_config_path.clone());
                if let Some((entry, true)) = self.configs.load_or_store(
                    extended_config_path.clone(),
                    new_extended_config_file_entry(
                        extended_config,
                        extending_config_path.clone(),
                    ),
                ) {
                    entry.change_if(
                        |config| {
                            config.is_some_and(|c| {
                                !c.retaining_configs.contains(extending_config_path)
                            })
                        },
                        |config| {
                            config
                                .retaining_configs
                                .insert(extending_config_path.clone());
                        },
                    );
                }
            }
        }
        if let Some(old_command_line) = old_command_line {
            for extended_config in old_command_line.extended_source_files() {
                let extended_config_path =
                    case_sensitivity.path_key(&extended_config.as_path());
                if new_extended_config_paths.has(&extended_config_path) {
                    continue;
                }
                if let Some(entry) = self.configs.load(&extended_config_path) {
                    entry.change_if(
                        |config| {
                            config.is_some_and(|c| {
                                c.retaining_configs.contains(extending_config_path)
                            })
                        },
                        |config| {
                            config.retaining_configs.remove(extending_config_path);
                        },
                    );
                }
            }
        }
    }

    /// `updateRootFilesWatch`.
    fn update_root_files_watch(&self, file_name: &RootedFilePath, entry: &mut ConfigFileEntry) {
        if entry.root_files_watch.is_none() {
            return;
        }
        let Some(command_line) = &entry.command_line else {
            return;
        };

        let mut globs: Vec<String> = Vec::new();
        let mut external_directories: Vec<RootedDirectoryPath> = Vec::new();
        let mut ignored: FxHashSet<RootedDirectoryPath> = FxHashSet::default();
        let mut include_workspace = false;
        let mut include_tsconfig_dir = false;
        let tsconfig_dir = file_name.directory();
        let case_sensitivity = self.fs.case_sensitivity();

        let workspace_directory = &self.session_options.current_directory;
        let tsconfig_directory = file_name.directory();
        if let Some(wildcard_directories) = command_line.wildcard_directories() {
            for dir in wildcard_directories.keys() {
                if case_sensitivity.contains_path(workspace_directory, &dir.as_path()) {
                    include_workspace = true;
                } else if case_sensitivity.contains_path(&tsconfig_directory, &dir.as_path()) {
                    include_tsconfig_dir = true;
                } else {
                    external_directories.push(dir.clone());
                }
            }
        }
        if let Some(literal_file_names) = command_line.literal_file_names() {
            for literal_file_name in literal_file_names {
                if case_sensitivity.contains_file_path(workspace_directory, literal_file_name) {
                    include_workspace = true;
                } else if case_sensitivity
                    .contains_file_path(&tsconfig_directory, literal_file_name)
                {
                    include_tsconfig_dir = true;
                } else {
                    external_directories.push(literal_file_name.directory());
                }
            }
        }

        if include_workspace {
            globs.push(get_recursive_glob_pattern(workspace_directory));
        }
        if include_tsconfig_dir {
            globs.push(get_recursive_glob_pattern(&tsconfig_dir));
        }
        for extended_source_file in command_line.extended_source_files() {
            if include_workspace
                && case_sensitivity
                    .contains_file_path(workspace_directory, &extended_source_file)
            {
                continue;
            }
            globs.push(extended_source_file.as_string().to_string());
        }
        if !external_directories.is_empty() {
            let (common_parents, ignored_external_dirs) =
                tsc_tspath::get_common_parent_directories(
                    &external_directories,
                    MIN_WATCH_LOCATION_DEPTH,
                    get_path_components_for_watching,
                    case_sensitivity,
                );
            for parent in &common_parents {
                globs.push(get_recursive_glob_pattern(parent));
            }
            ignored = ignored_external_dirs;
        }

        globs.sort();
        entry.root_files_watch = Some(entry.root_files_watch.as_ref().unwrap().clone_with(
            PatternsAndIgnored {
                patterns_inside_workspace: globs,
                ignored,
                ..Default::default()
            },
        ));
    }

    /// `acquireConfigForProject` loads a config file entry from the cache, or
    /// parses it if not already cached, then adds the project (if provided) to
    /// `retainingProjects` to keep it alive in the cache. Each call that
    /// passes a project should be accompanied by an eventual
    /// `releaseConfigForProject` call with the same project.
    ///
    /// PORT: takes `project_id` — Go only reads `project.ID()`.
    pub fn acquire_config_for_project(
        self: &Arc<Self>,
        file_name: &RootedFilePath,
        path: &PathKey,
        project_id: &Id,
        logger: &LogTree,
    ) -> Option<Arc<ParsedCommandLine>> {
        let (entry, _) = self
            .configs
            .load_or_store(
                path.clone(),
                new_config_file_entry(self.has_relative_pattern_capability, file_name.clone()),
            )
            .expect("LoadOrStore deleted entry");
        // `Cell` — Go shares `needsRetainProject`/`contentMappersChanged`
        // between the cond/apply closures and the caller.
        let needs_retain_project = Cell::new(false);
        let content_mappers_changed = Cell::new(false);
        entry.change_if(
            |config| {
                let config = config.expect("stored entry has a value");
                needs_retain_project
                    .set(!config.retaining_projects.contains(project_id));
                needs_retain_project.get() || config.pending_reload != PendingReload::None
            },
            |config| {
                if needs_retain_project.get() {
                    config.retaining_projects.insert(project_id.clone());
                }
                content_mappers_changed
                    .set(self.reload_if_needed(config, file_name, path, logger));
            },
        );
        if content_mappers_changed.get() {
            self.invalidate_content_mappers();
        }
        entry.value().and_then(|e| e.command_line.clone())
    }

    /// `acquireConfigForFile` loads a config file entry from the cache, or
    /// parses it if not already cached, then adds the open file to
    /// `retainingOpenFiles` to keep it alive in the cache. Each call that
    /// passes an `openFilePath` should be accompanied by an eventual
    /// `releaseConfigForOpenFile` call with the same open file.
    pub fn acquire_config_for_file(
        self: &Arc<Self>,
        config_file_name: &RootedFilePath,
        config_file_path: &PathKey,
        file_path: &PathKey,
        logger: &LogTree,
    ) -> Option<Arc<ParsedCommandLine>> {
        let (entry, _) = self
            .configs
            .load_or_store(
                config_file_path.clone(),
                new_config_file_entry(
                    self.has_relative_pattern_capability,
                    config_file_name.clone(),
                ),
            )
            .expect("LoadOrStore deleted entry");
        // `Cell` — Go shares `needsRetainOpenFile`/`contentMappersChanged`
        // between the cond/apply closures and the caller.
        let needs_retain_open_file = Cell::new(false);
        let content_mappers_changed = Cell::new(false);
        entry.change_if(
            |config| {
                let config = config.expect("stored entry has a value");
                if (self.is_open_file)(file_path) {
                    needs_retain_open_file
                        .set(!config.retaining_open_files.contains(file_path));
                }
                needs_retain_open_file.get() || config.pending_reload != PendingReload::None
            },
            |config| {
                if needs_retain_open_file.get() {
                    config.retaining_open_files.insert(file_path.clone());
                }
                content_mappers_changed.set(self.reload_if_needed(
                    config,
                    config_file_name,
                    config_file_path,
                    logger,
                ));
            },
        );
        if content_mappers_changed.get() {
            self.invalidate_content_mappers();
        }
        entry.value().and_then(|e| e.command_line.clone())
    }

    /// `releaseConfigForProject` removes the project from the config entry.
    /// Once no projects or files are associated with the config entry, it
    /// will be removed on the next call to `cleanup`.
    pub fn release_config_for_project(&self, config_file_path: &PathKey, project_id: &Id) {
        if let Some(entry) = self.configs.load(config_file_path) {
            entry.change_if(
                |config| {
                    config.is_some_and(|c| c.retaining_projects.contains(project_id))
                },
                |config| {
                    config.retaining_projects.remove(project_id);
                },
            );
        }
    }

    /// `retainConfigForProject`.
    pub fn retain_config_for_project(&self, config_file_path: &PathKey, project_id: &Id) {
        if let Some(entry) = self.configs.load(config_file_path) {
            entry.change_if(
                |config| {
                    config.is_some_and(|c| !c.retaining_projects.contains(project_id))
                },
                |config| {
                    config.retaining_projects.insert(project_id.clone());
                },
            );
        }
    }

    /// `didCloseFile` removes the open file from the config entry. Once no
    /// projects or files are associated with the config entry, it will be
    /// removed on the next call to `cleanup`.
    fn did_close_file(&self, path: &PathKey) {
        if path.is_dynamic() {
            return;
        }
        self.config_file_names.delete(path);
        self.configs.range(|entry| {
            entry.change_if(
                |config| config.is_some_and(|c| c.retaining_open_files.contains(path)),
                |config| {
                    config.retaining_open_files.remove(path);
                },
            );
            true
        });
    }

    /// `DidChangeCustomConfigFileName`.
    pub fn did_change_custom_config_file_name(&self, _logger: &LogTree) -> bool {
        if !self.custom_config_file_name_changed {
            return false;
        }
        self.config_file_names.clear();
        true
    }

    /// `invalidateCache`.
    fn invalidate_cache(&self, logger: &LogTree) -> ChangeFileResult {
        let mut affected_projects: BTreeSet<Id> = BTreeSet::new();
        let mut affected_files: BTreeSet<PathKey> = BTreeSet::new();

        logger.log(format_args!(
            "Too many files changed; marking all configs for reload"
        ));
        self.config_file_names.range(|entry| {
            affected_files.insert(entry.key());
            true
        });
        self.config_file_names.clear();

        self.configs.range(|entry| {
            entry.change(|entry| {
                affected_projects.extend(entry.retaining_projects.iter().cloned());
                if entry.pending_reload != PendingReload::Full {
                    let text = self.fs.read_file(&entry.file_name);
                    if text.is_none()
                        || entry.command_line.is_none()
                        || text.as_deref()
                            != entry
                                .command_line
                                .as_ref()
                                .and_then(|cl| cl.config_file.as_ref())
                                .map(|c| c.text())
                    {
                        entry.pending_reload = PendingReload::Full;
                    } else {
                        entry.pending_reload = PendingReload::FileNames;
                    }
                }
            });
            true
        });

        ChangeFileResult {
            affected_projects,
            affected_files,
        }
    }

    /// `isConfigBaseName`.
    fn is_config_base_name(&self, base_name: &str) -> bool {
        base_name == "tsconfig.json"
            || base_name == "jsconfig.json"
            || (!self.custom_config_file_name.is_empty()
                && base_name == self.custom_config_file_name)
    }

    /// `DidChangeFiles`.
    pub fn did_change_files(&self, summary: &FileChangeSummary, logger: &LogTree) -> ChangeFileResult {
        if summary.invalidate_all {
            return self.invalidate_cache(logger);
        }
        let mut affected_projects: BTreeSet<Id> = BTreeSet::new();
        let mut affected_files: BTreeSet<PathKey> = BTreeSet::new();
        let mut should_invalidate_cache = false;

        logger.log(format_args!("Summarizing file changes"));
        let has_excessive_changes = summary.has_excessive_watch_events()
            && summary.includes_watch_change_outside_node_modules;
        let mut created_files: FxHashMap<PathKey, RootedPath> =
            FxHashMap::with_capacity_and_hasher(summary.created.len(), Default::default());
        let mut deleted_files: FxHashMap<PathKey, RootedPath> =
            FxHashMap::with_capacity_and_hasher(summary.deleted.len(), Default::default());
        let mut created_or_deleted_config_files: Set<PathKey> = Set::new();
        let mut created_or_changed_or_deleted_files: Set<PathKey> = Set::with_size_hint(
            summary.changed.len() + summary.created.len() + summary.deleted.len(),
        );
        for uri in summary.changed.keys() {
            let file_name = uri.file_name();
            if contains_ignored_path(&file_name.as_path()) {
                continue;
            }
            let path = self.fs.case_sensitivity().path_key(&file_name.as_path());
            let base_name = path.base_name();
            if self.is_config_base_name(base_name) {
                created_or_deleted_config_files.add(path.clone());
            }
            created_or_changed_or_deleted_files.add(path);
        }
        for uri in summary.deleted.keys() {
            let file_path = uri.path();
            if contains_ignored_path(&file_path) {
                continue;
            }
            let path = self.fs.case_sensitivity().path_key(&file_path);
            deleted_files.insert(path.clone(), file_path);
            let base_name = path.base_name();
            if self.is_config_base_name(base_name) {
                created_or_deleted_config_files.add(path.clone());
            }
            created_or_changed_or_deleted_files.add(path);
        }
        for uri in summary.created.keys() {
            let file_path = uri.path();
            if contains_ignored_path(&file_path) {
                continue;
            }
            let path = self.fs.case_sensitivity().path_key(&file_path);
            created_files.insert(path.clone(), file_path);
            let base_name = path.base_name();
            if self.is_config_base_name(base_name) {
                created_or_deleted_config_files.add(path.clone());
            }
            created_or_changed_or_deleted_files.add(path);
        }

        // Handle closed files - this ranges over config entries and could be
        // combined with the file change handling, but a separate loop is
        // simpler and a snapshot change with both closing and watch changes
        // seems rare.
        for uri in summary.closed.keys() {
            let file_name = uri.file_name();
            let path = self.fs.case_sensitivity().path_key(&file_name.as_path());
            self.did_close_file(&path);
        }

        // Handle changes to stored config files and their content mapper
        // package manifests.
        logger.log(format_args!(
            "Checking if any changed files are configuration files"
        ));
        for path in created_or_changed_or_deleted_files.keys() {
            if let Some(entry) = self.configs.load(path) {
                if has_excessive_changes {
                    return self.invalidate_cache(logger);
                }

                affected_projects
                    .extend(self.handle_config_change(&entry, logger));
                if let Some(value) = entry.value() {
                    for extending_config_path in &value.retaining_configs {
                        if let Some(extending_config_entry) =
                            self.configs.load(extending_config_path)
                        {
                            affected_projects.extend(
                                self.handle_config_change(&extending_config_entry, logger),
                            );
                        }
                    }
                }
                // This was a config file, so assume it's not also a root file.
                created_files.remove(path);
            } else if path.base_name() == "package.json" {
                let mut manifest_changed = false;
                self.configs.range(|entry| {
                    if let Some(value) = entry.value() {
                        if content_mapper_manifest_path(value.command_line.as_ref(), path) {
                            affected_projects
                                .extend(self.handle_config_change(entry, logger));
                            manifest_changed = true;
                        }
                    }
                    true
                });
                if manifest_changed {
                    self.invalidate_content_mappers();
                }
            }
        }

        // Handle created/deleted files named "tsconfig.json" or
        // "jsconfig.json".
        for path in created_or_deleted_config_files.keys() {
            if has_excessive_changes {
                return self.invalidate_cache(logger);
            }
            let directory_path = path.parent();
            self.config_file_names.range(|entry| {
                if directory_path.contains_path(&entry.key()) {
                    affected_files.insert(entry.key());
                    entry.delete();
                }
                true
            });
        }

        // Handle deletions of wildcard-included root files.
        for (path, file_path) in &deleted_files {
            self.configs.range(|entry| {
                entry.change_if(
                    |config| {
                        let Some(config) = config else {
                            return false;
                        };
                        if config.pending_reload != PendingReload::None
                            || config.command_line.is_none()
                        {
                            return false;
                        }
                        let command_line = config.command_line.as_ref().unwrap();
                        if command_line.file_paths().has(path) {
                            // If the file is included in FileNames() but not
                            // matched by literal "files", it must be included
                            // via wildcard, which means a reload of filenames
                            // will remove it from the list. (Files explicitly
                            // specified in "files" are always included in the
                            // ParsedCommandLine, triggering a missing root
                            // file error during program construction.)
                            return command_line
                                .get_matched_file_spec(&rooted_file_path_from_path(
                                    file_path.clone(),
                                ))
                                .is_empty();
                        }
                        false
                    },
                    |config| {
                        config.pending_reload = PendingReload::FileNames;
                        affected_projects.extend(config.retaining_projects.iter().cloned());
                        logger.logf(format_args!(
                            "Root files for config {} changed",
                            entry.key().as_string()
                        ));
                        should_invalidate_cache = has_excessive_changes;
                    },
                );
                !should_invalidate_cache
            });
            if should_invalidate_cache {
                return self.invalidate_cache(logger);
            }
        }

        // Handle possible root file creation.
        if !created_files.is_empty() {
            self.configs.range(|entry| {
                entry.change_if(
                    |config| {
                        let Some(config) = config else {
                            return false;
                        };
                        if config.command_line.is_none()
                            || config.root_files_watch.is_none()
                            || config.pending_reload != PendingReload::None
                        {
                            return false;
                        }
                        logger.logf(format_args!(
                            "Checking if any of {} created files match root files for config {}",
                            created_files.len(),
                            entry.key().as_string()
                        ));
                        let command_line = config.command_line.as_ref().unwrap();
                        for (path, file_path) in &created_files {
                            if command_line.possibly_matches_file_name(
                                &rooted_file_path_from_path(file_path.clone()),
                            ) {
                                return true;
                            }
                            if command_line.possibly_matches_directory_name(path)
                                && self.fs.directory_exists(
                                    &rooted_directory_path_from_path(file_path.clone()),
                                )
                            {
                                // If we got a creation event for a directory,
                                // it's probably a symlink. We don't need to
                                // test realpath here; this is enough
                                // confidence to trigger a filename reload.
                                return true;
                            }
                        }
                        false
                    },
                    |config| {
                        config.pending_reload = PendingReload::FileNames;
                        affected_projects.extend(config.retaining_projects.iter().cloned());
                        logger.logf(format_args!(
                            "Root files for config {} changed",
                            entry.key().as_string()
                        ));
                        should_invalidate_cache = has_excessive_changes;
                    },
                );
                !should_invalidate_cache
            });
            if should_invalidate_cache {
                return self.invalidate_cache(logger);
            }
        }

        ChangeFileResult {
            affected_projects,
            affected_files,
        }
    }

    /// `handleConfigChange`.
    fn handle_config_change(
        &self,
        entry: &SyncMapEntry<PathKey, ConfigFileEntry>,
        logger: &LogTree,
    ) -> BTreeSet<Id> {
        let mut affected_projects = BTreeSet::new();
        let changed = entry.change_if(
            |config| {
                config.is_some_and(|c| c.pending_reload != PendingReload::Full)
            },
            |config| {
                config.pending_reload = PendingReload::Full;
            },
        );
        if changed {
            logger.logf(format_args!("Config file {} changed", entry.key().as_string()));
            if let Some(value) = entry.value() {
                affected_projects = value.retaining_projects.clone();
            }
        }
        affected_projects
    }

    /// `computeConfigFileName`.
    fn compute_config_file_name(
        &self,
        file_name: &RootedFilePath,
        skip_search_in_directory_of_file: bool,
        logger: &LogTree,
    ) -> RootedFilePath {
        let search_directory = file_name.directory();
        // Prefer custom config file if provided; search ancestors with
        // correct skip behavior.
        if !self.custom_config_file_name.is_empty() {
            let mut skip = skip_search_in_directory_of_file;
            if let Some(result) = search_directory.for_each_ancestor_directory(
                |directory| {
                    if !skip {
                        let custom_path =
                            directory.resolve_file(&self.custom_config_file_name);
                        if self.fs.file_exists(&custom_path) {
                            return (Some(custom_path), true);
                        }
                    }
                    if directory.as_path().base_name() == "node_modules" {
                        return (None, true);
                    }
                    skip = false;
                    (None, false)
                },
            ) {
                if let Some(result) = result {
                    logger.logf(format_args!(
                        "computeConfigFileName:: File: {}:: Result: {}",
                        file_name.as_string(),
                        result.as_string()
                    ));
                    return result;
                }
            }
        }

        // When searching for ancestor of a config file, determine which
        // config types to skip in the starting directory. This matches
        // TSServer's forEachConfigFileLocation behavior:
        // - For ancestor of tsconfig.json: skip tsconfig.json but still check
        //   jsconfig.json
        // - For ancestor of jsconfig.json: skip both tsconfig.json and
        //   jsconfig.json
        let mut skip_tsconfig = skip_search_in_directory_of_file;
        let mut skip_jsconfig =
            skip_search_in_directory_of_file && file_name.base_name() != "tsconfig.json";
        let result = search_directory
            .for_each_ancestor_directory(|directory| {
                if !skip_tsconfig {
                    let tsconfig_path = directory.resolve_file("tsconfig.json");
                    if self.fs.file_exists(&tsconfig_path) {
                        return (Some(tsconfig_path), true);
                    }
                }
                if !skip_jsconfig {
                    let jsconfig_path = directory.resolve_file("jsconfig.json");
                    if self.fs.file_exists(&jsconfig_path) {
                        return (Some(jsconfig_path), true);
                    }
                }
                if directory.as_path().base_name() == "node_modules" {
                    return (None, true);
                }
                skip_tsconfig = false;
                skip_jsconfig = false;
                (None, false)
            })
            .flatten();
        logger.logf(format_args!(
            "computeConfigFileName:: File: {}:: Result: {}",
            file_name.as_string(),
            result.as_ref().map(|r| r.as_string()).unwrap_or_default()
        ));
        result.unwrap_or_default()
    }

    /// `getConfigFileNameForFile`.
    pub fn get_config_file_name_for_file(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        logger: &LogTree,
    ) -> RootedFilePath {
        if file_name.is_dynamic() {
            return RootedFilePath::default();
        }

        if let Some(entry) = self.config_file_names.get(path) {
            if let Some(value) = entry.value() {
                return value.nearest_config_file_name;
            }
        }

        let config_name = self.compute_config_file_name(file_name, false, logger);
        if (self.is_open_file)(path) {
            self.config_file_names.add(
                path.clone(),
                ConfigFileNames {
                    nearest_config_file_name: config_name.clone(),
                    ancestors: FxHashMap::default(),
                },
            );
        }
        config_name
    }

    /// `forEachConfigFileNameFor`.
    pub fn for_each_config_file_name_for(
        &self,
        path: &PathKey,
        mut cb: impl FnMut(&RootedFilePath),
    ) {
        if path.is_dynamic() {
            return;
        }

        if let Some(entry) = self.config_file_names.get(path) {
            if let Some(value) = entry.value() {
                let mut config_file_name = value.nearest_config_file_name.clone();
                while !config_file_name.as_string().is_empty() {
                    cb(&config_file_name);
                    if let Some(ancestor) = value.ancestors.get(&config_file_name) {
                        config_file_name = ancestor.clone();
                    } else {
                        return;
                    }
                }
            }
        }
    }

    /// `getAncestorConfigFileName`.
    pub fn get_ancestor_config_file_name(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        config_file_name: &RootedFilePath,
        logger: &LogTree,
    ) -> RootedFilePath {
        if file_name.is_dynamic() {
            return RootedFilePath::default();
        }

        let Some(entry) = self.config_file_names.get(path) else {
            return RootedFilePath::default();
        };

        if let Some(value) = entry.value() {
            if let Some(ancestor) = value.ancestors.get(config_file_name) {
                return ancestor.clone();
            }
        }

        // Look for config in parent folders of config file.
        let result = self.compute_config_file_name(config_file_name, true, logger);

        if (self.is_open_file)(path) {
            entry.change(|value| {
                value
                    .ancestors
                    .insert(config_file_name.clone(), result.clone());
            });
        }
        result
    }

    /// `Cleanup`.
    pub fn cleanup(&self) {
        let mut changed = false;
        self.configs.range(|entry| {
            entry.delete_if(|value| {
                let should_delete = value.is_some_and(|v| {
                    v.retaining_projects.is_empty()
                        && v.retaining_open_files.is_empty()
                        && v.retaining_configs.is_empty()
                });
                changed = changed || should_delete;
                should_delete
            });
            true
        });
        if changed {
            self.invalidate_content_mappers();
        }
    }
}

/// `var _ tsoptions.ExtendedConfigCache = (*configFileRegistryBuilder)(nil)`
impl ExtendedConfigCacheTrait for ConfigFileRegistryBuilder {
    /// `GetExtendedConfig`.
    fn get_extended_config(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        resolution_stack: &[PathKey],
        fs: &Arc<dyn Vfs>,
    ) -> Option<ExtendedConfigCacheEntry> {
        let mut content = String::new();
        if let Some(fh) = self.fs.get_file_by_path(file_name, path) {
            content = fh.content().to_string();
        }

        Some(
            self.extended_config_cache
                .load_and_acquire(
                    path.clone(),
                    self.snapshot_id,
                    &ExtendedConfigParseArgs {
                        file_name: file_name.clone(),
                        content,
                        fs: self.fs.source(),
                        resolution_stack: resolution_stack.to_vec(),
                        config_fs: fs.clone(),
                        cache: self
                            .me
                            .upgrade()
                            .map(|me| me as Arc<dyn ExtendedConfigCacheTrait>),
                    },
                )
                .entry
                .clone(),
        )
    }
}

/// `changeFileResult`.
#[derive(Clone, Default)]
pub struct ChangeFileResult {
    /// `BTreeSet` is Go's `map[ID]struct{}`/`map[tspath.PathKey]struct{}`.
    pub affected_projects: BTreeSet<Id>,
    pub affected_files: BTreeSet<PathKey>,
}

impl ChangeFileResult {
    /// `IsEmpty`.
    pub fn is_empty(&self) -> bool {
        self.affected_projects.is_empty() && self.affected_files.is_empty()
    }
}

/// `contentMapperManifestPath`.
fn content_mapper_manifest_path(
    command_line: Option<&Arc<ParsedCommandLine>>,
    path: &PathKey,
) -> bool {
    let Some(command_line) = command_line else {
        return false;
    };
    for mapper in command_line.content_mappers() {
        if !mapper.package.is_empty()
            && mapper.contribution_id.is_empty()
            && !mapper.package_directory.as_string().is_empty()
            && command_line
                .case_sensitivity()
                .path_key(
                    &mapper
                        .package_directory
                        .resolve_file("package.json")
                        .as_path(),
                )
                == *path
        {
            return true;
        }
    }
    false
}

/// `oldCommandLine != entry.commandLine` — pointer comparison (Go compares
/// `*ParsedCommandLine` identity).
fn option_arc_ptr_eq<T>(a: &Option<Arc<T>>, b: &Option<Arc<T>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(a), Some(b)) => Arc::ptr_eq(a, b),
        _ => false,
    }
}
