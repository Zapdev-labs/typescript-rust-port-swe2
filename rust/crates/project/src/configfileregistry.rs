// Ported from tsc/internal/project/configfileregistry.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::BTreeSet;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use tsc_lsproto::WatchKind;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::project::{Id, PendingReload};
use crate::watch::{PatternsAndIgnored, WatchedFiles, new_watched_files};

/// `ConfigFileRegistry` — immutable snapshot state, cloned shallowly between
/// snapshots (the builder mutates its own copy before freeze). `Clone` is
/// `registry.clone()`.
#[derive(Clone, Default)]
pub struct ConfigFileRegistry {
    /// `configs` is a map of config file paths to their entries.
    pub(crate) configs: FxHashMap<PathKey, ConfigFileEntry>,
    /// `configFileNames` is a map of open file paths to information
    /// about their ancestor config file names. It is only used as
    /// a cache during project collection building.
    pub(crate) config_file_names: FxHashMap<PathKey, ConfigFileNames>,
    /// `customConfigFileName` is the custom config file name preference that was
    /// used when building this registry's `configFileNames` cache.
    pub(crate) custom_config_file_name: String,
    pub(crate) all_configured_content_mappers: Option<ConfiguredContentMappers>,
}

/// `configuredContentMappers`.
#[derive(Clone, Debug)]
pub struct ConfiguredContentMappers {
    pub extensions: Vec<String>,
}

/// `collectConfiguredContentMappers`.
pub fn collect_configured_content_mappers(
    command_lines: &[Arc<ParsedCommandLine>],
) -> ConfiguredContentMappers {
    let mut seen_extensions: BTreeSet<String> = BTreeSet::new();
    let mut extensions: Vec<String> = Vec::new();
    for command_line in command_lines {
        for mapper in command_line.content_mappers() {
            if let Some(mapper_extensions) = &mapper.extensions {
                for extension in mapper_extensions {
                    if seen_extensions.insert(extension.clone()) {
                        extensions.push(extension.clone());
                    }
                }
            }
        }
    }
    extensions.sort();
    ConfiguredContentMappers { extensions }
}

impl ConfigFileRegistry {
    /// `contentMappers` — the union of all extensions from every config's
    /// content mappers, cached eagerly on `allConfiguredContentMappers` when
    /// the builder can see all configs.
    pub fn content_mappers(&self) -> ConfiguredContentMappers {
        if let Some(mappers) = &self.all_configured_content_mappers {
            return mappers.clone();
        }
        let mut command_lines: Vec<Arc<ParsedCommandLine>> = Vec::new();
        for entry in self.configs.values() {
            if let Some(command_line) = &entry.command_line {
                command_lines.push(command_line.clone());
            }
        }
        collect_configured_content_mappers(&command_lines)
    }

    /// `GetConfig`.
    pub fn get_config(&self, path: &PathKey) -> Option<Arc<ParsedCommandLine>> {
        self.configs.get(path).and_then(|e| e.command_line.clone())
    }

    /// `isTracked`.
    pub fn is_tracked(&self, path: &PathKey) -> bool {
        self.configs.contains_key(path)
    }

    /// `GetConfigFileName` — the empty `RootedFilePath` default is Go's `""` return.
    pub fn get_config_file_name(&self, path: &PathKey) -> RootedFilePath {
        self.config_file_names
            .get(path)
            .map(|e| e.nearest_config_file_name.clone())
            .unwrap_or_default()
    }

    /// `GetAncestorConfigFileName`.
    pub fn get_ancestor_config_file_name(
        &self,
        path: &PathKey,
        higher_than_config: &RootedFilePath,
    ) -> RootedFilePath {
        self.config_file_names
            .get(path)
            .and_then(|e| e.ancestors.get(higher_than_config).cloned())
            .unwrap_or_default()
    }

    /// `clone` creates a shallow copy of the registry — Rust's `Clone` impl is
    /// the same operation.
    ///
    /// `ForEachTestConfigEntry`.
    pub fn for_each_test_config_entry(
        &self,
        mut cb: impl FnMut(&PathKey, TestConfigEntry<'_>),
    ) {
        for (path, entry) in &self.configs {
            cb(
                path,
                TestConfigEntry {
                    file_name: entry.file_name.clone(),
                    retaining_projects: entry.retaining_projects.iter(),
                    retaining_open_files: entry.retaining_open_files.iter(),
                    retaining_configs: entry.retaining_configs.iter(),
                },
            );
        }
    }

    /// `GetTestConfigEntry`.
    pub fn get_test_config_entry(&self, path: &PathKey) -> Option<TestConfigEntry<'_>> {
        self.configs.get(path).map(|entry| TestConfigEntry {
            file_name: entry.file_name.clone(),
            retaining_projects: entry.retaining_projects.iter(),
            retaining_open_files: entry.retaining_open_files.iter(),
            retaining_configs: entry.retaining_configs.iter(),
        })
    }

    /// `ForEachTestConfigFileNamesEntry`.
    pub fn for_each_test_config_file_names_entry(
        &self,
        mut cb: impl FnMut(&PathKey, &TestConfigFileNamesEntry),
    ) {
        for (path, entry) in &self.config_file_names {
            cb(
                path,
                &TestConfigFileNamesEntry {
                    nearest_config_file_name: entry.nearest_config_file_name.clone(),
                    ancestors: entry.ancestors.clone(),
                },
            );
        }
    }

    /// `GetTestConfigFileNamesEntry`.
    pub fn get_test_config_file_names_entry(
        &self,
        path: &PathKey,
    ) -> Option<TestConfigFileNamesEntry> {
        self.config_file_names.get(path).map(|entry| TestConfigFileNamesEntry {
            nearest_config_file_name: entry.nearest_config_file_name.clone(),
            ancestors: entry.ancestors.clone(),
        })
    }
}

/// `configFileEntry`.
#[derive(Clone)]
pub struct ConfigFileEntry {
    pub file_name: RootedFilePath,
    pub pending_reload: PendingReload,
    /// `Arc` — `commandLine` is shared immutable `*tsoptions.ParsedCommandLine`.
    pub command_line: Option<Arc<ParsedCommandLine>>,
    /// `retainingProjects` is the set of projects that have called acquireConfig
    /// without releasing it. A config file entry may be acquired by a project
    /// either because it is the config for that project or because it is the
    /// config for a referenced project.
    pub retaining_projects: BTreeSet<Id>,
    /// `retainingOpenFiles` is the set of open files that caused this config to
    /// load during project collection building. This config file may or may not
    /// end up being the config for the default project for these files, but
    /// determining the default project loaded this config as a candidate, so
    /// subsequent calls to `projectCollectionBuilder.findDefaultConfiguredProject`
    /// will use this config as part of the search, so it must be retained.
    pub retaining_open_files: BTreeSet<PathKey>,
    /// `retainingConfigs` is the set of config files that extend this one. This
    /// provides a cheap reverse mapping for a project config's
    /// `commandLine.ExtendedSourceFiles()` that can be used to notify the
    /// extending projects when this config changes. An extended config file may
    /// or may not also be used directly by a project, so it's possible that
    /// when this is set, no other fields will be used.
    pub retaining_configs: BTreeSet<PathKey>,
    /// `rootFilesWatch` is a watch for the root files of this config file.
    /// `Arc` — shared unchanged between cloned entries like Go's pointer.
    pub root_files_watch: Option<Arc<WatchedFiles<PatternsAndIgnored>>>,
}

/// `newConfigFileEntry`.
pub fn new_config_file_entry(
    has_relative_pattern_capability: bool,
    file_name: RootedFilePath,
) -> ConfigFileEntry {
    ConfigFileEntry {
        pending_reload: PendingReload::Full,
        root_files_watch: Some(new_watched_files(
            &format!("root files for {}", file_name.as_string()),
            WatchKind(WatchKind::Create.0 | WatchKind::Change.0 | WatchKind::Delete.0),
            has_relative_pattern_capability,
            // `core.Identity` — the compute input is the patterns themselves.
            PatternsAndIgnored::default(),
            |p| p.clone(),
        )),
        file_name,
        command_line: None,
        retaining_projects: BTreeSet::new(),
        retaining_open_files: BTreeSet::new(),
        retaining_configs: BTreeSet::new(),
    }
}

/// `newExtendedConfigFileEntry`.
pub fn new_extended_config_file_entry(
    file_name: RootedFilePath,
    extending_config_path: PathKey,
) -> ConfigFileEntry {
    let mut retaining_configs = BTreeSet::new();
    retaining_configs.insert(extending_config_path);
    ConfigFileEntry {
        file_name,
        pending_reload: PendingReload::Full,
        command_line: None,
        retaining_projects: BTreeSet::new(),
        retaining_open_files: BTreeSet::new(),
        retaining_configs,
        root_files_watch: None,
    }
}

/// For testing — `TestConfigEntry`. Iterators replace `iter.Seq`.
pub struct TestConfigEntry<'a> {
    pub file_name: RootedFilePath,
    pub retaining_projects: std::collections::btree_set::Iter<'a, Id>,
    pub retaining_open_files: std::collections::btree_set::Iter<'a, PathKey>,
    pub retaining_configs: std::collections::btree_set::Iter<'a, PathKey>,
}

/// For testing — `TestConfigFileNamesEntry`.
#[derive(Clone)]
pub struct TestConfigFileNamesEntry {
    pub nearest_config_file_name: RootedFilePath,
    pub ancestors: FxHashMap<RootedFilePath, RootedFilePath>,
}

/// `e.Clone()` — Go's `Clone()` is `#[derive(Clone)]` (map clones become
/// `BTreeSet` clones, `commandLine`/`rootFilesWatch` share like Go pointers).
/// `clone_value` is `Clone()` for `dirty` map copy-on-write.
impl tsc_dirty::Cloneable for ConfigFileEntry {
    fn clone_value(&self) -> Self {
        self.clone()
    }
}

/// `configFileNames` — per-open-file ancestor config cache entry.
#[derive(Clone)]
pub struct ConfigFileNames {
    /// `nearestConfigFileName` is the file name of the nearest ancestor config file.
    pub nearest_config_file_name: RootedFilePath,
    /// `ancestors` is a map from one ancestor config file path to the next.
    /// For example, if `/a`, `/a/b`, and `/a/b/c` all contain config files,
    /// the fully loaded map will look like:
    ///   `/a/b/c/tsconfig.json` → `/a/b/tsconfig.json`,
    ///   `/a/b/tsconfig.json` → `/a/tsconfig.json`.
    pub ancestors: FxHashMap<RootedFilePath, RootedFilePath>,
}

impl tsc_dirty::Cloneable for ConfigFileNames {
    fn clone_value(&self) -> Self {
        self.clone()
    }
}
