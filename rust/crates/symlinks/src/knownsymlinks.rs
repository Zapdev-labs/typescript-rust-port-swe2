// Ported from tsc/internal/symlinks/knownsymlinks.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_ast::ast_generated::SourceFile;
use tsc_collections::{SyncMap, SyncSet};
use tsc_core::compileroptions::ResolutionMode;
use tsc_module::{ResolvedModule, ResolvedTypeReferenceDirective};
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, contains_ignored_path_key,
    rooted_directory_path_from_path, rooted_file_path_from_path,
};

/// `type KnownDirectoryLink struct`
#[derive(Clone, Debug, Default)]
pub struct KnownDirectoryLink {
    /// Matches the spelling used to reach the symlink. Used to preserve the
    /// spelling of child paths when substituting the real directory.
    pub symlink: RootedDirectoryPath,
    /// Matches the casing returned by `realpath`. Used to compute the
    /// `realpath` of children.
    pub real: RootedDirectoryPath,
    /// Canonical key for `real`, stored to avoid repeated recomputation.
    pub real_path: PathKey,
}

impl KnownDirectoryLink {
    /// `func (link *KnownDirectoryLink) ResolveFilePath(...) (RootedFilePath, bool)`
    ///
    /// PORT: the Go `(value, ok)` pair becomes `Option`.
    pub fn resolve_file_path(
        &self,
        file_name: &RootedFilePath,
        case_sensitivity: CaseSensitivity,
    ) -> Option<RootedFilePath> {
        let relative =
            case_sensitivity.relative_file_path_from_directory(&self.symlink, file_name)?;
        Some(self.real.resolve_relative_file(&relative))
    }
}

/// `type KnownSymlinks struct`
///
/// PORT: Go stores `*KnownDirectoryLink` (nil-able) and `*SyncSet[...]` (a
/// shared pointer whose mutations are visible through the map). Rust values
/// cannot outlive the `SyncMap` lock, so the entries are
/// `Option<Arc<KnownDirectoryLink>>` — the inner `Option` is Go's nil pointer —
/// and `Arc<SyncSet<...>>`, whose clones share the underlying set exactly like
/// Go's pointer.
#[derive(Default)]
pub struct KnownSymlinks {
    directories: SyncMap<PathKey, Option<Arc<KnownDirectoryLink>>>,
    directories_by_realpath: SyncMap<PathKey, Arc<SyncSet<RootedDirectoryPath>>>,
    files: SyncMap<PathKey, RootedFilePath>,
    files_by_realpath: SyncMap<PathKey, Arc<SyncSet<RootedFilePath>>>,
    // PORT: `pub(crate)` so the in-package Go tests can read it, mirroring the
    // private `caseSensitivity` field accessed from the same package in Go.
    pub(crate) case_sensitivity: CaseSensitivity,
}

impl KnownSymlinks {
    /// `func NewKnownSymlinks(caseSensitivity CaseSensitivity) *KnownSymlinks`
    pub fn new(case_sensitivity: CaseSensitivity) -> Self {
        Self {
            case_sensitivity,
            ..Default::default()
        }
    }

    /// `func (cache *KnownSymlinks) HasDirectory(symlinkPath PathKey) bool`
    pub fn has_directory(&self, symlink_path: &PathKey) -> bool {
        self.directories.load(symlink_path).is_some()
    }

    /// Gets a map from symlink to realpath.
    ///
    /// `func (cache *KnownSymlinks) Directories() *SyncMap[PathKey, *KnownDirectoryLink]`
    pub fn directories(&self) -> &SyncMap<PathKey, Option<Arc<KnownDirectoryLink>>> {
        &self.directories
    }

    /// `func (cache *KnownSymlinks) DirectoriesByRealpath() *SyncMap[PathKey, *SyncSet[RootedDirectoryPath]]`
    pub fn directories_by_realpath(&self) -> &SyncMap<PathKey, Arc<SyncSet<RootedDirectoryPath>>> {
        &self.directories_by_realpath
    }

    /// Gets a map from symlink to realpath.
    ///
    /// `func (cache *KnownSymlinks) Files() *SyncMap[PathKey, RootedFilePath]`
    pub fn files(&self) -> &SyncMap<PathKey, RootedFilePath> {
        &self.files
    }

    /// Gets a map from realpath to symlinks.
    ///
    /// `func (cache *KnownSymlinks) FilesByRealpath() *SyncMap[PathKey, *SyncSet[RootedFilePath]]`
    pub fn files_by_realpath(&self) -> &SyncMap<PathKey, Arc<SyncSet<RootedFilePath>>> {
        &self.files_by_realpath
    }

    /// `func (cache *KnownSymlinks) SetDirectory(symlink RootedDirectoryPath, symlinkPath PathKey, realDirectory *KnownDirectoryLink)`
    ///
    /// PORT: `realDirectory` is `None` for Go's nil pointer.
    pub fn set_directory(
        &self,
        symlink: RootedDirectoryPath,
        symlink_path: PathKey,
        real_directory: Option<KnownDirectoryLink>,
    ) {
        let mut real_directory = real_directory;
        if let Some(link) = &mut real_directory {
            link.symlink = symlink.clone();
            if self.directories.load(&symlink_path).is_none() {
                let (set, _) = self
                    .directories_by_realpath
                    .load_or_store(link.real_path.clone(), Arc::new(SyncSet::new()));
                set.add(symlink);
            }
        }
        self.directories
            .store(symlink_path, real_directory.map(Arc::new));
    }

    /// `func (cache *KnownSymlinks) SetFile(symlink RootedFilePath, symlinkPath PathKey, realpath RootedFilePath)`
    pub fn set_file(
        &self,
        symlink: RootedFilePath,
        symlink_path: PathKey,
        realpath: RootedFilePath,
    ) {
        if self.files.load(&symlink_path).is_none() {
            let realpath_path = self.case_sensitivity.path_key(&realpath.as_path());
            let (set, _) = self
                .files_by_realpath
                .load_or_store(realpath_path, Arc::new(SyncSet::new()));
            set.add(symlink);
        }
        self.files.store(symlink_path, realpath);
    }

    /// `func (cache *KnownSymlinks) SetSymlinksFromResolutions(forEachResolvedModule, forEachResolvedTypeReferenceDirective)`
    ///
    /// PORT: Go's higher-order `forEach*` functions become `FnOnce`s taking a
    /// `&mut dyn FnMut` callback and an optional `&SourceFile` (`nil` in Go).
    /// The callback receives the resolution by reference rather than Go's
    /// `*module.ResolvedModule` pointer.
    pub fn set_symlinks_from_resolutions(
        &self,
        for_each_resolved_module: impl FnOnce(
            &mut dyn FnMut(&ResolvedModule, &str, ResolutionMode, &PathKey),
            Option<&SourceFile>,
        ),
        for_each_resolved_type_reference_directive: impl FnOnce(
            &mut dyn FnMut(&ResolvedTypeReferenceDirective, &str, ResolutionMode, &PathKey),
            Option<&SourceFile>,
        ),
    ) {
        for_each_resolved_module(
            &mut |resolution: &ResolvedModule,
                  _module_name: &str,
                  _mode: ResolutionMode,
                  _file_path: &PathKey| {
                self.process_resolution(
                    resolution.original_path.clone(),
                    resolution.resolved_file_name.clone(),
                );
            },
            None,
        );
        for_each_resolved_type_reference_directive(
            &mut |resolution: &ResolvedTypeReferenceDirective,
                  _module_name: &str,
                  _mode: ResolutionMode,
                  _file_path: &PathKey| {
                self.process_resolution(
                    resolution.original_path.clone(),
                    resolution.resolved_file_name.clone(),
                );
            },
            None,
        );
    }

    /// `func (cache *KnownSymlinks) ProcessResolution(originalFileName RootedFilePath, resolvedFileName RootedFilePath)`
    pub fn process_resolution(
        &self,
        original_file_name: RootedFilePath,
        resolved_file_name: RootedFilePath,
    ) {
        if original_file_name.is_empty() || resolved_file_name.is_empty() {
            return;
        }
        self.set_file(
            original_file_name.clone(),
            self.case_sensitivity
                .path_key(&original_file_name.as_path()),
            resolved_file_name.clone(),
        );
        let (common_resolved, common_original) =
            self.guess_directory_symlink_from_file_paths(&resolved_file_name, &original_file_name);
        if !common_resolved.is_empty() && !common_original.is_empty() {
            let symlink_path = self.case_sensitivity.path_key(&common_original.as_path());
            if !contains_ignored_path_key(&symlink_path) {
                self.set_directory(
                    common_original,
                    symlink_path,
                    Some(KnownDirectoryLink {
                        real: common_resolved.clone(),
                        real_path: self.case_sensitivity.path_key(&common_resolved.as_path()),
                        ..Default::default()
                    }),
                );
            }
        }
    }

    /// `func (cache *KnownSymlinks) guessDirectorySymlinkFromFilePaths(a, b RootedFilePath) (RootedDirectoryPath, RootedDirectoryPath)`
    ///
    /// PORT: `pub(crate)` for the in-package Go tests; not part of the Go
    /// package's exported API.
    pub(crate) fn guess_directory_symlink_from_file_paths(
        &self,
        a: &RootedFilePath,
        b: &RootedFilePath,
    ) -> (RootedDirectoryPath, RootedDirectoryPath) {
        let mut a = a.clone();
        let mut b = b.clone();
        let mut is_directory = false;
        loop {
            let a_parent = a.directory();
            let b_parent = b.directory();
            if a_parent.as_path() == a.as_path()
                || b_parent.as_path() == b.as_path()
                || self.is_node_modules_or_scoped_package_directory(a_parent.base_name())
                || self.is_node_modules_or_scoped_package_directory(b_parent.base_name())
                || self.case_sensitivity.canonicalize(a.base_name())
                    != self.case_sensitivity.canonicalize(b.base_name())
            {
                break;
            }
            a = rooted_file_path_from_path(a_parent.as_path());
            b = rooted_file_path_from_path(b_parent.as_path());
            is_directory = true;
        }
        if is_directory {
            return (
                rooted_directory_path_from_path(a.as_path()),
                rooted_directory_path_from_path(b.as_path()),
            );
        }
        (
            RootedDirectoryPath::default(),
            RootedDirectoryPath::default(),
        )
    }

    /// `func (cache *KnownSymlinks) isNodeModulesOrScopedPackageDirectory(s string) bool`
    ///
    /// PORT: `pub(crate)` for the in-package Go tests.
    pub(crate) fn is_node_modules_or_scoped_package_directory(&self, s: &str) -> bool {
        !s.is_empty()
            && (self.case_sensitivity.canonicalize(s).as_ref() == "node_modules"
                || s.starts_with('@'))
    }
}
