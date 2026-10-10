// Ported from tsc/internal/compiler/projectreferencedtsfakinghost.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `compilerResolutionHost` (declared in fileloader.go) lives here too —
// it is the inner host the dts-faking host wraps. `vfs.FS` is
// `Arc<dyn Vfs>`; `vfs.Vfs.WriteFile`/`AppendFile`/`Remove`/`Chtimes`/
// `GetAccessibleEntries`/`Stat` panic because the resolver never calls them
// on this wrapper (Go panics identically).
//
// The Go `projectReferenceDtsFakingVfs` aliases `*projectReferenceFileMapper`.
// `vfs.Vfs: Send + Sync` forbids that here — the mapper's
// `Arc<ParsedCommandLine>` fields are not `Sync` (config arenas contain
// `Cell`s), and this workspace forbids `unsafe`. The only mapper state the
// VFS reads is `outputDtsToProjectReference[path].Source` and
// `dtsDirectories`, both fully populated before the parser wraps the host,
// so they are snapshotted into the `Send + Sync` `DtsFakingView` below.

use std::sync::Arc;

use rustc_hash::{FxHashMap, FxHashSet};

use tsc_core::tristate::Tristate;
use tsc_module::ResolutionHost;
use tsc_symlinks::{KnownDirectoryLink, KnownSymlinks};
use tsc_tspath::{self, CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, RootedPath};
use tsc_vfs::fs::{FileInfo, FsError};
use tsc_vfs::{Entries, Vfs};

use crate::host::CompilerHost;
use crate::project_reference_file_mapper::ProjectReferenceFileMapper;

/// `type compilerResolutionHost struct` (fileloader.go) — the plain
/// `ResolutionHost` over the program's `CompilerHost`.
pub struct CompilerResolutionHost {
    pub host: Arc<dyn CompilerHost>,
    pub base_directory: RootedDirectoryPath,
}

impl ResolutionHost for CompilerResolutionHost {
    /// `(h *compilerResolutionHost) FS`.
    fn fs(&self) -> &Arc<dyn Vfs> {
        self.host.fs()
    }
    /// `(h *compilerResolutionHost) GetCurrentDirectory`.
    fn get_current_directory(&self) -> RootedDirectoryPath {
        self.base_directory.clone()
    }
}

/// The `Send + Sync` slice of `ProjectReferenceFileMapper` that the
/// dts-faking VFS reads (see header PORT note).
pub struct DtsFakingView {
    /// `outputDtsToProjectReference[path].source` — only the source path is
    /// needed by `fileExistsIfProjectReferenceDts`.
    pub output_dts_to_source: FxHashMap<PathKey, RootedFilePath>,
    /// Snapshot of `dtsDirectories`.
    pub dts_directories: FxHashSet<PathKey>,
}

/// `type projectReferenceDtsFakingHost struct`.
pub struct ProjectReferenceDtsFakingHost {
    current_directory: RootedDirectoryPath,
    /// `cachedvfs.From(&projectReferenceDtsFakingVfs{...})`.
    fs: Arc<dyn Vfs>,
}

/// `newProjectReferenceDtsFakingHost`.
pub fn new_project_reference_dts_faking_host(
    host: Arc<dyn ResolutionHost>,
    references: &ProjectReferenceFileMapper,
) -> Arc<dyn ResolutionHost> {
    // Create a new host that will fake the dts files
    let current_directory = host.get_current_directory();
    let case_sensitivity = host.fs().case_sensitivity();
    let fs: Arc<dyn Vfs> = tsc_vfs::cachedvfs::from(Arc::new(ProjectReferenceDtsFakingVfs {
        host,
        view: DtsFakingView {
            output_dts_to_source: references
                .output_dts_to_project_reference
                .iter()
                .map(|(path, source)| (path.clone(), source.source.clone()))
                .collect(),
            dts_directories: references.dts_directories.keys().into_iter().collect(),
        },
        known_symlinks: KnownSymlinks::new(case_sensitivity),
    }));
    Arc::new(ProjectReferenceDtsFakingHost {
        current_directory,
        fs,
    })
}

impl ResolutionHost for ProjectReferenceDtsFakingHost {
    /// `(h *projectReferenceDtsFakingHost) FS`.
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }
    /// `(h *projectReferenceDtsFakingHost) GetCurrentDirectory`.
    fn get_current_directory(&self) -> RootedDirectoryPath {
        self.current_directory.clone()
    }
}

/// `type projectReferenceDtsFakingVfs struct`.
struct ProjectReferenceDtsFakingVfs {
    host: Arc<dyn ResolutionHost>,
    view: DtsFakingView,
    known_symlinks: KnownSymlinks,
}

impl ProjectReferenceDtsFakingVfs {
    /// `(fs *projectReferenceDtsFakingVfs) pathKey`.
    fn path_key(&self, path: &RootedPath) -> PathKey {
        self.case_sensitivity().path_key(path)
    }

    /// `(fs *projectReferenceDtsFakingVfs) handleDirectoryCouldBeSymlink`.
    fn handle_directory_could_be_symlink(&self, directory: &RootedDirectoryPath) {
        if tsc_tspath::contains_ignored_directory(directory) {
            return;
        }

        // Because we already watch node_modules, handle symlinks in there
        if !directory.contains_lowercase_directory_sequence("/node_modules/") {
            return;
        }

        let directory_path = self.path_key(&directory.as_path());
        if self
            .known_symlinks
            .directories()
            .load(&directory_path)
            .is_some()
        {
            return;
        }

        let real_directory =
            tsc_tspath::rooted_directory_path_from_path(self.realpath(&directory.as_path()));
        if real_directory == *directory {
            // not symlinked
            return;
        }
        let real_path = self.path_key(&real_directory.as_path());
        if real_path == directory_path {
            // not symlinked
            return;
        }
        self.known_symlinks.set_directory(
            directory.clone(),
            directory_path,
            Some(KnownDirectoryLink {
                real: real_directory,
                real_path,
                // `set_directory` fills `symlink` from its first argument.
                ..Default::default()
            }),
        );
    }

    /// `(fs *projectReferenceDtsFakingVfs) fileExistsUsingSource`.
    fn file_exists_using_source(&self, file: &RootedFilePath) -> bool {
        let file_or_directory = file.as_path();
        let file_path = self.path_key(&file.as_path());
        self.file_or_directory_exists_using_source(
            &file_or_directory,
            &mut |path: &RootedPath| {
                self.file_exists_if_project_reference_dts(&tsc_tspath::rooted_file_path_from_path(
                    path.clone(),
                ))
            },
            &tsc_module::node_module_package_root_for_file(file),
            Some(&|real_file: &RootedFilePath| {
                self.known_symlinks
                    .set_file(file.clone(), file_path.clone(), real_file.clone());
            }),
        )
    }

    /// `(fs *projectReferenceDtsFakingVfs) directoryExistsUsingSource`.
    fn directory_exists_using_source(&self, directory: &RootedDirectoryPath) -> bool {
        self.file_or_directory_exists_using_source(
            &directory.as_path(),
            &mut |path: &RootedPath| {
                self.directory_exists_if_project_reference_decl_dir(
                    &tsc_tspath::rooted_directory_path_from_path(path.clone()),
                )
            },
            &tsc_module::node_module_package_root_for_directory(directory),
            None,
        )
    }

    /// `(fs *projectReferenceDtsFakingVfs) fileOrDirectoryExistsUsingSource`.
    fn file_or_directory_exists_using_source(
        &self,
        file_or_directory: &RootedPath,
        exists_using_source: &mut dyn FnMut(&RootedPath) -> Tristate,
        package_root: &RootedDirectoryPath,
        on_file_exists: Option<&dyn Fn(&RootedFilePath)>,
    ) -> bool {
        // Check current directory or file
        let result = exists_using_source(file_or_directory);
        if result != Tristate::Unknown {
            return result.is_true();
        }

        let file_or_directory_path = self.path_key(file_or_directory);
        if !file_or_directory_path.contains_lowercase_directory_sequence("/node_modules/") {
            return false;
        }
        // Check if the directory or file is a symlinked package
        if !package_root.as_string().is_empty() {
            self.handle_directory_could_be_symlink(package_root);
        }
        let known_directory_links = self.known_symlinks.directories();
        if known_directory_links.size() == 0 {
            return false;
        }
        if on_file_exists.is_some() {
            if self
                .known_symlinks
                .files()
                .load(&file_or_directory_path)
                .is_some()
            {
                return true;
            }
        }

        // If it contains node_modules check if its one of the symlinked path we know of
        let mut exists = false;
        known_directory_links.range(|directory_path, known_directory_link| {
            if directory_path == file_or_directory_path
                || !directory_path.contains_path(&file_or_directory_path)
            {
                return true;
            }
            let Some(link) = known_directory_link else {
                return true;
            };
            let real_file_or_directory = link
                .resolve_file_path(
                    &tsc_tspath::rooted_file_path_from_path(file_or_directory.clone()),
                    self.case_sensitivity(),
                )
                .expect("canonical symlink path did not match its presentation path");
            exists = exists_using_source(&real_file_or_directory.as_path()).is_true();
            if exists {
                if let Some(on_file_exists) = on_file_exists {
                    on_file_exists(&real_file_or_directory);
                }
                return false;
            }
            true
        });
        exists
    }

    /// `(fs *projectReferenceDtsFakingVfs) fileExistsIfProjectReferenceDts`.
    fn file_exists_if_project_reference_dts(&self, file: &RootedFilePath) -> Tristate {
        let source = self
            .view
            .output_dts_to_source
            .get(&self.path_key(&file.as_path()));
        if let Some(source) = source {
            return if self.host.fs().file_exists(source) {
                Tristate::True
            } else {
                Tristate::False
            };
        }
        Tristate::Unknown
    }

    /// `(fs *projectReferenceDtsFakingVfs) directoryExistsIfProjectReferenceDeclDir`.
    fn directory_exists_if_project_reference_decl_dir(
        &self,
        dir: &RootedDirectoryPath,
    ) -> Tristate {
        let dir_path = self.path_key(&dir.as_path());
        for decl_dir_path in &self.view.dts_directories {
            if dir_path.contains_path(decl_dir_path) || decl_dir_path.contains_path(&dir_path) {
                return Tristate::True;
            }
        }
        Tristate::Unknown
    }
}

impl Vfs for ProjectReferenceDtsFakingVfs {
    /// `(fs *projectReferenceDtsFakingVfs) CaseSensitivity`.
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.host.fs().case_sensitivity()
    }

    /// `(fs *projectReferenceDtsFakingVfs) FileExists`.
    fn file_exists(&self, path: &RootedFilePath) -> bool {
        if self.host.fs().file_exists(path) {
            return true;
        }
        if !path.is_declaration_file() {
            return false;
        }
        // Project references go to source file instead of .d.ts file
        self.file_exists_using_source(path)
    }

    /// `(fs *projectReferenceDtsFakingVfs) ReadFile`.
    fn read_file(&self, path: &RootedFilePath) -> Option<String> {
        // Dont need to override as we cannot mimick read file
        self.host.fs().read_file(path)
    }

    /// `(fs *projectReferenceDtsFakingVfs) WriteFile`.
    fn write_file(&self, _path: &RootedFilePath, _data: &str) -> Result<(), FsError> {
        panic!("should not be called by resolver")
    }

    /// `(fs *projectReferenceDtsFakingVfs) AppendFile`.
    fn append_file(&self, _path: &RootedFilePath, _data: &str) -> Result<(), FsError> {
        panic!("should not be called by resolver")
    }

    /// `(fs *projectReferenceDtsFakingVfs) Remove`.
    fn remove(&self, _path: &RootedPath) -> Result<(), FsError> {
        panic!("should not be called by resolver")
    }

    /// `(fs *projectReferenceDtsFakingVfs) Chtimes`.
    fn chtimes(
        &self,
        _path: &RootedPath,
        _a_time: std::time::SystemTime,
        _m_time: std::time::SystemTime,
    ) -> Result<(), FsError> {
        panic!("should not be called by resolver")
    }

    /// `(fs *projectReferenceDtsFakingVfs) DirectoryExists`.
    fn directory_exists(&self, path: &RootedDirectoryPath) -> bool {
        if self.host.fs().directory_exists(path) {
            self.handle_directory_could_be_symlink(path);
            return true;
        }
        self.directory_exists_using_source(path)
    }

    /// `(fs *projectReferenceDtsFakingVfs) GetAccessibleEntries`.
    fn get_accessible_entries(&self, _path: &RootedDirectoryPath) -> Entries {
        panic!("should not be called by resolver")
    }

    /// `(fs *projectReferenceDtsFakingVfs) Stat`.
    fn stat(&self, _path: &RootedPath) -> Option<Arc<dyn FileInfo>> {
        panic!("should not be called by resolver")
    }

    /// `(fs *projectReferenceDtsFakingVfs) Realpath`.
    fn realpath(&self, path: &RootedPath) -> RootedPath {
        if let Some(result) = self.known_symlinks.files().load(&self.path_key(path)) {
            return result.as_path();
        }
        self.host.fs().realpath(path)
    }
}
