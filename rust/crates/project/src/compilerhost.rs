// Ported from tsc/internal/project/compilerhost.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{Arc, Mutex, OnceLock};

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_compiler::host::CompilerHost as CompilerHostTrait;
use tsc_contentmapper::{
    Error as ContentMapperError, Mapper, ParsedSourceFile, Project, ProjectSpec, SourceFiles,
    TransformError, TransformErrorKind, check_supplemental_file_name_collisions,
    transform_and_parse,
};
use tsc_core::context::Context;
use tsc_diagnostics::Message;
use tsc_locale::{DEFAULT, from_context};
use tsc_project_logging::{LogTree, Logger};
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;

use crate::configfileregistry::ConfigFileRegistry;
use crate::configfileregistrybuilder::ConfigFileRegistryBuilder;
use crate::overlayfs::FileHandleSource;
use crate::parsecache::{
    ContentMappedParseCache, ParseCache, content_mapped_parse_cache_key, hash128,
    new_parse_cache_key,
};
use fragile::Fragile;

use crate::snapshotfs::FileSource;
use crate::project::Id;
use crate::session::SessionOptions;
use crate::snapshotfs::{SnapshotFs, SourceFs, new_source_fs};

/// `PORT(sibling)`: the view of `*Project` that `compilerHost` needs —
/// `configFilePath`, `ID()`, and `getCommandLineWithTypingsFiles()`.
/// The sibling session/project worker implements this on `Project`.
pub trait CompilerHostProject: Send + Sync {
    /// `project.configFilePath`.
    fn config_file_path(&self) -> &PathKey;
    /// `project.ID()`.
    fn id(&self) -> &Id;
    /// `project.getCommandLineWithTypingsFiles()`.
    fn get_command_line_with_typings_files(&self) -> Arc<ParsedCommandLine>;
}

/// `PORT(sibling)`: the view of `*ProjectCollectionBuilder` that
/// `compilerHost` needs — its session state, filesystem, parse caches,
/// config-file registry builder, ctx, and content mapper host.
/// The sibling session/project worker implements this on
/// `ProjectCollectionBuilder`.
pub trait CompilerHostBuilder: Send + Sync {
    /// `builder.sessionOptions`.
    fn session_options(&self) -> &SessionOptions;
    /// `builder.fs` — the `*snapshotFsBuilder` as a `FileSource`.
    fn fs(&self) -> Arc<dyn FileSource>;
    /// `builder.parseCache`.
    fn parse_cache(&self) -> &ParseCache;
    /// `builder.contentMappedParseCache`.
    fn content_mapped_parse_cache(&self) -> &ContentMappedParseCache;
    /// `builder.configFileRegistryBuilder`.
    fn config_file_registry_builder(&self) -> &Arc<ConfigFileRegistryBuilder>;
    /// `builder.ctx`.
    fn ctx(&self) -> &Context;
    /// `builder.contentMapperHost`.
    fn content_mapper_host(&self) -> Option<&Arc<dyn tsc_contentmapper::Host>>;
}

/// `PORT(sibling)`: the operations the snapshot/project layers perform on
/// `project.host` — freezing after snapshot finalization and the tracked
/// `sourceFS` (`SeenFile`, `SeenFileOrMissingParentDirectory`, `FS()`).
/// `Project.host` stores `Arc<dyn ProjectCompilerHost>` to erase the
/// concrete `CompilerHostWrapper<B, P>` generics.
pub trait ProjectCompilerHost: Send + Sync {
    /// `project.host.freeze`.
    fn freeze(&self, snapshot_fs: Arc<SnapshotFs>, config_file_registry: ConfigFileRegistry);
    /// `project.host.sourceFS`.
    fn source_fs(&self) -> &Arc<SourceFs>;
    /// `project.host.FS()` — the tracked source filesystem as `vfs.FS`.
    fn fs(&self) -> &Arc<dyn Vfs>;
}

/// `var _ compiler.CompilerHost = (*compilerHost)(nil)`
///
/// PORT: `builder`/`project`/`logger`/`configFileRegistry` are `Option`s
/// cleared by `freeze` — Go nils the pointers and panics in `ensureAlive`.
/// Generic over the sibling [`CompilerHostBuilder`]/[`CompilerHostProject`]
/// views until those ports land.
pub struct CompilerHostWrapper<B: CompilerHostBuilder, P: CompilerHostProject> {
    config_file_path: PathKey,
    session_options: SessionOptions,

    source_fs: Arc<SourceFs>,
    /// `fs_vfs` is `source_fs` erased to `Arc<dyn Vfs>` once — the
    /// `CompilerHost::fs` trait signature hands out `&Arc<dyn Vfs>`.
    fs_vfs: Arc<dyn Vfs>,
    /// `Fragile<ConfigFileRegistry>` — the `CompilerHost` trait requires
    /// `Send + Sync`, but `ConfigFileRegistry` holds `Arc<ParsedCommandLine>`
    /// whose `TsConfigSourceFile`/`Node` internals are `Cell`/`Rc`-based
    /// (`!Send`, `!Sync`). The workspace forbids `unsafe_code`, so
    /// `Fragile` (the external crate's `unsafe impl`) provides the bounds;
    /// it panics on cross-thread access — this port is single-threaded like
    /// the `Rc`-based checker/program pipeline, so that panic is the loud
    /// equivalent of Go's unchecked sharing.
    config_file_registry: Mutex<Option<Fragile<ConfigFileRegistry>>>,

    project: Mutex<Option<Arc<P>>>,
    builder: Mutex<Option<Arc<B>>>,
    logger: Mutex<Option<LogTree>>,
    /// `contentMapperOnce` + `contentMapperProject` — `OnceLock` both gates
    /// lazy initialization and caches the (possibly absent) result.
    content_mapper_project: OnceLock<Option<Arc<dyn Project>>>,
}

/// `newCompilerHost`.
pub fn new_compiler_host<B: CompilerHostBuilder, P: CompilerHostProject>(
    project: Arc<P>,
    builder: Arc<B>,
    logger: LogTree,
) -> CompilerHostWrapper<B, P> {
    let source_fs = Arc::new(new_source_fs(true, builder.fs()));
    CompilerHostWrapper {
        config_file_path: project.config_file_path().clone(),
        session_options: builder.session_options().clone(),
        fs_vfs: source_fs.clone() as Arc<dyn Vfs>,
        source_fs,
        project: Mutex::new(Some(project)),
        builder: Mutex::new(Some(builder)),
        logger: Mutex::new(Some(logger)),
        config_file_registry: Mutex::new(None),
        content_mapper_project: OnceLock::new(),
    }
}

impl<B: CompilerHostBuilder, P: CompilerHostProject> CompilerHostWrapper<B, P> {
    /// `freeze` clears references to mutable state to make the compilerHost
    /// safe for use after the snapshot has been finalized. See the usage in
    /// snapshot.go for more details.
    pub fn freeze(
        &self,
        snapshot_fs: Arc<SnapshotFs>,
        config_file_registry: ConfigFileRegistry,
    ) {
        {
            let mut builder = self.builder.lock().unwrap();
            if builder.is_none() {
                panic!("freeze can only be called once");
            }
            *builder = None;
        }
        self.source_fs
            .set_source(snapshot_fs as Arc<dyn FileSource>);
        self.source_fs.disable_tracking();
        *self.config_file_registry.lock().unwrap() =
            Some(Fragile::new(config_file_registry));
        *self.project.lock().unwrap() = None;
        *self.logger.lock().unwrap() = None;
    }

    /// `sourceFS` — the tracked source filesystem (ProjectCompilerHost).
    pub fn source_fs(&self) -> &Arc<SourceFs> {
        &self.source_fs
    }

    /// `h.FS()` — the tracked source filesystem as `vfs.FS`
    /// (ProjectCompilerHost; `fs_vfs` is `source_fs` erased once).
    pub fn fs_vfs(&self) -> &Arc<dyn Vfs> {
        &self.fs_vfs
    }

    /// `ensureAlive`.
    fn ensure_alive(&self) {
        if self.builder.lock().unwrap().is_none()
            || self.project.lock().unwrap().is_none()
        {
            panic!("method must not be called after snapshot initialization");
        }
    }

    /// `ContentMapperProject`.
    fn content_mapper_project_impl(&self) -> Option<Arc<dyn Project>> {
        self.content_mapper_project
            .get_or_init(|| {
                let builder = self.builder.lock().unwrap();
                let Some(builder) = builder.as_ref() else {
                    return None;
                };
                let Some(host) = builder.content_mapper_host() else {
                    return None;
                };
                let project = self.project.lock().unwrap();
                let Some(project) = project.as_ref() else {
                    return None;
                };
                let command_line = project.get_command_line_with_typings_files();
                if command_line.content_mappers().is_empty() {
                    return None;
                }
                host.project(&ProjectSpec {
                    config_file_name: command_line.config_name().clone(),
                    mappers: command_line.content_mappers().to_vec(),
                    compiler_options: command_line
                        .compiler_options()
                        .cloned()
                        .map(Arc::new),
                })
            })
            .clone()
    }
}

/// `var _ ProjectCompilerHost = (*compilerHost)(nil)` — the view
/// `Project.host` stores to erase the `B`/`P` generics.
impl<B: CompilerHostBuilder, P: CompilerHostProject> ProjectCompilerHost
    for CompilerHostWrapper<B, P>
{
    fn freeze(&self, snapshot_fs: Arc<SnapshotFs>, config_file_registry: ConfigFileRegistry) {
        CompilerHostWrapper::freeze(self, snapshot_fs, config_file_registry)
    }
    fn source_fs(&self) -> &Arc<SourceFs> {
        &self.source_fs
    }
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs_vfs
    }
}

impl<B: CompilerHostBuilder, P: CompilerHostProject> CompilerHostTrait
    for CompilerHostWrapper<B, P>
{
    /// `FS`.
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs_vfs
    }

    /// `DefaultLibraryPath`.
    fn default_library_path(&self) -> &RootedDirectoryPath {
        &self.session_options.default_library_path
    }

    /// `Trace`.
    fn trace(&self, msg: &'static Message, args: &[String]) {
        let localized = msg.localize(&DEFAULT, args);
        if let Some(logger) = self.logger.lock().unwrap().as_ref() {
            logger.log(format_args!("{localized}"));
        }
    }

    /// `GetSourceFile`. Files are cached in parseCache and acquired
    /// immediately for the in-progress program.
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<ParsedSourceFile> {
        self.ensure_alive();
        if let Some(fh) = self
            .source_fs
            .get_file_by_path(&opts.file_name, &opts.path_key)
        {
            let key = new_parse_cache_key(opts.clone(), fh.hash(), fh.kind());
            let builder = self.builder.lock().unwrap();
            let builder = builder.as_ref().unwrap();
            let parsed = builder.parse_cache().acquire(key, &fh);
            return Some(parsed.lock().unwrap().clone());
        }
        None
    }

    /// `GetContentMappedSourceFiles`.
    fn get_content_mapped_source_files(
        &self,
        parse_options: &SourceFileParseOptions,
        mapper: &Arc<Mapper>,
    ) -> Result<SourceFiles, ContentMapperError> {
        self.ensure_alive();
        let Some(fh) = self
            .source_fs
            .get_file_by_path(&parse_options.file_name, &parse_options.path_key)
        else {
            return Ok(SourceFiles::default());
        };
        // Resolve the content-mapper project BEFORE locking `builder` —
        // `content_mapper_project_impl` locks `self.builder`/`self.project`
        // itself (std `Mutex` is non-reentrant).
        let Some(project) = self.content_mapper_project_impl() else {
            return Err(ContentMapperError::ProjectUnavailable);
        };
        let builder_guard = self.builder.lock().unwrap();
        let builder = builder_guard.as_ref().unwrap();
        let diagnostic_locale = from_context(builder.ctx());
        let identity = project.identity(mapper).map_err(|e| {
            ContentMapperError::Transform(TransformError::new(
                TransformErrorKind::Project,
                Some(e),
            ))
        })?;
        let transform_identity = hash128(identity.as_bytes());
        let key = content_mapped_parse_cache_key(
            parse_options.clone(),
            fh.hash(),
            transform_identity,
            &diagnostic_locale,
        );
        let cache = builder.content_mapped_parse_cache();
        let files = cache.acquire_or_error(key.clone(), || {
            let mut files = transform_and_parse(parse_options, fh.content(), mapper, &project)?;
            // `files.Canonical.Hash = key.Hash`
            let canonical = &mut files.canonical;
            canonical.nodes[canonical.file].as_source_file_mut().hash = key.hash;
            for supplemental in &mut files.supplemental {
                supplemental.nodes[supplemental.file]
                    .as_source_file_mut()
                    .hash = key.hash;
            }
            // PORT: Go ran `binder.BindSourceFile` on each file here. The Rust
            // binder appends into the program's global `Vec<Symbol>`, so
            // binding is deferred to the program — see the PORT note in
            // `new_parse_cache`.
            Ok::<_, ContentMapperError>(files)
        });
        let files = match files {
            Ok(files) => files,
            Err(e) => return Err(e),
        };
        let files = files.lock().unwrap().clone();
        if let Err(err) = check_supplemental_file_name_collisions(&files, |path| {
            self.source_fs.file_exists(path)
        }) {
            cache.deref(&key);
            return Err(err);
        }
        Ok(files)
    }

    /// `ContentMapperProject`.
    fn content_mapper_project(&self) -> Option<&Arc<dyn Project>> {
        // Trait signature demands a reference; the OnceLock keeps the value
        // alive inside `self`.
        self.content_mapper_project_impl();
        self.content_mapper_project
            .get()
            .and_then(|p| p.as_ref())
    }

    /// `GetResolvedProjectReference`.
    fn get_resolved_project_reference(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<ParsedCommandLine>> {
        let builder = self.builder.lock().unwrap();
        if let Some(builder) = builder.as_ref() {
            // acquireConfigForProject will bypass sourceFS, so track the
            // file here.
            self.source_fs.track(file_name);
            let project = self.project.lock().unwrap();
            let project = project.as_ref().unwrap();
            builder.config_file_registry_builder().acquire_config_for_project(
                file_name,
                path,
                project.id(),
                // `logger` may already be frozen-cleared only after builder
                // is gone; alive implies a logger.
                &self
                    .logger
                    .lock()
                    .unwrap()
                    .clone()
                    .unwrap_or_else(LogTree::none),
            )
        } else {
            self.config_file_registry
                .lock()
                .unwrap()
                .as_ref()
                .and_then(|registry| registry.get().get_config(path))
        }
    }
}
