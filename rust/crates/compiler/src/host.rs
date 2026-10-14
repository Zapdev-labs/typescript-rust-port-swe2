// Ported from tsc/internal/compiler/host.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `*ast.SourceFile` becomes `ParsedSourceFile` (`NodeId` + arena).
// `vfs.FS` is `Arc<dyn Vfs>`; `contentmapper.Project` is
// `Option<Arc<dyn Project>>` (Go nil). The `trace` callback's `...any`
// args are `&[String]` (pre-stringified).

use std::sync::Arc;

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_contentmapper::{
    Error as ContentMapperError, Mapper, ParsedSourceFile, Project, SourceFiles,
};
use tsc_diagnostics::Message;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tsoptions::tsconfigparsing::ExtendedConfigCache;
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;

/// `type CompilerHost interface`.
///
/// PORT: `Send + Sync` — the host is shared through `Arc` inside
/// `module::ResolutionHost` implementations (`Send + Sync` bounds there).
pub trait CompilerHost: Send + Sync {
    fn fs(&self) -> &Arc<dyn Vfs>;
    fn default_library_path(&self) -> &RootedDirectoryPath;
    /// `Trace(msg, args ...any)` — Go's `...any` args arrive already
    /// stringified (`module.DiagAndArgs.args` is `[]string`).
    fn trace(&self, msg: &'static Message, args: &[String]);
    /// `GetSourceFile` — parses `opts`'s file from the FS, or `None` when
    /// the file cannot be read.
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<ParsedSourceFile>;
    /// `GetContentMappedSourceFiles` — produces the source files for a
    /// content-mapped (foreign) file by running `mapper`'s transform on the
    /// file's content. The caller resolves the mapper (and owns the failure
    /// accounting), so implementations must use it as-is. It returns `Ok` of
    /// a default `SourceFiles` if the file cannot be read, or an error if the
    /// transform fails or the mapper produces invalid position mappings.
    /// Implementations may cache successful results.
    fn get_content_mapped_source_files(
        &self,
        parse_options: &SourceFileParseOptions,
        mapper: &Arc<Mapper>,
    ) -> Result<SourceFiles, ContentMapperError>;
    /// `ContentMapperProject` — the project-scoped content mapper used by
    /// this host, or `None` when the command line has no content mappers.
    /// The project owns transform identity and lifecycle state.
    fn content_mapper_project(&self) -> Option<&Arc<dyn Project>>;
    /// `GetResolvedProjectReference`.
    ///
    /// PORT: `Arc` because `ParsedCommandLine::parse_input_output_names`
    /// self-links `SourceOutputAndProjectReference::resolved` through the
    /// `Arc` (Go stores `p` back-pointers).
    fn get_resolved_project_reference(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<ParsedCommandLine>>;
}

/// `func(msg *diagnostics.Message, args ...any)` — args pre-stringified.
pub type TraceFn = Box<dyn Fn(&'static Message, &[String]) + Send + Sync>;

/// `type compilerHost struct`.
pub struct BasicCompilerHost {
    fs: Arc<dyn Vfs>,
    default_library_path: RootedDirectoryPath,
    extended_config_cache: Option<Arc<dyn ExtendedConfigCache + Send + Sync>>,
    trace: TraceFn,
    content_mapper_project: Option<Arc<dyn Project>>,
}

/// `NewCachedFSCompilerHost`.
pub fn new_cached_fs_compiler_host(
    fs: Arc<dyn Vfs>,
    default_library_path: RootedDirectoryPath,
    extended_config_cache: Option<Arc<dyn ExtendedConfigCache + Send + Sync>>,
    trace: Option<TraceFn>,
    content_mapper_project: Option<Arc<dyn Project>>,
) -> BasicCompilerHost {
    new_compiler_host(
        tsc_vfs::cachedvfs::from(fs),
        default_library_path,
        extended_config_cache,
        trace,
        content_mapper_project,
    )
}

/// `NewCompilerHost`.
pub fn new_compiler_host(
    fs: Arc<dyn Vfs>,
    default_library_path: RootedDirectoryPath,
    extended_config_cache: Option<Arc<dyn ExtendedConfigCache + Send + Sync>>,
    trace: Option<TraceFn>,
    content_mapper_project: Option<Arc<dyn Project>>,
) -> BasicCompilerHost {
    let trace = trace.unwrap_or_else(|| Box::new(|_, _| {}));
    BasicCompilerHost {
        fs,
        default_library_path,
        extended_config_cache,
        trace,
        content_mapper_project,
    }
}

impl CompilerHost for BasicCompilerHost {
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }

    fn default_library_path(&self) -> &RootedDirectoryPath {
        &self.default_library_path
    }

    fn trace(&self, msg: &'static Message, args: &[String]) {
        (self.trace)(msg, args)
    }

    /// `(h *compilerHost) GetSourceFile`.
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<ParsedSourceFile> {
        let text = self.fs().read_file(&opts.file_name)?;
        let (file, nodes) = tsc_parser::parse_source_file(
            opts.clone(),
            &text,
            tsc_core::core::ensure_script_kind_from_file_name(&opts.file_name),
        );
        Some(ParsedSourceFile {
            file,
            nodes: std::rc::Rc::new(tsc_ast::NodeArenaBuf::new(nodes)),
        })
    }

    /// `(h *compilerHost) GetContentMappedSourceFiles`.
    fn get_content_mapped_source_files(
        &self,
        parse_options: &SourceFileParseOptions,
        mapper: &Arc<Mapper>,
    ) -> Result<SourceFiles, ContentMapperError> {
        let Some(project) = self.content_mapper_project.as_ref() else {
            return Err(tsc_contentmapper::err_project_unavailable());
        };
        let Some(content) = self.fs().read_file(&parse_options.file_name) else {
            return Ok(SourceFiles::default());
        };
        let files =
            tsc_contentmapper::transform_and_parse(parse_options, &content, mapper, project)?;
        tsc_contentmapper::check_supplemental_file_name_collisions(&files, |path| {
            self.fs().file_exists(path)
        })?;
        Ok(files)
    }

    fn content_mapper_project(&self) -> Option<&Arc<dyn Project>> {
        self.content_mapper_project.as_ref()
    }

    /// `(h *compilerHost) GetResolvedProjectReference`.
    fn get_resolved_project_reference(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<ParsedCommandLine>> {
        // Go ignores the errors (`commandLine, _ :=`).
        tsc_tsoptions::tsconfigparsing::get_parsed_command_line_of_config_file_path(
            file_name.clone(),
            path.clone(),
            None,
            None,
            &self.fs,
            self.extended_config_cache
                .as_deref()
                .map(|cache| cache as &dyn ExtendedConfigCache),
        )
        .ok()
        .map(Arc::new)
    }
}
