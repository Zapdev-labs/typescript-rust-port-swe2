// Ported from tsc/internal/execute/build/compilerHost.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Concurrency: stateless per-task host — no synchronization needed beyond
// the `CompilerHost: Send + Sync` bound (the orchestrator is sequential; see
// the concurrency note in `orchestrator.rs`).

use std::sync::Arc;

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_compiler::host::{CompilerHost, TraceFn};
use tsc_contentmapper::contentmapper::Mapper;
use tsc_contentmapper::host::{Error as ContentMapperError, Project};
use tsc_contentmapper::transform::{
    ParsedSourceFile, SourceFiles, check_supplemental_file_name_collisions, transform_and_parse,
};
use tsc_diagnostics::Message;
use tsc_tsoptions::parsedcommandline::ParsedCommandLine;
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::vfs::Vfs;

use super::host::BuildHost;

/// `type compilerHost struct` — the per-project `CompilerHost` created inside
/// `compileAndEmit`; it adds the task's trace writer and content mapper
/// project on top of the shared [`BuildHost`].
pub(crate) struct BuildCompilerHost {
    /// `host *host`.
    host: Arc<BuildHost>,
    /// `trace func(msg *diagnostics.Message, args ...any)`.
    trace: TraceFn,
    /// `contentMapperProject contentmapper.Project`.
    content_mapper_project: Option<Arc<dyn Project>>,
}

impl BuildCompilerHost {
    pub(crate) fn new(
        host: Arc<BuildHost>,
        trace: TraceFn,
        content_mapper_project: Option<Arc<dyn Project>>,
    ) -> BuildCompilerHost {
        BuildCompilerHost {
            host,
            trace,
            content_mapper_project,
        }
    }
}

impl CompilerHost for BuildCompilerHost {
    /// `(h *compilerHost) FS`.
    fn fs(&self) -> &Arc<dyn Vfs> {
        self.host.fs()
    }

    /// `(h *compilerHost) DefaultLibraryPath`.
    fn default_library_path(&self) -> &RootedDirectoryPath {
        self.host.default_library_path()
    }

    /// `(h *compilerHost) Trace`.
    fn trace(&self, msg: &'static Message, args: &[String]) {
        (self.trace)(msg, args)
    }

    /// `(h *compilerHost) GetSourceFile`.
    fn get_source_file(&self, opts: &SourceFileParseOptions) -> Option<ParsedSourceFile> {
        self.host.get_source_file(opts)
    }

    /// `(h *compilerHost) GetContentMappedSourceFiles`.
    fn get_content_mapped_source_files(
        &self,
        parse_options: &SourceFileParseOptions,
        mapper: &Arc<Mapper>,
    ) -> Result<SourceFiles, ContentMapperError> {
        let Some(project) = &self.content_mapper_project else {
            return Err(ContentMapperError::ProjectUnavailable);
        };
        let Some(content) = self.fs().read_file(&parse_options.file_name) else {
            return Ok(SourceFiles::default());
        };
        let files = transform_and_parse(parse_options, &content, mapper, project)?;
        check_supplemental_file_name_collisions(&files, |f| self.fs().file_exists(f))?;
        Ok(files)
    }

    /// `(h *compilerHost) ContentMapperProject`.
    fn content_mapper_project(&self) -> Option<&Arc<dyn Project>> {
        self.content_mapper_project.as_ref()
    }

    /// `(h *compilerHost) GetResolvedProjectReference`.
    fn get_resolved_project_reference(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<Arc<ParsedCommandLine>> {
        self.host.get_resolved_project_reference(file_name, path)
    }
}
