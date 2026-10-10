// Ported from tsc/internal/compiler/projectreferencefilemapper.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `collections.SyncMap`/`collections.Set` stay `SyncMap`/`SyncSet` —
// the dts-faking VFS aliases the mapper through `Arc` behind the
// `Send + Sync` `vfs.Vfs`/`module.ResolutionHost` bounds.
// `*tsoptions.ParsedCommandLine` is
// `Arc<ParsedCommandLine>` and `*tsoptions.SourceOutputAndProjectReference`
// is `Arc<SourceOutputAndProjectReference>` (matching tsoptions).
//
// `module.ResolvedProjectReference` requires `Send + Sync`, which
// `ParsedCommandLine` cannot satisfy (its config arena contains `Cell`s);
// `ParsedCommandLineRedirect` is a `Send + Sync` snapshot adapter used when
// handing a redirect to the module resolver — see the PORT note in
// tsoptions/parsedcommandline.rs.

use std::collections::HashSet;
use std::sync::Arc;

use rustc_hash::FxHashMap;

use tsc_ast::HasFileName;
use tsc_collections::{SyncMap, SyncSet};
use tsc_module::{ResolutionHost, ResolvedProjectReference};
use tsc_tsoptions::parsedcommandline::{ParsedCommandLine, SourceOutputAndProjectReference};
use tsc_tspath::{PathKey, RootedFilePath};

use crate::project_reference_dts_faking_host::new_project_reference_dts_faking_host;

/// `type projectReferenceFileMapper struct`.
pub struct ProjectReferenceFileMapper {
    pub config: Arc<ParsedCommandLine>,
    pub use_source_of_project_reference: bool,
    /// `dtsDirectories` — populated by the project-reference parser.
    /// `SyncSet` because the dts-faking VFS reads it through a shared `Arc`
    /// (`vfs.Vfs: Send + Sync`).
    pub dts_directories: SyncSet<PathKey>,

    /// `configToProjectReference` — all the resolved references needed. The
    /// `Option` mirrors Go storing a nil `*ParsedCommandLine` for unresolved
    /// references.
    pub config_to_project_reference: FxHashMap<PathKey, Option<Arc<ParsedCommandLine>>>,
    /// `referencesInConfigFile` — map of config file to its references.
    pub references_in_config_file: FxHashMap<PathKey, Vec<PathKey>>,
    pub source_to_project_reference: FxHashMap<PathKey, Arc<SourceOutputAndProjectReference>>,
    pub output_dts_to_project_reference: FxHashMap<PathKey, Arc<SourceOutputAndProjectReference>>,

    /// `realpathDtsToSource` — realpath from .d.ts in node_modules to source
    /// file from project reference needed during parsing. `None` values
    /// mirror Go storing a nil mapping. `SyncMap` because it is written
    /// through `&self` during `preserveSymlinks` resolution.
    pub realpath_dts_to_source: SyncMap<PathKey, Option<Arc<SourceOutputAndProjectReference>>>,
}

/// `type projectReferenceFileMapperBuilder struct`.
pub struct ProjectReferenceFileMapperBuilder {
    /// Go embeds `*projectReferenceFileMapper`; methods delegate to `mapper`.
    /// `Arc` because `resolutionHost` hands the mapper to the dts-faking FS
    /// while the loader still owns it; parse-time map mutation goes through
    /// `Arc::get_mut` before the host is wrapped (see
    /// project_reference_parser.rs).
    pub mapper: Arc<ProjectReferenceFileMapper>,
    pub host: Arc<dyn ResolutionHost>,
}

/// `ParsedCommandLineRedirect` — a `Send + Sync` snapshot of a resolved
/// project reference for the resolver's `&dyn ResolvedProjectReference`
/// parameters (Go passes `*tsoptions.ParsedCommandLine` directly, which is
// `Sync` there). Built per call; the resolver only reads `ConfigName` and
/// `CompilerOptions` during the resolution.
pub struct ParsedCommandLineRedirect {
    config_name: RootedFilePath,
    compiler_options: Option<tsc_core::options_generated::CompilerOptions>,
}

impl ParsedCommandLineRedirect {
    /// Wraps `config` — `configName` mirrors `ParsedCommandLine.ConfigName()`.
    pub fn new(config: &Arc<ParsedCommandLine>) -> Self {
        ParsedCommandLineRedirect {
            config_name: config.config_name().clone(),
            compiler_options: config.compiler_options().cloned(),
        }
    }
}

impl ResolvedProjectReference for ParsedCommandLineRedirect {
    fn config_name(&self) -> &RootedFilePath {
        &self.config_name
    }
    fn compiler_options(&self) -> Option<&tsc_core::options_generated::CompilerOptions> {
        self.compiler_options.as_ref()
    }
}

/// Convenience adapter: `Arc<ParsedCommandLine>` → `&dyn ResolvedProjectReference`
/// via a temporary snapshot. Returns the adapter to bind before the call:
///
/// ```ignore
/// let redirect = redirect.as_deref().map(ParsedCommandLineRedirect::new);
/// resolver.resolve_module_name(name, file, mode, redirect.as_ref().map(|r| r as &dyn ResolvedProjectReference))
/// ```
pub fn as_resolved_project_reference(config: &Arc<ParsedCommandLine>) -> ParsedCommandLineRedirect {
    ParsedCommandLineRedirect::new(config)
}

/// `(p *ParsedCommandLine) CompilerOptions` adapted to the `&Arc<CompilerOptions>`
/// the module resolver expects — clones the stored value into an `Arc`.
pub fn compiler_options_arc(
    config: &Arc<ParsedCommandLine>,
) -> Arc<tsc_core::options_generated::CompilerOptions> {
    config
        .compiler_options()
        .cloned()
        .map(Arc::new)
        .unwrap_or_default()
}

impl ProjectReferenceFileMapper {
    /// `(mapper *projectReferenceFileMapper) resolutionHost`.
    pub fn resolution_host(
        self: &Arc<Self>,
        host: Arc<dyn ResolutionHost>,
    ) -> Arc<dyn ResolutionHost> {
        if self.use_source_of_project_reference && !self.output_dts_to_project_reference.is_empty()
        {
            return new_project_reference_dts_faking_host(host, self.as_ref());
        }
        host
    }

    /// `(mapper *projectReferenceFileMapper) rootConfigPath`.
    pub fn root_config_path(&self) -> PathKey {
        match &self.config.config_file {
            Some(config_file) => config_file.nodes[config_file.source_file]
                .as_source_file()
                .path_key()
                .clone(),
            None => PathKey::default(),
        }
    }

    /// `(mapper *projectReferenceFileMapper) getParseFileRedirect`.
    pub fn get_parse_file_redirect(&self, file: &dyn HasFileName) -> (RootedFilePath, PathKey) {
        if self.use_source_of_project_reference {
            // Map to source file from project reference
            let mut source = self.get_project_reference_from_output_dts(file.path_key());
            if source.is_none() {
                source = self.realpath_dts_to_source.load(file.path_key()).flatten();
            }
            if let Some(source) = source {
                return (source.source.clone(), source.source_path.clone());
            }
        } else {
            // Map to dts file from project reference
            if let Some(output) = self.get_project_reference_from_source(file.path_key()) {
                if !output.output_dts.as_string().is_empty() {
                    return (output.output_dts.clone(), output.output_dts_path.clone());
                }
            }
        }
        (RootedFilePath::default(), PathKey::default())
    }

    /// `(mapper *projectReferenceFileMapper) getResolvedProjectReferences` —
    /// `Option` entries mirror Go's nil `*ParsedCommandLine` for unresolved
    /// references.
    pub fn get_resolved_project_references(&self) -> Vec<Option<Arc<ParsedCommandLine>>> {
        let mut result = Vec::new();
        if let Some(refs) = self.references_in_config_file.get(&self.root_config_path()) {
            result.reserve(refs.len());
            for ref_path in refs {
                result.push(
                    self.config_to_project_reference
                        .get(ref_path)
                        .cloned()
                        .unwrap_or_default(),
                );
            }
        }
        result
    }

    /// `(mapper *projectReferenceFileMapper) getProjectReferenceFromSource`.
    pub fn get_project_reference_from_source(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        self.source_to_project_reference.get(path).cloned()
    }

    /// `(mapper *projectReferenceFileMapper) getProjectReferenceFromOutputDts`.
    pub fn get_project_reference_from_output_dts(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        self.output_dts_to_project_reference.get(path).cloned()
    }

    /// `(mapper *projectReferenceFileMapper) isSourceFromProjectReference`.
    pub fn is_source_from_project_reference(&self, path: &PathKey) -> bool {
        self.use_source_of_project_reference
            && self.get_project_reference_from_source(path).is_some()
    }

    /// `(mapper *projectReferenceFileMapper) getCompilerOptionsForFile`.
    /// PORT: `ParsedCommandLine::compiler_options` stores a value (Go shares
    /// the `*core.CompilerOptions` pointer); wrapping the clone in `Arc`
    /// matches `get_compiler_options_with_redirect`'s signature.
    pub fn get_compiler_options_for_file(
        &self,
        file: &dyn HasFileName,
    ) -> Arc<tsc_core::options_generated::CompilerOptions> {
        let redirect = self.get_redirect_parsed_command_line_for_resolution(file);
        let redirect = redirect.as_ref().map(|r| as_resolved_project_reference(r));
        tsc_module::get_compiler_options_with_redirect(
            &compiler_options_arc(&self.config),
            redirect
                .as_ref()
                .map(|r| r as &dyn ResolvedProjectReference),
        )
    }

    /// `(mapper *projectReferenceFileMapper) getRedirectParsedCommandLineForResolution`.
    pub fn get_redirect_parsed_command_line_for_resolution(
        &self,
        file: &dyn HasFileName,
    ) -> Option<Arc<ParsedCommandLine>> {
        self.get_redirect_for_resolution(file).0
    }

    /// `(mapper *projectReferenceFileMapper) getRedirectForResolution`.
    pub fn get_redirect_for_resolution(
        &self,
        file: &dyn HasFileName,
    ) -> (Option<Arc<ParsedCommandLine>>, RootedFilePath) {
        let path = file.path_key();
        // Check if outputdts of source file from project reference
        if let Some(output) = self.get_project_reference_from_source(path) {
            return (Some(output.resolved.clone()), output.source.clone());
        }

        // Source file from project reference
        if let Some(result_from_dts) = self.get_project_reference_from_output_dts(path) {
            return (
                Some(result_from_dts.resolved.clone()),
                result_from_dts.source.clone(),
            );
        }

        if let Some(realpath_dts_to_source) = self.realpath_dts_to_source.load(path).flatten() {
            return (
                Some(realpath_dts_to_source.resolved.clone()),
                realpath_dts_to_source.source.clone(),
            );
        }
        (None, file.file_name().clone())
    }

    /// `(mapper *projectReferenceFileMapper) getResolvedReferenceFor` — the
    /// `bool` mirrors Go's map `ok` (present-but-nil is `true`).
    pub fn get_resolved_reference_for(
        &self,
        path: &PathKey,
    ) -> (Option<Arc<ParsedCommandLine>>, bool) {
        match self.config_to_project_reference.get(path) {
            Some(config) => (config.clone(), true),
            None => (None, false),
        }
    }

    /// `(mapper *projectReferenceFileMapper) rangeResolvedProjectReference`.
    pub fn range_resolved_project_reference(
        &self,
        f: &mut dyn FnMut(
            &PathKey,
            Option<&Arc<ParsedCommandLine>>,
            &Arc<ParsedCommandLine>,
            usize,
        ) -> bool,
    ) -> bool {
        if self.config.project_references().is_empty() {
            return false;
        }
        let mut seen_ref: HashSet<PathKey> =
            HashSet::with_capacity(self.references_in_config_file.len());
        let root_config_path = self.root_config_path();
        seen_ref.insert(root_config_path.clone());
        let refs = self
            .references_in_config_file
            .get(&root_config_path)
            .cloned()
            .unwrap_or_default();
        self.range_resolved_reference_worker(&refs, f, &self.config.clone(), &mut seen_ref)
    }

    /// `(mapper *projectReferenceFileMapper) rangeResolvedReferenceWorker`.
    fn range_resolved_reference_worker(
        &self,
        references: &[PathKey],
        f: &mut dyn FnMut(
            &PathKey,
            Option<&Arc<ParsedCommandLine>>,
            &Arc<ParsedCommandLine>,
            usize,
        ) -> bool,
        parent: &Arc<ParsedCommandLine>,
        seen_ref: &mut HashSet<PathKey>,
    ) -> bool {
        for (index, path) in references.iter().enumerate() {
            if !seen_ref.insert(path.clone()) {
                continue;
            }
            let config = self
                .config_to_project_reference
                .get(path)
                .cloned()
                .unwrap_or_default();
            if !f(path, config.as_ref(), parent, index) {
                return false;
            }
            if let Some(sub_references) = self.references_in_config_file.get(path).cloned() {
                let config = config.unwrap_or_else(|| self.config.clone());
                if !self.range_resolved_reference_worker(&sub_references, f, &config, seen_ref) {
                    return false;
                }
            }
        }
        true
    }

    /// `(mapper *projectReferenceFileMapper) rangeResolvedProjectReferenceInChildConfig`.
    pub fn range_resolved_project_reference_in_child_config(
        &self,
        child_config: &Arc<ParsedCommandLine>,
        f: &mut dyn FnMut(
            &PathKey,
            Option<&Arc<ParsedCommandLine>>,
            &Arc<ParsedCommandLine>,
            usize,
        ) -> bool,
    ) -> bool {
        let Some(config_file) = &child_config.config_file else {
            return false;
        };
        let child_path = config_file.nodes[config_file.source_file]
            .as_source_file()
            .path_key()
            .clone();
        let mut seen_ref: HashSet<PathKey> =
            HashSet::with_capacity(self.references_in_config_file.len());
        seen_ref.insert(child_path.clone());
        let refs = self
            .references_in_config_file
            .get(&child_path)
            .cloned()
            .unwrap_or_default();
        self.range_resolved_reference_worker(&refs, f, &self.config.clone(), &mut seen_ref)
    }
}

impl ProjectReferenceFileMapperBuilder {
    /// `(builder *projectReferenceFileMapperBuilder) getParseFileRedirect`.
    pub fn get_parse_file_redirect(&self, file: &dyn HasFileName) -> (RootedFilePath, PathKey) {
        if self.mapper.use_source_of_project_reference
            && self
                .mapper
                .get_project_reference_from_output_dts(file.path_key())
                .is_none()
        {
            self.resolve_symlink(file);
        }
        self.mapper.get_parse_file_redirect(file)
    }

    /// `(builder *projectReferenceFileMapperBuilder) getRedirectForResolution`.
    pub fn get_redirect_for_resolution(
        &self,
        file: &dyn HasFileName,
    ) -> (Option<Arc<ParsedCommandLine>>, RootedFilePath) {
        if self
            .mapper
            .get_project_reference_from_source(file.path_key())
            .is_none()
            && self
                .mapper
                .get_project_reference_from_output_dts(file.path_key())
                .is_none()
        {
            self.resolve_symlink(file);
        }
        self.mapper.get_redirect_for_resolution(file)
    }

    /// `(builder *projectReferenceFileMapperBuilder) getCompilerOptionsForFile`.
    pub fn get_compiler_options_for_file(
        &self,
        file: &dyn HasFileName,
    ) -> Arc<tsc_core::options_generated::CompilerOptions> {
        let (redirect, _) = self.get_redirect_for_resolution(file);
        let redirect = redirect.as_ref().map(|r| as_resolved_project_reference(r));
        tsc_module::get_compiler_options_with_redirect(
            &compiler_options_arc(&self.mapper.config),
            redirect
                .as_ref()
                .map(|r| r as &dyn ResolvedProjectReference),
        )
    }

    /// `(builder *projectReferenceFileMapperBuilder) getRedirectParsedCommandLineForResolution`.
    pub fn get_redirect_parsed_command_line_for_resolution(
        &self,
        file: &dyn HasFileName,
    ) -> Option<Arc<ParsedCommandLine>> {
        self.get_redirect_for_resolution(file).0
    }

    /// `(builder *projectReferenceFileMapperBuilder) resolveSymlink`.
    pub fn resolve_symlink(&self, file: &dyn HasFileName) {
        // If preserveSymlinks is true, module resolution wont jump the symlink
        // but the resolved real path may be the .d.ts from project reference
        // Note:: Currently we try the real path only if the
        // file is from node_modules to avoid having to run real path on all file paths
        let path = file.path_key().clone();
        if self.mapper.realpath_dts_to_source.load(&path).is_some() {
            return;
        }
        if !self
            .mapper
            .config
            .resolved_project_reference_paths()
            .is_empty()
            && self
                .mapper
                .config
                .compiler_options()
                .is_some_and(|o| o.preserve_symlinks == tsc_core::tristate::TS_TRUE)
        {
            let file_name = file.file_name();
            // `Path(file.FileName())` — the normalized path key.
            if !path.contains_lowercase_directory_sequence("/node_modules/") {
                self.mapper.realpath_dts_to_source.store(path, None);
            } else {
                let fs = self.host.fs();
                let real_declaration_path = fs
                    .case_sensitivity()
                    .path_key(&fs.realpath(&file_name.as_path()));
                if real_declaration_path == path {
                    self.mapper.realpath_dts_to_source.store(path, None);
                } else {
                    let source = self
                        .mapper
                        .get_project_reference_from_output_dts(&real_declaration_path);
                    self.mapper.realpath_dts_to_source.store(path, source);
                }
            }
        }
    }
}
