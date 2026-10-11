// Ported from tsc/internal/tsoptions/parsedcommandline.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

use tsc_ast::diagnostic::{DiagnosticRef, new_compiler_diagnostic};
use tsc_collections::Set;
use tsc_contentmapper::Mapper;
use tsc_core::core;
use tsc_core::options_generated::CompilerOptions;
use tsc_core::projectreference::{ProjectReference, resolve_project_reference_path};
use tsc_diagnostics::{self as diagnostics};
use tsc_glob::Glob;
use tsc_locale::Locale;
use tsc_outputpaths::{self as outputpaths, OutputPathsHost};
use tsc_tspath::{self as tspath, CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_vfs::Vfs;
use tsc_vfs::vfsmatch;

use crate::parsedoptions::ParsedOptions;
use crate::tsconfigparsing::{
    ConfigFileSpecs, TsConfigSourceFile, get_file_names_from_config_specs,
};
use crate::value::Value;
use crate::wildcarddirectories::get_wildcard_directories;

const FILE_GLOB_PATTERN: &str = "*.{js,jsx,mjs,cjs,ts,tsx,mts,cts,json}";
const RECURSIVE_FILE_GLOB_PATTERN: &str = "**/*.{js,jsx,mjs,cjs,ts,tsx,mts,cts,json}";

/// `type SourceOutputAndProjectReference struct`.
#[derive(Debug)]
pub struct SourceOutputAndProjectReference {
    pub source: RootedFilePath,
    pub source_path: PathKey,
    pub output_dts: RootedFilePath,
    pub output_dts_path: PathKey,
    pub resolved: Arc<ParsedCommandLine>,
}

/// The two maps `ParseInputOutputNames` builds together under a single
/// `sync.Once` in Go.
#[derive(Default)]
pub(crate) struct SourceAndOutputMaps {
    pub(crate) source_to_project_reference: HashMap<PathKey, Arc<SourceOutputAndProjectReference>>,
    pub(crate) output_dts_to_project_reference:
        HashMap<PathKey, Arc<SourceOutputAndProjectReference>>,
}

/// `type ParsedCommandLine struct`.
///
/// PORT: each Go `sync.Once` + field pair becomes a `OnceLock`; `withFileNames`
/// and `ReloadFileNamesOfParsedCommandLine` copy a computed value into the new
/// instance's `OnceLock`, matching Go copying the raw fields. `errors` is a
/// `Mutex<Vec<DiagnosticRef>>` because `checkSourceFilesBelongToPath` appends
/// through a `&self` receiver (from `CommonSourceDirectory`).
#[derive(Default)]
pub struct ParsedCommandLine {
    /// `ParsedConfig *ParsedOptions`
    pub parsed_config: Option<ParsedOptions>,

    /// `ConfigFile *TsConfigSourceFile` — used in Program and
    /// ExecuteCommandLine.
    pub config_file: Option<Arc<TsConfigSourceFile>>,
    /// `Errors []*ast.Diagnostic`
    pub errors: Mutex<Vec<DiagnosticRef>>,
    /// `Raw any`
    pub raw: Option<Value>,
    /// `CompileOnSave *bool`
    pub compile_on_save: Option<bool>,

    pub(crate) config_file_specs: Option<Arc<ConfigFileSpecs>>,
    pub(crate) base_directory: RootedDirectoryPath,
    pub(crate) case_sensitivity: CaseSensitivity,
    pub(crate) wildcard_directories: OnceLock<Option<HashMap<RootedDirectoryPath, bool>>>,
    pub(crate) include_globs: OnceLock<Vec<Glob>>,

    pub(crate) source_and_output_maps: OnceLock<SourceAndOutputMaps>,

    pub(crate) common_source_directory: OnceLock<RootedDirectoryPath>,

    pub(crate) resolved_project_reference_paths: OnceLock<Vec<RootedFilePath>>,

    pub literal_file_names_len: usize,
    pub root_file_names_for_diagnostics: Vec<String>,
    pub(crate) file_paths: OnceLock<Set<PathKey>>,

    // PORT: `ContentMapperExtensions()` is a pure function of `ContentMappers`
    // in Go; here it must return `&[String]` for `OutputPathsHost`, so it is
    // computed eagerly and kept in sync by `set_parsed_options`.
    pub(crate) content_mapper_extensions_cache: Vec<String>,

    pub(crate) locale: OnceLock<Locale>,

    // PORT: `ConfigName()` returns `&RootedFilePath` for the
    // `ResolvedProjectReference` trait; the empty-path fallback for a nil
    // `ConfigFile` lives here so the trait can return a reference.
    pub(crate) empty_config_name: RootedFilePath,
}

impl std::fmt::Debug for ParsedCommandLine {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ParsedCommandLine")
            .field("config_file", &self.config_file)
            .field("base_directory", &self.base_directory)
            .finish_non_exhaustive()
    }
}

/// `NewParsedCommandLine`.
pub fn new_parsed_command_line(
    compiler_options: CompilerOptions,
    root_file_names: Vec<RootedFilePath>,
    project_references: Vec<ProjectReference>,
    base_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> ParsedCommandLine {
    ParsedCommandLine {
        parsed_config: Some(ParsedOptions {
            compiler_options: Some(compiler_options),
            file_names: root_file_names,
            project_references,
            ..Default::default()
        }),
        base_directory,
        case_sensitivity,
        ..Default::default()
    }
}

/// Copy the value of a `OnceLock` into a fresh one (Go copies the raw field).
fn clone_once_lock<T: Clone>(src: &OnceLock<T>) -> OnceLock<T> {
    match src.get() {
        Some(v) => OnceLock::from(v.clone()),
        None => OnceLock::new(),
    }
}

impl ParsedCommandLine {
    /// `(p *ParsedCommandLine) WithFileNames`.
    pub fn with_file_names(&self, file_names: Vec<RootedFilePath>) -> ParsedCommandLine {
        let mut parsed_config = self.parsed_config.clone().unwrap_or_default();
        parsed_config.file_names = file_names;
        ParsedCommandLine {
            parsed_config: Some(parsed_config),
            config_file: self.config_file.clone(),
            errors: Mutex::new(
                self.errors
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone(),
            ),
            raw: self.raw.clone(),
            compile_on_save: self.compile_on_save,
            config_file_specs: self.config_file_specs.clone(),
            base_directory: self.base_directory.clone(),
            case_sensitivity: self.case_sensitivity,
            wildcard_directories: clone_once_lock(&self.wildcard_directories),
            include_globs: clone_once_lock(&self.include_globs),
            literal_file_names_len: self.literal_file_names_len,
            root_file_names_for_diagnostics: self.root_file_names_for_diagnostics.clone(),
            content_mapper_extensions_cache: self.content_mapper_extensions_cache.clone(),
            ..Default::default()
        }
    }

    /// `(p *ParsedCommandLine) getConfigFileSpecs`.
    pub(crate) fn get_config_file_specs(&self) -> Option<Arc<ConfigFileSpecs>> {
        if let Some(specs) = self.config_file_specs.as_ref() {
            return Some(specs.clone());
        }
        if let Some(config_file) = self.config_file.as_ref() {
            return config_file.config_file_specs();
        }
        None
    }

    /// `(p *ParsedCommandLine) fileGlobPatterns` — the include file glob
    /// patterns for this command line, augmenting the built-in patterns with
    /// the extensions registered by its content mappers so that created
    /// content-mapped files are recognized as possible root files.
    fn file_glob_patterns(&self) -> (String, String) {
        let mapper_extensions = self.content_mapper_extensions();
        if mapper_extensions.is_empty() {
            return (
                FILE_GLOB_PATTERN.to_string(),
                RECURSIVE_FILE_GLOB_PATTERN.to_string(),
            );
        }
        let mut extensions: Vec<&str> = Vec::with_capacity(9 + mapper_extensions.len());
        extensions.extend(["js", "jsx", "mjs", "cjs", "ts", "tsx", "mts", "cts", "json"]);
        for extension in mapper_extensions {
            extensions.push(extension.strip_prefix('.').unwrap_or(extension));
        }
        let file_glob = format!("*.{{{}}}", extensions.join(","));
        (file_glob.clone(), format!("**/{}", file_glob))
    }

    /// `(p *ParsedCommandLine) ConfigName`.
    pub fn config_name(&self) -> &RootedFilePath {
        match self.config_file.as_ref() {
            Some(config_file) => config_file.file_name(),
            None => &self.empty_config_name,
        }
    }

    /// `(p *ParsedCommandLine) ConfigFileName`.
    pub fn config_file_name(&self) -> &RootedFilePath {
        let config_name = self.config_name();
        if !config_name.is_empty() {
            return config_name;
        }
        self.compiler_options_config_file_path()
    }

    fn compiler_options_config_file_path(&self) -> &RootedFilePath {
        match self
            .parsed_config
            .as_ref()
            .and_then(|c| c.compiler_options.as_ref())
        {
            Some(options) => &options.config_file_path,
            None => &self.empty_config_name,
        }
    }

    /// `(p *ParsedCommandLine) SourceToProjectReference`.
    pub fn source_to_project_reference(
        &self,
    ) -> Option<&HashMap<PathKey, Arc<SourceOutputAndProjectReference>>> {
        self.source_and_output_maps
            .get()
            .map(|m| &m.source_to_project_reference)
    }

    /// `(p *ParsedCommandLine) OutputDtsToProjectReference`.
    pub fn output_dts_to_project_reference(
        &self,
    ) -> Option<&HashMap<PathKey, Arc<SourceOutputAndProjectReference>>> {
        self.source_and_output_maps
            .get()
            .map(|m| &m.output_dts_to_project_reference)
    }

    /// `(p *ParsedCommandLine) ParseInputOutputNames`.
    ///
    /// PORT: `&Arc<Self>` because each `SourceOutputAndProjectReference`'s
    /// `Resolved` field points back at this command line (Go stores `p`).
    pub fn parse_input_output_names(self: &Arc<Self>) {
        self.source_and_output_maps.get_or_init(|| {
            let mut source_to_output: HashMap<PathKey, Arc<SourceOutputAndProjectReference>> =
                HashMap::new();
            let mut output_dts_to_source: HashMap<PathKey, Arc<SourceOutputAndProjectReference>> =
                HashMap::new();

            for (output_dts_file_name, source_file_name) in
                self.get_output_declaration_and_source_file_names()
            {
                let project_reference = Arc::new(SourceOutputAndProjectReference {
                    source_path: self.case_sensitivity.path_key(&source_file_name.as_path()),
                    source: source_file_name,
                    output_dts_path: PathKey::default(),
                    output_dts: output_dts_file_name,
                    resolved: self.clone(),
                });
                if !project_reference.output_dts.is_empty() {
                    let output_dts_path = self
                        .case_sensitivity
                        .path_key(&project_reference.output_dts.as_path());
                    let keyed = Arc::new(SourceOutputAndProjectReference {
                        output_dts_path: output_dts_path.clone(),
                        // the same struct is shared between the two maps in
                        // Go; here the map entries share one `Arc` and the
                        // `output_dts_path` field is filled in before
                        // insertion.
                        source_path: project_reference.source_path.clone(),
                        source: project_reference.source.clone(),
                        output_dts: project_reference.output_dts.clone(),
                        resolved: self.clone(),
                    });
                    output_dts_to_source.insert(output_dts_path, keyed.clone());
                    source_to_output.insert(project_reference.source_path.clone(), keyed);
                } else {
                    source_to_output
                        .insert(project_reference.source_path.clone(), project_reference);
                }
            }
            SourceAndOutputMaps {
                source_to_project_reference: source_to_output,
                output_dts_to_project_reference: output_dts_to_source,
            }
        });
    }

    /// `(p *ParsedCommandLine) CommonSourceDirectory`.
    pub fn common_source_directory(&self) -> RootedDirectoryPath {
        self.common_source_directory
            .get_or_init(|| {
                let files = || -> Vec<RootedFilePath> {
                    self.parsed_config
                        .as_ref()
                        .map(|parsed_config| {
                            core::filter(&parsed_config.file_names, |file| {
                                !(parsed_config
                                    .compiler_options
                                    .as_ref()
                                    .is_some_and(|o| o.no_emit_for_js_files.is_true())
                                    && file.has_js_file_extension())
                                    && !file.is_declaration_file()
                            })
                            .into_owned()
                        })
                        .unwrap_or_default()
                };

                let options = self
                    .parsed_config
                    .as_ref()
                    .and_then(|c| c.compiler_options.as_ref())
                    .cloned()
                    .unwrap_or_default();
                outputpaths::get_common_source_directory(
                    &options,
                    files,
                    self.base_directory.clone(),
                    self.case_sensitivity,
                    Some(
                        &|files: &[RootedFilePath], root_directory: RootedDirectoryPath| {
                            self.check_source_files_belong_to_path(files, root_directory)
                        },
                    ),
                )
            })
            .clone()
    }

    /// `(p *ParsedCommandLine) checkSourceFilesBelongToPath`.
    fn check_source_files_belong_to_path(
        &self,
        source_files: &[RootedFilePath],
        root_directory: RootedDirectoryPath,
    ) -> bool {
        let mut all_files_belong_to_path = true;
        for file in source_files {
            if !self
                .case_sensitivity
                .contains_file_path(&root_directory, file)
            {
                self.errors
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .push(new_compiler_diagnostic(
                        &diagnostics::File_0_is_not_under_rootDir_1_rootDir_is_expected_to_contain_all_source_files,
                        &[
                            Value::Str(
                                self.case_sensitivity
                                    .path_key(&file.as_path())
                                    .as_string()
                                    .to_string(),
                            ),
                            Value::Str(root_directory.as_string().to_string()),
                        ],
                    ));
                all_files_belong_to_path = false;
            }
        }

        all_files_belong_to_path
    }

    /// `(p *ParsedCommandLine) BaseDirectory`.
    pub fn base_directory(&self) -> &RootedDirectoryPath {
        &self.base_directory
    }

    /// `(p *ParsedCommandLine) CaseSensitivity`.
    pub fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }

    /// `(p *ParsedCommandLine) getOutputDeclarationAndSourceFileNames` —
    /// yields `(outputDts, sourceFileName)` pairs.
    fn get_output_declaration_and_source_file_names(
        &self,
    ) -> Vec<(RootedFilePath, RootedFilePath)> {
        let mut result = Vec::new();
        if let Some(parsed_config) = self.parsed_config.as_ref() {
            let options = self.compiler_options_or_default();
            for file_name in &parsed_config.file_names {
                let mut output_dts = RootedFilePath::default();
                if !file_name.is_declaration_file()
                    && !file_name.extension_is(tspath::EXTENSION_JSON)
                {
                    output_dts = outputpaths::get_output_declaration_file_name_worker(
                        file_name, &options, self,
                    );
                }
                result.push((output_dts, file_name.clone()));
            }
        }
        result
    }

    /// `p.CompilerOptions()` with Go's nil-receiver/`nil` `CompilerOptions`
    /// collapse; returns an owned clone for contexts needing `&CompilerOptions`.
    fn compiler_options_or_default(&self) -> CompilerOptions {
        self.parsed_config
            .as_ref()
            .and_then(|c| c.compiler_options.clone())
            .unwrap_or_default()
    }

    /// `(p *ParsedCommandLine) GetOutputFileNames`.
    pub fn get_output_file_names(&self) -> Vec<RootedFilePath> {
        let mut result = Vec::new();
        if let Some(parsed_config) = self.parsed_config.as_ref() {
            let options = self.compiler_options_or_default();
            for file_name in &parsed_config.file_names {
                if file_name.is_declaration_file() {
                    continue;
                }
                let js_file_name = outputpaths::get_output_js_file_name(file_name, &options, self);
                let is_json = file_name.extension_is(tspath::EXTENSION_JSON);
                if !js_file_name.is_empty() {
                    result.push(js_file_name.clone());
                    if !is_json {
                        let source_map =
                            outputpaths::get_source_map_file_path(&js_file_name, &options);
                        if !source_map.is_empty() {
                            result.push(source_map);
                        }
                    }
                }
                if is_json {
                    continue;
                }
                if options.get_emit_declarations() {
                    let dts_file_name = outputpaths::get_output_declaration_file_name_worker(
                        file_name, &options, self,
                    );
                    result.push(dts_file_name.clone());
                    if self.get_content_mapper_for_file_name(file_name).is_none()
                        && options.get_are_declaration_maps_enabled()
                    {
                        result.push(dts_file_name.append_suffix(".map"));
                    }
                }
            }
        }
        result
    }

    /// `(p *ParsedCommandLine) GetBuildInfoFileName`.
    pub fn get_build_info_file_name(&self) -> RootedFilePath {
        outputpaths::get_build_info_file_name(
            &self.compiler_options_or_default(),
            self.case_sensitivity,
        )
    }

    /// `(p *ParsedCommandLine) WildcardDirectories` — the cached wildcard
    /// directories, initializing them if needed. `None` mirrors Go's nil map.
    pub fn wildcard_directories(&self) -> Option<&HashMap<RootedDirectoryPath, bool>> {
        self.wildcard_directories
            .get_or_init(|| {
                self.get_config_file_specs().and_then(|specs| {
                    get_wildcard_directories(
                        &specs.validated_include_specs,
                        &specs.validated_exclude_specs,
                        &self.base_directory,
                        self.case_sensitivity,
                    )
                })
            })
            .as_ref()
    }

    /// `(p *ParsedCommandLine) WildcardDirectoryGlobs`.
    pub fn wildcard_directory_globs(&self) -> Option<&Vec<Glob>> {
        let wildcard_directories = self.wildcard_directories()?;
        Some(self.include_globs.get_or_init(|| {
            let (file_glob, recursive_file_glob) = self.file_glob_patterns();
            let mut globs = Vec::with_capacity(wildcard_directories.len());
            for (dir, recursive) in wildcard_directories {
                let pattern = tspath::combine_paths(
                    dir.as_string(),
                    &[if *recursive {
                        &recursive_file_glob
                    } else {
                        &file_glob
                    }],
                );
                if let Ok(parsed) = tsc_glob::parse(&pattern) {
                    globs.push(parsed);
                }
            }
            globs
        }))
    }

    /// `(p *ParsedCommandLine) LiteralFileNames` — normalized file names
    /// explicitly specified in `files`.
    pub fn literal_file_names(&self) -> Option<&[RootedFilePath]> {
        if self.config_file.is_some() {
            let file_names = self.file_names();
            return Some(&file_names[..self.literal_file_names_len]);
        }
        None
    }

    /// `(p *ParsedCommandLine) SetParsedOptions`.
    pub fn set_parsed_options(&mut self, options: ParsedOptions) {
        // PORT: keep the `&[String]` extension cache in sync, since
        // `content_mapper_extensions` cannot recompute from `ContentMappers`
        // through a `&self` borrow.
        self.content_mapper_extensions_cache =
            Self::compute_content_mapper_extensions(options.content_mappers.as_slice());
        self.parsed_config = Some(options);
    }

    /// `(p *ParsedCommandLine) SetCompilerOptions`.
    pub fn set_compiler_options(&mut self, options: CompilerOptions) {
        if let Some(parsed_config) = self.parsed_config.as_mut() {
            parsed_config.compiler_options = Some(options);
        }
    }

    /// `(p *ParsedCommandLine) CompilerOptions`.
    pub fn compiler_options(&self) -> Option<&CompilerOptions> {
        self.parsed_config
            .as_ref()
            .and_then(|c| c.compiler_options.as_ref())
    }

    /// `(p *ParsedCommandLine) SetTypeAcquisition`.
    pub fn set_type_acquisition(&mut self, options: tsc_core::options_generated::TypeAcquisition) {
        if let Some(parsed_config) = self.parsed_config.as_mut() {
            parsed_config.type_acquisition = Some(options);
        }
    }

    /// `(p *ParsedCommandLine) TypeAcquisition`.
    pub fn type_acquisition(&self) -> Option<&tsc_core::options_generated::TypeAcquisition> {
        self.parsed_config
            .as_ref()
            .and_then(|c| c.type_acquisition.as_ref())
    }

    /// `(p *ParsedCommandLine) FileNames` — all file names matched by files,
    /// include, and exclude patterns.
    pub fn file_names(&self) -> &[RootedFilePath] {
        match self.parsed_config.as_ref() {
            Some(parsed_config) => &parsed_config.file_names,
            None => &[],
        }
    }

    /// `(p *ParsedCommandLine) RootFileNameForDiagnostic`.
    pub fn root_file_name_for_diagnostic(&self, index: usize) -> &str {
        if index < self.root_file_names_for_diagnostics.len() {
            return &self.root_file_names_for_diagnostics[index];
        }
        self.file_names()[index].as_string()
    }

    /// `(p *ParsedCommandLine) FilePaths`.
    pub fn file_paths(&self) -> &Set<PathKey> {
        self.file_paths.get_or_init(|| {
            let mut set = Set::with_size_hint(self.file_names().len());
            for file_name in self.file_names() {
                let path = self.case_sensitivity.path_key(&file_name.as_path());
                set.add(path);
            }
            set
        })
    }

    /// `(p *ParsedCommandLine) ProjectReferences`.
    pub fn project_references(&self) -> &[ProjectReference] {
        match self.parsed_config.as_ref() {
            Some(parsed_config) => &parsed_config.project_references,
            None => &[],
        }
    }

    /// `(p *ParsedCommandLine) ContentMappers`.
    pub fn content_mappers(&self) -> &[Arc<Mapper>] {
        match self.parsed_config.as_ref() {
            Some(parsed_config) => &parsed_config.content_mappers,
            None => &[],
        }
    }

    /// `(p *ParsedCommandLine) ContentMapperExtensions` — the flattened list
    /// of file extensions registered by the config's content mappers.
    pub fn content_mapper_extensions(&self) -> &[String] {
        &self.content_mapper_extensions_cache
    }

    /// `(p *ParsedCommandLine) SetContentMappers` — sets the parsed config's
    /// content mappers and keeps the flattened extension cache in sync (Go
    /// mutates `ParsedConfig.ContentMappers` directly and computes the
    /// extension list on demand).
    pub fn set_content_mappers(&mut self, mappers: Vec<Arc<Mapper>>) {
        self.content_mapper_extensions_cache =
            Self::compute_content_mapper_extensions(mappers.as_slice());
        self.parsed_config
            .get_or_insert_with(Default::default)
            .content_mappers = mappers;
    }

    fn compute_content_mapper_extensions(mappers: &[Arc<Mapper>]) -> Vec<String> {
        core::flat_map(mappers, |m| m.extensions.clone().unwrap_or_default())
    }

    /// `(p *ParsedCommandLine) GetContentMapperForFileName` — the configured
    /// content mapper whose extensions include `file_name`, or `None` if no
    /// content mapper is registered for the file's extension.
    pub fn get_content_mapper_for_file_name(
        &self,
        file_name: &RootedFilePath,
    ) -> Option<&Arc<Mapper>> {
        let case_sensitivity = self.case_sensitivity();
        let extension = file_name.longest_extension(
            &self
                .content_mapper_extensions()
                .iter()
                .map(String::as_str)
                .collect::<Vec<_>>(),
            case_sensitivity,
        );
        self.content_mappers().iter().find(|mapper| {
            mapper.extensions.as_ref().is_some_and(|extensions| {
                extensions.iter().any(|mapper_extension| {
                    extension == mapper_extension
                        || (case_sensitivity.is_case_insensitive()
                            && extension.eq_ignore_ascii_case(mapper_extension))
                })
            })
        })
    }

    /// `(p *ParsedCommandLine) ResolvedProjectReferencePaths`.
    pub fn resolved_project_reference_paths(&self) -> &Vec<RootedFilePath> {
        self.resolved_project_reference_paths
            .get_or_init(|| core::map(self.project_references(), resolve_project_reference_path))
    }

    /// `(p *ParsedCommandLine) ExtendedSourceFiles`.
    pub fn extended_source_files(&self) -> Vec<RootedFilePath> {
        match self.config_file.as_ref() {
            Some(config_file) => config_file.extended_source_files(),
            None => Vec::new(),
        }
    }

    /// `(p *ParsedCommandLine) GetConfigFileParsingDiagnostics`.
    pub fn get_config_file_parsing_diagnostics(&self) -> Vec<DiagnosticRef> {
        let errors = self
            .errors
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .clone();
        if let Some(config_file) = self.config_file.as_ref() {
            // todo: !!! should be ConfigFile.ParseDiagnostics, check if they are the same
            return core::concatenate(config_file.diagnostics(), errors.as_slice()).into_owned();
        }
        errors
    }

    /// `(p *ParsedCommandLine) PossiblyMatchesFileName` — a fast check to see
    /// if a file is currently included by a config or would be included if the
    /// file were to be created. It may return false positives.
    pub fn possibly_matches_file_name(&self, file_name: &RootedFilePath) -> bool {
        let path = self.case_sensitivity.path_key(&file_name.as_path());
        if self.file_paths().has(&path) {
            return true;
        }

        if let Some(specs) = self.get_config_file_specs() {
            for include in &specs.validated_include_specs {
                let text = include.as_string();
                if !text.contains(['*', '?']) && !vfsmatch::is_implicit_glob(text) {
                    let include_path = self
                        .case_sensitivity
                        .path_key(&tspath::to_rooted_path(text, &self.base_directory));
                    if include_path == path {
                        return true;
                    }
                }
            }
        }
        if self.get_content_mapper_for_file_name(file_name).is_some() {
            let directory_path = path.parent();
            if self.possibly_matches_directory_name(&directory_path) {
                return true;
            }
        }
        if let Some(wildcard_directory_globs) = self.wildcard_directory_globs() {
            if !wildcard_directory_globs.is_empty() {
                for glob in wildcard_directory_globs {
                    if glob.matches(file_name.as_string()) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// `(p *ParsedCommandLine) PossiblyMatchesDirectoryName`.
    pub fn possibly_matches_directory_name(&self, directory_path: &PathKey) -> bool {
        if let Some(wildcard_directories) = self.wildcard_directories() {
            for (wildcard_dir, recursive) in wildcard_directories {
                let wildcard_dir_path = self.case_sensitivity.path_key(&wildcard_dir.as_path());
                if *recursive {
                    if wildcard_dir_path.contains_path(directory_path) {
                        return true;
                    }
                } else if wildcard_dir_path == *directory_path {
                    return true;
                }
            }
        }
        false
    }

    /// `(p *ParsedCommandLine) GetMatchedFileSpec`.
    pub fn get_matched_file_spec(&self, file_name: &RootedFilePath) -> String {
        self.get_config_file_specs()
            .map(|specs| {
                specs
                    .get_matched_file_spec(&self.case_sensitivity.path_key(&file_name.as_path()))
                    .as_string()
                    .to_string()
            })
            .unwrap_or_default()
    }

    /// `(p *ParsedCommandLine) GetMatchedIncludeSpec` — `(spec, is_default)`.
    pub fn get_matched_include_spec(&self, file_name: &RootedFilePath) -> (String, bool) {
        let Some(specs) = self.get_config_file_specs() else {
            return (String::new(), false);
        };
        if specs.validated_include_specs.is_empty() {
            return (String::new(), false);
        }

        if specs.is_default_include_spec {
            return (
                specs.validated_include_specs[0].as_string().to_string(),
                true,
            );
        }

        (
            specs
                .get_matched_include_spec(file_name, &self.base_directory, self.case_sensitivity)
                .as_string()
                .to_string(),
            false,
        )
    }

    /// `(p *ParsedCommandLine) ReloadFileNamesOfParsedCommandLine`.
    pub fn reload_file_names_of_parsed_command_line(&self, fs: &Arc<dyn Vfs>) -> ParsedCommandLine {
        let mut parsed_config = self.parsed_config.clone().unwrap_or_default();
        let specs = self.get_config_file_specs().unwrap_or_default_arc();
        let options = self.compiler_options_or_default();
        let (file_names, literal_file_names_len) = get_file_names_from_config_specs(
            &specs,
            &self.base_directory,
            &options,
            fs,
            self.content_mapper_extensions(),
        );
        parsed_config.file_names = file_names;
        ParsedCommandLine {
            parsed_config: Some(parsed_config),
            config_file: self.config_file.clone(),
            errors: Mutex::new(
                self.errors
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone(),
            ),
            raw: self.raw.clone(),
            compile_on_save: self.compile_on_save,
            config_file_specs: self.config_file_specs.clone(),
            base_directory: self.base_directory.clone(),
            case_sensitivity: self.case_sensitivity,
            wildcard_directories: clone_once_lock(&self.wildcard_directories),
            include_globs: clone_once_lock(&self.include_globs),
            literal_file_names_len,
            root_file_names_for_diagnostics: self.root_file_names_for_diagnostics.clone(),
            content_mapper_extensions_cache: self.content_mapper_extensions_cache.clone(),
            ..Default::default()
        }
    }

    /// `(p *ParsedCommandLine) Locale`.
    pub fn locale(&self) -> &Locale {
        self.locale
            .get_or_init(|| tsc_locale::parse(&self.compiler_options_or_default().locale).0)
    }
}

/// Helper mirroring Go's nilable `*configFileSpecs` dereference at the reload
/// call site (`getFileNamesFromConfigSpecs(*p.getConfigFileSpecs(), ...)`).
trait UnwrapOrDefaultArc<T> {
    fn unwrap_or_default_arc(self) -> T;
}

impl UnwrapOrDefaultArc<ConfigFileSpecs> for Option<Arc<ConfigFileSpecs>> {
    fn unwrap_or_default_arc(self) -> ConfigFileSpecs {
        match self {
            Some(specs) => (*specs).clone(),
            // PORT: Go would panic dereferencing nil; this path is only
            // reachable for command lines that never had a config file.
            None => ConfigFileSpecs::default(),
        }
    }
}

impl OutputPathsHost for ParsedCommandLine {
    fn common_source_directory(&self) -> RootedDirectoryPath {
        self.common_source_directory()
    }

    fn content_mapper_extensions(&self) -> &[String] {
        self.content_mapper_extensions()
    }

    fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity()
    }
}

// PORT: Go asserts `module.ResolvedProjectReference` conformance on
// `*ParsedCommandLine`. `ResolvedProjectReference: Send + Sync`, but the
// config file arena (`Vec<Node>`) contains `Cell`s and this workspace forbids
// `unsafe`, so `ParsedCommandLine` cannot be `Sync`. Downstream code that
// needs a `ResolvedProjectReference` should wrap or snapshot this type once a
// shareable representation exists.
