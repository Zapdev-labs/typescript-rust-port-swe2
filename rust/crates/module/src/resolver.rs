// Ported from tsc/internal/module/resolver.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::ops::Deref;
use std::sync::Arc;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_collections::{OrderedMap, Set};
use tsc_core::compileroptions::{
    RESOLUTION_MODE_COMMON_JS, RESOLUTION_MODE_ESM, RESOLUTION_MODE_NONE, ResolutionMode,
};
use tsc_core::core::if_else;
use tsc_core::options_generated::{CompilerOptions, ModuleKind, ModuleResolutionKind};
use tsc_core::pattern::try_parse_pattern;
use tsc_core::text::TextRange;
use tsc_core::tristate::TS_TRUE;
use tsc_diagnostics::Message;
use tsc_packagejson::{
    ExportsOrImports, InfoCacheEntry, JSONValueType, PackageDirectory, PackageJson,
    TypeValidatedField, VersionPaths,
};
use tsc_tspath::{
    self, CaseSensitivity, FileNameStem, PathKey, RelativePath, RootedDirectoryPath,
    RootedFilePath, RootedPath,
};
use tsc_vfs::Vfs;
use tsc_vfs::vfsmatch;

use crate::cache::{
    ModuleResolutionCache, ModuleResolutionCacheKey, ParsedPatternsCache, ResolutionData,
    ResolverOptions, TypeRefDirectiveResolutionCache, TypeRefDirectiveResolutionCacheKey,
    get_redirect_config_name, new_resolution_data,
};
use crate::types::{
    EXTENSIONS_DECLARATION, EXTENSIONS_IMPLEMENTATION_FILES, EXTENSIONS_JAVA_SCRIPT,
    EXTENSIONS_JSON, EXTENSIONS_TYPE_SCRIPT, Extensions, NodeResolutionFeatures, PackageId,
    ResolvedModule, ResolvedProjectReference, ResolvedTypeReferenceDirective,
};
use crate::util::{
    INFERRED_TYPES_CONTAINING_FILE, is_applicable_versioned_types_key, mangle_scoped_package_name,
    node_module_package_root_for_file, parse_package_name, try_get_js_extension_for_file,
};

/// `type resolved struct`
///
/// PORT: Go's nil `*resolved` ("keep searching") becomes `None`; the
/// `&resolved{}` sentinel ("stop, not resolved") is `Some(Resolved::default())`.
#[derive(Clone, Default)]
pub(crate) struct Resolved {
    pub(crate) path: RootedFilePath,
    pub(crate) extension: String,
    pub(crate) package_id: PackageId,
    pub(crate) original_path: RootedFilePath,
    pub(crate) resolved_using_ts_extension: bool,
    pub(crate) resolved_using_extra_extensions: bool,
}

impl Resolved {
    /// `func (r *resolved) isResolved() bool`
    pub(crate) fn is_resolved(&self) -> bool {
        !self.path.as_string().is_empty()
    }
}

/// `func unresolved() *resolved`
fn unresolved() -> Option<Resolved> {
    Some(Resolved::default())
}

/// `type resolutionCandidate struct` — a rooted, normalized lookup location.
/// Its `path` omits any trailing separator; `directory_only` preserves the
/// resolver behavior that skips file lookup for candidates written with
/// directory intent.
#[derive(Clone, Default)]
pub(crate) struct ResolutionCandidate {
    pub(crate) path: RootedPath,
    pub(crate) directory_path: RootedDirectoryPath,
    pub(crate) directory_only: bool,
}

/// `func resolutionCandidateFromNormalized(path string) resolutionCandidate`
///
/// PORT: called only by `resolve_resolution_candidate`, which is exercised by
/// `resolver_internal_test.go`.
#[allow(dead_code)]
pub(crate) fn resolution_candidate_from_normalized(path: &str) -> ResolutionCandidate {
    let mut path = path.to_string();
    let directory_only = tsc_tspath::has_trailing_directory_separator(&path);
    if directory_only && path.len() > tsc_tspath::get_root_length(&path) {
        path = tsc_tspath::remove_trailing_directory_separator(&path).to_string();
    }
    ResolutionCandidate {
        path: tsc_tspath::rooted_path_from_normalized(&path),
        directory_only,
        ..ResolutionCandidate::default()
    }
}

/// `func resolveResolutionCandidate(path string, paths ...string) resolutionCandidate`
///
/// PORT: test-facing helper (used by `resolver_internal_test.go`).
#[allow(dead_code)]
pub(crate) fn resolve_resolution_candidate(path: &str, paths: &[&str]) -> ResolutionCandidate {
    resolution_candidate_from_normalized(&tsc_tspath::resolve_path(path, paths))
}

/// `func resolutionCandidateFromDirectory(directory tspath.RootedDirectoryPath) resolutionCandidate`
///
/// PORT: defined for parity with Go; not called by the resolver itself.
#[allow(dead_code)]
fn resolution_candidate_from_directory(directory: &RootedDirectoryPath) -> ResolutionCandidate {
    ResolutionCandidate {
        path: directory.as_path(),
        ..ResolutionCandidate::default()
    }
}

fn resolution_candidate_from_file_name(file_name: &RootedFilePath) -> ResolutionCandidate {
    ResolutionCandidate {
        path: file_name.as_path(),
        ..ResolutionCandidate::default()
    }
}

pub(crate) fn resolution_candidate_from_directory_path(
    directory: &RootedDirectoryPath,
    path: &str,
) -> ResolutionCandidate {
    let file_path = path_for_dynamic_resolution(directory, path, false);
    let directory_path = path_for_dynamic_resolution(directory, path, true);
    resolution_candidate_from_encoded_paths(
        directory,
        &file_path,
        &directory_path,
        tsc_tspath::has_trailing_directory_separator(path),
    )
}

pub(crate) fn resolution_candidate_from_dynamic_logical_path(
    directory: &RootedDirectoryPath,
    path: &str,
) -> ResolutionCandidate {
    let empty = path.is_empty();
    let directory_only = path.is_empty() || tsc_tspath::has_trailing_directory_separator(path);
    let mut path = path.to_string();
    if !path.is_empty() && directory_only {
        path = tsc_tspath::remove_trailing_directory_separator(&path).to_string();
    }
    if empty {
        return ResolutionCandidate {
            path: directory.as_path(),
            directory_only: true,
            ..ResolutionCandidate::default()
        };
    }
    resolution_candidate_from_encoded_paths(
        directory,
        &tsc_tspath::encode_dynamic_relative_uri_path(&path),
        &tsc_tspath::encode_dynamic_relative_uri_directory_path(&path),
        directory_only,
    )
}

pub(crate) fn resolution_candidate_from_disk_logical_path(
    directory: &RootedDirectoryPath,
    path: &str,
    directory_only: bool,
) -> ResolutionCandidate {
    let mut path = path.to_string();
    if !path.is_empty() && directory_only {
        path = tsc_tspath::remove_trailing_directory_separator(&path).to_string();
    }
    if path.is_empty() {
        return ResolutionCandidate {
            path: directory.as_path(),
            directory_only,
            ..ResolutionCandidate::default()
        };
    }
    ResolutionCandidate {
        path: directory
            .resolve_file_from_normalized_relative(&path)
            .as_path(),
        directory_only,
        ..ResolutionCandidate::default()
    }
}

fn resolution_candidate_from_encoded_paths(
    directory: &RootedDirectoryPath,
    file_path: &str,
    directory_path: &str,
    directory_only: bool,
) -> ResolutionCandidate {
    let resolved_directory_path = directory.resolve_directory(directory_path);
    if directory_only {
        return ResolutionCandidate {
            path: resolved_directory_path.as_path(),
            directory_only: true,
            ..ResolutionCandidate::default()
        };
    }
    let mut candidate = ResolutionCandidate {
        path: directory.resolve_file(file_path).as_path(),
        ..ResolutionCandidate::default()
    };
    if resolved_directory_path.as_path() != candidate.path {
        candidate.directory_path = resolved_directory_path;
    }
    candidate
}

fn path_for_dynamic_resolution(
    directory: &RootedDirectoryPath,
    path: &str,
    directory_only: bool,
) -> String {
    if tsc_tspath::is_encoded_dynamic_file_name(directory.as_string())
        && !tsc_tspath::path_is_absolute(path)
    {
        if directory_only {
            return tsc_tspath::encode_dynamic_directory_specifier(path).into_owned();
        }
        return tsc_tspath::encode_dynamic_module_specifier(path).into_owned();
    }
    path.to_string()
}

pub(crate) fn resolution_candidate_from_relative_path(
    directory: &RootedDirectoryPath,
    path: &RelativePath,
) -> ResolutionCandidate {
    let mut path = path.clone();
    let directory_only = path.as_string().is_empty() || path.has_trailing_directory_separator();
    if !path.as_string().is_empty() && directory_only {
        path = path.without_trailing_directory_separator();
    }
    if path.as_string().is_empty() {
        return ResolutionCandidate {
            path: directory.as_path(),
            directory_only: true,
            ..ResolutionCandidate::default()
        };
    }
    ResolutionCandidate {
        path: directory.resolve_relative_file(&path).as_path(),
        directory_only,
        ..ResolutionCandidate::default()
    }
}

impl ResolutionCandidate {
    /// `func (c resolutionCandidate) AsString() string`
    pub(crate) fn as_string(&self) -> String {
        if self.directory_only {
            return tsc_tspath::ensure_trailing_directory_separator(self.path.as_string())
                .into_owned();
        }
        self.path.as_string().to_string()
    }

    /// `func (c resolutionCandidate) AsDirectoryPath() tspath.RootedDirectoryPath`
    pub(crate) fn as_directory_path(&self) -> RootedDirectoryPath {
        if !self.directory_path.as_string().is_empty() {
            return self.directory_path.clone();
        }
        tsc_tspath::rooted_directory_path_from_path(self.path.clone())
    }

    /// `func (c resolutionCandidate) Directory() tspath.RootedDirectoryPath`
    pub(crate) fn directory(&self) -> RootedDirectoryPath {
        self.path.directory()
    }

    /// `func (c resolutionCandidate) HasTrailingDirectorySeparator() bool`
    pub(crate) fn has_trailing_directory_separator(&self) -> bool {
        self.directory_only
    }

    /// `func (c resolutionCandidate) RemoveFileExtension() tspath.FileNameStem`
    pub(crate) fn remove_file_extension(&self) -> FileNameStem {
        tsc_tspath::rooted_file_path_from_path(self.path.clone()).remove_file_extension()
    }

    /// `func (c resolutionCandidate) RemoveExtension(extension string) tspath.FileNameStem`
    pub(crate) fn remove_extension(&self, extension: &str) -> FileNameStem {
        tsc_tspath::rooted_file_path_from_path(self.path.clone()).remove_extension(extension)
    }

    /// `func (c resolutionCandidate) Resolve(path string) resolutionCandidate`
    /// PORT: defined for parity with Go; not called by the resolver itself.
    #[allow(dead_code)]
    pub(crate) fn resolve(&self, path: &str) -> ResolutionCandidate {
        resolution_candidate_from_directory_path(
            &tsc_tspath::rooted_directory_path_from_path(self.path.clone()),
            path,
        )
    }

    /// `func (c resolutionCandidate) HasDirectoryPrefix(directory tspath.RootedDirectoryPath) bool`
    pub(crate) fn has_directory_prefix(&self, directory: &RootedDirectoryPath) -> bool {
        match self.path.relative_to(directory) {
            Some(relative) => !relative.as_string().is_empty() || self.directory_only,
            None => false,
        }
    }

    /// `func (c resolutionCandidate) RelativeToDirectory(directory tspath.RootedDirectoryPath) tspath.RelativePath`
    pub(crate) fn relative_to_directory(&self, directory: &RootedDirectoryPath) -> RelativePath {
        let Some(relative) = self.path.relative_to(directory) else {
            panic!("resolution candidate must be within prefix");
        };
        if self.directory_only {
            return relative.with_trailing_directory_separator();
        }
        relative
    }

    /// `func (c resolutionCandidate) SplitExtension(extraExtensions []string) (tspath.FileNameStem, string)`
    pub(crate) fn split_extension(&self, extra_extensions: &[String]) -> (FileNameStem, String) {
        let file_name = tsc_tspath::rooted_file_path_from_path(self.path.clone());
        let mut extension = file_name.extension().to_string();
        let mut extensionless = self.remove_file_extension();
        if extensionless.as_string() == self.path.as_string() {
            let extras: Vec<&str> = extra_extensions.iter().map(|e| e.as_str()).collect();
            extension = file_name
                .longest_extension(&extras, CaseSensitivity::CaseSensitive)
                .to_string();
            if extension.is_empty() {
                let path = self.path.as_string();
                // PORT: Go's `strings.LastIndex` returning -1 slices path[-1:]
                // and panics; `expect` preserves the panic.
                let idx = path
                    .rfind('.')
                    .expect("SplitExtension fallback requires a '.' in path");
                extension = path[idx..].to_string();
            }
            extensionless = self.remove_extension(&extension);
        }
        (extensionless, extension)
    }
}

/// `func (c resolutionCandidate) String() string`
impl fmt::Display for ResolutionCandidate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.as_string())
    }
}

/// `type resolutionKindSpecificLoader = func(extensions extensions, candidate resolutionCandidate) *resolved`
///
/// PORT: loaders receive the state as a leading `&mut` argument instead of
/// closing over it — Rust forbids capturing `&mut self` while the enclosing
/// method also uses `self`.
pub(crate) type ResolutionKindSpecificLoader<'a, 'obj> = dyn for<'b> FnMut(&'b mut ResolutionState<'a>, Extensions, &ResolutionCandidate) -> Option<Resolved>
    + 'obj;

/// `type tracer struct`
pub struct Tracer {
    traces: Vec<DiagAndArgs>,
}

/// `type DiagAndArgs struct`
///
/// PORT: `Args []any` becomes `Vec<String>` — every traced argument in this
/// package is string-formattable, matching `packagejson::TraceFunc`'s choice.
#[derive(Clone)]
pub struct DiagAndArgs {
    pub message: &'static Message,
    pub args: Vec<String>,
}

impl Tracer {
    /// `func (t *tracer) write(diag *diagnostics.Message, args ...any)`
    ///
    /// PORT: args arrive pre-stringified; Go's nil receiver (`t == nil`) is
    /// the caller's `Option<Tracer>`.
    pub(crate) fn write<T: fmt::Display>(&mut self, diag: &'static Message, args: &[T]) {
        self.traces.push(DiagAndArgs {
            message: diag,
            args: args.iter().map(|a| a.to_string()).collect(),
        });
    }

    /// `func (t *tracer) getTraces() []DiagAndArgs`
    pub(crate) fn get_traces(self) -> Vec<DiagAndArgs> {
        self.traces
    }
}

/// `type resolutionState struct`
pub(crate) struct ResolutionState<'a> {
    pub(crate) resolver: &'a DefaultResolver,
    pub(crate) tracer: Option<Tracer>,

    // request fields
    pub(crate) name: String,
    pub(crate) containing_directory: RootedDirectoryPath,
    pub(crate) containing_directory_has_trailing_separator: bool,
    pub(crate) is_config_lookup: bool,
    pub(crate) features: NodeResolutionFeatures,
    pub(crate) esm_mode: bool,
    pub(crate) conditions: Vec<String>,
    pub(crate) extensions: Extensions,
    pub(crate) compiler_options: Arc<CompilerOptions>,
    pub(crate) resolve_package_directory_only: bool,

    // state fields
    // candidate_ending_is_from_config is set when the candidate file extension originated from
    // configuration (package.json fields, tsconfig.json paths entries, or wildcard substitutions)
    // rather than from the module specifier written in source code. When true, resolved_using_ts_extension
    // is suppressed so the checker does not attempt to extract a TS extension from the original specifier.
    pub(crate) candidate_ending_is_from_config: bool,
    pub(crate) resolved_package_directory: bool,
    pub(crate) diagnostics: Vec<DiagnosticRef>,
}

impl<'a> ResolutionState<'a> {
    /// Minimal state for tests and `GetPackageScopeForPath` — the Go
    /// `&resolutionState{...}` struct literal.
    pub(crate) fn bare(
        resolver: &'a DefaultResolver,
        compiler_options: Arc<CompilerOptions>,
    ) -> Self {
        ResolutionState {
            resolver,
            tracer: None,
            name: String::new(),
            containing_directory: RootedDirectoryPath::default(),
            containing_directory_has_trailing_separator: false,
            is_config_lookup: false,
            features: NodeResolutionFeatures::NONE,
            esm_mode: false,
            conditions: Vec::new(),
            extensions: Extensions(0),
            compiler_options,
            resolve_package_directory_only: false,
            candidate_ending_is_from_config: false,
            resolved_package_directory: false,
            diagnostics: Vec::new(),
        }
    }

    /// `r.tracer.write(...)` guarded by `r.tracer != nil`.
    fn trace<T: fmt::Display>(&mut self, diag: &'static Message, args: &[T]) {
        if let Some(t) = &mut self.tracer {
            t.write(diag, args);
        }
    }
}

/// `func newResolutionState(...) *resolutionState`
fn new_resolution_state<'a>(
    name: &str,
    containing_directory: RootedDirectoryPath,
    is_type_reference_directive: bool,
    resolution_mode: ResolutionMode,
    compiler_options: &Arc<CompilerOptions>,
    redirected_reference: Option<&dyn ResolvedProjectReference>,
    resolver: &'a DefaultResolver,
    trace_builder: Option<Tracer>,
) -> ResolutionState<'a> {
    let mut state = ResolutionState {
        resolver,
        tracer: trace_builder,
        name: name.to_string(),
        containing_directory,
        containing_directory_has_trailing_separator: false,
        is_config_lookup: false,
        features: NodeResolutionFeatures::NONE,
        esm_mode: false,
        conditions: Vec::new(),
        extensions: Extensions(0),
        compiler_options: get_compiler_options_with_redirect(
            compiler_options,
            redirected_reference,
        ),
        resolve_package_directory_only: false,
        candidate_ending_is_from_config: false,
        resolved_package_directory: false,
        diagnostics: Vec::new(),
    };

    // PORT: Go reads `compilerOptions` (the pre-redirect parameter) for the
    // extension/feature selection below, not the redirected value.
    if is_type_reference_directive {
        state.extensions = EXTENSIONS_DECLARATION;
    } else if compiler_options.no_dts_resolution == TS_TRUE {
        state.extensions = EXTENSIONS_IMPLEMENTATION_FILES;
    } else {
        state.extensions = EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_JAVA_SCRIPT | EXTENSIONS_DECLARATION;
    }

    if !is_type_reference_directive && compiler_options.get_resolve_json_module() {
        state.extensions |= EXTENSIONS_JSON;
    }

    match compiler_options.get_module_resolution_kind() {
        ModuleResolutionKind::Node16 => {
            state.features = NodeResolutionFeatures::NODE16_DEFAULT;
            state.esm_mode = resolution_mode == ModuleKind::ESNext;
            state.conditions = get_conditions(compiler_options, resolution_mode);
        }
        ModuleResolutionKind::NodeNext => {
            state.features = NodeResolutionFeatures::NODE_NEXT_DEFAULT;
            state.esm_mode = resolution_mode == ModuleKind::ESNext;
            state.conditions = get_conditions(compiler_options, resolution_mode);
        }
        ModuleResolutionKind::Bundler => {
            state.features = get_node_resolution_features(compiler_options);
            state.conditions = get_conditions(compiler_options, resolution_mode);
        }
        _ => {}
    }
    state
}

impl ResolutionState<'_> {
    /// `func (r *resolutionState) containingDirectoryPath() string`
    fn containing_directory_path(&self) -> String {
        if self.containing_directory_has_trailing_separator {
            return tsc_tspath::ensure_trailing_directory_separator(
                self.containing_directory.as_string(),
            )
            .into_owned();
        }
        self.containing_directory.as_string().to_string()
    }
}

/// `func GetCompilerOptionsWithRedirect(compilerOptions *core.CompilerOptions, redirectedReference ResolvedProjectReference) *core.CompilerOptions`
pub fn get_compiler_options_with_redirect(
    compiler_options: &Arc<CompilerOptions>,
    redirected_reference: Option<&dyn ResolvedProjectReference>,
) -> Arc<CompilerOptions> {
    let Some(redirected_reference) = redirected_reference else {
        return compiler_options.clone();
    };
    if let Some(options_from_redirect) = redirected_reference.compiler_options() {
        // PORT: Go shares the `*CompilerOptions` pointer; cloning keeps the
        // value semantics — the redirect options are read-only here.
        return Arc::new(options_from_redirect.clone());
    }
    compiler_options.clone()
}

/// `type DefaultResolver struct`
///
/// PORT: the embedded `*ResolutionData` becomes a `data` field exposed through
/// `Deref`, so `r.compilerOptions` maps to `self.compiler_options`.
pub struct DefaultResolver {
    pub(crate) data: ResolutionData,
    pub(crate) fs: Arc<dyn Vfs>,
    pub(crate) base_directory: RootedDirectoryPath,

    pub(crate) module_resolution_cache: ModuleResolutionCache,
    pub(crate) type_ref_directive_resolution_cache: TypeRefDirectiveResolutionCache,

    // Cached representations for `core.CompilerOptions.paths`, keyed by the
    // path mappings themselves. This does not handle other path patterns such
    // as `typesVersions`.
    pub(crate) parsed_patterns_for_paths: ParsedPatternsCache,
}

impl Deref for DefaultResolver {
    type Target = ResolutionData;
    fn deref(&self) -> &ResolutionData {
        &self.data
    }
}

impl DefaultResolver {
    /// `func (r *DefaultResolver) BaseDirectory() tspath.RootedDirectoryPath`
    pub fn base_directory(&self) -> RootedDirectoryPath {
        self.base_directory.clone()
    }

    /// `func (r *DefaultResolver) GetResolutionData() *ResolutionData`
    pub fn get_resolution_data(&self) -> &ResolutionData {
        &self.data
    }

    /// `func NewResolver(opts ResolverOptions) *DefaultResolver`
    pub fn new(opts: ResolverOptions) -> DefaultResolver {
        new_resolution_data(&opts).new_resolver(opts.host)
    }

    /// `func NewResolverWithOptions(...) *DefaultResolver`
    pub fn new_with_options(
        host: Arc<dyn crate::types::ResolutionHost>,
        compiler_options: Arc<CompilerOptions>,
        typings_location: RootedDirectoryPath,
        project_name: &str,
        mut opts: ResolverOptions,
    ) -> DefaultResolver {
        opts.host = host;
        opts.compiler_options = compiler_options;
        opts.typings_location = typings_location;
        opts.project_name = project_name.to_string();
        DefaultResolver::new(opts)
    }

    /// `func (r *DefaultResolver) newTraceBuilder() *tracer`
    fn new_trace_builder(&self) -> Option<Tracer> {
        if self.compiler_options.trace_resolution == TS_TRUE {
            return Some(Tracer { traces: Vec::new() });
        }
        None
    }

    /// `func (r *DefaultResolver) GetPackageScopeForPath(directory tspath.RootedDirectoryPath) *packagejson.InfoCacheEntry`
    pub fn get_package_scope_for_path(
        &self,
        directory: &RootedDirectoryPath,
    ) -> Option<Arc<InfoCacheEntry>> {
        ResolutionState::bare(self, self.compiler_options.clone())
            .get_package_scope_for_path(directory)
    }

    /// `func (r *DefaultResolver) PackageJsonCacheEntries(f func(key tspath.PathKey, value *packagejson.InfoCacheEntry) bool)`
    pub fn package_json_cache_entries(&self, f: impl FnMut(PathKey, Arc<InfoCacheEntry>) -> bool) {
        self.data.package_json_cache_entries(f);
    }

    /// `func (r *DefaultResolver) ResolveTypeReferenceDirective(...) (*ResolvedTypeReferenceDirective, []DiagAndArgs)`
    pub fn resolve_type_reference_directive(
        &self,
        type_reference_directive_name: &str,
        containing_file: &RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (ResolvedTypeReferenceDirective, Vec<DiagAndArgs>) {
        let containing_directory = containing_file.directory();
        let mut trace_builder = self.new_trace_builder();

        let from_inferred_types_containing_file =
            containing_file.base_name() == INFERRED_TYPES_CONTAINING_FILE;

        let cache_key = TypeRefDirectiveResolutionCacheKey {
            containing_directory: containing_directory.clone(),
            type_reference_name: type_reference_directive_name.to_string(),
            resolution_mode,
            redirect_config_name: get_redirect_config_name(redirected_reference),
            from_inferred_types_containing_file,
        };

        if trace_builder.is_none() {
            if let Some(cached) = self.type_ref_directive_resolution_cache.get(&cache_key) {
                return ((*cached).clone(), Vec::new());
            }
        }

        let compiler_options =
            get_compiler_options_with_redirect(&self.compiler_options, redirected_reference);

        let (type_roots, from_config) =
            compiler_options.get_effective_type_roots(&self.base_directory);
        let type_roots = type_roots.unwrap_or_default();
        if let Some(t) = &mut trace_builder {
            let roots = type_roots
                .iter()
                .map(|root| root.as_string())
                .collect::<Vec<_>>()
                .join(",");
            t.write(
                &tsc_diagnostics::Resolving_type_reference_directive_0_containing_file_1_root_directory_2,
                &[type_reference_directive_name, containing_file.as_string(), roots.as_str()],
            );
            trace_resolution_using_project_reference(t, redirected_reference);
        }

        let mut state = new_resolution_state(
            type_reference_directive_name,
            containing_directory,
            true, /*isTypeReferenceDirective*/
            resolution_mode,
            &compiler_options,
            redirected_reference,
            self,
            trace_builder,
        );
        let result = state.resolve_type_reference_directive(
            &type_roots,
            from_config,
            from_inferred_types_containing_file,
        );

        if let Some(t) = &mut state.tracer {
            trace_type_reference_directive_result(t, type_reference_directive_name, &result);
        }

        let result = Arc::new(result);
        self.type_ref_directive_resolution_cache
            .set(cache_key, result.clone());

        let traces = state.tracer.map_or(Vec::new(), |t| t.get_traces());
        ((*result).clone(), traces)
    }

    /// `func (r *DefaultResolver) ResolveModuleName(...) (*ResolvedModule, []DiagAndArgs, error)`
    pub fn resolve_module_name(
        &self,
        module_name: &str,
        containing_file: &RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>) {
        let containing_directory = containing_file.directory();
        self.resolve_module_name_impl(
            module_name,
            &containing_file.as_path(),
            &containing_directory,
            resolution_mode,
            redirected_reference,
        )
    }

    /// `func (r *DefaultResolver) ResolveModuleNameFromDirectory(...) (*ResolvedModule, []DiagAndArgs, error)`
    pub fn resolve_module_name_from_directory(
        &self,
        module_name: &str,
        containing_directory: &RootedDirectoryPath,
        resolution_mode: ResolutionMode,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>) {
        self.resolve_module_name_impl(
            module_name,
            &containing_directory.as_path(),
            containing_directory,
            resolution_mode,
            None,
        )
    }

    /// `func (r *DefaultResolver) resolveModuleName(...) (*ResolvedModule, []DiagAndArgs)`
    fn resolve_module_name_impl(
        &self,
        module_name: &str,
        containing_file: &RootedPath,
        containing_directory: &RootedDirectoryPath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>) {
        let mut trace_builder = self.new_trace_builder();

        let cache_key = ModuleResolutionCacheKey {
            containing_directory: containing_directory.clone(),
            module_name: module_name.to_string(),
            resolution_mode,
            redirect_config_name: get_redirect_config_name(redirected_reference),
        };

        if trace_builder.is_none() {
            if let Some(cached) = self.module_resolution_cache.get(&cache_key) {
                return (Some((*cached).clone()), Vec::new());
            }
        }

        let compiler_options =
            get_compiler_options_with_redirect(&self.compiler_options, redirected_reference);
        if let Some(t) = &mut trace_builder {
            t.write(
                &tsc_diagnostics::Resolving_module_0_from_1,
                &[module_name, containing_file.as_string()],
            );
            trace_resolution_using_project_reference(t, redirected_reference);
        }

        let module_resolution = compiler_options.get_module_resolution_kind();
        if compiler_options.module_resolution != module_resolution {
            if let Some(t) = &mut trace_builder {
                t.write(
                    &tsc_diagnostics::Module_resolution_kind_is_not_specified_using_0,
                    &[module_resolution.to_string()],
                );
            }
        } else if let Some(t) = &mut trace_builder {
            t.write(
                &tsc_diagnostics::Explicitly_specified_module_resolution_kind_Colon_0,
                &[module_resolution.to_string()],
            );
        }

        let result = match module_resolution {
            ModuleResolutionKind::Node16
            | ModuleResolutionKind::NodeNext
            | ModuleResolutionKind::Bundler => {
                let mut state = new_resolution_state(
                    module_name,
                    containing_directory.clone(),
                    false, /*isTypeReferenceDirective*/
                    resolution_mode,
                    &compiler_options,
                    redirected_reference,
                    self,
                    trace_builder,
                );
                let result = state.resolve_node_like();
                trace_builder = state.tracer.take();
                result
            }
            _ => panic!("Unexpected moduleResolution: {}", module_resolution as i32),
        };

        if let Some(t) = &mut trace_builder {
            if result.is_resolved() {
                if !result.package_id.name.is_empty() {
                    t.write(
                        &tsc_diagnostics::Module_name_0_was_successfully_resolved_to_1_with_Package_ID_2,
                        &[
                            module_name.to_string(),
                            result.resolved_file_name.to_string(),
                            result.package_id.to_string(),
                        ],
                    );
                } else {
                    t.write(
                        &tsc_diagnostics::Module_name_0_was_successfully_resolved_to_1,
                        &[
                            module_name.to_string(),
                            result.resolved_file_name.to_string(),
                        ],
                    );
                }
            } else {
                t.write(
                    &tsc_diagnostics::Module_name_0_was_not_resolved,
                    &[module_name.to_string()],
                );
            }
        }

        let (final_result, trace_builder) = self.try_resolve_from_typings_location(
            module_name,
            containing_directory,
            result,
            trace_builder,
        );
        let final_result = Arc::new(final_result);
        self.module_resolution_cache
            .set(cache_key, final_result.clone());

        (
            Some((*final_result).clone()),
            trace_builder.map_or(Vec::new(), |t| t.get_traces()),
        )
    }
}

impl ResolutionData {
    /// `func (d *ResolutionData) NewResolver(host ResolutionHost) *DefaultResolver`
    ///
    /// PORT: `&self` clones the Arc'd fields, so the new resolver shares the
    /// package.json info cache exactly like Go's embedded `*ResolutionData`.
    pub fn new_resolver(&self, host: Arc<dyn crate::types::ResolutionHost>) -> DefaultResolver {
        let fs = host.fs().clone();
        let base_directory = host.get_current_directory();
        if base_directory.as_string().is_empty() {
            panic!("resolver must have a rooted base directory");
        }
        if self.package_json_info_cache.case_sensitivity() != fs.case_sensitivity() {
            panic!("package JSON cache and resolver must use the same case sensitivity");
        }
        DefaultResolver {
            data: ResolutionData {
                compiler_options: self.compiler_options.clone(),
                typings_location: self.typings_location.clone(),
                project_name: self.project_name.clone(),
                extra_extensions: self.extra_extensions.clone(),
                package_json_info_cache: self.package_json_info_cache.clone(),
            },
            fs,
            base_directory,
            module_resolution_cache: ModuleResolutionCache::default(),
            type_ref_directive_resolution_cache: TypeRefDirectiveResolutionCache::default(),
            parsed_patterns_for_paths: ParsedPatternsCache::default(),
        }
    }
}

/// `func (r *tracer) traceResolutionUsingProjectReference(redirectedReference ResolvedProjectReference)`
fn trace_resolution_using_project_reference(
    tracer: &mut Tracer,
    redirected_reference: Option<&dyn ResolvedProjectReference>,
) {
    if let Some(redirect) = redirected_reference {
        if redirect.compiler_options().is_some() {
            tracer.write(
                &tsc_diagnostics::Using_compiler_options_of_project_reference_redirect_0,
                &[redirect.config_name().as_string()],
            );
        }
    }
}

impl DefaultResolver {
    /// `func (r *DefaultResolver) tryResolveFromTypingsLocation(...) *ResolvedModule`
    ///
    /// PORT: returns the trace builder alongside the result so the caller can
    /// finish draining traces without a second self-borrow.
    fn try_resolve_from_typings_location(
        &self,
        module_name: &str,
        containing_directory: &RootedDirectoryPath,
        original_result: ResolvedModule,
        mut trace_builder: Option<Tracer>,
    ) -> (ResolvedModule, Option<Tracer>) {
        if self.typings_location.as_string().is_empty()
            || tsc_tspath::is_external_module_name_relative(module_name)
            || (original_result.is_resolved()
                && tsc_tspath::extension_is_one_of(
                    &original_result.extension,
                    &tsc_tspath::SUPPORTED_TS_EXTENSIONS_WITH_JSON_FLAT[..],
                ))
        {
            return (original_result, trace_builder);
        }

        let mut state = new_resolution_state(
            module_name,
            containing_directory.clone(),
            false,            /*isTypeReferenceDirective*/
            ModuleKind::None, // resolutionMode,
            &self.compiler_options,
            None, // redirectedReference,
            self,
            trace_builder.take(),
        );
        if let Some(t) = &mut state.tracer {
            t.write(
                &tsc_diagnostics::Auto_discovery_for_typings_is_enabled_in_project_0_Running_extra_resolution_pass_for_module_1_using_cache_location_2,
                &[
                    self.project_name.as_str(),
                    module_name,
                    self.typings_location.as_string(),
                ],
            );
        }
        let global_resolved = state.load_module_from_immediate_node_modules_directory(
            EXTENSIONS_DECLARATION,
            &self.typings_location.clone(),
            false,
        );
        let trace_builder = state.tracer.take();
        let Some(global_resolved) = global_resolved else {
            return (original_result, trace_builder);
        };
        let mut result = state.create_resolved_module(Some(global_resolved), true);
        let mut diags = original_result.resolution_diagnostics.clone();
        diags.extend(result.resolution_diagnostics.iter().cloned());
        result.resolution_diagnostics = diags;
        (result, trace_builder)
    }

    /// `func (r *DefaultResolver) resolveConfig(moduleName string, containingFile tspath.RootedFilePath) *ResolvedModule`
    fn resolve_config(
        &self,
        module_name: &str,
        containing_file: &RootedFilePath,
    ) -> ResolvedModule {
        let containing_directory = containing_file.directory();
        let mut state = new_resolution_state(
            module_name,
            containing_directory,
            false, /*isTypeReferenceDirective*/
            RESOLUTION_MODE_COMMON_JS,
            &self.compiler_options,
            None,
            self,
            None,
        );
        state.is_config_lookup = true;
        state.extensions = EXTENSIONS_JSON;
        state.resolve_node_like()
    }

    /// `func (r *DefaultResolver) ResolvePackageDirectory(...) *ResolvedModule`
    pub fn resolve_package_directory(
        &self,
        module_name: &str,
        containing_file: &RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> Option<ResolvedModule> {
        let compiler_options =
            get_compiler_options_with_redirect(&self.compiler_options, redirected_reference);
        let containing_directory = containing_file.directory();
        let mut state = new_resolution_state(
            module_name,
            containing_directory,
            false, /*isTypeReferenceDirective*/
            resolution_mode,
            &compiler_options,
            redirected_reference,
            self,
            None,
        );
        state.resolve_package_directory_only = true;
        if let Some(result) =
            state.load_module_from_nearest_node_modules_directory(false /*typesScopeOnly*/)
        {
            if !result.path.as_string().is_empty() {
                return Some(state.create_resolved_module_handling_symlink(Some(result)));
            }
        }
        None
    }
}

/// `func (r *tracer) traceTypeReferenceDirectiveResult(typeReferenceDirectiveName string, result *ResolvedTypeReferenceDirective)`
fn trace_type_reference_directive_result(
    tracer: &mut Tracer,
    type_reference_directive_name: &str,
    result: &ResolvedTypeReferenceDirective,
) {
    if !result.is_resolved() {
        tracer.write(
            &tsc_diagnostics::Type_reference_directive_0_was_not_resolved,
            &[type_reference_directive_name],
        );
    } else if !result.package_id.name.is_empty() {
        tracer.write(
            &tsc_diagnostics::Type_reference_directive_0_was_successfully_resolved_to_1_with_Package_ID_2_primary_Colon_3,
            &[
                type_reference_directive_name.to_string(),
                result.resolved_file_name.to_string(),
                result.package_id.to_string(),
                result.primary.to_string(),
            ],
        );
    } else {
        tracer.write(
            &tsc_diagnostics::Type_reference_directive_0_was_successfully_resolved_to_1_primary_Colon_2,
            &[
                type_reference_directive_name.to_string(),
                result.resolved_file_name.to_string(),
                result.primary.to_string(),
            ],
        );
    }
}

impl<'a> ResolutionState<'a> {
    /// `func (r *resolutionState) resolveTypeReferenceDirective(...) *ResolvedTypeReferenceDirective`
    fn resolve_type_reference_directive(
        &mut self,
        type_roots: &[RootedDirectoryPath],
        from_config: bool,
        from_inferred_types_containing_file: bool,
    ) -> ResolvedTypeReferenceDirective {
        // Primary lookup
        if !type_roots.is_empty() {
            let roots = type_roots
                .iter()
                .map(|root| root.as_string())
                .collect::<Vec<_>>()
                .join(", ");
            self.trace(
                &tsc_diagnostics::Resolving_with_primary_search_path_0,
                &[roots],
            );
            for type_root in type_roots {
                let candidate = self.get_candidate_from_type_root(type_root);
                let directory_exists = self.resolver.fs.directory_exists(type_root);
                if !directory_exists {
                    self.trace(
                        &tsc_diagnostics::Directory_0_does_not_exist_skipping_all_lookups_in_it,
                        &[type_root.as_string()],
                    );
                    continue;
                }
                if from_config {
                    // Custom typeRoots resolve as file or directory just like we do modules
                    if !candidate.has_trailing_directory_separator() {
                        if let Some(mut resolved_from_file) =
                            self.load_module_from_file(EXTENSIONS_DECLARATION, &candidate)
                        {
                            let package_directory =
                                node_module_package_root_for_file(&resolved_from_file.path);
                            if !package_directory.as_string().is_empty() {
                                let pd = self
                                    .resolver
                                    .package_json_info_cache
                                    .package_directory(package_directory);
                                let package_info = self.get_package_json_info(&pd);
                                resolved_from_file.package_id =
                                    self.get_package_id(&resolved_from_file.path, &package_info);
                            }
                            return self.create_resolved_type_reference_directive(
                                Some(resolved_from_file),
                                true, /*primary*/
                            );
                        }
                    }
                }
                if let Some(resolved_from_directory) = self.load_node_module_from_directory(
                    EXTENSIONS_DECLARATION,
                    &candidate,
                    true, /*considerPackageJson*/
                ) {
                    return self.create_resolved_type_reference_directive(
                        Some(resolved_from_directory),
                        true, /*primary*/
                    );
                }
            }
        } else {
            self.trace(
                &tsc_diagnostics::Root_directory_cannot_be_determined_skipping_primary_search_paths,
                &[""; 0],
            );
        }

        // Secondary lookup
        let mut resolved = None;
        if !from_config || !from_inferred_types_containing_file {
            let dir = self.containing_directory_path();
            self.trace(
                &tsc_diagnostics::Looking_up_in_node_modules_folder_initial_location_0,
                &[dir],
            );
            if !tsc_tspath::is_external_module_name_relative(&self.name) {
                resolved = self
                    .load_module_from_nearest_node_modules_directory(false /*typesScopeOnly*/);
            } else {
                let candidate = normalize_path_for_cjs_resolution(
                    &self.containing_directory.clone(),
                    &self.name.clone(),
                );
                resolved = self.node_load_module_by_relative_name(
                    EXTENSIONS_DECLARATION,
                    &candidate,
                    true, /*considerPackageJson*/
                );
            }
        } else {
            self.trace(
                &tsc_diagnostics::Resolving_type_reference_directive_for_program_that_specifies_custom_typeRoots_skipping_lookup_in_node_modules_folder,
                &[""; 0],
            );
        }
        self.create_resolved_type_reference_directive(resolved, false /*primary*/)
    }

    /// `func (r *resolutionState) getCandidateFromTypeRoot(typeRoot tspath.RootedDirectoryPath) resolutionCandidate`
    fn get_candidate_from_type_root(
        &mut self,
        type_root: &RootedDirectoryPath,
    ) -> ResolutionCandidate {
        let mut name_for_lookup = self.name.clone();
        if type_root.base_name() == "@types"
            && type_root.as_path().directory().base_name() == "node_modules"
        {
            name_for_lookup = self.mangle_scoped_package_name(&self.name.clone());
        }
        resolution_candidate_from_directory_path(type_root, &name_for_lookup)
    }

    /// `func (r *resolutionState) mangleScopedPackageName(name string) string`
    fn mangle_scoped_package_name(&mut self, name: &str) -> String {
        let mangled = mangle_scoped_package_name(name);
        if mangled != name {
            self.trace(
                &tsc_diagnostics::Scoped_package_detected_looking_in_0,
                &[mangled.clone()],
            );
        }
        mangled
    }

    // resolveFromTypeRoot tries to resolve a module name from the configured typeRoots.
    // This is used as a fallback after node_modules resolution fails, for declaration file lookups.
    // Returns nil if typeRoots is not configured or if no matching module is found in any typeRoot directory.
    /// `func (r *resolutionState) resolveFromTypeRoot() *resolved`
    fn resolve_from_type_root(&mut self) -> Option<Resolved> {
        let Some(type_roots) = self.compiler_options.type_roots.clone() else {
            return None;
        };
        for type_root in &type_roots {
            let candidate = self.get_candidate_from_type_root(type_root);
            let directory_exists = self.resolver.fs.directory_exists(type_root);
            if !directory_exists {
                self.trace(
                    &tsc_diagnostics::Directory_0_does_not_exist_skipping_all_lookups_in_it,
                    &[type_root.as_string()],
                );
                continue;
            }
            if !candidate.has_trailing_directory_separator() {
                if let Some(mut resolved_from_file) =
                    self.load_module_from_file(EXTENSIONS_DECLARATION, &candidate)
                {
                    let package_directory =
                        node_module_package_root_for_file(&resolved_from_file.path);
                    if !package_directory.as_string().is_empty() {
                        let pd = self
                            .resolver
                            .package_json_info_cache
                            .package_directory(package_directory);
                        let package_info = self.get_package_json_info(&pd);
                        resolved_from_file.package_id =
                            self.get_package_id(&resolved_from_file.path, &package_info);
                    }
                    return Some(resolved_from_file);
                }
            }
            if let Some(resolved) = self.load_node_module_from_directory(
                EXTENSIONS_DECLARATION,
                &candidate,
                true, /*considerPackageJson*/
            ) {
                return Some(resolved);
            }
        }
        None
    }

    /// `func (r *resolutionState) getPackageScopeForPath(directory tspath.RootedDirectoryPath) *packagejson.InfoCacheEntry`
    fn get_package_scope_for_path(
        &mut self,
        directory: &RootedDirectoryPath,
    ) -> Option<Arc<InfoCacheEntry>> {
        let package_directory = self
            .resolver
            .package_json_info_cache
            .package_directory(directory.clone());
        let typings_location = self.resolver.typings_location.clone();
        tsc_packagejson::for_each_ancestor_directory_stopping_at_global_cache(
            &typings_location,
            package_directory,
            |directory| {
                let result = self.get_package_json_info(directory);
                let stop = result.is_some();
                (result, stop)
            },
        )
    }

    /// `func (r *resolutionState) resolveNodeLike() *ResolvedModule`
    fn resolve_node_like(&mut self) -> ResolvedModule {
        if self.tracer.is_some() {
            let conditions = self
                .conditions
                .iter()
                .map(|c| format!("'{c}'"))
                .collect::<Vec<_>>()
                .join(", ");
            self.trace(
                &tsc_diagnostics::Resolving_in_0_mode_with_conditions_1,
                &[if_else(self.esm_mode, "ESM", "CJS").to_string(), conditions],
            );
        }
        let mut result = self.resolve_node_like_worker();
        if self.resolved_package_directory
            && !self.is_config_lookup
            && self.features.contains(NodeResolutionFeatures::EXPORTS)
            && self
                .extensions
                .contains(EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION)
            && !tsc_tspath::is_external_module_name_relative(&self.name)
            && result.is_resolved()
            && result.is_external_library_import
            && !extension_is_ok(
                EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION,
                &result.extension,
            )
            && self.conditions.iter().any(|c| c == "import")
        {
            self.trace(
                &tsc_diagnostics::Resolution_of_non_relative_name_failed_trying_with_modern_Node_resolution_features_disabled_to_see_if_npm_library_needs_configuration_update,
                &[""; 0],
            );
            self.features =
                NodeResolutionFeatures(self.features.0 & !NodeResolutionFeatures::EXPORTS.0);
            self.extensions = self.extensions & (EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION);
            let diagnostics_count = self.diagnostics.len();
            let diagnostic_result = self.resolve_node_like_worker();
            if diagnostic_result.is_resolved() && diagnostic_result.is_external_library_import {
                result.alternate_result = diagnostic_result.resolved_file_name;
            }
            self.diagnostics.truncate(diagnostics_count);
        }
        result
    }

    /// `func (r *resolutionState) resolveNodeLikeWorker() *ResolvedModule`
    fn resolve_node_like_worker(&mut self) -> ResolvedModule {
        if let Some(resolved) = self.try_load_module_using_optional_resolution_settings() {
            return self.create_resolved_module_handling_symlink(Some(resolved));
        }

        if !tsc_tspath::is_external_module_name_relative(&self.name) {
            if self.features.contains(NodeResolutionFeatures::IMPORTS) && self.name.starts_with('#')
            {
                if let Some(resolved) = self.load_module_from_imports() {
                    return self.create_resolved_module_handling_symlink(Some(resolved));
                }
            }
            if self.features.contains(NodeResolutionFeatures::SELF_NAME) {
                if let Some(resolved) = self.load_module_from_self_name_reference() {
                    return self.create_resolved_module_handling_symlink(Some(resolved));
                }
            }
            if self.name.contains(':') {
                let name = self.name.clone();
                let extensions_str = self.extensions.to_string();
                self.trace(
                    &tsc_diagnostics::Skipping_module_0_that_looks_like_an_absolute_URI_target_file_types_Colon_1,
                    &[name, extensions_str],
                );
                return self.create_resolved_module(None, false);
            }
            let name = self.name.clone();
            let extensions_str = self.extensions.to_string();
            self.trace(
                &tsc_diagnostics::Loading_module_0_from_node_modules_folder_target_file_types_Colon_1,
                &[name, extensions_str],
            );
            if let Some(resolved) =
                self.load_module_from_nearest_node_modules_directory(false /*typesScopeOnly*/)
            {
                return self.create_resolved_module_handling_symlink(Some(resolved));
            }
            if self.extensions.contains(EXTENSIONS_DECLARATION) {
                if let Some(resolved) = self.resolve_from_type_root() {
                    return self.create_resolved_module_handling_symlink(Some(resolved));
                }
            }
        } else {
            let candidate = normalize_path_for_cjs_resolution(
                &self.containing_directory.clone(),
                &self.name.clone(),
            );
            let resolved =
                self.node_load_module_by_relative_name(self.extensions, &candidate, true);
            let is_external_library_import = resolved.as_ref().is_some_and(|r| {
                r.path
                    .contains_lowercase_directory_sequence("/node_modules/")
            });
            return self.create_resolved_module(resolved, is_external_library_import);
        }
        self.create_resolved_module(None, false)
    }

    /// `func (r *resolutionState) loadModuleFromSelfNameReference() *resolved`
    fn load_module_from_self_name_reference(&mut self) -> Option<Resolved> {
        let scope = self.get_package_scope_for_path(&self.containing_directory.clone());
        if !package_json_exists(&scope)
            || scope
                .as_deref()
                .and_then(|s| s.contents.as_deref())
                .is_none_or(|c| c.exports.is_falsy())
        {
            // !!! falsy check seems wrong?
            return None;
        }
        let scope = scope.unwrap();
        let contents = scope.contents.as_deref().unwrap();
        let Some(name) = contents.name.get_value() else {
            return None;
        };
        let name = name.clone();
        let parts = tsc_tspath::get_path_components(&self.name);
        let name_parts = tsc_tspath::get_path_components(&name);
        if parts.len() < name_parts.len() || name_parts.as_slice() != &parts[..name_parts.len()] {
            return None;
        }
        let trailing_parts = &parts[name_parts.len()..];
        let subpath;
        if !trailing_parts.is_empty() {
            let trailing: Vec<&str> = trailing_parts.iter().map(|s| s.as_str()).collect();
            subpath = tsc_tspath::combine_paths(".", &trailing);
        } else {
            subpath = ".".to_string();
        }
        // Maybe TODO: splitting extensions into two priorities should be unnecessary, except
        // https://github.com/microsoft/TypeScript/issues/50762 makes the behavior different.
        // As long as that bug exists, we need to do two passes here in self-name loading
        // in order to be consistent with (non-self) library-name loading in
        // `loadModuleFromNearestNodeModulesDirectoryWorker`, which uses two passes in order
        // to prioritize `@types` packages higher up the directory tree over untyped
        // implementation packages. See the selfNameModuleAugmentation.ts test for why this
        // matters.
        //
        // However, there's an exception. If the user has `allowJs` and `declaration`, we need
        // to ensure that self-name imports of their own package can resolve back to their
        // input JS files via `tryLoadInputFileForPath` at a higher priority than their output
        // declaration files, so we need to do a single pass with all extensions for that case.
        if self.compiler_options.get_allow_js()
            && !self
                .containing_directory
                .contains_lowercase_directory_sequence("/node_modules/")
        {
            return self.load_module_from_exports(&scope, self.extensions, &subpath);
        }
        let priority_extensions =
            self.extensions & (EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION);
        let secondary_extensions =
            Extensions(self.extensions.0 & !(EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION).0);
        if let Some(resolved) = self.load_module_from_exports(&scope, priority_extensions, &subpath)
        {
            return Some(resolved);
        }
        self.load_module_from_exports(&scope, secondary_extensions, &subpath)
    }

    /// `func (r *resolutionState) loadModuleFromImports() *resolved`
    fn load_module_from_imports(&mut self) -> Option<Resolved> {
        if self.name == "#"
            || (self.name.starts_with("#/")
                && !self
                    .features
                    .contains(NodeResolutionFeatures::IMPORTS_PATTERN_ROOT))
        {
            let name = self.name.clone();
            self.trace(
                &tsc_diagnostics::Invalid_import_specifier_0_has_no_possible_resolutions,
                &[name],
            );
            return None;
        }
        let directory_path = self.containing_directory.clone();
        let scope = self.get_package_scope_for_path(&directory_path);
        if !package_json_exists(&scope) {
            self.trace(
                &tsc_diagnostics::Directory_0_has_no_containing_package_json_scope_Imports_will_not_resolve,
                &[directory_path.as_string()],
            );
            return None;
        }
        let scope = scope.unwrap();
        let contents = scope.contents.as_deref().unwrap();
        if contents.imports.type_ != JSONValueType::Object {
            // !!! Old compiler only checks for undefined, but then assumes `imports` is an object if present.
            // Maybe should have a new diagnostic for imports of an invalid type. Also, array should be handled?
            let pd = scope.package_directory.to_string();
            self.trace(
                &tsc_diagnostics::X_package_json_scope_0_has_no_imports_defined,
                &[pd],
            );
            return None;
        }

        if let Some(result) = self.load_module_from_exports_or_imports(
            self.extensions,
            &self.name.clone(),
            contents.imports.as_object(),
            &scope,
            true, /*isImports*/
        ) {
            return Some(result);
        }

        let name = self.name.clone();
        let pd = scope.package_directory.to_string();
        self.trace(
            &tsc_diagnostics::Import_specifier_0_does_not_exist_in_package_json_scope_at_path_1,
            &[name, pd],
        );
        None
    }

    /// `func (r *resolutionState) loadModuleFromExports(packageInfo *packagejson.InfoCacheEntry, ext extensions, subpath string) *resolved`
    fn load_module_from_exports(
        &mut self,
        package_info: &InfoCacheEntry,
        ext: Extensions,
        subpath: &str,
    ) -> Option<Resolved> {
        // !!! This is ported exactly, but the falsy check seems wrong
        if !package_info.exists()
            || package_info
                .contents
                .as_deref()
                .is_none_or(|c| c.exports.is_falsy())
        {
            return None;
        }
        let contents = package_info.contents.as_deref().unwrap();

        if subpath == "." {
            let mut main_export: Option<&ExportsOrImports> = None;
            match contents.exports.type_ {
                JSONValueType::String | JSONValueType::Array => {
                    main_export = Some(&contents.exports);
                }
                JSONValueType::Object => {
                    if contents.exports.is_conditions() {
                        main_export = Some(&contents.exports);
                    } else if let Some(dot) = contents.exports.as_object().get(".") {
                        main_export = Some(dot);
                    }
                }
                _ => {}
            }
            if let Some(main_export) = main_export {
                if main_export.type_ != JSONValueType::NotPresent {
                    return self.load_module_from_target_export_or_import(
                        ext,
                        subpath,
                        package_info,
                        false, /*isImports*/
                        main_export,
                        "",
                        false, /*isPattern*/
                        ".",
                    );
                }
            }
        } else if contents.exports.type_ == JSONValueType::Object && contents.exports.is_subpaths()
        {
            if let Some(result) = self.load_module_from_exports_or_imports(
                ext,
                subpath,
                contents.exports.as_object(),
                package_info,
                false, /*isImports*/
            ) {
                return Some(result);
            }
        }

        let pd = package_info.package_directory.to_string();
        self.trace(
            &tsc_diagnostics::Export_specifier_0_does_not_exist_in_package_json_scope_at_path_1,
            &[subpath.to_string(), pd],
        );
        None
    }

    /// `func (r *resolutionState) loadModuleFromExportsOrImports(...) *resolved`
    fn load_module_from_exports_or_imports(
        &mut self,
        extensions: Extensions,
        module_name: &str,
        lookup_table: &OrderedMap<String, ExportsOrImports>,
        scope: &InfoCacheEntry,
        is_imports: bool,
    ) -> Option<Resolved> {
        if !module_name.ends_with('/') && !module_name.contains('*') {
            if let Some(target) = lookup_table.get(module_name) {
                return self.load_module_from_target_export_or_import(
                    extensions,
                    module_name,
                    scope,
                    is_imports,
                    target,
                    "",
                    false, /*isPattern*/
                    module_name,
                );
            }
        }

        let mut expanding_keys: Vec<&String> = Vec::with_capacity(lookup_table.size());
        for key in lookup_table.keys() {
            if key.matches('*').count() == 1 || key.ends_with('/') {
                expanding_keys.push(key);
            }
        }
        expanding_keys.sort_by(|a, b| crate::util::compare_pattern_keys(a, b));

        for potential_target in expanding_keys {
            if self
                .features
                .contains(NodeResolutionFeatures::EXPORTS_PATTERN_TRAILERS)
                && matches_pattern_with_trailer(potential_target, module_name)
            {
                let target = lookup_table.get(potential_target).unwrap();
                let star_pos = potential_target.find('*').unwrap();
                let subpath = &module_name
                    [star_pos..module_name.len() - (potential_target.len() - 1 - star_pos)];
                return self.load_module_from_target_export_or_import(
                    extensions,
                    module_name,
                    scope,
                    is_imports,
                    target,
                    subpath,
                    true,
                    potential_target,
                );
            } else if potential_target.ends_with('*')
                && module_name.starts_with(&potential_target[..potential_target.len() - 1])
            {
                let target = lookup_table.get(potential_target).unwrap();
                let subpath = &module_name[potential_target.len() - 1..];
                return self.load_module_from_target_export_or_import(
                    extensions,
                    module_name,
                    scope,
                    is_imports,
                    target,
                    subpath,
                    true,
                    potential_target,
                );
            } else if module_name.starts_with(potential_target.as_str()) {
                let target = lookup_table.get(potential_target).unwrap();
                let subpath = &module_name[potential_target.len()..];
                return self.load_module_from_target_export_or_import(
                    extensions,
                    module_name,
                    scope,
                    is_imports,
                    target,
                    subpath,
                    false,
                    potential_target,
                );
            }
        }

        None
    }

    /// `func (r *resolutionState) loadModuleFromTargetExportOrImport(...) *resolved`
    #[allow(clippy::too_many_arguments)]
    fn load_module_from_target_export_or_import(
        &mut self,
        extensions: Extensions,
        module_name: &str,
        scope: &InfoCacheEntry,
        is_imports: bool,
        target: &ExportsOrImports,
        subpath: &str,
        is_pattern: bool,
        key: &str,
    ) -> Option<Resolved> {
        match target.type_ {
            JSONValueType::String => {
                let target_string = target.as_string();
                if !is_pattern && !subpath.is_empty() && !target_string.ends_with('/') {
                    let pd = scope.package_directory.to_string();
                    let mn = module_name.to_string();
                    self.trace(
                        &tsc_diagnostics::X_package_json_scope_0_has_invalid_type_for_target_of_specifier_1,
                        &[pd, mn],
                    );
                    return None;
                }
                if !target_string.starts_with("./") {
                    if is_imports
                        && !target_string.starts_with("../")
                        && !target_string.starts_with('/')
                        && !tsc_tspath::is_rooted_disk_path(target_string)
                    {
                        let mut combined_lookup = format!("{target_string}{subpath}");
                        if is_pattern {
                            combined_lookup = target_string.replace('*', subpath);
                        }
                        let scope_containing_directory =
                            tsc_tspath::ensure_trailing_directory_separator(
                                scope.package_directory.as_directory_path().as_string(),
                            )
                            .into_owned();
                        let combined_for_trace = combined_lookup.clone();
                        self.trace(
                            &tsc_diagnostics::Using_0_subpath_1_with_target_2,
                            &["imports", key, combined_for_trace.as_str()],
                        );
                        self.trace(
                            &tsc_diagnostics::Resolving_module_0_from_1,
                            &[
                                combined_for_trace.as_str(),
                                scope_containing_directory.as_str(),
                            ],
                        );
                        // Go `defer` restore of name/containingDirectory/hasTrailingSeparator.
                        let saved_name = std::mem::take(&mut self.name);
                        let saved_directory = std::mem::replace(
                            &mut self.containing_directory,
                            scope.package_directory.as_directory_path().clone(),
                        );
                        let saved_trailing = self.containing_directory_has_trailing_separator;
                        self.name = combined_lookup;
                        self.containing_directory_has_trailing_separator = true;
                        let result = self.resolve_node_like();
                        self.name = saved_name;
                        self.containing_directory = saved_directory;
                        self.containing_directory_has_trailing_separator = saved_trailing;
                        if result.is_resolved() {
                            return Some(Resolved {
                                path: result.resolved_file_name,
                                extension: result.extension,
                                package_id: result.package_id,
                                original_path: result.original_path,
                                resolved_using_ts_extension: result.resolved_using_ts_extension,
                                ..Resolved::default()
                            });
                        }
                        return None;
                    }
                    let pd = scope.package_directory.to_string();
                    let mn = module_name.to_string();
                    self.trace(
                        &tsc_diagnostics::X_package_json_scope_0_has_invalid_type_for_target_of_specifier_1,
                        &[pd, mn],
                    );
                    return None;
                }
                let parts = if tsc_tspath::path_is_relative(target_string) {
                    tsc_tspath::get_path_components(target_string)[1..].to_vec()
                } else {
                    tsc_tspath::get_path_components(target_string)
                };
                let parts_after_first = &parts[1..];
                if parts_after_first.iter().any(|p| p == "..")
                    || parts_after_first.iter().any(|p| p == ".")
                    || parts_after_first.iter().any(|p| p == "node_modules")
                {
                    let pd = scope.package_directory.to_string();
                    let mn = module_name.to_string();
                    self.trace(
                        &tsc_diagnostics::X_package_json_scope_0_has_invalid_type_for_target_of_specifier_1,
                        &[pd, mn],
                    );
                    return None;
                }
                // TODO: Assert that `resolvedTarget` is actually within the package directory? That's what the spec says.... but I'm not sure we need
                // to be in the business of validating everyone's import and export map correctness.
                let subpath_parts = tsc_tspath::get_path_components(subpath);
                if subpath_parts.iter().any(|p| p == "..")
                    || subpath_parts.iter().any(|p| p == ".")
                    || subpath_parts.iter().any(|p| p == "node_modules")
                {
                    let pd = scope.package_directory.to_string();
                    let mn = module_name.to_string();
                    self.trace(
                        &tsc_diagnostics::X_package_json_scope_0_has_invalid_type_for_target_of_specifier_1,
                        &[pd, mn],
                    );
                    return None;
                }

                let target_path = if is_pattern {
                    target_string.replace('*', subpath)
                } else {
                    format!("{target_string}{subpath}")
                };
                let imports_or_exports = if is_imports { "imports" } else { "exports" };
                self.trace(
                    &tsc_diagnostics::Using_0_subpath_1_with_target_2,
                    &[imports_or_exports, key, target_path.as_str()],
                );
                let final_path = resolution_candidate_from_directory_path(
                    scope.package_directory.as_directory_path(),
                    &target_path,
                );
                if let Some(mut input_link) = self.try_load_input_file_for_path(
                    &final_path,
                    subpath,
                    &scope.package_directory.resolve_file("package.json"),
                    is_imports,
                ) {
                    input_link.package_id =
                        self.get_package_id(&input_link.path, &Some(Arc::new(scope.clone())));
                    return Some(input_link);
                }
                if let Some(mut result) = self.load_file_name_from_package_json_field(
                    extensions,
                    &final_path,
                    target_string,
                ) {
                    result.package_id =
                        self.get_package_id(&result.path, &Some(Arc::new(scope.clone())));
                    return Some(result);
                }
                None
            }
            JSONValueType::Object => {
                self.trace(
                    &tsc_diagnostics::Entering_conditional_exports,
                    &[] as &[String],
                );
                for condition in target.as_object().keys() {
                    if self.condition_matches(condition) {
                        let kind = if is_imports { "imports" } else { "exports" };
                        self.trace(
                            &tsc_diagnostics::Matched_0_condition_1,
                            &[kind, condition.as_str()],
                        );
                        let sub_target = target.as_object().get(condition).unwrap();
                        if let Some(result) = self.load_module_from_target_export_or_import(
                            extensions,
                            module_name,
                            scope,
                            is_imports,
                            sub_target,
                            subpath,
                            is_pattern,
                            key,
                        ) {
                            if result.is_resolved() && self.tracer.is_some() {
                                self.trace(
                                    &tsc_diagnostics::Resolved_under_condition_0,
                                    &[condition.clone()],
                                );
                            }
                            self.trace(
                                &tsc_diagnostics::Exiting_conditional_exports,
                                &[] as &[String],
                            );
                            return Some(result);
                        }
                        self.trace(
                            &tsc_diagnostics::Failed_to_resolve_under_condition_0,
                            &[condition.clone()],
                        );
                    } else {
                        self.trace(
                            &tsc_diagnostics::Saw_non_matching_condition_0,
                            &[condition.clone()],
                        );
                    }
                }
                self.trace(
                    &tsc_diagnostics::Exiting_conditional_exports,
                    &[] as &[String],
                );
                None
            }
            JSONValueType::Array => {
                if target.as_array().is_empty() {
                    let pd = scope.package_directory.to_string();
                    let mn = module_name.to_string();
                    self.trace(
                        &tsc_diagnostics::X_package_json_scope_0_has_invalid_type_for_target_of_specifier_1,
                        &[pd, mn],
                    );
                    return None;
                }
                for elem in target.as_array() {
                    if let Some(result) = self.load_module_from_target_export_or_import(
                        extensions,
                        module_name,
                        scope,
                        is_imports,
                        elem,
                        subpath,
                        is_pattern,
                        key,
                    ) {
                        return Some(result);
                    }
                }
                // fall through to the shared failure trace below
                let pd = scope.package_directory.to_string();
                let mn = module_name.to_string();
                self.trace(
                    &tsc_diagnostics::X_package_json_scope_0_has_invalid_type_for_target_of_specifier_1,
                    &[pd, mn],
                );
                None
            }
            JSONValueType::Null => {
                let pd = scope.package_directory.to_string();
                let mn = module_name.to_string();
                self.trace(
                    &tsc_diagnostics::X_package_json_scope_0_explicitly_maps_specifier_1_to_null,
                    &[pd, mn],
                );
                unresolved()
            }
            _ => {
                let pd = scope.package_directory.to_string();
                let mn = module_name.to_string();
                self.trace(
                    &tsc_diagnostics::X_package_json_scope_0_has_invalid_type_for_target_of_specifier_1,
                    &[pd, mn],
                );
                None
            }
        }
    }

    /// `func (r *resolutionState) tryLoadInputFileForPath(finalCandidate resolutionCandidate, entry string, packagePath tspath.RootedFilePath, isImports bool) *resolved`
    fn try_load_input_file_for_path(
        &mut self,
        final_candidate: &ResolutionCandidate,
        entry: &str,
        package_path: &RootedFilePath,
        is_imports: bool,
    ) -> Option<Resolved> {
        if final_candidate.directory_only {
            return None;
        }
        let final_file_name = tsc_tspath::rooted_file_path_from_path(final_candidate.path.clone());
        let case_sensitivity = self.resolver.fs.case_sensitivity();
        // Replace any references to outputs for files in the program with the input files to support package self-names used with outDir
        if !self.is_config_lookup
            && (!self.compiler_options.declaration_dir.is_empty()
                || !self.compiler_options.out_dir.is_empty())
            && !final_file_name.contains_lowercase_directory_sequence("/node_modules/")
            && (self.compiler_options.config_file_path.is_empty()
                || case_sensitivity.contains_file_path(
                    &package_path.directory(),
                    &self.compiler_options.config_file_path,
                ))
        {
            // Note: this differs from Strada's tryLoadInputFileForPath in that it
            // does not attempt to perform "guesses", instead requring a clear root indicator.
            let root_dir: RootedDirectoryPath;
            if !self.compiler_options.root_dir.is_empty() {
                // A `rootDir` compiler option strongly indicates the root location
                root_dir = self.compiler_options.root_dir.clone();
            } else if !self.compiler_options.config_file_path.is_empty() {
                // When no explicit rootDir is set, treat the config file's directory as the project root, which establishes the common source directory, so no other locations need to be checked.
                root_dir = self.compiler_options.config_file_path.directory();
            } else {
                let message = if is_imports {
                    &tsc_diagnostics::The_project_root_is_ambiguous_but_is_required_to_resolve_import_map_entry_0_in_file_1_Supply_the_rootDir_compiler_option_to_disambiguate
                } else {
                    &tsc_diagnostics::The_project_root_is_ambiguous_but_is_required_to_resolve_export_map_entry_0_in_file_1_Supply_the_rootDir_compiler_option_to_disambiguate
                };
                let diagnostic = tsc_ast::diagnostic::new_diagnostic(
                    None,
                    TextRange::default(),
                    message,
                    &[
                        // replace empty string with `.` - the reverse of the operation done when entries are built - so main entrypoint errors don't look weird
                        if_else(entry.is_empty(), ".", entry).to_string(),
                        package_path.as_string().to_string(),
                    ],
                );
                self.diagnostics.push(diagnostic);
                return unresolved();
            }

            let candidate_directories = self.get_output_directories();
            for candidate_dir in &candidate_directories {
                if let Some(path_fragment) =
                    case_sensitivity.relative_path_from_directory(candidate_dir, &final_file_name)
                {
                    // The matched export is looking up something in either the out declaration or js dir, now map the written path back into the source dir and source extension
                    let possible_input_base = root_dir.resolve_relative_file(&path_fragment);
                    let js_and_dts_extensions = [
                        tsc_tspath::EXTENSION_MJS,
                        tsc_tspath::EXTENSION_CJS,
                        tsc_tspath::EXTENSION_JS,
                        tsc_tspath::EXTENSION_JSON,
                        tsc_tspath::EXTENSION_DMTS,
                        tsc_tspath::EXTENSION_DCTS,
                        tsc_tspath::EXTENSION_DTS,
                    ];
                    for ext in js_and_dts_extensions {
                        if possible_input_base.extension_is(ext) {
                            let input_exts =
                                possible_input_base.possible_original_input_extensions();
                            for possible_ext in &input_exts {
                                if !extension_is_ok(self.extensions, possible_ext) {
                                    continue;
                                }
                                let possible_input_with_input_extension =
                                    possible_input_base.change_extension(possible_ext);
                                if self
                                    .resolver
                                    .fs
                                    .file_exists(&possible_input_with_input_extension)
                                {
                                    if let Some(resolved) = self
                                        .load_file_name_from_package_json_field(
                                            self.extensions,
                                            &resolution_candidate_from_file_name(
                                                &possible_input_with_input_extension,
                                            ),
                                            "",
                                        )
                                    {
                                        return Some(resolved);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// `func (r *resolutionState) getOutputDirectories() []tspath.RootedDirectoryPath`
    fn get_output_directories(&self) -> Vec<RootedDirectoryPath> {
        let mut candidate_directories: Vec<RootedDirectoryPath> = Vec::new();
        if !self.compiler_options.declaration_dir.is_empty() {
            candidate_directories.push(self.compiler_options.declaration_dir.clone());
        }
        if !self.compiler_options.out_dir.is_empty()
            && self.compiler_options.out_dir != self.compiler_options.declaration_dir
        {
            candidate_directories.push(self.compiler_options.out_dir.clone());
        }
        candidate_directories
    }

    /// `func (r *resolutionState) loadModuleFromNearestNodeModulesDirectory(typesScopeOnly bool) *resolved`
    fn load_module_from_nearest_node_modules_directory(
        &mut self,
        types_scope_only: bool,
    ) -> Option<Resolved> {
        let mode = if self.esm_mode || self.condition_matches("import") {
            RESOLUTION_MODE_ESM
        } else {
            RESOLUTION_MODE_COMMON_JS
        };
        let _ = mode; // PORT: `mode` is computed in Go but unused by the worker.
        // Do (up to) two passes through node_modules:
        //   1. For each ancestor node_modules directory, try to find:
        //      i.  TS/DTS files in the implementation package
        //      ii. DTS files in the @types package
        //   2. For each ancestor node_modules directory, try to find:
        //      i.  JS files in the implementation package
        let priority_extensions =
            self.extensions & (EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION);
        let secondary_extensions =
            Extensions(self.extensions.0 & !(EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION).0);
        // (1)
        if priority_extensions.0 != 0 {
            let ext_str = priority_extensions.to_string();
            self.trace(
                &tsc_diagnostics::Searching_all_ancestor_node_modules_directories_for_preferred_extensions_Colon_0,
                &[ext_str],
            );
            if let Some(result) = self.load_module_from_nearest_node_modules_directory_worker(
                priority_extensions,
                mode,
                types_scope_only,
            ) {
                return Some(result);
            }
        }
        // (2)
        if secondary_extensions.0 != 0 && !types_scope_only {
            let ext_str = secondary_extensions.to_string();
            self.trace(
                &tsc_diagnostics::Searching_all_ancestor_node_modules_directories_for_fallback_extensions_Colon_0,
                &[ext_str],
            );
            return self.load_module_from_nearest_node_modules_directory_worker(
                secondary_extensions,
                mode,
                types_scope_only,
            );
        }
        None
    }

    /// `func (r *resolutionState) loadModuleFromNearestNodeModulesDirectoryWorker(...) *resolved`
    fn load_module_from_nearest_node_modules_directory_worker(
        &mut self,
        ext: Extensions,
        mode: ResolutionMode,
        types_scope_only: bool,
    ) -> Option<Resolved> {
        let _ = mode; // PORT: Go computes `mode` but never reads it in the worker.
        let containing_directory = self.containing_directory.clone();
        containing_directory
            .for_each_ancestor_directory(|directory| {
                // !!! stop at global cache
                if directory.as_path().base_name() != "node_modules" {
                    let result = self.load_module_from_immediate_node_modules_directory(
                        ext,
                        directory,
                        types_scope_only,
                    );
                    let stop = result.is_some();
                    return (result, stop);
                }
                (None, false)
            })
            .flatten()
    }

    /// `func (r *resolutionState) loadModuleFromImmediateNodeModulesDirectory(...) *resolved`
    fn load_module_from_immediate_node_modules_directory(
        &mut self,
        extensions: Extensions,
        directory: &RootedDirectoryPath,
        types_scope_only: bool,
    ) -> Option<Resolved> {
        let node_modules_folder = directory.resolve_directory("node_modules");
        if !self.resolver.fs.directory_exists(&node_modules_folder) {
            let dir = node_modules_folder.as_string().to_string();
            self.trace(
                &tsc_diagnostics::Directory_0_does_not_exist_skipping_all_lookups_in_it,
                &[dir],
            );
            return None;
        }

        if !types_scope_only {
            let name = self.name.clone();
            if let Some(package_result) = self.load_module_from_specific_node_modules_directory(
                extensions,
                &name,
                &node_modules_folder,
            ) {
                return Some(package_result);
            }
        }

        if extensions.contains(EXTENSIONS_DECLARATION) {
            let node_modules_at_types = node_modules_folder.resolve_directory("@types");
            if !self.resolver.fs.directory_exists(&node_modules_at_types) {
                let dir = node_modules_at_types.as_string().to_string();
                self.trace(
                    &tsc_diagnostics::Directory_0_does_not_exist_skipping_all_lookups_in_it,
                    &[dir],
                );
                return None;
            }
            let mangled = self.mangle_scoped_package_name(&self.name.clone());
            return self.load_module_from_specific_node_modules_directory(
                EXTENSIONS_DECLARATION,
                &mangled,
                &node_modules_at_types,
            );
        }

        None
    }

    /// `func (r *resolutionState) loadModuleFromSpecificNodeModulesDirectory(ext extensions, moduleName string, nodeModulesDirectory tspath.RootedDirectoryPath) *resolved`
    fn load_module_from_specific_node_modules_directory(
        &mut self,
        ext: Extensions,
        module_name: &str,
        node_modules_directory: &RootedDirectoryPath,
    ) -> Option<Resolved> {
        // Strip any trailing directory separator so that imports like `pkg/` and `pkg`
        // produce identical `candidate` and `packageDirectory` strings. Otherwise the
        // `package.json` info cache (which is keyed by normalized path but stores the
        // caller's `PackageDirectory` verbatim) can hand back, under concurrent
        // inserts, an entry whose `PackageDirectory` doesn't match `candidate`,
        // causing `loadNodeModuleFromDirectoryWorker`'s `ComparePaths(candidate, ...)`
        // check to fail and skip loading the package's `main`/`types` entry.
        // https://github.com/microsoft/TypeScript/tsc/issues/3526
        let candidate =
            resolution_candidate_from_directory_path(node_modules_directory, module_name);
        let candidate_directory = candidate.as_directory_path();
        let (package_name, rest) = parse_package_name(module_name);
        let package_directory = if package_name.is_empty() {
            candidate_directory.clone()
        } else {
            node_modules_directory.resolve_directory(&path_for_dynamic_resolution(
                node_modules_directory,
                package_name,
                true,
            ))
        };

        if self.resolve_package_directory_only {
            if self.resolver.fs.directory_exists(&package_directory) {
                return Some(Resolved {
                    path: tsc_tspath::rooted_file_path_from_path(package_directory.as_path()),
                    ..Resolved::default()
                });
            }
            return None;
        }

        let mut root_package_info: Option<Arc<InfoCacheEntry>> = None;
        // First look for a nested package.json, as in `node_modules/foo/bar/package.json`
        let mut package_info =
            self.get_package_json_info(&self.package_directory(candidate_directory.clone()));
        // But only if we're not respecting export maps (if we are, we might redirect around this location)
        if !rest.is_empty() && package_json_exists(&package_info) {
            if self.features.contains(NodeResolutionFeatures::EXPORTS) {
                root_package_info =
                    self.get_package_json_info(&self.package_directory(package_directory.clone()));
            }
            if !package_json_exists(&root_package_info)
                || package_json_contents(&root_package_info)
                    .unwrap()
                    .exports
                    .type_
                    == JSONValueType::NotPresent
            {
                if let Some(from_file) = self.load_module_from_file(ext, &candidate) {
                    return Some(from_file);
                }

                if let Some(mut from_directory) = self.load_node_module_from_directory_worker(
                    ext,
                    &candidate_directory,
                    &package_info,
                ) {
                    from_directory.package_id =
                        self.get_package_id(&from_directory.path, &package_info);
                    return Some(from_directory);
                }
            }
        }

        // PORT: Go declares this loader closure before the `packageInfo` swap
        // below; since the closure only reads `packageInfo` when invoked (all
        // invocations happen after the swap), defining it after the swap is
        // observationally identical — a Rust closure could not capture the
        // binding across a reassignment.
        if !rest.is_empty() {
            package_info = root_package_info;
            if package_info.is_none() {
                // Previous `packageInfo` may have been from a nested package.json; ensure we have the one from the package root now.
                package_info =
                    self.get_package_json_info(&self.package_directory(package_directory.clone()));
            }
        }

        let mut loader = |r: &mut ResolutionState<'a>,
                          extensions: Extensions,
                          candidate: &ResolutionCandidate|
         -> Option<Resolved> {
            if !rest.is_empty() || !r.esm_mode {
                if let Some(mut from_file) = r.load_module_from_file(extensions, candidate) {
                    from_file.package_id = r.get_package_id(&from_file.path, &package_info);
                    return Some(from_file);
                }
            }
            if let Some(mut from_directory) = r.load_node_module_from_directory_worker(
                extensions,
                &candidate.as_directory_path(),
                &package_info,
            ) {
                from_directory.package_id = r.get_package_id(&from_directory.path, &package_info);
                return Some(from_directory);
            }
            if rest.is_empty()
                && package_json_exists(&package_info)
                && matches!(
                    package_json_contents(&package_info).unwrap().exports.type_,
                    JSONValueType::NotPresent | JSONValueType::Null
                )
                && r.esm_mode
            {
                // EsmMode disables index lookup in `loadNodeModuleFromDirectoryWorker` generally, however non-relative package resolutions still assume
                // a default `index.js` entrypoint if no `main` or `exports` are present
                let index_candidate = resolution_candidate_from_directory_path(
                    &candidate.as_directory_path(),
                    "index.js",
                );
                if let Some(mut index_result) =
                    r.load_module_from_file(extensions, &index_candidate)
                {
                    index_result.package_id = r.get_package_id(&index_result.path, &package_info);
                    return Some(index_result);
                }
            }
            None
        };

        if package_info.is_some() {
            self.resolved_package_directory = true;
            if self.features.contains(NodeResolutionFeatures::EXPORTS)
                && package_json_exists(&package_info)
                && !package_json_contents(&package_info)
                    .unwrap()
                    .exports
                    .is_falsy()
            {
                // package exports are higher priority than file/directory/typesVersions lookups and (and, if there's exports present*, blocks them)
                // *Well, weirdly enough a top-level `"exports": null` does NOT block fallback resolution.
                // https://github.com/microsoft/TypeScript/pull/49327
                return self.load_module_from_exports(
                    package_info.as_deref().unwrap(),
                    ext,
                    &tsc_tspath::combine_paths(".", &[rest]),
                );
            }
            if !rest.is_empty() && package_json_exists(&package_info) {
                let contents = package_json_contents(&package_info).unwrap();
                let mut version_paths = {
                    // PORT: `get_version_paths` requires a `'static`
                    // `TraceFunc`, so the tracer is shared through
                    // `Rc<RefCell>` for the duration of the call.
                    let shared = std::rc::Rc::new(std::cell::RefCell::new(self.tracer.take()));
                    let shared2 = std::rc::Rc::clone(&shared);
                    let mut trace_func = move |m: &'static Message, args: &[String]| {
                        if let Some(t) = shared2.borrow_mut().as_mut() {
                            t.write(m, args);
                        }
                    };
                    let version_paths = contents.get_version_paths(Some(&mut trace_func));
                    self.tracer = shared.borrow_mut().take();
                    version_paths
                };
                if version_paths.exists() {
                    let vv = version_paths.version.clone();
                    let version = tsc_core::version::version().to_string();
                    self.trace(
                        &tsc_diagnostics::X_package_json_has_a_typesVersions_entry_0_that_matches_compiler_version_1_looking_for_a_pattern_to_match_module_name_2,
                        &[vv, version, rest.to_string()],
                    );
                    let path_patterns = try_parse_patterns(version_paths.get_paths());
                    if let Some(paths_map) = version_paths.get_paths() {
                        if let Some(from_paths) = self.try_load_module_using_paths(
                            ext,
                            rest,
                            &package_directory,
                            paths_map,
                            &path_patterns,
                            &mut loader,
                        ) {
                            return Some(from_paths);
                        }
                    }
                }
            }
        }
        loader(self, ext, &candidate)
    }

    /// `func (r *resolutionState) createResolvedModuleHandlingSymlink(resolved *resolved) *ResolvedModule`
    fn create_resolved_module_handling_symlink(
        &mut self,
        resolved: Option<Resolved>,
    ) -> ResolvedModule {
        let is_external_library_import = resolved.as_ref().is_some_and(|r| {
            r.path
                .contains_lowercase_directory_sequence("/node_modules/")
        });
        let mut resolved = resolved;
        if self.compiler_options.preserve_symlinks != TS_TRUE
            && is_external_library_import
            && resolved
                .as_ref()
                .is_some_and(|r| r.original_path.as_string().is_empty())
            && !tsc_tspath::is_external_module_name_relative(&self.name)
        {
            let (original_path, resolved_file_name) =
                self.get_original_and_resolved_file_name(&resolved.as_ref().unwrap().path);
            if !original_path.as_string().is_empty() {
                let resolved = resolved.as_mut().unwrap();
                resolved.path = resolved_file_name;
                resolved.original_path = original_path;
            }
        }
        self.create_resolved_module(resolved, is_external_library_import)
    }

    /// `func (r *resolutionState) createResolvedModule(resolved *resolved, isExternalLibraryImport bool) *ResolvedModule`
    fn create_resolved_module(
        &self,
        resolved: Option<Resolved>,
        is_external_library_import: bool,
    ) -> ResolvedModule {
        let mut resolved_module = ResolvedModule::default();
        resolved_module.resolution_diagnostics = self.diagnostics.clone();

        if let Some(resolved) = resolved {
            if resolved.is_resolved() {
                resolved_module.resolved_file_name = resolved.path.clone();
                resolved_module.resolved_path = self
                    .resolver
                    .fs
                    .case_sensitivity()
                    .path_key(&resolved.path.as_path());
                if !resolved.original_path.as_string().is_empty() {
                    resolved_module.original_path = resolved.original_path.clone();
                }
            }
            resolved_module.is_external_library_import = is_external_library_import;
            resolved_module.resolved_using_ts_extension = resolved.resolved_using_ts_extension;
            resolved_module.resolved_using_extra_extensions =
                resolved.resolved_using_extra_extensions;
            resolved_module.extension = resolved.extension;
            resolved_module.package_id = resolved.package_id;
        }
        resolved_module
    }

    /// `func (r *resolutionState) createResolvedTypeReferenceDirective(resolved *resolved, primary bool) *ResolvedTypeReferenceDirective`
    fn create_resolved_type_reference_directive(
        &mut self,
        resolved: Option<Resolved>,
        primary: bool,
    ) -> ResolvedTypeReferenceDirective {
        let mut resolved_type_reference_directive = ResolvedTypeReferenceDirective::default();
        resolved_type_reference_directive.resolution_diagnostics = self.diagnostics.clone();

        // PORT: Go's `resolved.isResolved()` is a nil-receiver method call —
        // `resolved` may be `nil` here and returns false.
        if resolved.as_ref().is_some_and(|r| r.is_resolved()) {
            let resolved = resolved.unwrap();
            if !tsc_tspath::extension_is_ts(&resolved.extension) {
                panic!("expected a TypeScript file extension");
            }
            resolved_type_reference_directive.resolved_file_name = resolved.path.clone();
            resolved_type_reference_directive.primary = primary;
            resolved_type_reference_directive.package_id = resolved.package_id.clone();
            resolved_type_reference_directive.is_external_library_import = resolved
                .path
                .contains_lowercase_directory_sequence("/node_modules/");

            if self.compiler_options.preserve_symlinks != TS_TRUE {
                let (original_path, resolved_file_name) =
                    self.get_original_and_resolved_file_name(&resolved.path);
                if !original_path.as_string().is_empty() {
                    resolved_type_reference_directive.resolved_file_name = resolved_file_name;
                    resolved_type_reference_directive.original_path = original_path;
                }
            }
            resolved_type_reference_directive.resolved_path =
                self.resolver.fs.case_sensitivity().path_key(
                    &resolved_type_reference_directive
                        .resolved_file_name
                        .as_path(),
                );
        }
        resolved_type_reference_directive
    }

    /// `func (r *resolutionState) getOriginalAndResolvedFileName(fileName tspath.RootedFilePath) (tspath.RootedFilePath, tspath.RootedFilePath)`
    fn get_original_and_resolved_file_name(
        &mut self,
        file_name: &RootedFilePath,
    ) -> (RootedFilePath, RootedFilePath) {
        let resolved_file_name = self.real_path(file_name);
        let case_sensitivity = self.resolver.fs.case_sensitivity();
        if case_sensitivity.compare_file_paths(file_name, &resolved_file_name) == 0 {
            // If the fileName and realpath are differing only in casing, prefer fileName
            // so that we can issue correct errors for casing under forceConsistentCasingInFileNames
            return (RootedFilePath::default(), file_name.clone());
        }
        (file_name.clone(), resolved_file_name)
    }

    /// `func (r *resolutionState) tryLoadModuleUsingOptionalResolutionSettings() *resolved`
    fn try_load_module_using_optional_resolution_settings(&mut self) -> Option<Resolved> {
        if let Some(resolved) = self.try_load_module_using_paths_if_eligible() {
            return Some(resolved);
        }

        if !tsc_tspath::is_external_module_name_relative(&self.name) {
            // No more tryLoadModuleUsingBaseUrl.
            None
        } else {
            self.try_load_module_using_root_dirs()
        }
    }

    /// `func (r *resolutionState) getParsedPatternsForPaths() *ParsedPatterns`
    fn get_parsed_patterns_for_paths(&self) -> Arc<ParsedPatterns> {
        self.resolver
            .get_parsed_patterns_for_paths(&self.compiler_options)
    }

    /// `func (r *resolutionState) tryLoadModuleUsingPathsIfEligible() *resolved`
    fn try_load_module_using_paths_if_eligible(&mut self) -> Option<Resolved> {
        if self
            .compiler_options
            .paths
            .as_ref()
            .is_some_and(|p| p.size() > 0)
            && !tsc_tspath::path_is_relative(&self.name)
        {
            let name = self.name.clone();
            self.trace(
                &tsc_diagnostics::X_paths_option_is_specified_looking_for_a_pattern_to_match_module_name_0,
                &[name],
            );
        } else {
            return None;
        }
        let base_directory = self
            .compiler_options
            .get_paths_base_path(&self.resolver.base_directory);
        let path_patterns = self.get_parsed_patterns_for_paths();
        let name = self.name.clone();
        let paths = self.compiler_options.paths.clone().unwrap_or_default();
        let mut loader = |r: &mut ResolutionState<'a>,
                          extensions: Extensions,
                          candidate: &ResolutionCandidate|
         -> Option<Resolved> {
            r.node_load_module_by_relative_name(
                extensions, candidate, true, /*considerPackageJson*/
            )
        };
        self.try_load_module_using_paths(
            self.extensions,
            &name,
            &base_directory,
            &paths,
            &path_patterns,
            &mut loader,
        )
    }

    /// `func (r *resolutionState) tryLoadModuleUsingPaths(extensions extensions, moduleName string, containingDirectory tspath.RootedDirectoryPath, paths *collections.OrderedMap[string, []string], pathPatterns *ParsedPatterns, loader resolutionKindSpecificLoader) *resolved`
    ///
    /// PORT: `paths` is generic over the value type — `CompilerOptions.paths`
    /// is `OrderedMap<String, Option<Vec<String>>>` while `typesVersions`
    /// paths are `OrderedMap<String, Vec<String>>`; both share the
    /// `GetOrZero` iteration semantics.
    fn try_load_module_using_paths<V: PathSubstitutions>(
        &mut self,
        extensions: Extensions,
        module_name: &str,
        containing_directory: &RootedDirectoryPath,
        paths: &OrderedMap<String, V>,
        path_patterns: &ParsedPatterns,
        loader: &mut ResolutionKindSpecificLoader<'a, '_>,
    ) -> Option<Resolved> {
        let matched_pattern = match_pattern_or_exact(path_patterns, module_name);
        if matched_pattern.is_valid() {
            let matched_star = matched_pattern.matched_text(module_name);
            let mn = module_name.to_string();
            let text = matched_pattern.text.clone();
            self.trace(
                &tsc_diagnostics::Module_name_0_matched_pattern_1,
                &[mn, text],
            );
            let substitutions = paths
                .get(&matched_pattern.text)
                .map_or(&[][..], |v| v.substitutions());
            for subst in substitutions {
                let path = subst.replacen('*', matched_star, 1);
                let candidate =
                    resolution_candidate_from_directory_path(containing_directory, &path);
                self.trace(
                    &tsc_diagnostics::Trying_substitution_0_candidate_module_location_Colon_1,
                    &[subst.clone(), path],
                );
                // A path mapping may have an extension
                let extension_from_subst = tsc_tspath::try_get_extension_from_path(subst);
                if !extension_from_subst.is_empty() {
                    if let Some(path) = self.try_file(&candidate) {
                        return Some(Resolved {
                            path,
                            extension: extension_from_subst.to_string(),
                            ..Resolved::default()
                        });
                    }
                }
                // When the substitution path has an explicit extension, the extension came from the
                // paths config, not the module specifier. Suppress resolvedUsingTsExtension in that case.
                let save_candidate_ending_is_from_config = self.candidate_ending_is_from_config;
                if !extension_from_subst.is_empty() {
                    self.candidate_ending_is_from_config = true;
                }
                let resolved = loader(self, extensions, &candidate);
                self.candidate_ending_is_from_config = save_candidate_ending_is_from_config;
                if let Some(resolved) = resolved {
                    return Some(resolved);
                }
            }
        }
        None
    }

    /// `func (r *resolutionState) tryLoadModuleUsingRootDirs() *resolved`
    fn try_load_module_using_root_dirs(&mut self) -> Option<Resolved> {
        let root_dirs = self
            .compiler_options
            .get_effective_root_dirs()
            .unwrap_or_default();
        if root_dirs.is_empty() {
            return None;
        }

        let name = self.name.clone();
        self.trace(
            &tsc_diagnostics::X_rootDirs_option_is_set_using_it_to_resolve_relative_module_name_0,
            &[name],
        );

        let candidate =
            resolution_candidate_from_directory_path(&self.containing_directory, &self.name);

        let mut matched_root_dir = RootedDirectoryPath::default();
        for root_dir in &root_dirs {
            let is_longest_matching_prefix = candidate.has_directory_prefix(root_dir)
                && (matched_root_dir.is_empty() || matched_root_dir.len() < root_dir.len());
            self.trace(
                &tsc_diagnostics::Checking_if_0_is_the_longest_matching_prefix_for_1_2,
                &[
                    tsc_tspath::ensure_trailing_directory_separator(root_dir.as_string())
                        .into_owned(),
                    candidate.as_string(),
                    is_longest_matching_prefix.to_string(),
                ],
            );
            if is_longest_matching_prefix {
                matched_root_dir = root_dir.clone();
            }
        }

        if !matched_root_dir.is_empty() {
            let longest =
                tsc_tspath::ensure_trailing_directory_separator(matched_root_dir.as_string())
                    .into_owned();
            self.trace(
                &tsc_diagnostics::Longest_matching_prefix_for_0_is_1,
                &[candidate.as_string(), longest.clone()],
            );
            let suffix = candidate.relative_to_directory(&matched_root_dir);

            // first - try to load from a initial location
            self.trace(
                &tsc_diagnostics::Loading_0_from_the_root_dir_1_candidate_location_2,
                &[
                    suffix.as_string().to_string(),
                    longest.clone(),
                    candidate.as_string(),
                ],
            );
            let loader = |r: &mut ResolutionState<'a>,
                          extensions: Extensions,
                          candidate: &ResolutionCandidate|
             -> Option<Resolved> {
                r.node_load_module_by_relative_name(
                    extensions, candidate, true, /*considerPackageJson*/
                )
            };
            if let Some(resolved_file_name) = loader(self, self.extensions, &candidate) {
                return Some(resolved_file_name);
            }

            self.trace(
                &tsc_diagnostics::Trying_other_entries_in_rootDirs,
                &[] as &[String],
            );
            // then try to resolve using remaining entries in rootDirs
            for root_dir in &root_dirs {
                if *root_dir == matched_root_dir {
                    // skip the initially matched entry
                    continue;
                }
                let mut logical_suffix = suffix.as_string().to_string();
                let directory_only =
                    suffix.as_string().is_empty() || suffix.has_trailing_directory_separator();
                let candidate;
                if tsc_tspath::is_encoded_dynamic_file_name(root_dir.as_string()) {
                    if tsc_tspath::is_encoded_dynamic_file_name(matched_root_dir.as_string()) {
                        logical_suffix =
                            tsc_tspath::decode_dynamic_uri_path(&logical_suffix).into_owned();
                    }
                    candidate =
                        resolution_candidate_from_dynamic_logical_path(root_dir, &logical_suffix);
                } else if tsc_tspath::is_encoded_dynamic_file_name(matched_root_dir.as_string()) {
                    let Some(decoded) =
                        tsc_tspath::decode_dynamic_uri_path_for_disk(&logical_suffix)
                    else {
                        continue;
                    };
                    logical_suffix = decoded;
                    candidate = resolution_candidate_from_disk_logical_path(
                        root_dir,
                        &logical_suffix,
                        directory_only,
                    );
                } else {
                    candidate = resolution_candidate_from_relative_path(root_dir, &suffix);
                }
                self.trace(
                    &tsc_diagnostics::Loading_0_from_the_root_dir_1_candidate_location_2,
                    &[
                        suffix.as_string().to_string(),
                        root_dir.as_string().to_string(),
                        candidate.as_string(),
                    ],
                );
                if let Some(resolved_file_name) = loader(self, self.extensions, &candidate) {
                    return Some(resolved_file_name);
                }
            }
            self.trace(
                &tsc_diagnostics::Module_resolution_using_rootDirs_has_failed,
                &[] as &[String],
            );
        }
        None
    }

    /// `func (r *resolutionState) nodeLoadModuleByRelativeName(extensions extensions, candidate resolutionCandidate, considerPackageJson bool) *resolved`
    fn node_load_module_by_relative_name(
        &mut self,
        extensions: Extensions,
        candidate: &ResolutionCandidate,
        consider_package_json: bool,
    ) -> Option<Resolved> {
        let cand = candidate.as_string();
        let ext_str = extensions.to_string();
        self.trace(
            &tsc_diagnostics::Loading_module_as_file_Slash_folder_candidate_module_location_0_target_file_types_Colon_1,
            &[cand, ext_str],
        );
        if !candidate.has_trailing_directory_separator() {
            let parent_of_candidate = candidate.directory();
            if !self.resolver.fs.directory_exists(&parent_of_candidate) {
                let dir = parent_of_candidate.as_string().to_string();
                self.trace(
                    &tsc_diagnostics::Directory_0_does_not_exist_skipping_all_lookups_in_it,
                    &[dir],
                );
                return None;
            }
            if let Some(mut resolved_from_file) = self.load_module_from_file(extensions, candidate)
            {
                if consider_package_json {
                    let package_directory =
                        node_module_package_root_for_file(&resolved_from_file.path);
                    if !package_directory.is_empty() {
                        let pd = self.package_directory(package_directory);
                        let package_info = self.get_package_json_info(&pd);
                        resolved_from_file.package_id =
                            self.get_package_id(&resolved_from_file.path, &package_info);
                    }
                }
                return Some(resolved_from_file);
            }
        }
        if !self
            .resolver
            .fs
            .directory_exists(&candidate.as_directory_path())
        {
            let cand = candidate.as_string();
            self.trace(
                &tsc_diagnostics::Directory_0_does_not_exist_skipping_all_lookups_in_it,
                &[cand],
            );
            return None;
        }
        // esm mode relative imports shouldn't do any directory lookups (either inside `package.json`
        // files or implicit `index.js`es). This is a notable departure from cjs norms, where `./foo/pkg`
        // could have been redirected by `./foo/pkg/package.json` to an arbitrary location!
        if !self.esm_mode {
            return self.load_node_module_from_directory(
                extensions,
                candidate,
                consider_package_json,
            );
        }
        None
    }

    /// `func (r *resolutionState) loadModuleFromFile(extensions extensions, candidate resolutionCandidate) *resolved`
    fn load_module_from_file(
        &mut self,
        extensions: Extensions,
        candidate: &ResolutionCandidate,
    ) -> Option<Resolved> {
        // ./foo.js -> ./foo.ts
        let resolved_by_replacing_extension =
            self.load_module_from_file_no_implicit_extensions(extensions, candidate);
        if resolved_by_replacing_extension.is_some() {
            return resolved_by_replacing_extension;
        }

        // ./foo -> ./foo.ts
        if !self.esm_mode {
            let stem = tsc_tspath::rooted_file_path_from_path(candidate.path.clone()).as_stem();
            return self.try_adding_extensions(stem, &candidate.directory(), extensions, "");
        }

        None
    }

    /// `func (r *resolutionState) loadModuleFromFileNoImplicitExtensions(extensions extensions, candidate resolutionCandidate) *resolved`
    fn load_module_from_file_no_implicit_extensions(
        &mut self,
        extensions: Extensions,
        candidate: &ResolutionCandidate,
    ) -> Option<Resolved> {
        let base = candidate.path.base_name();
        if !base.contains('.') {
            // extensionless import, no lookups performed, since we don't support extensionless files
            return None;
        }
        let (extensionless, extension) = candidate.split_extension(&self.resolver.extra_extensions);
        let cand = candidate.as_string();
        self.trace(
            &tsc_diagnostics::File_name_0_has_a_1_extension_stripping_it,
            &[cand, extension.clone()],
        );
        self.try_adding_extensions(
            extensionless,
            &candidate.directory(),
            extensions,
            &extension,
        )
    }

    /// `func (r *resolutionState) tryAddingExtensions(extensionless tspath.FileNameStem, directory tspath.RootedDirectoryPath, extensions extensions, originalExtension string) *resolved`
    fn try_adding_extensions(
        &mut self,
        extensionless: FileNameStem,
        directory: &RootedDirectoryPath,
        extensions: Extensions,
        original_extension: &str,
    ) -> Option<Resolved> {
        if !directory.is_empty() && !self.resolver.fs.directory_exists(directory) {
            return None;
        }

        match original_extension {
            tsc_tspath::EXTENSION_MJS | tsc_tspath::EXTENSION_MTS | tsc_tspath::EXTENSION_DMTS => {
                if extensions.contains(EXTENSIONS_TYPE_SCRIPT) {
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_MTS,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_MTS
                            || original_extension == tsc_tspath::EXTENSION_DMTS,
                    ) {
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_DECLARATION) {
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_DMTS,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_MTS
                            || original_extension == tsc_tspath::EXTENSION_DMTS,
                    ) {
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_JAVA_SCRIPT) {
                    if let Some(resolved) =
                        self.try_extension(tsc_tspath::EXTENSION_MJS, &extensionless, false)
                    {
                        return Some(resolved);
                    }
                }
                None
            }
            tsc_tspath::EXTENSION_CJS | tsc_tspath::EXTENSION_CTS | tsc_tspath::EXTENSION_DCTS => {
                if extensions.contains(EXTENSIONS_TYPE_SCRIPT) {
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_CTS,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_CTS
                            || original_extension == tsc_tspath::EXTENSION_DCTS,
                    ) {
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_DECLARATION) {
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_DCTS,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_CTS
                            || original_extension == tsc_tspath::EXTENSION_DCTS,
                    ) {
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_JAVA_SCRIPT) {
                    if let Some(resolved) =
                        self.try_extension(tsc_tspath::EXTENSION_CJS, &extensionless, false)
                    {
                        return Some(resolved);
                    }
                }
                None
            }
            tsc_tspath::EXTENSION_JSON => {
                if extensions.contains(EXTENSIONS_DECLARATION) {
                    if let Some(resolved) = self.try_extension(".d.json.ts", &extensionless, false)
                    {
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_JSON) {
                    if let Some(resolved) =
                        self.try_extension(tsc_tspath::EXTENSION_JSON, &extensionless, false)
                    {
                        return Some(resolved);
                    }
                }
                None
            }
            tsc_tspath::EXTENSION_TSX | tsc_tspath::EXTENSION_JSX => {
                // basically idendical to the ts/js case below, but prefers matching tsx and jsx files exactly before falling back to the ts or js file path
                // (historically, we disallow having both a a.ts and a.tsx file in the same compilation, since their outputs clash)
                // TODO: We should probably error if `"./a.tsx"` resolved to `"./a.ts"`, right?
                if extensions.contains(EXTENSIONS_TYPE_SCRIPT) {
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_TSX,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_TSX,
                    ) {
                        return Some(resolved);
                    }
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_TS,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_TSX,
                    ) {
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_DECLARATION) {
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_DTS,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_TSX,
                    ) {
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_JAVA_SCRIPT) {
                    if let Some(resolved) =
                        self.try_extension(tsc_tspath::EXTENSION_JSX, &extensionless, false)
                    {
                        return Some(resolved);
                    }
                    if let Some(resolved) =
                        self.try_extension(tsc_tspath::EXTENSION_JS, &extensionless, false)
                    {
                        return Some(resolved);
                    }
                }
                None
            }
            tsc_tspath::EXTENSION_TS
            | tsc_tspath::EXTENSION_DTS
            | tsc_tspath::EXTENSION_JS
            | "" => {
                if extensions.contains(EXTENSIONS_TYPE_SCRIPT) {
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_TS,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_TS
                            || original_extension == tsc_tspath::EXTENSION_DTS,
                    ) {
                        return Some(resolved);
                    }
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_TSX,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_TS
                            || original_extension == tsc_tspath::EXTENSION_DTS,
                    ) {
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_DECLARATION) {
                    if let Some(resolved) = self.try_extension(
                        tsc_tspath::EXTENSION_DTS,
                        &extensionless,
                        original_extension == tsc_tspath::EXTENSION_TS
                            || original_extension == tsc_tspath::EXTENSION_DTS,
                    ) {
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_JAVA_SCRIPT) {
                    if let Some(resolved) =
                        self.try_extension(tsc_tspath::EXTENSION_JS, &extensionless, false)
                    {
                        return Some(resolved);
                    }
                    if let Some(resolved) =
                        self.try_extension(tsc_tspath::EXTENSION_JSX, &extensionless, false)
                    {
                        return Some(resolved);
                    }
                }
                if self.is_config_lookup {
                    if let Some(resolved) =
                        self.try_extension(tsc_tspath::EXTENSION_JSON, &extensionless, false)
                    {
                        return Some(resolved);
                    }
                }
                None
            }
            _ => {
                if self
                    .resolver
                    .extra_extensions
                    .iter()
                    .any(|e| e == original_extension)
                {
                    // A fully specified import of an extraExtension resolves directly to the file.
                    if let Some(mut resolved) =
                        self.try_extension(original_extension, &extensionless, false)
                    {
                        resolved.resolved_using_extra_extensions = true;
                        return Some(resolved);
                    }
                }
                if extensions.contains(EXTENSIONS_DECLARATION)
                    && !extensionless
                        .append_suffix(original_extension)
                        .is_declaration_file()
                {
                    if let Some(resolved) = self.try_extension(
                        &format!(".d{original_extension}.ts"),
                        &extensionless,
                        false,
                    ) {
                        return Some(resolved);
                    }
                }
                None
            }
        }
    }

    /// `func (r *resolutionState) tryExtension(extension string, extensionless tspath.FileNameStem, resolvedUsingTsExtension bool) *resolved`
    fn try_extension(
        &mut self,
        extension: &str,
        extensionless: &FileNameStem,
        resolved_using_ts_extension: bool,
    ) -> Option<Resolved> {
        let file_name =
            resolution_candidate_from_file_name(&extensionless.append_suffix(extension));
        if let Some(path) = self.try_file(&file_name) {
            return Some(Resolved {
                path,
                extension: extension.to_string(),
                resolved_using_ts_extension: !self.candidate_ending_is_from_config
                    && resolved_using_ts_extension,
                ..Resolved::default()
            });
        }
        None
    }

    /// `func (r *resolutionState) tryFile(fileName resolutionCandidate) (tspath.RootedFilePath, bool)`
    fn try_file(&mut self, file_name: &ResolutionCandidate) -> Option<RootedFilePath> {
        if file_name.directory_only {
            return None;
        }
        let module_suffixes = self
            .compiler_options
            .module_suffixes
            .clone()
            .unwrap_or_default();
        if module_suffixes.is_empty() {
            let candidate = tsc_tspath::rooted_file_path_from_path(file_name.path.clone());
            if self.try_file_lookup(&candidate) {
                return Some(candidate);
            }
            return None;
        }

        let ext = tsc_tspath::rooted_file_path_from_path(file_name.path.clone())
            .extension()
            .to_string();
        let file_name_no_extension = file_name.remove_extension(&ext);
        for suffix in &module_suffixes {
            let path = file_name_no_extension.append_suffix(&format!("{suffix}{ext}"));
            if self.try_file_lookup(&path) {
                return Some(path);
            }
        }
        None
    }

    /// `func (r *resolutionState) tryFileLookup(fileName tspath.RootedFilePath) bool`
    fn try_file_lookup(&mut self, file_name: &RootedFilePath) -> bool {
        if self.resolver.fs.file_exists(file_name) {
            let f = file_name.as_string().to_string();
            self.trace(
                &tsc_diagnostics::File_0_exists_use_it_as_a_name_resolution_result,
                &[f],
            );
            true
        } else {
            let f = file_name.as_string().to_string();
            self.trace(&tsc_diagnostics::File_0_does_not_exist, &[f]);
            false
        }
    }

    /// `func (r *resolutionState) loadNodeModuleFromDirectory(extensions extensions, candidate resolutionCandidate, considerPackageJson bool) *resolved`
    fn load_node_module_from_directory(
        &mut self,
        extensions: Extensions,
        candidate: &ResolutionCandidate,
        consider_package_json: bool,
    ) -> Option<Resolved> {
        let candidate_directory = candidate.as_directory_path();
        let package_info = if consider_package_json {
            self.get_package_json_info(&self.package_directory(candidate_directory.clone()))
        } else {
            None
        };

        self.load_node_module_from_directory_worker(extensions, &candidate_directory, &package_info)
    }

    /// `func (r *resolutionState) loadNodeModuleFromDirectoryWorker(ext extensions, candidate tspath.RootedDirectoryPath, packageInfo *packagejson.InfoCacheEntry) *resolved`
    fn load_node_module_from_directory_worker(
        &mut self,
        ext: Extensions,
        candidate: &RootedDirectoryPath,
        package_info: &Option<Arc<InfoCacheEntry>>,
    ) -> Option<Resolved> {
        let mut package_file = ResolutionCandidate::default();
        let mut version_paths = VersionPaths::default();
        if package_json_exists(package_info) {
            let contents = package_json_contents(package_info).unwrap();
            {
                // PORT: `get_version_paths` requires a `'static` `TraceFunc`,
                // so the tracer is shared through `Rc<RefCell>` for the
                // duration of the call.
                let shared = std::rc::Rc::new(std::cell::RefCell::new(self.tracer.take()));
                let shared2 = std::rc::Rc::clone(&shared);
                let mut trace_func = move |m: &'static Message, args: &[String]| {
                    if let Some(t) = shared2.borrow_mut().as_mut() {
                        t.write(m, args);
                    }
                };
                version_paths = contents.get_version_paths(Some(&mut trace_func));
                self.tracer = shared.borrow_mut().take();
            }
            let case_sensitivity = self.resolver.fs.case_sensitivity();
            if case_sensitivity.compare_paths(
                &candidate.as_path(),
                &package_info
                    .as_ref()
                    .unwrap()
                    .package_directory
                    .as_directory_path()
                    .as_path(),
            ) == 0
            {
                if let Some(file) = self.get_package_file(ext, package_info.as_deref().unwrap()) {
                    package_file = file;
                }
            }
        }

        let mut loader = |r: &mut ResolutionState<'a>,
                          extensions: Extensions,
                          candidate: &ResolutionCandidate|
         -> Option<Resolved> {
            if let Some(from_file) = r.load_file_name_from_package_json_field(
                extensions,
                candidate,
                &package_file.as_string(),
            ) {
                return Some(from_file);
            }

            // Even if `extensions == extensionsDeclaration`, we can still look up a .ts file as a result of package.json "types"
            // !!! should we not set this before the filename lookup above?
            let mut expanded_extensions = extensions;
            if extensions == EXTENSIONS_DECLARATION {
                expanded_extensions = EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION;
            }

            // Disable `esmMode` for the resolution of the package path for CJS-mode packages (so the `main` field can omit extensions)
            let save_esm_mode = r.esm_mode;
            let save_candidate_ending_is_from_config = r.candidate_ending_is_from_config;
            r.candidate_ending_is_from_config = true;
            if package_json_exists(package_info)
                && package_json_contents(package_info).unwrap().type_.value != "module"
            {
                r.esm_mode = false;
            }
            let result = r.node_load_module_by_relative_name(
                expanded_extensions,
                candidate,
                false, /*considerPackageJson*/
            );
            r.esm_mode = save_esm_mode;
            r.candidate_ending_is_from_config = save_candidate_ending_is_from_config;
            result
        };

        let index_path = if self.is_config_lookup {
            resolution_candidate_from_file_name(&candidate.resolve_file("tsconfig"))
        } else {
            resolution_candidate_from_file_name(&candidate.resolve_file("index"))
        };

        if version_paths.exists()
            && (package_file.path.is_empty()
                || CaseSensitivity::CaseInsensitive.contains_path(candidate, &package_file.path))
        {
            let module_path = if !package_file.path.is_empty() {
                package_file.path.clone()
            } else {
                index_path.path.clone()
            };
            let Some(relative_module_path) =
                CaseSensitivity::CaseInsensitive.relative_path_from_path(candidate, &module_path)
            else {
                panic!("package module path must have the same root as its candidate directory");
            };
            let mut module_name = relative_module_path.as_string().to_string();
            if tsc_tspath::is_encoded_dynamic_file_name(candidate.as_string()) {
                module_name = tsc_tspath::decode_dynamic_uri_path(&module_name).into_owned();
            }
            let vv = version_paths.version.clone();
            let cv = tsc_core::version::version().to_string();
            self.trace(
                &tsc_diagnostics::X_package_json_has_a_typesVersions_entry_0_that_matches_compiler_version_1_looking_for_a_pattern_to_match_module_name_2,
                &[vv, cv, module_name.clone()],
            );
            let path_patterns = try_parse_patterns(version_paths.get_paths());
            if let Some(paths_map) = version_paths.get_paths() {
                if let Some(result) = self.try_load_module_using_paths(
                    ext,
                    &module_name,
                    candidate,
                    paths_map,
                    &path_patterns,
                    &mut loader,
                ) {
                    if !result.package_id.name.is_empty() {
                        // !!! are these asserts really necessary?
                        panic!("expected packageId to be empty");
                    }
                    return Some(result);
                }
            }
        }

        if !package_file.path.is_empty() {
            if let Some(package_file_result) = loader(self, ext, &package_file) {
                if !package_file_result.package_id.name.is_empty() {
                    // !!! are these asserts really necessary?
                    panic!("expected packageId to be empty");
                }
                return Some(package_file_result);
            }
        }

        // ESM mode resolutions don't do package 'index' lookups
        if !self.esm_mode {
            if !self.resolver.fs.directory_exists(candidate) {
                return None;
            }
            return self.load_module_from_file(ext, &index_path);
        }
        None
    }

    // This function is only ever called with paths written in package.json files - never
    // module specifiers written in source files - and so it always allows the
    // candidate to end with a TS extension (but will also try substituting a JS extension for a TS extension).
    /// `func (r *resolutionState) loadFileNameFromPackageJSONField(extensions extensions, candidate resolutionCandidate, packageJSONValue string) *resolved`
    fn load_file_name_from_package_json_field(
        &mut self,
        extensions: Extensions,
        candidate: &ResolutionCandidate,
        package_json_value: &str,
    ) -> Option<Resolved> {
        if candidate.directory_only {
            return None;
        }
        let file_name = tsc_tspath::rooted_file_path_from_path(candidate.path.clone());
        if (extensions.contains(EXTENSIONS_TYPE_SCRIPT)
            && file_name.has_implementation_ts_file_extension())
            || (extensions.contains(EXTENSIONS_DECLARATION) && file_name.is_declaration_file())
        {
            if let Some(path) = self.try_file(candidate) {
                let extension = path.try_extract_ts_extension().to_string();
                // resolvedUsingTsExtension should be true when the pattern ends with * and the
                // candidate file ends in a TS extension. This means the * matched a TS extension
                // from the module specifier. For example:
                // - import "pkg/foo.ts" with pattern "./*" -> true
                // - import "pkg/foo.ts.omg" with pattern "./*.omg" -> true (star matched .ts)
                // - import "pkg/foo" with pattern "./*.ts" -> false (extension in pattern, not specifier)
                let resolved_using_ts_extension =
                    package_json_value.ends_with('*') && !extension.is_empty();
                return Some(Resolved {
                    path,
                    extension,
                    resolved_using_ts_extension,
                    ..Resolved::default()
                });
            }
            return None;
        }

        if self.is_config_lookup
            && extensions.contains(EXTENSIONS_JSON)
            && file_name.extension_is(tsc_tspath::EXTENSION_JSON)
        {
            if let Some(path) = self.try_file(candidate) {
                return Some(Resolved {
                    path,
                    extension: tsc_tspath::EXTENSION_JSON.to_string(),
                    ..Resolved::default()
                });
            }
        }

        self.load_module_from_file_no_implicit_extensions(extensions, candidate)
    }

    /// `func (r *resolutionState) getPackageFile(extensions extensions, packageInfo *packagejson.InfoCacheEntry) (resolutionCandidate, bool)`
    fn get_package_file(
        &mut self,
        extensions: Extensions,
        package_info: &InfoCacheEntry,
    ) -> Option<ResolutionCandidate> {
        if !package_info.exists() {
            return None;
        }
        let contents = package_info.contents.as_deref().unwrap();
        if self.is_config_lookup {
            return self.get_package_json_path_field(
                "tsconfig",
                &contents.ts_config,
                package_info.package_directory.as_directory_path(),
            );
        }
        if extensions.contains(EXTENSIONS_DECLARATION) {
            if let Some(package_file) = self.get_package_json_path_field(
                "typings",
                &contents.typings,
                package_info.package_directory.as_directory_path(),
            ) {
                return Some(package_file);
            }
            if let Some(package_file) = self.get_package_json_path_field(
                "types",
                &contents.types,
                package_info.package_directory.as_directory_path(),
            ) {
                return Some(package_file);
            }
        }
        if extensions.contains(EXTENSIONS_IMPLEMENTATION_FILES | EXTENSIONS_DECLARATION) {
            return self.get_package_json_path_field(
                "main",
                &contents.main,
                package_info.package_directory.as_directory_path(),
            );
        }
        None
    }

    /// `func (r *resolutionState) getPackageJsonInfo(packageDirectory packagejson.PackageDirectory) *packagejson.InfoCacheEntry`
    fn get_package_json_info(
        &mut self,
        package_directory: &PackageDirectory,
    ) -> Option<Arc<InfoCacheEntry>> {
        if let Some(existing) = self.resolver.package_json_info_cache.get(package_directory) {
            if existing.contents.is_some() {
                let f = package_directory.resolve_file("package.json");
                self.trace(
                    &tsc_diagnostics::File_0_exists_according_to_earlier_cached_lookups,
                    &[f.as_string().to_string()],
                );
                return Some(existing.with_package_directory(package_directory.clone()));
            } else {
                if existing.directory_exists && self.tracer.is_some() {
                    let f = package_directory.resolve_file("package.json");
                    self.trace(
                        &tsc_diagnostics::File_0_does_not_exist_according_to_earlier_cached_lookups,
                        &[f.as_string().to_string()],
                    );
                }
                return None;
            }
        }

        let package_json_file_name = package_directory.resolve_file("package.json");
        let directory_exists = self
            .resolver
            .fs
            .directory_exists(package_directory.as_directory_path());
        if directory_exists && self.resolver.fs.file_exists(&package_json_file_name) {
            // Ignore error
            let contents = self
                .resolver
                .fs
                .read_file(&package_json_file_name)
                .unwrap_or_default();
            // PORT: Go's `json.Unmarshal` leaves partially-populated `Fields`
            // on error; serde fails atomically, so a failed parse here yields
            // default fields.
            let (package_json_content, parseable) =
                match tsc_packagejson::parse(contents.as_bytes()) {
                    Ok(fields) => (fields, true),
                    Err(_) => (tsc_packagejson::Fields::default(), false),
                };
            let f = package_json_file_name.as_string().to_string();
            self.trace(&tsc_diagnostics::Found_package_json_at_0, &[f]);
            let mut package_json = PackageJson::default();
            package_json.fields = package_json_content;
            package_json.parseable = parseable;
            let result = Arc::new(InfoCacheEntry {
                package_directory: package_directory.clone(),
                directory_exists: true,
                contents: Some(Arc::new(package_json)),
            });
            let result = self
                .resolver
                .package_json_info_cache
                .set(package_directory.clone(), result);
            return Some(result.with_package_directory(package_directory.clone()));
        } else {
            if directory_exists && self.tracer.is_some() {
                let f = package_json_file_name.as_string().to_string();
                self.trace(&tsc_diagnostics::File_0_does_not_exist, &[f]);
            }
            self.resolver.package_json_info_cache.set(
                package_directory.clone(),
                Arc::new(InfoCacheEntry {
                    package_directory: package_directory.clone(),
                    directory_exists,
                    contents: None,
                }),
            );
        }
        None
    }

    /// `func (r *resolutionState) packageDirectory(directory tspath.RootedDirectoryPath) packagejson.PackageDirectory`
    fn package_directory(&self, directory: RootedDirectoryPath) -> PackageDirectory {
        self.resolver
            .package_json_info_cache
            .package_directory(directory)
    }

    /// `func (r *resolutionState) getPackageId(resolvedFileName tspath.RootedFilePath, packageInfo *packagejson.InfoCacheEntry) PackageId`
    fn get_package_id(
        &mut self,
        resolved_file_name: &RootedFilePath,
        package_info: &Option<Arc<InfoCacheEntry>>,
    ) -> PackageId {
        if package_json_exists(package_info) {
            let package_info = package_info.as_deref().unwrap();
            let package_json_content = package_info.contents.as_deref().unwrap();
            if let Some(name) = package_json_content.name.get_value() {
                if let Some(version) = package_json_content.version.get_value() {
                    let mut sub_module_name = String::new();
                    if let Some(relative) = resolved_file_name
                        .relative_to(package_info.package_directory.as_directory_path())
                    {
                        sub_module_name = relative.as_string().to_string();
                    }
                    return PackageId {
                        name: name.clone(),
                        version: version.clone(),
                        sub_module_name,
                        peer_dependencies: self.read_package_json_peer_dependencies(package_info),
                    };
                }
            }
        }
        PackageId::default()
    }

    /// `func (r *resolutionState) readPackageJsonPeerDependencies(packageJsonInfo *packagejson.InfoCacheEntry) string`
    fn read_package_json_peer_dependencies(
        &mut self,
        package_json_info: &InfoCacheEntry,
    ) -> String {
        let peer_dependencies = package_json_info
            .contents
            .as_deref()
            .map(|c| c.peer_dependencies.clone())
            .unwrap_or_default();
        let ok = self.validate_package_json_field("peerDependencies", &peer_dependencies);
        if !ok || peer_dependencies.value.is_empty() {
            return String::new();
        }
        self.trace(
            &tsc_diagnostics::X_package_json_has_a_peerDependencies_field,
            &[] as &[String],
        );
        let package_directory = self.real_path(&tsc_tspath::rooted_file_path_from_path(
            package_json_info
                .package_directory
                .as_directory_path()
                .as_path(),
        ));
        let Some((_, node_modules)) = package_directory.split_at_last_component("node_modules")
        else {
            return String::new();
        };
        let mut names: Vec<&String> = peer_dependencies.value.keys().collect();
        names.sort();
        let mut builder = String::new();
        for name in names {
            let dir = node_modules.resolve_directory(&path_for_dynamic_resolution(
                &node_modules,
                name,
                true,
            ));
            let peer_package_json = self.get_package_json_info(&self.package_directory(dir));
            if package_json_exists(&peer_package_json) {
                let version = package_json_contents(&peer_package_json)
                    .unwrap()
                    .version
                    .value
                    .clone();
                builder.push('+');
                builder.push_str(name);
                builder.push('@');
                builder.push_str(&version);
                self.trace(
                    &tsc_diagnostics::Found_peerDependency_0_with_1_version,
                    &[name.clone(), version],
                );
            } else {
                self.trace(
                    &tsc_diagnostics::Failed_to_find_peerDependency_0,
                    &[name.clone()],
                );
            }
        }
        builder
    }

    /// `func (r *resolutionState) realPath(path tspath.RootedFilePath) tspath.RootedFilePath`
    fn real_path(&mut self, path: &RootedFilePath) -> RootedFilePath {
        let rp = self.resolver.fs.realpath(&path.as_path());
        if self.tracer.is_some() {
            self.trace(
                &tsc_diagnostics::Resolving_real_path_for_0_result_1,
                &[path.as_string().to_string(), rp.as_string().to_string()],
            );
        }
        tsc_tspath::rooted_file_path_from_path(rp)
    }

    /// `func (r *resolutionState) validatePackageJSONField(fieldName string, field packagejson.TypeValidatedField) bool`
    fn validate_package_json_field(
        &mut self,
        field_name: &str,
        field: &dyn TypeValidatedField,
    ) -> bool {
        if field.is_present() {
            if field.is_valid() {
                return true;
            }
            let args = [
                field_name.to_string(),
                field.expected_json_type().to_string(),
                field.actual_json_type().to_string(),
            ];
            self.trace(
                &tsc_diagnostics::Expected_type_of_0_field_in_package_json_to_be_1_got_2,
                &args,
            );
            return false;
        }
        self.trace(
            &tsc_diagnostics::X_package_json_does_not_have_a_0_field,
            &[field_name.to_string()],
        );
        false
    }

    /// `func (r *resolutionState) getPackageJSONPathField(fieldName string, field *packagejson.Expected[string], directory tspath.RootedDirectoryPath) (resolutionCandidate, bool)`
    fn get_package_json_path_field(
        &mut self,
        field_name: &str,
        field: &tsc_packagejson::Expected<String>,
        directory: &RootedDirectoryPath,
    ) -> Option<ResolutionCandidate> {
        if !self.validate_package_json_field(field_name, field) {
            return None;
        }
        if field.value.is_empty() {
            let name = field_name.to_string();
            self.trace(
                &tsc_diagnostics::X_package_json_had_a_falsy_0_field,
                &[name],
            );
            return None;
        }
        let path = resolution_candidate_from_directory_path(directory, &field.value);
        let name = field_name.to_string();
        let value = field.value.clone();
        let path_str = path.as_string();
        self.trace(
            &tsc_diagnostics::X_package_json_has_0_field_1_that_references_2,
            &[name, value, path_str],
        );
        Some(path)
    }

    /// `func (r *resolutionState) conditionMatches(condition string) bool`
    fn condition_matches(&self, condition: &str) -> bool {
        if condition == "default" || self.conditions.iter().any(|c| c == condition) {
            return true;
        }
        if !self.conditions.iter().any(|c| c == "types") {
            return false; // only apply versioned types conditions if the types condition is applied
        }
        is_applicable_versioned_types_key(condition)
    }

    /// `func (r *resolutionState) loadEntrypointsFromExportMap(...) []*ResolvedEntrypoint`
    fn load_entrypoints_from_export_map(
        &mut self,
        package_json: &InfoCacheEntry,
        package_name: &str,
        exports: &ExportsOrImports,
    ) -> Vec<ResolvedEntrypoint> {
        let mut entrypoints: Vec<ResolvedEntrypoint> = Vec::new();

        match exports.type_ {
            JSONValueType::Array => {
                for element in exports.as_array() {
                    self.load_entrypoints_from_target_exports(
                        ".",
                        None,
                        None,
                        element,
                        package_json,
                        package_name,
                        &mut entrypoints,
                    );
                }
            }
            JSONValueType::Object => {
                if exports.is_subpaths() {
                    for (subpath, export) in exports.as_object().entries() {
                        self.load_entrypoints_from_target_exports(
                            subpath,
                            None,
                            None,
                            export,
                            package_json,
                            package_name,
                            &mut entrypoints,
                        );
                    }
                } else {
                    self.load_entrypoints_from_target_exports(
                        ".",
                        None,
                        None,
                        exports,
                        package_json,
                        package_name,
                        &mut entrypoints,
                    );
                }
            }
            _ => {
                self.load_entrypoints_from_target_exports(
                    ".",
                    None,
                    None,
                    exports,
                    package_json,
                    package_name,
                    &mut entrypoints,
                );
            }
        }

        entrypoints
    }

    /// `loadEntrypointsFromTargetExports` closure inside `loadEntrypointsFromExportMap`.
    ///
    /// PORT: a recursive method instead of a `var f func(...)` self-referencing
    /// closure; `entrypoints` accumulates instead of closing over the slice.
    fn load_entrypoints_from_target_exports(
        &mut self,
        subpath: &str,
        include_conditions: Option<&Set<String>>,
        exclude_conditions: Option<&Set<String>>,
        exports: &ExportsOrImports,
        package_json: &InfoCacheEntry,
        package_name: &str,
        entrypoints: &mut Vec<ResolvedEntrypoint>,
    ) {
        if exports.type_ == JSONValueType::String && exports.as_string().starts_with("./") {
            let exports_str = exports.as_string().to_string();
            if exports_str.contains('*') {
                if exports_str.find('*') != exports_str.rfind('*') {
                    return;
                }
                let dynamic_package = tsc_tspath::is_encoded_dynamic_file_name(
                    package_json
                        .package_directory
                        .as_directory_path()
                        .as_string(),
                );
                let mut include_patterns = vec![
                    tsc_tspath::change_full_extension(&exports_str.replacen('*', "**/*", 1), ".*")
                        .into_owned(),
                ];
                if dynamic_package {
                    include_patterns = vec!["**/*".to_string()];
                }
                let pattern_path = exports_str.trim_start_matches("./");
                let (leading_slice, trailing_slice) =
                    pattern_path.split_once('*').unwrap_or((pattern_path, ""));
                let files = vfsmatch::read_directory(
                    &self.resolver.fs,
                    package_json.package_directory.as_directory_path(),
                    &self.extensions.array(),
                    &[] as &[String],
                    &include_patterns,
                    vfsmatch::UNLIMITED_DEPTH,
                );
                for file in files {
                    let Some(relative_file) = self
                        .resolver
                        .fs
                        .case_sensitivity()
                        .relative_path_from_directory(
                            package_json.package_directory.as_directory_path(),
                            &file,
                        )
                    else {
                        continue;
                    };
                    let mut logical_file = relative_file.as_string().to_string();
                    if dynamic_package {
                        logical_file =
                            tsc_tspath::decode_dynamic_uri_path(&logical_file).into_owned();
                    }
                    let Some(matched_star) = self.get_matched_star_for_pattern_entrypoint(
                        &logical_file,
                        leading_slice,
                        trailing_slice,
                        dynamic_package,
                    ) else {
                        continue;
                    };
                    let matched_star = if dynamic_package {
                        tsc_tspath::encode_dynamic_logical_module_specifier(&matched_star)
                            .into_owned()
                    } else {
                        matched_star
                    };
                    let resolved_subpath = subpath.replacen('*', &matched_star, 1);
                    let resolved_subpath = resolved_subpath.trim_start_matches("./").to_string();
                    if resolved_subpath.is_empty() {
                        continue;
                    }
                    let module_specifier = tsc_tspath::to_module_specifier(&format!(
                        "{package_name}/{resolved_subpath}"
                    ));
                    let ending = if exports_str.ends_with('*') {
                        Ending::ExtensionChangeable
                    } else {
                        Ending::Fixed
                    };
                    entrypoints.push(self.resolver.create_resolved_entrypoint_handling_symlink(
                        file,
                        module_specifier,
                        include_conditions.cloned(),
                        exclude_conditions.cloned(),
                        ending,
                    ));
                }
            } else {
                let parts_after_first = &tsc_tspath::get_path_components(&exports_str)[2..];
                if parts_after_first.iter().any(|p| p == "..")
                    || parts_after_first.iter().any(|p| p == ".")
                    || parts_after_first.iter().any(|p| p == "node_modules")
                {
                    return;
                }
                let resolved_target = resolution_candidate_from_directory_path(
                    package_json.package_directory.as_directory_path(),
                    &exports_str,
                );
                if let Some(result) = self.load_file_name_from_package_json_field(
                    self.extensions,
                    &resolved_target,
                    &exports_str,
                ) {
                    if result.is_resolved() {
                        let ending = if exports_str.ends_with('*') {
                            Ending::ExtensionChangeable
                        } else {
                            Ending::Fixed
                        };
                        entrypoints.push(
                            self.resolver.create_resolved_entrypoint_handling_symlink(
                                result.path,
                                tsc_tspath::to_module_specifier(&tsc_tspath::resolve_path(
                                    package_name,
                                    &[subpath],
                                )),
                                include_conditions.cloned(),
                                exclude_conditions.cloned(),
                                ending,
                            ),
                        );
                    }
                }
            }
        } else if exports.type_ == JSONValueType::Array {
            for element in exports.as_array() {
                self.load_entrypoints_from_target_exports(
                    subpath,
                    include_conditions,
                    exclude_conditions,
                    element,
                    package_json,
                    package_name,
                    entrypoints,
                );
            }
        } else if exports.type_ == JSONValueType::Object {
            let mut prev_conditions: Vec<String> = Vec::new();
            let mut exclude_conditions = exclude_conditions.cloned();
            for (condition, export) in exports.as_object().entries() {
                if exclude_conditions
                    .as_ref()
                    .is_some_and(|e| e.has(condition))
                {
                    continue;
                }

                let condition_always_matches = condition == "default"
                    || condition == "types"
                    || is_applicable_versioned_types_key(condition);
                let mut new_include_conditions = include_conditions.cloned();
                if !condition_always_matches {
                    new_include_conditions = include_conditions.cloned();
                    let mut new_exclude = exclude_conditions.clone();
                    if new_include_conditions.is_none() {
                        new_include_conditions = Some(Set::new());
                    }
                    new_include_conditions
                        .as_mut()
                        .unwrap()
                        .add(condition.clone());
                    for prev_condition in &prev_conditions {
                        if new_exclude.is_none() {
                            new_exclude = Some(Set::new());
                        }
                        new_exclude.as_mut().unwrap().add(prev_condition.clone());
                    }
                    exclude_conditions = new_exclude;
                }

                prev_conditions.push(condition.clone());
                self.load_entrypoints_from_target_exports(
                    subpath,
                    new_include_conditions.as_ref(),
                    exclude_conditions.as_ref(),
                    export,
                    package_json,
                    package_name,
                    entrypoints,
                );
                if condition_always_matches {
                    break;
                }
            }
        }
    }

    /// `func (r *resolutionState) getMatchedStarForPatternEntrypoint(...) (string, bool)`
    fn get_matched_star_for_pattern_entrypoint(
        &self,
        file: &str,
        leading_slice: &str,
        trailing_slice: &str,
        force_case_sensitive: bool,
    ) -> Option<String> {
        let case_sensitivity = self.resolver.fs.case_sensitivity();
        let is_case_sensitive = force_case_sensitive || case_sensitivity.is_case_sensitive();
        if tsc_stringutil::has_prefix_and_suffix_without_overlap(
            file.as_bytes(),
            leading_slice.as_bytes(),
            trailing_slice.as_bytes(),
            is_case_sensitive,
        ) {
            return Some(file[leading_slice.len()..file.len() - trailing_slice.len()].to_string());
        }

        let js_extension = try_get_js_extension_for_file(file, &self.compiler_options);
        if !js_extension.is_empty() {
            let swapped = tsc_tspath::change_full_extension(file, js_extension).into_owned();
            if tsc_stringutil::has_prefix_and_suffix_without_overlap(
                swapped.as_bytes(),
                leading_slice.as_bytes(),
                trailing_slice.as_bytes(),
                is_case_sensitive,
            ) {
                return Some(
                    swapped[leading_slice.len()..swapped.len() - trailing_slice.len()].to_string(),
                );
            }
        }

        None
    }
}

/// `func GetConditions(options *core.CompilerOptions, resolutionMode core.ResolutionMode) []string`
pub fn get_conditions(options: &CompilerOptions, resolution_mode: ResolutionMode) -> Vec<String> {
    let module_resolution = options.get_module_resolution_kind();
    let mut resolution_mode = resolution_mode;
    if resolution_mode == RESOLUTION_MODE_NONE && module_resolution == ModuleResolutionKind::Bundler
    {
        resolution_mode = ModuleKind::ESNext;
    }
    let mut conditions =
        Vec::with_capacity(3 + options.custom_conditions.as_deref().map_or(0, |c| c.len()));
    if resolution_mode == ModuleKind::ESNext {
        conditions.push("import".to_string());
    } else {
        conditions.push("require".to_string());
    }

    if options.no_dts_resolution != TS_TRUE {
        conditions.push("types".to_string());
    }
    if module_resolution != ModuleResolutionKind::Bundler {
        conditions.push("node".to_string());
    }
    let custom = options.custom_conditions.clone().unwrap_or_default();
    tsc_core::core::concatenate(&conditions, &custom).into_owned()
}

/// `func getNodeResolutionFeatures(options *core.CompilerOptions) NodeResolutionFeatures`
fn get_node_resolution_features(options: &CompilerOptions) -> NodeResolutionFeatures {
    let mut features = NodeResolutionFeatures::NONE;

    match options.get_module_resolution_kind() {
        ModuleResolutionKind::Node16 => features = NodeResolutionFeatures::NODE16_DEFAULT,
        ModuleResolutionKind::NodeNext => features = NodeResolutionFeatures::NODE_NEXT_DEFAULT,
        ModuleResolutionKind::Bundler => features = NodeResolutionFeatures::BUNDLER_DEFAULT,
        _ => {}
    }
    if options.resolve_package_json_exports == TS_TRUE {
        features |= NodeResolutionFeatures::EXPORTS;
    } else if options.resolve_package_json_exports == tsc_core::tristate::TS_FALSE {
        features = NodeResolutionFeatures(features.0 & !NodeResolutionFeatures::EXPORTS.0);
    }
    if options.resolve_package_json_imports == TS_TRUE {
        features |= NodeResolutionFeatures::IMPORTS;
    } else if options.resolve_package_json_imports == tsc_core::tristate::TS_FALSE {
        features = NodeResolutionFeatures(features.0 & !NodeResolutionFeatures::IMPORTS.0);
    }
    features
}

/// `func moveToNextDirectorySeparatorIfAvailable(path string, prevSeparatorIndex int, isFolder bool) int`
pub(crate) fn move_to_next_directory_separator_if_available(
    path: &str,
    prev_separator_index: usize,
    is_folder: bool,
) -> usize {
    let offset = prev_separator_index + 1;
    let mut next_separator_index = None;
    if offset <= path.len() {
        next_separator_index = path[offset..].find('/');
    }
    match next_separator_index {
        None => {
            if is_folder {
                return path.len();
            }
            prev_separator_index
        }
        Some(next) => next + offset,
    }
}

/// `type ParsedPatterns struct`
#[derive(Default)]
pub struct ParsedPatterns {
    pub(crate) matchable_string_set: Set<String>,
    pub(crate) patterns: Vec<tsc_core::pattern::Pattern>,
}

/// `func (r *DefaultResolver) getParsedPatternsForPaths(compilerOptions *core.CompilerOptions) *ParsedPatterns`
impl DefaultResolver {
    pub(crate) fn get_parsed_patterns_for_paths(
        &self,
        compiler_options: &CompilerOptions,
    ) -> Arc<ParsedPatterns> {
        self.parsed_patterns_for_paths
            .get(compiler_options.paths.as_ref())
    }
}

/// `func TryParsePatterns(pathMappings *collections.OrderedMap[string, []string]) *ParsedPatterns`
///
/// PORT: `pathMappings` is `Option<&OrderedMap>` — Go's nil pointer maps to `None`.
pub fn try_parse_patterns<V>(path_mappings: Option<&OrderedMap<String, V>>) -> ParsedPatterns {
    let mut parsed = ParsedPatterns::default();
    let Some(path_mappings) = path_mappings else {
        return parsed;
    };
    for path in path_mappings.keys() {
        let pattern = try_parse_pattern(path);
        if pattern.is_valid() {
            if pattern.star_index == -1 {
                parsed.matchable_string_set.add(path.clone());
            } else {
                parsed.patterns.push(pattern);
            }
        }
    }
    parsed
}

/// `func MatchPatternOrExact(patterns *ParsedPatterns, candidate string) core.Pattern`
pub fn match_pattern_or_exact(
    patterns: &ParsedPatterns,
    candidate: &str,
) -> tsc_core::pattern::Pattern {
    if patterns.matchable_string_set.has(candidate) {
        return tsc_core::pattern::Pattern {
            text: candidate.to_string(),
            star_index: -1,
        };
    }
    if patterns.patterns.is_empty() {
        return tsc_core::pattern::Pattern::default();
    }
    tsc_core::pattern::find_best_pattern_match(&patterns.patterns, |p| p.clone(), candidate)
        .unwrap_or_default()
}

// If you import from "." inside a containing directory "/foo", the result of `tspath.NormalizePath`
// would be "/foo", but this loses the information that `foo` is a directory and we intended
// to look inside of it. The Node CommonJS resolution algorithm doesn't call this out
// (https://nodejs.org/api/modules.html#all-together), but it seems that module paths ending
// in `.` are actually normalized to `./` before proceeding with the resolution algorithm.
/// `func normalizePathForCJSResolution(containingDirectory tspath.RootedDirectoryPath, moduleName string) resolutionCandidate`
fn normalize_path_for_cjs_resolution(
    containing_directory: &RootedDirectoryPath,
    module_name: &str,
) -> ResolutionCandidate {
    let trimmed_module_name = module_name.trim_end_matches(['/', '\\']);
    let last_separator = trimmed_module_name.rfind(['/', '\\']);
    let last_part = &trimmed_module_name[last_separator.map_or(0, |i| i + 1)..];
    let mut candidate = resolution_candidate_from_directory_path(containing_directory, module_name);
    let directory_only = trimmed_module_name.len() != module_name.len()
        || last_part == "."
        || last_part == ".."
        || tsc_tspath::has_trailing_directory_separator(candidate.path.as_string());
    candidate.directory_only = directory_only;
    candidate
}

/// `func matchesPatternWithTrailer(target string, name string) bool`
fn matches_pattern_with_trailer(target: &str, name: &str) -> bool {
    if target.ends_with('*') {
        return false;
    }
    let Some((before, after)) = target.split_once('*') else {
        return false;
    };
    name.starts_with(before) && name.ends_with(after)
}

/// True if `extension` is one of the supported `extensions`.
///
/// `func extensionIsOk(extensions extensions, extension string) bool`
fn extension_is_ok(extensions: Extensions, extension: &str) -> bool {
    (extensions.contains(EXTENSIONS_JAVA_SCRIPT)
        && (extension == tsc_tspath::EXTENSION_JS
            || extension == tsc_tspath::EXTENSION_JSX
            || extension == tsc_tspath::EXTENSION_MJS
            || extension == tsc_tspath::EXTENSION_CJS))
        || (extensions.contains(EXTENSIONS_TYPE_SCRIPT)
            && (extension == tsc_tspath::EXTENSION_TS
                || extension == tsc_tspath::EXTENSION_TSX
                || extension == tsc_tspath::EXTENSION_MTS
                || extension == tsc_tspath::EXTENSION_CTS))
        || (extensions.contains(EXTENSIONS_DECLARATION)
            && (extension == tsc_tspath::EXTENSION_DTS
                || extension == tsc_tspath::EXTENSION_DMTS
                || extension == tsc_tspath::EXTENSION_DCTS))
        || (extensions.contains(EXTENSIONS_JSON) && extension == tsc_tspath::EXTENSION_JSON)
}

/// `packageInfo.Exists()` / `packageInfo.Contents` helpers — Go's
/// `*InfoCacheEntry` nil-safe methods against `Option<Arc<InfoCacheEntry>>`.
pub(crate) fn package_json_exists(info: &Option<Arc<InfoCacheEntry>>) -> bool {
    info.as_ref().is_some_and(|i| i.exists())
}

/// `packageInfo.Contents` — `None` when the entry or its contents are absent.
pub(crate) fn package_json_contents(info: &Option<Arc<InfoCacheEntry>>) -> Option<&PackageJson> {
    info.as_deref()?.contents.as_deref()
}

/// `[]string` view of a path-mapping value for `try_load_module_using_paths`.
///
/// PORT: `CompilerOptions.paths` values are `Option<Vec<String>>` (Go may
/// have a nil slice under a key — `GetOrZero` yields an empty iteration in
/// both cases), while `typesVersions` mappings are plain `Vec<String>`.
pub(crate) trait PathSubstitutions {
    fn substitutions(&self) -> &[String];
}

impl PathSubstitutions for Vec<String> {
    fn substitutions(&self) -> &[String] {
        self
    }
}

impl PathSubstitutions for Option<Vec<String>> {
    fn substitutions(&self) -> &[String] {
        self.as_deref().unwrap_or(&[])
    }
}

/// `type fileSystemResolutionHost struct`
struct FileSystemResolutionHost {
    fs: Arc<dyn Vfs>,
    current_directory: RootedDirectoryPath,
}

impl crate::types::ResolutionHost for FileSystemResolutionHost {
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }
    fn get_current_directory(&self) -> RootedDirectoryPath {
        self.current_directory.clone()
    }
}

/// `func ResolveConfig(moduleName string, containingFile tspath.RootedFilePath, fs vfs.FS) *ResolvedModule`
pub fn resolve_config(
    module_name: &str,
    containing_file: &RootedFilePath,
    fs: Arc<dyn Vfs>,
) -> ResolvedModule {
    let resolver = DefaultResolver::new(ResolverOptions {
        host: Arc::new(FileSystemResolutionHost {
            fs: fs.clone(),
            current_directory: containing_file.directory(),
        }),
        compiler_options: Arc::new(CompilerOptions {
            module_resolution: ModuleResolutionKind::NodeNext,
            ..CompilerOptions::default()
        }),
        typings_location: RootedDirectoryPath::default(),
        project_name: String::new(),
        extra_extensions: Vec::new(),
        package_json_cache: None,
    });
    resolver.resolve_config(module_name, containing_file)
}

/// `func GetAutomaticTypeDirectiveNames(options *core.CompilerOptions, baseDirectory tspath.RootedDirectoryPath, fs vfs.FS) []string`
pub fn get_automatic_type_directive_names(
    options: &CompilerOptions,
    base_directory: RootedDirectoryPath,
    fs: &Arc<dyn Vfs>,
) -> Vec<String> {
    if !options.uses_wildcard_types() {
        if let Some(types) = &options.types {
            return types.clone();
        }
        return Vec::new();
    }

    // Walk the primary type lookup locations
    let mut wildcard_matches: Vec<String> = Vec::new();
    let (type_roots, _) = options.get_effective_type_roots(&base_directory);
    for root in type_roots.unwrap_or_default() {
        if fs.directory_exists(&root) {
            for type_directive_path in fs.get_accessible_entries(&root).directories {
                let type_directive_directory = root.resolve_directory(&type_directive_path);
                let package_json_path = type_directive_directory.resolve_file("package.json");
                let mut is_not_needed_package = false;
                if fs.file_exists(&package_json_path) {
                    let contents = fs.read_file(&package_json_path).unwrap_or_default();
                    let package_json_content =
                        tsc_packagejson::parse(contents.as_bytes()).unwrap_or_default();
                    // `types-publisher` sometimes creates packages with `"typings": null` for packages that don't provide their own types.
                    // See `createNotNeededPackageJSON` in the types-publisher` repo.
                    is_not_needed_package = package_json_content.typings.null;
                }
                if !is_not_needed_package {
                    let directory_path = type_directive_directory.as_path();
                    let base_file_name = directory_path.base_name();
                    if !base_file_name.starts_with('.') {
                        wildcard_matches.push(base_file_name.to_string());
                    }
                }
            }
        }
    }

    // Order potentially matters in program construction, so substitute
    // in the wildcard in the position it was specified in the types array
    let mut result: Vec<String> = Vec::new();
    for t in options.types.as_deref().unwrap_or(&[]) {
        if t == "*" {
            result.extend(wildcard_matches.iter().cloned());
        } else {
            result.push(t.clone());
        }
    }
    tsc_core::core::deduplicate(&result).into_owned()
}

/// `type Ending int`
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum Ending {
    /// EndingFixed indicates that the module specifier cannot be changed without changing its resolution.
    #[default]
    Fixed = 0,
    /// EndingExtensionChangeable indicates that the module specifier's extension portion was inferred from a
    /// file on disk, so an interchangeable one could be used instead (e.g. replacing .d.ts with .js).
    ExtensionChangeable,
    /// EndingChangeable indicates that the module specifier's file name and extension portion were inferred
    /// from a file on disk without being matched as part of an 'exports' pattern, so can be changed according
    /// to the importer's module resolution rules (e.g. an /index.d.ts may be dropped entirely in CommonJS settings).
    Changeable,
}

/// `type ResolvedEntrypoint struct`
///
/// PORT: `*collections.Set[string]` conditions become `Option<Set<String>>`;
/// `ModuleSpecifier` is `tspath.ModuleSpecifier`.
#[derive(Clone, Debug)]
pub struct ResolvedEntrypoint {
    /// OriginalFileName is the symlink path if the entrypoint was discovered at a symlink. Empty otherwise.
    pub original_file_name: RootedFilePath,
    /// ResolvedFileName is the real path to the entrypoint file.
    pub resolved_file_name: RootedFilePath,
    pub resolved_path: PathKey,
    pub module_specifier: tsc_tspath::ModuleSpecifier,
    /// Ending indicates whether the file name and extension portion of ModuleSpecifier is fixed or can be changed.
    pub ending: Ending,
    /// IncludeConditions are the conditions that a resolver must have to reach this entrypoint.
    pub include_conditions: Option<Set<String>>,
    /// ExcludeConditions are the conditions that a resolver must not have to reach this entrypoint.
    pub exclude_conditions: Option<Set<String>>,
}

impl ResolvedEntrypoint {
    /// `func (e *ResolvedEntrypoint) SymlinkOrRealpath() tspath.RootedFilePath`
    pub fn symlink_or_realpath(&self) -> RootedFilePath {
        if !self.original_file_name.is_empty() {
            return self.original_file_name.clone();
        }
        self.resolved_file_name.clone()
    }
}

impl DefaultResolver {
    /// `func (r *DefaultResolver) GetEntrypointsFromPackageJsonInfo(packageJson *packagejson.InfoCacheEntry, packageName string, enableDirectorySearch bool) []*ResolvedEntrypoint`
    pub fn get_entrypoints_from_package_json_info(
        &self,
        package_json: &InfoCacheEntry,
        package_name: &str,
        enable_directory_search: bool,
    ) -> Vec<ResolvedEntrypoint> {
        let extensions = EXTENSIONS_TYPE_SCRIPT | EXTENSIONS_DECLARATION;
        let features = NodeResolutionFeatures::ALL;
        let mut state = ResolutionState {
            resolver: self,
            extensions,
            features,
            compiler_options: self.compiler_options.clone(),
            ..ResolutionState::bare(self, self.compiler_options.clone())
        };
        let dynamic_package = tsc_tspath::is_encoded_dynamic_file_name(
            package_json
                .package_directory
                .as_directory_path()
                .as_string(),
        );
        let mut source_package_name = package_name.to_string();
        if dynamic_package {
            source_package_name =
                tsc_tspath::dynamic_uri_path_to_module_specifier(package_name).into_owned();
        }
        if package_json.exists()
            && package_json
                .contents
                .as_deref()
                .is_some_and(|c| c.exports.is_present())
        {
            let contents = package_json.contents.as_deref().unwrap();
            let entrypoints = state.load_entrypoints_from_export_map(
                package_json,
                &source_package_name,
                &contents.exports,
            );
            return entrypoints;
        }

        let mut result: Vec<ResolvedEntrypoint> = Vec::new();
        let main_resolution = state.load_node_module_from_directory_worker(
            extensions,
            package_json.package_directory.as_directory_path(),
            &Some(Arc::new(package_json.clone())),
        );

        if main_resolution.as_ref().is_some_and(|r| r.is_resolved()) {
            result.push(self.create_resolved_entrypoint_handling_symlink(
                main_resolution.as_ref().unwrap().path.clone(),
                tsc_tspath::to_module_specifier(&source_package_name),
                None,
                None,
                Ending::Fixed,
            ));
        }

        if enable_directory_search {
            let other_files = vfsmatch::read_directory(
                &self.fs,
                package_json.package_directory.as_directory_path(),
                &extensions.array(),
                &["node_modules"],
                &["**/*"],
                vfsmatch::UNLIMITED_DEPTH,
            );

            let case_sensitivity = self.fs.case_sensitivity();
            for file in other_files {
                if main_resolution.as_ref().is_some_and(|r| r.is_resolved())
                    && case_sensitivity
                        .compare_file_paths(&file, &main_resolution.as_ref().unwrap().path)
                        == 0
                {
                    continue;
                }

                let Some(relative) = case_sensitivity.relative_path_from_directory(
                    package_json.package_directory.as_directory_path(),
                    &file,
                ) else {
                    continue;
                };
                let mut relative_specifier = relative.as_string().to_string();
                if dynamic_package {
                    relative_specifier =
                        tsc_tspath::dynamic_uri_path_to_module_specifier(&relative_specifier)
                            .into_owned();
                }
                result.push(self.create_resolved_entrypoint_handling_symlink(
                    file,
                    tsc_tspath::to_module_specifier(&format!(
                        "{source_package_name}/{relative_specifier}"
                    )),
                    None,
                    None,
                    Ending::Changeable,
                ));
            }
        }

        result
    }

    /// `func (r *DefaultResolver) createResolvedEntrypointHandlingSymlink(...) *ResolvedEntrypoint`
    fn create_resolved_entrypoint_handling_symlink(
        &self,
        file_name: RootedFilePath,
        module_specifier: tsc_tspath::ModuleSpecifier,
        include_conditions: Option<Set<String>>,
        exclude_conditions: Option<Set<String>>,
        ending: Ending,
    ) -> ResolvedEntrypoint {
        let mut original_file_name = RootedFilePath::default();
        let mut resolved_file_name = file_name.clone();
        let real_path = self.fs.realpath(&file_name.as_path());
        if real_path != file_name.as_path() {
            original_file_name = file_name.clone();
            resolved_file_name = tsc_tspath::rooted_file_path_from_path(real_path);
        }
        ResolvedEntrypoint {
            original_file_name,
            resolved_path: self
                .fs
                .case_sensitivity()
                .path_key(&resolved_file_name.as_path()),
            resolved_file_name,
            module_specifier,
            include_conditions,
            exclude_conditions,
            ending,
        }
    }
}

/// `func (r *DefaultResolver)` satisfies `Resolver`.
impl crate::types::Resolver for DefaultResolver {
    fn base_directory(&self) -> RootedDirectoryPath {
        self.base_directory()
    }
    fn resolve_module_name(
        &self,
        module_name: &str,
        containing_file: &RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>) {
        DefaultResolver::resolve_module_name(
            self,
            module_name,
            containing_file,
            resolution_mode,
            redirected_reference,
        )
    }
    fn resolve_module_name_from_directory(
        &self,
        module_name: &str,
        containing_directory: &RootedDirectoryPath,
        resolution_mode: ResolutionMode,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>) {
        DefaultResolver::resolve_module_name_from_directory(
            self,
            module_name,
            containing_directory,
            resolution_mode,
        )
    }
    fn resolve_type_reference_directive(
        &self,
        type_reference_directive_name: &str,
        containing_file: &RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (ResolvedTypeReferenceDirective, Vec<DiagAndArgs>) {
        DefaultResolver::resolve_type_reference_directive(
            self,
            type_reference_directive_name,
            containing_file,
            resolution_mode,
            redirected_reference,
        )
    }
    fn get_resolution_data(&self) -> &ResolutionData {
        self.get_resolution_data()
    }
}

#[cfg(test)]
mod resolver_internal_test;
