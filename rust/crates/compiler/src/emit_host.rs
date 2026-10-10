// Ported from tsc/internal/compiler/emitHost.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `*ast.SourceFile`/`​*ast.Node` are `NodeId` values resolved through
// the program's per-file `Vec<Node>` arenas (`Program::nodes`/
// `nodes_mut`). `printer.EmitHost`'s Go `*EmitContext` parameter maps to a
// shared `Rc<RefCell<EmitContext>>` the emit host owns; the `&EmitContext`
// trait parameter is accepted but the stored handle is used (they are the
// same object — the emitter always installs its own context via
// `set_emit_context`). `printer.EmitHost::source_files` cannot produce a
// `&[SourceFile]` from disjoint arenas and nothing in the workspace calls
// it, so it returns an empty slice; callers that need files use
// `emit_source_files`.

use std::cell::{Ref, RefCell};
use std::rc::Rc;
use std::sync::Arc;

use tsc_ast::utilities::HasFileName;
use tsc_ast::{FileReference, Node, NodeId, SourceFile};
use tsc_checker::checker_core::Checker;
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::options_generated::{CompilerOptions, ModuleKind};
use tsc_module::ResolvedModule;
use tsc_outputpaths::{ForceEmitPaths, OutputPaths, OutputPathsHost};
use tsc_packagejson::InfoCacheEntry;
use tsc_printer::{EmitContext, EmitHost as PrinterEmitHost, EmitResolver};
use tsc_symlinks::KnownSymlinks;
use tsc_transformers::declarations::host::DeclarationEmitHost;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_tsoptions::parsedcommandline::SourceOutputAndProjectReference;

use crate::program::Program;

/// `type EmitOnly byte` + `EmitAll`/`EmitOnlyJs`/`EmitOnlyDts`/
/// `EmitOnlyBuilderSignature`.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub enum EmitOnly {
    #[default]
    All,
    Js,
    Dts,
    BuilderSignature,
}

/// `type EmitResult struct`.
#[derive(Default)]
pub struct EmitResult {
    pub emit_skipped: bool,
    /// Contains declaration emit diagnostics.
    pub diagnostics: Vec<tsc_ast::diagnostic::DiagnosticRef>,
    /// Array of files the compiler wrote to disk.
    pub emitted_files: Vec<RootedFilePath>,
    /// Array of sourceMapData if compiler emitted sourcemaps.
    pub source_maps: Vec<SourceMapEmitResult>,
}

/// `type SourceMapEmitResult struct`.
pub struct SourceMapEmitResult {
    /// Input source file (which one can use on program to get the file),
    /// 1:1 mapping with the sourceMap.sources list.
    pub input_source_file_names: Vec<String>,
    pub source_map: tsc_sourcemap::RawSourceMap,
    pub generated_file: String,
}

/// `type WriteFileData struct`.
pub struct WriteFileData {
    pub source_map_url_pos: i32,
    /// `BuildInfo any` — the build-info producer layer stores its JSON value
    /// here; `serde_json::Value` is the workspace's `any`-JSON stand-in.
    pub build_info: Option<serde_json::Value>,
    pub diagnostics: Vec<tsc_ast::diagnostic::DiagnosticRef>,
    pub skipped_dts_write: bool,
    /// `SourceFile *ast.SourceFile` — the file being emitted.
    pub source_file: Option<NodeId>,
}

impl Default for WriteFileData {
    fn default() -> Self {
        WriteFileData {
            source_map_url_pos: -1,
            build_info: None,
            diagnostics: Vec::new(),
            skipped_dts_write: false,
            source_file: None,
        }
    }
}

/// `type WriteFile func` — returns a Go `error` as `Err(String)` (the
/// diagnostic path only uses `err.Error()`).
pub type WriteFileFn<'a> =
    Box<dyn Fn(&RootedFilePath, &str, &mut WriteFileData) -> Result<(), String> + 'a>;

/// `type EmitOptions struct`.
#[derive(Default)]
pub struct EmitOptions<'a> {
    /// Source files to emit. If `None`, emits all files.
    pub target_source_files: Option<Vec<NodeId>>,
    pub emit_only: EmitOnly,
    pub force_emit: bool,
    pub write_file: Option<WriteFileFn<'a>>,
}

/// `type EmitHost interface` (emitHost.go) — `printer.EmitHost` +
/// `declarations.DeclarationEmitHost` + the additional members declared on
/// the Go interface. `*ast.SourceFile` parameters are `NodeId`s; where the
/// Go signature takes `ast.HasFileName` this trait takes `&dyn HasFileName`.
///
/// NOTE: EmitHost operations must be thread-safe in Go; the Rust port is
/// single-threaded (see PORTING-NOTES), so no synchronization is needed.
pub trait EmitHost: PrinterEmitHost + DeclarationEmitHost {
    /// `SourceFiles() []*ast.SourceFile` — `NodeId`s of the program's files.
    fn emit_source_files(&self) -> &[NodeId];
    /// `BaseDirectory() tspath.RootedDirectoryPath`.
    fn base_directory(&self) -> &RootedDirectoryPath;
    /// `ContentMapperExtensions() []string` — part of `OutputPathsHost`.
    fn emit_content_mapper_extensions(&self) -> &[String];

    /// `GetModeForUsageLocation(file, moduleSpecifier)` —
    /// `moduleSpecifier` is the `*ast.StringLiteralLike` node id.
    fn get_mode_for_usage_location(
        &self,
        file: &dyn HasFileName,
        module_specifier: NodeId,
    ) -> ResolutionMode;
    /// `GetResolvedModuleFromModuleSpecifier(file, moduleSpecifier)`.
    fn get_resolved_module_from_module_specifier(
        &self,
        file: &dyn HasFileName,
        module_specifier: NodeId,
    ) -> Option<ResolvedModule>;
    /// `GetDefaultResolutionModeForFile(file)`.
    fn get_default_resolution_mode_for_file(&self, file: &dyn HasFileName) -> ResolutionMode;
    /// `FileExists(path)`.
    fn emit_host_file_exists(&self, path: &RootedFilePath) -> bool;
    /// `GetGlobalTypingsCacheLocation()`.
    fn get_global_typings_cache_location(&self) -> RootedDirectoryPath;
    /// `GetNearestAncestorDirectoryWithPackageJson(dirname)`.
    fn get_nearest_ancestor_directory_with_package_json(
        &self,
        dirname: &RootedDirectoryPath,
    ) -> RootedDirectoryPath;
    /// `GetPackageJsonInfo(pkgJsonPath)`.
    fn get_package_json_info(
        &self,
        pkg_json_path: &RootedFilePath,
    ) -> Option<Arc<InfoCacheEntry>>;
    /// `GetSourceOfProjectReferenceIfOutputIncluded(file)`.
    fn get_source_of_project_reference_if_output_included(
        &self,
        file: &dyn HasFileName,
    ) -> RootedFilePath;
    /// `GetRedirectTargets(path)`.
    fn get_redirect_targets(&self, path: &PathKey) -> Vec<RootedFilePath>;
    /// `GetSymlinkCache()`.
    fn get_symlink_cache(&self) -> Option<&KnownSymlinks>;
    /// `NewEmitResolver(emitContext)` — produces the checker-backed
    /// `EmitResolver` bound to `emit_context`, the `Rc<RefCell>` handle the
    /// emitter created for this emit run.
    /// Returns the *concrete* checker resolver so call sites can coerce the
    /// `Rc<RefCell<..>>` into `Rc<RefCell<dyn EmitResolver + 'a>>` at a
    /// locally-scoped `'a` (trait-object lifetimes inside `RefCell` are
    /// invariant and cannot be shortened after the fact).
    fn new_emit_resolver_for_context(
        &self,
        emit_context: Rc<RefCell<EmitContext>>,
    ) -> Rc<RefCell<tsc_checker::emitresolver::EmitResolver>>;

    /// Arena access for `NodeId`s owned by the program's files.
    fn emit_nodes(&self, file_index: u32) -> Ref<'_, Vec<Node>>;
    /// Mutable arena access (transforms, synthetic imports).
    fn emit_nodes_mut(&self, file_index: u32) -> std::cell::RefMut<'_, Vec<Node>>;
}

/// `type emitHost struct` — the `Program`-backed `EmitHost`.
///
/// PORT: `newEmitResolver func(*printer.EmitContext) *checker.EmitResolver`
/// becomes the checker's `Rc<RefCell<Checker>>` + this host's emit context.
pub struct BasicEmitHost<'p> {
    program: &'p Program,
    checker: Rc<RefCell<Checker>>,
    /// The `EmitContext` minted by the emitter for this file's emit; set by
    /// `set_emit_context` before transforms run.
    emit_context: RefCell<Option<Rc<RefCell<EmitContext>>>>,
    /// `sourceFiles` for `printer::EmitHost::source_files` — always empty;
    /// see the file header PORT note.
    empty_source_files: Vec<SourceFile>,
}

impl<'p> BasicEmitHost<'p> {
    /// `newEmitHost(ctx, program, file)` — acquires the file's checker.
    pub fn new(
        ctx: tsc_core::context::Context,
        program: &'p Program,
        file: NodeId,
    ) -> (Rc<BasicEmitHost<'p>>, impl FnOnce() + 'p) {
        let (checker, done) = program.get_type_checker_for_file(ctx, file);
        (
            Rc::new(BasicEmitHost {
                program,
                checker,
                emit_context: RefCell::new(None),
                empty_source_files: Vec::new(),
            }),
            done,
        )
    }

    /// Binds the shared emit context minted by the emitter.
    pub fn set_emit_context(&self, emit_context: Rc<RefCell<EmitContext>>) {
        *self.emit_context.borrow_mut() = Some(emit_context);
    }

    /// The backing `Program` — for `GetEmitModuleFormatOfFile`-style
    /// `ast.HasFileName` callbacks that don't fit the printer trait
    /// signatures.
    pub fn program(&self) -> &'p Program {
        self.program
    }

    pub fn checker(&self) -> &Rc<RefCell<Checker>> {
        &self.checker
    }

    fn emit_context_handle(&self) -> Rc<RefCell<EmitContext>> {
        self.emit_context
            .borrow()
            .clone()
            .expect("emit context installed before use")
    }
}

/// `SourceFileMayBeEmittedHost` — the narrow interface emitter.go checks
/// emission eligibility through; implemented by `Program`/`BasicEmitHost`
/// via a small adapter over `NodeId`s.
pub trait SourceFileMayBeEmittedHost {
    fn smbe_options(&self) -> &CompilerOptions;
    fn smbe_project_reference_from_source(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>>;
    fn smbe_is_source_file_from_external_library(&self, file: NodeId) -> bool;
    fn smbe_base_directory(&self) -> RootedDirectoryPath;
    fn smbe_case_sensitivity(&self) -> CaseSensitivity;
    fn smbe_source_files(&self) -> Vec<NodeId>;
    fn smbe_nodes(&self, file_index: u32) -> Ref<'_, Vec<Node>>;
}

/// `sourceFileMayBeEmitted`.
pub fn source_file_may_be_emitted(
    source_file: NodeId,
    host: &dyn SourceFileMayBeEmittedHost,
    force_dts_emit: bool,
    force_js_emit: bool,
) -> bool {
    // TODO: move this to outputpaths?
    let options = host.smbe_options();
    let nodes = host.smbe_nodes(source_file.file_index());
    let file = nodes[source_file].as_source_file();
    // Js files are emitted only if option is enabled
    if !force_js_emit
        && options.no_emit_for_js_files.is_true()
        && tsc_ast::is_source_file_js(file)
    {
        return false;
    }

    // Declaration files are not emitted
    if file.is_declaration_file {
        return false;
    }

    // Runtime output for content-mapped files is owned by the external
    // content mapper or build tool. Only include them in the emit set when
    // their transformed TypeScript can produce declarations.
    if !file.content_mapper().is_empty() && !force_dts_emit && !options.get_emit_declarations() {
        return false;
    }

    let path_key = file.path_key().clone();
    let file_name = file.file_name().clone();
    let is_json = tsc_ast::is_json_source_file(file);
    drop(nodes);

    // Source file from node_modules are not emitted
    if host.smbe_is_source_file_from_external_library(source_file) {
        return false;
    }

    // forcing dts emit => file needs to be emitted
    if force_dts_emit || force_js_emit {
        return true;
    }

    // Check other conditions for file emit
    // Source files from referenced projects are not emitted
    if host.smbe_project_reference_from_source(&path_key).is_some() {
        return false;
    }

    // Any non json file should be emitted
    if !is_json {
        return true;
    }

    // Json file is not emitted if outDir is not specified
    if options.out_dir.is_empty() {
        return false;
    }

    // Otherwise, if rootDir is specified or a config file exists, we know the
    // common source directory and can check if the file would be emitted in
    // the same location
    if !options.root_dir.is_empty() || !options.config_file_path.is_empty() {
        let common_dir = tsc_outputpaths::get_common_source_directory(
            options,
            || Vec::new(),
            host.smbe_base_directory(),
            host.smbe_case_sensitivity(),
            None,
        );
        let output_path = tsc_outputpaths::get_source_file_name_in_new_dir(
            &file_name,
            &options.out_dir,
            &common_dir,
            host.smbe_case_sensitivity(),
        );
        if host
            .smbe_case_sensitivity()
            .compare_file_paths(&file_name, &output_path)
            == 0
        {
            return false;
        }
    }

    true
}

/// `getSourceFilesToEmit`.
pub fn get_source_files_to_emit(
    host: &dyn SourceFileMayBeEmittedHost,
    target_source_files: Option<Vec<NodeId>>,
    force_dts_emit: bool,
    force_js_emit: bool,
) -> Vec<NodeId> {
    let target_source_files = target_source_files.unwrap_or_else(|| host.smbe_source_files());
    target_source_files
        .into_iter()
        .filter(|&source_file| {
            source_file_may_be_emitted(source_file, host, force_dts_emit, force_js_emit)
        })
        .collect()
}

/// `isSourceFileNotJson`.
pub fn is_source_file_not_json(file: NodeId, nodes: &[Node]) -> bool {
    !tsc_ast::is_json_source_file(nodes[file].as_source_file())
}

/// `getDeclarationDiagnostics` — runs just the declaration transformer over
/// `file` to collect its diagnostics.
pub fn get_declaration_diagnostics(
    host: &Rc<BasicEmitHost<'_>>,
    file: NodeId,
) -> Vec<tsc_ast::diagnostic::DiagnosticRef> {
    // TODO: use p.getSourceFilesToEmit cache
    let full_files: Vec<NodeId> = {
        let nodes = host.emit_nodes(file.file_index());
        get_source_files_to_emit(&**host, Some(vec![file]), false, false)
            .into_iter()
            .filter(|f| is_source_file_not_json(*f, &nodes))
            .collect()
    };
    if !full_files.iter().any(|f| *f == file) {
        return Vec::new();
    }
    let emit_context = Rc::new(RefCell::new(EmitContext::new()));
    host.set_emit_context(emit_context.clone());
    let emit_resolver = host.new_emit_resolver_for_context(emit_context);
    // PORT: `TransformOptions::symbols` — declaration tracking reads the
    // checker's symbol arena for isolated-declaration errors; the arena
    // outlives `transform` (both end in this scope).
    let symbol_arena = host.checker.borrow().symbol_arena.clone();
    let transform = tsc_transformers::declarations::transform::new_declaration_transformer(
        host.clone(),
        emit_resolver,
        PrinterEmitHost::options(&**host),
        RootedFilePath::default(),
        Some(&*symbol_arena),
    );
    let mut nodes_mut = host.emit_nodes_mut(file.file_index());
    transform.transform_source_file(&mut *nodes_mut, file);
    transform.get_diagnostics()
}

impl<'p> OutputPathsHost for BasicEmitHost<'p> {
    fn common_source_directory(&self) -> RootedDirectoryPath {
        self.program.common_source_directory()
    }
    fn content_mapper_extensions(&self) -> &[String] {
        self.emit_content_mapper_extensions()
    }
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.program.case_sensitivity()
    }
}

impl<'p> PrinterEmitHost for BasicEmitHost<'p> {
    fn options(&self) -> &CompilerOptions {
        self.program.options_ref()
    }
    /// `SourceFiles() []*ast.SourceFile` — see header note: Go's slice cannot
    /// be materialized from disjoint arenas; unused by the Rust workspace.
    fn source_files(&self) -> &[SourceFile] {
        &self.empty_source_files
    }
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.program.case_sensitivity()
    }
    fn common_source_directory(&self) -> &RootedDirectoryPath {
        self.program.common_source_directory_ref()
    }
    fn is_emit_blocked(&self, file: &RootedFilePath) -> bool {
        self.program.is_emit_blocked(file)
    }
    fn write_file(&self, file_name: &RootedFilePath, text: &str) -> std::io::Result<()> {
        self.program
            .host()
            .fs()
            .write_file(file_name, text)
            .map_err(|e| std::io::Error::other(e.to_string()))
    }
    fn get_emit_module_format_of_file(&self, file: &SourceFile) -> ModuleKind {
        self.program.get_emit_module_format_of_file(file)
    }
    /// `NewEmitResolver` — the trait's `&EmitContext` cannot be turned back
    /// into the `Rc<RefCell<EmitContext>>` the checker resolver requires; the
    /// host's stored handle is the same object (installed by the emitter via
    /// `set_emit_context`).
    fn new_emit_resolver(&self, _emit_context: &EmitContext) -> Box<dyn EmitResolver + '_> {
        Box::new(tsc_checker::emitresolver::new_emit_resolver(
            self.checker.clone(),
            self.emit_context_handle(),
        ))
    }
    fn get_project_reference_from_source(
        &self,
        path: PathKey,
    ) -> Option<&SourceOutputAndProjectReference> {
        self.program.get_project_reference_from_source_ref(&path)
    }
    fn is_source_file_from_external_library(&self, file: &SourceFile) -> bool {
        self.program
            .is_source_file_from_external_library_by_path(file.path_key())
    }
}

impl<'p> DeclarationEmitHost for BasicEmitHost<'p> {
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.program.case_sensitivity()
    }
    fn get_source_file_from_reference(
        &self,
        origin: NodeId,
        ref_: &FileReference,
        _nodes: &[Node],
    ) -> Option<NodeId> {
        self.program.get_source_file_from_reference(origin, ref_)
    }
    fn get_output_paths_for(
        &self,
        file: NodeId,
        force_dts_paths: bool,
        _nodes: &[Node],
    ) -> Option<OutputPaths> {
        // TODO: cache
        let nodes = self.program.nodes(file.file_index());
        Some(tsc_outputpaths::get_output_paths_for(
            file,
            self.program.options_ref(),
            self,
            ForceEmitPaths {
                dts: force_dts_paths,
                ..Default::default()
            },
            &nodes,
        ))
    }
    fn source_file_may_be_emitted(
        &self,
        file: NodeId,
        force_dts_emit: bool,
        _nodes: &[Node],
    ) -> bool {
        source_file_may_be_emitted(file, self, force_dts_emit, false)
    }
}

impl<'p> EmitHost for BasicEmitHost<'p> {
    fn emit_source_files(&self) -> &[NodeId] {
        self.program.source_files_slice()
    }
    fn base_directory(&self) -> &RootedDirectoryPath {
        self.program.base_directory_ref()
    }
    fn emit_content_mapper_extensions(&self) -> &[String] {
        self.program.content_mapper_extensions()
    }
    fn get_mode_for_usage_location(
        &self,
        file: &dyn HasFileName,
        module_specifier: NodeId,
    ) -> ResolutionMode {
        self.program.get_mode_for_usage_location(file, module_specifier)
    }
    fn get_resolved_module_from_module_specifier(
        &self,
        file: &dyn HasFileName,
        module_specifier: NodeId,
    ) -> Option<ResolvedModule> {
        self.program
            .get_resolved_module_from_module_specifier_has(file, module_specifier)
    }
    fn get_default_resolution_mode_for_file(&self, file: &dyn HasFileName) -> ResolutionMode {
        self.program.get_default_resolution_mode_for_file(file)
    }
    fn emit_host_file_exists(&self, path: &RootedFilePath) -> bool {
        self.program.file_exists(path)
    }
    fn get_global_typings_cache_location(&self) -> RootedDirectoryPath {
        self.program.get_global_typings_cache_location()
    }
    fn get_nearest_ancestor_directory_with_package_json(
        &self,
        dirname: &RootedDirectoryPath,
    ) -> RootedDirectoryPath {
        self.program
            .get_nearest_ancestor_directory_with_package_json(dirname)
    }
    fn get_package_json_info(
        &self,
        pkg_json_path: &RootedFilePath,
    ) -> Option<Arc<InfoCacheEntry>> {
        self.program.get_package_json_info(pkg_json_path)
    }
    fn get_source_of_project_reference_if_output_included(
        &self,
        file: &dyn HasFileName,
    ) -> RootedFilePath {
        self.program
            .get_source_of_project_reference_if_output_included(file)
    }
    fn get_redirect_targets(&self, path: &PathKey) -> Vec<RootedFilePath> {
        self.program.get_redirect_targets(path)
    }
    fn get_symlink_cache(&self) -> Option<&KnownSymlinks> {
        self.program.get_symlink_cache_opt()
    }
    fn new_emit_resolver_for_context(
        &self,
        emit_context: Rc<RefCell<EmitContext>>,
    ) -> Rc<RefCell<tsc_checker::emitresolver::EmitResolver>> {
        Rc::new(RefCell::new(tsc_checker::emitresolver::new_emit_resolver(
            self.checker.clone(),
            emit_context,
        )))
    }
    fn emit_nodes(&self, file_index: u32) -> Ref<'_, Vec<Node>> {
        self.program.nodes(file_index)
    }
    fn emit_nodes_mut(&self, file_index: u32) -> std::cell::RefMut<'_, Vec<Node>> {
        self.program.nodes_mut(file_index)
    }
}

impl<'p> SourceFileMayBeEmittedHost for BasicEmitHost<'p> {
    fn smbe_options(&self) -> &CompilerOptions {
        self.program.options_ref()
    }
    fn smbe_project_reference_from_source(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        self.program.get_project_reference_from_source(path)
    }
    fn smbe_is_source_file_from_external_library(&self, file: NodeId) -> bool {
        let nodes = self.program.nodes(file.file_index());
        let key = nodes[file].as_source_file().path_key().clone();
        drop(nodes);
        self.program.is_source_file_from_external_library_by_path(&key)
    }
    fn smbe_base_directory(&self) -> RootedDirectoryPath {
        self.program.base_directory_ref().clone()
    }
    fn smbe_case_sensitivity(&self) -> CaseSensitivity {
        self.program.case_sensitivity()
    }
    fn smbe_source_files(&self) -> Vec<NodeId> {
        self.program.source_files()
    }
    fn smbe_nodes(&self, file_index: u32) -> Ref<'_, Vec<Node>> {
        self.program.nodes(file_index)
    }
}
