// Ported from tsc/internal/ls/autoimport/aliasresolver.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(arena): `*ast.SourceFile` → `NodeId`. Files resolved lazily during
// checking live in arenas owned by `self.arenas` (append-only map of
// `Rc<ArenaCell>`); `nodes()` returns a `Ref` through a raw-pointer
// borrow — see the safety note there.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

use rustc_hash::FxHashMap;
use tsc_ast::symbol::SymbolArena;
use tsc_ast::utilities::HasFileName;
use tsc_ast::{ArenaCell, NodeId, ast};
use tsc_collections::SyncMap;
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::options_generated::{CompilerOptions, ModuleKind};
use tsc_module::resolver::DefaultResolver;
use tsc_module::{ModeAwareCache, ModeAwareCacheKey, ResolvedModule};
use tsc_tsoptions::parsedcommandline::{ParsedCommandLine, SourceOutputAndProjectReference};
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};

use crate::autoimport::registry::RegistryCloneHost;
use crate::autoimport::util::PathAndFileName;

/// `type aliasResolver struct` — a `checker.Program` over a set of package
/// entrypoint files so the checker can resolve `export *`/alias targets.
pub(crate) struct AliasResolver {
    case_sensitivity: CaseSensitivity,
    host: Rc<dyn RegistryCloneHost>,
    module_resolver: Rc<DefaultResolver>,

    pub(crate) root_files: Vec<NodeId>,
    /// `symlinks` maps from realpath to symlinked path and file name.
    pub(crate) symlinks: HashMap<PathKey, PathAndFileName>,
    /// `onFailedAmbientModuleLookup`.
    on_failed_ambient_module_lookup: Option<Rc<dyn Fn(&dyn HasFileName, &str)>>,
    /// `resolvedModules`.
    resolved_modules: SyncMap<PathKey, Arc<SyncMap<ModeAwareCacheKey, Option<ResolvedModule>>>>,
    /// `getResolvedModules` result — never populated (diagnostics only).
    resolved_modules_empty: FxHashMap<PathKey, ModeAwareCache<Option<ResolvedModule>>>,

    /// `Options()` — `{NoCheck: core.TSTrue}` allocated once.
    options: Rc<CompilerOptions>,

    /// The program-global symbol arena (`symbols()`); the binder appends to
    /// it for every file loaded through `get_source_file`.
    symbols: SymbolArena,
    /// `file_index -> arena`. Append-only: entries are never removed or
    /// replaced, so each `RefCell`'s heap address is stable for the life of
    /// the resolver (required for the `nodes()` borrow below).
    arenas: RefCell<HashMap<u32, Rc<ArenaCell>>>,
    /// `file_index -> &'static Rc<RefCell<arena>>` — each arena is
    /// `Box::leak`ed once so `nodes()`/`nodes_mut()` can return a `Ref`
    /// bounded by `&self` without `unsafe` (the crate forbids `unsafe`).
    leaked_arenas: RefCell<HashMap<u32, &'static Rc<ArenaCell>>>,
}

/// `newAliasResolver`.
///
/// `root_files` pairs each file's root `NodeId` with its node arena; the
/// resolver registers every arena and eagerly binds each root file into its
/// program-global symbol arena (Go binds them in `extractPackage`'s load
/// loop; binding here keeps the `symbols` arena shared and lazy `get_source_file`
/// loads still bind on demand).
pub(crate) fn new_alias_resolver(
    root_files: Vec<(NodeId, Rc<ArenaCell>)>,
    symlinks: HashMap<PathKey, PathAndFileName>,
    host: Rc<dyn RegistryCloneHost>,
    module_resolver: Rc<DefaultResolver>,
    on_failed_ambient_module_lookup: Option<Rc<dyn Fn(&dyn HasFileName, &str)>>,
) -> Rc<AliasResolver> {
    let mut arenas = HashMap::new();
    for (file, arena) in &root_files {
        arenas.insert(file.file_index(), arena.clone());
    }
    let resolver = Rc::new(AliasResolver {
        case_sensitivity: host.fs().case_sensitivity(),
        host,
        module_resolver,
        root_files: root_files.iter().map(|(f, _)| *f).collect(),
        symlinks,
        on_failed_ambient_module_lookup,
        resolved_modules: SyncMap::new(),
        resolved_modules_empty: FxHashMap::default(),
        options: Rc::new(CompilerOptions {
            no_check: tsc_core::tristate::Tristate::True,
            ..Default::default()
        }),
        symbols: SymbolArena::default(),
        arenas: RefCell::new(arenas),
        leaked_arenas: RefCell::new(HashMap::new()),
    });
    // Bind root files eagerly (Go's `binder.BindSourceFile(file)`).
    for (file, arena) in root_files {
        let mut nodes = arena.cow();
        let mut symbols = resolver.symbols.clone();
        tsc_binder::binder::bind_source_file(&mut nodes, file, &mut symbols);
    }
    resolver
}

impl AliasResolver {
    /// `getSourceFile` — `file` may be absent due to symlink/realpath
    /// mismatch; see TestAutoImportBuilderFS.
    fn get_source_file(&self, file_name: &RootedFilePath, path: &PathKey) -> Option<NodeId> {
        let (file, arena) = self.host.get_source_file(file_name, path)?;
        self.arenas
            .borrow_mut()
            .entry(file.file_index())
            .or_insert(arena);
        {
            let arena = self.arenas.borrow()[&file.file_index()].clone();
            let mut nodes = arena.cow();
            let mut symbols = self.symbols.clone();
            tsc_binder::binder::bind_source_file(&mut nodes, file, &mut symbols);
        }
        Some(file)
    }

    /// `getSourceFileByFileName`.
    pub(crate) fn get_source_file_by_file_name(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
    ) -> Option<NodeId> {
        self.get_source_file(file_name, path)
    }

    /// `&'static` handle for `file_index`'s arena. Entries in `self.arenas`
    /// are append-only; each `Rc` is `Box::leak`ed exactly once (the crate
    /// forbids `unsafe`, so this trades a bounded 16-byte-per-file leak for
    /// a safe `Ref` bounded by `&self`). `RefCell`'s runtime borrow rules
    /// are still enforced.
    fn leaked_arena(&self, file_index: u32) -> &'static Rc<ArenaCell> {
        if let Some(rc) = self.leaked_arenas.borrow().get(&file_index) {
            return rc;
        }
        let rc = self
            .arenas
            .borrow()
            .get(&file_index)
            .expect("unknown file_index")
            .clone();
        let leaked: &'static Rc<ArenaCell> = Box::leak(Box::new(rc));
        self.leaked_arenas.borrow_mut().insert(file_index, leaked);
        leaked
    }
}

impl tsc_outputpaths::OutputPathsHost for AliasResolver {
    /// `CommonSourceDirectory` — unimplemented in Go.
    fn common_source_directory(&self) -> RootedDirectoryPath {
        panic!("unimplemented")
    }

    /// `ContentMapperExtensions`.
    fn content_mapper_extensions(&self) -> &[String] {
        &[]
    }

    /// `CaseSensitivity`.
    fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }
}

impl tsc_modulespecifiers::ModuleSpecifierGenerationHost for AliasResolver {
    /// `GetSymlinkCache` — unimplemented in Go.
    fn get_symlink_cache(&self) -> Option<&tsc_symlinks::KnownSymlinks> {
        panic!("unimplemented")
    }

    /// `GetGlobalTypingsCacheLocation` — unimplemented in Go.
    fn get_global_typings_cache_location(&self) -> RootedDirectoryPath {
        panic!("unimplemented")
    }

    /// `BaseDirectory`.
    fn base_directory(&self) -> RootedDirectoryPath {
        self.module_resolver.base_directory()
    }

    /// `GetProjectReferenceFromSource` — unimplemented in Go.
    fn get_project_reference_from_source(
        &self,
        _path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        panic!("unimplemented")
    }

    /// `GetRedirectTargets` — unimplemented in Go.
    fn get_redirect_targets(&self, _path: &PathKey) -> Vec<RootedFilePath> {
        panic!("unimplemented")
    }

    /// `GetSourceOfProjectReferenceIfOutputIncluded` — unimplemented in Go.
    fn get_source_of_project_reference_if_output_included(
        &self,
        _file: &dyn HasFileName,
    ) -> RootedFilePath {
        panic!("unimplemented")
    }

    /// `FileExists` — unimplemented in Go.
    fn file_exists(&self, _path: &RootedFilePath) -> bool {
        panic!("unimplemented")
    }

    /// `GetNearestAncestorDirectoryWithPackageJson` — unimplemented in Go.
    fn get_nearest_ancestor_directory_with_package_json(
        &self,
        _dirname: &RootedDirectoryPath,
    ) -> RootedDirectoryPath {
        panic!("unimplemented")
    }

    /// `GetPackageJsonInfo` — unimplemented in Go.
    fn get_package_json_info(
        &self,
        _pkg_json_path: &RootedFilePath,
    ) -> Option<Arc<tsc_packagejson::InfoCacheEntry>> {
        panic!("unimplemented")
    }

    /// `GetDefaultResolutionModeForFile`.
    fn get_default_resolution_mode_for_file(&self, _file: &dyn HasFileName) -> ResolutionMode {
        ModuleKind::ESNext
    }

    /// `GetResolvedModuleFromModuleSpecifier` — unimplemented in Go.
    fn get_resolved_module_from_module_specifier(
        &self,
        _file: &dyn HasFileName,
        _module_specifier: NodeId,
    ) -> Option<ResolvedModule> {
        panic!("unimplemented")
    }

    /// `GetModeForUsageLocation`.
    fn get_mode_for_usage_location(
        &self,
        _file: &dyn HasFileName,
        _module_specifier: NodeId,
    ) -> ResolutionMode {
        ModuleKind::ESNext
    }
}

impl tsc_checker::checker_types::Host for AliasResolver {}

impl tsc_checker::checker_types::Program for AliasResolver {
    /// `Options`.
    fn options(&self) -> Rc<CompilerOptions> {
        self.options.clone()
    }

    /// `SourceFiles`.
    fn source_files(&self) -> Vec<NodeId> {
        self.root_files.clone()
    }

    /// `BindSourceFiles` — we bind as we parse.
    fn bind_source_files(&self) {}

    /// The program-global symbol arena.
    fn symbols(&self) -> SymbolArena {
        self.symbols.clone()
    }

    /// `FileExists` — unimplemented in Go.
    fn file_exists(&self, _file_name: &RootedFilePath) -> bool {
        panic!("unimplemented")
    }

    /// `GetSourceFileForResolvedModule`.
    fn get_source_file_for_resolved_module(&self, resolved: &ResolvedModule) -> Option<NodeId> {
        self.get_source_file(&resolved.resolved_file_name, &resolved.resolved_path)
    }

    /// `GetEmitModuleFormatOfFile`.
    fn get_emit_module_format_of_file(&self, _source_file: &dyn HasFileName) -> ModuleKind {
        ModuleKind::ESNext
    }

    /// `GetEmitSyntaxForUsageLocation`.
    fn get_emit_syntax_for_usage_location(
        &self,
        _source_file: &dyn HasFileName,
        _usage_location: NodeId,
    ) -> ResolutionMode {
        ModuleKind::ESNext
    }

    /// `GetImpliedNodeFormatForEmit`.
    fn get_implied_node_format_for_emit(&self, _source_file: &dyn HasFileName) -> ModuleKind {
        ModuleKind::ESNext
    }

    /// `GetResolvedModule`.
    fn get_resolved_module(
        &self,
        current_source_file: &dyn HasFileName,
        module_reference: &str,
        mode: ResolutionMode,
    ) -> Option<ResolvedModule> {
        let (cache, _) = self.resolved_modules.load_or_store(
            current_source_file.path_key().clone(),
            Arc::new(SyncMap::new()),
        );
        let key = ModeAwareCacheKey {
            name: module_reference.to_string(),
            mode,
        };
        if let Some(resolved) = cache.load(&key) {
            return resolved;
        }
        let (resolved, _diags) = self.module_resolver.resolve_module_name(
            module_reference,
            current_source_file.file_name(),
            mode,
            None,
        );
        let (resolved, _) = cache.load_or_store(key, resolved);
        if !resolved.as_ref().is_some_and(|r| r.is_resolved())
            && !tsc_tspath::path_is_relative(module_reference)
            && let Some(callback) = &self.on_failed_ambient_module_lookup
        {
            callback(current_source_file, module_reference);
        }
        resolved
    }

    /// `GetResolvedModules` — only used for diagnostics, which the checker
    /// hopefully won't produce.
    fn get_resolved_modules(&self) -> &FxHashMap<PathKey, ModeAwareCache<Option<ResolvedModule>>> {
        &self.resolved_modules_empty
    }

    /// `GetPackagesMap`.
    fn get_packages_map(&self) -> FxHashMap<String, bool> {
        FxHashMap::default()
    }

    /// `GetSourceFileMetaData` — unimplemented in Go.
    fn get_source_file_meta_data(&self, _path: &PathKey) -> ast::SourceFileMetaData {
        panic!("unimplemented")
    }

    /// `GetJSXRuntimeImportSpecifier`.
    fn get_jsx_runtime_import_specifier(&self, _path: &PathKey) -> (String, Option<NodeId>) {
        (String::new(), None)
    }

    /// `GetImportHelpersImportSpecifier` — unimplemented in Go.
    fn get_import_helpers_import_specifier(&self, _path: &PathKey) -> Option<NodeId> {
        panic!("unimplemented")
    }

    /// `SourceFileMayBeEmitted` — unimplemented in Go.
    fn source_file_may_be_emitted(&self, _source_file: NodeId, _force_dts_emit: bool) -> bool {
        panic!("unimplemented")
    }

    /// `IsSourceFileDefaultLibrary`.
    fn is_source_file_default_library(&self, _path: &PathKey) -> bool {
        false
    }

    /// `GetProjectReferenceFromOutputDts` — unimplemented in Go.
    fn get_project_reference_from_output_dts(
        &self,
        _path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>> {
        panic!("unimplemented")
    }

    /// `GetRedirectForResolution` — unimplemented in Go.
    fn get_redirect_for_resolution(
        &self,
        _file: &dyn HasFileName,
    ) -> Option<Arc<ParsedCommandLine>> {
        panic!("unimplemented")
    }

    /// `CommonSourceDirectory` — unimplemented in Go.
    fn common_source_directory(&self) -> RootedDirectoryPath {
        panic!("unimplemented")
    }

    /// Arena snapshot for a file index. Arenas are registered lazily by
    /// `get_source_file` and are append-only.
    fn nodes(&self, file_index: u32) -> Rc<ast::NodeArenaBuf> {
        self.leaked_arena(file_index).snapshot()
    }

    /// Mutable arena access — copy-on-write via `ArenaMut`.
    fn nodes_mut(&self, file_index: u32) -> tsc_ast::ArenaMut {
        self.leaked_arena(file_index).cow()
    }

    /// `nodes_handle`.
    fn nodes_handle(&self, file_index: u32) -> Rc<ArenaCell> {
        self.arenas
            .borrow()
            .get(&file_index)
            .expect("unknown file_index")
            .clone()
    }
}
