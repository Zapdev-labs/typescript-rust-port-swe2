// Ported from tsc/internal/modulespecifiers/types.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_ast::ast_generated::SourceFile;
use tsc_ast::ids::{NodeId, SymbolId};
use tsc_ast::utilities::{HasFileName, is_source_file_js};
use tsc_core::compileroptions::ResolutionMode;
use tsc_module::ResolvedModule;
use tsc_outputpaths::OutputPathsHost;
use tsc_packagejson::InfoCacheEntry;
use tsc_symlinks::KnownSymlinks;
use tsc_tsoptions::parsedcommandline::SourceOutputAndProjectReference;
use tsc_tspath::{ModuleSpecifier, PathKey, RootedDirectoryPath, RootedFilePath};

/// `type SourceFileForSpecifierGeneration interface`.
///
// PORT: `*ast.StringLiteralLike` nodes become `NodeId`s resolved through the
// `nodes: &[Node]` arena threaded to the functions that consume them.
// `PathKey()`/`FileName()` are covered by the `HasFileName` supertrait.
pub trait SourceFileForSpecifierGeneration: HasFileName {
    /// `Imports()`.
    fn imports(&self) -> &[NodeId];
    /// `IsJS()`.
    fn is_js(&self) -> bool;
}

/// `*ast.SourceFile` satisfies the Go interface (`Imports()` returns the
/// file's import literals; `IsJS()` is `IsSourceFileJS`).
impl SourceFileForSpecifierGeneration for SourceFile {
    fn imports(&self) -> &[NodeId] {
        &self.imports
    }

    fn is_js(&self) -> bool {
        is_source_file_js(self)
    }
}

/// `type CheckerShape interface`.
///
// PORT: `*ast.Symbol` -> `SymbolId`; Go's nil return becomes `Option`. The
// implementor owns the node/symbol arenas (as in nodebuilder's SymbolTracker).
pub trait CheckerShape {
    /// `GetSymbolAtLocation(node *ast.Node) *ast.Symbol`.
    fn get_symbol_at_location(&self, node: NodeId) -> Option<SymbolId>;
    /// `GetAliasedSymbol(symbol *ast.Symbol) *ast.Symbol`.
    fn get_aliased_symbol(&self, symbol: SymbolId) -> SymbolId;
}

/// `type ResultKind uint8`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
#[repr(u8)]
pub enum ResultKind {
    /// `ResultKindNone`.
    #[default]
    None = 0,
    /// `ResultKindNodeModules`.
    NodeModules,
    /// `ResultKindPaths`.
    Paths,
    /// `ResultKindRedirect`.
    Redirect,
    /// `ResultKindRelative`.
    Relative,
    /// `ResultKindAmbient`.
    Ambient,
}

/// `type ModuleSpecifiersResult struct`.
#[derive(Clone, Default)]
pub struct ModuleSpecifiersResult {
    /// `Specifiers`.
    pub specifiers: Vec<ModuleSpecifier>,
    /// `Kind`.
    pub kind: ResultKind,
    /// `AmbientModuleSymbol` — used to construct an import attributes node, if
    /// one is needed. PORT: `*ast.Symbol` -> `Option<SymbolId>`.
    pub ambient_module_symbol: Option<SymbolId>,
}

/// `type ModulePath struct`.
#[derive(Clone, Default)]
pub struct ModulePath {
    /// `FileName`.
    pub file_name: RootedFilePath,
    /// `IsInNodeModules`.
    pub is_in_node_modules: bool,
    /// `IsRedirect`.
    pub is_redirect: bool,
}

/// `type ModuleSpecifierGenerationHost interface`.
///
// PORT: `*ast.SourceFile`/`ast.HasFileName` arguments become `&dyn HasFileName`,
// `*ast.StringLiteralLike` becomes `NodeId`. The `CommonSourceDirectory`,
// `ContentMapperExtensions`, and `CaseSensitivity` members are supplied by the
// `OutputPathsHost` supertrait — the Go interface is structurally an
// `outputpaths.OutputPathsHost` and is passed to `GetOutputJSFileNameWorker`/
// `GetOutputDeclarationFileNameWorker` in specifiers.go.
pub trait ModuleSpecifierGenerationHost: OutputPathsHost {
    // `GetModuleResolutionCache() any` — !!! TODO: adapt new resolution cache model (not ported, as in Go).
    /// `GetSymlinkCache()`.
    fn get_symlink_cache(&self) -> Option<&KnownSymlinks>;
    // `GetFileIncludeReasons() any` — !!! TODO: adapt new resolution cache model (not ported, as in Go).
    /// `GetGlobalTypingsCacheLocation()`.
    fn get_global_typings_cache_location(&self) -> RootedDirectoryPath;
    /// `BaseDirectory()`.
    fn base_directory(&self) -> RootedDirectoryPath;

    /// `GetProjectReferenceFromSource(path)`.
    fn get_project_reference_from_source(
        &self,
        path: &PathKey,
    ) -> Option<Arc<SourceOutputAndProjectReference>>;
    /// `GetRedirectTargets(path)`.
    fn get_redirect_targets(&self, path: &PathKey) -> Vec<RootedFilePath>;
    /// `GetSourceOfProjectReferenceIfOutputIncluded(file)`.
    fn get_source_of_project_reference_if_output_included(
        &self,
        file: &dyn HasFileName,
    ) -> RootedFilePath;

    /// `FileExists(path)`.
    fn file_exists(&self, path: &RootedFilePath) -> bool;

    /// `GetNearestAncestorDirectoryWithPackageJson(dirname)`.
    fn get_nearest_ancestor_directory_with_package_json(
        &self,
        dirname: &RootedDirectoryPath,
    ) -> RootedDirectoryPath;
    /// `GetPackageJsonInfo(pkgJsonPath)`.
    fn get_package_json_info(&self, pkg_json_path: &RootedFilePath) -> Option<Arc<InfoCacheEntry>>;
    /// `GetDefaultResolutionModeForFile(file)`.
    fn get_default_resolution_mode_for_file(&self, file: &dyn HasFileName) -> ResolutionMode;
    /// `GetResolvedModuleFromModuleSpecifier(file, moduleSpecifier)`.
    fn get_resolved_module_from_module_specifier(
        &self,
        file: &dyn HasFileName,
        module_specifier: NodeId,
    ) -> Option<ResolvedModule>;
    /// `GetModeForUsageLocation(file, moduleSpecifier)`.
    fn get_mode_for_usage_location(
        &self,
        file: &dyn HasFileName,
        module_specifier: NodeId,
    ) -> ResolutionMode;
}

/// `type ImportModuleSpecifierPreference string`.
///
// PORT: stays a string newtype so callers can store user-preference values
// verbatim; unknown values behave like Go's default switch arm (Shortest).
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct ImportModuleSpecifierPreference(pub &'static str);

impl ImportModuleSpecifierPreference {
    /// `ImportModuleSpecifierPreferenceNone`.
    pub const NONE: Self = Self("");
    /// `ImportModuleSpecifierPreferenceShortest`.
    pub const SHORTEST: Self = Self("shortest");
    /// `ImportModuleSpecifierPreferenceProjectRelative`.
    pub const PROJECT_RELATIVE: Self = Self("project-relative");
    /// `ImportModuleSpecifierPreferenceRelative`.
    pub const RELATIVE: Self = Self("relative");
    /// `ImportModuleSpecifierPreferenceNonRelative`.
    pub const NON_RELATIVE: Self = Self("non-relative");
}

/// `type ImportModuleSpecifierEndingPreference string`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct ImportModuleSpecifierEndingPreference(pub &'static str);

impl ImportModuleSpecifierEndingPreference {
    /// `ImportModuleSpecifierEndingPreferenceNone`.
    pub const NONE: Self = Self("");
    /// `ImportModuleSpecifierEndingPreferenceAuto`.
    pub const AUTO: Self = Self("auto");
    /// `ImportModuleSpecifierEndingPreferenceMinimal`.
    pub const MINIMAL: Self = Self("minimal");
    /// `ImportModuleSpecifierEndingPreferenceIndex`.
    pub const INDEX: Self = Self("index");
    /// `ImportModuleSpecifierEndingPreferenceJs`.
    pub const JS: Self = Self("js");
}

/// `type UserPreferences struct`.
#[derive(Clone, Default)]
pub struct UserPreferences {
    /// `ImportModuleSpecifierPreference`.
    pub import_module_specifier_preference: ImportModuleSpecifierPreference,
    /// `ImportModuleSpecifierEnding`.
    pub import_module_specifier_ending: ImportModuleSpecifierEndingPreference,
    /// `AutoImportSpecifierExcludeRegexes`.
    pub auto_import_specifier_exclude_regexes: Vec<String>,
}

/// `type ModuleSpecifierOptions struct`.
#[derive(Clone, Copy, Default)]
pub struct ModuleSpecifierOptions {
    /// `OverrideImportMode`.
    pub override_import_mode: ResolutionMode,
}

/// `type RelativePreferenceKind uint8`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum RelativePreferenceKind {
    /// `RelativePreferenceRelative`.
    Relative = 0,
    /// `RelativePreferenceNonRelative`.
    NonRelative,
    /// `RelativePreferenceShortest`.
    Shortest,
    /// `RelativePreferenceExternalNonRelative`.
    ExternalNonRelative,
}

/// `type ModuleSpecifierEnding uint8`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum ModuleSpecifierEnding {
    /// `ModuleSpecifierEndingMinimal`.
    Minimal = 0,
    /// `ModuleSpecifierEndingIndex`.
    Index,
    /// `ModuleSpecifierEndingJsExtension`.
    JsExtension,
    /// `ModuleSpecifierEndingTsExtension`.
    TsExtension,
}

/// `type MatchingMode uint8`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum MatchingMode {
    /// `MatchingModeExact`.
    Exact = 0,
    /// `MatchingModeDirectory`.
    Directory,
    /// `MatchingModePattern`.
    Pattern,
}
