// Ported from tsc/internal/module/staticresolver.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;
use std::sync::Arc;

use tsc_core::compileroptions::ResolutionMode;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};

use crate::cache::ResolutionData;
use crate::resolver::DiagAndArgs;
use crate::types::{
    ResolvedModule, ResolvedProjectReference, ResolvedTypeReferenceDirective, Resolver,
};

/// `type StaticResolutionEntry struct`
///
/// PORT: `ResolutionMode *core.ResolutionMode` is `Option<ResolutionMode>`,
/// `Result *ResolvedModule` is `Option<ResolvedModule>` (Go nil → `None`).
pub struct StaticResolutionEntry {
    pub module_name: String,
    pub containing_directory: RootedDirectoryPath,
    pub resolution_mode: Option<ResolutionMode>,
    pub result: Option<ResolvedModule>,
}

/// `type staticResolutionKey struct`
#[derive(Clone, PartialEq, Eq, Hash)]
struct StaticResolutionKey {
    module_name: String,
    directory: PathKey,
    mode: ResolutionMode,
    has_directory: bool,
    has_mode: bool,
}

/// `type StaticResolutions struct`
///
/// PORT: `Clone` so a shared registration can hand copies to each
/// `StaticResolver` wrapper it creates (Go shares the `*StaticResolutions`
/// pointer; here each wrapper owns an equal copy).
#[derive(Clone)]
pub struct StaticResolutions {
    fallback_to_resolver: bool,
    entries: HashMap<StaticResolutionKey, Option<ResolvedModule>>,
    /// PORT: stored but never read — matching the Go field, which is also
    /// written only by the constructor.
    #[allow(dead_code)]
    current_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
}

/// `func NewStaticResolutions(...) (*StaticResolutions, error)`
///
/// PORT: the error return becomes `Err(String)` carrying the Go message text.
pub fn new_static_resolutions(
    entries: Vec<StaticResolutionEntry>,
    fallback_to_resolver: bool,
    current_directory: RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> Result<StaticResolutions, String> {
    let mut resolutions = StaticResolutions {
        fallback_to_resolver,
        entries: HashMap::with_capacity(entries.len()),
        current_directory,
        case_sensitivity,
    };
    for entry in entries {
        if entry.module_name.is_empty() {
            return Err("module name is empty".to_string());
        }
        let mut key = StaticResolutionKey {
            module_name: entry.module_name.clone(),
            directory: PathKey::default(),
            mode: ResolutionMode::default(),
            has_directory: false,
            has_mode: false,
        };
        if !entry.containing_directory.is_empty() {
            key.directory = case_sensitivity.path_key(&entry.containing_directory.as_path());
            key.has_directory = true;
        }
        if let Some(resolution_mode) = entry.resolution_mode {
            key.mode = resolution_mode;
            key.has_mode = true;
        }
        if resolutions.entries.contains_key(&key) {
            return Err(format!(
                "duplicate static module resolution for {:?}",
                entry.module_name
            ));
        }
        resolutions.entries.insert(key, entry.result);
    }
    Ok(resolutions)
}

impl StaticResolutions {
    /// `func (r *StaticResolutions) lookup(moduleName string, containingDirectory tspath.RootedDirectoryPath, resolutionMode core.ResolutionMode) (*ResolvedModule, bool)`
    ///
    /// PORT: `Some(entry)` is a hit (the entry may itself be `None` — a
    /// recorded *unresolved* resolution); `None` is a miss.
    pub fn lookup(
        &self,
        module_name: &str,
        containing_directory: &RootedDirectoryPath,
        resolution_mode: ResolutionMode,
    ) -> Option<Option<ResolvedModule>> {
        let directory = self
            .case_sensitivity
            .path_key(&containing_directory.as_path());
        let keys = [
            StaticResolutionKey {
                module_name: module_name.to_string(),
                directory: directory.clone(),
                mode: resolution_mode,
                has_directory: true,
                has_mode: true,
            },
            StaticResolutionKey {
                module_name: module_name.to_string(),
                directory: directory.clone(),
                mode: ResolutionMode::default(),
                has_directory: true,
                has_mode: false,
            },
            StaticResolutionKey {
                module_name: module_name.to_string(),
                directory: PathKey::default(),
                mode: resolution_mode,
                has_directory: false,
                has_mode: true,
            },
            StaticResolutionKey {
                module_name: module_name.to_string(),
                directory: PathKey::default(),
                mode: ResolutionMode::default(),
                has_directory: false,
                has_mode: false,
            },
        ];
        for key in keys {
            if let Some(result) = self.entries.get(&key) {
                return Some(result.clone());
            }
        }
        None
    }
}

/// `type StaticResolver struct`
pub struct StaticResolver {
    fallback: Arc<dyn Resolver>,
    resolutions: StaticResolutions,
}

/// `func NewStaticResolver(fallback Resolver, resolutions *StaticResolutions) *StaticResolver`
pub fn new_static_resolver(
    fallback: Arc<dyn Resolver>,
    resolutions: StaticResolutions,
) -> StaticResolver {
    StaticResolver {
        fallback,
        resolutions,
    }
}

impl StaticResolver {
    /// `func (r *StaticResolver) resolveModuleName(...) (*ResolvedModule, []DiagAndArgs, error)`
    fn resolve_module_name_impl(
        &self,
        module_name: &str,
        containing_file: &RootedFilePath,
        containing_directory: &RootedDirectoryPath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>) {
        if let Some(result) =
            self.resolutions
                .lookup(module_name, containing_directory, resolution_mode)
        {
            return (result, Vec::new());
        }
        if !self.resolutions.fallback_to_resolver {
            return (None, Vec::new());
        }
        self.fallback.resolve_module_name(
            module_name,
            containing_file,
            resolution_mode,
            redirected_reference,
        )
    }
}

impl Resolver for StaticResolver {
    /// `func (r *StaticResolver) BaseDirectory() tspath.RootedDirectoryPath`
    fn base_directory(&self) -> RootedDirectoryPath {
        self.fallback.base_directory()
    }

    /// `func (r *StaticResolver) ResolveModuleName(...) (*ResolvedModule, []DiagAndArgs, error)`
    fn resolve_module_name(
        &self,
        module_name: &str,
        containing_file: &RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>) {
        self.resolve_module_name_impl(
            module_name,
            containing_file,
            &containing_file.directory(),
            resolution_mode,
            redirected_reference,
        )
    }

    /// `func (r *StaticResolver) ResolveModuleNameFromDirectory(...) (*ResolvedModule, []DiagAndArgs, error)`
    fn resolve_module_name_from_directory(
        &self,
        module_name: &str,
        containing_directory: &RootedDirectoryPath,
        resolution_mode: ResolutionMode,
    ) -> (Option<ResolvedModule>, Vec<DiagAndArgs>) {
        if let Some(result) =
            self.resolutions
                .lookup(module_name, containing_directory, resolution_mode)
        {
            return (result, Vec::new());
        }
        if !self.resolutions.fallback_to_resolver {
            return (None, Vec::new());
        }
        self.fallback.resolve_module_name_from_directory(
            module_name,
            containing_directory,
            resolution_mode,
        )
    }

    /// `func (r *StaticResolver) ResolveTypeReferenceDirective(...) (*ResolvedTypeReferenceDirective, []DiagAndArgs)`
    fn resolve_type_reference_directive(
        &self,
        type_reference_directive_name: &str,
        containing_file: &RootedFilePath,
        resolution_mode: ResolutionMode,
        redirected_reference: Option<&dyn ResolvedProjectReference>,
    ) -> (ResolvedTypeReferenceDirective, Vec<DiagAndArgs>) {
        self.fallback.resolve_type_reference_directive(
            type_reference_directive_name,
            containing_file,
            resolution_mode,
            redirected_reference,
        )
    }

    /// `func (r *StaticResolver) GetResolutionData() *ResolutionData`
    fn get_resolution_data(&self) -> &ResolutionData {
        self.fallback.get_resolution_data()
    }
}
