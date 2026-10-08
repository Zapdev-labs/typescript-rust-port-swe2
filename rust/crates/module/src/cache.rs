// Ported from tsc/internal/module/cache.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use rustc_hash::FxHashMap;
use tsc_collections::{OrderedMap, SyncMap};
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::options_generated::CompilerOptions;
use tsc_packagejson::{InfoCache, InfoCacheEntry};
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};

use crate::resolver::ParsedPatterns;
use crate::types::{
    ModeAwareCacheKey, ResolvedModule, ResolvedProjectReference, ResolvedTypeReferenceDirective,
};

/// `type ModeAwareCache[T any] map[ModeAwareCacheKey]T`
pub type ModeAwareCache<T> = FxHashMap<ModeAwareCacheKey, T>;

/// `type moduleResolutionCacheKey struct`
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct ModuleResolutionCacheKey {
    pub(crate) containing_directory: RootedDirectoryPath,
    pub(crate) module_name: String,
    pub(crate) resolution_mode: ResolutionMode,
    pub(crate) redirect_config_name: RootedFilePath,
}

/// `type moduleResolutionCache struct`
#[derive(Default)]
pub(crate) struct ModuleResolutionCache {
    pub(crate) cache: SyncMap<ModuleResolutionCacheKey, Arc<ResolvedModule>>,
}

impl ModuleResolutionCache {
    /// `func (c *moduleResolutionCache) Get(key moduleResolutionCacheKey) (*ResolvedModule, bool)`
    pub(crate) fn get(&self, key: &ModuleResolutionCacheKey) -> Option<Arc<ResolvedModule>> {
        self.cache.load(key)
    }

    /// `func (c *moduleResolutionCache) Set(key moduleResolutionCacheKey, value *ResolvedModule)`
    ///
    /// PORT: `LoadOrStore` semantics preserved — the existing value wins.
    pub(crate) fn set(&self, key: ModuleResolutionCacheKey, value: Arc<ResolvedModule>) {
        self.cache.load_or_store(key, value);
    }
}

/// `type typeRefDirectiveResolutionCacheKey struct`
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct TypeRefDirectiveResolutionCacheKey {
    pub(crate) containing_directory: RootedDirectoryPath,
    pub(crate) type_reference_name: String,
    pub(crate) resolution_mode: ResolutionMode,
    pub(crate) redirect_config_name: RootedFilePath,
    pub(crate) from_inferred_types_containing_file: bool,
}

/// `type typeRefDirectiveResolutionCache struct`
#[derive(Default)]
pub(crate) struct TypeRefDirectiveResolutionCache {
    pub(crate) cache:
        SyncMap<TypeRefDirectiveResolutionCacheKey, Arc<ResolvedTypeReferenceDirective>>,
}

impl TypeRefDirectiveResolutionCache {
    /// `func (c *typeRefDirectiveResolutionCache) Get(...) (*ResolvedTypeReferenceDirective, bool)`
    pub(crate) fn get(
        &self,
        key: &TypeRefDirectiveResolutionCacheKey,
    ) -> Option<Arc<ResolvedTypeReferenceDirective>> {
        self.cache.load(key)
    }

    /// `func (c *typeRefDirectiveResolutionCache) Set(...)`
    pub(crate) fn set(
        &self,
        key: TypeRefDirectiveResolutionCacheKey,
        value: Arc<ResolvedTypeReferenceDirective>,
    ) {
        self.cache.store(key, value);
    }
}

/// `type parsedPatternsCache struct`
///
/// PORT: Go keys the cache by `*collections.OrderedMap` pointer identity.
/// Here the key is the address of the `OrderedMap` inside the
/// `Arc<CompilerOptions>` (or `Option` inline slot) — stable for as long as
/// the owning options are alive, which is every lookup in practice. Unlike
/// Go's GC-pinned keys a dropped map's address could theoretically be reused
/// by a different map, yielding a stale hit; `ParsedPatterns` is a pure
/// function of the map's keys, so this is a (remote) correctness hazard only
/// for aliasing maps with different keys.
#[derive(Default)]
pub(crate) struct ParsedPatternsCache {
    pub(crate) cache: SyncMap<usize, Arc<ParsedPatterns>>,
}

impl ParsedPatternsCache {
    /// `func (c *parsedPatternsCache) Get(pathMappings *collections.OrderedMap[string, []string]) *ParsedPatterns`
    pub(crate) fn get<V>(
        &self,
        path_mappings: Option<&OrderedMap<String, V>>,
    ) -> Arc<ParsedPatterns> {
        let key = path_mappings.map_or(0usize, |m| m as *const OrderedMap<String, V> as usize);
        if let Some(patterns) = self.cache.load(&key) {
            return patterns;
        }
        self.cache
            .load_or_store(
                key,
                Arc::new(crate::resolver::try_parse_patterns(path_mappings)),
            )
            .0
    }
}

/// `type ResolutionData struct`
pub struct ResolutionData {
    /// `compilerOptions *core.CompilerOptions`
    ///
    /// PORT: shared `Arc` mirrors the Go pointer; `Default` is the Go `nil`
    /// embedded value (used by tests that build a bare `ResolutionData{}`).
    pub(crate) compiler_options: Arc<CompilerOptions>,
    pub(crate) typings_location: RootedDirectoryPath,
    pub(crate) project_name: String,
    pub(crate) extra_extensions: Vec<String>,
    pub(crate) package_json_info_cache: Arc<InfoCache>,
}

impl Default for ResolutionData {
    /// The Go `&ResolutionData{}` zero value (all fields nil/empty).
    fn default() -> Self {
        ResolutionData {
            compiler_options: Arc::new(CompilerOptions::default()),
            typings_location: RootedDirectoryPath::default(),
            project_name: String::new(),
            extra_extensions: Vec::new(),
            package_json_info_cache: Arc::new(InfoCache::new(
                tsc_tspath::CaseSensitivity::CaseSensitive,
            )),
        }
    }
}

/// `func newResolutionData(opts ResolverOptions) *ResolutionData`
pub(crate) fn new_resolution_data(opts: &ResolverOptions) -> ResolutionData {
    ResolutionData {
        compiler_options: opts.compiler_options.clone(),
        typings_location: opts.typings_location.clone(),
        project_name: opts.project_name.clone(),
        extra_extensions: opts.extra_extensions.clone(),
        package_json_info_cache: opts
            .package_json_cache
            .clone()
            .unwrap_or_else(|| Arc::new(InfoCache::new(opts.host.fs().case_sensitivity()))),
    }
}

/// `type ResolverOptions struct`
///
/// PORT: lives here (rather than resolver.rs) so `new_resolution_data` can
/// borrow it; `Host` is `Arc<dyn ResolutionHost>` for shared ownership.
#[derive(Clone)]
pub struct ResolverOptions {
    pub host: Arc<dyn crate::types::ResolutionHost>,
    pub compiler_options: Arc<CompilerOptions>,
    pub typings_location: RootedDirectoryPath,
    pub project_name: String,
    pub extra_extensions: Vec<String>,
    pub package_json_cache: Option<Arc<InfoCache>>,
}

impl ResolutionData {
    /// `func (c *ResolutionData) Clone() *ResolutionData`
    ///
    /// Clone copies the package-json cache table without copying its entries
    /// (entries are shared `Arc`s, as in Go).
    pub fn clone(&self) -> ResolutionData {
        ResolutionData {
            compiler_options: self.compiler_options.clone(),
            typings_location: self.typings_location.clone(),
            project_name: self.project_name.clone(),
            extra_extensions: self.extra_extensions.clone(),
            package_json_info_cache: Arc::new((*self.package_json_info_cache).clone()),
        }
    }

    /// `func (c *ResolutionData) PackageJsonCacheEntries(f func(key tspath.PathKey, value *packagejson.InfoCacheEntry) bool)`
    pub fn package_json_cache_entries(&self, f: impl FnMut(PathKey, Arc<InfoCacheEntry>) -> bool) {
        self.package_json_info_cache.range(f);
    }
}

/// `func getRedirectConfigName(redirect ResolvedProjectReference) tspath.RootedFilePath`
pub(crate) fn get_redirect_config_name(
    redirect: Option<&dyn ResolvedProjectReference>,
) -> RootedFilePath {
    match redirect {
        None => RootedFilePath::default(),
        Some(redirect) => redirect.config_name().clone(),
    }
}
