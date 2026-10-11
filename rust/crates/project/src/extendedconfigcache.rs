// Ported from tsc/internal/project/extendedconfigcache.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_ast::Uint128;
use tsc_tsoptions::tsconfigparsing::{self, ExtendedConfigCacheEntry};
use tsc_tspath::{PathKey, RootedFilePath};
use tsc_vfs::Vfs;

use crate::ownercache::OwnerCache;
use crate::snapshotfs::FileSource;

/// `ExtendedConfigParseArgs`.
pub struct ExtendedConfigParseArgs {
    pub file_name: RootedFilePath,
    pub content: String,
    pub fs: Arc<dyn FileSource>,
    pub config_fs: Arc<dyn Vfs>,
    pub resolution_stack: Vec<PathKey>,
    /// PORT: Go `tsoptions.ExtendedConfigCache` interface, nil-able.
    pub cache: Option<Arc<dyn tsconfigparsing::ExtendedConfigCache>>,
}

/// `ExtendedConfigCacheEntry` — Go embeds `*tsoptions.ExtendedConfigCacheEntry`.
#[derive(Clone)]
pub struct ProjectExtendedConfigCacheEntry {
    pub entry: ExtendedConfigCacheEntry,
    pub hash: Uint128,
}

impl std::ops::Deref for ProjectExtendedConfigCacheEntry {
    type Target = ExtendedConfigCacheEntry;

    fn deref(&self) -> &ExtendedConfigCacheEntry {
        &self.entry
    }
}

/// `ExtendedConfigCache` — `OwnerCache[tspath.PathKey, *ExtendedConfigCacheEntry, ExtendedConfigParseArgs]`.
///
/// PORT: `*ExtendedConfigCacheEntry` becomes `Arc<ExtendedConfigCacheEntry>`
/// (Go shares the entry pointer between owners).
pub type ExtendedConfigCache =
    OwnerCache<PathKey, Arc<ProjectExtendedConfigCacheEntry>, ExtendedConfigParseArgs>;

/// `NewExtendedConfigCache`.
pub fn new_extended_config_cache() -> ExtendedConfigCache {
    OwnerCache::new(
        |path: &PathKey, args: &ExtendedConfigParseArgs| {
            let entry = tsconfigparsing::parse_extended_config(
                &args.file_name,
                path,
                &args.resolution_stack,
                &args.config_fs,
                args.cache.as_deref(),
            );
            let result = ProjectExtendedConfigCacheEntry {
                hash: hash_extended_config(&entry, args),
                entry,
            };
            Arc::new(result)
        },
        Some(|_path: &PathKey,
              entry: &Arc<ProjectExtendedConfigCacheEntry>,
              args: &ExtendedConfigParseArgs| {
            entry.hash == Uint128::default()
                || entry.hash != hash_extended_config(&entry.entry, args)
        }),
    )
}

/// `hash` — `xxh3.New()` + `WriteString` + `Sum128` over the config content
/// and the contents of every extended file.
fn hash_extended_config(
    entry: &ExtendedConfigCacheEntry,
    args: &ExtendedConfigParseArgs,
) -> Uint128 {
    let mut hasher = xxhash_rust::xxh3::Xxh3::new();
    hasher.update(args.content.as_bytes());
    for file_name in entry.extended_file_names() {
        let Some(fh) = args.fs.get_file(&file_name) else {
            return Uint128::default();
        };
        hasher.update(fh.content().as_bytes());
    }
    let h = hasher.digest128();
    Uint128 {
        lo: h as u64,
        hi: (h >> 64) as u64,
    }
}
