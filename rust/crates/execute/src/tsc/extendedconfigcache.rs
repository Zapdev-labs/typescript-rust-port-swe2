// Ported from tsc/internal/execute/tsc/extendedconfigcache.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{Arc, Mutex, OnceLock};

use tsc_collections::SyncMap;
use tsc_tsoptions::tsconfigparsing::{ExtendedConfigCacheEntry, parse_extended_config};
use tsc_tspath::{PathKey, RootedFilePath};
use tsc_vfs::vfs::Vfs;

/// `extendedConfigCacheEntry` — the per-path mutex + cache slot; Go stores
/// `*ExtendedConfigCacheEntry` behind a `sync.Mutex` that serializes the
/// initial parse (`loaded` flag → `OnceLock`).
#[derive(Default)]
struct CacheEntry {
    lock: Mutex<()>,
    cell: OnceLock<ExtendedConfigCacheEntry>,
}

/// `type ExtendedConfigCache struct` — a minimal implementation of
/// `tsoptions.ExtendedConfigCache`. It is concurrency-safe, but stores cached
/// entries permanently. This implementation should not be used for
/// long-running processes where configuration changes over the course of
/// multiple compilations.
#[derive(Default)]
pub struct ExtendedConfigCache {
    m: SyncMap<PathKey, Arc<CacheEntry>>,
}

impl tsc_tsoptions::tsconfigparsing::ExtendedConfigCache for ExtendedConfigCache {
    /// `(e *ExtendedConfigCache) GetExtendedConfig`.
    fn get_extended_config(
        &self,
        file_name: &RootedFilePath,
        path: &PathKey,
        resolution_stack: &[PathKey],
        fs: &Arc<dyn Vfs>,
    ) -> Option<ExtendedConfigCacheEntry> {
        // `loadOrStoreNewLockedEntry` — the entry lock serializes the
        // initial parse exactly like Go's `entry.mu` held across
        // `ParseExtendedConfig`.
        let (entry, _loaded) = self
            .m
            .load_or_store(path.clone(), Arc::new(CacheEntry::default()));
        let _guard = entry.lock.lock().unwrap_or_else(|e| e.into_inner());
        Some(
            entry
                .cell
                .get_or_init(|| {
                    parse_extended_config(file_name, path, resolution_stack, fs, Some(self))
                })
                .clone(),
        )
    }
}
