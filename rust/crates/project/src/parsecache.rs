// Ported from tsc/internal/project/parsecache.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::{Arc, Mutex};

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::{Node, NodeId, Uint128};
use tsc_compiler::file_loader::DuplicateSourceFile;
use tsc_contentmapper::{ParsedSourceFile, SourceFiles};
use tsc_core::core;
use tsc_core::scriptkind::ScriptKind;
use tsc_locale::Locale;

use crate::overlayfs::FileHandle;
use crate::refcountcache::{RefCountCache, RefCountCacheOptions};

/// `xxh3.Hash128(b)` — Go's `xxh3.Uint128` is `{Lo, Hi}` uint64 halves;
/// `xxhash_rust` returns the same digest as a `u128`.
pub fn hash128(bytes: &[u8]) -> Uint128 {
    let h = xxhash_rust::xxh3::xxh3_128(bytes);
    Uint128 {
        lo: h as u64,
        hi: (h >> 64) as u64,
    }
}

/// `xxh3.HashString128(s)`.
pub fn hash_string_128(s: &str) -> Uint128 {
    hash128(s.as_bytes())
}

/// `ParseCacheKey`.
#[derive(Clone)]
pub struct ParseCacheKey {
    pub source_file_parse_options: SourceFileParseOptions,
    pub script_kind: ScriptKind,
    pub hash: Uint128,
}

impl PartialEq for ParseCacheKey {
    fn eq(&self, other: &Self) -> bool {
        self.source_file_parse_options.file_name == other.source_file_parse_options.file_name
            && self.source_file_parse_options.path_key == other.source_file_parse_options.path_key
            && self.source_file_parse_options.external_module_indicator_options.jsx
                == other
                    .source_file_parse_options
                    .external_module_indicator_options
                    .jsx
            && self.source_file_parse_options.external_module_indicator_options.force
                == other
                    .source_file_parse_options
                    .external_module_indicator_options
                    .force
            && self.script_kind == other.script_kind
            && self.hash == other.hash
    }
}

impl Eq for ParseCacheKey {}

impl std::hash::Hash for ParseCacheKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.source_file_parse_options.file_name.hash(state);
        self.source_file_parse_options.path_key.hash(state);
        self.source_file_parse_options
            .external_module_indicator_options
            .jsx
            .hash(state);
        self.source_file_parse_options
            .external_module_indicator_options
            .force
            .hash(state);
        self.script_kind.hash(state);
        self.hash.hash(state);
    }
}

/// `NewParseCacheKey`.
pub fn new_parse_cache_key(
    options: SourceFileParseOptions,
    hash: Uint128,
    script_kind: ScriptKind,
) -> ParseCacheKey {
    let script_kind = if script_kind == ScriptKind::Unknown {
        core::ensure_script_kind_from_file_name(&options.file_name)
    } else {
        script_kind
    };
    ParseCacheKey {
        source_file_parse_options: options,
        hash,
        script_kind,
    }
}

/// `ContentMappedParseCacheKey` identifies the complete output bundle for one
/// mapped input. Hash folds the original content, mapper transform identity,
/// and diagnostic locale together.
#[derive(Clone)]
pub struct ContentMappedParseCacheKey {
    pub source_file_parse_options: SourceFileParseOptions,
    pub hash: Uint128,
}

impl PartialEq for ContentMappedParseCacheKey {
    fn eq(&self, other: &Self) -> bool {
        self.source_file_parse_options.file_name == other.source_file_parse_options.file_name
            && self.source_file_parse_options.path_key == other.source_file_parse_options.path_key
            && self.source_file_parse_options.external_module_indicator_options.jsx
                == other
                    .source_file_parse_options
                    .external_module_indicator_options
                    .jsx
            && self.source_file_parse_options.external_module_indicator_options.force
                == other
                    .source_file_parse_options
                    .external_module_indicator_options
                    .force
            && self.hash == other.hash
    }
}

impl Eq for ContentMappedParseCacheKey {}

impl std::hash::Hash for ContentMappedParseCacheKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.source_file_parse_options.file_name.hash(state);
        self.source_file_parse_options.path_key.hash(state);
        self.source_file_parse_options
            .external_module_indicator_options
            .jsx
            .hash(state);
        self.source_file_parse_options
            .external_module_indicator_options
            .force
            .hash(state);
        self.hash.hash(state);
    }
}

/// `contentMappedParseCacheKey`.
pub fn content_mapped_parse_cache_key(
    options: SourceFileParseOptions,
    raw_hash: Uint128,
    transform_identity: Uint128,
    diagnostic_locale: &Locale,
) -> ContentMappedParseCacheKey {
    let mut buf = Vec::with_capacity(32 + diagnostic_locale.to_string().len());
    buf.extend_from_slice(&raw_hash.hi.to_le_bytes());
    buf.extend_from_slice(&raw_hash.lo.to_le_bytes());
    buf.extend_from_slice(&transform_identity.hi.to_le_bytes());
    buf.extend_from_slice(&transform_identity.lo.to_le_bytes());
    buf.extend_from_slice(diagnostic_locale.to_string().as_bytes());
    ContentMappedParseCacheKey {
        source_file_parse_options: options,
        hash: hash128(&buf),
    }
}

/// `parseCacheKeyForFile` reconstructs the ordinary parse-cache key for a
/// source file held by a program.
pub fn parse_cache_key_for_file(nodes: &[Node], file: NodeId) -> ParseCacheKey {
    let file = nodes[file].as_source_file();
    new_parse_cache_key(file.parse_options().clone(), file.hash, file.script_kind)
}

/// `contentMappedParseCacheKeyForFile`.
pub fn content_mapped_parse_cache_key_for_file(
    nodes: &[Node],
    file: NodeId,
) -> ContentMappedParseCacheKey {
    let file = nodes[file].as_source_file();
    ContentMappedParseCacheKey {
        source_file_parse_options: file.content_mapper_parse_options(),
        hash: file.hash,
    }
}

/// `parseCacheKeyForDuplicate` reconstructs an ordinary parse-cache key for a
/// deduplicated source file.
pub fn parse_cache_key_for_duplicate(file: &DuplicateSourceFile) -> ParseCacheKey {
    new_parse_cache_key(file.parse_options.clone(), file.hash, file.script_kind)
}

/// `contentMappedParseCacheKeyForDuplicate`.
pub fn content_mapped_parse_cache_key_for_duplicate(
    file: &DuplicateSourceFile,
) -> ContentMappedParseCacheKey {
    ContentMappedParseCacheKey {
        source_file_parse_options: file.content_mapper_parse_options.clone(),
        hash: file.hash,
    }
}

/// `ParseCache` — `RefCountCache[ParseCacheKey, *ast.SourceFile, FileHandle]`.
///
/// PORT: `*ast.SourceFile` becomes `Arc<Mutex<ParsedSourceFile>>` — the shared
/// heap pointer is an `Arc`, and the mutex stands in for Go's unstructured
/// sharing of the parsed file (binding mutates the arena in place in Go; in
/// the Rust port binding happens in the program's arena — see PORT note in
/// `new_parse_cache`).
pub type ParseCache =
    RefCountCache<ParseCacheKey, Arc<Mutex<ParsedSourceFile>>, Arc<dyn FileHandle>>;

/// `NewParseCache`.
///
/// The cache automatically handles reference counting and eviction.
/// Entries with zero references are removed unless `disable_deletion` is set
/// on the options (used for testing).
pub fn new_parse_cache(options: RefCountCacheOptions) -> ParseCache {
    RefCountCache::new(options, |key: &ParseCacheKey, fh: &Arc<dyn FileHandle>| {
        let (file, mut nodes) = tsc_parser::parse_source_file(
            key.source_file_parse_options.clone(),
            fh.content(),
            key.script_kind,
        );
        nodes[file].as_source_file_mut().hash = fh.hash();
        // PORT: Go ran `binder.BindSourceFile(file)` here, marking the cached
        // file as already-bound for reuse across snapshots. The Rust binder
        // appends into the program's global `Vec<Symbol>`, so binding is
        // deferred to `Program::bind_source_files`/`get_bind_diagnostics`,
        // which bind per-file arenas on demand.
        Arc::new(Mutex::new(ParsedSourceFile { file, nodes }))
    })
}

/// `ContentMappedParseCache`.
///
/// One reference owns the canonical file and all supplemental files as a
/// bundle. Callers ref and deref the canonical file only.
///
/// PORT: Go embeds `*RefCountCache[...]` with a panicking `parse`, forcing
/// callers through `AcquireOrError`; here the wrapper only exposes
/// `acquire_or_error`/`deref`/`has`/`ref_`.
pub struct ContentMappedParseCache {
    inner: RefCountCache<ContentMappedParseCacheKey, Arc<Mutex<SourceFiles>>, ()>,
}

/// `NewContentMappedParseCache`.
pub fn new_content_mapped_parse_cache(options: RefCountCacheOptions) -> ContentMappedParseCache {
    ContentMappedParseCache {
        inner: RefCountCache::new(options, |_, ()| {
            panic!("content-mapped source files must be produced with acquire_or_error")
        }),
    }
}

impl ContentMappedParseCache {
    /// `AcquireOrError` — see [`RefCountCache::acquire_or_error`]. `produce`
    /// runs `transform_and_parse` (and applies the content hash) at the call
    /// site.
    pub fn acquire_or_error<E>(
        &self,
        identity: ContentMappedParseCacheKey,
        produce: impl FnOnce() -> Result<SourceFiles, E>,
    ) -> Result<Arc<Mutex<SourceFiles>>, E> {
        self.inner
            .acquire_or_error(identity, || produce().map(|files| Arc::new(Mutex::new(files))))
    }

    /// `Deref` — release one reference on the canonical-file bundle.
    pub fn deref(&self, identity: &ContentMappedParseCacheKey) {
        self.inner.deref(identity);
    }

    /// `Has`.
    pub fn has(&self, identity: &ContentMappedParseCacheKey) -> bool {
        self.inner.has(identity)
    }

    /// `Ref`.
    pub fn ref_(&self, identity: &ContentMappedParseCacheKey) {
        self.inner.ref_(identity);
    }
}
