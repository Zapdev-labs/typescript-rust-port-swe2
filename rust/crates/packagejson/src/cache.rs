// Ported from tsc/internal/packagejson/cache.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::ops::Deref;
use std::sync::{Arc, LazyLock, OnceLock};

use tsc_collections::{OrderedMap, SyncMap};
use tsc_core::version::{version, version_major_minor};
use tsc_diagnostics::{
    Expected_type_of_0_field_in_package_json_to_be_1_got_2, Message,
    X_package_json_does_not_have_a_0_field,
    X_package_json_does_not_have_a_typesVersions_entry_that_matches_version_0,
    X_package_json_has_a_typesVersions_entry_0_that_is_not_a_valid_semver_range,
    X_package_json_has_a_typesVersions_field_with_version_specific_path_mappings,
};
use tsc_semver::{Version, must_parse, try_parse_version_range};
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};

use crate::jsonvalue::{JSONValue, JSONValueType};
use crate::packagejson::Fields;

/// `var typeScriptVersion = semver.MustParse(core.Version())`
static TYPE_SCRIPT_VERSION: LazyLock<Version> = LazyLock::new(|| must_parse(version()));

/// `type diagnosticAndArgs struct`
struct DiagnosticAndArgs {
    /// `message *diagnostics.Message`
    message: &'static Message,
    /// `args []any` — every message traced here takes string args only.
    args: Vec<String>,
}

/// `func(m *diagnostics.Message, args ...any)` — the trace sink threaded into
/// `GetVersionPaths` by the module resolvers (`getTraceFunc`).
///
/// PORT: Go args are `[]any`, but every call site here traces string args
/// only, so the callback takes `&[String]`.
pub type TraceFunc = dyn FnMut(&'static Message, &[String]);

/// `type PackageJson struct`
#[derive(Default)]
pub struct PackageJson {
    /// `Fields` (embedded)
    pub fields: Fields,
    /// `Parseable bool` — the cache entry was loadable, even if invalid
    pub parseable: bool,
    /// PORT: `versionPaths`, `versionTraces`, and `once sync.Once` fold into
    /// one `OnceLock` — Go lazily fills the two fields exactly once inside
    /// `once.Do`; `OnceLock::get_or_init` is the same compute-once primitive.
    version_state: OnceLock<VersionState>,
}

/// PORT: the once-computed result of `GetVersionPaths` (Go stores the two
/// fields on `PackageJson` behind `sync.Once`).
struct VersionState {
    version_paths: VersionPaths,
    version_traces: Vec<DiagnosticAndArgs>,
}

// Go promotes the embedded `Fields` — `p.Fields.X` and `p.X` alike.
impl Deref for PackageJson {
    type Target = Fields;

    fn deref(&self) -> &Fields {
        &self.fields
    }
}

impl PackageJson {
    /// `func (p *PackageJson) GetVersionPaths(trace func(m *diagnostics.Message, args ...any)) VersionPaths`
    ///
    /// PORT: `trace` mirrors the optional Go trace func — `None` is the Go
    /// `nil`.
    pub fn get_version_paths(&self, mut trace: Option<&mut TraceFunc>) -> VersionPaths {
        let state = self.version_state.get_or_init(|| {
            let mut version_traces: Vec<DiagnosticAndArgs> = Vec::new();
            let mut version_paths = VersionPaths::default();
            'done: {
                if self.fields.types_versions.type_ == JSONValueType::NotPresent {
                    version_traces.push(DiagnosticAndArgs {
                        message: &X_package_json_does_not_have_a_0_field,
                        args: vec!["typesVersions".to_string()],
                    });
                    break 'done;
                }
                if self.fields.types_versions.type_ != JSONValueType::Object {
                    version_traces.push(DiagnosticAndArgs {
                        message: &Expected_type_of_0_field_in_package_json_to_be_1_got_2,
                        args: vec![
                            "typesVersions".to_string(),
                            "object".to_string(),
                            self.fields.types_versions.type_.to_string(),
                        ],
                    });
                    break 'done;
                }
                version_traces.push(DiagnosticAndArgs {
                    message:
                        &X_package_json_has_a_typesVersions_field_with_version_specific_path_mappings,
                    args: Vec::new(),
                });
                for (key, value) in self.fields.types_versions.as_object().entries() {
                    let (key_range, ok) = try_parse_version_range(key);
                    if !ok {
                        version_traces.push(DiagnosticAndArgs {
                            message:
                                &X_package_json_has_a_typesVersions_entry_0_that_is_not_a_valid_semver_range,
                            args: vec![key.clone()],
                        });
                        continue;
                    }
                    if key_range.test(Some(&TYPE_SCRIPT_VERSION)) {
                        if value.type_ != JSONValueType::Object {
                            version_traces.push(DiagnosticAndArgs {
                                message:
                                    &Expected_type_of_0_field_in_package_json_to_be_1_got_2,
                                args: vec![
                                    format!("typesVersions['{key}']"),
                                    "object".to_string(),
                                    value.type_.to_string(),
                                ],
                            });
                            break 'done;
                        }
                        version_paths = VersionPaths {
                            version: key.clone(),
                            // PORT: Go's `pathsJSON` aliases the OrderedMap
                            // inside `p.Fields.TypesVersions`; `Arc` shares
                            // the same read-only map without a per-call clone.
                            paths_json: Some(Arc::new(value.as_object().clone())),
                            paths: None,
                        };
                        break 'done;
                    }
                }
                version_traces.push(DiagnosticAndArgs {
                    message:
                        &X_package_json_does_not_have_a_typesVersions_entry_that_matches_version_0,
                    args: vec![version_major_minor().to_string()],
                });
            }
            VersionState {
                version_paths,
                version_traces,
            }
        });
        if let Some(trace) = &mut trace {
            for msg in &state.version_traces {
                trace(msg.message, &msg.args);
            }
        }
        state.version_paths.clone()
    }
}

/// `type VersionPaths struct`
#[derive(Clone, Debug, Default)]
pub struct VersionPaths {
    /// `Version string`
    pub version: String,
    paths_json: Option<Arc<OrderedMap<String, JSONValue>>>,
    paths: Option<OrderedMap<String, Vec<String>>>,
}

impl VersionPaths {
    /// `func (v *VersionPaths) Exists() bool`
    ///
    /// PORT: Go's `v != nil` check is expressed by callers holding
    /// `Option<VersionPaths>`/`Option<&VersionPaths>`.
    pub fn exists(&self) -> bool {
        !self.version.is_empty() && self.paths_json.is_some()
    }

    /// `func (v *VersionPaths) GetPaths() *collections.OrderedMap[string, []string]`
    pub fn get_paths(&mut self) -> Option<&OrderedMap<String, Vec<String>>> {
        if !self.exists() {
            return None;
        }
        if self.paths.is_none() {
            let paths_json = self.paths_json.as_ref().unwrap();
            let mut paths = OrderedMap::with_size_hint(paths_json.size());
            for (key, value) in paths_json.entries() {
                if value.type_ != JSONValueType::Array {
                    continue;
                }
                let array = value.as_array();
                let mut slice = vec![String::new(); array.len()];
                for (i, path) in array.iter().enumerate() {
                    if path.type_ != JSONValueType::String {
                        continue;
                    }
                    slice[i] = path.as_string().to_string();
                }
                paths.set(key.clone(), slice);
            }
            self.paths = Some(paths);
        }
        self.paths.as_ref()
    }
}

/// `type PackageDirectory struct`
#[derive(Clone, PartialEq, Eq)]
pub struct PackageDirectory {
    /// `name` is the presentation path of the directory
    name: RootedDirectoryPath,
    /// `key` is the canonical path of the directory.
    /// It will be in canonical form and have no trailing slashes.
    key: PathKey,
}

impl PackageDirectory {
    /// `func NewPackageDirectory(directory tspath.RootedDirectoryPath, caseSensitivity tspath.CaseSensitivity) PackageDirectory`
    ///
    /// Construct a new package directory from a path.
    /// The name is the presentation path, the key is canonical path.
    ///
    /// Use `NewPackageDirectory` instead of creating a `PackageDirectory`
    /// struct directly, unless the caller is `InfoCache.PackageDirectory` or
    /// `PackageDirectory.Parent`.
    pub fn new(
        directory: RootedDirectoryPath,
        case_sensitivity: CaseSensitivity,
    ) -> PackageDirectory {
        PackageDirectory {
            name: directory.clone(),
            key: case_sensitivity.path_key(&directory.as_path()),
        }
    }

    /// `func (p PackageDirectory) AsDirectoryPath() tspath.RootedDirectoryPath`
    ///
    /// The presentation path of the directory.
    pub fn as_directory_path(&self) -> &RootedDirectoryPath {
        &self.name
    }

    /// `func (p PackageDirectory) PathKey() tspath.PathKey`
    ///
    /// The canonical path of the directory.
    /// It will be in canonical form and have no trailing slashes.
    pub fn path_key(&self) -> &PathKey {
        &self.key
    }

    /// `func (p PackageDirectory) ResolveFile(path string) tspath.RootedFilePath`
    pub fn resolve_file(&self, path: &str) -> RootedFilePath {
        self.name.resolve_file(path)
    }

    /// `func (p PackageDirectory) String() string`
    ///
    /// PORT: implemented via `fmt::Display` (`to_string()`); `String()` is
    /// Go's `fmt.Stringer` contract.
    /// See also the `Display` impl below.
    fn string(&self) -> &str {
        self.name.as_string()
    }

    /// `func (p PackageDirectory) Parent() PackageDirectory`
    pub fn parent(&self) -> PackageDirectory {
        let parent_name = self.name.as_path().directory();
        let parent_key = self.key.parent();
        PackageDirectory {
            name: parent_name,
            key: parent_key,
        }
    }
}

impl fmt::Display for PackageDirectory {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.string())
    }
}

/// `func ForEachAncestorDirectoryStoppingAtGlobalCache[T any](globalCache tspath.RootedDirectoryPath, directory PackageDirectory, callback func(directory PackageDirectory) (T, bool)) T`
///
/// PORT: the callback borrows the directory (`&PackageDirectory`); Go copies
/// it by value. `globalCache` is likewise borrowed.
pub fn for_each_ancestor_directory_stopping_at_global_cache<T: Default>(
    global_cache: &RootedDirectoryPath,
    directory: PackageDirectory,
    mut callback: impl FnMut(&PackageDirectory) -> (T, bool),
) -> T {
    let mut directory = directory;
    loop {
        let (result, stop) = callback(&directory);
        if stop {
            return result;
        }
        // Not checking key here since we assume the canonicalized global cache
        // path and directory will be on the same casing system. The name check
        // is necessary for correctness.
        if directory.as_directory_path() == global_cache {
            return T::default();
        }
        let parent = directory.parent();
        if parent == directory {
            return T::default();
        }
        directory = parent;
    }
}

/// `type InfoCacheEntry struct`
///
/// PORT: `Contents` is `*PackageJson` in Go — `Option<Arc<PackageJson>>`
/// shares the same read-only value cheaply and stays `Sync` for `SyncMap`.
#[derive(Clone)]
pub struct InfoCacheEntry {
    /// `PackageDirectory PackageDirectory`
    pub package_directory: PackageDirectory,
    /// `DirectoryExists bool`
    pub directory_exists: bool,
    /// `Contents *PackageJson`
    pub contents: Option<Arc<PackageJson>>,
}

impl InfoCacheEntry {
    /// `func (p *InfoCacheEntry) Exists() bool`
    ///
    /// PORT: nil-receiver safety moves to the caller —
    /// `entry.map_or(false, |e| e.exists())`.
    pub fn exists(&self) -> bool {
        self.contents.is_some()
    }

    /// `func (p *InfoCacheEntry) GetContents() *PackageJson`
    ///
    /// PORT: returns the shared `Arc` clone; the Go nil-receiver case is the
    /// caller's `Option<Arc<InfoCacheEntry>>`.
    pub fn get_contents(&self) -> Option<Arc<PackageJson>> {
        self.contents.clone()
    }

    /// `func (p *InfoCacheEntry) WithPackageDirectory(dir PackageDirectory) *InfoCacheEntry`
    ///
    /// Returns a shallow copy of the cache entry with the package directory
    /// updated to the correct presentation path.
    ///
    /// PORT: `self: &Arc<Self>` lets the unchanged case return the same
    /// pointer — `cache.set`/`cache.get` return `*InfoCacheEntry` in Go.
    pub fn with_package_directory(
        self: &Arc<Self>,
        package_directory: PackageDirectory,
    ) -> Arc<InfoCacheEntry> {
        if self.package_directory == package_directory {
            return Arc::clone(self);
        }
        Arc::new(InfoCacheEntry {
            package_directory,
            directory_exists: self.directory_exists,
            contents: self.contents.clone(),
        })
    }
}

/// `type InfoCache struct`
///
/// Cache is a map from canonical paths of directories to their package.json
/// contents.
///
/// PORT: `SyncMap[tspath.PathKey, *InfoCacheEntry]` →
/// `SyncMap<PathKey, Arc<InfoCacheEntry>>`.
#[derive(Clone)]
pub struct InfoCache {
    /// The package.json cache. This can be shared between different
    /// program instances, and cleaned up via tsbuildinfo.
    ///
    ///  * `Get` on a packageDirectory returns the contents of
    ///    the package.json file, or nil if the file does not exist.
    ///  * `Set` on a packageDirectory returns the cache entry.
    cache: SyncMap<PathKey, Arc<InfoCacheEntry>>,
    case_sensitivity: CaseSensitivity,
}

impl InfoCache {
    /// `func NewInfoCache(caseSensitivity tspath.CaseSensitivity) *InfoCache`
    pub fn new(case_sensitivity: CaseSensitivity) -> InfoCache {
        InfoCache {
            cache: SyncMap::new(),
            case_sensitivity,
        }
    }

    /// `func (p *InfoCache) CaseSensitivity() tspath.CaseSensitivity`
    pub fn case_sensitivity(&self) -> CaseSensitivity {
        self.case_sensitivity
    }

    /// `func (p *InfoCache) PackageDirectory(directory tspath.RootedDirectoryPath) PackageDirectory`
    pub fn package_directory(&self, directory: RootedDirectoryPath) -> PackageDirectory {
        PackageDirectory::new(directory, self.case_sensitivity)
    }

    /// `func (p *InfoCache) Get(directory PackageDirectory) *InfoCacheEntry`
    ///
    /// PORT: Go nil result → `None`.
    pub fn get(&self, directory: &PackageDirectory) -> Option<Arc<InfoCacheEntry>> {
        self.cache.load(directory.path_key())
    }

    /// `func (p *InfoCache) Set(directory PackageDirectory, info *InfoCacheEntry) *InfoCacheEntry`
    ///
    /// Sets the package directory to the cache entry, or returns the
    /// existing entry if it already exists.
    ///
    /// PORT: `&PackageDirectory` for the borrow — Go copies the struct.
    /// `info` is `*InfoCacheEntry` in Go → `Arc<InfoCacheEntry>`.
    pub fn set(
        &self,
        directory: PackageDirectory,
        info: Arc<InfoCacheEntry>,
    ) -> Arc<InfoCacheEntry> {
        self.cache.load_or_store(directory.key, info).0
    }

    /// `func (p *InfoCache) Range(f func(key tspath.PathKey, value *InfoCacheEntry) bool)`
    pub fn range(&self, f: impl FnMut(PathKey, Arc<InfoCacheEntry>) -> bool) {
        self.cache.range(f);
    }
}
