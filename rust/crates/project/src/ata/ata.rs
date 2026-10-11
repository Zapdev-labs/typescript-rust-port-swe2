// Ported from tsc/internal/project/ata/ata.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::{Arc, Mutex, Once};

use rustc_hash::FxHashMap;
use serde::Deserialize;
use tsc_collections::{Set, SyncMap};
use tsc_core::context::Context;
use tsc_core::options_generated::{
    CompilerOptions, ModuleKind, ModuleResolutionKind, TypeAcquisition,
};
use tsc_core::semaphore::{LimitedSemaphore, new_limited_semaphore};
use tsc_core::version::{version, version_major_minor};
use tsc_core::workgroup::{ThrottleGroup, new_throttle_group};
use tsc_json as json;
use tsc_module::{self as module, DefaultResolver, ResolutionHost, ResolverOptions};
use tsc_project_logging::Logger;
use tsc_semver as semver;
use tsc_tspath::{
    RootedDirectoryPath, RootedFilePath, RootedPath,
};
use tsc_vfs::Vfs;

use super::discovertypings::discover_typings;
use super::validatepackagename::{
    render_package_name_validation_failure, validate_package_name, NameValidationResult,
};

/// `type TypingsInfo struct`
#[derive(Clone)]
pub struct TypingsInfo {
    pub type_acquisition: Arc<TypeAcquisition>,
    pub compiler_options: Arc<CompilerOptions>,
    pub unresolved_imports: Option<Set<String>>,
}

impl TypingsInfo {
    /// `func (ti TypingsInfo) Equals(other TypingsInfo) bool`
    pub fn equals(&self, other: &TypingsInfo) -> bool {
        TypeAcquisition::equals(
            Some(self.type_acquisition.as_ref()),
            Some(other.type_acquisition.as_ref()),
        ) && self.compiler_options.get_allow_js() == other.compiler_options.get_allow_js()
            && Set::equals(
                self.unresolved_imports.as_ref(),
                other.unresolved_imports.as_ref(),
            )
    }
}

/// `type CachedTyping struct`
#[derive(Clone)]
pub struct CachedTyping {
    pub typings_location: RootedFilePath,
    pub version: semver::Version,
}

/// `type TypingsInstallerOptions struct`
pub struct TypingsInstallerOptions {
    pub typings_location: RootedDirectoryPath,
    pub throttle_limit: i32,
}

/// `type NpmExecutor interface`
///
/// PORT: `([]byte, error)` becomes `Result<Vec<u8>, ...>`; the error is boxed
/// so implementors may return any error type.
pub trait NpmExecutor: Send + Sync {
    fn npm_install(
        &self,
        ctx: &Context,
        cwd: &RootedDirectoryPath,
        args: &[String],
    ) -> Result<Vec<u8>, Box<dyn std::error::Error + Send + Sync>>;
}

/// `type TypingsInstaller struct`
pub struct TypingsInstaller {
    typings_location: RootedDirectoryPath,
    fs: Arc<dyn Vfs>,
    npm_executor: Arc<dyn NpmExecutor>,

    init_once: Once,

    package_name_to_typing_location: SyncMap<String, Arc<CachedTyping>>,
    missing_typings_set: SyncMap<String, bool>,

    types_registry: Mutex<FxHashMap<String, FxHashMap<String, String>>>,

    install_run_count: AtomicI32,
    concurrency_semaphore: LimitedSemaphore,
}

/// `type resolutionHost struct`
struct ResolutionHostImpl {
    fs: Arc<dyn Vfs>,
    current_directory: RootedDirectoryPath,
}

impl ResolutionHost for ResolutionHostImpl {
    fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }

    fn get_current_directory(&self) -> RootedDirectoryPath {
        self.current_directory.clone()
    }
}

/// `func NewTypingsInstaller(options *TypingsInstallerOptions, fs vfs.FS, npmExecutor NpmExecutor) *TypingsInstaller`
pub fn new_typings_installer(
    options: &TypingsInstallerOptions,
    fs: Arc<dyn Vfs>,
    npm_executor: Arc<dyn NpmExecutor>,
) -> TypingsInstaller {
    TypingsInstaller {
        typings_location: options.typings_location.clone(),
        fs,
        npm_executor,
        init_once: Once::new(),
        package_name_to_typing_location: SyncMap::new(),
        missing_typings_set: SyncMap::new(),
        types_registry: Mutex::new(FxHashMap::default()),
        install_run_count: AtomicI32::new(0),
        concurrency_semaphore: new_limited_semaphore(options.throttle_limit),
    }
}

/// `type ProjectID interface { fmt.Stringer }`
pub trait ProjectId: fmt::Display {}
impl<T: fmt::Display> ProjectId for T {}

/// `const tsVersionToUse = "latest"`
const TS_VERSION_TO_USE: &str = "latest";

/// `type TypingsInstallRequest struct`
pub struct TypingsInstallRequest {
    pub project_id: String,
    pub typings_info: TypingsInfo,
    pub file_names: Vec<RootedFilePath>,
    pub project_root_path: RootedDirectoryPath,
    pub fs: Arc<dyn Vfs>,
    pub logger: Arc<dyn Logger>,
}

/// `type TypingsInstallResult struct`
pub struct TypingsInstallResult {
    pub typings_files: Vec<RootedFilePath>,
    pub files_to_watch: Vec<RootedPath>,
}

impl TypingsInstaller {
    /// `func (ti *TypingsInstaller) IsKnownTypesPackageName(...) bool`
    pub fn is_known_types_package_name(
        &self,
        name: &str,
        fs: &Arc<dyn Vfs>,
        logger: &dyn Logger,
    ) -> bool {
        // We want to avoid looking this up in the registry as that is expensive. So first check that it's actually an NPM package.
        let (validation_result, _, _) = validate_package_name(name);
        if validation_result != NameValidationResult::NameOk {
            return false;
        }
        // Strada did this lazily - is that needed here to not waiting on and returning false on first request
        self.init(&Context::background(), fs, logger);
        self.types_registry.lock().unwrap().contains_key(name)
    }

    /// `func (ti *TypingsInstaller) InstallTypings(ctx context.Context, request *TypingsInstallRequest) (*TypingsInstallResult, error)`
    pub fn install_typings(
        &self,
        ctx: &Context,
        request: &TypingsInstallRequest,
    ) -> Result<TypingsInstallResult, String> {
        let result = self.discover_and_install_typings(ctx, request);
        match result {
            Ok(mut result) => {
                result.typings_files.sort();
                result.files_to_watch.sort();
                request.logger.log(format_args!(
                    "ATA:: Got install request for: {}",
                    request.project_id
                ));
                Ok(result)
            }
            Err(err) => Err(err),
        }
    }

    /// `func (ti *TypingsInstaller) discoverAndInstallTypings(...)`
    fn discover_and_install_typings(
        &self,
        ctx: &Context,
        request: &TypingsInstallRequest,
    ) -> Result<TypingsInstallResult, String> {
        self.init(ctx, &request.fs, &*request.logger);

        let (cached_typing_paths, new_typing_names, files_to_watch) = discover_typings(
            &request.fs,
            &*request.logger,
            &request.typings_info,
            &request.file_names,
            &request.project_root_path,
            &self.package_name_to_typing_location,
            &self.types_registry.lock().unwrap(),
        );

        let request_id = self.install_run_count.fetch_add(1, Ordering::SeqCst) + 1;
        // install typings
        if !new_typing_names.is_empty() {
            let filtered_typings = self.filter_typings(&*request.logger, &new_typing_names);
            if !filtered_typings.is_empty() {
                let typings_files = self.install_typings_impl(
                    ctx,
                    request_id,
                    cached_typing_paths,
                    &filtered_typings,
                    &request.logger,
                )?;
                return Ok(TypingsInstallResult {
                    typings_files,
                    files_to_watch,
                });
            }
            request.logger.log(format_args!(
                "ATA:: All typings are known to be missing or invalid - no need to install more typings"
            ));
        } else {
            request.logger.log(format_args!(
                "ATA:: No new typings were requested as a result of typings discovery"
            ));
        }

        Ok(TypingsInstallResult {
            typings_files: cached_typing_paths,
            files_to_watch,
        })
        // !!! sheetal events to send
        // this.event(response, "setTypings");
    }

    /// `func (ti *TypingsInstaller) installTypings(...)`
    fn install_typings_impl(
        &self,
        ctx: &Context,
        request_id: i32,
        currently_cached_typings: Vec<RootedFilePath>,
        filtered_typings: &[String],
        logger: &Arc<dyn Logger>,
    ) -> Result<Vec<RootedFilePath>, String> {
        // !!! sheetal events to send
        // send progress event — see Go source for commented-out event bodies.

        let scoped_typings: Vec<String> = filtered_typings
            .iter()
            .map(|package_name| format!("@types/{package_name}@{TS_VERSION_TO_USE}"))
            .collect();

        if let Some(package_names) = self.install_worker(ctx, request_id, &scoped_typings, logger) {
            logger.log(format_args!("ATA:: Installed typings {package_names:?}"));
            let mut installed_typing_files: Vec<RootedFilePath> = Vec::new();
            let resolver = DefaultResolver::new(ResolverOptions {
                host: Arc::new(ResolutionHostImpl {
                    fs: self.fs.clone(),
                    current_directory: self.typings_location.clone(),
                }),
                compiler_options: Arc::new(CompilerOptions {
                    module_resolution: ModuleResolutionKind::NodeNext,
                    ..Default::default()
                }),
                typings_location: RootedDirectoryPath::default(),
                project_name: String::new(),
                extra_extensions: Vec::new(),
                package_json_cache: None,
            });
            for package_name in filtered_typings {
                let typing_file = self.typing_to_file_name(&resolver, package_name);
                let Some(typing_file) = typing_file else {
                    logger.log(format_args!(
                        "ATA:: Failed to find typing file for package '{package_name}'"
                    ));
                    self.missing_typings_set.store(package_name.clone(), true);
                    continue;
                };

                // packageName is guaranteed to exist in typesRegistry by filterTypings
                let types_registry = self.types_registry.lock().unwrap();
                let dist_tags = &types_registry[package_name];
                let use_version = dist_tags
                    .get(&format!("ts{}", version_major_minor()))
                    .unwrap_or_else(|| dist_tags.get("latest").expect("dist-tag 'latest'"));
                let new_version = semver::must_parse(use_version);
                drop(types_registry);
                let new_typing = CachedTyping {
                    typings_location: typing_file.clone(),
                    version: new_version,
                };
                self.package_name_to_typing_location
                    .store(package_name.clone(), Arc::new(new_typing));
                installed_typing_files.push(typing_file);
            }
            logger.log(format_args!(
                "ATA:: Installed typing files {installed_typing_files:?}"
            ));
            let mut all = currently_cached_typings;
            all.extend(installed_typing_files);
            return Ok(all);
        }

        logger.log(format_args!(
            "ATA:: install request failed, marking packages as missing to prevent repeated requests: {filtered_typings:?}"
        ));
        for typing in filtered_typings {
            self.missing_typings_set.store(typing.clone(), true);
        }

        Err("npm install failed".to_string())
    }

    /// `func (ti *TypingsInstaller) installWorker(...)`
    ///
    /// PORT: returns `Some(packageNames)` on success where Go returned
    /// `(packageNames, ok)`.
    fn install_worker(
        &self,
        ctx: &Context,
        request_id: i32,
        package_names: &[String],
        logger: &Arc<dyn Logger>,
    ) -> Option<Vec<String>> {
        logger.log(format_args!(
            "ATA:: #{request_id} with cwd: {} arguments: {package_names:?}",
            self.typings_location.as_string()
        ));
        // PORT: the throttled tasks run on spawned threads, so the install
        // callback must own its captures (Go closures capture pointers).
        let npm_executor = self.npm_executor.clone();
        let typings_location = self.typings_location.clone();
        let task_ctx = ctx.clone();
        let task_logger = logger.clone();
        let result = install_npm_packages(
            ctx,
            package_names,
            &self.concurrency_semaphore,
            Arc::new(move |package_names: &[String]| {
                let mut npm_args: Vec<String> = vec![
                    "install".to_string(),
                    "--ignore-scripts".to_string(),
                ];
                npm_args.extend(package_names.iter().cloned());
                npm_args.push("--save-dev".to_string());
                npm_args.push(format!("--user-agent=\"typesInstaller/{}\"", version()));
                match npm_executor.npm_install(&task_ctx, &typings_location, &npm_args) {
                    Err(err) => {
                        // Go logs the captured command output on failure, not
                        // the error itself; the executor bundles both into the
                        // boxed error's Display.
                        task_logger.log(format_args!("ATA:: Output is: {err}"));
                        Err(err.to_string())
                    }
                    Ok(_) => Ok(()),
                }
            }),
        );
        logger.log(format_args!("TI:: npm install #{request_id} completed"));
        result.ok().map(|_| package_names.to_vec())
    }

    /// `func (ti *TypingsInstaller) filterTypings(...) []string`
    fn filter_typings(&self, logger: &dyn Logger, typings_to_install: &[String]) -> Vec<String> {
        let mut result = Vec::new();
        for typing in typings_to_install {
            let typing_key = module::mangle_scoped_package_name(typing);
            if self.missing_typings_set.load(&typing_key).is_some() {
                logger.log(format_args!(
                    "ATA:: '{typing}':: '{typing_key}' is in missingTypingsSet - skipping..."
                ));
                continue;
            }
            let (validation_result, name, is_scope_name) = validate_package_name(typing);
            if validation_result != NameValidationResult::NameOk {
                // add typing name to missing set so we won't process it again
                self.missing_typings_set.store(typing_key.clone(), true);
                logger.log(format_args!(
                    "ATA:: {}",
                    render_package_name_validation_failure(
                        typing,
                        validation_result,
                        &name,
                        is_scope_name
                    )
                ));
                continue;
            }
            let types_registry = self.types_registry.lock().unwrap();
            let Some(types_registry_entry) = types_registry.get(&typing_key) else {
                drop(types_registry);
                logger.log(format_args!(
                    "ATA:: '{typing}':: Entry for package '{typing_key}' does not exist in local types registry - skipping..."
                ));
                continue;
            };
            let up_to_date = self
                .package_name_to_typing_location
                .load(&typing_key)
                .is_some_and(|typing_location| {
                    super::discovertypings::is_typing_up_to_date(
                        &typing_location,
                        types_registry_entry,
                    )
                });
            drop(types_registry);
            if up_to_date {
                logger.log(format_args!(
                    "ATA:: '{typing}':: '{typing_key}' already has an up-to-date typing - skipping..."
                ));
                continue;
            }
            result.push(typing_key);
        }
        result
    }

    /// `func (ti *TypingsInstaller) init(ctx, fs, logger)`
    fn init(&self, ctx: &Context, fs: &Arc<dyn Vfs>, logger: &dyn Logger) {
        // PORT: `initOnce` needs `ctx`/`fs`/`logger` at the call site; Once::
        // call_once captures them as in Go's sync.Once.Do closure.
        self.init_once.call_once(|| {
            logger.log(format_args!(
                "ATA:: Global cache location '{}'",
                self.typings_location.as_string()
            ));
            self.process_cache_location(fs, logger);
            self.ensure_typings_location_exists(fs, logger);
            logger.log(format_args!("ATA:: Updating types-registry@latest npm package..."));
            match self.npm_executor.npm_install(
                ctx,
                &self.typings_location,
                &[
                    "install".to_string(),
                    "--ignore-scripts".to_string(),
                    "types-registry@latest".to_string(),
                ],
            ) {
                Ok(_) => {
                    logger.log(format_args!("ATA:: Updated types-registry npm package"));
                }
                Err(err) => {
                    logger.log(format_args!(
                        "ATA:: Error updating types-registry package: {err}"
                    ));
                    // !!! sheetal events to send — see Go source.
                }
            }
            *self.types_registry.lock().unwrap() = self.load_types_registry_file(fs, logger);
        });
    }

    /// `func (ti *TypingsInstaller) processCacheLocation(fs, logger)`
    fn process_cache_location(&self, fs: &Arc<dyn Vfs>, logger: &dyn Logger) {
        logger.log(format_args!(
            "ATA:: Processing cache location {}",
            self.typings_location.as_string()
        ));
        let package_json = self.typings_location.resolve_file("package.json");
        let package_lock_json = self.typings_location.resolve_file("package-lock.json");
        logger.log(format_args!(
            "ATA:: Trying to find '{}'...",
            package_json.as_string()
        ));
        if fs.file_exists(&package_json) && fs.file_exists(&package_lock_json) {
            let (npm_config, npm_config_contents) =
                parse_npm_config_or_lock::<NpmConfig>(fs, &package_json);
            let (npm_lock, npm_lock_contents) =
                parse_npm_config_or_lock::<NpmLock>(fs, &package_lock_json);

            logger.log(format_args!(
                "ATA:: Loaded content of {}: {}",
                package_json.as_string(),
                npm_config_contents
            ));
            logger.log(format_args!(
                "ATA:: Loaded content of {}: {}",
                package_lock_json.as_string(),
                npm_lock_contents
            ));

            // !!! sheetal strada uses Node10
            let resolver = DefaultResolver::new(ResolverOptions {
                host: Arc::new(ResolutionHostImpl {
                    fs: self.fs.clone(),
                    current_directory: self.typings_location.clone(),
                }),
                compiler_options: Arc::new(CompilerOptions {
                    module_resolution: ModuleResolutionKind::NodeNext,
                    ..Default::default()
                }),
                typings_location: RootedDirectoryPath::default(),
                project_name: String::new(),
                extra_extensions: Vec::new(),
                package_json_cache: None,
            });
            if npm_config.dev_dependencies.is_some()
                && (npm_lock.packages.is_some() || npm_lock.dependencies.is_some())
            {
                let dev_dependencies = npm_config.dev_dependencies.clone().unwrap_or_default();
                for key in dev_dependencies.keys() {
                    let npm_lock_value = npm_lock
                        .packages
                        .as_ref()
                        .and_then(|packages| packages.get(&format!("node_modules/{key}")))
                        .or_else(|| {
                            npm_lock
                                .dependencies
                                .as_ref()
                                .and_then(|deps| deps.get(key))
                        });
                    let Some(npm_lock_value) = npm_lock_value else {
                        // if package in package.json but not package-lock.json, skip adding to cache so it is reinstalled on next use
                        continue;
                    };
                    // key is @types/<package name>
                    let package_name = tsc_tspath::get_base_file_name(key).to_string();
                    if package_name.is_empty() {
                        continue;
                    }
                    let Some(typing_file) = self.typing_to_file_name(&resolver, &package_name)
                    else {
                        self.missing_typings_set.store(package_name, true);
                        continue;
                    };
                    if let Some(existing_typing_file) =
                        self.package_name_to_typing_location.load(&package_name)
                    {
                        if existing_typing_file.typings_location == typing_file {
                            continue;
                        }
                        logger.log(format_args!(
                            "ATA:: New typing for package {package_name} from {} conflicts with existing typing file {}",
                            typing_file.as_string(),
                            existing_typing_file.typings_location.as_string()
                        ));
                    }
                    logger.log(format_args!(
                        "ATA:: Adding entry into typings cache: {package_name} => {}",
                        typing_file.as_string()
                    ));
                    let version_str = &npm_lock_value.version;
                    if version_str.is_empty() {
                        continue;
                    }
                    let new_version = semver::must_parse(version_str);
                    let new_typing = CachedTyping {
                        typings_location: typing_file,
                        version: new_version,
                    };
                    self.package_name_to_typing_location
                        .store(package_name, Arc::new(new_typing));
                }
            }
        }
        logger.log(format_args!(
            "ATA:: Finished processing cache location {}",
            self.typings_location.as_string()
        ));
    }

    /// `func (ti *TypingsInstaller) ensureTypingsLocationExists(fs, logger)`
    fn ensure_typings_location_exists(&self, fs: &Arc<dyn Vfs>, logger: &dyn Logger) {
        let npm_config_path = self.typings_location.resolve_file("package.json");
        logger.log(format_args!(
            "ATA:: Npm config file: {}",
            npm_config_path.as_string()
        ));

        if !fs.file_exists(&npm_config_path) {
            logger.log(format_args!(
                "ATA:: Npm config file: '{}' is missing, creating new one...",
                npm_config_path.as_string()
            ));
            if let Err(err) = fs.write_file(&npm_config_path, "{ \"private\": true }") {
                logger.log(format_args!("ATA:: Npm config file write failed: {err}"));
            }
        }
    }

    /// `func (ti *TypingsInstaller) typingToFileName(resolver, packageName) tspath.RootedFilePath`
    ///
    /// PORT: returns `Option` — Go's `""` means "not found".
    fn typing_to_file_name(
        &self,
        resolver: &DefaultResolver,
        package_name: &str,
    ) -> Option<RootedFilePath> {
        let containing_file = self.typings_location.resolve_file("index.d.ts");
        let (result, _diags) =
            resolver.resolve_module_name(package_name, &containing_file, ModuleKind::None, None);
        result.and_then(|r| {
            if r.is_resolved() {
                Some(r.resolved_file_name)
            } else {
                None
            }
        })
    }

    /// `func (ti *TypingsInstaller) loadTypesRegistryFile(fs, logger) map[string]map[string]string`
    fn load_types_registry_file(
        &self,
        fs: &Arc<dyn Vfs>,
        logger: &dyn Logger,
    ) -> FxHashMap<String, FxHashMap<String, String>> {
        let types_registry_file = self
            .typings_location
            .resolve_file("node_modules/types-registry/index.json");
        if let Some(types_registry_file_contents) = fs.read_file(&types_registry_file) {
            let entries: Result<
                FxHashMap<String, FxHashMap<String, FxHashMap<String, String>>>,
                _,
            > = json::unmarshal(types_registry_file_contents.as_bytes(), &[]);
            match entries {
                Ok(entries) => {
                    if let Some(types_registry) = entries.get("entries") {
                        return types_registry.clone();
                    }
                }
                Err(err) => {
                    logger.log(format_args!(
                        "ATA:: Error when loading types registry file '{}': {err}",
                        types_registry_file.as_string()
                    ));
                    return FxHashMap::default();
                }
            }
        } else {
            logger.log(format_args!(
                "ATA:: Error reading types registry file '{}'",
                types_registry_file.as_string()
            ));
        }
        FxHashMap::default()
    }
}

/// `func installNpmPackages(...) error`
///
/// PORT: `installPackages` is an `Arc` so each spawned task may hold its own
/// clone (Go captures the func value in the goroutine closure).
fn install_npm_packages(
    ctx: &Context,
    package_names: &[String],
    concurrency_semaphore: &LimitedSemaphore,
    install_packages: Arc<dyn Fn(&[String]) -> Result<(), String> + Send + Sync>,
) -> Result<(), String> {
    let tg: ThrottleGroup<String> =
        new_throttle_group(ctx, concurrency_semaphore.clone());

    let mut current_command_start = 0usize;
    let mut current_command_end = 0usize;
    let mut current_command_size = 100usize;

    for package_name in package_names {
        current_command_size += package_name.len() + 1;
        if current_command_size < 8000 {
            current_command_end += 1;
        } else {
            let packages = package_names[current_command_start..current_command_end].to_vec();
            let install_packages = install_packages.clone();
            tg.go(move || install_packages(&packages));
            current_command_start = current_command_end;
            current_command_size = 100 + package_name.len() + 1;
            current_command_end += 1;
        }
    }

    // Handle the final batch
    if current_command_start < package_names.len() {
        let packages = package_names[current_command_start..current_command_end].to_vec();
        let install_packages = install_packages.clone();
        tg.go(move || install_packages(&packages));
    }

    tg.wait()
}

/// `type npmConfig struct` / `type npmLock struct`
#[derive(Deserialize, Default)]
struct NpmConfig {
    #[serde(rename = "devDependencies")]
    dev_dependencies: Option<FxHashMap<String, serde_json::Value>>,
}

#[derive(Deserialize, Default)]
struct NpmDependencyEntry {
    version: String,
}

#[derive(Deserialize, Default)]
struct NpmLock {
    dependencies: Option<FxHashMap<String, NpmDependencyEntry>>,
    packages: Option<FxHashMap<String, NpmDependencyEntry>>,
}

/// `func parseNpmConfigOrLock[T](fs, logger, location, config) string`
///
/// PORT: returns `(parsed, rawContents)`; Go ignored the unmarshal error, so
/// parse failures yield `T::default()`.
fn parse_npm_config_or_lock<T: serde::de::DeserializeOwned + Default>(
    fs: &Arc<dyn Vfs>,
    location: &RootedFilePath,
) -> (T, String) {
    let contents = fs.read_file(location).unwrap_or_default();
    let parsed = json::unmarshal::<T>(contents.as_bytes(), &[]).unwrap_or_default();
    (parsed, contents)
}
