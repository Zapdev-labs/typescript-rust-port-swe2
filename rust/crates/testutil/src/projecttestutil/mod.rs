// Ported from tsc/internal/testutil/projecttestutil/projecttestutil.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `testing.T` conventions (see crate root): `BaselineLogs`'s Go `t.Name()`
// becomes a `test_name` parameter and `t.Error` becomes `Err(Error)`.
// `t.Cleanup(session.Close)` has no equivalent — callers keep or drop the
// returned `Arc<Session>` and invoke `close` themselves (the fixtures in
// `autoimporttestutil` do so from `Drop`).
//
// PORT: `TypesRegistryConfig` is a `BTreeMap` so `TypesRegistryConfigText`
// is deterministic; Go iterates a `map[string]string` once under
// `sync.Once`, so its order (and the written file content) is randomized
// per process — no Go test can depend on the ordering.

//go:generate npx hereby generate:projecttestutil

pub mod clientmock;
pub mod npmexecutormock;

pub use clientmock::ClientMock;
pub use npmexecutormock::NpmExecutorMock;

use std::collections::BTreeMap;
use std::sync::{Arc, LazyLock, OnceLock};

use rustc_hash::FxHashMap;
use tsc_bundled as bundled;
use tsc_core::context::{self, Context};
use tsc_glob as glob;
use tsc_lsproto::{DocumentUri, PositionEncodingKind};
use tsc_project::session::{self, Session, SessionInit, SessionOptions};
use tsc_project_logging::{self as logging, TestLogger};
use tsc_tspath::{self as tspath, PathKey, RootedDirectoryPath, RootedPath};
use tsc_vfs::iovfs::FsWithSys;
use tsc_vfs::{Vfs, osvfs, vfstest};

use crate::baseline;
use crate::Error;
use crate::projecttestutil::npmexecutormock::NpmInstallResult;

/// `const TestTypingsLocation`.
pub const TEST_TYPINGS_LOCATION: &str = "/home/src/Library/Caches/typescript";

static TEST_TYPINGS_DIRECTORY: LazyLock<RootedDirectoryPath> =
    LazyLock::new(|| tspath::rooted_directory_path_from_normalized(TEST_TYPINGS_LOCATION));

/// `var TestTypingsDirectory`.
pub fn test_typings_directory() -> RootedDirectoryPath {
    TEST_TYPINGS_DIRECTORY.clone()
}

/// `type TypingsInstallerOptions struct`.
#[derive(Default)]
pub struct TypingsInstallerOptions {
    pub types_registry: Vec<String>,
    pub package_to_file: FxHashMap<String, String>,
}

/// `type SessionUtils struct`.
///
/// PORT: `fs`, `client`, `npmExecutor`, and `logger` are `Arc` because the
/// same values are shared with the session's `SessionInit` (Go shares the
/// pointers). `tiOptions`/`fsFromFileMap` are `Option` for Go's nil.
pub struct SessionUtils {
    current_directory: RootedDirectoryPath,
    fs_from_file_map: Option<Arc<dyn Vfs>>,
    fs: Arc<dyn Vfs>,
    client: Arc<ClientMock>,
    npm_executor: Arc<NpmExecutorMock>,
    ti_options: Option<Arc<TypingsInstallerOptions>>,
    logger: Arc<TestLogger>,
}

impl SessionUtils {
    /// `func (h *SessionUtils) FsFromFileMap() iovfs.FsWithSys`
    ///
    /// PORT: `None` when the session was built on the real FS
    /// ([setup_with_real_fs]); otherwise the `Vfs` value produced by
    /// `vfstest::from_map` unwrapped to `dyn FsWithSys` (Go's
    /// `fsFromFileMap.(iovfs.FsWithSys)` assertion — panic on failure, as Go).
    pub fn fs_from_file_map(&self) -> Option<&dyn FsWithSys> {
        self.fs_from_file_map.as_ref().map(|fs| {
            fs.as_fs_with_sys()
                .expect("FS from file map is not an iovfs.FsWithSys")
        })
    }

    /// `func (h *SessionUtils) Client() *ClientMock`
    pub fn client(&self) -> &Arc<ClientMock> {
        &self.client
    }

    /// `func (h *SessionUtils) NpmExecutor() *NpmExecutorMock`
    pub fn npm_executor(&self) -> &Arc<NpmExecutorMock> {
        &self.npm_executor
    }

    /// `func (h *SessionUtils) SetupNpmExecutorForTypingsInstaller()`
    pub fn setup_npm_executor_for_typings_installer(&self) {
        let Some(ti_options) = self.ti_options.clone() else {
            return;
        };

        let fs = self.fs.clone();
        *self.npm_executor.npm_install_func.lock().unwrap() =
            Some(Box::new(move |_ctx: &Context, current_directory: &RootedDirectoryPath, package_names: &[String]| -> NpmInstallResult {
                // packageNames is actually npmInstallArgs due to interface misnaming
                let npm_install_args = package_names;
                let len_npm_install_args = npm_install_args.len();
                if len_npm_install_args < 3 {
                    return Err(format!(
                        "unexpected npm install: {} {:?}",
                        current_directory.as_string(),
                        npm_install_args
                    )
                    .into());
                }

                if len_npm_install_args == 3 && npm_install_args[2] == "types-registry@latest" {
                    // Write typings file
                    let content = create_types_registry_file_content(&ti_options);
                    return fs
                        .write_file(
                            &current_directory
                                .resolve_file("node_modules/types-registry/index.json"),
                            &content,
                        )
                        .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
                            Box::new(e)
                        })
                        .map(|()| Vec::new());
                }

                // Find the packages: they start at index 2 and continue until we hit a flag starting with --
                let mut package_end = len_npm_install_args;
                for (i, arg) in npm_install_args.iter().enumerate().skip(2) {
                    if arg.starts_with("--") {
                        package_end = i;
                        break;
                    }
                }

                for at_types_package_ts in &npm_install_args[2..package_end] {
                    // @types/packageName@TsVersionToUse
                    let mut at_types_package = at_types_package_ts.as_str();
                    // Remove version suffix
                    if let Some(version_index) = at_types_package.rfind('@') {
                        // "@types/".length is 7, so version @ must be after
                        if version_index > 6 {
                            at_types_package = &at_types_package[..version_index];
                        }
                    }
                    // Extract package name from @types/packageName
                    let package_base_name = &at_types_package[7..]; // Remove "@types/" prefix
                    let Some(content) = ti_options.package_to_file.get(package_base_name) else {
                        return Err(format!("content not provided for {package_base_name}").into());
                    };
                    fs.write_file(
                        &current_directory.resolve_file(&format!(
                            "node_modules/@types/{package_base_name}/index.d.ts"
                        )),
                        content,
                    )
                    .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
                        Box::new(e)
                    })?;
                }
                Ok(Vec::new())
            }));
    }

    /// `func (h *SessionUtils) PathKey(fileName string) tspath.PathKey`
    pub fn path_key(&self, file_name: &str) -> PathKey {
        self.fs
            .case_sensitivity()
            .path_key(&tspath::to_rooted_path(file_name, &self.current_directory))
    }

    /// `func (h *SessionUtils) PathKeyForPath(path tspath.RootedPath) tspath.PathKey`
    pub fn path_key_for_path(&self, path: &RootedPath) -> PathKey {
        self.fs.case_sensitivity().path_key(path)
    }

    /// `func (h *SessionUtils) FS() vfs.FS`
    pub fn fs(&self) -> &Arc<dyn Vfs> {
        &self.fs
    }

    /// WatchesFile reports whether any registered file watcher would match the
    /// given file path. It handles both absolute glob patterns and relative
    /// patterns with a base URI according to the test file system's case
    /// sensitivity.
    pub fn watches_file(&self, file_path: &str) -> bool {
        let case_sensitivity = self.fs.case_sensitivity();
        let file_name = tspath::to_rooted_file_path(file_path, &self.current_directory);
        let calls = self.client.calls();
        for call in &calls.watch_files {
            for watcher in &call.watchers {
                if let Some(pattern) = &watcher.glob_pattern.pattern {
                    let mut pattern = pattern.clone();
                    let mut path = file_name.as_string().to_string();
                    if !case_sensitivity.is_case_sensitive() {
                        pattern = case_sensitivity.canonicalize(&pattern).into_owned();
                        path = case_sensitivity.canonicalize(&path).into_owned();
                    }
                    if let Ok(g) = glob::parse(&pattern) {
                        if g.matches(&path) {
                            return true;
                        }
                    }
                } else if let Some(rp) = &watcher.glob_pattern.relative_pattern {
                    let uri = rp
                        .base_uri
                        .uri
                        .as_ref()
                        .expect("relative pattern baseUri must be a URI");
                    let base_dir = tspath::rooted_directory_path_from_path(
                        DocumentUri(uri.0.clone()).file_name().as_path(),
                    );
                    if let Some(relative_path) =
                        case_sensitivity.relative_file_path_from_directory(&base_dir, &file_name)
                    {
                        let mut pattern = rp.pattern.clone();
                        let mut relative_path = relative_path;
                        if !case_sensitivity.is_case_sensitive() {
                            pattern = case_sensitivity.canonicalize(&pattern).into_owned();
                            relative_path = case_sensitivity.canonical_relative_path(&relative_path);
                        }
                        if let Ok(g) = glob::parse(&pattern) {
                            if g.matches(relative_path.as_string()) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// `func (h *SessionUtils) Logs() string`
    pub fn logs(&self) -> String {
        self.logger.to_string()
    }

    /// `func (h *SessionUtils) BaselineLogs(t *testing.T)`
    ///
    /// PORT: `t.Name()` becomes the `test_name` parameter; `t.Error` becomes
    /// `Err`.
    pub fn baseline_logs(&self, test_name: &str) -> Result<(), Error> {
        baseline::run(
            &format!("{test_name}.log"),
            &self.logs(),
            &baseline::Options {
                subfolder: "project".to_string(),
                ..Default::default()
            },
        )
    }
}

/// `func TypesRegistryConfigText() string`
pub fn types_registry_config_text() -> &'static str {
    static TEXT: OnceLock<String> = OnceLock::new();
    TEXT.get_or_init(|| {
        let mut result = String::new();
        for (key, value) in types_registry_config().iter() {
            if !result.is_empty() {
                result.push(',');
            }
            result.push_str(&format!("\n      \"{key}\": \"{value}\""));
        }
        result
    })
}

/// `func TypesRegistryConfig() map[string]string`
///
/// PORT: `BTreeMap` for deterministic iteration (see the module note).
pub fn types_registry_config() -> &'static BTreeMap<String, String> {
    static CONFIG: OnceLock<BTreeMap<String, String>> = OnceLock::new();
    CONFIG.get_or_init(|| {
        BTreeMap::from([
            ("latest".to_string(), "1.3.0".to_string()),
            ("ts2.0".to_string(), "1.0.0".to_string()),
            ("ts2.1".to_string(), "1.0.0".to_string()),
            ("ts2.2".to_string(), "1.2.0".to_string()),
            ("ts2.3".to_string(), "1.3.0".to_string()),
            ("ts2.4".to_string(), "1.3.0".to_string()),
            ("ts2.5".to_string(), "1.3.0".to_string()),
            ("ts2.6".to_string(), "1.3.0".to_string()),
            ("ts2.7".to_string(), "1.3.0".to_string()),
        ])
    })
}

/// `func (h *SessionUtils) createTypesRegistryFileContent() string`
///
/// PORT: a free function over `ti_options` (the `Arc` snapshot captured by
/// the npm-install closure) instead of a method on `SessionUtils`.
fn create_types_registry_file_content(ti_options: &TypingsInstallerOptions) -> String {
    let mut builder = String::new();
    builder.push_str("{\n  \"entries\": {");
    for (index, entry) in ti_options.types_registry.iter().enumerate() {
        append_types_registry_config(&mut builder, index, entry);
    }
    let mut index = ti_options.types_registry.len();
    for key in ti_options.package_to_file.keys() {
        if !ti_options.types_registry.contains(key) {
            append_types_registry_config(&mut builder, index, key);
            index += 1;
        }
    }
    builder.push_str("\n  }\n}");
    builder
}

/// `func (h *SessionUtils) appendTypesRegistryConfig(builder, index, entry)`
fn append_types_registry_config(builder: &mut String, index: usize, entry: &str) {
    if index > 0 {
        builder.push(',');
    }
    builder.push_str(&format!(
        "\n    \"{entry}\": {{{}\n    }}",
        types_registry_config_text()
    ));
}

/// `func Setup(files map[string]any) (*project.Session, *SessionUtils)`
pub fn setup<I, K, F>(files: I) -> (Arc<Session>, SessionUtils)
where
    I: IntoIterator<Item = (K, F)>,
    K: Into<String>,
    F: Into<vfstest::TestFile>,
{
    setup_with_typings_installer(files, TypingsInstallerOptions::default())
}

/// `func SetupWithRealFS() (*project.Session, *SessionUtils)`
pub fn setup_with_real_fs() -> (Arc<Session>, SessionUtils) {
    let fs = bundled::wrap_fs(osvfs::fs());
    let client_mock = Arc::new(ClientMock::default());
    let npm_executor_mock = Arc::new(NpmExecutorMock::default());
    let wd = std::env::current_dir().unwrap_or_else(|err| panic!("{err}"));
    let wd = wd.to_string_lossy();

    let logger = Arc::new(logging::new_test_logger());
    let session_utils = SessionUtils {
        current_directory: tspath::rooted_directory_path_from_absolute(&wd),
        fs_from_file_map: None,
        fs: fs.clone(),
        client: client_mock.clone(),
        npm_executor: npm_executor_mock.clone(),
        ti_options: None,
        logger: logger.clone(),
    };

    (
        session::new_session(SessionInit {
            background_ctx: Context::background(),
            fs,
            client: Some(client_mock),
            npm_executor: Some(npm_executor_mock),
            logger: Some(logger),
            options: Arc::new(SessionOptions {
                current_directory: tspath::rooted_directory_path_from_absolute(&wd),
                default_library_path: bundled::lib_path(),
                position_encoding: PositionEncodingKind::UTF8,
                watch_enabled: true,
                logging_enabled: true,
                push_diagnostics_enabled: true,
                ..Default::default()
            }),
            spawner: None,
            content_mapper_logger: None,
            parse_cache: None,
            content_mapped_parse_cache: None,
        }),
        session_utils,
    )
}

/// `func SetupWithOptions(files map[string]any, options *project.SessionOptions) (*project.Session, *SessionUtils)`
///
/// PORT: `options` is owned (`None` is Go's nil).
pub fn setup_with_options<I, K, F>(
    files: I,
    options: Option<SessionOptions>,
) -> (Arc<Session>, SessionUtils)
where
    I: IntoIterator<Item = (K, F)>,
    K: Into<String>,
    F: Into<vfstest::TestFile>,
{
    setup_with_options_and_typings_installer(files, options, Some(TypingsInstallerOptions::default()))
}

/// `func SetupWithTypingsInstaller(files map[string]any, tiOptions *TypingsInstallerOptions) (*project.Session, *SessionUtils)`
///
/// PORT: `ti_options` is owned (`None` is Go's nil).
pub fn setup_with_typings_installer<I, K, F>(
    files: I,
    ti_options: TypingsInstallerOptions,
) -> (Arc<Session>, SessionUtils)
where
    I: IntoIterator<Item = (K, F)>,
    K: Into<String>,
    F: Into<vfstest::TestFile>,
{
    setup_with_options_and_typings_installer(files, None, Some(ti_options))
}

/// `func SetupWithOptionsAndTypingsInstaller(files map[string]any, options *project.SessionOptions, tiOptions *TypingsInstallerOptions) (*project.Session, *SessionUtils)`
pub fn setup_with_options_and_typings_installer<I, K, F>(
    files: I,
    options: Option<SessionOptions>,
    ti_options: Option<TypingsInstallerOptions>,
) -> (Arc<Session>, SessionUtils)
where
    I: IntoIterator<Item = (K, F)>,
    K: Into<String>,
    F: Into<vfstest::TestFile>,
{
    let (init, session_utils) = get_session_init_options(files, options, ti_options);
    let session = session::new_session(init);
    (session, session_utils)
}

/// `func WithRequestID(ctx context.Context) context.Context`
pub fn with_request_id(ctx: &Context) -> Context {
    context::with_request_id(ctx, "0".to_string())
}

/// `func GetSessionInitOptions(files map[string]any, options *project.SessionOptions, tiOptions *TypingsInstallerOptions) (*project.SessionInit, *SessionUtils)`
pub fn get_session_init_options<I, K, F>(
    files: I,
    options: Option<SessionOptions>,
    ti_options: Option<TypingsInstallerOptions>,
) -> (SessionInit, SessionUtils)
where
    I: IntoIterator<Item = (K, F)>,
    K: Into<String>,
    F: Into<vfstest::TestFile>,
{
    let fs_from_file_map = vfstest::from_map(files, tspath::CaseSensitivity::CaseInsensitive);
    let fs = bundled::wrap_fs(fs_from_file_map.clone());
    let client_mock = Arc::new(ClientMock::default());
    let npm_executor_mock = Arc::new(NpmExecutorMock::default());
    let session_utils = SessionUtils {
        current_directory: tspath::rooted_directory_path_from_normalized("/"),
        fs_from_file_map: Some(fs_from_file_map),
        fs: fs.clone(),
        client: client_mock.clone(),
        npm_executor: npm_executor_mock.clone(),
        ti_options: ti_options.map(Arc::new),
        logger: Arc::new(logging::new_test_logger()),
    };

    // Configure the npm executor mock to handle typings installation
    session_utils.setup_npm_executor_for_typings_installer();

    // Use provided options or create default ones
    let options = options.unwrap_or_else(|| SessionOptions {
        current_directory: tspath::rooted_directory_path_from_normalized("/"),
        default_library_path: bundled::lib_path(),
        typings_location: test_typings_directory(),
        position_encoding: PositionEncodingKind::UTF8,
        watch_enabled: true,
        logging_enabled: true,
        push_diagnostics_enabled: true,
        ..Default::default()
    });

    (
        SessionInit {
            background_ctx: Context::background(),
            options: Arc::new(options),
            fs,
            client: Some(client_mock),
            npm_executor: Some(npm_executor_mock),
            logger: Some(session_utils.logger.clone()),
            spawner: None,
            content_mapper_logger: None,
            parse_cache: None,
            content_mapped_parse_cache: None,
        },
        session_utils,
    )
}
