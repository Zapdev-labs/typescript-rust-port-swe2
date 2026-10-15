// Ported from tsc/internal/fourslash/fourslash.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT conventions (shared with verify.rs / verify_baseline.rs /
// baselineutil.rs / statebaseline.rs / semantictokens.rs):
// - `*testing.T` is dropped everywhere: `t.Fatalf`/`t.Fatal`/`t.Errorf`/
//   `t.Error` panic; `t.Helper` is a no-op; `t.Skip` is an early return.
// - `NewFourslash(t, caps, content) (*FourslashTest, func())` becomes
//   `new_fourslash(test_name, test_path, caps, content) -> FourslashTest`;
//   the Go cleanup closure is `FourslashTest::close`. `t.Name()`/`runtime.
//   Caller` have no equivalent, so callers supply `test_name`/`test_path`
//   (or set `set_current_test_name` for baseline file naming).
// - `go-cmp`/`cmpopts` have no analog: equality is `PartialEq` + `Debug`
//   dumps; ignored fields are cleared before comparing (see verify.rs).
// - `*Marker`/`*RangeMarker`/`*scriptInfo` become `Rc` handles / values
//   following `crate::test_parser`; marker position updates rebuild the
//   `Rc`s under the same identity (see `edit_script_and_update_markers_worker`).
// - `MarkerOrRange` (the Go interface) is `Rc<dyn MarkerOrRange>`.
// - `f.client.SendRequest` returns `(Option<Message>, R, bool)` as in
//   Go; transport errors panic (there is no `testing.T` to report them).
//
// PORT(assumption): `tsc-lsp`'s `Server`/`ServerOptions` are still
// skeletons; this file assumes the snake_case Go API (`ServerOptions { cwd,
// fs, default_library_path, parse_cache, spawn, .. }`, `Server::session`,
// `Server::init_complete().recv()`), matching `lsptestutil`'s assumptions.

use std::cell::RefCell;
use std::fmt::Write as _;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

use rustc_hash::{FxHashMap, FxHashSet};
use serde::Serialize;
use serde::de::DeserializeOwned;
use tsc_bundled as bundled;
use tsc_collections::MultiMap;
use tsc_core::context::Context;
use tsc_core::core::{self as core, last_or_nil, stringify_json};
use tsc_core::options_generated::{CompilerOptions, JsxEmit, ScriptTarget};
use tsc_core::text::{TextPos, TextRange};
use tsc_core::textchange::TextChange;
use tsc_core::tristate::{TS_TRUE, TS_UNKNOWN};
use tsc_debug as debug;
use tsc_json as json;
use tsc_jsonrpc as jsonrpc;
use tsc_lsconv::{self as lsconv, LspLineMap, Script};
use tsc_lsproto::{
    self as lsproto, DocumentUri, Method, NotificationInfo, RequestInfo, RequestMessage,
    ResponseMessage,
};
use tsc_lsutil::{self as lsutil, UserPreferences};
use tsc_project as project;
use tsc_spanmap::Feature;
use tsc_stringutil as stringutil;
use tsc_testutil::baseline;
use tsc_testutil::harnessutil;
use tsc_tspath::{
    self as tspath, CaseSensitivity, RootedDirectoryPath, RootedFilePath, RootedPath,
};
use tsc_vfs::vfstest;
use tsc_vfs::Vfs;

pub(crate) use tsc_lsproto::compare_positions;

use crate::baselineutil::{self, BaselineCommand};
use crate::statebaseline::{StateBaseline, new_state_baseline};
use crate::test_parser::{self, Marker, MarkerOrRange, RangeMarker, TestData};

/// `FourslashTest` — Go `type FourslashTest struct`.
pub struct FourslashTest {
    /// `client *lsptestutil.LSPClient` — the Go field embeds the LSP client
    /// pointer directly; `send_request`/`send_notification` panic on
    /// transport errors (there is no `testing.T` to report them to).
    pub(crate) client: LspClient,
    close_client: Option<Box<dyn FnOnce() -> Result<(), tsc_testutil::Error> + Send>>,
    pub(crate) vfs: Arc<dyn Vfs>,

    pub(crate) test_data: TestData,
    pub(crate) baselines: FxHashMap<BaselineCommand, String>,
    /// `rangesByText *multimap.MultiMap[string, *RangeMarker]`
    pub(crate) ranges_by_text: Option<MultiMap<String, Rc<RangeMarker>>>,
    pub(crate) open_files: FxHashSet<RootedFilePath>,
    pub(crate) state_baseline: Option<StateBaseline>,

    /// `scriptInfos map[tspath.Path]*scriptInfo` — values, not pointers:
    /// reads hand out `&ScriptInfo` and all writes go through `&mut self`.
    pub(crate) script_infos: FxHashMap<RootedFilePath, ScriptInfo>,

    pub(crate) state_enable_formatting: bool,
    pub(crate) report_format_on_type_crash: bool,
    /// `userPreferences *lsutil.UserPreferences` — `Arc` so
    /// `self.user_preferences.as_ref()` yields `&UserPreferences` (Go `*`).
    pub(crate) user_preferences: Arc<UserPreferences>,
    /// Mirror of `user_preferences` read by the (Send+Sync) server-request
    /// handler; kept in sync by [`FourslashTest::configure`].
    user_preferences_shared: Arc<Mutex<Arc<UserPreferences>>>,
    pub(crate) current_caret_position: lsproto::Position,
    pub(crate) last_known_marker_name: Option<String>,
    pub(crate) active_filename: RootedFilePath,
    /// `selectionEnd *lsproto.Position`
    pub(crate) selection_end: Option<lsproto::Position>,

    /// `capabilities *lsproto.ClientCapabilities`
    pub(crate) capabilities: Option<lsproto::ClientCapabilities>,
    /// Whether this is a fourslash server test in Strada. !!! Remove once we
    /// don't need to diff baselines.
    pub(crate) is_strada_server: bool,

    // Semantic token configuration
    pub(crate) semantic_token_types: Vec<String>,
    pub(crate) semantic_token_modifiers: Vec<String>,
}

/// `lsptestutil.ServerRequestHandler` — handles server-initiated requests
/// (e.g., workspace/configuration), returning the response to send back.
///
/// PORT(skeleton): kept here so `handle_server_request` stays wired; the
/// real alias lands with `tsc_testutil::lsptestutil`.
type ServerRequestHandler =
    Arc<dyn Fn(&Context, &RequestMessage) -> Option<ResponseMessage> + Send + Sync>;

/// `(*lsptestutil.LSPClient)` — thin wrapper returning the Go
/// `(*Message, Resp, bool)` triple from `send_request` (transport errors
/// panic) and exposing `server()`.
///
/// PORT(skeleton): `tsc_testutil::lsptestutil` is gated on the `tsc_lsp`
/// port, which is still a skeleton, so this type wraps nothing — every
/// operation panics with `tsc-lsp server port pending` until it lands.
/// `new_lsp_client` below is the single point that materializes a client.
pub struct LspClient {
    _private: (),
}

impl LspClient {
    /// `client.SendRequest` — Go's triple; `Err` from the client becomes a
    /// panic (Go's `t.Fatal` equivalent).
    pub(crate) fn send_request<Params, Resp>(
        &self,
        _info: &RequestInfo<Params, Resp>,
        _params: Params,
    ) -> (Option<lsproto::Message>, Resp, bool)
    where
        Params: Serialize,
        Resp: DeserializeOwned + Default,
    {
        unimplemented!("tsc-lsp server port pending")
    }

    /// `client.SendNotification`.
    pub(crate) fn send_notification<Params>(
        &self,
        _info: &NotificationInfo<Params>,
        _params: Params,
    ) where
        Params: Serialize,
    {
        unimplemented!("tsc-lsp server port pending")
    }

    /// `client.Server`.
    pub(crate) fn server(&self) -> &LspServer {
        unimplemented!("tsc-lsp server port pending")
    }

    /// `client.SetCompilerOptionsForInferredProjects`.
    pub(crate) fn set_compiler_options_for_inferred_projects(&self, _options: &CompilerOptions) {
        unimplemented!("tsc-lsp server port pending")
    }
}

/// `lsp.Server` stand-in while `tsc_lsp` is a skeleton (see [LspClient]).
pub(crate) struct LspServer {
    _private: (),
}

impl LspServer {
    /// `(*Server).InitComplete` — the channel `initialize` waits on.
    pub(crate) fn init_complete(&self) -> &std::sync::mpsc::Receiver<()> {
        unimplemented!("tsc-lsp server port pending")
    }

    /// `(*Server).Session`.
    pub(crate) fn session(&self) -> &LspSession {
        unimplemented!("tsc-lsp server port pending")
    }
}

/// `project.Session` stand-in while `tsc_lsp` is a skeleton (see
/// [LspClient]).
pub(crate) struct LspSession {
    _private: (),
}

impl LspSession {
    /// `(*Session).Snapshot`.
    pub(crate) fn snapshot(&self) -> project::snapshot::Snapshot {
        unimplemented!("tsc-lsp server port pending")
    }
}

/// `type scriptInfo struct`.
pub struct ScriptInfo {
    pub(crate) file_name: RootedFilePath,
    pub content: String,
    pub(crate) line_map: LspLineMap,
    pub(crate) version: i32,
}

/// `type testConverters struct` — wraps `lsconv.Converters` (fourslash
/// scripts never carry a span map, so `to_lsp_*`/`from_lsp_*` are always a
/// single exact projection, which the helpers below assert).
pub(crate) struct TestConverters<'a> {
    pub(crate) converters: lsconv::Converters<'a>,
}

/// `newTestConverters`.
pub(crate) fn new_test_converters<'a>(converters: lsconv::Converters<'a>) -> TestConverters<'a> {
    TestConverters { converters }
}

impl TestConverters<'_> {
    /// `func (c *testConverters) PositionToLineAndCharacter`.
    pub(crate) fn position_to_line_and_character(
        &self,
        script: &dyn Script,
        position: TextPos,
    ) -> lsproto::Position {
        self.converters.to_lsp_position(script, position).0
    }

    /// `func (c *testConverters) LineAndCharacterToPosition` — normal
    /// scripts produce exactly one exact mapped position.
    pub(crate) fn line_and_character_to_position(
        &self,
        script: &dyn Script,
        position: lsproto::Position,
    ) -> TextPos {
        let mapped = self
            .converters
            .from_lsp_position(script, position, Feature::All);
        debug::assert_!(!mapped.is_empty(), "expected exactly one mapped position");
        mapped[0].position
    }

    /// `ToLSPRange` — asserts the single exact projection like the Go code.
    pub(crate) fn to_lsp_range(&self, script: &dyn Script, text_range: TextRange) -> lsproto::Range {
        self.converters.to_lsp_range(script, text_range).0
    }

    /// `FromLSPRange` — `len(...) == 1` assertion folded in.
    pub(crate) fn from_lsp_range(&self, script: &dyn Script, range: lsproto::Range) -> TextRange {
        let spans = self.converters.from_lsp_range(script, range, Feature::All);
        debug::assert_!(spans.len() == 1, "expected exactly one mapped span");
        spans[0].span
    }
}

/// `type textEditSpan struct`.
#[derive(Clone)]
pub(crate) struct TextEditSpan {
    pub(crate) start: i32,
    pub(crate) end: i32,
    pub(crate) length: i32,
}

/// `newScriptInfo`.
pub(crate) fn new_script_info(file_name: &str, content: &str) -> ScriptInfo {
    new_script_info_from_file_name(
        tspath::to_rooted_file_path(file_name, &root_dir()),
        content,
    )
}

/// `newScriptInfoFromFileName`.
pub(crate) fn new_script_info_from_file_name(
    file_name: RootedFilePath,
    content: &str,
) -> ScriptInfo {
    ScriptInfo {
        file_name,
        content: content.to_string(),
        line_map: lsconv::compute_lsp_line_starts(content.as_bytes()),
        version: 1,
    }
}

impl ScriptInfo {
    /// `(*scriptInfo).editContent`.
    pub(crate) fn edit_content(&mut self, change: &TextChange) {
        self.content = change.apply_to(&self.content);
        self.line_map = lsconv::compute_lsp_line_starts(self.content.as_bytes());
        self.version += 1;
    }

    /// `(*scriptInfo).GetLineContent`.
    pub(crate) fn get_line_content(&self, line: i32) -> &str {
        let num_lines = self.line_map.line_starts.len() as i32;
        if line < 0 || line >= num_lines {
            return "";
        }
        let start = self.line_map.line_starts[line as usize] as usize;
        let end = if line + 1 < num_lines {
            self.line_map.line_starts[line as usize + 1] as usize
        } else {
            self.content.len()
        };
        self.content[start..end].trim_end_matches(['\r', '\n'])
    }
}

/// `var _ lsconv.Script = (*scriptInfo)(nil)` — the reference impl so
/// `&ScriptInfo` works as `Script`/`MappedSpan<T>` via the `&T` blanket impl.
impl Script for ScriptInfo {
    fn file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    fn original_file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    fn text(&self) -> &[u8] {
        self.content.as_bytes()
    }

    fn span_map(&self) -> Option<Arc<tsc_spanmap::SpanMap>> {
        None
    }

    fn original_text(&self) -> &[u8] {
        self.content.as_bytes()
    }
}

/// `var rootDir` — by value so `&crate::fourslash::root_dir()` is a
/// `&RootedDirectoryPath` (tspath APIs take a reference).
pub(crate) fn root_dir() -> RootedDirectoryPath {
    test_parser::root_dir().clone()
}

/// The current test's name (`t.Name()` equivalent), set by `new_fourslash`;
/// used by `get_baseline_file_name`.
thread_local! {
    static CURRENT_TEST_NAME: RefCell<String> = const { RefCell::new(String::new()) };
}

/// Stores `t.Name()` for `get_base_file_name_from_test`.
pub(crate) fn set_current_test_name(name: &str) {
    CURRENT_TEST_NAME.with(|n| *n.borrow_mut() = name.to_string());
}

/// `getBaseFileNameFromTest` — the test name supplied to `new_fourslash`
/// (or `set_current_test_name`).
pub(crate) fn get_base_file_name_from_test() -> String {
    let test_name = CURRENT_TEST_NAME.with(|n| n.borrow().clone());
    let mut name = last_or_nil(
        &test_name.split('/').map(str::to_string).collect::<Vec<_>>(),
    )
    .unwrap_or_default();
    name = name.trim_start_matches("Test").to_string();
    name = String::from_utf8(stringutil::lower_first_char(name.as_bytes()))
        .expect("test name is not UTF-8");

    // Special case: TypeScript has "callHierarchyFunctionAmbiguity.N" with periods
    match name.as_str() {
        "callHierarchyFunctionAmbiguity1" => "callHierarchyFunctionAmbiguity.1".to_string(),
        "callHierarchyFunctionAmbiguity2" => "callHierarchyFunctionAmbiguity.2".to_string(),
        "callHierarchyFunctionAmbiguity3" => "callHierarchyFunctionAmbiguity.3".to_string(),
        "callHierarchyFunctionAmbiguity4" => "callHierarchyFunctionAmbiguity.4".to_string(),
        "callHierarchyFunctionAmbiguity5" => "callHierarchyFunctionAmbiguity.5".to_string(),
        _ => name,
    }
}

/// `var parseCache`.
///
/// PORT(skeleton): `ParseCache` embeds `Rc`s (`ParsedSourceFile`), so it is
/// not `Sync` and cannot live in a `static`. It is only consumed by the
/// `ServerOptions` stand-in for the still-skeleton `tsc_lsp` port; a `Box`
/// leak keeps the `&'static` shape until that lands.
fn parse_cache() -> &'static project::parsecache::ParseCache {
    Box::leak(Box::new(project::parsecache::new_parse_cache(
        project::refcountcache::RefCountCacheOptions {
            disable_deletion: true,
        },
    )))
}

/// `FourslashOptions`.
#[derive(Default)]
pub struct FourslashOptions {
    pub capabilities: Option<lsproto::ClientCapabilities>,
    pub content_mapper_spawner: Option<Arc<dyn tsc_contentmapper::Spawner>>,
    pub run_external_code: bool,
    /// Makes every textDocument/diagnostic request also emit the program and
    /// compare the diagnostics before and after emit, e.g. to catch ones
    /// added by the emit resolver.
    pub track_flaky_diagnostics: Option<lsproto::DiagnosticFlakeLogLevel>,
}

/// `NewFourslash` — `test_name` is the Go test's `t.Name()`, `test_path`
/// the `runtime.Caller(1)` path of the test file (currently unused, kept
/// for parity).
pub fn new_fourslash(
    test_name: &str,
    test_path: &str,
    capabilities: Option<lsproto::ClientCapabilities>,
    content: &str,
) -> FourslashTest {
    new_fourslash_worker(
        test_name,
        test_path,
        content,
        FourslashOptions {
            capabilities,
            ..Default::default()
        },
    )
}

/// `NewFourslashWithOptions`.
pub fn new_fourslash_with_options(
    test_name: &str,
    test_path: &str,
    content: &str,
    options: FourslashOptions,
) -> FourslashTest {
    new_fourslash_worker(test_name, test_path, content, options)
}

/// `lsp.ServerOptions` stand-in — only the fields `newFourslash`
/// populates, while `tsc_lsp` is a skeleton (see [LspClient]).
struct ServerOptions {
    #[allow(dead_code)]
    cwd: RootedDirectoryPath,
    #[allow(dead_code)]
    fs: Arc<dyn Vfs>,
    #[allow(dead_code)]
    default_library_path: RootedDirectoryPath,
    #[allow(dead_code)]
    parse_cache: &'static project::parsecache::ParseCache,
    #[allow(dead_code)]
    spawn: Option<Arc<dyn tsc_contentmapper::Spawner>>,
}

/// `lsptestutil::new_lsp_client` — PORT(skeleton): the `tsc_lsp` server is
/// still a skeleton, so materializing a client panics; fourslash tests
/// cannot run until it lands.
#[allow(clippy::type_complexity)]
fn new_lsp_client(
    _ctx: &Context,
    _options: ServerOptions,
    _on_server_request: Option<ServerRequestHandler>,
) -> (LspClient, Box<dyn FnOnce() -> Result<(), tsc_testutil::Error> + Send>) {
    unimplemented!("tsc-lsp server port pending")
}

/// `newFourslash`.
fn new_fourslash_worker(
    test_name: &str,
    _test_path: &str,
    content: &str,
    options: FourslashOptions,
) -> FourslashTest {
    set_current_test_name(test_name);
    if !bundled::EMBEDDED {
        // Without embedding, we'd need to read all of the lib files out
        // from disk into the MapFS. `t.Skip` has no Rust equivalent — the
        // constant is always true in the Rust port anyway.
        panic!("bundled files are not embedded");
    }

    let file_name = get_base_file_name_from_test() + tspath::EXTENSION_TS;
    let mut testfs: FxHashMap<String, vfstest::TestFile> = FxHashMap::default();
    let mut script_infos: FxHashMap<RootedFilePath, ScriptInfo> = FxHashMap::default();
    let test_data = test_parser::parse_test_data(content, &file_name)
        .unwrap_or_else(|e| panic!("{e}"));
    for file in &test_data.files {
        let file_path = file.file_name().clone();
        // Dynamic files (e.g., untitled:) shouldn't be added to the VFS
        if !file_path.is_dynamic() {
            testfs.insert(
                file_path.as_string().to_string(),
                file.content.clone().into(),
            );
        }
        script_infos.insert(
            file_path.clone(),
            new_script_info_from_file_name(file_path, &file.content),
        );
    }

    let root = root_dir();
    for (link, target) in &test_data.symlinks {
        let file_path = tspath::get_normalized_absolute_path(link, &root);
        testfs.insert(
            file_path.into_owned(),
            vfstest::symlink(&tspath::get_normalized_absolute_path(target, &root)).into(),
        );
    }

    // !!! use default compiler options for inferred project as base
    let mut compiler_options = CompilerOptions {
        skip_default_lib_check: TS_TRUE,
        target: ScriptTarget::LATEST_STANDARD,
        jsx: JsxEmit::Preserve,
        ..Default::default()
    };
    let mut harness_options = harnessutil::HarnessOptions {
        case_sensitivity: CaseSensitivity::CaseSensitive,
        current_directory: root_dir(),
        ..Default::default()
    };
    harnessutil::set_options_from_test_config(
        &test_data.global_options,
        &mut compiler_options,
        &mut harness_options,
        &root_dir(),
        true, /*allowUnknownOptions*/
    )
    .unwrap_or_else(|e| panic!("{e}"));
    if let Some(command_lines) = test_data.global_options.get("tsc") {
        if !command_lines.is_empty() {
            for command_line in command_lines.split(',') {
                let _args: Vec<String> =
                    command_line.split(' ').map(str::to_string).collect();
                // PORT(skeleton): `tsc_execute::tsctests` is `#[cfg(test)]`-
                // gated inside tsc-execute (dev-dependency cycle), so
                // `get_file_map_with_build` is unreachable from here; tests
                // using the `tsc` global option panic until it is exposed.
                unimplemented!("tsc-execute::tsctests get_file_map_with_build pending");
            }
        }
    }

    if let Some(reason) = harnessutil::skip_unsupported_compiler_options(&compiler_options) {
        panic!("unsupported compiler options: {reason}");
    }

    let fs_from_map = vfstest::from_map(
        testfs.iter().map(|(k, v)| (k.clone(), v.clone())),
        harness_options.case_sensitivity,
    );
    let fs = bundled::wrap_fs(fs_from_map.clone());

    let server_opts = ServerOptions {
        cwd: root_dir(),
        fs: fs.clone(),
        default_library_path: bundled::lib_path(),
        parse_cache: parse_cache(),
        spawn: options.content_mapper_spawner.clone(),
    };

    let user_preferences: Arc<UserPreferences> =
        Arc::new(lsutil::new_default_user_preferences());
    let user_preferences_shared: Arc<Mutex<Arc<UserPreferences>>> =
        Arc::new(Mutex::new(user_preferences.clone()));

    let handler_prefs = user_preferences_shared.clone();
    let handler: ServerRequestHandler =
        Arc::new(move |ctx: &Context, req: &RequestMessage| {
            handle_server_request(ctx, &handler_prefs, req)
        });

    let ctx = Context::background();
    let (client, close_client) = new_lsp_client(&ctx, server_opts, Some(handler));

    let mut f = FourslashTest {
        client,
        close_client: Some(close_client),
        vfs: fs,
        test_data,
        baselines: FxHashMap::default(),
        ranges_by_text: None,
        open_files: FxHashSet::default(),
        state_baseline: None,
        script_infos,
        state_enable_formatting: true,
        report_format_on_type_crash: true,
        user_preferences,
        user_preferences_shared,
        current_caret_position: lsproto::Position::default(),
        last_known_marker_name: None,
        active_filename: RootedFilePath::default(),
        selection_end: None,
        capabilities: None,
        is_strada_server: false,
        semantic_token_types: default_semantic_token_types(),
        semantic_token_modifiers: default_semantic_token_modifiers(),
    };

    // !!! temporary; remove when we have `handleDidChangeConfiguration`/implicit project config support
    // !!! replace with a proper request *after initialize*
    f.client
        .set_compiler_options_for_inferred_projects(&compiler_options);
    f.initialize(&options);

    if f.test_data.is_state_baselining_enabled() {
        // Single baseline, so initialize project state baseline too
        f.state_baseline = Some(new_state_baseline(
            fs_from_map
                .as_fs_with_sys()
                .expect("vfstest::from_map returns an FsWithSys"),
        ));
    } else {
        let files: Vec<RootedFilePath> = f
            .test_data
            .files
            .iter()
            .filter(|file| file.open)
            .map(|file| file.file_name().clone())
            .collect();
        for file_name in files {
            f.open_file(file_name);
        }
        f.active_filename = f.test_data.files[0].file_name().clone();
    }

    f
}

impl FourslashTest {
    /// `closeClient` + `verifyBaselines` — the `func()` returned by Go's
    /// `NewFourslash`. Consumes the harness; call once per test.
    pub fn close(mut self) {
        if let Some(close_client) = self.close_client.take() {
            if let Err(err) = close_client() {
                panic!("goroutine error: {err}");
            }
        }
        self.verify_baselines();
    }
}

impl Drop for FourslashTest {
    /// Best-effort client shutdown if the test never called
    /// [`FourslashTest::close`].
    fn drop(&mut self) {
        if let Some(close_client) = self.close_client.take() {
            let _ = close_client();
        }
    }
}

/// `handleServerRequest` handles requests initiated by the server (e.g.,
/// workspace/configuration).
fn handle_server_request(
    _ctx: &Context,
    user_preferences: &Arc<Mutex<Arc<UserPreferences>>>,
    req: &RequestMessage,
) -> Option<ResponseMessage> {
    match req.method.as_str() {
        m if m == Method::WorkspaceConfiguration.as_str() => {
            // Return current user preferences for each requested section.
            // The server requests multiple sections (js/ts, typescript,
            // javascript, editor); we return user preferences for "js/ts" and
            // nil for others.
            let prefs = user_preferences.lock().unwrap().clone();
            let params = req.unmarshal_params::<Option<lsproto::ConfigurationParams>>();
            let items = match params {
                Err(_) | Ok(None) => None,
                Ok(Some(p)) => p.items,
            };
            match items {
                None => Some(ResponseMessage {
                    id: req.id.clone(),
                    jsonrpc: req.jsonrpc.clone(),
                    result: Some(to_json_value(&vec![&*prefs])),
                    error: None,
                }),
                Some(items) => {
                    let mut results: Vec<serde_json::Value> = Vec::with_capacity(items.len());
                    for item in items {
                        if item.section.as_deref() == Some("js/ts") {
                            results.push(
                                serde_json::to_value(&*prefs)
                                    .expect("marshal user preferences"),
                            );
                        } else {
                            results.push(serde_json::Value::Null);
                        }
                    }
                    Some(ResponseMessage {
                        id: req.id.clone(),
                        jsonrpc: req.jsonrpc.clone(),
                        result: Some(to_json_value(&results)),
                        error: None,
                    })
                }
            }
        }
        m if m == Method::ClientRegisterCapability.as_str()
            || m == Method::ClientUnregisterCapability.as_str() =>
        {
            // Accept all capability (un)registrations
            Some(ResponseMessage {
                id: req.id.clone(),
                jsonrpc: req.jsonrpc.clone(),
                result: Some(to_json_value(&lsproto::Null)),
                error: None,
            })
        }
        // Unknown server request — `None` yields the default MethodNotFound.
        _ => None,
    }
}

/// Marshal `v` into an inbound `json::Value` (raw JSON), the same encoding
/// `RequestInfo::new_request_message` produces for params.
fn to_json_value<T: ?Sized + Serialize>(v: &T) -> json::Value {
    let bytes = json::marshal(v, &[]).expect("marshal response result");
    serde_json::value::RawValue::from_string(
        String::from_utf8(bytes).expect("marshal produced invalid UTF-8"),
    )
    .expect("marshal produced invalid JSON")
}

pub(crate) const SHOW_CODE_LENS_LOCATIONS_COMMAND_NAME: &str =
    "typescript.showCodeLensLocations";

impl FourslashTest {
    /// `(*FourslashTest).initialize`.
    fn initialize(&mut self, options: &FourslashOptions) {
        let initialization_options = lsproto::InitializationOptions {
            code_lens_show_locations_command_name: Some(
                SHOW_CODE_LENS_LOCATIONS_COMMAND_NAME.to_string(),
            ),
            track_flaky_diagnostics: options.track_flaky_diagnostics,
            run_external_code: options.run_external_code.then_some(true),
            ..Default::default()
        };
        let params = lsproto::InitializeParams {
            locale: Some("en-US".to_string()),
            initialization_options: Some(lsproto::InitializationOptionsOrNull {
                initialization_options: Some(initialization_options),
            }),
            capabilities: get_capabilities_with_defaults(options.capabilities.as_ref()),
            ..Default::default()
        };
        self.capabilities = params.capabilities.clone();
        let (resp, _result, ok) = self
            .client
            .send_request(&lsproto::INITIALIZE_INFO, Some(params));
        if !ok {
            panic!("Initialize request failed");
        }
        if let Some(resp) = resp {
            if let Some(error) = &resp.as_response().error {
                panic!("Initialize request returned error: {error}");
            }
        }
        self.client.send_notification(
            &lsproto::INITIALIZED_INFO,
            Some(lsproto::InitializedParams::default()),
        );

        // Wait for the initial configuration exchange to complete
        // The server will send workspace/configuration as part of handleInitialized
        let _ = self.client.server().init_complete().recv();
    }

    /// `(*FourslashTest).testConverters` — builds converters whose line-map
    /// lookup resolves against `script_infos` (Go creates them once in
    /// `newFourslash`; the lookup closure borrows `self` here instead).
    pub(crate) fn test_converters(&self) -> TestConverters<'_> {
        new_test_converters(lsconv::new_converters(
            lsproto::PositionEncodingKind::UTF8,
            |file_name: &RootedFilePath| {
                &self
                    .script_infos
                    .get(file_name)
                    .expect("script info not found for line map lookup")
                    .line_map
            },
        ))
    }

    /// `(*FourslashTest).sendRequest`.
    pub(crate) fn send_request<P, R>(
        &mut self,
        info: &RequestInfo<Option<P>, R>,
        params: P,
    ) -> R
    where
        P: Serialize,
        R: DeserializeOwned + Default,
    {
        self.send_request_and_baseline_worker(info, params, true)
    }

    /// `(*FourslashTest).sendRequestAndBaselineWorker`.
    pub(crate) fn send_request_and_baseline_worker<P, R>(
        &mut self,
        info: &RequestInfo<Option<P>, R>,
        params: P,
        baseline_projects: bool,
    ) -> R
    where
        P: Serialize,
        R: DeserializeOwned + Default,
    {
        let prefix = self.get_current_position_prefix();
        if baseline_projects {
            self.baseline_state();
        }
        let params = Some(params);
        self.baseline_request_or_notification(&info.method, &params);
        let (res_msg, result, result_ok) = self.client.send_request(info, params);
        if baseline_projects {
            self.baseline_state();
        }
        if !(info.method == Method::TextDocumentOnTypeFormatting
            && !self.report_format_on_type_crash)
        {
            let Some(res_msg) = res_msg else {
                panic!("{prefix}Nil response received for {} request", info.method);
            };
            let resp = res_msg.as_response();
            if let Some(error) = &resp.error {
                panic!("{prefix}{} request returned error: {error}", info.method);
            }
            if !result_ok {
                panic!(
                    "{prefix}Unexpected {} response type: {:?}, error: {:?}",
                    info.method, resp.result, resp.error
                );
            }
        }
        result
    }

    /// `(*FourslashTest).sendNotification`.
    pub(crate) fn send_notification<P>(&mut self, info: &NotificationInfo<Option<P>>, params: P)
    where
        P: Serialize,
    {
        if info.method != Method::TextDocumentDidChange {
            // This is called eg when doing typeText = which is series of edits and formatting - which becomes non deterministic "after state"
            // The notification can only guarantee before state and thats what it baselines, but in case of type it creates
            // multiple edits which results in getting different state -based on if the snapshot was updated or not at the time of formatting requests
            // So this is used for all the incremental edits - to baseline only request data but not project state between those edits
            self.baseline_state();
            let params_json =
                serde_json::to_value(&params).expect("marshal notification params for state");
            self.update_state(&info.method, &params_json);
        }
        let params = Some(params);
        self.baseline_request_or_notification(&info.method, &params);
        self.client.send_notification(info, params);
    }

    /// `(*FourslashTest).updateState` — params is the marshaled notification
    /// (`{"textDocument": {"uri": ...}}`), replacing Go's `any` type switch.
    fn update_state(&mut self, method: &Method, params: &serde_json::Value) {
        let uri = params
            .pointer("/textDocument/uri")
            .and_then(|v| v.as_str());
        let Some(uri) = uri else {
            return;
        };
        let file_name = DocumentUri(uri.to_string()).file_name();
        if method == &Method::TextDocumentDidOpen {
            self.open_files.insert(file_name);
        } else if method == &Method::TextDocumentDidClose {
            self.open_files.remove(&file_name);
        }
    }

    /// `(*FourslashTest).GetOptions`.
    pub fn get_options(&self) -> UserPreferences {
        self.user_preferences.as_ref().clone()
    }

    /// `(*FourslashTest).Configure`.
    pub fn configure(&mut self, config: UserPreferences) {
        // We send 'js/ts' by default because that is what we expect the primary config to be in vscode and VS (one
        // set of preferences for both languages). This should be fine in fourslash since tests that need
        // multiple options usually send reconfiguration commands for each `verify` anyways
        self.user_preferences = Arc::new(config.clone());
        *self.user_preferences_shared.lock().unwrap() = self.user_preferences.clone();
        let settings = serde_json::json!({ "js/ts": config });
        self.send_notification(
            &lsproto::WORKSPACE_DID_CHANGE_CONFIGURATION_INFO,
            lsproto::DidChangeConfigurationParams { settings },
        );
    }

    /// `(*FourslashTest).ConfigureWithReset` — returns the previous
    /// preferences; restore with `self.configure(prev)` (Go returns a
    /// `reset func()`).
    pub fn configure_with_reset(&mut self, config: UserPreferences) -> UserPreferences {
        let original_config = self.user_preferences.as_ref().clone();
        self.configure(config);
        original_config
    }
}

impl FourslashTest {
    /// `caretOffset` — the current caret position as a byte offset into the
    /// active file (Go inlines
    /// `f.converters.LineAndCharacterToPosition(script, f.currentCaretPosition)`).
    pub(crate) fn caret_offset(&self) -> i32 {
        let script = self.get_script_info_or_panic(&self.active_filename);
        self.test_converters()
            .line_and_character_to_position(script, self.current_caret_position)
    }

    /// `(*FourslashTest).getCurrentPositionPrefix`.
    pub(crate) fn get_current_position_prefix(&self) -> String {
        if let Some(name) = &self.last_known_marker_name {
            return format!("At marker '{name}': ");
        }
        format!(
            "At position {}(Ln {}, Col {}): ",
            self.active_filename.as_string(),
            self.current_caret_position.line,
            self.current_caret_position.character
        )
    }

    /// `(*FourslashTest).getScriptInfo` — panics when missing like Go's
    /// `f.scriptInfos[fileName]`-then-deref pattern.
    pub(crate) fn get_script_info_or_panic(&self, file_name: &RootedFilePath) -> &ScriptInfo {
        self.script_infos
            .get(file_name)
            .unwrap_or_else(|| {
                panic!("Script info for file {} not found", file_name.as_string())
            })
    }

    /// `get_script_info` — the non-panicking lookup.
    pub(crate) fn get_script_info(&self, file_name: &RootedFilePath) -> Option<&ScriptInfo> {
        self.script_infos.get(file_name)
    }

    /// `(*FourslashTest).getOrLoadScriptInfo`.
    pub(crate) fn get_or_load_script_info(
        &mut self,
        file_name: &RootedFilePath,
    ) -> Option<&ScriptInfo> {
        if self.script_infos.contains_key(file_name) {
            return self.script_infos.get(file_name);
        }
        if let Some(content) = self.vfs.read_file(file_name) {
            let script = new_script_info_from_file_name(file_name.clone(), &content);
            self.script_infos.insert(file_name.clone(), script);
            return self.script_infos.get(file_name);
        }
        None
    }

    /// `(*FourslashTest).GoToMarkerOrRange`.
    pub fn go_to_marker_or_range(&mut self, marker_or_range: &Rc<dyn MarkerOrRange>) {
        self.go_to_marker_impl(marker_or_range);
    }

    /// `(*FourslashTest).GoToMarker`.
    pub fn go_to_marker(&mut self, marker_name: &str) {
        let Some(marker) = self.test_data.marker_positions.get(marker_name).cloned() else {
            panic!("Marker '{marker_name}' not found");
        };
        self.go_to_marker_impl(&(marker as Rc<dyn MarkerOrRange>));
    }

    /// `(*FourslashTest).goToMarker`.
    pub(crate) fn go_to_marker_impl(&mut self, marker_or_range: &Rc<dyn MarkerOrRange>) {
        self.ensure_active_file(marker_or_range.file_name());
        self.go_to_position(marker_or_range.ls_pos());
        self.last_known_marker_name = marker_or_range.get_name().map(str::to_string);
    }

    /// `(*FourslashTest).GoToEOF`.
    pub fn go_to_eof(&mut self) {
        let pos = {
            let script = self.get_script_info_or_panic(&self.active_filename);
            let converters = self.test_converters();
            converters.position_to_line_and_character(script, script.content.len() as TextPos)
        };
        self.go_to_position(pos);
    }

    /// `(*FourslashTest).GoToBOF`.
    pub fn go_to_bof(&mut self) {
        self.go_to_position(lsproto::Position {
            line: 0,
            character: 0,
        });
    }

    /// `(*FourslashTest).GoToPosition`.
    pub fn go_to_position_offset(&mut self, position: i32) {
        let pos = {
            let script = self.get_script_info_or_panic(&self.active_filename);
            let converters = self.test_converters();
            converters.position_to_line_and_character(script, position as TextPos)
        };
        self.go_to_position(pos);
    }

    /// `(*FourslashTest).goToPosition`.
    pub(crate) fn go_to_position(&mut self, position: lsproto::Position) {
        self.current_caret_position = position;
        self.selection_end = None;
    }

    /// `(*FourslashTest).GoToEachMarker` — `action` receives the marker and
    /// index (Go: `func(marker *Marker, index int)`).
    pub fn go_to_each_marker(
        &mut self,
        marker_names: &[String],
        mut action: impl FnMut(&mut Self, &Rc<Marker>, usize),
    ) {
        let markers: Vec<Rc<Marker>> = if marker_names.is_empty() {
            self.test_data.markers.clone()
        } else {
            marker_names
                .iter()
                .map(|name| {
                    self.test_data
                        .marker_positions
                        .get(name)
                        .cloned()
                        .unwrap_or_else(|| panic!("Marker '{name}' not found"))
                })
                .collect()
        };
        for (i, marker) in markers.iter().enumerate() {
            self.go_to_marker_impl(&(marker.clone() as Rc<dyn MarkerOrRange>));
            action(self, marker, i);
        }
    }

    /// `(*FourslashTest).GoToEachRange`.
    pub fn go_to_each_range(&mut self, mut action: impl FnMut(&mut Self, &Rc<RangeMarker>)) {
        let ranges = self.test_data.ranges.clone();
        for range_marker in &ranges {
            let start = range_marker.ls_range.start;
            self.go_to_position(start);
            action(self, range_marker);
        }
    }

    /// `(*FourslashTest).GoToRangeStart`.
    pub fn go_to_range_start(&mut self, range_marker: &Rc<RangeMarker>) {
        self.open_file(range_marker.file_name().clone());
        self.go_to_position(range_marker.ls_range.start);
    }

    /// `(*FourslashTest).GoToSelect`.
    pub fn go_to_select(&mut self, start_marker_name: &str, end_marker_name: &str) {
        let Some(start_marker) = self.test_data.marker_positions.get(start_marker_name).cloned()
        else {
            panic!("Start marker '{start_marker_name}' not found");
        };
        let Some(end_marker) = self.test_data.marker_positions.get(end_marker_name).cloned() else {
            panic!("End marker '{end_marker_name}' not found");
        };
        if start_marker.file_name() != end_marker.file_name() {
            panic!("Markers '{start_marker_name}' and '{end_marker_name}' are in different files");
        }
        self.ensure_active_file(start_marker.file_name());
        self.go_to_position(start_marker.ls_position);
        self.selection_end = Some(end_marker.ls_position);
    }

    /// `(*FourslashTest).GoToSelectRange`.
    pub fn go_to_select_range(&mut self, range_marker: &Rc<RangeMarker>) {
        self.go_to_range_start(range_marker);
        self.selection_end = Some(range_marker.ls_range.end);
    }

    /// `(*FourslashTest).GoToFile`.
    pub fn go_to_file(&mut self, filename: &str) {
        self.open_file(tspath::to_rooted_file_path(filename, &root_dir()));
    }

    /// `(*FourslashTest).GoToFileNumber`.
    pub fn go_to_file_number(&mut self, index: i32) {
        if index < 0 || index as usize >= self.test_data.files.len() {
            panic!(
                "File index {index} out of range (0-{})",
                self.test_data.files.len() as i32 - 1
            );
        }
        let file_name = self.test_data.files[index as usize].file_name().clone();
        self.open_file(file_name);
    }

    /// `(*FourslashTest).Markers`.
    pub fn markers(&self) -> Vec<Rc<Marker>> {
        self.test_data.markers.clone()
    }

    /// `(*FourslashTest).MarkerNames`.
    pub fn marker_names(&self) -> Vec<String> {
        self.test_data
            .markers
            .iter()
            .filter_map(|marker| marker.name.clone())
            .collect()
    }

    /// `(*FourslashTest).MarkerByName`.
    pub fn marker_by_name(&self, name: &str) -> Option<Rc<Marker>> {
        self.test_data.marker_positions.get(name).cloned()
    }

    /// `(*FourslashTest).Ranges`.
    pub fn ranges(&self) -> Vec<Rc<RangeMarker>> {
        self.test_data.ranges.clone()
    }

    /// `(*FourslashTest).getRangesInFile`.
    pub(crate) fn get_ranges_in_file(&self, file_name: &RootedFilePath) -> Vec<Rc<RangeMarker>> {
        self.test_data
            .ranges
            .iter()
            .filter(|r| r.file_name() == file_name)
            .cloned()
            .collect()
    }

    /// `(*FourslashTest).ensureActiveFile`.
    fn ensure_active_file(&mut self, filename: &RootedFilePath) {
        if &self.active_filename != filename {
            if !self.open_files.contains(filename) {
                self.open_file(filename.clone());
            } else {
                self.active_filename = filename.clone();
            }
        }
    }

    /// `(*FourslashTest).CloseFileOfMarker`.
    pub fn close_file_of_marker(&mut self, marker_name: &str) {
        let Some(marker) = self.test_data.marker_positions.get(marker_name).cloned() else {
            panic!("Marker '{marker_name}' not found");
        };
        let marker_file_name = marker.file_name().clone();
        if self.active_filename == marker_file_name {
            self.active_filename = RootedFilePath::default();
        }
        if let Some(test_file) = self
            .test_data
            .files
            .iter()
            .find(|f| f.file_name() == &marker_file_name)
        {
            let script =
                new_script_info_from_file_name(test_file.file_name().clone(), &test_file.content);
            self.script_infos
                .insert(test_file.file_name().clone(), script);
        } else {
            self.script_infos.remove(&marker_file_name);
        }
        self.send_notification(
            &lsproto::TEXT_DOCUMENT_DID_CLOSE_INFO,
            lsproto::DidCloseTextDocumentParams {
                text_document: lsproto::TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&marker_file_name),
                },
            },
        );
    }

    /// `(*FourslashTest).openFile`.
    pub(crate) fn open_file(&mut self, filename: RootedFilePath) {
        if self.get_script_info(&filename).is_none() {
            if let Some(content) = self.vfs.read_file(&filename) {
                let script = new_script_info_from_file_name(filename.clone(), &content);
                self.script_infos.insert(filename.clone(), script);
            } else {
                panic!("File {} not found in test data", filename.as_string());
            }
        }
        let text = self.get_script_info_or_panic(&filename).content.clone();
        self.active_filename = filename.clone();
        self.send_notification(
            &lsproto::TEXT_DOCUMENT_DID_OPEN_INFO,
            lsproto::DidOpenTextDocumentParams {
                text_document: Some(lsproto::TextDocumentItem {
                    uri: lsconv::file_name_to_document_uri(&filename),
                    language_id: get_language_kind(filename.as_string()),
                    version: 0,
                    text,
                }),
            },
        );
        self.baseline_projects_after_notification(&filename);
    }

    /// `(*FourslashTest).FormatDocument`.
    pub fn format_document(&mut self, filename: &str) {
        let file_name = if filename.is_empty() {
            self.active_filename.clone()
        } else {
            tspath::to_rooted_file_path(filename, &root_dir())
        };
        let format_options = self
            .user_preferences
            .format_code_settings
            .to_ls_format_options();
        let result = self.send_request(
            &lsproto::TEXT_DOCUMENT_FORMATTING_INFO,
            lsproto::DocumentFormattingParams {
                text_document: lsproto::TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&file_name),
                },
                options: Some(format_options),
                ..Default::default()
            },
        );
        if let Some(text_edits) = result.text_edits {
            self.apply_text_edits(&text_edits);
        }
    }

    /// `(*FourslashTest).FormatSelection`.
    pub fn format_selection(&mut self, start_marker_name: &str, end_marker_name: &str) {
        let Some(start_marker) = self.test_data.marker_positions.get(start_marker_name).cloned()
        else {
            panic!("Marker '{start_marker_name}' not found");
        };
        let Some(end_marker) = self.test_data.marker_positions.get(end_marker_name).cloned() else {
            panic!("Marker '{end_marker_name}' not found");
        };
        if start_marker.file_name() != end_marker.file_name() {
            panic!("Markers '{start_marker_name}' and '{end_marker_name}' are in different files");
        }
        let range = lsproto::Range {
            start: start_marker.ls_position,
            end: end_marker.ls_position,
        };
        let file_name = start_marker.file_name().clone();
        let format_options = self
            .user_preferences
            .format_code_settings
            .to_ls_format_options();
        let result = self.send_request(
            &lsproto::TEXT_DOCUMENT_RANGE_FORMATTING_INFO,
            lsproto::DocumentRangeFormattingParams {
                text_document: lsproto::TextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(&file_name),
                },
                range,
                options: Some(format_options),
                ..Default::default()
            },
        );
        if let Some(text_edits) = result.text_edits {
            self.apply_text_edits(&text_edits);
        }
    }

    /// `(*FourslashTest).VerifyCurrentFileContent`.
    pub fn verify_current_file_content(&mut self, expected_content: &str) {
        assert_eq!(
            self.get_script_info_or_panic(&self.active_filename).content,
            expected_content,
            "current file content mismatch"
        );
    }

    /// `(*FourslashTest).VerifyCurrentLineContent`.
    pub fn verify_current_line_content(&mut self, expected_content: &str) {
        let actual_content = self
            .get_script_info_or_panic(&self.active_filename)
            .get_line_content(self.current_caret_position.line as i32)
            .to_string();
        assert_eq!(
            actual_content, expected_content,
            "\n  actual line: \"{actual_content}\"\nexpected line: \"{expected_content}\"\n"
        );
    }

    /// `(*FourslashTest).VerifyIndentation`.
    pub fn verify_indentation(&mut self, _num_spaces: i32) {
        // not implemented
    }

    // --- editing ---

    /// `(*FourslashTest).Insert` — insert text at the current caret position.
    pub fn insert(&mut self, text: &str) {
        self.baseline_state();
        self.type_text(text);
    }

    /// `(*FourslashTest).InsertLine` — insert text and a new line at the
    /// current caret position.
    pub fn insert_line(&mut self, text: &str) {
        self.baseline_state();
        self.type_text(&format!("{text}\n"));
    }

    /// `(*FourslashTest).Backspace` — removes the text at the current caret
    /// position as if the user pressed backspace `count` times.
    pub fn backspace(&mut self, count: i32) {
        let mut offset = {
            let script = self.get_script_info_or_panic(&self.active_filename);
            let converters = self.test_converters();
            converters.line_and_character_to_position(script, self.current_caret_position)
        };
        self.baseline_state();

        for _ in 0..count {
            offset -= 1;
            self.edit_script_and_update_markers(
                self.active_filename.clone(),
                offset,
                offset + 1,
                "",
            );
            self.current_caret_position = {
                let script = self.get_script_info_or_panic(&self.active_filename);
                let converters = self.test_converters();
                converters.position_to_line_and_character(script, offset)
            };
            // Don't need to examine formatting because there are no formatting changes on backspace.
        }

        // self.check_post_edit_invariants() // !!! do we need this?
    }

    /// `(*FourslashTest).DeleteAtCaret` — removes the text at the current
    /// caret position as if the user pressed delete `count` times.
    pub fn delete_at_caret(&mut self, count: i32) {
        let offset = {
            let script = self.get_script_info_or_panic(&self.active_filename);
            let converters = self.test_converters();
            converters.line_and_character_to_position(script, self.current_caret_position)
        };
        self.baseline_state();

        for _ in 0..count {
            self.edit_script_and_update_markers(
                self.active_filename.clone(),
                offset,
                offset + 1,
                "",
            );
            // Position stays the same after delete (unlike backspace)
        }
    }

    /// `(*FourslashTest).Paste` — enters text as if the user had pasted it.
    pub fn paste(&mut self, text: &str) {
        let start = {
            let script = self.get_script_info_or_panic(&self.active_filename);
            let converters = self.test_converters();
            converters.line_and_character_to_position(script, self.current_caret_position)
        };
        self.baseline_state();
        self.edit_script_and_update_markers(self.active_filename.clone(), start, start, text);

        // post-paste formatting
        if self.state_enable_formatting {
            let end = {
                let script = self.get_script_info_or_panic(&self.active_filename);
                let converters = self.test_converters();
                converters.position_to_line_and_character(script, start + text.len() as i32)
            };
            let format_options = self
                .user_preferences
                .format_code_settings
                .to_ls_format_options();
            let file_name = self.active_filename.clone();
            let result = self.send_request_and_baseline_worker(
                &lsproto::TEXT_DOCUMENT_RANGE_FORMATTING_INFO,
                lsproto::DocumentRangeFormattingParams {
                    text_document: lsproto::TextDocumentIdentifier {
                        uri: lsconv::file_name_to_document_uri(&file_name),
                    },
                    range: lsproto::Range {
                        start: self.current_caret_position,
                        end,
                    },
                    options: Some(format_options),
                    ..Default::default()
                },
                false,
            );
            if let Some(text_edits) = result.text_edits {
                self.apply_text_edits(&text_edits);
            }
        }
        // this.check_post_edit_invariants(); // !!! do we need this?
    }

    /// `(*FourslashTest).ReplaceLine` — selects a line and replaces it with
    /// a new text.
    pub fn replace_line(&mut self, line_index: i32, text: &str) {
        self.baseline_state();
        self.select_line(line_index);
        self.type_text(text);
    }

    /// `(*FourslashTest).selectLine`.
    fn select_line(&mut self, line_index: i32) {
        let script = self.get_script_info_or_panic(&self.active_filename);
        let start = script.line_map.line_starts[line_index as usize];
        let end = if line_index as usize + 1 >= script.line_map.line_starts.len() {
            script.content.len() as TextPos
        } else {
            script.line_map.line_starts[line_index as usize + 1] - 1
        };
        self.select_range(TextRange::new(start, end));
    }

    /// `(*FourslashTest).selectRange`.
    fn select_range(&mut self, text_range: TextRange) {
        let (start, end) = {
            let script = self.get_script_info_or_panic(&self.active_filename);
            let converters = self.test_converters();
            (
                converters.position_to_line_and_character(script, text_range.pos()),
                converters.position_to_line_and_character(script, text_range.end()),
            )
        };
        self.go_to_position(start);
        self.selection_end = Some(end);
    }

    /// `(*FourslashTest).getSelection`.
    pub(crate) fn get_selection(&self) -> TextRange {
        let script = self.get_script_info_or_panic(&self.active_filename);
        let converters = self.test_converters();
        let start = converters.line_and_character_to_position(script, self.current_caret_position);
        let end = match &self.selection_end {
            None => start,
            Some(selection_end) => {
                converters.line_and_character_to_position(script, *selection_end)
            }
        };
        TextRange::new(start, end)
    }

    /// `(*FourslashTest).applyTextEdits` — updates `current_caret_position`;
    /// returns the total offset delta.
    pub(crate) fn apply_text_edits(&mut self, edits: &[lsproto::TextEdit]) -> i32 {
        let mut edits = edits.to_vec();
        {
            let script = self.get_script_info_or_panic(&self.active_filename);
            let converters = self.test_converters();
            edits.sort_by(|a, b| {
                let a_start = converters.line_and_character_to_position(script, a.range.start);
                let b_start = converters.line_and_character_to_position(script, b.range.start);
                a_start.cmp(&b_start)
            });
        }

        let mut total_offset = 0i32;
        let mut current_caret_position = {
            let script = self.get_script_info_or_panic(&self.active_filename);
            let converters = self.test_converters();
            converters.line_and_character_to_position(script, self.current_caret_position)
        };
        // Apply edits in reverse order to avoid affecting the positions of earlier edits.
        for edit in edits.iter().rev() {
            let (start, end) = {
                let script = self.get_script_info_or_panic(&self.active_filename);
                let converters = self.test_converters();
                (
                    converters.line_and_character_to_position(script, edit.range.start),
                    converters.line_and_character_to_position(script, edit.range.end),
                )
            };
            self.edit_script_and_update_markers(
                self.active_filename.clone(),
                start,
                end,
                &edit.new_text,
            );

            let delta = edit.new_text.len() as i32 - (end - start);
            if start <= current_caret_position {
                if end <= current_caret_position {
                    // The entirety of the edit span falls before the caret position, shift the caret accordingly
                    current_caret_position += delta;
                } else {
                    // The span being replaced includes the caret position, place the caret at the beginning of the span
                    current_caret_position = start;
                }
            }
            total_offset += delta;
        }
        self.current_caret_position = {
            let script = self.get_script_info_or_panic(&self.active_filename);
            let converters = self.test_converters();
            converters.position_to_line_and_character(script, current_caret_position)
        };
        total_offset
    }

    /// `(*FourslashTest).Replace`.
    pub fn replace(&mut self, start: i32, length: i32, text: &str) {
        self.baseline_state();
        self.replace_worker(start, length, text);
    }

    /// `(*FourslashTest).replaceWorker`.
    fn replace_worker(&mut self, start: i32, length: i32, text: &str) {
        self.edit_script_and_update_markers(
            self.active_filename.clone(),
            start,
            start + length,
            text,
        );
        // self.check_post_edit_invariants() // !!! do we need this?
    }

    /// `(*FourslashTest).typeText` — inserts the text at the caret position
    /// character by character, as if the user typed it.
    fn type_text(&mut self, text: &str) {
        // temporary -- this disables tests failing if format crashes; this unblocks unrelated tests such as codefixes
        self.report_format_on_type_crash = false;
        let _reset = ReportFormatOnTypeCrashReset(self);

        let selection = _reset.0.get_selection();
        _reset.0.replace_worker(selection.pos(), selection.end() - selection.pos(), "");

        let mut total_size = 0usize;

        let mut offset = {
            let script = _reset.0.get_script_info_or_panic(&_reset.0.active_filename);
            let converters = _reset.0.test_converters();
            converters.line_and_character_to_position(script, _reset.0.current_caret_position)
        };
        while total_size < text.len() {
            let (r, size) = decode_rune_in_string(&text.as_bytes()[total_size..]);
            _reset.0.edit_script_and_update_markers(
                _reset.0.active_filename.clone(),
                offset,
                offset,
                &r.to_string(),
            );

            total_size += size;
            offset += size as i32;
            _reset.0.current_caret_position = {
                let script = _reset.0.get_script_info_or_panic(&_reset.0.active_filename);
                let converters = _reset.0.test_converters();
                converters.position_to_line_and_character(script, offset)
            };

            // Handle post-keystroke formatting
            if _reset.0.state_enable_formatting {
                let format_options = _reset
                    .0
                    .user_preferences
                    .format_code_settings
                    .to_ls_format_options();
                let file_name = _reset.0.active_filename.clone();
                let result = _reset.0.send_request_and_baseline_worker(
                    &lsproto::TEXT_DOCUMENT_ON_TYPE_FORMATTING_INFO,
                    lsproto::DocumentOnTypeFormattingParams {
                        text_document: lsproto::TextDocumentIdentifier {
                            uri: lsconv::file_name_to_document_uri(&file_name),
                        },
                        position: _reset.0.current_caret_position,
                        ch: r.to_string(),
                        options: Some(format_options),
                    },
                    false,
                );
                if let Some(text_edits) = result.text_edits {
                    offset += _reset.0.apply_text_edits(&text_edits);
                }
            }
        }

        // self.check_post_edit_invariants() // !!! do we need this?
    }

    /// `(*FourslashTest).editScriptAndUpdateMarkers` — edits the script and
    /// updates marker and range positions accordingly. Does not update the
    /// current caret position.
    pub(crate) fn edit_script_and_update_markers(
        &mut self,
        file_name: RootedFilePath,
        edit_start: i32,
        edit_end: i32,
        new_text: &str,
    ) {
        self.edit_script_and_update_markers_worker(
            file_name,
            vec![TextChange {
                text_range: TextRange::new(edit_start, edit_end),
                new_text: new_text.to_string(),
            }],
        );
    }

    /// `(*FourslashTest).editScriptAndUpdateMarkersWorker` — markers are
    /// immutable `Rc`s, so every changed marker/range is rebuilt and swapped
    /// into `markers`, `marker_positions`, `ranges`, and `RangeMarker.marker`
    /// under the same identity (Go mutates the shared pointers).
    pub(crate) fn edit_script_and_update_markers_worker(
        &mut self,
        file_name: RootedFilePath,
        changes: Vec<TextChange>,
    ) {
        // Sort changes by position (ascending) so we can apply in reverse
        let mut sorted_changes = changes;
        sorted_changes.sort_by(|a, b| a.pos().cmp(&b.pos()));

        // Apply changes in reverse order to preserve positions of earlier changes
        for change in sorted_changes.iter().rev() {
            let edit_start = change.pos();
            let edit_end = change.end();
            self.edit_script(&file_name, change);

            // `converters` borrows `self` immutably, so all conversions are
            // computed inside a scope first; the `&mut` rebuilds below run
            // after it is dropped.
            let mut replacements: FxHashMap<*const Marker, Rc<Marker>> = FxHashMap::default();
            let mut range_updates: FxHashMap<*const RangeMarker, (TextRange, lsproto::Range)> =
                FxHashMap::default();
            {
                let converters = self.test_converters();

                // old marker pointer -> rebuilt marker
                for marker_rc in &self.test_data.markers {
                    if marker_rc.file_name() != &file_name {
                        continue;
                    }
                    let new_position = update_position(
                        marker_rc.position,
                        edit_start,
                        edit_end,
                        &change.new_text,
                    );
                    let new_ls_position = converters.position_to_line_and_character(
                        &self.script_infos[&file_name],
                        new_position,
                    );
                    let new_marker = Rc::new(Marker {
                        file_name: marker_rc.file_name().clone(),
                        position: new_position,
                        ls_position: new_ls_position,
                        name: marker_rc.name.clone(),
                        data: marker_rc.data.clone(),
                    });
                    replacements.insert(Rc::as_ptr(marker_rc), new_marker);
                }
                for range_rc in &self.test_data.ranges {
                    if range_rc.file_name() != &file_name {
                        continue;
                    }
                    let start = update_position(
                        range_rc.range.pos(),
                        edit_start,
                        edit_end,
                        &change.new_text,
                    );
                    let end = update_position(
                        range_rc.range.end(),
                        edit_start,
                        edit_end,
                        &change.new_text,
                    );
                    let new_range = TextRange::new(start, end);
                    let new_ls_range =
                        converters.to_lsp_range(&self.script_infos[&file_name], new_range);
                    range_updates.insert(Rc::as_ptr(range_rc), (new_range, new_ls_range));
                }
            }
            if !replacements.is_empty() {
                for marker_rc in self.test_data.markers.iter_mut() {
                    if let Some(new_marker) = replacements.get(&Rc::as_ptr(marker_rc)) {
                        *marker_rc = new_marker.clone();
                    }
                }
                for (_, marker_rc) in self.test_data.marker_positions.iter_mut() {
                    if let Some(new_marker) = replacements.get(&Rc::as_ptr(marker_rc)) {
                        *marker_rc = new_marker.clone();
                    }
                }
            }
            for range_rc in self.test_data.ranges.iter_mut() {
                let Some((new_range, new_ls_range)) =
                    range_updates.get(&Rc::as_ptr(range_rc)).cloned()
                else {
                    continue;
                };
                *range_rc = Rc::new(RangeMarker {
                    file_name: range_rc.file_name().clone(),
                    range: new_range,
                    ls_range: new_ls_range,
                    marker: range_rc
                        .marker
                        .as_ref()
                        .map(|m| {
                            replacements
                                .get(&Rc::as_ptr(m))
                                .cloned()
                                .unwrap_or_else(|| m.clone())
                        }),
                });
            }
        }
        self.ranges_by_text = None;
    }

    /// `(*FourslashTest).fromLSPRange`.
    pub(crate) fn from_lsp_range(&self, script: &ScriptInfo, r: lsproto::Range) -> TextRange {
        self.test_converters().from_lsp_range(script, r)
    }

    /// `(*FourslashTest).editScript`.
    fn edit_script(&mut self, file_name: &RootedFilePath, change: &TextChange) {
        if self.get_or_load_script_info(file_name).is_none() {
            panic!("Script info for file {} not found", file_name.as_string());
        }
        let change_range = {
            let script = &self.script_infos[file_name];
            let converters = self.test_converters();
            converters.to_lsp_range(script, TextRange::new(change.pos(), change.end()))
        };
        self.script_infos
            .get_mut(file_name)
            .unwrap()
            .edit_content(change);
        if let Err(err) = self
            .vfs
            .write_file(file_name, &self.script_infos[file_name].content)
        {
            panic!(
                "failed to write to VFS for {}: {err}",
                file_name.as_string()
            );
        }
        let version = self.script_infos[file_name].version;
        self.send_notification(
            &lsproto::TEXT_DOCUMENT_DID_CHANGE_INFO,
            lsproto::DidChangeTextDocumentParams {
                text_document: lsproto::VersionedTextDocumentIdentifier {
                    uri: lsconv::file_name_to_document_uri(file_name),
                    version,
                },
                content_changes: Some(vec![
                    lsproto::TextDocumentContentChangePartialOrWholeDocument {
                        partial: Some(lsproto::TextDocumentContentChangePartial {
                            range: change_range,
                            range_length: None,
                            text: change.new_text.clone(),
                        }),
                        ..Default::default()
                    },
                ]),
            },
        );
    }

    /// `(*FourslashTest).GetRangesByText`.
    pub fn get_ranges_by_text(&mut self) -> &MultiMap<String, Rc<RangeMarker>> {
        if self.ranges_by_text.is_none() {
            let mut ranges_by_text = MultiMap::new();
            for r in &self.test_data.ranges {
                let range_text = self.get_range_text(r);
                ranges_by_text.add(range_text, r.clone());
            }
            self.ranges_by_text = Some(ranges_by_text);
        }
        self.ranges_by_text.as_ref().unwrap()
    }

    /// `(*FourslashTest).getRangeText`.
    pub(crate) fn get_range_text(&self, r: &Rc<RangeMarker>) -> String {
        let script = self.get_script_info_or_panic(r.file_name());
        script.content[r.range.pos() as usize..r.range.end() as usize].to_string()
    }

    /// `(*FourslashTest).verifyBaselines`.
    fn verify_baselines(&self) {
        if !self.test_data.is_state_baselining_enabled() {
            for (command, content) in &self.baselines {
                baseline::run(
                    &baselineutil::get_baseline_file_name(*command),
                    content,
                    &self.get_baseline_options(*command),
                )
                .unwrap_or_else(|e| panic!("{e}"));
            }
        } else if let Some(state_baseline) = &self.state_baseline {
            baseline::run(
                &(get_base_file_name_from_test() + ".baseline"),
                state_baseline.baseline.borrow().as_str(),
                &baseline::Options {
                    subfolder: "fourslash/state".to_string(),
                    ..Default::default()
                },
            )
            .unwrap_or_else(|e| panic!("{e}"));
        }
    }
}

/// `updatePosition`.
fn update_position(pos: i32, edit_start: i32, edit_end: i32, new_text: &str) -> i32 {
    if pos <= edit_start {
        return pos;
    }
    // If inside the edit, return -1 to mark as invalid
    if pos < edit_end {
        return -1;
    }
    pos + new_text.len() as i32 - (edit_end - edit_start)
}

/// `updatePositionForTextEdit`.
pub(crate) fn update_position_for_text_edit(
    position: i32,
    edit_start: i32,
    edit_end: i32,
    new_text_length: i32,
) -> i32 {
    if position <= edit_start {
        return position;
    }
    if position < edit_end {
        return -1;
    }
    position + new_text_length - (edit_end - edit_start)
}

/// `removeWhitespace`.
pub(crate) fn remove_whitespace(text: &str) -> String {
    let mut builder = String::new();
    for ch in text.chars() {
        if stringutil::is_white_space_like(ch) {
            continue;
        }
        builder.push(ch);
    }
    builder
}

/// `assertValidTextRange`.
pub(crate) fn assert_valid_text_range(text_range: TextRange, message: &str) {
    if text_range.pos() >= 0 && text_range.end() >= 0 {
        return;
    }
    panic!("{message}");
}

/// `selectCodeFixDiagnostic`.
pub(crate) fn select_code_fix_diagnostic(
    diagnostics: &[lsproto::Diagnostic],
    error_code: i32,
) -> Option<&lsproto::Diagnostic> {
    if error_code == 0 {
        return diagnostics.first();
    }
    diagnostics.iter().find(|diagnostic| {
        diagnostic.code.as_ref().and_then(|c| c.integer) == Some(error_code)
    })
}

/// `isLibFile`.
pub(crate) fn is_lib_file(file_name: &str) -> bool {
    let base_name = tspath::get_base_file_name(file_name);
    base_name.starts_with("lib.") && base_name.ends_with(".d.ts")
}

/// `computeLineStarts`.
pub(crate) fn compute_line_starts(content: &str) -> Vec<usize> {
    let mut line_starts = vec![0usize];
    for (i, ch) in content.char_indices() {
        if ch == '\n' {
            line_starts.push(i + 1);
        }
    }
    line_starts
}

/// `symbolKindToLowercase`.
pub(crate) fn symbol_kind_to_lowercase(kind: lsproto::SymbolKind) -> String {
    kind.to_string().to_lowercase()
}

/// `roundtripThroughJson` — intended for spots where a complex value needs
/// to be reinterpreted following some prior JSON deserialization.
pub(crate) fn roundtrip_through_json<T: DeserializeOwned>(
    value: &serde_json::Value,
) -> Result<T, serde_json::Error> {
    let bytes = serde_json::to_vec(value)?;
    json::unmarshal(&bytes, &[])
}

/// `getLanguageKind`.
pub(crate) fn get_language_kind(filename: &str) -> lsproto::LanguageKind {
    if tspath::file_extension_is_one_of(
        filename,
        &[
            tspath::EXTENSION_TS,
            tspath::EXTENSION_MTS,
            tspath::EXTENSION_CTS,
            tspath::EXTENSION_DMTS,
            tspath::EXTENSION_DCTS,
            tspath::EXTENSION_DTS,
        ],
    ) {
        return lsproto::LanguageKind::TypeScript;
    }
    if tspath::file_extension_is_one_of(
        filename,
        &[
            tspath::EXTENSION_JS,
            tspath::EXTENSION_MJS,
            tspath::EXTENSION_CJS,
        ],
    ) {
        return lsproto::LanguageKind::JavaScript;
    }
    if tspath::file_extension_is(filename, tspath::EXTENSION_JSX) {
        return lsproto::LanguageKind::JavaScriptReact;
    }
    if tspath::file_extension_is(filename, tspath::EXTENSION_TSX) {
        return lsproto::LanguageKind::TypeScriptReact;
    }
    if tspath::file_extension_is(filename, tspath::EXTENSION_JSON) {
        return lsproto::LanguageKind::JSON;
    }
    lsproto::LanguageKind::TypeScript // !!! should we error in this case?
}

/// `utf8.DecodeRuneInString` — `(rune, size)`; invalid input yields
/// `(RuneError=0xFFFD, 1)` like Go. Used for splitting typed text into
/// characters.
fn decode_rune_in_string(s: &[u8]) -> (char, usize) {
    let Some(first) = s.first() else {
        return ('\u{FFFD}', 0);
    };
    if *first < 0x80 {
        return (*first as char, 1);
    }
    let valid_up_to = match std::str::from_utf8(s) {
        Ok(st) => return (st.chars().next().unwrap(), st.chars().next().unwrap().len_utf8()),
        Err(e) => e.valid_up_to(),
    };
    if valid_up_to == 0 {
        return ('\u{FFFD}', 1);
    }
    let ch = std::str::from_utf8(&s[..valid_up_to])
        .unwrap()
        .chars()
        .next()
        .unwrap();
    (ch, ch.len_utf8())
}

/// Restores `report_format_on_type_crash` on drop — the Rust spelling of
/// Go's `defer func() { f.reportFormatOnTypeCrash = true }()` in `typeText`.
struct ReportFormatOnTypeCrashReset<'a>(&'a mut FourslashTest);

impl Drop for ReportFormatOnTypeCrashReset<'_> {
    fn drop(&mut self) {
        self.0.report_format_on_type_crash = true;
    }
}

/// `defaultSemanticTokenTypes`.
fn default_semantic_token_types() -> Vec<String> {
    use lsproto::SemanticTokenType as T;
    [
        T::Namespace,
        T::Class,
        T::Enum,
        T::Interface,
        T::Struct,
        T::TypeParameter,
        T::Type,
        T::Parameter,
        T::Variable,
        T::Property,
        T::EnumMember,
        T::Decorator,
        T::Event,
        T::Function,
        T::Method,
        T::Macro,
        T::Label,
        T::Comment,
        T::String,
        T::Keyword,
        T::Number,
        T::Regexp,
        T::Operator,
    ]
    .iter()
    .map(|t| t.as_str().to_string())
    .collect()
}

/// `defaultSemanticTokenModifiers`.
fn default_semantic_token_modifiers() -> Vec<String> {
    use lsproto::SemanticTokenModifier as M;
    let mut v: Vec<String> = [
        M::Declaration,
        M::Definition,
        M::Readonly,
        M::Static,
        M::Deprecated,
        M::Abstract,
        M::Async,
        M::Modification,
        M::Documentation,
        M::DefaultLibrary,
    ]
    .iter()
    .map(|m| m.as_str().to_string())
    .collect();
    v.push("local".to_string());
    v
}

/// `GetDefaultCapabilities`.
pub fn get_default_capabilities() -> lsproto::ClientCapabilities {
    get_capabilities_with_defaults(None).unwrap()
}

/// `ClientCapabilitiesOptions`.
#[derive(Default)]
pub struct ClientCapabilitiesOptions {
    pub completion_item: Option<lsproto::ClientCompletionItemOptions>,
}

/// `GetDefaultCapabilitiesWithOptions`.
pub fn get_default_capabilities_with_options(
    options: Option<&ClientCapabilitiesOptions>,
) -> lsproto::ClientCapabilities {
    let mut capabilities = get_default_capabilities();
    let Some(options) = options else {
        return capabilities;
    };
    if let Some(completion_item_options) = &options.completion_item {
        let target = capabilities
            .text_document
            .as_mut()
            .unwrap()
            .completion
            .as_mut()
            .unwrap()
            .completion_item
            .as_mut()
            .unwrap();
        if completion_item_options.snippet_support.is_some() {
            target.snippet_support = completion_item_options.snippet_support;
        }
        if completion_item_options.commit_characters_support.is_some() {
            target.commit_characters_support = completion_item_options.commit_characters_support;
        }
        if completion_item_options.documentation_format.is_some() {
            target.documentation_format = completion_item_options.documentation_format.clone();
        }
        if completion_item_options.deprecated_support.is_some() {
            target.deprecated_support = completion_item_options.deprecated_support;
        }
        if completion_item_options.preselect_support.is_some() {
            target.preselect_support = completion_item_options.preselect_support;
        }
        if completion_item_options.tag_support.is_some() {
            target.tag_support = completion_item_options.tag_support.clone();
        }
        if completion_item_options.insert_replace_support.is_some() {
            target.insert_replace_support = completion_item_options.insert_replace_support;
        }
        if completion_item_options.resolve_support.is_some() {
            target.resolve_support = completion_item_options.resolve_support.clone();
        }
        if completion_item_options.insert_text_mode_support.is_some() {
            target.insert_text_mode_support =
                completion_item_options.insert_text_mode_support.clone();
        }
        if completion_item_options.label_details_support.is_some() {
            target.label_details_support = completion_item_options.label_details_support;
        }
    }
    capabilities
}

/// `getCapabilitiesWithDefaults`.
fn get_capabilities_with_defaults(
    capabilities: Option<&lsproto::ClientCapabilities>,
) -> Option<lsproto::ClientCapabilities> {
    let mut c = capabilities.cloned().unwrap_or_default();
    c.general = Some(lsproto::GeneralClientCapabilities {
        position_encodings: Some(vec![lsproto::PositionEncodingKind::UTF8]),
        ..Default::default()
    });
    if c.experimental.is_none() {
        c.experimental = Some(lsproto::ExperimentalClientCapabilities {
            hover_verbosity_level: Some(true),
            ..Default::default()
        });
    }
    let text_document = c.text_document.get_or_insert_with(Default::default);
    if text_document.completion.is_none() {
        text_document.completion = Some(lsproto::CompletionClientCapabilities {
            completion_item: Some(lsproto::ClientCompletionItemOptions {
                snippet_support: Some(false),
                commit_characters_support: Some(true),
                preselect_support: Some(true),
                label_details_support: Some(false),
                insert_replace_support: Some(true),
                documentation_format: Some(vec![
                    lsproto::MarkupKind::Markdown,
                    lsproto::MarkupKind::PlainText,
                ]),
                ..Default::default()
            }),
            completion_list: Some(lsproto::CompletionListCapabilities {
                item_defaults: Some(vec![
                    "commitCharacters".to_string(),
                    "editRange".to_string(),
                ]),
                ..Default::default()
            }),
            ..Default::default()
        });
    }
    if text_document.diagnostic.is_none() {
        text_document.diagnostic = Some(lsproto::DiagnosticClientCapabilities {
            related_information: Some(true),
            tag_support: Some(lsproto::ClientDiagnosticsTagOptions {
                value_set: Some(vec![
                    lsproto::DiagnosticTag::Unnecessary,
                    lsproto::DiagnosticTag::Deprecated,
                ]),
            }),
            ..Default::default()
        });
    }
    if text_document.publish_diagnostics.is_none() {
        text_document.publish_diagnostics = Some(lsproto::PublishDiagnosticsClientCapabilities {
            related_information: Some(true),
            tag_support: Some(lsproto::ClientDiagnosticsTagOptions {
                value_set: Some(vec![
                    lsproto::DiagnosticTag::Unnecessary,
                    lsproto::DiagnosticTag::Deprecated,
                ]),
            }),
            ..Default::default()
        });
    }
    if text_document.semantic_tokens.is_none() {
        text_document.semantic_tokens = Some(lsproto::SemanticTokensClientCapabilities {
            requests: Some(lsproto::ClientSemanticTokensRequestOptions {
                full: Some(lsproto::BooleanOrClientSemanticTokensRequestFullDelta {
                    boolean: Some(true),
                    ..Default::default()
                }),
                ..Default::default()
            }),
            token_types: Some(default_semantic_token_types()),
            token_modifiers: Some(default_semantic_token_modifiers()),
            formats: Some(vec![lsproto::TokenFormat::Relative]),
            ..Default::default()
        });
    }
    let workspace = c.workspace.get_or_insert_with(Default::default);
    if workspace.file_operations.is_none() {
        workspace.file_operations = Some(lsproto::FileOperationClientCapabilities {
            will_rename: Some(true),
            ..Default::default()
        });
    }
    if workspace.workspace_edit.is_none() {
        workspace.workspace_edit = Some(lsproto::WorkspaceEditClientCapabilities {
            document_changes: Some(true),
            resource_operations: Some(vec![lsproto::ResourceOperationKind::Rename]),
            ..Default::default()
        });
    }
    if workspace.configuration.is_none() {
        workspace.configuration = Some(true);
    }
    if text_document.definition.is_none() {
        text_document.definition = Some(lsproto::DefinitionClientCapabilities {
            link_support: Some(true),
            ..Default::default()
        });
    }
    if text_document.type_definition.is_none() {
        text_document.type_definition = Some(lsproto::TypeDefinitionClientCapabilities {
            link_support: Some(true),
            ..Default::default()
        });
    }
    if text_document.implementation.is_none() {
        text_document.implementation = Some(lsproto::ImplementationClientCapabilities {
            link_support: Some(true),
            ..Default::default()
        });
    }
    if text_document.hover.is_none() {
        text_document.hover = Some(lsproto::HoverClientCapabilities {
            content_format: Some(vec![
                lsproto::MarkupKind::Markdown,
                lsproto::MarkupKind::PlainText,
            ]),
            ..Default::default()
        });
    }
    if text_document.signature_help.is_none() {
        text_document.signature_help = Some(lsproto::SignatureHelpClientCapabilities {
            signature_information: Some(lsproto::ClientSignatureInformationOptions {
                documentation_format: Some(vec![
                    lsproto::MarkupKind::Markdown,
                    lsproto::MarkupKind::PlainText,
                ]),
                parameter_information: Some(
                    lsproto::ClientSignatureParameterInformationOptions {
                        label_offset_support: Some(true),
                    },
                ),
                active_parameter_support: Some(true),
                ..Default::default()
            }),
            context_support: Some(true),
            ..Default::default()
        });
    }
    if text_document.document_symbol.is_none() {
        text_document.document_symbol = Some(lsproto::DocumentSymbolClientCapabilities {
            hierarchical_document_symbol_support: Some(true),
            ..Default::default()
        });
    }
    if text_document.folding_range.is_none() {
        text_document.folding_range = Some(lsproto::FoldingRangeClientCapabilities {
            range_limit: Some(5000),
            folding_range_kind: Some(lsproto::ClientFoldingRangeKindOptions {
                value_set: Some(vec![
                    lsproto::FoldingRangeKind::Comment,
                    lsproto::FoldingRangeKind::Imports,
                    lsproto::FoldingRangeKind::Region,
                ]),
            }),
            folding_range: Some(lsproto::ClientFoldingRangeOptions {
                collapsed_text: Some(true), // Unused by our testing, but set to exercise the code.
            }),
            ..Default::default()
        });
    }
    Some(c)
}
