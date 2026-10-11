// Ported from tsc/internal/project/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
// PORT(skeleton): pending full port.
//
// PORT(sibling): the session-level types below are declared here because
// owned infrastructure (snapshothost.rs, snapshot.rs,
// configfileregistrybuilder.rs, compilerhost.rs) names them. The sibling
// session worker owns the rest of session.go (Session, watchers, client
// plumbing) and should reconcile these definitions.

use std::rc::Rc;
use std::sync::Arc;
use std::time::Duration;

use tsc_contentmapper::{Host as ContentMapperHostTrait, HostOptions, Mapper, Spawner};
use tsc_core::context::Context;
use tsc_lsproto::PositionEncodingKind;
use tsc_project_logging::Logger;
use tsc_tspath::RootedDirectoryPath;
use tsc_vfs::Vfs;

use crate::ata::NpmExecutor;
use crate::checkerpool::CheckerPoolOptions;
use crate::client::Client;
use crate::parsecache::{ContentMappedParseCache, ParseCache};

/// `UpdateReason` (session.go).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum UpdateReason {
    #[default]
    Unknown,
    DidOpenFile,
    DidCloseFile,
    DidChangeCompilerOptionsForInferredProjects,
    RequestedLanguageServicePendingChanges,
    RequestedLanguageServiceProjectNotLoaded,
    RequestedLanguageServiceForFileNotOpen,
    RequestedLanguageServiceProjectDirty,
    RequestedLoadProjectTree,
    RequestedLanguageServiceWithAutoImports,
    IdleCleanDiskCache,
    DidChangeConfigFile,
    DidChangeContentMapperContributions,
}

/// `ErrNoProjectForUnknownScriptKind` identifies requests for otherwise
/// unsupported files (Go `errors.New`; compared by message string).
pub const ERR_NO_PROJECT_FOR_UNKNOWN_SCRIPT_KIND: &str =
    "no project for unknown script kind";

/// `ContentMapperContributions` (session.go).
#[derive(Clone, Default)]
pub struct ContentMapperContributions {
    pub mappers: Vec<Arc<Mapper>>,
    pub extensions: Vec<String>,
}

/// `SessionOptions` are the immutable initialization options for a session.
/// Snapshots may reference them as a pointer since they never change
/// (Go `*SessionOptions` → `Arc<SessionOptions>`).
#[derive(Clone, Default)]
pub struct SessionOptions {
    pub current_directory: RootedDirectoryPath,
    pub default_library_path: RootedDirectoryPath,
    pub typings_location: RootedDirectoryPath,
    pub position_encoding: PositionEncodingKind,
    pub watch_enabled: bool,
    pub logging_enabled: bool,
    pub telemetry_enabled: bool,
    pub push_diagnostics_enabled: bool,
    /// `RunExternalCode` allows configured content mappers to run their
    /// (external) processes, gated on workspace trust by the client. It
    /// corresponds to the `--runExternalCode` CLI flag.
    pub run_external_code: bool,
    pub debounce_delay: Duration,
    pub checker_pool_options: CheckerPoolOptions,
}

/// `SessionInit` (session.go) — inputs shared by `Session`/`NewSnapshotHost`.
pub struct SessionInit {
    pub background_ctx: Context,
    /// `Options *SessionOptions` — the pointer is shared, hence `Arc`.
    pub options: Arc<SessionOptions>,
    pub fs: Arc<dyn Vfs>,
    /// `Client` — Go's nil-able interface.
    pub client: Option<Arc<dyn Client>>,
    /// `Logger` — Go's nil-able interface.
    pub logger: Option<Arc<dyn Logger>>,
    /// `NpmExecutor` — Go's nil-able interface.
    pub npm_executor: Option<Arc<dyn NpmExecutor>>,
    /// `Spawner` launches content mapper processes. It is `None` when the
    /// host cannot spawn processes (Go nil).
    pub spawner: Option<Arc<dyn Spawner>>,
    /// `ContentMapperLogger` — Go `contentmapper.Logger` (func type → `Arc`).
    pub content_mapper_logger: Option<tsc_contentmapper::Logger>,
    /// `ParseCache` — `None` → `NewParseCache` (Go nil). `Rc` because the
    /// Go `*ParseCache` pointer is shared between the host, builders, and
    /// auto-import leases (the cache itself is `!Clone`).
    pub parse_cache: Option<Rc<ParseCache>>,
    /// `ContentMappedParseCache` — `None` → `NewContentMappedParseCache`.
    pub content_mapped_parse_cache: Option<Rc<ContentMappedParseCache>>,
}

/// `newContentMapperHost` creates the session's shared content mapper host
/// when the workspace is trusted and a spawner is available; otherwise it
/// returns `None`, and configured content mappers are rejected by the
/// config-file gate.
pub fn new_content_mapper_host(init: &SessionInit) -> Option<Arc<dyn ContentMapperHostTrait>> {
    if !init.options.run_external_code || init.spawner.is_none() {
        return None;
    }
    let diagnostic_locale = init
        .client
        .as_ref()
        .map(|c| c.get_locale())
        .unwrap_or(tsc_locale::DEFAULT);
    Some(tsc_contentmapper::new_host_with_options(
        &init.background_ctx,
        init.spawner.clone().unwrap(),
        diagnostic_locale,
        HostOptions {
            logger: init.content_mapper_logger.clone(),
        },
    ))
}
