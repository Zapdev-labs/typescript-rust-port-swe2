// Ported from tsc/internal/project/client.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_core::context::Context;
use tsc_diagnostics::Message;
use tsc_locale::Locale;
use tsc_lsproto::{FileSystemWatcher, PublishDiagnosticsParams, TelemetryEvent};

use crate::watch::WatcherId;

/// `ClientError` — Go `error` results on the `Client` interface.
pub type ClientResult = Result<(), Box<dyn std::error::Error + Send + Sync>>;

/// `type Client interface` — the session's connection back to the LSP
/// client: file watching, workspace refreshes, progress, telemetry, and
/// locale.
///
/// PORT(sibling): `session.go` is the primary consumer; the surface is
/// declared here so owned infrastructure (watch registry, snapshot host)
/// can name it. Reconcile with the sibling session/client port.
pub trait Client: Send + Sync {
    /// `WatchFiles`.
    fn watch_files(
        &self,
        ctx: &Context,
        id: &WatcherId,
        watchers: &[Arc<FileSystemWatcher>],
    ) -> ClientResult;
    /// `UnwatchFiles`.
    fn unwatch_files(&self, ctx: &Context, id: &WatcherId) -> ClientResult;
    /// `RegisterContentMapperExtensions`.
    fn register_content_mapper_extensions(
        &self,
        ctx: &Context,
        extensions: &[String],
    ) -> ClientResult;
    /// `RefreshDiagnostics`.
    fn refresh_diagnostics(&self, ctx: &Context) -> ClientResult;
    /// `PublishDiagnostics`.
    fn publish_diagnostics(
        &self,
        ctx: &Context,
        params: &PublishDiagnosticsParams,
    ) -> ClientResult;
    /// `RefreshInlayHints`.
    fn refresh_inlay_hints(&self, ctx: &Context) -> ClientResult;
    /// `RefreshCodeLens`.
    fn refresh_code_lens(&self, ctx: &Context) -> ClientResult;
    /// `ProgressStart` — `args` are the diagnostic message's format args
    /// (Go `args ...any`).
    fn progress_start(&self, message: &Message, args: &[String]);
    /// `ProgressFinish`.
    fn progress_finish(&self, message: &Message, args: &[String]);
    /// `SendTelemetry`.
    fn send_telemetry(&self, ctx: &Context, telemetry: &TelemetryEvent) -> ClientResult;
    /// `IsActive`.
    fn is_active(&self) -> bool;
    /// `SetLocale` updates the locale used for diagnostic messages.
    fn set_locale(&self, locale: &str);
    /// `GetLocale` returns the current display locale for diagnostic messages.
    fn get_locale(&self) -> Locale;
}
