// Ported from tsc/internal/project/api.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::rc::Rc;
use std::sync::Arc;

use tsc_core::context::Context;

use crate::filechange::{FileChangeSummary, merge_file_change_summary};
use crate::overlayfs::LayeredFsInput;
use crate::session::Session;
use crate::snapshot::{ApiSnapshotRequest, Snapshot, SnapshotChange};

impl Session {
    /// `s.APIUpdate` creates a new snapshot incorporating the given file
    /// changes and the supplied API open/close request. The `api_request`
    /// may open or close projects and files; opens are tracked in the
    /// snapshot (ref-counted) so they persist across future updates, and
    /// closes release a previously taken ref. Programs are updated only
    /// when explicitly requested by an open or ensure operation.
    /// On success, returns a ref'd snapshot which the caller must deref
    /// when done. On failure, releases the rejected snapshot and returns
    /// the error. A snapshot with an API error is never adopted as
    /// canonical session state; host changes flushed alongside it are
    /// adopted separately.
    pub fn api_update(
        self: &Arc<Self>,
        ctx: &Context,
        api_file_changes: FileChangeSummary,
        api_request: Option<Rc<ApiSnapshotRequest>>,
    ) -> Result<Arc<Snapshot>, String> {
        let _update_guard = self.snapshot_update_mu.lock().unwrap();
        self.cancel_scheduled_snapshot_update();

        let (host_file_changes, overlays, ata_changes, _) = self.flush_changes(ctx);
        let mut file_changes = host_file_changes.clone_summary();
        merge_file_change_summary(&mut file_changes, api_file_changes);
        let (fs, replace_file_system) = match api_request.as_ref() {
            Some(request) => (request.file_system.clone(), request.replace_file_system),
            None => (None, false),
        };
        let file_system_override = fs.is_some();

        let new_snapshot = self
            .update_snapshot(
                ctx,
                overlays.clone(),
                SnapshotChange {
                    api_request,
                    fs: fs.map(LayeredFsInput::Plain),
                    file_system_override,
                    replace_file_system,
                    file_changes,
                    ata_changes: ata_changes.clone(),
                    ..Default::default()
                },
                true,
            )
            .expect("update_snapshot with caller_ref always returns a snapshot");
        if let Some(api_error) = new_snapshot.api_error() {
            let api_error = api_error.to_string();
            new_snapshot.deref();
            drop(new_snapshot);
            if !host_file_changes.is_empty() || !ata_changes.is_empty() {
                // The API request is rejected as a unit, but host changes
                // were already flushed and must still advance the canonical
                // session snapshot.
                self.update_snapshot(
                    ctx,
                    overlays,
                    SnapshotChange {
                        file_changes: host_file_changes,
                        ata_changes,
                        ..Default::default()
                    },
                    false,
                );
            }
            return Err(api_error);
        }
        Ok(new_snapshot)
    }

    /// `s.TryAdoptSnapshotInBackground` retains a derived snapshot and
    /// attempts to adopt it as the session's current snapshot without
    /// blocking the caller.
    pub fn try_adopt_snapshot_in_background(
        self: &Arc<Self>,
        base_snapshot: &Arc<Snapshot>,
        new_snapshot: &Arc<Snapshot>,
    ) {
        self.host.retain_snapshot(new_snapshot);
        self.try_adopt_snapshot_change_in_background(base_snapshot, new_snapshot);
    }
}
