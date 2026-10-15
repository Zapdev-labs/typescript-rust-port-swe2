// Ported from tsc/internal/api/requestfilesystem/filechanges.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `baseFS.(project.LayeredFileSystem)` → the `as_layered` downcast;
// `s.FS()`-style `vfs.FS` values arrive as `Arc<dyn Vfs>` with an explicit
// `FileHandleSource` twin carried by `RequestFileSystem` itself.

use std::sync::Arc;

use rustc_hash::FxHashSet;
use tsc_collections::Set;
use tsc_lsconv::file_name_to_document_uri;
use tsc_lsproto::DocumentUri;
use tsc_project::filechange::FileChangeSummary;
use tsc_project::overlayfs::{FileHandle, LayeredFileSystem};
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, rooted_file_path_from_path, rooted_directory_path_from_path, to_rooted_path};
use tsc_vfs::Vfs;

use crate::requestfilesystem::{
    RequestFileSystem, RequestFileSystemParams, as_layered, get_request_file_system,
};

/// `(s *requestFileSystem) ExpandFileChanges` — every changed, created, or
/// deleted URI expands through the symlink aliases this filesystem knows.
pub fn expand_file_changes(
    s: &RequestFileSystem,
    mut summary: FileChangeSummary,
) -> FileChangeSummary {
    let expand = |uris: &mut Set<DocumentUri>| {
        let mut additional: FxHashSet<DocumentUri> = FxHashSet::default();
        for uri in uris.keys() {
            for alias in s.aliases_for_path(uri.file_name().as_path()) {
                additional.insert(file_name_to_document_uri(
                    &rooted_file_path_from_path(alias.clone()),
                ));
            }
        }
        for uri in additional {
            uris.add(uri);
        }
    };
    expand(&mut summary.changed);
    expand(&mut summary.created);
    expand(&mut summary.deleted);
    summary
}

/// `addFileChanges`
pub fn add_file_changes(
    summary: &mut FileChangeSummary,
    request: &RequestFileSystemParams,
    base_fs: &Arc<dyn Vfs>,
    file_system: &RequestFileSystem,
    current_directory: &RootedDirectoryPath,
) {
    let case_sensitivity: CaseSensitivity = base_fs.case_sensitivity();
    let base_request_fs = get_request_file_system(base_fs);
    let add_change = |file_name: &tsc_tspath::RootedPath, deleted: bool, summary: &mut FileChangeSummary| {
        let uri = file_name_to_document_uri(&rooted_file_path_from_path(file_name.clone()));
        if deleted {
            if base_fs.file_exists(&rooted_file_path_from_path(file_name.clone()))
                || base_fs.directory_exists(&rooted_directory_path_from_path(file_name.clone()))
            {
                summary.deleted.add(uri);
            }
            return;
        }
        if base_fs.file_exists(&rooted_file_path_from_path(file_name.clone())) {
            summary.changed.add(uri);
        } else {
            summary.created.add(uri);
        }
    };
    let add_change_and_aliases =
        |file_name: &tsc_tspath::RootedPath, deleted: bool, summary: &mut FileChangeSummary| {
            add_change(file_name, deleted, summary);
            if let Some(base_request_fs) = base_request_fs {
                for alias in base_request_fs.aliases_for_path(file_name.clone()) {
                    add_change(&alias, deleted, summary);
                }
            }
        };
    let mut overlay_files: FxHashSet<PathKey> = FxHashSet::default();
    for file_name in request.files.keys() {
        let absolute_file_name = to_rooted_path(file_name, current_directory);
        overlay_files.insert(case_sensitivity.path_key(&absolute_file_name));
        add_change_and_aliases(&absolute_file_name, false, summary);
    }
    for removed_path in &request.removed_paths {
        let absolute_path = to_rooted_path(removed_path, current_directory);
        if overlay_files.contains(&case_sensitivity.path_key(&absolute_path)) {
            continue;
        }
        add_change_and_aliases(&absolute_path, true, summary);
    }
    // Replacing a listing or a symlink can change every cached descendant.
    // Delete events expand through the snapshot's cached directory tree and
    // create events that refresh wildcard roots and previously missing
    // module resolutions.
    let add_replacement = |path: &str, summary: &mut FileChangeSummary| {
        let absolute_path = to_rooted_path(path, current_directory);
        add_change_and_aliases(&absolute_path, true, summary);
        summary.created.add(file_name_to_document_uri(
            &rooted_file_path_from_path(absolute_path.clone()),
        ));
        if let Some(base_request_fs) = base_request_fs {
            for alias in base_request_fs.aliases_for_path(absolute_path.clone()) {
                summary.created.add(file_name_to_document_uri(
                    &rooted_file_path_from_path(alias.clone()),
                ));
            }
        }
    };
    for directory_name in request.directories.keys() {
        add_replacement(directory_name, summary);
    }
    for link_name in request.symlinks.keys() {
        add_replacement(link_name, summary);
    }
    if let Some(layered_base) = as_layered(base_fs) {
        let overlays = file_system.overlays();
        for (path, overlay) in layered_base.overlays() {
            if overlays.contains_key(&path) {
                continue;
            }
            let uri = file_name_to_document_uri(overlay.file_name());
            if summary.closed.has(&uri) {
                continue;
            }
            summary.created.delete(&uri);
            if file_system.file_exists(overlay.file_name()) {
                summary.deleted.delete(&uri);
                summary.changed.add(uri);
            } else {
                summary.changed.delete(&uri);
                summary.deleted.add(uri);
            }
        }
    }
    if summary.changed.len() + summary.created.len() + summary.deleted.len() > 0 {
        summary.includes_watch_change_outside_node_modules = true;
    }
}
