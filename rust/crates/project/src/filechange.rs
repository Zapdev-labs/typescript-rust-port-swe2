// Ported from tsc/internal/project/filechange.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_collections::Set;
use tsc_lsproto::{DocumentUri, LanguageKind, TextDocumentContentChangePartialOrWholeDocument};

/// `excessiveChangeThreshold`.
pub const EXCESSIVE_CHANGE_THRESHOLD: usize = 1000;

/// `FileChangeExpander`.
pub trait FileChangeExpander {
    fn expand_file_changes(&self, summary: FileChangeSummary) -> FileChangeSummary;
}

/// `FileChangeKind`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub enum FileChangeKind {
    #[default]
    Open,
    Close,
    Change,
    Save,
    WatchCreate,
    WatchChange,
    WatchDelete,
}

impl FileChangeKind {
    /// `(k FileChangeKind) IsWatchKind`.
    pub fn is_watch_kind(&self) -> bool {
        matches!(
            self,
            FileChangeKind::WatchCreate | FileChangeKind::WatchChange | FileChangeKind::WatchDelete
        )
    }
}

/// `FileChange`.
#[derive(Clone, Default)]
pub struct FileChange {
    pub kind: FileChangeKind,
    pub uri: DocumentUri,
    /// Only set for Open/Change.
    pub version: i32,
    /// Only set for Open.
    pub content: String,
    /// Only set for Open.
    pub language_kind: LanguageKind,
    /// Only set for Change.
    pub changes: Vec<TextDocumentContentChangePartialOrWholeDocument>,
}

/// `FileChangeSummary`.
#[derive(Clone, Default)]
pub struct FileChangeSummary {
    /// Only one file can be opened at a time per request
    pub opened: DocumentUri,
    /// Reopened is set if a close and open occurred for the same file in a
    /// single batch of changes.
    pub reopened: DocumentUri,
    pub closed: Set<DocumentUri>,
    pub changed: Set<DocumentUri>,
    /// Only set when file watching is enabled
    pub created: Set<DocumentUri>,
    /// Only set when file watching is enabled
    pub deleted: Set<DocumentUri>,

    /// IncludesWatchChangeOutsideNodeModules is true if the summary includes a
    /// create, change, or delete watch event of a file outside a node_modules
    /// directory.
    pub includes_watch_change_outside_node_modules: bool,
    /// InvalidateAll indicates that all cached file state should be discarded.
    pub invalidate_all: bool,
}

impl FileChangeSummary {
    /// `(f FileChangeSummary) Clone` — `Clone::clone` on the sets is already a
    /// deep copy of each `FxHashSet`, matching Go's `Set.Clone`.
    /// (Method retained for parity with the Go API surface.)
    pub fn clone_summary(&self) -> FileChangeSummary {
        self.clone()
    }

    /// `(f FileChangeSummary) IsEmpty`.
    pub fn is_empty(&self) -> bool {
        !self.invalidate_all
            && self.opened.as_str().is_empty()
            && self.reopened.as_str().is_empty()
            && self.closed.len() == 0
            && self.changed.len() == 0
            && self.created.len() == 0
            && self.deleted.len() == 0
    }

    /// `(f FileChangeSummary) HasExcessiveWatchEvents`.
    pub fn has_excessive_watch_events(&self) -> bool {
        self.invalidate_all
            || self.created.len() + self.deleted.len() + self.changed.len()
                > EXCESSIVE_CHANGE_THRESHOLD
    }

    /// `(f FileChangeSummary) HasExcessiveNonCreateWatchEvents`.
    pub fn has_excessive_non_create_watch_events(&self) -> bool {
        self.invalidate_all || self.deleted.len() + self.changed.len() > EXCESSIVE_CHANGE_THRESHOLD
    }
}

/// `mergeFileChangeSummary` merges src into dst, combining their change sets.
pub fn merge_file_change_summary(dst: &mut FileChangeSummary, src: FileChangeSummary) {
    if src.is_empty() {
        return;
    }
    if src.invalidate_all {
        dst.invalidate_all = true;
    }
    for uri in src.changed.keys() {
        dst.changed.add(uri.clone());
    }
    for uri in src.created.keys() {
        dst.created.add(uri.clone());
    }
    for uri in src.deleted.keys() {
        dst.deleted.add(uri.clone());
    }
    if src.includes_watch_change_outside_node_modules {
        dst.includes_watch_change_outside_node_modules = true;
    }
}
