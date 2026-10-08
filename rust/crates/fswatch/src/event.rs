// Ported from tsc/internal/fswatch/event.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fmt;
use std::sync::Mutex;

use rustc_hash::FxHashMap;

use crate::error::Error;

/// `EventKind` classifies a filesystem change.
///
/// PORT: Go's `EventKind int` with `iota` values becomes a Rust enum; the
/// discriminants preserve Go's ordinals (`EventUpdate` = 1, `EventDelete` = 2).
/// Go's `String()` maps to `Display` ("update"/"delete").
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(i32)]
pub enum EventKind {
    /// `EventUpdate` — a path was created or modified. Like Go, create and
    /// update are deliberately not distinguished.
    Update = 1,
    /// `EventDelete` — a path was deleted or moved away.
    Delete = 2,
}

impl fmt::Display for EventKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EventKind::Update => f.write_str("update"),
            EventKind::Delete => f.write_str("delete"),
        }
    }
}

/// `Event` describes a single filesystem change.
///
/// PORT: Go composite literals (`fswatch.Event{Kind, Path}`) work from
/// outside the package because the remaining field is unexported; Rust
/// requires all fields, so `Event::new` stands in for them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Event {
    /// `Kind` — whether the path was updated or deleted.
    pub kind: EventKind,
    /// `Path` — the changed path, rooted at the watched directory as supplied
    /// by the caller (not the physical/realpath root).
    ///
    /// PORT: Go strings carry arbitrary bytes; Rust `String` requires UTF-8,
    /// so non-UTF-8 event paths are lossy-decoded at the backend boundary.
    pub path: String,
    /// `includedWatchRoot` — true when the event path is a watch root shared
    /// with a coarser watch (used to retain root-self update events when
    /// filtering). Only the consolidated-watch path sets it; the notify
    /// backend never consolidates, so it stays false in practice.
    pub(crate) included_watch_root: bool,
}

impl Event {
    /// `fswatch.Event{Kind: kind, Path: path}`.
    pub fn new(kind: EventKind, path: impl Into<String>) -> Event {
        Event {
            kind,
            path: path.into(),
            included_watch_root: false,
        }
    }
}

/// `eventEntry` tracks coalescing state during a debounce batch.
#[derive(Default)]
struct EventEntry {
    created_seq: u64,
    updated_seq: u64,
    deleted_seq: u64,
    included_watch_root: bool,
}

impl EventEntry {
    fn is_deleted(&self) -> bool {
        self.deleted_seq > self.created_seq && self.deleted_seq > self.updated_seq
    }

    fn kind_since(&self, start_seq: u64) -> Option<EventKind> {
        if self.deleted_seq > start_seq {
            if self.created_seq > start_seq
                && self.created_seq < self.deleted_seq
                && self.updated_seq < self.deleted_seq
            {
                return None;
            }
            return Some(EventKind::Delete);
        }
        let seq = self.created_seq.max(self.updated_seq);
        if seq > start_seq {
            return Some(EventKind::Update);
        }
        None
    }
}

/// `eventList` coalesces filesystem events by path within a debounce window.
///   - create after delete → update (rapid delete+recreate)
///   - `get_events`/`snapshot` skip entries that were both created and deleted
#[derive(Default)]
pub(crate) struct EventList {
    inner: Mutex<EventListInner>,
}

#[derive(Default)]
struct EventListInner {
    entries: FxHashMap<String, EventEntry>,
    err: Option<Error>,
    seq: u64,
}

impl EventListInner {
    fn get_or_create(&mut self, path: &str) -> &mut EventEntry {
        self.entries.entry(path.to_owned()).or_default()
    }

    fn next_seq(&mut self) -> u64 {
        self.seq += 1;
        self.seq
    }

    fn advance_seq(&mut self, seq: u64) {
        if seq > self.seq {
            self.seq = seq;
        }
    }

    fn create_locked(&mut self, path: &str, seq: u64) {
        let entry = self.get_or_create(path);
        if entry.is_deleted() {
            // Rapid delete+recreate: clear both flags so the entry
            // emits EventUpdate (the default for non-deleted entries).
            // https://github.com/parcel-bundler/watcher/issues/72
            entry.deleted_seq = 0;
            entry.created_seq = 0;
            entry.updated_seq = seq;
        } else {
            entry.created_seq = seq;
        }
    }

    fn update_locked(&mut self, path: &str, seq: u64) {
        self.get_or_create(path).updated_seq = seq;
    }

    fn remove_locked(&mut self, path: &str, seq: u64) {
        self.get_or_create(path).deleted_seq = seq;
    }

    /// `snapshotLocked` — the current set of pending events with
    /// create+delete pairs filtered out.
    fn snapshot(&self) -> Vec<Event> {
        self.snapshot_since(0)
    }

    fn snapshot_since(&self, start_seq: u64) -> Vec<Event> {
        let mut out = Vec::with_capacity(self.entries.len());
        for (path, e) in &self.entries {
            let Some(kind) = e.kind_since(start_seq) else {
                continue;
            };
            out.push(Event {
                kind,
                path: path.clone(),
                included_watch_root: e.included_watch_root,
            });
        }
        out
    }
}

impl EventList {
    /// `create` records a new-file event for path. Both create and update
    /// produce `EventUpdate` externally; sequence state tracks coalescing
    /// (create+delete within a batch cancels out).
    pub(crate) fn create(&self, path: &str) {
        let mut inner = self.inner.lock().unwrap();
        let seq = inner.next_seq();
        inner.create_locked(path, seq);
    }

    #[allow(dead_code)]
    pub(crate) fn create_at(&self, path: &str, seq: u64) {
        let mut inner = self.inner.lock().unwrap();
        inner.advance_seq(seq);
        inner.create_locked(path, seq);
    }

    /// `update` records an update event for path.
    pub(crate) fn update(&self, path: &str) {
        let mut inner = self.inner.lock().unwrap();
        let seq = inner.next_seq();
        inner.update_locked(path, seq);
    }

    #[allow(dead_code)]
    pub(crate) fn update_at(&self, path: &str, seq: u64) {
        let mut inner = self.inner.lock().unwrap();
        inner.advance_seq(seq);
        inner.update_locked(path, seq);
    }

    #[allow(dead_code)]
    pub(crate) fn update_watch_root_at(&self, path: &str, seq: u64) {
        let mut inner = self.inner.lock().unwrap();
        inner.advance_seq(seq);
        inner.update_locked(path, seq);
        inner.get_or_create(path).included_watch_root = true;
    }

    /// `remove` records a delete event for path.
    pub(crate) fn remove(&self, path: &str) {
        let mut inner = self.inner.lock().unwrap();
        let seq = inner.next_seq();
        inner.remove_locked(path, seq);
    }

    #[allow(dead_code)]
    pub(crate) fn remove_and_get_sequence(&self, path: &str) -> u64 {
        let mut inner = self.inner.lock().unwrap();
        let seq = inner.next_seq();
        inner.remove_locked(path, seq);
        seq
    }

    #[allow(dead_code)]
    pub(crate) fn remove_at(&self, path: &str, seq: u64) {
        let mut inner = self.inner.lock().unwrap();
        inner.advance_seq(seq);
        inner.remove_locked(path, seq);
    }

    #[allow(dead_code)]
    pub(crate) fn remove_watch_root_at(&self, path: &str, seq: u64) {
        let mut inner = self.inner.lock().unwrap();
        inner.advance_seq(seq);
        inner.remove_locked(path, seq);
        inner.get_or_create(path).included_watch_root = true;
    }

    /// `size` returns the number of tracked entries (including ones that may
    /// cancel out in `get_events`).
    pub(crate) fn size(&self) -> usize {
        self.inner.lock().unwrap().entries.len()
    }

    /// `getEvents` returns a snapshot of events, skipping entries that were
    /// both created and deleted. Order is not guaranteed.
    #[allow(dead_code)]
    pub(crate) fn get_events(&self) -> Vec<Event> {
        self.inner.lock().unwrap().snapshot()
    }

    /// `drain` atomically snapshots all pending events and the stored error,
    /// then clears the list. This prevents events added between a separate
    /// get+clear from being silently dropped.
    pub(crate) fn drain(&self) -> (Vec<Event>, Option<Error>) {
        let mut inner = self.inner.lock().unwrap();
        let out = inner.snapshot();
        let err = inner.err.take();
        inner.entries.clear();
        (out, err)
    }

    /// `drainForSequences` snapshots each callback's events since its own
    /// start sequence, then clears the list.
    pub(crate) fn drain_for_sequences(
        &self,
        start_seqs: &[u64],
    ) -> (Vec<Vec<Event>>, Option<Error>) {
        let mut inner = self.inner.lock().unwrap();
        let out = start_seqs
            .iter()
            .map(|&start_seq| inner.snapshot_since(start_seq))
            .collect();
        let err = inner.err.take();
        inner.entries.clear();
        (out, err)
    }

    /// `setError` stores the first error encountered (later errors are ignored).
    pub(crate) fn set_error(&self, err: Error) {
        let mut inner = self.inner.lock().unwrap();
        if inner.err.is_none() {
            inner.err = Some(err);
        }
    }

    /// `hasError` reports whether an error has been recorded.
    pub(crate) fn has_error(&self) -> bool {
        self.inner.lock().unwrap().err.is_some()
    }

    /// `sequence` returns the current event sequence number.
    pub(crate) fn sequence(&self) -> u64 {
        self.inner.lock().unwrap().seq
    }
}
