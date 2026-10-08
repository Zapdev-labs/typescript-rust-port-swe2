// Smoke tests for the notify-backed port of tsc/internal/fswatch.
// Go's per-backend tests (watcher_test.go, inotify fanotify/fsevents/kqueue
// suites) exercise syscall-level details that do not exist here; these cover
// the consumed contract: batched EventUpdate/EventDelete delivery, recursive
// and ignore options, WatchFile, and ErrWatchTerminated on root deletion.

use std::fs;
use std::path::PathBuf;
use std::sync::Arc;
use std::sync::mpsc::{Receiver, channel};
use std::time::{Duration, Instant};

use crate::event::EventList;
use crate::{
    ERR_OVERFLOW, ERR_WATCH_TERMINATED, Error, Event, EventKind, Watch, WatchCallback,
    WatchDirectoryRequest, default, with_ignore, with_recursive,
};

const BATCH_TIMEOUT: Duration = Duration::from_secs(10);
const QUIET_TIMEOUT: Duration = Duration::from_millis(300);

fn test_dir(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tsc-fswatch-test-{}-{name}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn dir_str(dir: &PathBuf) -> String {
    dir.to_string_lossy().into_owned()
}

fn collector() -> (WatchCallback, Receiver<(Vec<Event>, Option<Error>)>) {
    let (tx, rx) = channel();
    let cb: WatchCallback = Arc::new(move |events, err| {
        let _ = tx.send((events, err));
    });
    (cb, rx)
}

/// Receive batches until `pred` sees a matching event or the deadline hits;
/// returns all events observed.
fn collect_until(
    rx: &Receiver<(Vec<Event>, Option<Error>)>,
    pred: impl Fn(&Event) -> bool,
) -> (Vec<Event>, bool) {
    let deadline = Instant::now() + BATCH_TIMEOUT;
    let mut all = Vec::new();
    loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return (all, false);
        }
        match rx.recv_timeout(remaining) {
            Ok((events, _)) => {
                all.extend(events.iter().cloned());
                if events.iter().any(&pred) {
                    return (all, true);
                }
            }
            Err(_) => return (all, false),
        }
    }
}

/// Drain whatever batches arrive within `QUIET_TIMEOUT` — used to assert
/// nothing is delivered.
fn collect_quiet(rx: &Receiver<(Vec<Event>, Option<Error>)>) -> Vec<Event> {
    let mut all = Vec::new();
    while let Ok((events, _)) = rx.recv_timeout(QUIET_TIMEOUT) {
        all.extend(events);
    }
    all
}

#[test]
fn watch_directory_create_update_delete() {
    let dir = test_dir("basic");
    let file = dir.join("a.ts");
    let file_str = file.to_string_lossy().into_owned();

    let (cb, rx) = collector();
    let _watch = default()
        .watch_directory(&dir_str(&dir), cb, vec![])
        .unwrap();

    fs::write(&file, "let a = 1;\n").unwrap();
    let (_, found) = collect_until(&rx, |e| e.path == file_str && e.kind == EventKind::Update);
    assert!(found, "expected update event for {file_str}");

    fs::write(&file, "let a = 2;\n").unwrap();
    let (_, found) = collect_until(&rx, |e| e.path == file_str && e.kind == EventKind::Update);
    assert!(found, "expected update event for modified {file_str}");

    fs::remove_file(&file).unwrap();
    let (_, found) = collect_until(&rx, |e| e.path == file_str && e.kind == EventKind::Delete);
    assert!(found, "expected delete event for {file_str}");
}

#[test]
fn watch_directory_nonrecursive_ignores_nested() {
    let dir = test_dir("nonrec");
    let sub = dir.join("sub");
    let nested = sub.join("nested.ts");
    let nested_str = nested.to_string_lossy().into_owned();
    fs::create_dir(&sub).unwrap();

    let (cb, rx) = collector();
    let _watch = default()
        .watch_directory(&dir_str(&dir), cb, vec![])
        .unwrap();

    // Give the subscription a moment to arm before the change.
    std::thread::sleep(Duration::from_millis(100));
    fs::write(&nested, "x\n").unwrap();
    let events = collect_quiet(&rx);
    assert!(
        !events.iter().any(|e| e.path == nested_str),
        "non-recursive watch delivered nested event: {events:?}"
    );
}

#[test]
fn watch_directory_recursive_sees_nested() {
    let dir = test_dir("rec");
    let sub = dir.join("sub");
    let nested = sub.join("nested.ts");
    let nested_str = nested.to_string_lossy().into_owned();

    let (cb, rx) = collector();
    let _watch = default()
        .watch_directory(&dir_str(&dir), cb, vec![with_recursive()])
        .unwrap();

    fs::create_dir(&sub).unwrap();
    fs::write(&nested, "x\n").unwrap();
    let (_, found) = collect_until(&rx, |e| e.path == nested_str && e.kind == EventKind::Update);
    assert!(
        found,
        "recursive watch missed nested create for {nested_str}"
    );
}

#[test]
fn watch_directory_ignore_filter() {
    let dir = test_dir("ignore");
    let ignored = dir.join("ignored.ts");
    let kept = dir.join("kept.ts");
    let ignored_str = ignored.to_string_lossy().into_owned();
    let kept_str = kept.to_string_lossy().into_owned();

    let (cb, rx) = collector();
    let _watch = default()
        .watch_directory(
            &dir_str(&dir),
            cb,
            vec![with_ignore(|path| path.ends_with("ignored.ts"))],
        )
        .unwrap();

    fs::write(&ignored, "x\n").unwrap();
    fs::write(&kept, "x\n").unwrap();
    let (all, found) = collect_until(&rx, |e| e.path == kept_str && e.kind == EventKind::Update);
    assert!(found, "expected update event for {kept_str}");
    let mut all = all;
    all.extend(collect_quiet(&rx));
    assert!(
        !all.iter().any(|e| e.path == ignored_str),
        "ignored path was delivered: {all:?}"
    );
}

#[test]
fn watch_file_reports_file() {
    let dir = test_dir("file");
    let file = dir.join("watched.ts");
    let file_str = file.to_string_lossy().into_owned();

    let (cb, rx) = collector();
    let _watch = default().watch_file(&file_str, cb).unwrap();

    fs::write(&file, "x\n").unwrap();
    let (_, found) = collect_until(&rx, |e| e.path == file_str && e.kind == EventKind::Update);
    assert!(found, "expected update event for watched file {file_str}");
}

#[test]
fn watch_root_delete_terminates() {
    let dir = test_dir("term");
    let root = dir.join("watched");
    fs::create_dir(&root).unwrap();
    let root_str = root.to_string_lossy().into_owned();

    let (cb, rx) = collector();
    let _watch = default().watch_directory(&root_str, cb, vec![]).unwrap();

    std::thread::sleep(Duration::from_millis(100));
    fs::remove_dir(&root).unwrap();

    let deadline = Instant::now() + BATCH_TIMEOUT;
    let mut saw_delete = false;
    let mut saw_terminated = false;
    loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() || (saw_delete && saw_terminated) {
            break;
        }
        match rx.recv_timeout(remaining) {
            Ok((events, err)) => {
                saw_delete |= events
                    .iter()
                    .any(|e| e.path == root_str && e.kind == EventKind::Delete);
                saw_terminated |= err.is_some_and(|e| e.is(&ERR_WATCH_TERMINATED));
            }
            Err(_) => break,
        }
    }
    assert!(
        saw_terminated,
        "expected ErrWatchTerminated when watch root deleted"
    );
}

/// `eventList` coalescing rules from event.go, exercised directly.
#[test]
fn event_list_coalescing() {
    // create+update → one update.
    let el = EventList::default();
    el.create("/a");
    el.update("/a");
    let (events, err) = el.drain();
    assert!(err.is_none());
    assert_eq!(events, vec![Event::new(EventKind::Update, "/a")]);

    // create+delete within one batch → suppressed.
    let el = EventList::default();
    el.create("/a");
    el.remove("/a");
    let (events, err) = el.drain();
    assert!(err.is_none());
    assert!(events.is_empty());

    // update+delete → delete wins.
    let el = EventList::default();
    el.update("/a");
    el.remove("/a");
    let (events, _) = el.drain();
    assert_eq!(events, vec![Event::new(EventKind::Delete, "/a")]);

    // delete+recreate → update (parcel-bundler/watcher#72).
    let el = EventList::default();
    el.remove("/a");
    el.create("/a");
    let (events, _) = el.drain();
    assert_eq!(events, vec![Event::new(EventKind::Update, "/a")]);

    // drain clears state and the first error wins.
    let el = EventList::default();
    el.create("/a");
    let _ = el.drain();
    el.set_error(ERR_OVERFLOW);
    el.set_error(ERR_WATCH_TERMINATED);
    let (events, err) = el.drain();
    assert!(events.is_empty());
    assert!(err.unwrap().is(&ERR_OVERFLOW));
}

#[test]
fn watch_directories_batch_and_relative_path_error() {
    let dir = test_dir("batch");
    let (cb, rx) = collector();

    // Relative paths are rejected with errNotAbsolute.
    let err = default()
        .watch_directories(vec![WatchDirectoryRequest {
            dir: "relative/dir".to_owned(),
            callback: Some(Arc::clone(&cb)),
            options: vec![],
        }])
        .unwrap_err();
    assert!(matches!(err, Error::NotAbsolute), "unexpected error: {err}");

    // Missing callback is rejected with errNilCallback.
    let err = default()
        .watch_directories(vec![WatchDirectoryRequest {
            dir: dir_str(&dir),
            callback: None,
            options: vec![],
        }])
        .unwrap_err();
    assert!(matches!(err, Error::NilCallback), "unexpected error: {err}");

    // A batch over two directories arms both.
    let dir2 = test_dir("batch2");
    let file2 = dir2.join("b.ts");
    let file2_str = file2.to_string_lossy().into_owned();
    let watches: Vec<Watch> = default()
        .watch_directories(vec![
            WatchDirectoryRequest {
                dir: dir_str(&dir),
                callback: Some(Arc::clone(&cb)),
                options: vec![],
            },
            WatchDirectoryRequest {
                dir: dir_str(&dir2),
                callback: Some(cb),
                options: vec![],
            },
        ])
        .unwrap();
    assert_eq!(watches.len(), 2);

    fs::write(&file2, "x\n").unwrap();
    let (_, found) = collect_until(&rx, |e| e.path == file2_str && e.kind == EventKind::Update);
    assert!(found, "expected update event for {file2_str}");
    drop(watches);
}
