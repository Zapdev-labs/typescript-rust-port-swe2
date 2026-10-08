// Ported from tsc/internal/execute/watchmanager/watchmanager_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io;
use std::sync::{Arc, Mutex};

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath};

use crate::watchbackend::{WatchBackend, WatchDirectoryRequest, WatchHandle};
use crate::watchmanager::{new_dir_watch_set, new_watch_manager};

const CASE_SENSITIVE: CaseSensitivity = CaseSensitivity::CaseSensitive;
const CASE_INSENSITIVE: CaseSensitivity = CaseSensitivity::CaseInsensitive;

fn dir(s: &str) -> RootedDirectoryPath {
    RootedDirectoryPath::from(s)
}

fn set(s: &[&str]) -> FxHashSet<RootedDirectoryPath> {
    s.iter().map(|p| dir(p)).collect()
}

fn desired(s: &[(&str, bool)]) -> FxHashMap<RootedDirectoryPath, bool> {
    s.iter().map(|(p, r)| (dir(p), *r)).collect()
}

// `TestDirWatchSetCoverage` — a recursive watch covers itself and all
// descendants, while a non-recursive watch covers only itself. Ancestors
// and unrelated paths are never covered.
#[test]
fn dir_watch_set_coverage() {
    let mut set = new_dir_watch_set(CASE_SENSITIVE);
    set.set(dir("/repo/src"), true); // recursive
    set.set(dir("/repo/config"), false); // non-recursive
    set.set(dir("/repo/node_modules/a"), false); // non-recursive

    let tests: &[(&str, bool)] = &[
        ("/repo/src", true),             // exact recursive
        ("/repo/src/nested", true),      // descendant of recursive
        ("/repo/src/nested/deep", true), // deep descendant of recursive
        ("/repo/config", true),          // exact non-recursive
        ("/repo/config/nested", false),  // descendant of non-recursive: NOT covered
        ("/repo/node_modules/a", true),  // exact non-recursive
        ("/repo/node_modules/b", false), // sibling, absent
        ("/repo", false),                // ancestor of watched dirs: NOT covered
        ("/other", false),               // unrelated
    ];
    for (path, want) in tests {
        assert_eq!(set.covered(&dir(path)), *want, "Covered({path:?})");
    }
}

// `TestDirWatchSetCaseSensitive` — on a case-sensitive filesystem a
// differently-cased directory is a distinct, uncovered directory.
#[test]
fn dir_watch_set_case_sensitive() {
    let mut set = new_dir_watch_set(CASE_SENSITIVE);
    set.set(dir("/repo/node_modules/a"), false);
    set.set(dir("/repo/Src"), true);

    assert!(set.covered(&dir("/repo/node_modules/a")));
    assert!(
        !set.covered(&dir("/repo/node_modules/A")),
        "case-sensitive FS must not cover differently-cased dir"
    );
    assert!(
        set.covered(&dir("/repo/Src/nested")),
        "recursive descendant with matching case is covered"
    );
    assert!(
        !set.covered(&dir("/repo/src/nested")),
        "case-sensitive FS must not cover differently-cased descendant"
    );
}

// `TestDirWatchSetCaseInsensitive` — on a case-insensitive filesystem
// coverage ignores casing for both exact matches and recursive containment.
#[test]
fn dir_watch_set_case_insensitive() {
    let mut set = new_dir_watch_set(CASE_INSENSITIVE);
    set.set(dir("/repo/node_modules/a"), false);
    set.set(dir("/repo/Src"), true);

    assert!(
        set.covered(&dir("/repo/node_modules/A")),
        "exact match should be case-insensitive"
    );
    assert!(
        set.covered(&dir("/REPO/NODE_MODULES/a")),
        "exact match should be case-insensitive across components"
    );
    assert!(
        set.covered(&dir("/repo/src/nested/deep")),
        "recursive containment should be case-insensitive"
    );
}

// `TestDirWatchSetCanonicalDedup` — on a case-insensitive filesystem
// directories that differ only by casing collapse to a single entry while
// retaining the spelling used for the actual watch request. A
// case-sensitive filesystem keeps them distinct.
#[test]
fn dir_watch_set_canonical_dedup() {
    let mut insensitive = new_dir_watch_set(CASE_INSENSITIVE);
    insensitive.set(dir("/repo/Node_Modules/PkgName"), false);
    insensitive.set(dir("/repo/node_modules/pkgname"), false); // same dir, different casing

    let dirs = insensitive.dirs();
    assert_eq!(
        dirs.len(),
        1,
        "differently-cased dirs must collapse to one entry"
    );
    assert!(
        dirs.contains_key(&dir("/repo/Node_Modules/PkgName")),
        "Dirs must retain the first requested spelling"
    );

    let mut sensitive = new_dir_watch_set(CASE_SENSITIVE);
    sensitive.set(dir("/repo/Node_Modules/PkgName"), false);
    sensitive.set(dir("/repo/node_modules/pkgname"), false); // distinct dirs when case-sensitive
    assert_eq!(
        sensitive.dirs().len(),
        2,
        "case-sensitive FS keeps differently-cased dirs distinct"
    );
}

// `TestDirWatchSetUpgradeToRecursive` — upgrading a directory from
// non-recursive to recursive begins covering its descendants.
#[test]
fn dir_watch_set_upgrade_to_recursive() {
    let mut set = new_dir_watch_set(CASE_SENSITIVE);
    set.set(dir("/repo/src"), false);
    assert!(set.covered(&dir("/repo/src")));
    assert!(
        !set.covered(&dir("/repo/src/nested")),
        "descendant not covered while non-recursive"
    );

    set.set(dir("/repo/src"), true);
    assert!(
        set.covered(&dir("/repo/src/nested")),
        "descendant covered after upgrade to recursive"
    );
    assert!(set.dirs()[&dir("/repo/src")]);
}

// `TestDirWatchSetNeverDowngrades` — a recursive watch is not downgraded by
// a subsequent non-recursive `Set` of the same directory.
#[test]
fn dir_watch_set_never_downgrades() {
    let mut set = new_dir_watch_set(CASE_SENSITIVE);
    set.set(dir("/repo/src"), true);
    set.set(dir("/repo/src"), false);

    assert!(set.dirs()[&dir("/repo/src")]);
    assert!(
        set.covered(&dir("/repo/src/nested")),
        "recursive coverage retained after non-recursive Set"
    );
}

// `TestDirWatchSetDirs` — the emitted map reflects every added directory
// with the expected recursive flags.
#[test]
fn dir_watch_set_dirs() {
    let mut set = new_dir_watch_set(CASE_SENSITIVE);
    set.set(dir("/repo/a"), false);
    set.set(dir("/repo/b"), true);
    set.set(dir("/repo/a"), false); // duplicate non-recursive add is idempotent

    let dirs = set.dirs();
    assert_eq!(dirs.len(), 2);
    assert!(!dirs[&dir("/repo/a")]);
    assert!(dirs[&dir("/repo/b")]);
}

// `TestResolveDesiredDirsShallowProject` — a directory that exists and was
// asked for is watched at any depth. A project close to the filesystem root
// (/app, /srv/app, a Docker WORKDIR) must not be silently ignored.
#[test]
fn resolve_desired_dirs_shallow_project() {
    let existing = set(&[
        "/", "/app", "/app/src", "/srv", "/srv/app", "/home", "/home/user",
        "/home/user/project",
    ]);
    let wm = new_watch_manager(
        Box::new(io::sink()),
        move |dir: &RootedDirectoryPath| existing.contains(dir),
        CASE_SENSITIVE,
    );

    let resolved = wm.resolve_desired_dirs(desired(&[
        ("/app", true),
        ("/app/src", false),
        ("/srv/app", true),
        ("/home/user/project", true),
    ]));

    assert_eq!(
        resolved,
        desired(&[
            ("/app", true),
            ("/app/src", false),
            ("/srv/app", true),
            ("/home/user/project", true),
        ])
    );
}

// `TestResolveDesiredDirsAncestorFallback` — the depth check still guards
// the fallback to an ancestor, so a missing directory never turns into a
// watch on something too generic like /, /home or /home/user.
#[test]
fn resolve_desired_dirs_ancestor_fallback() {
    let existing = set(&[
        "/", "/app", "/home", "/home/user", "/repo", "/repo/a", "/repo/a/b",
        "/repo/a/b/c",
    ]);
    let wm = new_watch_manager(
        Box::new(io::sink()),
        move |dir: &RootedDirectoryPath| existing.contains(dir),
        CASE_SENSITIVE,
    );

    let resolved = wm.resolve_desired_dirs(desired(&[
        ("/app/missing", true), // ancestor /app is too shallow
        ("/home/user/missing", true), // ancestor /home/user is too shallow
        ("/repo/a/b/c/missing/deep", true), // ancestor /repo/a/b/c is deep enough, and is never recursive
        ("/nothing/exists/anywhere", true), // no existing ancestor except /
    ]));

    assert_eq!(resolved, desired(&[("/repo/a/b/c", false)]));
}

// `TestResolveDesiredDirsSkipsNonDiskPaths` — a directory that is not on
// disk, such as the embedded libs (bundled:///libs), is never watched, even
// though the wrapped FS reports that it exists.
#[test]
fn resolve_desired_dirs_skips_non_disk_paths() {
    let wm = new_watch_manager(
        Box::new(io::sink()),
        |_dir: &RootedDirectoryPath| true,
        CASE_SENSITIVE,
    );

    let resolved = wm.resolve_desired_dirs(desired(&[
        ("bundled:///libs", false),
        ("/app", true),
    ]));

    assert_eq!(resolved, desired(&[("/app", true)]));
}

// `TestResolveDesiredDirsDeduplicatesCaseInsensitiveAncestors`.
#[test]
fn resolve_desired_dirs_deduplicates_case_insensitive_ancestors() {
    let manager = new_watch_manager(
        Box::new(io::sink()),
        |dir: &RootedDirectoryPath| dir.as_string().eq_ignore_ascii_case("/home/repo/project/src"),
        CASE_INSENSITIVE,
    );
    let resolved = manager.resolve_desired_dirs(desired(&[
        ("/home/Repo/Project/Src/missing/a", false),
        ("/home/repo/project/src/missing/b", true),
    ]));

    assert_eq!(resolved.len(), 1);
    for (dir, recursive) in &resolved {
        assert!(dir.as_string().eq_ignore_ascii_case("/home/repo/project/src"));
        assert!(!recursive);
    }
}

// `recordingWatchBackend` — collects requests, returns no-op closers.
struct NopCloser;

impl WatchHandle for NopCloser {
    fn close(&self) {}
}

struct RecordingWatchBackend {
    requests: Mutex<Vec<WatchDirectoryRequest>>,
}

impl WatchBackend for RecordingWatchBackend {
    fn watch_directories(
        &self,
        requests: Vec<WatchDirectoryRequest>,
    ) -> Result<Vec<Box<dyn WatchHandle>>, tsc_fswatch::Error> {
        let count = requests.len();
        self.requests.lock().unwrap().extend(requests);
        Ok((0..count)
            .map(|_| Box::new(NopCloser) as Box<dyn WatchHandle>)
            .collect())
    }
}

// `TestReconcileWatchesIgnoresCaseOnlySpellingChanges`.
#[test]
fn reconcile_watches_ignores_case_only_spelling_changes() {
    let manager = new_watch_manager(
        Box::new(io::sink()),
        |_: &RootedDirectoryPath| true,
        CASE_INSENSITIVE,
    );
    let backend = Arc::new(RecordingWatchBackend {
        requests: Mutex::new(Vec::new()),
    });
    manager.set_backend(backend.clone());

    {
        let mut guard = manager.lock();
        guard
            .reconcile_watches(desired(&[("/Repo", false)]))
            .unwrap();
    }
    {
        let mut guard = manager.lock();
        guard
            .reconcile_watches(desired(&[("/repo", false)]))
            .unwrap();
    }

    let requests = backend.requests.lock().unwrap();
    assert_eq!(requests.len(), 1);
    assert_eq!(requests[0].dir.as_string(), "/Repo");
}
