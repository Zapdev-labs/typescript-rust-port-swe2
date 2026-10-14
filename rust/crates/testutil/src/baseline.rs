// Ported from tsc/internal/testutil/baseline/{baseline.go,testmain.go} @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `testing.TB` is dropped — `t.Error`/`t.Errorf` sites return
// `Err(Error)` (test callers unwrap or `?`), and `t.Error` inside
// `recordBaseline` becomes an `Err` with the same message. `baseline.Track`
// returns a [TrackGuard] whose `Drop` writes the tracking file, replacing
// Go's `defer baseline.Track()()`. Go hashes `runtime.Callers` frame
// filenames to name the tracking file per calling package; the port hashes
// backtrace frame filenames (falling back to symbol names), which is unique
// per caller but does not reproduce Go's FNV-1a hash values — tracking file
// names differ from the Go tool's (they are internal to the test run).
// `DiffText`'s Go `string` lines are `[u8]` lines; see baseline/patience.rs.

mod patience;

use std::env;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::LazyLock;
use std::sync::atomic::{AtomicBool, Ordering};
use std::{fs, process};

use tsc_collections::SyncSet;
use tsc_repo::test_data_path;
use tsc_stringutil::split_lines;

use crate::Error;

/// DiffFixup is `func(string) string` — a pre-diff content transformer.
pub type DiffFixup = Box<dyn Fn(&str) -> String + Send + Sync>;

/// Options for [run].
#[derive(Default)]
pub struct Options {
    pub subfolder: String,
    /// DiffFixupOld is reserved for callers of [diff_text] (e.g. tsbaseline);
    /// `run` itself does not apply it, matching Go.
    pub diff_fixup_old: Option<DiffFixup>,
    pub diff_fixup_new: Option<DiffFixup>,
    pub skip_diff_with_old: bool,
}

/// NoContent is the sentinel actual-content value meaning "no baselining
/// is required".
pub const NO_CONTENT: &str = "<no content>";

/// Run compares `actual` against the reference baseline for `file_name`
/// (under `opts.subfolder`), writing the local baseline on mismatch.
///
/// Go: `baseline.Run(t, fileName, actual, opts)` — errors that Go reports
/// via `t.Error`/`t.Errorf` come back as `Err`.
pub fn run(file_name: &str, actual: &str, opts: &Options) -> Result<(), Error> {
    let subfolder = &opts.subfolder;
    let local_path = Path::new(&*LOCAL_ROOT).join(subfolder).join(file_name);
    let reference_path = Path::new(&*REFERENCE_ROOT).join(subfolder).join(file_name);
    record_baseline(&Path::new(subfolder).join(file_name).to_string_lossy())?;
    write_comparison(actual, &local_path, &reference_path)
}

/// DiffText returns a unified diff (3 lines of context) between `expected`
/// and `actual` with the given header names.
pub fn diff_text(old_name: &str, new_name: &str, expected: &[u8], actual: &[u8]) -> Vec<u8> {
    let diffs = patience::diff(&split_lines(expected), &split_lines(actual));
    patience::unified_diff_text_with_options(
        &diffs,
        &patience::UnifiedDiffOptions {
            precontext: 3,
            postcontext: 3,
            src_header: old_name,
            dst_header: new_name,
        },
    )
}

fn write_comparison(actual_content: &str, local: &Path, reference: &Path) -> Result<(), Error> {
    if actual_content.is_empty() {
        panic!(
            "the generated content was \"\". Return 'baseline.NO_CONTENT' if no baselining is required."
        );
    }
    // filepath.Dir(local) — local always has a file name, so parent() is Some.
    let dir = local.parent().unwrap_or_else(|| Path::new(""));
    if let Err(err) = fs::create_dir_all(dir) {
        return Err(Error::wrap(
            format!(
                "failed to create directories for the local baseline file {}",
                local.display()
            ),
            err,
        ));
    }
    if local.try_exists().unwrap_or(false) {
        if let Err(err) = fs::remove_file(local) {
            return Err(Error::wrap(
                format!(
                    "failed to remove the local baseline file {}",
                    local.display()
                ),
                err,
            ));
        }
    }

    let actual_bytes = tsc_vfs::internal::faithful_bytes(actual_content);
    let mut expected: Vec<u8> = NO_CONTENT.as_bytes().to_vec();
    let mut found_expected = false;
    if let Ok(content) = fs::read(reference) {
        expected = content;
        found_expected = true;
    }
    if expected == actual_bytes && !(actual_content == NO_CONTENT && found_expected) {
        return Ok(());
    }
    if actual_content == NO_CONTENT {
        // Go: os.WriteFile(local+".delete", []byte{}, 0o644)
        let mut delete_path = local.as_os_str().to_os_string();
        delete_path.push(".delete");
        if let Err(err) = fs::write(&delete_path, b"") {
            return Err(Error::wrap(
                format!(
                    "failed to write the local baseline file {}",
                    Path::new(&delete_path).display()
                ),
                err,
            ));
        }
        return Ok(());
    }
    if let Err(err) = fs::write(local, &actual_bytes) {
        return Err(Error::wrap(
            format!(
                "failed to write the local baseline file {}",
                local.display()
            ),
            err,
        ));
    }
    if !found_expected {
        return Err(Error::new(format!(
            "new baseline created at {}.",
            local.display()
        )));
    }
    Err(Error::new(format!(
        "the baseline file {} has changed. (Run `hereby baseline-accept` if the new baseline is correct.)",
        reference.display()
    )))
}

static LOCAL_ROOT: LazyLock<PathBuf> =
    LazyLock::new(|| Path::new(test_data_path()).join("baselines").join("local"));
static REFERENCE_ROOT: LazyLock<PathBuf> = LazyLock::new(|| {
    Path::new(test_data_path())
        .join("baselines")
        .join("reference")
});

// testmain.go — baseline tracking.
//
// Go package-level vars: `recordedBaselines` (a collections.SyncSet),
// `trackingInitialized`, and `trackingDir = os.Getenv("TSGO_BASELINE_TRACKING_DIR")`
// read once at package init — a LazyLock captures the same read-once semantics.
static RECORDED_BASELINES: LazyLock<SyncSet<String>> = LazyLock::new(SyncSet::new);
static TRACKING_INITIALIZED: AtomicBool = AtomicBool::new(false);
static TRACKING_DIR: LazyLock<Option<PathBuf>> = LazyLock::new(|| {
    env::var_os("TSGO_BASELINE_TRACKING_DIR")
        .map(PathBuf::from)
        .filter(|p| !p.as_os_str().is_empty())
});

/// TrackGuard writes the recorded-baselines tracking file when dropped.
/// See [track].
#[derive(Debug)]
pub struct TrackGuard {
    tracking_path: Option<PathBuf>,
}

impl Drop for TrackGuard {
    fn drop(&mut self) {
        // After tests complete, write the recorded baselines.
        if let Some(path) = &self.tracking_path {
            write_recorded_baselines(path);
        }
    }
}

const FNV_OFFSET_64A: u64 = 0xcbf29ce484222325;
const FNV_PRIME_64: u64 = 0x100000001b3;

fn fnv1a_update(h: &mut u64, data: &[u8]) {
    for &b in data {
        *h ^= u64::from(b);
        *h = h.wrapping_mul(FNV_PRIME_64);
    }
}

/// Track sets up baseline tracking and returns a guard whose `Drop` writes
/// the tracking file. Rust idiom:
///
/// ```ignore
/// let _baseline_tracking = baseline::track();
/// ```
pub fn track() -> TrackGuard {
    TRACKING_INITIALIZED.store(true, Ordering::SeqCst);

    let Some(tracking_dir) = &*TRACKING_DIR else {
        return TrackGuard {
            tracking_path: None,
        };
    };

    // Hash the entire call stack to create a unique filename per calling
    // package. This must be done in track(), not in the dropped cleanup,
    // because the Drop won't include the caller's frames.
    //
    // PORT: Go hashes each runtime.Callers frame's file;
    // `Backtrace::frames`/`BacktraceSymbol::filename` are unstable (issue
    // #79676), so the port hashes the rendered backtrace (which resolves
    // symbol names and file:line when debuginfo is present). Unique per
    // caller; hash values do not match Go's.
    let mut h = FNV_OFFSET_64A;
    let backtrace = format!("{:#}", std::backtrace::Backtrace::capture());
    fnv1a_update(&mut h, backtrace.as_bytes());
    TrackGuard {
        tracking_path: Some(tracking_dir.join(format!("{h:016x}.txt"))),
    }
}

/// recordBaseline adds a baseline file path to the recorded set.
/// The path should be relative to the baselines/reference directory.
fn record_baseline(relative_path: &str) -> Result<(), Error> {
    if TRACKING_DIR.is_some() {
        if !TRACKING_INITIALIZED.load(Ordering::SeqCst) {
            // PORT: the Go message references TestMain; the Rust idiom holds
            // a track() guard for the duration of the test run.
            return Err(Error::new(
                "baseline: test uses baselines but baseline::track() was not called. \
                 Please hold a `baseline::track()` guard for the duration of the test run.",
            ));
        }
        RECORDED_BASELINES.add(relative_path.to_string());
    }
    Ok(())
}

/// writeRecordedBaselines writes the list of recorded baseline files to a tracking file.
fn write_recorded_baselines(tracking_path: &Path) {
    if RECORDED_BASELINES.is_empty() {
        return;
    }

    if let Err(err) = do_write_recorded_baselines(tracking_path) {
        // Go: fmt.Fprintf(os.Stderr, ...) + os.Exit(1).
        eprintln!(
            "baseline: failed to write tracking file {}: {err}",
            tracking_path.display()
        );
        process::exit(1);
    }
}

fn do_write_recorded_baselines(tracking_path: &Path) -> std::io::Result<()> {
    let f = fs::File::create(tracking_path)?;
    let mut w = BufWriter::new(f);
    for baseline in RECORDED_BASELINES.keys() {
        writeln!(w, "{baseline}")?;
    }
    w.flush()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diff_text_changed_line() {
        let diff = diff_text("expected", "actual", b"a\nb\nc\n", b"a\nx\nc\n");
        assert_eq!(
            diff,
            b"--- expected\n+++ actual\n@@ -1,3 +1,3 @@\n a\n-b\n+x\n c".to_vec()
        );
    }

    #[test]
    fn diff_text_identical() {
        // No hunks when identical; headers still emitted (same as Go).
        let diff = diff_text("a", "b", b"same\n", b"same\n");
        assert_eq!(diff, b"--- a\n+++ b".to_vec());
    }

    #[test]
    fn diff_text_new_lines_at_end() {
        let diff = diff_text("expected", "actual", b"a\n", b"a\nb\n");
        assert_eq!(
            diff,
            b"--- expected\n+++ actual\n@@ -1,1 +1,2 @@\n a\n+b".to_vec()
        );
    }

    #[test]
    fn track_guard_no_tracking_dir_is_noop() {
        // TSGO_BASELINE_TRACKING_DIR is unset in tests; dropping the guard
        // must not write anything.
        let guard = track();
        drop(guard);
    }

    #[test]
    #[should_panic(expected = "NO_CONTENT")]
    fn write_comparison_empty_panics() {
        write_comparison("", Path::new("/tmp/x"), Path::new("/tmp/y")).unwrap();
    }

    #[test]
    fn write_comparison_delete_marker() {
        // Reference baseline exists with content; actual is NO_CONTENT ->
        // writes <local>.delete and returns Ok.
        let dir = crate::TempDir::new();
        let reference = dir.path().join("ref").join("f.baseline");
        fs::create_dir_all(reference.parent().unwrap()).unwrap();
        fs::write(&reference, b"old").unwrap();
        let local = dir.path().join("loc").join("f.baseline");
        write_comparison(NO_CONTENT, &local, &reference).unwrap();
        let mut delete_path = local.as_os_str().to_os_string();
        delete_path.push(".delete");
        assert!(Path::new(&delete_path).exists());
        assert!(!local.exists());
    }

    #[test]
    fn write_comparison_new_baseline() {
        let dir = crate::TempDir::new();
        let local = dir.path().join("loc").join("f.baseline");
        let reference = dir.path().join("ref").join("f.baseline");
        let err = write_comparison("new content", &local, &reference).unwrap_err();
        assert!(err.to_string().contains("new baseline created at"));
        assert_eq!(fs::read(&local).unwrap(), b"new content");
    }

    #[test]
    fn write_comparison_unchanged() {
        let dir = crate::TempDir::new();
        let reference = dir.path().join("f.baseline");
        fs::write(&reference, b"same").unwrap();
        let local = dir.path().join("other.baseline");
        write_comparison("same", &local, &reference).unwrap();
        assert!(!local.exists());
    }
}
