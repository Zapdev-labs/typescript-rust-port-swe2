// Ported from tsc/internal/testutil/testutil.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// tsc-testutil — port of tsc/internal/testutil and its dep-satisfied
// subpackages. One Rust module per Go subpackage.
//
// PORT: Go's `testing.TB` has no Rust equivalent. Everywhere Go takes a
// `testing.TB` for `t.Error`/`t.Fatalf`, the port returns `Result<_, Error>`
// (t.Error / t.Fatalf -> `Err`, which test callers `?` or `.unwrap()`), or
// panics where Go would panic. `t.Skip` has no equivalent: the helpers that
// Go implements with `t.Skip` are exposed as predicates (`exists`,
// `node_js_available`) — the caller early-returns instead. `t.TempDir` is
// ported as [TempDir], an RAII guard that removes the directory on drop.

use std::any::Any;
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::{env, fs, panic, process};

pub mod baseline;
pub mod contentmappertest;
pub mod filefixture;
pub mod fixtures;
pub mod fsbaselineutil;
pub mod harnessutil;
pub mod jstest;
pub mod parsetestutil;
pub mod race;
pub mod stringtestutil;
pub mod tsbaseline;

/// Error is the `t.Error`/`t.Fatalf` payload for helpers that Go reports
/// through `testing.TB`. Test callers unwrap or `?` it.
#[derive(Debug)]
pub struct Error {
    message: String,
}

impl Error {
    pub fn new(message: impl Into<String>) -> Error {
        Error {
            message: message.into(),
        }
    }

    /// Go: `t.Error(fmt.Errorf("%s: %w", context, err))` /
    /// `fmt.Errorf("%s: %w", context, err)`.
    pub fn wrap(context: impl fmt::Display, err: impl fmt::Display) -> Error {
        Error {
            message: format!("{context}: {err}"),
        }
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

impl std::error::Error for Error {}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Error {
        Error {
            message: e.to_string(),
        }
    }
}

impl From<String> for Error {
    fn from(message: String) -> Error {
        Error { message }
    }
}

impl From<&str> for Error {
    fn from(message: &str) -> Error {
        Error {
            message: message.to_string(),
        }
    }
}

/// AssertPanics asserts that `f` panics and that the panic payload equals
/// `expected`. Go compares `recover()` against `expected any` with
/// `assert.Equal`; the Rust port downcasts the `catch_unwind` payload to `T`.
///
/// PORT: Go's variadic `msgAndArgs ...any` assertion context is dropped —
/// Rust callers attach context with `#[should_panic]`-style test names or by
/// wrapping `f`.
pub fn assert_panics<T>(f: impl FnOnce() + panic::UnwindSafe, expected: &T)
where
    T: PartialEq + fmt::Debug + Send + 'static,
{
    let payload = match panic::catch_unwind(f) {
        Ok(()) => panic!("assert failed: expected panic, got none"),
        Err(payload) => payload,
    };
    match payload.downcast::<T>() {
        Ok(got) => {
            assert_eq!(&*got, expected, "panic payload mismatch");
        }
        Err(payload) => {
            panic!(
                "assert failed: panic payload type mismatch: {}",
                describe_payload(&payload)
            );
        }
    }
}

fn describe_payload(payload: &Box<dyn Any + Send>) -> String {
    if let Some(s) = payload.downcast_ref::<String>() {
        return s.clone();
    }
    if let Some(s) = payload.downcast_ref::<&'static str>() {
        return (*s).to_string();
    }
    "<non-string payload>".to_string()
}

/// RecoverAndFail converts a caught panic into a test failure carrying a
/// backtrace. Go's `defer testutil.RecoverAndFail(t, msg)` relies on
/// `recover()` inside the deferred function; the Rust idiom is:
///
/// ```ignore
/// let result = panic::catch_unwind(f);
/// if let Err(payload) = result {
///     testutil::recover_and_fail(msg, &payload);
/// }
/// ```
pub fn recover_and_fail(msg: &str, payload: &Box<dyn Any + Send>) -> ! {
    // Go: `t.Fatalf("%s:\n%v\n%s", msg, r, debug.Stack())`.
    panic!(
        "{msg}:\n{}\n{}",
        describe_payload(payload),
        std::backtrace::Backtrace::capture()
    );
}

fn test_program_is_single_threaded_init() -> bool {
    // Leave Program in SingleThreaded mode unless explicitly configured or in race mode.
    if let Ok(v) = env::var("TS_TEST_PROGRAM_SINGLE_THREADED") {
        if let Some(b) = parse_go_bool(&v) {
            return b;
        }
    }
    !race::ENABLED
}

static TEST_PROGRAM_IS_SINGLE_THREADED: OnceLock<bool> = OnceLock::new();

/// TestProgramIsSingleThreaded reports whether test Programs should run in
/// single-threaded mode (the default outside the Go race detector).
pub fn test_program_is_single_threaded() -> bool {
    *TEST_PROGRAM_IS_SINGLE_THREADED.get_or_init(test_program_is_single_threaded_init)
}

/// strconv.ParseBool accepts "1", "t", "T", "true", "TRUE", "True",
/// "0", "f", "F", "false", "FALSE", "False".
fn parse_go_bool(v: &str) -> Option<bool> {
    match v {
        "1" | "t" | "T" | "true" | "TRUE" | "True" => Some(true),
        "0" | "f" | "F" | "false" | "FALSE" | "False" => Some(false),
        _ => None,
    }
}

// PORT(deferred): CheckDataOnly is not portable to stable Rust. Go walks a
// `reflect.Type` graph at runtime and rejects Func/Interface/Chan/
// UnsafePointer members; Rust has no runtime type reflection (no
// `reflect.Type`/`Kind`), and a static equivalent needs either a
// proc-macro derive walking each type's fields or an inventory registry —
// neither exists in this workspace. Port when a reflection/derive mechanism
// lands.
//
// Original Go signature:
//   func CheckDataOnly(root reflect.Type, leaves []reflect.Type) error

/// TempDir is `testing.TB.TempDir`: a unique directory under the OS temp dir,
/// removed when the guard is dropped.
#[derive(Debug)]
pub struct TempDir {
    path: PathBuf,
}

static TEMP_DIR_COUNTER: AtomicU64 = AtomicU64::new(0);

impl TempDir {
    /// New creates a fresh temporary directory.
    ///
    /// PORT: Go's `os.MkdirTemp` picks a random name; we pick
    /// `tsc-testutil-<pid>-<counter>` which is equally unique per process.
    pub fn new() -> TempDir {
        let path = env::temp_dir().join(format!(
            "tsc-testutil-{}-{}",
            process::id(),
            TEMP_DIR_COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&path)
            .unwrap_or_else(|e| panic!("failed to create temp dir {}: {e}", path.display()));
        TempDir { path }
    }

    pub fn path(&self) -> &Path {
        &self.path
    }
}

impl Default for TempDir {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn temp_dir_created_and_removed() {
        let path;
        {
            let t = TempDir::new();
            path = t.path().to_path_buf();
            assert!(path.is_dir());
        }
        assert!(!path.exists());
    }

    #[test]
    fn single_threaded_default() {
        // race::ENABLED is false, so the default (env unset) is true.
        assert!(test_program_is_single_threaded());
    }

    #[test]
    fn assert_panics_matching_payload() {
        assert_panics(|| panic!("boom"), &"boom");
        assert_panics(|| panic!("{}", 42), &"42".to_string());
    }

    #[test]
    #[should_panic(expected = "expected panic, got none")]
    fn assert_panics_no_panic() {
        assert_panics(|| {}, &"x");
    }

    #[test]
    #[should_panic(expected = "ctx:\ninner")]
    fn recover_and_fail_panics_with_context() {
        let result = panic::catch_unwind(|| panic!("inner"));
        let payload = result.unwrap_err();
        recover_and_fail("ctx", &payload);
    }

    #[test]
    fn parse_go_bool_values() {
        assert_eq!(parse_go_bool("1"), Some(true));
        assert_eq!(parse_go_bool("TRUE"), Some(true));
        assert_eq!(parse_go_bool("0"), Some(false));
        assert_eq!(parse_go_bool("False"), Some(false));
        assert_eq!(parse_go_bool("yes"), None);
    }
}
