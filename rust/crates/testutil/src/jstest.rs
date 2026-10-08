// Ported from tsc/internal/testutil/jstest/node.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `testing.TB` is dropped — `getNodeExe`'s `t.Fatal` becomes `Err`,
// and `SkipIfNoNodeJS` becomes the predicate [node_js_available] (call
// `if !node_js_available() { return; }` instead of `t.Skip`). `t.TempDir`
// becomes [crate::TempDir]. `exec.LookPath` is a PATH walk; `CombinedOutput`
// merges stdout/stderr in arrival order in Go — the port collects them
// separately and concatenates (stdout then stderr), so interleaved output
// ordering in error messages may differ.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;

use serde::de::DeserializeOwned;
use tsc_repo::root_path;
use tsc_tspath::normalize_path;

use crate::{Error, TempDir};

const LOADER_SCRIPT: &str = r#"import script from "./script.mjs";
process.stdout.write(JSON.stringify(await script(...process.argv.slice(2))));"#;

/// getNodeExeOnce — `exec.LookPath("node")` resolved once.
static NODE_EXE: OnceLock<Option<PathBuf>> = OnceLock::new();

fn node_exe() -> Option<&'static Path> {
    NODE_EXE.get_or_init(|| look_path("node")).as_deref()
}

/// exec.LookPath: find an executable file named `file` on PATH.
fn look_path(file: &str) -> Option<PathBuf> {
    let path_var = env::var_os("PATH")?;
    for dir in env::split_paths(&path_var) {
        let candidate = dir.join(file);
        if is_executable(&candidate) {
            return Some(candidate);
        }
        #[cfg(windows)]
        {
            let candidate = dir.join(format!("{file}.exe"));
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    None
}

#[cfg(unix)]
fn is_executable(p: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;
    fs::metadata(p)
        .map(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
        .unwrap_or(false)
}

#[cfg(not(unix))]
fn is_executable(p: &Path) -> bool {
    p.is_file()
}

/// NodeJsAvailable reports whether a `node` executable was found on PATH.
///
/// Go: `SkipIfNoNodeJS(t)` — call `if !node_js_available() { return; }`.
pub fn node_js_available() -> bool {
    node_exe().is_some()
}

/// EvalNodeScript imports a Node.js script that default-exports a single function,
/// calls it with the provided arguments, and unmarshals the JSON-stringified
/// awaited return value into T.
pub fn eval_node_script<T: DeserializeOwned>(
    script: &str,
    dir: &Path,
    args: &[&str],
) -> Result<T, Error> {
    eval_node_script_inner(script, LOADER_SCRIPT, dir, args)
}

/// EvalNodeScriptWithTS is like [eval_node_script], but provides the TypeScript
/// library to the script as the first argument.
pub fn eval_node_script_with_ts<T: DeserializeOwned>(
    script: &str,
    dir: Option<&Path>,
    args: &[&str],
) -> Result<T, Error> {
    let owned_dir;
    let dir = match dir {
        Some(d) => d,
        None => {
            owned_dir = TempDir::new();
            owned_dir.path()
        }
    };
    let ts_src_path = format!(
        "{}/../node_modules/typescript/lib/typescript.js",
        root_path()
    );
    let ts_src = normalize_path(&ts_src_path);
    let ts_src = if ts_src.starts_with('/') {
        format!("file://{ts_src}")
    } else {
        format!("file:///{ts_src}")
    };
    let ts_loader_script = format!(
        r#"import script from "./script.mjs";
import * as ts from "{ts_src}";
process.stdout.write(JSON.stringify(await script(ts, ...process.argv.slice(2))));"#
    );
    eval_node_script_inner(script, &ts_loader_script, dir, args)
}

fn eval_node_script_inner<T: DeserializeOwned>(
    script: &str,
    loader: &str,
    dir: &Path,
    args: &[&str],
) -> Result<T, Error> {
    // Go: getNodeExe(t) -> t.Fatal("Node.js not found")
    let exe = node_exe().ok_or_else(|| Error::new("Node.js not found"))?;
    let script_path = dir.join("script.mjs");
    fs::write(&script_path, script).map_err(Error::from)?;
    let loader_path = dir.join("loader.mjs");
    fs::write(&loader_path, loader).map_err(Error::from)?;

    let output = Command::new(exe)
        .arg(&loader_path)
        .args(args)
        .current_dir(dir)
        .output()
        .map_err(|err| {
            // Go: CombinedOutput on a spawn failure returns the error and
            // whatever output was collected (none).
            Error::new(format!("failed to run node: {err}\n"))
        })?;
    if !output.status.success() {
        let mut combined = output.stdout.clone();
        combined.extend_from_slice(&output.stderr);
        return Err(Error::new(format!(
            "failed to run node: {}\n{}",
            exit_error_string(&output.status),
            String::from_utf8_lossy(&combined)
        )));
    }

    let result = tsc_json::unmarshal(&output.stdout, &[])
        .map_err(|err| Error::new(format!("failed to unmarshal JSON output: {err}")))?;

    Ok(result)
}

/// Go formats `*exec.ExitError` as e.g. "exit status 1".
fn exit_error_string(status: &std::process::ExitStatus) -> String {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(code) = status.code() {
            return format!("exit status {code}");
        }
        if let Some(sig) = status.signal() {
            return format!("signal: {sig}");
        }
        format!("exit status {status}")
    }
    #[cfg(not(unix))]
    {
        format!("exit status {status}")
    }
}
