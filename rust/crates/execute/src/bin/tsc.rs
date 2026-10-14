// Ported from tsc/cmd/tsc/{main,sys}.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The `tsc` binary entry point: an OS-backed `execute/tsc.System` plus
// `main()`'s arg dispatch. `--lsp`/`--api` dispatch exists in Go but those
// servers are not yet ported — they exit with an error here (PORT(deferred)).

use std::io::{self, IsTerminal, Read, Write};
use std::process::{Child, Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, SystemTime};

use tsc_bundled::{lib_path, wrap_fs};
use tsc_contentmapper::hostimpl::SpawnedProcess;
use tsc_core::context::Context;
use tsc_execute::tsc::{
    CommandLineTesting, DiagnosticRegistry, SharedWriter, System,
};
use tsc_execute::{CommandLineResult, command_line};
use tsc_tspath::{RootedDirectoryPath, rooted_directory_path_from_absolute};
use tsc_vfs::vfs::Vfs;

/// `osSys` — the OS-backed `execute/tsc.System`.
struct OsSys {
    writer: SharedWriter,
    error_writer: SharedWriter,
    fs: Arc<dyn Vfs>,
    default_library_path: RootedDirectoryPath,
    cwd: RootedDirectoryPath,
    start: SystemTime,
    diagnostic_registry: Arc<DiagnosticRegistry>,
}

impl System for OsSys {
    fn writer(&self) -> SharedWriter {
        self.writer.clone()
    }

    fn error_writer(&self) -> SharedWriter {
        self.error_writer.clone()
    }

    fn fs(&self) -> Arc<dyn Vfs> {
        self.fs.clone()
    }

    fn default_library_path(&self) -> RootedDirectoryPath {
        self.default_library_path.clone()
    }

    fn current_directory(&self) -> RootedDirectoryPath {
        self.cwd.clone()
    }

    fn write_output_is_tty(&self) -> bool {
        io::stdout().is_terminal()
    }

    fn width_of_terminal(&self) -> usize {
        // PORT: Go uses `term.GetSize`; no terminal-size dep in the
        // workspace — 0 is Go's error-path return.
        0
    }

    fn environment_variable(&self, name: &str) -> Option<String> {
        std::env::var(name).ok()
    }

    fn spawn(
        &self,
        command: &[String],
        dir: &str,
        stderr: Option<Box<dyn io::Write + Send>>,
    ) -> io::Result<Arc<dyn SpawnedProcess>> {
        spawn_process(command, dir, stderr)
    }

    fn now(&self) -> SystemTime {
        SystemTime::now()
    }

    fn since_start(&self) -> Duration {
        self.start.elapsed().unwrap_or_default()
    }

    fn diagnostic_registry(&self) -> &Arc<DiagnosticRegistry> {
        &self.diagnostic_registry
    }
}

/// `childProcess` — read is the child's stdout, write is its stdin.
struct ChildProcess {
    child: Mutex<Child>,
    stdin: Mutex<std::process::ChildStdin>,
    stdout: Mutex<std::process::ChildStdout>,
}

impl SpawnedProcess for ChildProcess {
    fn spawned_read(&self, buf: &mut [u8]) -> io::Result<usize> {
        self.stdout.lock().unwrap_or_else(|e| e.into_inner()).read(buf)
    }

    fn spawned_write(&self, buf: &[u8]) -> io::Result<usize> {
        self.stdin.lock().unwrap_or_else(|e| e.into_inner()).write(buf)
    }

    fn spawned_flush(&self) -> io::Result<()> {
        self.stdin.lock().unwrap_or_else(|e| e.into_inner()).flush()
    }

    fn spawned_close(&self) -> io::Result<()> {
        let mut child = self.child.lock().unwrap_or_else(|e| e.into_inner());
        let _ = child.kill();
        match child.wait() {
            Ok(_) => Ok(()),
            Err(e) => Err(e),
        }
    }

    fn spawned_exit_code(&self) -> Option<i64> {
        self.child
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .try_wait()
            .ok()
            .flatten()
            .and_then(|s| s.code().map(i64::from))
    }
}

/// `spawnProcess`.
fn spawn_process(
    command: &[String],
    dir: &str,
    stderr: Option<Box<dyn io::Write + Send>>,
) -> io::Result<Arc<dyn SpawnedProcess>> {
    let mut cmd = Command::new(&command[0]);
    cmd.args(&command[1..])
        .current_dir(dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped());
    if stderr.is_none() {
        cmd.stderr(Stdio::null());
    }
    let mut child = cmd.spawn()?;
    let stdin = child.stdin.take().expect("stdin piped");
    let stdout = child.stdout.take().expect("stdout piped");
    // `stderr` writer: Go attaches the provided writer to the child's
    // stderr; std::process can't redirect into a `Box<dyn Write>` without a
    // pump thread, so a live writer is a TODO (PORT(deferred): only used
    // when content-mapper debug logging is enabled).
    let _ = stderr;
    Ok(Arc::new(ChildProcess {
        child: Mutex::new(child),
        stdin: Mutex::new(stdin),
        stdout: Mutex::new(stdout),
    }))
}

/// `newSystem`.
fn new_system() -> Arc<OsSys> {
    let cwd = match std::env::current_dir() {
        Ok(cwd) => cwd,
        Err(err) => {
            eprintln!("Error getting current directory: {err}");
            std::process::exit(3); // ExitStatusInvalidProject_OutputsSkipped
        }
    };
    let cwd = cwd.to_string_lossy().into_owned();
    Arc::new(OsSys {
        cwd: rooted_directory_path_from_absolute(&cwd),
        fs: wrap_fs(tsc_vfs::osvfs::fs()),
        default_library_path: lib_path(),
        writer: SharedWriter::new(io::stdout()),
        error_writer: SharedWriter::new(io::stderr()),
        start: SystemTime::now(),
        diagnostic_registry: Arc::new(DiagnosticRegistry::default()),
    })
}

/// `runMain`.
fn run_main() -> i32 {
    tsc_core::core::apply_debug_stack_limit();
    let args = tsc_osutil::osutil::args();
    let args = &args[1..];
    if let Some(first) = args.first() {
        match first.as_str() {
            "--lsp" | "--api" => {
                eprintln!("{first}: server mode is not yet ported");
                return 5; // ExitStatusNotImplemented
            }
            _ => {}
        }
    }
    // Go uses signal.NotifyContext; the compile is synchronous so a plain
    // background ctx is equivalent (Ctrl-C still kills the process).
    let ctx = Context::background();
    let sys: Arc<dyn System> = new_system();
    let testing: Option<Arc<dyn CommandLineTesting>> = None;
    let result: CommandLineResult = command_line(&ctx, &sys, args, testing);
    result.status as i32
}

fn main() {
    std::process::exit(run_main());
}
