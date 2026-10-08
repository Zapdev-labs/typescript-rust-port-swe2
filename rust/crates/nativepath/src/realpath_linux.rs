// Ported from tsc/internal/nativepath/realpath_linux.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::fs::OpenOptions;
use std::io;
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::io::AsRawFd;
use std::path::Path;
use std::sync::OnceLock;

use crate::eintr_unix::ignoring_eintr;

// On Linux, we use the O_PATH + /proc/self/fd trick to resolve the canonical
// path in O(1) syscalls (open + readlink + close) instead of Go's
// filepath.EvalSymlinks which does an lstat per path component — O(depth).
//
// This is the approach libuv/Node.js could use, though libuv currently just
// calls C realpath(3) which itself does a readlink per component. On the Go
// side, the per-component approach is even more expensive because each
// os.Lstat call involves goroutine scheduling overhead (entersyscall /
// exitsyscall).
//
// How it works:
//   - open(path, O_PATH|O_CLOEXEC) gives us a lightweight fd that follows all
//     symlinks to the final target. O_PATH requires only search permission on
//     directories (same as lstat), and works for both files and directories.
//   - readlink("/proc/self/fd/<fd>") returns the fully resolved canonical path
//     that the kernel computed during the open.
//
// Falls back to filepath.EvalSymlinks if /proc is not available (e.g. containers
// or chroots without procfs mounted).

// PORT: unix.O_PATH / unix.O_CLOEXEC are spelled as literal Linux ABI values
// because libc is not an approved workspace dependency (SPEC §5.11).
const O_PATH: i32 = 0o10000000;
const O_CLOEXEC: i32 = 0o2000000;

const PROC_SELF_FD: &str = "/proc/self/fd/";

static HAS_PROC_SELF_FD: OnceLock<bool> = OnceLock::new();

fn has_proc_self_fd() -> bool {
    // unix.Stat(_procSelfFD, &stat) == nil
    *HAS_PROC_SELF_FD.get_or_init(|| Path::new(PROC_SELF_FD).exists())
}

pub fn realpath(path: &str) -> Result<String, io::Error> {
    if !has_proc_self_fd() {
        // filepath.EvalSymlinks — std::fs::canonicalize is its std equivalent.
        return crate::path_to_string(std::fs::canonicalize(path)?);
    }

    // PORT: Go wraps syscall errors in *os.PathError{Op, Path, Err}; std's
    // io::Error carries the same errno but not the op/path context.
    let file = ignoring_eintr(|| {
        OpenOptions::new()
            .read(true)
            .custom_flags(O_CLOEXEC | O_PATH)
            .open(path)
    })?;

    let proc_path = format!("{PROC_SELF_FD}{}", file.as_raw_fd());
    // `file` closes on drop, mirroring `defer unix.Close(fd)`.

    // PORT: Go grows a 256-byte readlink buffer manually until the result
    // fits; std::fs::read_link performs the same grow-until-fits loop.
    crate::path_to_string(ignoring_eintr(|| std::fs::read_link(&proc_path))?)
}
