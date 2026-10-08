// Ported from tsc/internal/osutil/osutil.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io;

/// Args returns the command-line arguments with platform-specific launcher details removed.
#[cfg(not(target_os = "android"))]
pub fn args() -> Vec<String> {
    crate::os_other::args()
}

/// Executable returns the path of the current executable, accounting for platform-specific launchers.
#[cfg(not(target_os = "android"))]
pub fn executable() -> Result<String, io::Error> {
    crate::os_other::executable()
}

// TODO(port): android — os_android.go handles Termux's TERMUX_EXEC__PROC_SELF_EXE
// launcher detail (argv[1] is the real executable under Android's linker).
