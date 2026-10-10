// Ported from tsc/internal/execute/incremental/host.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;
use std::time::SystemTime;

use tsc_compiler::host::CompilerHost;
use tsc_tspath::RootedFilePath;

/// `type Host interface`.
pub trait Host {
    /// `GetMTime`.
    fn get_mtime(&self, file_name: &RootedFilePath) -> SystemTime;
    /// `SetMTime`.
    fn set_mtime(&self, file_name: &RootedFilePath, m_time: SystemTime) -> Result<(), String>;
}

/// `type host struct`.
struct HostImpl {
    host: Arc<dyn CompilerHost>,
}

impl Host for HostImpl {
    fn get_mtime(&self, file_name: &RootedFilePath) -> SystemTime {
        get_mtime(self.host.as_ref(), file_name)
    }

    fn set_mtime(&self, file_name: &RootedFilePath, m_time: SystemTime) -> Result<(), String> {
        self.host
            .fs()
            .chtimes(&file_name.as_path(), SystemTime::UNIX_EPOCH, m_time)
            .map_err(|e| e.to_string())
    }
}

/// `func CreateHost`.
pub fn create_host(compiler_host: Arc<dyn CompilerHost>) -> Arc<dyn Host> {
    Arc::new(HostImpl {
        host: compiler_host,
    })
}

/// `func GetMTime` — Go returns the zero `time.Time` when the file cannot be
/// stat'ed; `SystemTime::UNIX_EPOCH` is the Rust stand-in for that zero value.
pub fn get_mtime(host: &dyn CompilerHost, file_name: &RootedFilePath) -> SystemTime {
    host.fs()
        .stat(&file_name.as_path())
        .map(|stat| stat.mod_time())
        .unwrap_or(SystemTime::UNIX_EPOCH)
}
