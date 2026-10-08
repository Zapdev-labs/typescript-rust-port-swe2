// Ported from tsc/internal/osutil @ ec47d33c23e464a17cdf2475632cba629bee8763
#[cfg(not(target_os = "android"))]
mod os_other;
pub mod osutil;

pub use osutil::{args, executable};
