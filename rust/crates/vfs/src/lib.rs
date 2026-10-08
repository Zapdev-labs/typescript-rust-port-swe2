// Ported from tsc/internal/vfs @ ec47d33c23e464a17cdf2475632cba629bee8763

pub mod fs;
pub mod internal;
pub mod iovfs;
pub mod osvfs;
pub mod vfs;
pub mod vfstest;
pub mod walkdir;

pub use vfs::{
    Entries, Vfs, WalkDirFunc, ERR_CLOSED, ERR_EXIST, ERR_INVALID, ERR_NOT_EXIST, ERR_PERMISSION,
    SKIP_ALL, SKIP_DIR,
};
pub use walkdir::walk_dir as walk_dir;
