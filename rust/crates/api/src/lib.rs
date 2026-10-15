// Ported from tsc/internal/api @ ec47d33c23e464a17cdf2475632cba629bee8763
// Native-API layer: msgpack protocol server/session over project+ls.
pub mod requestfilesystem;

mod callbackfs;
mod enum_values_generated;
mod module_resolution;
mod dispatch;
mod handlers_checker;
mod handlers_emit;
mod handlers_files;
mod handlers_lifecycle;
mod handlers_ls;
mod handlers_resolve;
mod proto;
mod protocol_msgpack;
mod server;
mod session;
mod stringer_generated;
