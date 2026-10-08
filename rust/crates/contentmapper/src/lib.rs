// tsc-contentmapper — port of tsc/internal/contentmapper
//
// Defines the types describing an external content mapper: a plugin that
// transforms otherwise unsupported file content (e.g. .vue) into virtual
// TypeScript during program construction, and drives the configured mappers
// at build time over JSON-RPC child processes (see `host`/`hostimpl`).

pub mod contentmapper;
pub mod host;
pub mod hostimpl;
pub mod transform;
mod xxh3;

pub use contentmapper::*;
pub use host::*;
pub use hostimpl::*;
pub use transform::*;
pub use xxh3::Uint128;

#[cfg(test)]
mod host_test;
#[cfg(test)]
mod transform_test;
