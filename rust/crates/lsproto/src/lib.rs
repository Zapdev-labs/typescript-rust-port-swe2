// tsc-lsproto — port of tsc/internal/lsp/lsproto @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// LSP protocol definitions for the TypeScript LSP server: generated protocol
// types (lsp_generated.rs, produced by gen.py from lsp_generated.go), document
// URI handling and JSON plumbing helpers (lsp.rs), JSON-RPC message wrappers
// (jsonrpc.rs), Content-Length framing compatibility shims (baseproto.rs),
// and generated-code runtime support (structcodec.rs).

pub mod baseproto;
pub mod jsonrpc;
pub mod lsp;
pub mod lsp_generated;
pub mod structcodec;
pub mod util;

pub use baseproto::*;
pub use jsonrpc::*;
pub use lsp::*;
pub use lsp_generated::*;
pub use util::*;

pub(crate) use structcodec::*;

#[cfg(test)]
mod baseproto_test;
#[cfg(test)]
mod lsp_json_test;
#[cfg(test)]
mod lsp_test;
