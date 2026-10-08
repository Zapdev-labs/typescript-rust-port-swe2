// tsc-lsconv — port of tsc/internal/ls/lsconv @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Conversions between internal types (positions, ranges, diagnostics,
// TextSpan) and LSP protocol types (`lsp/lsproto`):
// - `linemap.rs` is `linemap.go` — the LSP line-start table (`\n`, `\r`,
//   `\r\n` only, plus an ASCII-only flag).
// - `converters.rs` is `converters.go` — position/range/location/diagnostic
//   conversion, including content-mapped (virtual text) file handling and
//   file-name↔DocumentUri encoding.
// - `runes.rs` holds the shared Go `unicode/utf8`+`unicode/utf16` shims the
//   other two modules need (the decoder in `tsc-stringutil` is
//   crate-private, so a local copy lives here — same as `tsc-scanner`).

pub mod converters;
pub mod linemap;
pub(crate) mod runes;

// Flat re-exports so call sites mirror Go's `lsconv.X` as `lsconv::X`.
pub use converters::*;
pub use linemap::*;

#[cfg(test)]
mod converters_test;
