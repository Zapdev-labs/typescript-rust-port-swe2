// Ported from tsc/internal/lsp @ ec47d33c23e464a17cdf2475632cba629bee8763
// The LSP server over project+ls (vscode languageserver protocol).
pub mod lspwatcher;

mod dynamic_queue;
mod logger;
mod progress;
mod server;
mod stack_sanitizer;
