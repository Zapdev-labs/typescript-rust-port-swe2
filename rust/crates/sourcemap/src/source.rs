// Ported from tsc/internal/sourcemap/source.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_core::text::TextPos;
use tsc_tspath::RootedFilePath;

/// `type Source interface` — implemented by `ast::SourceFile` (see
/// `SourceFileLike` in tsc-ast, which is the same contract minus `FileName`).
pub trait Source {
    /// `Text() string`.
    fn text(&self) -> &str;
    /// `FileName() tspath.RootedFilePath`.
    fn file_name(&self) -> &RootedFilePath;
    /// `ECMALineMap() []core.TextPos`.
    fn ecma_line_map(&self) -> &[TextPos];
}
