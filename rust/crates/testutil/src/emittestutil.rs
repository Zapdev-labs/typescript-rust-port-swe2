// Ported from tsc/internal/testutil/emittestutil/emittestutil.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `testing.TB` has no Rust equivalent — the `assert.Equal` failure
// becomes `Err(Error)`. Go's `*ast.SourceFile` is the arena pair
// `(nodes, file: NodeId)`; `symbols` is the printer's name-generation arena
// (a `SymbolArena::default()` works for a freshly parsed file, matching the
// emit tests).

use tsc_ast::SymbolArena;
use tsc_ast::ast::Node;
use tsc_ast::ids::NodeId;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::NewLineKind;
use tsc_printer::{EmitContext, PrintHandlers, Printer, PrinterOptions};

use crate::Error;
use crate::parsetestutil;

/// Checks that pretty-printing the given file matches the expected output.
///
/// `emit_context` is Go's `*printer.EmitContext`; `nodes`+`file` identify the
/// `*ast.SourceFile`.
pub fn check_emit(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    file: NodeId,
    expected: &str,
) -> Result<(), Error> {
    let jsx = nodes[file].as_source_file().language_variant == LanguageVariant::Jsx;
    let text = {
        let symbols = SymbolArena::default();
        let mut printer = Printer::new(
            PrinterOptions {
                new_line: NewLineKind::LF,
                ..Default::default()
            },
            PrintHandlers::default(),
            emit_context,
            nodes,
            &symbols,
        );
        printer.emit_source_file(file)
    };
    let actual = text.strip_suffix('\n').unwrap_or(&text);
    if actual != expected {
        // Go: `assert.Equal(t, expected, actual)`.
        return Err(Error::new(format!(
            "assertion failed: expected {expected:?}, got {actual:?}"
        )));
    }
    let (file2, nodes2) = parsetestutil::parse_typescript(&text, jsx);
    parsetestutil::check_diagnostics_message(&nodes2, file2, "error on reparse: ")
}
