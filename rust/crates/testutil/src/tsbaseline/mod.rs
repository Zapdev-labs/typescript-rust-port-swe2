// Ported from tsc/internal/testutil/tsbaseline @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `testing.TB` conventions (see crate root): `baseline.Run`'s `t.Error`/
// `t.Fatalf` payloads panic through `Result::unwrap_or_else(panic)`.
// `baselinePath`/`header` are `&str`; `*core.CompilerOptions` is `&
// CompilerOptions`.
//
// One submodule per Go file. `util.rs` holds the path-prefix replacers and
// regex helpers; `SnapshotDiagnostic` in `error_baseline.rs` renders
// diagnostics through the `DiagnosticFile` snapshot where Go's
// `ASTDiagnostic` would resolve the live `*ast.SourceFile` (see that
// file's header).

pub mod contentmapper_baseline;
pub mod error_baseline;
pub mod js_emit_baseline;
pub mod module_resolution_baseline;
pub mod sourcemap_baseline;
pub mod sourcemap_record_baseline;
pub mod type_symbol_baseline;
pub(crate) mod util;

pub use contentmapper_baseline::do_content_mapper_baseline;
pub use error_baseline::{do_error_baseline, get_error_baseline};
pub use js_emit_baseline::do_js_emit_baseline;
pub use module_resolution_baseline::do_module_resolution_baseline;
pub use sourcemap_baseline::do_sourcemap_baseline;
pub use sourcemap_record_baseline::do_sourcemap_record_baseline;
pub use type_symbol_baseline::do_type_and_symbol_baseline;
