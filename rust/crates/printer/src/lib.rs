// Ported from tsc/internal/printer @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The `printer` package — a pretty-printer for TS ASTs, plus the writer
// interfaces and implementations used to drive it.
//
// PORT: Go's `*ast.Node` pointers are `NodeId`s into a `Vec<ast::Node>`
// arena threaded through the API (`nodes: &mut Vec<Node>`). Methods that
// returned nilable nodes return `Option<NodeId>`. Go interface types
// (`EmitTextWriter`, `EmitResolver`, `EmitHost`) are Rust traits. Function
// pointer fields are boxed closures.

mod change_tracker_writer;
mod emit_context;
mod emit_flags;
mod emit_helpers;
mod emit_host;
mod emit_resolver;
mod emit_text_writer;
mod factory;
mod name_generator;
mod printer;
mod semicolon_writer;
mod single_line_writer;
mod source_file_meta_data_provider;
mod synthetic_file;
mod text_writer;
mod utilities;

pub use change_tracker_writer::*;
pub use emit_context::*;
pub use emit_flags::*;
pub use emit_helpers::*;
pub use emit_host::*;
pub use emit_resolver::*;
pub use emit_text_writer::*;
pub use factory::*;
pub use printer::*;
pub use semicolon_writer::*;
pub use single_line_writer::*;
pub use source_file_meta_data_provider::*;
pub use synthetic_file::*;
pub use text_writer::*;
pub use utilities::*;
