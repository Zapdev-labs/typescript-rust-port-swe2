// Ported from tsc/internal/format @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The Go formatter operates on `*ast.Node` pointers into a shared AST; the
// Rust port threads `NodeId` + `&mut Vec<Node>` (the arena) through the same
// call structure. `file` parameters are the `NodeId` of the `SourceFile`
// node; `nodes[file].as_source_file()` recovers the `*ast.SourceFile`
// equivalent.
//
// PORT: `formattingScanner` owns a `Scanner<'a>` borrowing the (cloned)
// source text, so `FormatSpanWorker` state is kept behind `Rc<RefCell<..>>`
// and per-field `Cell`/`RefCell` interior mutability — Go's `formatSpanWorker`
// methods are `&self`-style here so the `visit_each_child` callbacks can
// re-enter the worker without double-borrow panics.

mod api;
mod context;
mod indent;
mod kinditer;
mod rule;
mod rulecontext;
mod rules;
mod rulesmap;
mod scanner;
mod span;
mod util;

pub use api::*;
pub use context::FormattingContext;
pub use indent::{
    find_first_non_whitespace_column, get_containing_list, get_indentation,
    get_indentation_for_node,
};
pub use scanner::TextRangeWithKind;
pub use span::LineAction;
pub use util::get_line_start_position_for_position;

#[cfg(test)]
mod api_test;
#[cfg(test)]
mod comment_test;
#[cfg(test)]
mod format_test;
#[cfg(test)]
mod indent_getindentation_test;
#[cfg(test)]
mod indent_test;
