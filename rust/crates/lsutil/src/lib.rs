// tsc-lsutil — port of tsc/internal/ls/lsutil @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Shared language-service utilities (ASI candidates, last/first token
// navigation, completed-node detection, format code settings, organize-imports
// comparers, user preferences, symbol display kinds).
//
// Layout mirrors the Go files one-to-one:
//   - asi.go                       -> asi.rs
//   - children.go                  -> children.rs
//   - completednode.go             -> completednode.rs
//   - formatcodeoptions.go         -> formatcodeoptions.rs
//   - organizeimports.go           -> organizeimports.rs
//   - symbol_display.go            -> symbol_display.rs
//   - userpreferences.go           -> userpreferences.rs
//   - userpreferences_generated.go -> userpreferences_generated.rs
//   - utilities.go                 -> utilities.rs
//
// PORT(global): `*ast.Node` is `NodeId` and `*ast.SourceFile` is the arena
// `NodeId` of the file; file data is reached via
// `nodes[file].as_source_file()`. Functions thread the arena
// (`nodes: &[Node]` or `&mut Vec<Node>` when the scanner may allocate tokens
// into `SourceFile::token_cache`) after the Go parameter list.
// `Scanner<'a>` borrows `&'a str`; it cannot borrow `SourceFile::text` out of
// `nodes` while `get_or_create_token` needs `&mut Vec<Node>`, so each entry
// point that rescans clones the file text once (same compromise as
// tsc-astnav's `nav_scanner`).

// Go-stdlib unicode tables + helpers backing organize-imports collation
// and `ModuleSpecifierToValidIdentifier`.
#[allow(dead_code)]
mod case_ranges_generated;
mod unicode;
#[allow(dead_code)]
mod unicode_categories_generated;

pub mod asi;
pub mod children;
pub mod completednode;
pub mod formatcodeoptions;
pub mod organizeimports;
pub mod symbol_display;
pub mod userpreferences;
pub mod userpreferences_generated;
pub mod utilities;

pub use asi::*;
pub use children::*;
pub use completednode::*;
pub use formatcodeoptions::*;
pub use organizeimports::*;
pub use symbol_display::*;
pub use userpreferences::*;
pub use userpreferences_generated::*;
pub use utilities::*;

#[cfg(test)]
mod userpreferences_test;
#[cfg(test)]
mod utilities_test;
