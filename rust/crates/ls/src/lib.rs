// Ported from tsc/internal/ls @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The language service. Go's `LanguageService` methods become inherent
// methods on a `LanguageService` struct holding `Rc<Program>`; per-Go-file
// Rust modules mirror the source layout. AST access goes through
// `program.nodes(file_index)` arenas (`NodeId`/`SymbolId`/`TypeId`).

pub mod autoimport;
pub mod change;

pub(crate) mod api;
mod autoinsert;
mod callhierarchy;
mod codeactions;
mod codeactions_fixclassincorrectlyimplementsinterface;
mod codeactions_fixmissingtypeannotation;
mod codeactions_importfixes;
mod codeactions_missingmemberfixer;
mod codelens;
mod completions;
mod constants;
mod crossproject;
mod definition;
mod diagnostics;
mod displaypartswriter;
mod documenthighlights;
mod file_rename;
mod findallreferences;
mod folding;
mod format;
pub mod host;
mod hover;
mod hovericon;
mod import_tracker;
mod inlay_hints;
mod jsdoc;
mod jsdoc_snippet;
pub mod languageservice;
mod linkedediting;
mod organizeimports;
mod rename;
mod selectionranges;
mod semantictokens;
mod signaturehelp;
mod source_map;
mod sourcedefinition;
mod string_completions;
mod symbols;
mod utilities;
