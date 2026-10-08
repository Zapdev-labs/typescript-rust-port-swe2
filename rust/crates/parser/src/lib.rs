// tsc-parser — port of tsc/internal/parser

mod jsdoc;
pub mod parser;
mod references;
mod reparser;
mod types;
pub mod utilities;

pub use parser::{
    Parser, ParsingContext, attach_file_to_diagnostics, get_comment_pragmas, parse_source_file,
};
pub use references::collect_external_module_references;
pub use types::ParseFlags;
pub use utilities::{
    get_jsdoc_comment_ranges, get_language_variant, is_jsdoc_like_text, is_keyword_or_punctuation,
    token_is_identifier_or_keyword, token_is_identifier_or_keyword_or_greater_than,
};
