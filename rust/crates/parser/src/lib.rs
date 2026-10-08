// tsc-parser — port of tsc/internal/parser

mod jsdoc;
pub mod parser;
mod references;
mod reparser;
mod types;
pub mod utilities;

pub use parser::{
    Parser, ParsingContext, attach_file_to_diagnostics, get_comment_pragmas,
    parse_source_file,
};
pub use references::collect_external_module_references;
pub use reparser::{
    extract_eventual_pos, has_parsed_jsdoc_namespace, is_matching_tag,
    is_valid_statement_type, is_valid_tuple_type, reparse_top_level_import,
    reparse_un_parenthesized_arrow_function,
};
pub use types::ParseFlags;
pub use utilities::{
    get_jsdoc_comment_ranges, get_language_variant, is_jsdoc_like_text,
    is_keyword_or_punctuation, token_is_identifier_or_keyword,
    token_is_identifier_or_keyword_or_greater_than,
};
