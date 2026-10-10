// Ported from tsc/internal/format/indent_getindentation_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::scriptkind::ScriptKind;
use tsc_lsutil::get_default_format_code_settings;
use tsc_parser::parse_source_file;
use tsc_tspath::{path_key_from_canonical, rooted_file_path_from_normalized};

use crate::get_indentation;
use crate::util::get_line_start_position_for_position;

fn test_parse_options(file_name: &str) -> SourceFileParseOptions {
    SourceFileParseOptions {
        file_name: rooted_file_path_from_normalized(file_name),
        path_key: path_key_from_canonical(file_name),
        ..Default::default()
    }
}

#[test]
fn test_get_indentation_for_named_imports_position() {
    let text = "import {\n    type SomeInterface,\n} from \"./exports.js\";";
    // Position 9: \n
    // Position 10: first space of "    type SomeInterface"

    let (source_file, mut nodes) =
        parse_source_file(test_parse_options("/test.ts"), text, ScriptKind::Ts);

    let options = get_default_format_code_settings();

    // The line that contains "    type SomeInterface" starts at position 9 (the \n).
    // The getAdjustedStartPosition with LeadingTriviaOptionNone returns line start.
    // Let's test at position 9 (start of line containing the specifier)
    let line_start = get_line_start_position_for_position(14, source_file, &nodes); // 14 is somewhere in "    type"

    let indent = get_indentation(line_start, source_file, &options, true, &mut nodes);
    eprintln!(
        "lineStart={line_start}, text[line_start:]={:?}",
        &text[line_start as usize..line_start as usize + 10]
    );
    eprintln!("GetIndentation at lineStart {line_start} = {indent}");

    assert_eq!(indent, 4, "Expected indentation 4, got {indent}");
}
