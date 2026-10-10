// Ported from tsc/internal/format/format_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::context::Context;
use tsc_core::scriptkind::ScriptKind;
use tsc_core::textchange::apply_bulk_edits;
use tsc_core::tristate::TS_TRUE;
use tsc_lsutil::{EditorSettings, FormatCodeSettings, IndentStyle};
use tsc_parser::parse_source_file;
use tsc_tspath::{path_key_from_canonical, rooted_file_path_from_normalized};

use crate::{format_document, with_format_code_settings};

fn test_parse_options(file_name: &str) -> SourceFileParseOptions {
    SourceFileParseOptions {
        file_name: rooted_file_path_from_normalized(file_name),
        path_key: path_key_from_canonical(file_name),
        ..Default::default()
    }
}

#[test]
fn test_format_no_trailing_space() {
    let test_cases: &[(&str, &str)] = &[
        ("simple statement without trailing newline", "1;"),
        (
            "function call without trailing newline",
            "console.log('hello');",
        ),
        ("if block on single line", "if (true) { }"),
        (
            "class declaration",
            "class A {\n    // Class Contents Go Here\n}",
        ),
        (
            "class declaration with trailing newline",
            "class A {\n    // Class Contents Go Here\n}\n",
        ),
        ("empty block", "if (true) {}"),
        ("module declaration", "module M { }"),
        ("enum declaration", "enum E { A, B }"),
    ];

    for (name, text) in test_cases {
        let ctx = with_format_code_settings(
            &Context::background(),
            FormatCodeSettings {
                editor_settings: EditorSettings {
                    tab_size: 4,
                    indent_size: 4,
                    new_line_character: "\n".to_string(),
                    convert_tabs_to_spaces: TS_TRUE,
                    indent_style: IndentStyle::SMART,
                    trim_trailing_whitespace: TS_TRUE,
                    ..Default::default()
                },
                ..Default::default()
            },
            "\n",
        );
        let (source_file, mut nodes) =
            parse_source_file(test_parse_options("/test.ts"), text, ScriptKind::Ts);
        let edits = format_document(&ctx, source_file, &mut nodes);
        let new_text = apply_bulk_edits(text, &edits);
        // Formatting should not add trailing whitespace at end of file
        for (i, line) in new_text.split('\n').enumerate() {
            let trimmed = line.trim_end_matches([' ', '\t']);
            assert_eq!(
                line,
                trimmed,
                "Formatter should not add trailing whitespace on line {} (case {name})",
                i + 1
            );
        }
    }
}
