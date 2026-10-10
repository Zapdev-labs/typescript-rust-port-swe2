// Ported from tsc/internal/format/api_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(deferred): `BenchmarkFormat` is not ported — Rust benchmarks need the
// nightly `test` crate; the "no edit application" and "pretty print"
// sub-benchmarks additionally need `printer`'s emit path exercised in a
// benchmark context. The `applyBulkEdits` helper is provided by
// `tsc_core::textchange::apply_bulk_edits`.

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::context::Context;
use tsc_core::scriptkind::ScriptKind;
use tsc_core::textchange::apply_bulk_edits;
use tsc_core::tristate::TS_TRUE;
use tsc_lsutil::{EditorSettings, FormatCodeSettings, IndentStyle};
use tsc_parser::parse_source_file;
use tsc_repo::test_data_path;
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
fn test_format() {
    // format checker.ts
    let ctx = with_format_code_settings(
        &Context::background(),
        FormatCodeSettings {
            editor_settings: EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 4,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces: TS_TRUE,
                indent_style: IndentStyle::SMART,
                trim_trailing_whitespace: TS_TRUE,
                ..Default::default()
            },
            insert_space_before_type_annotation: TS_TRUE,
            ..Default::default()
        },
        "\n",
    );
    let file_path = format!(
        "{test_data_path}/fixtures/compiler/checker.ts",
        test_data_path = test_data_path()
    );
    let text = std::fs::read_to_string(&file_path).expect("read checker.ts fixture");
    let (source_file, mut nodes) =
        parse_source_file(test_parse_options("/checker.ts"), &text, ScriptKind::Ts);
    let edits = format_document(&ctx, source_file, &mut nodes);
    let new_text = apply_bulk_edits(&text, &edits);
    assert!(!new_text.is_empty());
    assert_ne!(text, new_text);
}
