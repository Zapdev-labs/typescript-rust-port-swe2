// Ported from tsc/internal/format/comment_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::context::Context;
use tsc_core::scriptkind::ScriptKind;
use tsc_core::textchange::apply_bulk_edits;
use tsc_core::tristate::{TS_FALSE, TS_TRUE};
use tsc_lsutil::{EditorSettings, FormatCodeSettings, IndentStyle};
use tsc_parser::parse_source_file;
use tsc_tspath::{path_key_from_canonical, rooted_file_path_from_normalized};

use crate::{format_document, format_selection, with_format_code_settings};

fn test_parse_options(file_name: &str) -> SourceFileParseOptions {
    SourceFileParseOptions {
        file_name: rooted_file_path_from_normalized(file_name),
        path_key: path_key_from_canonical(file_name),
        ..Default::default()
    }
}

fn comment_ctx(convert_tabs_to_spaces: tsc_core::tristate::Tristate) -> Context {
    with_format_code_settings(
        &Context::background(),
        FormatCodeSettings {
            editor_settings: EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 4,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces,
                indent_style: IndentStyle::SMART,
                trim_trailing_whitespace: TS_TRUE,
                ..Default::default()
            },
            insert_space_before_type_annotation: TS_TRUE,
            ..Default::default()
        },
        "\n",
    )
}

fn comment_ctx_zero_base(convert_tabs_to_spaces: tsc_core::tristate::Tristate) -> Context {
    with_format_code_settings(
        &Context::background(),
        FormatCodeSettings {
            editor_settings: EditorSettings {
                tab_size: 4,
                indent_size: 4,
                base_indent_size: 0,
                new_line_character: "\n".to_string(),
                convert_tabs_to_spaces,
                indent_style: IndentStyle::SMART,
                trim_trailing_whitespace: TS_TRUE,
                ..Default::default()
            },
            insert_space_before_type_annotation: TS_TRUE,
            ..Default::default()
        },
        "\n",
    )
}

#[test]
fn test_comment_formatting() {
    // format comment issue reproduction
    {
        let ctx = comment_ctx(TS_TRUE);

        // Original code that causes the bug
        let original_text = "class C {\n    /**\n     *\n    */\n    async x() {}\n}";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.ts"),
            original_text,
            ScriptKind::Ts,
        );

        // Apply formatting once
        let edits = format_document(&ctx, source_file, &mut nodes);
        let first_formatted = apply_bulk_edits(original_text, &edits);

        // Check that the asterisk is not corrupted
        assert!(
            !first_formatted.contains("*/\n   /"),
            "should not corrupt */ to /"
        );
        assert!(first_formatted.contains("*/"), "should preserve */ token");
        assert!(
            first_formatted.contains("async"),
            "should preserve async keyword"
        );

        // Apply formatting a second time to test stability
        let (source_file2, mut nodes2) = parse_source_file(
            test_parse_options("/test.ts"),
            &first_formatted,
            ScriptKind::Ts,
        );

        let edits2 = format_document(&ctx, source_file2, &mut nodes2);
        let second_formatted = apply_bulk_edits(&first_formatted, &edits2);

        // Check that second formatting doesn't introduce corruption
        assert!(
            !second_formatted.contains(" sync x()"),
            "should not corrupt async to sync"
        );
        assert!(
            second_formatted.contains("async"),
            "should preserve async keyword on second pass"
        );
    }

    // format JSDoc with tab indentation
    {
        let ctx = comment_ctx_zero_base(TS_FALSE);

        // Original code with tab indentation (tabs represented as \t)
        let original_text = "class Foo {\n\t/**\n\t * @param {string} argument - This is a param description.\n\t */\n\texample(argument) {\nconsole.log(argument);\n\t}\n}";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.ts"),
            original_text,
            ScriptKind::Ts,
        );

        // Apply formatting
        let edits = format_document(&ctx, source_file, &mut nodes);
        let formatted = apply_bulk_edits(original_text, &edits);

        // Check that tabs come before spaces (not spaces before tabs)
        // The comment lines should have format: tab followed by space and asterisk
        // NOT: space followed by tab and asterisk
        assert!(
            !formatted.contains(" \t*"),
            "should not have space before tab before asterisk"
        );
        assert!(
            formatted.contains("\t *"),
            "should have tab before space before asterisk"
        );

        // Verify console.log is properly indented with tabs
        assert!(
            formatted.contains("\t\tconsole.log"),
            "console.log should be indented with two tabs"
        );
    }

    // format comment inside multi-line argument list
    {
        let ctx = comment_ctx_zero_base(TS_FALSE);

        // Original code with proper indentation
        let original_text = "console.log(\n\t\"a\",\n\t// the second arg\n\t\"b\"\n);";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.ts"),
            original_text,
            ScriptKind::Ts,
        );

        // Apply formatting
        let edits = format_document(&ctx, source_file, &mut nodes);
        let formatted = apply_bulk_edits(original_text, &edits);

        // The comment should remain indented with a tab
        assert!(
            formatted.contains("\t// the second arg"),
            "comment should be indented with tab"
        );
        // The comment should not lose its indentation
        assert!(
            !formatted.contains("\n// the second arg"),
            "comment should not lose indentation"
        );
    }

    // format comment in chained method calls
    {
        let ctx = comment_ctx_zero_base(TS_FALSE);

        // Original code with proper indentation
        let original_text = "foo\n\t.bar()\n\t// A second call\n\t.baz();";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.ts"),
            original_text,
            ScriptKind::Ts,
        );

        // Apply formatting
        let edits = format_document(&ctx, source_file, &mut nodes);
        let formatted = apply_bulk_edits(original_text, &edits);

        // The comment should remain indented
        assert!(
            formatted.contains("\t// A second call") || formatted.contains("   // A second call"),
            "comment should be indented"
        );
        // The comment should not lose its indentation
        assert!(
            !formatted.contains("\n// A second call"),
            "comment should not lose indentation"
        );
    }

    // Regression test for issue #1928 - panic when formatting chained method call with comment
    // format chained method call with comment (issue #1928)
    {
        let ctx = comment_ctx_zero_base(TS_FALSE);

        // This code previously caused a panic with "strings: negative Repeat count"
        // because tokenIndentation was -1 and was being used directly for indentation
        let original_text = "foo\n\t.bar()\n\t// A second call\n\t.baz();";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.ts"),
            original_text,
            ScriptKind::Ts,
        );

        // Apply formatting - should not panic
        let edits = format_document(&ctx, source_file, &mut nodes);
        let formatted = apply_bulk_edits(original_text, &edits);

        // Verify the comment maintains proper indentation and doesn't lose it
        assert!(
            formatted.contains("\t// A second call") || formatted.contains("   // A second call"),
            "comment should be indented"
        );
        assert!(
            !formatted.contains("\n// A second call"),
            "comment should not be at column 0"
        );
    }

    // multiline comment inside block that opens on first line (issue #2649)
    {
        let ctx = with_format_code_settings(
            &Context::background(),
            FormatCodeSettings {
                editor_settings: EditorSettings {
                    tab_size: 4,
                    indent_size: 4,
                    base_indent_size: 0,
                    new_line_character: "\n".to_string(),
                    convert_tabs_to_spaces: TS_FALSE,
                    indent_style: IndentStyle::SMART,
                    trim_trailing_whitespace: TS_TRUE,
                    ..Default::default()
                },
                ..Default::default()
            },
            "\n",
        );

        let original_text = "document.addEventListener('DOMContentLoaded', () => {\n    /** @type {NodeListOf<HTMLSpanElement>} */\n    const elements = document.querySelectorAll('.test')\n});";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.js"),
            original_text,
            ScriptKind::Js,
        );

        let edits = format_document(&ctx, source_file, &mut nodes);
        let formatted = apply_bulk_edits(original_text, &edits);
        assert!(!formatted.is_empty(), "formatted text should not be empty");
    }

    // single-line comment inside block that opens on first line (issue #2649)
    {
        let ctx = with_format_code_settings(
            &Context::background(),
            FormatCodeSettings {
                editor_settings: EditorSettings {
                    tab_size: 4,
                    indent_size: 4,
                    base_indent_size: 0,
                    new_line_character: "\n".to_string(),
                    convert_tabs_to_spaces: TS_FALSE,
                    indent_style: IndentStyle::SMART,
                    trim_trailing_whitespace: TS_TRUE,
                    ..Default::default()
                },
                ..Default::default()
            },
            "\n",
        );

        let original_text = "document.addEventListener('DOMContentLoaded', () => {\n    // a comment\n    const x = 1\n});";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.ts"),
            original_text,
            ScriptKind::Ts,
        );

        let edits = format_document(&ctx, source_file, &mut nodes);
        let formatted = apply_bulk_edits(original_text, &edits);
        assert!(!formatted.is_empty(), "formatted text should not be empty");
    }
}

#[test]
fn test_format_selection_preserves_comments() {
    // format selection should not delete block comment when selection ends inside comment
    {
        let ctx = comment_ctx_zero_base(TS_TRUE);

        // Reproduce: const test/* comment */=5;
        // When selecting a range that ends inside the comment (before */), format selection should not delete the comment.
        let original_text = "const test/* comment */=5;";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.ts"),
            original_text,
            ScriptKind::Ts,
        );

        // Select a range that starts at the beginning of the line and ends inside the block comment.
        // This covers `const test/* comment`, stopping before the closing `*/`.
        let comment_start = original_text.find("/*").unwrap() as i32;
        let selection_end = comment_start + "/* comment".len() as i32; // ends inside the comment, before the closing `*/`

        let edits = format_selection(&ctx, source_file, 0, selection_end, &mut nodes);
        let formatted = apply_bulk_edits(original_text, &edits);

        // The entire statement should be preserved unchanged
        assert_eq!(
            formatted, original_text,
            "format selection should not delete the block comment or alter the statement"
        );
    }

    // format selection should not delete block comment when selection starts inside comment
    {
        let ctx = comment_ctx_zero_base(TS_TRUE);

        let original_text = "const test/* comment */=5;";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.ts"),
            original_text,
            ScriptKind::Ts,
        );

        // Select from inside the comment to the end
        let comment_start = original_text.find("/*").unwrap() as i32;
        let selection_start = comment_start + 3; // inside the comment

        let edits = format_selection(
            &ctx,
            source_file,
            selection_start,
            original_text.len() as i32,
            &mut nodes,
        );
        let formatted = apply_bulk_edits(original_text, &edits);

        // The entire statement should be preserved unchanged
        assert_eq!(
            formatted, original_text,
            "format selection should not delete the block comment or alter the statement"
        );
    }

    // full document format should preserve block comment and add spaces
    {
        let ctx = with_format_code_settings(
            &Context::background(),
            FormatCodeSettings {
                editor_settings: EditorSettings {
                    tab_size: 4,
                    indent_size: 4,
                    base_indent_size: 0,
                    new_line_character: "\n".to_string(),
                    convert_tabs_to_spaces: TS_TRUE,
                    indent_style: IndentStyle::SMART,
                    trim_trailing_whitespace: TS_TRUE,
                    ..Default::default()
                },
                insert_space_before_and_after_binary_operators: TS_TRUE,
                ..Default::default()
            },
            "\n",
        );

        let original_text = "const test/* comment */=5;";

        let (source_file, mut nodes) = parse_source_file(
            test_parse_options("/test.ts"),
            original_text,
            ScriptKind::Ts,
        );

        let edits = format_document(&ctx, source_file, &mut nodes);
        let formatted = apply_bulk_edits(original_text, &edits);

        // Full document format should preserve the comment and add spaces around `=`
        assert_eq!(
            "const test/* comment */ = 5;", formatted,
            "full format should preserve the block comment and add spaces"
        );
    }
}

#[test]
fn test_slice_bounds_panic() {
    // format code with trailing semicolon should not panic
    let ctx = comment_ctx(TS_TRUE);

    // Code from the issue that causes slice bounds panic
    let original_text = "const _enableDisposeWithListenerWarning = false\n\t// || Boolean(\"TRUE\") // causes a linter warning so that it cannot be pushed\n\t;\n";

    let (source_file, mut nodes) = parse_source_file(
        test_parse_options("/test.ts"),
        original_text,
        ScriptKind::Ts,
    );

    // This should not panic
    let edits = format_document(&ctx, source_file, &mut nodes);
    let formatted = apply_bulk_edits(original_text, &edits);

    // Basic sanity checks
    assert!(!formatted.is_empty(), "formatted text should not be empty");
    assert!(
        formatted.contains("_enableDisposeWithListenerWarning"),
        "should preserve variable name"
    );
}
