// Ported from tsc/internal/diagnosticwriter/diagnosticwriter_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `testDiagnostic`/`testFile` implement the `Diagnostic` trait over a
// `FileLike::from_text` file; `FromASTDiagnostics` needs a real parser, which
// lives in testutil crates this crate cannot depend on. `assert.DeepEqual` on
// the internals of `errorSummary` is dropped for the same reason — the
// rendered summary output covers the observable behavior.

use tsc_diagnostics::Category;
use tsc_locale::Locale;
use tsc_tspath::RootedFilePath;

use crate::diagnosticwriter::*;

#[derive(Clone)]
struct TestDiagnostic {
    file: Option<FileLike<'static>>,
    pos: i32,
    end: i32,
    code: i32,
    category: Category,
    source: String,
    message: String,
    message_chain: Vec<TestDiagnostic>,
    related_information: Vec<TestDiagnostic>,
}

/// `makeTestDiagnostic`
fn make_test_diagnostic(
    file: Option<FileLike<'static>>,
    pos: i32,
    end: i32,
    code: i32,
    category: Category,
    source: &str,
    message: &str,
    message_chain: Vec<TestDiagnostic>,
    related_information: Vec<TestDiagnostic>,
) -> TestDiagnostic {
    TestDiagnostic {
        file,
        pos,
        end,
        code,
        category,
        source: source.to_string(),
        message: message.to_string(),
        message_chain,
        related_information,
    }
}

impl Diagnostic for TestDiagnostic {
    fn file<'s>(&'s self) -> Option<FileLike<'s>> {
        self.file.clone()
    }
    fn pos(&self) -> i32 {
        self.pos
    }
    fn end(&self) -> i32 {
        self.end
    }
    fn len(&self) -> i32 {
        self.end - self.pos
    }
    fn code(&self) -> i32 {
        self.code
    }
    fn category(&self) -> Category {
        self.category
    }
    fn source(&self) -> String {
        self.source.clone()
    }
    fn localize(&self, _locale: &Locale) -> String {
        self.message.clone()
    }
    fn message_chain<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        self.message_chain
            .iter()
            .map(|c| Box::new(c.clone()) as Box<dyn Diagnostic + 's>)
            .collect()
    }
    fn related_information<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        self.related_information
            .iter()
            .map(|c| Box::new(c.clone()) as Box<dyn Diagnostic + 's>)
            .collect()
    }
}

fn render<D: Diagnostic>(diags: &[D]) -> String {
    let mut output = Vec::new();
    write_format_diagnostics(
        &mut output,
        diags,
        &FormattingOptions {
            new_line: "\n".to_string(),
            ..Default::default()
        },
    );
    String::from_utf8(output).unwrap()
}

#[test]
fn test_format_diagnostics() {
    let no_file = make_test_diagnostic(
        None, /*file*/
        0,
        0,
        2322,
        Category::Error,
        "",
        "You can't handle the truth!",
        vec![],
        vec![],
    );
    let file = FileLike::from_text(RootedFilePath::from("/main.ts"), "Hello, World!");
    let file_name = file.file_name().as_string().to_string();
    let default_file = make_test_diagnostic(
        Some(file.clone()),
        0,
        5,
        2323,
        Category::Error,
        "",
        "If only I had some brains...",
        vec![],
        vec![],
    );
    let multi_line_file =
        FileLike::from_text(RootedFilePath::from("/multiline.ts"), "Hello\nWorld\n");
    let multi_line_file_name = multi_line_file.file_name().as_string().to_string();
    let multi_line = make_test_diagnostic(
        Some(multi_line_file.clone()),
        2,
        9,
        2324,
        Category::Error,
        "",
        "I can show you the world",
        vec![],
        vec![],
    );
    let emoji_file = FileLike::from_text(RootedFilePath::from("/multiline.ts"), "a🧝b");
    let emoji_file_name = emoji_file.file_name().as_string().to_string();
    let emoji = make_test_diagnostic(
        Some(emoji_file.clone()),
        0,
        5,
        2325,
        Category::Error,
        "",
        "Shining, shimmering, splendid",
        vec![],
        vec![],
    );

    // TestDiagnostics does not test the localization of messages.
    let cases: &[(&[TestDiagnostic], &str)] = &[
        (&[], ""),
        (&[no_file], "error TS2322: You can't handle the truth!\n"),
        (
            &[default_file],
            &format!("{file_name}(1,1): error TS2323: If only I had some brains...\n"),
        ),
        (
            &[multi_line],
            &format!("{multi_line_file_name}(1,3): error TS2324: I can show you the world\n"),
        ),
        (
            &[emoji],
            &format!("{emoji_file_name}(1,1): error TS2325: Shining, shimmering, splendid\n"),
        ),
    ];
    for (diagnostics, expected_output) in cases {
        let output = render(diagnostics);
        assert_eq!(&output, expected_output);
    }
}

#[test]
fn test_format_diagnostics_spanning_multiple_lines() {
    let cases: &[(&str, i32, i32, &str)] = &[
        ("abcdefghjkl\nmnopqrstuvw\nxyz\n", 2, 12, "(1,3)"),
        ("abcdefghjkl\nmnopqrstuvw\nxyz\n", 9, 14, "(1,10)"),
        // Pos 11 is the line-1 terminator: it belongs to line 1 (col 12),
        // matching `compute_line_of_position`.
        ("abcdefghjkl\nmnopqrstuvw\nxyz\n", 11, 12, "(1,12)"),
        ("abcdefghjkl\nmnopqrstuvw\nxyz\n", 19, 20, "(2,8)"),
    ];
    for (text, pos, end, expected_output) in cases {
        let diagnostics = [make_test_diagnostic(
            Some(FileLike::from_text(RootedFilePath::from("/main.ts"), *text)),
            *pos,
            *end,
            1337,
            Category::Error,
            "",
            "A whole new world",
            vec![],
            vec![],
        )];
        let output = render(&diagnostics);
        assert!(output.contains(expected_output), "output: {output:?}");
    }
}

#[test]
fn test_write_error_summary_text() {
    let empty_string_message = "Message 1";
    // (`(fileName, numErrors)`, `numGlobalErrors`, expectedOutput)
    let cases: &[(&[(&str, usize)], usize, &str)] = &[
        (
            &[
                ("/error/reports/theFile1.ts", 1),
                ("/error/reports/theFile2.ts", 1),
            ],
            0,
            "\nFound 2 errors in 2 files.\n\nErrors  Files\n     1  error/reports/theFile1.ts\u{1b}[90m:1\u{1b}[0m\n     1  error/reports/theFile2.ts\u{1b}[90m:1\u{1b}[0m\n\n",
        ),
        (
            &[("/error/reports/theFile.ts", 2)],
            0,
            "\nFound 2 errors in the same file, starting at: error/reports/theFile.ts\u{1b}[90m:1\u{1b}[0m\n\n",
        ),
        (&[], 2, "\nFound 2 errors.\n\n"),
        (
            &[("/error/reports/theFile.ts", 1)],
            0,
            "\nFound 1 error in error/reports/theFile.ts\u{1b}[90m:1\u{1b}[0m\n\n",
        ),
        (&[], 1, "\nFound 1 error.\n\n"),
    ];
    for (files, global_errors, expected_output) in cases {
        let mut diagnostics = Vec::new();
        for (file_name, num_errors) in *files {
            let file = FileLike::from_text(RootedFilePath::from(*file_name), empty_string_message);
            for _ in 0..*num_errors {
                diagnostics.push(make_test_diagnostic(
                    Some(file.clone()),
                    0,
                    2,
                    2322,
                    Category::Error,
                    "",
                    empty_string_message,
                    vec![],
                    vec![],
                ));
            }
        }
        for _ in 0..*global_errors {
            diagnostics.push(make_test_diagnostic(
                None,
                0,
                0,
                2322,
                Category::Error,
                "",
                empty_string_message,
                vec![],
                vec![],
            ));
        }

        let mut output = Vec::new();
        write_error_summary_text(
            &mut output,
            &diagnostics,
            &FormattingOptions {
                new_line: "\n".to_string(),
                current_directory: "/".into(),
                ..Default::default()
            },
        );
        let output = String::from_utf8(output).unwrap();
        assert_eq!(&output, expected_output);
    }
}
