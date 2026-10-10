// Ported from tsc/internal/ls/lsutil/utilities_test.go @
// ec47d33c23e464a17cdf2475632cba629bee8763.

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::{Node, NodeId};
use tsc_core::scriptkind::ScriptKind;
use tsc_core::tristate::{TS_FALSE, TS_TRUE};
use tsc_parser::parse_source_file;
use tsc_tspath::{path_key_from_canonical, rooted_file_path_from_normalized};

use crate::organizeimports::{
    get_organize_imports_preset_string_comparer, resolve_organize_imports_sort,
};
use crate::userpreferences::{
    OrganizeImportsCollation, OrganizeImportsSort,
};
use crate::userpreferences_generated::UserPreferences;
use crate::utilities::probably_uses_semicolons;

fn parse_ts(text: &str) -> (NodeId, Vec<Node>) {
    parse_source_file(
        SourceFileParseOptions {
            file_name: rooted_file_path_from_normalized("/test.ts"),
            path_key: path_key_from_canonical("/test.ts"),
            ..Default::default()
        },
        text,
        ScriptKind::Ts,
    )
}

#[test]
fn test_probably_uses_semicolons() {
    let tests: &[(&str, &str, bool)] = &[
        (
            "mixed semicolons and ASI favors semicolons when ratio exceeds one fifth",
            // First five observations: 2 with semicolon, 3 without. Real ratio 2/3 > 1/5.
            // Integer division bug compared against 1/5==0 and used with/without as ints,
            // so the old check was effectively (with/without) > 0, which failed here.
            "let a = 1;\nlet b = 2;\nlet c = 3\nlet d = 4\nlet e = 5\n",
            true,
        ),
        (
            "consistent ASI with no semicolons",
            "let a = 1\nlet b = 2\nlet c = 3\n",
            false,
        ),
        (
            "consistent semicolons",
            "let a = 1;\nlet b = 2;\nlet c = 3;\n",
            true,
        ),
    ];

    for &(name, src, want) in tests {
        let (file, mut nodes) = parse_ts(src);
        let got = probably_uses_semicolons(&mut nodes, file);
        assert_eq!(got, want, "ProbablyUsesSemicolons() failed: {name}");
    }
}

#[test]
fn test_resolve_organize_imports_sort() {
    let tests: &[(&str, UserPreferences, OrganizeImportsSort)] = &[
        (
            "explicit sort wins",
            UserPreferences {
                organize_imports_sort: OrganizeImportsSort::ORDINAL,
                organize_imports_collation: OrganizeImportsCollation::UNICODE,
                organize_imports_ignore_case: TS_TRUE,
                ..Default::default()
            },
            OrganizeImportsSort::ORDINAL,
        ),
        (
            "unicode case-sensitive maps to natural",
            UserPreferences {
                organize_imports_collation: OrganizeImportsCollation::UNICODE,
                organize_imports_ignore_case: TS_FALSE,
                ..Default::default()
            },
            OrganizeImportsSort::NATURAL,
        ),
        (
            "unicode ignore case maps to natural ignore case",
            UserPreferences {
                organize_imports_collation: OrganizeImportsCollation::UNICODE,
                organize_imports_ignore_case: TS_TRUE,
                ..Default::default()
            },
            OrganizeImportsSort::NATURAL_IGNORE_CASE,
        ),
        (
            "unicode unknown case sensitivity stays auto for detection",
            UserPreferences {
                organize_imports_collation: OrganizeImportsCollation::UNICODE,
                ..Default::default()
            },
            OrganizeImportsSort::AUTO,
        ),
        (
            "ordinal ignore case maps to ordinal ignore case",
            UserPreferences {
                organize_imports_ignore_case: TS_TRUE,
                ..Default::default()
            },
            OrganizeImportsSort::ORDINAL_IGNORE_CASE,
        ),
        (
            "ordinal case sensitive maps to ordinal",
            UserPreferences {
                organize_imports_ignore_case: TS_FALSE,
                ..Default::default()
            },
            OrganizeImportsSort::ORDINAL,
        ),
        (
            "unknown ordinal stays auto",
            UserPreferences::default(),
            OrganizeImportsSort::AUTO,
        ),
    ];

    for (name, preferences, want) in tests {
        let got = resolve_organize_imports_sort(preferences);
        assert_eq!(got, *want, "ResolveOrganizeImportsSort() failed: {name}");
    }
}

#[test]
fn test_compare_organize_imports_natural_strings() {
    let comparer = get_organize_imports_preset_string_comparer(
        OrganizeImportsSort::NATURAL_IGNORE_CASE,
    );
    let tests: &[(&str, &str, &str, i32)] = &[
        ("numeric runs sort by numeric value", "a2", "a100", -1),
        (
            "numeric runs with equal value use raw tie break",
            "a02",
            "a2",
            -1,
        ),
        (
            "accents are folded for primary comparison",
            "\u{C0}",
            "B",
            -1,
        ),
        ("raw comparison breaks accent ties", "A", "\u{C0}", -1),
        (
            "hyphen sorts before slash like Intl.Collator fallback",
            "app-init",
            "app/app",
            -1,
        ),
    ];

    for &(name, a, b, want) in tests {
        let got = cmp_sign(comparer(a, b));
        assert_eq!(got, want, "comparer({a:?}, {b:?}) failed: {name}");
    }
}

/// `cmpSign`.
fn cmp_sign(value: i32) -> i32 {
    if value < 0 {
        -1
    } else if value > 0 {
        1
    } else {
        0
    }
}
