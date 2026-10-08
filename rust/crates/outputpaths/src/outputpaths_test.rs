// Ported from tsc/internal/outputpaths/outputpaths_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_core::options_generated::CompilerOptions;
use tsc_core::tristate::TS_TRUE;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath};

use crate::{
    OutputPathsHost, get_build_info_file_name, get_output_declaration_file_name_worker,
    get_output_js_file_name_worker, get_source_file_name_in_new_dir,
};

/// `type outputPathsHost struct` — the test host.
struct TestHost {
    common_source_directory: RootedDirectoryPath,
    content_mapper_extensions: Vec<String>,
}

impl OutputPathsHost for TestHost {
    fn common_source_directory(&self) -> RootedDirectoryPath {
        self.common_source_directory.clone()
    }

    fn content_mapper_extensions(&self) -> &[String] {
        &self.content_mapper_extensions
    }

    fn case_sensitivity(&self) -> CaseSensitivity {
        CaseSensitivity::CaseInsensitive
    }
}

#[test]
fn test_get_source_file_name_in_new_dir_source_matches_common_directory() {
    let actual = get_source_file_name_in_new_dir(
        &RootedFilePath::from("/project/src"),
        &RootedDirectoryPath::from("/project/out"),
        &RootedDirectoryPath::from("/project/src"),
        CaseSensitivity::CaseSensitive,
    );
    assert_eq!(actual, RootedFilePath::from("/project/src"));
}

#[test]
fn test_get_source_file_name_in_new_dir_canonicalization_shrinks_common_directory() {
    // Each Kelvin sign '\u212A' case-folds to the single-byte 'k', so the raw
    // (non-canonicalized) commonSourceDirectory is longer, in bytes, than the source
    // file path it's a case-insensitive prefix of, even though the file path itself
    // is longer overall once its own (already-lowercase) suffix is included.
    // Slicing sourceFilePath by len(commonSourceDirectory) bytes would still panic
    // here ([14:11]); this must clamp per-rune instead, like the reference
    // implementation's substring does.
    let actual = get_source_file_name_in_new_dir(
        &RootedFilePath::from("/kkkk/a.ts"),
        &RootedDirectoryPath::from("/out"),
        &RootedDirectoryPath::from("/\u{212A}\u{212A}\u{212A}\u{212A}"),
        CaseSensitivity::CaseInsensitive,
    );
    assert_eq!(actual, RootedFilePath::from("/out/a.ts"));
}

#[test]
fn test_get_build_info_file_name_across_roots() {
    struct TestCase {
        name: &'static str,
        root_dir: &'static str,
        out_dir: &'static str,
        config_file_path: &'static str,
        expected: &'static str,
    }

    let tests = [
        TestCase {
            name: "same root",
            root_dir: "c:/src",
            out_dir: "c:/out",
            config_file_path: "c:/src/project/tsconfig.json",
            expected: "c:/out/project/tsconfig.tsbuildinfo",
        },
        TestCase {
            name: "empty stem",
            root_dir: "c:/src",
            out_dir: "c:/out",
            config_file_path: "c:/src/project/.json",
            expected: "c:/out/project/.tsbuildinfo",
        },
        TestCase {
            name: "dot stem",
            root_dir: "c:/src",
            out_dir: "c:/out",
            config_file_path: "c:/src/project/..json",
            expected: "c:/out/project/..tsbuildinfo",
        },
        TestCase {
            name: "empty filename stem without rootDir",
            root_dir: "",
            out_dir: "c:/out",
            config_file_path: "c:/src/project/.json",
            expected: "c:/out/.tsbuildinfo",
        },
        TestCase {
            name: "parent-dot filename stem without rootDir",
            root_dir: "",
            out_dir: "c:/out",
            config_file_path: "c:/src/project/...json",
            expected: "c:/out/...tsbuildinfo",
        },
        TestCase {
            name: "empty filename stem without outDir",
            root_dir: "",
            out_dir: "",
            config_file_path: "c:/src/project/.json",
            expected: "c:/src/project/.tsbuildinfo",
        },
        TestCase {
            name: "dot filename stem without outDir",
            root_dir: "",
            out_dir: "",
            config_file_path: "c:/src/project/..json",
            expected: "c:/src/project/..tsbuildinfo",
        },
        TestCase {
            name: "different drive",
            root_dir: "c:/src",
            out_dir: "c:/out",
            config_file_path: "d:/project/tsconfig.json",
            expected: "d:/project/tsconfig.tsbuildinfo",
        },
        TestCase {
            name: "different UNC authority",
            root_dir: "//server-a/src",
            out_dir: "//server-a/out",
            config_file_path: "//server-b/project/tsconfig.json",
            expected: "//server-b/project/tsconfig.tsbuildinfo",
        },
        TestCase {
            name: "different URL authority",
            root_dir: "file://server-a/src",
            out_dir: "file://server-a/out",
            config_file_path: "file://server-b/project/tsconfig.json",
            expected: "file://server-b/project/tsconfig.tsbuildinfo",
        },
    ];

    for test in tests {
        let options = CompilerOptions {
            incremental: TS_TRUE,
            root_dir: RootedDirectoryPath::from(test.root_dir),
            out_dir: RootedDirectoryPath::from(test.out_dir),
            config_file_path: RootedFilePath::from(test.config_file_path),
            ..Default::default()
        };
        let actual = get_build_info_file_name(&options, CaseSensitivity::CaseInsensitive);
        assert_eq!(
            actual,
            RootedFilePath::from(test.expected),
            "case {:?}",
            test.name
        );
    }
}

#[test]
fn test_get_output_file_name_across_roots() {
    let input = RootedFilePath::from("d:/shared.ts");
    let options = CompilerOptions {
        out_dir: RootedDirectoryPath::from("c:/dist"),
        ..Default::default()
    };
    let host = TestHost {
        common_source_directory: RootedDirectoryPath::from("c:/src"),
        content_mapper_extensions: Vec::new(),
    };

    assert_eq!(
        get_output_js_file_name_worker(&input, &options, &host),
        RootedFilePath::from("d:/shared.js")
    );
    assert_eq!(
        get_output_declaration_file_name_worker(&input, &options, &host),
        RootedFilePath::from("d:/shared.d.ts")
    );
}

#[test]
fn test_output_file_names_preserve_empty_and_dot_stems() {
    let host = TestHost {
        common_source_directory: RootedDirectoryPath::from("/project/src"),
        content_mapper_extensions: vec![".css".to_string()],
    };
    let options = CompilerOptions {
        out_dir: RootedDirectoryPath::from("/project/out"),
        ..Default::default()
    };
    for (input, js, declaration) in [
        ("/project/src/.ts", "/project/out/.js", "/project/out/.d.ts"),
        (
            "/project/src/..ts",
            "/project/out/..js",
            "/project/out/..d.ts",
        ),
        (
            "/project/src/...ts",
            "/project/out/...js",
            "/project/out/...d.ts",
        ),
        (
            "/project/src/.mts",
            "/project/out/.mjs",
            "/project/out/.d.mts",
        ),
        (
            "/project/src/.d.ts",
            "/project/out/.js",
            "/project/out/.d.ts",
        ),
        (
            "/project/src/.css",
            "/project/out/.css",
            "/project/out/.d.css.ts",
        ),
    ] {
        let input = RootedFilePath::from(input);
        assert_eq!(
            get_output_js_file_name_worker(&input, &options, &host),
            RootedFilePath::from(js),
            "input {input:?}"
        );
        assert_eq!(
            get_output_declaration_file_name_worker(&input, &options, &host),
            RootedFilePath::from(declaration),
            "input {input:?}"
        );
    }
}
