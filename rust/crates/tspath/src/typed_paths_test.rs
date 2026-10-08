// Ported from tsc/internal/tspath/typed_paths_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go benchmarks (BenchmarkRootedDirectoryPathResolveFile,
// BenchmarkRootedFilePathToPathKey) are omitted — no stable-Rust cargo test
// equivalent. Go's `assertPanics` is `assert_panics` via catch_unwind.

use crate::{
    CaseSensitivity, FileNameStem, ModuleSpecifier, PathKey, RelativePath, RootedDirectoryPath,
    RootedFilePath, RootedPath, get_root_length, path_key_from_canonical,
    relative_path_from_normalized, rooted_directory_path_from_absolute,
    rooted_directory_path_from_normalized, rooted_directory_path_from_path,
    rooted_file_path_from_absolute, rooted_file_path_from_normalized, rooted_file_path_from_path,
    rooted_path_from_absolute, rooted_path_from_normalized, to_module_specifier, to_relative_path,
    to_rooted_directory_path, to_rooted_file_path, to_rooted_path, to_source_map_location,
    try_path_key_from_canonical, try_rooted_file_path_from_absolute,
    try_rooted_file_path_from_normalized, try_rooted_path_from_absolute,
    try_rooted_path_from_normalized,
};

fn assert_panics(f: impl FnOnce()) {
    // PORT: mirrors Go's assertPanics helper (recover() != nil).
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).is_err());
}

#[test]
fn test_to_rooted_file_path() {
    let ignored = RootedDirectoryPath::from("/ignored");
    let project = RootedDirectoryPath::from("/project");

    assert_eq!(
        to_rooted_file_path("./src/../src/a.ts", &project).as_string(),
        "/project/src/a.ts"
    );
    assert_eq!(
        to_rooted_file_path("/project/src/", &ignored).as_string(),
        "/project/src"
    );
    assert_eq!(to_rooted_file_path("/", &ignored).as_string(), "/");
    assert_eq!(
        to_rooted_file_path("file:///project/src/a.ts", &ignored).as_string(),
        "file:///project/src/a.ts"
    );
    assert_eq!(
        to_rooted_file_path("^/untitled/ts-nul-authority/Untitled-1", &ignored).as_string(),
        "^/untitled/ts-nul-authority/Untitled-1"
    );
    for (input, expected) in [
        ("c:", "c:/"),
        ("//server", "//server/"),
        ("file://server", "file://server/"),
        (
            "^/~ts-uri~/custom/ts-nul-authority",
            "^/~ts-uri~/custom/ts-nul-authority/",
        ),
        (
            "^/~ts-uri~/custom/authority?query",
            "^/~ts-uri~/custom/authority?query/",
        ),
    ] {
        assert_eq!(to_rooted_path(input, &ignored).as_string(), expected);
        assert_eq!(to_rooted_file_path(input, &ignored).as_string(), expected);
        assert_eq!(
            to_rooted_directory_path(input, &ignored).as_string(),
            expected
        );
    }
    let disk_with_scheme_text = to_rooted_path("/a://b?x/../y", &ignored);
    assert_eq!(disk_with_scheme_text.as_string(), "/a:/y");
    assert!(try_rooted_path_from_normalized(disk_with_scheme_text.as_string()).is_some());
    for input in [
        "http://server?query#fragment",
        "http://server?x/../y",
        "file:///c:?query/path",
    ] {
        assert_panics(|| {
            to_rooted_path(input, &ignored);
        });
        assert!(try_rooted_path_from_absolute(input).is_none());
        assert!(try_rooted_path_from_normalized(input).is_none());
    }
    let url_directory = rooted_directory_path_from_normalized("http://server/base");
    assert_panics(|| {
        to_rooted_path("file.ts?query/..", &url_directory);
    });
    assert_panics(|| {
        url_directory.resolve_file("file.ts?query");
    });
    assert_panics(|| {
        url_directory.resolve_file("file.ts?query/..");
    });
    assert_panics(|| {
        url_directory.resolve_relative_file(&RelativePath::from("file.ts?query"));
    });
    assert_panics(|| {
        url_directory.resolve_file_from_normalized_relative("file.ts?query");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("http://server/file.ts").append_suffix("?query");
    });
    assert_panics(|| {
        PathKey::from("http://server/file.ts").append_canonical_suffix("#fragment");
    });
    assert_panics(|| {
        PathKey::from("http://server/base").append_canonical_component("file.ts?query");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("http://server/file.ts").change_extension(".js?query");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("http://server/file.ts")
            .change_full_extension(".js#fragment");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("http://server/file.ts").change_any_extension(
            ".js?query",
            &[".ts"],
            CaseSensitivity::CaseSensitive,
        );
    });
    assert_eq!(
        url_directory.resolve_file("/disk/file?name.ts"),
        RootedFilePath::from("/disk/file?name.ts")
    );
    assert_eq!(
        url_directory.resolve_directory("^/~ts-uri~/custom/authority?query/"),
        RootedDirectoryPath::from("^/~ts-uri~/custom/authority?query/")
    );
}

#[test]
fn test_encoded_dynamic_paths_preserve_opaque_identity() {
    let root = "^/~ts-uri~/custom/authority";
    let root_with_separator = RootedPath::from(format!("{root}/"));
    let upper = rooted_file_path_from_normalized(&format!("{root}/Foo.ts"));
    let lower = rooted_file_path_from_normalized(&format!("{root}/foo.ts"));

    assert_eq!(get_root_length(root), root.len());
    assert_eq!(
        CaseSensitivity::CaseInsensitive.path_key(&RootedPath::from(root)),
        CaseSensitivity::CaseInsensitive.path_key(&root_with_separator)
    );
    assert!(CaseSensitivity::CaseInsensitive.compare_file_paths(&upper, &lower) != 0);
    assert!(!CaseSensitivity::CaseInsensitive.contains_file_path(
        &RootedDirectoryPath::from(format!("{root}/Folder")),
        &RootedFilePath::from(format!("{root}/folder/file.ts"))
    ));
    let relative = CaseSensitivity::CaseInsensitive
        .relative_file_path_from_directory(&RootedDirectoryPath::from(root), &upper);
    let relative = relative.expect("expected a relative path");
    assert_eq!(relative, RelativePath::from("Foo.ts"));
    assert!(
        CaseSensitivity::CaseInsensitive
            .relative_path_from_path(
                &RootedDirectoryPath::from("^/~ts-uri~/custom/Authority/src"),
                &RootedPath::from("^/~ts-uri~/custom/authority/lib/x.ts"),
            )
            .is_none()
    );
    assert!(
        !PathKey::from("^/~ts-uri~/custom/Authority/src")
            .contains_path(&PathKey::from("^/~ts-uri~/custom/authority/src/file.ts"))
    );
}

#[test]
fn test_path_key_from_canonical_rejects_url_suffix() {
    let path = "http://server/?x/../y";
    assert!(try_path_key_from_canonical(path).is_none());
}

#[test]
fn test_dynamic_path_key_case_insensitive_key_preserves_identity() {
    let upper = CaseSensitivity::CaseInsensitive.path_key(&rooted_path_from_normalized(
        "^/~ts-uri~/custom/ts-nul-authority/Foo.ts",
    ));
    let lower = CaseSensitivity::CaseInsensitive.path_key(&rooted_path_from_normalized(
        "^/~ts-uri~/custom/ts-nul-authority/foo.ts",
    ));

    assert_eq!(upper.case_insensitive_key(), upper);
    assert_eq!(lower.case_insensitive_key(), lower);
    assert!(upper.case_insensitive_key() != lower.case_insensitive_key());
}

#[test]
fn test_extension_mutations_preserve_normalized_invariant() {
    // Each mutation must panic; Go uses a slice of thunks.
    let mutates: Vec<Box<dyn Fn() -> RootedFilePath>> = vec![
        Box::new(|| {
            rooted_file_path_from_normalized("/project/.ts")
                .remove_file_extension()
                .append_suffix("")
        }),
        Box::new(|| {
            rooted_file_path_from_normalized("/project/.ts")
                .remove_extension(".ts")
                .append_suffix("")
        }),
        Box::new(|| rooted_file_path_from_normalized("/project/.ts").change_extension("")),
        Box::new(|| rooted_file_path_from_normalized("/project/.d.ts").change_full_extension("")),
        Box::new(|| {
            rooted_file_path_from_normalized("/project/.ts").change_any_extension(
                "",
                &[".ts"],
                CaseSensitivity::CaseSensitive,
            )
        }),
        Box::new(|| {
            rooted_file_path_from_normalized("/project/..ts")
                .remove_file_extension()
                .append_suffix("")
        }),
        Box::new(|| {
            rooted_file_path_from_normalized("/project/..ts")
                .remove_extension(".ts")
                .append_suffix("")
        }),
        Box::new(|| rooted_file_path_from_normalized("/project/..ts").change_extension("")),
        Box::new(|| rooted_file_path_from_normalized("/project/...ts").change_full_extension("")),
        Box::new(|| {
            rooted_file_path_from_normalized("/project/..ts").change_any_extension(
                "",
                &[".ts"],
                CaseSensitivity::CaseSensitive,
            )
        }),
        Box::new(|| {
            rooted_file_path_from_normalized("http://example.com/file.ts").change_any_extension(
                "",
                &[".com/file.ts"],
                CaseSensitivity::CaseSensitive,
            )
        }),
    ];
    for mutate in mutates {
        assert_panics(move || {
            mutate();
        });
    }

    for (file_name, component) in [
        ("//node_modules/pkg/index.d.ts", "node_modules"),
        ("http://node_modules/pkg/index.d.ts", "node_modules"),
        ("file:///c:/pkg/index.d.ts", "c:"),
        ("^/~ts-uri~/https/node_modules/file.ts", "node_modules"),
    ] {
        let file_name = RootedFilePath::from(file_name);
        assert!(file_name.split_at_component(component).is_none());
        assert!(file_name.split_at_last_component(component).is_none());
        assert!(
            CaseSensitivity::CaseSensitive
                .path_key(&file_name.as_path())
                .split_at_canonical_component(component)
                .is_none()
        );
    }

    assert!(
        PathKey::from("")
            .split_at_canonical_component("node_modules")
            .is_none()
    );
    assert!(
        RootedFilePath::from("")
            .split_at_component("node_modules")
            .is_none()
    );
}

#[test]
fn test_file_name_stems_preserve_filename_prefixes() {
    for (file_name, stem, output) in [
        ("", "", ""),
        ("/project/file.ts", "/project/file", "/project/file.js"),
        ("/project/.ts", "/project/", "/project/.js"),
        ("/project/..ts", "/project/.", "/project/..js"),
        ("/project/...ts", "/project/..", "/project/...js"),
        ("/project/.d.ts", "/project/", "/project/.js"),
        ("/.ts", "/", "/.js"),
        ("c:/.ts", "c:/", "c:/.js"),
        ("//server/.ts", "//server/", "//server/.js"),
        ("file:///.ts", "file:///", "file:///.js"),
        (
            "^/~ts-uri~/custom/ts-nul-authority/.ts",
            "^/~ts-uri~/custom/ts-nul-authority/",
            "^/~ts-uri~/custom/ts-nul-authority/.js",
        ),
    ] {
        let file_name = RootedFilePath::from(file_name);
        let stem = FileNameStem::from(stem);
        let output = RootedFilePath::from(output);
        assert_eq!(file_name.as_stem().as_string(), file_name.as_string());
        assert_eq!(file_name.as_stem().append_suffix(""), file_name);
        let stem0: FileNameStem = file_name.remove_file_extension();
        assert_eq!(stem0, stem);
        if file_name.is_empty() {
            assert_eq!(stem.append_suffix(""), output);
            assert_panics(|| {
                stem.append_suffix(".js");
            });
        } else {
            let output0 = stem.append_suffix(".js");
            assert_eq!(output0, output);
            assert_eq!(
                rooted_file_path_from_normalized(output0.as_string()),
                output0
            );
            assert_eq!(
                file_name.remove_extension(".ts").append_suffix(".ts"),
                file_name
            );
        }
    }

    for file_name in ["/project/.ts", "/project/..ts", "/project/...ts"] {
        let file_name = RootedFilePath::from(file_name);
        assert_panics(|| {
            file_name.remove_file_extension().append_suffix("");
        });
    }
    let stem = RootedFilePath::from("/project/file.ts").remove_file_extension();
    assert_panics(|| {
        stem.append_suffix("/other.js");
    });
    assert_panics(|| {
        stem.append_suffix("\\other.js");
    });
    assert_panics(|| {
        RootedFilePath::from("http://example.com/.ts")
            .remove_file_extension()
            .append_suffix("?query");
    });
    assert_panics(|| {
        RootedFilePath::from("/project/file.ts").remove_extension(".js");
    });
    assert_panics(|| {
        RootedFilePath::from("/project/file.ts").remove_extension("/file.ts");
    });
}

#[test]
fn test_compare_file_name_stems_keeps_literal_dot_components_and_casing_policy() {
    for (a, b, equal_sensitive, equal_insensitive) in [
        ("/project/.ts", "/project/.d.ts", true, true),
        ("/project/..ts", "/project.ts", false, false),
        ("/project/...ts", "/.ts", false, false),
        ("c:/project/.ts", "C:/project/.d.ts", true, true),
        ("/project/File.ts", "/project/file.js", false, true),
        (
            "^/~ts-uri~/custom/ts-nul-authority/Foo.ts",
            "^/~ts-uri~/custom/ts-nul-authority/foo.js",
            false,
            false,
        ),
    ] {
        let a = RootedFilePath::from(a).remove_file_extension();
        let b = RootedFilePath::from(b).remove_file_extension();
        assert_eq!(
            CaseSensitivity::CaseSensitive.compare_file_name_stems(&a, &b) == 0,
            equal_sensitive
        );
        assert_eq!(
            CaseSensitivity::CaseInsensitive.compare_file_name_stems(&a, &b) == 0,
            equal_insensitive
        );
    }
}

#[test]
fn test_split_at_root_level_component_keeps_root() {
    for file_name in [
        "/node_modules/pkg/index.d.ts",
        "c:/node_modules/pkg/index.d.ts",
        "file:///node_modules/pkg/index.d.ts",
    ] {
        let file_name = rooted_file_path_from_normalized(file_name);
        let (before, through) = file_name.split_at_component("node_modules").unwrap();
        let (root, _) = file_name.root_and_relative_path();
        assert_eq!(before, root);
        assert_eq!(through, root.resolve_directory("node_modules"));

        let (before, through) = file_name.split_at_last_component("node_modules").unwrap();
        assert_eq!(before, root);
        assert_eq!(through, root.resolve_directory("node_modules"));

        let (key_before, key_through) = CaseSensitivity::CaseSensitive
            .path_key(&file_name.as_path())
            .split_at_canonical_component("node_modules")
            .unwrap();
        assert_eq!(
            key_before,
            CaseSensitivity::CaseSensitive.path_key(&root.as_path())
        );
        assert_eq!(
            key_through,
            CaseSensitivity::CaseSensitive
                .path_key(&root.resolve_directory("node_modules").as_path())
        );
    }
}

#[test]
fn test_to_rooted_file_path_requires_root() {
    let project = RootedDirectoryPath::from("/project");
    assert_panics(|| {
        to_rooted_file_path("", &project);
    });
    assert_panics(|| {
        to_rooted_file_path("src/a.ts", &RootedDirectoryPath::default());
    });
}

#[test]
fn test_rooted_file_path_from_absolute() {
    assert_eq!(
        rooted_file_path_from_absolute("C:\\project\\src\\..\\a.ts"),
        rooted_file_path_from_normalized("C:/project/a.ts")
    );
    assert_panics(|| {
        rooted_file_path_from_absolute("src/a.ts");
    });
    assert!(try_rooted_file_path_from_absolute("src/a.ts").is_none());
    let absolute = try_rooted_file_path_from_absolute("/project/src/../a.ts").unwrap();
    assert_eq!(absolute, rooted_file_path_from_normalized("/project/a.ts"));
    for (input, expected) in [
        ("c:", "c:/"),
        ("//server", "//server/"),
        ("file://server", "file://server/"),
    ] {
        assert_eq!(rooted_file_path_from_absolute(input).as_string(), expected);
    }
}

#[test]
fn test_rooted_file_path_from_normalized() {
    assert_eq!(
        rooted_file_path_from_normalized("/project/src/a.ts").as_string(),
        "/project/src/a.ts"
    );
    assert_eq!(rooted_file_path_from_normalized("c:/").as_string(), "c:/");
    assert_eq!(
        rooted_file_path_from_normalized("//server/").as_string(),
        "//server/"
    );
    assert_eq!(
        rooted_file_path_from_normalized("file://server/").as_string(),
        "file://server/"
    );
    assert_panics(|| {
        rooted_file_path_from_normalized("/project/src/../a.ts");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("src/a.ts");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("/project/src/");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("/project\\src\\a.ts");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("/project//src/a.ts");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("c:");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("//server");
    });
    assert_panics(|| {
        rooted_file_path_from_normalized("file://server");
    });

    for file_name in ["/project/src/a.ts", "c:/", "//server/", "file://server/"] {
        let result = try_rooted_file_path_from_normalized(file_name).unwrap();
        assert_eq!(result.as_string(), file_name);
    }
    for file_name in [
        "",
        "/project/src/../a.ts",
        "src/a.ts",
        "/project/src/",
        "/project\\src\\a.ts",
        "/project//src/a.ts",
        "c://project/src/a.ts",
        "//server//share/a.ts",
        "file://server//a.ts",
        "c:",
        "//server",
        "file://server",
    ] {
        assert!(try_rooted_file_path_from_normalized(file_name).is_none());
    }
}

#[test]
fn test_typed_path_constructors_and_decoders() {
    let project = RootedDirectoryPath::from("/project");

    assert_eq!(
        to_rooted_directory_path("./src", &project).as_string(),
        "/project/src"
    );
    assert_eq!(
        rooted_directory_path_from_absolute("/project/src/../lib/").as_string(),
        "/project/lib"
    );
    assert_eq!(
        rooted_directory_path_from_absolute("c:\\project\\src\\..\\lib\\").as_string(),
        "c:/project/lib"
    );
    assert_eq!(
        rooted_directory_path_from_absolute("file:///project/src/../lib/").as_string(),
        "file:///project/lib"
    );
    assert_eq!(
        rooted_directory_path_from_normalized("/project/src").as_string(),
        "/project/src"
    );
    assert_eq!(
        path_key_from_canonical("/project/src").as_string(),
        "/project/src"
    );
    assert_eq!(
        CaseSensitivity::CaseSensitive.path_key(&rooted_path_from_absolute("/project/src/")),
        PathKey::from("/project/src")
    );
    let path = try_path_key_from_canonical("/project/src").unwrap();
    assert_eq!(path.as_string(), "/project/src");
    assert_eq!(to_module_specifier("./src").as_string(), "./src");

    assert_panics(|| {
        rooted_directory_path_from_absolute("project/src");
    });
    assert_panics(|| {
        rooted_directory_path_from_normalized("/project/src/");
    });
    assert_panics(|| {
        path_key_from_canonical("/project/../src");
    });
    assert_panics(|| {
        path_key_from_canonical("project/src");
    });
    for value in [
        "/project/../src",
        "project/src",
        "c:",
        "//server",
        "http://server",
        "file:///c:",
    ] {
        assert!(try_path_key_from_canonical(value).is_none());
    }
    assert_panics(|| {
        CaseSensitivity::CaseSensitive.path_key(&to_rooted_path(
            "project/src",
            &RootedDirectoryPath::default(),
        ));
    });
}

#[test]
fn test_relative_path() {
    assert_eq!(
        to_relative_path(".\\src\\..\\lib\\file.ts").as_string(),
        "lib/file.ts"
    );
    assert_eq!(
        relative_path_from_normalized("../lib/file.ts").as_string(),
        "../lib/file.ts"
    );
    assert_eq!(relative_path_from_normalized("").as_string(), "");
    assert_panics(|| {
        relative_path_from_normalized("./lib/file.ts");
    });
    assert_panics(|| {
        to_relative_path("/lib/file.ts");
    });

    assert_eq!(
        relative_path_from_normalized("lib/file.ts")
            .as_module_specifier()
            .as_string(),
        "./lib/file.ts"
    );
    assert_eq!(
        relative_path_from_normalized("../lib/file.ts")
            .as_module_specifier()
            .as_string(),
        "../lib/file.ts"
    );
    assert_eq!(
        rooted_file_path_from_normalized("/project/lib/file.ts").as_module_specifier(),
        ModuleSpecifier::from("/project/lib/file.ts")
    );
    assert!(to_module_specifier("./lib/file.ts").is_relative());
    assert!(!to_module_specifier("lib").is_relative());
    assert!(to_module_specifier("/project/lib").is_absolute());
    assert!(!to_module_specifier("lib").is_absolute());
    assert_eq!(
        to_module_specifier("pkg").resolve(&["./dist", "file.js"]),
        ModuleSpecifier::from("pkg/dist/file.js")
    );
    assert_eq!(
        to_module_specifier("pkg").resolve_relative(&relative_path_from_normalized("lib/file.js")),
        ModuleSpecifier::from("pkg/lib/file.js")
    );
    assert_eq!(
        to_module_specifier("pkg").combine_relative(&relative_path_from_normalized("lib/file.js")),
        ModuleSpecifier::from("pkg/lib/file.js")
    );
    assert_eq!(
        to_module_specifier("pkg/lib/file.d.ts").remove_file_extension(),
        ModuleSpecifier::from("pkg/lib/file")
    );
    assert!(relative_path_from_normalized("../lib/file.ts").is_parent_relative());
    assert!(!relative_path_from_normalized("..file.ts").is_parent_relative());
    assert!(relative_path_from_normalized("lib/").has_trailing_directory_separator());
    assert_eq!(
        relative_path_from_normalized("lib").with_trailing_directory_separator(),
        RelativePath::from("lib/")
    );
    assert_eq!(
        rooted_directory_path_from_normalized("/project/dist")
            .resolve_relative_file(&relative_path_from_normalized("../src/file.ts")),
        rooted_file_path_from_normalized("/project/src/file.ts")
    );
}

#[test]
fn test_typed_path_components() {
    let file_name = rooted_file_path_from_normalized("/project/node_modules/pkg/index.ts");
    assert!(file_name.contains_lowercase_directory_sequence("/node_modules/"));
    assert!(
        !rooted_file_path_from_normalized("/project/node_modules")
            .contains_lowercase_directory_sequence("/node_modules/")
    );
    assert!(
        !rooted_file_path_from_normalized("/project/not_node_modules/pkg/index.ts")
            .contains_lowercase_directory_sequence("/node_modules/")
    );

    let path = path_key_from_canonical("/project/node_modules/@types/node/index.d.ts");
    assert!(path.contains_lowercase_directory_sequence("/node_modules/@types/node/"));
    assert!(
        !path_key_from_canonical("/project/node_modules/@types/node")
            .contains_lowercase_directory_sequence("/node_modules/@types/node/")
    );
}

#[test]
fn test_try_relative_path_between_file_paths() {
    let from = rooted_directory_path_from_normalized("/project/src");
    let to = rooted_file_path_from_normalized("/project/lib/file.ts");
    let relative = CaseSensitivity::CaseSensitive
        .relative_path_from_directory(&from, &to)
        .unwrap();
    assert_eq!(relative.as_string(), "../lib/file.ts");

    assert!(
        CaseSensitivity::CaseSensitive
            .relative_path_from_directory(
                &rooted_directory_path_from_normalized("c:/project/src"),
                &rooted_file_path_from_normalized("d:/project/lib/file.ts"),
            )
            .is_none()
    );
}

#[test]
fn test_rooted_file_path_directory() {
    assert_eq!(
        rooted_file_path_from_normalized("/project/src/a.ts")
            .directory()
            .as_string(),
        "/project/src"
    );
    assert_eq!(
        rooted_file_path_from_normalized("/")
            .directory()
            .as_string(),
        "/"
    );
    assert_eq!(
        rooted_file_path_from_normalized("c:/project/src/a.ts")
            .directory()
            .as_string(),
        "c:/project/src"
    );
    assert_eq!(
        rooted_file_path_from_normalized("file:///project/src/a.ts")
            .directory()
            .as_string(),
        "file:///project/src"
    );
}

#[test]
fn test_rooted_file_path_without_root() {
    assert_eq!(
        rooted_file_path_from_normalized("/project/src/a.ts").without_root(),
        "project/src/a.ts"
    );
    assert_eq!(
        rooted_file_path_from_normalized("c:/project/src/a.ts").without_root(),
        "project/src/a.ts"
    );
    assert_eq!(
        rooted_file_path_from_normalized("file:///project/src/a.ts").without_root(),
        "project/src/a.ts"
    );
}

#[test]
fn test_rooted_file_path_root_and_relative_path() {
    let file = rooted_file_path_from_normalized("file:///project/src/a.ts");
    let (root, relative) = file.root_and_relative_path();
    assert_eq!(root.as_string(), "file:///");
    assert_eq!(relative, "project/src/a.ts");
    assert_eq!(
        root.resolve_file_from_normalized_relative(relative),
        rooted_file_path_from_normalized("file:///project/src/a.ts")
    );
    assert_eq!(
        rooted_directory_path_from_normalized("/")
            .resolve_file_from_normalized_relative("C:/src/a.ts"),
        rooted_file_path_from_normalized("/C:/src/a.ts")
    );
    assert_panics(|| {
        root.resolve_file_from_normalized_relative("");
    });
    assert_panics(|| {
        root.resolve_file_from_normalized_relative("../a.ts");
    });
}

#[test]
fn test_common_directory_of_files() {
    let file_names = vec![
        rooted_file_path_from_normalized("/Project/src/a.ts"),
        rooted_file_path_from_normalized("/project/src/nested/b.ts"),
        rooted_file_path_from_normalized("/project/test/c.ts"),
    ];
    assert_eq!(
        CaseSensitivity::CaseInsensitive.common_directory_of_files(&file_names),
        rooted_directory_path_from_normalized("/Project")
    );
    assert_eq!(
        CaseSensitivity::CaseSensitive.common_directory_of_files(&file_names),
        rooted_directory_path_from_normalized("/")
    );
    assert_eq!(
        CaseSensitivity::CaseInsensitive.common_directory_of_files(&[
            rooted_file_path_from_normalized("/repo/\u{0130}project/a.ts"),
            rooted_file_path_from_normalized("/repo/iproject/b.ts"),
        ]),
        rooted_directory_path_from_normalized("/repo")
    );
}

#[test]
fn test_relative_paths_from_typed_paths() {
    let from_directory = rooted_directory_path_from_normalized("/project/src");
    let from_file = rooted_file_path_from_normalized("/project/src/index.ts");
    let to_file = rooted_file_path_from_normalized("/project/lib/util.ts");

    let relative = CaseSensitivity::CaseSensitive
        .relative_path_from_directory(&from_directory, &to_file)
        .unwrap();
    assert_eq!(relative.as_string(), "../lib/util.ts");
    let relative = CaseSensitivity::CaseSensitive
        .relative_path_from_file(&from_file, &to_file)
        .unwrap();
    assert_eq!(relative.as_string(), "../lib/util.ts");
    let relative = CaseSensitivity::CaseInsensitive
        .relative_path_from_directory(
            &rooted_directory_path_from_normalized("/PROJECT/src"),
            &to_file,
        )
        .unwrap();
    assert_eq!(relative.as_string(), "../lib/util.ts");
    let relative = CaseSensitivity::CaseInsensitive
        .relative_file_path_from_directory(
            &rooted_directory_path_from_normalized("/repo/\u{212A}"),
            &rooted_file_path_from_normalized("/repo/k/a.ts"),
        )
        .unwrap();
    assert_eq!(relative.as_string(), "a.ts");
}

#[test]
fn test_contains_file_path() {
    struct TestCase {
        name: &'static str,
        case_sensitivity: CaseSensitivity,
        directory: &'static str,
        file_name: &'static str,
        relative: &'static str,
        contained: bool,
    }
    let tests = [
        TestCase {
            name: "same path",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            directory: "/project/src",
            file_name: "/project/src",
            relative: "",
            contained: true,
        },
        TestCase {
            name: "child",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            directory: "/project/src",
            file_name: "/project/src/a.ts",
            relative: "a.ts",
            contained: true,
        },
        TestCase {
            name: "prefix sibling",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            directory: "/project/src",
            file_name: "/project/source/a.ts",
            relative: "",
            contained: false,
        },
        TestCase {
            name: "root",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            directory: "/",
            file_name: "/project/src/a.ts",
            relative: "project/src/a.ts",
            contained: true,
        },
        TestCase {
            name: "case sensitive mismatch",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            directory: "/PROJECT",
            file_name: "/project/a.ts",
            relative: "",
            contained: false,
        },
        TestCase {
            name: "case insensitive",
            case_sensitivity: CaseSensitivity::CaseInsensitive,
            directory: "/PROJECT",
            file_name: "/project/a.ts",
            relative: "a.ts",
            contained: true,
        },
        TestCase {
            name: "case folded rune",
            case_sensitivity: CaseSensitivity::CaseInsensitive,
            directory: "/repo/\u{212A}",
            file_name: "/repo/k/a.ts",
            relative: "a.ts",
            contained: true,
        },
        TestCase {
            name: "drive root casing",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            directory: "C:/project",
            file_name: "c:/project/a.ts",
            relative: "a.ts",
            contained: true,
        },
        TestCase {
            name: "file URL scheme and drive casing",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            directory: "FILE:///C:/project",
            file_name: "file:///c:/project/a.ts",
            relative: "a.ts",
            contained: true,
        },
        TestCase {
            name: "file URL localhost and drive casing",
            case_sensitivity: CaseSensitivity::CaseSensitive,
            directory: "file://LOCALHOST/C:/project",
            file_name: "file://localhost/c:/project/a.ts",
            relative: "a.ts",
            contained: true,
        },
        TestCase {
            name: "different root",
            case_sensitivity: CaseSensitivity::CaseInsensitive,
            directory: "c:/project",
            file_name: "d:/project/a.ts",
            relative: "",
            contained: false,
        },
    ];

    for test in &tests {
        let directory = rooted_directory_path_from_normalized(test.directory);
        let file_name = rooted_file_path_from_normalized(test.file_name);
        assert_eq!(
            test.case_sensitivity
                .contains_file_path(&directory, &file_name),
            test.contained,
            "{}",
            test.name
        );
        assert_eq!(
            test.case_sensitivity
                .contains_path(&directory, &file_name.as_path()),
            test.contained,
            "{}",
            test.name
        );
        assert_eq!(
            test.case_sensitivity
                .starts_with_directory(&file_name, &directory),
            test.contained && !test.relative.is_empty(),
            "{}",
            test.name
        );
        let relative = test
            .case_sensitivity
            .relative_file_path_from_directory(&directory, &file_name);
        assert_eq!(relative.is_some(), test.contained, "{}", test.name);
        if let Some(relative) = relative {
            assert_eq!(relative.as_string(), test.relative, "{}", test.name);
        }
    }

    let parent_key = CaseSensitivity::CaseSensitive
        .path_key(&rooted_directory_path_from_normalized("C:/project").as_path());
    let child_key = CaseSensitivity::CaseSensitive
        .path_key(&rooted_file_path_from_normalized("c:/project/a.ts").as_path());
    assert!(parent_key.contains_path(&child_key));

    let relative = rooted_file_path_from_normalized("c:/project/a.ts")
        .relative_to(&rooted_directory_path_from_normalized("C:/project"))
        .unwrap();
    assert_eq!(relative, RelativePath::from("a.ts"));
}

#[test]
fn test_source_map_location() {
    let relative = to_source_map_location("maps\\generated");
    assert_eq!(relative.as_string(), "maps/generated");
    assert!(relative.is_relative());
    assert_eq!(
        relative
            .resolve_directory(
                &rooted_directory_path_from_normalized("/project/src"),
                &rooted_directory_path_from_normalized("/project")
            )
            .as_string(),
        "/project/src/maps/generated"
    );

    let rooted = to_source_map_location("/maps\\generated");
    assert!(!rooted.is_relative());
    assert_eq!(
        rooted
            .resolve_directory(
                &rooted_directory_path_from_normalized("/project/src"),
                &rooted_directory_path_from_normalized("/project")
            )
            .as_string(),
        "/maps/generated"
    );

    let decoded: crate::SourceMapLocation = serde_json::from_str("\"maps\\\\generated\"").unwrap();
    assert_eq!(decoded.as_string(), "maps/generated");
    let encoded = serde_json::to_string(&decoded).unwrap();
    assert_eq!(encoded, "\"maps/generated\"");
}

#[test]
fn test_rooted_path() {
    let path = to_rooted_path(
        "src\\config.json",
        &rooted_directory_path_from_normalized("/project"),
    );
    assert_eq!(path.as_string(), "/project/src/config.json");
    assert_eq!(
        rooted_file_path_from_path(path.clone()),
        rooted_file_path_from_normalized("/project/src/config.json")
    );
    assert_eq!(
        rooted_directory_path_from_path(path),
        rooted_directory_path_from_normalized("/project/src/config.json")
    );
    assert_eq!(
        RootedPath::from(rooted_directory_path_from_normalized("/project/src")),
        rooted_path_from_normalized("/project/src")
    );
}

#[test]
fn test_rooted_path_compare() {
    assert_eq!(
        rooted_path_from_normalized("/a").compare(&rooted_path_from_normalized("/b")),
        -1
    );
    assert_eq!(
        rooted_file_path_from_normalized("/a").compare(&rooted_file_path_from_normalized("/a")),
        0
    );
    assert_eq!(
        rooted_directory_path_from_normalized("/b")
            .compare(&rooted_directory_path_from_normalized("/a")),
        1
    );
}

#[test]
fn test_path_operations_separate_rooting() {
    assert_eq!(
        crate::compare_paths(
            "src/a.ts",
            "/project/src/a.ts",
            CaseSensitivity::CaseSensitive
        ),
        -1
    );
    assert_eq!(
        crate::compare_paths_relative_to(
            "src/a.ts",
            "/project/src/a.ts",
            &RootedDirectoryPath::from("/project"),
            CaseSensitivity::CaseSensitive
        ),
        0
    );
    assert!(crate::contains_path(
        "src",
        "src/a.ts",
        CaseSensitivity::CaseSensitive
    ));
    assert!(!crate::contains_path(
        "/project/src",
        "src/a.ts",
        CaseSensitivity::CaseSensitive
    ));
    assert_eq!(
        crate::get_relative_path_from_directory("src", "lib/a.ts", CaseSensitivity::CaseSensitive),
        "../lib/a.ts"
    );
    assert_eq!(
        crate::resolve_relative_path_from_directory(
            "src",
            "lib/a.ts",
            &RootedDirectoryPath::from("/project"),
            CaseSensitivity::CaseSensitive
        ),
        "../lib/a.ts"
    );
}

#[test]
fn test_rooted_file_path_extension_operations_preserve_invariants() {
    let file_name = rooted_file_path_from_normalized("/project/src/file.ts");
    assert_eq!(
        file_name.remove_file_extension(),
        FileNameStem::from("/project/src/file")
    );
    assert_eq!(
        file_name.change_extension(".js"),
        rooted_file_path_from_normalized("/project/src/file.js")
    );
    assert_eq!(
        rooted_file_path_from_normalized("/project/src/file.d.ts").change_full_extension(""),
        rooted_file_path_from_normalized("/project/src/file")
    );
    assert_panics(|| {
        file_name.change_extension("../other");
    });
    assert_panics(|| {
        file_name.change_full_extension("\\nested");
    });
    assert_panics(|| {
        file_name.remove_extension(".js");
    });
}

#[test]
fn test_for_each_ancestor_directory_path() {
    let mut ancestors: Vec<RootedDirectoryPath> = Vec::new();
    rooted_directory_path_from_normalized("/project/src/lib").for_each_ancestor_directory(
        |directory| {
            ancestors.push(directory.clone());
            ((), false)
        },
    );
    assert_eq!(
        ancestors,
        vec![
            rooted_directory_path_from_normalized("/project/src/lib"),
            rooted_directory_path_from_normalized("/project/src"),
            rooted_directory_path_from_normalized("/project"),
            rooted_directory_path_from_normalized("/"),
        ]
    );
}

#[test]
fn test_rooted_file_path_components() {
    let file_name =
        rooted_file_path_from_normalized("/store/node_modules/pkg/node_modules/dep/index.d.ts");
    assert_eq!(
        file_name.directory_before(23),
        rooted_directory_path_from_normalized("/store/node_modules/pkg")
    );
    assert_eq!(
        file_name.suffix_after_separator(23),
        "node_modules/dep/index.d.ts"
    );
    let relative = file_name
        .relative_to(&rooted_directory_path_from_normalized(
            "/store/node_modules/pkg",
        ))
        .unwrap();
    assert_eq!(relative.as_string(), "node_modules/dep/index.d.ts");
    assert!(
        file_name
            .relative_to(&rooted_directory_path_from_normalized("/other"))
            .is_none()
    );

    let (before, through) = file_name.split_at_component("node_modules").unwrap();
    assert_eq!(before, rooted_directory_path_from_normalized("/store"));
    assert_eq!(
        through,
        rooted_directory_path_from_normalized("/store/node_modules")
    );

    let (before, through) = file_name.split_at_last_component("node_modules").unwrap();
    assert_eq!(
        before,
        rooted_directory_path_from_normalized("/store/node_modules/pkg")
    );
    assert_eq!(
        through,
        rooted_directory_path_from_normalized("/store/node_modules/pkg/node_modules")
    );
    assert_panics(|| {
        file_name.directory_before(22);
    });
    assert_panics(|| {
        file_name.suffix_after_separator(22);
    });
}

#[test]
fn test_case_sensitivity_key() {
    let file_name = rooted_file_path_from_normalized("/Project/SRC/a.ts");
    let case_sensitive = CaseSensitivity::CaseSensitive;
    let case_insensitive = CaseSensitivity::CaseInsensitive;
    assert_eq!(
        case_sensitive.path_key(&file_name.as_path()).as_string(),
        "/Project/SRC/a.ts"
    );
    assert_eq!(
        case_insensitive.path_key(&file_name.as_path()).as_string(),
        "/project/src/a.ts"
    );
    assert_eq!(
        case_sensitive.compare_file_paths(
            &file_name,
            &rooted_file_path_from_normalized("/Project/SRC/b.ts")
        ),
        -1
    );
    assert_eq!(
        case_insensitive.compare_file_paths(
            &file_name,
            &rooted_file_path_from_normalized("/project/src/A.ts")
        ),
        0
    );
    assert_eq!(file_name.directory_separator_count(), 3);
}

#[test]
fn test_path_key_construction_methods() {
    let path = PathKey::from("/project/src");
    assert_eq!(
        path.append_canonical_component("node_modules").as_string(),
        "/project/src/node_modules"
    );
    assert_eq!(
        path.append_canonical_suffix(".0.ts").as_string(),
        "/project/src.0.ts"
    );
    assert_eq!(path.append_canonical_suffix(".ts").extension(), ".ts");
    let (before, through) = PathKey::from("/project/node_modules/pkg/index.d.ts")
        .split_at_canonical_component("node_modules")
        .unwrap();
    assert_eq!(before, PathKey::from("/project"));
    assert_eq!(through, PathKey::from("/project/node_modules"));
    assert!(
        PathKey::from("/project/not_node_modules/pkg")
            .split_at_canonical_component("node_modules")
            .is_none()
    );
    assert_panics(|| {
        path.append_canonical_component("../src");
    });
    assert_panics(|| {
        path.append_canonical_suffix("/src");
    });
    assert_panics(|| {
        PathKey::from("").append_canonical_component("src");
    });
    assert_panics(|| {
        PathKey::from("").append_canonical_suffix(".ts");
    });
    assert_panics(|| {
        path.split_at_canonical_component("../node_modules");
    });
    assert_panics(|| {
        RootedFilePath::from("").append_suffix(".ts");
    });
    assert_panics(|| {
        RootedDirectoryPath::from("").resolve_file("file.ts");
    });
    assert_eq!(
        rooted_directory_path_from_normalized("/project/src")
            .resolve_directory("types")
            .as_string(),
        "/project/src/types"
    );
    assert_eq!(
        rooted_directory_path_from_normalized("/project/src")
            .resolve_directory("types/")
            .as_string(),
        "/project/src/types"
    );
    assert_eq!(
        rooted_directory_path_from_normalized("/project/src")
            .resolve_directory("")
            .as_string(),
        "/project/src"
    );
    assert_eq!(
        rooted_directory_path_from_normalized("/project/src")
            .resolve_file("file.ts/")
            .as_string(),
        "/project/src/file.ts"
    );
    assert_eq!(
        rooted_directory_path_from_normalized("/project/src")
            .resolve_file("")
            .as_string(),
        "/project/src"
    );
    assert_panics(|| {
        RootedDirectoryPath::from("").resolve_directory("types");
    });
}

#[test]
fn test_rooted_directory_path_resolution_matches_general_rooting() {
    let base = rooted_directory_path_from_normalized("/project/src");
    for path in [
        "file.ts",
        "nested/file.ts",
        "./file.ts",
        "../file.ts",
        "nested\\file.ts",
        "nested/file.ts/",
        "/absolute/file.ts",
        "c:/absolute/file.ts",
        "file:///absolute/file.ts",
    ] {
        assert_eq!(
            base.resolve_file(path),
            to_rooted_file_path(path, &base),
            "{path}"
        );
        assert_eq!(
            base.resolve_directory(path),
            to_rooted_directory_path(path, &base),
            "{path}"
        );
    }
}
