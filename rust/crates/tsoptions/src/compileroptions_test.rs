// Ported from tsc/internal/tsoptions/compileroptions_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use crate::generated::options;
use crate::parsinghelpers::parse_compiler_options;
use crate::tsconfigparsing::ParsedCompilerOptions;
use crate::tsconfigparsing::UnresolvedCompilerOptionPaths;
use crate::value::Value;
use std::panic::{AssertUnwindSafe, catch_unwind};
use tsc_collections::OrderedMap;
use tsc_core::options_generated::{
    CompilerOptions, JsxEmit, ModuleDetectionKind, ModuleResolutionKind, PluginImport,
};
use tsc_core::tristate::{TS_TRUE, TS_UNKNOWN};
use tsc_tspath::RootedDirectoryPath;

/// `TestOptionEnumStrings` — valid variants produce the Go `String()` output;
/// zero values panic. (The "unhandled case" panics for out-of-range
/// discriminants cannot be constructed for real Rust enums.)
#[test]
fn test_option_enum_strings() {
    let cases: [(String, &str); 10] = [
        (ModuleResolutionKind::Classic.to_string(), "Classic"),
        (ModuleResolutionKind::Node10.to_string(), "Node10"),
        (ModuleResolutionKind::Node16.to_string(), "Node16"),
        (ModuleResolutionKind::NodeNext.to_string(), "NodeNext"),
        (ModuleResolutionKind::Bundler.to_string(), "Bundler"),
        (JsxEmit::Preserve.to_string(), "preserve"),
        (JsxEmit::ReactNative.to_string(), "react-native"),
        (JsxEmit::React.to_string(), "react"),
        (JsxEmit::ReactJSX.to_string(), "react-jsx"),
        (JsxEmit::ReactJSXDev.to_string(), "react-jsxdev"),
    ];
    for (got, want) in cases {
        assert_eq!(got, want);
    }

    let panics = catch_unwind(AssertUnwindSafe(|| {
        ModuleResolutionKind::Unknown.to_string()
    }));
    assert!(panics.is_err());
    let panics = catch_unwind(AssertUnwindSafe(|| JsxEmit::None.to_string()));
    assert!(panics.is_err());
}

/// `TestGeneratedCompilerOptionParsingAndClone` — reduced port: the Go test
/// iterates fields reflectively; this exercises one representative field per
/// generated parse shape and the `Clone` shallow-copy guarantee.
#[test]
fn test_generated_compiler_option_parsing_and_clone() {
    // Tristate.
    let mut options = CompilerOptions::default();
    parse_compiler_options("strict", &Value::Bool(true), &mut options);
    assert_eq!(options.strict, TS_TRUE);
    let clone = options.clone();
    assert_eq!(clone.strict, options.strict);

    // String-valued path option.
    let mut options = CompilerOptions::default();
    parse_compiler_options("jsxFactory", &Value::Str("h".into()), &mut options);
    assert_eq!(options.jsx_factory, "h");

    // `*int`.
    let mut options = CompilerOptions::default();
    parse_compiler_options("maxNodeModuleJsDepth", &Value::Float(2.0), &mut options);
    assert_eq!(options.max_node_module_js_depth, Some(2));

    // `[]string`.
    let mut options = CompilerOptions::default();
    parse_compiler_options(
        "customConditions",
        &Value::List(vec![
            Value::Str("/first".into()),
            Value::Str("/second".into()),
        ]),
        &mut options,
    );
    assert_eq!(
        options
            .custom_conditions
            .as_deref()
            .map(|v| v.iter().map(String::as_str).collect::<Vec<_>>()),
        Some(vec!["/first", "/second"])
    );

    // `[]core.PluginImport` — elements are `*OrderedMap` values.
    let mut plugin = OrderedMap::new();
    plugin.set("name".to_string(), Value::Str("plugin".into()));
    let mut options = CompilerOptions::default();
    parse_compiler_options(
        "plugins",
        &Value::List(vec![Value::Map(plugin)]),
        &mut options,
    );
    assert_eq!(
        options.plugins.as_deref(),
        Some(
            [PluginImport {
                name: "plugin".into()
            }]
            .as_slice()
        )
    );

    // `*OrderedMap[string, []string]` (paths).
    let mut paths = OrderedMap::new();
    paths.set(
        "@/*".to_string(),
        Value::List(vec![Value::Str("src/*".into())]),
    );
    let mut options = CompilerOptions::default();
    parse_compiler_options("paths", &Value::Map(paths), &mut options);
    let paths = options.paths.as_ref().expect("paths");
    assert_eq!(
        paths
            .get("@/*")
            .and_then(|v| v.as_deref())
            .map(|v| v.iter().map(String::as_str).collect::<Vec<_>>()),
        Some(vec!["src/*"])
    );

    // Typed enum via enum-map value, then the same via a JSON number.
    let mut options = CompilerOptions::default();
    parse_compiler_options("moduleDetection", &Value::Int(3), &mut options);
    assert_eq!(options.module_detection, ModuleDetectionKind::Force);
    let mut numeric = CompilerOptions::default();
    parse_compiler_options("moduleDetection", &Value::Float(1.0), &mut numeric);
    assert_eq!(numeric.module_detection, ModuleDetectionKind::Auto);

    // Clone preserves zero values.
    assert!(CompilerOptions::equals(
        Some(&CompilerOptions::default()),
        Some(&CompilerOptions::default().clone())
    ));
}

/// `TestGeneratedCompilerOptionParserCompatibility`.
#[test]
fn test_generated_compiler_option_parser_compatibility() {
    let mut options = CompilerOptions::default();
    parse_compiler_options("STRICT", &Value::Bool(true), &mut options);
    parse_compiler_options(
        "moduleDetectionKind",
        &Value::Int(ModuleDetectionKind::Force as i64),
        &mut options,
    );
    parse_compiler_options(
        "lib",
        &Value::StringList(vec!["lib.es2025.d.ts".into()]),
        &mut options,
    );
    parse_compiler_options("strict", &Value::Null, &mut options);
    assert_eq!(options.strict, TS_TRUE);
    assert_eq!(options.module_detection, ModuleDetectionKind::Force);
    assert_eq!(
        options
            .lib
            .as_deref()
            .map(|v| v.iter().map(String::as_str).collect::<Vec<_>>()),
        Some(vec!["lib.es2025.d.ts"])
    );
    let before = options.clone();
    parse_compiler_options("unknownOption", &Value::Bool(true), &mut options);
    assert!(
        CompilerOptions::equals(Some(&options), Some(&before)),
        "Unknown options must not change parsed options"
    );
}

/// `TestCompilerOptionsEquality` — reduced port: Go iterates fields
/// reflectively; this covers the nil/empty matrix, representative fields, and
/// the full `Paths` ordered-map matrix (including key order and nil vs empty).
#[test]
fn test_compiler_options_equality() {
    fn check(a: Option<&CompilerOptions>, b: Option<&CompilerOptions>, want: bool) {
        assert_eq!(CompilerOptions::equals(a, b), want, "for\n{a:?}\n{b:?}");
    }
    let options_deep_equal = |a: Option<&CompilerOptions>, b: Option<&CompilerOptions>| {
        // reflect.DeepEqual approximation: compare serialized contents
        // (serde output preserves OrderedMap ordering, so path key order is
        // covered). `equals` itself is the function under test.
        match (a, b) {
            (None, None) => true,
            (Some(a), Some(b)) => {
                // `paths` uses an order-sensitive entry comparison, matching
                // Go's reflect.DeepEqual over the OrderedMap's ordered slices.
                let paths_equal = match (&a.paths, &b.paths) {
                    (None, None) => true,
                    (Some(pa), Some(pb)) => pa
                        .entries()
                        .map(|(k, v)| (k.clone(), v.clone()))
                        .eq(pb.entries().map(|(k, v)| (k.clone(), v.clone()))),
                    _ => false,
                };
                let mut af = a.clone();
                let mut bf = b.clone();
                af.paths = None;
                bf.paths = None;
                paths_equal
                    && serde_json::to_value(af).unwrap() == serde_json::to_value(bf).unwrap()
            }
            _ => false,
        }
    };
    let check_auto = |a: Option<&CompilerOptions>, b: Option<&CompilerOptions>| {
        check(a, b, options_deep_equal(a, b));
    };

    check(None, None, true);
    check(None, Some(&CompilerOptions::default()), false);
    check(Some(&CompilerOptions::default()), None, false);
    check(
        Some(&CompilerOptions::default()),
        Some(&CompilerOptions::default()),
        true,
    );
    check_auto(
        Some(&CompilerOptions::default()),
        Some(&CompilerOptions {
            strict: TS_TRUE,
            ..Default::default()
        }),
    );

    // Representative field matrices.
    for a_value in [TS_UNKNOWN, TS_TRUE] {
        for b_value in [TS_UNKNOWN, TS_TRUE] {
            let a = CompilerOptions {
                strict: a_value,
                ..Default::default()
            };
            let b = CompilerOptions {
                strict: b_value,
                ..Default::default()
            };
            check_auto(Some(&a), Some(&b));
            check(Some(&a), Some(&a), true);
            check(Some(&a), Some(&a.clone()), true);
        }
    }
    for a_value in [
        None,
        Some(vec![]),
        Some(vec!["a".to_string(), "b".to_string()]),
        Some(vec!["b".to_string(), "a".to_string()]),
    ] {
        for b_value in [
            None,
            Some(vec![]),
            Some(vec!["a".to_string(), "b".to_string()]),
            Some(vec!["b".to_string(), "a".to_string()]),
        ] {
            let a = CompilerOptions {
                custom_conditions: a_value.clone(),
                ..Default::default()
            };
            let b = CompilerOptions {
                custom_conditions: b_value,
                ..Default::default()
            };
            check_auto(Some(&a), Some(&b));
        }
    }

    // The `paths` ordered-map matrix: nil vs empty, key order, nil vs empty
    // values, and cleared maps.
    let mut paths_variants: Vec<Option<OrderedMap<String, Option<Vec<String>>>>> = vec![
        None,
        Some(OrderedMap::new()),
        Some(OrderedMap::with_size_hint(0)),
    ];
    for values in [
        None,
        Some(vec![]),
        Some(vec!["a".to_string()]),
        Some(vec!["b".to_string()]),
        Some(vec!["a".to_string(), "b".to_string()]),
        Some(vec!["b".to_string(), "a".to_string()]),
    ] {
        for keys in [["x", "y"], ["y", "x"]] {
            let mut m = OrderedMap::new();
            for key in keys {
                m.set(key.to_string(), values.clone());
            }
            paths_variants.push(Some(m.clone()));
            paths_variants.push(Some(m));
        }
    }
    let mut cleared = paths_variants.last().unwrap().clone().unwrap_or_default();
    cleared.clear();
    paths_variants.push(Some(cleared));
    for a in &paths_variants {
        for b in &paths_variants {
            let a = CompilerOptions {
                paths: a.clone(),
                ..Default::default()
            };
            let b = CompilerOptions {
                paths: b.clone(),
                ..Default::default()
            };
            check_auto(Some(&a), Some(&b));
        }
    }
}

/// `TestCompilerOptionConfigDirSubstitution`.
#[test]
fn test_compiler_option_config_dir_substitution() {
    options::handle_option_config_dir_template_substitution(
        None,
        RootedDirectoryPath::from("/config"),
    );

    // (option name, accessor of the substituted string value)
    let tests: &[(&str, fn(&CompilerOptions) -> String)] = &[
        ("generateCpuProfile", |o| {
            o.generate_cpu_profile.as_string().to_string()
        }),
        ("generateTrace", |o| {
            o.generate_trace.as_string().to_string()
        }),
        ("outFile", |o| o.out_file.as_string().to_string()),
        ("outDir", |o| o.out_dir.as_string().to_string()),
        ("rootDir", |o| o.root_dir.as_string().to_string()),
        ("tsBuildInfoFile", |o| {
            o.ts_build_info_file.as_string().to_string()
        }),
        ("baseUrl", |o| o.base_url.as_string().to_string()),
        ("declarationDir", |o| {
            o.declaration_dir.as_string().to_string()
        }),
    ];
    for (option, field) in tests {
        let mut unresolved_paths = UnresolvedCompilerOptionPaths::new();
        unresolved_paths.insert(option.to_string(), Value::Str("${configDir}/output".into()));
        let mut options = ParsedCompilerOptions {
            compiler_options: Some(Box::new(CompilerOptions::default())),
            unresolved_paths,
        };
        options::handle_option_config_dir_template_substitution(
            Some(&mut options),
            RootedDirectoryPath::from("/config"),
        );
        let actual = field(options.compiler_options.as_deref().unwrap());
        assert_eq!(actual, "/config/output", "{option}");
    }
}

/// `TestCompilerOptionConfigDirSubstitutionCopyOnWrite`.
#[test]
fn test_compiler_option_config_dir_substitution_copy_on_write() {
    for (field_name, option_name) in [("RootDirs", "rootDirs"), ("TypeRoots", "typeRoots")] {
        let mut unresolved_paths = UnresolvedCompilerOptionPaths::new();
        unresolved_paths.insert(
            option_name.to_string(),
            Value::List(vec![
                Value::Str("${configDir}/types".into()),
                Value::Str("unchanged".into()),
            ]),
        );
        let mut options = ParsedCompilerOptions {
            compiler_options: Some(Box::new(CompilerOptions::default())),
            unresolved_paths,
        };
        options::handle_option_config_dir_template_substitution(
            Some(&mut options),
            RootedDirectoryPath::from("/config"),
        );
        let co = options.compiler_options.as_deref().unwrap();
        let values: Vec<String> = match field_name {
            "RootDirs" => co
                .root_dirs
                .as_deref()
                .unwrap_or_default()
                .iter()
                .map(|p| p.as_string().to_string())
                .collect(),
            _ => co
                .type_roots
                .as_deref()
                .unwrap_or_default()
                .iter()
                .map(|p| p.as_string().to_string())
                .collect(),
        };
        assert_eq!(
            values,
            ["/config/types", "/config/unchanged"],
            "{field_name}: want substituted paths"
        );
    }

    let mut original = OrderedMap::new();
    let unchanged = vec!["unchanged".to_string()];
    let changed = vec!["${configDir}/src".to_string(), "other".to_string()];
    original.set("unchanged".to_string(), Some(unchanged.clone()));
    original.set("changed".to_string(), Some(changed.clone()));
    let mut options = ParsedCompilerOptions {
        compiler_options: Some(Box::new(CompilerOptions {
            paths: Some(original.clone()),
            ..Default::default()
        })),
        unresolved_paths: UnresolvedCompilerOptionPaths::new(),
    };
    options::handle_option_config_dir_template_substitution(
        Some(&mut options),
        RootedDirectoryPath::from("/config"),
    );
    let co = options.compiler_options.as_deref().unwrap();
    let paths = co.paths.as_ref().expect("paths");
    assert_eq!(
        paths
            .get("changed")
            .and_then(|v| v.as_deref())
            .map(|v| v.iter().map(String::as_str).collect::<Vec<_>>()),
        Some(vec!["/config/src", "other"]),
        "Substitution must clone paths before changing them"
    );
    // The original map and unchanged slices are preserved.
    assert_eq!(
        original.get("changed").and_then(|v| v.as_deref()),
        Some(changed.as_slice())
    );
    assert_eq!(
        paths.get("unchanged").and_then(|v| v.as_deref()),
        Some(unchanged.as_slice())
    );
    let keys: Vec<&str> = paths.keys().map(String::as_str).collect();
    assert_eq!(keys, ["unchanged", "changed"]);
}
