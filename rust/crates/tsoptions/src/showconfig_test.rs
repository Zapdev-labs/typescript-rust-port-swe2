// Ported from tsc/internal/tsoptions/showconfig_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;

use crate::generated::{declarations, options};
use crate::value::Value;
use tsc_collections::OrderedMap;
use tsc_core::options_generated::{CompilerOptions, ModuleKind, PluginImport, ScriptTarget};
use tsc_core::tristate::TS_TRUE;
use tsc_tspath::{CaseSensitivity, RootedDirectoryPath, RootedFilePath};

/// `TestShowConfigSerialization` — reduced port. The Go test cross-checks the
/// generated serializer against a reflection-based independent serializer;
/// the serialization coverage (key set) is verified against the Go baseline
/// separately, so this checks representative values by hand.
#[test]
fn test_show_config_serialization() {
    let config_file_path = RootedFilePath::from("/project/tsconfig.json");
    let case_sensitivity = CaseSensitivity::CaseSensitive;

    // Empty options serialize to an empty map.
    let got = options::serialize_compiler_options(
        &CompilerOptions::default(),
        config_file_path.clone(),
        case_sensitivity,
    );
    assert_eq!(got.size(), 0);

    // Tristate, enum, list, and path-valued fields.
    let mut paths = OrderedMap::new();
    paths.set(
        "@/*".to_string(),
        Some(vec!["./src/*".to_string(), "../shared/*".to_string()]),
    );
    paths.set("empty".to_string(), Some(vec![]));
    let all_options = CompilerOptions {
        strict: TS_TRUE,
        target: ScriptTarget::ES2015,
        module: ModuleKind::ES2015,
        out_dir: RootedDirectoryPath::from("/project/dist"),
        root_dirs: Some(vec![RootedDirectoryPath::from("/project/src")]),
        paths: Some(paths),
        plugins: Some(vec![PluginImport {
            name: "plugin".into(),
        }]),
        max_node_module_js_depth: Some(0),
        lib: Some(vec!["lib.es2015.d.ts".to_string()]),
        custom_conditions: Some(vec!["cond".to_string()]),
        ..Default::default()
    };
    let got = options::serialize_compiler_options(
        &all_options,
        config_file_path.clone(),
        case_sensitivity,
    );
    // `Value` mirrors Go comparability (slices are not `==`), so compare
    // serialized JSON values.
    let got_json = |key: &str| got.get(key).map(|v| serde_json::to_value(v).unwrap());
    assert_eq!(got_json("strict"), Some(serde_json::json!(true)));
    assert_eq!(got_json("target"), Some(serde_json::json!("es6")));
    // "es6" is the first alias in the module enum map for ES2015.
    assert_eq!(got_json("module"), Some(serde_json::json!("es6")));
    // Rooted paths serialize relative to the config file directory.
    assert_eq!(got_json("outDir"), Some(serde_json::json!("./dist")));
    assert_eq!(got_json("rootDirs"), Some(serde_json::json!(["./src"])));
    let serialized_paths = got.get("paths").expect("paths");
    let Value::StringListMap(serialized_paths) = serialized_paths else {
        panic!("paths should serialize as a StringListMap")
    };
    let keys: Vec<&str> = serialized_paths.keys().map(String::as_str).collect();
    assert_eq!(keys, ["@/*", "empty"]);
    assert_eq!(got_json("maxNodeModuleJsDepth"), Some(serde_json::json!(0)));
    // `lib` elements serialize through the lib enum map.
    assert_eq!(got_json("lib"), Some(serde_json::json!(["es6"])));
    // `plugins` and `customConditions` serialize verbatim.
    assert!(got.get("plugins").is_some());
    assert_eq!(
        got_json("customConditions"),
        Some(serde_json::json!(["cond"]))
    );
    // Command-line-only options are not serialized.
    for absent in ["listFiles", "listEmittedFiles", "watch", "build", "init"] {
        assert!(!got.has(absent), "{absent} should not be serialized");
    }
}

/// `TestShowConfigEnumSerialization` — every enum-map value serializes to its
/// first alias.
#[test]
fn test_show_config_enum_serialization() {
    let mut failures = Vec::new();
    for option in declarations::options_declarations() {
        let Some(enum_map) = option.enum_map() else {
            continue;
        };
        let mut seen: HashMap<i64, String> = HashMap::new();
        for (name, value) in enum_map.entries() {
            let Value::Int(v) = value else {
                continue;
            };
            let want = seen.entry(*v).or_insert_with(|| name.clone()).clone();
            let got = options::serialize_compiler_option_enum(enum_map, *v);
            if got != want {
                failures.push(format!(
                    "{}: {v}: got {got:?}, want first alias {want:?}",
                    option.name
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
