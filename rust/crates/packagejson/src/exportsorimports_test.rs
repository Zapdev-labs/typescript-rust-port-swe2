// Ported from tsc/internal/packagejson/exportsorimports_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_json as json;

use crate::{ExportsOrImports, JSONValueType};

/// `func TestExportsOrImports(t *testing.T)`
#[test]
fn test_exports_or_imports() {
    /// `type Exports struct`
    ///
    /// PORT: serde derive + `serde(default)` — see `expected_test.rs`.
    #[derive(serde::Deserialize, Default)]
    #[serde(default)]
    struct Exports {
        imports: ExportsOrImports,
        exports: ExportsOrImports,
    }

    // PORT: `r##` — the fixture contains the member name `"#dep"`.
    let json_string = r##"{
		"imports": {
			"#dep": {
				"node": "import",
				"browser": "browser-import"
			}
		},
		"exports": {
			".": {
				"node": "import",
				"browser": "browser-import"
			},
			"./features/*": {
				"node": "import",
				"browser": "browser-import"
			},
			"./test": ["test1", "test2", null]
		}
	}"##;

    let e: Exports = json::unmarshal(json_string.as_bytes(), &[]).unwrap();

    assert!(e.imports.is_imports());
    assert!(e.exports.is_subpaths());

    assert_eq!(e.imports.as_object().size(), 1);
    assert!(e.imports.as_object().get_or_zero("#dep").is_conditions());
    assert_eq!(
        e.imports.as_object().get_or_zero("#dep").as_object().size(),
        2
    );
    assert_eq!(
        e.imports
            .as_object()
            .get_or_zero("#dep")
            .as_object()
            .get_or_zero("node")
            .type_,
        JSONValueType::String
    );
    assert_eq!(
        e.imports
            .as_object()
            .get_or_zero("#dep")
            .as_object()
            .get_or_zero("browser")
            .type_,
        JSONValueType::String
    );
    assert_eq!(
        e.imports
            .as_object()
            .get_or_zero("#dep")
            .as_object()
            .get_or_zero("import")
            .type_,
        JSONValueType::NotPresent
    );

    assert_eq!(e.exports.as_object().size(), 3);
    assert!(e.exports.as_object().get_or_zero(".").is_conditions());
    assert_eq!(
        e.exports
            .as_object()
            .get_or_zero(".")
            .as_object()
            .get_or_zero("import")
            .type_,
        JSONValueType::NotPresent
    );
    assert_eq!(
        e.exports.as_object().get_or_zero("./test").as_array()[2].type_,
        JSONValueType::Null
    );
    assert_eq!(
        e.exports
            .as_object()
            .get_or_zero("./features/*")
            .as_object()
            .size(),
        2
    );
}
