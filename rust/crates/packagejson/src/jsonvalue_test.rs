// Ported from tsc/internal/packagejson/jsonvalue_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_json as json;

use crate::{JSONValue, JSONValueData, JSONValueType};

/// `func TestJSONValue(t *testing.T)`
///
/// PORT: the Go test wraps `testJSONValue` in `t.Run("UnmarshalJSONV2")` to
/// mark it as covering the v2 unmarshaler; the subtest wrapper is dropped.
#[test]
fn test_json_value() {
    /// `type packageJson struct`
    ///
    /// PORT: serde derive + `serde(default)` — see `expected_test.rs`.
    #[derive(serde::Deserialize, Default)]
    #[serde(default)]
    struct PackageJson {
        private: JSONValue,
        #[serde(rename = "false")]
        false_: JSONValue,
        name: JSONValue,
        version: JSONValue,
        exports: JSONValue,
        imports: JSONValue,
        #[serde(rename = "notPresent")]
        not_present: JSONValue,
    }

    let json_string = r#"{
		"private": true,
		"false": false,
		"name": "test",
		"version": 2,
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
	}"#;

    let p: PackageJson = json::unmarshal(json_string.as_bytes(), &[]).unwrap();

    assert_eq!(p.private.type_, JSONValueType::Boolean);
    // Go `p.Private.Value` is `any` holding `bool(true)`.
    assert_eq!(p.private.value, JSONValueData::Boolean(true));

    assert_eq!(p.false_.type_, JSONValueType::Boolean);
    assert_eq!(p.false_.value, JSONValueData::Boolean(false));

    assert_eq!(p.name.type_, JSONValueType::String);
    assert_eq!(p.name.value, JSONValueData::String("test".to_string()));

    assert_eq!(p.version.type_, JSONValueType::Number);
    assert_eq!(p.version.value, JSONValueData::Number(2.0));

    assert_eq!(p.exports.type_, JSONValueType::Object);
    assert_eq!(p.exports.as_object().size(), 3);
    assert_eq!(
        p.exports.as_object().get_or_zero("./test").as_array()[2].type_,
        JSONValueType::Null
    );
    assert_eq!(
        p.exports.as_object().get_or_zero("./test").as_array()[2].value,
        JSONValueData::Null
    );
    assert_eq!(
        p.exports.as_object().get_or_zero(".").type_,
        JSONValueType::Object
    );
    assert_eq!(p.exports.as_object().get_or_zero(".").as_object().size(), 2);
    assert_eq!(
        p.exports
            .as_object()
            .get_or_zero(".")
            .as_object()
            .get_or_zero("node")
            .type_,
        JSONValueType::String
    );
    assert_eq!(
        p.exports
            .as_object()
            .get_or_zero(".")
            .as_object()
            .get_or_zero("node")
            .value,
        JSONValueData::String("import".to_string())
    );
    assert_eq!(
        p.exports.as_object().get_or_zero("./test").type_,
        JSONValueType::Array
    );
    assert_eq!(
        p.exports.as_object().get_or_zero("./test").as_array().len(),
        3
    );
    assert_eq!(
        p.exports.as_object().get_or_zero("./features/*").type_,
        JSONValueType::Object
    );
    assert_eq!(
        p.exports
            .as_object()
            .get_or_zero("./features/*")
            .as_object()
            .size(),
        2
    );
    assert_eq!(
        p.exports
            .as_object()
            .get_or_zero("./features/*")
            .as_object()
            .get_or_zero("browser")
            .type_,
        JSONValueType::String
    );
    assert_eq!(
        p.exports
            .as_object()
            .get_or_zero("./features/*")
            .as_object()
            .get_or_zero("browser")
            .value,
        JSONValueData::String("browser-import".to_string())
    );

    assert_eq!(p.imports.type_, JSONValueType::NotPresent);
    assert_eq!(p.imports.value, JSONValueData::Null);

    assert_eq!(p.not_present.type_, JSONValueType::NotPresent);
    assert_eq!(p.not_present.value, JSONValueData::Null);
}
