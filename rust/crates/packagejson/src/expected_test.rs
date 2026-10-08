// Ported from tsc/internal/packagejson/expected_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_json as json;

use crate::Expected;

/// `func TestExpected(t *testing.T)`
#[test]
fn test_expected() {
    /// `type packageJson struct`
    ///
    /// PORT: serde's derive emits struct-field deserialization (no duplicate
    /// member names appear in this fixture, so the map visitor and a manual
    /// visitor decode identically here). `serde(default)` mirrors Go's
    /// unmarshaler leaving absent members as zero values.
    #[derive(serde::Deserialize, Default)]
    #[serde(default)]
    struct PackageJson {
        name: Expected<String>,
        version: Expected<String>,
        /// `Exports packagejson.Expected[any]` — `serde_json::Value` is the
        /// `any` stand-in (SPEC §5.9).
        exports: Expected<serde_json::Value>,
        main: Expected<String>,
    }

    let json_string = r#"{
		"name": "test",
		"version": 2,
		"exports": null
	}"#;

    let p: PackageJson = json::unmarshal(json_string.as_bytes(), &[]).unwrap();

    assert!(p.name.valid);
    assert_eq!(p.name.value, "test");
    assert!(!p.version.valid);
    assert_eq!(p.version.value, "");
    assert!(p.exports.null);
    assert!(!p.exports.valid);
    assert!(!p.main.valid);
    assert!(!p.main.null);
    assert_eq!(p.main.value, "");
}
