// Ported from tsc/internal/sourcemap/generator_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_tspath::CaseSensitivity;

use crate::generator::{Generator, RawSourceMap};

fn new_generator() -> Generator {
    Generator::new("main.js", "/", "/", CaseSensitivity::CaseInsensitive)
}

#[test]
fn test_source_map_generator_empty() {
    let mut sm = new_generator();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec![],
            mappings: String::new(),
            names: vec![],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_empty_serialized() {
    let mut sm = new_generator();
    let actual = sm.to_json_string();
    let expected =
        r#"{"version":3,"file":"main.js","sourceRoot":"/","sources":[],"names":[],"mappings":""}"#;
    assert_eq!(actual, expected);
}

#[test]
fn test_source_map_generator_add_source() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    let source_map = sm.raw_source_map();
    assert_eq!(source_index, 0);
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["main.ts".to_string()],
            mappings: String::new(),
            names: vec![],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_set_source_content() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.set_source_content(source_index, "foo").unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(source_index, 0);
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["main.ts".to_string()],
            mappings: String::new(),
            names: vec![],
            sources_content: Some(vec![Some("foo".to_string())]),
        }
    );
}

#[test]
fn test_source_map_generator_set_source_content_for_second_source_only() {
    let mut sm = new_generator();
    sm.add_source("/skipped.ts");
    let source_index = sm.add_source("/main.ts");
    sm.set_source_content(source_index, "foo").unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(source_index, 1);
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["skipped.ts".to_string(), "main.ts".to_string()],
            mappings: String::new(),
            names: vec![],
            sources_content: Some(vec![None, Some("foo".to_string())]),
        }
    );
}

#[test]
fn test_source_map_generator_set_source_content_source_index_out_of_range() {
    let mut sm = new_generator();
    assert_eq!(
        sm.set_source_content(-1, ""),
        Err("sourceIndex is out of range")
    );
    assert_eq!(
        sm.set_source_content(0, ""),
        Err("sourceIndex is out of range")
    );
}

#[test]
fn test_source_map_generator_set_source_content_for_second_source_only_serialized() {
    let mut sm = new_generator();
    sm.add_source("/skipped.ts");
    let source_index = sm.add_source("/main.ts");
    sm.set_source_content(source_index, "foo").unwrap();
    let actual = sm.to_json_string();
    let expected = r#"{"version":3,"file":"main.js","sourceRoot":"/","sources":["skipped.ts","main.ts"],"names":[],"mappings":"","sourcesContent":[null,"foo"]}"#;
    assert_eq!(actual, expected);
}

#[test]
fn test_source_map_generator_add_name() {
    let mut sm = new_generator();
    let name_index = sm.add_name("foo");
    let source_map = sm.raw_source_map();
    assert_eq!(name_index, 0);
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec![],
            mappings: String::new(),
            names: vec!["foo".to_string()],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_generated_mapping() {
    let mut sm = new_generator();
    sm.add_generated_mapping(0, 0).unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec![],
            mappings: "A".to_string(),
            names: vec![],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_generated_mapping_replaces_pending_source_mapping() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.add_source_mapping(0, 0, source_index, 0, 0).unwrap();
    sm.add_generated_mapping(0, 0).unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(source_map.mappings, "A");
}

#[test]
fn test_source_map_generator_add_generated_mapping_is_not_replaced_by_source_mapping() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.add_generated_mapping(0, 0).unwrap();
    sm.add_source_mapping(0, 0, source_index, 0, 0).unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(source_map.mappings, "A");
}

#[test]
fn test_source_map_generator_add_generated_mapping_on_second_line_only() {
    let mut sm = new_generator();
    sm.add_generated_mapping(1, 0).unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec![],
            mappings: ";A".to_string(),
            names: vec![],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_source_mapping() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.add_source_mapping(0, 0, source_index, 0, 0).unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["main.ts".to_string()],
            mappings: "AAAA".to_string(),
            names: vec![],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_source_mapping_next_generated_character() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.add_source_mapping(0, 0, source_index, 0, 0).unwrap();
    sm.add_source_mapping(0, 1, source_index, 0, 0).unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["main.ts".to_string()],
            mappings: "AAAA,CAAA".to_string(),
            names: vec![],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_source_mapping_next_generated_and_source_character() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.add_source_mapping(0, 0, source_index, 0, 0).unwrap();
    sm.add_source_mapping(0, 1, source_index, 0, 1).unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["main.ts".to_string()],
            mappings: "AAAA,CAAC".to_string(),
            names: vec![],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_source_mapping_next_generated_line() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.add_source_mapping(0, 0, source_index, 0, 0).unwrap();
    sm.add_source_mapping(1, 0, source_index, 0, 0).unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["main.ts".to_string()],
            mappings: "AAAA;AAAA".to_string(),
            names: vec![],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_source_mapping_previous_source_character() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.add_source_mapping(0, 0, source_index, 0, 1).unwrap();
    sm.add_source_mapping(0, 1, source_index, 0, 0).unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["main.ts".to_string()],
            mappings: "AAAC,CAAD".to_string(),
            names: vec![],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_named_source_mapping() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    let name_index = sm.add_name("foo");
    sm.add_named_source_mapping(0, 0, source_index, 0, 0, name_index)
        .unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["main.ts".to_string()],
            mappings: "AAAAA".to_string(),
            names: vec!["foo".to_string()],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_named_source_mapping_with_previous_name() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    let name_index1 = sm.add_name("foo");
    let name_index2 = sm.add_name("bar");
    sm.add_named_source_mapping(0, 0, source_index, 0, 0, name_index2)
        .unwrap();
    sm.add_named_source_mapping(0, 1, source_index, 0, 0, name_index1)
        .unwrap();
    let source_map = sm.raw_source_map();
    assert_eq!(
        source_map,
        RawSourceMap {
            version: 3,
            file: "main.js".to_string(),
            source_root: "/".to_string(),
            sources: vec!["main.ts".to_string()],
            mappings: "AAAAC,CAAAD".to_string(),
            names: vec!["foo".to_string(), "bar".to_string()],
            sources_content: None,
        }
    );
}

#[test]
fn test_source_map_generator_add_generated_mapping_generated_line_cannot_backtrack() {
    let mut sm = new_generator();
    sm.add_generated_mapping(1, 0).unwrap();
    assert_eq!(
        sm.add_generated_mapping(0, 0),
        Err("generatedLine cannot backtrack")
    );
}

#[test]
fn test_source_map_generator_add_generated_mapping_generated_character_cannot_be_negative() {
    let mut sm = new_generator();
    sm.add_generated_mapping(0, 0).unwrap();
    assert_eq!(
        sm.add_generated_mapping(0, -1),
        Err("generatedCharacter cannot be negative")
    );
}

#[test]
fn test_source_map_generator_add_source_mapping_generated_line_cannot_backtrack() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.add_source_mapping(1, 0, source_index, 0, 0).unwrap();
    assert_eq!(
        sm.add_source_mapping(0, 0, source_index, 0, 0),
        Err("generatedLine cannot backtrack")
    );
}

#[test]
fn test_source_map_generator_add_source_mapping_generated_character_cannot_be_negative() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    sm.add_source_mapping(0, 0, source_index, 0, 0).unwrap();
    assert_eq!(
        sm.add_source_mapping(0, -1, source_index, 0, 0),
        Err("generatedCharacter cannot be negative")
    );
}

#[test]
fn test_source_map_generator_add_source_mapping_source_index_is_out_of_range() {
    let mut sm = new_generator();
    assert_eq!(
        sm.add_source_mapping(0, 0, -1, 0, 0),
        Err("sourceIndex is out of range")
    );
    assert_eq!(
        sm.add_source_mapping(0, 0, 0, 0, 0),
        Err("sourceIndex is out of range")
    );
}

#[test]
fn test_source_map_generator_add_source_mapping_source_line_cannot_be_negative() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    assert_eq!(
        sm.add_source_mapping(0, 0, source_index, -1, 0),
        Err("sourceLine cannot be negative")
    );
}

#[test]
fn test_source_map_generator_add_source_mapping_source_character_cannot_be_negative() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    assert_eq!(
        sm.add_source_mapping(0, 0, source_index, 0, -1),
        Err("sourceCharacter cannot be negative")
    );
}

#[test]
fn test_source_map_generator_add_named_source_mapping_generated_line_cannot_backtrack() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    let name_index = sm.add_name("foo");
    sm.add_named_source_mapping(1, 0, source_index, 0, 0, name_index)
        .unwrap();
    assert_eq!(
        sm.add_named_source_mapping(0, 0, source_index, 0, 0, name_index),
        Err("generatedLine cannot backtrack")
    );
}

#[test]
fn test_source_map_generator_add_named_source_mapping_generated_character_cannot_be_negative() {
    let mut sm = new_generator();
    let source_index = sm.add_source("/main.ts");
    let name_index = sm.add_name("foo");
    sm.add_named_source_mapping(0, 0, source_index, 0, 0, name_index)
        .unwrap();
    assert_eq!(
        sm.add_named_source_mapping(0, -1, source_index, 0, 0, name_index),
        Err("generatedCharacter cannot be negative")
    );
}

#[test]
fn test_source_map_generator_add_named_source_mapping_source_index_is_out_of_range() {
    let mut sm = new_generator();
    let name_index = sm.add_name("foo");
    assert_eq!(
        sm.add_named_source_mapping(0, 0, -1, 0, 0, name_index),
        Err("sourceIndex is out of range")
    );
    assert_eq!(
        sm.add_named_source_mapping(0, 0, 0, 0, 0, name_index),
        Err("sourceIndex is out of range")
    );
}

#[test]
fn test_source_map_generator_add_named_source_mapping_source_line_cannot_be_negative() {
    let mut sm = new_generator();
    let name_index = sm.add_name("foo");
    let source_index = sm.add_source("/main.ts");
    assert_eq!(
        sm.add_named_source_mapping(0, 0, source_index, -1, 0, name_index),
        Err("sourceLine cannot be negative")
    );
}

#[test]
fn test_source_map_generator_add_named_source_mapping_source_character_cannot_be_negative() {
    let mut sm = new_generator();
    let name_index = sm.add_name("foo");
    let source_index = sm.add_source("/main.ts");
    assert_eq!(
        sm.add_named_source_mapping(0, 0, source_index, 0, -1, name_index),
        Err("sourceCharacter cannot be negative")
    );
}

#[test]
fn test_source_map_generator_add_named_source_mapping_name_index_is_out_of_range() {
    let mut sm = new_generator();
    sm.add_source("/main.ts");
    assert_eq!(
        sm.add_named_source_mapping(0, 0, 0, 0, 0, -1),
        Err("nameIndex is out of range")
    );
    assert_eq!(
        sm.add_named_source_mapping(0, 0, 0, 0, 0, 0),
        Err("nameIndex is out of range")
    );
}
