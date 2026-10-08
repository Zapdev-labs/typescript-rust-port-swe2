// Tests for the ported scanner (tsc/internal/scanner/scanner_test.go).
//
// PORT: the Go tests build bare `*ast.Node` structs by field; here they are
// constructed through `NodeFactory::new_token` (kind is the only field the
// tested predicates inspect) with `flags`/`parent`/`loc` patched afterwards.

use tsc_ast::kind_generated::Kind;
use tsc_ast::nodeflags::NodeFlags;
use tsc_ast::{NodeFactory, NodeFactoryHooks};
use tsc_core::options_generated::NewLineKind;
use tsc_core::text::TextRange;
use tsc_stringutil as stringutil;

use super::{Scanner, string_to_token, token_to_string};
use crate::utilities::{
    get_text_of_node_from_source_text, is_jsdoc_type_expression_or_child,
    normalize_jsdoc_type_source_text,
};

#[test]
fn test_scan_string_preserves_lone_surrogates() {
    let mut s = Scanner::new();
    s.set_text("\"🦀\\ud7ff\\ud800\\ud801\\uD83E\\uDD80\"");
    assert_eq!(s.scan(), Kind::StringLiteral);
    let mut expected = "🦀".as_bytes().to_vec();
    expected.extend_from_slice(&stringutil::encode_js_string_rune(0xD7FF));
    expected.extend_from_slice(&stringutil::encode_js_string_rune(0xD800));
    expected.extend_from_slice(&stringutil::encode_js_string_rune(0xD801));
    expected.extend_from_slice("🦀".as_bytes());
    assert_eq!(s.token_value(), expected.as_slice());
}

#[test]
fn test_normalize_jsdoc_type_source_text() {
    let tests: &[(&str, &str, &[&str])] = &[
        ("single line", " \t* \tFoo", &["Foo"]),
        (
            "ECMAScript line breaks",
            "Foo\r\n * Bar\r\t* Baz\u{2028} * Qux\u{2029}* Quux",
            &["Foo", "Bar", "Baz", "Qux", "Quux"],
        ),
        (
            "blank and trailing lines",
            "Foo\r\n *\r\n",
            &["Foo", "", ""],
        ),
        ("line without marker", "Foo\n  Bar", &["Foo", "Bar"]),
        ("only leading marker", "**Foo", &["*Foo"]),
    ];

    for &(name, text, expected_lines) in tests {
        let expected = expected_lines.join(NewLineKind::LF.get_new_line_character());
        assert_eq!(normalize_jsdoc_type_source_text(text), expected, "{name}");
    }
}

#[test]
fn test_is_jsdoc_type_expression_or_child() {
    let mut nodes = Vec::new();
    let mut f = NodeFactory::new(NodeFactoryHooks::default());

    let jsdoc_type = f.new_token(&mut nodes, Kind::TypeReference);
    nodes[jsdoc_type].flags = NodeFlags::JSDOC;
    let jsdoc_type_child = f.new_identifier(&mut nodes, "x");
    nodes[jsdoc_type_child].flags = NodeFlags::JSDOC;
    nodes[jsdoc_type_child].parent = Some(jsdoc_type);

    let reparsed_type = f.new_token(&mut nodes, Kind::TypeLiteral);
    nodes[reparsed_type].flags = NodeFlags::REPARSED;
    let reparsed_type_child = f.new_identifier(&mut nodes, "y");
    nodes[reparsed_type_child].flags = NodeFlags::REPARSED;
    nodes[reparsed_type_child].parent = Some(reparsed_type);

    let ordinary_type = f.new_token(&mut nodes, Kind::TypeReference);

    let jsdoc_tag = f.new_token(&mut nodes, Kind::JSDocParameterTag);
    nodes[jsdoc_tag].flags = NodeFlags::JSDOC;
    let jsdoc_tag_child = f.new_identifier(&mut nodes, "z");
    nodes[jsdoc_tag_child].flags = NodeFlags::JSDOC;
    nodes[jsdoc_tag_child].parent = Some(jsdoc_tag);

    let type_expression = f.new_token(&mut nodes, Kind::JSDocTypeExpression);

    let tests: &[(&str, tsc_ast::NodeId, bool)] = &[
        ("type expression", type_expression, true),
        ("JSDoc type", jsdoc_type, true),
        ("JSDoc type child", jsdoc_type_child, true),
        ("reparsed type", reparsed_type, true),
        ("reparsed type child", reparsed_type_child, true),
        ("ordinary type", ordinary_type, false),
        ("other JSDoc child", jsdoc_tag_child, false),
    ];

    for &(name, node, expected) in tests {
        assert_eq!(
            is_jsdoc_type_expression_or_child(node, &nodes),
            expected,
            "{name}"
        );
    }
}

#[test]
fn test_get_text_of_node_from_jsdoc_type_preserves_asterisk_type() {
    let source_text = ["", " * *"].join(NewLineKind::LF.get_new_line_character());
    let mut nodes = Vec::new();
    let mut f = NodeFactory::new(NodeFactoryHooks::default());
    let node = f.new_token(&mut nodes, Kind::JSDocAllType);
    nodes[node].flags = NodeFlags::JSDOC;
    nodes[node].loc = TextRange::new(0, source_text.len() as i32);

    assert_eq!(
        &*get_text_of_node_from_source_text(&source_text, node, false, &nodes),
        "*"
    );
}

#[test]
fn test_scan_source_keyword() {
    let mut s = Scanner::new();
    s.set_text("source sourceValue");

    assert_eq!(s.scan(), Kind::SourceKeyword);
    assert_eq!(token_to_string(Kind::SourceKeyword), "source");
    assert_eq!(string_to_token("source"), Kind::SourceKeyword);
    assert_eq!(s.scan(), Kind::Identifier);
    assert_eq!(s.token_value(), b"sourceValue");
}
