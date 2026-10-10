// Ported from tsc/internal/format/indent_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::ast::Node;
use tsc_ast::ids::NodeId;
use tsc_ast::kind_generated::Kind;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::scriptkind::ScriptKind;
use tsc_parser::parse_source_file;
use tsc_tspath::{path_key_from_canonical, rooted_file_path_from_normalized};

use crate::get_containing_list;

fn test_parse_options(file_name: &str) -> SourceFileParseOptions {
    SourceFileParseOptions {
        file_name: rooted_file_path_from_normalized(file_name),
        path_key: path_key_from_canonical(file_name),
        ..Default::default()
    }
}

#[test]
fn test_get_containing_list_named_imports() {
    let text = "import type {\n    AAA,\n    BBB,\n} from \"./bar\";";

    let (source_file, mut nodes) =
        parse_source_file(test_parse_options("/test.ts"), text, ScriptKind::Ts);

    // Find ImportSpecifier nodes (AAA and BBB)
    let mut import_specifiers: Vec<NodeId> = Vec::new();
    for_each_descendant_of_kind(
        source_file,
        Kind::ImportSpecifier,
        &mut |node| {
            import_specifiers.push(node);
        },
        &nodes,
    );

    assert_eq!(
        import_specifiers.len(),
        2,
        "Expected 2 import specifiers, got {}",
        import_specifiers.len()
    );

    // Test GetContainingList for each import specifier
    for specifier in import_specifiers {
        let list = get_containing_list(specifier, source_file, &mut nodes);
        assert!(
            list.is_some(),
            "GetContainingList should return non-nil for import specifier"
        );
        let list = list.unwrap();
        assert_eq!(
            list.nodes.len(),
            2,
            "Expected list with 2 elements, got {}",
            list.nodes.len()
        );
    }
}

fn for_each_descendant_of_kind(
    node: NodeId,
    kind: Kind,
    action: &mut dyn FnMut(NodeId),
    nodes: &[Node],
) {
    nodes[node].for_each_child(nodes, &mut |child| {
        if nodes[child].kind == kind {
            action(child);
        }
        for_each_descendant_of_kind(child, kind, action, nodes);
        false
    });
}
