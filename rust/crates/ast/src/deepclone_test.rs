// Ported from tsc/internal/ast/deepclone_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT(deferred): the Go test drives `parsetestutil.ParseTypeScript` over a
// ~300-case table of source snippets; it lands with the parser (M3). This
// file ports the same structural checks against a factory-built tree so the
// deepclone machinery is exercised now.

use tsc_core::text::TextRange;
use tsc_tspath::RootedFilePath;

use crate::ast::{Node, NodeFactory, NodeFactoryHooks};
use crate::ids::NodeId;
use crate::kind_generated::Kind;
use crate::nodeflags::NodeFlags;
use crate::parseoptions::SourceFileParseOptions;
use crate::tokenflags::TokenFlags;

fn assert_trees_isomorphic(nodes: &[Node], original: NodeId, copy: NodeId) {
    assert_ne!(original, copy, "clone must be a fresh node");
    let mut work = vec![(original, copy)];
    while let Some((o, c)) = work.pop() {
        let on = &nodes[o];
        let cn = &nodes[c];
        assert_eq!(on.kind, cn.kind, "kind mismatch at {o:?}/{c:?}");
        // BFS children via for_each_child (immutable variant of getChildren).
        let mut o_children = Vec::new();
        on.for_each_child(nodes, &mut |child| {
            o_children.push(child);
            false
        });
        let mut c_children = Vec::new();
        cn.for_each_child(nodes, &mut |child| {
            c_children.push(child);
            false
        });
        assert_eq!(o_children.len(), c_children.len());
        work.extend(o_children.into_iter().zip(c_children));
    }
}

fn collect_all(nodes: &[Node], root: NodeId) -> Vec<NodeId> {
    let mut out = vec![root];
    let mut i = 0;
    while i < out.len() {
        let n = out[i];
        i += 1;
        nodes[n].for_each_child(nodes, &mut |child| {
            out.push(child);
            false
        });
    }
    out
}

#[test]
fn test_deep_clone_node_synthetic_tree() {
    let mut nodes: Vec<Node> = Vec::new();
    let mut f = NodeFactory::new(NodeFactoryHooks::default());

    // f(x, "s") as an expression statement inside a source file.
    let callee = f.new_identifier(&mut nodes, "f");
    let arg1 = f.new_identifier(&mut nodes, "x");
    let arg2 = f.new_string_literal(&mut nodes, "s", TokenFlags::NONE);
    let args = f.new_node_list(vec![arg1, arg2].into_boxed_slice());
    let call = f.new_call_expression(
        &mut nodes,
        Some(callee),
        None,
        None,
        Some(args),
        NodeFlags::NONE,
    );
    let stmt = f.new_expression_statement(&mut nodes, Some(call));
    let stmts = f.new_node_list(vec![stmt].into_boxed_slice());
    let eof = f.new_token(&mut nodes, Kind::EndOfFile);
    let file = f.new_source_file(
        &mut nodes,
        &SourceFileParseOptions {
            file_name: RootedFilePath::from("test.ts"),
            ..Default::default()
        },
        "f(x, \"s\")",
        Some(stmts),
        Some(eof),
    );

    // Real locations on the source tree.
    nodes[call].loc = TextRange::new(0, 9);
    nodes[callee].loc = TextRange::new(0, 1);

    let clone = f
        .deep_clone_node(&mut nodes, file)
        .expect("deep clone produces a node");

    assert_trees_isomorphic(&nodes, file, clone);

    // DeepCloneNode forces synthetic (-1,-1) locations on every clone.
    for &id in &collect_all(&nodes, clone) {
        assert_eq!(
            nodes[id].loc,
            TextRange::new(-1, -1),
            "cloned node {id:?} should have synthetic loc"
        );
    }
}
