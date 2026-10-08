// Ported from tsc/internal/binder/binder_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The Go file only contains `BenchmarkBind` over fixture files. Fixture
// infrastructure does not exist in the Rust port yet, so instead this file
// provides smoke tests that parse a small source string, bind it, and assert
// on the produced symbol tables, diagnostics, and flow graph.

use tsc_ast::ast::Node;
use tsc_ast::ids::{FlowNodeId, NodeId};
use tsc_ast::kind_generated::Kind;
use tsc_ast::nodeflags::NodeFlags;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::symbolflags::SymbolFlags;
use tsc_core::scriptkind::ScriptKind;
use tsc_parser::parse_source_file;
use tsc_tspath::{PathKey, RootedFilePath};

use crate::binder::{bind_result, bind_source_file};

fn parse_and_bind(source: &str, file_name: &str) -> (NodeId, Vec<Node>) {
    let file_name = RootedFilePath::from(file_name);
    let opts = SourceFileParseOptions {
        file_name,
        path_key: PathKey::default(),
        ..Default::default()
    };
    let (file, mut nodes) = parse_source_file(opts, source, ScriptKind::Ts);
    bind_source_file(&mut nodes, file);
    (file, nodes)
}

/// Binding a small module declares symbols into file locals and marks the
//  external module indicator.
#[test]
fn bind_declares_symbols_and_module_indicator() {
    let (file, nodes) = parse_and_bind(
        "import {x} from \"./m\";\nexport const y = x + 1;\nfunction foo() { return y; }\n",
        "/src/test.ts",
    );
    assert!(nodes[file].as_source_file().is_bound());
    assert!(
        nodes[file]
            .as_source_file()
            .external_module_indicator
            .is_some()
    );
    assert!(nodes[file].as_source_file().bind_diagnostics.is_empty());

    let locals = nodes[file].locals().expect("source file locals");
    assert!(locals.get("y").is_some());
    assert!(locals.get("foo").is_some());
    assert!(locals.get("x").is_some());

    // The bound symbol arena and flow graph are retrievable.
    let result = bind_result(&nodes, file).expect("bind result");
    assert!(!result.symbols.is_empty());
    assert!(!result.flow_nodes.is_empty());
    let foo = *locals.get("foo").unwrap();
    assert!(
        result.symbols[foo.index()]
            .flags
            .intersects(SymbolFlags::FUNCTION)
    );
    assert_eq!(result.symbols[foo.index()].declarations.len(), 1);
}

/// Re-binding a bound file is a no-op (`bind_once`).
#[test]
fn bind_is_idempotent() {
    let (file, mut nodes) = parse_and_bind("export const a = 1;", "/src/a.ts");
    let result_ptr = bind_result(&nodes, file).expect("bind result") as *const _;
    bind_source_file(&mut nodes, file);
    assert_eq!(
        bind_result(&nodes, file).expect("bind result") as *const _,
        result_ptr,
        "second bind must reuse, not rebuild"
    );
}

/// Control-flow graph: a return statement ends the current flow and records
//  explicit-return flags on the function.
#[test]
fn bind_builds_function_flow() {
    // `if (b) return 1;` leaves a fall-through path, so the function gets both
    // HAS_IMPLICIT_RETURN and HAS_EXPLICIT_RETURN (Go sets both only when the
    // end flow is reachable and hasExplicitReturn).
    let (file, nodes) = parse_and_bind(
        "export function f(b: boolean) { if (b) { return 1; } }",
        "/src/flow.ts",
    );
    assert!(nodes[file].as_source_file().bind_diagnostics.is_empty());
    let result = bind_result(&nodes, file).expect("bind result");

    // Find the function declaration and check reachability flags.
    let locals = nodes[file].locals().expect("locals");
    let f = *locals.get("f").expect("f symbol");
    let decl = result.symbols[f.index()].declarations[0];
    assert!(nodes[decl].flags.intersects(NodeFlags::HAS_IMPLICIT_RETURN));
    assert!(nodes[decl].flags.intersects(NodeFlags::HAS_EXPLICIT_RETURN));
    assert!(
        nodes[decl]
            .body_data()
            .expect("body data")
            .end_flow_node
            .is_some()
    );
    let end_flow = nodes[decl].body_data().unwrap().end_flow_node.unwrap();
    assert_ne!(end_flow, FlowNodeId::NONE);
}

/// Strict-mode grammar check: `with` inside a module is a bind diagnostic.
#[test]
fn bind_reports_strict_mode_with() {
    let (file, nodes) = parse_and_bind(
        "export {};\ndeclare const o: any;\nwith (o) { console.log(1); }",
        "/src/strict.ts",
    );
    let diagnostics = &nodes[file].as_source_file().bind_diagnostics;
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        tsc_ast::diagnostic::lock_diagnostic(&diagnostics[0]).code(),
        tsc_diagnostics::X_with_statements_are_not_allowed_in_strict_mode.code()
    );
}

/// `FindUseStrictPrologue` port check.
#[test]
fn find_use_strict_prologue_detects_directive() {
    let (file, nodes) = parse_and_bind("\"use strict\";\nexport const a = 1;", "/src/prologue.ts");
    let statements = nodes[file].statements().expect("statements");
    let prologue =
        crate::binder::find_use_strict_prologue(nodes[file].as_source_file(), statements, &nodes);
    assert!(prologue.is_some());
    assert_eq!(nodes[prologue.unwrap()].kind, Kind::ExpressionStatement);
}
