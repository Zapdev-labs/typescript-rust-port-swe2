// Ported from tsc/internal/testutil/parsetestutil/parsetestutil.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - Go returns `*ast.SourceFile`; the ported parser produces
//   `(NodeId, Vec<Node>)` — the file id plus the arena owning it (Go's heap
//   pointer needs no arena). Callers pass `nodes` back into
//   [check_diagnostics]/[mark_synthetic_recursive].
// - `testing.TB` has no Rust equivalent: `CheckDiagnostics`/
//   `CheckDiagnosticsMessage` return `Result<(), Error>` — `t.Error` becomes
//   `Err`, which test callers `?` or `.unwrap()`.
// - `MarkSyntheticRecursive` mutates `node.Loc` in place in Go (heap
//   pointers). The arena visitor rebuilds nodes whose embedded `NodeList`/
//   `ModifierList` changed `loc` (the `update_*` path clones changed
//   nodes), so the port returns the resulting root `NodeId` — callers
//   replace their file handle with it.

use tsc_ast::ast::{ModifierList, Node, NodeFactory, NodeList};
use tsc_ast::ids::NodeId;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::visitor::{NodeVisitor, NodeVisitorHooks, VisitorCx};
use tsc_core::core::{get_script_kind_from_file_name, if_else};
use tsc_core::text::TextRange;
use tsc_diagnosticwriter as diagnosticwriter;
use tsc_parser as parser;
use tsc_tspath::{self as tspath, CaseSensitivity, RootedFilePath, RootedPath};

use crate::Error;

/// Simplifies parsing an input string into a SourceFile for testing purposes.
///
/// PORT: returns the `Kind::SourceFile` node id and its arena instead of
/// `*ast.SourceFile`.
pub fn parse_typescript(text: &str, jsx: bool) -> (NodeId, Vec<Node>) {
    let file_name: RootedFilePath =
        tspath::rooted_file_path_from_normalized(if_else(jsx, "/main.tsx", "/main.ts"));
    parser::parse_source_file(
        SourceFileParseOptions {
            file_name: file_name.clone(),
            path_key: CaseSensitivity::CaseSensitive
                .path_key(&RootedPath::from(file_name.clone())),
            ..Default::default()
        },
        text,
        get_script_kind_from_file_name(&file_name),
    )
}

/// Asserts that the given file has no parse diagnostics.
///
/// PORT: `t.Error` → `Err(Error)` carrying the formatted diagnostics.
pub fn check_diagnostics(nodes: &[Node], file: NodeId) -> Result<(), Error> {
    let diagnostics = nodes[file].as_source_file().diagnostics();
    if !diagnostics.is_empty() {
        let mut b = Vec::new();
        diagnosticwriter::write_format_diagnostics(
            &mut b,
            &diagnosticwriter::from_ast_diagnostics(diagnostics, nodes),
            &diagnosticwriter::FormattingOptions {
                new_line: "\n".to_string(),
                ..Default::default()
            },
        );
        return Err(Error::new(String::from_utf8_lossy(&b).into_owned()));
    }
    Ok(())
}

/// Asserts that the given file has no parse diagnostics and asserts the given message.
///
/// PORT: `t.Error` → `Err(Error)` carrying `message` plus the formatted
/// diagnostics.
pub fn check_diagnostics_message(
    nodes: &[Node],
    file: NodeId,
    message: &str,
) -> Result<(), Error> {
    let diagnostics = nodes[file].as_source_file().diagnostics();
    if !diagnostics.is_empty() {
        let mut b = Vec::new();
        diagnosticwriter::write_format_diagnostics(
            &mut b,
            &diagnosticwriter::from_ast_diagnostics(diagnostics, nodes),
            &diagnosticwriter::FormattingOptions {
                new_line: "\n".to_string(),
                ..Default::default()
            },
        );
        return Err(Error::new(format!(
            "{message}{}",
            String::from_utf8_lossy(&b)
        )));
    }
    Ok(())
}

/// `newSyntheticRecursiveVisitor` — a visitor that marks every visited node,
/// token, list, and modifier list as synthetic (`loc = (-1,-1)`).
///
/// PORT: Go's `Visit` closure captures the enclosing `v` before assignment;
/// the ported visitor is passed to the closure as a parameter instead (the
/// ported `VisitFn`/hook signatures receive `&NodeVisitor`). The factory is
/// threaded through `VisitorCx` rather than bound at construction.
fn new_synthetic_recursive_visitor() -> NodeVisitor<'static> {
    NodeVisitor::new(
        Box::new(|v: &NodeVisitor, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
            // `return v.VisitEachChild(node)` — `None` here means "unchanged",
            // not "removed"; map it back to the input node.
            Some(v.visit_each_child(cx, node).unwrap_or(node))
        }),
        NodeVisitorHooks {
            visit_node: Some(Box::new(
                |cx: &mut VisitorCx<'_, '_>, node: NodeId, v: &NodeVisitor| {
                    cx.nodes[node].loc = TextRange::undefined();
                    v.visit_node(cx, Some(node))
                },
            )),
            visit_token: Some(Box::new(
                |cx: &mut VisitorCx<'_, '_>, node: NodeId, v: &NodeVisitor| {
                    cx.nodes[node].loc = TextRange::undefined();
                    v.visit_node(cx, Some(node))
                },
            )),
            visit_nodes: Some(Box::new(
                |cx: &mut VisitorCx<'_, '_>, mut nodes: Option<NodeList>, v: &NodeVisitor| {
                    if let Some(nodes) = &mut nodes {
                        nodes.loc = TextRange::undefined();
                    }
                    v.visit_nodes(cx, nodes)
                },
            )),
            visit_modifiers: Some(Box::new(
                |cx: &mut VisitorCx<'_, '_>, mut nodes: Option<ModifierList>, v: &NodeVisitor| {
                    if let Some(nodes) = &mut nodes {
                        nodes.loc = TextRange::undefined();
                    }
                    v.visit_modifiers(cx, nodes)
                },
            )),
            ..Default::default()
        },
    )
}

/// Sets the Loc of the given node and every Node in its subtree to an undefined TextRange (-1,-1).
///
/// PORT: as in Go the root node itself keeps its `loc` — the marking hooks
/// only fire on children visited by `visit_each_child`. Because children with
/// re-marked lists are rebuilt, the (possibly new) root id is returned.
pub fn mark_synthetic_recursive(nodes: &mut Vec<Node>, node: NodeId) -> NodeId {
    let mut factory = NodeFactory::default();
    let mut cx = VisitorCx::new(nodes, &mut factory);
    new_synthetic_recursive_visitor()
        .visit_node(&mut cx, Some(node))
        .unwrap_or(node)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_typescript_ts_and_tsx() {
        let (ts, nodes) = parse_typescript("const x = 1;", false);
        check_diagnostics(&nodes, ts).unwrap();
        assert_eq!(nodes[ts].kind, tsc_ast::Kind::SourceFile);

        // JSX syntax parses only when `jsx` is true.
        let (tsx, nodes) = parse_typescript("const el = <div />;", true);
        check_diagnostics(&nodes, tsx).unwrap();
    }

    #[test]
    fn check_diagnostics_reports_errors() {
        let (file, nodes) = parse_typescript("const = ;", false);
        assert!(!nodes[file].as_source_file().diagnostics().is_empty());
        assert!(check_diagnostics(&nodes, file).is_err());
        assert!(check_diagnostics_message(&nodes, file, "want parse error\n").is_err());
    }

    #[test]
    fn mark_synthetic_recursive_undefined_locs() {
        let (file, mut nodes) = parse_typescript("function f(x: number) { return x + 1; }", false);
        let file = mark_synthetic_recursive(&mut nodes, file);

        // Go parity notes:
        // - The root keeps its own `loc` (`MarkSyntheticRecursive` calls
        //   `v.VisitNode(root)` — the `VisitNode` hook does not fire for the
        //   root itself).
        // - `VisitSlice` invokes the raw `Visit` fn on list elements,
        //   bypassing the `VisitNode` hook, so list elements retain their
        //   original locs.
        // - Node fields (visited via `v.visitNode`), tokens, and lists
        //   (visited via the `VisitNodes`/`VisitModifiers` hooks) are marked.
        assert_ne!(nodes[file].loc.pos(), -1, "root should not be marked");

        let statements = nodes[file]
            .as_source_file()
            .statements
            .as_ref()
            .expect("statements");
        assert_eq!(
            statements.loc.pos(),
            -1,
            "statements list should be marked synthetic"
        );

        let func_decl = statements.nodes[0];
        assert_eq!(nodes[func_decl].kind, tsc_ast::Kind::FunctionDeclaration);
        assert_ne!(
            nodes[func_decl].loc.pos(),
            -1,
            "list element should retain its original loc (Go parity)"
        );

        let name = nodes[func_decl]
            .as_function_declaration()
            .name
            .expect("function name");
        assert_eq!(
            nodes[name].loc.pos(),
            -1,
            "name node field should be marked synthetic"
        );
        let body = nodes[func_decl]
            .as_function_declaration()
            .function_like_with_body_base
            .body_base
            .body
            .expect("function body");
        assert_eq!(
            nodes[body].loc.pos(),
            -1,
            "body node field should be marked synthetic"
        );
    }
}
