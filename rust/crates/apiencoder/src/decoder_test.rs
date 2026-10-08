// Ported from tsc/internal/api/encoder/decoder_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `parser.ParseSourceFile` returns `(NodeId, Vec<Node>)`; encode
// returns `(Vec<u8>, NodeIndexTable)` and decode returns
// `(NodeId, Vec<Node>)` — arena vecs are threaded explicitly. Optional
// child/list fields are `Option<NodeId>`/`Option<NodeList>`; `Option`
// assertions replace Go nil checks. `assert.ErrorContains` becomes
// `err.to_string().contains(...)`. The benchmark is an ignored
// single-iteration test.

use std::cell::Cell;

use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::{Kind, Node, NodeFlags, NodeId, NodeVisitor, NodeVisitorHooks, VisitorCx};
use tsc_core::scriptkind::ScriptKind;
use tsc_parser::parse_source_file;
use tsc_tspath::{path_key_from_canonical, rooted_file_path_from_normalized};

use crate::decoder::{decode_nodes, decode_source_file};
use crate::encoder::{encode_node, encode_source_file};

fn test_parse_options(file_name: &str) -> SourceFileParseOptions {
    SourceFileParseOptions {
        file_name: rooted_file_path_from_normalized(file_name),
        path_key: path_key_from_canonical(file_name),
        ..Default::default()
    }
}

fn parse_test_source_file(code: &str) -> (NodeId, Vec<Node>) {
    parse_source_file(test_parse_options("/test.ts"), code, ScriptKind::Ts)
}

fn round_trip(sf: NodeId, nodes: &mut Vec<Node>) -> (NodeId, Vec<Node>) {
    let (buf, _) = encode_source_file(nodes, sf);
    decode_source_file(&buf).unwrap()
}

#[test]
fn test_decode_source_file_basic() {
    let (sf, mut nodes) = parse_test_source_file("let x = 1;");
    let (buf, _) = encode_source_file(&mut nodes, sf);

    let (decoded, arena) = decode_source_file(&buf).unwrap();
    assert_eq!(arena[decoded].kind, Kind::SourceFile);
    assert_eq!(
        arena[decoded].as_source_file().file_name.as_string(),
        "/test.ts"
    );
    assert_eq!(arena[decoded].as_source_file().text, "let x = 1;");
    assert!(arena[decoded].as_source_file().statements.is_some());
    assert!(arena[decoded].as_source_file().end_of_file_token.is_some());
}

#[test]
fn test_decode_source_file_metadata() {
    let tests: [(&str, &str, ScriptKind, &str); 3] = [
        ("JSON", "/test.json", ScriptKind::Json, "{\"x\": 1}"),
        ("JSX", "/test.jsx", ScriptKind::Jsx, "const x = <div />;"),
        (
            "declaration",
            "/test.d.ts",
            ScriptKind::Ts,
            "declare const x: number;",
        ),
    ];

    for (name, file_name, script_kind, code) in tests {
        let (source_file, mut nodes) = parse_source_file(
            test_parse_options(file_name),
            code,
            script_kind,
        );
        let (buf, _) = encode_source_file(&mut nodes, source_file);

        let (decoded, arena) = decode_source_file(&buf).unwrap();
        let decoded_sf = arena[decoded].as_source_file();
        let source_sf = nodes[source_file].as_source_file();
        assert_eq!(decoded_sf.script_kind, source_sf.script_kind, "{name}");
        assert_eq!(decoded_sf.language_variant, source_sf.language_variant, "{name}");
        assert_eq!(
            decoded_sf.is_declaration_file, source_sf.is_declaration_file,
            "{name}"
        );
    }
}

#[test]
fn test_decode_source_file_rejects_invalid_file_name() {
    let (sf, mut nodes) = parse_source_file(
        SourceFileParseOptions {
            file_name: rooted_file_path_from_normalized("/Test.ts"),
            path_key: path_key_from_canonical("/test.ts"),
            ..Default::default()
        },
        "",
        ScriptKind::Ts,
    );
    let (mut buf, _) = encode_source_file(&mut nodes, sf);

    let invalid_file_name = b"Test/.ts";
    let index = buf
        .windows(8)
        .position(|w| w == b"/Test.ts")
        .expect("file name not found in buffer");
    buf[index..index + invalid_file_name.len()].copy_from_slice(invalid_file_name);
    let Err(err) = decode_source_file(&buf) else {
        panic!("expected decode to fail for invalid file name")
    };
    assert!(
        err.to_string()
            .contains("invalid source file name \"Test/.ts\""),
        "unexpected error: {err}"
    );
}

#[test]
fn test_decode_source_file_statements() {
    let (sf, mut nodes) = parse_test_source_file("let a = 1;\nlet b = 2;\nlet c = 3;");
    let (decoded, arena) = round_trip(sf, &mut nodes);
    let statements = arena[decoded].as_source_file().statements.as_ref().unwrap();
    assert_eq!(statements.nodes.len(), 3);
    for (i, stmt) in statements.nodes.iter().enumerate() {
        assert_eq!(arena[*stmt].kind, Kind::VariableStatement, "statement {i}");
    }
}

#[test]
fn test_decode_source_file_variable_declaration() {
    let (sf, mut nodes) = parse_test_source_file("let x = 1;");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let var_stmt = arena[stmt].as_variable_statement();
    let decl_list_id = var_stmt.declaration_list.unwrap();
    let decl_list = arena[decl_list_id].as_variable_declaration_list();
    let declarations = decl_list.declarations.as_ref().unwrap();
    assert_eq!(declarations.nodes.len(), 1);

    let decl = arena[declarations.nodes[0]].as_variable_declaration();
    let name = decl.name.unwrap();
    assert_eq!(arena[name].kind, Kind::Identifier);
    assert_eq!(arena[name].as_identifier().text, "x");
    let initializer = decl.initializer.unwrap();
    assert_eq!(arena[initializer].kind, Kind::NumericLiteral);
    assert_eq!(arena[initializer].text(&arena), "1");
}

#[test]
fn test_decode_source_file_variable_declaration_list_flags() {
    let tests: [(&str, &str, NodeFlags); 3] = [
        ("const", "const x = 1;", NodeFlags::CONST),
        ("let", "let x = 1;", NodeFlags::LET),
        ("var", "var x = 1;", NodeFlags::NONE),
    ];

    for (name, code, expected) in tests {
        let (sf, mut nodes) = parse_test_source_file(code);
        let (decoded, arena) = round_trip(sf, &mut nodes);

        let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
        let decl_list = arena[stmt]
            .as_variable_statement()
            .declaration_list
            .unwrap();
        let got = arena[decl_list].flags & (NodeFlags::LET | NodeFlags::CONST);
        assert_eq!(
            got, expected,
            "flags for {code:?}: got {got:?}, want {expected:?} ({name})"
        );
    }
}

#[test]
fn test_decode_source_file_function_declaration() {
    let (sf, mut nodes) =
        parse_test_source_file("function add(a: number, b: number): number { return a + b; }");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let func = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let func_decl = arena[func].as_function_declaration();
    let name = func_decl.name.unwrap();
    assert_eq!(arena[name].as_identifier().text, "add");
    let params = arena[func].parameters().unwrap();
    assert_eq!(params.len(), 2);
    assert!(arena[func].type_().is_some());
    assert!(arena[func].body().is_some());

    let param0 = arena[params[0]].as_parameter_declaration();
    assert_eq!(
        arena[param0.name.unwrap()].as_identifier().text,
        "a"
    );
    assert!(param0.type_.is_some());
}

#[test]
fn test_decode_source_file_import_declaration() {
    let (sf, mut nodes) = parse_test_source_file("import { bar } from \"bar\";");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let imp = arena[stmt].as_import_declaration();
    assert!(imp.import_clause.is_some());
    let module_specifier = imp.module_specifier.unwrap();
    assert_eq!(arena[module_specifier].text(&arena), "bar");

    let clause = arena[imp.import_clause.unwrap()].as_import_clause();
    let named_bindings = clause.named_bindings.unwrap();
    let named_imports = arena[named_bindings].as_named_imports();
    let elements = named_imports.elements.as_ref().unwrap();
    assert_eq!(elements.nodes.len(), 1);
    let spec = arena[elements.nodes[0]].as_import_specifier();
    assert_eq!(
        arena[spec.name.unwrap()].as_identifier().text,
        "bar"
    );
}

#[test]
fn test_decode_source_file_source_phase_import() {
    let (sf, mut nodes) = parse_test_source_file("import source a from \"./a.wasm\";");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let clause = arena[arena[stmt].as_import_declaration().import_clause.unwrap()]
        .as_import_clause();
    assert_eq!(clause.phase_modifier, Kind::SourceKeyword);
    assert_eq!(arena[clause.name.unwrap()].text(&arena), "a");
}

#[test]
fn test_decode_source_file_if_statement() {
    let (sf, mut nodes) = parse_test_source_file("if (true) { } else { }");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let if_stmt = arena[stmt].as_if_statement();
    assert!(if_stmt.expression.is_some());
    let then_stmt = if_stmt.then_statement.unwrap();
    let else_stmt = if_stmt.else_statement.unwrap();
    assert_eq!(arena[then_stmt].kind, Kind::Block);
    assert_eq!(arena[else_stmt].kind, Kind::Block);
}

#[test]
fn test_decode_source_file_template_expression() {
    let (sf, mut nodes) = parse_test_source_file("let x = `hello ${name} world`;");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let decl_list = arena[stmt]
        .as_variable_statement()
        .declaration_list
        .unwrap();
    let decl_id = arena[decl_list]
        .as_variable_declaration_list()
        .declarations
        .as_ref()
        .unwrap()
        .nodes[0];
    let var_decl = arena[decl_id].as_variable_declaration();
    let tmpl_expr = arena[var_decl.initializer.unwrap()].as_template_expression();
    let head = tmpl_expr.head.unwrap();
    assert_eq!(arena[head].text(&arena), "hello ");
    let template_spans = tmpl_expr.template_spans.as_ref().unwrap();
    assert_eq!(template_spans.nodes.len(), 1);

    let span = arena[template_spans.nodes[0]].as_template_span();
    let expression = span.expression.unwrap();
    assert_eq!(arena[expression].kind, Kind::Identifier);
    let literal = span.literal.unwrap();
    assert_eq!(arena[literal].text(&arena), " world");
}

#[test]
fn test_decode_source_file_export_modifier() {
    let (sf, mut nodes) = parse_test_source_file("export function foo() {}");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let func = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let modifiers = arena[func].modifiers().unwrap();
    assert_eq!(modifiers.nodes.len(), 1);
    assert_eq!(arena[modifiers.nodes[0]].kind, Kind::ExportKeyword);
}

#[test]
fn test_decode_source_file_positions() {
    let code = "let x = 1;";
    let (sf, mut nodes) = parse_test_source_file(code);
    let (decoded, arena) = round_trip(sf, &mut nodes);

    assert_eq!(arena[decoded].pos(), 0);
    assert_eq!(arena[decoded].end(), code.len() as i32);
}

#[test]
fn test_decode_source_file_class_declaration() {
    let (sf, mut nodes) = parse_test_source_file("class Foo { bar(): void {} }");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    assert_eq!(arena[stmt].kind, Kind::ClassDeclaration);
    let name = arena[stmt].as_class_declaration().class_like_base.name.unwrap();
    assert_eq!(arena[name].as_identifier().text, "Foo");
    let members = arena[stmt].members().unwrap();
    assert_eq!(members.len(), 1);
    assert_eq!(arena[members[0]].kind, Kind::MethodDeclaration);
}

#[test]
fn test_decode_nodes_subtree_round_trip() {
    let (sf, mut nodes) =
        parse_test_source_file("function greet(name: string) { return `Hello, ${name}!`; }");

    let func_cell: Cell<Option<NodeId>> = Cell::new(None);
    {
        let mut factory = tsc_ast::NodeFactory::default();
        let mut cx = VisitorCx::new(&mut nodes, &mut factory);
        let visit = |_v: &NodeVisitor<'_>,
                     cx: &mut VisitorCx<'_, '_>,
                     node: NodeId|
         -> Option<NodeId> {
            if cx.nodes[node].kind == Kind::FunctionDeclaration && func_cell.get().is_none() {
                func_cell.set(Some(node));
            }
            Some(node)
        };
        let visitor = NodeVisitor::new(Box::new(visit), NodeVisitorHooks::default());
        visitor.visit_each_child(&mut cx, sf);
    }
    let func_node = func_cell.get().expect("function declaration not found");

    let (buf, _) = encode_node(&mut nodes, func_node, Some(sf));
    let (decoded, arena) = decode_nodes(&buf).unwrap();

    assert_eq!(arena[decoded].kind, Kind::FunctionDeclaration);
    let func_decl = arena[decoded].as_function_declaration();
    let name = func_decl.name.unwrap();
    assert_eq!(arena[name].as_identifier().text, "greet");
    assert_eq!(arena[decoded].parameters().unwrap().len(), 1);
    assert!(arena[decoded].body().is_some());
}

#[test]
fn test_decode_source_file_binary_expression() {
    let (sf, mut nodes) = parse_test_source_file("let x = 1 + 2;");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let decl_id = arena[arena[stmt].as_variable_statement().declaration_list.unwrap()]
        .as_variable_declaration_list()
        .declarations
        .as_ref()
        .unwrap()
        .nodes[0];
    let decl = arena[decl_id].as_variable_declaration();
    let bin_expr = arena[decl.initializer.unwrap()].as_binary_expression();
    let left = bin_expr.left.unwrap();
    let right = bin_expr.right.unwrap();
    assert!(bin_expr.operator_token.is_some());
    assert_eq!(arena[left].kind, Kind::NumericLiteral);
    assert_eq!(arena[right].kind, Kind::NumericLiteral);
}

#[test]
fn test_decode_source_file_keyword_expressions() {
    // "this" must decode as KeywordExpression, not Token, or the printer panics
    let (sf, mut nodes) = parse_test_source_file("const x = this;");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    // Navigate: const x = this -> VariableStatement -> declaration -> initializer
    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let decl_id = arena[arena[stmt].as_variable_statement().declaration_list.unwrap()]
        .as_variable_declaration_list()
        .declarations
        .as_ref()
        .unwrap()
        .nodes[0];
    let decl = arena[decl_id].as_variable_declaration();
    let this_expr = decl.initializer.unwrap();
    assert_eq!(arena[this_expr].kind, Kind::ThisKeyword);
    // This would panic if decoded as Token instead of KeywordExpression
    let _ = arena[this_expr].as_keyword_expression();
}

#[test]
fn test_decode_source_file_empty_module_block() {
    let (sf, mut nodes) = parse_test_source_file("namespace N { }");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    // Navigate: namespace N { } -> ModuleDeclaration -> ModuleBlock
    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let module = arena[stmt].as_module_declaration();
    let body = module.body_base.body.unwrap();
    let block = arena[body].as_module_block();
    // Statements must be non-nil even when empty, otherwise the printer panics
    let statements = block.statements.as_ref().unwrap();
    assert_eq!(statements.nodes.len(), 0);
}

#[test]
fn test_decode_source_file_empty_block_and_params() {
    // Empty blocks and parameter lists must decode with non-nil NodeLists (not nil),
    // matching parser behavior. Previously the decoder left them nil, crashing the printer.
    let (sf, mut nodes) = parse_test_source_file("function foo() {}");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let func = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    assert_eq!(arena[func].kind, Kind::FunctionDeclaration);
    assert!(
        arena[func].parameters().is_some(),
        "FunctionDeclaration.Parameters must be non-nil for foo()"
    );
    assert_eq!(arena[func].parameters().unwrap().len(), 0);
    let body = arena[func].body().unwrap();
    let block = arena[body].as_block();
    assert!(
        block.statements.is_some(),
        "Block.Statements must be non-nil for empty blocks"
    );
    assert_eq!(block.statements.as_ref().unwrap().nodes.len(), 0);
}

#[test]
fn test_decode_source_file_arrow_function_empty_params() {
    // `() => {}` must decode with non-nil Parameters (empty NodeList),
    // matching parser behavior. Previously the decoder left it nil, crashing the printer.
    let (sf, mut nodes) = parse_test_source_file("const f = () => {};");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let decl_id = arena[arena[stmt].as_variable_statement().declaration_list.unwrap()]
        .as_variable_declaration_list()
        .declarations
        .as_ref()
        .unwrap()
        .nodes[0];
    let arrow = arena[decl_id].as_variable_declaration().initializer.unwrap();
    assert!(
        arena[arrow].parameters().is_some(),
        "ArrowFunction.Parameters must be non-nil for () => {{}}"
    );
    assert_eq!(arena[arrow].parameters().unwrap().len(), 0);
    let body = arena[arrow].body().unwrap();
    let block = arena[body].as_block();
    assert!(
        block.statements.is_some(),
        "Block.Statements must be non-nil for empty body"
    );
    assert_eq!(block.statements.as_ref().unwrap().nodes.len(), 0);
}

#[test]
fn test_decode_source_file_function_expression_empty_params() {
    // `function() {}` must decode with non-nil Parameters (empty NodeList).
    let (sf, mut nodes) = parse_test_source_file("const f = function() {};");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[0];
    let decl_id = arena[arena[stmt].as_variable_statement().declaration_list.unwrap()]
        .as_variable_declaration_list()
        .declarations
        .as_ref()
        .unwrap()
        .nodes[0];
    let func_expr = arena[decl_id].as_variable_declaration().initializer.unwrap();
    assert!(
        arena[func_expr].parameters().is_some(),
        "FunctionExpression.Parameters must be non-nil for function() {{}}"
    );
    assert_eq!(arena[func_expr].parameters().unwrap().len(), 0);
}

#[test]
fn test_decode_source_file_postfix_unary_operator() {
    let (sf, mut nodes) = parse_test_source_file("let i = 0; i++;");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let expr_stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[1];
    let postfix = arena[arena[expr_stmt].as_expression_statement().expression.unwrap()]
        .as_postfix_unary_expression();
    assert_eq!(postfix.operator, Kind::PlusPlusToken);
    assert_eq!(arena[postfix.operand.unwrap()].kind, Kind::Identifier);
}

#[test]
fn test_decode_source_file_prefix_unary_operator() {
    let (sf, mut nodes) = parse_test_source_file("let x = true; !x;");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let expr_stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[1];
    let prefix = arena[arena[expr_stmt].as_expression_statement().expression.unwrap()]
        .as_prefix_unary_expression();
    assert_eq!(prefix.operator, Kind::ExclamationToken);
    assert_eq!(arena[prefix.operand.unwrap()].kind, Kind::Identifier);
}

#[test]
fn test_decode_source_file_postfix_decrement() {
    let (sf, mut nodes) = parse_test_source_file("let n = 5; n--;");
    let (decoded, arena) = round_trip(sf, &mut nodes);

    let expr_stmt = arena[decoded].as_source_file().statements.as_ref().unwrap().nodes[1];
    let postfix = arena[arena[expr_stmt].as_expression_statement().expression.unwrap()]
        .as_postfix_unary_expression();
    assert_eq!(postfix.operator, Kind::MinusMinusToken);
}

/// `BenchmarkDecodeSourceFile` — kept as an ignored single-iteration test.
#[test]
#[ignore]
fn bench_decode_source_file() {
    let file_content = std::fs::read_to_string(format!(
        "{}/fixtures/compiler/checker.ts",
        tsc_repo::test_data_path()
    ))
    .unwrap();
    let (source_file, mut nodes) = parse_source_file(
        test_parse_options("/checker.ts"),
        &file_content,
        ScriptKind::Ts,
    );
    let (buf, _) = encode_source_file(&mut nodes, source_file);

    // "parse" sub-benchmark.
    let _ = parse_source_file(test_parse_options("/checker.ts"), &file_content, ScriptKind::Ts);
    // "decode" sub-benchmark.
    let _ = decode_source_file(&buf).unwrap();
}
