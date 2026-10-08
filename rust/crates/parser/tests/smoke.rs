use tsc_ast::kind_generated::Kind;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::scriptkind::ScriptKind;
use tsc_parser::parse_source_file;

fn opts(name: &str) -> SourceFileParseOptions {
    SourceFileParseOptions {
        file_name: tsc_tspath::rooted_file_path_from_normalized(&format!("/{}", name)),
        path_key: tsc_tspath::PathKey::from(format!("/{}", name)),
        external_module_indicator_options: Default::default(),
    }
}

#[test]
fn parses_variable_statement() {
    let src = "let x = 1 + 2;\n";
    let (file, nodes) = parse_source_file(opts("a.ts"), src, ScriptKind::Ts);
    assert_eq!(nodes[file].kind, Kind::SourceFile);
    let stmts = nodes[file].statements().expect("statements");
    assert_eq!(stmts.len(), 1);
    assert_eq!(nodes[stmts[0]].kind, Kind::VariableStatement);
}

#[test]
fn parses_function_declaration() {
    let src = "function f(a: number, b: string): boolean { return a > 0 && b !== ''; }\n";
    let (file, nodes) = parse_source_file(opts("b.ts"), src, ScriptKind::Ts);
    let stmts = nodes[file].statements().expect("statements");
    assert_eq!(nodes[stmts[0]].kind, Kind::FunctionDeclaration);
}

#[test]
fn parses_class_with_members() {
    let src = "class C<T> extends B { x: T = 0; m<U>(u: U): T { return this.x; } }\n";
    let (file, nodes) = parse_source_file(opts("c.ts"), src, ScriptKind::Ts);
    let stmts = nodes[file].statements().expect("statements");
    assert_eq!(nodes[stmts[0]].kind, Kind::ClassDeclaration);
}

#[test]
fn parses_import_export() {
    let src = "import { a } from 'm'; export default a;\n";
    let (file, nodes) = parse_source_file(opts("d.ts"), src, ScriptKind::Ts);
    let stmts = nodes[file].statements().expect("statements");
    assert_eq!(nodes[stmts[0]].kind, Kind::ImportDeclaration);
    assert_eq!(nodes[stmts[1]].kind, Kind::ExportAssignment);
}

#[test]
fn parses_json() {
    let src = "{ \"a\": 1, \"b\": [true, null] }\n";
    let (file, nodes) = parse_source_file(opts("e.json"), src, ScriptKind::Json);
    assert_eq!(nodes[file].kind, Kind::SourceFile);
}

#[test]
fn parses_jsx() {
    let src = "const el = <div a={1}>hi<span/></div>;\n";
    let (file, nodes) = parse_source_file(opts("f.tsx"), src, ScriptKind::Tsx);
    let stmts = nodes[file].statements().expect("statements");
    assert_eq!(nodes[stmts[0]].kind, Kind::VariableStatement);
}

#[test]
fn parses_arrow_and_generics() {
    let src = "const f = <T>(x: T): T => x; const g = async () => await p;\n";
    let (file, nodes) = parse_source_file(opts("g.ts"), src, ScriptKind::Ts);
    let stmts = nodes[file].statements().expect("statements");
    assert_eq!(stmts.len(), 2);
}

#[test]
fn parses_jsdoc_in_js() {
    // In JS files JSDoc is parsed eagerly and @param/@returns/@type are
    // rehosted onto the declaration.
    let src = "/**\n * Add two.\n * @param {number} a first\n * @param {number} [b=1] second\n * @returns {number} sum\n */\nfunction add(a, b) { return a + b; }\n";
    let (file, nodes) = parse_source_file(opts("h.js"), src, ScriptKind::Js);
    let stmts = nodes[file].statements().expect("statements");
    assert_eq!(nodes[stmts[0]].kind, Kind::FunctionDeclaration);
    let params = nodes[stmts[0]].parameters().expect("parameters");
    assert_eq!(params.len(), 2);
    // @param {number} a — rehosted type annotation
    assert!(nodes[params[0]].type_().is_some());
    // @param {number} [b=1] — bracketed -> question token
    assert!(
        nodes[params[1]]
            .as_parameter_declaration()
            .question_token
            .is_some()
    );
    // @returns {number} — rehosted return type
    assert!(nodes[stmts[0]].type_().is_some());
}

#[test]
fn parses_jsdoc_typedef_in_js() {
    let src = "/**\n * @typedef {Object} Point\n * @property {number} x\n * @property {number} y\n */\nvar p;\n";
    let (file, nodes) = parse_source_file(opts("i.js"), src, ScriptKind::Js);
    let stmts = nodes[file].statements().expect("statements");
    // var statement plus the reparsed JSTypeAliasDeclaration in the reparse list
    assert!(
        stmts
            .iter()
            .any(|&s| nodes[s].kind == Kind::JSTypeAliasDeclaration)
    );
}

#[test]
fn parses_jsdoc_lazy_in_ts() {
    // TS files defer JSDoc; the node carries HasJSDoc and lazy parse works.
    let src = "/** doc */\nconst x = 1;\n";
    let (file, mut nodes) = parse_source_file(opts("j.ts"), src, ScriptKind::Ts);
    let stmts = nodes[file].statements().expect("statements").to_vec();
    // withJSDoc wraps the VariableStatement — HAS_JSDOC lands there.
    let jsdoc = tsc_ast::ast::js_doc(&mut nodes, stmts[0], Some(file));
    assert!(!jsdoc.is_empty());
    assert_eq!(nodes[jsdoc[0]].kind, Kind::JSDoc);
}
