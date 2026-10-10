//! Ported from tsc/internal/transformers/tstransforms/typeeraser_test.go
//! `TestTypeEraser` @ ec47d33c23e464a17cdf2475632cba629bee8763.
//!
//! Each case parses `input` as TS (or TSX when `jsx`), runs
//! `NewTypeEraserTransformer`, and asserts that `EmitSourceFile` produces
//! `output` exactly (modulo the trailing newline, which Go's `CheckEmit`
//! trims before comparing).
//!
//! PORT: Go's `parsetestutil.ParseTypeScript`/`CheckDiagnostics` map onto
//! `tsc_testutil::parsetestutil::{parse_typescript, check_diagnostics}`, and
//! `emittestutil.CheckEmit` is inlined as in `printer/tests/emit_test.rs`.

use std::cell::RefCell;
use std::rc::Rc;

use tsc_core::options_generated::{CompilerOptions, NewLineKind};
use tsc_core::tristate::TS_TRUE;
use tsc_printer::{EmitContext, PrintHandlers, Printer, PrinterOptions};
use tsc_testutil::parsetestutil;
use tsc_transformers::TransformOptions;
use tsc_transformers::tstransforms::new_type_eraser_transformer;

fn check_emit(
    title: &str,
    input: &str,
    expected: &str,
    jsx: bool,
    vms: bool,
) -> Result<(), String> {
    let (file, mut nodes) = parsetestutil::parse_typescript(input, jsx);
    parsetestutil::check_diagnostics(&nodes, file).map_err(|e| format!("{title}: {e}"))?;

    let mut compiler_options = CompilerOptions::default();
    if vms {
        compiler_options.verbatim_module_syntax = TS_TRUE;
    }
    let emit_context = Rc::new(RefCell::new(EmitContext::new()));
    let opts = TransformOptions {
        compiler_options: Some(&compiler_options),
        context: Some(emit_context.clone()),
        ..Default::default()
    };
    let transformer =
        new_type_eraser_transformer(&opts).expect("NewTypeEraserTransformer returned nil");
    let file = transformer
        .transform_source_file(&mut nodes, file)
        .expect("transformed SourceFile");

    let mut emit_context = emit_context.borrow_mut();
    let mut printer = Printer::new(
        PrinterOptions {
            new_line: NewLineKind::LF,
            ..Default::default()
        },
        PrintHandlers::default(),
        &mut emit_context,
        &mut nodes,
        &[],
    );
    let text = printer.emit_source_file(file);
    let actual = text.strip_suffix('\n').unwrap_or(&text);
    if actual != expected {
        return Err(format!(
            "{title}: input {input:?}\n  expected: {expected:?}\n  actual:   {actual:?}"
        ));
    }
    Ok(())
}

static DATA: &[(&str, &str, &str, bool, bool)] = &[
    (
        "Modifiers",
        "class C { public x; private y }",
        "class C {\n    x;\n    y;\n}",
        false,
        false,
    ),
    ("InterfaceDeclaration", "interface I { }", "", false, false),
    ("TypeAliasDeclaration", "type T = U;", "", false, false),
    (
        "NamespaceExportDeclaration",
        "export as namespace N;",
        "",
        false,
        false,
    ),
    (
        "UninstantiatedNamespace1",
        "namespace N {}",
        "",
        false,
        false,
    ),
    (
        "UninstantiatedNamespace2",
        "namespace N { export interface I {} }",
        "",
        false,
        false,
    ),
    (
        "UninstantiatedNamespace3",
        "namespace N { export type T = U; }",
        "",
        false,
        false,
    ),
    ("ExpressionWithTypeArguments", "F<T>", "F;", false, false),
    (
        "PropertyDeclaration1",
        "class C { declare x; }",
        "class C {\n}",
        false,
        false,
    ),
    (
        "PropertyDeclaration2",
        "class C { public x: number; }",
        "class C {\n    x;\n}",
        false,
        false,
    ),
    (
        "PropertyDeclaration3",
        "class C { public static x: number; }",
        "class C {\n    static x;\n}",
        false,
        false,
    ),
    (
        "ConstructorDeclaration1",
        "class C { constructor(); }",
        "class C {\n}",
        false,
        false,
    ),
    (
        "ConstructorDeclaration2",
        "class C { public constructor() {} }",
        "class C {\n    constructor() { }\n}",
        false,
        false,
    ),
    (
        "MethodDeclaration1",
        "class C { m(); }",
        "class C {\n}",
        false,
        false,
    ),
    (
        "MethodDeclaration2",
        "class C { public m<T>(): U {} }",
        "class C {\n    m() { }\n}",
        false,
        false,
    ),
    (
        "MethodDeclaration3",
        "class C { public static m<T>(): U {} }",
        "class C {\n    static m() { }\n}",
        false,
        false,
    ),
    (
        "GetAccessorDeclaration1",
        "class C { get m(); }",
        "class C {\n    get m() { }\n}",
        false,
        false,
    ),
    (
        "GetAccessorDeclaration2",
        "class C { public get m<T>(): U {} }",
        "class C {\n    get m() { }\n}",
        false,
        false,
    ),
    (
        "GetAccessorDeclaration3",
        "class C { public static get m<T>(): U {} }",
        "class C {\n    static get m() { }\n}",
        false,
        false,
    ),
    (
        "SetAccessorDeclaration1",
        "class C { set m(v); }",
        "class C {\n    set m(v) { }\n}",
        false,
        false,
    ),
    (
        "SetAccessorDeclaration2",
        "class C { public set m<T>(v): U {} }",
        "class C {\n    set m(v) { }\n}",
        false,
        false,
    ),
    (
        "SetAccessorDeclaration3",
        "class C { public static set m<T>(v): U {} }",
        "class C {\n    static set m(v) { }\n}",
        false,
        false,
    ),
    (
        "IndexSignature",
        "class C { [key: string]: number; }",
        "class C {\n}",
        false,
        false,
    ),
    ("VariableDeclaration1", "declare var a;", "", false, false),
    (
        "VariableDeclaration2",
        "var a: number",
        "var a;",
        false,
        false,
    ),
    (
        "HeritageClause",
        "class C implements I {}",
        "class C {\n}",
        false,
        false,
    ),
    ("ClassDeclaration1", "declare class C {}", "", false, false),
    (
        "ClassDeclaration2",
        "class C<T> {}",
        "class C {\n}",
        false,
        false,
    ),
    (
        "ClassExpression",
        "(class C<T> {})",
        "(class C {\n});",
        false,
        false,
    ),
    (
        "FunctionDeclaration1",
        "declare function f() {}",
        "",
        false,
        false,
    ),
    ("FunctionDeclaration2", "function f();", "", false, false),
    (
        "FunctionDeclaration3",
        "function f<T>(): U {}",
        "function f() { }",
        false,
        false,
    ),
    (
        "FunctionExpression",
        "(function f<T>(): U {})",
        "(function f() { });",
        false,
        false,
    ),
    (
        "ArrowFunction",
        "(<T>(): U => {})",
        "(() => { });",
        false,
        false,
    ),
    (
        "ParameterDeclaration",
        "function f(this: x, a: number, b?: boolean) {}",
        "function f(a, b) { }",
        false,
        false,
    ),
    ("CallExpression", "f<T>()", "f();", false, false),
    ("NewExpression1", "new f<T>()", "new f();", false, false),
    ("NewExpression2", "new f<T>", "new f;", false, false),
    ("TaggedTemplateExpression", "f<T>``", "f ``;", false, false),
    ("NonNullExpression", "x!", "x;", false, false),
    ("TypeAssertionExpression#1", "<T>x", "x;", false, false),
    (
        "TypeAssertionExpression#2",
        "(<T>x).c",
        "x.c;",
        false,
        false,
    ),
    ("AsExpression#1", "x as T", "x;", false, false),
    ("AsExpression#2", "(x as T).c", "x.c;", false, false),
    ("SatisfiesExpression#1", "x satisfies T", "x;", false, false),
    (
        "SatisfiesExpression#2",
        "(x satisfies T).c",
        "x.c;",
        false,
        false,
    ),
    ("JsxSelfClosingElement", "<x<T> />", "<x />;", true, false),
    ("JsxOpeningElement", "<x<T>></x>", "<x></x>;", true, false),
    (
        "ImportEqualsDeclaration#1",
        "import x = require(\"m\");",
        "import x = require(\"m\");",
        false,
        false,
    ),
    (
        "ImportEqualsDeclaration#2",
        "import type x = require(\"m\");",
        "",
        false,
        false,
    ),
    (
        "ImportEqualsDeclaration#3",
        "import x = y;",
        "import x = y;",
        false,
        false,
    ),
    (
        "ImportEqualsDeclaration#4",
        "import type x = y;",
        "",
        false,
        false,
    ),
    (
        "ImportDeclaration#1",
        "import \"m\";",
        "import \"m\";",
        false,
        false,
    ),
    (
        "ImportDeclaration#2",
        "import * as x from \"m\"; x;",
        "import * as x from \"m\";\nx;",
        false,
        false,
    ),
    (
        "ImportDeclaration#3",
        "import x from \"m\"; x;",
        "import x from \"m\";\nx;",
        false,
        false,
    ),
    (
        "ImportDeclaration#4",
        "import { x } from \"m\"; x;",
        "import { x } from \"m\";\nx;",
        false,
        false,
    ),
    (
        "ImportDeclaration#5",
        "import type * as x from \"m\";",
        "",
        false,
        false,
    ),
    (
        "ImportDeclaration#6",
        "import type x from \"m\";",
        "",
        false,
        false,
    ),
    (
        "ImportDeclaration#7",
        "import type { x } from \"m\";",
        "",
        false,
        false,
    ),
    (
        "ImportDeclaration#8",
        "import { type x } from \"m\";",
        "",
        false,
        false,
    ),
    (
        "ImportDeclaration#9",
        "import { type x } from \"m\";",
        "import {} from \"m\";",
        false,
        true,
    ),
    (
        "ExportDeclaration#1",
        "export * from \"m\";",
        "export * from \"m\";",
        false,
        false,
    ),
    (
        "ExportDeclaration#2",
        "export * as x from \"m\";",
        "export * as x from \"m\";",
        false,
        false,
    ),
    (
        "ExportDeclaration#3",
        "export { x } from \"m\";",
        "export { x } from \"m\";",
        false,
        false,
    ),
    (
        "ExportDeclaration#4",
        "export type * from \"m\";",
        "",
        false,
        false,
    ),
    (
        "ExportDeclaration#5",
        "export type * as x from \"m\";",
        "",
        false,
        false,
    ),
    (
        "ExportDeclaration#6",
        "export type { x } from \"m\";",
        "",
        false,
        false,
    ),
    (
        "ExportDeclaration#7",
        "export { type x } from \"m\";",
        "",
        false,
        false,
    ),
    // NOTE: the Go table contains a duplicate "ExportDeclaration#7" entry (the
    // verbatim-module-syntax variant below); the duplicate title is kept for
    // fidelity.
    (
        "ExportDeclaration#7",
        "export { type x } from \"m\";",
        "export {} from \"m\";",
        false,
        true,
    ),
];

#[test]
fn tstransforms_type_eraser() {
    let mut failures = Vec::new();
    for (title, input, expected, jsx, vms) in DATA {
        if let Err(e) = check_emit(title, input, expected, *jsx, *vms) {
            failures.push(e);
        }
    }
    if !failures.is_empty() {
        panic!("{} emit failures:\n{}", failures.len(), failures.join("\n"));
    }
}
