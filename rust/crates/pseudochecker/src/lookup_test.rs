// Tests for the pseudochecker port (tsc/internal/pseudochecker).
//
// The binder is not yet ported, so `declaration_base.symbol` is never
// populated here; tests exercise the paths that only need `nodes` (plus an
// empty `symbols` arena). Parent links are wired with
// `set_parent_in_children`, which binding normally does.

use tsc_ast::ast::Node;
use tsc_ast::ids::NodeId;
use tsc_ast::kind_generated::Kind;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_ast::symbol::SymbolArena;
use tsc_ast::utilities::set_parent_in_children;
use tsc_core::scriptkind::ScriptKind;
use tsc_parser::parse_source_file;

use crate::checker::PseudoChecker;
use crate::lookup::is_in_const_context;
use crate::types::{PseudoObjectElementKind, PseudoTypeKind};

fn parse(source: &str) -> (NodeId, Vec<Node>) {
    let (file, mut nodes) =
        parse_source_file(SourceFileParseOptions::default(), source, ScriptKind::Ts);
    set_parent_in_children(&mut nodes, file);
    (file, nodes)
}

/// Finds the first node (in arena order) of `kind`.
fn find_first(nodes: &[Node], kind: Kind) -> NodeId {
    nodes
        .iter()
        .find(|n| n.kind == kind)
        .expect("expected node of given kind")
        .id
}

#[test]
fn expression_literal_kinds() {
    let (_file, nodes) = parse("null; undefined; true;");
    let ch = PseudoChecker::new(true, false);
    let symbols = SymbolArena::default();

    let null_expr = nodes
        .iter()
        .find(|n| n.kind == Kind::NullKeyword)
        .expect("null literal")
        .id;
    assert_eq!(
        ch.get_type_of_expression(null_expr, &nodes, &symbols)
            .kind(),
        PseudoTypeKind::Null
    );

    let undefined_expr = nodes
        .iter()
        .find(|n| n.kind == Kind::Identifier && n.as_identifier().text.as_ref() == "undefined")
        .expect("undefined identifier")
        .id;
    assert_eq!(
        ch.get_type_of_expression(undefined_expr, &nodes, &symbols)
            .kind(),
        PseudoTypeKind::Undefined
    );

    let true_expr = nodes
        .iter()
        .find(|n| n.kind == Kind::TrueKeyword)
        .expect("true literal")
        .id;
    let t = ch.get_type_of_expression(true_expr, &nodes, &symbols);
    assert_eq!(t.kind(), PseudoTypeKind::MaybeConstLocation);
    let mc = t.as_pseudo_type_maybe_const_location();
    assert_eq!(mc.const_type.kind(), PseudoTypeKind::True);
    assert_eq!(mc.regular_type.kind(), PseudoTypeKind::Boolean);
}

#[test]
fn numeric_literal_maybe_const_location() {
    let (_file, nodes) = parse("let x = 42;");
    let ch = PseudoChecker::new(true, false);
    let lit = find_first(&nodes, Kind::NumericLiteral);
    let t = ch.get_type_of_expression(lit, &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::MaybeConstLocation);
    let mc = t.as_pseudo_type_maybe_const_location();
    assert_eq!(mc.const_type.kind(), PseudoTypeKind::NumericLiteral);
    assert_eq!(mc.regular_type.kind(), PseudoTypeKind::Number);
}

#[test]
fn array_literal_const_context() {
    // Non-const array literal: error node is the array expression itself.
    let (_file, nodes) = parse("let a = [1, 2];");
    let ch = PseudoChecker::new(true, false);
    let arr = find_first(&nodes, Kind::ArrayLiteralExpression);
    assert!(!is_in_const_context(arr, &nodes));
    let t = ch.get_type_of_expression(arr, &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::Inferred);
    assert_eq!(t.as_pseudo_type_inferred().error_nodes, vec![arr]);

    // `as const` array literal: produces a tuple of element pseudotypes.
    let (_file, nodes) = parse("let a = [1, 2] as const;");
    let arr = find_first(&nodes, Kind::ArrayLiteralExpression);
    assert!(is_in_const_context(arr, &nodes));
    let t = ch.get_type_of_expression(arr, &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::Tuple);
    assert_eq!(t.as_pseudo_type_tuple().elements.len(), 2);
    // Elements keep their `MaybeConstLocation` wrappers; the const/regular
    // choice is deferred to the builder.
    let element = &t.as_pseudo_type_tuple().elements[0];
    assert_eq!(element.kind(), PseudoTypeKind::MaybeConstLocation);
    assert_eq!(
        element
            .as_pseudo_type_maybe_const_location()
            .const_type
            .kind(),
        PseudoTypeKind::NumericLiteral
    );
}

#[test]
fn object_literal_in_const_context() {
    let (_file, nodes) = parse("let o = { a: 1, b: 's' } as const;");
    let ch = PseudoChecker::new(true, false);
    let obj = find_first(&nodes, Kind::ObjectLiteralExpression);
    assert!(is_in_const_context(obj, &nodes));
    let t = ch.get_type_of_expression(obj, &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::ObjectLiteral);
    let elements = &t.as_pseudo_type_object_literal().elements;
    assert_eq!(elements.len(), 2);
    assert_eq!(
        elements[0].kind(),
        PseudoObjectElementKind::PropertyAssignment
    );
    assert!(!elements[0].optional);
}

#[test]
fn object_literal_with_spread_errors() {
    let (_file, nodes) = parse("const rest = { b: 2 }; let o = { a: 1, ...rest } as const;");
    let ch = PseudoChecker::new(true, false);
    // Find the object literal containing the spread (the second one).
    let obj = nodes
        .iter()
        .filter(|n| n.kind == Kind::ObjectLiteralExpression)
        .nth(1)
        .expect("second object literal")
        .id;
    let spread = find_first(&nodes, Kind::SpreadAssignment);
    let t = ch.get_type_of_expression(obj, &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::Inferred);
    assert_eq!(t.as_pseudo_type_inferred().error_nodes, vec![spread]);
}

#[test]
fn arrow_function_single_call_signature() {
    let (_file, nodes) = parse("const f = (a: number, b = 1) => true;");
    let ch = PseudoChecker::new(true, false);
    let arrow = find_first(&nodes, Kind::ArrowFunction);
    let t = ch.get_type_of_expression(arrow, &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::SingleCallSignature);
    let sig = t.as_pseudo_type_single_call_signature();
    assert_eq!(sig.parameters.len(), 2);
    // `a: number` — annotated parameter gives a Direct pseudotype.
    assert_eq!(sig.parameters[0].type_.kind(), PseudoTypeKind::Direct);
    assert!(!sig.parameters[0].optional);
    // `b = 1` — initializer; inferred, and not optional in Go's terms only when
    // followed by required params (it's last, so optional).
    assert!(sig.parameters[1].optional);
    // Return type comes from the lone body expression.
    let rt = &sig.return_type;
    assert_eq!(rt.kind(), PseudoTypeKind::MaybeConstLocation);
    assert_eq!(
        rt.as_pseudo_type_maybe_const_location().const_type.kind(),
        PseudoTypeKind::True
    );
}

#[test]
fn function_declaration_return_type() {
    let (_file, nodes) = parse("function g(): number { return 1 } function h() { return 's' }");
    let ch = PseudoChecker::new(true, false);
    let fns: Vec<NodeId> = nodes
        .iter()
        .filter(|n| n.kind == Kind::FunctionDeclaration)
        .map(|n| n.id)
        .collect();
    // Annotated return type → Direct.
    let t = ch.get_return_type_of_signature(fns[0], &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::Direct);
    // Unannotated, single return → pseudotype of the expression.
    let t = ch.get_return_type_of_signature(fns[1], &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::MaybeConstLocation);
    assert_eq!(
        t.as_pseudo_type_maybe_const_location().const_type.kind(),
        PseudoTypeKind::StringLiteral
    );
}

#[test]
fn type_assertion_and_as_expression() {
    // `x as const` unwraps to the inner expression's pseudotype.
    let (_file, nodes) =
        parse("declare const s: string; const u = s as const; const v = s as any;");
    let ch = PseudoChecker::new(true, false);
    let as_const = nodes
        .iter()
        .find(|n| {
            n.kind == Kind::AsExpression
                && is_in_const_context(n.as_as_expression().expression.expect("expr"), &nodes)
        })
        .expect("as const expression")
        .id;
    let t = ch.get_type_of_expression(as_const, &nodes, &SymbolArena::default());
    // `s` is an identifier → Inferred.
    assert_eq!(t.kind(), PseudoTypeKind::Inferred);

    // `s as any` → Direct to the `any` type reference.
    let as_any = nodes
        .iter()
        .filter(|n| n.kind == Kind::AsExpression)
        .find(|n| n.id != as_const)
        .expect("as any expression")
        .id;
    let t = ch.get_type_of_expression(as_any, &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::Direct);
}

#[test]
fn declaration_without_symbol_is_no_result() {
    // PORT/deferral: `type_from_variable` requires `declaration.symbol` (set by
    // the binder); unbound declarations yield NoResult, mirroring Go's nil
    // symbol check.
    let (_file, nodes) = parse("let x = 42;");
    let ch = PseudoChecker::new(true, false);
    let decl = find_first(&nodes, Kind::VariableDeclaration);
    let t = ch.get_type_of_declaration(decl, &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::NoResult);
}

#[test]
fn parameter_and_property_declarations() {
    let (_file, nodes) = parse("class C { p: string = 'x'; q = 3; }");
    let ch = PseudoChecker::new(true, false);
    let props: Vec<NodeId> = nodes
        .iter()
        .filter(|n| n.kind == Kind::PropertyDeclaration)
        .map(|n| n.id)
        .collect();
    // Annotated property → Direct.
    let t = ch.get_type_of_declaration(props[0], &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::Direct);
    // `q = 3` — initializer; MaybeConstLocation since not contextually typed.
    let t = ch.get_type_of_declaration(props[1], &nodes, &SymbolArena::default());
    assert_eq!(t.kind(), PseudoTypeKind::MaybeConstLocation);
}
