// Ported from tsc/internal/transformers/declarations/util.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Small predicates and flag helpers shared by the declaration transformer.
//
// PORT: Go `*ast.Node` parameters become `NodeId` plus the `&[Node]` arena.
// `resolver` parameters take `&dyn EmitResolver` — the same trait the
// checker-side emit resolver implements.

use tsc_ast::{self as ast, Kind, ModifierFlags, Node, NodeId, SymbolArena};
use tsc_printer::EmitContext;
use tsc_printer::EmitResolver;

/// `needsScopeMarker(result)` — a statement that does not make a scope
/// `export {}` marker unnecessary.
pub(crate) fn needs_scope_marker(result: &Node, nodes: &[Node]) -> bool {
    !ast::is_any_import_or_re_export(result)
        && !ast::is_export_assignment(result)
        && !ast::has_syntactic_modifier(result, ModifierFlags::EXPORT)
        && !ast::is_ambient_module(result, nodes)
}

/// `canHaveLiteralInitializer(resolver, node)`.
pub(crate) fn can_have_literal_initializer(
    resolver: &dyn EmitResolver,
    node: NodeId,
    nodes: &[Node],
) -> bool {
    match nodes[node].kind {
        Kind::PropertyDeclaration | Kind::PropertySignature => resolver
            .get_effective_declaration_flags(node, ModifierFlags::PRIVATE, nodes)
            .is_empty(),
        Kind::Parameter | Kind::VariableDeclaration => true,
        _ => false,
    }
}

/// `canProduceDiagnostics(node)`.
pub(crate) fn can_produce_diagnostics(node: &Node) -> bool {
    ast::is_variable_declaration(node)
        || ast::is_property_declaration(node)
        || ast::is_property_signature_declaration(node)
        || ast::is_binding_element(node)
        || ast::is_set_accessor_declaration(node)
        || ast::is_get_accessor_declaration(node)
        || ast::is_construct_signature_declaration(node)
        || ast::is_call_signature_declaration(node)
        || ast::is_method_declaration(node)
        || ast::is_method_signature_declaration(node)
        || ast::is_function_declaration(node)
        || ast::is_parameter_declaration(node)
        || ast::is_type_parameter_declaration(node)
        || ast::is_expression_with_type_arguments(node)
        || ast::is_import_equals_declaration(node)
        || ast::is_type_alias_declaration(node)
        || ast::is_js_type_alias_declaration(node)
        || ast::is_constructor_declaration(node)
        || ast::is_index_signature_declaration(node)
        || ast::is_property_access_expression(node)
        || ast::is_element_access_expression(node)
        || ast::is_binary_expression(node)
        || ast::is_call_expression(node)
    // || // !!! TODO: JSDoc support
    /* ast.IsJSDocTypeAlias(node); */
}

/// `canReuseModifierNodes(nodes)` — reparsed modifiers (e.g. JS modifiers
/// added by the reparsing pass) cannot be reused verbatim.
pub(crate) fn can_reuse_modifier_nodes(list: &[NodeId], nodes: &[Node]) -> bool {
    for &node in list {
        if ast::is_modifier(&nodes[node]) && nodes[node].flags.intersects(ast::NodeFlags::REPARSED)
        {
            return false;
        }
    }
    true
}

/// `isDeclarationAndNotVisible(emitContext, resolver, node)`.
pub(crate) fn is_declaration_and_not_visible(
    emit_context: &EmitContext,
    resolver: &dyn EmitResolver,
    node: NodeId,
    nodes: &[Node],
) -> bool {
    // PORT: Go's `ParseNode` can return nil; the Rust version returns `Option`.
    // The Go code then unconditionally reads `node.Kind`, so nil would panic —
    // keep the synthesized node here instead so synthesized inputs fall
    // through to `false` rather than crashing.
    let node = emit_context.parse_node(nodes, node).unwrap_or(node);
    match nodes[node].kind {
        Kind::FunctionDeclaration
        | Kind::ModuleDeclaration
        | Kind::InterfaceDeclaration
        | Kind::ClassDeclaration
        | Kind::TypeAliasDeclaration
        | Kind::JSTypeAliasDeclaration
        | Kind::EnumDeclaration => !resolver.is_declaration_visible(node, nodes),
        // The following should be doing their own visibility checks based on filtering their members
        Kind::VariableDeclaration => !get_binding_name_visible(resolver, node, nodes),
        Kind::ImportEqualsDeclaration
        | Kind::ImportDeclaration
        | Kind::JSImportDeclaration
        | Kind::ExportDeclaration
        | Kind::ExportAssignment => false,
        Kind::ClassStaticBlockDeclaration => true,
        _ => false,
    }
}

/// `getBindingNameVisible(resolver, elem)`.
pub(crate) fn get_binding_name_visible(
    resolver: &dyn EmitResolver,
    elem: NodeId,
    nodes: &[Node],
) -> bool {
    if ast::is_omitted_expression(&nodes[elem]) {
        return false;
    }
    // TODO: parseArrayBindingElement _never_ parses out an OmittedExpression anymore, instead producing a nameless binding element
    // Audit if OmittedExpression should be removed
    let Some(name) = nodes[elem].name() else {
        return false;
    };
    if ast::is_binding_pattern(&nodes[name]) {
        // If any child binding pattern element has been marked visible (usually by collect linked aliases), then this is visible
        if let Some(elements) = nodes[name].elements() {
            for &elem in elements {
                if get_binding_name_visible(resolver, elem, nodes) {
                    return true;
                }
            }
        }
        false
    } else {
        resolver.is_declaration_visible(elem, nodes)
    }
}

/// `isEnclosingDeclaration(node)`.
pub(crate) fn is_enclosing_declaration(node: &Node, nodes: &[Node]) -> bool {
    ast::is_source_file(node)
        || ast::is_type_alias_declaration(node)
        || ast::is_js_type_alias_declaration(node)
        || ast::is_module_declaration(node)
        || ast::is_class_declaration(node)
        || ast::is_interface_declaration(node)
        || ast::is_function_like(Some(node.id), nodes)
        || ast::is_index_signature_declaration(node)
        || ast::is_mapped_type_node(node)
        || ast::is_variable_declaration(node)
}

/// `isAlwaysType(node)` — interfaces are always emitted as types (never
/// `declare`'d).
pub(crate) fn is_always_type(node: &Node) -> bool {
    node.kind == Kind::InterfaceDeclaration
}

/// `maskModifierFlags(node, modifierMask, modifierAdditions)`.
pub(crate) fn mask_modifier_flags(
    node: NodeId,
    modifier_mask: ModifierFlags,
    modifier_additions: ModifierFlags,
    nodes: &[Node],
) -> ModifierFlags {
    let mut flags =
        (ast::get_combined_modifier_flags(node, nodes) & modifier_mask) | modifier_additions;
    if flags.intersects(ModifierFlags::DEFAULT) && !flags.intersects(ModifierFlags::EXPORT) {
        // A non-exported default is a nonsequitor - we usually try to remove all export modifiers
        // from statements in ambient declarations; but a default export must retain its export modifier to be syntactically valid
        flags = ModifierFlags(flags.0 ^ ModifierFlags::EXPORT.0);
    }
    if flags.intersects(ModifierFlags::DEFAULT) && flags.intersects(ModifierFlags::AMBIENT) {
        // `declare` is never required alongside `default` (and would be an error if printed)
        flags = ModifierFlags(flags.0 ^ ModifierFlags::AMBIENT.0);
    }
    flags
}

/// `unwrapParenthesizedExpression(o)`.
pub(crate) fn unwrap_parenthesized_expression(mut o: NodeId, nodes: &[Node]) -> NodeId {
    while nodes[o].kind == Kind::ParenthesizedExpression {
        o = nodes[o]
            .expression()
            .expect("ParenthesizedExpression.expression");
    }
    o
}

/// `isPrivateMethodTypeParameter(resolver, node)`.
pub(crate) fn is_private_method_type_parameter(
    resolver: &dyn EmitResolver,
    node: NodeId,
    nodes: &[Node],
) -> bool {
    nodes[node].parent.is_some_and(|p| {
        nodes[p].kind == Kind::MethodDeclaration
            && !resolver
                .get_effective_declaration_flags(p, ModifierFlags::PRIVATE, nodes)
                .is_empty()
    })
}

/// `shouldEmitFunctionProperties(input)` — expando properties are emitted
/// for a function if any overload in the symbol has a body (implementation).
pub(crate) fn should_emit_function_properties(
    input: NodeId,
    nodes: &[Node],
    symbols: &SymbolArena,
) -> bool {
    if nodes[input]
        .as_function_declaration()
        .function_like_with_body_base
        .body_base
        .body
        .is_some()
    {
        return true;
    }
    let Some(symbol) = nodes[input].symbol() else {
        // Go: `input.Symbol.Declarations` on a nil Symbol would panic; treat a
        // missing symbol as "no body-bearing overload" (emit properties).
        return true;
    };
    !tsc_core::core::every(&symbols[symbol.index()].declarations, |decl| {
        !ast::is_function_declaration(&nodes[*decl])
            || nodes[*decl]
                .as_function_declaration()
                .function_like_with_body_base
                .body_base
                .body
                .is_none()
    })
}

/// `getEffectiveBaseTypeNode(node)` — the `extends` clause element of a
/// class, if any.
pub(crate) fn get_effective_base_type_node(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let base_type = ast::get_class_extends_heritage_element(&nodes[node], nodes);
    // !!! TODO: JSDoc support
    // if (baseType && isInJSFile(node)) {
    //     // Prefer an @augments tag because it may have type parameters.
    //     const tag = getJSDocAugmentsTag(node);
    //     if (tag) {
    //         return tag.class;
    //     }
    // }
    base_type
}

/// `isScopeMarker(node)` — `export =` or `export {}` mark a scope so no
/// fix-up marker is needed.
pub(crate) fn is_scope_marker(node: &Node) -> bool {
    ast::is_export_assignment(node) || ast::is_export_declaration(node)
}

/// `hasScopeMarker(statements)`.
pub(crate) fn has_scope_marker(statements: Option<&ast::NodeList>, nodes: &[Node]) -> bool {
    let Some(statements) = statements else {
        return false;
    };
    tsc_core::core::some(&statements.nodes, |n| is_scope_marker(&nodes[*n]))
}
