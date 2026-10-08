// Ported from the parts of tsc/internal/ast/utilities.go needed by the
// generated AST and subtree-facts code @ ec47d33c23e464a17cdf2475632cba629bee8763.
//
// Only the helpers referenced by the AST core live here — modifier-flag
// rollup, identifier/import-call predicates used by subtree facts, and the
// binding/assignment-pattern machinery behind `ContainsObjectRestOrSpread`.
// The remaining ~4000 lines of utilities.go port alongside the checker.

use crate::ast::Node;
use crate::ast_generated::{
    is_array_literal_expression, is_binary_expression, is_call_expression,
    is_identifier, is_meta_property, is_object_literal_expression,
    is_private_identifier, is_property_assignment, is_shorthand_property_assignment,
    is_spread_assignment, is_spread_element,
};
use crate::ids::NodeId;
use crate::kind_generated::Kind;
use crate::modifierflags::ModifierFlags;
use crate::subtreefacts::SubtreeFacts;

/// `ModifierToFlag(token)`.
pub fn modifier_to_flag(token: Kind) -> ModifierFlags {
    match token {
        Kind::StaticKeyword => ModifierFlags::STATIC,
        Kind::PublicKeyword => ModifierFlags::PUBLIC,
        Kind::ProtectedKeyword => ModifierFlags::PROTECTED,
        Kind::PrivateKeyword => ModifierFlags::PRIVATE,
        Kind::AbstractKeyword => ModifierFlags::ABSTRACT,
        Kind::AccessorKeyword => ModifierFlags::ACCESSOR,
        Kind::ExportKeyword => ModifierFlags::EXPORT,
        Kind::DeclareKeyword => ModifierFlags::AMBIENT,
        Kind::ConstKeyword => ModifierFlags::CONST,
        Kind::DefaultKeyword => ModifierFlags::DEFAULT,
        Kind::AsyncKeyword => ModifierFlags::ASYNC,
        Kind::ReadonlyKeyword => ModifierFlags::READONLY,
        Kind::OverrideKeyword => ModifierFlags::OVERRIDE,
        Kind::InKeyword => ModifierFlags::IN,
        Kind::OutKeyword => ModifierFlags::OUT,
        Kind::Decorator => ModifierFlags::DECORATOR,
        _ => ModifierFlags::NONE,
    }
}

/// `ModifiersToFlags(modifiers)` — rolls up a modifier node list.
pub fn modifiers_to_flags(modifiers: &[NodeId], nodes: &[Node]) -> ModifierFlags {
    let mut flags = ModifierFlags::NONE;
    for &modifier in modifiers {
        flags |= modifier_to_flag(nodes[modifier].kind);
    }
    flags
}

/// `HasSyntacticModifier(node, flags)`.
pub fn has_syntactic_modifier(node: &Node, flags: ModifierFlags) -> bool {
    node.modifier_flags().intersects(flags)
}

/// `IsThisIdentifier(node)`.
pub fn is_this_identifier(node: &Node) -> bool {
    is_identifier(node) && node.as_identifier().text == "this"
}

/// `isImportMetaProperty(node, name)`.
fn is_import_meta_property(node: &Node, nodes: &[Node], name: &str) -> bool {
    is_meta_property(node)
        && node.as_meta_property().keyword_token == Kind::ImportKeyword
        && node
            .name()
            .is_some_and(|n| nodes[n].text(nodes) == name)
}

/// `IsImportDeferMetaProperty(node)`.
pub fn is_import_defer_meta_property(node: &Node, nodes: &[Node]) -> bool {
    is_import_meta_property(node, nodes, "defer")
}

/// `IsImportSourceMetaProperty(node)`.
pub fn is_import_source_meta_property(node: &Node, nodes: &[Node]) -> bool {
    is_import_meta_property(node, nodes, "source")
}

/// `IsImportPhaseMetaProperty(node)`.
pub fn is_import_phase_meta_property(node: &Node, nodes: &[Node]) -> bool {
    is_import_defer_meta_property(node, nodes) || is_import_source_meta_property(node, nodes)
}

/// `IsImportCall(node)`.
pub fn is_import_call(node: &Node, nodes: &[Node]) -> bool {
    if !is_call_expression(node) {
        return false;
    }
    let Some(e) = node.expression() else {
        return false;
    };
    nodes[e].kind == Kind::ImportKeyword || is_import_phase_meta_property(&nodes[e], nodes)
}

/// `SkipPartiallyEmittedExpressions(node)`.
pub fn skip_partially_emitted_expressions(mut node: NodeId, nodes: &[Node]) -> NodeId {
    while nodes[node].kind == Kind::PartiallyEmittedExpression {
        match nodes[node].as_partially_emitted_expression().expression {
            Some(inner) => node = inner,
            None => break,
        }
    }
    node
}

/// `isLeftHandSideExpressionKind(kind)` — the kind-only check used by
/// `IsLeftHandSideExpression` (utilities.go).
pub fn is_left_hand_side_expression_kind(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::PropertyAccessExpression
            | Kind::ElementAccessExpression
            | Kind::NewExpression
            | Kind::CallExpression
            | Kind::JsxElement
            | Kind::JsxSelfClosingElement
            | Kind::JsxFragment
            | Kind::TaggedTemplateExpression
            | Kind::ArrayLiteralExpression
            | Kind::ParenthesizedExpression
            | Kind::ObjectLiteralExpression
            | Kind::ClassExpression
            | Kind::FunctionExpression
            | Kind::Identifier
            | Kind::PrivateIdentifier
            | Kind::RegularExpressionLiteral
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::StringLiteral
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::TemplateExpression
            | Kind::FalseKeyword
            | Kind::NullKeyword
            | Kind::ThisKeyword
            | Kind::TrueKeyword
            | Kind::SuperKeyword
            | Kind::NonNullExpression
            | Kind::ExpressionWithTypeArguments
            | Kind::MetaProperty
            | Kind::ImportKeyword
            | Kind::MissingDeclaration
    )
}

/// `IsLeftHandSideExpression(node)` — kind-only determination.
pub fn is_left_hand_side_expression(node: &Node, nodes: &[Node]) -> bool {
    is_left_hand_side_expression_kind(nodes[skip_partially_emitted_expressions(node.id, nodes)].kind)
}

/// `IsAssignmentExpression(node, excludeCompoundAssignment)`.
pub fn is_assignment_expression(node: &Node, nodes: &[Node], exclude_compound_assignment: bool) -> bool {
    if node.kind != Kind::BinaryExpression {
        return false;
    }
    let expr = node.as_binary_expression();
    let Some(token) = expr.operator_token else {
        return false;
    };
    let op = nodes[token].kind;
    (op == Kind::EqualsToken || (!exclude_compound_assignment && op.is_assignment_operator()))
        && expr
            .left
            .is_some_and(|l| is_left_hand_side_expression(&nodes[l], nodes))
}

/// `IsAssignmentPattern(node)` — a `= ...` target at a binding/assignment
/// element position is an object or array literal.
pub fn is_assignment_pattern(node: &Node) -> bool {
    is_array_literal_expression(node) || is_object_literal_expression(node)
}

/// `IsDeclarationBindingElement(bindingElement)`.
pub fn is_declaration_binding_element(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::VariableDeclaration | Kind::Parameter | Kind::BindingElement
    )
}

/// `IsObjectLiteralElement(node)`.
pub fn is_object_literal_element(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::PropertyAssignment
            | Kind::ShorthandPropertyAssignment
            | Kind::SpreadAssignment
            | Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor
    )
}

/// `GetElementsOfBindingOrAssignmentPattern(name)`.
pub fn get_elements_of_binding_or_assignment_pattern(node: &Node) -> &[NodeId] {
    match node.kind {
        Kind::ObjectBindingPattern | Kind::ArrayBindingPattern | Kind::ArrayLiteralExpression => {
            node.element_list().map(|l| l.nodes()).unwrap_or(&[])
        }
        Kind::ObjectLiteralExpression => node.property_list().map(|l| l.nodes()).unwrap_or(&[]),
        _ => &[],
    }
}

/// `GetTargetOfBindingOrAssignmentElement(bindingElement)` — `None` for
/// Go's nil result.
pub fn get_target_of_binding_or_assignment_element(
    binding_element: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    let el = &nodes[binding_element];
    if is_declaration_binding_element(el) {
        return el.name();
    }
    if is_object_literal_element(el) {
        match el.kind {
            Kind::PropertyAssignment => {
                return el.initializer().and_then(|i| {
                    get_target_of_binding_or_assignment_element(i, nodes)
                });
            }
            Kind::ShorthandPropertyAssignment => return el.name(),
            Kind::SpreadAssignment => {
                return el.expression().and_then(|e| {
                    get_target_of_binding_or_assignment_element(e, nodes)
                });
            }
            _ => return None, // no target
        }
    }
    if is_assignment_expression(el, nodes, true /* exclude_compound_assignment */) {
        return el
            .as_binary_expression()
            .left
            .and_then(|l| get_target_of_binding_or_assignment_element(l, nodes));
    }
    if is_spread_element(el) {
        return el
            .expression()
            .and_then(|e| get_target_of_binding_or_assignment_element(e, nodes));
    }
    Some(binding_element)
}

/// `ContainsObjectRestOrSpread(node)` — does the subtree contain a
/// `{...x}` object rest/spread that is relevant to an assignment target.
pub fn contains_object_rest_or_spread(node: &Node, nodes: &[Node]) -> bool {
    let facts = node.subtree_facts(nodes);
    if facts.intersects(SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD) {
        return true;
    }
    if facts.intersects(SubtreeFacts::CONTAINS_ES_OBJECT_REST_OR_SPREAD) {
        // check for nested spread assignments, otherwise
        // '{ x: { a, ...b } = foo } = c' will not be correctly interpreted
        // by the rest/spread transformer
        for &element in get_elements_of_binding_or_assignment_pattern(node) {
            let Some(target) = get_target_of_binding_or_assignment_element(element, nodes) else {
                continue;
            };
            if is_assignment_pattern(&nodes[target]) {
                let tfacts = nodes[target].subtree_facts(nodes);
                if tfacts.intersects(SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD) {
                    return true;
                }
                if tfacts.intersects(SubtreeFacts::CONTAINS_ES_OBJECT_REST_OR_SPREAD)
                    && contains_object_rest_or_spread(&nodes[target], nodes)
                {
                    return true;
                }
            }
        }
    }
    false
}

/// `IsMethodOrAccessor(node)` — used by
/// `IsPrivateIdentifierClassElementDeclaration`.
pub fn is_method_or_accessor(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::MethodDeclaration | Kind::GetAccessor | Kind::SetAccessor
    )
}

/// `IsPrivateIdentifierClassElementDeclaration(node)`.
pub fn is_private_identifier_class_element_declaration(node: &Node, nodes: &[Node]) -> bool {
    (crate::ast_generated::is_property_declaration(node) || is_method_or_accessor(node))
        && node
            .name()
            .is_some_and(|n| is_private_identifier(&nodes[n]))
}
