// Ported from tsc/internal/ast/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORTING NOTES:
// - `*Node` parameters map to `&Node` (non-nullable), `NodeId` (non-nullable
//   but arena access needed), or `Option<NodeId>` (Go's nullable `*Node`).
// - `[]*Node` parameters map to `&[NodeId]`; `*NodeList` maps to
//   `Option<&NodeList>` / `Option<NodeList>` depending on ownership.
// - Symbol tables (`SymbolTable`) are `OrderedMap`s that are always
//   initialized in this port — `GetSymbolTable`/`GetMembers`/`GetExports`/
//   `GetLocals` therefore just return the field instead of lazily allocating.
// - `GetNodeId` returns the `NodeId` assigned at arena insertion; Go's lazy
//   atomic id assignment does not exist here.
// - `sync.Pool`-backed closures (e.g. in `SetParentInChildren`) are plain
//   local helpers.
// - `ForEachChild`-driven traversal that mutates the arena collects child
//   `NodeId`s into a `Vec` first, because the traversal borrows the arena
//   immutably while the body needs `&mut` access.
// - `TextPos`/`TextRange` come from `tsc_core`; equality against
//   `TextRange::new(-1, -1)` mirrors `positionIsSynthesized`.
// - Go `Node.Parent` is `Option<NodeId>` here; unconditional Go dereferences
//   (`node.Parent.Kind`) become `unwrap()`/`expect()`, which panics on missing
//   parents exactly where Go would panic on a nil dereference.

use std::borrow::Cow;

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::options_generated::{
    CompilerOptions, JsxEmit, ModuleDetectionKind, ModuleKind, ModuleResolutionKind,
};
use tsc_core::text::{TextPos, TextRange};
use tsc_core::tristate::{Tristate, TS_TRUE, TS_UNKNOWN};
use tsc_tspath::{self as tspath, RootedFilePath};

use crate::ast::{ModifierList, Node, NodeList, SourceFileMetaData};
use crate::ast_generated::*;
use crate::ids::{NodeId, SymbolId};
use crate::kind_generated::Kind;
use crate::modifierflags::ModifierFlags;
use crate::nodeflags::NodeFlags;
use crate::subtreefacts::SubtreeFacts;
use crate::symbol::{
    is_ambient_module_symbol_name, try_get_ambient_module_name_from_symbol_name, Symbol,
    SymbolTable,
};

// Go's `Node.JSDoc` resolution (lazy `jsdocCache`) is not yet ported; helpers
// that depend on it are listed at the bottom of this file as PORT(deferred).

// ---------------------------------------------------------------------------
// Section 1: ids / symbol access

/// `GetNodeId(node)` — in this port the `NodeId` is assigned at arena
/// insertion, so this reads `node.id` instead of lazily allocating.
pub fn get_node_id(node: &Node) -> NodeId {
    node.id
}

/// `GetSymbolTable(data)` — `SymbolTable` is always allocated in this port, so
/// this simply returns the table rather than lazily initializing it.
pub fn get_symbol_table(data: &mut SymbolTable) -> &mut SymbolTable {
    data
}

/// `GetMembers(symbol)`.
pub fn get_members(symbol: &mut Symbol) -> &mut SymbolTable {
    get_symbol_table(&mut symbol.members)
}

/// `GetExports(symbol)`.
pub fn get_exports(symbol: &mut Symbol) -> &mut SymbolTable {
    get_symbol_table(&mut symbol.exports)
}

/// `GetLocals(node)`.
pub fn get_locals(node: &mut Node) -> Option<&mut SymbolTable> {
    node.data
        .locals_container_data_mut()
        .and_then(|data| data.locals.as_mut())
}

/// `NodeIsMissing(node)`.
pub fn node_is_missing(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_none_or(|n| {
        let node = &nodes[n];
        node.kind == Kind::MissingDeclaration
            || position_is_synthesized(node.loc.pos())
            || node.loc.pos() >= node.loc.end()
    })
}

/// `NodeIsPresent(node)`.
pub fn node_is_present(node: Option<NodeId>, nodes: &[Node]) -> bool {
    !node_is_missing(node, nodes)
}

/// `NodeIsSynthesized(node)` — in this port every node has a `loc`, so this is
/// just the range check.
pub fn node_is_synthesized(node: &Node) -> bool {
    range_is_synthesized(node.loc)
}

/// `RangeIsSynthesized(range)`.
pub fn range_is_synthesized(range: TextRange) -> bool {
    position_is_synthesized(range.pos()) || position_is_synthesized(range.end())
}

/// `PositionIsSynthesized(pos)`.
pub fn position_is_synthesized(pos: TextPos) -> bool {
    pos < TextPos(0)
}

/// `FindLastVisibleNode(nodes)`.
pub fn find_last_visible_node(list: &[NodeId], nodes: &[Node]) -> Option<NodeId> {
    for &node in list.iter().rev() {
        if !node_is_missing(Some(node), nodes) {
            return Some(node);
        }
    }
    None
}

/// `NodeKindIs(node, kinds...)`.
pub fn node_kind_is(node: &Node, kinds: &[Kind]) -> bool {
    kinds.contains(&node.kind)
}

// ---------------------------------------------------------------------------
// Section 3: modifiers / assignment

/// `IsModifier(node)`.
pub fn is_modifier(node: &Node) -> bool {
    node.kind.is_modifier_kind()
}

/// `IsModifierLike(node)`.
pub fn is_modifier_like(node: &Node) -> bool {
    is_modifier(node) || is_decorator(node)
}

/// `IsCompoundAssignment(token)`.
pub fn is_compound_assignment(token: Kind) -> bool {
    token.is_compound_assignment_operator()
}

/// `IsAssignmentExpression(node, excludeCompoundAssignment)`.
pub fn is_assignment_expression(
    node: &Node,
    nodes: &[Node],
    exclude_compound_assignment: bool,
) -> bool {
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

/// `GetRightMostAssignedExpression(node)`.
pub fn get_right_most_assigned_expression(mut node: NodeId, nodes: &[Node]) -> NodeId {
    while is_assignment_expression(&nodes[node], nodes, false /* exclude_compound_assignment */) {
        node = nodes[node].as_binary_expression().right.unwrap();
    }
    node
}

/// `IsDestructuringAssignment(node)`.
pub fn is_destructuring_assignment(node: &Node, nodes: &[Node]) -> bool {
    if is_assignment_expression(node, nodes, true /* exclude_compound_assignment */) {
        let kind = nodes[node.as_binary_expression().left.unwrap()].kind;
        return kind == Kind::ObjectLiteralExpression || kind == Kind::ArrayLiteralExpression;
    }
    false
}

/// `IsObjectBindingOrAssignmentElement(node)`.
pub fn is_object_binding_or_assignment_element(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::BindingElement
            | Kind::PropertyAssignment
            | Kind::ShorthandPropertyAssignment
            | Kind::SpreadAssignment
    )
}

/// `IsArrayBindingOrAssignmentElement(node)`.
pub fn is_array_binding_or_assignment_element(node: &Node, nodes: &[Node]) -> bool {
    matches!(
        node.kind,
        Kind::BindingElement
            | Kind::OmittedExpression
            | Kind::SpreadElement
            | Kind::ArrayLiteralExpression
            | Kind::ObjectLiteralExpression
            | Kind::Identifier
            | Kind::PropertyAccessExpression
            | Kind::ElementAccessExpression
    ) || is_assignment_expression(node, nodes, true /* exclude_compound_assignment */)
}

/// `IsBindingPattern(node)`.
pub fn is_binding_pattern(node: &Node) -> bool {
    node.kind == Kind::ObjectBindingPattern || node.kind == Kind::ArrayBindingPattern
}

/// `IsForInOrOfStatement(node)`.
pub fn is_for_in_or_of_statement(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| {
        matches!(nodes[n].kind, Kind::ForInStatement | Kind::ForOfStatement)
    })
}

/// `IsAssignmentTarget(node)`.
pub fn is_assignment_target(node: NodeId, nodes: &[Node]) -> bool {
    get_assignment_target(node, nodes).is_some()
}

/// `GetAssignmentTarget(node)`.
pub fn get_assignment_target(mut node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    loop {
        let parent = nodes[node]
            .parent
            .expect("nil parent in GetAssignmentTarget");
        let pn = &nodes[parent];
        match pn.kind {
            Kind::BinaryExpression => {
                let be = pn.as_binary_expression();
                if nodes[be.operator_token.unwrap()].kind.is_assignment_operator()
                    && be.left == Some(node)
                {
                    return Some(parent);
                }
                return None;
            }
            Kind::PrefixUnaryExpression => {
                let op = pn.as_prefix_unary_expression().operator;
                if op == Kind::PlusPlusToken || op == Kind::MinusMinusToken {
                    return Some(parent);
                }
                return None;
            }
            Kind::PostfixUnaryExpression => {
                let op = pn.as_postfix_unary_expression().operator;
                if op == Kind::PlusPlusToken || op == Kind::MinusMinusToken {
                    return Some(parent);
                }
                return None;
            }
            Kind::ForInStatement | Kind::ForOfStatement => {
                if pn.initializer() == Some(node) {
                    return Some(parent);
                }
                return None;
            }
            Kind::ParenthesizedExpression
            | Kind::ArrayLiteralExpression
            | Kind::SpreadElement
            | Kind::NonNullExpression => {
                node = parent;
            }
            Kind::SpreadAssignment => {
                node = pn.parent.expect("nil parent in GetAssignmentTarget");
            }
            Kind::ShorthandPropertyAssignment => {
                if pn.name() != Some(node) {
                    return None;
                }
                node = pn.parent.expect("nil parent in GetAssignmentTarget");
            }
            Kind::PropertyAssignment => {
                if pn.name() == Some(node) {
                    return None;
                }
                node = pn.parent.expect("nil parent in GetAssignmentTarget");
            }
            _ => return None,
        }
    }
}

/// `IsLogicalBinaryOperator(token)`.
pub fn is_logical_binary_operator(token: Kind) -> bool {
    token == Kind::BarBarToken || token == Kind::AmpersandAmpersandToken
}

/// `IsLogicalOrCoalescingBinaryOperator(token)`.
pub fn is_logical_or_coalescing_binary_operator(token: Kind) -> bool {
    is_logical_binary_operator(token) || token == Kind::QuestionQuestionToken
}

/// `IsLogicalOrCoalescingBinaryExpression(expr)`.
pub fn is_logical_or_coalescing_binary_expression(expr: &Node, nodes: &[Node]) -> bool {
    is_binary_expression(expr)
        && is_logical_or_coalescing_binary_operator(
            nodes[expr.as_binary_expression().operator_token.unwrap()].kind,
        )
}

/// `IsLogicalOrCoalescingAssignmentExpression(expr)`.
pub fn is_logical_or_coalescing_assignment_expression(expr: &Node, nodes: &[Node]) -> bool {
    is_binary_expression(expr)
        && nodes[expr.as_binary_expression().operator_token.unwrap()]
            .kind
            .is_logical_or_coalescing_assignment_operator()
}

/// `IsLogicalExpression(node)`.
pub fn is_logical_expression(mut node: NodeId, nodes: &[Node]) -> bool {
    loop {
        if nodes[node].kind == Kind::ParenthesizedExpression {
            node = nodes[node].expression().unwrap();
        } else if nodes[node].kind == Kind::PrefixUnaryExpression
            && nodes[node].as_prefix_unary_expression().operator == Kind::ExclamationToken
        {
            node = nodes[node].as_prefix_unary_expression().operand.unwrap();
        } else {
            return is_logical_or_coalescing_binary_expression(&nodes[node], nodes);
        }
    }
}

// ---------------------------------------------------------------------------
// Section 4: names / literals

/// `IsAccessor(node)`.
pub fn is_accessor(node: &Node) -> bool {
    node.kind == Kind::GetAccessor || node.kind == Kind::SetAccessor
}

/// `IsPropertyNameLiteral(node)`.
pub fn is_property_name_literal(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::Identifier
            | Kind::StringLiteral
            | Kind::NoSubstitutionTemplateLiteral
            | Kind::NumericLiteral
    )
}

/// `IsMemberName(node)`.
pub fn is_member_name(node: &Node) -> bool {
    node.kind == Kind::Identifier || node.kind == Kind::PrivateIdentifier
}

/// `IsEntityName(node)`.
pub fn is_entity_name(node: &Node) -> bool {
    node.kind == Kind::Identifier || node.kind == Kind::QualifiedName
}

/// `IsPropertyName(node)`.
pub fn is_property_name(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::Identifier
            | Kind::PrivateIdentifier
            | Kind::StringLiteral
            | Kind::NumericLiteral
            | Kind::ComputedPropertyName
    )
}

/// `IsIdentifierName(node)` — classifies an identifier by its parent.
pub fn is_identifier_name(node: NodeId, nodes: &[Node]) -> bool {
    let parent = nodes[node].parent.expect("nil parent in IsIdentifierName");
    let pn = &nodes[parent];
    match pn.kind {
        Kind::PropertyDeclaration
        | Kind::PropertySignature
        | Kind::MethodDeclaration
        | Kind::MethodSignature
        | Kind::GetAccessor
        | Kind::SetAccessor
        | Kind::EnumMember
        | Kind::PropertyAssignment
        | Kind::PropertyAccessExpression => pn.name() == Some(node),
        Kind::QualifiedName => pn.as_qualified_name().right == Some(node),
        Kind::BindingElement | Kind::ImportSpecifier => pn.property_name() == Some(node),
        Kind::ExportSpecifier
        | Kind::JsxAttribute
        | Kind::JsxSelfClosingElement
        | Kind::JsxOpeningElement
        | Kind::JsxClosingElement => true,
        _ => false,
    }
}

/// `IsPushOrUnshiftIdentifier(node)`.
pub fn is_push_or_unshift_identifier(node: &Node, nodes: &[Node]) -> bool {
    let text = node.text(nodes);
    text == "push" || text == "unshift"
}

/// `IsBooleanLiteral(node)`.
pub fn is_boolean_literal(node: &Node) -> bool {
    node.kind == Kind::TrueKeyword || node.kind == Kind::FalseKeyword
}

/// `IsLiteralExpression(node)`.
pub fn is_literal_expression(node: &Node) -> bool {
    node.kind.is_literal_kind()
}

/// `IsStringLiteralLike(node)`.
pub fn is_string_literal_like(node: &Node) -> bool {
    matches!(node.kind, Kind::StringLiteral | Kind::NoSubstitutionTemplateLiteral)
}

/// `IsStringOrNumericLiteralLike(node)`.
pub fn is_string_or_numeric_literal_like(node: &Node) -> bool {
    is_string_literal_like(node) || is_numeric_literal(node)
}

/// `IsSignedNumericLiteral(node)`.
pub fn is_signed_numeric_literal(node: &Node, nodes: &[Node]) -> bool {
    if node.kind == Kind::PrefixUnaryExpression {
        let node = node.as_prefix_unary_expression();
        return (node.operator == Kind::PlusToken || node.operator == Kind::MinusToken)
            && is_numeric_literal(&nodes[node.operand.unwrap()]);
    }
    false
}

// ---------------------------------------------------------------------------
// Optional chains

/// `IsOptionalChain(node)`.
pub fn is_optional_chain(node: &Node) -> bool {
    if node.flags.intersects(NodeFlags::OPTIONAL_CHAIN) {
        return matches!(
            node.kind,
            Kind::PropertyAccessExpression
                | Kind::ElementAccessExpression
                | Kind::CallExpression
                | Kind::NonNullExpression
        );
    }
    false
}

/// `getQuestionDotToken(node)`.
fn get_question_dot_token(node: &Node) -> Option<NodeId> {
    node.question_dot_token()
}

/// `IsOptionalChainRoot(node)`.
pub fn is_optional_chain_root(node: &Node) -> bool {
    is_optional_chain(node) && !is_non_null_expression(node) && get_question_dot_token(node).is_some()
}

/// `IsOutermostOptionalChain(node)`.
pub fn is_outermost_optional_chain(node: &Node, nodes: &[Node]) -> bool {
    let parent = node.parent;
    !parent.is_some_and(|p| is_optional_chain(&nodes[p])) // cases 1, 2, and 3
        || parent.is_some_and(|p| is_optional_chain_root(&nodes[p])) // case 4
        || parent.and_then(|p| nodes[p].expression()) != Some(node.id) // case 5
}

/// `IsExpressionOfOptionalChainRoot(node)`.
pub fn is_expression_of_optional_chain_root(node: NodeId, nodes: &[Node]) -> bool {
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    is_optional_chain_root(&nodes[parent]) && nodes[parent].expression() == Some(node)
}

/// `IsNullishCoalesce(node)`.
pub fn is_nullish_coalesce(node: &Node, nodes: &[Node]) -> bool {
    node.kind == Kind::BinaryExpression
        && nodes[node.as_binary_expression().operator_token.unwrap()].kind
            == Kind::QuestionQuestionToken
}

/// `IsAssertionExpression(node)`.
pub fn is_assertion_expression(node: &Node) -> bool {
    node.kind == Kind::TypeAssertionExpression || node.kind == Kind::AsExpression
}

// ---------------------------------------------------------------------------
// Expression-kind predicates

/// `isLeftHandSideExpressionKind(kind)` — the kind-only check used by
/// `IsLeftHandSideExpression`.
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

/// `IsLeftHandSideExpression(node)` — kind-only determination.
pub fn is_left_hand_side_expression(node: &Node, nodes: &[Node]) -> bool {
    is_left_hand_side_expression_kind(
        nodes[skip_partially_emitted_expressions(node.id, nodes)].kind,
    )
}

/// `isUnaryExpressionKind(kind)`.
pub fn is_unary_expression_kind(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::PrefixUnaryExpression
            | Kind::PostfixUnaryExpression
            | Kind::DeleteExpression
            | Kind::TypeOfExpression
            | Kind::VoidExpression
            | Kind::AwaitExpression
            | Kind::TypeAssertionExpression
    ) || is_left_hand_side_expression_kind(kind)
}

/// `IsUnaryExpression(node)`.
pub fn is_unary_expression(node: &Node, nodes: &[Node]) -> bool {
    is_unary_expression_kind(nodes[skip_partially_emitted_expressions(node.id, nodes)].kind)
}

/// `isExpressionKind(kind)`.
fn is_expression_kind(kind: Kind) -> bool {
    is_unary_expression_kind(kind)
        || matches!(
            kind,
            Kind::YieldExpression
                | Kind::ObjectLiteralExpression
                | Kind::JsxElement
                | Kind::JsxSelfClosingElement
                | Kind::JsxFragment
                | Kind::TemplateExpression
                | Kind::TaggedTemplateExpression
                | Kind::TemplateHead
                | Kind::TemplateMiddle
                | Kind::TemplateTail
                | Kind::BinaryExpression
                | Kind::ConditionalExpression
                | Kind::FunctionExpression
                | Kind::ArrowFunction
                | Kind::ClassExpression
                | Kind::OmittedExpression
                | Kind::CommaToken
        )
}

/// `IsExpression(node)`.
pub fn is_expression(node: &Node, nodes: &[Node]) -> bool {
    is_expression_kind(nodes[skip_partially_emitted_expressions(node.id, nodes)].kind)
}

/// `IsCommaExpression(node)`.
pub fn is_comma_expression(node: &Node, nodes: &[Node]) -> bool {
    node.kind == Kind::BinaryExpression
        && nodes[node.as_binary_expression().operator_token.unwrap()].kind == Kind::CommaToken
}

/// `IsCommaSequence(node)`.
pub fn is_comma_sequence(node: &Node, nodes: &[Node]) -> bool {
    is_comma_expression(node, nodes)
}

/// `IsIterationStatement(node, lookInLabeledStatements)`.
pub fn is_iteration_statement(node: &Node, nodes: &[Node], look_in_labeled_statements: bool) -> bool {
    match node.kind {
        Kind::ForStatement | Kind::ForInStatement | Kind::ForOfStatement | Kind::DoStatement
        | Kind::WhileStatement => true,
        Kind::LabeledStatement => {
            look_in_labeled_statements
                && is_iteration_statement(
                    &nodes[node.as_labeled_statement().statement.unwrap()],
                    nodes,
                    look_in_labeled_statements,
                )
        }
        _ => false,
    }
}

/// `IsAccessExpression(node)`.
pub fn is_access_expression(node: &Node) -> bool {
    node.kind == Kind::PropertyAccessExpression || node.kind == Kind::ElementAccessExpression
}

// ---------------------------------------------------------------------------
// Function-like / class predicates

/// `isFunctionLikeDeclarationKind(kind)` — the 7 declaration kinds.
fn is_function_like_declaration_kind(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::FunctionDeclaration
            | Kind::MethodDeclaration
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::FunctionExpression
            | Kind::ArrowFunction
    )
}

/// `IsFunctionLikeDeclaration(node)` — function-like, but not a signature
/// declaration.
pub fn is_function_like_declaration(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| is_function_like_declaration_kind(nodes[n].kind))
}

/// `IsFunctionLikeKind(kind)` — signature kinds plus declaration kinds.
pub fn is_function_like_kind(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::MethodSignature
            | Kind::CallSignature
            | Kind::JSDocSignature
            | Kind::ConstructSignature
            | Kind::IndexSignature
            | Kind::FunctionType
            | Kind::ConstructorType
    ) || is_function_like_declaration_kind(kind)
}

/// `IsFunctionLike(node)` — function- or signature-like.
pub fn is_function_like(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| is_function_like_kind(nodes[n].kind))
}

/// `IsFunctionLikeOrClassStaticBlockDeclaration(node)`.
pub fn is_function_like_or_class_static_block_declaration(
    node: Option<NodeId>,
    nodes: &[Node],
) -> bool {
    node.is_some_and(|n| {
        is_function_like(Some(n), nodes) || nodes[n].kind == Kind::ClassStaticBlockDeclaration
    })
}

/// `IsFunctionOrSourceFile(node)` — node can directly contain statements.
pub fn is_function_or_source_file(node: &Node, nodes: &[Node]) -> bool {
    is_function_like(Some(node.id), nodes) || node.kind == Kind::SourceFile
}

/// `IsClassLike(node)`.
pub fn is_class_like(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| {
        matches!(nodes[n].kind, Kind::ClassDeclaration | Kind::ClassExpression)
    })
}

/// `IsClassOrInterfaceLike(node)`.
pub fn is_class_or_interface_like(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| {
        matches!(
            nodes[n].kind,
            Kind::ClassDeclaration | Kind::ClassExpression | Kind::InterfaceDeclaration
        )
    })
}

/// `IsClassElement(node)`.
pub fn is_class_element(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::Constructor
            | Kind::PropertyDeclaration
            | Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::IndexSignature
            | Kind::ClassStaticBlockDeclaration
            | Kind::SemicolonClassElement
            | Kind::NotEmittedStatement
    )
}

/// `IsMethodOrAccessor(node)`.
pub fn is_method_or_accessor(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::MethodDeclaration | Kind::GetAccessor | Kind::SetAccessor
    )
}

/// `IsPrivateIdentifierClassElementDeclaration(node)`.
pub fn is_private_identifier_class_element_declaration(node: &Node, nodes: &[Node]) -> bool {
    (is_property_declaration(node) || is_method_or_accessor(node))
        && node
            .name()
            .is_some_and(|n| is_private_identifier(&nodes[n]))
}

/// `IsObjectLiteralOrClassExpressionMethodOrAccessor(node)`.
pub fn is_object_literal_or_class_expression_method_or_accessor(
    node: NodeId,
    nodes: &[Node],
) -> bool {
    let kind = nodes[node].kind;
    (kind == Kind::MethodDeclaration || kind == Kind::GetAccessor || kind == Kind::SetAccessor)
        && nodes[node].parent.is_some_and(|p| {
            matches!(
                nodes[p].kind,
                Kind::ObjectLiteralExpression | Kind::ClassExpression
            )
        })
}

/// `IsTypeElement(node)`.
pub fn is_type_element(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::ConstructSignature
            | Kind::CallSignature
            | Kind::PropertySignature
            | Kind::MethodSignature
            | Kind::IndexSignature
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::NotEmittedTypeElement
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

/// `IsObjectLiteralMethod(node)` — a method declaration in an object literal
/// (i.e. one that contributes its name to the object).
pub fn is_object_literal_method(node: NodeId, nodes: &[Node]) -> bool {
    is_method_declaration(&nodes[node])
        && nodes[node].parent.is_some_and(|p| {
            nodes[p].kind == Kind::ObjectLiteralExpression
                || (nodes[p].kind == Kind::PropertyAssignment
                    && nodes[p].name() == Some(node))
        })
}

/// `IsAutoAccessorPropertyDeclaration(node)`.
pub fn is_auto_accessor_property_declaration(node: &Node) -> bool {
    is_property_declaration(node) && has_syntactic_modifier(node, ModifierFlags::ACCESSOR)
}

/// `IsParameterPropertyDeclaration(node, parent)`.
pub fn is_parameter_property_declaration(node: &Node, parent: &Node) -> bool {
    is_parameter_declaration(node)
        && has_syntactic_modifier(node, ModifierFlags::PARAMETER_PROPERTY_MODIFIER)
        && parent.kind == Kind::Constructor
}

/// `IsParameterPropertyModifier(kind)`.
pub fn is_parameter_property_modifier(kind: Kind) -> bool {
    modifier_to_flag(kind).intersects(ModifierFlags::PARAMETER_PROPERTY_MODIFIER)
}

// ---------------------------------------------------------------------------
// JSX child predicates

/// `IsJsxChild(node)`.
pub fn is_jsx_child(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::JsxElement
            | Kind::JsxExpression
            | Kind::JsxSelfClosingElement
            | Kind::JsxText
            | Kind::JsxFragment
    )
}

/// `IsJsxAttributeLike(node)`.
pub fn is_jsx_attribute_like(node: &Node) -> bool {
    matches!(node.kind, Kind::JsxAttribute | Kind::JsxSpreadAttribute)
}

// ---------------------------------------------------------------------------
// Statement predicates

/// `isDeclarationStatementKind(kind)`.
fn is_declaration_statement_kind(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::FunctionDeclaration
            | Kind::MissingDeclaration
            | Kind::ClassDeclaration
            | Kind::InterfaceDeclaration
            | Kind::TypeAliasDeclaration
            | Kind::EnumDeclaration
            | Kind::ModuleDeclaration
            | Kind::ImportDeclaration
            | Kind::ImportEqualsDeclaration
            | Kind::ExportDeclaration
            | Kind::ExportAssignment
            | Kind::VariableStatement
    )
}

/// `IsDeclarationStatement(node)`.
pub fn is_declaration_statement(node: &Node) -> bool {
    is_declaration_statement_kind(node.kind)
}

/// `isStatementKindButNotDeclarationKind(kind)`.
fn is_statement_kind_but_not_declaration_kind(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::BreakStatement
            | Kind::ContinueStatement
            | Kind::DebuggerStatement
            | Kind::DoStatement
            | Kind::ExpressionStatement
            | Kind::EmptyStatement
            | Kind::ForInStatement
            | Kind::ForOfStatement
            | Kind::ForStatement
            | Kind::IfStatement
            | Kind::LabeledStatement
            | Kind::ReturnStatement
            | Kind::SwitchStatement
            | Kind::ThrowStatement
            | Kind::TryStatement
            | Kind::VariableStatement
            | Kind::WhileStatement
            | Kind::WithStatement
            | Kind::NotEmittedStatement
    )
}

/// `IsStatementButNotDeclaration(node)`.
pub fn is_statement_but_not_declaration(node: &Node) -> bool {
    is_statement_kind_but_not_declaration_kind(node.kind)
}

/// `isBlockStatement(node)` — a Block whose parent is not a try/catch and not
/// the block-like body of a function.
fn is_block_statement(node: &Node, nodes: &[Node]) -> bool {
    if node.kind != Kind::Block {
        return false;
    }
    if let Some(parent) = node.parent {
        let pk = nodes[parent].kind;
        if pk == Kind::TryStatement || pk == Kind::CatchClause {
            return false;
        }
    }
    !is_function_block(Some(node.id), nodes)
}

/// `IsStatement(node)` — true when the node is not part of a declaration
/// statement or a statement-like node.
pub fn is_statement(node: &Node, nodes: &[Node]) -> bool {
    let kind = node.kind;
    (is_statement_kind_but_not_declaration_kind(kind)
        || is_declaration_statement_kind(kind)
        || kind == Kind::EmptyStatement)
        && !is_block_statement(node, nodes)
}

/// `IsBlockOrCatchScoped(declaration)` — reports whether the declaration is
/// `let`/`const`/`using`/etc. scoped.
pub fn is_block_or_catch_scoped(declaration: NodeId, nodes: &[Node]) -> bool {
    get_combined_node_flags(declaration, nodes).intersects(NodeFlags::BLOCK_SCOPED)
        || is_catch_clause_variable_declaration_or_binding_element(declaration, nodes)
}

/// `IsCatchClauseVariableDeclarationOrBindingElement(declaration)`.
pub fn is_catch_clause_variable_declaration_or_binding_element(
    declaration: NodeId,
    nodes: &[Node],
) -> bool {
    let node = get_root_declaration(declaration, nodes);
    nodes[node].kind == Kind::VariableDeclaration
        && nodes[nodes[node].parent.expect("nil parent in IsCatchClauseVariableDeclarationOrBindingElement")].kind
            == Kind::CatchClause
}

/// `IsFunctionBlock(node)` — `node` may be absent (Go's nil `*Node`).
pub fn is_function_block(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| {
        nodes[n].kind == Kind::Block
            && nodes[n].parent.is_some_and(|p| is_function_like(Some(p), nodes))
    })
}

// ---------------------------------------------------------------------------
// Type nodes / JSDoc

/// `IsTypeNodeKind(kind)`.
pub fn is_type_node_kind(kind: Kind) -> bool {
    match kind {
        Kind::AnyKeyword
        | Kind::UnknownKeyword
        | Kind::NumberKeyword
        | Kind::BigIntKeyword
        | Kind::ObjectKeyword
        | Kind::BooleanKeyword
        | Kind::StringKeyword
        | Kind::SymbolKeyword
        | Kind::VoidKeyword
        | Kind::UndefinedKeyword
        | Kind::NeverKeyword
        | Kind::IntrinsicKeyword
        | Kind::ExpressionWithTypeArguments
        | Kind::JSDocAllType
        | Kind::JSDocNullableType
        | Kind::JSDocNonNullableType
        | Kind::JSDocOptionalType
        | Kind::JSDocVariadicType => true,
        _ => kind >= Kind::FIRST_TYPE_NODE && kind <= Kind::LAST_TYPE_NODE,
    }
}

/// `IsTypeNode(node)`.
pub fn is_type_node(node: &Node) -> bool {
    is_type_node_kind(node.kind)
}

/// `IsJSDocKind(kind)`.
pub fn is_js_doc_kind(kind: Kind) -> bool {
    kind.is_js_doc_node_kind()
}

/// `IsJSDocTypeAssertion(node)` — a parenthesized `as` assertion reparsed in
/// a JS file.
pub fn is_js_doc_type_assertion(node: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(node) = node else {
        return false;
    };
    if !is_parenthesized_expression(&nodes[node]) || !is_in_js_file(Some(node), nodes) {
        return false;
    }
    let Some(expr) = nodes[node].expression() else {
        return false;
    };
    is_as_expression(&nodes[expr])
        && nodes[expr].type_().is_some_and(|t| {
            nodes[t].flags.intersects(NodeFlags::REPARSED)
        })
}

/// `IsPrologueDirective(node)`.
pub fn is_prologue_directive(node: &Node, nodes: &[Node]) -> bool {
    node.kind == Kind::ExpressionStatement
        && node
            .expression()
            .is_some_and(|e| nodes[e].kind == Kind::StringLiteral)
}

// ---------------------------------------------------------------------------
// Outer expressions

/// `OuterExpressionKinds` flags.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct OuterExpressionKinds(pub u16);

pub mod outer_expression_kinds {
    use super::OuterExpressionKinds;

    pub const PARENTHESES: OuterExpressionKinds = OuterExpressionKinds(1 << 0);
    pub const TYPE_ASSERTIONS: OuterExpressionKinds = OuterExpressionKinds(1 << 1);
    pub const NON_NULL_ASSERTIONS: OuterExpressionKinds = OuterExpressionKinds(1 << 2);
    pub const PARTIALLY_EMITTED_EXPRESSIONS: OuterExpressionKinds = OuterExpressionKinds(1 << 3);
    pub const EXPRESSIONS_WITH_TYPE_ARGUMENTS: OuterExpressionKinds = OuterExpressionKinds(1 << 4);
    pub const SATISFIES: OuterExpressionKinds = OuterExpressionKinds(1 << 5);
    pub const EXCLUDE_JS_DOC_TYPE_ASSERTION: OuterExpressionKinds = OuterExpressionKinds(1 << 6);
    pub const ASSIGNMENTS: OuterExpressionKinds = OuterExpressionKinds(1 << 7);
    pub const COMMA: OuterExpressionKinds = OuterExpressionKinds(1 << 8);
    pub const ALL: OuterExpressionKinds = OuterExpressionKinds(0xFFFF);
    pub const ALL_EXCLUDING_JS_DOC_TYPE_ASSERTIONS: OuterExpressionKinds =
        OuterExpressionKinds(ALL.0 | EXCLUDE_JS_DOC_TYPE_ASSERTION.0);
}

impl std::ops::BitOr for OuterExpressionKinds {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        OuterExpressionKinds(self.0 | rhs.0)
    }
}

impl std::ops::BitAnd for OuterExpressionKinds {
    type Output = u16;
    fn bitand(self, rhs: Self) -> u16 {
        self.0 & rhs.0
    }
}

/// `IsOuterExpression(node, kinds)`.
pub fn is_outer_expression(node: &Node, kinds: OuterExpressionKinds, nodes: &[Node]) -> bool {
    match node.kind {
        Kind::ParenthesizedExpression => {
            kinds & outer_expression_kinds::PARENTHESES != 0
                && !(kinds & outer_expression_kinds::EXCLUDE_JS_DOC_TYPE_ASSERTION != 0
                    && is_js_doc_type_assertion(Some(node.id), nodes))
        }
        Kind::TypeAssertionExpression | Kind::AsExpression => {
            kinds & outer_expression_kinds::TYPE_ASSERTIONS != 0
        }
        Kind::SatisfiesExpression => {
            kinds
                & (outer_expression_kinds::EXPRESSIONS_WITH_TYPE_ARGUMENTS
                    | outer_expression_kinds::SATISFIES)
                != 0
        }
        Kind::ExpressionWithTypeArguments => {
            kinds & outer_expression_kinds::EXPRESSIONS_WITH_TYPE_ARGUMENTS != 0
        }
        Kind::NonNullExpression => kinds & outer_expression_kinds::NON_NULL_ASSERTIONS != 0,
        Kind::PartiallyEmittedExpression => {
            kinds & outer_expression_kinds::PARTIALLY_EMITTED_EXPRESSIONS != 0
        }
        Kind::BinaryExpression => {
            match nodes[node.as_binary_expression().operator_token.unwrap()].kind {
                Kind::EqualsToken => kinds & outer_expression_kinds::ASSIGNMENTS != 0,
                Kind::CommaToken => kinds & outer_expression_kinds::COMMA != 0,
                _ => false,
            }
        }
        _ => false,
    }
}

/// `SkipOuterExpressions(node, kinds)`.
pub fn skip_outer_expressions(
    mut node: NodeId,
    kinds: OuterExpressionKinds,
    nodes: &[Node],
) -> NodeId {
    while is_outer_expression(&nodes[node], kinds, nodes) {
        if is_binary_expression(&nodes[node]) {
            node = nodes[node].as_binary_expression().right.unwrap();
        } else {
            node = nodes[node].expression().unwrap();
        }
    }
    node
}

/// `SkipParentheses(node)`.
pub fn skip_parentheses(node: NodeId, nodes: &[Node]) -> NodeId {
    skip_outer_expressions(node, outer_expression_kinds::PARENTHESES, nodes)
}

/// `SkipTypeParentheses(node)`.
pub fn skip_type_parentheses(node: NodeId, nodes: &[Node]) -> NodeId {
    let mut node = node;
    while is_parenthesized_type_node(&nodes[node]) {
        node = nodes[node].as_parenthesized_type_node().type_.unwrap();
    }
    node
}

/// `WalkUpParenthesizedExpressions(node)`.
pub fn walk_up_parenthesized_expressions(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let mut node = Some(node);
    while let Some(n) = node {
        if nodes[n].kind != Kind::ParenthesizedExpression {
            break;
        }
        node = nodes[n].parent;
    }
    node
}

/// `WalkUpParenthesizedTypes(node)`.
pub fn walk_up_parenthesized_types(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let mut node = Some(node);
    while let Some(n) = node {
        if nodes[n].kind != Kind::ParenthesizedType {
            break;
        }
        node = nodes[n].parent;
    }
    node
}

// ---------------------------------------------------------------------------
// Source files / parents / ancestors

/// `GetSourceFileOfNode(node)` — the SourceFile containing the node, or `None`.
pub fn get_source_file_of_node(mut node: Option<NodeId>, nodes: &[Node]) -> Option<NodeId> {
    while let Some(n) = node {
        if nodes[n].kind == Kind::SourceFile {
            return Some(n);
        }
        node = nodes[n].parent;
    }
    None
}

/// `SetParentInChildren(node)` — assigns `node.parent` to each descendant.
///
/// PORT: Go pools the recursive `VisitChildren` closure with `sync.Pool`;
/// here a plain recursive helper is used instead. Children are collected into
/// a scratch `Vec` because `for_each_child` borrows the arena immutably while
/// assigning `parent` needs `&mut` access.
pub fn set_parent_in_children(nodes: &mut Vec<Node>, node: NodeId) {
    fn visit(nodes: &mut Vec<Node>, parent: Option<NodeId>, node: NodeId) {
        if let Some(parent) = parent {
            nodes[node].parent = Some(parent);
        }
        let mut children = Vec::new();
        nodes[node].for_each_child(nodes, &mut |child| {
            children.push(child);
            false
        });
        for child in children {
            visit(nodes, Some(node), child);
        }
    }
    visit(nodes, None, node);
}

/// `SetImportsOfSourceFile(sourceFile, imports)`.
pub fn set_imports_of_source_file(
    nodes: &mut Vec<Node>,
    source_file: NodeId,
    imports: Vec<NodeId>,
) {
    if !is_source_file(&nodes[source_file]) {
        return;
    }
    nodes[source_file].as_source_file_mut().imports = imports.into();
}

/// `FindAncestorResult` — return value of `FindAncestorOrQuit` callbacks.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FindAncestorResult {
    /// `FindAncestorFalse` — keep walking.
    False,
    /// `FindAncestorTrue` — this node is the match.
    True,
    /// `FindAncestorQuit` — stop walking and return `None`.
    Quit,
}

/// `ToFindAncestorResult(b)`.
pub fn to_find_ancestor_result(b: bool) -> FindAncestorResult {
    if b {
        FindAncestorResult::True
    } else {
        FindAncestorResult::False
    }
}

/// `FindAncestor(node, callback)`.
pub fn find_ancestor(
    node: Option<NodeId>,
    nodes: &[Node],
    callback: &mut dyn FnMut(&Node, &[Node]) -> bool,
) -> Option<NodeId> {
    let mut node = node;
    while let Some(n) = node {
        let result = callback(&nodes[n], nodes);
        if result {
            return Some(n);
        }
        node = nodes[n].parent;
    }
    None
}

/// `FindManyAncestors(node, callbacks...)` — returns one ancestor per
/// callback (positionally `nil`/`None` for callbacks that never matched).
pub fn find_many_ancestors(
    node: Option<NodeId>,
    nodes: &[Node],
    callbacks: &mut [&mut dyn FnMut(&Node) -> bool],
) -> Vec<Option<NodeId>> {
    let mut ancestors: Vec<Option<NodeId>> = vec![None; callbacks.len()];
    let mut found = 0usize;
    let mut node = node;
    while let Some(n) = node {
        for (i, callback) in callbacks.iter_mut().enumerate() {
            if ancestors[i].is_none() && callback(&nodes[n]) {
                ancestors[i] = Some(n);
                found += 1;
                if found == callbacks.len() {
                    return ancestors;
                }
                break;
            }
        }
        node = nodes[n].parent;
    }
    ancestors
}

/// `FindAncestorKind(node, kind)` — walks up until `kind` is found.
pub fn find_ancestor_kind(node: Option<NodeId>, kind: Kind, nodes: &[Node]) -> Option<NodeId> {
    find_ancestor(node, nodes, &mut |n, _| n.kind == kind)
}

/// `FindAncestorOrQuit(node, callback)` — `callback` returns
/// `FindAncestorResult::{True,False,Quit}`.
pub fn find_ancestor_or_quit(
    node: Option<NodeId>,
    nodes: &[Node],
    callback: &mut dyn FnMut(&Node, &[Node]) -> FindAncestorResult,
) -> Option<NodeId> {
    let mut node = node;
    while let Some(n) = node {
        match callback(&nodes[n], nodes) {
            FindAncestorResult::Quit => return None,
            FindAncestorResult::True => return Some(n),
            FindAncestorResult::False => {}
        }
        node = nodes[n].parent;
    }
    None
}

/// `IsNodeDescendantOf(node, ancestor)`.
pub fn is_node_descendant_of(node: Option<NodeId>, ancestor: Option<NodeId>, nodes: &[Node]) -> bool {
    let mut node = node;
    while let Some(n) = node {
        if Some(n) == ancestor {
            return true;
        }
        node = nodes[n].parent;
    }
    false
}

// ---------------------------------------------------------------------------
// Modifier flags

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

/// `HasAccessorModifier(node)`.
pub fn has_accessor_modifier(node: &Node) -> bool {
    has_syntactic_modifier(node, ModifierFlags::ACCESSOR)
}

/// `HasStaticModifier(node)`.
pub fn has_static_modifier(node: &Node) -> bool {
    has_syntactic_modifier(node, ModifierFlags::STATIC)
}

/// `IsStatic(node)`.
pub fn is_static(node: &Node) -> bool {
    // https://tc39.es/ecma262/#sec-static-semantics-isstatic
    is_class_element(node) && has_static_modifier(node) || is_class_static_block_declaration(node)
}

/// `CanHaveSymbol(node)`.
pub fn can_have_symbol(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::ArrowFunction | Kind::BinaryExpression | Kind::BindingElement | Kind::CallExpression
            | Kind::CallSignature | Kind::ClassDeclaration | Kind::ClassExpression
            | Kind::ClassStaticBlockDeclaration | Kind::Constructor | Kind::ConstructorType
            | Kind::ConstructSignature | Kind::ElementAccessExpression | Kind::EnumDeclaration
            | Kind::EnumMember | Kind::ExportAssignment | Kind::ExportDeclaration
            | Kind::ExportSpecifier | Kind::FunctionDeclaration | Kind::FunctionExpression
            | Kind::FunctionType | Kind::GetAccessor | Kind::ImportClause
            | Kind::ImportEqualsDeclaration | Kind::ImportSpecifier | Kind::IndexSignature
            | Kind::InterfaceDeclaration | Kind::JSTypeAliasDeclaration | Kind::JsxAttribute
            | Kind::JsxAttributes | Kind::JsxSpreadAttribute | Kind::MappedType
            | Kind::MethodDeclaration | Kind::MethodSignature | Kind::ModuleDeclaration
            | Kind::NamedTupleMember | Kind::NamespaceExport | Kind::NamespaceExportDeclaration
            | Kind::NamespaceImport | Kind::NewExpression | Kind::NoSubstitutionTemplateLiteral
            | Kind::NumericLiteral | Kind::ObjectLiteralExpression | Kind::Parameter
            | Kind::PropertyAccessExpression | Kind::PropertyAssignment | Kind::PropertyDeclaration
            | Kind::PropertySignature | Kind::SetAccessor | Kind::ShorthandPropertyAssignment
            | Kind::SourceFile | Kind::SpreadAssignment | Kind::StringLiteral
            | Kind::TypeAliasDeclaration | Kind::TypeLiteral | Kind::TypeParameter
            | Kind::VariableDeclaration
    )
}

/// `CanHaveIllegalDecorators(node)`.
pub fn can_have_illegal_decorators(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::PropertyAssignment
            | Kind::ShorthandPropertyAssignment
            | Kind::FunctionDeclaration
            | Kind::Constructor
            | Kind::IndexSignature
            | Kind::ClassStaticBlockDeclaration
            | Kind::MissingDeclaration
            | Kind::VariableStatement
            | Kind::InterfaceDeclaration
            | Kind::TypeAliasDeclaration
            | Kind::EnumDeclaration
            | Kind::ModuleDeclaration
            | Kind::ImportEqualsDeclaration
            | Kind::ImportDeclaration
            | Kind::JSImportDeclaration
            | Kind::NamespaceExportDeclaration
            | Kind::ExportDeclaration
            | Kind::ExportAssignment
    )
}

/// `CanHaveIllegalModifiers(node)`.
pub fn can_have_illegal_modifiers(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::ClassStaticBlockDeclaration
            | Kind::PropertyAssignment
            | Kind::ShorthandPropertyAssignment
            | Kind::MissingDeclaration
            | Kind::NamespaceExportDeclaration
    )
}

/// `CanHaveModifiers(node)`.
pub fn can_have_modifiers(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::TypeParameter
            | Kind::Parameter
            | Kind::PropertySignature
            | Kind::PropertyDeclaration
            | Kind::MethodSignature
            | Kind::MethodDeclaration
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::IndexSignature
            | Kind::ConstructorType
            | Kind::FunctionExpression
            | Kind::ArrowFunction
            | Kind::ClassExpression
            | Kind::VariableStatement
            | Kind::FunctionDeclaration
            | Kind::ClassDeclaration
            | Kind::InterfaceDeclaration
            | Kind::TypeAliasDeclaration
            | Kind::EnumDeclaration
            | Kind::ModuleDeclaration
            | Kind::ImportEqualsDeclaration
            | Kind::ImportDeclaration
            | Kind::JSImportDeclaration
            | Kind::ExportAssignment
            | Kind::ExportDeclaration
    )
}

/// `CanHaveDecorators(node)`.
pub fn can_have_decorators(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::Parameter
            | Kind::PropertyDeclaration
            | Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::ClassExpression
            | Kind::ClassDeclaration
    )
}

// ---------------------------------------------------------------------------
// Statement traversal helpers

/// `IsFunctionOrModuleBlock(node)`.
pub fn is_function_or_module_block(node: &Node, nodes: &[Node]) -> bool {
    is_source_file(node)
        || is_module_block(node)
        || (is_block(node) && is_function_like(node.parent, nodes))
}

/// `IsFunctionExpressionOrArrowFunction(node)`.
pub fn is_function_expression_or_arrow_function(node: &Node) -> bool {
    node.kind == Kind::FunctionExpression || node.kind == Kind::ArrowFunction
}

/// `ForEachReturnStatement(body, visitor)`.
pub fn for_each_return_statement(
    nodes: &[Node],
    body: NodeId,
    visitor: &mut dyn FnMut(NodeId) -> bool,
) -> bool {
    fn traverse(nodes: &[Node], node: NodeId, visitor: &mut dyn FnMut(NodeId) -> bool) -> bool {
        match nodes[node].kind {
            Kind::ReturnStatement => visitor(node),
            Kind::CaseBlock
            | Kind::Block
            | Kind::IfStatement
            | Kind::DoStatement
            | Kind::WhileStatement
            | Kind::ForStatement
            | Kind::ForInStatement
            | Kind::ForOfStatement
            | Kind::WithStatement
            | Kind::SwitchStatement
            | Kind::CaseClause
            | Kind::DefaultClause
            | Kind::TryStatement
            | Kind::CatchClause => nodes[node].for_each_child(nodes, &mut |c| {
                traverse(nodes, c, visitor)
            }),
            _ => false,
        }
    }
    traverse(nodes, body, visitor)
}

/// `GetRootDeclaration(node)` — walks up past binding elements to the
/// enclosing variable/parameter declaration.
pub fn get_root_declaration(mut node: NodeId, nodes: &[Node]) -> NodeId {
    while nodes[node].kind == Kind::BindingElement {
        node = nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .expect("nil parent in GetRootDeclaration");
    }
    node
}

/// `GetCombinedModifierFlags(node)` — rolls up modifier flags through a
/// variable declaration chain.
pub fn get_combined_modifier_flags(node: NodeId, nodes: &[Node]) -> ModifierFlags {
    get_combined_flags(node, nodes, &|b| b.modifier_flags())
}

/// `GetCombinedNodeFlags(node)` — rolls up node flags through a variable
/// declaration chain.
pub fn get_combined_node_flags(node: NodeId, nodes: &[Node]) -> NodeFlags {
    // PORT: `get_combined_flags` is generic over the flags type; `NodeFlags`
    // and `ModifierFlags` share the same `bits` representation here.
    get_combined_flags(node, nodes, &|b| b.flags)
}

fn get_combined_flags<T>(node: NodeId, nodes: &[Node], get_flags: &dyn Fn(&Node) -> T) -> T
where
    T: std::ops::BitOrAssign + Default,
{
    let mut node = get_root_declaration(node, nodes);
    let mut flags = get_flags(&nodes[node]);
    let mut parent_opt = if nodes[node].kind == Kind::VariableDeclaration {
        nodes[node].parent
    } else {
        Some(node)
    };
    if let Some(parent) = parent_opt {
        if nodes[parent].kind == Kind::VariableDeclarationList {
            flags |= get_flags(&nodes[parent]);
            parent_opt = nodes[parent].parent;
        }
    }
    if let Some(parent) = parent_opt {
        if nodes[parent].kind == Kind::VariableStatement {
            flags |= get_flags(&nodes[parent]);
        }
    }
    flags
}

/// `IsVarAwaitUsing(node)` — reports whether the combined block-scoped flags
/// say `await using`.
pub fn is_var_await_using(node: NodeId, nodes: &[Node]) -> bool {
    get_combined_node_flags(node, nodes) & NodeFlags::BLOCK_SCOPED == NodeFlags::AWAIT_USING
}

/// `IsVarUsing(node)`.
pub fn is_var_using(node: NodeId, nodes: &[Node]) -> bool {
    get_combined_node_flags(node, nodes) & NodeFlags::BLOCK_SCOPED == NodeFlags::USING
}

/// `IsVarConst(node)`.
pub fn is_var_const(node: NodeId, nodes: &[Node]) -> bool {
    get_combined_node_flags(node, nodes) & NodeFlags::BLOCK_SCOPED == NodeFlags::CONST
}

/// `IsVarConstLike(node)` — `const`, `using`, or `await using`.
pub fn is_var_const_like(node: NodeId, nodes: &[Node]) -> bool {
    let block_flags = get_combined_node_flags(node, nodes) & NodeFlags::BLOCK_SCOPED;
    block_flags == NodeFlags::CONST
        || block_flags == NodeFlags::USING
        || block_flags == NodeFlags::AWAIT_USING
}

/// `IsVarLet(node)`.
pub fn is_var_let(node: NodeId, nodes: &[Node]) -> bool {
    get_combined_node_flags(node, nodes) & NodeFlags::BLOCK_SCOPED == NodeFlags::LET
}

/// `IsLet(node)` — same computation as `IsVarLet` (combined flags).
pub fn is_let(node: NodeId, nodes: &[Node]) -> bool {
    get_combined_node_flags(node, nodes) & NodeFlags::BLOCK_SCOPED == NodeFlags::LET
}

// PORT(deferred): GetJSDocDeprecatedTag — needs `Node::JSDoc`/`file.jsdocCache`
//   (the lazy JSDoc resolution machinery from the parser).
// PORT(deferred): IsDeprecatedDeclaration — needs `Node::JSDoc`/`jsdocCache`.
// PORT(deferred): IsDeprecatedDeclarationWithCachedFlags — needs
//   `file.jsdocCache`.

/// `isImportMetaProperty(node, name)`.
fn is_import_meta_property(node: &Node, nodes: &[Node], name: &str) -> bool {
    is_meta_property(node)
        && node.as_meta_property().keyword_token == Kind::ImportKeyword
        && node.name().is_some_and(|n| nodes[n].text(nodes) == name)
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

/// `IsImportMeta(node)`.
pub fn is_import_meta(node: &Node, nodes: &[Node]) -> bool {
    is_import_meta_property(node, nodes, "meta")
}

/// `WalkUpBindingElementsAndPatterns(node)` — walks up past binding elements
/// and binding patterns to the node enclosing them.
pub fn walk_up_binding_elements_and_patterns(binding: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let mut node = nodes[binding]
        .parent
        .expect("nil parent in WalkUpBindingElementsAndPatterns");
    while nodes[node]
        .parent
        .is_some_and(|p| is_binding_element(&nodes[p]))
    {
        node = nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .expect("nil parent in WalkUpBindingElementsAndPatterns");
    }
    nodes[node].parent
}

/// `IsSourceFileJS(file)`.
pub fn is_source_file_js(file: &SourceFile) -> bool {
    file.script_kind == tsc_core::scriptkind::ScriptKind::Js
        || file.script_kind == tsc_core::scriptkind::ScriptKind::Jsx
}

/// `IsInJSFile(node)`.
pub fn is_in_js_file(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| {
        nodes[n].flags.intersects(NodeFlags::JAVA_SCRIPT_FILE)
    })
}

/// `IsDeclarationNode(node)` — `isDeclarationNode` in ast.go, re-ported here
/// because the AST helper is not generated as a public predicate.
pub fn is_declaration_node(node: &Node) -> bool {
    node.declaration_data().is_some()
}

/// `IsDeclaration(node)`.
pub fn is_declaration(node: &Node) -> bool {
    if node.kind == Kind::TypeParameter {
        node.parent.is_some()
    } else {
        is_declaration_node(node)
    }
}

/// `IsDeclarationName(name)`.
pub fn is_declaration_name(name: NodeId, nodes: &[Node]) -> bool {
    !is_source_file(&nodes[name])
        && !is_binding_pattern(&nodes[name])
        && is_declaration(&nodes[nodes[name].parent.expect("nil parent in IsDeclarationName")])
        && nodes[nodes[name].parent.unwrap()].name() == Some(name)
}

/// `IsDeclarationNameOrImportPropertyName(name)` — like `isDeclarationName`,
/// but returns true for the LHS of `import { x as y }` or `export { x as y }`.
pub fn is_declaration_name_or_import_property_name(name: NodeId, nodes: &[Node]) -> bool {
    match nodes[nodes[name].parent.expect("nil parent in IsDeclarationNameOrImportPropertyName")].kind {
        Kind::ImportSpecifier | Kind::ExportSpecifier => {
            is_identifier(&nodes[name]) || nodes[name].kind == Kind::StringLiteral
        }
        _ => is_declaration_name(name, nodes),
    }
}

/// `IsLiteralComputedPropertyDeclarationName(node)` — `node` is the literal
/// inside a `["name"]` computed property name.
pub fn is_literal_computed_property_declaration_name(node: NodeId, nodes: &[Node]) -> bool {
    is_string_or_numeric_literal_like(&nodes[node])
        && nodes[node].parent.is_some_and(|p| nodes[p].kind == Kind::ComputedPropertyName)
        && nodes[nodes[node].parent.unwrap()]
            .parent
            .is_some_and(|gp| is_declaration(&nodes[gp]))
}

/// `IsExternalModuleImportEqualsDeclaration(node)`.
pub fn is_external_module_import_equals_declaration(node: &Node, nodes: &[Node]) -> bool {
    node.kind == Kind::ImportEqualsDeclaration
        && nodes[node.as_import_equals_declaration().module_reference.unwrap()].kind
            == Kind::ExternalModuleReference
}

/// `IsModuleOrEnumDeclaration(node)`.
pub fn is_module_or_enum_declaration(node: &Node) -> bool {
    node.kind == Kind::ModuleDeclaration || node.kind == Kind::EnumDeclaration
}

/// `IsLiteralImportTypeNode(node)`.
pub fn is_literal_import_type_node(node: &Node, nodes: &[Node]) -> bool {
    is_import_type_node(node)
        && node.as_import_type_node().argument.is_some_and(|arg| {
            is_literal_type_node(&nodes[arg])
                && is_string_literal(&nodes[nodes[arg].as_literal_type_node().literal.unwrap()])
        })
}

/// `IsJsxTagName(node)`.
pub fn is_jsx_tag_name(node: NodeId, nodes: &[Node]) -> bool {
    let parent = nodes[node].parent.expect("nil parent in IsJsxTagName");
    let pn = &nodes[parent];
    match pn.kind {
        Kind::JsxOpeningElement | Kind::JsxClosingElement | Kind::JsxSelfClosingElement => {
            pn.tag_name() == Some(node)
        }
        _ => false,
    }
}

/// `IsImportOrExportSpecifier(node)`.
pub fn is_import_or_export_specifier(node: &Node) -> bool {
    is_import_specifier(node) || is_export_specifier(node)
}

/// `IsVoidZero(node)` — `void 0`.
pub fn is_void_zero(node: &Node, nodes: &[Node]) -> bool {
    is_void_expression(node)
        && node.expression().is_some_and(|e| {
            is_numeric_literal(&nodes[e]) && nodes[e].text(nodes) == "0"
        })
}

/// `IsExportsIdentifier(node)`.
pub fn is_exports_identifier(node: &Node) -> bool {
    is_identifier(node) && node.as_identifier().text == "exports"
}

/// `IsModuleIdentifier(node)`.
pub fn is_module_identifier(node: &Node) -> bool {
    is_identifier(node) && node.as_identifier().text == "module"
}

/// `IsThisIdentifier(node)`.
pub fn is_this_identifier(node: &Node) -> bool {
    is_identifier(node) && node.as_identifier().text == "this"
}

/// `IsThisParameter(parameter)`.
pub fn is_this_parameter(parameter: &Node, nodes: &[Node]) -> bool {
    is_parameter_declaration(parameter)
        && parameter.name().is_some_and(|n| is_this_identifier(&nodes[n]))
}

// ---------------------------------------------------------------------------
// Bindable static access expressions

/// `IsBindableStaticAccessExpression(node, excludeThisKeyword)`.
pub fn is_bindable_static_access_expression(
    node: &Node,
    nodes: &[Node],
    exclude_this_keyword: bool,
) -> bool {
    is_property_access_expression(node)
        && ((!exclude_this_keyword
            && node.expression().is_some_and(|e| nodes[e].kind == Kind::ThisKeyword))
            || (node.name().is_some_and(|n| is_identifier(&nodes[n]))
                && node.expression().is_some_and(|e| {
                    is_bindable_static_name_expression(e, nodes, true /* excludeThisKeyword */)
                })))
        || is_bindable_static_element_access_expression(node, nodes, exclude_this_keyword)
}

/// `IsBindableStaticElementAccessExpression(node, excludeThisKeyword)`.
pub fn is_bindable_static_element_access_expression(
    node: &Node,
    nodes: &[Node],
    exclude_this_keyword: bool,
) -> bool {
    is_literal_like_element_access(node, nodes)
        && (node.expression().is_some_and(|e| {
            (!exclude_this_keyword && nodes[e].kind == Kind::ThisKeyword)
                || is_entity_name_expression(&nodes[e], nodes)
                || is_bindable_static_access_expression(
                    &nodes[e],
                    nodes,
                    true, /* excludeThisKeyword */
                )
        }))
}

/// `IsPrototypeAccess(expression)`.
pub fn is_prototype_access(node: &Node, nodes: &[Node]) -> bool {
    if is_bindable_static_access_expression(node, nodes, false /* excludeThisKeyword */) {
        if let Some(name) = get_element_or_property_access_name(node, nodes) {
            return nodes[name].text(nodes) == "prototype";
        }
    }
    false
}

/// `IsLiteralLikeElementAccess(node)` — element access with a literal arg.
pub fn is_literal_like_element_access(node: &Node, nodes: &[Node]) -> bool {
    is_element_access_expression(node)
        && node.as_element_access_expression().argument_expression.is_some_and(|a| {
            is_string_or_numeric_literal_like(&nodes[a])
        })
}

/// `IsBindableStaticNameExpression(node, excludeThisKeyword)`.
pub fn is_bindable_static_name_expression(
    node: NodeId,
    nodes: &[Node],
    exclude_this_keyword: bool,
) -> bool {
    let node = &nodes[node];
    is_entity_name_expression(node, nodes)
        || is_bindable_static_access_expression(node, nodes, exclude_this_keyword)
}

/// `GetElementOrPropertyAccessName(node)` — the name node of a
/// `x.y`/`x["y"]`/`x[0]` access, or `None`.
///
/// Does not handle signed numeric names like `a[+0]` (matching Go).
pub fn get_element_or_property_access_name(node: &Node, nodes: &[Node]) -> Option<NodeId> {
    match node.kind {
        Kind::PropertyAccessExpression => {
            let name = node.name().unwrap();
            if is_identifier(&nodes[name]) {
                return Some(name);
            }
            None
        }
        Kind::ElementAccessExpression => {
            let arg = skip_parentheses(
                node.as_element_access_expression().argument_expression.unwrap(),
                nodes,
            );
            if is_string_or_numeric_literal_like(&nodes[arg]) {
                return Some(arg);
            }
            None
        }
        _ => panic!("Unhandled case in GetElementOrPropertyAccessName"),
    }
}

/// `GetInitializerOfBinaryExpression(expr)` — the innermost right operand of
/// a right-associative binary expression chain.
///
/// PORT: Go calls `expr.Right.Expression()` which panics on `*Node` kinds
/// without an `Expression` field; the Rust accessor returns `Option`, so this
/// returns `None` where Go would panic.
pub fn get_initializer_of_binary_expression(mut expr: NodeId, nodes: &[Node]) -> Option<NodeId> {
    while is_binary_expression(&nodes[nodes[expr].as_binary_expression().right.unwrap()]) {
        expr = nodes[expr].as_binary_expression().right.unwrap();
    }
    nodes[nodes[expr].as_binary_expression().right.unwrap()].expression()
}

/// `IsExpressionWithTypeArgumentsInClassExtendsClause(node)`.
pub fn is_expression_with_type_arguments_in_class_extends_clause(
    node: NodeId,
    nodes: &[Node],
) -> bool {
    try_get_class_extending_expression_with_type_arguments(node, nodes).is_some()
}

/// `TryGetClassExtendingExpressionWithTypeArguments(node)` — returns the
/// containing class declaration.
pub fn try_get_class_extending_expression_with_type_arguments(
    node: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    if !is_expression_with_type_arguments(&nodes[node]) {
        return None;
    }
    let (cls, is_implements) =
        try_get_class_implementing_or_extending_heritage_clause_element(node, nodes);
    if cls.is_some() && !is_implements {
        return cls;
    }
    None
}

/// `TryGetClassImplementingOrExtendingHeritageClauseElement(node)` — returns
/// `(classLikeDeclaration, isImplements)`.
pub fn try_get_class_implementing_or_extending_heritage_clause_element(
    node: NodeId,
    nodes: &[Node],
) -> (Option<NodeId>, bool) {
    let n = &nodes[node];
    if (is_expression_with_type_arguments(n) || is_type_reference_node(n))
        && n.parent.is_some_and(|p| is_heritage_clause(&nodes[p]))
        && nodes[n.parent.unwrap()]
            .parent
            .is_some_and(|p| is_class_like(Some(p), nodes))
    {
        return (
            nodes[n.parent.unwrap()].parent,
            nodes[n.parent.unwrap()].as_heritage_clause().token == Kind::ImplementsKeyword,
        );
    }
    (None, false)
}

// ---------------------------------------------------------------------------
// Names of declarations / JS declaration kinds

/// `GetNameOfDeclaration(declaration)`.
pub fn get_name_of_declaration(declaration: Option<NodeId>, nodes: &[Node]) -> Option<NodeId> {
    let declaration = declaration?;
    if let Some(non_assigned_name) = get_non_assigned_name_of_declaration(declaration, nodes) {
        return Some(non_assigned_name);
    }
    let d = &nodes[declaration];
    if is_function_expression(d) || is_arrow_function(d) || is_class_expression(d) {
        return get_assigned_name(declaration, nodes);
    }
    None
}

/// `GetNonAssignedNameOfDeclaration(declaration)`.
pub fn get_non_assigned_name_of_declaration(
    declaration: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    // !!!
    let decl = &nodes[declaration];
    match decl.kind {
        Kind::BinaryExpression | Kind::CallExpression => {
            match get_assignment_declaration_kind(declaration, nodes) {
                JsDeclarationKind::Property
                | JsDeclarationKind::ThisProperty
                | JsDeclarationKind::ExportsProperty => {
                    let left = decl.as_binary_expression().left.unwrap();
                    if let Some(name) =
                        get_element_or_property_access_name(&nodes[left], nodes)
                    {
                        return Some(name);
                    }
                    return Some(left);
                }
                JsDeclarationKind::ObjectDefinePropertyValue
                | JsDeclarationKind::ObjectDefinePropertyExports => {
                    return decl.arguments().map(|args| args[1]);
                }
                _ => {}
            }
            None
        }
        Kind::ExportAssignment => {
            let expr = decl.expression()?;
            if is_identifier(&nodes[expr]) {
                return Some(expr);
            }
            None
        }
        _ => decl.name(),
    }
}

/// `GetAssignedName(node)`.
pub fn get_assigned_name(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let parent = nodes[node].parent?;
    let p = &nodes[parent];
    match p.kind {
        Kind::PropertyAssignment => p.name(),
        Kind::BindingElement => p.as_binding_element().name,
        Kind::BinaryExpression => {
            let be = p.as_binary_expression();
            if Some(node) == be.right {
                let left = be.left.unwrap();
                match nodes[left].kind {
                    Kind::Identifier => return Some(left),
                    Kind::PropertyAccessExpression => return nodes[left].name(),
                    Kind::ElementAccessExpression => {
                        let arg = skip_parentheses(
                            nodes[left]
                                .as_element_access_expression()
                                .argument_expression
                                .unwrap(),
                            nodes,
                        );
                        if is_string_or_numeric_literal_like(&nodes[arg]) {
                            return Some(arg);
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        Kind::VariableDeclaration => {
            let name = p.as_variable_declaration().name?;
            if is_identifier(&nodes[name]) {
                return Some(name);
            }
            None
        }
        _ => None,
    }
}

/// `JSDeclarationKind` — classification of JS-assignment declarations.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Default)]
pub enum JsDeclarationKind {
    /// `JSDeclarationKindNone`.
    #[default]
    None = 0,
    /// `JSDeclarationKindModuleExports` — `module.exports = expr` (except
    /// `module.exports = exports`).
    ModuleExports,
    /// `JSDeclarationKindExportsProperty` — `exports.name = expr` /
    /// `module.exports.name = expr`.
    ExportsProperty,
    /// `JSDeclarationKindThisProperty` — `this.name = expr`.
    ThisProperty,
    /// `JSDeclarationKindProperty` — `F.name = expr`, `F[name] = expr`, in JS
    /// or TS file.
    Property,
    /// `JSDeclarationKindObjectDefinePropertyValue` —
    /// `Object.defineProperty(x, 'name', ...)`.
    ObjectDefinePropertyValue,
    /// `JSDeclarationKindObjectDefinePropertyExports` —
    /// `Object.defineProperty(exports || module.exports, 'name', ...)`.
    ObjectDefinePropertyExports,
}

/// `GetAssignmentDeclarationKind(node)`.
pub fn get_assignment_declaration_kind(node: NodeId, nodes: &[Node]) -> JsDeclarationKind {
    match nodes[node].kind {
        Kind::BinaryExpression => {
            let bin = nodes[node].as_binary_expression();
            if nodes[bin.operator_token.unwrap()].kind == Kind::EqualsToken
                && is_access_expression(&nodes[bin.left.unwrap()])
            {
                let left = bin.left.unwrap();
                if is_in_js_file(Some(left), nodes) {
                    if is_module_exports_access_expression(&nodes[left], nodes)
                        && !is_exports_identifier(&nodes[bin.right.unwrap()])
                    {
                        return JsDeclarationKind::ModuleExports;
                    }
                    if (is_module_exports_access_expression(
                        &nodes[nodes[left].expression().unwrap()],
                        nodes,
                    ) || is_exports_identifier(
                        &nodes[nodes[left].expression().unwrap()],
                    )) && get_element_or_property_access_name(&nodes[left], nodes).is_some()
                    {
                        return JsDeclarationKind::ExportsProperty;
                    }
                    if nodes[left].expression().is_some_and(|e| {
                        nodes[e].kind == Kind::ThisKeyword
                    }) {
                        return JsDeclarationKind::ThisProperty;
                    }
                }
                if nodes[left].kind == Kind::PropertyAccessExpression
                    && is_entity_name_expression_ex(
                        &nodes[nodes[left].expression().unwrap()],
                        is_in_js_file(Some(left), nodes),
                        nodes,
                    )
                    && nodes[left].name().is_some_and(|n| is_identifier(&nodes[n]))
                    || nodes[left].kind == Kind::ElementAccessExpression
                        && is_entity_name_expression_ex(
                            &nodes[nodes[left].expression().unwrap()],
                            is_in_js_file(Some(left), nodes),
                            nodes,
                        )
                {
                    return JsDeclarationKind::Property;
                }
            }
            JsDeclarationKind::None
        }
        Kind::CallExpression => {
            if is_in_js_file(Some(node), nodes)
                && is_bindable_object_define_property_call(node, nodes)
            {
                let entity_name = nodes[node].arguments().unwrap()[0];
                if is_exports_identifier(&nodes[entity_name])
                    || is_module_exports_access_expression(&nodes[entity_name], nodes)
                {
                    return JsDeclarationKind::ObjectDefinePropertyExports;
                }
                return JsDeclarationKind::ObjectDefinePropertyValue;
            }
            JsDeclarationKind::None
        }
        _ => JsDeclarationKind::None,
    }
}

/// `IsBindableObjectDefinePropertyCall(node)`.
pub fn is_bindable_object_define_property_call(node: NodeId, nodes: &[Node]) -> bool {
    if let Some(args) = nodes[node].arguments() {
        if args.len() == 3 {
            if let Some(expr) = nodes[node].expression() {
                let e = &nodes[expr];
                if is_property_access_expression(e)
                    && e.expression().is_some_and(|x| {
                        is_identifier(&nodes[x]) && nodes[x].text(nodes) == "Object"
                    })
                    && e.name().is_some_and(|n| nodes[n].text(nodes) == "defineProperty")
                    && is_string_or_numeric_literal_like(&nodes[args[1]])
                    && is_bindable_static_name_expression(
                        args[0],
                        nodes,
                        true, /* excludeThisKeyword */
                    )
                {
                    return true;
                }
            }
        }
    }
    false
}

/// `HasDynamicName(declaration)` — declaration has a computed name that is not
/// a literal or signed numeric literal.
pub fn has_dynamic_name(declaration: NodeId, nodes: &[Node]) -> bool {
    get_name_of_declaration(Some(declaration), nodes)
        .is_some_and(|name| is_dynamic_name(name, nodes))
}

/// `IsDynamicName(name)`.
pub fn is_dynamic_name(name: NodeId, nodes: &[Node]) -> bool {
    let expr: NodeId = match nodes[name].kind {
        Kind::ComputedPropertyName => nodes[name].expression().unwrap(),
        Kind::ElementAccessExpression => {
            skip_parentheses(
                nodes[name]
                    .as_element_access_expression()
                    .argument_expression
                    .unwrap(),
                nodes,
            )
        }
        _ => return false,
    };
    !is_string_or_numeric_literal_like(&nodes[expr]) && !is_signed_numeric_literal(&nodes[expr], nodes)
}

/// `IsEntityNameExpression(node)` — a simple or dotted name.
pub fn is_entity_name_expression(node: &Node, nodes: &[Node]) -> bool {
    is_entity_name_expression_ex(node, false /* allowJS */, nodes)
}

/// `IsEntityNameExpressionEx(node, allowJS)`.
pub fn is_entity_name_expression_ex(node: &Node, allow_js: bool, nodes: &[Node]) -> bool {
    is_identifier(node)
        || is_property_access_entity_name_expression(node, allow_js, nodes)
        || (allow_js
            && (node.kind == Kind::ThisKeyword
                || is_element_access_entity_name_expression(node, allow_js, nodes)))
}

/// `IsPropertyAccessEntityNameExpression(node, allowJS)`.
pub fn is_property_access_entity_name_expression(
    node: &Node,
    allow_js: bool,
    nodes: &[Node],
) -> bool {
    is_property_access_expression(node)
        && node.name().is_some_and(|n| is_identifier(&nodes[n]))
        && node
            .expression()
            .is_some_and(|e| is_entity_name_expression_ex(&nodes[e], allow_js, nodes))
}

/// `isElementAccessEntityNameExpression(node, allowJS)`.
fn is_element_access_entity_name_expression(node: &Node, allow_js: bool, nodes: &[Node]) -> bool {
    is_element_access_expression(node)
        && node.as_element_access_expression().argument_expression.is_some_and(|a| {
            is_string_or_numeric_literal_like(&nodes[a])
        })
        && node
            .expression()
            .is_some_and(|e| is_entity_name_expression_ex(&nodes[e], allow_js, nodes))
}

/// `IsDottedName(node)`.
pub fn is_dotted_name(node: &Node, nodes: &[Node]) -> bool {
    match node.kind {
        Kind::Identifier | Kind::ThisKeyword | Kind::SuperKeyword | Kind::MetaProperty => true,
        Kind::PropertyAccessExpression | Kind::ParenthesizedExpression => {
            is_dotted_name(&nodes[node.expression().unwrap()], nodes)
        }
        _ => false,
    }
}

/// `HasSamePropertyAccessName(node1, node2)`.
pub fn has_same_property_access_name(node1: &Node, node2: &Node, nodes: &[Node]) -> bool {
    if node1.kind == Kind::Identifier && node2.kind == Kind::Identifier {
        node1.text(nodes) == node2.text(nodes)
    } else if node1.kind == Kind::PropertyAccessExpression
        && node2.kind == Kind::PropertyAccessExpression
    {
        let name1 = node1.as_property_access_expression().name.unwrap();
        let name2 = node2.as_property_access_expression().name.unwrap();
        nodes[name1].text(nodes) == nodes[name2].text(nodes)
            && has_same_property_access_name(
                &nodes[node1.expression().unwrap()],
                &nodes[node2.expression().unwrap()],
                nodes,
            )
    } else {
        false
    }
}

// ---------------------------------------------------------------------------
// Modules

/// `IsAmbientModule(node)`.
pub fn is_ambient_module(node: &Node, nodes: &[Node]) -> bool {
    is_module_declaration(node)
        && (node.name().is_some_and(|n| nodes[n].kind == Kind::StringLiteral)
            || is_global_scope_augmentation(node))
}

/// `IsAmbientModuleSymbolName(s)` — delegates to the port in `symbol.rs`.
pub fn is_ambient_module_symbol_name_util(s: &str) -> bool {
    is_ambient_module_symbol_name(s)
}

/// `TryGetAmbientModuleNameFromSymbolName(s)` — delegates to `symbol.rs`.
pub fn try_get_ambient_module_name_from_symbol_name_util(s: &str) -> Option<String> {
    try_get_ambient_module_name_from_symbol_name(s)
}

/// `IsExternalModule(file)`.
pub fn is_external_module(file: &SourceFile) -> bool {
    file.external_module_indicator.is_some()
}

/// `IsExternalOrCommonJSModule(file)`.
pub fn is_external_or_commonjs_module(file: &SourceFile) -> bool {
    file.external_module_indicator.is_some() || file.common_js_module_indicator.is_some()
}

// TODO: Should we deprecate `IsExternalOrCommonJSModule` in favor of this function?
/// `IsEffectiveExternalModule(node, compilerOptions)`.
pub fn is_effective_external_module(
    node: &SourceFile,
    compiler_options: &CompilerOptions,
) -> bool {
    is_external_module(node)
        || (is_commonjs_containing_module_kind(compiler_options.get_emit_module_kind())
            && node.common_js_module_indicator.is_some())
}

/// `isCommonJSContainingModuleKind(kind)`.
fn is_commonjs_containing_module_kind(kind: ModuleKind) -> bool {
    kind == ModuleKind::CommonJS
        || (ModuleKind::Node16 <= kind && kind <= ModuleKind::NodeNext)
}

/// `IsExternalModuleIndicator(node)` — exported top-level member indicates
/// moduleness.
pub fn is_external_module_indicator(node: &Node) -> bool {
    is_any_import_or_re_export(node)
        || is_export_assignment(node)
        || has_syntactic_modifier(node, ModifierFlags::EXPORT)
}

/// `IsExportNamespaceAsDefaultDeclaration(node)`.
pub fn is_export_namespace_as_default_declaration(node: &Node, nodes: &[Node]) -> bool {
    if is_export_declaration(node) {
        let decl = node.as_export_declaration();
        return decl.export_clause.is_some_and(|clause| {
            is_namespace_export(&nodes[clause])
                && nodes[clause].name().is_some_and(|n| {
                    module_export_name_is_default(&nodes[n], nodes)
                })
        });
    }
    false
}

/// `IsGlobalScopeAugmentation(node)`.
pub fn is_global_scope_augmentation(node: &Node) -> bool {
    is_module_declaration(node) && node.as_module_declaration().keyword == Kind::GlobalKeyword
}

/// `IsModuleAugmentationExternal(node)`.
pub fn is_module_augmentation_external(node: &Node, nodes: &[Node]) -> bool {
    // external module augmentation is a ambient module declaration that is either:
    // - defined in the top level scope and source file is an external module
    // - defined inside ambient module declaration located in the top level scope and source file not an external module
    let parent = node.parent.expect("nil parent in IsModuleAugmentationExternal");
    match nodes[parent].kind {
        Kind::SourceFile => is_external_module(nodes[parent].as_source_file()),
        Kind::ModuleBlock => {
            let grand_parent = nodes[parent]
                .parent
                .expect("nil grandparent in IsModuleAugmentationExternal");
            is_ambient_module(&nodes[grand_parent], nodes)
                && nodes[grand_parent].parent.is_some_and(|gp| {
                    is_source_file(&nodes[gp])
                        && !is_external_module(nodes[gp].as_source_file())
                })
        }
        _ => false,
    }
}

/// `IsModuleWithStringLiteralName(node)`.
pub fn is_module_with_string_literal_name(node: &Node, nodes: &[Node]) -> bool {
    is_module_declaration(node)
        && node.name().is_some_and(|n| nodes[n].kind == Kind::StringLiteral)
}

/// `GetContainingClass(node)`.
pub fn get_containing_class(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    find_ancestor(nodes[node].parent, nodes, &mut |n, _| {
        matches!(
            n.kind,
            Kind::ClassDeclaration | Kind::ClassExpression
        )
    })
}

/// `GetExtendsHeritageClauseElements(node)`.
pub fn get_extends_heritage_clause_elements<'a>(
    node: &Node,
    nodes: &'a [Node],
) -> Option<&'a [NodeId]> {
    get_heritage_elements(node, Kind::ExtendsKeyword, nodes)
}

/// `GetImplementsHeritageClauseElements(node)`.
pub fn get_implements_heritage_clause_elements<'a>(
    node: &Node,
    nodes: &'a [Node],
) -> Option<&'a [NodeId]> {
    get_heritage_elements(node, Kind::ImplementsKeyword, nodes)
}

/// `GetHeritageElements(node, kind)`.
pub fn get_heritage_elements<'a>(
    node: &Node,
    kind: Kind,
    nodes: &'a [Node],
) -> Option<&'a [NodeId]> {
    let clause = get_heritage_clause(node, kind, nodes)?;
    nodes[clause].as_heritage_clause().types.as_ref().map(|t| t.nodes())
}

/// `GetHeritageClauseElementName(node)` — the expression or type name of a
/// heritage clause element.
pub fn get_heritage_clause_element_name(node: &Node, _nodes: &[Node]) -> Option<NodeId> {
    if is_type_reference_node(node) {
        return node.as_type_reference_node().type_name;
    }
    node.as_expression_with_type_arguments().expression
}

/// `IsNameOfHeritageClauseTypeReference(node)`.
pub fn is_name_of_heritage_clause_type_reference(mut node: NodeId, nodes: &[Node]) -> bool {
    while nodes[node].parent.is_some_and(|p| is_qualified_name(&nodes[p])) {
        node = nodes[node].parent.unwrap();
    }
    nodes[node].parent.is_some_and(|p| {
        is_type_reference_node(&nodes[p])
            && nodes[p].as_type_reference_node().type_name == Some(node)
            && nodes[p].parent.is_some_and(|gp| is_heritage_clause(&nodes[gp]))
    })
}

/// `GetHeritageClause(node, kind)`.
pub fn get_heritage_clause(node: &Node, kind: Kind, nodes: &[Node]) -> Option<NodeId> {
    if let Some(clauses) = get_heritage_clauses(node) {
        for &clause in clauses.nodes() {
            if nodes[clause].as_heritage_clause().token == kind {
                return Some(clause);
            }
        }
    }
    None
}

/// `getHeritageClauses(node)`.
fn get_heritage_clauses(node: &Node) -> Option<&NodeList> {
    match node.kind {
        Kind::ClassDeclaration => node
            .as_class_declaration()
            .class_like_base
            .heritage_clauses
            .as_ref(),
        Kind::ClassExpression => node
            .as_class_expression()
            .class_like_base
            .heritage_clauses
            .as_ref(),
        Kind::InterfaceDeclaration => node
            .as_interface_declaration()
            .heritage_clauses
            .as_ref(),
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Containers / contexts

/// `IsPartOfTypeQuery(node)`.
pub fn is_part_of_type_query(mut node: NodeId, nodes: &[Node]) -> bool {
    while matches!(nodes[node].kind, Kind::QualifiedName | Kind::Identifier) {
        node = nodes[node].parent.expect("nil parent in IsPartOfTypeQuery");
    }
    nodes[node].kind == Kind::TypeQuery
}

/// `IsPartOfParameterDeclaration(node)` — the root declaration is a parameter.
pub fn is_part_of_parameter_declaration(node: NodeId, nodes: &[Node]) -> bool {
    nodes[get_root_declaration(node, nodes)].kind == Kind::Parameter
}

/// `IsInTopLevelContext(node)`.
pub fn is_in_top_level_context(mut node: NodeId, nodes: &[Node]) -> bool {
    // The name of a class or function declaration is a BindingIdentifier in its
    // surrounding scope.
    if is_identifier(&nodes[node]) {
        let parent = nodes[node].parent;
        if let Some(p) = parent {
            if (is_class_declaration(&nodes[p]) || is_function_declaration(&nodes[p]))
                && nodes[p].name() == Some(node)
            {
                node = p;
            }
        }
    }
    let container = get_this_container(
        node,
        nodes,
        true,  /* includeArrowFunctions */
        false, /* includeClassComputedPropertyName */
    );
    is_source_file(&nodes[container])
}

/// `GetThisContainer(node, includeArrowFunctions, includeClassComputedPropertyName)`.
pub fn get_this_container(
    mut node: NodeId,
    nodes: &[Node],
    include_arrow_functions: bool,
    include_class_computed_property_name: bool,
) -> NodeId {
    loop {
        node = nodes[node]
            .parent
            .expect("nil parent in GetThisContainer");
        match nodes[node].kind {
            Kind::ComputedPropertyName => {
                if include_class_computed_property_name
                    && nodes[node].parent.is_some_and(|p| {
                        nodes[p]
                            .parent
                            .is_some_and(|gp| is_class_like(Some(gp), nodes))
                    })
                {
                    return node;
                }
                node = nodes[node]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .expect("nil parent in GetThisContainer");
            }
            Kind::Decorator => {
                let parent = nodes[node].parent.expect("nil parent in GetThisContainer");
                if nodes[parent].kind == Kind::Parameter
                    && nodes[parent]
                        .parent
                        .is_some_and(|gp| is_class_element(&nodes[gp]))
                {
                    // If the decorator's parent is a ParameterDeclaration, we
                    // resolve the this container from the grandparent class
                    // declaration.
                    node = nodes[parent].parent.unwrap();
                } else if is_class_element(&nodes[parent]) {
                    // If the decorator's parent is a class element, we resolve
                    // the 'this' container from the parent class declaration.
                    node = parent;
                }
            }
            Kind::ArrowFunction => {
                if include_arrow_functions {
                    return node;
                }
            }
            Kind::FunctionDeclaration
            | Kind::FunctionExpression
            | Kind::ModuleDeclaration
            | Kind::ClassStaticBlockDeclaration
            | Kind::PropertyDeclaration
            | Kind::PropertySignature
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::CallSignature
            | Kind::ConstructSignature
            | Kind::IndexSignature
            | Kind::EnumDeclaration
            | Kind::SourceFile => return node,
            _ => {}
        }
    }
}

/// `GetSuperContainer(node, stopOnFunctions)`.
pub fn get_super_container(node: NodeId, nodes: &[Node], stop_on_functions: bool) -> Option<NodeId> {
    let mut node = nodes[node].parent;
    while let Some(n) = node {
        match nodes[n].kind {
            Kind::ComputedPropertyName => {
                node = nodes[n].parent;
            }
            Kind::FunctionDeclaration | Kind::FunctionExpression | Kind::ArrowFunction => {
                if stop_on_functions {
                    return Some(n);
                }
            }
            Kind::PropertyDeclaration
            | Kind::PropertySignature
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::ClassStaticBlockDeclaration => return Some(n),
            Kind::Decorator => {
                // Decorators are always applied outside of the body of a class
                // or method.
                let parent = nodes[n].parent;
                if parent.is_some_and(|p| nodes[p].kind == Kind::Parameter)
                    && parent
                        .and_then(|p| nodes[p].parent)
                        .is_some_and(|gp| is_class_element(&nodes[gp]))
                {
                    // If the decorator's parent is a ParameterDeclaration, we
                    // resolve the this container from the grandparent class
                    // declaration.
                    node = parent.and_then(|p| nodes[p].parent);
                } else if parent.is_some_and(|p| is_class_element(&nodes[p])) {
                    // If the decorator's parent is a class element, we resolve
                    // the 'this' container from the parent class declaration.
                    node = parent;
                }
            }
            _ => {}
        }
        node = node.and_then(|n| nodes[n].parent);
    }
    None
}

/// `GetImmediatelyInvokedFunctionExpression(fn)`.
pub fn get_immediately_invoked_function_expression(
    fn_: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    if is_function_expression_or_arrow_function(&nodes[fn_]) {
        let mut prev = fn_;
        let mut parent = nodes[fn_].parent;
        while let Some(p) = parent {
            if !is_parenthesized_expression(&nodes[p]) {
                break;
            }
            prev = p;
            parent = nodes[p].parent;
        }
        if let Some(p) = parent {
            if is_call_expression(&nodes[p]) && nodes[p].expression() == Some(prev) {
                return Some(p);
            }
        }
    }
    None
}

/// `IsEnumConst(node)`.
pub fn is_enum_const(node: NodeId, nodes: &[Node]) -> bool {
    get_combined_modifier_flags(node, nodes).intersects(ModifierFlags::CONST)
}

/// `ExpressionIsAlias(node)`.
pub fn expression_is_alias(node: &Node, nodes: &[Node]) -> bool {
    is_entity_name_expression(node, nodes) || is_class_expression(node)
}

/// `IsInstanceOfExpression(node)`.
pub fn is_instance_of_expression(node: &Node, nodes: &[Node]) -> bool {
    is_binary_expression(node)
        && nodes[node.as_binary_expression().operator_token.unwrap()].kind
            == Kind::InstanceOfKeyword
}

/// `IsAnyImportOrReExport(node)`.
pub fn is_any_import_or_re_export(node: &Node) -> bool {
    is_import_node(node) || is_export_declaration(node)
}

/// `IsImportNode(node)`.
pub fn is_import_node(node: &Node) -> bool {
    is_any_import_syntax(node) || node_kind_is(node, &[Kind::JSImportDeclaration])
}

/// `IsAnyImportSyntax(node)` — a genuine import declaration (the re-parsed
/// `KindJSImportDeclaration` is explicitly excluded; see `IsImportNode`).
pub fn is_any_import_syntax(node: &Node) -> bool {
    node_kind_is(node, &[Kind::ImportDeclaration, Kind::ImportEqualsDeclaration])
}

/// `IsJsonSourceFile(file)`.
pub fn is_json_source_file(file: &SourceFile) -> bool {
    file.script_kind == tsc_core::scriptkind::ScriptKind::Json
}

/// `IsInJsonFile(node)`.
pub fn is_in_json_file(node: &Node) -> bool {
    node.flags.intersects(NodeFlags::JSON_FILE)
}

/// `GetExternalModuleName(node)` — the module specifier expression.
pub fn get_external_module_name(node: &Node, nodes: &[Node]) -> Option<NodeId> {
    match node.kind {
        Kind::ImportDeclaration | Kind::JSImportDeclaration | Kind::ExportDeclaration => {
            node.module_specifier()
        }
        Kind::ImportEqualsDeclaration => {
            let decl = node.as_import_equals_declaration();
            if nodes[decl.module_reference.unwrap()].kind == Kind::ExternalModuleReference {
                return nodes[decl.module_reference.unwrap()].expression();
            }
            None
        }
        Kind::ImportType => get_import_type_node_literal(node, nodes),
        Kind::CallExpression => node.arguments().and_then(|a| a.first()).copied(),
        Kind::ModuleDeclaration => {
            let name = node.as_module_declaration().name.unwrap();
            if is_string_literal(&nodes[name]) {
                return Some(name);
            }
            None
        }
        _ => panic!("Unhandled case in getExternalModuleName"),
    }
}

/// `HasImportAttributes(node)` — node kinds that can carry attributes.
pub fn has_import_attributes(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::ImportDeclaration
            | Kind::JSImportDeclaration
            | Kind::ExportDeclaration
            | Kind::ImportType
    )
}

/// `GetImportAttributes(node)`.
pub fn get_import_attributes(node: &Node) -> Option<NodeId> {
    match node.kind {
        Kind::ImportDeclaration | Kind::JSImportDeclaration => {
            node.as_import_declaration().attributes
        }
        Kind::ExportDeclaration => node.as_export_declaration().attributes,
        Kind::ImportType => node.as_import_type_node().attributes,
        _ => panic!("Unhandled case in getImportAttributes"),
    }
}

/// `getImportTypeNodeLiteral(node)`.
pub fn get_import_type_node_literal(node: &Node, nodes: &[Node]) -> Option<NodeId> {
    if is_import_type_node(node) {
        let import_type_node = node.as_import_type_node();
        if let Some(arg) = import_type_node.argument {
            if is_literal_type_node(&nodes[arg]) {
                let literal_type_node = nodes[arg].as_literal_type_node();
                if let Some(lit) = literal_type_node.literal {
                    if is_string_literal(&nodes[lit]) {
                        return Some(lit);
                    }
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Expression context / type nodes

/// `IsExpressionNode(node)`.
pub fn is_expression_node(node: NodeId, nodes: &[Node]) -> bool {
    let mut node = node;
    match nodes[node].kind {
        Kind::SuperKeyword
        | Kind::NullKeyword
        | Kind::TrueKeyword
        | Kind::FalseKeyword
        | Kind::RegularExpressionLiteral
        | Kind::ArrayLiteralExpression
        | Kind::ObjectLiteralExpression
        | Kind::PropertyAccessExpression
        | Kind::ElementAccessExpression
        | Kind::CallExpression
        | Kind::NewExpression
        | Kind::TaggedTemplateExpression
        | Kind::AsExpression
        | Kind::TypeAssertionExpression
        | Kind::SatisfiesExpression
        | Kind::NonNullExpression
        | Kind::ParenthesizedExpression
        | Kind::FunctionExpression
        | Kind::ClassExpression
        | Kind::ArrowFunction
        | Kind::VoidExpression
        | Kind::DeleteExpression
        | Kind::TypeOfExpression
        | Kind::PrefixUnaryExpression
        | Kind::PostfixUnaryExpression
        | Kind::BinaryExpression
        | Kind::ConditionalExpression
        | Kind::SpreadElement
        | Kind::TemplateExpression
        | Kind::OmittedExpression
        | Kind::JsxElement
        | Kind::JsxSelfClosingElement
        | Kind::JsxFragment
        | Kind::YieldExpression
        | Kind::AwaitExpression => true,
        Kind::MetaProperty => {
            // `import.<phase>` in `import.<phase>(...)` is not an expression
            let Some(parent) = nodes[node].parent else {
                return false;
            };
            !is_import_call(&nodes[parent], nodes) || nodes[parent].expression() != Some(node)
        }
        Kind::ExpressionWithTypeArguments => {
            nodes[node]
                .parent
                .is_none_or(|p| !is_heritage_clause(&nodes[p]))
        }
        Kind::QualifiedName => {
            while nodes[node]
                .parent
                .is_some_and(|p| nodes[p].kind == Kind::QualifiedName)
            {
                node = nodes[node].parent.unwrap();
            }
            let parent = nodes[node].parent.expect("nil parent in IsExpressionNode");
            is_type_query_node(&nodes[parent])
                || is_js_doc_link_like(&nodes[parent])
                || is_js_doc_name_reference(&nodes[parent])
                || is_jsx_tag_name(node, nodes)
        }
        Kind::PrivateIdentifier => {
            let Some(parent) = nodes[node].parent else {
                return false;
            };
            is_binary_expression(&nodes[parent])
                && nodes[parent].as_binary_expression().left == Some(node)
                && nodes[nodes[parent].as_binary_expression().operator_token.unwrap()].kind
                    == Kind::InKeyword
        }
        Kind::Identifier => {
            let parent = nodes[node].parent.expect("nil parent in IsExpressionNode");
            let pn = &nodes[parent];
            if is_type_query_node(pn)
                || is_js_doc_link_like(pn)
                || is_js_doc_name_reference(pn)
                || is_jsx_tag_name(node, nodes)
            {
                return true;
            }
            // fallthrough
            is_in_expression_context(node, nodes)
        }
        Kind::NumericLiteral
        | Kind::BigIntLiteral
        | Kind::StringLiteral
        | Kind::NoSubstitutionTemplateLiteral
        | Kind::ThisKeyword => is_in_expression_context(node, nodes),
        _ => false,
    }
}

/// `IsInExpressionContext(node)`.
pub fn is_in_expression_context(node: NodeId, nodes: &[Node]) -> bool {
    let parent = nodes[node]
        .parent
        .expect("nil parent in IsInExpressionContext");
    let pn = &nodes[parent];
    match pn.kind {
        Kind::VariableDeclaration
        | Kind::Parameter
        | Kind::PropertyDeclaration
        | Kind::PropertySignature
        | Kind::EnumMember
        | Kind::PropertyAssignment
        | Kind::BindingElement => pn.initializer() == Some(node),
        Kind::ExpressionStatement
        | Kind::IfStatement
        | Kind::DoStatement
        | Kind::WhileStatement
        | Kind::ReturnStatement
        | Kind::WithStatement
        | Kind::SwitchStatement
        | Kind::CaseClause
        | Kind::DefaultClause
        | Kind::ThrowStatement
        | Kind::TypeAssertionExpression
        | Kind::AsExpression
        | Kind::TemplateSpan
        | Kind::ComputedPropertyName
        | Kind::SatisfiesExpression => pn.expression() == Some(node),
        Kind::ForStatement => {
            let s = pn.as_for_statement();
            (s.initializer == Some(node)
                && nodes[s.initializer.unwrap()].kind != Kind::VariableDeclarationList)
                || s.condition == Some(node)
                || s.incrementor == Some(node)
        }
        Kind::ForInStatement | Kind::ForOfStatement => {
            let s = pn.as_for_in_or_of_statement();
            (s.initializer == Some(node)
                && nodes[s.initializer.unwrap()].kind != Kind::VariableDeclarationList)
                || s.expression == Some(node)
        }
        Kind::Decorator
        | Kind::JsxExpression
        | Kind::JsxSpreadAttribute
        | Kind::SpreadAssignment => true,
        Kind::ExpressionWithTypeArguments => {
            pn.expression() == Some(node) && !is_part_of_type_node(parent, nodes)
        }
        Kind::ShorthandPropertyAssignment => {
            pn.as_shorthand_property_assignment().object_assignment_initializer == Some(node)
        }
        Kind::FunctionExpression | Kind::ClassExpression => {
            // The name of a function or class expression is a declaration name,
            // not an expression.
            pn.name() != Some(node)
        }
        _ => is_expression_node(parent, nodes),
    }
}

/// `IsPartOfTypeNode(node)`.
pub fn is_part_of_type_node(mut node: NodeId, nodes: &[Node]) -> bool {
    let kind = nodes[node].kind;
    if kind >= Kind::FIRST_TYPE_NODE && kind <= Kind::LAST_TYPE_NODE {
        return true;
    }
    match nodes[node].kind {
        Kind::AnyKeyword
        | Kind::UnknownKeyword
        | Kind::NumberKeyword
        | Kind::BigIntKeyword
        | Kind::StringKeyword
        | Kind::BooleanKeyword
        | Kind::SymbolKeyword
        | Kind::ObjectKeyword
        | Kind::UndefinedKeyword
        | Kind::NullKeyword
        | Kind::NeverKeyword => true,
        Kind::VoidKeyword => {
            nodes[node].parent.is_some_and(|p| nodes[p].kind != Kind::VoidExpression)
        }
        Kind::ExpressionWithTypeArguments => {
            is_part_of_type_expression_with_type_arguments(node, nodes)
        }
        Kind::TypeParameter => nodes[node].parent.is_some_and(|p| {
            matches!(nodes[p].kind, Kind::MappedType | Kind::InferType)
        }),
        Kind::Identifier => {
            let parent = nodes[node].parent.expect("nil parent in IsPartOfTypeNode");
            if is_qualified_name(&nodes[parent])
                && nodes[parent].as_qualified_name().right == Some(node)
            {
                return is_part_of_type_node_in_parent(parent, nodes);
            }
            if is_property_access_expression(&nodes[parent])
                && nodes[parent].name() == Some(node)
            {
                return is_part_of_type_node_in_parent(parent, nodes);
            }
            is_part_of_type_node_in_parent(node, nodes)
        }
        Kind::QualifiedName | Kind::PropertyAccessExpression | Kind::ThisKeyword => {
            is_part_of_type_node_in_parent(node, nodes)
        }
        _ => false,
    }
}

/// `isPartOfTypeNodeInParent(node)`.
fn is_part_of_type_node_in_parent(node: NodeId, nodes: &[Node]) -> bool {
    let parent = nodes[node]
        .parent
        .expect("nil parent in isPartOfTypeNodeInParent");
    let pn = &nodes[parent];
    if pn.kind == Kind::TypeQuery {
        return false;
    }
    if pn.kind == Kind::ImportType {
        return !pn.as_import_type_node().is_type_of;
    }

    // Do not recursively call isPartOfTypeNode on the parent. In the example:
    //
    //     let a: A.B.C;
    //
    // Calling isPartOfTypeNode would consider the qualified name A.B a type
    // node. Only C and A.B.C are type nodes.
    if pn.kind >= Kind::FIRST_TYPE_NODE && pn.kind <= Kind::LAST_TYPE_NODE {
        return true;
    }
    match pn.kind {
        Kind::ExpressionWithTypeArguments => {
            is_part_of_type_expression_with_type_arguments(parent, nodes)
        }
        Kind::TypeParameter => {
            Some(node) == pn.as_type_parameter_declaration().constraint
        }
        Kind::VariableDeclaration
        | Kind::Parameter
        | Kind::PropertyDeclaration
        | Kind::PropertySignature
        | Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::ArrowFunction
        | Kind::Constructor
        | Kind::MethodDeclaration
        | Kind::MethodSignature
        | Kind::GetAccessor
        | Kind::SetAccessor
        | Kind::CallSignature
        | Kind::ConstructSignature
        | Kind::IndexSignature
        | Kind::TypeAssertionExpression => pn.type_() == Some(node),
        Kind::CallExpression | Kind::NewExpression | Kind::TaggedTemplateExpression => {
            pn.type_arguments().is_some_and(|args| args.contains(&node))
        }
        _ => false,
    }
}

/// `isPartOfTypeExpressionWithTypeArguments(node)`.
fn is_part_of_type_expression_with_type_arguments(node: NodeId, nodes: &[Node]) -> bool {
    let parent = nodes[node]
        .parent
        .expect("nil parent in isPartOfTypeExpressionWithTypeArguments");
    (is_heritage_clause(&nodes[parent])
        && (!is_class_like(nodes[parent].parent, nodes)
            || nodes[parent].as_heritage_clause().token == Kind::ImplementsKeyword))
        || is_js_doc_implements_tag(&nodes[parent])
        || is_js_doc_augments_tag(&nodes[parent])
}

/// `IsJSDocLinkLike(node)`.
pub fn is_js_doc_link_like(node: &Node) -> bool {
    node_kind_is(
        node,
        &[Kind::JSDocLink, Kind::JSDocLinkCode, Kind::JSDocLinkPlain],
    )
}

/// `IsJSDocTag(node)`.
pub fn is_js_doc_tag(node: &Node) -> bool {
    node.kind >= Kind::FIRST_J_S_DOC_TAG_NODE && node.kind <= Kind::LAST_J_S_DOC_TAG_NODE
}

/// `IsSuperCall(node)`.
pub fn is_super_call(node: &Node, nodes: &[Node]) -> bool {
    is_call_expression(node)
        && node
            .expression()
            .is_some_and(|e| nodes[e].kind == Kind::SuperKeyword)
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

/// `IsSourcePhaseImport(node)` — `import source ... from ...` or
/// `import.source(...)`.
pub fn is_source_phase_import(node: &Node, nodes: &[Node]) -> bool {
    if is_import_declaration(node) {
        let clause = node.as_import_declaration().import_clause;
        return clause.is_some_and(|c| {
            nodes[c].as_import_clause().phase_modifier == Kind::SourceKeyword
        });
    }
    is_source_phase_import_call(node, nodes)
}

/// `IsSourcePhaseImportCall(node)` — `import.source(...)`.
pub fn is_source_phase_import_call(node: &Node, nodes: &[Node]) -> bool {
    is_call_expression(node)
        && node
            .expression()
            .is_some_and(|e| is_import_source_meta_property(&nodes[e], nodes))
}

/// `IsComputedNonLiteralName(name)`.
pub fn is_computed_non_literal_name(name: &Node, nodes: &[Node]) -> bool {
    is_computed_property_name(name)
        && name
            .expression()
            .is_some_and(|e| !is_string_or_numeric_literal_like(&nodes[e]))
}

/// `IsQuestionToken(node)` — may be `None` (Go's nil `*Node`).
pub fn is_question_token(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| nodes[n].kind == Kind::QuestionToken)
}

/// `EntityNameToString(name, getTextOfNode)` — `get_text_of_node` is Go's
/// optional `getTextOfNode func(*Node) string` callback; `None` falls back to
/// the node's own text.
pub fn entity_name_to_string(
    name: NodeId,
    nodes: &[Node],
    get_text_of_node: Option<&mut dyn FnMut(&[Node], NodeId) -> String>,
) -> String {
    entity_name_to_string_worker(name, nodes, get_text_of_node)
}

fn entity_name_to_string_worker(
    name: NodeId,
    nodes: &[Node],
    mut get_text_of_node: Option<&mut dyn FnMut(&[Node], NodeId) -> String>,
) -> String {
    match nodes[name].kind {
        Kind::ThisKeyword => "this".to_string(),
        Kind::Identifier | Kind::PrivateIdentifier => {
            if node_is_synthesized(&nodes[name]) || get_text_of_node.is_none() {
                return nodes[name].text(nodes).into_owned();
            }
            get_text_of_node.as_deref_mut().unwrap()(nodes, name)
        }
        Kind::QualifiedName => {
            let q = nodes[name].as_qualified_name();
            let left =
                entity_name_to_string_worker(q.left.unwrap(), nodes, get_text_of_node.as_deref_mut());
            let right = entity_name_to_string_worker(
                q.right.unwrap(),
                nodes,
                get_text_of_node.as_deref_mut(),
            );
            format!("{}.{}", left, right)
        }
        Kind::PropertyAccessExpression => {
            let expr = nodes[name].expression().unwrap();
            let pname = nodes[name].as_property_access_expression().name.unwrap();
            let left =
                entity_name_to_string_worker(expr, nodes, get_text_of_node.as_deref_mut());
            let right =
                entity_name_to_string_worker(pname, nodes, get_text_of_node.as_deref_mut());
            format!("{}.{}", left, right)
        }
        Kind::JsxNamespacedName => {
            let j = nodes[name].as_jsx_namespaced_name();
            let left = entity_name_to_string_worker(
                j.namespace.unwrap(),
                nodes,
                get_text_of_node.as_deref_mut(),
            );
            let right = entity_name_to_string_worker(
                j.name.unwrap(),
                nodes,
                get_text_of_node.as_deref_mut(),
            );
            format!("{}:{}", left, right)
        }
        _ => panic!("Unhandled case in EntityNameToString"),
    }
}

/// `GetTextOfPropertyName(name)` — the property name text or `""`.
pub fn get_text_of_property_name(name: NodeId, nodes: &[Node]) -> String {
    try_get_text_of_property_name(name, nodes).0.unwrap_or_default()
}

/// `TryGetTextOfPropertyName(name)` — `(text, ok)`.
pub fn try_get_text_of_property_name(name: NodeId, nodes: &[Node]) -> (Option<String>, bool) {
    match nodes[name].kind {
        Kind::Identifier
        | Kind::PrivateIdentifier
        | Kind::StringLiteral
        | Kind::NumericLiteral
        | Kind::BigIntLiteral
        | Kind::NoSubstitutionTemplateLiteral => {
            (Some(nodes[name].text(nodes).into_owned()), true)
        }
        Kind::ComputedPropertyName => {
            let expr = nodes[name].expression();
            if let Some(e) = expr {
                if is_string_or_numeric_literal_like(&nodes[e]) {
                    return (Some(nodes[e].text(nodes).into_owned()), true);
                }
            }
            (None, false)
        }
        Kind::JsxNamespacedName => {
            let j = nodes[name].as_jsx_namespaced_name();
            (
                Some(format!(
                    "{}:{}",
                    nodes[j.namespace.unwrap()].text(nodes),
                    nodes[j.name.unwrap()].text(nodes)
                )),
                true,
            )
        }
        _ => (None, false),
    }
}

/// `IsJSDocNode(node)`.
pub fn is_js_doc_node(node: &Node) -> bool {
    node.kind.is_js_doc_node_kind()
}

/// `IsNonWhitespaceToken(node)` — token kinds that are not whitespace-only
/// JSX text.
pub fn is_non_whitespace_token(node: &Node) -> bool {
    node.kind.is_token_kind() && !is_whitespace_only_jsx_text(node)
}

/// `IsWhitespaceOnlyJsxText(node)`.
pub fn is_whitespace_only_jsx_text(node: &Node) -> bool {
    node.kind == Kind::JsxText && node.as_jsx_text().contains_only_trivia_white_spaces
}

/// `GetNewTargetContainer(node)`.
pub fn get_new_target_container(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    let container = get_this_container(
        node,
        nodes,
        false, /* includeArrowFunctions */
        false, /* includeClassComputedPropertyName */
    );
    match nodes[container].kind {
        Kind::Constructor | Kind::FunctionDeclaration | Kind::FunctionExpression => {
            Some(container)
        }
        _ => None,
    }
}

/// `GetEnclosingBlockScopeContainer(node)`.
pub fn get_enclosing_block_scope_container(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    find_ancestor(nodes[node].parent, nodes, &mut |current, nodes| {
        is_block_scope(current, nodes)
    })
}

/// `IsBlockScope(node, parentNode)`.
pub fn is_block_scope(node: &Node, nodes: &[Node]) -> bool {
    match node.kind {
        Kind::SourceFile
        | Kind::CaseBlock
        | Kind::CatchClause
        | Kind::ModuleDeclaration
        | Kind::ForStatement
        | Kind::ForInStatement
        | Kind::ForOfStatement
        | Kind::Constructor
        | Kind::MethodDeclaration
        | Kind::GetAccessor
        | Kind::SetAccessor
        | Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::ArrowFunction
        | Kind::PropertyDeclaration
        | Kind::ClassStaticBlockDeclaration => true,
        Kind::Block => {
            // function block is not considered block-scope container
            // see comment in binder.ts: bind(...), case for SyntaxKind.Block
            !is_function_like_or_class_static_block_declaration(node.parent, nodes)
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Semantic meaning

/// `SemanticMeaning` — `SemanticMeaning` bitmask in utilities.go.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub struct SemanticMeaning(pub i32);

impl SemanticMeaning {
    /// `SemanticMeaningNone`.
    pub const NONE: SemanticMeaning = SemanticMeaning(0);
    /// `SemanticMeaningValue`.
    pub const VALUE: SemanticMeaning = SemanticMeaning(1 << 0);
    /// `SemanticMeaningType`.
    pub const TYPE: SemanticMeaning = SemanticMeaning(1 << 1);
    /// `SemanticMeaningNamespace`.
    pub const NAMESPACE: SemanticMeaning = SemanticMeaning(1 << 2);
    /// `SemanticMeaningAll`.
    pub const ALL: SemanticMeaning = SemanticMeaning(
        Self::VALUE.0 | Self::TYPE.0 | Self::NAMESPACE.0,
    );
}

impl std::ops::BitOr for SemanticMeaning {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        SemanticMeaning(self.0 | rhs.0)
    }
}

impl std::ops::BitAnd for SemanticMeaning {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        SemanticMeaning(self.0 & rhs.0)
    }
}

impl std::ops::BitOrAssign for SemanticMeaning {
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

/// `GetMeaningFromDeclaration(node)`.
pub fn get_meaning_from_declaration(node: &Node, nodes: &[Node]) -> SemanticMeaning {
    match node.kind {
        Kind::VariableDeclaration => SemanticMeaning::VALUE,
        Kind::Parameter
        | Kind::BindingElement
        | Kind::PropertyDeclaration
        | Kind::PropertySignature
        | Kind::PropertyAssignment
        | Kind::ShorthandPropertyAssignment
        | Kind::MethodDeclaration
        | Kind::MethodSignature
        | Kind::Constructor
        | Kind::GetAccessor
        | Kind::SetAccessor
        | Kind::FunctionDeclaration
        | Kind::FunctionExpression
        | Kind::ArrowFunction
        | Kind::CatchClause
        | Kind::JsxAttribute => SemanticMeaning::VALUE,
        Kind::TypeParameter
        | Kind::InterfaceDeclaration
        | Kind::TypeAliasDeclaration
        | Kind::JSTypeAliasDeclaration
        | Kind::TypeLiteral => SemanticMeaning::TYPE,
        Kind::EnumMember | Kind::ClassDeclaration => {
            SemanticMeaning::VALUE | SemanticMeaning::TYPE
        }
        Kind::ModuleDeclaration => {
            if is_ambient_module(node, nodes) {
                SemanticMeaning::NAMESPACE | SemanticMeaning::VALUE
            } else if get_module_instance_state(node.id, nodes) == ModuleInstanceState::Instantiated
            {
                SemanticMeaning::NAMESPACE | SemanticMeaning::VALUE
            } else {
                SemanticMeaning::NAMESPACE
            }
        }
        Kind::EnumDeclaration
        | Kind::NamedImports
        | Kind::ImportSpecifier
        | Kind::ImportEqualsDeclaration
        | Kind::ImportDeclaration
        | Kind::JSImportDeclaration
        | Kind::ExportAssignment
        | Kind::ExportDeclaration => SemanticMeaning::ALL,
        // An external module can be a Value
        Kind::SourceFile => SemanticMeaning::NAMESPACE | SemanticMeaning::VALUE,
        _ => SemanticMeaning::ALL,
    }
}

/// `IsPropertyAccessOrQualifiedName(node)`.
pub fn is_property_access_or_qualified_name(node: &Node) -> bool {
    node.kind == Kind::PropertyAccessExpression || node.kind == Kind::QualifiedName
}

/// `IsLabelName(node)`.
pub fn is_label_name(node: NodeId, nodes: &[Node]) -> bool {
    is_label_of_labeled_statement(node, nodes) || is_jump_statement_target(node, nodes)
}

/// `IsLabelOfLabeledStatement(node)`.
pub fn is_label_of_labeled_statement(node: NodeId, nodes: &[Node]) -> bool {
    if !is_identifier(&nodes[node]) {
        return false;
    }
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    if !is_labeled_statement(&nodes[parent]) {
        return false;
    }
    nodes[parent].as_labeled_statement().label == Some(node)
}

/// `IsJumpStatementTarget(node)`.
pub fn is_jump_statement_target(node: NodeId, nodes: &[Node]) -> bool {
    if !is_identifier(&nodes[node]) {
        return false;
    }
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    if !is_break_or_continue_statement(&nodes[parent]) {
        return false;
    }
    nodes[parent].label() == Some(node)
}

/// `IsBreakOrContinueStatement(node)`.
pub fn is_break_or_continue_statement(node: &Node) -> bool {
    node_kind_is(node, &[Kind::BreakStatement, Kind::ContinueStatement])
}

// ---------------------------------------------------------------------------
// Module instance state

/// `type ModuleInstanceState int32`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ModuleInstanceState {
    #[default]
    Unknown = 0,
    NonInstantiated,
    Instantiated,
    ConstEnumOnly,
}

/// `pushAncestor(ancestors, parent)`.
fn push_ancestor(ancestors: &mut Vec<NodeId>, parent: NodeId) {
    ancestors.push(parent);
}

/// `popAncestor(ancestors, node)` — returns the virtual parent or the real
/// `Parent` of `node`.
fn pop_ancestor(ancestors: &mut Vec<NodeId>, node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    if ancestors.is_empty() {
        return nodes[node].parent;
    }
    ancestors.pop()
}

/// `GetModuleInstanceState(node)` — `ancestors` and `visited` are virtual
/// parent stacks/caches used during binding.
pub fn get_module_instance_state(node: NodeId, nodes: &[Node]) -> ModuleInstanceState {
    get_module_instance_state_full(node, &mut Vec::new(), None, nodes)
}

/// `getModuleInstanceState(node, ancestors, visited)`.
pub fn get_module_instance_state_full(
    node: NodeId,
    ancestors: &mut Vec<NodeId>,
    visited: Option<&mut FxHashMap<NodeId, ModuleInstanceState>>,
    nodes: &[Node],
) -> ModuleInstanceState {
    let module = nodes[node].as_module_declaration();
    if let Some(body) = module.body_base.body {
        ancestors.push(node);
        get_module_instance_state_cached(body, ancestors, visited, nodes)
    } else {
        ModuleInstanceState::Instantiated
    }
}

fn get_module_instance_state_cached(
    node: NodeId,
    ancestors: &mut Vec<NodeId>,
    visited: Option<&mut FxHashMap<NodeId, ModuleInstanceState>>,
    nodes: &[Node],
) -> ModuleInstanceState {
    // PORT: `visited` in Go is lazily created map; callers passing `None` get
    // a fresh local map.
    let mut local;
    let visited: &mut FxHashMap<NodeId, ModuleInstanceState> = match visited {
        Some(v) => v,
        None => {
            local = FxHashMap::default();
            &mut local
        }
    };
    let node_id = get_node_id(&nodes[node]);
    if let Some(&cached) = visited.get(&node_id) {
        if cached != ModuleInstanceState::Unknown {
            return cached;
        }
        return ModuleInstanceState::NonInstantiated;
    }
    visited.insert(node_id, ModuleInstanceState::Unknown);
    let result = get_module_instance_state_worker(node, ancestors, visited, nodes);
    visited.insert(node_id, result);
    result
}

/// `getModuleInstanceStateWorker(node, ancestors, visited)`.
fn get_module_instance_state_worker(
    node: NodeId,
    ancestors: &mut Vec<NodeId>,
    visited: &mut FxHashMap<NodeId, ModuleInstanceState>,
    nodes: &[Node],
) -> ModuleInstanceState {
    // A module is uninstantiated if it contains only
    match nodes[node].kind {
        Kind::InterfaceDeclaration | Kind::TypeAliasDeclaration | Kind::JSTypeAliasDeclaration => {
            return ModuleInstanceState::NonInstantiated;
        }
        Kind::EnumDeclaration => {
            if is_enum_const(node, nodes) {
                return ModuleInstanceState::ConstEnumOnly;
            }
        }
        Kind::ImportDeclaration | Kind::JSImportDeclaration | Kind::ImportEqualsDeclaration => {
            if !has_syntactic_modifier(&nodes[node], ModifierFlags::EXPORT) {
                return ModuleInstanceState::NonInstantiated;
            }
        }
        Kind::ExportDeclaration => {
            let decl = nodes[node].as_export_declaration();
            if decl.module_specifier.is_none()
                && decl.export_clause.is_some_and(|c| nodes[c].kind == Kind::NamedExports)
            {
                let mut state = ModuleInstanceState::NonInstantiated;
                ancestors.push(node);
                ancestors.push(decl.export_clause.unwrap());
                for specifier in nodes[decl.export_clause.unwrap()].elements().unwrap_or(&[]) {
                    let specifier_state = get_module_instance_state_for_alias_target(
                        *specifier,
                        ancestors,
                        visited,
                        nodes,
                    );
                    if specifier_state > state {
                        state = specifier_state;
                    }
                    if state == ModuleInstanceState::Instantiated {
                        return state;
                    }
                }
                return state;
            }
        }
        Kind::ModuleBlock => {
            let mut state = ModuleInstanceState::NonInstantiated;
            ancestors.push(node);
            // Collect children so we can iterate while calling back into
            // functions that borrow `nodes`.
            let mut children = Vec::new();
            nodes[node].for_each_child(nodes, &mut |n| {
                children.push(n);
                false
            });
            for child in children {
                let child_state =
                    get_module_instance_state_cached(child, ancestors, Some(&mut *visited), nodes);
                match child_state {
                    ModuleInstanceState::NonInstantiated => {}
                    ModuleInstanceState::ConstEnumOnly => {
                        state = ModuleInstanceState::ConstEnumOnly;
                    }
                    ModuleInstanceState::Instantiated => {
                        return ModuleInstanceState::Instantiated;
                    }
                    ModuleInstanceState::Unknown => {
                        panic!("Unhandled case in getModuleInstanceStateWorker")
                    }
                }
            }
            return state;
        }
        Kind::ModuleDeclaration => {
            return get_module_instance_state_full(node, ancestors, Some(&mut *visited), nodes);
        }
        _ => {}
    }
    ModuleInstanceState::Instantiated
}

/// `getModuleInstanceStateForAliasTarget(node, ancestors, visited)`.
fn get_module_instance_state_for_alias_target(
    node: NodeId,
    ancestors: &mut Vec<NodeId>,
    visited: &mut FxHashMap<NodeId, ModuleInstanceState>,
    nodes: &[Node],
) -> ModuleInstanceState {
    let name = nodes[node].property_name_or_name().unwrap();
    if nodes[name].kind != Kind::Identifier {
        // Skip for invalid syntax like this: export { "x" }
        return ModuleInstanceState::Instantiated;
    }
    let mut p = pop_ancestor(ancestors, node, nodes);
    while let Some(parent) = p {
        if is_block(&nodes[parent]) || is_module_block(&nodes[parent]) || is_source_file(&nodes[parent]) {
            let mut found = ModuleInstanceState::Unknown;
            let mut statements_ancestors = ancestors.clone();
            push_ancestor(&mut statements_ancestors, parent);
            for &statement in nodes[parent].statements().unwrap_or(&[]) {
                if node_has_name(statement, name, nodes) {
                    let state = get_module_instance_state_cached(
                        statement,
                        &mut statements_ancestors,
                        Some(&mut *visited),
                        nodes,
                    );
                    if found == ModuleInstanceState::Unknown || state > found {
                        found = state;
                    }
                    if found == ModuleInstanceState::Instantiated {
                        return found;
                    }
                    if nodes[statement].kind == Kind::ImportEqualsDeclaration {
                        // Treat re-exports of import aliases as instantiated
                        // since they're ambiguous.
                        found = ModuleInstanceState::Instantiated;
                    }
                }
            }
            if found != ModuleInstanceState::Unknown {
                return found;
            }
        }
        p = pop_ancestor(ancestors, parent, nodes);
    }
    // Couldn't locate, assume could refer to a value
    ModuleInstanceState::Instantiated
}

/// `IsInstantiatedModule(node, preserveConstEnums)`.
pub fn is_instantiated_module(node: NodeId, preserve_const_enums: bool, nodes: &[Node]) -> bool {
    let module_state = get_module_instance_state(node, nodes);
    module_state == ModuleInstanceState::Instantiated
        || (preserve_const_enums && module_state == ModuleInstanceState::ConstEnumOnly)
}

/// `NodeHasName(statement, id)`.
pub fn node_has_name(statement: NodeId, id: NodeId, nodes: &[Node]) -> bool {
    if let Some(name) = nodes[statement].name() {
        return is_identifier(&nodes[name]) && nodes[name].text(nodes) == nodes[id].text(nodes);
    }
    if is_variable_statement(&nodes[statement]) {
        let declarations = nodes[statement]
            .as_variable_statement()
            .declaration_list
            .map(|dl| {
                nodes[dl]
                    .as_variable_declaration_list()
                    .declarations
                    .as_ref()
                    .map(|d| d.nodes().to_vec())
                    .unwrap_or_default()
            })
            .unwrap_or_default();
        return declarations
            .iter()
            .any(|&d| node_has_name(d, id, nodes));
    }
    false
}

/// `IsInternalModuleImportEqualsDeclaration(node)`.
pub fn is_internal_module_import_equals_declaration(node: &Node, nodes: &[Node]) -> bool {
    is_import_equals_declaration(node)
        && nodes[node.as_import_equals_declaration().module_reference.unwrap()].kind
            != Kind::ExternalModuleReference
}

/// `IsConstAssertion(node)` — `expr as const` or `<const>expr`.
pub fn is_const_assertion(node: &Node, nodes: &[Node]) -> bool {
    match node.kind {
        Kind::AsExpression | Kind::TypeAssertionExpression => node
            .type_()
            .is_some_and(|t| is_const_type_reference(&nodes[t], nodes)),
        _ => false,
    }
}

/// `IsConstTypeReference(node)`.
pub fn is_const_type_reference(node: &Node, nodes: &[Node]) -> bool {
    is_type_reference_node(node)
        && node.type_arguments().is_none_or(|args| args.is_empty())
        && node.as_type_reference_node().type_name.is_some_and(|tn| {
            is_identifier(&nodes[tn]) && nodes[tn].text(nodes) == "const"
        })
}

/// `IsGlobalSourceFile(node)`.
pub fn is_global_source_file(node: &Node, nodes: &[Node]) -> bool {
    node.kind == Kind::SourceFile && !is_external_or_commonjs_module(nodes[node.id].as_source_file())
}

// PORT: `is_global_source_file` takes `&Node` but reaches back into the arena
// for `as_source_file` — the `nodes` param satisfies that; the `node.id`
// round-trip mirrors Go's `node.AsSourceFile()`.

/// `IsParameterLike(node)` — might be `IsIdentifier` for computed property
/// names in old AST — checks kinds here.
pub fn is_parameter_like(node: &Node) -> bool {
    matches!(node.kind, Kind::Parameter | Kind::TypeParameter)
}

/// `GetDeclarationOfKind(symbol, kind)`.
pub fn get_declaration_of_kind(symbol: &Symbol, kind: Kind, nodes: &[Node]) -> Option<NodeId> {
    for &declaration in &symbol.declarations {
        if nodes[declaration].kind == kind {
            return Some(declaration);
        }
    }
    None
}

/// `FindConstructorDeclaration(node)` — the constructor with a body.
pub fn find_constructor_declaration(node: &Node, nodes: &[Node]) -> Option<NodeId> {
    for &member in node.members().unwrap_or(&[]) {
        if is_constructor_declaration(&nodes[member])
            && node_is_present(nodes[member].body(), nodes)
        {
            return Some(member);
        }
    }
    None
}

/// `GetFirstIdentifier(node)`.
pub fn get_first_identifier(node: NodeId, nodes: &[Node]) -> NodeId {
    match nodes[node].kind {
        Kind::Identifier => node,
        Kind::QualifiedName => {
            get_first_identifier(nodes[node].as_qualified_name().left.unwrap(), nodes)
        }
        Kind::PropertyAccessExpression => {
            get_first_identifier(nodes[node].expression().unwrap(), nodes)
        }
        _ => panic!("Unhandled case in GetFirstIdentifier"),
    }
}

/// `GetNamespaceDeclarationNode(node)`.
pub fn get_namespace_declaration_node(node: &Node, nodes: &[Node]) -> Option<NodeId> {
    match node.kind {
        Kind::ImportDeclaration | Kind::JSImportDeclaration => {
            if let Some(import_clause) = node.import_clause() {
                if let Some(named_bindings) = nodes[import_clause].as_import_clause().named_bindings
                {
                    if is_namespace_import(&nodes[named_bindings]) {
                        return Some(named_bindings);
                    }
                }
            }
            None
        }
        Kind::ImportEqualsDeclaration => Some(node.id),
        Kind::ExportDeclaration => {
            let export_clause = node.as_export_declaration().export_clause;
            if let Some(clause) = export_clause {
                if is_namespace_export(&nodes[clause]) {
                    return Some(clause);
                }
            }
            None
        }
        _ => panic!("Unhandled case in getNamespaceDeclarationNode"),
    }
}

/// `ModuleExportNameIsDefault(node)`.
pub fn module_export_name_is_default(node: &Node, nodes: &[Node]) -> bool {
    node.text(nodes) == "default"
}

/// `IsDefaultImport(node)` — `ImportDeclaration | ImportEqualsDeclaration |
/// ExportDeclaration`.
pub fn is_default_import(node: &Node, nodes: &[Node]) -> bool {
    match node.kind {
        Kind::ImportDeclaration | Kind::JSImportDeclaration => {
            node.import_clause().is_some_and(|clause| {
                nodes[clause].as_import_clause().name.is_some()
            })
        }
        _ => false,
    }
}

/// `GetImpliedNodeFormatForFile(fileName, packageJsonType)`.
pub fn get_implied_node_format_for_file(
    file_name: &RootedFilePath,
    package_json_type: &str,
) -> ModuleKind {
    let mut implied_node_format = ResolutionMode::None;
    if file_name.extension_is_one_of(&[
        tspath::EXTENSION_DMTS,
        tspath::EXTENSION_MTS,
        tspath::EXTENSION_MJS,
    ]) {
        implied_node_format = ModuleKind::ESNext;
    } else if file_name.extension_is_one_of(&[
        tspath::EXTENSION_DCTS,
        tspath::EXTENSION_CTS,
        tspath::EXTENSION_CJS,
    ]) {
        implied_node_format = ModuleKind::CommonJS;
    } else if file_name.extension_is_one_of(&[
        tspath::EXTENSION_DTS,
        tspath::EXTENSION_TS,
        tspath::EXTENSION_TSX,
        tspath::EXTENSION_JS,
        tspath::EXTENSION_JSX,
    ]) {
        implied_node_format = if package_json_type == "module" {
            ModuleKind::ESNext
        } else {
            ModuleKind::CommonJS
        };
    }
    implied_node_format
}

/// `GetEmitModuleFormatOfFileWorker(fileName, options, sourceFileMetaData)`.
pub fn get_emit_module_format_of_file_worker(
    file_name: &RootedFilePath,
    options: &CompilerOptions,
    source_file_meta_data: &SourceFileMetaData,
) -> ModuleKind {
    let result = get_implied_node_format_for_emit_worker(
        file_name,
        options.get_emit_module_kind(),
        source_file_meta_data,
    );
    if result != ModuleKind::None {
        return result;
    }
    options.get_emit_module_kind()
}

/// `GetImpliedNodeFormatForEmitWorker(fileName, emitModuleKind, sourceFileMetaData)`.
pub fn get_implied_node_format_for_emit_worker(
    file_name: &RootedFilePath,
    emit_module_kind: ModuleKind,
    source_file_meta_data: &SourceFileMetaData,
) -> ResolutionMode {
    if (ModuleKind::Node16..=ModuleKind::NodeNext).contains(&emit_module_kind) {
        return source_file_meta_data.implied_node_format;
    }
    if source_file_meta_data.implied_node_format == ModuleKind::CommonJS
        && (source_file_meta_data.package_json_type == "commonjs"
            || file_name.extension_is_one_of(&[tspath::EXTENSION_CJS, tspath::EXTENSION_CTS]))
    {
        return ModuleKind::CommonJS;
    }
    if source_file_meta_data.implied_node_format == ModuleKind::ESNext
        && (source_file_meta_data.package_json_type == "module"
            || file_name.extension_is_one_of(&[tspath::EXTENSION_MJS, tspath::EXTENSION_MTS]))
    {
        return ModuleKind::ESNext;
    }
    ModuleKind::None
}

/// `GetDeclarationContainer(node)`.
pub fn get_declaration_container(node: NodeId, nodes: &[Node]) -> Option<NodeId> {
    find_ancestor(
        Some(get_root_declaration(node, nodes)),
        nodes,
        &mut |n, _| {
            !matches!(
                n.kind,
                Kind::VariableDeclaration
                    | Kind::VariableDeclarationList
                    | Kind::ImportSpecifier
                    | Kind::NamedImports
                    | Kind::NamespaceImport
                    | Kind::ImportClause
            )
        },
    )
    .and_then(|container| nodes[container].parent)
}

/// `IsNonLocalAlias(symbol, excludes)` — indicates that a symbol is an alias
/// that does not merge with a local declaration, or a JSContainer which may
/// merge an alias with a local declaration.
pub fn is_non_local_alias(symbol: Option<&Symbol>, excludes: SymbolFlags) -> bool {
    let Some(symbol) = symbol else {
        return false;
    };
    symbol.flags & (SymbolFlags::ALIAS | excludes) == SymbolFlags::ALIAS
        || (symbol.flags.intersects(SymbolFlags::ALIAS)
            && symbol.flags.intersects(SymbolFlags::ASSIGNMENT))
}

/// `IsAliasSymbolDeclaration(node)` — an alias symbol is created by one of:
/// `import <symbol> = ...`, `const <symbol> = ...` (JS only), destructured
/// `const { <symbol>, ... } = ...` (JS only), `import <symbol> from ...`,
/// `import * as <symbol> from ...`, `import { x as <symbol> } from ...`,
/// `export { x as <symbol> } from ...`, `export * as ns <symbol> from ...`,
/// `export = <EntityNameExpression>`, `export default <EntityNameExpression>`,
/// `module.exports = <EntityNameExpression>` (JS only), etc.
pub fn is_alias_symbol_declaration(node: NodeId, nodes: &[Node]) -> bool {
    let n = &nodes[node];
    match n.kind {
        Kind::ImportEqualsDeclaration
        | Kind::NamespaceExportDeclaration
        | Kind::NamespaceImport
        | Kind::NamespaceExport
        | Kind::ImportSpecifier
        | Kind::ExportSpecifier => true,
        Kind::ImportClause => n.as_import_clause().name.is_some(),
        Kind::ExportAssignment => {
            n.expression()
                .is_some_and(|e| expression_is_alias(&nodes[e], nodes))
        }
        Kind::VariableDeclaration | Kind::BindingElement => {
            is_variable_declaration_initialized_to_require(node, nodes)
        }
        Kind::BinaryExpression => match get_assignment_declaration_kind(node, nodes) {
            JsDeclarationKind::ModuleExports | JsDeclarationKind::ExportsProperty => {
                let right = n.as_binary_expression().right.unwrap();
                expression_is_alias(&nodes[right], nodes)
            }
            _ => false,
        },
        _ => false,
    }
}

/// `IsParseTreeNode(node)`.
pub fn is_parse_tree_node(node: &Node) -> bool {
    !node.flags.intersects(NodeFlags::SYNTHESIZED)
}

/// `GetNodeAtPosition(file, position, includeJSDoc)` — returns the innermost
/// node containing `position` (including the leading trivia of the node start),
/// or the containing node when `position` lands on a `MetaProperty` name.
///
/// PORT(deferred): the `includeJSDoc` branch iterates `current.JSDoc(file)`,
/// which requires the unported lazy JSDoc resolution cache. When
/// `include_jsdoc` is `true`, JSDoc children are simply not scanned here.
pub fn get_node_at_position(
    file: NodeId,
    position: TextPos,
    include_jsdoc: bool,
    nodes: &[Node],
) -> NodeId {
    let _ = include_jsdoc;
    let mut current = file;
    loop {
        let mut child = None;
        nodes[current].for_each_child(nodes, &mut |n| {
            if node_contains_position(&nodes[n], position) {
                child = Some(n);
                return true;
            }
            false
        });
        match child {
            None => return current,
            Some(c) if is_meta_property(&nodes[c]) => return current,
            Some(c) => current = c,
        }
    }
}

/// `nodeContainsPosition(node, position)`.
fn node_contains_position(node: &Node, position: TextPos) -> bool {
    node.kind >= Kind::FIRST_NODE
        && node.pos() <= position
        && (position < node.end()
            || (position == node.end() && node.kind == Kind::EndOfFile))
}

/// `findImportOrRequire(text, start)` — returns `(index, size)` of the next
/// `import`/`require` token-ish occurrence, or `(-1, 0)`.
pub fn find_import_or_require(text: &str, start: i32) -> (i32, i32) {
    let bytes = text.as_bytes();
    let n = bytes.len() as i32;
    let mut index = start.max(0);
    while index < n {
        let rel = bytes[index as usize..]
            .iter()
            .position(|&b| b == b'i' || b == b'r');
        let Some(next) = rel else { break };
        index += next as i32;
        let (size, expected): (i32, &[u8]) = if bytes[index as usize] == b'i' {
            (6, b"import")
        } else {
            (7, b"require")
        };
        if index + size <= n
            && &bytes[index as usize..(index + size) as usize] == expected
        {
            return (index, size);
        }
        index += 1;
    }
    (-1, 0)
}

/// `ForEachDynamicImportOrRequireCall(file, includeTypeSpaceImports,
/// requireStringLiteralLikeArgument, cb)` — iterates every dynamic
/// `import(...)`/`require(...)` call (and, when requested, literal import type
/// nodes) found by a textual scan of `file.text`.
pub fn for_each_dynamic_import_or_require_call(
    file: NodeId,
    include_type_space_imports: bool,
    require_string_literal_like_argument: bool,
    cb: &mut dyn FnMut(NodeId, NodeId) -> bool,
    nodes: &[Node],
) -> bool {
    let is_java_script_file = is_in_js_file(Some(file), nodes);
    let text = nodes[file].as_source_file().text.clone();
    let (mut last_index, mut size) = find_import_or_require(&text, 0);
    while last_index >= 0 {
        let node = get_node_at_position(
            file,
            last_index,
            is_java_script_file && include_type_space_imports,
            nodes,
        );
        if is_java_script_file
            && is_require_call(&nodes[node], require_string_literal_like_argument, nodes)
        {
            if cb(node, nodes[node].arguments().unwrap()[0]) {
                return true;
            }
        } else if is_import_call(&nodes[node], nodes)
            && !nodes[node].arguments().unwrap().is_empty()
            && (!require_string_literal_like_argument
                || is_string_literal_like(&nodes[nodes[node].arguments().unwrap()[0]]))
        {
            if cb(node, nodes[node].arguments().unwrap()[0]) {
                return true;
            }
        } else if include_type_space_imports && is_literal_import_type_node(&nodes[node], nodes) {
            let literal = nodes[nodes[node].as_import_type_node().argument.unwrap()]
                .as_literal_type_node()
                .literal
                .unwrap();
            if cb(node, literal) {
                return true;
            }
        }
        last_index += size;
        let r = find_import_or_require(&text, last_index);
        last_index = r.0;
        size = r.1;
    }
    false
}

/// `IsRequireCall(node, requireStringLiteralLikeArgument)` — true for a
/// `CallExpression` on the identifier `require` with exactly one argument.
/// Does not test whether the node is in a JavaScript file.
pub fn is_require_call(
    node: &Node,
    require_string_literal_like_argument: bool,
    nodes: &[Node],
) -> bool {
    if !is_call_expression(node) {
        return false;
    }
    let call = node.as_call_expression();
    let expr = match call.expression {
        Some(e) => e,
        None => return false,
    };
    if !is_identifier(&nodes[expr]) || nodes[expr].text(nodes) != "require" {
        return false;
    }
    let args = call.arguments.as_ref().map(|a| a.nodes()).unwrap_or(&[]);
    if args.len() != 1 {
        return false;
    }
    !require_string_literal_like_argument || is_string_literal_like(&nodes[args[0]])
}

/// `IsRequireVariableStatement(node)`.
pub fn is_require_variable_statement(node: &Node, nodes: &[Node]) -> bool {
    if is_variable_statement(node) {
        if let Some(dl) = node.as_variable_statement().declaration_list {
            let declarations = nodes[dl]
                .as_variable_declaration_list()
                .declarations
                .as_ref()
                .map(|d| d.nodes())
                .unwrap_or(&[]);
            if !declarations.is_empty() {
                return declarations
                    .iter()
                    .all(|&d| is_variable_declaration_initialized_to_require(d, nodes));
            }
        }
    }
    false
}

/// `GetJSXImplicitImportBase(compilerOptions, file)` — `file` may be `None`
/// (Go accepts nil through `GetPragmaFromSourceFile`).
pub fn get_jsx_implicit_import_base(
    compiler_options: &CompilerOptions,
    file: Option<&SourceFile>,
) -> String {
    let jsx_import_source_pragma = file.and_then(|f| get_pragma_from_source_file(f, "jsximportsource"));
    let jsx_runtime_pragma = file.and_then(|f| get_pragma_from_source_file(f, "jsxruntime"));
    if get_pragma_argument(jsx_runtime_pragma, "factory") == "classic" {
        return String::new();
    }
    if compiler_options.jsx == JsxEmit::ReactJSX
        || compiler_options.jsx == JsxEmit::ReactJSXDev
        || !compiler_options.jsx_import_source.is_empty()
        || jsx_import_source_pragma.is_some()
        || get_pragma_argument(jsx_runtime_pragma, "factory") == "automatic"
    {
        let mut result = get_pragma_argument(jsx_import_source_pragma, "factory");
        if result.is_empty() {
            result = compiler_options.jsx_import_source.clone();
        }
        if result.is_empty() {
            result = "react".to_string();
        }
        return result;
    }
    String::new()
}

/// `GetJSXRuntimeImport(base, options)`.
pub fn get_jsx_runtime_import(base: &str, options: &CompilerOptions) -> String {
    if base.is_empty() {
        return base.to_string();
    }
    let suffix = if options.jsx == JsxEmit::ReactJSXDev {
        "jsx-dev-runtime"
    } else {
        "jsx-runtime"
    };
    format!("{}/{}", base, suffix)
}

/// `GetPragmaFromSourceFile(file, name)` — last pragma wins.
pub fn get_pragma_from_source_file<'a>(
    file: &'a SourceFile,
    name: &str,
) -> Option<&'a crate::ast::Pragma> {
    let mut result = None;
    for pragma in file.pragmas.iter() {
        if pragma.name == name {
            result = Some(pragma);
        }
    }
    result
}

/// `GetPragmaArgument(pragma, name)`.
pub fn get_pragma_argument(pragma: Option<&crate::ast::Pragma>, name: &str) -> String {
    if let Some(pragma) = pragma {
        if let Some(arg) = pragma.args.get(name) {
            return arg.value.clone();
        }
    }
    String::new()
}

/// `IsVariableDeclarationInitializedToRequire(node)` — `const x = require("x")`
/// / `const { x } = require("x")` (or `var`/`let`). The variable must not be
/// exported and must not have a type annotation.
pub fn is_variable_declaration_initialized_to_require(node: NodeId, nodes: &[Node]) -> bool {
    let mut node = node;
    if nodes[node].kind == Kind::BindingElement {
        node = nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .expect("nil grandparent in IsVariableDeclarationInitializedToRequire");
    }
    is_variable_declaration_initialized_with_require_helper(node, false, nodes)
}

/// `IsVariableDeclarationInitializedToBareOrAccessedRequire(node)`.
pub fn is_variable_declaration_initialized_to_bare_or_accessed_require(
    node: NodeId,
    nodes: &[Node],
) -> bool {
    is_variable_declaration_initialized_with_require_helper(node, true, nodes)
}

/// `isVariableDeclarationInitializedWithRequireHelper(node, allowAccessedRequire)`.
fn is_variable_declaration_initialized_with_require_helper(
    node: NodeId,
    allow_accessed_require: bool,
    nodes: &[Node],
) -> bool {
    if !is_in_js_file(Some(node), nodes) {
        return false;
    }
    if nodes[node].kind != Kind::VariableDeclaration {
        return false;
    }
    let Some(mut initializer) = nodes[node].initializer() else {
        return false;
    };
    if allow_accessed_require {
        initializer = get_leftmost_access_expression(initializer, nodes);
    }
    let grandparent = nodes[node]
        .parent
        .and_then(|p| nodes[p].parent)
        .expect("nil grandparent in isVariableDeclarationInitializedWithRequireHelper");
    nodes[grandparent]
        .modifier_flags()
        .intersects(ModifierFlags::EXPORT)
        == false
        && nodes[node].type_().is_none()
        && is_require_call(&nodes[initializer], true, nodes)
}

/// `GetModuleSpecifierOfBareOrAccessedRequire(node)`.
pub fn get_module_specifier_of_bare_or_accessed_require(
    node: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    if is_variable_declaration_initialized_with_require_helper(node, false, nodes) {
        return Some(nodes[node].arguments().unwrap()[0]);
    }
    if is_variable_declaration_initialized_with_require_helper(node, true, nodes) {
        let leftmost = get_leftmost_access_expression(nodes[node].initializer().unwrap(), nodes);
        if is_require_call(&nodes[leftmost], true, nodes) {
            return Some(nodes[leftmost].arguments().unwrap()[0]);
        }
    }
    None
}

/// `IsModuleExportsAccessExpression(node)` — `module.exports`.
pub fn is_module_exports_access_expression(node: &Node, nodes: &[Node]) -> bool {
    if is_access_expression(node) && node.expression().is_some_and(|e| is_module_identifier(&nodes[e], nodes)) {
        if let Some(name) = get_element_or_property_access_name(node, nodes) {
            return nodes[name].text(nodes) == "exports";
        }
    }
    false
}

/// `IsModuleExportsQualifiedName(node)` — the qualified name `module.exports`.
pub fn is_module_exports_qualified_name(node: &Node, nodes: &[Node]) -> bool {
    is_qualified_name(node)
        && is_module_identifier(&nodes[node.as_qualified_name().left.unwrap()], nodes)
        && nodes[node.as_qualified_name().right.unwrap()].text(nodes) == "exports"
}

/// `IsCheckJSEnabledForFile(sourceFile, compilerOptions)`.
pub fn is_check_js_enabled_for_file(
    source_file: &SourceFile,
    compiler_options: &CompilerOptions,
) -> bool {
    if let Some(directive) = &source_file.check_js_directive {
        return directive.enabled;
    }
    compiler_options.check_js == TS_TRUE
}

/// `IsPlainJSFile(file, checkJs)`.
pub fn is_plain_js_file(file: Option<&SourceFile>, check_js: Tristate) -> bool {
    let Some(file) = file else {
        return false;
    };
    (file.script_kind == tsc_core::scriptkind::ScriptKind::Js
        || file.script_kind == tsc_core::scriptkind::ScriptKind::Jsx)
        && file.check_js_directive.is_none()
        && check_js == TS_UNKNOWN
}

/// `GetLeftmostAccessExpression(expr)`.
pub fn get_leftmost_access_expression(mut expr: NodeId, nodes: &[Node]) -> NodeId {
    while is_access_expression(&nodes[expr]) {
        expr = nodes[expr].expression().unwrap();
    }
    expr
}

/// `IsTypeOnlyImportDeclaration(node)`.
pub fn is_type_only_import_declaration(node: NodeId, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::ImportSpecifier => {
            nodes[node].is_type_only()
                || nodes[nodes[node]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .expect("nil grandparent in IsTypeOnlyImportDeclaration")]
                .is_type_only()
        }
        Kind::NamespaceImport => nodes[nodes[node]
            .parent
            .expect("nil parent in IsTypeOnlyImportDeclaration")]
        .is_type_only(),
        Kind::ImportClause | Kind::ImportEqualsDeclaration => nodes[node].is_type_only(),
        _ => false,
    }
}

/// `isTypeOnlyExportDeclaration(node)`.
fn is_type_only_export_declaration(node: NodeId, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::ExportSpecifier => {
            nodes[node].is_type_only()
                || nodes[nodes[node]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .expect("nil grandparent in isTypeOnlyExportDeclaration")]
                .is_type_only()
        }
        Kind::ExportDeclaration => {
            let d = nodes[node].as_export_declaration();
            d.is_type_only && d.module_specifier.is_some() && d.export_clause.is_none()
        }
        Kind::NamespaceExport => nodes[nodes[node]
            .parent
            .expect("nil parent in isTypeOnlyExportDeclaration")]
        .is_type_only(),
        _ => false,
    }
}

/// `IsTypeOnlyImportOrExportDeclaration(node)`.
pub fn is_type_only_import_or_export_declaration(node: NodeId, nodes: &[Node]) -> bool {
    is_type_only_import_declaration(node, nodes) || is_type_only_export_declaration(node, nodes)
}

/// `IsExclusivelyTypeOnlyImportOrExport(node)`.
pub fn is_exclusively_type_only_import_or_export(node: NodeId, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::ExportDeclaration => nodes[node].is_type_only(),
        Kind::ImportDeclaration | Kind::JSImportDeclaration => {
            if let Some(import_clause) = nodes[node].import_clause() {
                return nodes[import_clause].as_import_clause().is_type_only;
            }
            false
        }
        Kind::JSDocImportTag => {
            if let Some(import_clause) = nodes[node].import_clause() {
                return nodes[import_clause].as_import_clause().is_type_only;
            }
            false
        }
        _ => false,
    }
}

/// `GetClassLikeDeclarationOfSymbol(symbol)`.
pub fn get_class_like_declaration_of_symbol(
    symbol: &Symbol,
    nodes: &[Node],
) -> Option<NodeId> {
    symbol
        .declarations
        .iter()
        .copied()
        .find(|&d| is_class_like(Some(d), nodes))
}

/// `IsCallLikeExpression(node)`.
pub fn is_call_like_expression(node: &Node, _nodes: &[Node]) -> bool {
    match node.kind {
        Kind::JsxOpeningElement
        | Kind::JsxSelfClosingElement
        | Kind::JsxOpeningFragment
        | Kind::CallExpression
        | Kind::NewExpression
        | Kind::TaggedTemplateExpression
        | Kind::Decorator => true,
        Kind::BinaryExpression => {
            node.as_binary_expression().operator_token == Kind::InstanceOfKeyword
        }
        _ => false,
    }
}

/// `IsJsxCallLike(node)`.
pub fn is_jsx_call_like(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::JsxOpeningElement | Kind::JsxSelfClosingElement | Kind::JsxOpeningFragment
    )
}

/// `IsCallLikeOrFunctionLikeExpression(node)`.
pub fn is_call_like_or_function_like_expression(node: &Node, nodes: &[Node]) -> bool {
    is_call_like_expression(node, nodes)
        || is_function_expression_or_arrow_function(node)
}

/// `NodeHasKind(node, kind)` — `node` may be `None` (Go's nil `*Node`).
pub fn node_has_kind(node: Option<NodeId>, kind: Kind, nodes: &[Node]) -> bool {
    node.is_some_and(|n| nodes[n].kind == kind)
}

/// `IsContextualKeyword(token)`.
pub fn is_contextual_keyword(token: Kind) -> bool {
    Kind::FIRST_CONTEXTUAL_KEYWORD <= token && token <= Kind::LAST_CONTEXTUAL_KEYWORD
}

/// `IsThisInTypeQuery(node)` — `this` in a `typeof this.x` position.
pub fn is_this_in_type_query(mut node: NodeId, nodes: &[Node]) -> bool {
    if !is_this_identifier(&nodes[node]) {
        return false;
    }
    while nodes[node].parent.is_some_and(|p| {
        is_qualified_name(&nodes[p]) && nodes[p].as_qualified_name().left == Some(node)
    }) {
        node = nodes[node].parent.unwrap();
    }
    nodes[nodes[node].parent.expect("nil parent in IsThisInTypeQuery")].kind == Kind::TypeQuery
}

/// `IsClassMemberModifier(token)`.
pub fn is_class_member_modifier(token: Kind) -> bool {
    is_parameter_property_modifier(token)
        || token == Kind::StaticKeyword
        || token == Kind::OverrideKeyword
        || token == Kind::AccessorKeyword
}

// PORT(deferred): `ForEachChildAndJSDoc(node, sourceFile, v)` — requires
// `Node.JSDoc(sourceFile)` (the lazy JSDoc resolution cache), which is not yet
// ported to this crate.

/// `HasTypeArguments(node)`.
pub fn has_type_arguments(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::CallExpression
            | Kind::NewExpression
            | Kind::TaggedTemplateExpression
            | Kind::TypeReference
            | Kind::ExpressionWithTypeArguments
            | Kind::ImportType
            | Kind::TypeQuery
            | Kind::JsxOpeningElement
            | Kind::JsxSelfClosingElement
    )
}

/// `IsTypeReferenceType(node)`.
pub fn is_type_reference_type(node: &Node) -> bool {
    node.kind == Kind::TypeReference || node.kind == Kind::ExpressionWithTypeArguments
}

/// `IsVariableLike(node)`.
pub fn is_variable_like(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::BindingElement
            | Kind::EnumMember
            | Kind::Parameter
            | Kind::PropertyAssignment
            | Kind::PropertyDeclaration
            | Kind::PropertySignature
            | Kind::ShorthandPropertyAssignment
            | Kind::VariableDeclaration
    )
}

/// `HasInitializer(node)`.
pub fn has_initializer(node: &Node) -> bool {
    match node.kind {
        Kind::VariableDeclaration
        | Kind::Parameter
        | Kind::BindingElement
        | Kind::PropertyDeclaration
        | Kind::PropertyAssignment
        | Kind::EnumMember
        | Kind::ForStatement
        | Kind::ForInStatement
        | Kind::ForOfStatement
        | Kind::JsxAttribute => node.initializer().is_some(),
        _ => false,
    }
}

/// `IsVariableParameterOrProperty(node)`.
pub fn is_variable_parameter_or_property(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::VariableDeclaration
            | Kind::Parameter
            | Kind::PropertySignature
            | Kind::PropertyDeclaration
    )
}

/// `GetTypeAnnotationNode(node)`.
pub fn get_type_annotation_node(node: &Node) -> Option<NodeId> {
    match node.kind {
        Kind::VariableDeclaration
        | Kind::Parameter
        | Kind::PropertySignature
        | Kind::PropertyDeclaration
        | Kind::TypePredicate
        | Kind::ParenthesizedType
        | Kind::TypeOperator
        | Kind::MappedType
        | Kind::TypeAssertionExpression
        | Kind::AsExpression
        | Kind::SatisfiesExpression
        | Kind::TypeAliasDeclaration
        | Kind::JSTypeAliasDeclaration
        | Kind::NamedTupleMember
        | Kind::OptionalType
        | Kind::RestType
        | Kind::TemplateLiteralTypeSpan
        | Kind::JSDocTypeExpression
        | Kind::JSDocParameterTag
        | Kind::JSDocPropertyTag
        | Kind::JSDocNullableType
        | Kind::JSDocNonNullableType
        | Kind::JSDocOptionalType => node.type_(),
        _ => node.function_like_data().and_then(|f| f.type_),
    }
}

/// `IsObjectTypeDeclaration(node)`.
pub fn is_object_type_declaration(node: &Node, nodes: &[Node]) -> bool {
    is_class_like(Some(node.id), nodes)
        || is_interface_declaration(node)
        || is_type_literal_node(node)
}

/// `IsClassOrTypeElement(node)`.
pub fn is_class_or_type_element(node: &Node) -> bool {
    is_class_element(node) || is_type_element(node)
}

/// `GetClassExtendsHeritageElement(node)`.
pub fn get_class_extends_heritage_element<'a>(
    node: &Node,
    nodes: &'a [Node],
) -> Option<&'a [NodeId]> {
    get_heritage_elements(node, Kind::ExtendsKeyword, nodes)
}

/// `GetClassExtendsHeritageElementNode(node)` — the first `extends` element.
pub fn get_class_extends_heritage_element_node(
    node: &Node,
    nodes: &[Node],
) -> Option<NodeId> {
    get_heritage_elements(node, Kind::ExtendsKeyword, nodes)
        .and_then(|elements| elements.first().copied())
}

/// `IsTypeKeywordToken(node)`.
pub fn is_type_keyword_token(node: &Node) -> bool {
    node.kind == Kind::TypeKeyword
}

/// `hasComment(kind)` — node kinds that have a `comment` property.
fn has_comment(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::JSDoc
            | Kind::JSDocUnknownTag
            | Kind::JSDocAugmentsTag
            | Kind::JSDocImplementsTag
            | Kind::JSDocDeprecatedTag
            | Kind::JSDocPublicTag
            | Kind::JSDocPrivateTag
            | Kind::JSDocProtectedTag
            | Kind::JSDocReadonlyTag
            | Kind::JSDocOverrideTag
            | Kind::JSDocCallbackTag
            | Kind::JSDocOverloadTag
            | Kind::JSDocParameterTag
            | Kind::JSDocPropertyTag
            | Kind::JSDocReturnTag
            | Kind::JSDocThisTag
            | Kind::JSDocTypeTag
            | Kind::JSDocTemplateTag
            | Kind::JSDocTypedefTag
            | Kind::JSDocSeeTag
            | Kind::JSDocThrowsTag
            | Kind::JSDocSatisfiesTag
            | Kind::JSDocImportTag
    )
}

/// `IsJSDocSingleCommentNodeList(nodeList)` — see `IsJSDocSingleCommentNode`.
pub fn is_js_doc_single_comment_node_list(
    node_list: Option<&NodeList>,
    nodes: &[Node],
) -> bool {
    let Some(node_list) = node_list else {
        return false;
    };
    if node_list.nodes().is_empty() {
        return false;
    }
    let Some(parent) = nodes[node_list.nodes()[0]].parent else {
        return false;
    };
    is_js_doc_single_comment_node(&nodes[parent], nodes)
        && nodes[parent]
            .comment_list()
            .is_some_and(|c| std::ptr::eq(c, node_list))
}

/// `IsJSDocSingleCommentNodeComment(node)` — see `IsJSDocSingleCommentNode`.
pub fn is_js_doc_single_comment_node_comment(node: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(node) = node else {
        return false;
    };
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    is_js_doc_single_comment_node(&nodes[parent], nodes)
        && nodes[parent]
            .comment_list()
            .is_some_and(|c| c.nodes().first() == Some(&node))
}

/// `IsJSDocSingleCommentNode(node)` — in Strada, if a JSDoc node has a single
/// comment, that comment is represented as a string property and is therefore
/// not visited by `forEachChild`.
pub fn is_js_doc_single_comment_node(node: &Node, _nodes: &[Node]) -> bool {
    has_comment(node.kind)
        && node
            .comment_list()
            .is_some_and(|c| c.nodes().len() == 1)
}

/// `IsValidTypeOnlyAliasUseSite(useSite)`.
pub fn is_valid_type_only_alias_use_site(use_site: NodeId, nodes: &[Node]) -> bool {
    nodes[use_site]
        .flags
        .intersects(NodeFlags::AMBIENT | NodeFlags::J_S_DOC)
        || is_part_of_type_query(use_site, nodes)
        || is_identifier_in_non_emitting_heritage_clause(use_site, nodes)
        || is_part_of_possibly_valid_type_or_abstract_computed_property_name(use_site, nodes)
        || !(is_expression_node(use_site, nodes)
            || is_shorthand_property_name_use_site(use_site, nodes))
}

/// `isIdentifierInNonEmittingHeritageClause(node)`.
fn is_identifier_in_non_emitting_heritage_clause(node: NodeId, nodes: &[Node]) -> bool {
    if !is_identifier(&nodes[node]) {
        return false;
    }
    let mut parent = nodes[node].parent.expect("nil parent in isIdentifierInNonEmittingHeritageClause");
    while is_property_access_expression(&nodes[parent])
        || is_expression_with_type_arguments(&nodes[parent])
    {
        parent = nodes[parent].parent.expect("nil parent in isIdentifierInNonEmittingHeritageClause");
    }
    is_heritage_clause(&nodes[parent])
        && (nodes[parent].as_heritage_clause().token == Kind::ImplementsKeyword
            || is_interface_declaration(
                &nodes[nodes[parent].parent.expect("nil parent of heritage clause")],
            ))
}

/// `isPartOfPossiblyValidTypeOrAbstractComputedPropertyName(node)`.
fn is_part_of_possibly_valid_type_or_abstract_computed_property_name(
    mut node: NodeId,
    nodes: &[Node],
) -> bool {
    while node_kind_is(&nodes[node], &[Kind::Identifier, Kind::PropertyAccessExpression]) {
        node = nodes[node]
            .parent
            .expect("nil parent in isPartOfPossiblyValidTypeOrAbstractComputedPropertyName");
    }
    if nodes[node].kind != Kind::ComputedPropertyName {
        return false;
    }
    let parent = nodes[node]
        .parent
        .expect("nil parent of computed property name");
    if has_syntactic_modifier(&nodes[parent], ModifierFlags::ABSTRACT) {
        return true;
    }
    node_kind_is(
        &nodes[nodes[parent].parent.expect("nil grandparent of computed property name")],
        &[Kind::InterfaceDeclaration, Kind::TypeLiteral],
    )
}

/// `isShorthandPropertyNameUseSite(useSite)`.
fn is_shorthand_property_name_use_site(use_site: NodeId, nodes: &[Node]) -> bool {
    is_identifier(&nodes[use_site])
        && nodes[use_site].parent.is_some_and(|p| {
            is_shorthand_property_assignment(&nodes[p]) && nodes[p].name() == Some(use_site)
        })
}

/// `GetPropertyNameForPropertyNameNode(name)`.
pub fn get_property_name_for_property_name_node(name: NodeId, nodes: &[Node]) -> String {
    match nodes[name].kind {
        Kind::Identifier
        | Kind::PrivateIdentifier
        | Kind::StringLiteral
        | Kind::NoSubstitutionTemplateLiteral
        | Kind::NumericLiteral
        | Kind::BigIntLiteral
        | Kind::JsxNamespacedName => nodes[name].text(nodes).into_owned(),
        Kind::ComputedPropertyName => {
            let name_expression = nodes[name].expression().expect("nil expression");
            if is_string_or_numeric_literal_like(&nodes[name_expression]) {
                return nodes[name_expression].text(nodes).into_owned();
            }
            if is_signed_numeric_literal(&nodes[name_expression], nodes) {
                let unary = nodes[name_expression].as_prefix_unary_expression();
                let operand = unary.operand.expect("nil operand");
                let mut text = nodes[operand].text(nodes).into_owned();
                if unary.operator == Kind::MinusToken {
                    text = format!("-{}", text);
                }
                return text;
            }
            crate::symbol::INTERNAL_SYMBOL_NAME_MISSING.to_string()
        }
        _ => panic!("Unhandled case in getPropertyNameForPropertyNameNode"),
    }
}

/// `IsPartOfTypeOnlyImportOrExportDeclaration(node)`.
pub fn is_part_of_type_only_import_or_export_declaration(node: NodeId, nodes: &[Node]) -> bool {
    find_ancestor(Some(node), nodes, &mut |n, ns| {
        is_type_only_import_or_export_declaration(n.id, ns)
    })
    .is_some()
}

/// `IsEmittableImport(node)`.
pub fn is_emittable_import(node: &Node, nodes: &[Node]) -> bool {
    match node.kind {
        Kind::ImportDeclaration => {
            node.import_clause()
                .is_some_and(|c| !nodes[c].is_type_only())
        }
        Kind::ExportDeclaration | Kind::ImportEqualsDeclaration => !node.is_type_only(),
        Kind::CallExpression => is_import_call(node, nodes),
        _ => false,
    }
}

/// `IsResolutionModeOverrideHost(node)` — `node` may be `None`.
pub fn is_resolution_mode_override_host(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| {
        matches!(
            nodes[n].kind,
            Kind::ImportType
                | Kind::ExportDeclaration
                | Kind::ImportDeclaration
                | Kind::JSImportDeclaration
        )
    })
}

/// `ImportAttributesNode.GetResolutionModeOverride(grammarErrorOnNode)` —
/// `grammar_error_on_node` is invoked with the offending value node (the Go
/// diagnostic message is always
/// `X_resolution_mode_should_be_either_require_or_import`).
pub fn import_attributes_resolution_mode_override(
    attributes: Option<NodeId>,
    grammar_error_on_node: Option<&mut dyn FnMut(NodeId)>,
    nodes: &[Node],
) -> (ResolutionMode, bool) {
    let Some(attributes_node) = attributes else {
        return (ResolutionMode::None, false);
    };
    let attrs = nodes[attributes_node].as_import_attributes();
    let Some(list) = attrs.attributes.as_ref() else {
        return (ResolutionMode::None, false);
    };
    let attribute = list.nodes().iter().copied().find(|&a| {
        nodes[a].name().is_some_and(|n| nodes[n].text(nodes) == "resolution-mode")
    });
    let Some(attribute) = attribute else {
        return (ResolutionMode::None, false);
    };
    let elem = nodes[attribute].as_import_attribute();
    let Some(value) = elem.value else {
        return (ResolutionMode::None, false);
    };
    if !is_string_literal_like(&nodes[value]) {
        return (ResolutionMode::None, false);
    }
    let text = nodes[value].text(nodes);
    if text != "import" && text != "require" {
        if let Some(grammar_error_on_node) = grammar_error_on_node {
            grammar_error_on_node(value);
        }
        return (ResolutionMode::None, false);
    }
    if text == "import" {
        (tsc_core::compileroptions::RESOLUTION_MODE_ESM, true)
    } else {
        (ModuleKind::CommonJS, true)
    }
}

/// `HasResolutionModeOverride(node)` — `node` may be `None`.
pub fn has_resolution_mode_override(node: Option<NodeId>, nodes: &[Node]) -> bool {
    let Some(node) = node else {
        return false;
    };
    let attributes = match nodes[node].kind {
        Kind::ImportType => nodes[node].as_import_type_node().attributes,
        Kind::ImportDeclaration | Kind::JSImportDeclaration => {
            nodes[node].as_import_declaration().attributes
        }
        Kind::ExportDeclaration => nodes[node].as_export_declaration().attributes,
        _ => None,
    };
    if attributes.is_some() {
        let (_, ok) = import_attributes_resolution_mode_override(attributes, None, nodes);
        return ok;
    }
    false
}

/// `IsStringTextContainingNode(node)`.
pub fn is_string_text_containing_node(node: &Node) -> bool {
    node.kind == Kind::StringLiteral || is_template_literal_kind(node.kind)
}

/// `IsTemplateLiteralKind(kind)`.
pub fn is_template_literal_kind(kind: Kind) -> bool {
    Kind::FIRST_TEMPLATE_TOKEN <= kind && kind <= Kind::LAST_TEMPLATE_TOKEN
}

/// `IsTemplateLiteralToken(node)`.
pub fn is_template_literal_token(node: &Node) -> bool {
    is_template_literal_kind(node.kind)
}

/// `GetExternalModuleImportEqualsDeclarationExpression(node)` — panics if the
/// node is not an external `import = require(...)` declaration (Go's
/// `debug.Assert`).
pub fn get_external_module_import_equals_declaration_expression(
    node: &Node,
    nodes: &[Node],
) -> Option<NodeId> {
    debug_assert!(
        is_external_module_import_equals_declaration(node, nodes),
        "IsExternalModuleImportEqualsDeclaration(node) failed"
    );
    nodes[node.as_import_equals_declaration().module_reference.unwrap()]
        .expression()
}

/// `CreateModifiersFromModifierFlags(flags, createModifier)` — `create_modifier`
/// allocates a modifier token for the given kind.
pub fn create_modifiers_from_modifier_flags(
    flags: ModifierFlags,
    create_modifier: &mut dyn FnMut(Kind) -> NodeId,
) -> Vec<NodeId> {
    let mut result = Vec::new();
    let mut push = |flags: ModifierFlags, mask: ModifierFlags, kind: Kind| {
        if flags.intersects(mask) {
            result.push(create_modifier(kind));
        }
    };
    push(flags, ModifierFlags::EXPORT, Kind::ExportKeyword);
    push(flags, ModifierFlags::AMBIENT, Kind::DeclareKeyword);
    push(flags, ModifierFlags::DEFAULT, Kind::DefaultKeyword);
    push(flags, ModifierFlags::CONST, Kind::ConstKeyword);
    push(flags, ModifierFlags::PUBLIC, Kind::PublicKeyword);
    push(flags, ModifierFlags::PRIVATE, Kind::PrivateKeyword);
    push(flags, ModifierFlags::PROTECTED, Kind::ProtectedKeyword);
    push(flags, ModifierFlags::ABSTRACT, Kind::AbstractKeyword);
    push(flags, ModifierFlags::STATIC, Kind::StaticKeyword);
    push(flags, ModifierFlags::OVERRIDE, Kind::OverrideKeyword);
    push(flags, ModifierFlags::READONLY, Kind::ReadonlyKeyword);
    push(flags, ModifierFlags::ACCESSOR, Kind::AccessorKeyword);
    push(flags, ModifierFlags::ASYNC, Kind::AsyncKeyword);
    push(flags, ModifierFlags::IN, Kind::InKeyword);
    push(flags, ModifierFlags::OUT, Kind::OutKeyword);
    result
}

/// `GetThisParameter(signature)` — callback tags do not currently support
/// `this` parameters.
pub fn get_this_parameter(signature: &Node, nodes: &[Node]) -> Option<NodeId> {
    if let Some(parameters) = signature.parameters() {
        if !parameters.is_empty() {
            let this_parameter = parameters[0];
            if is_this_parameter(&nodes[this_parameter], nodes) {
                return Some(this_parameter);
            }
        }
    }
    None
}

/// `ReplaceModifiers(factory, node, modifierArray)` — returns the updated node
/// id, or `None` when nothing changed (matching the Rust `update_*`
/// convention; Go returns the input node pointer in that case).
///
/// PORT: the update functions take `nodes`/`NodeId` rather than struct
/// pointers; all preserved fields are re-read from `nodes[node]`.
#[allow(clippy::too_many_arguments)]
pub fn replace_modifiers(
    factory: &mut crate::ast::NodeFactory<'_>,
    nodes: &mut Vec<Node>,
    node: NodeId,
    modifier_array: Option<ModifierList>,
) -> Option<NodeId> {
    match nodes[node].kind {
        Kind::TypeParameter => {
            let d = nodes[node].as_type_parameter_declaration();
            let (name, constraint, expression, default_type) =
                (d.name, d.constraint, d.expression, d.default_type);
            factory.update_type_parameter_declaration(
                nodes,
                node,
                modifier_array,
                name,
                constraint,
                expression,
                default_type,
            )
        }
        Kind::Parameter => {
            let d = nodes[node].as_parameter_declaration();
            let (dot_dot_dot_token, name, question_token, type_node, initializer) = (
                d.dot_dot_dot_token,
                d.name,
                d.question_token,
                d.type_,
                d.initializer,
            );
            factory.update_parameter_declaration(
                nodes,
                node,
                modifier_array,
                dot_dot_dot_token,
                name,
                question_token,
                type_node,
                initializer,
            )
        }
        Kind::ConstructorType => {
            let d = nodes[node].as_constructor_type_node();
            let (type_parameters, parameters, type_node) = (
                d.function_like_base.type_parameters.clone(),
                d.function_like_base.parameters.clone(),
                d.function_like_base.type_,
            );
            factory.update_constructor_type_node(
                nodes,
                node,
                modifier_array,
                type_parameters,
                parameters,
                type_node,
            )
        }
        Kind::PropertySignature => {
            let d = nodes[node].as_property_signature_declaration();
            let (name, postfix_token, type_node, initializer) =
                (d.name, d.postfix_token, d.type_, d.initializer);
            factory.update_property_signature_declaration(
                nodes,
                node,
                modifier_array,
                name,
                postfix_token,
                type_node,
                initializer,
            )
        }
        Kind::PropertyDeclaration => {
            let d = nodes[node].as_property_declaration();
            let (name, postfix_token, type_node, initializer) =
                (d.name, d.postfix_token, d.type_, d.initializer);
            factory.update_property_declaration(
                nodes,
                node,
                modifier_array,
                name,
                postfix_token,
                type_node,
                initializer,
            )
        }
        Kind::MethodSignature => {
            let d = nodes[node].as_method_signature_declaration();
            let (name, postfix_token, type_parameters, parameters, type_node) = (
                d.name,
                d.postfix_token,
                d.function_like_base.type_parameters.clone(),
                d.function_like_base.parameters.clone(),
                d.function_like_base.type_,
            );
            factory.update_method_signature_declaration(
                nodes,
                node,
                modifier_array,
                name,
                postfix_token,
                type_parameters,
                parameters,
                type_node,
            )
        }
        Kind::MethodDeclaration => {
            let d = nodes[node].as_method_declaration();
            let fl = &d.function_like_with_body_base.function_like_base;
            let (asterisk_token, name, postfix_token, type_parameters, parameters, type_node) = (
                d.asterisk_token,
                d.name,
                d.postfix_token,
                fl.type_parameters.clone(),
                fl.parameters.clone(),
                fl.type_,
            );
            let (full_signature, body) =
                (fl.full_signature, d.function_like_with_body_base.body_base.body);
            factory.update_method_declaration(
                nodes,
                node,
                modifier_array,
                asterisk_token,
                name,
                postfix_token,
                type_parameters,
                parameters,
                type_node,
                full_signature,
                body,
            )
        }
        Kind::Constructor => {
            let d = nodes[node].as_constructor_declaration();
            let fl = &d.function_like_with_body_base.function_like_base;
            let (type_parameters, parameters, type_node, full_signature, body) = (
                fl.type_parameters.clone(),
                fl.parameters.clone(),
                fl.type_,
                fl.full_signature,
                d.function_like_with_body_base.body_base.body,
            );
            factory.update_constructor_declaration(
                nodes,
                node,
                modifier_array,
                type_parameters,
                parameters,
                type_node,
                full_signature,
                body,
            )
        }
        Kind::GetAccessor => {
            let d = nodes[node].as_get_accessor_declaration();
            let fl = &d.function_like_with_body_base.function_like_base;
            let (name, type_parameters, parameters, type_node, full_signature, body) = (
                d.name,
                fl.type_parameters.clone(),
                fl.parameters.clone(),
                fl.type_,
                fl.full_signature,
                d.function_like_with_body_base.body_base.body,
            );
            factory.update_get_accessor_declaration(
                nodes,
                node,
                modifier_array,
                name,
                type_parameters,
                parameters,
                type_node,
                full_signature,
                body,
            )
        }
        Kind::SetAccessor => {
            let d = nodes[node].as_set_accessor_declaration();
            let fl = &d.function_like_with_body_base.function_like_base;
            let (name, type_parameters, parameters, type_node, full_signature, body) = (
                d.name,
                fl.type_parameters.clone(),
                fl.parameters.clone(),
                fl.type_,
                fl.full_signature,
                d.function_like_with_body_base.body_base.body,
            );
            factory.update_set_accessor_declaration(
                nodes,
                node,
                modifier_array,
                name,
                type_parameters,
                parameters,
                type_node,
                full_signature,
                body,
            )
        }
        Kind::IndexSignature => {
            let d = nodes[node].as_index_signature_declaration();
            let (parameters, type_node) =
                (d.function_like_base.parameters.clone(), d.function_like_base.type_);
            factory.update_index_signature_declaration(
                nodes,
                node,
                modifier_array,
                parameters,
                type_node,
            )
        }
        Kind::FunctionExpression => {
            let d = nodes[node].as_function_expression();
            let fl = &d.function_like_with_body_base.function_like_base;
            let (asterisk_token, name, type_parameters, parameters, type_node) = (
                d.asterisk_token,
                d.name,
                fl.type_parameters.clone(),
                fl.parameters.clone(),
                fl.type_,
            );
            let (full_signature, body) =
                (fl.full_signature, d.function_like_with_body_base.body_base.body);
            factory.update_function_expression(
                nodes,
                node,
                modifier_array,
                asterisk_token,
                name,
                type_parameters,
                parameters,
                type_node,
                full_signature,
                body,
            )
        }
        Kind::ArrowFunction => {
            let d = nodes[node].as_arrow_function();
            let fl = &d.function_like_with_body_base.function_like_base;
            let equals_greater_than_token =
                d.function_like_with_body_base.equals_greater_than_token;
            let (type_parameters, parameters, type_node, full_signature, body) = (
                fl.type_parameters.clone(),
                fl.parameters.clone(),
                fl.type_,
                fl.full_signature,
                d.function_like_with_body_base.body_base.body,
            );
            factory.update_arrow_function(
                nodes,
                node,
                modifier_array,
                type_parameters,
                parameters,
                type_node,
                full_signature,
                equals_greater_than_token,
                body,
            )
        }
        Kind::ClassExpression => {
            let d = nodes[node].as_class_expression();
            let cl = &d.class_like_base;
            let (name, type_parameters, heritage_clauses, members) = (
                cl.name,
                cl.type_parameters.clone(),
                cl.heritage_clauses.clone(),
                cl.members.clone(),
            );
            factory.update_class_expression(
                nodes,
                node,
                modifier_array,
                name,
                type_parameters,
                heritage_clauses,
                members,
            )
        }
        Kind::VariableStatement => {
            let declaration_list = nodes[node].as_variable_statement().declaration_list;
            factory.update_variable_statement(nodes, node, modifier_array, declaration_list)
        }
        Kind::FunctionDeclaration => {
            let d = nodes[node].as_function_declaration();
            let fl = &d.function_like_with_body_base.function_like_base;
            let (asterisk_token, name, type_parameters, parameters, type_node) = (
                d.asterisk_token,
                d.name,
                fl.type_parameters.clone(),
                fl.parameters.clone(),
                fl.type_,
            );
            let (full_signature, body) =
                (fl.full_signature, d.function_like_with_body_base.body_base.body);
            factory.update_function_declaration(
                nodes,
                node,
                modifier_array,
                asterisk_token,
                name,
                type_parameters,
                parameters,
                type_node,
                full_signature,
                body,
            )
        }
        Kind::ClassDeclaration => {
            let d = nodes[node].as_class_declaration();
            let cl = &d.class_like_base;
            let (name, type_parameters, heritage_clauses, members) = (
                cl.name,
                cl.type_parameters.clone(),
                cl.heritage_clauses.clone(),
                cl.members.clone(),
            );
            factory.update_class_declaration(
                nodes,
                node,
                modifier_array,
                name,
                type_parameters,
                heritage_clauses,
                members,
            )
        }
        Kind::InterfaceDeclaration => {
            let d = nodes[node].as_interface_declaration();
            let (name, type_parameters, heritage_clauses, members) = (
                d.name,
                d.type_parameters.clone(),
                d.heritage_clauses.clone(),
                d.members.clone(),
            );
            factory.update_interface_declaration(
                nodes,
                node,
                modifier_array,
                name,
                type_parameters,
                heritage_clauses,
                members,
            )
        }
        Kind::TypeAliasDeclaration => {
            let d = nodes[node].as_type_alias_declaration();
            let (name, type_parameters, type_node) =
                (d.name, d.type_parameters.clone(), d.type_);
            factory.update_type_alias_declaration(
                nodes,
                node,
                modifier_array,
                name,
                type_parameters,
                type_node,
            )
        }
        Kind::EnumDeclaration => {
            let d = nodes[node].as_enum_declaration();
            let (name, members) = (d.name, d.members.clone());
            factory.update_enum_declaration(nodes, node, modifier_array, name, members)
        }
        Kind::ModuleDeclaration => {
            let d = nodes[node].as_module_declaration();
            let (keyword, name, attributes, body) =
                (d.keyword, d.name, d.attributes, d.body_base.body);
            factory.update_module_declaration(
                nodes,
                node,
                modifier_array,
                keyword,
                name,
                attributes,
                body,
            )
        }
        Kind::ImportEqualsDeclaration => {
            let d = nodes[node].as_import_equals_declaration();
            let (is_type_only, name, module_reference) =
                (d.is_type_only, d.name, d.module_reference);
            factory.update_import_equals_declaration(
                nodes,
                node,
                modifier_array,
                is_type_only,
                name,
                module_reference,
            )
        }
        Kind::ImportDeclaration => {
            let d = nodes[node].as_import_declaration();
            let (import_clause, module_specifier, attributes) =
                (d.import_clause, d.module_specifier, d.attributes);
            factory.update_import_declaration(
                nodes,
                node,
                modifier_array,
                import_clause,
                module_specifier,
                attributes,
            )
        }
        Kind::ExportAssignment => {
            let d = nodes[node].as_export_assignment();
            let (is_export_equals, type_node, expression) =
                (d.is_export_equals, d.type_, d.expression);
            factory.update_export_assignment(
                nodes,
                node,
                modifier_array,
                is_export_equals,
                type_node,
                expression,
            )
        }
        Kind::ExportDeclaration => {
            let d = nodes[node].as_export_declaration();
            let (is_type_only, export_clause, module_specifier, attributes) = (
                d.is_type_only,
                d.export_clause,
                d.module_specifier,
                d.attributes,
            );
            factory.update_export_declaration(
                nodes,
                node,
                modifier_array,
                is_type_only,
                export_clause,
                module_specifier,
                attributes,
            )
        }
        _ => panic!(
            "Node that does not have modifiers tried to have modifier replaced: {}",
            nodes[node].kind_string()
        ),
    }
}

/// `IsLateVisibilityPaintedStatement(node)`.
pub fn is_late_visibility_painted_statement(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::ImportDeclaration
            | Kind::JSImportDeclaration
            | Kind::ImportEqualsDeclaration
            | Kind::VariableStatement
            | Kind::ClassDeclaration
            | Kind::FunctionDeclaration
            | Kind::ModuleDeclaration
            | Kind::TypeAliasDeclaration
            | Kind::JSTypeAliasDeclaration
            | Kind::InterfaceDeclaration
            | Kind::EnumDeclaration
    )
}

/// `IsExternalModuleAugmentation(node)` — ambient module augmentation in an
/// external module.
pub fn is_external_module_augmentation(node: &Node, nodes: &[Node]) -> bool {
    is_ambient_module(node, nodes) && is_module_augmentation_external(node, nodes)
}

/// `GetSourceFileOfModule(module)`.
pub fn get_source_file_of_module(module: &Symbol, nodes: &[Node]) -> Option<NodeId> {
    let declaration = module
        .value_declaration
        .or_else(|| get_non_augmentation_declaration(module, nodes));
    get_source_file_of_node(declaration, nodes)
}

/// `GetNonAugmentationDeclaration(symbol)` — the first declaration that is not
/// an external module augmentation nor a `global` augmentation.
pub fn get_non_augmentation_declaration(symbol: &Symbol, nodes: &[Node]) -> Option<NodeId> {
    symbol.declarations.iter().copied().find(|&d| {
        !is_external_module_augmentation(&nodes[d], nodes)
            && !is_global_scope_augmentation(&nodes[d])
    })
}

/// `IsTypeDeclaration(node)`.
pub fn is_type_declaration(node: NodeId, nodes: &[Node]) -> bool {
    match nodes[node].kind {
        Kind::TypeParameter
        | Kind::ClassDeclaration
        | Kind::InterfaceDeclaration
        | Kind::TypeAliasDeclaration
        | Kind::JSTypeAliasDeclaration
        | Kind::EnumDeclaration => true,
        Kind::ImportClause => {
            nodes[node].is_type_only() && nodes[node].as_import_clause().name.is_some()
        }
        Kind::ImportSpecifier | Kind::ExportSpecifier => nodes[nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .expect("nil grandparent in IsTypeDeclaration")]
        .is_type_only(),
        _ => false,
    }
}

/// `IsTypeDeclarationName(name)`.
pub fn is_type_declaration_name(name: NodeId, nodes: &[Node]) -> bool {
    nodes[name].kind == Kind::Identifier
        && nodes[name]
            .parent
            .is_some_and(|p| is_type_declaration(p, nodes))
        && get_name_of_declaration(nodes[name].parent, nodes) == Some(name)
}

/// `IsRightSideOfPropertyAccess(node)`.
pub fn is_right_side_of_property_access(node: NodeId, nodes: &[Node]) -> bool {
    let parent = nodes[node].parent.expect("nil parent in IsRightSideOfPropertyAccess");
    nodes[parent].kind == Kind::PropertyAccessExpression
        && nodes[parent].name() == Some(node)
}

/// `IsArgumentExpressionOfElementAccess(node)`.
pub fn is_argument_expression_of_element_access(node: NodeId, nodes: &[Node]) -> bool {
    nodes[node].parent.is_some_and(|parent| {
        nodes[parent].kind == Kind::ElementAccessExpression
            && nodes[parent].as_element_access_expression().argument_expression == Some(node)
    })
}

/// `ClimbPastPropertyAccess(node)`.
pub fn climb_past_property_access(node: NodeId, nodes: &[Node]) -> NodeId {
    if is_right_side_of_property_access(node, nodes) {
        return nodes[node].parent.unwrap();
    }
    node
}

/// `climbPastPropertyOrElementAccess(node)`.
fn climb_past_property_or_element_access(node: NodeId, nodes: &[Node]) -> NodeId {
    if is_right_side_of_property_access(node, nodes)
        || is_argument_expression_of_element_access(node, nodes)
    {
        return nodes[node].parent.unwrap();
    }
    node
}

/// `selectExpressionOfCallOrNewExpressionOrDecorator(node)`.
fn select_expression_of_call_or_new_expression_or_decorator(
    node: &Node,
) -> Option<NodeId> {
    if is_call_expression(node) || is_new_expression(node) || is_decorator(node) {
        return node.expression();
    }
    None
}

/// `selectTagOfTaggedTemplateExpression(node)`.
fn select_tag_of_tagged_template_expression(node: &Node) -> Option<NodeId> {
    if is_tagged_template_expression(node) {
        return node.as_tagged_template_expression().tag;
    }
    None
}

/// `selectTagNameOfJsxOpeningLikeElement(node)`.
fn select_tag_name_of_jsx_opening_like_element(node: &Node) -> Option<NodeId> {
    if is_jsx_opening_element(node) || is_jsx_self_closing_element(node) {
        return node.tag_name();
    }
    None
}

/// `IsCallExpressionTarget(node, includeElementAccess, skipPastOuterExpressions)`.
pub fn is_call_expression_target(
    node: NodeId,
    include_element_access: bool,
    skip_past_outer_expressions: bool,
    nodes: &[Node],
) -> bool {
    is_callee_worker(
        node,
        &mut |n| is_call_expression(n),
        &mut select_expression_of_call_or_new_expression_or_decorator,
        include_element_access,
        skip_past_outer_expressions,
        nodes,
    )
}

/// `IsNewExpressionTarget(node, includeElementAccess, skipPastOuterExpressions)`.
pub fn is_new_expression_target(
    node: NodeId,
    include_element_access: bool,
    skip_past_outer_expressions: bool,
    nodes: &[Node],
) -> bool {
    is_callee_worker(
        node,
        &mut |n| is_new_expression(n),
        &mut select_expression_of_call_or_new_expression_or_decorator,
        include_element_access,
        skip_past_outer_expressions,
        nodes,
    )
}

/// `IsCallOrNewExpressionTarget(node, includeElementAccess, skipPastOuterExpressions)`.
pub fn is_call_or_new_expression_target(
    node: NodeId,
    include_element_access: bool,
    skip_past_outer_expressions: bool,
    nodes: &[Node],
) -> bool {
    is_callee_worker(
        node,
        &mut |n| is_call_or_new_expression(n),
        &mut select_expression_of_call_or_new_expression_or_decorator,
        include_element_access,
        skip_past_outer_expressions,
        nodes,
    )
}

/// `IsTaggedTemplateTag(node, includeElementAccess, skipPastOuterExpressions)`.
pub fn is_tagged_template_tag(
    node: NodeId,
    include_element_access: bool,
    skip_past_outer_expressions: bool,
    nodes: &[Node],
) -> bool {
    is_callee_worker(
        node,
        &mut |n| is_tagged_template_expression(n),
        &mut select_tag_of_tagged_template_expression,
        include_element_access,
        skip_past_outer_expressions,
        nodes,
    )
}

/// `IsDecoratorTarget(node, includeElementAccess, skipPastOuterExpressions)`.
pub fn is_decorator_target(
    node: NodeId,
    include_element_access: bool,
    skip_past_outer_expressions: bool,
    nodes: &[Node],
) -> bool {
    is_callee_worker(
        node,
        &mut |n| is_decorator(n),
        &mut select_expression_of_call_or_new_expression_or_decorator,
        include_element_access,
        skip_past_outer_expressions,
        nodes,
    )
}

/// `IsJsxOpeningLikeElementTagName(node, includeElementAccess, skipPastOuterExpressions)`.
pub fn is_jsx_opening_like_element_tag_name(
    node: NodeId,
    include_element_access: bool,
    skip_past_outer_expressions: bool,
    nodes: &[Node],
) -> bool {
    is_callee_worker(
        node,
        &mut |n| is_jsx_opening_like_element(n),
        &mut select_tag_name_of_jsx_opening_like_element,
        include_element_access,
        skip_past_outer_expressions,
        nodes,
    )
}

/// `isCalleeWorker(node, pred, calleeSelector, includeElementAccess, skipPastOuterExpressions)`.
fn is_callee_worker(
    node: NodeId,
    pred: &mut dyn FnMut(&Node) -> bool,
    callee_selector: &mut dyn FnMut(&Node) -> Option<NodeId>,
    include_element_access: bool,
    skip_past_outer_expressions: bool,
    nodes: &[Node],
) -> bool {
    let mut target = if include_element_access {
        climb_past_property_or_element_access(node, nodes)
    } else {
        climb_past_property_access(node, nodes)
    };
    if skip_past_outer_expressions && is_expression(&nodes[target], nodes) {
        target = skip_outer_expressions(target, oek::ALL, nodes);
    }
    nodes[target]
        .parent
        .is_some_and(|parent| pred(&nodes[parent]) && callee_selector(&nodes[parent]) == Some(target))
}

/// `IsRightSideOfQualifiedNameOrPropertyAccess(node)`.
pub fn is_right_side_of_qualified_name_or_property_access(
    node: NodeId,
    nodes: &[Node],
) -> bool {
    let Some(parent_id) = nodes[node].parent else {
        return false;
    };
    let parent = &nodes[parent_id];
    match parent.kind {
        Kind::QualifiedName => parent.as_qualified_name().right == Some(node),
        Kind::PropertyAccessExpression => parent.name() == Some(node),
        Kind::MetaProperty => parent.as_meta_property().name == Some(node),
        _ => false,
    }
}

/// `ShouldTransformImportCall(fileName, options, impliedNodeFormatForEmit)`.
pub fn should_transform_import_call(
    _file_name: &RootedFilePath,
    options: &CompilerOptions,
    implied_node_format_for_emit: ModuleKind,
) -> bool {
    let module_kind = options.get_emit_module_kind();
    if (ModuleKind::Node16..=ModuleKind::NodeNext).contains(&module_kind)
        || module_kind == ModuleKind::Preserve
    {
        return false;
    }
    implied_node_format_for_emit < ModuleKind::ES2015
}

/// `HasQuestionToken(node)`.
pub fn has_question_token(node: &Node, nodes: &[Node]) -> bool {
    is_question_token(node.question_token(nodes), nodes)
}

/// `IsJsxOpeningLikeElement(node)`.
pub fn is_jsx_opening_like_element(node: &Node) -> bool {
    is_jsx_opening_element(node) || is_jsx_self_closing_element(node)
}

/// `GetInvokedExpression(node)` — the callee/tag/argument expression of a
/// call-like node.
pub fn get_invoked_expression(node: &Node, _nodes: &[Node]) -> Option<NodeId> {
    match node.kind {
        Kind::TaggedTemplateExpression => node.as_tagged_template_expression().tag,
        Kind::JsxOpeningElement | Kind::JsxSelfClosingElement => node.tag_name(),
        Kind::BinaryExpression => node.as_binary_expression().right,
        Kind::JsxOpeningFragment => Some(node.id),
        _ => node.expression(),
    }
}

/// `IsCallOrNewExpression(node)`.
pub fn is_call_or_new_expression(node: &Node) -> bool {
    is_call_expression(node) || is_new_expression(node)
}

/// `CompareNodePositions(n1, n2)` — compares `loc` ranges.
pub fn compare_node_positions(n1: &Node, n2: &Node) -> i32 {
    tsc_core::text::compare_text_ranges(&n1.loc, &n2.loc)
}

/// `IndexOfNode(nodes, node)` — binary search by position; `-1` if absent.
pub fn index_of_node(node_list: &[NodeId], node: NodeId, nodes: &[Node]) -> i32 {
    match node_list.binary_search_by(|&id| {
        compare_node_positions(&nodes[id], &nodes[node]).cmp(&0)
    }) {
        Ok(index) => index as i32,
        Err(_) => -1,
    }
}

/// `IsUnterminatedLiteral(node)`.
pub fn is_unterminated_literal(node: &Node) -> bool {
    (is_literal_kind(node.kind)
        && node
            .literal_like_data()
            .is_some_and(|d| d.token_flags.intersects(TokenFlags::UNTERMINATED)))
        || (is_template_literal_kind(node.kind)
            && node.template_literal_like_data().is_some_and(|d| {
                d.template_flags.intersects(TokenFlags::UNTERMINATED)
            }))
}

/// `IsInitializedProperty(member)` — a property declaration with initializer.
pub fn is_initialized_property(member: &Node) -> bool {
    member.kind == Kind::PropertyDeclaration && member.initializer().is_some()
}

/// `IsTrivia(token)`.
pub fn is_trivia(token: Kind) -> bool {
    Kind::FIRST_TRIVIA_TOKEN <= token && token <= Kind::LAST_TRIVIA_TOKEN
}

/// `HasDecorators(node)` — the node has a syntactic decorator.
pub fn has_decorators(node: &Node) -> bool {
    has_syntactic_modifier(node, ModifierFlags::DECORATOR)
}

// __NEXT3__
