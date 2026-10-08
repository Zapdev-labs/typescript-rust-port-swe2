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

use rustc_hash::FxHashMap;
use tsc_core::compileroptions::ResolutionMode;
use tsc_core::options_generated::{CompilerOptions, JsxEmit, ModuleKind, ModuleResolutionKind};
use tsc_core::textrange::{TextPos, TextRange};
use tsc_tspath::{self as tspath, RootedFilePath};

use crate::ast::{
    AllAccessorDeclarations, HasFileName, ModifierList, Node, NodeList, SourceFile,
    SourceFileMetaData, Symbol, SymbolTable,
};
use crate::ast_generated::*;
use crate::ids::{NodeId, SymbolId};
use crate::kind_generated::Kind;
use crate::modifierflags::ModifierFlags;
use crate::nodeflags::NodeFlags;
use crate::subtreefacts::SubtreeFacts;
use crate::symbol::{
    is_ambient_module_symbol_name, try_get_ambient_module_name_from_symbol_name,
    ModuleInstanceState,
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
    node.locals_container_data_mut()
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
                if pn.as_shorthand_property_assignment().name != Some(node) {
                    return None;
                }
                node = pn.parent.expect("nil parent in GetAssignmentTarget");
            }
            Kind::PropertyAssignment => {
                if pn.as_property_assignment().name == Some(node) {
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

/// `isFunctionLikeDeclarationKind(kind)` — subset checked by kind.
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
            | Kind::MethodSignature
            | Kind::FunctionType
            | Kind::ConstructorType
            | Kind::JSDocFunctionType
            | Kind::CallSignature
            | Kind::ConstructSignature
            | Kind::IndexSignature
            | Kind::ClassStaticBlockDeclaration
    )
}

/// `IsFunctionLikeDeclaration(node)` — like `IsFunctionLike` but returns `true`
/// only when the kind is a declaration kind or `SignatureDeclaration`-like.
pub fn is_function_like_declaration(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| is_function_like_declaration_kind(nodes[n].kind))
}

/// `IsFunctionLikeKind(kind)`.
pub fn is_function_like_kind(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::MethodSignature
            | Kind::CallSignature
            | Kind::JSDocSignature
            | Kind::ConstructSignature
            | Kind::IndexSignature
            | Kind::FunctionType
            | Kind::JSDocFunctionType
            | Kind::ConstructorType
    )
}

/// `IsFunctionLike(node)` — returns `true` for nodes that contain parameters
/// or type parameters.
pub fn is_function_like(node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|n| {
        let kind = nodes[n].kind;
        is_function_like_declaration_kind(kind) || is_function_like_kind(kind)
    })
}

/// `IsFunctionLikeOrClassStaticBlockDeclaration(node)`.
pub fn is_function_like_or_class_static_block_declaration(
    node: Option<NodeId>,
    nodes: &[Node],
) -> bool {
    node.is_some_and(|n| {
        is_function_like_kind(nodes[n].kind) || is_function_like_declaration_kind(nodes[n].kind)
    })
}

/// `IsFunctionOrSourceFile(node)` — node can directly contain statements.
pub fn is_function_or_source_file(node: &Node) -> bool {
    matches!(
        node.kind,
        Kind::SourceFile
            | Kind::FunctionDeclaration
            | Kind::MethodDeclaration
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::FunctionExpression
            | Kind::ArrowFunction
            | Kind::ClassStaticBlockDeclaration
    )
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
                    && nodes[p].as_property_assignment().name == Some(node))
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
    nodes[source_file].as_source_file_mut().imports = Some(imports);
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

/// `IsLet(node)` — `isLet` in Go checks `NodeFlagsLet` intersection.
pub fn is_let(node: &Node) -> bool {
    node.flags.intersects(NodeFlags::LET)
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
    file.script_kind == crate::scriptkind::ScriptKind::JS
        || file.script_kind == crate::scriptkind::ScriptKind::JSX
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
        && nodes[name].parent.is_some_and(|p| {
            is_declaration(&nodes[p]) && nodes[p].name() == Some(name)
        })
}

/// `IsDeclarationNameOrImportPropertyName(name)`.
pub fn is_declaration_name_or_import_property_name(name: NodeId, nodes: &[Node]) -> bool {
    if let Some(parent) = nodes[name].parent {
        let pk = nodes[parent].kind;
        match pk {
            Kind::ImportSpecifier | Kind::ExportSpecifier => {
                return nodes[parent].property_name() == Some(name);
            }
            Kind::ImportClause | Kind::NamespaceImport => {
                return nodes[parent].name() == Some(name);
            }
            _ => {}
        }
    }
    is_declaration_name(name, nodes)
}

/// `IsLiteralComputedPropertyDeclarationName(node)`.
pub fn is_literal_computed_property_declaration_name(node: NodeId, nodes: &[Node]) -> bool {
    is_computed_property_name(&nodes[node])
        && nodes[node]
            .expression()
            .is_some_and(|e| is_string_literal_like(&nodes[e]) || is_numeric_literal(&nodes[e]))
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
    if !is_import_type_node(node) {
        return false;
    }
    node.as_import_type_node()
        .argument
        .is_some_and(|arg| {
            is_literal_type_node(&nodes[arg])
                && nodes[arg]
                    .expression()
                    .is_some_and(|e| is_string_literal(&nodes[e]))
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

/// `IsImportOrExportSpecifier(node)` — KindJSAttributeLike? matches Go:
/// `node.Kind == KindImportSpecifier || node.Kind == KindExportSpecifier`.
pub fn is_import_or_export_specifier(node: &Node) -> bool {
    node.kind == Kind::ImportSpecifier || node.kind == Kind::ExportSpecifier
}

/// `IsVoidZero(node)`.
pub fn is_void_zero(node: &Node, nodes: &[Node]) -> bool {
    node.kind == Kind::VoidExpression
        && node.expression().is_some_and(|e| {
            is_numeric_literal(&nodes[e]) && nodes[e].text(nodes) == "0"
        })
}

/// `IsExportsIdentifier(node)` — in JS files only.
pub fn is_exports_identifier(node: &Node, nodes: &[Node]) -> bool {
    is_identifier(node) && node.as_identifier().text == "exports"
}

/// `IsModuleIdentifier(node)`.
pub fn is_module_identifier(node: &Node, nodes: &[Node]) -> bool {
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

/// `IsBindableStaticAccessExpression(node)` — `expr?.name` chains.
pub fn is_bindable_static_access_expression(node: &Node, nodes: &[Node]) -> bool {
    is_property_access_expression(node)
        && !node.flags.intersects(NodeFlags::OPTIONAL_CHAIN)
        && node.name().is_some_and(|n| {
            let n = &nodes[n];
            is_identifier(n) || is_keyword_expression_kind(n.kind)
        })
}

// PORT: `is_bindable_static_access_expression` on a non-optional-chain checks
// the last token is an identifier-ish — Go's `isPushOrUnshiftIdentifier` and
// `IsIdentifier` exclusions are handled by `is_bindable_static_name_expression`.

/// `IsBindableStaticElementAccessExpression(node, excludeComputedLiterals)`.
pub fn is_bindable_static_element_access_expression(
    node: &Node,
    nodes: &[Node],
    exclude_computed_literals: bool,
) -> bool {
    if !is_literal_like_element_access(node, nodes) {
        return false;
    }
    if exclude_computed_literals
        && !is_bindable_static_name_expression(
            nodes[node.as_element_access_expression().expression.unwrap()].id,
            nodes,
        )
    {
        return false;
    }
    true
}

/// `IsPrototypeAccess(expression)`.
pub fn is_prototype_access(node: &Node, nodes: &[Node]) -> bool {
    is_bindable_static_access_expression(node, nodes)
        && node.name().is_some_and(|n| nodes[n].text(nodes) == "prototype")
}

/// `IsLiteralLikeElementAccess(node)` — element access with a literal arg.
pub fn is_literal_like_element_access(node: &Node, nodes: &[Node]) -> bool {
    is_element_access_expression(node)
        && !node.flags.intersects(NodeFlags::OPTIONAL_CHAIN)
        && node.as_element_access_expression().argument_expression.is_some_and(|a| {
            is_string_or_numeric_literal_like(&nodes[a])
                || is_entity_name_expression_ex(&nodes[a], nodes)
        })
}

/// `IsBindableStaticNameExpression(node, excludeKeywordLiterals)` —
/// `isBindableStaticNameExpression` in Go.
pub fn is_bindable_static_name_expression(node: NodeId, nodes: &[Node]) -> bool {
    let node = &nodes[node];
    is_entity_name_expression_ex(node, nodes)
        || is_bindable_static_access_expression(node, nodes)
        || is_bindable_static_element_access_expression(node, nodes, false /* excludeComputedLiterals */)
}

/// `GetElementOrPropertyAccessName(access)`.
pub fn get_element_or_property_access_name(access: &Node, nodes: &[Node]) -> Option<Cow<'_, str>> {
    if is_property_access_expression(access) {
        return access.name().map(|n| nodes[n].text(nodes));
    }
    if is_element_access_expression(access) {
        if let Some(arg) = access.as_element_access_expression().argument_expression {
            let arg_node = &nodes[arg];
            if is_string_or_numeric_literal_like(arg_node) {
                return Some(arg_node.text(nodes));
            }
            if is_entity_name_expression_ex(arg_node, nodes) {
                return Some(get_right_most_entity_name(arg, nodes).text(nodes));
            }
        }
    }
    None
}

/// `getRightMostEntityName(expr)` — walks `.Left`/`Right`/`Expression`/`Name`
/// to the right-most identifier — used by `GetElementOrPropertyAccessName`.
fn get_right_most_entity_name(node: NodeId, nodes: &[Node]) -> NodeId {
    let mut node = node;
    loop {
        match nodes[node].kind {
            Kind::QualifiedName => node = nodes[node].as_qualified_name().right.unwrap(),
            Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
                if let Some(n) = nodes[node].name() {
                    node = n;
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
    node
}

/// `GetInitializerOfBinaryExpression(expr)`.
pub fn get_initializer_of_binary_expression(expr: &Node, nodes: &[Node]) -> Option<NodeId> {
    if !is_assignment_expression(expr, nodes, true /* excludeCompoundAssignment */) {
        return None;
    }
    expr.as_binary_expression().right
}

/// `IsExpressionWithTypeArgumentsInClassExtendsClause(node)`.
pub fn is_expression_with_type_arguments_in_class_extends_clause(
    node: &Node,
    nodes: &[Node],
) -> bool {
    // PORT: Go walks `node.Parent` -> heritage clause -> class heritage clause.
    node.parent
        .is_some_and(|p| try_get_class_extends_clause_node(p, nodes))
}

/// `tryGetClassExtendsClauseNode` — `IsExpressionWithTypeArgumentsInClassExtendsClause` helper.
fn try_get_class_extends_clause_node(node: NodeId, nodes: &[Node]) -> bool {
    let Some(clause) = try_get_class_implementing_or_extending_heritage_clause_element(node, nodes)
    else {
        return false;
    };
    nodes[clause.clause_node].kind == Kind::HeritageClause
        && nodes[clause.clause_node].as_heritage_clause().token == Kind::ExtendsKeyword
        && is_class_like(clause.parent, nodes)
}

/// `TryGetClassExtendingExpressionWithTypeArguments(node)`.
pub fn try_get_class_extending_expression_with_type_arguments(
    node: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    let cls = try_get_class_implementing_or_extending_heritage_clause_element(node, nodes)?;
    if is_class_like(cls.parent, nodes) && nodes[cls.clause_node].as_heritage_clause().token == Kind::ExtendsKeyword {
        return Some(cls.node);
    }
    None
}

/// `HeritageClauseElement` — Go's returned `{node, parent, clauseNode}` from
/// `TryGetClassImplementingOrExtendingHeritageClauseElement`.
#[derive(Clone, Copy, Debug)]
pub struct HeritageClauseElement {
    /// The `ExpressionWithTypeArguments`/`TypeReference`-ish element node.
    pub node: NodeId,
    /// The class-like or interface declaration node.
    pub parent: NodeId,
    /// The `HeritageClause` node.
    pub clause_node: NodeId,
}

/// `TryGetClassImplementingOrExtendingHeritageClauseElement(node)`.
pub fn try_get_class_implementing_or_extending_heritage_clause_element(
    node: NodeId,
    nodes: &[Node],
) -> Option<HeritageClauseElement> {
    let decl = &nodes[node];
    let (is_heritage_clause, parent_kinds) = match decl.kind {
        Kind::ExpressionWithTypeArguments => (true, &[Kind::ClassDeclaration, Kind::ClassExpression][..]),
        Kind::TypeReference => (true, &[Kind::InterfaceDeclaration][..]),
        _ => (false, &[][..]),
    };
    if !is_heritage_clause {
        return None;
    }
    let clause = decl.parent?;
    if !is_heritage_clause(&nodes[clause]) {
        return None;
    }
    let parent = nodes[clause].parent?;
    if !parent_kinds.contains(&nodes[parent].kind) {
        return None;
    }
    Some(HeritageClauseElement {
        node,
        parent,
        clause_node: clause,
    })
}

// __NEXT__
