// Ported from tsc/internal/transformers/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Shared helpers used by the transform subpackages: identifier classification
// against the emit context, binding-pattern → assignment-pattern conversion,
// `super()` statement search, and `TextRange` adjustment helpers.
//
// PORT: `emitContext` parameters that mint nodes take `&mut EmitContext`
// (the factory needs `&mut`); read-only helpers take `&EmitContext`. Inside a
// visit, callers reach these through `tx.emit_context().borrow[_mut]()`.

use tsc_ast::{self as ast, Kind, Node, NodeId};
use tsc_core::core::{find_last, last_or_nil};
use tsc_core::text::TextRange;
use tsc_printer::{EmitContext, EmitFlags};

/// `IsGeneratedIdentifier(emitContext, name)` — `name` must be an Identifier.
pub fn is_generated_identifier(emit_context: &EmitContext, name: NodeId) -> bool {
    emit_context.has_auto_generate_info(Some(name))
}

/// `IsHelperName(emitContext, name)` — `name` must be an Identifier.
pub fn is_helper_name(emit_context: &EmitContext, name: NodeId) -> bool {
    emit_context.emit_flags(name) & EmitFlags::HELPER_NAME != EmitFlags::NONE
}

/// `IsLocalName(emitContext, name)` — `name` must be an Identifier.
pub fn is_local_name(emit_context: &EmitContext, name: NodeId) -> bool {
    emit_context.emit_flags(name) & EmitFlags::LOCAL_NAME != EmitFlags::NONE
}

/// `IsExportName(emitContext, name)` — `name` must be an Identifier.
pub fn is_export_name(emit_context: &EmitContext, name: NodeId) -> bool {
    emit_context.emit_flags(name) & EmitFlags::EXPORT_NAME != EmitFlags::NONE
}

/// `IsIdentifierReference(name, parent)` — `name` must be an Identifier.
pub fn is_identifier_reference(nodes: &[Node], name: NodeId, parent: NodeId) -> bool {
    match nodes[parent].kind {
        Kind::BinaryExpression
        | Kind::PrefixUnaryExpression
        | Kind::PostfixUnaryExpression
        | Kind::YieldExpression
        | Kind::AsExpression
        | Kind::SatisfiesExpression
        | Kind::ElementAccessExpression
        | Kind::NonNullExpression
        | Kind::SpreadElement
        | Kind::SpreadAssignment
        | Kind::ParenthesizedExpression
        | Kind::ArrayLiteralExpression
        | Kind::DeleteExpression
        | Kind::TypeOfExpression
        | Kind::VoidExpression
        | Kind::AwaitExpression
        | Kind::TypeAssertionExpression
        | Kind::ExpressionWithTypeArguments
        | Kind::JsxSelfClosingElement
        | Kind::JsxSpreadAttribute
        | Kind::JsxExpression
        | Kind::PartiallyEmittedExpression => {
            // all immediate children that can be `Identifier` would be instances of `IdentifierReference`
            true
        }
        Kind::ComputedPropertyName
        | Kind::Decorator
        | Kind::IfStatement
        | Kind::DoStatement
        | Kind::WhileStatement
        | Kind::WithStatement
        | Kind::ReturnStatement
        | Kind::SwitchStatement
        | Kind::CaseClause
        | Kind::ThrowStatement
        | Kind::ExpressionStatement
        | Kind::ExportAssignment
        | Kind::PropertyAccessExpression
        | Kind::TemplateSpan => {
            // only an `Expression()` child that can be `Identifier` would be an instance of `IdentifierReference`
            nodes[parent].expression() == Some(name)
        }
        Kind::VariableDeclaration
        | Kind::Parameter
        | Kind::BindingElement
        | Kind::PropertyDeclaration
        | Kind::PropertySignature
        | Kind::PropertyAssignment
        | Kind::EnumMember
        | Kind::JsxAttribute => {
            // only an `Initializer()` child that can be `Identifier` would be an instance of `IdentifierReference`
            nodes[parent].initializer() == Some(name)
        }
        Kind::ShorthandPropertyAssignment => {
            nodes[parent]
                .as_shorthand_property_assignment()
                .object_assignment_initializer
                == Some(name)
        }
        Kind::ForStatement => {
            let for_statement = nodes[parent].as_for_statement();
            nodes[parent].initializer() == Some(name)
                || for_statement.condition == Some(name)
                || for_statement.incrementor == Some(name)
        }
        Kind::ForInStatement | Kind::ForOfStatement => {
            nodes[parent].initializer() == Some(name) || nodes[parent].expression() == Some(name)
        }
        Kind::ImportEqualsDeclaration => {
            nodes[parent]
                .as_import_equals_declaration()
                .module_reference
                == Some(name)
        }
        Kind::ArrowFunction => nodes[parent].body() == Some(name),
        Kind::ConditionalExpression => {
            let conditional = nodes[parent].as_conditional_expression();
            conditional.condition == Some(name)
                || conditional.when_true == Some(name)
                || conditional.when_false == Some(name)
        }
        Kind::CallExpression | Kind::NewExpression => {
            nodes[parent].expression() == Some(name)
                || nodes[parent]
                    .arguments()
                    .is_some_and(|args| args.contains(&name))
        }
        Kind::TaggedTemplateExpression => {
            nodes[parent].as_tagged_template_expression().tag == Some(name)
        }
        Kind::ImportAttribute => nodes[parent].as_import_attribute().value == Some(name),
        Kind::JsxOpeningElement | Kind::JsxClosingElement => nodes[parent].tag_name() == Some(name),
        _ => false,
    }
}

/// `convertBindingElementToArrayAssignmentElement(emitContext, element)` —
/// `element` must be a `BindingElement` node (`element.AsBindingElement()`).
fn convert_binding_element_to_array_assignment_element(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    element: NodeId,
) -> NodeId {
    let element_data = nodes[element].as_binding_element();
    let (name, dot_dot_dot_token, initializer) = (
        element_data.name,
        element_data.dot_dot_dot_token,
        element_data.initializer,
    );
    let Some(name) = name else {
        let elision = emit_context.factory.new_omitted_expression(nodes);
        emit_context.set_original(elision, element);
        emit_context.assign_comment_and_source_map_ranges(nodes, elision, element);
        return elision;
    };
    let expression = convert_binding_name_to_assignment_element_target(emit_context, nodes, name);
    if dot_dot_dot_token.is_some() {
        let spread = emit_context
            .factory
            .new_spread_element(nodes, Some(expression));
        emit_context.set_original(spread, element);
        emit_context.assign_comment_and_source_map_ranges(nodes, spread, element);
        return spread;
    }
    if let Some(initializer) = initializer {
        let assignment =
            emit_context
                .factory
                .new_assignment_expression(nodes, expression, initializer);
        emit_context.set_original(assignment, element);
        emit_context.assign_comment_and_source_map_ranges(nodes, assignment, element);
        return assignment;
    }
    expression
}

/// `convertBindingElementToObjectAssignmentElement(emitContext, element)` —
/// `element` must be a `BindingElement` node.
fn convert_binding_element_to_object_assignment_element(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    element: NodeId,
) -> NodeId {
    let element_data = nodes[element].as_binding_element();
    let (name, dot_dot_dot_token, property_name, initializer) = (
        element_data.name,
        element_data.dot_dot_dot_token,
        element_data.property_name,
        element_data.initializer,
    );
    if dot_dot_dot_token.is_some() {
        let spread = emit_context.factory.new_spread_assignment(nodes, name);
        emit_context.set_original(spread, element);
        emit_context.assign_comment_and_source_map_ranges(nodes, spread, element);
        return spread;
    }
    if let Some(property_name) = property_name {
        let mut expression = convert_binding_name_to_assignment_element_target(
            emit_context,
            nodes,
            name.expect("binding element has no name"),
        );
        if let Some(initializer) = initializer {
            expression =
                emit_context
                    .factory
                    .new_assignment_expression(nodes, expression, initializer);
        }
        let assignment = emit_context.factory.new_property_assignment(
            nodes,
            None, // modifiers
            Some(property_name),
            None, // postfixToken
            None, // typeNode
            Some(expression),
        );
        emit_context.set_original(assignment, element);
        emit_context.assign_comment_and_source_map_ranges(nodes, assignment, element);
        return assignment;
    }
    let equals_token = if initializer.is_some() {
        Some(emit_context.factory.new_token(nodes, Kind::EqualsToken))
    } else {
        None
    };
    let assignment = emit_context.factory.new_shorthand_property_assignment(
        nodes,
        None, // modifiers
        name,
        None, // postfixToken
        None, // typeNode
        equals_token,
        initializer,
    );
    emit_context.set_original(assignment, element);
    emit_context.assign_comment_and_source_map_ranges(nodes, assignment, element);
    assignment
}

/// `ConvertBindingPatternToAssignmentPattern(emitContext, element)` —
/// `element` must be an `ArrayBindingPattern` or `ObjectBindingPattern`.
pub fn convert_binding_pattern_to_assignment_pattern(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    element: NodeId,
) -> NodeId {
    match nodes[element].kind {
        Kind::ArrayBindingPattern => {
            convert_binding_element_to_array_assignment_pattern(emit_context, nodes, element)
        }
        Kind::ObjectBindingPattern => {
            convert_binding_element_to_object_assignment_pattern(emit_context, nodes, element)
        }
        _ => panic!("Unknown binding pattern"),
    }
}

/// `convertBindingElementToObjectAssignmentPattern(emitContext, element)` —
/// `element` must be a `BindingPattern`.
fn convert_binding_element_to_object_assignment_pattern(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    element: NodeId,
) -> NodeId {
    let elements = nodes[element]
        .as_binding_pattern()
        .elements
        .clone()
        .expect("binding pattern has no elements");
    let mut properties = Vec::with_capacity(elements.nodes.len());
    for &element_id in elements.nodes.iter() {
        properties.push(convert_binding_element_to_object_assignment_element(
            emit_context,
            nodes,
            element_id,
        ));
    }
    let mut property_list = emit_context.factory.new_node_list(properties);
    property_list.loc = elements.loc;
    let object =
        emit_context
            .factory
            .new_object_literal_expression(nodes, Some(property_list), false);
    emit_context.set_original(object, element);
    emit_context.assign_comment_and_source_map_ranges(nodes, object, element);
    object
}

/// `convertBindingElementToArrayAssignmentPattern(emitContext, element)` —
/// `element` must be a `BindingPattern`.
fn convert_binding_element_to_array_assignment_pattern(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    element: NodeId,
) -> NodeId {
    let elements = nodes[element]
        .as_binding_pattern()
        .elements
        .clone()
        .expect("binding pattern has no elements");
    let mut element_ids = Vec::with_capacity(elements.nodes.len());
    for &element_id in elements.nodes.iter() {
        element_ids.push(convert_binding_element_to_array_assignment_element(
            emit_context,
            nodes,
            element_id,
        ));
    }
    let mut element_list = emit_context.factory.new_node_list(element_ids);
    element_list.loc = elements.loc;
    let object =
        emit_context
            .factory
            .new_array_literal_expression(nodes, Some(element_list), false);
    emit_context.set_original(object, element);
    emit_context.assign_comment_and_source_map_ranges(nodes, object, element);
    object
}

/// `convertBindingNameToAssignmentElementTarget(emitContext, element)`.
fn convert_binding_name_to_assignment_element_target(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    element: NodeId,
) -> NodeId {
    if ast::is_binding_pattern(&nodes[element]) {
        return convert_binding_pattern_to_assignment_pattern(emit_context, nodes, element);
    }
    element
}

/// `ConvertVariableDeclarationToAssignmentExpression(emitContext, element)` —
/// `element` must be a `VariableDeclaration`; `None` when it has no
/// initializer (Go nil).
pub fn convert_variable_declaration_to_assignment_expression(
    emit_context: &mut EmitContext,
    nodes: &mut Vec<Node>,
    element: NodeId,
) -> Option<NodeId> {
    let element_data = nodes[element].as_variable_declaration();
    let (name, initializer) = (element_data.name, element_data.initializer);
    let initializer = initializer?;
    let expression = convert_binding_name_to_assignment_element_target(
        emit_context,
        nodes,
        name.expect("variable declaration has no name"),
    );
    let assignment = emit_context
        .factory
        .new_assignment_expression(nodes, expression, initializer);
    emit_context.set_original(assignment, element);
    emit_context.assign_comment_and_source_map_ranges(nodes, assignment, element);
    Some(assignment)
}

/// `SingleOrMany(nodes, factory)` — `None` mirrors the empty/nil input slice.
///
/// PORT: Go takes `[]*ast.Node` (nilable) plus the printer factory; here the
/// list is `Option<Vec<NodeId>>` (`None` ↔ Go nil slice, `Some(vec![])` ↔ an
/// allocated-but-empty slice) and only the `ast::NodeFactory` half of the
/// printer factory is needed for `NewSyntaxList`.
pub fn single_or_many(
    factory: &mut ast::NodeFactory<'_>,
    nodes: &mut Vec<Node>,
    list: Option<Vec<NodeId>>,
) -> Option<NodeId> {
    let list = list?;
    if list.len() == 1 {
        return list.into_iter().next();
    }
    Some(factory.new_syntax_list(nodes, &list))
}

/// `IsSimpleCopiableExpression(expression)` — used in the module transformer
/// to check if an expression is reasonably without side-effect, and thus
/// better to copy into multiple places rather than to cache in a temporary
/// variable (this is mostly subjective beyond the requirement that the
/// expression not be side-effecting). Also used by the logical assignment
/// downleveling transform to skip temp variables when they're not needed.
pub fn is_simple_copiable_expression(expression: &Node) -> bool {
    ast::is_string_literal_like(expression)
        || ast::is_numeric_literal(expression)
        || expression.kind.is_keyword_kind()
        || ast::is_identifier(expression)
}

/// `IsOriginalNodeSingleLine(emitContext, node)`.
pub fn is_original_node_single_line(
    emit_context: &EmitContext,
    nodes: &[Node],
    node: Option<NodeId>,
) -> bool {
    let Some(node) = node else {
        return false;
    };
    let Some(original) = emit_context.most_original(Some(node)) else {
        return false;
    };
    let Some(source) = ast::get_source_file_of_node(Some(original), nodes) else {
        return false;
    };
    let source = nodes[source].as_source_file();
    // PORT: `scanner.GetECMALineOfPosition` takes the *scanner's*
    // `SourceFileLike`, which `ast::SourceFile` does not implement; the
    // cached `ecma_line_map` plus `compute_line_of_position` is the
    // equivalent the printer uses.
    let line_map = tsc_ast::SourceFileLike::ecma_line_map(source);
    let start_line =
        tsc_scanner::scanner::compute_line_of_position(line_map, nodes[original].loc.pos());
    let end_line =
        tsc_scanner::scanner::compute_line_of_position(line_map, nodes[original].loc.end());
    start_line == end_line
}

/// `IsSimpleInlineableExpression(expression)` — a simple inlinable expression
/// is an expression which can be copied into multiple locations without risk
/// of repeating any side-effects and whose value could not possibly change
/// between any such locations.
pub fn is_simple_inlineable_expression(expression: &Node) -> bool {
    !ast::is_identifier(expression) && is_simple_copiable_expression(expression)
}

/// `FindSuperStatementIndexPath(statements, start)` — finds a path of
/// indices to a statement containing a `super()` call.
pub fn find_super_statement_index_path(
    nodes: &[Node],
    statements: &[NodeId],
    start: usize,
) -> Vec<i32> {
    let mut indices = find_super_statement_index_path_worker(nodes, statements, start, Vec::new())
        .unwrap_or_default();
    indices.reverse();
    indices
}

/// `findSuperStatementIndexPathWorker` — `None` mirrors Go's nil return.
fn find_super_statement_index_path_worker(
    nodes: &[Node],
    statements: &[NodeId],
    start: usize,
    mut indices: Vec<i32>,
) -> Option<Vec<i32>> {
    for (i, &statement) in statements.iter().enumerate().skip(start) {
        if get_super_call_from_statement(nodes, statement).is_some() {
            indices.push(i as i32);
            return Some(indices);
        } else if ast::is_try_statement(&nodes[statement]) {
            let try_statements = nodes[statement]
                .as_try_statement()
                .try_block
                .and_then(|try_block| nodes[try_block].statements())
                .unwrap_or(&[]);
            if let Some(mut result) =
                find_super_statement_index_path_worker(nodes, try_statements, 0, indices.clone())
            {
                result.push(i as i32);
                return Some(result);
            }
        }
    }
    None
}

/// `GetSuperCallFromStatement(statement)` — extracts the `super()` call
/// expression from an expression statement, if any.
pub fn get_super_call_from_statement(nodes: &[Node], statement: NodeId) -> Option<NodeId> {
    if !ast::is_expression_statement(&nodes[statement]) {
        return None;
    }
    let expression = ast::skip_parentheses(nodes[statement].expression()?, nodes);
    if ast::is_super_call(&nodes[expression], nodes) {
        return Some(expression);
    }
    None
}

/// `MoveRangePastModifiers(node)` — returns a text range that starts past
/// any modifiers on the node.
pub fn move_range_past_modifiers(nodes: &[Node], node: NodeId) -> TextRange {
    if ast::is_property_declaration(&nodes[node]) || ast::is_method_declaration(&nodes[node]) {
        let name = nodes[node].name().expect("declaration has no name");
        return TextRange::new(nodes[name].pos(), nodes[node].end());
    }

    let last_modifier = if ast::can_have_modifiers(&nodes[node]) {
        nodes[node].modifier_nodes().and_then(last_or_nil)
    } else {
        None
    };

    if let Some(last_modifier) = last_modifier
        && !ast::position_is_synthesized(nodes[last_modifier].end())
    {
        return TextRange::new(nodes[last_modifier].end(), nodes[node].end());
    }
    move_range_past_decorators(nodes, node)
}

/// `MoveRangePastDecorators(node)` — returns a text range that starts past
/// any decorators on the node.
pub fn move_range_past_decorators(nodes: &[Node], node: NodeId) -> TextRange {
    let last_decorator = if ast::can_have_modifiers(&nodes[node]) {
        nodes[node]
            .modifier_nodes()
            .and_then(|modifier_nodes| find_last(modifier_nodes, |m| ast::is_decorator(&nodes[*m])))
    } else {
        None
    };

    if let Some(last_decorator) = last_decorator
        && !ast::position_is_synthesized(nodes[last_decorator].end())
    {
        return TextRange::new(nodes[last_decorator].end(), nodes[node].end());
    }
    nodes[node].loc
}

/// `GetNonAssignmentOperatorForCompoundAssignment(kind)` — returns the
/// non-assignment operator for a compound assignment.
pub fn get_non_assignment_operator_for_compound_assignment(kind: Kind) -> Kind {
    match kind {
        Kind::PlusEqualsToken => Kind::PlusToken,
        Kind::MinusEqualsToken => Kind::MinusToken,
        Kind::AsteriskEqualsToken => Kind::AsteriskToken,
        Kind::AsteriskAsteriskEqualsToken => Kind::AsteriskAsteriskToken,
        Kind::SlashEqualsToken => Kind::SlashToken,
        Kind::PercentEqualsToken => Kind::PercentToken,
        Kind::LessThanLessThanEqualsToken => Kind::LessThanLessThanToken,
        Kind::GreaterThanGreaterThanEqualsToken => Kind::GreaterThanGreaterThanToken,
        Kind::GreaterThanGreaterThanGreaterThanEqualsToken => {
            Kind::GreaterThanGreaterThanGreaterThanToken
        }
        Kind::AmpersandEqualsToken => Kind::AmpersandToken,
        Kind::BarEqualsToken => Kind::BarToken,
        Kind::CaretEqualsToken => Kind::CaretToken,
        Kind::BarBarEqualsToken => Kind::BarBarToken,
        Kind::AmpersandAmpersandEqualsToken => Kind::AmpersandAmpersandToken,
        Kind::QuestionQuestionEqualsToken => Kind::QuestionQuestionToken,
        _ => kind,
    }
}
