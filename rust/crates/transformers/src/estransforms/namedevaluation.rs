// Ported from tsc/internal/transformers/estransforms/namedevaluation.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Named evaluation: assigning `.name` to anonymous class/function expressions
// per the ECMAScript NamedEvaluation semantics (`__setFunctionName` helper or
// an injected `static {}` block).

use std::cell::RefCell;
use std::rc::Rc;

use tsc_ast::visitor::VisitorCx;
use tsc_ast::{self as ast, Kind, NodeId, TokenFlags, outer_expression_kinds};
use tsc_printer::EmitContext;

use super::classthis::is_class_this_assignment_block;

/// Gets whether a node is a `static {}` block containing only a single call
/// to the `__setFunctionName` helper where that call's second argument is the
/// value stored in the `assignedName` property of the block's `EmitNode`.
/// @internal
pub(crate) fn is_class_named_evaluation_helper_block(
    emit_context: &EmitContext,
    nodes: &[tsc_ast::Node],
    node: NodeId,
) -> bool {
    if !ast::is_class_static_block_declaration(&nodes[node])
        || nodes[node]
            .as_class_static_block_declaration()
            .body
            .and_then(|b| nodes[b].statements().map(<[_]>::len))
            != Some(1)
    {
        return false;
    }

    let statement = nodes[node]
        .as_class_static_block_declaration()
        .body
        .and_then(|b| nodes[b].statements().map(|s| s[0]))
        .unwrap();
    if ast::is_expression_statement(&nodes[statement])
        && let Some(expression) = nodes[statement].expression()
        && emit_context.is_call_to_helper(nodes, expression, "__setFunctionName")
    {
        let arguments = &nodes[expression].as_call_expression().arguments;
        return arguments.as_ref().is_some_and(|a| {
            a.nodes.len() >= 2 && Some(a.nodes[1]) == emit_context.assigned_name(node)
        });
    }
    false
}

/// Gets whether a `ClassLikeDeclaration` has a `static {}` block containing
/// only a single call to the `__setFunctionName` helper.
/// @internal
pub(crate) fn class_has_explicitly_assigned_name(
    emit_context: &EmitContext,
    nodes: &[tsc_ast::Node],
    node: NodeId,
) -> bool {
    if emit_context.assigned_name(node).is_some()
        && let Some(members) = nodes[node].members()
    {
        for &member in members {
            if is_class_named_evaluation_helper_block(emit_context, nodes, member) {
                return true;
            }
        }
    }
    false
}

/// Gets whether a `ClassLikeDeclaration` has a declared name or contains a
/// `static {}` block containing only a single call to the
/// `__setFunctionName` helper.
/// @internal
pub(crate) fn class_has_declared_or_explicitly_assigned_name(
    emit_context: &EmitContext,
    nodes: &[tsc_ast::Node],
    node: NodeId,
) -> bool {
    nodes[node].name().is_some() || class_has_explicitly_assigned_name(emit_context, nodes, node)
}

/// Indicates whether an expression is an anonymous function definition.
/// `node` is `ClassExpression | FunctionExpression | ArrowFunction`.
///
/// See https://tc39.es/ecma262/#sec-isanonymousfunctiondefinition
pub(crate) fn is_anonymous_function_definition(
    emit_context: &EmitContext,
    nodes: &[tsc_ast::Node],
    node: NodeId,
    mut cb: Option<&mut dyn FnMut(NodeId) -> bool>,
) -> bool {
    let node = ast::skip_outer_expressions(node, outer_expression_kinds::ALL, nodes);
    match nodes[node].kind {
        Kind::ClassExpression => {
            if class_has_declared_or_explicitly_assigned_name(emit_context, nodes, node) {
                return false;
            }
        }
        Kind::FunctionExpression => {
            if nodes[node].name().is_some() {
                return false;
            }
        }
        Kind::ArrowFunction => {
            // arrow functions are always anonymous
        }
        _ => return false,
    }
    if let Some(cb) = cb.as_deref_mut() {
        return cb(node);
    }
    true
}

/// `isNamedEvaluation`.
pub(crate) fn is_named_evaluation(
    emit_context: &EmitContext,
    nodes: &[tsc_ast::Node],
    node: NodeId,
) -> bool {
    is_named_evaluation_and(emit_context, nodes, node, None)
}

/// `isNamedEvaluationAnd`.
pub(crate) fn is_named_evaluation_and(
    emit_context: &EmitContext,
    nodes: &[tsc_ast::Node],
    node: NodeId,
    cb: Option<&mut dyn FnMut(NodeId) -> bool>,
) -> bool {
    if !ast::is_named_evaluation_source(&nodes[node], nodes) {
        return false;
    }
    match nodes[node].kind {
        Kind::ShorthandPropertyAssignment => is_anonymous_function_definition(
            emit_context,
            nodes,
            nodes[node]
                .as_shorthand_property_assignment()
                .object_assignment_initializer
                .expect("named evaluation shorthand property has no initializer"),
            cb,
        ),
        Kind::PropertyAssignment
        | Kind::VariableDeclaration
        | Kind::Parameter
        | Kind::BindingElement
        | Kind::PropertyDeclaration => is_anonymous_function_definition(
            emit_context,
            nodes,
            nodes[node]
                .initializer()
                .expect("named evaluation source has no initializer"),
            cb,
        ),
        Kind::BinaryExpression => is_anonymous_function_definition(
            emit_context,
            nodes,
            nodes[node]
                .as_binary_expression()
                .right
                .expect("named evaluation binary expression has no right"),
            cb,
        ),
        Kind::ExportAssignment => is_anonymous_function_definition(
            emit_context,
            nodes,
            nodes[node]
                .expression()
                .expect("export assignment has no expression"),
            cb,
        ),
        _ => tsc_debug::fail("Unhandled case in isNamedEvaluation"),
    }
}

/// Gets a string literal to use as the assigned name of an anonymous class or
/// function declaration. `name` must be an Identifier; `expression` is a
/// `WrappedExpression<AnonymousFunctionDefinition>`.
pub(crate) fn get_assigned_name_of_identifier(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    name: NodeId,
    expression: NodeId,
) -> NodeId {
    let skipped = ast::skip_outer_expressions(expression, outer_expression_kinds::ALL, cx.nodes);
    let original = emit_context.borrow().most_original(Some(skipped));
    if let Some(original) = original
        && (ast::is_class_declaration(&cx.nodes[original])
            || ast::is_function_declaration(&cx.nodes[original]))
        && cx.nodes[original].name().is_none()
        && ast::has_syntactic_modifier(&cx.nodes[original], ast::ModifierFlags::DEFAULT)
    {
        return emit_context.borrow_mut().factory.new_string_literal(
            cx.nodes,
            "default",
            TokenFlags::NONE,
        );
    }
    emit_context
        .borrow_mut()
        .factory
        .new_string_literal_from_node(cx.nodes, name)
}

/// `getAssignedNameOfPropertyName` — `name` must be a `PropertyName`.
/// Returns `(assignedName, updatedName)`.
pub(crate) fn get_assigned_name_of_property_name(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    name: NodeId,
    assigned_name_text: &str,
) -> (NodeId, NodeId) {
    if !assigned_name_text.is_empty() {
        let assigned_name = emit_context.borrow_mut().factory.new_string_literal(
            cx.nodes,
            assigned_name_text,
            TokenFlags::NONE,
        );
        return (assigned_name, name);
    }

    if ast::is_property_name_literal(&cx.nodes[name]) || ast::is_private_identifier(&cx.nodes[name])
    {
        let assigned_name = emit_context
            .borrow_mut()
            .factory
            .new_string_literal_from_node(cx.nodes, name);
        return (assigned_name, name);
    }

    let expression = cx.nodes[name]
        .expression()
        .expect("property name has no expression");
    if ast::is_property_name_literal(&cx.nodes[expression])
        && !ast::is_identifier(&cx.nodes[expression])
    {
        let assigned_name = emit_context
            .borrow_mut()
            .factory
            .new_string_literal_from_node(cx.nodes, expression);
        return (assigned_name, name);
    }

    tsc_debug::assert_!(
        ast::is_computed_property_name(&cx.nodes[name]),
        "Expected computed property name"
    );

    let assigned_name = emit_context
        .borrow_mut()
        .factory
        .new_generated_name_for_node(cx.nodes, name);
    emit_context
        .borrow_mut()
        .add_variable_declaration(cx.nodes, assigned_name);

    let key = emit_context
        .borrow_mut()
        .factory
        .new_prop_key_helper(cx.nodes, expression);
    let assignment =
        emit_context
            .borrow_mut()
            .factory
            .new_assignment_expression(cx.nodes, assigned_name, key);
    let updated_name = emit_context
        .borrow_mut()
        .factory
        .update_computed_property_name(cx.nodes, name, Some(assignment))
        .unwrap_or(name);
    (assigned_name, updated_name)
}

/// Creates a class `static {}` block used to dynamically set the name of a
/// class.
///
/// The `assigned_name` parameter is the expression used to resolve the
/// assigned name at runtime. This expression should not produce side
/// effects.
/// The `this_expression` parameter overrides the expression to use for the
/// actual `this` reference. This can be used to provide an expression that
/// has already had its `EmitFlags` set or may have been tracked to prevent
/// substitution.
pub(crate) fn create_class_named_evaluation_helper_block(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    assigned_name: NodeId,
    this_expression: Option<NodeId>,
) -> NodeId {
    // produces:
    //
    //  static { __setFunctionName(this, "C"); }
    //

    let this_expression = match this_expression {
        Some(t) => t,
        None => emit_context
            .borrow_mut()
            .factory
            .new_this_expression(cx.nodes),
    };

    let mut ec = emit_context.borrow_mut();
    let f = &mut ec.factory;
    let expression = f.new_set_function_name_helper(cx.nodes, this_expression, assigned_name, "");
    let statement = f.new_expression_statement(cx.nodes, Some(expression));
    let statements = f.new_node_list(vec![statement]);
    let body = f.new_block(cx.nodes, Some(statements), false /* multi_line */);
    let block =
        f.new_class_static_block_declaration(cx.nodes, None /* modifiers */, Some(body));
    drop(ec);

    // We use `emitNode.assignedName` to indicate this is a NamedEvaluation
    // helper block and to stash the expression used to resolve the assigned
    // name.
    emit_context
        .borrow()
        .set_assigned_name(block, assigned_name);
    block
}

/// Injects a class `static {}` block used to dynamically set the name of a
/// class, if one does not already exist. `node` must be a
/// `ClassLikeDeclaration`.
pub(crate) fn inject_class_named_evaluation_helper_block_if_missing(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    assigned_name: NodeId,
    this_expression: Option<NodeId>,
) -> NodeId {
    // given:
    //
    //  let C = class {
    //  };
    //
    // produces:
    //
    //  let C = class {
    //      static { __setFunctionName(this, "C"); }
    //  };

    // NOTE: If the class has a `_classThis` assignment block, this helper
    // will be injected after that block.

    if class_has_explicitly_assigned_name(&emit_context.borrow(), cx.nodes, node) {
        return node;
    }

    let named_evaluation_block = create_class_named_evaluation_helper_block(
        emit_context,
        cx,
        assigned_name,
        this_expression,
    );
    if let Some(name) = cx.nodes[node].name() {
        let block_body = cx.nodes[named_evaluation_block].body().unwrap();
        let first_statement = cx.nodes[block_body].statements().unwrap()[0];
        let loc = cx.nodes[name].loc;
        emit_context
            .borrow()
            .set_source_map_range(first_statement, loc);
    }

    let members: Vec<NodeId> = cx.nodes[node]
        .members()
        .map(<[_]>::to_vec)
        .unwrap_or_default();
    let insertion_index = members
        .iter()
        .position(|&n| is_class_this_assignment_block(&emit_context.borrow(), cx.nodes, n))
        .map(|i| i + 1)
        .unwrap_or(0);
    let mut new_members: Vec<NodeId> = Vec::with_capacity(members.len() + 1);
    new_members.extend_from_slice(&members[..insertion_index]);
    new_members.push(named_evaluation_block);
    new_members.extend_from_slice(&members[insertion_index..]);
    let member_list_loc = cx.nodes[node]
        .member_list()
        .map(|l| l.loc)
        .unwrap_or_default();
    let mut members_list = emit_context.borrow_mut().factory.new_node_list(new_members);
    members_list.loc = member_list_loc;

    let old_node = node;
    let modifiers = cx.nodes[node].modifiers().cloned();
    let name = cx.nodes[node].name();
    let type_parameters = cx.nodes[node].type_parameter_list().cloned();
    let heritage_clauses = if ast::is_class_declaration(&cx.nodes[node]) {
        cx.nodes[node]
            .as_class_declaration()
            .class_like_base
            .heritage_clauses
            .clone()
    } else {
        cx.nodes[node]
            .as_class_expression()
            .class_like_base
            .heritage_clauses
            .clone()
    };
    let node = if ast::is_class_declaration(&cx.nodes[old_node]) {
        emit_context
            .borrow_mut()
            .factory
            .update_class_declaration(
                cx.nodes,
                old_node,
                modifiers,
                name,
                type_parameters,
                heritage_clauses,
                Some(members_list),
            )
            .unwrap_or(old_node)
    } else {
        emit_context
            .borrow_mut()
            .factory
            .update_class_expression(
                cx.nodes,
                old_node,
                modifiers,
                name,
                type_parameters,
                heritage_clauses,
                Some(members_list),
            )
            .unwrap_or(old_node)
    };

    emit_context.borrow().set_assigned_name(node, assigned_name);

    // Transfer ClassThis from old to new node, since UpdateClassExpression
    // creates a new node that won't have ClassThis set on it.
    if let Some(ct) = emit_context.borrow().class_this(old_node) {
        emit_context.borrow().set_class_this(node, ct);
    }

    node
}

/// `finishTransformNamedEvaluation`.
pub(crate) fn finish_transform_named_evaluation(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    expression: NodeId,
    assigned_name: NodeId,
    ignore_empty_string_literal: bool,
) -> NodeId {
    if ignore_empty_string_literal
        && ast::is_string_literal(&cx.nodes[assigned_name])
        && cx.nodes[assigned_name].text(cx.nodes).is_empty()
    {
        return expression;
    }

    let inner_expression =
        ast::skip_outer_expressions(expression, outer_expression_kinds::ALL, cx.nodes);

    let updated_expression = if ast::is_class_expression(&cx.nodes[inner_expression]) {
        inject_class_named_evaluation_helper_block_if_missing(
            emit_context,
            cx,
            inner_expression,
            assigned_name,
            None, // this_expression
        )
    } else {
        emit_context
            .borrow_mut()
            .factory
            .new_set_function_name_helper(
                cx.nodes,
                inner_expression,
                assigned_name,
                "", // prefix
            )
    };

    emit_context.borrow_mut().factory.restore_outer_expressions(
        cx.nodes,
        Some(expression),
        updated_expression,
        outer_expression_kinds::ALL,
    )
}

/// `transformNamedEvaluationOfPropertyAssignment` — `node` must be a
/// `PropertyAssignment` that is a NamedEvaluation source.
pub(crate) fn transform_named_evaluation_of_property_assignment(
    context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> NodeId {
    // 13.2.5.5 RS: PropertyDefinitionEvaluation
    //   PropertyAssignment : PropertyName `:` AssignmentExpression
    //     ...
    //     5. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true* and _isProtoSetter_ is *false*, then
    //        a. Let _popValue_ be ? NamedEvaluation of |AssignmentExpression| with argument _propKey_.
    //     ...

    let name = cx.nodes[node]
        .name()
        .expect("property assignment has no name");
    let (assigned_name, name) =
        get_assigned_name_of_property_name(context, cx, name, assigned_name_text);
    let initializer = cx.nodes[node].initializer();
    let initializer = finish_transform_named_evaluation(
        context,
        cx,
        initializer.expect("property assignment has no initializer"),
        assigned_name,
        ignore_empty_string_literal,
    );
    context
        .borrow_mut()
        .factory
        .update_property_assignment(
            cx.nodes,
            node,
            None, // modifiers
            Some(name),
            None, // postfix_token
            None, // type_node
            Some(initializer),
        )
        .unwrap_or(node)
}

/// `transformNamedEvaluationOfShorthandAssignmentProperty` — `node` must be a
/// `ShorthandPropertyAssignment` that is a NamedEvaluation source.
pub(crate) fn transform_named_evaluation_of_shorthand_assignment_property(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> NodeId {
    // 13.15.5.3 RS: PropertyDestructuringAssignmentEvaluation
    //   AssignmentProperty : IdentifierReference Initializer?
    //     ...
    //     4. If |Initializer?| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _P_.
    //     ...

    let (name, equals_token, object_assignment_initializer) = {
        let d = cx.nodes[node].as_shorthand_property_assignment();
        (
            d.named_member_base.name,
            d.equals_token,
            d.object_assignment_initializer,
        )
    };
    let assigned_name = if !assigned_name_text.is_empty() {
        emit_context.borrow_mut().factory.new_string_literal(
            cx.nodes,
            assigned_name_text,
            TokenFlags::NONE,
        )
    } else {
        get_assigned_name_of_identifier(
            emit_context,
            cx,
            name.expect("shorthand property assignment has no name"),
            object_assignment_initializer.expect("no object assignment initializer"),
        )
    };
    let object_assignment_initializer = finish_transform_named_evaluation(
        emit_context,
        cx,
        object_assignment_initializer.expect("no object assignment initializer"),
        assigned_name,
        ignore_empty_string_literal,
    );
    emit_context
        .borrow_mut()
        .factory
        .update_shorthand_property_assignment(
            cx.nodes,
            node,
            None, // modifiers
            name,
            None, // postfix_token
            None, // type_node
            equals_token,
            Some(object_assignment_initializer),
        )
        .unwrap_or(node)
}

/// `transformNamedEvaluationOfVariableDeclaration` — `node` must be a
/// `VariableDeclaration` that is a NamedEvaluation source.
pub(crate) fn transform_named_evaluation_of_variable_declaration(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> NodeId {
    // 14.3.1.2 RS: Evaluation
    //   LexicalBinding : BindingIdentifier Initializer
    //     ...
    //     3. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //        a. Let _value_ be ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...
    //
    // 14.3.2.1 RS: Evaluation
    //   VariableDeclaration : BindingIdentifier Initializer
    //     ...
    //     3. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //        a. Let _value_ be ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...

    let name = cx.nodes[node].name();
    let initializer = cx.nodes[node].initializer();
    let assigned_name = if !assigned_name_text.is_empty() {
        emit_context.borrow_mut().factory.new_string_literal(
            cx.nodes,
            assigned_name_text,
            TokenFlags::NONE,
        )
    } else {
        get_assigned_name_of_identifier(
            emit_context,
            cx,
            name.expect("variable declaration has no name"),
            initializer.expect("variable declaration has no initializer"),
        )
    };
    let initializer = finish_transform_named_evaluation(
        emit_context,
        cx,
        initializer.expect("variable declaration has no initializer"),
        assigned_name,
        ignore_empty_string_literal,
    );
    emit_context
        .borrow_mut()
        .factory
        .update_variable_declaration(
            cx.nodes,
            node,
            name,
            None, // exclamation_token
            None, // type_node
            Some(initializer),
        )
        .unwrap_or(node)
}

/// `transformNamedEvaluationOfParameterDeclaration` — `node` must be a
/// `ParameterDeclaration` that is a NamedEvaluation source.
pub(crate) fn transform_named_evaluation_of_parameter_declaration(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> NodeId {
    // 8.6.3 RS: IteratorBindingInitialization
    //   SingleNameBinding : BindingIdentifier Initializer?
    //     ...
    //     5. If |Initializer| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...
    //
    // 14.3.3.3 RS: KeyedBindingInitialization
    //   SingleNameBinding : BindingIdentifier Initializer?
    //     ...
    //     4. If |Initializer| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...

    let (dot_dot_dot_token, name, initializer) = {
        let d = cx.nodes[node].as_parameter_declaration();
        (d.dot_dot_dot_token, d.name, d.initializer)
    };
    let assigned_name = if !assigned_name_text.is_empty() {
        emit_context.borrow_mut().factory.new_string_literal(
            cx.nodes,
            assigned_name_text,
            TokenFlags::NONE,
        )
    } else {
        get_assigned_name_of_identifier(
            emit_context,
            cx,
            name.expect("parameter declaration has no name"),
            initializer.expect("parameter declaration has no initializer"),
        )
    };
    let initializer = finish_transform_named_evaluation(
        emit_context,
        cx,
        initializer.expect("parameter declaration has no initializer"),
        assigned_name,
        ignore_empty_string_literal,
    );
    emit_context
        .borrow_mut()
        .factory
        .update_parameter_declaration(
            cx.nodes,
            node,
            None, // modifiers
            dot_dot_dot_token,
            name,
            None, // question_token
            None, // type_node
            Some(initializer),
        )
        .unwrap_or(node)
}

/// `transformNamedEvaluationOfBindingElement` — `node` must be a
/// `BindingElement` that is a NamedEvaluation source.
pub(crate) fn transform_named_evaluation_of_binding_element(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> NodeId {
    // 8.6.3 RS: IteratorBindingInitialization
    //   SingleNameBinding : BindingIdentifier Initializer?
    //     ...
    //     5. If |Initializer| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...
    //
    // 14.3.3.3 RS: KeyedBindingInitialization
    //   SingleNameBinding : BindingIdentifier Initializer?
    //     ...
    //     4. If |Initializer| is present and _v_ is *undefined*, then
    //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
    //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _bindingId_.
    //     ...

    let (dot_dot_dot_token, property_name, name, initializer) = {
        let d = cx.nodes[node].as_binding_element();
        (d.dot_dot_dot_token, d.property_name, d.name, d.initializer)
    };
    let assigned_name = if !assigned_name_text.is_empty() {
        emit_context.borrow_mut().factory.new_string_literal(
            cx.nodes,
            assigned_name_text,
            TokenFlags::NONE,
        )
    } else {
        get_assigned_name_of_identifier(
            emit_context,
            cx,
            name.expect("binding element has no name"),
            initializer.expect("binding element has no initializer"),
        )
    };
    let initializer = finish_transform_named_evaluation(
        emit_context,
        cx,
        initializer.expect("binding element has no initializer"),
        assigned_name,
        ignore_empty_string_literal,
    );
    emit_context
        .borrow_mut()
        .factory
        .update_binding_element(
            cx.nodes,
            node,
            dot_dot_dot_token,
            property_name,
            name,
            Some(initializer),
        )
        .unwrap_or(node)
}

/// `transformNamedEvaluationOfPropertyDeclaration` — `node` must be a
/// `PropertyDeclaration` that is a NamedEvaluation source.
pub(crate) fn transform_named_evaluation_of_property_declaration(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> NodeId {
    // 10.2.1.3 RS: EvaluateBody
    //   Initializer : `=` AssignmentExpression
    //     ...
    //     3. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true*, then
    //        a. Let _value_ be ? NamedEvaluation of |Initializer| with argument _functionObject_.[[ClassFieldInitializerName]].
    //     ...

    let name = cx.nodes[node]
        .name()
        .expect("property declaration has no name");
    let (assigned_name, name) =
        get_assigned_name_of_property_name(emit_context, cx, name, assigned_name_text);
    let initializer = cx.nodes[node].initializer();
    let initializer = finish_transform_named_evaluation(
        emit_context,
        cx,
        initializer.expect("property declaration has no initializer"),
        assigned_name,
        ignore_empty_string_literal,
    );
    let modifiers = cx.nodes[node].modifiers().cloned();
    emit_context
        .borrow_mut()
        .factory
        .update_property_declaration(
            cx.nodes,
            node,
            modifiers,
            Some(name),
            None, // postfix_token
            None, // type_node
            Some(initializer),
        )
        .unwrap_or(node)
}

/// `transformNamedEvaluationOfAssignmentExpression` — `node` must be a
/// `BinaryExpression` that is a NamedEvaluation source.
pub(crate) fn transform_named_evaluation_of_assignment_expression(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> NodeId {
    // 13.15.2 RS: Evaluation
    //   AssignmentExpression : LeftHandSideExpression `=` AssignmentExpression
    //     1. If |LeftHandSideExpression| is neither an |ObjectLiteral| nor an |ArrayLiteral|, then
    //        a. Let _lref_ be ? Evaluation of |LeftHandSideExpression|.
    //        b. If IsAnonymousFunctionDefinition(|AssignmentExpression|) and IsIdentifierRef of |LeftHandSideExpression| are both *true*, then
    //           i. Let _rval_ be ? NamedEvaluation of |AssignmentExpression| with argument _lref_.[[ReferencedName]].
    //     ...
    //
    //   AssignmentExpression : LeftHandSideExpression `&&=` AssignmentExpression
    //     ... (same)
    //   AssignmentExpression : LeftHandSideExpression `||=` AssignmentExpression
    //     ... (same)
    //   AssignmentExpression : LeftHandSideExpression `??=` AssignmentExpression
    //     ... (same)

    let (left, operator_token, right) = {
        let d = cx.nodes[node].as_binary_expression();
        (d.left, d.operator_token, d.right)
    };
    let assigned_name = if !assigned_name_text.is_empty() {
        emit_context.borrow_mut().factory.new_string_literal(
            cx.nodes,
            assigned_name_text,
            TokenFlags::NONE,
        )
    } else {
        get_assigned_name_of_identifier(
            emit_context,
            cx,
            left.expect("assignment expression has no left operand"),
            right.expect("assignment expression has no right operand"),
        )
    };
    let right = finish_transform_named_evaluation(
        emit_context,
        cx,
        right.expect("assignment expression has no right operand"),
        assigned_name,
        ignore_empty_string_literal,
    );
    emit_context
        .borrow_mut()
        .factory
        .update_binary_expression(
            cx.nodes,
            node,
            None, // modifiers
            left,
            None, // type_node
            operator_token,
            Some(right),
        )
        .unwrap_or(node)
}

/// `transformNamedEvaluationOfExportAssignment` — `node` must be an
/// `ExportAssignment` that is a NamedEvaluation source.
pub(crate) fn transform_named_evaluation_of_export_assignment(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    ignore_empty_string_literal: bool,
    assigned_name_text: &str,
) -> NodeId {
    // 16.2.3.7 RS: Evaluation
    //   ExportDeclaration : `export` `default` AssignmentExpression `;`
    //     1. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true*, then
    //        a. Let _value_ be ? NamedEvaluation of |AssignmentExpression| with argument `"default"`.
    //     ...

    // NOTE: Since emit for `export =` translates to `module.exports = ...`,
    // the assigned name of the class or function is `""`.

    let is_export_equals = cx.nodes[node].as_export_assignment().is_export_equals;
    let assigned_name = if !assigned_name_text.is_empty() {
        emit_context.borrow_mut().factory.new_string_literal(
            cx.nodes,
            assigned_name_text,
            TokenFlags::NONE,
        )
    } else if is_export_equals {
        emit_context
            .borrow_mut()
            .factory
            .new_string_literal(cx.nodes, "", TokenFlags::NONE)
    } else {
        emit_context
            .borrow_mut()
            .factory
            .new_string_literal(cx.nodes, "default", TokenFlags::NONE)
    };
    let expression = cx.nodes[node].expression();
    let expression = finish_transform_named_evaluation(
        emit_context,
        cx,
        expression.expect("export assignment has no expression"),
        assigned_name,
        ignore_empty_string_literal,
    );
    emit_context
        .borrow_mut()
        .factory
        .update_export_assignment(
            cx.nodes,
            node,
            None, // modifiers
            is_export_equals,
            None, // type_node
            Some(expression),
        )
        .unwrap_or(node)
}

/// Performs a shallow transformation of a `NamedEvaluation` node, such that
/// a valid name will be assigned.
pub(crate) fn transform_named_evaluation(
    context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    ignore_empty_string_literal: bool,
    assigned_name: &str,
) -> NodeId {
    match cx.nodes[node].kind {
        Kind::PropertyAssignment => transform_named_evaluation_of_property_assignment(
            context,
            cx,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        Kind::ShorthandPropertyAssignment => {
            transform_named_evaluation_of_shorthand_assignment_property(
                context,
                cx,
                node,
                ignore_empty_string_literal,
                assigned_name,
            )
        }
        Kind::VariableDeclaration => transform_named_evaluation_of_variable_declaration(
            context,
            cx,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        Kind::Parameter => transform_named_evaluation_of_parameter_declaration(
            context,
            cx,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        Kind::BindingElement => transform_named_evaluation_of_binding_element(
            context,
            cx,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        Kind::PropertyDeclaration => transform_named_evaluation_of_property_declaration(
            context,
            cx,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        Kind::BinaryExpression => transform_named_evaluation_of_assignment_expression(
            context,
            cx,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        Kind::ExportAssignment => transform_named_evaluation_of_export_assignment(
            context,
            cx,
            node,
            ignore_empty_string_literal,
            assigned_name,
        ),
        _ => tsc_debug::fail("Unhandled case in transformNamedEvaluation"),
    }
}
