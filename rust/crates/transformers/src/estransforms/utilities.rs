// Ported from tsc/internal/transformers/estransforms/utilities.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Helpers shared across the ES transforms: class-declaration → class-expression
// conversion, `x != null && x !== void 0` conditions, the `super` access
// tracking/substitution used by async and for-await, and the accessor backing
// field helper used by class fields.
//
// PORT: `superAccessState.factory` (a `*printer.NodeFactory` captured at init)
// is dropped — every use site passed `tx.Factory()`, i.e. the emit-context
// factory, which is reached here through `ec.borrow_mut().factory`.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, NodeId};
use tsc_collections::OrderedSet;
use tsc_printer::{AutoGenerateOptions, EmitContext};

use super::Ec;
use super::r#async::{assignment_target_contains_super_property, is_update_expression};
use crate::modifier_visitor::extract_modifiers;

/// `convertClassDeclarationToClassExpression(emitContext, node)` — `node`
/// must be a `ClassDeclaration`.
pub(crate) fn convert_class_declaration_to_class_expression(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    let modifiers = cx.nodes[node].modifiers().cloned();
    let (name, type_parameters, heritage_clauses, members, loc) = {
        let d = &cx.nodes[node].as_class_declaration().class_like_base;
        (
            d.name,
            d.type_parameters.clone(),
            d.heritage_clauses.clone(),
            d.members.clone(),
            cx.nodes[node].loc,
        )
    };
    let extracted = extract_modifiers(
        Some(emit_context),
        cx.nodes,
        modifiers,
        !ast::ModifierFlags::EXPORT_DEFAULT,
    );
    let updated = emit_context.borrow_mut().factory.new_class_expression(
        cx.nodes,
        extracted,
        name,
        type_parameters,
        heritage_clauses,
        members,
    );
    emit_context.borrow().set_original(updated, node);
    cx.nodes[updated].loc = loc;
    updated
}

/// `createNotNullCondition(emitContext, left, right, invert)` —
/// `left !== null && right !== void 0`, or `===`/`||` when `invert`.
pub(crate) fn create_not_null_condition(
    emit_context: &Rc<RefCell<EmitContext>>,
    cx: &mut VisitorCx<'_, '_>,
    left: NodeId,
    right: NodeId,
    invert: bool,
) -> NodeId {
    let (token, op) = if invert {
        (Kind::EqualsEqualsEqualsToken, Kind::BarBarToken)
    } else {
        (
            Kind::ExclamationEqualsEqualsToken,
            Kind::AmpersandAmpersandToken,
        )
    };
    let mut ec = emit_context.borrow_mut();
    let f = &mut ec.factory;
    let null_expr = f.new_keyword_expression(cx.nodes, Kind::NullKeyword);
    let token1 = f.new_token(cx.nodes, token);
    let left_check = f.new_binary_expression(
        cx.nodes,
        None,
        Some(left),
        None,
        Some(token1),
        Some(null_expr),
    );
    let void_zero = f.new_void_zero_expression(cx.nodes);
    let token2 = f.new_token(cx.nodes, token);
    let right_check = f.new_binary_expression(
        cx.nodes,
        None,
        Some(right),
        None,
        Some(token2),
        Some(void_zero),
    );
    let op_token = f.new_token(cx.nodes, op);
    f.new_binary_expression(
        cx.nodes,
        None,
        Some(left_check),
        None,
        Some(op_token),
        Some(right_check),
    )
}

/// `superAccessState` — tracks super property/element accesses and super
/// property assignments within async function or async generator bodies. It
/// is embedded by both `asyncTransformer` and `forAwaitTransformer` to share
/// the tracking logic.
///
/// PORT: Go embeds the struct (methods reachable as `tx.method()`); the Rust
/// port stores it behind `Rc` so the super-access visitor's own visit
/// closure can capture it without creating a self-reference through the
/// parent transformer state. Field mutability is interior (`Cell`/`RefCell`)
/// since the visit callbacks take `Fn`, not `FnMut`.
pub(crate) struct SuperAccessState<'a> {
    /// Keeps track of property names accessed on super (`super.x`) within
    /// async functions. `None` mirrors Go's nil `*OrderedSet`.
    pub captured_super_properties: RefCell<Option<OrderedSet<String>>>,
    /// Whether the async function contains an element access on super
    /// (`super[x]`).
    pub has_super_element_access: Cell<bool>,
    pub has_super_property_assignment: Cell<bool>,

    pub super_binding: Cell<Option<NodeId>>,
    pub super_index_binding: Cell<Option<NodeId>>,
    pub super_access_visitor: RefCell<Option<NodeVisitor<'a>>>,
}

impl<'a> Default for SuperAccessState<'a> {
    fn default() -> Self {
        SuperAccessState {
            captured_super_properties: RefCell::new(None),
            has_super_element_access: Cell::new(false),
            has_super_property_assignment: Cell::new(false),
            super_binding: Cell::new(None),
            super_index_binding: Cell::new(None),
            super_access_visitor: RefCell::new(None),
        }
    }
}

impl<'a> SuperAccessState<'a> {
    /// `initSuperAccessVisitor(emitContext, factory)` — the `factory`
    /// argument is subsumed by `ec` (every Go call site passes
    /// `tx.Factory()`).
    pub(crate) fn init_super_access_visitor(self: &Rc<Self>, ec: &Ec) {
        // `Weak` mirrors the Go object graph without an Rc cycle: the
        // visitor is owned by this state and its visit callback re-enters
        // the state.
        let weak = Rc::downgrade(self);
        let ec2 = ec.clone();
        let visit: Box<tsc_ast::visitor::VisitFn<'a>> = Box::new(
            move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                let s = weak
                    .upgrade()
                    .expect("superAccessState dropped during visit");
                s.visit_super_access_node(&ec2, v, cx, node)
            },
        );
        let visitor = ec.borrow().new_node_visitor(visit);
        *self.super_access_visitor.borrow_mut() = Some(visitor);
    }

    /// `visitSuperAccessNode` walks the async/generator body and replaces
    /// super property/element accesses with _super/_superIndex references.
    /// This is necessary because the async body ends up inside a generator
    /// function where `super` is not valid.
    fn visit_super_access_node(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::CallExpression => {
                let call_expr = cx.nodes[node].as_call_expression().expression;
                if ast::is_super_property(&cx.nodes[call_expr.unwrap()], cx.nodes) {
                    return Some(
                        self.substitute_call_expression_with_super_access(ec, v, cx, node),
                    );
                }
                Some(super::visit_each_child(v, cx, node))
            }
            Kind::PropertyAccessExpression => {
                if cx.nodes[cx.nodes[node].expression().unwrap()].kind == Kind::SuperKeyword {
                    // super.x → _super.x
                    let name = cx.nodes[node].name();
                    return Some(ec.borrow_mut().factory.new_property_access_expression(
                        cx.nodes,
                        self.super_binding.get(),
                        None,
                        name,
                        ast::NodeFlags::NONE,
                    ));
                }
                Some(super::visit_each_child(v, cx, node))
            }
            Kind::ElementAccessExpression => {
                if cx.nodes[cx.nodes[node].expression().unwrap()].kind == Kind::SuperKeyword {
                    // super[x] → _superIndex(x) or _superIndex(x).value
                    let argument_expression = cx.nodes[node]
                        .as_element_access_expression()
                        .argument_expression;
                    return Some(self.create_super_element_access_in_async_method(
                        ec,
                        cx,
                        argument_expression.unwrap(),
                    ));
                }
                Some(super::visit_each_child(v, cx, node))
            }
            // Don't recurse into non-arrow function scopes or classes
            Kind::FunctionExpression
            | Kind::FunctionDeclaration
            | Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::Constructor
            | Kind::ClassDeclaration
            | Kind::ClassExpression => Some(node),
            _ => Some(super::visit_each_child(v, cx, node)),
        }
    }

    /// `substituteSuperAccessesInBody`.
    pub(crate) fn substitute_super_accesses_in_body(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        body: NodeId,
    ) -> Option<NodeId> {
        self.super_access_visitor
            .borrow()
            .as_ref()
            .expect("super access visitor not initialized")
            .visit_node(cx, Some(body))
    }

    /// `substituteCallExpressionWithSuperAccess` handles `super.x(args)` and
    /// `super[x](args)`. `call` must be a `CallExpression` node.
    fn substitute_call_expression_with_super_access(
        &self,
        ec: &Ec,
        visitor: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        call: NodeId,
    ) -> NodeId {
        let expression = cx.nodes[call].as_call_expression().expression.unwrap();
        let target: NodeId;
        if ast::is_property_access_expression(&cx.nodes[expression]) {
            // super.x(args) → _super.x.call(this, args)
            let name = cx.nodes[expression].as_property_access_expression().name;
            target = ec.borrow_mut().factory.new_property_access_expression(
                cx.nodes,
                self.super_binding.get(),
                None,
                name,
                ast::NodeFlags::NONE,
            );
        } else if ast::is_element_access_expression(&cx.nodes[expression]) {
            // super[x](args) → _superIndex(x).call(this, args) or
            // _superIndex(x).value.call(this, args)
            let argument_expression = cx.nodes[expression]
                .as_element_access_expression()
                .argument_expression
                .unwrap();
            target = self.create_super_element_access_in_async_method(ec, cx, argument_expression);
        } else {
            return super::visit_each_child(visitor, cx, call);
        }

        let call_target = {
            let mut e = ec.borrow_mut();
            let call_ident = e.factory.new_identifier(cx.nodes, "call");
            e.factory.new_property_access_expression(
                cx.nodes,
                Some(target),
                None,
                Some(call_ident),
                ast::NodeFlags::NONE,
            )
        };

        let mut all_args: Vec<NodeId> = Vec::new();
        all_args.push(ec.borrow_mut().factory.new_this_expression(cx.nodes));
        if let Some(arguments) = &cx.nodes[call].as_call_expression().arguments {
            if let Some(visited_args) = visitor.visit_nodes(cx, Some(arguments.clone())) {
                all_args.extend_from_slice(&visited_args.nodes);
            }
        }

        let arg_list = ec.borrow_mut().factory.new_node_list(all_args);
        let result = ec.borrow_mut().factory.new_call_expression(
            cx.nodes,
            Some(call_target),
            None,
            None,
            Some(arg_list),
            ast::NodeFlags::NONE,
        );
        cx.nodes[result].loc = cx.nodes[call].loc;
        result
    }

    /// `createSuperElementAccessInAsyncMethod` creates `_superIndex(x)` or
    /// `_superIndex(x).value`.
    fn create_super_element_access_in_async_method(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        argument_expression: NodeId,
    ) -> NodeId {
        let arg_list = ec
            .borrow_mut()
            .factory
            .new_node_list(vec![argument_expression]);
        let super_index_call = ec.borrow_mut().factory.new_call_expression(
            cx.nodes,
            self.super_index_binding.get(),
            None,
            None,
            Some(arg_list),
            ast::NodeFlags::NONE,
        );
        if self.has_super_property_assignment.get() {
            let value_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "value");
            return ec.borrow_mut().factory.new_property_access_expression(
                cx.nodes,
                Some(super_index_call),
                None,
                Some(value_ident),
                ast::NodeFlags::NONE,
            );
        }
        super_index_call
    }

    /// `createSuperAccessVariableStatement` creates a variable named `_super`
    /// with accessor properties for the given property names.
    ///
    /// Create a variable declaration with a getter/setter (if binding)
    /// definition for each name:
    ///
    /// ```text
    /// const _super = Object.create(null, {
    ///     x: { get: () => super.x },                           // read-only
    ///     x: { get: () => super.x, set: (v) => super.x = v }, // read-write
    /// });
    /// ```
    pub(crate) fn create_super_access_variable_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
    ) -> NodeId {
        let mut accessors: Vec<NodeId> = Vec::new();

        // PORT: Go iterates the OrderedSet directly; the RefCell is borrowed
        // once for the whole loop (factory calls only borrow `ec`, never this
        // RefCell).
        let names: Vec<String> = self
            .captured_super_properties
            .borrow()
            .as_ref()
            .map(|s| s.values().cloned().collect())
            .unwrap_or_default();
        for name in names {
            let mut e = ec.borrow_mut();
            let f = &mut e.factory;
            let mut descriptor_properties: Vec<NodeId> = Vec::new();

            // getter: get: () => super.name
            let super_kw = f.new_keyword_expression(cx.nodes, Kind::SuperKeyword);
            let name_ident = f.new_identifier(cx.nodes, &name);
            let getter_body = f.new_property_access_expression(
                cx.nodes,
                Some(super_kw),
                None,
                Some(name_ident),
                ast::NodeFlags::NONE,
            );
            let empty_params = f.new_node_list(vec![]);
            let arrow_token = f.new_token(cx.nodes, Kind::EqualsGreaterThanToken);
            let getter_arrow = f.new_arrow_function(
                cx.nodes,
                None,
                None,
                Some(empty_params),
                None,
                None,
                Some(arrow_token),
                Some(getter_body),
            );
            let get_ident = f.new_identifier(cx.nodes, "get");
            let getter = f.new_property_assignment(
                cx.nodes,
                None,
                Some(get_ident),
                None,
                None,
                Some(getter_arrow),
            );
            descriptor_properties.push(getter);

            if self.has_super_property_assignment.get() {
                // setter: set: v => super.name = v
                let v_ident = f.new_identifier(cx.nodes, "v");
                let v_param = f.new_parameter_declaration(
                    cx.nodes,
                    None,
                    None,
                    Some(v_ident),
                    None,
                    None,
                    None,
                );
                let super_kw = f.new_keyword_expression(cx.nodes, Kind::SuperKeyword);
                let name_ident = f.new_identifier(cx.nodes, &name);
                let super_prop = f.new_property_access_expression(
                    cx.nodes,
                    Some(super_kw),
                    None,
                    Some(name_ident),
                    ast::NodeFlags::NONE,
                );
                let v_ident2 = f.new_identifier(cx.nodes, "v");
                let assign_expr = f.new_assignment_expression(cx.nodes, super_prop, v_ident2);
                let param_list = f.new_node_list(vec![v_param]);
                let arrow_token = f.new_token(cx.nodes, Kind::EqualsGreaterThanToken);
                let setter_arrow = f.new_arrow_function(
                    cx.nodes,
                    None,
                    None,
                    Some(param_list),
                    None,
                    None,
                    Some(arrow_token),
                    Some(assign_expr),
                );
                let set_ident = f.new_identifier(cx.nodes, "set");
                let setter = f.new_property_assignment(
                    cx.nodes,
                    None,
                    Some(set_ident),
                    None,
                    None,
                    Some(setter_arrow),
                );
                descriptor_properties.push(setter);
            }

            let descriptor_list = f.new_node_list(descriptor_properties);
            let descriptor =
                f.new_object_literal_expression(cx.nodes, Some(descriptor_list), false);
            let name_ident = f.new_identifier(cx.nodes, &name);
            let accessor = f.new_property_assignment(
                cx.nodes,
                None,
                Some(name_ident),
                None,
                None,
                Some(descriptor),
            );
            accessors.push(accessor);
        }

        let mut e = ec.borrow_mut();
        let f = &mut e.factory;
        let accessor_list = f.new_node_list(accessors);
        let descriptors_object =
            f.new_object_literal_expression(cx.nodes, Some(accessor_list), true);

        let object_ident = f.new_identifier(cx.nodes, "Object");
        let create_ident = f.new_identifier(cx.nodes, "create");
        let object_create = f.new_property_access_expression(
            cx.nodes,
            Some(object_ident),
            None,
            Some(create_ident),
            ast::NodeFlags::NONE,
        );
        let null_expr = f.new_keyword_expression(cx.nodes, Kind::NullKeyword);
        let create_args = f.new_node_list(vec![null_expr, descriptors_object]);
        let object_create_call = f.new_call_expression(
            cx.nodes,
            Some(object_create),
            None,
            None,
            Some(create_args),
            ast::NodeFlags::NONE,
        );

        let decl = f.new_variable_declaration(
            cx.nodes,
            self.super_binding.get(),
            None,
            None,
            Some(object_create_call),
        );
        let decl_list_nodes = f.new_node_list(vec![decl]);
        let decl_list =
            f.new_variable_declaration_list(cx.nodes, Some(decl_list_nodes), ast::NodeFlags::CONST);
        f.new_variable_statement(cx.nodes, None, Some(decl_list))
    }

    /// `trackSuperAccess` records super property/element accesses and super
    /// property assignments for the enclosing async method body. Called from
    /// both the main visitor and auxiliary visitors to ensure super accesses
    /// are tracked regardless of whether the node has transform flags.
    pub(crate) fn track_super_access(&self, cx: &VisitorCx<'_, '_>, node: NodeId) {
        if self.captured_super_properties.borrow().is_none() {
            return;
        }
        match cx.nodes[node].kind {
            Kind::PropertyAccessExpression => {
                if cx.nodes[cx.nodes[node].expression().unwrap()].kind == Kind::SuperKeyword {
                    let name = cx.nodes[node].name().unwrap();
                    let text = cx.nodes[name].text(cx.nodes).into_owned();
                    self.captured_super_properties
                        .borrow_mut()
                        .as_mut()
                        .unwrap()
                        .add(text);
                }
            }
            Kind::ElementAccessExpression => {
                if cx.nodes[cx.nodes[node].expression().unwrap()].kind == Kind::SuperKeyword {
                    self.has_super_element_access.set(true);
                }
            }
            Kind::BinaryExpression => {
                let b = cx.nodes[node].as_binary_expression();
                if b.operator_token
                    .is_some_and(|t| cx.nodes[t].kind.is_assignment_operator())
                    && b.left
                        .is_some_and(|l| assignment_target_contains_super_property(cx, l))
                {
                    self.has_super_property_assignment.set(true);
                }
            }
            Kind::PrefixUnaryExpression => {
                if is_update_expression(&cx.nodes[node])
                    && assignment_target_contains_super_property(
                        cx,
                        cx.nodes[node].as_prefix_unary_expression().operand.unwrap(),
                    )
                {
                    self.has_super_property_assignment.set(true);
                }
            }
            Kind::PostfixUnaryExpression => {
                if is_update_expression(&cx.nodes[node])
                    && assignment_target_contains_super_property(
                        cx,
                        cx.nodes[node]
                            .as_postfix_unary_expression()
                            .operand
                            .unwrap(),
                    )
                {
                    self.has_super_property_assignment.set(true);
                }
            }
            _ => {}
        }
    }
}

/// `createAccessorPropertyBackingField` creates a private backing field for
/// an `accessor` PropertyDeclaration. `node` must be a `PropertyDeclaration`.
pub(crate) fn create_accessor_property_backing_field(
    ec: &Ec,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    modifiers: Option<ast::ModifierList>,
    initializer: Option<NodeId>,
) -> NodeId {
    let name = cx.nodes[node].name().unwrap();
    let backing_name = ec
        .borrow_mut()
        .factory
        .new_generated_private_name_for_node_ex(
            cx.nodes,
            name,
            &AutoGenerateOptions {
                suffix: "_accessor_storage".to_string(),
                ..Default::default()
            },
        );
    ec.borrow_mut()
        .factory
        .update_property_declaration(
            cx.nodes,
            node,
            modifiers,
            Some(backing_name),
            None, // postfix_token
            None, // type_node
            initializer,
        )
        .unwrap_or(node)
}
