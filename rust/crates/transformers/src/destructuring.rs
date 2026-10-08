// Ported from tsc/internal/transformers/destructuring.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Destructuring flattening: decomposes binding/assignment patterns into
// individual element accesses and assignments, used by the ES/module/TS
// downlevel transforms (ported separately).
//
// PORT notes:
//   - Go's `flattener` carries four function fields set per entry point
//     (`emitBindingOrAssignment`, `create{Array,Object}BindingOrAssignmentPattern`,
//     `createArrayBindingOrAssignmentElement`). Rust cannot take method
//     values, so `FlattenMode` selects the same dispatch.
//   - `f.tx` (the `*Transformer`) splits into `tx` (`Transformer`, for
//     `Visitor()`/`EmitContext()`) and `cx` (`VisitorCx`, the arena +
//     transform factory) since Rust threads both through a visit.
//   - Element slices from `GetElementsOfBindingOrAssignmentPattern` are
//     cloned into `Vec`s because the arena is mutated while iterating (Go
//     shares the backing array with the AST).

use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{self as ast, Kind, Node, NodeId, SubtreeFacts};
use tsc_core::text::TextRange;

use crate::transformer::Transformer;
use crate::utilities::{is_simple_copiable_expression, is_simple_inlineable_expression};

/// `FlattenLevel` controls how deeply binding/assignment patterns are
/// decomposed.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum FlattenLevel {
    /// `FlattenLevelAll` — fully decompose all patterns into individual
    /// assignments/bindings.
    All,
    /// `FlattenLevelObjectRest` — only decompose patterns containing object
    /// rest elements.
    ObjectRest,
}

/// `CreateAssignmentCallback` — used to create custom assignment expressions
/// during destructuring flattening. When provided, `name` is always an
/// Identifier, and the callback can wrap the assignment with additional logic
/// (e.g., export expressions in CJS modules or namespace member assignments).
///
/// PORT: Go callbacks capture their transform's `*Transformer`; Rust
/// callbacks additionally receive the in-flight `(visitor, cx)` pair, and
/// should capture `Rc<RefCell<EmitContext>>` if they need emit-context ops.
pub type CreateAssignmentCallback<'a> = dyn for<'v, 'cx, 'f> FnMut(
        &'v NodeVisitor<'a>,
        &'v mut VisitorCx<'cx, 'f>,
        NodeId,         // name — always an Identifier node
        Option<NodeId>, // value (Go `*ast.Expression`, nilable)
        &TextRange,     // location (Go `*core.TextRange`, always non-nil here)
    ) -> NodeId
    + 'a;

/// `FlattenDestructuringAssignment` flattens a destructuring assignment
/// expression into a sequence of individual property/element access
/// assignments. Supports custom assignment callbacks for module export or
/// namespace member expressions.
///
/// `node` is a `VariableDeclaration` or a destructuring-assignment
/// `BinaryExpression`. `None` return mirrors a nil `*ast.Expression`.
pub fn flatten_destructuring_assignment<'a>(
    tx: &Transformer<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    needs_value: bool,
    level: FlattenLevel,
    create_assignment_callback: Option<Box<CreateAssignmentCallback<'a>>>,
) -> Option<NodeId> {
    let mut f = Flattener {
        tx,
        cx,
        level,
        create_assignment_callback,
        expressions: Vec::new(),
        declarations: Vec::new(),
        has_transformed_prior_element: false,
        hoist_temp_variables: true,
        mode: FlattenMode::Assignment,
    };
    f.flatten_destructuring_assignment(node, needs_value)
}

/// `pendingDecl` — tracks a pending variable declaration during binding
/// flattening.
struct PendingDecl {
    pending_expressions: Vec<NodeId>,
    name: Option<NodeId>,
    value: Option<NodeId>,
    location: TextRange,
    original: Option<NodeId>,
}

/// `FlattenDestructuringBinding` flattens a binding pattern in a variable
/// declaration or parameter into individual variable declarations. Returns a
/// single `VariableDeclaration`, a `SyntaxList` of declarations, or `None`
/// (Go nil).
///
/// `node` is a `VariableDeclaration`, `ParameterDeclaration`, or
/// `BindingElement`.
pub fn flatten_destructuring_binding<'a>(
    tx: &Transformer<'a>,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    rval: Option<NodeId>,
    level: FlattenLevel,
    hoist_temp_variables: bool,
    skip_initializer: bool,
) -> Option<NodeId> {
    let mut f = Flattener {
        tx,
        cx,
        level,
        create_assignment_callback: None,
        expressions: Vec::new(),
        declarations: Vec::new(),
        has_transformed_prior_element: false,
        hoist_temp_variables,
        mode: FlattenMode::Binding,
    };
    f.flatten_destructuring_binding(node, rval, skip_initializer)
}

/// `FlattenMode` — selects the assignment/binding implementations that Go
/// installs as `flattener` function fields.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FlattenMode {
    Assignment,
    Binding,
}

/// `flattener` encapsulates the state and logic for flattening destructuring
/// patterns. Equivalent to TypeScript's `FlattenContext` in destructuring.ts.
struct Flattener<'t, 'a, 'cx, 'f> {
    tx: &'t Transformer<'a>,
    cx: &'t mut VisitorCx<'cx, 'f>,
    level: FlattenLevel,

    create_assignment_callback: Option<Box<CreateAssignmentCallback<'a>>>,

    // State
    expressions: Vec<NodeId>,
    declarations: Vec<PendingDecl>,
    has_transformed_prior_element: bool,
    hoist_temp_variables: bool,

    // Mode dispatch (Go's function fields)
    mode: FlattenMode,
}

impl<'t, 'a, 'cx, 'f> Flattener<'t, 'a, 'cx, 'f> {
    // --- Mode dispatch (Go's flattener function fields) ---

    /// `f.emitBindingOrAssignment`
    fn emit_binding_or_assignment(
        &mut self,
        target: NodeId,
        value: Option<NodeId>,
        location: TextRange,
        original: Option<NodeId>,
    ) {
        match self.mode {
            FlattenMode::Assignment => {
                self.emit_assignment(target, value, location, original);
            }
            FlattenMode::Binding => {
                self.emit_binding(target, value, location, original);
            }
        }
    }

    /// `f.createArrayBindingOrAssignmentPattern`
    fn create_array_binding_or_assignment_pattern(&mut self, elements: Vec<NodeId>) -> NodeId {
        match self.mode {
            // `(*flattener) createArrayAssignmentPattern`
            FlattenMode::Assignment => {
                let list = self
                    .tx
                    .emit_context()
                    .borrow()
                    .factory
                    .new_node_list(elements);
                self.tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_array_literal_expression(self.cx.nodes, Some(list), false)
            }
            // `(*flattener) createArrayBindingPattern`
            FlattenMode::Binding => {
                let list = self
                    .tx
                    .emit_context()
                    .borrow()
                    .factory
                    .new_node_list(elements);
                self.tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_binding_pattern(self.cx.nodes, Kind::ArrayBindingPattern, Some(list))
            }
        }
    }

    /// `f.createObjectBindingOrAssignmentPattern`
    fn create_object_binding_or_assignment_pattern(&mut self, elements: Vec<NodeId>) -> NodeId {
        match self.mode {
            // `(*flattener) createObjectAssignmentPattern`
            FlattenMode::Assignment => {
                let list = self
                    .tx
                    .emit_context()
                    .borrow()
                    .factory
                    .new_node_list(elements);
                self.tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_object_literal_expression(self.cx.nodes, Some(list), false)
            }
            // `(*flattener) createObjectBindingPattern`
            FlattenMode::Binding => {
                let list = self
                    .tx
                    .emit_context()
                    .borrow()
                    .factory
                    .new_node_list(elements);
                self.tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_binding_pattern(self.cx.nodes, Kind::ObjectBindingPattern, Some(list))
            }
        }
    }

    /// `f.createArrayBindingOrAssignmentElement`
    fn create_array_binding_or_assignment_element(&mut self, expr: NodeId) -> NodeId {
        match self.mode {
            // `(*flattener) createArrayAssignmentElement`
            FlattenMode::Assignment => expr,
            // `(*flattener) createArrayBindingElement`
            FlattenMode::Binding => self
                .tx
                .emit_context()
                .borrow_mut()
                .factory
                .new_binding_element(self.cx.nodes, None, None, Some(expr), None),
        }
    }

    // --- Assignment mode callbacks ---

    /// `(*flattener) emitAssignment`
    fn emit_assignment(
        &mut self,
        target: NodeId,
        value: Option<NodeId>,
        location: TextRange,
        original: Option<NodeId>,
    ) {
        let expression = if let Some(callback) = self.create_assignment_callback.as_mut()
            && ast::is_identifier(&self.cx.nodes[target])
        {
            // `f.createAssignmentCallback(target, value, &location)`
            callback(self.tx.visitor(), self.cx, target, value, &location)
        } else {
            let left = self
                .tx
                .visitor()
                .visit_node(self.cx, Some(target))
                .expect("VisitNode returned no node");
            let mut ctx = self.tx.emit_context().borrow_mut();
            let expression = ctx.factory.new_assignment_expression(
                self.cx.nodes,
                left,
                value.expect("assignment has no value"),
            );
            self.cx.nodes[expression].loc = location;
            expression
        };
        self.tx
            .emit_context()
            .borrow()
            .set_original(expression, original.expect("Original cannot be nil."));
        self.emit_expression(expression);
    }

    // --- Binding mode callbacks ---

    /// `(*flattener) emitBinding`
    fn emit_binding(
        &mut self,
        target: NodeId,
        mut value: Option<NodeId>,
        location: TextRange,
        original: Option<NodeId>,
    ) {
        if !self.expressions.is_empty() {
            // `value = InlineExpressions(append(f.expressions, value))`.
            // PORT: Go may append a nil `value`; `Option` elements cannot be
            // represented in the inline list, so a `None` value is dropped.
            let mut expressions = std::mem::take(&mut self.expressions);
            if let Some(v) = value {
                expressions.push(v);
            }
            value = self
                .tx
                .emit_context()
                .borrow_mut()
                .factory
                .inline_expressions(self.cx.nodes, &expressions);
        }
        self.declarations.push(PendingDecl {
            pending_expressions: Vec::new(),
            name: Some(target),
            value,
            location,
            original,
        });
    }

    // --- Shared helpers ---

    /// `(*flattener) emitExpression`
    fn emit_expression(&mut self, expr: NodeId) {
        self.expressions.push(expr);
    }

    /// `(*flattener) ensureIdentifier`
    fn ensure_identifier(
        &mut self,
        value: NodeId,
        reuse_identifier_expressions: bool,
        location: TextRange,
    ) -> NodeId {
        if reuse_identifier_expressions && ast::is_identifier(&self.cx.nodes[value]) {
            return value;
        }
        let temp = self
            .tx
            .emit_context()
            .borrow_mut()
            .factory
            .new_temp_variable(self.cx.nodes);
        if self.hoist_temp_variables {
            self.tx
                .emit_context()
                .borrow_mut()
                .add_variable_declaration(self.cx.nodes, temp);
            let assign = self
                .tx
                .emit_context()
                .borrow_mut()
                .factory
                .new_assignment_expression(self.cx.nodes, temp, value);
            self.cx.nodes[assign].loc = location;
            self.emit_expression(assign);
        } else {
            self.emit_binding_or_assignment(temp, Some(value), location, None);
        }
        temp
    }

    /// `(*flattener) createDefaultValueCheck`
    fn create_default_value_check(
        &mut self,
        value: NodeId,
        default_value: NodeId,
        location: TextRange,
    ) -> NodeId {
        let value = self.ensure_identifier(value, true, location);
        let mut ctx = self.tx.emit_context().borrow_mut();
        let type_check = ctx
            .factory
            .new_type_check(self.cx.nodes, value, "undefined");
        let question_token = ctx.factory.new_token(self.cx.nodes, Kind::QuestionToken);
        let colon_token = ctx.factory.new_token(self.cx.nodes, Kind::ColonToken);
        ctx.factory.new_conditional_expression(
            self.cx.nodes,
            Some(type_check),
            Some(question_token),
            Some(default_value),
            Some(colon_token),
            Some(value),
        )
    }

    /// `(*flattener) createDestructuringPropertyAccess`
    fn create_destructuring_property_access(
        &mut self,
        value: Option<NodeId>,
        property_name: Option<NodeId>,
    ) -> NodeId {
        let property_name = property_name.expect("binding element has no property name");
        if ast::is_computed_property_name(&self.cx.nodes[property_name]) {
            let argument_expression = {
                let expression = self.cx.nodes[property_name]
                    .expression()
                    .expect("computed property name has no expression");
                let visited = self
                    .tx
                    .visitor()
                    .visit_node(self.cx, Some(expression))
                    .expect("VisitNode returned no node");
                let loc = self.cx.nodes[property_name].loc;
                self.ensure_identifier(visited, false, loc)
            };
            self.tx
                .emit_context()
                .borrow_mut()
                .factory
                .new_element_access_expression(
                    self.cx.nodes,
                    value,
                    None,
                    Some(argument_expression),
                    ast::NodeFlags::NONE,
                )
        } else if ast::is_string_or_numeric_literal_like(&self.cx.nodes[property_name])
            || ast::is_big_int_literal(&self.cx.nodes[property_name])
        {
            let argument_expression = self
                .tx
                .emit_context()
                .borrow_mut()
                .factory
                .clone_node(self.cx.nodes, property_name);
            self.tx
                .emit_context()
                .borrow_mut()
                .factory
                .new_element_access_expression(
                    self.cx.nodes,
                    value,
                    None,
                    Some(argument_expression),
                    ast::NodeFlags::NONE,
                )
        } else {
            let name = {
                let text = self.cx.nodes[property_name]
                    .text(self.cx.nodes)
                    .into_owned();
                self.tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_identifier(self.cx.nodes, &text)
            };
            self.tx
                .emit_context()
                .borrow_mut()
                .factory
                .new_property_access_expression(
                    self.cx.nodes,
                    value,
                    None,
                    Some(name),
                    ast::NodeFlags::NONE,
                )
        }
    }

    // --- Entry points ---

    /// `(*flattener) flattenDestructuringAssignment`
    fn flatten_destructuring_assignment(
        &mut self,
        node: NodeId,
        needs_value: bool,
    ) -> Option<NodeId> {
        let mut node = node;
        let mut location = self.cx.nodes[node].loc;
        let mut value: Option<NodeId> = None;
        if ast::is_destructuring_assignment(&self.cx.nodes[node], self.cx.nodes) {
            value = self.cx.nodes[node].as_binary_expression().right;
            loop {
                let left = self.cx.nodes[node]
                    .as_binary_expression()
                    .left
                    .expect("destructuring assignment has no left operand");
                if !(ast::is_empty_array_literal(&self.cx.nodes[left])
                    || ast::is_empty_object_literal(&self.cx.nodes[left]))
                {
                    break;
                }
                let v = value.expect("destructuring assignment has no right operand");
                if ast::is_destructuring_assignment(&self.cx.nodes[v], self.cx.nodes) {
                    node = v;
                    location = self.cx.nodes[node].loc;
                    value = self.cx.nodes[node].as_binary_expression().right;
                } else {
                    return self.tx.visitor().visit_node(self.cx, Some(v));
                }
            }
        }

        if let Some(v) = value {
            value = self.tx.visitor().visit_node(self.cx, Some(v));
            let value_id = value.expect("VisitNode returned no node");
            let assigns_to_name = ast::is_identifier(&self.cx.nodes[value_id])
                && binding_or_assignment_element_assigns_to_name(
                    self.cx.nodes,
                    node,
                    self.cx.nodes[value_id].text(self.cx.nodes).as_ref(),
                );
            if assigns_to_name
                || binding_or_assignment_element_contains_non_literal_computed_name(
                    self.cx.nodes,
                    node,
                )
            {
                value = Some(self.ensure_identifier(value_id, false, location));
            } else if needs_value {
                value = Some(self.ensure_identifier(value_id, true, location));
            } else if ast::node_is_synthesized(&self.cx.nodes[node]) {
                location = self.cx.nodes[value_id].loc;
            }
        }

        let skip_initializer =
            ast::is_destructuring_assignment(&self.cx.nodes[node], self.cx.nodes);
        self.flatten_binding_or_assignment_element(node, value, location, skip_initializer);

        if needs_value && let Some(v) = value {
            if self.expressions.is_empty() {
                return Some(v);
            }
            self.expressions.push(v);
        }

        if let Some(res) = self
            .tx
            .emit_context()
            .borrow_mut()
            .factory
            .inline_expressions(self.cx.nodes, &self.expressions)
        {
            return Some(res);
        }
        Some(
            self.tx
                .emit_context()
                .borrow_mut()
                .factory
                .new_omitted_expression(self.cx.nodes),
        )
    }

    /// `(*flattener) flattenDestructuringBinding`
    fn flatten_destructuring_binding(
        &mut self,
        node: NodeId,
        rval: Option<NodeId>,
        skip_initializer: bool,
    ) -> Option<NodeId> {
        let mut node = node;
        if ast::is_variable_declaration(&self.cx.nodes[node]) {
            let initializer =
                get_initializer_of_binding_or_assignment_element(self.cx.nodes, Some(node));
            let should_ensure = initializer.is_some_and(|init| {
                (ast::is_identifier(&self.cx.nodes[init])
                    && binding_or_assignment_element_assigns_to_name(
                        self.cx.nodes,
                        node,
                        self.cx.nodes[init].text(self.cx.nodes).as_ref(),
                    ))
                    || binding_or_assignment_element_contains_non_literal_computed_name(
                        self.cx.nodes,
                        node,
                    )
            });
            if let Some(init) = initializer
                && should_ensure
            {
                let init_loc = self.cx.nodes[init].loc;
                let visited = self
                    .tx
                    .visitor()
                    .visit_node(self.cx, Some(init))
                    .expect("VisitNode returned no node");
                let initializer = Some(self.ensure_identifier(visited, false, init_loc));
                let name = self.cx.nodes[node].name();
                node = self
                    .tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .update_variable_declaration(self.cx.nodes, node, name, None, None, initializer)
                    .unwrap_or(node);
            }
        }

        let loc = self.cx.nodes[node].loc;
        self.flatten_binding_or_assignment_element(node, rval, loc, skip_initializer);

        if !self.expressions.is_empty() {
            let temp = self
                .tx
                .emit_context()
                .borrow_mut()
                .factory
                .new_temp_variable(self.cx.nodes);
            if self.hoist_temp_variables {
                let expressions = std::mem::take(&mut self.expressions);
                let value = self
                    .tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .inline_expressions(self.cx.nodes, &expressions);
                self.emit_binding_or_assignment(temp, value, TextRange::default(), None);
            } else {
                self.tx
                    .emit_context()
                    .borrow_mut()
                    .add_variable_declaration(self.cx.nodes, temp);
                let last = self.declarations.last_mut().expect("declarations is empty");
                let assign = self
                    .tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_assignment_expression(
                        self.cx.nodes,
                        temp,
                        last.value.expect("pending declaration has no value"),
                    );
                last.pending_expressions.push(assign);
                last.pending_expressions.append(&mut self.expressions);
                last.value = Some(temp);
            }
        }

        let mut decls: Vec<NodeId> = Vec::with_capacity(self.declarations.len());
        for pending in &self.declarations {
            let mut expr = pending.value;
            if !pending.pending_expressions.is_empty() {
                // `InlineExpressions(append(pending.pendingExpressions, pending.value))`
                let mut expressions = pending.pending_expressions.clone();
                if let Some(v) = pending.value {
                    expressions.push(v);
                }
                expr = self
                    .tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .inline_expressions(self.cx.nodes, &expressions);
            }
            let decl = self
                .tx
                .emit_context()
                .borrow_mut()
                .factory
                .new_variable_declaration(self.cx.nodes, pending.name, None, None, expr);
            self.cx.nodes[decl].loc = pending.location;
            if let Some(original) = pending.original {
                self.tx.emit_context().borrow().set_original(decl, original);
            }
            decls.push(decl);
        }

        match decls.len() {
            1 => decls.into_iter().next(),
            0 => None,
            _ => Some(
                self.tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_syntax_list(self.cx.nodes, &decls),
            ),
        }
    }

    // --- Core flattening ---

    /// `(*flattener) flattenBindingOrAssignmentElement`
    fn flatten_binding_or_assignment_element(
        &mut self,
        element: NodeId,
        value: Option<NodeId>,
        location: TextRange,
        skip_initializer: bool,
    ) {
        let Some(binding_target) =
            ast::get_target_of_binding_or_assignment_element(element, self.cx.nodes)
        else {
            return;
        };
        let mut value = value;
        if !skip_initializer {
            let init =
                get_initializer_of_binding_or_assignment_element(self.cx.nodes, Some(element));
            let initializer = self.tx.visitor().visit_node(self.cx, init);
            if let Some(initializer) = initializer {
                if let Some(v) = value {
                    let checked = self.create_default_value_check(v, initializer, location);
                    value = Some(checked);
                    if !is_simple_copiable_expression(&self.cx.nodes[initializer])
                        && (ast::is_binding_pattern(&self.cx.nodes[binding_target])
                            || ast::is_assignment_pattern(&self.cx.nodes[binding_target]))
                    {
                        value = Some(self.ensure_identifier(checked, true, location));
                    }
                } else {
                    value = Some(initializer);
                }
            } else if value.is_none() {
                value = Some(
                    self.tx
                        .emit_context()
                        .borrow_mut()
                        .factory
                        .new_void_zero_expression(self.cx.nodes),
                );
            }
        }

        if is_object_binding_or_assignment_pattern(self.cx.nodes, Some(binding_target)) {
            self.flatten_object_binding_or_assignment_pattern(
                element,
                binding_target,
                value,
                location,
            );
        } else if is_array_binding_or_assignment_pattern(self.cx.nodes, Some(binding_target)) {
            self.flatten_array_binding_or_assignment_pattern(
                element,
                binding_target,
                value,
                location,
            );
        } else {
            self.emit_binding_or_assignment(binding_target, value, location, Some(element));
        }
    }

    /// `(*flattener) flattenObjectBindingOrAssignmentPattern`
    fn flatten_object_binding_or_assignment_pattern(
        &mut self,
        parent: NodeId,
        pattern: NodeId,
        value: Option<NodeId>,
        location: TextRange,
    ) {
        // PORT: Go iterates `pattern.Elements.Nodes` while mutating the AST;
        // the slice is cloned here because the arena is borrowed mutably.
        let elements: Vec<NodeId> = ast::get_elements_of_binding_or_assignment_pattern(
            &self.cx.nodes[pattern],
            self.cx.nodes,
        )
        .map(|s| s.to_vec())
        .unwrap_or_default();
        let num_elements = elements.len();
        let mut value = value;
        if num_elements != 1 {
            let reuse_identifier_expressions =
                !ast::is_declaration_binding_element(&self.cx.nodes[parent]) || num_elements != 0;
            value = Some(self.ensure_identifier(
                value.expect("binding pattern has no value"),
                reuse_identifier_expressions,
                location,
            ));
        }
        let mut binding_elements: Vec<NodeId> = Vec::new();
        let mut computed_temp_variables: Vec<NodeId> = Vec::new();
        for (i, &element) in elements.iter().enumerate() {
            if ast::get_rest_indicator_of_binding_or_assignment_element(element, self.cx.nodes)
                .is_none()
            {
                let property_name = ast::try_get_property_name_of_binding_or_assignment_element(
                    element,
                    self.cx.nodes,
                );
                let element_facts = self.cx.nodes[element].subtree_facts(self.cx.nodes);
                let target_facts =
                    ast::get_target_of_binding_or_assignment_element(element, self.cx.nodes)
                        .map(|t| self.cx.nodes[t].subtree_facts(self.cx.nodes))
                        .unwrap_or(SubtreeFacts::NONE);
                // Go evaluates `IsComputedPropertyName(propertyName)`
                // unconditionally here (nil would panic); property names are
                // always present for elements reaching this point.
                let is_computed = ast::is_computed_property_name(
                    &self.cx.nodes[property_name.expect("binding element has no property name")],
                );
                if self.level >= FlattenLevel::ObjectRest
                    && element_facts
                        & (SubtreeFacts::CONTAINS_REST_OR_SPREAD
                            | SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD)
                        == SubtreeFacts::NONE
                    && target_facts
                        & (SubtreeFacts::CONTAINS_REST_OR_SPREAD
                            | SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD)
                        == SubtreeFacts::NONE
                    && !is_computed
                {
                    let visited = self
                        .tx
                        .visitor()
                        .visit_node(self.cx, Some(element))
                        .expect("VisitNode removed a binding element");
                    binding_elements.push(visited);
                } else {
                    if !binding_elements.is_empty() {
                        let pattern_node = self.create_object_binding_or_assignment_pattern(
                            std::mem::take(&mut binding_elements),
                        );
                        self.emit_binding_or_assignment(
                            pattern_node,
                            value,
                            location,
                            Some(pattern),
                        );
                    }
                    let rhs_value = self.create_destructuring_property_access(value, property_name);
                    if is_computed {
                        let argument_expression = self.cx.nodes[rhs_value]
                            .as_element_access_expression()
                            .argument_expression
                            .expect("element access has no argument");
                        computed_temp_variables.push(argument_expression);
                    }
                    let element_loc = self.cx.nodes[element].loc;
                    self.flatten_binding_or_assignment_element(
                        element,
                        Some(rhs_value),
                        element_loc,
                        false,
                    );
                }
            } else if i == num_elements - 1 {
                if !binding_elements.is_empty() {
                    let pattern_node = self.create_object_binding_or_assignment_pattern(
                        std::mem::take(&mut binding_elements),
                    );
                    self.emit_binding_or_assignment(pattern_node, value, location, Some(pattern));
                }
                let pattern_loc = self.cx.nodes[pattern].loc;
                let rhs_value = self.tx.emit_context().borrow_mut().factory.new_rest_helper(
                    self.cx.nodes,
                    value.expect("rest helper has no value"),
                    &elements,
                    if computed_temp_variables.is_empty() {
                        None
                    } else {
                        Some(computed_temp_variables.as_slice())
                    },
                    pattern_loc,
                );
                let element_loc = self.cx.nodes[element].loc;
                self.flatten_binding_or_assignment_element(
                    element,
                    Some(rhs_value),
                    element_loc,
                    false,
                );
            }
        }
        if !binding_elements.is_empty() {
            let pattern_node = self.create_object_binding_or_assignment_pattern(binding_elements);
            self.emit_binding_or_assignment(pattern_node, value, location, Some(pattern));
        }
    }

    /// `(*flattener) flattenArrayBindingOrAssignmentPattern` — the
    /// `restIdElemPair` pairs are `(id, element)` tuples.
    fn flatten_array_binding_or_assignment_pattern(
        &mut self,
        parent: NodeId,
        pattern: NodeId,
        value: Option<NodeId>,
        location: TextRange,
    ) {
        // PORT: see the clone note on the object-pattern flatten.
        let elements: Vec<NodeId> = ast::get_elements_of_binding_or_assignment_pattern(
            &self.cx.nodes[pattern],
            self.cx.nodes,
        )
        .map(|s| s.to_vec())
        .unwrap_or_default();
        let num_elements = elements.len();
        let mut value = value;
        if (num_elements != 1 && (self.level < FlattenLevel::ObjectRest || num_elements == 0))
            || tsc_core::core::every(&elements, |e| {
                ast::is_omitted_expression(&self.cx.nodes[*e])
            })
        {
            let reuse_identifier_expressions =
                !ast::is_declaration_binding_element(&self.cx.nodes[parent]) || num_elements != 0;
            value = Some(self.ensure_identifier(
                value.expect("binding pattern has no value"),
                reuse_identifier_expressions,
                location,
            ));
        }
        let mut binding_elements: Vec<NodeId> = Vec::new();
        let mut rest_containing_elements: Vec<(NodeId, NodeId)> = Vec::new();
        for (i, &element) in elements.iter().enumerate() {
            if self.level >= FlattenLevel::ObjectRest {
                let element_facts = self.cx.nodes[element].subtree_facts(self.cx.nodes);
                if element_facts & SubtreeFacts::CONTAINS_OBJECT_REST_OR_SPREAD
                    != SubtreeFacts::NONE
                    || (self.has_transformed_prior_element
                        && !is_simple_binding_or_assignment_element(self.cx.nodes, element))
                {
                    self.has_transformed_prior_element = true;
                    let temp = self
                        .tx
                        .emit_context()
                        .borrow_mut()
                        .factory
                        .new_temp_variable(self.cx.nodes);
                    if self.hoist_temp_variables {
                        self.tx
                            .emit_context()
                            .borrow_mut()
                            .add_variable_declaration(self.cx.nodes, temp);
                    }
                    rest_containing_elements.push((temp, element));
                    let element = self.create_array_binding_or_assignment_element(temp);
                    binding_elements.push(element);
                } else {
                    binding_elements.push(element);
                }
            } else if ast::is_omitted_expression(&self.cx.nodes[element]) {
                continue;
            } else if ast::get_rest_indicator_of_binding_or_assignment_element(
                element,
                self.cx.nodes,
            )
            .is_none()
            {
                let argument_expression = self
                    .tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_numeric_literal(self.cx.nodes, &i.to_string(), ast::TokenFlags::NONE);
                let rhs_value = self
                    .tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_element_access_expression(
                        self.cx.nodes,
                        value,
                        None,
                        Some(argument_expression),
                        ast::NodeFlags::NONE,
                    );
                let element_loc = self.cx.nodes[element].loc;
                self.flatten_binding_or_assignment_element(
                    element,
                    Some(rhs_value),
                    element_loc,
                    false,
                );
            } else if i == num_elements - 1 {
                let rhs_value = self
                    .tx
                    .emit_context()
                    .borrow_mut()
                    .factory
                    .new_array_slice_call(
                        self.cx.nodes,
                        value.expect("array slice call has no value"),
                        i as i32,
                    );
                let element_loc = self.cx.nodes[element].loc;
                self.flatten_binding_or_assignment_element(
                    element,
                    Some(rhs_value),
                    element_loc,
                    false,
                );
            }
        }
        if !binding_elements.is_empty() {
            let pattern_node = self.create_array_binding_or_assignment_pattern(binding_elements);
            self.emit_binding_or_assignment(pattern_node, value, location, Some(pattern));
        }
        for (id, element) in rest_containing_elements {
            let element_loc = self.cx.nodes[element].loc;
            self.flatten_binding_or_assignment_element(element, Some(id), element_loc, false);
        }
    }
}

// --- Exported helper functions ---

/// `BindingOrAssignmentElementAssignsToName(element, name)` — checks if any
/// target in a binding/assignment pattern assigns to the given name.
pub fn binding_or_assignment_element_assigns_to_name(
    nodes: &[Node],
    element: NodeId,
    name: &str,
) -> bool {
    let Some(target) = ast::get_target_of_binding_or_assignment_element(element, nodes) else {
        return false;
    };
    if ast::is_binding_pattern(&nodes[target]) || ast::is_assignment_pattern(&nodes[target]) {
        binding_or_assignment_pattern_assigns_to_name(nodes, target, name)
    } else if ast::is_identifier(&nodes[target]) {
        nodes[target].text(nodes).as_ref() == name
    } else {
        false
    }
}

/// `bindingOrAssignmentPatternAssignsToName`.
fn binding_or_assignment_pattern_assigns_to_name(
    nodes: &[Node],
    pattern: NodeId,
    name: &str,
) -> bool {
    let Some(elements) = ast::get_elements_of_binding_or_assignment_pattern(&nodes[pattern], nodes)
    else {
        return false;
    };
    elements
        .iter()
        .any(|&element| binding_or_assignment_element_assigns_to_name(nodes, element, name))
}

/// `BindingOrAssignmentElementContainsNonLiteralComputedName(element)` —
/// checks if any element has a non-literal computed property name.
pub fn binding_or_assignment_element_contains_non_literal_computed_name(
    nodes: &[Node],
    element: NodeId,
) -> bool {
    if let Some(property_name) =
        ast::try_get_property_name_of_binding_or_assignment_element(element, nodes)
        && ast::is_computed_property_name(&nodes[property_name])
    {
        let expression = nodes[property_name]
            .expression()
            .expect("computed property name has no expression");
        if !ast::is_literal_expression(&nodes[expression]) {
            return true;
        }
    }
    let Some(target) = ast::get_target_of_binding_or_assignment_element(element, nodes) else {
        return false;
    };
    (ast::is_binding_pattern(&nodes[target]) || ast::is_assignment_pattern(&nodes[target]))
        && binding_or_assignment_pattern_contains_non_literal_computed_name(nodes, target)
}

/// `bindingOrAssignmentPatternContainsNonLiteralComputedName`.
fn binding_or_assignment_pattern_contains_non_literal_computed_name(
    nodes: &[Node],
    pattern: NodeId,
) -> bool {
    let Some(elements) = ast::get_elements_of_binding_or_assignment_pattern(&nodes[pattern], nodes)
    else {
        return false;
    };
    elements.iter().any(|&element| {
        binding_or_assignment_element_contains_non_literal_computed_name(nodes, element)
    })
}

/// `GetInitializerOfBindingOrAssignmentElement(bindingElement)` — returns the
/// initializer/default value of a binding or assignment element.
pub fn get_initializer_of_binding_or_assignment_element(
    nodes: &[Node],
    binding_element: Option<NodeId>,
) -> Option<NodeId> {
    let binding_element = binding_element?;
    if ast::is_declaration_binding_element(&nodes[binding_element]) {
        return nodes[binding_element].initializer();
    }
    if ast::is_property_assignment(&nodes[binding_element]) {
        let initializer = nodes[binding_element].initializer();
        if let Some(init) = initializer
            && ast::is_assignment_expression(&nodes[init], nodes, true)
        {
            return nodes[init].as_binary_expression().right;
        }
        return None;
    }
    if ast::is_shorthand_property_assignment(&nodes[binding_element]) {
        return nodes[binding_element]
            .as_shorthand_property_assignment()
            .object_assignment_initializer;
    }
    if ast::is_assignment_expression(&nodes[binding_element], nodes, true) {
        return nodes[binding_element].as_binary_expression().right;
    }
    if ast::is_spread_element(&nodes[binding_element]) {
        return get_initializer_of_binding_or_assignment_element(
            nodes,
            nodes[binding_element].expression(),
        );
    }
    None
}

/// `isObjectBindingOrAssignmentPattern(node)`.
fn is_object_binding_or_assignment_pattern(nodes: &[Node], node: Option<NodeId>) -> bool {
    node.is_some_and(|node| {
        matches!(
            nodes[node].kind,
            Kind::ObjectBindingPattern | Kind::ObjectLiteralExpression
        )
    })
}

/// `isArrayBindingOrAssignmentPattern(node)`.
fn is_array_binding_or_assignment_pattern(nodes: &[Node], node: Option<NodeId>) -> bool {
    node.is_some_and(|node| {
        matches!(
            nodes[node].kind,
            Kind::ArrayBindingPattern | Kind::ArrayLiteralExpression
        )
    })
}

/// `isSimpleBindingOrAssignmentElement(element)`.
fn is_simple_binding_or_assignment_element(nodes: &[Node], element: NodeId) -> bool {
    let Some(target) = ast::get_target_of_binding_or_assignment_element(element, nodes) else {
        return true;
    };
    if ast::is_omitted_expression(&nodes[target]) {
        return true;
    }
    if let Some(property_name) =
        ast::try_get_property_name_of_binding_or_assignment_element(element, nodes)
        && !ast::is_property_name_literal(&nodes[property_name])
    {
        return false;
    }
    if let Some(initializer) =
        get_initializer_of_binding_or_assignment_element(nodes, Some(element))
        && !is_simple_inlineable_expression(&nodes[initializer])
    {
        return false;
    }
    if ast::is_binding_pattern(&nodes[target]) || ast::is_assignment_pattern(&nodes[target]) {
        return tsc_core::core::every(
            ast::get_elements_of_binding_or_assignment_pattern(&nodes[target], nodes)
                .unwrap_or(&[]),
            |&element| is_simple_binding_or_assignment_element(nodes, element),
        );
    }
    ast::is_identifier(&nodes[target])
}
