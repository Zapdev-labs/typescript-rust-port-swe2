// Ported from tsc/internal/pseudochecker/lookup.go @ ec47d33c23e464a17cdf2475632cba629bee8763

// PORT: Go `*ast.Node` parameters/returns become `NodeId` (or `Option<NodeId>`
// where Go passes/returns nil). The node arena `nodes: &[Node]` resolves ids;
// methods that dereference `*ast.Symbol` (for `.Declarations`) additionally
// take the symbol arena `symbols: &[Symbol]`, which the binder owns. Go
// `slices.Index`/`slices.Backward` and `int` arithmetic are preserved so that
// `-1` "not found" and `lastRequired-1 == -1` behave identically.

use tsc_ast::ast::{Node, NodeList};
use tsc_ast::ast_generated::{
    is_arrow_function, is_block, is_call_expression, is_constructor_declaration,
    is_function_declaration, is_function_expression, is_get_accessor_declaration, is_identifier,
    is_jsx_element, is_jsx_expression, is_method_declaration, is_parameter_declaration,
    is_property_declaration, is_satisfies_expression, is_template_expression,
    is_type_predicate_node, is_variable_declaration,
};
use tsc_ast::functionflags::{FunctionFlags, get_function_flags};
use tsc_ast::ids::NodeId;
use tsc_ast::kind_generated::Kind;
use tsc_ast::modifierflags::ModifierFlags;
use tsc_ast::nodeflags::NodeFlags;
use tsc_ast::symbol::Symbol;
use tsc_ast::utilities::{
    AllAccessorDeclarations, JsDeclarationKind, find_ancestor, for_each_return_statement,
    get_all_accessor_declarations_for_declaration, get_assignment_declaration_kind, has_modifier,
    is_accessor, is_assertion_expression, is_const_assertion, is_const_type_reference,
    is_function_like, is_primitive_literal_value, is_var_const, is_variable_parameter_or_property,
    node_is_missing,
};
use tsc_core::core::count_where;
use tsc_debug as debug;

use crate::checker::PseudoChecker;
use crate::types::*;

impl PseudoChecker {
    /// `(ch *PseudoChecker) GetReturnTypeOfSignature`.
    pub fn get_return_type_of_signature(
        &self,
        signature_node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        match nodes[signature_node].kind {
            Kind::GetAccessor => self.get_type_of_accessor(signature_node, nodes, symbols),
            Kind::MethodDeclaration
            | Kind::FunctionDeclaration
            | Kind::Constructor
            | Kind::MethodSignature
            | Kind::CallSignature
            | Kind::ConstructSignature
            | Kind::SetAccessor
            | Kind::IndexSignature
            | Kind::FunctionType
            | Kind::ConstructorType
            | Kind::FunctionExpression
            | Kind::ArrowFunction
            | Kind::JSDocSignature => {
                self.create_return_from_signature(signature_node, nodes, symbols)
            }
            _ => debug::fail_bad_syntax_kind!(
                nodes[signature_node],
                "Node needs to be an inferrable node"
            ),
        }
    }

    /// `(ch *PseudoChecker) GetTypeOfAccessor`.
    pub fn get_type_of_accessor(
        &self,
        accessor: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        self.type_from_accessor(accessor, nodes, symbols)
    }

    /// `(ch *PseudoChecker) GetTypeOfExpression`.
    pub fn get_type_of_expression(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        self.type_from_expression(node, nodes, symbols)
    }

    /// `(ch *PseudoChecker) GetTypeOfDeclaration`.
    pub fn get_type_of_declaration(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        match nodes[node].kind {
            Kind::Parameter => self.type_from_parameter(node, nodes, symbols),
            Kind::VariableDeclaration => self.type_from_variable(node, nodes, symbols),
            Kind::PropertySignature | Kind::PropertyDeclaration | Kind::JSDocPropertyTag => {
                self.type_from_property(node, nodes, symbols)
            }
            Kind::BindingElement => new_pseudo_type_no_result(node),
            Kind::ExportAssignment => {
                // `node.AsExportAssignment().Expression` — nil derefs in Go if absent.
                let expression = nodes[node]
                    .as_export_assignment()
                    .expression
                    .expect("nil expression in ExportAssignment");
                self.type_from_expression(expression, nodes, symbols)
            }
            Kind::PropertyAccessExpression
            | Kind::ElementAccessExpression
            | Kind::BinaryExpression => self.type_from_expando_property(node, nodes),
            Kind::PropertyAssignment | Kind::ShorthandPropertyAssignment => {
                self.type_from_property_assignment(node, nodes, symbols)
            }
            Kind::CallExpression => {
                match get_assignment_declaration_kind(node, nodes) {
                    // TODO: How much of the checker's getTypeFromPropertyDescriptor is worth trying to emulate over ASTs?
                    JsDeclarationKind::ObjectDefinePropertyValue => {
                        // !!!
                    }
                    JsDeclarationKind::ObjectDefinePropertyExports => {
                        // !!!
                    }
                    _ => {}
                }
                new_pseudo_type_no_result(node)
            }
            _ => debug::fail_bad_syntax_kind!(nodes[node], "node needs to be an inferrable node"),
        }
    }

    /// `(ch *PseudoChecker) typeFromPropertyAssignment`.
    fn type_from_property_assignment(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        if let Some(annotation) = nodes[node].type_() {
            return new_pseudo_type_direct(annotation);
        }
        if nodes[node].kind == Kind::PropertyAssignment {
            if let Some(init) = nodes[node].initializer() {
                let expr = self.type_from_expression(init, nodes, symbols);
                if expr.kind() != PseudoTypeKind::Inferred
                    || !expr.as_pseudo_type_inferred().error_nodes.is_empty()
                {
                    return expr;
                }
                // fallback to NoResult if PseudoTypeKindInferred without error nodes
            }
        }
        new_pseudo_type_no_result(node)
    }

    /// `(ch *PseudoChecker) typeFromExpandoProperty`.
    ///
    /// This is _not_ redundant with the reparser; see how
    /// expandoFunctionSymbolProperty.ts and similar behaves.
    fn type_from_expando_property(&self, node: NodeId, nodes: &[Node]) -> PseudoTypeRef {
        if let Some(declared_type) = nodes[node].type_() {
            return new_pseudo_type_direct(declared_type);
        }
        // While `node` is an expression, as an expando, it should also always be a
        // declaration with a `.Symbol()` which requires declaration fallback handling
        new_pseudo_type_no_result(node)
    }

    /// `(ch *PseudoChecker) typeFromProperty`.
    fn type_from_property(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        if let Some(t) = nodes[node].type_() {
            return new_pseudo_type_direct(t);
        }
        if is_property_declaration(&nodes[node]) {
            if let Some(init) = nodes[node].initializer() {
                if !is_contextually_typed(node, nodes) {
                    // explicit fail on readonly template literals to allow for literal freshness in the future
                    if has_modifier(&nodes[node], ModifierFlags::READONLY)
                        && is_template_expression(&nodes[init])
                    {
                        return new_pseudo_type_no_result(node);
                    }
                    let expr = self.type_from_expression(init, nodes, symbols);
                    if expr.kind() != PseudoTypeKind::Inferred
                        || !expr.as_pseudo_type_inferred().error_nodes.is_empty()
                    {
                        let has_question_token = nodes[node]
                            .as_property_declaration()
                            .named_member_base
                            .postfix_token
                            .is_some_and(|t| nodes[t].kind == Kind::QuestionToken);
                        if expr.kind() != PseudoTypeKind::Direct && has_question_token {
                            // type comes from the initializer expression on a property with a `?` - add `| undefined` to the type
                            return add_undefined_if_definitely_required(expr, nodes);
                        }
                        return expr;
                    }
                    // fallback to NoResult if PseudoTypeKindInferred without error nodes
                }
            }
        }
        new_pseudo_type_no_result(node)
    }

    /// `(ch *PseudoChecker) typeFromVariable`.
    fn type_from_variable(
        &self,
        declaration: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        let decl = nodes[declaration].as_variable_declaration();
        if let Some(t) = decl.type_ {
            return new_pseudo_type_direct(t);
        }
        if let Some(init) = decl.initializer {
            if let Some(symbol) = decl.declaration_base.symbol {
                let declarations = &symbols[symbol.index()].declarations;
                if declarations.len() == 1
                    || count_where(declarations, |d| is_variable_declaration(&nodes[*d])) == 1
                {
                    // TODO: also should bail on expando declarations; reuse syntactic expando check used in declaration emit
                    if !is_contextually_typed(declaration, nodes) {
                        // TODO: Strada forces an inference fallback on `const` variables with template expression initializers, to leave space for template literal freshness in the future
                        if is_var_const(declaration, nodes) && is_template_expression(&nodes[init])
                        {
                            return new_pseudo_type_no_result(declaration);
                        }
                        let expr = self.type_from_expression(init, nodes, symbols);
                        if expr.kind() != PseudoTypeKind::Inferred
                            || !expr.as_pseudo_type_inferred().error_nodes.is_empty()
                        {
                            return expr;
                        }
                        // fallback to NoResult if PseudoTypeKindInferred without error nodes
                    }
                }
            }
        }
        new_pseudo_type_no_result(declaration)
    }

    /// `(ch *PseudoChecker) typeFromAccessor`.
    fn type_from_accessor(
        &self,
        accessor: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        // `accessor.DeclarationData().Symbol.Declarations` — Go nil-panics on a
        // symbol-less accessor.
        let symbol = nodes[accessor]
            .declaration_data()
            .and_then(|d| d.symbol)
            .expect("nil symbol on accessor in typeFromAccessor");
        let accessor_declarations = get_all_accessor_declarations_for_declaration(
            accessor,
            &symbols[symbol.index()].declarations,
            nodes,
        );
        let accessor_type = self.get_type_annotation_from_all_accessor_declarations(
            accessor,
            &accessor_declarations,
            nodes,
        );
        if let Some(accessor_type) = accessor_type {
            if !is_type_predicate_node(&nodes[accessor_type]) {
                return new_pseudo_type_direct(accessor_type);
            }
        }
        if let Some(get_accessor) = accessor_declarations.get_accessor {
            let res = self.create_return_from_signature(get_accessor, nodes, symbols);
            if let PseudoType::Inferred(inferred) = &*res {
                if inferred.error_nodes.is_empty() {
                    let mut error_nodes = vec![get_accessor];
                    if let Some(set_accessor) = accessor_declarations.set_accessor {
                        error_nodes.push(set_accessor);
                    }
                    // Move error up to the accessor
                    return new_pseudo_type_inferred_with_errors(
                        inferred.expression,
                        inferred.is_signature_return,
                        error_nodes,
                    );
                }
            }
            return res;
        }
        new_pseudo_type_no_result(accessor)
    }

    /// `(ch *PseudoChecker) getTypeAnnotationFromAllAccessorDeclarations`.
    fn get_type_annotation_from_all_accessor_declarations(
        &self,
        node: NodeId,
        accessors: &AllAccessorDeclarations,
        nodes: &[Node],
    ) -> Option<NodeId> {
        let mut accessor_type = self.get_type_annotation_from_accessor(Some(node), nodes);
        if accessor_type.is_none() && node != accessors.first_accessor {
            accessor_type =
                self.get_type_annotation_from_accessor(Some(accessors.first_accessor), nodes);
        }
        if accessor_type.is_none()
            && accessors
                .second_accessor
                .is_some_and(|second| node != second)
        {
            accessor_type =
                self.get_type_annotation_from_accessor(accessors.second_accessor, nodes);
        }
        accessor_type
    }

    /// `(ch *PseudoChecker) getTypeAnnotationFromAccessor`.
    fn get_type_annotation_from_accessor(
        &self,
        node: Option<NodeId>,
        nodes: &[Node],
    ) -> Option<NodeId> {
        let node = node?;
        // !!! TODO: support ripping return type off of .FullSignature
        if nodes[node].kind == Kind::GetAccessor {
            return nodes[node]
                .as_get_accessor_declaration()
                .accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .type_;
        }
        let set = nodes[node].as_set_accessor_declaration();
        let parameters = set
            .accessor_declaration_base
            .function_like_with_body_base
            .function_like_base
            .parameters
            .as_ref()?;
        let &p = parameters.nodes().first()?;
        if !is_parameter_declaration(&nodes[p]) {
            return None;
        }
        nodes[p].as_parameter_declaration().type_
    }

    /// `(ch *PseudoChecker) createReturnFromSignature` — does not return
    /// `nil`, returns a `NoResult` pseudotype instead.
    fn create_return_from_signature(
        &self,
        fn_: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        if is_function_like(Some(fn_), nodes) {
            // !!! TODO: support ripping return type off of .FullSignature
            if let Some(r) = nodes[fn_].function_like_data().and_then(|d| d.type_) {
                return new_pseudo_type_direct(r);
            }
        }
        if is_value_signature_declaration(&nodes[fn_]) {
            return self.type_from_single_return_expression(fn_, nodes, symbols);
        }
        new_pseudo_type_no_result(fn_)
    }

    /// `(ch *PseudoChecker) typeFromSingleReturnExpression`.
    fn type_from_single_return_expression(
        &self,
        fn_: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        let mut candidate_expr: Option<NodeId> = None;
        if !node_is_missing(nodes[fn_].body(), nodes) {
            let flags = get_function_flags(Some(&nodes[fn_]));
            if flags.intersects(FunctionFlags::ASYNC_GENERATOR) {
                return new_pseudo_type_inferred(fn_, true);
            }

            // `node_is_missing` returned false, so `body` is `Some`.
            let body = nodes[fn_].body().expect("non-missing body was None");
            if is_block(&nodes[body]) {
                for_each_return_statement(nodes, body, &mut |stmt| {
                    if nodes[stmt].parent != Some(body) {
                        // Why bail on nested return statements?
                        candidate_expr = None;
                        return true;
                    }
                    if candidate_expr.is_none() {
                        candidate_expr = nodes[stmt].as_return_statement().expression;
                    } else {
                        candidate_expr = None;
                        return true;
                    }
                    false
                });
            } else {
                candidate_expr = Some(body);
            }
        }
        if let Some(candidate_expr) = candidate_expr {
            if is_contextually_typed(candidate_expr, nodes) {
                let mut t: Option<NodeId> = None;
                if nodes[candidate_expr].kind == Kind::TypeAssertionExpression {
                    t = nodes[candidate_expr].as_type_assertion().type_;
                } else if nodes[candidate_expr].kind == Kind::AsExpression {
                    t = nodes[candidate_expr].as_as_expression().type_;
                }
                if let Some(t) = t {
                    if !is_const_type_reference(&nodes[t], nodes) {
                        return new_pseudo_type_direct(t);
                    }
                }
            } else {
                return self.type_from_expression(candidate_expr, nodes, symbols);
            }
        }
        new_pseudo_type_inferred(fn_, true)
    }

    /// `(ch *PseudoChecker) typeFromExpression` — this is basically
    /// `checkExpression` for pseudotypes.
    fn type_from_expression(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        match nodes[node].kind {
            Kind::OmittedExpression => pseudo_type_undefined(),
            Kind::ParenthesizedExpression => {
                // assertions transformed on reparse, just unwrap
                let expression = nodes[node]
                    .as_parenthesized_expression()
                    .expression
                    .expect("nil expression in ParenthesizedExpression");
                self.type_from_expression(expression, nodes, symbols)
            }
            Kind::Identifier => {
                // !!! TODO: in strada, this uses symbol information to ensure `node` refers to the global `undefined` symbol instead
                // we should probably import `resolveName` and use it here to check for the same; but we have to setup some barebones pseudoglobals for that to work!
                if nodes[node].as_identifier().text.as_ref() == "undefined" {
                    return pseudo_type_undefined();
                }
                new_pseudo_type_inferred(node, false)
            }
            Kind::NullKeyword => pseudo_type_null(),
            Kind::ArrowFunction | Kind::FunctionExpression => {
                self.type_from_function_like_expression(node, nodes, symbols)
            }
            Kind::TypeAssertionExpression => {
                let assertion = nodes[node].as_type_assertion();
                self.type_from_type_assertion(
                    assertion
                        .expression
                        .expect("nil expression in TypeAssertion"),
                    assertion.type_.expect("nil type in TypeAssertion"),
                    nodes,
                    symbols,
                )
            }
            Kind::AsExpression => {
                let as_expr = nodes[node].as_as_expression();
                self.type_from_type_assertion(
                    as_expr.expression.expect("nil expression in AsExpression"),
                    as_expr.type_.expect("nil type in AsExpression"),
                    nodes,
                    symbols,
                )
            }
            Kind::PrefixUnaryExpression => {
                if is_primitive_literal_value(&nodes[node], true, nodes) {
                    return self.type_from_primitive_literal_prefix(node, nodes);
                }
                new_pseudo_type_inferred(node, false)
            }
            Kind::ArrayLiteralExpression => self.type_from_array_literal(node, nodes, symbols),
            Kind::ObjectLiteralExpression => self.type_from_object_literal(node, nodes, symbols),
            Kind::ClassExpression => {
                // No possible annotation/directly mappable syntax
                new_pseudo_type_inferred_with_errors(node, false, vec![node])
            }
            Kind::TemplateExpression => {
                // templateLitWithHoles as const, not supported
                if is_in_const_context(node, nodes) {
                    return new_pseudo_type_inferred(node, false);
                }
                new_pseudo_type_maybe_const_location(
                    node,
                    new_pseudo_type_inferred(node, false),
                    pseudo_type_string(),
                )
            }
            Kind::NumericLiteral => new_pseudo_type_maybe_const_location(
                node,
                new_pseudo_type_numeric_literal(node),
                pseudo_type_number(),
            ),
            Kind::NoSubstitutionTemplateLiteral | Kind::StringLiteral => {
                new_pseudo_type_maybe_const_location(
                    node,
                    new_pseudo_type_string_literal(node),
                    pseudo_type_string(),
                )
            }
            Kind::BigIntLiteral => new_pseudo_type_maybe_const_location(
                node,
                new_pseudo_type_big_int_literal(node),
                pseudo_type_big_int(),
            ),
            Kind::TrueKeyword => new_pseudo_type_maybe_const_location(
                node,
                pseudo_type_true(),
                pseudo_type_boolean(),
            ),
            Kind::FalseKeyword => new_pseudo_type_maybe_const_location(
                node,
                pseudo_type_false(),
                pseudo_type_boolean(),
            ),
            _ => new_pseudo_type_inferred(node, false),
        }
    }

    /// `(ch *PseudoChecker) typeFromObjectLiteral`.
    fn type_from_object_literal(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        let error_nodes = self.can_get_type_from_object_literal(node, nodes);
        if !error_nodes.is_empty() {
            return new_pseudo_type_inferred_with_errors(node, false, error_nodes);
        }
        // we are in a const context producing an object literal type, there are no shorthand or spread assignments
        let properties = nodes[node]
            .as_object_literal_expression()
            .properties
            .as_ref();
        if properties.is_none_or(|p| p.is_empty()) {
            return new_pseudo_type_object_literal(Vec::new());
        }
        let properties = properties.expect("checked above");
        let mut results: Vec<PseudoObjectElement> = Vec::with_capacity(properties.len());
        for &e in properties.nodes() {
            match nodes[e].kind {
                Kind::MethodDeclaration => {
                    let optional = nodes[e]
                        .as_method_declaration()
                        .named_member_base
                        .postfix_token
                        .is_some_and(|t| nodes[t].kind == Kind::QuestionToken);
                    if let Some(full_signature) =
                        nodes[e].function_like_data().and_then(|d| d.full_signature)
                    {
                        results.push(new_pseudo_property_assignment(
                            false,
                            nodes[e].name(),
                            optional,
                            new_pseudo_type_direct(full_signature),
                        ));
                    } else {
                        results.push(new_pseudo_object_method(
                            e,
                            nodes[e].name(),
                            optional,
                            self.clone_type_parameters(nodes[e].type_parameter_list(), nodes),
                            self.clone_parameters(nodes[e].parameter_list(), nodes, symbols),
                            self.create_return_from_signature(e, nodes, symbols),
                        ));
                    }
                }
                Kind::PropertyAssignment => {
                    results.push(new_pseudo_property_assignment(
                        false,
                        nodes[e].name(),
                        nodes[e]
                            .as_property_assignment()
                            .named_member_base
                            .postfix_token
                            .is_some_and(|t| nodes[t].kind == Kind::QuestionToken),
                        self.type_from_expression(
                            nodes[e]
                                .initializer()
                                .expect("nil initializer in PropertyAssignment"),
                            nodes,
                            symbols,
                        ),
                    ));
                }
                Kind::SetAccessor | Kind::GetAccessor => {
                    if let Some(member) =
                        self.get_accessor_member(e, nodes[e].name(), nodes, symbols)
                    {
                        results.push(member);
                    }
                }
                _ => {}
            }
        }
        new_pseudo_type_object_literal(results)
    }

    /// `(ch *PseudoChecker) getAccessorMember` — roughly analogous to
    /// typeFromObjectLiteralAccessor in strada.
    fn get_accessor_member(
        &self,
        accessor: NodeId,
        name: Option<NodeId>,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> Option<PseudoObjectElement> {
        // TODO: node preservation for late-bound accessor pairs?
        // `accessor.Symbol().Declarations` — Go nil-panics without a symbol.
        let symbol = nodes[accessor]
            .symbol()
            .expect("nil symbol on accessor in getAccessorMember");
        let all_accessors = get_all_accessor_declarations_for_declaration(
            accessor,
            &symbols[symbol.index()].declarations,
            nodes,
        );

        // TODO: handle pseudo-annotations from get accessor return positions?
        let both_accessors_annotated = all_accessors.get_accessor.is_some_and(|get| {
            nodes[get]
                .function_like_data()
                .and_then(|d| d.type_)
                .is_some()
        }) && all_accessors.set_accessor.is_some_and(|set| {
            nodes[set].parameter_list().is_some_and(|params| {
                params
                    .nodes()
                    .first()
                    .is_some_and(|&p| nodes[p].as_parameter_declaration().type_.is_some())
            })
        });
        if both_accessors_annotated {
            // We have possible types for both accessors, we can't know if they are the same type so we keep both accessors
            if is_get_accessor_declaration(&nodes[accessor]) {
                return Some(new_pseudo_get_accessor(
                    accessor,
                    name,
                    false,
                    self.type_from_accessor(accessor, nodes, symbols),
                ));
            }
            return Some(new_pseudo_set_accessor(
                accessor,
                name,
                false,
                self.clone_parameters(nodes[accessor].parameter_list(), nodes, symbols)
                    .into_iter()
                    .next()
                    .expect("empty parameter list on set accessor"),
            ));
        }

        if accessor == all_accessors.first_accessor {
            // only one annotated accessor; output a property - `readonly` for a single `get` accessor
            let accessor_type = self.type_from_accessor(accessor, nodes, symbols);
            let readonly = is_get_accessor_declaration(&nodes[accessor])
                && all_accessors.second_accessor.is_none();
            return Some(new_pseudo_property_assignment(
                readonly,
                name,
                false,
                accessor_type,
            ));
        }
        None
    }

    /// `(ch *PseudoChecker) canGetTypeFromObjectLiteral` — checks whether an
    /// object literal can be typed by the pseudochecker.
    ///
    /// Returns an empty `Vec` if the object can be typed, or the error nodes
    /// (shorthand/spread properties, non-literal computed names) that prevent
    /// typing.
    fn can_get_type_from_object_literal(&self, node: NodeId, nodes: &[Node]) -> Vec<NodeId> {
        let Some(properties) = nodes[node]
            .as_object_literal_expression()
            .properties
            .as_ref()
        else {
            return Vec::new(); // empty object, ok
        };
        let mut error_nodes: Vec<NodeId> = Vec::new();
        for &e in properties.nodes() {
            if nodes[e].flags.intersects(NodeFlags::THIS_NODE_HAS_ERROR) {
                error_nodes.push(e);
                continue;
            }
            if nodes[e].kind == Kind::ShorthandPropertyAssignment
                || nodes[e].kind == Kind::SpreadAssignment
            {
                error_nodes.push(e);
                continue;
            }
            // `e.Name()` — Go nil-panics on a nameless element here.
            let name = nodes[e].name().expect("nil name on object literal element");
            if nodes[name].flags.intersects(NodeFlags::THIS_NODE_HAS_ERROR) {
                error_nodes.push(name);
                continue;
            }
            if nodes[name].kind == Kind::PrivateIdentifier {
                error_nodes.push(e);
                continue;
            }
            if nodes[name].kind == Kind::ComputedPropertyName {
                let expression = nodes[name]
                    .expression()
                    .expect("nil expression in ComputedPropertyName");
                if !is_primitive_literal_value(&nodes[expression], false, nodes) {
                    error_nodes.push(name);
                }
            }
        }
        error_nodes
    }

    /// `(ch *PseudoChecker) typeFromArrayLiteral`.
    fn type_from_array_literal(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        let error_nodes = self.can_get_type_from_array_literal(node, nodes);
        if !error_nodes.is_empty() {
            return new_pseudo_type_inferred_with_errors(node, false, error_nodes);
        }
        if is_in_const_context(node, nodes) && is_contextually_typed(node, nodes) {
            // expr in an as const cast with a contextual type has variable readonly state, bail
            return new_pseudo_type_inferred(node, false);
        }
        // we are in a const context producing a tuple type, there are no spread elements
        let elements = nodes[node]
            .as_array_literal_expression()
            .elements
            .as_ref()
            .map(|l| l.nodes())
            .unwrap_or(&[]);
        let mut results: Vec<PseudoTypeRef> = Vec::with_capacity(elements.len());
        for &e in elements {
            results.push(self.type_from_expression(e, nodes, symbols));
        }
        new_pseudo_type_tuple(results)
    }

    /// `(ch *PseudoChecker) canGetTypeFromArrayLiteral` — checks whether an
    /// array literal can be typed by the pseudochecker.
    ///
    /// Returns an empty `Vec` if the array can be typed, or the error nodes
    /// that prevent typing. For non-const arrays, the error node is the array
    /// expression itself. For const arrays with spreads, the error node is the
    /// spread element.
    fn can_get_type_from_array_literal(&self, node: NodeId, nodes: &[Node]) -> Vec<NodeId> {
        if !is_in_const_context(node, nodes) {
            return vec![node];
        }
        if let Some(elements) = nodes[node].as_array_literal_expression().elements.as_ref() {
            for &e in elements.nodes() {
                if nodes[e].kind == Kind::SpreadElement {
                    return vec![e];
                }
            }
        }
        Vec::new()
    }

    /// `(ch *PseudoChecker) typeFromPrimitiveLiteralPrefix`.
    fn type_from_primitive_literal_prefix(&self, node_id: NodeId, nodes: &[Node]) -> PseudoTypeRef {
        let node = nodes[node_id].as_prefix_unary_expression();
        let mut expr = node_id;
        if node.operator == Kind::PlusToken {
            expr = node.operand.expect("nil operand in PrefixUnaryExpression");
        }
        let inner = node.operand.expect("nil operand in PrefixUnaryExpression");
        match nodes[inner].kind {
            Kind::BigIntLiteral => new_pseudo_type_maybe_const_location(
                node_id,
                new_pseudo_type_big_int_literal(expr),
                pseudo_type_big_int(),
            ),
            Kind::NumericLiteral => new_pseudo_type_maybe_const_location(
                node_id,
                new_pseudo_type_numeric_literal(expr),
                pseudo_type_number(),
            ),
            _ => debug::fail_bad_syntax_kind!(nodes[inner]),
        }
    }

    /// `(ch *PseudoChecker) typeFromTypeAssertion`.
    fn type_from_type_assertion(
        &self,
        expression: NodeId,
        type_node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        if is_const_type_reference(&nodes[type_node], nodes) {
            return self.type_from_expression(expression, nodes, symbols);
        }
        new_pseudo_type_direct(type_node)
    }

    /// `(ch *PseudoChecker) typeFromFunctionLikeExpression`.
    fn type_from_function_like_expression(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        let data = nodes[node]
            .function_like_data()
            .expect("nil FunctionLikeData in typeFromFunctionLikeExpression");
        if let Some(full_signature) = data.full_signature {
            return new_pseudo_type_direct(full_signature);
        }
        let return_type = self.create_return_from_signature(node, nodes, symbols);
        let type_parameters = self.clone_type_parameters(data.type_parameters.as_ref(), nodes);
        let parameters = self.clone_parameters(data.parameters.as_ref(), nodes, symbols);
        new_pseudo_type_single_call_signature(node, parameters, type_parameters, return_type)
    }

    /// `(ch *PseudoChecker) cloneTypeParameters` — returns the type parameter
    /// declaration node ids (`[]*ast.TypeParameterDeclaration` in Go).
    fn clone_type_parameters(&self, nodes_list: Option<&NodeList>, nodes: &[Node]) -> Vec<NodeId> {
        let Some(nodes_list) = nodes_list else {
            return Vec::new();
        };
        let mut result = Vec::with_capacity(nodes_list.len());
        for &e in nodes_list.nodes() {
            // `e.AsTypeParameterDeclaration()` — asserts the kind, like Go.
            nodes[e].as_type_parameter_declaration();
            result.push(e);
        }
        result
    }

    /// `(ch *PseudoChecker) typeFromParameter`.
    fn type_from_parameter(
        &self,
        node: NodeId,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        // `node.Parent` — a parameter always has a function-like parent; Go
        // nil-panics otherwise.
        let parent = nodes[node].parent.expect("nil parent in typeFromParameter");
        if nodes[parent].kind == Kind::SetAccessor {
            return self.get_type_of_accessor(parent, nodes, symbols);
        }
        let p = nodes[node].as_parameter_declaration();
        // Fast path: no initializer means we never need parameter position info.
        if p.initializer.is_none() {
            if let Some(t) = p.type_ {
                return new_pseudo_type_direct(t);
            }
            return new_pseudo_type_no_result(node);
        }
        let params = nodes[parent]
            .parameters()
            .expect("nil ParameterList in typeFromParameter");
        let self_idx = params
            .iter()
            .position(|&id| id == node)
            .map_or(-1, |i| i as i32);
        let last_required = last_required_param_index(params, nodes);
        self.type_from_parameter_worker(node, self_idx, last_required, nodes, symbols)
    }

    /// `(ch *PseudoChecker) typeFromParameterWorker`.
    fn type_from_parameter_worker(
        &self,
        node: NodeId,
        self_idx: i32,
        last_required: i32,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> PseudoTypeRef {
        let parent = nodes[node]
            .parent
            .expect("nil parent in typeFromParameterWorker");
        if nodes[parent].kind == Kind::SetAccessor {
            return self.get_type_of_accessor(parent, nodes, symbols);
        }
        let has_required_after = self_idx < last_required - 1;
        let p = nodes[node].as_parameter_declaration();
        if let Some(declared_type) = p.type_ {
            let result = new_pseudo_type_direct(declared_type);
            // When the parameter has an initializer and strict null checks are enabled,
            // check if `| undefined` needs to be added because there are required parameters after this one.
            // This mirrors the checker's getTypeOfParameter which adds optionality for initialized parameters.
            if self.strict_null_checks && p.initializer.is_some() && has_required_after {
                return add_undefined_if_definitely_required(result, nodes);
            }
            return result;
        }
        if p.initializer.is_some()
            && p.name.is_some_and(|name| is_identifier(&nodes[name]))
            && !is_contextually_typed(node, nodes)
        {
            let initializer = p.initializer.expect("checked above");
            let mut expr = self.type_from_expression(initializer, nodes, symbols);
            let move_error_up =
                matches!(&*expr, PseudoType::Inferred(i) if i.error_nodes.is_empty());
            if move_error_up {
                // Move error up to the parameter
                let expression = expr.as_pseudo_type_inferred().expression;
                expr = new_pseudo_type_inferred_with_errors(expression, false, vec![node]);
            }
            if !self.strict_null_checks {
                return expr;
            }
            if !has_required_after {
                return expr;
            }
            // if there is a non-optional parameter after this one, a `| undefined` will need to explicitly be emitted on this parameter, if it's not already there
            return add_undefined_if_definitely_required(expr, nodes);
        }
        // TODO: In strada, the ID checker doesn't infer a parameter type from binding pattern names, but the real checker _does_!
        // This means ID won't let you write, say, `({elem}) => false` without an annotation, even though it's trivially of type
        // `(p0: {elem: any}) => boolean` and error-free under `noImplicitAny: false`!
        // That limitation is retained here.
        new_pseudo_type_no_result(node)
    }

    /// `(ch *PseudoChecker) cloneParameters`.
    fn clone_parameters(
        &self,
        nodes_list: Option<&NodeList>,
        nodes: &[Node],
        symbols: &[Symbol],
    ) -> Vec<PseudoParameter> {
        let Some(nodes_list) = nodes_list else {
            return Vec::new();
        };
        if nodes_list.is_empty() {
            return Vec::new();
        }
        let last_required = last_required_param_index(nodes_list.nodes(), nodes);
        let mut result = Vec::with_capacity(nodes_list.len());
        for (i, &e) in nodes_list.nodes().iter().enumerate() {
            let p = nodes[e].as_parameter_declaration();
            let mut optional = p.question_token.is_some();
            if !optional && p.initializer.is_some() {
                // A parameter with an initializer is optional only if all subsequent
                // parameters are also optional/have initializers/are rest parameters.
                // This matches the checker's isOptionalParameter semantics.
                optional = i as i32 >= last_required - 1;
            }
            result.push(new_pseudo_parameter(
                p.dot_dot_dot_token.is_some(),
                nodes[e].name(),
                optional,
                self.type_from_parameter_worker(e, i as i32, last_required, nodes, symbols),
            ));
        }
        result
    }
}

/// `isValueSignatureDeclaration`.
fn is_value_signature_declaration(node: &Node) -> bool {
    is_function_expression(node)
        || is_arrow_function(node)
        || is_method_declaration(node)
        || is_accessor(node)
        || is_function_declaration(node)
        || is_constructor_declaration(node)
}

/// `isConstContextPropagatingKind` — see `isConstContext` in `checker.go`;
/// this is basically any node kind mentioned in that.
fn is_const_context_propagating_kind(kind: Kind) -> bool {
    matches!(
        kind,
        Kind::ArrayLiteralExpression
            | Kind::ObjectLiteralExpression
            | Kind::ParenthesizedExpression
            | Kind::SpreadElement
            | Kind::PropertyAssignment
            | Kind::ShorthandPropertyAssignment
            | Kind::TemplateSpan
            | Kind::PrefixUnaryExpression
    )
}

/// `IsInConstContext` traverses up the parent chain to determine if the node
/// is within a const context without needing any persistent traversal scope
/// tracking (which could be unreliable in the presence of `typeof` queries
/// anyway!)
pub fn is_in_const_context(node: NodeId, nodes: &[Node]) -> bool {
    // An expression is in a const context if an ancestor is a const type maybeAssertion expression
    let maybe_assertion = find_ancestor(nodes[node].parent, nodes, &mut |n, _| {
        // stop traversing at assertions or anything not an array/object literal, since only those create or transfer const-ness
        is_assertion_expression(n) || !is_const_context_propagating_kind(n.kind)
    });
    // PORT: Go's `IsConstAssertion(nil)` on a nil `maybeAssertion` would nil-
    // panic; an unbound node simply isn't in a const context here.
    maybe_assertion.is_some_and(|id| is_const_assertion(&nodes[id], nodes))
}

/// `isUndefinedPseudoType`.
fn is_undefined_pseudo_type(t: &PseudoType) -> bool {
    t.kind() == PseudoTypeKind::Undefined
        || (t.kind() == PseudoTypeKind::MaybeConstLocation
            && is_undefined_pseudo_type(&t.as_pseudo_type_maybe_const_location().const_type))
}

/// `typeNodeCouldReferToUndefined`.
fn type_node_could_refer_to_undefined(mut node: NodeId, nodes: &[Node]) -> bool {
    while nodes[node].kind == Kind::ParenthesizedType {
        node = nodes[node]
            .as_parenthesized_type_node()
            .type_
            .expect("nil type in ParenthesizedTypeNode");
    }
    match nodes[node].kind {
        // these types require symbolic/type resolution to know if they definitely do or do not refer to `undefined`, so might (or definitely do)
        Kind::TypeReference
        | Kind::IndexedAccessType
        | Kind::TypeQuery
        | Kind::OptionalType
        | Kind::RestType
        | Kind::ImportType => true,
        Kind::IntersectionType => {
            // TODO: why is this not `core.Every`? strada treated unions and intersections the same, but logically every intersection member needs to contain a possible `undefined`
            // for the result type to contain `undefined`. Likely a bug persisting from strada.
            nodes[node]
                .as_intersection_type_node()
                .union_or_intersection_type_node_base
                .types
                .as_ref()
                .is_some_and(|types| {
                    types
                        .nodes()
                        .iter()
                        .any(|&t| type_node_could_refer_to_undefined(t, nodes))
                })
        }
        Kind::UnionType => nodes[node]
            .as_union_type_node()
            .union_or_intersection_type_node_base
            .types
            .as_ref()
            .is_some_and(|types| {
                types
                    .nodes()
                    .iter()
                    .any(|&t| type_node_could_refer_to_undefined(t, nodes))
            }),
        // suspect - should be treated as a union of both branches instead, likely a bug persisted from strada
        Kind::ConditionalType => true,
        // suspect - always refers to a subset of `string | number | symbol` for `keyof` or `symbol` for `unique`
        Kind::TypeOperator => true,
        // suspect - always refers to `never` or `boolean`, depending on kind - considered possibly-`undefined` referencing for strada compat
        Kind::TypePredicate => true,
        Kind::UndefinedKeyword => true,
        // all other keywords, literal types, function-y types, array/tuple types, type literals, template types, this types
        _ => false,
    }
}

/// `CouldAlreadyReferToUndefinedType` — see this as the inverse of
/// `canAddUndefined` in `expressionToTypeNode` in strada.
pub fn could_already_refer_to_undefined_type(t: &PseudoType, nodes: &[Node]) -> bool {
    if t.kind() == PseudoTypeKind::NoResult
        || t.kind() == PseudoTypeKind::Inferred
        || is_undefined_pseudo_type(t)
    {
        return true;
    }
    if t.kind() == PseudoTypeKind::MaybeConstLocation {
        let mc = t.as_pseudo_type_maybe_const_location();
        // if we're even asking this question, it's not a `const` location
        return could_already_refer_to_undefined_type(&mc.regular_type, nodes);
    }
    if t.kind() == PseudoTypeKind::Direct {
        // inspect the direct type node
        let node = t.as_pseudo_type_direct().type_node;
        return type_node_could_refer_to_undefined(node, nodes);
    }
    if t.kind() == PseudoTypeKind::Union {
        return t
            .as_pseudo_type_union()
            .types
            .iter()
            .any(|ty| could_already_refer_to_undefined_type(ty, nodes));
    }
    false
}

/// `isOptionalInitializedOrRestParameter`.
fn is_optional_initialized_or_rest_parameter(node: &Node) -> bool {
    let p = node.as_parameter_declaration();
    p.dot_dot_dot_token.is_some() || p.initializer.is_some() || p.question_token.is_some()
}

/// `lastRequiredParamIndex` returns the index just past the last required
/// parameter in the list. A parameter is "required" if it has no question
/// token, no initializer, and no rest token. This is computed in a single
/// reverse pass so callers can determine "has required parameter after index
/// i" with `i+1 < lastRequired` (equivalently, `i < lastRequired-1`) in O(1).
fn last_required_param_index(params: &[NodeId], nodes: &[Node]) -> i32 {
    for (i, &param) in params.iter().enumerate().rev() {
        if !is_optional_initialized_or_rest_parameter(&nodes[param]) {
            return i as i32 + 1;
        }
    }
    0
}

/// `addUndefinedIfDefinitelyRequired`.
fn add_undefined_if_definitely_required(expr: PseudoTypeRef, nodes: &[Node]) -> PseudoTypeRef {
    // If `expr` doesn't already contain `| undefined` or a direct/inferred type that may contain `undefined`, add `| undefined`
    // in Strada, this reached into the checker to see if `undefined` was necessary, using `isRequiredOptionalParameter` from the emit resolver,
    // but that's not required on top of the syntactic checks to get the same behavior. (If we get the type wrong, it'll mismatch later and be discarded
    // for an inference error since corsa actually validates that pseudotypes semantically match the inferred type the checker produces)
    if could_already_refer_to_undefined_type(&expr, nodes) {
        // will just error later, more like than not, unless the `undefined` is explicit in the pseudo
        return expr;
    }
    // Explicitly add an `| undefined`
    new_pseudo_type_union(vec![expr, pseudo_type_undefined()])
}

/// `isContextuallyTyped`.
fn is_contextually_typed(node: NodeId, nodes: &[Node]) -> bool {
    find_ancestor(nodes[node].parent, nodes, &mut |n, nodes| {
        // Functions calls or parent type annotations (but not the return type of a function expression) may impact the inferred type and local inference is unreliable
        if is_call_expression(n) {
            return true;
        }
        if is_satisfies_expression(n) {
            return true;
        }
        if (is_variable_parameter_or_property(n) || is_assertion_expression(n))
            && n.type_().is_some()
            && !is_const_assertion(n, nodes)
        {
            return true;
        }
        is_jsx_element(n) || is_jsx_expression(n)
    })
    .is_some()
}
