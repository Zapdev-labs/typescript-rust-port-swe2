// Ported from tsc/internal/transformers/tstransforms/legacydecorators.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The legacy (TypeScript "experimental") decorators transform — rewrites
// decorated class declarations into a `let` binding plus `__decorate` /
// `__param` helper calls, tracks `classAliases` for classes with internal
// self-references, and elides decorator nodes from class members.
//
// PORT notes:
//   - `classAliases` is `RefCell<Option<FxHashMap<NodeId, NodeId>>>` —
//     `None` mirrors Go's nil map outside of a `SourceFile` visit (Go
//     re-creates it on each `KindSourceFile` and resets it to nil after).
//   - `enclosingClasses` is `RefCell<Vec<NodeId>>` (Go's `[]*ast.ClassDeclaration`
//     stack — push/pop around the decorated-class transform).
//   - `referenceResolver` is `Option<Rc<RefCell<dyn ReferenceResolver>>>` and
//     `symbols` is `opts.symbols` (`&'a RefCell<Vec<Symbol>>`, the binder
//     symbol arena) — the same convention as `estransforms/classfields.rs`.
//     `GetReferencedValueDeclaration` on a Go nil interface would panic; the
//     port `.expect()`s at the same call sites.
//   - Go's `ast.ChildIsDecorated(useLegacyDecorators, node, nil)` takes a
//     nilable parent; the ported `ast::child_is_decorated` takes a
//     non-optional `parent` it forwards as `Some(grandparent)`, so the
//     nil-parent call is spelled out in `child_is_decorated_no_parent`
//     (identical bodies, `None` grandparent).
//   - `transformDecoratorsOfClassElements`/`getConstructorDecorationStatement`
//     return `(Option<NodeList>, Vec<NodeId>)`/`Option<NodeId>` — Go's nilable
//     `*ast.NodeList`/`[]*ast.Node` map onto `Option`/`Vec`.
//   - `[][]*ast.Node` parameter-decorator tables are `Vec<Vec<NodeId>>`; Go's
//     nil-vs-empty distinctions only gate `len(...) == 0` checks, which an
//     empty `Vec` answers identically.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{
    self as ast, Kind, ModifierFlags, ModifierList, Node, NodeFlags, NodeId, NodeList,
    SubtreeFacts, Symbol,
};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS;
use tsc_core::core::some;
use tsc_core::options_generated::ScriptTarget;
use tsc_printer::{AssignedNameOptions, EmitFlags, NameOptions};

use crate::chain::TransformOptions;
use crate::estransforms::{Ec, make_transformer, visit_each_child};
use crate::transformer::Transformer;
use crate::utilities::{
    is_generated_identifier, is_simple_inlineable_expression, move_range_past_modifiers,
};

/// `type allDecorators struct`.
#[derive(Default)]
pub struct AllDecorators {
    /// `decorators []*ast.Node`
    pub decorators: Vec<NodeId>,
    /// `parameters [][]*ast.Node`
    pub parameters: Vec<Vec<NodeId>>,
}

/// `type LegacyDecoratorsTransformer struct`.
pub struct LegacyDecoratorsTransformer<'a> {
    /// `languageVersion core.ScriptTarget`
    language_version: ScriptTarget,
    /// `referenceResolver binder.ReferenceResolver`
    reference_resolver: Option<Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    /// `opts.Symbols` — the binder symbol arena `ReferenceResolver` methods
    /// index into (see `crate::chain::TransformOptions::symbols`).
    symbols: Option<&'a RefCell<Vec<Symbol>>>,
    /// `classAliases map[*ast.Node]*ast.Node` — a map that keeps track of
    /// aliases created for classes with decorators to avoid issues with the
    /// double-binding behavior of classes. `None` mirrors Go's nil map.
    class_aliases: RefCell<Option<HashMap<NodeId, NodeId>>>,
    /// `enclosingClasses []*ast.ClassDeclaration`
    enclosing_classes: RefCell<Vec<NodeId>>,
}

/// `n.Decorators()` — the ids of the `Decorator` modifier nodes on `node`.
fn decorators_of(node: &Node, nodes: &[Node]) -> Vec<NodeId> {
    node.modifiers()
        .map(|m| {
            m.nodes
                .iter()
                .copied()
                .filter(|&n| ast::is_decorator(&nodes[n]))
                .collect()
        })
        .unwrap_or_default()
}

/// `elideNodes` — replaces a non-empty node list with an empty list at the
/// same location (`nil`/`None` passes through). Dead code, as in Go.
#[allow(dead_code)]
fn elide_nodes(ec: &Ec, nodes: Option<NodeList>) -> Option<NodeList> {
    let nodes = nodes?;
    if nodes.nodes.is_empty() {
        return Some(nodes);
    }
    let mut replacement = ec.borrow().factory.new_node_list(Vec::<NodeId>::new());
    replacement.loc = nodes.loc;
    Some(replacement)
}

/// `elideModifiers` — replaces a non-empty modifier list with an empty list
/// at the same location (`nil`/`None` passes through).
fn elide_modifiers(
    ec: &Ec,
    cx: &VisitorCx<'_, '_>,
    nodes: Option<ModifierList>,
) -> Option<ModifierList> {
    let nodes = nodes?;
    if nodes.nodes.is_empty() {
        return Some(nodes);
    }
    let mut replacement = ec
        .borrow()
        .factory
        .new_modifier_list(cx.nodes, Vec::<NodeId>::new());
    replacement.loc = nodes.loc;
    Some(replacement)
}

/// `isClassStaticBlockDeclarationOrStaticProperty`.
fn is_class_static_block_declaration_or_static_property(node: &Node) -> bool {
    ast::is_class_static_block_declaration(node)
        || (ast::is_property_declaration(node) && ast::has_static_modifier(node))
}

/// `isNotExportOrDefaultOrDecorator`.
fn is_not_export_or_default_or_decorator(node: &Node) -> bool {
    !(ast::is_decorator(node)
        || node.kind == Kind::ExportKeyword
        || node.kind == Kind::DefaultKeyword)
}

/// `decoratorContainsPrivateIdentifierInExpression`.
fn decorator_contains_private_identifier_in_expression(decorator: &Node, nodes: &[Node]) -> bool {
    decorator.subtree_facts(nodes) & SubtreeFacts::CONTAINS_PRIVATE_IDENTIFIER_IN_EXPRESSION
        != SubtreeFacts::NONE
}

/// `parameterDecoratorsContainPrivateIdentifierInExpression`.
fn parameter_decorators_contain_private_identifier_in_expression(
    parameter_decorators: &[NodeId],
    nodes: &[Node],
) -> bool {
    some(parameter_decorators, |&d| {
        decorator_contains_private_identifier_in_expression(&nodes[d], nodes)
    })
}

/// `hasClassElementWithDecoratorContainingPrivateIdentifierInExpression`.
fn has_class_element_with_decorator_containing_private_identifier_in_expression(
    node: NodeId,
    nodes: &[Node],
) -> bool {
    let members: &[NodeId] = nodes[node].members().unwrap_or(&[]);
    if members.is_empty() {
        return false;
    }
    for &member in members {
        if !ast::can_have_decorators(&nodes[member]) {
            continue;
        }
        let Some(all_decorators) = get_all_decorators_of_class_element(member, node, true, nodes)
        else {
            continue;
        };
        if some(&all_decorators.decorators, |&d| {
            decorator_contains_private_identifier_in_expression(&nodes[d], nodes)
        }) {
            return true;
        }
        if some(&all_decorators.parameters, |p| {
            parameter_decorators_contain_private_identifier_in_expression(p, nodes)
        }) {
            return true;
        }
    }
    false
}

/// `getAllDecoratorsOfClass` — gets an `AllDecorators` containing the
/// decorators for the class and the decorators for the parameters of the
/// constructor of the class (`None` mirrors Go's nil return).
fn get_all_decorators_of_class(
    node: NodeId,
    use_legacy_decorators: bool,
    nodes: &[Node],
) -> Option<AllDecorators> {
    let decorators = decorators_of(&nodes[node], nodes);
    let mut parameters = Vec::new();
    if use_legacy_decorators {
        parameters = get_decorators_of_parameters(
            ast::get_first_constructor_with_body(&nodes[node], nodes),
            nodes,
        );
    }
    if decorators.is_empty() && parameters.is_empty() {
        return None;
    }
    Some(AllDecorators {
        decorators,
        parameters,
    })
}

/// `getAllDecoratorsOfClassElement` — gets an `AllDecorators` containing the
/// decorators for the member and its parameters.
fn get_all_decorators_of_class_element(
    member: NodeId,
    parent: NodeId,
    use_legacy_decorators: bool,
    nodes: &[Node],
) -> Option<AllDecorators> {
    match nodes[member].kind {
        Kind::GetAccessor | Kind::SetAccessor => {
            if !use_legacy_decorators {
                return get_all_decorators_of_method(member, false, nodes);
            }
            get_all_decorators_of_accessors(member, parent, true, nodes)
        }
        Kind::MethodDeclaration => {
            get_all_decorators_of_method(member, use_legacy_decorators, nodes)
        }
        Kind::PropertyDeclaration => get_all_decorators_of_property(member, nodes),
        _ => None,
    }
}

/// `getAllDecoratorsOfAccessors` — gets an `AllDecorators` containing the
/// decorators for the accessor and its parameters.
fn get_all_decorators_of_accessors(
    accessor: NodeId,
    parent: NodeId,
    use_legacy_decorators: bool,
    nodes: &[Node],
) -> Option<AllDecorators> {
    if nodes[accessor].body().is_none() {
        return None;
    }
    let decls = ast::get_all_accessor_declarations(
        nodes[parent]
            .member_list()
            .map(|m| m.nodes())
            .unwrap_or(&[]),
        accessor,
        nodes,
    );
    let first_accessor_with_decorators = if ast::has_decorators(&nodes[decls.first_accessor]) {
        Some(decls.first_accessor)
    } else if decls
        .second_accessor
        .is_some_and(|s| ast::has_decorators(&nodes[s]))
    {
        decls.second_accessor
    } else {
        None
    };

    let Some(first_accessor_with_decorators) = first_accessor_with_decorators else {
        return None;
    };
    if accessor != first_accessor_with_decorators {
        return None;
    }

    let decorators = decorators_of(&nodes[first_accessor_with_decorators], nodes);
    let mut parameters = Vec::new();
    if use_legacy_decorators && decls.set_accessor.is_some() {
        parameters = get_decorators_of_parameters(decls.set_accessor, nodes);
    }

    if decorators.is_empty() && parameters.is_empty() {
        return None;
    }
    Some(AllDecorators {
        decorators,
        parameters,
    })
}

/// `getAllDecoratorsOfProperty`.
fn get_all_decorators_of_property(property: NodeId, nodes: &[Node]) -> Option<AllDecorators> {
    let decorators = decorators_of(&nodes[property], nodes);
    if decorators.is_empty() {
        return None;
    }
    Some(AllDecorators {
        decorators,
        parameters: Vec::new(),
    })
}

/// `getAllDecoratorsOfMethod`.
fn get_all_decorators_of_method(
    method: NodeId,
    use_legacy_decorators: bool,
    nodes: &[Node],
) -> Option<AllDecorators> {
    if nodes[method].body().is_none() {
        return None;
    }
    let decorators = decorators_of(&nodes[method], nodes);
    let mut parameters = Vec::new();
    if use_legacy_decorators {
        parameters = get_decorators_of_parameters(Some(method), nodes);
    }
    if decorators.is_empty() && parameters.is_empty() {
        return None;
    }
    Some(AllDecorators {
        decorators,
        parameters,
    })
}

/// `getDecoratorsOfParameters` — gets a vector of vectors of decorators for
/// the parameters of a function-like node. The offset into the result should
/// correspond to the offset of the parameter.
///
/// PORT: Go returns `[][]*ast.Node` lazily allocated once the first decorated
/// parameter is seen; `Vec<Vec<NodeId>>` is empty until then and `None` mirrors
/// Go's `nil` node.
pub fn get_decorators_of_parameters(node: Option<NodeId>, nodes: &[Node]) -> Vec<Vec<NodeId>> {
    let mut decorators: Vec<Vec<NodeId>> = Vec::new();
    if let Some(node) = node {
        let parameters: Vec<NodeId> = nodes[node].parameters().unwrap_or(&[]).to_vec();
        let first_parameter_is_this =
            !parameters.is_empty() && ast::is_this_parameter(&nodes[parameters[0]], nodes);
        let mut first_parameter_offset = 0;
        let mut num_parameters = parameters.len();
        if first_parameter_is_this {
            first_parameter_offset = 1;
            num_parameters -= 1;
        }
        for i in 0..num_parameters {
            let p = parameters[i + first_parameter_offset];
            if !decorators.is_empty() || ast::has_decorators(&nodes[p]) {
                if decorators.is_empty() {
                    decorators = vec![Vec::new(); num_parameters];
                }
                decorators[i] = decorators_of(&nodes[p], nodes);
            }
        }
    }
    decorators
}

/// `ast.ChildIsDecorated(useLegacyDecorators, node, nil)` — Go's `parent` is
/// nilable while `ast::child_is_decorated` takes a `NodeId` it forwards as
/// `Some(grandparent)`; this spells out the nil-parent call with the same
/// bodies (`None` grandparent).
pub(crate) fn child_is_decorated_no_parent(
    use_legacy_decorators: bool,
    node: NodeId,
    nodes: &[Node],
) -> bool {
    match nodes[node].kind {
        Kind::ClassDeclaration | Kind::ClassExpression => nodes[node]
            .member_list()
            .map(|m| m.nodes().to_vec())
            .unwrap_or_default()
            .iter()
            .any(|&m| {
                ast::node_or_child_is_decorated(use_legacy_decorators, m, Some(node), None, nodes)
            }),
        Kind::MethodDeclaration | Kind::SetAccessor | Kind::Constructor => nodes[node]
            .parameters()
            .unwrap_or(&[])
            .iter()
            .any(|&p| ast::node_is_decorated(use_legacy_decorators, p, Some(node), None, nodes)),
        _ => false,
    }
}

/// `isDecoratedClassElement` — determines whether a class member is either a
/// static or an instance member of a class that is decorated, or has
/// parameters that are decorated.
fn is_decorated_class_element(
    member: NodeId,
    is_static_element: bool,
    parent: NodeId,
    nodes: &[Node],
) -> bool {
    is_static_element == ast::is_static(&nodes[member])
        && ast::node_or_child_is_decorated(true, member, Some(parent), None, nodes)
}

/// `getDecoratedClassElements` — gets either the static or instance members
/// of a class that are decorated, or have parameters that are decorated.
fn get_decorated_class_elements(node: NodeId, is_static: bool, nodes: &[Node]) -> Vec<NodeId> {
    let members = nodes[node]
        .member_list()
        .map(|m| m.nodes().to_vec())
        .unwrap_or_default();
    if members.is_empty() {
        return Vec::new();
    }
    members
        .iter()
        .copied()
        .filter(|&m| is_decorated_class_element(m, is_static, node, nodes))
        .collect()
}

impl<'a> LegacyDecoratorsTransformer<'a> {
    /// `tx.visit`
    fn visit<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // we have to visit all identifiers in classes, just in case they
        // require substitution
        if cx.nodes[node].subtree_facts(cx.nodes) & SubtreeFacts::CONTAINS_DECORATORS
            == SubtreeFacts::NONE
            && self.enclosing_classes.borrow().is_empty()
        {
            return Some(node);
        }

        match cx.nodes[node].kind {
            Kind::Identifier => Some(self.visit_identifier(ec, cx, node)),
            Kind::PropertyAccessExpression => {
                Some(self.visit_property_access_expression(ec, v, cx, node))
            }
            // Decorators are elided. They will be emitted as part of
            // `visitClassDeclaration`.
            Kind::Decorator => None,
            Kind::ClassDeclaration => Some(self.visit_class_declaration(ec, v, cx, node)),
            Kind::ClassExpression => Some(self.visit_class_expression(ec, v, cx, node)),
            Kind::Constructor => Some(self.visit_constructor_declaration(ec, v, cx, node)),
            Kind::MethodDeclaration => Some(self.visit_method_declaration(ec, v, cx, node)),
            Kind::SetAccessor => Some(self.visit_set_accessor_declaration(ec, v, cx, node)),
            Kind::GetAccessor => Some(self.visit_get_accessor_declaration(ec, v, cx, node)),
            Kind::PropertyDeclaration => self.visit_property_declaration(ec, v, cx, node),
            Kind::Parameter => Some(self.visit_parameter_declaration(ec, v, cx, node)),
            Kind::SourceFile => {
                *self.class_aliases.borrow_mut() = Some(HashMap::new());
                self.enclosing_classes.borrow_mut().clear();
                let result = v.visit_each_child(cx, node).unwrap_or(node);
                let helpers = ec.borrow_mut().read_emit_helpers();
                ec.borrow().add_emit_helper(result, &helpers);
                *self.class_aliases.borrow_mut() = None;
                self.enclosing_classes.borrow_mut().clear();
                Some(result)
            }
            _ => Some(visit_each_child(v, cx, node)),
        }
    }

    /// `GetReferencedValueDeclaration` through `referenceResolver` — Go
    /// panics on a nil interface; the port `.expect()`s.
    fn get_referenced_value_declaration(&self, nodes: &[Node], node: NodeId) -> Option<NodeId> {
        let resolver = self
            .reference_resolver
            .as_ref()
            .expect("LegacyDecoratorsTransformer requires a reference resolver");
        let symbols = self
            .symbols
            .expect("opts.symbols (the binder symbol arena) is required alongside opts.Resolver");
        resolver
            .borrow_mut()
            .get_referenced_value_declaration(node, nodes, symbols)
    }

    /// `tx.visitIdentifier` — takes the place of `substituteIdentifier` in
    /// the strada transform.
    fn visit_identifier(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        for &d in &*self.enclosing_classes.borrow() {
            let alias = self
                .class_aliases
                .borrow()
                .as_ref()
                .and_then(|m| m.get(&d).copied());
            if let Some(alias) = alias {
                let original = ec.borrow().most_original(Some(node)).unwrap_or(node);
                if self.get_referenced_value_declaration(cx.nodes, original)
                    == ec.borrow().most_original(Some(d))
                {
                    return alias;
                }
            }
        }
        node
    }

    /// `tx.visitPropertyAccessExpression` — visits the expression but not the
    /// name, since property access names should not be substituted. Strada's
    /// onSubstituteNode only fires for EmitHint.Expression, which excludes the
    /// `.name` of PropertyAccessExpression.
    fn visit_property_access_expression<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, question_dot_token, name, flags) = {
            let d = cx.nodes[node].as_property_access_expression();
            (
                d.expression,
                d.question_dot_token,
                d.name,
                cx.nodes[node].flags,
            )
        };
        let visited_expression = v.visit_node(cx, expression);
        if visited_expression != expression {
            return ec
                .borrow_mut()
                .factory
                .update_property_access_expression(
                    cx.nodes,
                    node,
                    visited_expression,
                    question_dot_token,
                    name,
                    flags,
                )
                .unwrap_or(node);
        }
        node
    }

    /// `finishClassElement`.
    fn finish_class_element(
        &self,
        ec: &Ec,
        cx: &VisitorCx<'_, '_>,
        updated: NodeId,
        original: NodeId,
    ) -> NodeId {
        if updated != original {
            // While we emit the source map for the node after skipping
            // decorators and modifiers, we need to emit the comments for the
            // original range.
            ec.borrow()
                .set_comment_range(updated, cx.nodes[original].loc);
            let range = move_range_past_modifiers(cx.nodes, original);
            ec.borrow().set_source_map_range(updated, range);
        }
        updated
    }

    /// `tx.visitParamerDeclaration` (sic — Go's misspelling kept as the
    /// canonical name in the comment).
    fn visit_parameter_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = elide_modifiers(ec, cx, cx.nodes[node].modifiers().cloned());
        let (dot_dot_dot_token, name, initializer) = {
            let d = cx.nodes[node].as_parameter_declaration();
            (d.dot_dot_dot_token, d.name, d.initializer)
        };
        let name = v.visit_node(cx, name);
        let initializer = v.visit_node(cx, initializer);
        let updated = ec
            .borrow_mut()
            .factory
            .update_parameter_declaration(
                cx.nodes,
                node,
                modifiers,
                dot_dot_dot_token,
                name,
                None,
                None,
                initializer,
            )
            .unwrap_or(node);
        if updated != node {
            // While we emit the source map for the node after skipping
            // decorators and modifiers, we need to emit the comments for the
            // original range.
            let loc = cx.nodes[node].loc;
            ec.borrow().set_comment_range(updated, loc);
            let new_loc = move_range_past_modifiers(cx.nodes, node);
            cx.nodes[updated].loc = new_loc;
            ec.borrow().set_source_map_range(updated, new_loc);
            if let Some(name) = cx.nodes[updated].name() {
                ec.borrow()
                    .set_emit_flags(name, EmitFlags::NO_TRAILING_SOURCE_MAP);
            }
        }
        updated
    }

    /// `visitPropertyNameOfClassElement` — visits the property name of a
    /// class element, for use when emitting property initializers. For a
    /// computed property on a node with decorators, a temporary value is
    /// stored for later use.
    fn visit_property_name_of_class_element<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        member: NodeId,
    ) -> Option<NodeId> {
        let name = cx.nodes[member].name();
        if let Some(name_id) = name
            && ast::is_computed_property_name(&cx.nodes[name_id])
            && ast::has_decorators(&cx.nodes[member])
        {
            let expression = cx.nodes[name_id].as_computed_property_name().expression;
            let expression = v.visit_node(cx, expression);
            let inner_expression =
                expression.map(|e| ast::skip_partially_emitted_expressions(e, cx.nodes));
            if !inner_expression.is_some_and(|e| is_simple_inlineable_expression(&cx.nodes[e])) {
                let generated_name = ec
                    .borrow_mut()
                    .factory
                    .new_generated_name_for_node(cx.nodes, name_id);
                ec.borrow_mut()
                    .add_variable_declaration(cx.nodes, generated_name);
                let assignment = ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    generated_name,
                    expression.expect("decorated computed property name expression"),
                );
                return Some(
                    ec.borrow_mut()
                        .factory
                        .update_computed_property_name(cx.nodes, name_id, Some(assignment))
                        .unwrap_or(name_id),
                );
            }
        }
        v.visit_node(cx, name)
    }

    /// `tx.visitPropertyDeclaration` — `None` return elides the member.
    fn visit_property_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].flags & NodeFlags::AMBIENT != NodeFlags::NONE {
            return None;
        }
        if ast::has_syntactic_modifier(
            &cx.nodes[node],
            ModifierFlags::AMBIENT | ModifierFlags::ABSTRACT,
        ) {
            return None;
        }

        let modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let name = self.visit_property_name_of_class_element(ec, v, cx, node);
        let initializer = v.visit_node(cx, cx.nodes[node].as_property_declaration().initializer);
        let updated = ec
            .borrow_mut()
            .factory
            .update_property_declaration(cx.nodes, node, modifiers, name, None, None, initializer)
            .unwrap_or(node);
        Some(self.finish_class_element(ec, cx, updated, node))
    }

    /// `tx.visitGetAccessorDeclaration`.
    fn visit_get_accessor_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let name = self.visit_property_name_of_class_element(ec, v, cx, node);
        let parameters = v.visit_nodes(cx, cx.nodes[node].parameter_list().cloned());
        let body = v.visit_node(cx, cx.nodes[node].body());
        let updated = ec
            .borrow_mut()
            .factory
            .update_get_accessor_declaration(
                cx.nodes, node, modifiers, name, None, parameters, None, None, body,
            )
            .unwrap_or(node);
        self.finish_class_element(ec, cx, updated, node)
    }

    /// `tx.visitSetAccessorDeclaration`.
    fn visit_set_accessor_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let name = self.visit_property_name_of_class_element(ec, v, cx, node);
        let parameters = v.visit_nodes(cx, cx.nodes[node].parameter_list().cloned());
        let body = v.visit_node(cx, cx.nodes[node].body());
        let updated = ec
            .borrow_mut()
            .factory
            .update_set_accessor_declaration(
                cx.nodes, node, modifiers, name, None, parameters, None, None, body,
            )
            .unwrap_or(node);
        self.finish_class_element(ec, cx, updated, node)
    }

    /// `tx.visitMethodDeclaration`.
    fn visit_method_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let asterisk_token = cx.nodes[node]
            .as_method_declaration()
            .function_like_with_body_base
            .body_base
            .asterisk_token;
        let modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let name = self.visit_property_name_of_class_element(ec, v, cx, node);
        let parameters = v.visit_nodes(cx, cx.nodes[node].parameter_list().cloned());
        let body = v.visit_node(cx, cx.nodes[node].body());
        let updated = ec
            .borrow_mut()
            .factory
            .update_method_declaration(
                cx.nodes,
                node,
                modifiers,
                asterisk_token,
                name,
                None,
                None,
                parameters,
                None,
                None,
                body,
            )
            .unwrap_or(node);
        self.finish_class_element(ec, cx, updated, node)
    }

    /// `tx.visitConstructorDeclaration`.
    fn visit_constructor_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let parameters = v.visit_nodes(cx, cx.nodes[node].parameter_list().cloned());
        let body = v.visit_node(cx, cx.nodes[node].body());
        ec.borrow_mut()
            .factory
            .update_constructor_declaration(
                cx.nodes, node, modifiers, None, parameters, None, None, body,
            )
            .unwrap_or(node)
    }

    /// `tx.visitClassExpression` — legacy decorators were not supported on
    /// class expressions.
    fn visit_class_expression<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let (name, heritage_clauses, members) = {
            let d = cx.nodes[node].as_class_expression();
            (
                d.class_like_base.name,
                d.class_like_base.heritage_clauses.clone(),
                d.class_like_base.members.clone(),
            )
        };
        let heritage_clauses = v.visit_nodes(cx, heritage_clauses);
        let members = v.visit_nodes(cx, members);
        ec.borrow_mut()
            .factory
            .update_class_expression(
                cx.nodes,
                node,
                modifiers,
                name,
                None,
                heritage_clauses,
                members,
            )
            .unwrap_or(node)
    }

    /// `tx.visitClassDeclaration`.
    fn visit_class_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let decorated = ast::class_or_constructor_parameter_is_decorated(true, node, cx.nodes);
        if !(decorated || child_is_decorated_no_parent(true, node, cx.nodes)) {
            return visit_each_child(v, cx, node);
        }

        let name = cx.nodes[node].name();
        if decorated {
            return self.transform_class_declaration_with_class_decorators(ec, v, cx, node, name);
        }
        self.transform_class_declaration_without_class_decorators(ec, v, cx, node, name)
    }

    /// `transformClassDeclarationWithoutClassDecorators` — transforms a
    /// non-decorated class declaration:
    ///
    /// ```text
    ///  ${modifiers} class ${name} ${heritageClauses} {
    ///      ${members}
    ///  }
    /// ```
    fn transform_class_declaration_without_class_decorators<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        name: Option<NodeId>,
    ) -> NodeId {
        let modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let (heritage_clauses, members) = {
            let d = cx.nodes[node].as_class_declaration();
            (
                d.class_like_base.heritage_clauses.clone(),
                d.class_like_base.members.clone(),
            )
        };
        let heritage_clauses = v.visit_nodes(cx, heritage_clauses);
        let initial_members = v.visit_nodes(cx, members);
        let (members, decoration_statements) =
            self.transform_decorators_of_class_elements(ec, v, cx, node, initial_members);

        let mut name = name;
        if name.is_none() && !decoration_statements.is_empty() {
            name = Some(
                ec.borrow_mut()
                    .factory
                    .new_generated_name_for_node(cx.nodes, node),
            );
        }

        let updated = ec
            .borrow_mut()
            .factory
            .update_class_declaration(
                cx.nodes,
                node,
                modifiers,
                name,
                None,
                heritage_clauses,
                members,
            )
            .unwrap_or(node);

        if decoration_statements.is_empty() {
            return updated;
        }
        let mut statements = vec![updated];
        statements.extend(decoration_statements);
        ec.borrow_mut()
            .factory
            .new_syntax_list(cx.nodes, &statements)
    }

    /// `popEnclosingClass`.
    fn pop_enclosing_class(&self) {
        self.enclosing_classes.borrow_mut().pop();
    }

    /// `pushEnclosingClass`.
    fn push_enclosing_class(&self, cls: NodeId) {
        self.enclosing_classes.borrow_mut().push(cls);
    }

    /// `transformClassDeclarationWithClassDecorators` — transforms a
    /// decorated class declaration and appends the resulting statements. If
    /// the class requires an alias to avoid issues with double-binding, the
    /// alias is used for references inside the class body.
    ///
    /// See the Go source for the full emit-shape commentary ([Example 1]–[4]).
    fn transform_class_declaration_with_class_decorators<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        name: Option<NodeId>,
    ) -> NodeId {
        let is_export = ast::has_syntactic_modifier(&cx.nodes[node], ModifierFlags::EXPORT);
        let is_default = ast::has_syntactic_modifier(&cx.nodes[node], ModifierFlags::DEFAULT);
        let mut modifiers: Option<ModifierList> = None;
        if let Some(m) = cx.nodes[node].modifiers()
            && !m.nodes.is_empty()
        {
            let modifier_nodes: Vec<NodeId> = m
                .nodes
                .iter()
                .copied()
                .filter(|&n| is_not_export_or_default_or_decorator(&cx.nodes[n]))
                .collect();
            if modifier_nodes.len() != m.nodes.len() {
                let mut new_modifiers = ec
                    .borrow()
                    .factory
                    .new_modifier_list(cx.nodes, modifier_nodes);
                new_modifiers.loc = m.loc;
                modifiers = Some(new_modifiers);
            } else {
                modifiers = Some(m.clone());
            }
        }

        let location = move_range_past_modifiers(cx.nodes, node);
        let class_alias = self.get_class_alias_if_needed(ec, cx, node);
        if class_alias.is_some() {
            self.push_enclosing_class(node);
        }

        // Go uses `defer tx.popEnclosingClass()` — the body is split out so
        // the pop always runs (panics aside, which abort the visit anyway).
        let result = self.transform_class_declaration_with_class_decorators_inner(
            ec,
            v,
            cx,
            node,
            name,
            modifiers,
            location,
            class_alias,
            is_export,
            is_default,
        );
        if class_alias.is_some() {
            self.pop_enclosing_class();
        }
        result
    }

    /// The `defer`-guarded body of `transformClassDeclarationWithClassDecorators`.
    #[allow(clippy::too_many_arguments)]
    fn transform_class_declaration_with_class_decorators_inner<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        name: Option<NodeId>,
        modifiers: Option<ModifierList>,
        location: tsc_core::text::TextRange,
        class_alias: Option<NodeId>,
        is_export: bool,
        is_default: bool,
    ) -> NodeId {
        // When we used to transform to ES5/3 this would be moved inside an
        // IIFE and should reference the name without any block-scoped variable
        // collision handling - but we don't support that anymore, so we always
        // use the local name for the class.
        let decl_name = ec.borrow_mut().factory.get_local_name_ex(
            cx.nodes,
            Some(node),
            &AssignedNameOptions {
                allow_comments: false,
                allow_source_maps: true,
                ..Default::default()
            },
        );

        //  ... = class ${name} ${heritageClauses} {
        //      ${members}
        //  }
        let (heritage_clauses, members) = {
            let d = cx.nodes[node].as_class_declaration();
            (
                d.class_like_base.heritage_clauses.clone(),
                d.class_like_base.members.clone(),
            )
        };
        let heritage_clauses = v.visit_nodes(cx, heritage_clauses);
        let members = v.visit_nodes(cx, members);

        let (mut members, decoration_statements) =
            self.transform_decorators_of_class_elements(ec, v, cx, node, members);

        // If we're emitting to ES2022 or later then we need to reassign the
        // class alias before static initializers are evaluated.
        let assign_class_alias_in_static_block = self.language_version >= ScriptTarget::ES2022
            && class_alias.is_some()
            && members.as_ref().is_some_and(|m| !m.nodes.is_empty())
            && members.as_ref().is_some_and(|m| {
                some(&m.nodes, |&n| {
                    is_class_static_block_declaration_or_static_property(&cx.nodes[n])
                })
            });
        if assign_class_alias_in_static_block {
            let mut member_list: Vec<NodeId> = Vec::new();
            let assign_statement = {
                let mut ecg = ec.borrow_mut();
                let f = &mut ecg.factory;
                let this = f.new_keyword_expression(cx.nodes, Kind::ThisKeyword);
                let assign = f.new_assignment_expression(cx.nodes, class_alias.unwrap(), this);
                let stmt = f.new_expression_statement(cx.nodes, Some(assign));
                let list = f.new_node_list([stmt]);
                let block = f.new_block(cx.nodes, Some(list), false);
                f.new_class_static_block_declaration(cx.nodes, None, Some(block))
            };
            member_list.push(assign_statement);
            member_list.extend_from_slice(&members.as_ref().unwrap().nodes);
            let mut new_list = ec.borrow().factory.new_node_list(member_list);
            new_list.loc = members.as_ref().unwrap().loc;
            members = Some(new_list);
        }

        let mut expr_name = name;
        if let Some(n) = name
            && is_generated_identifier(&ec.borrow(), n)
        {
            expr_name = None;
        }
        let class_expression = ec.borrow_mut().factory.new_class_expression(
            cx.nodes,
            modifiers,
            expr_name,
            None,
            heritage_clauses,
            members,
        );

        ec.borrow().set_original(class_expression, node);
        cx.nodes[class_expression].loc = location;

        //  let ${name} = ${classExpression} where name is either declaredName
        //  if the class doesn't contain self-reference or decoratedClassAlias
        //  if the class contains self-reference.
        let var_initializer = if class_alias.is_some() && !assign_class_alias_in_static_block {
            ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                class_alias.unwrap(),
                class_expression,
            )
        } else {
            class_expression
        };
        let var_decl = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(decl_name),
            None,
            None,
            Some(var_initializer),
        );
        ec.borrow().set_original(var_decl, node);

        let var_decl_list = {
            let mut ecg = ec.borrow_mut();
            let f = &mut ecg.factory;
            let decls = f.new_node_list([var_decl]);
            f.new_variable_declaration_list(cx.nodes, Some(decls), NodeFlags::LET)
        };
        let var_statement =
            ec.borrow_mut()
                .factory
                .new_variable_statement(cx.nodes, None, Some(var_decl_list));
        ec.borrow().set_original(var_statement, node);
        cx.nodes[var_statement].loc = location;
        let node_loc = cx.nodes[node].loc;
        ec.borrow().set_comment_range(var_statement, node_loc);

        let mut statements = vec![var_statement];
        statements.extend(decoration_statements);
        if let Some(statement) = self.get_constructor_decoration_statement(ec, v, cx, node) {
            statements.push(statement);
        }

        if is_export {
            let export_statement = if is_default {
                ec.borrow_mut()
                    .factory
                    .new_export_default(cx.nodes, decl_name)
            } else {
                let export_name = ec
                    .borrow_mut()
                    .factory
                    .get_declaration_name(cx.nodes, Some(node));
                ec.borrow_mut()
                    .factory
                    .new_external_module_export(cx.nodes, export_name)
            };
            statements.push(export_statement);
        }

        // NOTE: Go appends `getConstructorDecorationStatement` even when it
        // returns nil, so `len(statements) == 1` is unreachable there; the
        // port cannot store nil in a `SyntaxList`, so it filters the `None`
        // above. The paths differ only when the constructor decoration is
        // absent — impossible in practice because `decorated` guarantees a
        // class decorator or a constructor parameter decorator.
        if statements.len() == 1 {
            return statements[0];
        }
        ec.borrow_mut()
            .factory
            .new_syntax_list(cx.nodes, &statements)
    }

    /// `hasInternalStaticReference` — determines whether the class contains
    /// an internal reference to the static side of the class.
    fn has_internal_static_reference(&self, ec: &Ec, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        fn is_or_contains_static_self_reference(
            tx: &LegacyDecoratorsTransformer<'_>,
            ec: &Ec,
            nodes: &[Node],
            class_node: Option<NodeId>,
            n: NodeId,
        ) -> bool {
            if ast::is_identifier(&nodes[n]) {
                let original = ec.borrow().most_original(Some(n)).unwrap_or(n);
                if tx.get_referenced_value_declaration(nodes, original) == class_node {
                    return true;
                }
            }
            // For PropertyAccessExpression, only check the expression, not the
            // name. The `.name` is a property access name, not a value
            // reference to the class.
            if ast::is_property_access_expression(&nodes[n]) {
                return match nodes[n].expression() {
                    Some(expression) => {
                        is_or_contains_static_self_reference(tx, ec, nodes, class_node, expression)
                    }
                    None => false,
                };
            }
            nodes[n].for_each_child(nodes, &mut |child| {
                is_or_contains_static_self_reference(tx, ec, nodes, class_node, child)
            })
        }

        let class_node = ec.borrow().most_original(Some(node));
        let members = cx.nodes[node]
            .member_list()
            .map(|m| m.nodes().to_vec())
            .unwrap_or_default();
        for member in members {
            if cx.nodes[member].for_each_child(cx.nodes, &mut |child| {
                is_or_contains_static_self_reference(self, ec, cx.nodes, class_node, child)
            }) {
                return true;
            }
        }
        false
    }

    /// `getClassAliasIfNeeded` — gets a local alias for a class declaration
    /// if it is a decorated class with an internal reference to the static
    /// side of the class. This is necessary to avoid issues with
    /// double-binding semantics for the class name.
    fn get_class_alias_if_needed(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if !self.has_internal_static_reference(ec, cx, node) {
            return None;
        }
        let name_text = match cx.nodes[node].name() {
            Some(name) if !is_generated_identifier(&ec.borrow(), name) => {
                cx.nodes[name].text(cx.nodes).into_owned()
            }
            _ => "default".to_string(),
        };

        let class_alias = ec
            .borrow_mut()
            .factory
            .new_unique_name(cx.nodes, &name_text);
        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, class_alias);
        self.class_aliases
            .borrow_mut()
            .as_mut()
            .expect("classAliases map initialized during SourceFile visit")
            .insert(node, class_alias);

        Some(class_alias)
    }

    /// `getConstructorDecorationStatement` — generates a `__decorate` helper
    /// call for a class constructor.
    fn get_constructor_decoration_statement<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let expression = self.generate_constructor_decoration_expression(ec, v, cx, node)?;
        let result = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(expression));
        ec.borrow().set_original(result, node);
        Some(result)
    }

    /// `generateConstructorDecorationExpression` — generates a `__decorate`
    /// helper call for a class constructor.
    fn generate_constructor_decoration_expression<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let all_decorators = get_all_decorators_of_class(node, true, cx.nodes);
        // Decorator expressions are evaluated outside the class body, so
        // references to the class name should use the original binding, not
        // the class alias. In Strada, this is handled by
        // NodeCheckFlags.ConstructorReference which is only set for
        // identifiers inside the class body. Since Corsa lacks per-node
        // flags, we temporarily pop the enclosing class to prevent alias
        // substitution during decorator expression visiting.
        let has_alias = self.enclosing_classes.borrow().last() == Some(&node);
        if has_alias {
            self.pop_enclosing_class();
        }
        let decorator_expressions =
            self.transform_all_decorators_of_declaration(ec, v, cx, all_decorators);
        if has_alias {
            self.push_enclosing_class(node);
        }
        if decorator_expressions.is_empty() {
            return None;
        }

        let class_alias = self
            .class_aliases
            .borrow()
            .as_ref()
            .and_then(|m| m.get(&node).copied());

        // When we used to transform to ES5/3 this would be moved inside an
        // IIFE and should reference the name without any block-scoped variable
        // collision handling - but we don't support that anymore, so we always
        // use the local name for the class.
        let local_name = ec.borrow_mut().factory.get_declaration_name_ex(
            cx.nodes,
            Some(node),
            &NameOptions {
                allow_comments: false,
                allow_source_maps: true,
            },
        );
        let decorate = ec.borrow_mut().factory.new_decorate_helper(
            cx.nodes,
            decorator_expressions,
            local_name,
            None,
            None,
        );
        let assignment_target = if let Some(class_alias) = class_alias {
            ec.borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, class_alias, decorate)
        } else {
            decorate
        };
        let expression = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            local_name,
            assignment_target,
        );
        ec.borrow()
            .set_emit_flags(expression, EmitFlags::NO_COMMENTS);
        let range = move_range_past_modifiers(cx.nodes, node);
        ec.borrow().set_source_map_range(expression, range);
        Some(expression)
    }

    /// `transformDecoratorsOfClassElements` — returns the updated member list
    /// plus the decoration statements (lifted into a static block when a
    /// decorator expression mentions a private identifier).
    fn transform_decorators_of_class_elements<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        members: Option<NodeList>,
    ) -> (Option<NodeList>, Vec<NodeId>) {
        let mut decoration_statements =
            self.get_class_element_decoration_statements(ec, v, cx, node, false);
        decoration_statements
            .extend(self.get_class_element_decoration_statements(ec, v, cx, node, true));
        let mut members = members;
        if has_class_element_with_decorator_containing_private_identifier_in_expression(
            node, cx.nodes,
        ) {
            let mut member_nodes: Vec<NodeId> = members
                .as_ref()
                .map(|m| m.nodes.to_vec())
                .unwrap_or_default();
            let stmts = std::mem::take(&mut decoration_statements);
            let list = ec.borrow().factory.new_node_list(stmts);
            let block = ec
                .borrow_mut()
                .factory
                .new_block(cx.nodes, Some(list), true);
            member_nodes.push(ec.borrow_mut().factory.new_class_static_block_declaration(
                cx.nodes,
                None,
                Some(block),
            ));
            members = Some(ec.borrow().factory.new_node_list(member_nodes));
        }

        (members, decoration_statements)
    }

    /// `getClassElementDecorationStatements` — generates statements used to
    /// apply decorators to either the static or instance members of a class.
    fn get_class_element_decoration_statements<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        is_static: bool,
    ) -> Vec<NodeId> {
        let exprs = self.generate_class_element_decoration_expressions(ec, v, cx, node, is_static);
        exprs
            .into_iter()
            .map(|e| {
                ec.borrow_mut()
                    .factory
                    .new_expression_statement(cx.nodes, Some(e))
            })
            .collect()
    }

    /// `generateClassElementDecorationExpressions` — generates expressions
    /// used to apply decorators to either the static or instance members of a
    /// class.
    fn generate_class_element_decoration_expressions<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        is_static: bool,
    ) -> Vec<NodeId> {
        let members = get_decorated_class_elements(node, is_static, cx.nodes);
        let mut expressions = Vec::new();
        for member in members {
            if let Some(expr) =
                self.generate_class_element_decoration_expression(ec, v, cx, node, member)
            {
                expressions.push(expr);
            }
        }
        expressions
    }

    /// `generateClassElementDecorationExpression` — generates an expression
    /// used to evaluate class element decorators at runtime.
    ///
    /// Emits the call to `__decorate`. Given the following:
    ///
    /// ```text
    ///   class C {
    ///     @dec method(@dec2 x) {}
    ///     @dec get accessor() {}
    ///     @dec prop;
    ///   }
    /// ```
    ///
    /// The emit for a method is `__decorate([...], C.prototype, "method", null)`;
    /// for an accessor `__decorate([...], C.prototype, "accessor", null)`;
    /// for a property `__decorate([...], C.prototype, "prop")`.
    fn generate_class_element_decoration_expression<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        member: NodeId,
    ) -> Option<NodeId> {
        let all_decorators = get_all_decorators_of_class_element(member, node, true, cx.nodes);
        let decorator_expressions =
            self.transform_all_decorators_of_declaration(ec, v, cx, all_decorators);
        if decorator_expressions.is_empty() {
            return None;
        }

        let prefix = self.get_class_member_prefix(ec, cx, node, member);
        let member_name = self.get_expression_for_property_name(
            ec,
            cx,
            member,
            cx.nodes[member].flags & NodeFlags::AMBIENT == NodeFlags::NONE,
        );
        let descriptor = if ast::is_property_declaration(&cx.nodes[member])
            && !ast::has_accessor_modifier(&cx.nodes[member])
        {
            // We emit `void 0` here to indicate to `__decorate` that it can
            // invoke `Object.defineProperty` directly, but that it should not
            // invoke `Object.getOwnPropertyDescriptor`.
            ec.borrow_mut().factory.new_void_zero_expression(cx.nodes)
        } else {
            // We emit `null` here to indicate to `__decorate` that it can
            // invoke `Object.getOwnPropertyDescriptor` directly. We have this
            // extra argument here so that we can inject an explicit property
            // descriptor at a later date.
            ec.borrow_mut()
                .factory
                .new_keyword_expression(cx.nodes, Kind::NullKeyword)
        };

        let helper = ec.borrow_mut().factory.new_decorate_helper(
            cx.nodes,
            decorator_expressions,
            prefix,
            member_name,
            Some(descriptor),
        );

        ec.borrow().set_emit_flags(helper, EmitFlags::NO_COMMENTS);
        let range = move_range_past_modifiers(cx.nodes, member);
        ec.borrow().set_source_map_range(helper, range);
        Some(helper)
    }

    /// `isSyntheticMetadataDecorator`.
    fn is_synthetic_metadata_decorator(
        &self,
        ec: &Ec,
        cx: &VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        match cx.nodes[node].as_decorator().expression {
            Some(expression) => ec
                .borrow()
                .is_call_to_helper(cx.nodes, expression, "__metadata"),
            None => false,
        }
    }

    /// `transformAllDecoratorsOfDeclaration` — transforms all of the
    /// decorators for a declaration into a vector of expressions.
    fn transform_all_decorators_of_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        all_decorators: Option<AllDecorators>,
    ) -> Vec<NodeId> {
        let Some(all_decorators) = all_decorators else {
            return Vec::new();
        };

        // ensure that metadata decorators are last
        // (`collections.GroupBy(decorators, isSyntheticMetadataDecorator)`)
        let mut metadata: Vec<NodeId> = Vec::new();
        let mut decorators: Vec<NodeId> = Vec::new();
        for d in all_decorators.decorators {
            if self.is_synthetic_metadata_decorator(ec, cx, d) {
                metadata.push(d);
            } else {
                decorators.push(d);
            }
        }

        let mut decorator_expressions = self.transform_decorators(v, cx, &decorators);
        decorator_expressions.extend(self.transform_decorators_of_parameters(
            ec,
            v,
            cx,
            &all_decorators.parameters,
        ));
        decorator_expressions.extend(self.transform_decorators(v, cx, &metadata));
        decorator_expressions
    }

    /// `transformDecoratorsOfParameters`.
    fn transform_decorators_of_parameters<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        parameters: &[Vec<NodeId>],
    ) -> Vec<NodeId> {
        let mut results = Vec::new();
        for (i, decorators) in parameters.iter().enumerate() {
            if !decorators.is_empty() {
                for &decorator in decorators {
                    let expression = cx.nodes[decorator].as_decorator().expression;
                    let visited = v.visit_node(cx, expression).expect("decorator expression");
                    let loc = expression.map(|e| cx.nodes[e].loc).unwrap_or_default();
                    let helper = ec
                        .borrow_mut()
                        .factory
                        .new_param_helper(cx.nodes, visited, i as i32, loc);
                    ec.borrow().set_emit_flags(helper, EmitFlags::NO_COMMENTS);
                    results.push(helper);
                }
            }
        }
        results
    }

    /// `transformDecorators` — transforms a list of decorators into
    /// expressions.
    fn transform_decorators<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        decorators: &[NodeId],
    ) -> Vec<NodeId> {
        let mut results = Vec::with_capacity(decorators.len());
        for &d in decorators {
            let expression = cx.nodes[d].as_decorator().expression;
            results.push(v.visit_node(cx, expression).expect("decorator expression"));
        }
        results
    }

    /// `getClassMemberPrefix`.
    fn get_class_member_prefix(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        member: NodeId,
    ) -> NodeId {
        if ast::is_static(&cx.nodes[member]) {
            return ec
                .borrow_mut()
                .factory
                .get_declaration_name(cx.nodes, Some(node));
        }
        self.get_class_prototype(ec, cx, node)
    }

    /// `getClassPrototype`.
    fn get_class_prototype(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let mut ecg = ec.borrow_mut();
        let f = &mut ecg.factory;
        let name = f.get_declaration_name(cx.nodes, Some(node));
        let prototype = f.new_identifier(cx.nodes, "prototype");
        f.new_property_access_expression(
            cx.nodes,
            Some(name),
            None,
            Some(prototype),
            NodeFlags::NONE,
        )
    }

    /// `getExpressionForPropertyName` — `None` mirrors Go's nil return
    /// (unreachable for named members; `DeepCloneNode(nil)` → nil in Go).
    fn get_expression_for_property_name(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        member: NodeId,
        generate_name_for_computed_property_name: bool,
    ) -> Option<NodeId> {
        let name = cx.nodes[member].name();
        let name_id = name?;
        if ast::is_private_identifier(&cx.nodes[name_id]) {
            Some(ec.borrow_mut().factory.new_identifier(cx.nodes, ""))
        } else if ast::is_computed_property_name(&cx.nodes[name_id]) {
            let expression = cx.nodes[name_id].as_computed_property_name().expression;
            if generate_name_for_computed_property_name
                && !expression.is_some_and(|e| is_simple_inlineable_expression(&cx.nodes[e]))
            {
                return Some(
                    ec.borrow_mut()
                        .factory
                        .new_generated_name_for_node(cx.nodes, name_id),
                );
            }
            expression
        } else if ast::is_identifier(&cx.nodes[name_id]) {
            let text = cx.nodes[name_id].text(cx.nodes).into_owned();
            Some(
                ec.borrow_mut()
                    .factory
                    .new_string_literal(cx.nodes, &text, ast::TokenFlags::NONE),
            )
        } else {
            ec.borrow_mut().factory.deep_clone_node(cx.nodes, name_id)
        }
    }
}

/// `NewLegacyDecoratorsTransformer`.
pub fn new_legacy_decorators_transformer<'a>(
    opt: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    let language_version = opt
        .compiler_options
        .unwrap_or(&EMPTY_COMPILER_OPTIONS)
        .get_emit_script_target();
    let state = Rc::new(LegacyDecoratorsTransformer {
        language_version,
        reference_resolver: opt.resolver.clone(),
        symbols: opt.symbols,
        class_aliases: RefCell::new(None),
        enclosing_classes: RefCell::new(Vec::new()),
    });
    make_transformer(opt, move |ec| {
        let state = state.clone();
        let visit: Box<VisitFn<'a>> = Box::new(
            move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, v, cx, node)
            },
        );
        visit
    })
}
