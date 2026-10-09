// Ported from tsc/internal/transformers/estransforms/classfields.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `newClassFieldsTransformer` — transforms class fields, private identifiers,
// class static blocks, auto-accessors, and static `this`/`super` references.
//
// PORT notes: see `mod.rs`/`async.rs`/`esdecorator.rs` for `Rc<State>` +
// `txv` + `ec_visit_*` conventions. The Go `classLexicalEnv` linked list is a
// `RefCell<Vec<ClassLexicalEnvFrame>>` (previous == parent frame). Callback
// parameters like `setCurrentClassElementAnd(classElement, visitor, node)`
// become the `Cb` discriminant since Go method values can't be stored.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{
    self as ast, Kind, ModifierFlags, ModifierList, NodeFlags, NodeId, NodeList, SubtreeFacts,
    Symbol, TokenFlags,
};
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::{CompilerOptions, ScriptTarget};
use tsc_core::tristate::Tristate;
use tsc_printer::{AutoGenerateOptions, EmitFlags, GeneratedIdentifierFlags, PrivateIdentifierKind};
use tsc_scanner::utilities::is_identifier_text;

use super::classthis::is_class_this_assignment_block;
use super::namedevaluation::{
    class_has_explicitly_assigned_name, is_class_named_evaluation_helper_block,
    is_named_evaluation_and, transform_named_evaluation,
};
use super::utilities::create_accessor_property_backing_field;
use super::{ec_visit_function_body, ec_visit_iteration_body, make_transformer, subtree_facts, Ec};
use crate::chain::TransformOptions;
use crate::modifier_visitor::extract_modifiers;
use crate::transformer::Transformer;
use crate::utilities as transformer_utilities;

// `classFacts` tracks various facts about a class being transformed.
type ClassFacts = u8;
const CLASS_FACTS_NONE: ClassFacts = 0;
const CLASS_FACTS_CLASS_WAS_DECORATED: ClassFacts = 1 << 0;
const CLASS_FACTS_NEEDS_CLASS_CONSTRUCTOR_REFERENCE: ClassFacts = 1 << 1;
const CLASS_FACTS_NEEDS_CLASS_SUPER_REFERENCE: ClassFacts = 1 << 2;
#[allow(dead_code)]
const CLASS_FACTS_NEEDS_SUBSTITUTION_FOR_THIS_IN_CLASS_STATIC_FIELD: ClassFacts = 1 << 3;
const CLASS_FACTS_WILL_HOIST_INITIALIZERS_TO_CONSTRUCTOR: ClassFacts = 1 << 4;

/// `privateIdentifierInfo` stores information about a private identifier
/// during transformation.
#[derive(Clone)]
struct PrivateIdentifierInfo {
    kind: PrivateIdentifierKind,
    /// For instance field: the WeakMap used as storage; for instance methods
    /// or accessors: the WeakSet used for brand checking; for static members:
    /// the constructor used for brand checking.
    brand_check_identifier: Option<NodeId>,
    is_static: bool,
    is_valid: bool,
    /// the variable that serves as storage for a static field.
    variable_name: Option<NodeId>,
    /// identifier for a variable containing the private method implementation.
    method_name: Option<NodeId>,
    /// identifier for a variable containing the private get accessor.
    getter_name: Option<NodeId>,
    /// identifier for a variable containing the private set accessor.
    setter_name: Option<NodeId>,
}

// `PrivateIdentifierKind` lives in tsc_printer so we cannot impl `Default`
// for it (orphan rule); give `PrivateIdentifierInfo` the Go zero-value
// default (`kind` == Field) manually instead.
impl Default for PrivateIdentifierInfo {
    fn default() -> Self {
        PrivateIdentifierInfo {
            kind: PrivateIdentifierKind::Field,
            brand_check_identifier: None,
            is_static: false,
            is_valid: false,
            variable_name: None,
            method_name: None,
            getter_name: None,
            setter_name: None,
        }
    }
}

/// `privateEnvironmentData` stores class-scoped environment data for private
/// identifiers.
#[derive(Default)]
struct PrivateEnvironmentData {
    /// used for prefixing generated variable names.
    class_name: Option<NodeId>,
    /// used for brand check on private methods.
    weak_set_name: Option<NodeId>,
}

/// `privateEnvironment` — two maps: one for non-generated identifiers (keyed
/// by text) and one for generated identifiers (keyed by original AST node).
#[derive(Default)]
struct PrivateEnvironment {
    data: PrivateEnvironmentData,
    members: HashMap<String, Rc<RefCell<PrivateIdentifierInfo>>>,
    generated_identifiers: HashMap<NodeId, Rc<RefCell<PrivateIdentifierInfo>>>,
}

/// `classLexicalEnvironment` stores information about the lexical
/// environment of a class.
#[derive(Default)]
struct ClassLexicalEnvironment {
    facts: ClassFacts,
    /// used for brand checks on static members and `this` references in
    /// static initializers.
    class_constructor: Option<NodeId>,
    class_this: Option<NodeId>,
    /// used for `super` references in static initializers.
    super_class_reference: Option<NodeId>,
}

/// `classLexicalEnv` — a frame in the lexical environment stack.
#[derive(Default)]
struct ClassLexicalEnvFrame {
    data: Option<Rc<RefCell<ClassLexicalEnvironment>>>,
    private_env: Option<Rc<RefCell<PrivateEnvironment>>>,
}

/// `Cb` discriminates the Go method-value parameters passed to helpers like
/// `setCurrentClassElementAnd` / `setInIterationStatementAnd` /
/// `visitInNewClassLexicalEnvironment`.
#[derive(Clone, Copy)]
enum Cb {
    VisitConstructorDeclaration,
    VisitMethodOrAccessorDeclaration,
    VisitPropertyDeclaration,
    VisitClassStaticBlockDeclaration,
    VisitEachChild,
    VisitFunctionExpressionOrDeclaration,
    SetClassElementAndVisitEachChild,
    TransformClassStaticBlockDeclaration,
    VisitClassDeclarationInner,
    VisitClassExpressionInner,
}

/// `type classFieldsTransformer struct`.
pub(crate) struct ClassFieldsTransformer<'a> {
    compiler_options: Option<&'a CompilerOptions>,
    resolver: Option<Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    symbols: Option<&'a RefCell<Vec<Symbol>>>,

    // Computed configuration flags
    should_transform_initializers_using_set: Cell<bool>,
    should_transform_initializers_using_define: Cell<bool>,
    should_transform_initializers: Cell<bool>,
    should_transform_private_elements_or_class_static_blocks: Cell<bool>,
    should_transform_auto_accessors: Cell<bool>,
    should_transform_this_in_static_initializers: Cell<bool>,
    should_transform_super_in_static_initializers: Cell<bool>,
    should_transform_private_static_elements_in_file: Cell<bool>,
    legacy_decorators: bool,

    pending_expressions: RefCell<Vec<NodeId>>,
    pending_statements: RefCell<Vec<NodeId>>,
    lexical_environment: RefCell<Vec<ClassLexicalEnvFrame>>,
    current_class_container: Cell<Option<NodeId>>,
    current_class_element: Cell<Option<NodeId>>,
    /// maps class declarations to alias identifiers for substituting class
    /// name references in static initializers.
    class_aliases: RefCell<HashMap<NodeId, NodeId>>,
    enclosing_class_declarations: RefCell<HashSet<NodeId>>,
    in_iteration_statement: Cell<bool>,
    /// used by `visitThisExpression` to apply the outer environment's
    /// substitution without requiring `currentClassElement` to be static.
    inside_computed_property_name: Cell<bool>,
    parent_node: Cell<Option<NodeId>>,
    current_node: Cell<Option<NodeId>>,

    // Visitors
    modifier_visitor: RefCell<Option<NodeVisitor<'a>>>,
    discarded_value_visitor: RefCell<Option<NodeVisitor<'a>>>,
    heritage_clause_visitor: RefCell<Option<NodeVisitor<'a>>>,
    assignment_target_visitor: RefCell<Option<NodeVisitor<'a>>>,
    class_element_visitor: RefCell<Option<NodeVisitor<'a>>>,
    accessor_field_result_visitor: RefCell<Option<NodeVisitor<'a>>>,
    array_assignment_element_visitor: RefCell<Option<NodeVisitor<'a>>>,
    object_assignment_element_visitor: RefCell<Option<NodeVisitor<'a>>>,
    substitution_visitor: RefCell<Option<NodeVisitor<'a>>>,
}

macro_rules! vref {
    ($self:expr, $field:ident) => {
        $self.$field.borrow().as_ref().expect(concat!(
            stringify!($field),
            " not initialized"
        ))
    };
}

impl<'a> ClassFieldsTransformer<'a> {
    /// `tx.Visitor()` equivalent.
    fn txv(self: &Rc<Self>, ec: &Ec) -> NodeVisitor<'a> {
        let state = self.clone();
        let ec2 = ec.clone();
        ec.borrow().new_node_visitor(Box::new(
            move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec2, cx, node)
            },
        ))
    }

    /// `requiresBlockScopedVar` — private field temp variables are declared
    /// block-scoped when a class expression is directly inside a loop body.
    fn requires_block_scoped_var(&self, cx: &VisitorCx<'_, '_>) -> bool {
        self.in_iteration_statement.get()
            && self.current_class_container.get().is_some_and(|c| {
                ast::is_class_expression(&cx.nodes[c])
            })
    }

    /// `classExpressionNeedsBlockScopedTemp`.
    fn class_expression_needs_block_scoped_temp(&self, cx: &VisitorCx<'_, '_>) -> bool {
        if !self.requires_block_scoped_var(cx) {
            return false;
        }
        let Some(container) = self.current_class_container.get() else {
            return false;
        };
        for member in cx.nodes[container].members().unwrap_or(&[]) {
            if ast::is_property_declaration(&cx.nodes[*member])
                && !ast::has_static_modifier(&cx.nodes[*member])
                && cx.nodes[*member]
                    .name()
                    .is_some_and(|n| ast::is_computed_property_name(&cx.nodes[n]))
            {
                return true;
            }
        }
        false
    }

    /// `visitSourceFile`.
    fn visit_source_file(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if cx.nodes[node].as_source_file().is_declaration_file {
            return node;
        }
        self.lexical_environment.borrow_mut().clear();
        self.should_transform_private_static_elements_in_file.set(
            ec.borrow().emit_flags(node) & EmitFlags::TRANSFORM_PRIVATE_STATIC_ELEMENTS
                != EmitFlags::NONE,
        );
        self.class_aliases.borrow_mut().clear();
        self.enclosing_class_declarations.borrow_mut().clear();
        let visited = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
        let helpers = ec.borrow_mut().read_emit_helpers();
        ec.borrow().add_emit_helper(visited, &helpers);
        self.class_aliases.borrow_mut().clear();
        self.enclosing_class_declarations.borrow_mut().clear();
        visited
    }

    /// `visitModifier` — the `modifierVisitor` callback. Takes `_ec` so the
    /// `install!` macro's uniform `s.$method(&ec2, cx, node)` call applies.
    fn visit_modifier(
        &self,
        _ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].kind == Kind::AccessorKeyword {
            if self.should_transform_auto_accessors_in_current_class() {
                return None;
            }
            return Some(node);
        }
        if ast::is_modifier(&cx.nodes[node]) {
            return Some(node);
        }
        None
    }

    /// `pushNode` — returns grandparent node.
    fn push_node(&self, node: NodeId) -> Option<NodeId> {
        let grandparent = self.parent_node.get();
        self.parent_node.set(self.current_node.get());
        self.current_node.set(Some(node));
        grandparent
    }

    /// `popNode`.
    fn pop_node(&self, grandparent_node: Option<NodeId>) {
        self.current_node.set(self.parent_node.get());
        self.parent_node.set(grandparent_node);
    }

    /// `visitForSubstitution` — substitutes identifiers that reference class
    /// declarations with their aliases.
    fn visit_for_substitution(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if cx.nodes[node].kind == Kind::Identifier {
            return self.visit_identifier(ec, cx, node);
        }
        if cx.nodes[node].kind == Kind::PropertyAccessExpression
            && ast::is_identifier(
                &cx.nodes[cx.nodes[node]
                    .as_property_access_expression()
                    .name
                    .expect("property access name")],
            )
        {
            return self.visit_property_access_expression_for_substitution(ec, cx, node);
        }
        vref!(self, substitution_visitor)
            .visit_each_child(cx, node)
            .unwrap_or(node)
    }

    /// `VisitFn`-shaped adapter for `visit_for_substitution` so it can be
    /// installed as `substitutionVisitor`.
    fn visit_for_substitution_opt(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        Some(self.visit_for_substitution(ec, cx, node))
    }

    /// `visit` — the main visitor.
    pub(crate) fn visit(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let grandparent_node = self.push_node(node);
        let result = self.visit_inner(ec, cx, node);
        self.pop_node(grandparent_node);
        result
    }

    fn visit_inner(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if subtree_facts(cx, node)
            & (SubtreeFacts::CONTAINS_CLASS_FIELDS | SubtreeFacts::CONTAINS_LEXICAL_THIS_OR_SUPER)
            == SubtreeFacts::NONE
        {
            if self.current_class_container.get().is_some()
                && !self.class_aliases.borrow().is_empty()
            {
                // Continue visiting for alias substitution even in non-class-field subtrees.
                return Some(self.visit_for_substitution(ec, cx, node));
            }
            return Some(node);
        }

        match cx.nodes[node].kind {
            Kind::SourceFile => Some(self.visit_source_file(ec, cx, node)),
            Kind::ClassDeclaration => Some(self.visit_class_declaration(ec, cx, node)),
            Kind::ClassExpression => Some(self.visit_class_expression(ec, cx, node)),
            Kind::ClassStaticBlockDeclaration | Kind::PropertyDeclaration => {
                panic!("Use `classElementVisitor` instead.")
            }
            Kind::PropertyAssignment => Some(self.visit_property_assignment(ec, cx, node)),
            Kind::VariableStatement => Some(self.visit_variable_statement(ec, cx, node)),
            Kind::VariableDeclaration => Some(self.visit_variable_declaration(ec, cx, node)),
            Kind::Parameter => Some(self.visit_parameter_declaration(ec, cx, node)),
            Kind::BindingElement => Some(self.visit_binding_element(ec, cx, node)),
            Kind::ExportAssignment => Some(self.visit_export_assignment(ec, cx, node)),
            Kind::PrivateIdentifier => Some(self.visit_private_identifier(ec, cx, node)),
            Kind::PropertyAccessExpression => {
                Some(self.visit_property_access_expression(ec, cx, node))
            }
            Kind::ElementAccessExpression => {
                Some(self.visit_element_access_expression(ec, cx, node))
            }
            Kind::PrefixUnaryExpression | Kind::PostfixUnaryExpression => {
                Some(self.visit_pre_or_postfix_unary_expression(ec, cx, node, false))
            }
            Kind::BinaryExpression => Some(self.visit_binary_expression(ec, cx, node, false)),
            Kind::ParenthesizedExpression => {
                Some(self.visit_parenthesized_expression(ec, cx, node, false))
            }
            Kind::CallExpression => Some(self.visit_call_expression(ec, cx, node)),
            Kind::ExpressionStatement => Some(self.visit_expression_statement(ec, cx, node)),
            Kind::TaggedTemplateExpression => {
                Some(self.visit_tagged_template_expression(ec, cx, node))
            }
            Kind::ForStatement => Some(self.visit_for_statement(ec, cx, node)),
            Kind::ForInStatement
            | Kind::ForOfStatement
            | Kind::DoStatement
            | Kind::WhileStatement => {
                self.set_in_iteration_statement_and(true, Cb::VisitEachChild, ec, cx, node)
            }
            Kind::ThisKeyword => Some(self.visit_this_expression(ec, cx, node)),
            Kind::FunctionDeclaration | Kind::FunctionExpression => self
                .set_in_iteration_statement_and(
                    false,
                    Cb::VisitFunctionExpressionOrDeclaration,
                    ec,
                    cx,
                    node,
                ),
            Kind::Constructor | Kind::MethodDeclaration | Kind::GetAccessor | Kind::SetAccessor => {
                self.set_in_iteration_statement_and(
                    false,
                    Cb::SetClassElementAndVisitEachChild,
                    ec,
                    cx,
                    node,
                )
            }
            _ => self.txv(ec).visit_each_child(cx, node).or(Some(node)),
        }
    }

    /// `visitDiscardedValue` — the `discardedValueVisitor` callback.
    fn visit_discarded_value(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::PrefixUnaryExpression | Kind::PostfixUnaryExpression => {
                Some(self.visit_pre_or_postfix_unary_expression(ec, cx, node, true))
            }
            Kind::BinaryExpression => Some(self.visit_binary_expression(ec, cx, node, true)),
            Kind::ParenthesizedExpression => {
                Some(self.visit_parenthesized_expression(ec, cx, node, true))
            }
            _ => self.visit(ec, cx, node),
        }
    }

    /// `visitHeritageClause` — the `heritageClauseVisitor` callback.
    fn visit_heritage_clause(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::HeritageClause => vref!(self, heritage_clause_visitor)
                .visit_each_child(cx, node)
                .or(Some(node)),
            Kind::ExpressionWithTypeArguments => {
                Some(self.visit_expression_with_type_arguments_in_heritage_clause(ec, cx, node))
            }
            _ => self.visit(ec, cx, node),
        }
    }

    /// `visitAssignmentTarget` — the `assignmentTargetVisitor` callback.
    fn visit_assignment_target(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::ObjectLiteralExpression | Kind::ArrayLiteralExpression => {
                Some(self.visit_assignment_pattern(ec, cx, node))
            }
            _ => self.visit(ec, cx, node),
        }
    }

    /// `visitDestructuringAssignmentTarget`.
    fn visit_destructuring_assignment_target(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if ast::is_object_literal_expression(&cx.nodes[node])
            || ast::is_array_literal_expression(&cx.nodes[node])
        {
            return self.visit_assignment_pattern(ec, cx, node);
        }
        if ast::is_property_access_expression(&cx.nodes[node])
            && ast::is_private_identifier(
                &cx.nodes[cx.nodes[node]
                    .as_property_access_expression()
                    .name
                    .expect("property access name")],
            )
        {
            return self.wrap_private_identifier_for_destructuring_target(ec, cx, node);
        }
        if self.should_transform_super_in_static_initializers.get()
            && self.current_class_element.get().is_some()
            && ast::is_super_property(&cx.nodes[node], cx.nodes)
            && is_static_property_declaration_or_class_static_block(
                &cx.nodes[self.current_class_element.get().unwrap()],
            )
            && self.lexical_data().is_some()
        {
            let data = self.lexical_data().unwrap();
            let data = data.borrow();
            if data.facts & CLASS_FACTS_CLASS_WAS_DECORATED != 0 {
                return self.visit_invalid_super_property(ec, cx, node);
            }
            if let (Some(class_constructor), Some(super_class_reference)) =
                (data.class_constructor, data.super_class_reference)
            {
                let mut name: Option<NodeId> = None;
                if ast::is_element_access_expression(&cx.nodes[node]) {
                    let arg = cx.nodes[node]
                        .as_element_access_expression()
                        .argument_expression;
                    drop(data);
                    name = self.txv(ec).visit_node(cx, arg);
                } else if ast::is_property_access_expression(&cx.nodes[node])
                    && ast::is_identifier(
                        &cx.nodes[cx.nodes[node]
                            .as_property_access_expression()
                            .name
                            .expect("property access name")],
                    )
                {
                    name = Some(ec.borrow_mut().factory.new_string_literal_from_node(
                        cx.nodes,
                        cx.nodes[node]
                            .as_property_access_expression()
                            .name
                            .expect("property access name"),
                    ));
                }
                if let Some(name) = name {
                    let temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                    let set_expr = ec.borrow_mut().factory.new_reflect_set_call(
                        cx.nodes,
                        super_class_reference,
                        name,
                        temp,
                        class_constructor,
                    );
                    return ec.borrow_mut().factory.new_assignment_target_wrapper(
                        cx.nodes,
                        temp,
                        set_expr,
                    );
                }
            }
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `runCb` — dispatches the `Cb` discriminant used in place of Go method
    /// values.
    fn run_cb(
        self: &Rc<Self>,
        ec: &Ec,
        cb: Cb,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cb {
            Cb::VisitConstructorDeclaration => self.visit_constructor_declaration(ec, cx, node),
            Cb::VisitMethodOrAccessorDeclaration => {
                self.visit_method_or_accessor_declaration(ec, cx, node)
            }
            Cb::VisitPropertyDeclaration => self.visit_property_declaration(ec, cx, node),
            Cb::VisitClassStaticBlockDeclaration => {
                self.visit_class_static_block_declaration(ec, cx, node)
            }
            Cb::VisitEachChild => self.txv(ec).visit_each_child(cx, node).or(Some(node)),
            Cb::VisitFunctionExpressionOrDeclaration => {
                Some(self.visit_function_expression_or_declaration(ec, cx, node))
            }
            Cb::SetClassElementAndVisitEachChild => {
                Some(self.set_class_element_and_visit_each_child(ec, cx, node))
            }
            Cb::TransformClassStaticBlockDeclaration => {
                self.transform_class_static_block_declaration(ec, cx, node)
            }
            Cb::VisitClassDeclarationInner => {
                let facts = self.lexical_facts();
                Some(self.visit_class_declaration_inner(ec, cx, node, facts))
            }
            Cb::VisitClassExpressionInner => {
                let facts = self.lexical_facts();
                Some(self.visit_class_expression_inner(ec, cx, node, facts))
            }
        }
    }

    /// `visitClassElement` — the `classElementVisitor` callback.
    fn visit_class_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::Constructor => self.set_current_class_element_and(
                ec,
                Some(node),
                Cb::VisitConstructorDeclaration,
                cx,
                node,
            ),
            Kind::GetAccessor | Kind::SetAccessor | Kind::MethodDeclaration => self
                .set_current_class_element_and(
                    ec,
                    Some(node),
                    Cb::VisitMethodOrAccessorDeclaration,
                    cx,
                    node,
                ),
            Kind::PropertyDeclaration => self.set_current_class_element_and(
                ec,
                Some(node),
                Cb::VisitPropertyDeclaration,
                cx,
                node,
            ),
            Kind::ClassStaticBlockDeclaration => self.set_current_class_element_and(
                ec,
                Some(node),
                Cb::VisitClassStaticBlockDeclaration,
                cx,
                node,
            ),
            Kind::ComputedPropertyName => Some(self.visit_computed_property_name(ec, cx, node)),
            Kind::SemicolonClassElement => Some(node),
            _ => {
                if ast::is_modifier_like(&cx.nodes[node]) {
                    return self.visit_modifier(ec, cx, node);
                }
                self.visit(ec, cx, node)
            }
        }
    }

    /// `visitPropertyName`.
    fn visit_property_name(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: Option<NodeId>,
    ) -> Option<NodeId> {
        if name.is_some_and(|n| ast::is_computed_property_name(&cx.nodes[n])) {
            return Some(self.visit_computed_property_name(ec, cx, name.unwrap()));
        }
        self.txv(ec).visit_node(cx, name)
    }

    /// `visitAccessorFieldResult` — the `accessorFieldResultVisitor` callback.
    fn visit_accessor_field_result(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::PropertyDeclaration => self.transform_field_initializer(ec, cx, node),
            Kind::GetAccessor | Kind::SetAccessor => self.visit_class_element(ec, cx, node),
            _ => panic!(
                "Expected node to either be a PropertyDeclaration, GetAccessorDeclaration, or SetAccessorDeclaration"
            ),
        }
    }

    /// `visitIdentifier` — replaces Strada's onSubstituteNode/trySubstituteClassAlias.
    fn visit_identifier(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if let (Some(resolver), Some(symbols)) = (&self.resolver, self.symbols) {
            let original = ec.borrow().most_original(Some(node));
            let declaration = original.and_then(|o| {
                resolver.borrow_mut().get_referenced_value_declaration(
                    o,
                    cx.nodes,
                    &mut symbols.borrow_mut(),
                )
            });
            if let Some(declaration) = declaration
                && let Some(&alias) = self.class_aliases.borrow().get(&declaration)
                && self
                    .enclosing_class_declarations
                    .borrow()
                    .contains(&declaration)
            {
                let clone = ec.borrow_mut().factory.clone_node(cx.nodes, alias);
                ec.borrow().set_source_map_range(clone, cx.nodes[node].loc);
                ec.borrow().set_comment_range(clone, cx.nodes[node].loc);
                return clone;
            }
        }
        node
    }

    /// `visitPrivateIdentifier` — handles an undeclared private name.
    fn visit_private_identifier(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if !self
            .should_transform_private_elements_or_class_static_blocks
            .get()
        {
            return node;
        }
        if self
            .parent_node
            .get()
            .is_some_and(|p| ast::is_statement(&cx.nodes[p], cx.nodes))
        {
            return node;
        }
        let result = ec.borrow_mut().factory.new_identifier(cx.nodes, "");
        ec.borrow().set_original(result, node);
        result
    }

    /// `transformPrivateIdentifierInInExpression` — visits `#id in expr`.
    fn transform_private_identifier_in_in_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (left, right) = {
            let bin = cx.nodes[node].as_binary_expression();
            (bin.left, bin.right)
        };
        if let Some(info) = self.access_private_identifier(ec, cx, left.expect("in lhs")) {
            let receiver = self.txv(ec).visit_node(cx, right);
            let result = ec.borrow_mut().factory.new_class_private_field_in_helper(
                cx.nodes,
                info.borrow()
                    .brand_check_identifier
                    .expect("brandCheckIdentifier"),
                receiver.expect("in rhs"),
            );
            ec.borrow().set_original(result, node);
            return result;
        }
        // Private name has not been declared. Subsequent transformers will handle this error
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `namedEvaluation` — shared `isNamedEvaluationAnd` + `transformNamedEvaluation`
    /// used by the property-assignment/variable/parameter/binding/export visitors.
    fn named_evaluation(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        ignore_empty_string_literal: bool,
        assigned_name: &str,
    ) -> NodeId {
        let nodes: &[tsc_ast::Node] = &*cx.nodes;
        let mut pred = |n: NodeId| self.is_anonymous_class_needing_assigned_name(ec, nodes, n);
        if is_named_evaluation_and(&ec.borrow(), cx.nodes, node, Some(&mut pred)) {
            return transform_named_evaluation(
                ec,
                cx,
                node,
                ignore_empty_string_literal,
                assigned_name,
            );
        }
        node
    }

    /// `visitPropertyAssignment`.
    fn visit_property_assignment(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let node = self.named_evaluation(ec, cx, node, false, "");
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitVariableStatement`.
    fn visit_variable_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let saved_pending_statements: Vec<NodeId> =
            std::mem::take(&mut *self.pending_statements.borrow_mut());
        let visited_node = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
        if !self.pending_statements.borrow().is_empty() {
            let mut result: Vec<NodeId> = Vec::with_capacity(1 + self.pending_statements.borrow().len());
            result.push(visited_node);
            result.extend(self.pending_statements.borrow().iter().copied());
            *self.pending_statements.borrow_mut() = saved_pending_statements;
            return ec.borrow_mut().factory.new_syntax_list(cx.nodes, &result);
        }
        *self.pending_statements.borrow_mut() = saved_pending_statements;
        visited_node
    }

    /// `visitVariableDeclaration`.
    fn visit_variable_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let node = self.named_evaluation(ec, cx, node, false, "");
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitParameterDeclaration`.
    fn visit_parameter_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let node = self.named_evaluation(ec, cx, node, false, "");
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitBindingElement`.
    fn visit_binding_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let node = self.named_evaluation(ec, cx, node, false, "");
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitExportAssignment`.
    fn visit_export_assignment(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let is_export_equals = cx.nodes[node].as_export_assignment().is_export_equals;
        let assigned_name = if !is_export_equals { "default" } else { "" };
        // NOTE: Since emit for `export =` translates to `module.exports = ...`, the assigned name of the class
        // is `""`.
        let node = self.named_evaluation(ec, cx, node, true, assigned_name);
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `injectPendingExpressions`.
    fn inject_pending_expressions(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        expression: Option<NodeId>,
    ) -> Option<NodeId> {
        if self.pending_expressions.borrow().is_empty() {
            return expression;
        }
        let mut pending: Vec<NodeId> = self.pending_expressions.borrow().clone();
        let Some(expression) = expression else {
            self.pending_expressions.borrow_mut().clear();
            return ec.borrow_mut().factory.inline_expressions(cx.nodes, &pending);
        };
        let result = if ast::is_parenthesized_expression(&cx.nodes[expression]) {
            pending.push(
                cx.nodes[expression]
                    .as_parenthesized_expression()
                    .expression
                    .expect("parenthesized expression"),
            );
            let inlined = ec.borrow_mut().factory.inline_expressions(cx.nodes, &pending);
            ec.borrow_mut()
                .factory
                .update_parenthesized_expression(cx.nodes, expression, inlined)
                .unwrap_or(expression)
        } else {
            pending.push(expression);
            ec.borrow_mut()
                .factory
                .inline_expressions(cx.nodes, &pending)
                .unwrap_or(expression)
        };
        self.pending_expressions.borrow_mut().clear();
        Some(result)
    }

    /// `visitComputedPropertyName` — computed property names are evaluated in
    /// the enclosing scope, not the current class.
    fn visit_computed_property_name(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // Switch to the outer lexical environment, mirroring Strada's onEmitNode.
        let saved_inside = self.inside_computed_property_name.replace(true);
        let popped = {
            let mut stack = self.lexical_environment.borrow_mut();
            if stack.len() >= 2 { stack.pop() } else { None }
        };
        let expression = cx.nodes[node].as_computed_property_name().expression;
        let expression = self.txv(ec).visit_node(cx, expression);
        if let Some(frame) = popped {
            self.lexical_environment.borrow_mut().push(frame);
        }
        self.inside_computed_property_name.set(saved_inside);
        let expression = self.inject_pending_expressions(ec, cx, expression);
        ec.borrow_mut()
            .factory
            .update_computed_property_name(cx.nodes, node, expression)
            .unwrap_or(node)
    }

    /// `visitConstructorDeclaration`.
    fn visit_constructor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if let Some(container) = self.current_class_container.get() {
            return self.transform_constructor(ec, cx, Some(node), container);
        }
        self.txv(ec).visit_each_child(cx, node).or(Some(node))
    }

    /// `shouldTransformClassElementToWeakMap`.
    fn should_transform_class_element_to_weak_map(
        &self,
        ec: &Ec,
        cx: &VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        if self
            .should_transform_private_elements_or_class_static_blocks
            .get()
        {
            return true;
        }
        self.should_always_transform_private_static_elements(ec, cx, node)
    }

    /// `shouldAlwaysTransformPrivateStaticElements`.
    fn should_always_transform_private_static_elements(
        &self,
        ec: &Ec,
        cx: &VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        ast::has_static_modifier(&cx.nodes[node])
            && ec.borrow().emit_flags(node) & EmitFlags::TRANSFORM_PRIVATE_STATIC_ELEMENTS
                != EmitFlags::NONE
    }

    /// `nodeHasTransformPrivateStaticElementsFlag`.
    fn node_has_transform_private_static_elements_flag(&self, ec: &Ec, node: NodeId) -> bool {
        ec.borrow().emit_flags(node) & EmitFlags::TRANSFORM_PRIVATE_STATIC_ELEMENTS
            != EmitFlags::NONE
    }

    /// `visitMethodOrAccessorDeclaration`.
    fn visit_method_or_accessor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        debug_assert!(!ast::has_decorators(&cx.nodes[node]));

        if !ast::is_private_identifier_class_element_declaration(&cx.nodes[node], cx.nodes)
            || !self.should_transform_class_element_to_weak_map(ec, cx, node)
        {
            return vref!(self, class_element_visitor)
                .visit_each_child(cx, node)
                .or(Some(node));
        }

        // leave invalid code untransformed
        let name = cx.nodes[node].name();
        let info = self.get_private_identifier(
            ec,
            cx.nodes,
            &self.get_private_identifier_environment(),
            name.expect("member name"),
        );
        debug_assert!(info.is_some(), "Undeclared private name for property declaration.");
        let Some(info) = info else { return Some(node) };
        if info.borrow().kind == PrivateIdentifierKind::Untransformed || !info.borrow().is_valid {
            return Some(node);
        }
        drop(info);

        if let Some(function_name) = self.get_hoisted_function_name(ec, cx, node) {
            let modifiers = self.extract_non_static_non_accessor_modifiers(ec, cx, node);
            ec.borrow_mut().start_variable_environment();
            let saved = self.in_iteration_statement.replace(false);
            let txv = self.txv(ec);
            let body = ec_visit_function_body(&txv, cx, cx.nodes[node].body());
            let params = txv.visit_nodes(cx, cx.nodes[node].parameter_list().cloned());
            self.in_iteration_statement.set(saved);

            let asterisk_token = match cx.nodes[node].kind {
                Kind::MethodDeclaration => {
                    cx.nodes[node]
                        .as_method_declaration()
                        .function_like_with_body_base
                        .body_base
                        .asterisk_token
                }
                Kind::GetAccessor => {
                    cx.nodes[node]
                        .as_get_accessor_declaration()
                        .accessor_declaration_base
                        .function_like_with_body_base
                        .body_base
                        .asterisk_token
                }
                Kind::SetAccessor => {
                    cx.nodes[node]
                        .as_set_accessor_declaration()
                        .accessor_declaration_base
                        .function_like_with_body_base
                        .body_base
                        .asterisk_token
                }
                _ => None,
            };
            let func_expr = ec.borrow_mut().factory.new_function_expression(
                cx.nodes,
                modifiers,
                asterisk_token,
                Some(function_name),
                None,
                params,
                None,
                None,
                body,
            );
            let assignment = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                function_name,
                func_expr,
            );
            self.add_pending_expressions(&[assignment]);
        }

        // remove method declaration from class
        None
    }

    /// `extractNonStaticNonAccessorModifiers`.
    fn extract_non_static_non_accessor_modifiers(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<ModifierList> {
        extract_modifiers(
            Some(ec),
            cx.nodes,
            cx.nodes[node].modifiers().cloned(),
            !(ModifierFlags::STATIC | ModifierFlags::ACCESSOR),
        )
    }

    /// `setCurrentClassElementAnd`.
    fn set_current_class_element_and(
        self: &Rc<Self>,
        ec: &Ec,
        class_element: Option<NodeId>,
        cb: Cb,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if class_element != self.current_class_element.get() {
            let saved = self.current_class_element.replace(class_element);
            let result = self.run_cb(ec, cb, cx, node);
            self.current_class_element.set(saved);
            return result;
        }
        self.run_cb(ec, cb, cx, node)
    }

    /// `setInIterationStatementAnd`.
    fn set_in_iteration_statement_and(
        self: &Rc<Self>,
        in_iteration: bool,
        cb: Cb,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if self.in_iteration_statement.get() != in_iteration {
            let saved = self.in_iteration_statement.replace(in_iteration);
            let result = self.run_cb(ec, cb, cx, node);
            self.in_iteration_statement.set(saved);
            return result;
        }
        self.run_cb(ec, cb, cx, node)
    }

    /// `setClassElementAndVisitEachChild`.
    fn set_class_element_and_visit_each_child(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.set_current_class_element_and(ec, Some(node), Cb::VisitEachChild, cx, node)
            .unwrap_or(node)
    }

    /// `visitFunctionExpressionOrDeclaration` — preserves `currentClassElement`
    /// for function expressions whose original node is a static class member.
    fn visit_function_expression_or_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if self.current_class_element.get().is_some() {
            let original = ec.borrow().most_original(Some(node));
            if original != Some(node)
                && let Some(container) = self.current_class_container.get()
            {
                for member in cx.nodes[container].members().unwrap_or(&[]) {
                    if ec.borrow().most_original(Some(*member)) == original
                        && ast::is_static(&cx.nodes[*member])
                    {
                        // The function expression originates from a static class member.
                        return self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
                    }
                }
            }
        }
        self.set_current_class_element_and(ec, None, Cb::VisitEachChild, cx, node)
            .unwrap_or(node)
    }

    /// `getHoistedFunctionName`.
    fn get_hoisted_function_name(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let name = cx.nodes[node].name();
        debug_assert!(name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])));
        let info = self.access_private_identifier(ec, cx, name.expect("member name"));
        debug_assert!(info.is_some(), "Undeclared private name for property declaration.");
        let info = info?;
        let info = info.borrow();
        if info.kind == PrivateIdentifierKind::Method {
            return info.method_name;
        }
        if info.kind == PrivateIdentifierKind::Accessor {
            if ast::is_get_accessor_declaration(&cx.nodes[node]) {
                return info.getter_name;
            }
            if ast::is_set_accessor_declaration(&cx.nodes[node]) {
                return info.setter_name;
            }
        }
        None
    }

    /// `tryGetClassThis`.
    fn try_get_class_this(&self, cx: &VisitorCx<'_, '_>) -> Option<NodeId> {
        if let Some(class_this) = self.try_get_class_this_no_container() {
            return Some(class_this);
        }
        if let Some(container) = self.current_class_container.get() {
            return cx.nodes[container].name();
        }
        None
    }

    /// `tryGetClassThisNoContainer`.
    fn try_get_class_this_no_container(&self) -> Option<NodeId> {
        let lex = self.get_class_lexical_environment();
        let lex = lex.borrow();
        if let Some(class_this) = lex.class_this {
            return Some(class_this);
        }
        lex.class_constructor
    }

    /// `transformAutoAccessor` — transforms `accessor x = 1;` into a private
    /// backing field plus get/set accessors.
    fn transform_auto_accessor(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let comment_range = ec.borrow().comment_range(cx.nodes, node);
        let source_map_range = ec.borrow().source_map_range(cx.nodes, node);

        // Since we're creating two declarations where there was previously one, cache
        // the expression for any computed property names.
        let name = cx.nodes[node].name();
        let mut getter_name = name;
        let mut setter_name = name;
        if let Some(name) = name
            && ast::is_computed_property_name(&cx.nodes[name])
            && !cx.nodes[name]
                .expression()
                .is_some_and(|e| transformer_utilities::is_simple_inlineable_expression(&cx.nodes[e]))
        {
            let cpn_expression = cx.nodes[name].expression();
            let cache_assignment = find_computed_property_name_cache_assignment(cx.nodes, name);
            if let Some(cache_assignment) = cache_assignment {
                let visited_cpn_expression = self.txv(ec).visit_node(cx, cpn_expression);
                getter_name = Some(
                    ec.borrow_mut()
                        .factory
                        .update_computed_property_name(cx.nodes, name, visited_cpn_expression)
                        .unwrap_or(name),
                );
                let left = cx.nodes[cache_assignment].as_binary_expression().left;
                setter_name = Some(
                    ec.borrow_mut()
                        .factory
                        .update_computed_property_name(cx.nodes, name, left)
                        .unwrap_or(name),
                );
            } else {
                let temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                if let Some(expr) = cpn_expression {
                    ec.borrow().set_source_map_range(temp, cx.nodes[expr].loc);
                }
                ec.borrow_mut().add_variable_declaration(cx.nodes, temp);
                let expression = self.txv(ec).visit_node(cx, cpn_expression);
                let assignment = ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    temp,
                    expression.expect("computed name expression"),
                );
                if let Some(expr) = cpn_expression {
                    ec.borrow()
                        .set_source_map_range(assignment, cx.nodes[expr].loc);
                }
                getter_name = Some(
                    ec.borrow_mut()
                        .factory
                        .update_computed_property_name(cx.nodes, name, Some(assignment))
                        .unwrap_or(name),
                );
                setter_name = Some(
                    ec.borrow_mut()
                        .factory
                        .update_computed_property_name(cx.nodes, name, Some(temp))
                        .unwrap_or(name),
                );
            }
        }

        let modifiers = vref!(self, modifier_visitor)
            .visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let initializer = cx.nodes[node].initializer();
        let backing_field = create_accessor_property_backing_field(
            ec,
            cx,
            node,
            modifiers.clone(),
            initializer,
        );
        ec.borrow().set_original(backing_field, node);
        ec.borrow().add_emit_flags(backing_field, EmitFlags::NO_COMMENTS);
        ec.borrow().set_source_map_range(backing_field, source_map_range);

        let receiver = if ast::is_static(&cx.nodes[node]) {
            match self.try_get_class_this(cx) {
                Some(r) => r,
                None => ec.borrow_mut().factory.new_this_expression(cx.nodes),
            }
        } else {
            ec.borrow_mut().factory.new_this_expression(cx.nodes)
        };

        let getter =
            self.create_accessor_property_get_redirector(ec, cx, node, modifiers.clone(), getter_name, receiver);
        ec.borrow().set_original(getter, node);
        ec.borrow().set_comment_range(getter, comment_range);
        ec.borrow().set_source_map_range(getter, source_map_range);

        // create a fresh copy of the modifiers so that we don't duplicate comments
        let setter_modifiers = modifiers.map(|m| {
            let mods = ast::create_modifiers_from_modifier_flags(
                m.modifier_flags,
                &mut |kind| ec.borrow_mut().factory.new_token(cx.nodes, kind),
            );
            ec.borrow_mut().factory.new_modifier_list(&*cx.nodes, mods)
        });
        let setter =
            self.create_accessor_property_set_redirector(ec, cx, node, setter_modifiers, setter_name, receiver);
        ec.borrow().set_original(setter, node);
        ec.borrow().add_emit_flags(setter, EmitFlags::NO_COMMENTS);
        ec.borrow().set_source_map_range(setter, source_map_range);

        // Visit the results in a second pass
        let visited = vref!(self, accessor_field_result_visitor)
            .visit_slice(cx, &[backing_field, getter, setter])
            .unwrap_or_default();
        Some(ec.borrow_mut().factory.new_syntax_list(cx.nodes, &visited))
    }

    /// `transformPrivateFieldInitializer`.
    fn transform_private_field_initializer(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if self.should_transform_class_element_to_weak_map(ec, cx, node) {
            // If we are transforming private elements into WeakMap/WeakSet, we should elide the node.
            let name = cx.nodes[node].name();
            let info = self.get_private_identifier(
                ec,
                cx.nodes,
                &self.get_private_identifier_environment(),
                name.expect("member name"),
            );
            debug_assert!(info.is_some(), "Undeclared private name for property declaration.");
            let Some(info) = info else { return Some(node) };
            let (kind, is_valid, is_static) = {
                let i = info.borrow();
                (i.kind, i.is_valid, i.is_static)
            };

            // Leave invalid code untransformed
            if kind == PrivateIdentifierKind::Untransformed || !is_valid {
                return Some(node);
            }

            // If we encounter a valid private static field and we're not transforming
            // class static blocks, convert to a static block initializer.
            if is_static
                && !self
                    .should_transform_private_elements_or_class_static_blocks
                    .get()
            {
                let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
                let statement = self.transform_property_or_class_static_block(ec, cx, node, this_expr);
                if let Some(statement) = statement {
                    let stmts = ec.borrow_mut().factory.new_node_list([statement]);
                    let block = ec.borrow_mut().factory.new_block(cx.nodes, Some(stmts), true);
                    return Some(ec.borrow_mut().factory.new_class_static_block_declaration(
                        cx.nodes,
                        None,
                        Some(block),
                    ));
                }
            }

            return None;
        }

        if self.should_transform_initializers_using_set.get()
            && !ast::has_static_modifier(&cx.nodes[node])
            && self
                .lexical_data()
                .is_some_and(|d| d.borrow().facts & CLASS_FACTS_WILL_HOIST_INITIALIZERS_TO_CONSTRUCTOR != 0)
        {
            let modifiers = self.txv(ec).visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
            let name = cx.nodes[node].name();
            return Some(
                ec.borrow_mut()
                    .factory
                    .update_property_declaration(
                        cx.nodes,
                        node,
                        modifiers,
                        name,
                        None,
                        None,
                        None,
                    )
                    .unwrap_or(node),
            );
        }

        let node = self.named_evaluation(ec, cx, node, false, "");
        let modifiers = vref!(self, modifier_visitor)
            .visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let name = self.visit_property_name(ec, cx, cx.nodes[node].name());
        let initializer = self.txv(ec).visit_node(cx, cx.nodes[node].initializer());
        Some(
            ec.borrow_mut()
                .factory
                .update_property_declaration(cx.nodes, node, modifiers, name, None, None, initializer)
                .unwrap_or(node),
        )
    }

    /// `transformPublicFieldInitializer`.
    fn transform_public_field_initializer(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if self.should_transform_initializers.get()
            && !ast::is_auto_accessor_property_declaration(&cx.nodes[node])
        {
            // Elide the property declaration; the initializer will be moved to the constructor.
            // For computed property names, we still need to emit the expression.
            let should_hoist = cx.nodes[node].initializer().is_some()
                || self
                    .compiler_options
                    .map(|o| o.get_use_define_for_class_fields())
                    .unwrap_or(false);
            let expr = self.get_property_name_expression_if_needed(
                ec,
                cx,
                cx.nodes[node].name(),
                should_hoist,
            );
            if let Some(expr) = expr {
                for e in flatten_comma_list(cx.nodes, expr) {
                    self.add_pending_expressions(&[e]);
                }
            }

            // When target >= ES2022 and we still need to transform initializers
            // (useDefineForClassFields: false), static property initializers must
            // be converted into `static { this.x = ...; }` blocks.
            if ast::is_static(&cx.nodes[node])
                && !self
                    .should_transform_private_elements_or_class_static_blocks
                    .get()
            {
                let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
                let initializer_statement =
                    self.transform_property_or_class_static_block(ec, cx, node, this_expr);
                if let Some(initializer_statement) = initializer_statement {
                    let stmts = ec
                        .borrow_mut()
                        .factory
                        .new_node_list([initializer_statement]);
                    let block = ec.borrow_mut().factory.new_block(cx.nodes, Some(stmts), false);
                    let static_block = ec.borrow_mut().factory.new_class_static_block_declaration(
                        cx.nodes,
                        None,
                        Some(block),
                    );
                    ec.borrow().set_original(static_block, node);
                    ec.borrow().set_comment_range(static_block, cx.nodes[node].loc);
                    ec.borrow()
                        .add_emit_flags(initializer_statement, EmitFlags::NO_COMMENTS);
                    return Some(static_block);
                }
            }

            return None;
        }

        let modifiers = vref!(self, modifier_visitor)
            .visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let name = self.visit_property_name(ec, cx, cx.nodes[node].name());
        let initializer = self.txv(ec).visit_node(cx, cx.nodes[node].initializer());
        Some(
            ec.borrow_mut()
                .factory
                .update_property_declaration(cx.nodes, node, modifiers, name, None, None, initializer)
                .unwrap_or(node),
        )
    }

    /// `transformFieldInitializer`.
    fn transform_field_initializer(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        debug_assert!(
            !ast::has_decorators(&cx.nodes[node]),
            "Decorators should already have been transformed and elided."
        );
        if ast::is_private_identifier_class_element_declaration(&cx.nodes[node], cx.nodes) {
            return self.transform_private_field_initializer(ec, cx, node);
        }
        self.transform_public_field_initializer(ec, cx, node)
    }

    /// `shouldTransformAutoAccessorsInCurrentClass`.
    fn should_transform_auto_accessors_in_current_class(&self) -> bool {
        if self.should_transform_auto_accessors.get() {
            return true;
        }
        // When targeting ESNext with useDefineForClassFields: false, auto-accessors are only
        // transformed if the current class will hoist initializers to the constructor.
        self.lexical_data()
            .is_some_and(|d| d.borrow().facts & CLASS_FACTS_WILL_HOIST_INITIALIZERS_TO_CONSTRUCTOR != 0)
    }

    /// `visitPropertyDeclaration`.
    fn visit_property_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        // If this is an auto-accessor, we defer to `transformAutoAccessor`. That function
        // will in turn call `transformFieldInitializer` as needed.
        if ast::is_auto_accessor_property_declaration(&cx.nodes[node])
            && (self.should_transform_auto_accessors_in_current_class()
                || (ast::has_static_modifier(&cx.nodes[node])
                    && self.should_always_transform_private_static_elements(ec, cx, node)))
        {
            return self.transform_auto_accessor(ec, cx, node);
        }
        self.transform_field_initializer(ec, cx, node)
    }

    /// `createPrivateIdentifierAccess`.
    fn create_private_identifier_access(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        info: &Rc<RefCell<PrivateIdentifierInfo>>,
        receiver: NodeId,
    ) -> NodeId {
        let receiver = self.txv(ec).visit_node(cx, Some(receiver)).expect("receiver");
        self.create_private_identifier_access_helper(ec, cx, info, receiver)
    }

    /// `createPrivateIdentifierAccessHelper`.
    fn create_private_identifier_access_helper(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        info: &Rc<RefCell<PrivateIdentifierInfo>>,
        receiver: NodeId,
    ) -> NodeId {
        ec.borrow().set_comment_range(
            receiver,
            tsc_core::text::TextRange::new(-1, cx.nodes[receiver].end()),
        );
        let info = info.borrow();
        match info.kind {
            PrivateIdentifierKind::Accessor => {
                ec.borrow_mut().factory.new_class_private_field_get_helper(
                    cx.nodes,
                    receiver,
                    info.brand_check_identifier.expect("brandCheckIdentifier"),
                    info.kind,
                    info.getter_name,
                )
            }
            PrivateIdentifierKind::Method => {
                ec.borrow_mut().factory.new_class_private_field_get_helper(
                    cx.nodes,
                    receiver,
                    info.brand_check_identifier.expect("brandCheckIdentifier"),
                    info.kind,
                    info.method_name,
                )
            }
            PrivateIdentifierKind::Field => {
                let f = if info.is_static { info.variable_name } else { None };
                ec.borrow_mut().factory.new_class_private_field_get_helper(
                    cx.nodes,
                    receiver,
                    info.brand_check_identifier.expect("brandCheckIdentifier"),
                    info.kind,
                    f,
                )
            }
            PrivateIdentifierKind::Untransformed => {
                panic!("Access helpers should not be created for untransformed private elements")
            }
        }
    }

    /// `visitPropertyAccessExpression`.
    fn visit_property_access_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, name, question_dot_token, flags) = {
            let pa = cx.nodes[node].as_property_access_expression();
            (pa.expression, pa.name, pa.question_dot_token, cx.nodes[node].flags)
        };
        if name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])) {
            if let Some(info) = self.access_private_identifier(ec, cx, name.expect("name")) {
                let result = self.create_private_identifier_access(
                    ec,
                    cx,
                    &info,
                    expression.expect("access expression"),
                );
                ec.borrow().set_original(result, node);
                cx.nodes[result].loc = cx.nodes[node].loc;
                return result;
            }
        }
        if self.should_transform_super_in_static_initializers.get()
            && self.current_class_element.get().is_some()
            && ast::is_super_property(&cx.nodes[node], cx.nodes)
            && name.is_some_and(|n| ast::is_identifier(&cx.nodes[n]))
            && is_static_property_declaration_or_class_static_block(
                &cx.nodes[self.current_class_element.get().unwrap()],
            )
            && self.lexical_data().is_some()
        {
            let data = self.lexical_data().unwrap();
            let data = data.borrow();
            if data.facts & CLASS_FACTS_CLASS_WAS_DECORATED != 0 {
                return self.visit_invalid_super_property(ec, cx, node);
            }
            if let (Some(class_constructor), Some(super_class_reference)) =
                (data.class_constructor, data.super_class_reference)
            {
                // converts `super.x` into `Reflect.get(_baseTemp, "x", _classTemp)`
                let property_name = ec.borrow_mut().factory.new_string_literal_from_node(
                    cx.nodes,
                    name.expect("name"),
                );
                let super_property = ec.borrow_mut().factory.new_reflect_get_call(
                    cx.nodes,
                    super_class_reference,
                    property_name,
                    class_constructor,
                );
                if let Some(expression) = expression {
                    ec.borrow().set_original(super_property, expression);
                    cx.nodes[super_property].loc = cx.nodes[expression].loc;
                }
                return super_property;
            }
        }
        // Visit only the expression, not the name (when it's a regular identifier), to prevent
        // substitution of property names. Private identifier names are still visited through
        // VisitEachChild so they can be transformed by visitPrivateIdentifier.
        let _ = (question_dot_token, flags);
        if name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
            return self.visit_property_access_expression_for_substitution(ec, cx, node);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitPropertyAccessExpressionForSubstitution`.
    fn visit_property_access_expression_for_substitution(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, question_dot_token, name, flags) = {
            let pa = cx.nodes[node].as_property_access_expression();
            (
                pa.expression,
                pa.question_dot_token,
                pa.name,
                cx.nodes[node].flags,
            )
        };
        let visited = self.txv(ec).visit_node(cx, expression);
        if visited != expression {
            return ec
                .borrow_mut()
                .factory
                .update_property_access_expression(
                    cx.nodes,
                    node,
                    visited,
                    question_dot_token,
                    name,
                    flags,
                )
                .unwrap_or(node);
        }
        node
    }

    /// `visitElementAccessExpression`.
    fn visit_element_access_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, argument_expression) = {
            let ea = cx.nodes[node].as_element_access_expression();
            (ea.expression, ea.argument_expression)
        };
        if self.should_transform_super_in_static_initializers.get()
            && self.current_class_element.get().is_some()
            && ast::is_super_property(&cx.nodes[node], cx.nodes)
            && is_static_property_declaration_or_class_static_block(
                &cx.nodes[self.current_class_element.get().unwrap()],
            )
            && self.lexical_data().is_some()
        {
            let data = self.lexical_data().unwrap();
            let data = data.borrow();
            if data.facts & CLASS_FACTS_CLASS_WAS_DECORATED != 0 {
                return self.visit_invalid_super_property(ec, cx, node);
            }
            if let (Some(class_constructor), Some(super_class_reference)) =
                (data.class_constructor, data.super_class_reference)
            {
                // converts `super[x]` into `Reflect.get(_baseTemp, x, _classTemp)`
                let visited_arg = self.txv(ec).visit_node(cx, argument_expression);
                let super_property = ec.borrow_mut().factory.new_reflect_get_call(
                    cx.nodes,
                    super_class_reference,
                    visited_arg.expect("element argument"),
                    class_constructor,
                );
                if let Some(expression) = expression {
                    ec.borrow().set_original(super_property, expression);
                    cx.nodes[super_property].loc = cx.nodes[expression].loc;
                }
                return super_property;
            }
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitPreOrPostfixUnaryExpression`.
    fn visit_pre_or_postfix_unary_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        discarded: bool,
    ) -> NodeId {
        let is_prefix = ast::is_prefix_unary_expression(&cx.nodes[node]);
        let (operator, operand_node) = if is_prefix {
            let p = cx.nodes[node].as_prefix_unary_expression();
            (p.operator, p.operand)
        } else {
            let p = cx.nodes[node].as_postfix_unary_expression();
            (p.operator, p.operand)
        };

        if operator == Kind::PlusPlusToken || operator == Kind::MinusMinusToken {
            let operand_skipped = ast::skip_parentheses(operand_node.expect("operand"), cx.nodes);

            // Private identifier property access
            if ast::is_property_access_expression(&cx.nodes[operand_skipped])
                && ast::is_private_identifier(
                    &cx.nodes[cx.nodes[operand_skipped]
                        .as_property_access_expression()
                        .name
                        .expect("property access name")],
                )
            {
                let name = cx.nodes[operand_skipped]
                    .as_property_access_expression()
                    .name
                    .expect("property access name");
                if let Some(info) = self.access_private_identifier(ec, cx, name) {
                    let receiver_expr = cx.nodes[operand_skipped]
                        .as_property_access_expression()
                        .expression;
                    let receiver = self.txv(ec).visit_node(cx, receiver_expr);
                    let (read_expression, initialize_expression) = self
                        .create_copiable_receiver_expr(
                            ec,
                            cx,
                            receiver.expect("receiver"),
                        );

                    let mut expression = self.create_private_identifier_access_helper(
                        ec,
                        cx,
                        &info,
                        read_expression,
                    );
                    let mut temp: Option<NodeId> = None;
                    if !is_prefix && !discarded {
                        temp = Some(ec.borrow_mut().factory.new_temp_variable(cx.nodes));
                        ec.borrow_mut().add_variable_declaration(cx.nodes, temp.unwrap());
                    }
                    expression = expand_pre_or_postfix_increment_or_decrement_expression(
                        ec, cx, node, expression, temp,
                    );
                    let assign_receiver = initialize_expression.unwrap_or(read_expression);
                    expression = self.create_private_identifier_assignment(
                        ec,
                        cx,
                        &info,
                        assign_receiver,
                        expression,
                        Kind::EqualsToken,
                    );
                    ec.borrow().set_original(expression, node);
                    cx.nodes[expression].loc = cx.nodes[node].loc;
                    if let Some(temp) = temp {
                        expression = ec.borrow_mut().factory.new_comma_expression(
                            cx.nodes,
                            expression,
                            temp,
                        );
                        cx.nodes[expression].loc = cx.nodes[node].loc;
                    }
                    return expression;
                }
            } else if self.should_transform_super_in_static_initializers.get()
                && self.current_class_element.get().is_some()
                && ast::is_super_property(&cx.nodes[operand_skipped], cx.nodes)
                && is_static_property_declaration_or_class_static_block(
                    &cx.nodes[self.current_class_element.get().unwrap()],
                )
                && self.lexical_data().is_some()
            {
                let data = self.lexical_data().unwrap();
                let (facts, class_constructor, super_class_reference) = {
                    let d = data.borrow();
                    (d.facts, d.class_constructor, d.super_class_reference)
                };
                if facts & CLASS_FACTS_CLASS_WAS_DECORATED != 0 {
                    let visited_expr = self.visit_invalid_super_property(ec, cx, operand_skipped);
                    if is_prefix {
                        return ec
                            .borrow_mut()
                            .factory
                            .update_prefix_unary_expression(
                                cx.nodes,
                                node,
                                cx.nodes[node].as_prefix_unary_expression().operator,
                                Some(visited_expr),
                            )
                            .unwrap_or(node);
                    }
                    return ec
                        .borrow_mut()
                        .factory
                        .update_postfix_unary_expression(
                            cx.nodes,
                            node,
                            Some(visited_expr),
                            cx.nodes[node].as_postfix_unary_expression().operator,
                        )
                        .unwrap_or(node);
                }
                if let (Some(class_constructor), Some(super_class_reference)) =
                    (class_constructor, super_class_reference)
                {
                    // converts `++super.a` into `(Reflect.set(_baseTemp, "a", (_a = Reflect.get(_baseTemp, "a", _classTemp), _b = ++_a), _classTemp), _b)`
                    // (and equivalents for `super[f()]`, `--`, and postfix)
                    let mut setter_name: Option<NodeId> = None;
                    let mut getter_name: Option<NodeId> = None;
                    if ast::is_property_access_expression(&cx.nodes[operand_skipped])
                        && ast::is_identifier(
                            &cx.nodes[cx.nodes[operand_skipped]
                                .as_property_access_expression()
                                .name
                                .expect("property access name")],
                        )
                    {
                        getter_name = Some(
                            ec.borrow_mut().factory.new_string_literal_from_node(
                                cx.nodes,
                                cx.nodes[operand_skipped]
                                    .as_property_access_expression()
                                    .name
                                    .expect("property access name"),
                            ),
                        );
                        setter_name = getter_name;
                    } else if ast::is_element_access_expression(&cx.nodes[operand_skipped]) {
                        let arg = cx.nodes[operand_skipped]
                            .as_element_access_expression()
                            .argument_expression;
                        if arg.is_some_and(|a| {
                            transformer_utilities::is_simple_inlineable_expression(&cx.nodes[a])
                        }) {
                            getter_name = arg;
                            setter_name = getter_name;
                        } else {
                            let temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                            ec.borrow_mut().add_variable_declaration(cx.nodes, temp);
                            getter_name = Some(temp);
                            let visited_arg = self.txv(ec).visit_node(cx, arg);
                            setter_name = Some(ec.borrow_mut().factory.new_assignment_expression(
                                cx.nodes,
                                temp,
                                visited_arg.expect("element argument"),
                            ));
                        }
                    }
                    if let (Some(setter_name), Some(getter_name)) = (setter_name, getter_name) {
                        let mut expression = ec.borrow_mut().factory.new_reflect_get_call(
                            cx.nodes,
                            super_class_reference,
                            getter_name,
                            class_constructor,
                        );
                        cx.nodes[expression].loc = cx.nodes[operand_skipped].loc;

                        let mut temp: Option<NodeId> = None;
                        if !discarded {
                            temp = Some(ec.borrow_mut().factory.new_temp_variable(cx.nodes));
                            ec.borrow_mut()
                                .add_variable_declaration(cx.nodes, temp.unwrap());
                        }
                        expression = expand_pre_or_postfix_increment_or_decrement_expression(
                            ec, cx, node, expression, temp,
                        );
                        expression = ec.borrow_mut().factory.new_reflect_set_call(
                            cx.nodes,
                            super_class_reference,
                            setter_name,
                            expression,
                            class_constructor,
                        );
                        ec.borrow().set_original(expression, node);
                        cx.nodes[expression].loc = cx.nodes[node].loc;
                        if let Some(temp) = temp {
                            expression = ec.borrow_mut().factory.new_comma_expression(
                                cx.nodes,
                                expression,
                                temp,
                            );
                            cx.nodes[expression].loc = cx.nodes[node].loc;
                        }
                        return expression;
                    }
                }
            }
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitForStatement`.
    fn visit_for_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (initializer, condition, incrementor, statement) = {
            let d = cx.nodes[node].as_for_statement();
            (
                d.initializer,
                d.condition,
                d.incrementor,
                d.iteration_statement_base.statement,
            )
        };
        let txv = self.txv(ec);
        let visited_initializer =
            vref!(self, discarded_value_visitor).visit_node(cx, initializer);
        let visited_condition = txv.visit_node(cx, condition);
        let visited_incrementor =
            vref!(self, discarded_value_visitor).visit_node(cx, incrementor);
        let saved = self.in_iteration_statement.replace(true);
        let visited_statement = ec_visit_iteration_body(&txv, cx, statement);
        self.in_iteration_statement.set(saved);
        ec.borrow_mut()
            .factory
            .update_for_statement(
                cx.nodes,
                node,
                visited_initializer,
                visited_condition,
                visited_incrementor,
                visited_statement,
            )
            .unwrap_or(node)
    }

    /// `visitExpressionStatement`.
    fn visit_expression_statement(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // Preserve private identifiers that appear directly as the expression of an
        // ExpressionStatement (e.g., `#;`). This is error-recovery output from the parser.
        let expression = cx.nodes[node].expression();
        if expression.is_some_and(|e| ast::is_private_identifier(&cx.nodes[e]))
            && self
                .should_transform_private_elements_or_class_static_blocks
                .get()
        {
            return node;
        }
        let visited = vref!(self, discarded_value_visitor).visit_node(cx, expression);
        ec.borrow_mut()
            .factory
            .update_expression_statement(cx.nodes, node, visited)
            .unwrap_or(node)
    }

    /// `createCopiableReceiverExpr` — returns `(readExpression, initializeExpression)`.
    fn create_copiable_receiver_expr(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        receiver: NodeId,
    ) -> (NodeId, Option<NodeId>) {
        let mut clone = receiver;
        if !ast::node_is_synthesized(&cx.nodes[receiver]) {
            clone = ec.borrow_mut().factory.clone_node(cx.nodes, receiver);
        }
        if transformer_utilities::is_simple_inlineable_expression(&cx.nodes[receiver]) {
            return (clone, None);
        }
        let read_expression = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, read_expression);
        let initialize_expression = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            read_expression,
            clone,
        );
        (read_expression, Some(initialize_expression))
    }

    /// `visitCallExpression`.
    fn visit_call_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, question_dot_token, arguments, flags) = {
            let call = cx.nodes[node].as_call_expression();
            (
                call.expression,
                call.question_dot_token,
                call.arguments.clone(),
                cx.nodes[node].flags,
            )
        };
        if expression.is_some_and(|e| {
            ast::is_property_access_expression(&cx.nodes[e])
                && ast::is_private_identifier(
                    &cx.nodes[cx.nodes[e]
                        .as_property_access_expression()
                        .name
                        .expect("property access name")],
                )
        }) {
            let callee = expression.expect("call expression");
            let callee_name = cx.nodes[callee]
                .as_property_access_expression()
                .name
                .expect("property access name");
            if self.access_private_identifier(ec, cx, callee_name).is_some() {
                // obj.#x()
                // Transform call expressions of private names to properly bind `this`.
                let (this_arg, target) = self.create_call_binding(ec, cx, callee);
                let visited_target = self.txv(ec).visit_node(cx, Some(target));
                let visited_this_arg = self.txv(ec).visit_node(cx, Some(this_arg));
                let visited_args = self.txv(ec).visit_nodes(cx, arguments);
                let mut all_args: Vec<NodeId> =
                    Vec::with_capacity(1 + visited_args.as_ref().map(|a| a.len()).unwrap_or(0));
                all_args.push(visited_this_arg.expect("thisArg"));
                if let Some(visited_args) = visited_args {
                    all_args.extend(visited_args.nodes.iter().copied());
                }
                let call_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "call");
                let access_flags = if flags & NodeFlags::OPTIONAL_CHAIN != NodeFlags::NONE {
                    NodeFlags::OPTIONAL_CHAIN
                } else {
                    NodeFlags::NONE
                };
                let call_access = ec.borrow_mut().factory.new_property_access_expression(
                    cx.nodes,
                    visited_target,
                    if access_flags == NodeFlags::OPTIONAL_CHAIN {
                        question_dot_token
                    } else {
                        None
                    },
                    Some(call_ident),
                    access_flags,
                );
                let args_list = ec.borrow_mut().factory.new_node_list(all_args);
                return ec
                    .borrow_mut()
                    .factory
                    .update_call_expression(
                        cx.nodes,
                        node,
                        Some(call_access),
                        None,
                        None,
                        Some(args_list),
                        flags,
                    )
                    .unwrap_or(node);
            }
        }

        if self.should_transform_super_in_static_initializers.get()
            && self.current_class_element.get().is_some()
            && expression.is_some_and(|e| ast::is_super_property(&cx.nodes[e], cx.nodes))
            && is_static_property_declaration_or_class_static_block(
                &cx.nodes[self.current_class_element.get().unwrap()],
            )
            && self.lexical_data().is_some()
            && self.lexical_data().unwrap().borrow().class_constructor.is_some()
        {
            let class_constructor = self
                .lexical_data()
                .unwrap()
                .borrow()
                .class_constructor
                .unwrap();
            // super.x()
            // super[x]()
            // converts `super.f(...)` into `Reflect.get(_baseTemp, "f", _classTemp).call(_classTemp, ...)`
            let visited_expr = self.txv(ec).visit_node(cx, expression);
            let visited_args = self.txv(ec).visit_nodes(cx, arguments);
            let args: Vec<NodeId> = visited_args
                .map(|a| a.nodes.to_vec())
                .unwrap_or_default();
            let invocation = ec.borrow_mut().factory.new_function_call_call(
                cx.nodes,
                visited_expr.expect("call expression"),
                Some(class_constructor),
                args,
            );
            ec.borrow().set_original(invocation, node);
            cx.nodes[invocation].loc = cx.nodes[node].loc;
            return invocation;
        }

        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitTaggedTemplateExpression`.
    fn visit_tagged_template_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (tag, template, flags) = {
            let tte = cx.nodes[node].as_tagged_template_expression();
            (tte.tag, tte.template, cx.nodes[node].flags)
        };
        if tag.is_some_and(|t| {
            ast::is_property_access_expression(&cx.nodes[t])
                && ast::is_private_identifier(
                    &cx.nodes[cx.nodes[t]
                        .as_property_access_expression()
                        .name
                        .expect("property access name")],
                )
        }) {
            let tag_node = tag.expect("tag");
            let tag_name = cx.nodes[tag_node]
                .as_property_access_expression()
                .name
                .expect("property access name");
            if self.access_private_identifier(ec, cx, tag_name).is_some() {
                // Bind the `this` correctly for tagged template literals.
                let (this_arg, target) = self.create_call_binding(ec, cx, tag_node);
                let visited_target = self.txv(ec).visit_node(cx, Some(target));
                let bind_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "bind");
                let bind_access = ec.borrow_mut().factory.new_property_access_expression(
                    cx.nodes,
                    visited_target,
                    None,
                    Some(bind_ident),
                    NodeFlags::NONE,
                );
                let visited_this_arg = self.txv(ec).visit_node(cx, Some(this_arg));
                let args = ec
                    .borrow_mut()
                    .factory
                    .new_node_list([visited_this_arg.expect("thisArg")]);
                let bind_expr = ec.borrow_mut().factory.new_call_expression(
                    cx.nodes,
                    Some(bind_access),
                    None,
                    None,
                    Some(args),
                    NodeFlags::NONE,
                );
                let visited_template = self.txv(ec).visit_node(cx, template);
                return ec
                    .borrow_mut()
                    .factory
                    .update_tagged_template_expression(
                        cx.nodes,
                        node,
                        Some(bind_expr),
                        None,
                        None,
                        visited_template,
                        flags,
                    )
                    .unwrap_or(node);
            }
        }

        if self.should_transform_super_in_static_initializers.get()
            && self.current_class_element.get().is_some()
            && tag.is_some_and(|t| ast::is_super_property(&cx.nodes[t], cx.nodes))
            && is_static_property_declaration_or_class_static_block(
                &cx.nodes[self.current_class_element.get().unwrap()],
            )
            && self.lexical_data().is_some()
            && self.lexical_data().unwrap().borrow().class_constructor.is_some()
        {
            let class_constructor = self
                .lexical_data()
                .unwrap()
                .borrow()
                .class_constructor
                .unwrap();
            // converts `` super.f`x` `` into `` Reflect.get(_baseTemp, "f", _classTemp).bind(_classTemp)`x` ``
            let visited_tag = self.txv(ec).visit_node(cx, tag);
            let invocation = ec.borrow_mut().factory.new_function_bind_call(
                cx.nodes,
                visited_tag.expect("tag"),
                class_constructor,
                vec![],
            );
            ec.borrow().set_original(invocation, node);
            cx.nodes[invocation].loc = cx.nodes[node].loc;
            let visited_template = self.txv(ec).visit_node(cx, template);
            return ec
                .borrow_mut()
                .factory
                .update_tagged_template_expression(
                    cx.nodes,
                    node,
                    Some(invocation),
                    None,
                    None,
                    visited_template,
                    flags,
                )
                .unwrap_or(node);
        }

        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `transformClassStaticBlockDeclaration`.
    fn transform_class_static_block_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if !self
            .should_transform_private_elements_or_class_static_blocks
            .get()
        {
            return None;
        }

        if is_class_this_assignment_block(&ec.borrow(), cx.nodes, node) {
            let body = cx.nodes[node]
                .as_class_static_block_declaration()
                .body
                .expect("static block body");
            let first = cx.nodes[body].as_block().statements.as_ref().expect("statements").nodes[0];
            let result = self.txv(ec).visit_node(cx, cx.nodes[first].expression());
            // If the generated `_classThis` assignment is a noop (i.e., `_classThis = _classThis`), we can
            // eliminate the expression
            if let Some(result) = result
                && ast::is_assignment_expression(&cx.nodes[result], cx.nodes, true)
            {
                let bin = cx.nodes[result].as_binary_expression();
                if bin.left == bin.right {
                    return None;
                }
            }
            return result;
        }

        if is_class_named_evaluation_helper_block(&ec.borrow(), cx.nodes, node) {
            let body = cx.nodes[node]
                .as_class_static_block_declaration()
                .body
                .expect("static block body");
            let first = cx.nodes[body].as_block().statements.as_ref().expect("statements").nodes[0];
            return self.txv(ec).visit_node(cx, cx.nodes[first].expression());
        }

        ec.borrow_mut().start_variable_environment();
        let body = cx.nodes[node]
            .as_class_static_block_declaration()
            .body
            .expect("static block body");
        let stmts: Vec<NodeId> = cx.nodes[body]
            .as_block()
            .statements
            .as_ref()
            .map(|l| l.nodes.to_vec())
            .unwrap_or_default();
        let stmts_loc = cx.nodes[body]
            .as_block()
            .statements
            .as_ref()
            .map(|l| l.loc)
            .unwrap_or_default();
        let statements = self.set_current_class_element_and_visit_statements(
            ec,
            cx,
            node,
            &stmts,
        );
        let statements = ec
            .borrow_mut()
            .end_and_merge_variable_environment(cx.nodes, &statements);

        let iife = ec
            .borrow_mut()
            .factory
            .new_immediately_invoked_arrow_function(cx.nodes, statements);
        let arrow_function = ast::skip_parentheses(
            cx.nodes[iife].expression().expect("iife expression"),
            cx.nodes,
        );
        ec.borrow().set_original(arrow_function, node);
        ec.borrow()
            .add_emit_flags(arrow_function, EmitFlags::NO_LEXICAL_ARGUMENTS);
        // Preserve the statement list source range so the printer can emit detached comments
        if let Some(arrow_body) = cx.nodes[arrow_function].body()
            && let Some(stmts_list) = cx.nodes[arrow_body]
                .as_block_mut()
                .statements
                .as_mut()
        {
            stmts_list.loc = stmts_loc;
        }
        ec.borrow().set_original(iife, node);
        ec.borrow().assign_source_map_range(cx.nodes, iife, node);
        ec.borrow()
            .add_emit_flags(arrow_function, EmitFlags::NO_LEXICAL_THIS);
        Some(iife)
    }

    /// `setCurrentClassElementAndVisitStatements`.
    fn set_current_class_element_and_visit_statements(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        class_element: NodeId,
        statements: &[NodeId],
    ) -> Vec<NodeId> {
        let saved = self.current_class_element.replace(Some(class_element));
        let result = self.txv(ec).visit_slice(cx, statements).unwrap_or_default();
        self.current_class_element.set(saved);
        result
    }

    /// `isAnonymousClassNeedingAssignedName`.
    fn is_anonymous_class_needing_assigned_name(
        &self,
        ec: &Ec,
        nodes: &[tsc_ast::Node],
        node: NodeId,
    ) -> bool {
        if ast::is_class_expression(&nodes[node]) && nodes[node].name().is_none() {
            let static_properties_or_class_static_blocks =
                self.get_static_properties_and_class_static_block(nodes, node);
            if static_properties_or_class_static_blocks.iter().any(|&n| {
                // `named_evaluation` invokes this predicate while `ec` is
                // shared-borrowed via `is_named_evaluation_and`; a nested
                // shared borrow is safe.
                is_class_named_evaluation_helper_block(&ec.borrow(), nodes, n)
            }) {
                return false;
            }
            let has_transformable_statics = (self
                .should_transform_private_elements_or_class_static_blocks
                .get()
                || self.node_has_transform_private_static_elements_flag(ec, node))
                && static_properties_or_class_static_blocks.iter().any(|&n| {
                    ast::is_class_static_block_declaration(&nodes[n])
                        || ast::is_private_identifier_class_element_declaration(&nodes[n], nodes)
                        || (self.should_transform_initializers.get()
                            && ast::is_initialized_property(&nodes[n]))
                });
            return has_transformable_statics;
        }
        false
    }

    /// `visitBinaryExpression`.
    fn visit_binary_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        discarded: bool,
    ) -> NodeId {
        if ast::is_destructuring_assignment(&cx.nodes[node], cx.nodes) {
            // ({ x: obj.#x } = ...)
            // ({ x: super.x } = ...)
            // ({ x: super[x] } = ...)
            let saved_pending_expressions: Vec<NodeId> =
                std::mem::take(&mut *self.pending_expressions.borrow_mut());
            let (left, operator_token, right) = {
                let bin = cx.nodes[node].as_binary_expression();
                (bin.left, bin.operator_token, bin.right)
            };
            let visited_left =
                vref!(self, assignment_target_visitor).visit_node(cx, left);
            let visited_right = self.txv(ec).visit_node(cx, right);
            let updated = ec
                .borrow_mut()
                .factory
                .update_binary_expression(
                    cx.nodes,
                    node,
                    None,
                    visited_left,
                    None,
                    operator_token,
                    visited_right,
                )
                .unwrap_or(node);
            let pending = self.pending_expressions.borrow().clone();
            let result = if !pending.is_empty() {
                let mut exprs = pending;
                exprs.push(updated);
                ec.borrow_mut()
                    .factory
                    .inline_expressions(cx.nodes, &exprs)
                    .unwrap_or(updated)
            } else {
                updated
            };
            *self.pending_expressions.borrow_mut() = saved_pending_expressions;
            return result;
        }

        if ast::is_assignment_expression(&cx.nodes[node], cx.nodes, false) {
            // 13.15.2 RS: Evaluation — see esdecorator.rs for the full comment.
            let node = self.named_evaluation(ec, cx, node, false, "");
            debug_assert!(ast::is_assignment_expression(&cx.nodes[node], cx.nodes, false));

            let (left, operator_token, right) = {
                let bin = cx.nodes[node].as_binary_expression();
                (bin.left, bin.operator_token, bin.right)
            };
            let left_skipped = ast::skip_outer_expressions(
                left.expect("assignment lhs"),
                ast::outer_expression_kinds::PARTIALLY_EMITTED_EXPRESSIONS
                    | ast::outer_expression_kinds::PARENTHESES,
                cx.nodes,
            );
            if ast::is_property_access_expression(&cx.nodes[left_skipped])
                && ast::is_private_identifier(
                    &cx.nodes[cx.nodes[left_skipped]
                        .as_property_access_expression()
                        .name
                        .expect("property access name")],
                )
            {
                // obj.#x = ...
                let name = cx.nodes[left_skipped]
                    .as_property_access_expression()
                    .name
                    .expect("property access name");
                if let Some(info) = self.access_private_identifier(ec, cx, name) {
                    let receiver = cx.nodes[left_skipped]
                        .as_property_access_expression()
                        .expression
                        .expect("receiver");
                    let result = self.create_private_identifier_assignment(
                        ec,
                        cx,
                        &info,
                        receiver,
                        right.expect("assignment rhs"),
                        operator_token.map(|t| cx.nodes[t].kind).unwrap_or(Kind::EqualsToken),
                    );
                    ec.borrow().set_original(result, node);
                    cx.nodes[result].loc = cx.nodes[node].loc;
                    return result;
                }
            } else if self.should_transform_super_in_static_initializers.get()
                && self.current_class_element.get().is_some()
                && ast::is_super_property(&cx.nodes[left.unwrap()], cx.nodes)
                && is_static_property_declaration_or_class_static_block(
                    &cx.nodes[self.current_class_element.get().unwrap()],
                )
                && self.lexical_data().is_some()
            {
                let data = self.lexical_data().unwrap();
                let (facts, class_constructor, super_class_reference) = {
                    let d = data.borrow();
                    (d.facts, d.class_constructor, d.super_class_reference)
                };
                // super.x = ...
                // super[x] = ...
                // super.x += ...
                if facts & CLASS_FACTS_CLASS_WAS_DECORATED != 0 {
                    let visited_left = self.visit_invalid_super_property(ec, cx, left.unwrap());
                    let visited_right = self.txv(ec).visit_node(cx, right);
                    return ec
                        .borrow_mut()
                        .factory
                        .update_binary_expression(
                            cx.nodes,
                            node,
                            None,
                            Some(visited_left),
                            None,
                            operator_token,
                            visited_right,
                        )
                        .unwrap_or(node);
                }
                if let (Some(class_constructor), Some(super_class_reference)) =
                    (class_constructor, super_class_reference)
                {
                    let mut setter_name: Option<NodeId> = None;
                    let left = left.unwrap();
                    if ast::is_element_access_expression(&cx.nodes[left]) {
                        let arg = cx.nodes[left]
                            .as_element_access_expression()
                            .argument_expression;
                        setter_name = self.txv(ec).visit_node(cx, arg);
                    } else if ast::is_property_access_expression(&cx.nodes[left])
                        && ast::is_identifier(
                            &cx.nodes[cx.nodes[left]
                                .as_property_access_expression()
                                .name
                                .expect("property access name")],
                        )
                    {
                        setter_name = Some(ec.borrow_mut().factory.new_string_literal_from_node(
                            cx.nodes,
                            cx.nodes[left]
                                .as_property_access_expression()
                                .name
                                .expect("property access name"),
                        ));
                    }
                    if let Some(mut setter_name) = setter_name {
                        // converts `super.x = 1` into `(Reflect.set(_baseTemp, "x", _a = 1, _classTemp), _a)`
                        // converts `super[f()] += 1` into `(Reflect.set(_baseTemp, _a = f(), _b = Reflect.get(_baseTemp, _a, _classtemp) + 1, _classTemp), _b)`
                        let mut expression = self.txv(ec).visit_node(cx, right);
                        let operator_kind = operator_token.map(|t| cx.nodes[t].kind);
                        if operator_kind.is_some_and(|k| ast::is_compound_assignment(k)) {
                            let mut getter_name = setter_name;
                            if !transformer_utilities::is_simple_inlineable_expression(
                                &cx.nodes[setter_name],
                            ) {
                                getter_name =
                                    ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                                ec.borrow_mut()
                                    .add_variable_declaration(cx.nodes, getter_name);
                                setter_name = ec.borrow_mut().factory.new_assignment_expression(
                                    cx.nodes,
                                    getter_name,
                                    setter_name,
                                );
                            }
                            let super_property_get = ec.borrow_mut().factory.new_reflect_get_call(
                                cx.nodes,
                                super_class_reference,
                                getter_name,
                                class_constructor,
                            );
                            ec.borrow().set_original(super_property_get, left);
                            cx.nodes[super_property_get].loc = cx.nodes[left].loc;
                            let op_token = ec.borrow_mut().factory.new_token(
                                cx.nodes,
                                transformer_utilities::get_non_assignment_operator_for_compound_assignment(
                                    operator_kind.expect("compound operator"),
                                ),
                            );
                            expression = Some(ec.borrow_mut().factory.new_binary_expression(
                                cx.nodes,
                                None,
                                Some(super_property_get),
                                None,
                                Some(op_token),
                                expression,
                            ));
                            if let Some(e) = expression {
                                cx.nodes[e].loc = cx.nodes[node].loc;
                            }
                        }

                        let mut temp: Option<NodeId> = None;
                        if !discarded {
                            temp = Some(ec.borrow_mut().factory.new_temp_variable(cx.nodes));
                            ec.borrow_mut()
                                .add_variable_declaration(cx.nodes, temp.unwrap());
                        }
                        if let Some(temp) = temp {
                            expression = Some(ec.borrow_mut().factory.new_assignment_expression(
                                cx.nodes,
                                temp,
                                expression.expect("expression"),
                            ));
                            if let Some(e) = expression {
                                cx.nodes[e].loc = cx.nodes[node].loc;
                            }
                        }

                        let mut expression = ec.borrow_mut().factory.new_reflect_set_call(
                            cx.nodes,
                            super_class_reference,
                            setter_name,
                            expression.expect("expression"),
                            class_constructor,
                        );
                        ec.borrow().set_original(expression, node);
                        cx.nodes[expression].loc = cx.nodes[node].loc;

                        if let Some(temp) = temp {
                            expression = ec.borrow_mut().factory.new_comma_expression(
                                cx.nodes,
                                expression,
                                temp,
                            );
                            cx.nodes[expression].loc = cx.nodes[node].loc;
                        }
                        return expression;
                    }
                }
            }
        }

        let (left, operator_token, _right) = {
            let bin = cx.nodes[node].as_binary_expression();
            (bin.left, bin.operator_token, bin.right)
        };
        if operator_token.map(|t| cx.nodes[t].kind) == Some(Kind::InKeyword)
            && left.is_some_and(|l| ast::is_private_identifier(&cx.nodes[l]))
        {
            // #x in obj
            return self.transform_private_identifier_in_in_expression(ec, cx, node);
        }

        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitParenthesizedExpression`.
    fn visit_parenthesized_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        discarded: bool,
    ) -> NodeId {
        // 8.4.5 RS: NamedEvaluation
        let expression = cx.nodes[node].as_parenthesized_expression().expression;
        let expression = if discarded {
            vref!(self, discarded_value_visitor).visit_node(cx, expression)
        } else {
            self.txv(ec).visit_node(cx, expression)
        };
        ec.borrow_mut()
            .factory
            .update_parenthesized_expression(cx.nodes, node, expression)
            .unwrap_or(node)
    }

    /// `createPrivateIdentifierAssignment`.
    fn create_private_identifier_assignment(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        info: &Rc<RefCell<PrivateIdentifierInfo>>,
        receiver: NodeId,
        right: NodeId,
        operator: Kind,
    ) -> NodeId {
        let receiver = self.txv(ec).visit_node(cx, Some(receiver)).expect("receiver");
        let mut right = self.txv(ec).visit_node(cx, Some(right)).expect("right");

        let mut receiver = receiver;
        if ast::is_compound_assignment(operator) {
            let (read_expression, initialize_expression) =
                self.create_copiable_receiver_expr(ec, cx, receiver);
            receiver = initialize_expression.unwrap_or(read_expression);
            let access =
                self.create_private_identifier_access_helper(ec, cx, info, read_expression);
            let op_token = ec.borrow_mut().factory.new_token(
                cx.nodes,
                transformer_utilities::get_non_assignment_operator_for_compound_assignment(
                    operator,
                ),
            );
            right = ec.borrow_mut().factory.new_binary_expression(
                cx.nodes,
                None,
                Some(access),
                None,
                Some(op_token),
                Some(right),
            );
        }

        ec.borrow().set_comment_range(
            receiver,
            tsc_core::text::TextRange::new(-1, cx.nodes[receiver].end()),
        );

        let info = info.borrow();
        match info.kind {
            PrivateIdentifierKind::Accessor => {
                ec.borrow_mut().factory.new_class_private_field_set_helper(
                    cx.nodes,
                    receiver,
                    info.brand_check_identifier.expect("brandCheckIdentifier"),
                    right,
                    info.kind,
                    info.setter_name,
                )
            }
            PrivateIdentifierKind::Method => {
                ec.borrow_mut().factory.new_class_private_field_set_helper(
                    cx.nodes,
                    receiver,
                    info.brand_check_identifier.expect("brandCheckIdentifier"),
                    right,
                    info.kind,
                    None,
                )
            }
            PrivateIdentifierKind::Field => {
                let f = if info.is_static { info.variable_name } else { None };
                ec.borrow_mut().factory.new_class_private_field_set_helper(
                    cx.nodes,
                    receiver,
                    info.brand_check_identifier.expect("brandCheckIdentifier"),
                    right,
                    info.kind,
                    f,
                )
            }
            PrivateIdentifierKind::Untransformed => {
                panic!("Access helpers should not be created for untransformed private elements")
            }
        }
    }

    /// `getPrivateInstanceMethodsAndAccessors`.
    fn get_private_instance_methods_and_accessors(
        &self,
        nodes: &[tsc_ast::Node],
        node: NodeId,
    ) -> Vec<NodeId> {
        nodes[node]
            .members()
            .unwrap_or(&[])
            .iter()
            .copied()
            .filter(|&m| is_non_static_method_or_accessor_with_private_name(nodes, m))
            .collect()
    }

    /// `memberContainsConstructorReference`.
    fn member_contains_constructor_reference(
        &self,
        ec: &Ec,
        nodes: &[tsc_ast::Node],
        member: NodeId,
        class_decl: NodeId,
    ) -> bool {
        let Some(class_original) = ec.borrow().most_original(Some(class_decl)) else {
            return false;
        };
        let class_name = ast::get_name_of_declaration(Some(class_decl), nodes);
        let Some(resolver) = &self.resolver else {
            return false;
        };
        let Some(symbols) = self.symbols else {
            return false;
        };

        // recursive check
        fn check<'r>(
            nodes: &[tsc_ast::Node],
            resolver: &Rc<RefCell<dyn ReferenceResolver + 'r>>,
            symbols: &RefCell<Vec<Symbol>>,
            class_original: NodeId,
            class_name: Option<NodeId>,
            n: NodeId,
        ) -> bool {
            if ast::is_identifier(&nodes[n]) && Some(n) != class_name {
                let decl = resolver.borrow_mut().get_referenced_value_declaration(
                    n,
                    nodes,
                    &mut symbols.borrow_mut(),
                );
                if decl == Some(class_original) {
                    return true;
                }
            }
            // For PropertyAccessExpression, only check the expression, not the name.
            if ast::is_property_access_expression(&nodes[n]) {
                if let Some(e) = nodes[n].expression() {
                    return check(nodes, resolver, symbols, class_original, class_name, e);
                }
                return false;
            }
            nodes[n].for_each_child(nodes, &mut |child| {
                check(nodes, resolver, symbols, class_original, class_name, child)
            })
        }

        // Check only the body/initializer of the member, not the name.
        if ast::is_class_static_block_declaration(&nodes[member]) {
            if let Some(body) = cx_body(nodes, member)
                && check(nodes, resolver, symbols, class_original, class_name, body)
            {
                return true;
            }
        } else {
            if let Some(body) = nodes[member].body()
                && check(nodes, resolver, symbols, class_original, class_name, body)
            {
                return true;
            }
        }
        if ast::is_property_declaration(&nodes[member])
            && let Some(init) = nodes[member].initializer()
            && check(nodes, resolver, symbols, class_original, class_name, init)
        {
            return true;
        }
        false
    }

    /// `classContainsConstructorReference`.
    fn class_contains_constructor_reference(
        &self,
        ec: &Ec,
        nodes: &[tsc_ast::Node],
        node: NodeId,
    ) -> bool {
        for member in nodes[node].members().unwrap_or(&[]) {
            if self.member_contains_constructor_reference(ec, nodes, *member, node) {
                return true;
            }
        }
        false
    }

    /// `getClassFacts`.
    fn get_class_facts(
        &self,
        ec: &Ec,
        cx: &VisitorCx<'_, '_>,
        node: NodeId,
    ) -> ClassFacts {
        let nodes = &*cx.nodes;
        let mut facts = CLASS_FACTS_NONE;

        let original = ec.borrow().most_original(Some(node));
        if let Some(original) = original
            && ast::is_class_like(Some(original), nodes)
            && ast::class_or_constructor_parameter_is_decorated(
                self.legacy_decorators,
                original,
                nodes,
            )
        {
            facts |= CLASS_FACTS_CLASS_WAS_DECORATED;
        }

        if self
            .should_transform_private_elements_or_class_static_blocks
            .get()
            && (class_has_class_this_assignment(&ec.borrow(), nodes, node)
                || class_has_explicitly_assigned_name(&ec.borrow(), nodes, node))
        {
            facts |= CLASS_FACTS_NEEDS_CLASS_CONSTRUCTOR_REFERENCE;
        }

        let mut contains_public_instance_fields = false;
        let mut contains_initialized_public_instance_fields = false;
        let mut contains_instance_private_elements = false;
        let mut contains_instance_auto_accessors = false;

        for member in nodes[node].members().unwrap_or(&[]) {
            let member = *member;
            if ast::is_static(&nodes[member]) {
                if nodes[member].name().is_some_and(|n| {
                    ast::is_private_identifier(&nodes[n])
                        || ast::is_auto_accessor_property_declaration(&nodes[member])
                }) && self
                    .should_transform_private_elements_or_class_static_blocks
                    .get()
                {
                    facts |= CLASS_FACTS_NEEDS_CLASS_CONSTRUCTOR_REFERENCE;
                } else if ast::is_auto_accessor_property_declaration(&nodes[member])
                    && self.should_transform_auto_accessors.get()
                    && nodes[node].name().is_none()
                    && ec.borrow().class_this(node).is_none()
                {
                    facts |= CLASS_FACTS_NEEDS_CLASS_CONSTRUCTOR_REFERENCE;
                }
                if ast::is_property_declaration(&nodes[member])
                    || ast::is_class_static_block_declaration(&nodes[member])
                {
                    if self.should_transform_this_in_static_initializers.get()
                        && nodes[member].subtree_facts(nodes)
                            & SubtreeFacts::CONTAINS_LEXICAL_THIS
                            != SubtreeFacts::NONE
                    {
                        facts |=
                            CLASS_FACTS_NEEDS_SUBSTITUTION_FOR_THIS_IN_CLASS_STATIC_FIELD;
                        if facts & CLASS_FACTS_CLASS_WAS_DECORATED == 0 {
                            facts |= CLASS_FACTS_NEEDS_CLASS_CONSTRUCTOR_REFERENCE;
                        }
                    }
                    if self.should_transform_super_in_static_initializers.get()
                        && nodes[member].subtree_facts(nodes)
                            & SubtreeFacts::CONTAINS_LEXICAL_SUPER
                            != SubtreeFacts::NONE
                    {
                        if facts & CLASS_FACTS_CLASS_WAS_DECORATED == 0 {
                            facts |= CLASS_FACTS_NEEDS_CLASS_CONSTRUCTOR_REFERENCE
                                | CLASS_FACTS_NEEDS_CLASS_SUPER_REFERENCE;
                        }
                    }
                }
            } else if !ast::has_abstract_modifier(
                &nodes[ec.borrow().most_original(Some(member)).unwrap_or(member)],
            ) {
                if ast::is_auto_accessor_property_declaration(&nodes[member]) {
                    contains_instance_auto_accessors = true;
                    contains_instance_private_elements = contains_instance_private_elements
                        || ast::is_private_identifier_class_element_declaration(
                            &nodes[member],
                            nodes,
                        );
                } else if ast::is_private_identifier_class_element_declaration(
                    &nodes[member],
                    nodes,
                ) {
                    contains_instance_private_elements = true;
                    if self.member_contains_constructor_reference(ec, nodes, member, node) {
                        facts |= CLASS_FACTS_NEEDS_CLASS_CONSTRUCTOR_REFERENCE;
                    }
                } else if ast::is_property_declaration(&nodes[member]) {
                    contains_public_instance_fields = true;
                    contains_initialized_public_instance_fields =
                        contains_initialized_public_instance_fields
                            || nodes[member].initializer().is_some();
                }
            }
        }

        let will_hoist_initializers_to_constructor =
            (self.should_transform_initializers_using_define.get()
                && contains_public_instance_fields)
                || (self.should_transform_initializers_using_set.get()
                    && contains_initialized_public_instance_fields)
                || (self
                    .should_transform_private_elements_or_class_static_blocks
                    .get()
                    && contains_instance_private_elements)
                || (self
                    .should_transform_private_elements_or_class_static_blocks
                    .get()
                    && contains_instance_auto_accessors
                    && self.should_transform_auto_accessors.get());

        if will_hoist_initializers_to_constructor {
            facts |= CLASS_FACTS_WILL_HOIST_INITIALIZERS_TO_CONSTRUCTOR;
        }

        facts
    }

    /// `lexicalData` — returns the current classLexicalEnvironment data, if any.
    fn lexical_data(&self) -> Option<Rc<RefCell<ClassLexicalEnvironment>>> {
        self.lexical_environment
            .borrow()
            .last()
            .and_then(|f| f.data.clone())
    }

    /// `lexicalFacts`.
    fn lexical_facts(&self) -> ClassFacts {
        self.lexical_data()
            .map(|d| d.borrow().facts)
            .unwrap_or(CLASS_FACTS_NONE)
    }

    /// `visitExpressionWithTypeArgumentsInHeritageClause`.
    fn visit_expression_with_type_arguments_in_heritage_clause(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let facts = self.lexical_facts();
        if facts & CLASS_FACTS_NEEDS_CLASS_SUPER_REFERENCE != 0 {
            let temp = ec.borrow_mut().factory.new_temp_variable_ex(
                cx.nodes,
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                    ..Default::default()
                },
            );
            ec.borrow_mut().add_variable_declaration(cx.nodes, temp);
            self.get_class_lexical_environment()
                .borrow_mut()
                .super_class_reference = Some(temp);
            let expression = cx.nodes[node]
                .as_expression_with_type_arguments()
                .expression;
            let visited = self.txv(ec).visit_node(cx, expression);
            let assign = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                temp,
                visited.expect("extends expression"),
            );
            return ec
                .borrow_mut()
                .factory
                .update_expression_with_type_arguments(cx.nodes, node, Some(assign), None)
                .unwrap_or(node);
        }
        vref!(self, heritage_clause_visitor)
            .visit_each_child(cx, node)
            .unwrap_or(node)
    }

    /// `visitInNewClassLexicalEnvironment`.
    fn visit_in_new_class_lexical_environment(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        cb: Cb,
    ) -> Option<NodeId> {
        let saved_current_class_container = self.current_class_container.get();
        let saved_pending_expressions: Vec<NodeId> =
            std::mem::take(&mut *self.pending_expressions.borrow_mut());
        let saved_lexical_environment_len = self.lexical_environment.borrow().len();
        self.current_class_container.set(Some(node));
        self.start_class_lexical_environment();
        let original = ec.borrow().most_original(Some(node));
        if let Some(original) = original {
            self.enclosing_class_declarations
                .borrow_mut()
                .insert(original);
        }

        if self
            .should_transform_private_elements_or_class_static_blocks
            .get()
            || self.node_has_transform_private_static_elements_flag(ec, node)
        {
            let name = ast::get_name_of_declaration(Some(node), cx.nodes);
            let env = self.get_private_identifier_environment();
            if let Some(name) = name
                && ast::is_identifier(&cx.nodes[name])
            {
                env.borrow_mut().data.class_name = Some(name);
            } else if let Some(assigned_name) = original
                .and_then(|_| ec.borrow().assigned_name(node))
                .or_else(|| ec.borrow().assigned_name(node))
            {
                if ast::is_string_literal(&cx.nodes[assigned_name]) {
                    // If the assigned name has a textSourceNode that is an identifier, use it directly.
                    let text_source = ec.borrow().text_source(assigned_name);
                    if let Some(text_source) = text_source
                        && ast::is_identifier(&cx.nodes[text_source])
                    {
                        env.borrow_mut().data.class_name = Some(text_source);
                    } else {
                        let text = cx.nodes[assigned_name]
                            .as_string_literal()
                            .literal_expression_base
                            .literal_like_node_base
                            .text
                            .clone();
                        if is_identifier_text(&text, LanguageVariant::Standard) {
                            // If the text is a valid identifier, create an identifier from it.
                            let prefix_name =
                                ec.borrow_mut().factory.new_identifier(cx.nodes, &text);
                            env.borrow_mut().data.class_name = Some(prefix_name);
                        }
                    }
                }
            }
        }

        if self
            .should_transform_private_elements_or_class_static_blocks
            .get()
        {
            let private_instance_methods_and_accessors =
                self.get_private_instance_methods_and_accessors(cx.nodes, node);
            if !private_instance_methods_and_accessors.is_empty() {
                let name = cx.nodes[private_instance_methods_and_accessors[0]].name();
                let weak_set_name = self.create_hoisted_variable_for_class(
                    ec,
                    cx,
                    "instances",
                    name,
                    "",
                );
                self.get_private_identifier_environment()
                    .borrow_mut()
                    .data
                    .weak_set_name = Some(weak_set_name);
            }
        }

        let facts = self.get_class_facts(ec, cx, node);
        if facts != CLASS_FACTS_NONE {
            self.get_class_lexical_environment().borrow_mut().facts = facts;
        }

        // Run the visitor with the computed facts.
        let result = match cb {
            Cb::VisitClassDeclarationInner => {
                self.visit_class_declaration_inner(ec, cx, node, facts)
            }
            Cb::VisitClassExpressionInner => {
                self.visit_class_expression_inner(ec, cx, node, facts)
            }
            _ => unreachable!(),
        };

        if let Some(original) = original {
            self.enclosing_class_declarations
                .borrow_mut()
                .remove(&original);
        }
        self.end_class_lexical_environment();
        debug_assert_eq!(self.lexical_environment.borrow().len(), saved_lexical_environment_len);
        self.current_class_container.set(saved_current_class_container);
        *self.pending_expressions.borrow_mut() = saved_pending_expressions;
        Some(result)
    }

    /// `visitClassDeclaration`.
    fn visit_class_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.visit_in_new_class_lexical_environment(ec, cx, node, Cb::VisitClassDeclarationInner)
            .unwrap_or(node)
    }

    /// `visitClassDeclarationInNewClassLexicalEnvironment`.
    fn visit_class_declaration_inner(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        facts: ClassFacts,
    ) -> NodeId {
        // If a class has private static fields, or a static field has a `this` or `super` reference,
        // then we need to allocate a temp variable to hold on to that reference.
        let mut pending_class_reference_assignment: Option<NodeId> = None;
        if facts & CLASS_FACTS_NEEDS_CLASS_CONSTRUCTOR_REFERENCE != 0 {
            if self
                .should_transform_private_elements_or_class_static_blocks
                .get()
                && ec.borrow().class_this(node).is_some()
            {
                let class_this = ec.borrow().class_this(node).unwrap();
                self.get_class_lexical_environment()
                    .borrow_mut()
                    .class_constructor = Some(class_this);
                let local_name = ec.borrow_mut().factory.get_local_name(cx.nodes, Some(node));
                pending_class_reference_assignment = Some(
                    ec.borrow_mut()
                        .factory
                        .new_assignment_expression(cx.nodes, class_this, local_name),
                );
            } else {
                let temp = ec.borrow_mut().factory.new_temp_variable_ex(
                    cx.nodes,
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                        ..Default::default()
                    },
                );
                ec.borrow_mut().add_variable_declaration(cx.nodes, temp);
                let cloned = ec.borrow_mut().factory.clone_node(cx.nodes, temp);
                self.get_class_lexical_environment()
                    .borrow_mut()
                    .class_constructor = Some(cloned);
                let local_name = ec.borrow_mut().factory.get_local_name(cx.nodes, Some(node));
                pending_class_reference_assignment = Some(
                    ec.borrow_mut()
                        .factory
                        .new_assignment_expression(cx.nodes, temp, local_name),
                );
            }
        }

        if let Some(class_this) = ec.borrow().class_this(node) {
            self.get_class_lexical_environment()
                .borrow_mut()
                .class_this = Some(class_this);
        }

        let is_class_with_constructor_reference =
            self.class_contains_constructor_reference(ec, cx.nodes, node);

        // Register class alias BEFORE visiting members.
        let alias = self
            .get_class_lexical_environment()
            .borrow()
            .class_constructor;
        if is_class_with_constructor_reference
            && let (Some(alias), Some(original)) = (alias, ec.borrow().most_original(Some(node)))
        {
            self.class_aliases.borrow_mut().insert(original, alias);
        }

        let modifiers = vref!(self, modifier_visitor)
            .visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let heritage_clauses = vref!(self, heritage_clause_visitor).visit_nodes(
            cx,
            cx.nodes[node].as_class_declaration().class_like_base.heritage_clauses.clone(),
        );
        let (members, members_prologue) = self.transform_class_members(ec, cx, node);

        let mut statements: Vec<NodeId> = Vec::new();

        if let Some(pending_class_reference_assignment) = pending_class_reference_assignment {
            self.pending_expressions
                .borrow_mut()
                .insert(0, pending_class_reference_assignment);
        }

        // Write any pending expressions from elided or moved computed property names
        if !self.pending_expressions.borrow().is_empty() {
            let pending: Vec<NodeId> = self.pending_expressions.borrow().clone();
            let inlined = ec.borrow_mut().factory.inline_expressions(cx.nodes, &pending);
            let stmt = ec.borrow_mut().factory.new_expression_statement(cx.nodes, inlined);
            statements.push(stmt);
        }

        // A class declaration without a name needs a generated name if it has static
        // initialized properties, since those will be moved outside the class body and
        // need to reference the class by name.
        let mut name = cx.nodes[node].name();

        if self.should_transform_initializers_using_set.get()
            || self
                .should_transform_private_elements_or_class_static_blocks
                .get()
        {
            // Emit static property assignment. Because classDeclaration is lexically evaluated,
            // it is safe to emit static property assignment after classDeclaration.
            let static_properties =
                self.get_static_properties_and_class_static_block(cx.nodes, node);
            if !static_properties.is_empty() {
                if name.is_none() {
                    name = Some(ec.borrow_mut().factory.new_generated_name_for_node(
                        cx.nodes, node,
                    ));
                }
                let local_name = ec.borrow_mut().factory.get_local_name(cx.nodes, Some(node));
                statements = self.add_property_or_class_static_block_statements(
                    ec, cx, statements, &static_properties, local_name,
                );
            }
        }

        let is_export =
            ast::has_syntactic_modifier(&cx.nodes[node], ModifierFlags::EXPORT);
        let is_default =
            ast::has_syntactic_modifier(&cx.nodes[node], ModifierFlags::DEFAULT);

        let mut modifiers = modifiers;
        if !statements.is_empty() && is_export && is_default {
            modifiers = extract_modifiers(
                Some(ec),
                cx.nodes,
                modifiers,
                !ModifierFlags::EXPORT_DEFAULT,
            );
            let local_name = ec.borrow_mut().factory.get_local_name(cx.nodes, Some(node));
            let export_assignment = ec.borrow_mut().factory.new_export_assignment(
                cx.nodes,
                None,
                false,
                None,
                Some(local_name),
            );
            statements.push(export_assignment);
        }

        let updated_class = ec
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

        let mut result: Vec<NodeId> = Vec::with_capacity(1 + statements.len() + 1);
        if let Some(members_prologue) = members_prologue {
            result.push(
                ec.borrow_mut()
                    .factory
                    .new_expression_statement(cx.nodes, Some(members_prologue)),
            );
        }
        result.push(updated_class);
        result.extend(statements);
        ec.borrow_mut().factory.new_syntax_list(cx.nodes, &result)
    }

    /// `visitClassExpression`.
    fn visit_class_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.visit_in_new_class_lexical_environment(ec, cx, node, Cb::VisitClassExpressionInner)
            .unwrap_or(node)
    }

    /// `visitClassExpressionInNewClassLexicalEnvironment`.
    fn visit_class_expression_inner(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        facts: ClassFacts,
    ) -> NodeId {
        // If this class expression is a transformation of a decorated class declaration,
        // then we want to output the pendingExpressions as statements, not as inlined
        // expressions with the class statement.
        let is_decorated_class_declaration = facts & CLASS_FACTS_CLASS_WAS_DECORATED != 0;

        if let Some(class_this) = ec.borrow().class_this(node) {
            self.get_class_lexical_environment()
                .borrow_mut()
                .class_this = Some(class_this);
        }

        let mut temp: Option<NodeId> = None;
        if facts & CLASS_FACTS_NEEDS_CLASS_CONSTRUCTOR_REFERENCE != 0 {
            if (self
                .should_transform_private_elements_or_class_static_blocks
                .get()
                || self.node_has_transform_private_static_elements_flag(ec, node))
                && ec.borrow().class_this(node).is_some()
            {
                let class_this = ec.borrow().class_this(node).unwrap();
                self.get_class_lexical_environment()
                    .borrow_mut()
                    .class_constructor = Some(class_this);
                temp = Some(class_this);
            } else {
                let t = ec.borrow_mut().factory.new_temp_variable_ex(
                    cx.nodes,
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                        ..Default::default()
                    },
                );
                if self.class_expression_needs_block_scoped_temp(cx) {
                    ec.borrow_mut().add_lexical_declaration(cx.nodes, t);
                } else {
                    ec.borrow_mut().add_variable_declaration(cx.nodes, t);
                }
                let cloned = ec.borrow_mut().factory.clone_node(cx.nodes, t);
                self.get_class_lexical_environment()
                    .borrow_mut()
                    .class_constructor = Some(cloned);
                temp = Some(t);
            }
        }

        let static_properties_or_class_static_blocks =
            self.get_static_properties_and_class_static_block(cx.nodes, node);

        // Pre-compute whether the class expression will need a temp variable wrapper.
        let mut is_class_with_constructor_reference = false;
        let mut has_transformable_statics = false;
        let mut defer_temp_declaration = false;
        if !is_decorated_class_declaration {
            is_class_with_constructor_reference =
                self.class_contains_constructor_reference(ec, cx.nodes, node);
            has_transformable_statics = (self
                .should_transform_private_elements_or_class_static_blocks
                .get()
                || self.node_has_transform_private_static_elements_flag(ec, node))
                && static_properties_or_class_static_blocks.iter().any(|&n| {
                    ast::is_class_static_block_declaration(&cx.nodes[n])
                        || ast::is_private_identifier_class_element_declaration(
                            &cx.nodes[n],
                            cx.nodes,
                        )
                        || (self.should_transform_initializers.get()
                            && ast::is_initialized_property(&cx.nodes[n]))
                });

            // Private instance elements (fields, methods, accessors) transformed to
            // WeakMap/WeakSet will add initialization expressions to pendingExpressions
            // during transformClassMembers. Pre-detect this so we know whether the class
            // will be wrapped with a temp variable.
            let will_have_private_pending_expressions = self
                .should_transform_private_elements_or_class_static_blocks
                .get()
                && cx.nodes[node].members().unwrap_or(&[]).iter().any(|&n| {
                    ast::is_private_identifier_class_element_declaration(&cx.nodes[n], cx.nodes)
                        && !ast::has_static_modifier(&cx.nodes[n])
                        && self.should_transform_class_element_to_weak_map(ec, cx, n)
                });
            let will_need_temp_wrapper =
                has_transformable_statics || will_have_private_pending_expressions;

            // Register class alias BEFORE visiting members. Only register when the class will be
            // wrapped with a temp, matching Strada's conditional registration.
            if is_class_with_constructor_reference
                && will_need_temp_wrapper
                && self
                    .get_class_lexical_environment()
                    .borrow()
                    .class_constructor
                    .is_none()
            {
                // Create temp early so the alias is available during member visiting.
                temp = Some(ec.borrow_mut().factory.new_temp_variable_ex(
                    cx.nodes,
                    &AutoGenerateOptions {
                        flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                        ..Default::default()
                    },
                ));
                // Defer AddVariableDeclaration to preserve Strada's variable declaration ordering.
                defer_temp_declaration = true;
                let cloned = ec.borrow_mut().factory.clone_node(cx.nodes, temp.unwrap());
                self.get_class_lexical_environment()
                    .borrow_mut()
                    .class_constructor = Some(cloned);
            }
            let alias = self
                .get_class_lexical_environment()
                .borrow()
                .class_constructor;
            if is_class_with_constructor_reference
                && will_need_temp_wrapper
                && let (Some(alias), Some(original)) =
                    (alias, ec.borrow().most_original(Some(node)))
            {
                self.class_aliases.borrow_mut().insert(original, alias);
            }
        }

        let modifiers = vref!(self, modifier_visitor)
            .visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let heritage_clauses = vref!(self, heritage_clause_visitor).visit_nodes(
            cx,
            cx.nodes[node].as_class_expression().class_like_base.heritage_clauses.clone(),
        );
        let (members, members_prologue) = self.transform_class_members(ec, cx, node);

        if defer_temp_declaration {
            if self.class_expression_needs_block_scoped_temp(cx) {
                ec.borrow_mut()
                    .add_lexical_declaration(cx.nodes, temp.unwrap());
            } else {
                ec.borrow_mut()
                    .add_variable_declaration(cx.nodes, temp.unwrap());
            }
        }

        let name = cx.nodes[node].name();
        let class_expression = ec
            .borrow_mut()
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
            .unwrap_or(node);

        let mut expressions: Vec<NodeId> = Vec::new();
        if let Some(members_prologue) = members_prologue {
            expressions.push(members_prologue);
        }

        if !is_decorated_class_declaration {
            if has_transformable_statics || !self.pending_expressions.borrow().is_empty() {
                if temp.is_none() {
                    let t = ec.borrow_mut().factory.new_temp_variable_ex(
                        cx.nodes,
                        &AutoGenerateOptions {
                            flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                            ..Default::default()
                        },
                    );
                    if self.class_expression_needs_block_scoped_temp(cx) {
                        ec.borrow_mut().add_lexical_declaration(cx.nodes, t);
                    } else {
                        ec.borrow_mut().add_variable_declaration(cx.nodes, t);
                    }
                    let cloned = ec.borrow_mut().factory.clone_node(cx.nodes, t);
                    self.get_class_lexical_environment()
                        .borrow_mut()
                        .class_constructor = Some(cloned);
                    temp = Some(t);
                    if is_class_with_constructor_reference {
                        let alias = self
                            .get_class_lexical_environment()
                            .borrow()
                            .class_constructor;
                        if let (Some(alias), Some(original)) =
                            (alias, ec.borrow().most_original(Some(node)))
                        {
                            self.class_aliases.borrow_mut().insert(original, alias);
                        }
                    }
                }

                let temp = temp.unwrap();
                expressions.push(ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    temp,
                    class_expression,
                ));

                // Add any pending expressions leftover from elided or relocated computed property names
                let pending: Vec<NodeId> = self.pending_expressions.borrow().clone();
                expressions.extend(pending);

                let receiver = temp;
                let generated = self.generate_initialized_property_expressions_or_class_static_block(
                    ec,
                    cx,
                    &static_properties_or_class_static_blocks,
                    receiver,
                );
                expressions.extend(generated);
                let cloned = ec.borrow_mut().factory.clone_node(cx.nodes, temp);
                expressions.push(cloned);
            } else {
                expressions.push(class_expression);
            }
        } else {
            // Decorated class declaration path: emit static properties as separate statements
            // via pendingStatements, matching the class declaration output structure.

            // Write any pending expressions from elided or moved computed property names
            if !self.pending_expressions.borrow().is_empty() {
                let pending: Vec<NodeId> = self.pending_expressions.borrow().clone();
                for expr in pending {
                    let stmt = ec.borrow_mut().factory.new_expression_statement(
                        cx.nodes,
                        Some(expr),
                    );
                    self.pending_statements.borrow_mut().push(stmt);
                }
            }

            // Emit static properties as statements (via pendingStatements) using the class's
            // internal name as the receiver, matching the class declaration output structure.
            if !static_properties_or_class_static_blocks.is_empty() {
                let class_this_or_name = match ec.borrow().class_this(node) {
                    Some(class_this) => class_this,
                    None => ec.borrow_mut().factory.get_local_name(cx.nodes, Some(node)),
                };
                let new_pending = self.add_property_or_class_static_block_statements(
                    ec,
                    cx,
                    Vec::new(),
                    &static_properties_or_class_static_blocks,
                    class_this_or_name,
                );
                self.pending_statements.borrow_mut().extend(new_pending);
            }

            if let Some(temp) = temp {
                expressions.push(ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    temp,
                    class_expression,
                ));
            } else if self
                .should_transform_private_elements_or_class_static_blocks
                .get()
                && ec.borrow().class_this(node).is_some()
            {
                let class_this = ec.borrow().class_this(node).unwrap();
                expressions.push(ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    class_this,
                    class_expression,
                ));
            } else {
                expressions.push(class_expression);
            }
        }

        if expressions.len() > 1 {
            ec.borrow()
                .add_emit_flags(class_expression, EmitFlags::INDENTED);
            for expr in &expressions {
                ec.borrow().add_emit_flags(*expr, EmitFlags::START_ON_NEW_LINE);
            }
        }
        ec.borrow_mut()
            .factory
            .inline_expressions(cx.nodes, &expressions)
            .unwrap_or(class_expression)
    }

    /// `visitClassStaticBlockDeclaration` — class static blocks are transformed
    /// in `visitClassDeclaration`/`visitClassExpression`.
    fn visit_class_static_block_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if !self
            .should_transform_private_elements_or_class_static_blocks
            .get()
        {
            return self.txv(ec).visit_each_child(cx, node).or(Some(node));
        }
        None
    }

    /// `visitThisExpression` — replaces Strada's substituteThisExpression.
    fn visit_this_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if self.inside_computed_property_name.get()
            && self.should_transform_this_in_static_initializers.get()
            && self.lexical_data().is_some()
        {
            let data = self.lexical_data().unwrap();
            let facts = data.borrow().facts;
            // Don't replace `this` in computed property names for ES-decorated classes.
            if facts & CLASS_FACTS_CLASS_WAS_DECORATED == 0 || self.legacy_decorators {
                if let Some(class_this) = self.try_get_class_this_no_container() {
                    return class_this;
                }
            }
        }
        if self.should_transform_this_in_static_initializers.get()
            && self.current_class_element.get().is_some()
            && {
                let el = self.current_class_element.get().unwrap();
                ast::is_class_static_block_declaration(&cx.nodes[el])
                    || (ast::is_property_declaration(&cx.nodes[el])
                        && ast::has_static_modifier(&cx.nodes[el]))
            }
            && self.lexical_data().is_some()
        {
            if let Some(class_this) = self.try_get_class_this_no_container() {
                return class_this;
            }
            // When the class was decorated with legacy decorators and no class constructor
            // reference is available, the decorator may replace the constructor, so `this`
            // cannot reliably point to the class. Use `(void 0)` instead.
            let facts = self.lexical_data().unwrap().borrow().facts;
            if facts & CLASS_FACTS_CLASS_WAS_DECORATED != 0 && self.legacy_decorators {
                let void_zero = ec.borrow_mut().factory.new_void_zero_expression(cx.nodes);
                return ec
                    .borrow_mut()
                    .factory
                    .new_parenthesized_expression(cx.nodes, Some(void_zero));
            }
        }
        node
    }

    /// `transformClassMembers` — returns `(members, prologue)`.
    fn transform_class_members(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> (Option<NodeList>, Option<NodeId>) {
        let should_transform_private_static_elements_in_class =
            self.node_has_transform_private_static_elements_flag(ec, node);

        // Declare private names
        if self
            .should_transform_private_elements_or_class_static_blocks
            .get()
            || self
                .should_transform_private_static_elements_in_file
                .get()
        {
            for member in cx.nodes[node].members().unwrap_or(&[]).to_vec() {
                if ast::is_private_identifier_class_element_declaration(&cx.nodes[member], cx.nodes)
                {
                    if self.should_transform_class_element_to_weak_map(ec, cx, member) {
                        self.add_private_identifier_to_environment(ec, cx, member);
                    } else {
                        let env = self.get_private_identifier_environment();
                        self.set_private_identifier(
                            ec,
                            cx,
                            &env,
                            cx.nodes[member].name().expect("member name"),
                            PrivateIdentifierInfo {
                                kind: PrivateIdentifierKind::Untransformed,
                                ..Default::default()
                            },
                        );
                    }
                }
            }

            if self
                .should_transform_private_elements_or_class_static_blocks
                .get()
                && !self
                    .get_private_instance_methods_and_accessors(cx.nodes, node)
                    .is_empty()
            {
                self.create_brand_check_weak_set_for_private_methods(ec, cx);
            }

            if self.should_transform_auto_accessors_in_current_class() {
                for member in cx.nodes[node].members().unwrap_or(&[]).to_vec() {
                    if ast::is_auto_accessor_property_declaration(&cx.nodes[member]) {
                        let name = cx.nodes[member].name().expect("member name");
                        let storage_name = ec
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
                        if self
                            .should_transform_private_elements_or_class_static_blocks
                            .get()
                            || (should_transform_private_static_elements_in_class
                                && ast::has_static_modifier(&cx.nodes[member]))
                        {
                            self.add_private_identifier_property_declaration_to_environment(
                                ec,
                                cx,
                                member,
                                storage_name,
                            );
                        } else {
                            let env = self.get_private_identifier_environment();
                            // Only register as untransformed if it hasn't already been registered
                            // by the first loop (e.g., if esDecorators expanded a private
                            // auto-accessor into a backing field with the same generated name).
                            if self
                                .get_private_identifier(ec, cx.nodes, &env, storage_name)
                                .is_none()
                            {
                                self.set_private_identifier(
                                    ec,
                                    cx,
                                    &env,
                                    storage_name,
                                    PrivateIdentifierInfo {
                                        kind: PrivateIdentifierKind::Untransformed,
                                        ..Default::default()
                                    },
                                );
                            }
                        }
                    }
                }
            }
        }

        let member_list = cx.nodes[node].member_list().cloned();
        let mut members = vref!(self, class_element_visitor).visit_nodes(cx, member_list);
        let mut prologue: Option<NodeId> = None;

        // Create a synthetic constructor if necessary
        let mut synthetic_constructor: Option<NodeId> = None;
        if !members
            .as_ref()
            .map(|m| m.nodes.iter().any(|&n| ast::is_constructor_declaration(&cx.nodes[n])))
            .unwrap_or(false)
        {
            synthetic_constructor = self.transform_constructor(ec, cx, None, node);
        }

        // If there are pending expressions create a class static block in which to evaluate them, but only if
        // class static blocks are not also being transformed. This block will be injected at the top of the class
        // to ensure that expressions from computed property names are evaluated before any other static
        // initializers.
        let mut synthetic_static_block: Option<NodeId> = None;
        if !self
            .should_transform_private_elements_or_class_static_blocks
            .get()
            && !self.pending_expressions.borrow().is_empty()
        {
            let pending: Vec<NodeId> = self.pending_expressions.borrow().clone();
            let inlined = ec.borrow_mut().factory.inline_expressions(cx.nodes, &pending);
            let mut statement = ec
                .borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, inlined);
            if subtree_facts(cx, statement) & SubtreeFacts::CONTAINS_LEXICAL_THIS_OR_SUPER
                != SubtreeFacts::NONE
            {
                // If there are `this` or `super` references from computed property names, shift the
                // expression into an arrow function to be evaluated in the outer scope.
                let temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                ec.borrow_mut().add_variable_declaration(cx.nodes, temp);
                let params = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
                let eq_gt = ec
                    .borrow_mut()
                    .factory
                    .new_token(cx.nodes, Kind::EqualsGreaterThanToken);
                let stmts = ec.borrow_mut().factory.new_node_list([statement]);
                let arrow_body = ec.borrow_mut().factory.new_block(cx.nodes, Some(stmts), false);
                let arrow = ec.borrow_mut().factory.new_arrow_function(
                    cx.nodes,
                    None,
                    None,
                    Some(params),
                    None,
                    None,
                    Some(eq_gt),
                    Some(arrow_body),
                );
                prologue = Some(ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    temp,
                    arrow,
                ));
                let args = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
                let call = ec.borrow_mut().factory.new_call_expression(
                    cx.nodes,
                    Some(temp),
                    None,
                    None,
                    Some(args),
                    NodeFlags::NONE,
                );
                statement = ec.borrow_mut().factory.new_expression_statement(
                    cx.nodes,
                    Some(call),
                );
            }

            let stmts = ec.borrow_mut().factory.new_node_list([statement]);
            let block = ec.borrow_mut().factory.new_block(cx.nodes, Some(stmts), false);
            synthetic_static_block = Some(ec.borrow_mut().factory.new_class_static_block_declaration(
                cx.nodes,
                None,
                Some(block),
            ));
            self.pending_expressions.borrow_mut().clear();
        }

        // If we created a synthetic constructor or class static block, add them to the visited members
        if synthetic_constructor.is_some() || synthetic_static_block.is_some() {
            let member_ids: Vec<NodeId> = members
                .as_ref()
                .map(|m| m.nodes.to_vec())
                .unwrap_or_default();
            let mut members_array: Vec<NodeId> = Vec::with_capacity(member_ids.len() + 2);

            // Find and preserve classThis assignment block and named evaluation helper block at the top
            let class_this_idx = member_ids.iter().position(|&n| {
                is_class_this_assignment_block(&ec.borrow(), cx.nodes, n)
            });
            let named_eval_idx = member_ids.iter().position(|&n| {
                is_class_named_evaluation_helper_block(&ec.borrow(), cx.nodes, n)
            });

            if let Some(i) = class_this_idx {
                members_array.push(member_ids[i]);
            }
            if let Some(i) = named_eval_idx {
                members_array.push(member_ids[i]);
            }
            if let Some(sc) = synthetic_constructor {
                members_array.push(sc);
            }
            if let Some(sb) = synthetic_static_block {
                members_array.push(sb);
            }

            for (i, member) in member_ids.iter().enumerate() {
                if Some(i) != class_this_idx && Some(i) != named_eval_idx {
                    members_array.push(*member);
                }
            }
            let mut new_members = ec.borrow_mut().factory.new_node_list(members_array);
            new_members.loc = cx.nodes[node]
                .member_list()
                .map(|l| l.loc)
                .unwrap_or_default();
            members = Some(new_members);
        }

        (members, prologue)
    }

    /// `createBrandCheckWeakSetForPrivateMethods`.
    fn create_brand_check_weak_set_for_private_methods(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>) {
        let env = self.get_private_identifier_environment();
        let weak_set_name = env.borrow().data.weak_set_name;
        debug_assert!(weak_set_name.is_some(), "weakSetName should be set in private identifier environment");
        let weak_set_name = weak_set_name.expect("weakSetName");

        let weakset_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "WeakSet");
        let args = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
        let new_expr = ec.borrow_mut().factory.new_new_expression(
            cx.nodes,
            Some(weakset_ident),
            None,
            Some(args),
        );
        let assignment = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            weak_set_name,
            new_expr,
        );
        self.add_pending_expressions(&[assignment]);
    }

    /// `transformConstructor`.
    fn transform_constructor(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        constructor: Option<NodeId>,
        container: NodeId,
    ) -> Option<NodeId> {
        // NOTE: see the Go source — the Strada reference pre-visits the constructor before
        // checking WillHoistInitializersToConstructor; this is not done here because the
        // variable environment is scoped inside transformConstructorBody.
        if self
            .lexical_data()
            .map(|d| d.borrow().facts)
            .unwrap_or(CLASS_FACTS_NONE)
            & CLASS_FACTS_WILL_HOIST_INITIALIZERS_TO_CONSTRUCTOR
            == 0
        {
            if let Some(constructor) = constructor {
                return self.txv(ec).visit_each_child(cx, constructor).or(Some(constructor));
            }
            return None;
        }

        let extends_clause_element = ast::get_class_extends_heritage_element(&cx.nodes[container], cx.nodes);
        let is_derived_class = extends_clause_element.is_some_and(|e| {
            let expr = cx.nodes[e]
                .as_expression_with_type_arguments()
                .expression
                .expect("extends expression");
            let unwrapped = ast::skip_outer_expressions(expr, ast::outer_expression_kinds::ALL, cx.nodes);
            cx.nodes[unwrapped].kind != Kind::NullKeyword
        });

        let parameters = constructor
            .and_then(|c| self.txv(ec).visit_nodes(cx, cx.nodes[c].parameter_list().cloned()));

        let body = self.transform_constructor_body(ec, cx, container, constructor, is_derived_class);
        if body.is_none() {
            if let Some(constructor) = constructor {
                return self.txv(ec).visit_each_child(cx, constructor).or(Some(constructor));
            }
            return None;
        }
        let body = body.unwrap();

        if let Some(constructor) = constructor {
            debug_assert!(parameters.is_some());
            return Some(
                ec.borrow_mut()
                    .factory
                    .update_constructor_declaration(
                        cx.nodes,
                        constructor,
                        None,
                        None,
                        parameters,
                        None,
                        None,
                        Some(body),
                    )
                    .unwrap_or(constructor),
            );
        }

        let parameters = parameters
            .or_else(|| Some(ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new())));

        let result = ec.borrow_mut().factory.new_constructor_declaration(
            cx.nodes,
            None,
            None,
            parameters,
            None,
            None,
            Some(body),
        );
        cx.nodes[result].loc = cx.nodes[container].loc;
        Some(result)
    }

    /// `transformConstructorBodyWorker`.
    fn transform_constructor_body_worker(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements_out: Vec<NodeId>,
        statements_in: &[NodeId],
        statement_offset: usize,
        super_path: &[i32],
        super_path_depth: usize,
        initializer_statements: &[NodeId],
        constructor: NodeId,
    ) -> Vec<NodeId> {
        let super_statement_index = super_path[super_path_depth] as usize;
        let super_statement = statements_in[super_statement_index];
        let mut statement_offset = statement_offset;

        // Visit statements before super
        if statement_offset < super_statement_index {
            let visited = self
                .txv(ec)
                .visit_slice(cx, &statements_in[statement_offset..super_statement_index])
                .unwrap_or_default();
            statements_out.extend(visited);
        }
        statement_offset = super_statement_index + 1;

        if ast::is_try_statement(&cx.nodes[super_statement]) {
            let (try_block_node, catch_clause, finally_block) = {
                let t = cx.nodes[super_statement].as_try_statement();
                (t.try_block, t.catch_clause, t.finally_block)
            };
            let try_block_node = try_block_node.expect("try block");
            let (try_stmts, try_stmts_loc, multi_line) = {
                let b = cx.nodes[try_block_node].as_block();
                (
                    b.statements.as_ref().map(|l| l.nodes.to_vec()).unwrap_or_default(),
                    b.statements.as_ref().map(|l| l.loc).unwrap_or_default(),
                    b.multi_line,
                )
            };
            let try_block_statements = self.transform_constructor_body_worker(
                ec,
                cx,
                Vec::new(),
                &try_stmts,
                0,
                super_path,
                super_path_depth + 1,
                initializer_statements,
                constructor,
            );
            let mut try_statement_list = ec.borrow_mut().factory.new_node_list(try_block_statements);
            try_statement_list.loc = try_stmts_loc;

            let catch_clause = catch_clause.and_then(|c| self.txv(ec).visit_node(cx, Some(c)));
            let finally_block =
                finally_block.and_then(|f| self.txv(ec).visit_node(cx, Some(f)));

            let new_try_block = ec
                .borrow_mut()
                .factory
                .update_block(cx.nodes, try_block_node, Some(try_statement_list), multi_line)
                .unwrap_or(try_block_node);
            let updated = ec
                .borrow_mut()
                .factory
                .update_try_statement(
                    cx.nodes,
                    super_statement,
                    Some(new_try_block),
                    catch_clause,
                    finally_block,
                )
                .unwrap_or(super_statement);
            statements_out.push(updated);
        } else {
            let visited = self
                .txv(ec)
                .visit_slice(cx, &statements_in[super_statement_index..super_statement_index + 1])
                .unwrap_or_default();
            statements_out.extend(visited);

            // parameter-property assignments should occur immediately after the prologue and
            // `super()`, so only count the statements that immediately follow.
            while statement_offset < statements_in.len() {
                let stmt = statements_in[statement_offset];
                let orig = ec.borrow().most_original(Some(stmt));
                if orig.is_some_and(|o| {
                    ast::is_parameter_property_declaration(&cx.nodes[o], &cx.nodes[constructor])
                }) {
                    statement_offset += 1;
                } else {
                    break;
                }
            }

            statements_out.extend(initializer_statements.iter().copied());
        }

        // Visit remaining statements
        if statement_offset < statements_in.len() {
            let visited = self
                .txv(ec)
                .visit_slice(cx, &statements_in[statement_offset..])
                .unwrap_or_default();
            statements_out.extend(visited);
        }
        statements_out
    }

    /// `transformConstructorBody`.
    fn transform_constructor_body(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        container: NodeId,
        constructor: Option<NodeId>,
        is_derived_class: bool,
    ) -> Option<NodeId> {
        let instance_properties = self.get_properties(cx.nodes, container, false, false);
        let mut properties = instance_properties.clone();
        if !self
            .compiler_options
            .map(|o| o.get_use_define_for_class_fields())
            .unwrap_or(false)
        {
            properties.retain(|&prop| {
                cx.nodes[prop].initializer().is_some()
                    || cx.nodes[prop]
                        .name()
                        .is_some_and(|n| ast::is_private_identifier(&cx.nodes[n]))
                    || ast::has_accessor_modifier(&cx.nodes[prop])
            });
        }

        let private_methods_and_accessors =
            self.get_private_instance_methods_and_accessors(cx.nodes, container);
        let needs_constructor_body =
            !properties.is_empty() || !private_methods_and_accessors.is_empty();

        // Only generate synthetic constructor when there are property initializers to move.
        if constructor.is_none() && !needs_constructor_body {
            let txv = self.txv(ec);
            return ec_visit_function_body(&txv, cx, None);
        }

        ec.borrow_mut().start_variable_environment();

        let needs_synthetic_constructor = constructor.is_none() && is_derived_class;
        let mut statements: Vec<NodeId> = Vec::new();

        // Add the property initializers.
        let mut initializer_statements: Vec<NodeId> = Vec::new();
        let receiver = ec.borrow_mut().factory.new_this_expression(cx.nodes);

        // private methods can be called in property initializers, they should execute first
        initializer_statements = self.add_instance_method_statements(
            ec,
            cx,
            initializer_statements,
            &private_methods_and_accessors,
            receiver,
        );

        if let Some(constructor) = constructor {
            let parameter_properties: Vec<NodeId> = instance_properties
                .iter()
                .copied()
                .filter(|&prop| {
                    let orig = ec.borrow().most_original(Some(prop));
                    orig.is_some_and(|o| {
                        ast::is_parameter_property_declaration(&cx.nodes[o], &cx.nodes[constructor])
                    })
                })
                .collect();
            let non_parameter_properties: Vec<NodeId> = properties
                .iter()
                .copied()
                .filter(|&prop| {
                    let orig = ec.borrow().most_original(Some(prop));
                    !orig.is_some_and(|o| {
                        ast::is_parameter_property_declaration(&cx.nodes[o], &cx.nodes[constructor])
                    })
                })
                .collect();
            initializer_statements = self.add_property_or_class_static_block_statements(
                ec,
                cx,
                initializer_statements,
                &parameter_properties,
                receiver,
            );
            initializer_statements = self.add_property_or_class_static_block_statements(
                ec,
                cx,
                initializer_statements,
                &non_parameter_properties,
                receiver,
            );
        } else {
            initializer_statements = self.add_property_or_class_static_block_statements(
                ec,
                cx,
                initializer_statements,
                &properties,
                receiver,
            );
        }

        if let Some(constructor) = constructor
            && let Some(body_node) = cx.nodes[constructor].body()
        {
            let body_statements: Vec<NodeId> = cx.nodes[body_node]
                .as_block()
                .statements
                .as_ref()
                .map(|l| l.nodes.to_vec())
                .unwrap_or_default();

            // Copy prologue
            for &stmt in &body_statements {
                if ast::is_prologue_directive(&cx.nodes[stmt], cx.nodes) {
                    statements.push(stmt);
                } else {
                    break;
                }
            }
            let mut statement_offset = statements.len();

            let super_path = transformer_utilities::find_super_statement_index_path(
                cx.nodes,
                &body_statements,
                statement_offset,
            );
            if !super_path.is_empty() {
                statements = self.transform_constructor_body_worker(
                    ec,
                    cx,
                    statements,
                    &body_statements,
                    statement_offset,
                    &super_path,
                    0,
                    &initializer_statements,
                    constructor,
                );
            } else {
                // parameter-property assignments should occur immediately after the prologue and
                // `super()`, so only count the statements that immediately follow.
                while statement_offset < body_statements.len() {
                    let stmt = body_statements[statement_offset];
                    let orig = ec.borrow().most_original(Some(stmt));
                    if orig.is_some_and(|o| {
                        ast::is_parameter_property_declaration(&cx.nodes[o], &cx.nodes[constructor])
                    }) {
                        statement_offset += 1;
                    } else {
                        break;
                    }
                }
                statements.extend(initializer_statements.iter().copied());
                let visited = self
                    .txv(ec)
                    .visit_slice(cx, &body_statements[statement_offset..])
                    .unwrap_or_default();
                statements.extend(visited);
            }
        } else {
            if needs_synthetic_constructor {
                // Add a synthetic `super` call:
                //
                //  super(...arguments);
                let arguments_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "arguments");
                let spread = ec.borrow_mut().factory.new_spread_element(cx.nodes, Some(arguments_ident));
                let super_keyword = ec
                    .borrow_mut()
                    .factory
                    .new_keyword_expression(cx.nodes, Kind::SuperKeyword);
                let args = ec.borrow_mut().factory.new_node_list([spread]);
                let super_call_expr = ec.borrow_mut().factory.new_call_expression(
                    cx.nodes,
                    Some(super_keyword),
                    None,
                    None,
                    Some(args),
                    NodeFlags::NONE,
                );
                let super_call = ec.borrow_mut().factory.new_expression_statement(
                    cx.nodes,
                    Some(super_call_expr),
                );
                statements.push(super_call);
            }
            statements.extend(initializer_statements.iter().copied());
        }

        let statements = ec
            .borrow_mut()
            .end_and_merge_variable_environment(cx.nodes, &statements);

        if statements.is_empty() && constructor.is_none() {
            return None;
        }

        let (ctor_body, ctor_body_stmts_loc, ctor_body_multi_line, ctor_body_loc) = constructor
            .and_then(|c| cx.nodes[c].body())
            .map(|b| {
                let bb = cx.nodes[b].as_block();
                (
                    Some(b),
                    bb.statements.as_ref().map(|l| l.loc),
                    bb.multi_line,
                    cx.nodes[b].loc,
                )
            })
            .unwrap_or((None, None, false, tsc_core::text::TextRange::default()));

        let multi_line = if ctor_body.is_some()
            && cx.nodes[ctor_body.unwrap()].as_block().statements.as_ref().map(|l| l.len()).unwrap_or(0)
                >= statements.len()
        {
            ctor_body_multi_line
        } else {
            !statements.is_empty()
        };

        let mut statement_list = ec.borrow_mut().factory.new_node_list(statements);
        if ctor_body.is_some() {
            statement_list.loc = ctor_body_stmts_loc.unwrap_or_default();
        } else {
            let member_list_loc = cx.nodes[container]
                .member_list()
                .map(|l| l.loc)
                .unwrap_or_default();
            statement_list.loc =
                tsc_core::text::TextRange::new(member_list_loc.pos(), member_list_loc.end());
        }

        let block = ec
            .borrow_mut()
            .factory
            .new_block(cx.nodes, Some(statement_list), multi_line);
        if let Some(ctor_body) = ctor_body {
            cx.nodes[block].loc = cx.nodes[ctor_body].loc;
            let _ = ctor_body_loc;
        }
        Some(block)
    }

    /// `addPropertyOrClassStaticBlockStatements`.
    fn add_property_or_class_static_block_statements(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        properties: &[NodeId],
        receiver: NodeId,
    ) -> Vec<NodeId> {
        for &property in properties {
            if ast::is_static(&cx.nodes[property])
                && !self
                    .should_transform_private_elements_or_class_static_blocks
                    .get()
            {
                continue;
            }
            if let Some(statement) =
                self.transform_property_or_class_static_block(ec, cx, property, receiver)
            {
                statements.push(statement);
            }
        }
        statements
    }

    /// `transformPropertyOrClassStaticBlock`.
    fn transform_property_or_class_static_block(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        property: NodeId,
        receiver: NodeId,
    ) -> Option<NodeId> {
        let expression = if ast::is_class_static_block_declaration(&cx.nodes[property]) {
            self.set_current_class_element_and(
                ec,
                Some(property),
                Cb::TransformClassStaticBlockDeclaration,
                cx,
                property,
            )
        } else {
            self.transform_property(ec, cx, property, receiver)
        };
        let expression = expression?;

        let statement = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(expression));
        ec.borrow().set_original(statement, property);
        let flags = ec.borrow().emit_flags(property) & EmitFlags::NO_COMMENTS;
        ec.borrow().add_emit_flags(statement, flags);
        ec.borrow().set_comment_range(statement, cx.nodes[property].loc);

        let property_original = ec.borrow().most_original(Some(property));
        if property_original.is_some_and(|o| ast::is_parameter_declaration(&cx.nodes[o])) {
            ec.borrow().set_source_map_range(
                statement,
                cx.nodes[property_original.unwrap()].loc,
            );
            ec.borrow().add_emit_flags(statement, EmitFlags::NO_COMMENTS);
        } else {
            ec.borrow().set_source_map_range(
                statement,
                transformer_utilities::move_range_past_modifiers(cx.nodes, property),
            );
        }

        // `setOriginalNode` *copies* the `emitNode` from `property`, so now both
        // `statement` and `expression` have a copy of the synthesized comments.
        // Drop the comments from expression to avoid printing them twice.
        ec.borrow()
            .set_synthetic_leading_comments(expression, Vec::new());
        ec.borrow()
            .set_synthetic_trailing_comments(expression, Vec::new());

        // If the property was originally an auto-accessor, don't emit comments here since they will
        // be attached to the synthesized getter.
        if property_original.is_some_and(|o| ast::has_accessor_modifier(&cx.nodes[o])) {
            ec.borrow().add_emit_flags(statement, EmitFlags::NO_COMMENTS);
        }

        Some(statement)
    }

    /// `generateInitializedPropertyExpressionsOrClassStaticBlock`.
    fn generate_initialized_property_expressions_or_class_static_block(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        properties_or_class_static_blocks: &[NodeId],
        receiver: NodeId,
    ) -> Vec<NodeId> {
        let mut expressions: Vec<NodeId> = Vec::new();
        for &property in properties_or_class_static_blocks {
            let expression = if ast::is_class_static_block_declaration(&cx.nodes[property]) {
                self.set_current_class_element_and(
                    ec,
                    Some(property),
                    Cb::TransformClassStaticBlockDeclaration,
                    cx,
                    property,
                )
            } else {
                self.transform_property(ec, cx, property, receiver)
            };
            let Some(expression) = expression else {
                continue;
            };
            ec.borrow().set_original_ex(expression, property, true);
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, expression, property);
            expressions.push(expression);
        }
        expressions
    }

    /// `transformProperty` — transforms a property initializer into an
    /// assignment expression.
    fn transform_property(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        property: NodeId,
        receiver: NodeId,
    ) -> Option<NodeId> {
        let saved_current_class_element = self.current_class_element.get();
        let transformed = self.transform_property_worker(ec, cx, property, receiver);
        if transformed.is_some() && ast::has_static_modifier(&cx.nodes[property]) {
            ec.borrow().add_emit_flags(
                transformed.unwrap(),
                EmitFlags::NO_LEXICAL_THIS,
            );
        }
        if transformed.is_some()
            && ast::has_static_modifier(&cx.nodes[property])
            && self
                .lexical_data()
                .is_some_and(|d| d.borrow().facts != CLASS_FACTS_NONE)
        {
            // capture the lexical environment for the member
            ec.borrow().set_original(transformed.unwrap(), property);
            let name_range = cx.nodes[property]
                .name()
                .map(|n| ec.borrow().source_map_range(cx.nodes, n))
                .unwrap_or_default();
            ec.borrow().set_source_map_range(transformed.unwrap(), name_range);
        }
        self.current_class_element.set(saved_current_class_element);
        transformed
    }

    /// `transformPropertyWorker`.
    fn transform_property_worker(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        property: NodeId,
        receiver: NodeId,
    ) -> Option<NodeId> {
        // We generate a name here in order to reuse the value cached by the relocated computed name
        // expression (which uses the same generated name)
        let emit_assignment = !self
            .compiler_options
            .map(|o| o.get_use_define_for_class_fields())
            .unwrap_or(false);

        let property = self.named_evaluation(ec, cx, property, false, "");

        let mut property_name = cx.nodes[property].name();
        if ast::has_accessor_modifier(&cx.nodes[property]) {
            property_name = Some(ec.borrow_mut().factory.new_generated_private_name_for_node_ex(
                cx.nodes,
                cx.nodes[property].name().expect("property name"),
                &AutoGenerateOptions {
                    suffix: "_accessor_storage".to_string(),
                    ..Default::default()
                },
            ));
        } else if property_name.is_some_and(|n| ast::is_computed_property_name(&cx.nodes[n]))
            && !cx.nodes[property_name.unwrap()]
                .expression()
                .is_some_and(|e| transformer_utilities::is_simple_inlineable_expression(&cx.nodes[e]))
        {
            let name = property_name.unwrap();
            let generated = ec
                .borrow_mut()
                .factory
                .new_generated_name_for_node(cx.nodes, name);
            property_name = Some(
                ec.borrow_mut()
                    .factory
                    .update_computed_property_name(cx.nodes, name, Some(generated))
                    .unwrap_or(name),
            );
        }

        if ast::has_static_modifier(&cx.nodes[property]) {
            self.current_class_element.set(Some(property));
        }

        if property_name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n]))
            && self.should_transform_class_element_to_weak_map(ec, cx, property)
        {
            let info = self.access_private_identifier(ec, cx, property_name.unwrap());
            if let Some(info) = info {
                if info.borrow().kind == PrivateIdentifierKind::Field {
                    if !info.borrow().is_static {
                        let initializer =
                            self.txv(ec).visit_node(cx, cx.nodes[property].initializer());
                        let initializer = initializer
                            .unwrap_or_else(|| {
                                ec.borrow_mut().factory.new_void_zero_expression(cx.nodes)
                            });
                        let receiver = self
                            .txv(ec)
                            .visit_node(cx, Some(receiver))
                            .unwrap_or(receiver);
                        let set_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "set");
                        let args = ec
                            .borrow_mut()
                            .factory
                            .new_node_list([receiver, initializer]);
                        let call = ec.borrow_mut().factory.new_method_call(
                            cx.nodes,
                            info.borrow().brand_check_identifier.expect("weakMapName"),
                            set_ident,
                            args.nodes.to_vec(),
                        );
                        return Some(call);
                    }
                    let initializer = self.txv(ec).visit_node(cx, cx.nodes[property].initializer());
                    return Some(create_private_static_field_initializer(
                        ec,
                        cx,
                        info.borrow().variable_name.expect("variableName"),
                        initializer,
                    ));
                }
                return None;
            }
            panic!("Undeclared private name for property declaration.");
        }

        if (property_name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n]))
            || ast::has_static_modifier(&cx.nodes[property]))
            && cx.nodes[property].initializer().is_none()
        {
            return None;
        }

        // TODO: can we get rid of this original checking and better coordinate with runtimesyntax?
        if ast::has_abstract_modifier(
            &cx.nodes[ec.borrow().most_original(Some(property)).unwrap_or(property)],
        ) {
            return None;
        }

        let mut initializer = self.txv(ec).visit_node(cx, cx.nodes[property].initializer());
        let property_original = ec.borrow().most_original(Some(property));
        if property_original.is_some_and(|o| {
            ast::is_parameter_property_declaration(
                &cx.nodes[o],
                cx.nodes[o].parent.map(|p| &cx.nodes[p]).unwrap_or(&cx.nodes[o]),
            )
        }) && property_name.is_some_and(|n| ast::is_identifier(&cx.nodes[n]))
        {
            // A parameter-property declaration always overrides the initializer. The only time a
            // parameter-property declaration *should* have an initializer is when decorators have
            // added initializers that need to run before any other initializer.
            let local_name = ec.borrow_mut().factory.clone_node(cx.nodes, property_name.unwrap());
            if let Some(mut unwrapped) = initializer {
                // unwrap `(__runInitializers(this, _instanceExtraInitializers), void 0)`
                if ast::is_parenthesized_expression(&cx.nodes[unwrapped]) {
                    let inner = cx.nodes[unwrapped]
                        .as_parenthesized_expression()
                        .expression;
                    if let Some(inner) = inner
                        && ast::is_comma_expression(&cx.nodes[inner], cx.nodes)
                    {
                        let (l, r) = {
                            let b = cx.nodes[inner].as_binary_expression();
                            (b.left, b.right)
                        };
                        if let (Some(l), Some(r)) = (l, r)
                            && ec.borrow().is_call_to_helper(cx.nodes, l, "__runInitializers")
                            && ast::is_void_expression(&cx.nodes[r])
                            && cx.nodes[r]
                                .expression()
                                .is_some_and(|e| ast::is_numeric_literal(&cx.nodes[e]))
                        {
                            unwrapped = l;
                        }
                    }
                }
                initializer = ec
                    .borrow_mut()
                    .factory
                    .inline_expressions(cx.nodes, &[unwrapped, local_name]);
            } else {
                initializer = Some(local_name);
            }
            ec.borrow().add_emit_flags(
                property_name.unwrap(),
                EmitFlags::NO_COMMENTS | EmitFlags::NO_SOURCE_MAP,
            );
            if let Some(orig_name) = cx.nodes[property_original.unwrap()].name() {
                ec.borrow()
                    .set_source_map_range(local_name, cx.nodes[orig_name].loc);
            }
            ec.borrow().add_emit_flags(local_name, EmitFlags::NO_COMMENTS);
        } else if initializer.is_none() {
            initializer = Some(ec.borrow_mut().factory.new_void_zero_expression(cx.nodes));
        }

        if emit_assignment
            || property_name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n]))
        {
            let member_access = create_member_access_for_property_name(
                ec,
                cx,
                receiver,
                property_name.unwrap(),
                property_name.unwrap(),
            );
            ec.borrow()
                .add_emit_flags(member_access, EmitFlags::NO_LEADING_COMMENTS);
            return Some(ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                member_access,
                initializer.unwrap(),
            ));
        }

        // useDefineForClassFields: Object.defineProperty
        let name = if property_name.is_some_and(|n| ast::is_computed_property_name(&cx.nodes[n])) {
            cx.nodes[property_name.unwrap()].expression().unwrap()
        } else if property_name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
            let text = cx.nodes[property_name.unwrap()].as_identifier().text.clone();
            ec.borrow_mut()
                .factory
                .new_string_literal(cx.nodes, &text, TokenFlags::NONE)
        } else {
            property_name.unwrap()
        };
        let mut descriptor_props: Vec<NodeId> = Vec::with_capacity(4);
        for (prop_name, value_expr) in [
            ("enumerable", None),
            ("configurable", None),
            ("writable", None),
            ("value", initializer),
        ] {
            let ident = ec.borrow_mut().factory.new_identifier(cx.nodes, prop_name);
            let init = match value_expr {
                Some(v) => v,
                None => ec.borrow_mut().factory.new_true_expression(cx.nodes),
            };
            let prop = ec.borrow_mut().factory.new_property_assignment(
                cx.nodes,
                None,
                Some(ident),
                None,
                None,
                Some(init),
            );
            descriptor_props.push(prop);
        }
        let props = ec.borrow_mut().factory.new_node_list(descriptor_props);
        let descriptor = ec.borrow_mut().factory.new_object_literal_expression(
            cx.nodes,
            Some(props),
            true,
        );
        Some(ec.borrow_mut().factory.new_object_define_property_call(
            cx.nodes,
            receiver,
            name,
            descriptor,
        ))
    }

    /// `addInstanceMethodStatements` — generates brand-check initializer for
    /// private methods.
    fn add_instance_method_statements(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        methods: &[NodeId],
        receiver: NodeId,
    ) -> Vec<NodeId> {
        if !self
            .should_transform_private_elements_or_class_static_blocks
            .get()
            || methods.is_empty()
        {
            return statements;
        }

        let env = self.get_private_identifier_environment();
        let weak_set_name = env.borrow().data.weak_set_name;
        debug_assert!(weak_set_name.is_some(), "weakSetName should be set in private identifier environment");
        let weak_set_name = weak_set_name.expect("weakSetName");

        let add_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "add");
        let call = ec.borrow_mut().factory.new_method_call(
            cx.nodes,
            weak_set_name,
            add_ident,
            vec![receiver],
        );
        let stmt = ec.borrow_mut().factory.new_expression_statement(cx.nodes, Some(call));
        statements.push(stmt);
        statements
    }

    /// `visitInvalidSuperProperty`.
    fn visit_invalid_super_property(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let void_zero = ec.borrow_mut().factory.new_void_zero_expression(cx.nodes);
        if ast::is_property_access_expression(&cx.nodes[node]) {
            let (name, flags) = {
                let pa = cx.nodes[node].as_property_access_expression();
                (pa.name, cx.nodes[node].flags)
            };
            return ec
                .borrow_mut()
                .factory
                .update_property_access_expression(
                    cx.nodes,
                    node,
                    Some(void_zero),
                    None,
                    name,
                    flags,
                )
                .unwrap_or(node);
        }
        let (argument_expression, flags) = {
            let ea = cx.nodes[node].as_element_access_expression();
            (ea.argument_expression, cx.nodes[node].flags)
        };
        let visited_arg = self.txv(ec).visit_node(cx, argument_expression);
        ec.borrow_mut()
            .factory
            .update_element_access_expression(
                cx.nodes,
                node,
                Some(void_zero),
                None,
                visited_arg,
                flags,
            )
            .unwrap_or(node)
    }

    /// `getPropertyNameExpressionIfNeeded` — transforms a computed property
    /// name, then either returns an expression which caches the value of the
    /// result or the expression itself if the value is either unused or safe
    /// to inline into multiple locations.
    fn get_property_name_expression_if_needed(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: Option<NodeId>,
        should_hoist: bool,
    ) -> Option<NodeId> {
        let name = name?;
        if !ast::is_computed_property_name(&cx.nodes[name]) {
            return None;
        }
        let cache_assignment = find_computed_property_name_cache_assignment(cx.nodes, name);
        // Switch to outer lex env for computed property name expressions.
        let saved_inside = self.inside_computed_property_name.replace(true);
        let popped = {
            let mut stack = self.lexical_environment.borrow_mut();
            if stack.len() >= 2 { stack.pop() } else { None }
        };
        let expression_node = cx.nodes[name].expression();
        let expression = self.txv(ec).visit_node(cx, expression_node);
        if let Some(frame) = popped {
            self.lexical_environment.borrow_mut().push(frame);
        }
        self.inside_computed_property_name.set(saved_inside);
        let expression = expression?;
        let inner_expression = ast::skip_partially_emitted_expressions(expression, cx.nodes);
        let inlinable =
            transformer_utilities::is_simple_inlineable_expression(&cx.nodes[inner_expression]);
        let already_transformed = cache_assignment.is_some()
            || (ast::is_assignment_expression(&cx.nodes[inner_expression], cx.nodes, true)
                && cx.nodes[inner_expression]
                    .as_binary_expression()
                    .left
                    .is_some_and(|l| {
                        ast::is_identifier(&cx.nodes[l])
                            && transformer_utilities::is_generated_identifier(&ec.borrow(), l)
                    }));
        if !already_transformed && !inlinable && should_hoist {
            let generated_name = ec
                .borrow_mut()
                .factory
                .new_generated_name_for_node(cx.nodes, name);
            if self.requires_block_scoped_var(cx) {
                ec.borrow_mut().add_lexical_declaration(cx.nodes, generated_name);
            } else {
                ec.borrow_mut().add_variable_declaration(cx.nodes, generated_name);
            }
            return Some(ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                generated_name,
                expression,
            ));
        }
        if inlinable || ast::is_identifier(&cx.nodes[inner_expression]) {
            return None;
        }
        Some(expression)
    }

    /// `startClassLexicalEnvironment`.
    fn start_class_lexical_environment(&self) {
        self.lexical_environment
            .borrow_mut()
            .push(ClassLexicalEnvFrame::default());
    }

    /// `endClassLexicalEnvironment`.
    fn end_class_lexical_environment(&self) {
        self.lexical_environment.borrow_mut().pop();
    }

    /// `getClassLexicalEnvironment`.
    fn get_class_lexical_environment(
        &self,
    ) -> Rc<RefCell<ClassLexicalEnvironment>> {
        let mut stack = self.lexical_environment.borrow_mut();
        let frame = stack.last_mut().expect("lexicalEnvironment");
        if frame.data.is_none() {
            frame.data = Some(Rc::new(RefCell::new(ClassLexicalEnvironment::default())));
        }
        frame.data.as_ref().unwrap().clone()
    }

    /// `getPrivateIdentifierEnvironment`.
    fn get_private_identifier_environment(&self) -> Rc<RefCell<PrivateEnvironment>> {
        let mut stack = self.lexical_environment.borrow_mut();
        let frame = stack.last_mut().expect("lexicalEnvironment");
        if frame.private_env.is_none() {
            frame.private_env = Some(Rc::new(RefCell::new(PrivateEnvironment::default())));
        }
        frame.private_env.as_ref().unwrap().clone()
    }

    /// `addPendingExpressions`.
    fn add_pending_expressions(&self, exprs: &[NodeId]) {
        self.pending_expressions.borrow_mut().extend_from_slice(exprs);
    }

    /// `addPrivateIdentifierPropertyDeclarationToEnvironment`.
    fn add_private_identifier_property_declaration_to_environment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        name: NodeId,
    ) {
        let lex = self.get_class_lexical_environment();
        let env = self.get_private_identifier_environment();
        let is_static = ast::has_static_modifier(&cx.nodes[node]);
        let previous_info = self.get_private_identifier(ec, cx.nodes, &env, name);
        let is_valid = !self.is_reserved_private_name(ec, cx, name) && previous_info.is_none();

        if is_static {
            let brand_check_identifier = lex
                .borrow()
                .class_this
                .or(lex.borrow().class_constructor);
            let variable_name = self.create_hoisted_variable_for_private_name(ec, cx, name, "");
            self.set_private_identifier(
                ec,
                cx,
                &env,
                name,
                PrivateIdentifierInfo {
                    kind: PrivateIdentifierKind::Field,
                    is_static: true,
                    brand_check_identifier,
                    variable_name: Some(variable_name),
                    is_valid,
                    ..Default::default()
                },
            );
        } else {
            let weak_map_name = self.create_hoisted_variable_for_private_name(ec, cx, name, "");
            self.set_private_identifier(
                ec,
                cx,
                &env,
                name,
                PrivateIdentifierInfo {
                    kind: PrivateIdentifierKind::Field,
                    is_static: false,
                    brand_check_identifier: Some(weak_map_name),
                    is_valid,
                    ..Default::default()
                },
            );
            let weakmap_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "WeakMap");
            let args = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
            let new_expr = ec.borrow_mut().factory.new_new_expression(
                cx.nodes,
                Some(weakmap_ident),
                None,
                Some(args),
            );
            let assignment = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                weak_map_name,
                new_expr,
            );
            self.add_pending_expressions(&[assignment]);
        }
    }

    /// `brandCheckForStaticOrWeakSet` — shared brand-check identifier lookup
    /// used by the method/accessor environment helpers.
    fn brand_check_for(&self, is_static: bool) -> Option<NodeId> {
        let lex = self.get_class_lexical_environment();
        let env = self.get_private_identifier_environment();
        if is_static {
            let b = lex.borrow().class_this.or(lex.borrow().class_constructor);
            debug_assert!(b.is_some(), "classConstructor should be set in private identifier environment");
            b
        } else {
            let b = env.borrow().data.weak_set_name;
            debug_assert!(b.is_some(), "weakSetName should be set in private identifier environment");
            b
        }
    }

    /// `addPrivateIdentifierMethodToEnvironment`.
    fn add_private_identifier_method_to_environment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        is_static: bool,
        is_valid: bool,
    ) {
        let method_name = self.create_hoisted_variable_for_private_name(ec, cx, name, "");
        let brand_check_identifier = self.brand_check_for(is_static);
        let env = self.get_private_identifier_environment();
        self.set_private_identifier(
            ec,
            cx,
            &env,
            name,
            PrivateIdentifierInfo {
                kind: PrivateIdentifierKind::Method,
                method_name: Some(method_name),
                brand_check_identifier,
                is_static,
                is_valid,
                ..Default::default()
            },
        );
    }

    /// `addPrivateIdentifierGetAccessorToEnvironment`.
    fn add_private_identifier_get_accessor_to_environment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        is_static: bool,
        is_valid: bool,
        previous_info: Option<Rc<RefCell<PrivateIdentifierInfo>>>,
    ) {
        let getter_name = self.create_hoisted_variable_for_private_name(ec, cx, name, "_get");
        let brand_check_identifier = self.brand_check_for(is_static);

        let env = self.get_private_identifier_environment();
        if let Some(previous_info) = previous_info
            && previous_info.borrow().kind == PrivateIdentifierKind::Accessor
            && previous_info.borrow().is_static == is_static
            && previous_info.borrow().getter_name.is_none()
        {
            previous_info.borrow_mut().getter_name = Some(getter_name);
        } else {
            self.set_private_identifier(
                ec,
                cx,
                &env,
                name,
                PrivateIdentifierInfo {
                    kind: PrivateIdentifierKind::Accessor,
                    getter_name: Some(getter_name),
                    brand_check_identifier,
                    is_static,
                    is_valid,
                    ..Default::default()
                },
            );
        }
    }

    /// `addPrivateIdentifierSetAccessorToEnvironment`.
    fn add_private_identifier_set_accessor_to_environment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        is_static: bool,
        is_valid: bool,
        previous_info: Option<Rc<RefCell<PrivateIdentifierInfo>>>,
    ) {
        let setter_name = self.create_hoisted_variable_for_private_name(ec, cx, name, "_set");
        let brand_check_identifier = self.brand_check_for(is_static);

        let env = self.get_private_identifier_environment();
        if let Some(previous_info) = previous_info
            && previous_info.borrow().kind == PrivateIdentifierKind::Accessor
            && previous_info.borrow().is_static == is_static
            && previous_info.borrow().setter_name.is_none()
        {
            previous_info.borrow_mut().setter_name = Some(setter_name);
        } else {
            self.set_private_identifier(
                ec,
                cx,
                &env,
                name,
                PrivateIdentifierInfo {
                    kind: PrivateIdentifierKind::Accessor,
                    setter_name: Some(setter_name),
                    brand_check_identifier,
                    is_static,
                    is_valid,
                    ..Default::default()
                },
            );
        }
    }

    /// `addPrivateIdentifierAutoAccessorToEnvironment`.
    fn add_private_identifier_auto_accessor_to_environment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        is_static: bool,
        is_valid: bool,
    ) {
        let getter_name = self.create_hoisted_variable_for_private_name(ec, cx, name, "_get");
        let setter_name = self.create_hoisted_variable_for_private_name(ec, cx, name, "_set");
        let brand_check_identifier = self.brand_check_for(is_static);

        let env = self.get_private_identifier_environment();
        self.set_private_identifier(
            ec,
            cx,
            &env,
            name,
            PrivateIdentifierInfo {
                kind: PrivateIdentifierKind::Accessor,
                getter_name: Some(getter_name),
                setter_name: Some(setter_name),
                brand_check_identifier,
                is_static,
                is_valid,
                ..Default::default()
            },
        );
    }

    /// `addPrivateIdentifierToEnvironment`.
    fn add_private_identifier_to_environment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) {
        let env = self.get_private_identifier_environment();
        let name = cx.nodes[node].name().expect("member name");
        let is_static = ast::has_static_modifier(&cx.nodes[node]);
        let previous_info = self.get_private_identifier(ec, cx.nodes, &env, name);
        let is_valid = !self.is_reserved_private_name(ec, cx, name) && previous_info.is_none();

        if ast::is_auto_accessor_property_declaration(&cx.nodes[node]) {
            self.add_private_identifier_auto_accessor_to_environment(
                ec, cx, name, is_static, is_valid,
            );
        } else if ast::is_property_declaration(&cx.nodes[node]) {
            self.add_private_identifier_property_declaration_to_environment(
                ec, cx, node, name,
            );
        } else if ast::is_method_declaration(&cx.nodes[node]) {
            self.add_private_identifier_method_to_environment(ec, cx, name, is_static, is_valid);
        } else if ast::is_get_accessor_declaration(&cx.nodes[node]) {
            self.add_private_identifier_get_accessor_to_environment(
                ec,
                cx,
                name,
                is_static,
                is_valid,
                previous_info,
            );
        } else if ast::is_set_accessor_declaration(&cx.nodes[node]) {
            self.add_private_identifier_set_accessor_to_environment(
                ec,
                cx,
                name,
                is_static,
                is_valid,
                previous_info,
            );
        }
    }

    /// `setPrivateIdentifier`.
    fn set_private_identifier(
        &self,
        ec: &Ec,
        cx: &VisitorCx<'_, '_>,
        env: &Rc<RefCell<PrivateEnvironment>>,
        name: NodeId,
        info: PrivateIdentifierInfo,
    ) {
        if ec.borrow().has_auto_generate_info(Some(name)) {
            let key = ec.borrow().get_node_for_generated_name(cx.nodes, name);
            env.borrow_mut()
                .generated_identifiers
                .insert(key, Rc::new(RefCell::new(info)));
        } else {
            let text = cx.nodes[name].text(cx.nodes);
            env.borrow_mut()
                .members
                .insert(text.into_owned(), Rc::new(RefCell::new(info)));
        }
    }

    /// `getPrivateIdentifier` — returns the info if present.
    fn get_private_identifier(
        &self,
        ec: &Ec,
        nodes: &[tsc_ast::Node],
        env: &Rc<RefCell<PrivateEnvironment>>,
        name: NodeId,
    ) -> Option<Rc<RefCell<PrivateIdentifierInfo>>> {
        if ec.borrow().has_auto_generate_info(Some(name)) {
            let key = ec.borrow().get_node_for_generated_name(nodes, name);
            return env.borrow().generated_identifiers.get(&key).cloned();
        }
        let text = nodes[name].text(nodes);
        env.borrow().members.get(text.as_ref()).cloned()
    }

    /// `accessPrivateIdentifier` — accesses an already defined
    /// PrivateIdentifier in the current PrivateIdentifierEnvironment.
    fn access_private_identifier(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
    ) -> Option<Rc<RefCell<PrivateIdentifierInfo>>> {
        let stack_snapshot: Vec<Option<Rc<RefCell<PrivateEnvironment>>>> = self
            .lexical_environment
            .borrow()
            .iter()
            .map(|f| f.private_env.clone())
            .collect();
        for private_env in stack_snapshot.into_iter().rev() {
            if let Some(env) = private_env {
                if let Some(info) = self.get_private_identifier(ec, cx.nodes, &env, name)
                    && info.borrow().kind != PrivateIdentifierKind::Untransformed
                {
                    return Some(info);
                }
            }
        }
        None
    }

    /// `createHoistedVariableForClass`.
    fn create_hoisted_variable_for_class(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name_text: &str,
        _node: Option<NodeId>,
        suffix: &str,
    ) -> NodeId {
        let env = self.get_private_identifier_environment();
        let class_name = env.borrow().data.class_name;
        let identifier = if let Some(class_name) = class_name {
            let prefix = format!("_{}_", cx.nodes[class_name].text(cx.nodes));
            ec.borrow_mut().factory.new_unique_name_ex(
                cx.nodes,
                &format!("{prefix}{name_text}"),
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC
                        | GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                    suffix: suffix.to_string(),
                    ..Default::default()
                },
            )
        } else {
            ec.borrow_mut().factory.new_unique_name_ex(
                cx.nodes,
                &format!("_{name_text}"),
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC
                        | GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                    suffix: suffix.to_string(),
                    ..Default::default()
                },
            )
        };
        if self.requires_block_scoped_var(cx) {
            ec.borrow_mut().add_lexical_declaration(cx.nodes, identifier);
        } else {
            ec.borrow_mut().add_variable_declaration(cx.nodes, identifier);
        }
        identifier
    }

    /// `createHoistedVariableForClassFromNode`.
    fn create_hoisted_variable_for_class_from_node(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        suffix: &str,
    ) -> NodeId {
        let env = self.get_private_identifier_environment();
        let class_name = env.borrow().data.class_name;
        let prefix = if let Some(class_name) = class_name {
            format!("_{}_", cx.nodes[class_name].text(cx.nodes))
        } else {
            "_".to_string()
        };
        let identifier = ec.borrow_mut().factory.new_generated_name_for_node_ex(
            cx.nodes,
            name,
            &AutoGenerateOptions {
                flags: GeneratedIdentifierFlags::OPTIMISTIC
                    | GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                prefix,
                suffix: suffix.to_string(),
                ..Default::default()
            },
        );
        if self.requires_block_scoped_var(cx) {
            ec.borrow_mut().add_lexical_declaration(cx.nodes, identifier);
        } else {
            ec.borrow_mut().add_variable_declaration(cx.nodes, identifier);
        }
        identifier
    }

    /// `createHoistedVariableForPrivateName`.
    fn create_hoisted_variable_for_private_name(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        suffix: &str,
    ) -> NodeId {
        // If the name is a generated identifier (e.g., auto-accessor backing field),
        // use node-based name generation so the emitter can resolve the name properly.
        if ec.borrow().has_auto_generate_info(Some(name)) {
            return self.create_hoisted_variable_for_class_from_node(ec, cx, name, suffix);
        }
        let mut text = cx.nodes[name].text(cx.nodes).into_owned();
        if text.starts_with('#') {
            text = text[1..].to_string(); // strip leading '#'
        }
        self.create_hoisted_variable_for_class(ec, cx, &text, Some(name), suffix)
    }

    /// `wrapPrivateIdentifierForDestructuringTarget`.
    fn wrap_private_identifier_for_destructuring_target(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, name) = {
            let pa = cx.nodes[node].as_property_access_expression();
            (pa.expression, pa.name)
        };
        let parameter = ec
            .borrow_mut()
            .factory
            .new_generated_name_for_node(cx.nodes, node);
        let Some(info) = self.access_private_identifier(ec, cx, name.expect("name")) else {
            return self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
        };
        let mut receiver = expression.expect("receiver");
        // We cannot copy `this` or `super` into the function because they will be bound
        // differently inside the function.
        let is_this_or_super_property = cx.nodes[receiver].kind == Kind::ThisKeyword
            || cx.nodes[receiver].kind == Kind::SuperKeyword;
        if is_this_or_super_property
            || !transformer_utilities::is_simple_copiable_expression(&cx.nodes[receiver])
        {
            receiver = ec.borrow_mut().factory.new_temp_variable_ex(
                cx.nodes,
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
                    ..Default::default()
                },
            );
            ec.borrow_mut().add_variable_declaration(cx.nodes, receiver);
            let visited = self.txv(ec).visit_node(cx, expression);
            let assignment = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                receiver,
                visited.expect("receiver"),
            );
            self.pending_expressions.borrow_mut().push(assignment);
        }
        let assign_expr = self.create_private_identifier_assignment(
            ec,
            cx,
            &info,
            receiver,
            parameter,
            Kind::EqualsToken,
        );
        ec.borrow_mut()
            .factory
            .new_assignment_target_wrapper(cx.nodes, parameter, assign_expr)
    }

    /// `visitAssignmentElement`.
    fn visit_assignment_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // 13.15.5.5 RS: IteratorDestructuringAssignmentEvaluation — see esdecorator.rs.
        let node = self.named_evaluation(ec, cx, node, false, "");
        if ast::is_assignment_expression(&cx.nodes[node], cx.nodes, true) {
            let (left, operator_token, right) = {
                let bin = cx.nodes[node].as_binary_expression();
                (bin.left, bin.operator_token, bin.right)
            };
            let left = self.visit_destructuring_assignment_target(ec, cx, left.expect("lhs"));
            let right = self.txv(ec).visit_node(cx, right);
            return ec
                .borrow_mut()
                .factory
                .update_binary_expression(
                    cx.nodes,
                    node,
                    None,
                    Some(left),
                    None,
                    operator_token,
                    right,
                )
                .unwrap_or(node);
        }
        self.visit_destructuring_assignment_target(ec, cx, node)
    }

    /// `visitAssignmentRestElement`.
    fn visit_assignment_rest_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let expression = cx.nodes[node].as_spread_element().expression;
        if expression.is_some_and(|e| ast::is_left_hand_side_expression(&cx.nodes[e], cx.nodes)) {
            let expr = self.visit_destructuring_assignment_target(ec, cx, expression.unwrap());
            return ec
                .borrow_mut()
                .factory
                .update_spread_element(cx.nodes, node, Some(expr))
                .unwrap_or(node);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitArrayAssignmentElement` — the `arrayAssignmentElementVisitor` callback.
    fn visit_array_assignment_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if ast::is_array_binding_or_assignment_element(&cx.nodes[node], cx.nodes) {
            if ast::is_spread_element(&cx.nodes[node]) {
                return Some(self.visit_assignment_rest_element(ec, cx, node));
            }
            if cx.nodes[node].kind != Kind::OmittedExpression {
                return Some(self.visit_assignment_element(ec, cx, node));
            }
        }
        self.txv(ec).visit_each_child(cx, node).or(Some(node))
    }

    /// `visitAssignmentProperty`.
    fn visit_assignment_property(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // AssignmentProperty : PropertyName `:` AssignmentElement
        // 13.15.5.6 RS: KeyedDestructuringAssignmentEvaluation
        let (name, initializer) = {
            let pa = cx.nodes[node].as_property_assignment();
            (pa.named_member_base.name, pa.initializer)
        };
        let name = self.txv(ec).visit_node(cx, name);
        if initializer.is_some_and(|i| ast::is_assignment_expression(&cx.nodes[i], cx.nodes, true)) {
            let assign_elem = self.visit_assignment_element(ec, cx, initializer.unwrap());
            return ec
                .borrow_mut()
                .factory
                .update_property_assignment(cx.nodes, node, None, name, None, None, Some(assign_elem))
                .unwrap_or(node);
        }
        if initializer.is_some_and(|i| ast::is_left_hand_side_expression(&cx.nodes[i], cx.nodes)) {
            let target =
                self.visit_destructuring_assignment_target(ec, cx, initializer.unwrap());
            return ec
                .borrow_mut()
                .factory
                .update_property_assignment(cx.nodes, node, None, name, None, None, Some(target))
                .unwrap_or(node);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitShorthandAssignmentProperty`.
    fn visit_shorthand_assignment_property(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // AssignmentProperty : IdentifierReference Initializer?
        // 13.15.5.3 RS: PropertyDestructuringAssignmentEvaluation
        let node = self.named_evaluation(ec, cx, node, false, "");
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitAssignmentRestProperty`.
    fn visit_assignment_rest_property(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let expression = cx.nodes[node].as_spread_assignment().expression;
        if expression.is_some_and(|e| ast::is_left_hand_side_expression(&cx.nodes[e], cx.nodes)) {
            let expr = self.visit_destructuring_assignment_target(ec, cx, expression.unwrap());
            return ec
                .borrow_mut()
                .factory
                .update_spread_assignment(cx.nodes, node, Some(expr))
                .unwrap_or(node);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitObjectAssignmentElement` — the `objectAssignmentElementVisitor` callback.
    fn visit_object_assignment_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        debug_assert!(ast::is_object_literal_element(&cx.nodes[node]));
        if ast::is_spread_assignment(&cx.nodes[node]) {
            return Some(self.visit_assignment_rest_property(ec, cx, node));
        }
        if ast::is_shorthand_property_assignment(&cx.nodes[node]) {
            return Some(self.visit_shorthand_assignment_property(ec, cx, node));
        }
        if ast::is_property_assignment(&cx.nodes[node]) {
            return Some(self.visit_assignment_property(ec, cx, node));
        }
        self.txv(ec).visit_each_child(cx, node).or(Some(node))
    }

    /// `visitAssignmentPattern`.
    fn visit_assignment_pattern(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if ast::is_array_literal_expression(&cx.nodes[node]) {
            // Transforms private names and super property assignments in destructuring
            // assignment array bindings.
            let (elements, multi_line) = {
                let ale = cx.nodes[node].as_array_literal_expression();
                (ale.elements.clone(), ale.multi_line)
            };
            let elements =
                vref!(self, array_assignment_element_visitor).visit_nodes(cx, elements);
            return ec
                .borrow_mut()
                .factory
                .update_array_literal_expression(cx.nodes, node, elements, multi_line)
                .unwrap_or(node);
        }
        // Transforms private names and super property assignments in destructuring
        // assignment object bindings.
        let (properties, multi_line) = {
            let ole = cx.nodes[node].as_object_literal_expression();
            (ole.properties.clone(), ole.multi_line)
        };
        let properties =
            vref!(self, object_assignment_element_visitor).visit_nodes(cx, properties);
        ec.borrow_mut()
            .factory
            .update_object_literal_expression(cx.nodes, node, properties, multi_line)
            .unwrap_or(node)
    }

    /// `isReservedPrivateName`.
    fn is_reserved_private_name(&self, ec: &Ec, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        !(ast::is_private_identifier(&cx.nodes[node]) && ec.borrow().has_auto_generate_info(Some(node)))
            && cx.nodes[node].text(cx.nodes) == "#constructor"
    }

    /// `getProperties`.
    fn get_properties(
        &self,
        nodes: &[tsc_ast::Node],
        node: NodeId,
        require_initializer: bool,
        is_static: bool,
    ) -> Vec<NodeId> {
        let mut result = Vec::new();
        for member in nodes[node].members().unwrap_or(&[]) {
            if ast::is_property_declaration(&nodes[*member])
                && (!require_initializer || nodes[*member].initializer().is_some())
                && ast::has_static_modifier(&nodes[*member]) == is_static
            {
                result.push(*member);
            }
        }
        result
    }

    /// `getStaticPropertiesAndClassStaticBlock`.
    fn get_static_properties_and_class_static_block(
        &self,
        nodes: &[tsc_ast::Node],
        node: NodeId,
    ) -> Vec<NodeId> {
        let mut result = Vec::new();
        for member in nodes[node].members().unwrap_or(&[]) {
            if ast::is_class_static_block_declaration(&nodes[*member])
                || (ast::is_property_declaration(&nodes[*member])
                    && ast::has_static_modifier(&nodes[*member]))
            {
                result.push(*member);
            }
        }
        result
    }

    /// `createCallBinding` — returns `(thisArg, target)` — NOTE: Go returns
    /// `(thisArg, target)`, opposite order to esdecorator's `(target, thisArg)`.
    fn create_call_binding(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> (NodeId, NodeId) {
        if ast::is_super_property(&cx.nodes[node], cx.nodes) {
            let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
            return (this_expr, node);
        }
        if ast::is_property_access_expression(&cx.nodes[node]) {
            let (expression, name) = {
                let pa = cx.nodes[node].as_property_access_expression();
                (pa.expression, pa.name)
            };
            if should_be_captured_in_temp_variable(cx.nodes, expression.expect("receiver")) {
                let this_arg = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                ec.borrow_mut().add_variable_declaration(cx.nodes, this_arg);
                let assign = ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    this_arg,
                    expression.unwrap(),
                );
                let paren = ec.borrow_mut().factory.new_parenthesized_expression(
                    cx.nodes,
                    Some(assign),
                );
                let target = ec.borrow_mut().factory.new_property_access_expression(
                    cx.nodes,
                    Some(paren),
                    None,
                    name,
                    NodeFlags::NONE,
                );
                return (this_arg, target);
            }
            return (expression.unwrap(), node);
        }
        let void_zero = ec.borrow_mut().factory.new_void_zero_expression(cx.nodes);
        (void_zero, node)
    }

    /// `createAccessorPropertyGetRedirector` — creates a GetAccessor that
    /// forwards to the private backing field of an auto-accessor.
    fn create_accessor_property_get_redirector(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        modifiers: Option<ModifierList>,
        name: Option<NodeId>,
        receiver: NodeId,
    ) -> NodeId {
        let backing_field_name = ec.borrow_mut().factory.new_generated_private_name_for_node_ex(
            cx.nodes,
            cx.nodes[node].name().expect("node name"),
            &AutoGenerateOptions {
                suffix: "_accessor_storage".to_string(),
                ..Default::default()
            },
        );
        let return_expr = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(receiver),
            None,
            Some(backing_field_name),
            NodeFlags::NONE,
        );
        let return_stmt = ec
            .borrow_mut()
            .factory
            .new_return_statement(cx.nodes, Some(return_expr));
        let stmts = ec.borrow_mut().factory.new_node_list([return_stmt]);
        let body = ec.borrow_mut().factory.new_block(cx.nodes, Some(stmts), false);
        let params = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
        ec.borrow_mut().factory.new_get_accessor_declaration(
            cx.nodes,
            modifiers,
            name,
            None,
            Some(params),
            None,
            None,
            Some(body),
        )
    }

    /// `createAccessorPropertySetRedirector` — creates a SetAccessor that
    /// forwards to the private backing field of an auto-accessor.
    fn create_accessor_property_set_redirector(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        modifiers: Option<ModifierList>,
        name: Option<NodeId>,
        receiver: NodeId,
    ) -> NodeId {
        let backing_field_name = ec.borrow_mut().factory.new_generated_private_name_for_node_ex(
            cx.nodes,
            cx.nodes[node].name().expect("node name"),
            &AutoGenerateOptions {
                suffix: "_accessor_storage".to_string(),
                ..Default::default()
            },
        );
        let value_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "value");
        let value_param = ec.borrow_mut().factory.new_parameter_declaration(
            cx.nodes,
            None,
            None,
            Some(value_ident),
            None,
            None,
            None,
        );
        let access = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(receiver),
            None,
            Some(backing_field_name),
            NodeFlags::NONE,
        );
        let value_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "value");
        let assign_expr = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            access,
            value_ident,
        );
        let expr_stmt = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(assign_expr));
        let stmts = ec.borrow_mut().factory.new_node_list([expr_stmt]);
        let body = ec.borrow_mut().factory.new_block(cx.nodes, Some(stmts), false);
        let params = ec.borrow_mut().factory.new_node_list([value_param]);
        ec.borrow_mut().factory.new_set_accessor_declaration(
            cx.nodes,
            modifiers,
            name,
            None,
            Some(params),
            None,
            None,
            Some(body),
        )
    }
}

/// `cx_body` — `member.AsClassStaticBlockDeclaration().Body` accessor.
fn cx_body(nodes: &[tsc_ast::Node], member: NodeId) -> Option<NodeId> {
    nodes[member].as_class_static_block_declaration().body
}

/// `classHasClassThisAssignment` — checks if a class has a static block that
/// is a class-this assignment.
pub(crate) fn class_has_class_this_assignment(
    emit_context: &tsc_printer::EmitContext,
    nodes: &[tsc_ast::Node],
    node: NodeId,
) -> bool {
    for member in nodes[node].members().unwrap_or(&[]) {
        if is_class_this_assignment_block(emit_context, nodes, *member) {
            return true;
        }
    }
    false
}

/// `isStaticPropertyDeclarationOrClassStaticBlock`.
fn is_static_property_declaration_or_class_static_block(node: &tsc_ast::Node) -> bool {
    ast::is_class_static_block_declaration(node)
        || (ast::is_property_declaration(node) && ast::has_static_modifier(node))
}

/// `isNonStaticMethodOrAccessorWithPrivateName`.
fn is_non_static_method_or_accessor_with_private_name(
    nodes: &[tsc_ast::Node],
    member: NodeId,
) -> bool {
    !ast::is_static(&nodes[member])
        && (ast::is_method_or_accessor(&nodes[member])
            || ast::is_auto_accessor_property_declaration(&nodes[member]))
        && nodes[member]
            .name()
            .is_some_and(|n| ast::is_private_identifier(&nodes[n]))
}

/// `shouldBeCapturedInTempVariable`.
fn should_be_captured_in_temp_variable(nodes: &[tsc_ast::Node], node: NodeId) -> bool {
    let target = ast::skip_parentheses(node, nodes);
    !matches!(
        nodes[target].kind,
        Kind::Identifier | Kind::ThisKeyword | Kind::NumericLiteral | Kind::BigIntLiteral | Kind::StringLiteral
    )
}

/// `createMemberAccessForPropertyName`.
fn create_member_access_for_property_name(
    ec: &Ec,
    cx: &mut VisitorCx<'_, '_>,
    receiver: NodeId,
    name: NodeId,
    location: NodeId,
) -> NodeId {
    if ast::is_computed_property_name(&cx.nodes[name]) {
        let expression = cx.nodes[name].expression();
        let access = ec.borrow_mut().factory.new_element_access_expression(
            cx.nodes,
            Some(receiver),
            None,
            expression,
            NodeFlags::NONE,
        );
        cx.nodes[access].loc = cx.nodes[location].loc;
        return access;
    }
    let expression = if ast::is_identifier(&cx.nodes[name])
        || ast::is_private_identifier(&cx.nodes[name])
    {
        ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(receiver),
            None,
            Some(name),
            NodeFlags::NONE,
        )
    } else {
        // string or numeric literal
        ec.borrow_mut().factory.new_element_access_expression(
            cx.nodes,
            Some(receiver),
            None,
            Some(name),
            NodeFlags::NONE,
        )
    };
    ec.borrow().set_comment_range(expression, cx.nodes[name].loc);
    ec.borrow().set_source_map_range(expression, cx.nodes[name].loc);
    ec.borrow()
        .add_emit_flags(expression, EmitFlags::NO_NESTED_SOURCE_MAPS);
    expression
}

/// `createPrivateStaticFieldInitializer`.
fn create_private_static_field_initializer(
    ec: &Ec,
    cx: &mut VisitorCx<'_, '_>,
    variable_name: NodeId,
    initializer: Option<NodeId>,
) -> NodeId {
    let initializer = initializer
        .unwrap_or_else(|| ec.borrow_mut().factory.new_void_zero_expression(cx.nodes));
    let value_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "value");
    let prop = ec.borrow_mut().factory.new_property_assignment(
        cx.nodes,
        None,
        Some(value_ident),
        None,
        None,
        Some(initializer),
    );
    let props = ec.borrow_mut().factory.new_node_list([prop]);
    let obj = ec.borrow_mut().factory.new_object_literal_expression(
        cx.nodes,
        Some(props),
        false,
    );
    ec.borrow_mut()
        .factory
        .new_assignment_expression(cx.nodes, variable_name, obj)
}

/// `flattenCommaList` decomposes a comma expression tree into a sequence of
/// expressions.
fn flatten_comma_list(nodes: &[tsc_ast::Node], node: NodeId) -> Vec<NodeId> {
    fn worker(nodes: &[tsc_ast::Node], node: NodeId, out: &mut Vec<NodeId>) {
        if ast::is_parenthesized_expression(&nodes[node])
            && ast::node_is_synthesized(&nodes[node])
        {
            if let Some(e) = nodes[node].expression() {
                worker(nodes, e, out);
            }
        } else if ast::is_comma_expression(&nodes[node], nodes) {
            let bin = nodes[node].as_binary_expression();
            if let Some(l) = bin.left {
                worker(nodes, l, out);
            }
            if let Some(r) = bin.right {
                worker(nodes, r, out);
            }
        } else {
            out.push(node);
        }
    }
    let mut out = Vec::new();
    worker(nodes, node, &mut out);
    out
}

/// `findComputedPropertyNameCacheAssignment`.
pub(crate) fn find_computed_property_name_cache_assignment(
    nodes: &[tsc_ast::Node],
    name: NodeId,
) -> Option<NodeId> {
    let mut node = nodes[name].expression();
    loop {
        let Some(n) = node else { return None };
        let next = ast::skip_outer_expressions(n, ast::OuterExpressionKinds(0), nodes);
        if ast::is_binary_expression(&nodes[next])
            && nodes[next]
                .as_binary_expression()
                .operator_token
                .is_some_and(|t| nodes[t].kind == Kind::CommaToken)
        {
            node = nodes[next].as_binary_expression().right;
            continue;
        }
        if ast::is_assignment_expression(&nodes[next], nodes, true)
            && nodes[next]
                .as_binary_expression()
                .left
                .is_some_and(|l| ast::is_identifier(&nodes[l]))
        {
            return Some(next);
        }
        return None;
    }
}

/// `expandPreOrPostfixIncrementOrDecrementExpression`.
pub(crate) fn expand_pre_or_postfix_increment_or_decrement_expression(
    ec: &Ec,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    expression: NodeId,
    result_variable: Option<NodeId>,
) -> NodeId {
    let (is_prefix, operator, operand) = if ast::is_prefix_unary_expression(&cx.nodes[node]) {
        let p = cx.nodes[node].as_prefix_unary_expression();
        (true, p.operator, p.operand)
    } else {
        let p = cx.nodes[node].as_postfix_unary_expression();
        (false, p.operator, p.operand)
    };

    let temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
    ec.borrow_mut().add_variable_declaration(cx.nodes, temp);
    let mut expression =
        ec.borrow_mut()
            .factory
            .new_assignment_expression(cx.nodes, temp, expression);
    if let Some(operand) = operand {
        cx.nodes[expression].loc = cx.nodes[operand].loc;
    }

    let mut operation = if is_prefix {
        ec.borrow_mut()
            .factory
            .new_prefix_unary_expression(cx.nodes, operator, Some(temp))
    } else {
        ec.borrow_mut()
            .factory
            .new_postfix_unary_expression(cx.nodes, Some(temp), operator)
    };
    cx.nodes[operation].loc = cx.nodes[node].loc;

    if let Some(result_variable) = result_variable {
        operation = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            result_variable,
            operation,
        );
        cx.nodes[operation].loc = cx.nodes[node].loc;
    }

    expression = ec.borrow_mut().factory.new_comma_expression(cx.nodes, expression, operation);
    cx.nodes[expression].loc = cx.nodes[node].loc;

    if !is_prefix {
        expression = ec.borrow_mut().factory.new_comma_expression(cx.nodes, expression, temp);
        cx.nodes[expression].loc = cx.nodes[node].loc;
    }

    expression
}

/// `newClassFieldsTransformer`.
pub(crate) fn new_class_fields_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    let compiler_options = opts.compiler_options?;
    let language_version = compiler_options.get_emit_script_target();
    let use_define_for_class_fields = compiler_options.get_use_define_for_class_fields();

    // When targeting ESNext+ with useDefineForClassFields (the default), there are no class
    // field transformations to perform and no prior transform sets EFTransformPrivateStaticElements,
    // so every node would be returned unchanged. Skip entirely.
    if language_version >= ScriptTarget::ESNext && use_define_for_class_fields {
        return None;
    }

    let resolver = opts.resolver.clone();
    let symbols = opts.symbols;

    make_transformer(opts, |ec| {
        let state = Rc::new(ClassFieldsTransformer {
            compiler_options: opts.compiler_options,
            resolver,
            symbols,
            should_transform_initializers_using_set: Cell::new(!use_define_for_class_fields),
            should_transform_initializers_using_define: Cell::new(
                use_define_for_class_fields && language_version < ScriptTarget::ES2022,
            ),
            should_transform_initializers: Cell::new(
                !use_define_for_class_fields
                    || (use_define_for_class_fields && language_version < ScriptTarget::ES2022),
            ),
            should_transform_private_elements_or_class_static_blocks: Cell::new(
                language_version < ScriptTarget::ES2022,
            ),
            should_transform_auto_accessors: Cell::new(language_version < ScriptTarget::ESNext),
            should_transform_this_in_static_initializers: Cell::new(
                language_version < ScriptTarget::ES2022,
            ),
            should_transform_super_in_static_initializers: Cell::new(
                language_version < ScriptTarget::ES2022,
            ),
            should_transform_private_static_elements_in_file: Cell::new(false),
            legacy_decorators: compiler_options.experimental_decorators == Tristate::True,
            pending_expressions: RefCell::new(Vec::new()),
            pending_statements: RefCell::new(Vec::new()),
            lexical_environment: RefCell::new(Vec::new()),
            current_class_container: Cell::new(None),
            current_class_element: Cell::new(None),
            class_aliases: RefCell::new(HashMap::new()),
            enclosing_class_declarations: RefCell::new(HashSet::new()),
            in_iteration_statement: Cell::new(false),
            inside_computed_property_name: Cell::new(false),
            parent_node: Cell::new(None),
            current_node: Cell::new(None),
            modifier_visitor: RefCell::new(None),
            discarded_value_visitor: RefCell::new(None),
            heritage_clause_visitor: RefCell::new(None),
            assignment_target_visitor: RefCell::new(None),
            class_element_visitor: RefCell::new(None),
            accessor_field_result_visitor: RefCell::new(None),
            array_assignment_element_visitor: RefCell::new(None),
            object_assignment_element_visitor: RefCell::new(None),
            substitution_visitor: RefCell::new(None),
        });
        macro_rules! install {
            ($field:ident, $method:ident) => {{
                let weak = Rc::downgrade(&state);
                let ec2 = ec.clone();
                let visit: Box<VisitFn<'a>> = Box::new(
                    move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                        let s = weak
                            .upgrade()
                            .expect("classFieldsTransformer dropped during visit");
                        s.$method(&ec2, cx, node)
                    },
                );
                *state.$field.borrow_mut() = Some(ec.borrow().new_node_visitor(visit));
            }};
        }
        install!(modifier_visitor, visit_modifier);
        install!(discarded_value_visitor, visit_discarded_value);
        install!(heritage_clause_visitor, visit_heritage_clause);
        install!(assignment_target_visitor, visit_assignment_target);
        install!(class_element_visitor, visit_class_element);
        install!(accessor_field_result_visitor, visit_accessor_field_result);
        install!(array_assignment_element_visitor, visit_array_assignment_element);
        install!(object_assignment_element_visitor, visit_object_assignment_element);
        install!(substitution_visitor, visit_for_substitution_opt);
        Box::new(
            move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, cx, node)
            },
        )
    })
}
