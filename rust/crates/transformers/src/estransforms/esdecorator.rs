// Ported from tsc/internal/transformers/estransforms/esdecorator.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `newESDecoratorTransformer` — transforms ES decorators (the "TC39
// decorators" proposal semantics, not `experimentalDecorators`).
//
// PORT notes: see `mod.rs` and `async.rs` — same `Rc<State>` + `txv`
// (synthesized `tx.Visitor()` equivalent) + `ec_visit_*` hook conventions.
// The Go `top *lexicalEntry` linked stack is a `RefCell<Vec<LexicalEntry>>`;
// `next` becomes the previous element. `classInfo`/`memberInfo` are shared
// `Rc<RefCell<…>>` so nested visitors mutate the same record.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{
    self as ast, Kind, ModifierList, NodeFlags, NodeId, NodeList, SubtreeFacts, TokenFlags,
};
use tsc_collections::OrderedMap;
use tsc_core::languagevariant::LanguageVariant;
use tsc_core::options_generated::{CompilerOptions, ScriptTarget};
use tsc_core::tristate::Tristate;
use tsc_printer::{AutoGenerateOptions, EmitFlags, GeneratedIdentifierFlags};
use tsc_scanner::utilities::is_identifier_text;

use super::classfields::class_has_class_this_assignment;
use super::classthis::is_class_this_assignment_block;
use super::namedevaluation::{
    class_has_declared_or_explicitly_assigned_name,
    inject_class_named_evaluation_helper_block_if_missing, is_class_named_evaluation_helper_block,
    is_named_evaluation_and, transform_named_evaluation,
};
use super::utilities::create_accessor_property_backing_field;
use super::{Ec, ec_visit_iteration_body, make_transformer, subtree_facts};
use crate::chain::TransformOptions;
use crate::transformer::Transformer;
use crate::utilities as transformer_utilities;

// Class/Decorator evaluation order, as it pertains to this transformer:
//
// 1. Class decorators are evaluated outside of the private name scope of the class.
//    - 15.8.20 RS: BindingClassDeclarationEvaluation
//    - 15.8.21 RS: Evaluation
//    - 8.3.5 RS: NamedEvaluation
// 2. ClassHeritage clause is evaluated outside of the private name scope of the class.
//    - 15.8.19 RS: ClassDefinitionEvaluation, Step 8.c.
// 3. The name of the class is assigned.
// 4. For each member:
//    a. Member Decorators are evaluated.
//       - 15.8.19 RS: ClassDefinitionEvaluation, Step 23.
//       - Probably 15.7.13 RS: ClassElementEvaluation, but it's missing from spec text.
//    b. Computed Property name is evaluated
//       - 15.8.19 RS: ClassDefinitionEvaluation, Step 23.
//       - 15.8.15 RS: ClassFieldDefinitionEvaluation, Step 1.
//       - 15.4.5 RS: MethodDefinitionEvaluation, Step 1.
// 5. Static non-field (method/getter/setter/auto-accessor) element decorators are applied
// 6. Non-static non-field (method/getter/setter/auto-accessor) element decorators are applied
// 7. Static field (excl. auto-accessor) element decorators are applied
// 8. Non-static field (excl. auto-accessor) element decorators are applied
// 9. Class decorators are applied
// 10. Class binding is initialized
// 11. Static method extra initializers are evaluated
// 12. Static fields are initialized (incl. extra initializers) and static blocks are evaluated
// 13. Class extra initializers are evaluated
//
// Class constructor evaluation order, as it pertains to this transformer:
//
// 1. Instance method extra initializers are evaluated
// 2. For each instance field/auto-accessor:
//    a. The field is initialized and defined on the instance.
//    b. Extra initializers for the field are evaluated.

/// `lexicalEntryKind` discriminates the kind of lexical scope entry.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LexicalEntryKind {
    Class,
    ClassElement,
    Name,
    Other,
}

/// `lexicalEntry` represents a single entry in the lexical scope stack used
/// to track nested class declarations and their state during transformation.
struct LexicalEntry {
    kind: LexicalEntryKind,
    class_info_data: Option<Rc<RefCell<ClassInfo>>>,
    saved_pending_expressions: Vec<NodeId>,
    class_this_data: Option<NodeId>,
    class_super_data: Option<NodeId>,
    depth: usize,
}

/// `memberInfo` stores decoration-related data for a single class element.
#[derive(Default)]
struct MemberInfo {
    /// used in class definition step 4.a
    member_decorators_name: Option<NodeId>,
    /// used in class definition step 12 and constructor evaluation step 2.a
    member_initializers_name: Option<NodeId>,
    /// used in class definition step 12 and constructor evaluation step 2.b
    member_extra_initializers_name: Option<NodeId>,
    member_descriptor_name: Option<NodeId>,
}

/// `classInfo` stores all transformation data for a single decorated class.
#[derive(Default)]
struct ClassInfo {
    class: Option<NodeId>,
    /// used in class definition step 2
    class_decorators_name: Option<NodeId>,
    /// used in class definition step 10
    class_descriptor_name: Option<NodeId>,
    /// used in class definition step 13
    class_extra_initializers_name: Option<NodeId>,
    /// `_classThis`, if needed.
    class_this: Option<NodeId>,
    /// `_classSuper`, if needed.
    class_super: Option<NodeId>,
    metadata_reference: Option<NodeId>,
    /// used in class definition step 4.a, 12, and constructor evaluation
    member_infos: OrderedMap<NodeId, Rc<RefCell<MemberInfo>>>,
    /// used in constructor evaluation step 1
    instance_method_extra_initializers_name: Option<NodeId>,
    /// used in class definition step 11
    static_method_extra_initializers_name: Option<NodeId>,
    static_non_field_decoration_statements: Vec<NodeId>,
    non_static_non_field_decoration_statements: Vec<NodeId>,
    static_field_decoration_statements: Vec<NodeId>,
    non_static_field_decoration_statements: Vec<NodeId>,
    has_static_initializers: bool,
    has_non_ambient_instance_fields: bool,
    has_static_private_class_elements: bool,
    pending_static_initializers: Vec<NodeId>,
    pending_instance_initializers: Vec<NodeId>,
}

/// `partialResult`.
#[derive(Default)]
struct PartialResult {
    modifiers: Option<ModifierList>,
    referenced_name: Option<NodeId>,
    name: Option<NodeId>,
    initializers_name: Option<NodeId>,
    extra_initializers_name: Option<NodeId>,
    descriptor_name: Option<NodeId>,
    this_arg: Option<NodeId>,
}

/// `createDescriptorFunc` — the `createDescriptor` callbacks are methods on
/// the transformer, so they're modeled as a discriminant.
#[derive(Clone, Copy)]
enum CreateDescriptor {
    Method,
    GetAccessor,
    SetAccessor,
    AccessorProperty,
}

/// `type esDecoratorTransformer struct`.
pub(crate) struct EsDecoratorTransformer<'a> {
    compiler_options: Option<&'a CompilerOptions>,
    top: RefCell<Vec<LexicalEntry>>,
    class_info_stack: RefCell<Option<Rc<RefCell<ClassInfo>>>>,
    class_this: Cell<Option<NodeId>>,
    class_super: Cell<Option<NodeId>>,
    pending_expressions: RefCell<Vec<NodeId>>,
    outer_this: Cell<Option<NodeId>>,
    should_transform_private_static_elements_in_file: Cell<bool>,
    outer_this_visitor: RefCell<Option<NodeVisitor<'a>>>,
    discarded_visitor: RefCell<Option<NodeVisitor<'a>>>,
    modifier_visitor: RefCell<Option<NodeVisitor<'a>>>,
    export_stripping_modifier_visitor: RefCell<Option<NodeVisitor<'a>>>,
    class_element_visitor: RefCell<Option<NodeVisitor<'a>>>,
    non_constructor_class_element_visitor: RefCell<Option<NodeVisitor<'a>>>,
    constructor_class_element_visitor: RefCell<Option<NodeVisitor<'a>>>,
    array_assignment_visitor: RefCell<Option<NodeVisitor<'a>>>,
    object_assignment_visitor: RefCell<Option<NodeVisitor<'a>>>,
    static_only_modifier_visitor: RefCell<Option<NodeVisitor<'a>>>,
    async_only_modifier_visitor: RefCell<Option<NodeVisitor<'a>>>,
    accessor_stripping_modifier_visitor: RefCell<Option<NodeVisitor<'a>>>,
}

macro_rules! visitor_ref {
    ($self:expr, $field:ident) => {
        $self
            .$field
            .borrow()
            .as_ref()
            .expect(concat!(stringify!($field), " not initialized"))
    };
}

impl<'a> EsDecoratorTransformer<'a> {
    /// A `NodeVisitor` equivalent to `tx.Visitor()` (see `async.rs` PORT note).
    fn txv(self: &Rc<Self>, ec: &Ec) -> NodeVisitor<'a> {
        let state = self.clone();
        let ec2 = ec.clone();
        ec.borrow().new_node_visitor(Box::new(
            move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec2, _v, cx, node)
            },
        ))
    }

    fn update_state(&self) {
        *self.class_info_stack.borrow_mut() = None;
        self.class_this.set(None);
        self.class_super.set(None);
        let stack = self.top.borrow();
        let Some(top) = stack.last() else {
            return;
        };
        match top.kind {
            LexicalEntryKind::Class => {
                *self.class_info_stack.borrow_mut() = top.class_info_data.clone();
            }
            LexicalEntryKind::ClassElement => {
                if stack.len() >= 2 {
                    *self.class_info_stack.borrow_mut() =
                        stack[stack.len() - 2].class_info_data.clone();
                }
                self.class_this.set(top.class_this_data);
                self.class_super.set(top.class_super_data);
            }
            LexicalEntryKind::Name => {
                if stack.len() >= 4 {
                    let grandparent = &stack[stack.len() - 4];
                    if grandparent.kind == LexicalEntryKind::ClassElement {
                        *self.class_info_stack.borrow_mut() =
                            stack[stack.len() - 3].class_info_data.clone();
                        self.class_this.set(grandparent.class_this_data);
                        self.class_super.set(grandparent.class_super_data);
                    }
                }
            }
            LexicalEntryKind::Other => {}
        }
    }

    /// `enterClass`.
    fn enter_class(&self, ci: Option<Rc<RefCell<ClassInfo>>>) {
        let saved_pending_expressions = std::mem::take(&mut *self.pending_expressions.borrow_mut());
        self.top.borrow_mut().push(LexicalEntry {
            kind: LexicalEntryKind::Class,
            class_info_data: ci,
            saved_pending_expressions,
            class_this_data: None,
            class_super_data: None,
            depth: 0,
        });
        self.update_state();
    }

    /// `exitClass`.
    fn exit_class(&self) {
        let entry = self.top.borrow_mut().pop();
        debug_assert!(
            entry
                .as_ref()
                .is_some_and(|e| e.kind == LexicalEntryKind::Class),
            "Incorrect value for top.kind. Expected top.kind to be 'class'."
        );
        if let Some(entry) = entry {
            *self.pending_expressions.borrow_mut() = entry.saved_pending_expressions;
        }
        self.update_state();
    }

    /// `enterClassElement`.
    fn enter_class_element(&self, cx: &VisitorCx<'_, '_>, node: NodeId) {
        {
            let stack = self.top.borrow();
            let top = stack.last();
            debug_assert!(
                top.is_some_and(|e| e.kind == LexicalEntryKind::Class),
                "Incorrect value for top.kind. Expected top.kind to be 'class'."
            );
        }
        let mut entry = LexicalEntry {
            kind: LexicalEntryKind::ClassElement,
            class_info_data: None,
            saved_pending_expressions: Vec::new(),
            class_this_data: None,
            class_super_data: None,
            depth: 0,
        };
        if ast::is_class_static_block_declaration(&cx.nodes[node])
            || (ast::is_property_declaration(&cx.nodes[node])
                && ast::has_static_modifier(&cx.nodes[node]))
        {
            let class_info_data = self
                .top
                .borrow()
                .last()
                .and_then(|e| e.class_info_data.clone());
            if let Some(ci) = class_info_data {
                let ci = ci.borrow();
                entry.class_this_data = ci.class_this;
                entry.class_super_data = ci.class_super;
            }
        }
        self.top.borrow_mut().push(entry);
        self.update_state();
    }

    /// `exitClassElement`.
    fn exit_class_element(&self) {
        {
            let stack = self.top.borrow();
            let top = stack.last();
            debug_assert!(
                top.is_some_and(|e| e.kind == LexicalEntryKind::ClassElement),
                "Incorrect value for top.kind. Expected top.kind to be 'class-element'."
            );
            debug_assert!(
                stack.len() >= 2 && stack[stack.len() - 2].kind == LexicalEntryKind::Class,
                "Incorrect value for top.next.kind. Expected top.next.kind to be 'class'."
            );
        }
        self.top.borrow_mut().pop();
        self.update_state();
    }

    /// `enterName`.
    fn enter_name(&self) {
        {
            let stack = self.top.borrow();
            let top = stack.last();
            debug_assert!(
                top.is_some_and(|e| e.kind == LexicalEntryKind::ClassElement),
                "Incorrect value for top.kind. Expected top.kind to be 'class-element'."
            );
        }
        self.top.borrow_mut().push(LexicalEntry {
            kind: LexicalEntryKind::Name,
            class_info_data: None,
            saved_pending_expressions: Vec::new(),
            class_this_data: None,
            class_super_data: None,
            depth: 0,
        });
        self.update_state();
    }

    /// `exitName`.
    fn exit_name(&self) {
        let entry = self.top.borrow_mut().pop();
        debug_assert!(
            entry
                .as_ref()
                .is_some_and(|e| e.kind == LexicalEntryKind::Name),
            "Incorrect value for top.kind. Expected top.kind to be 'name'."
        );
        self.update_state();
    }

    /// `enterOther`.
    fn enter_other(&self) {
        let mut stack = self.top.borrow_mut();
        if let Some(top) = stack.last_mut()
            && top.kind == LexicalEntryKind::Other
        {
            debug_assert!(self.pending_expressions.borrow().is_empty());
            top.depth += 1;
            return;
        }
        let saved_pending_expressions = std::mem::take(&mut *self.pending_expressions.borrow_mut());
        stack.push(LexicalEntry {
            kind: LexicalEntryKind::Other,
            class_info_data: None,
            saved_pending_expressions,
            class_this_data: None,
            class_super_data: None,
            depth: 0,
        });
        drop(stack);
        self.update_state();
    }

    /// `exitOther`.
    fn exit_other(&self) {
        let mut stack = self.top.borrow_mut();
        let top = stack.last_mut();
        debug_assert!(
            top.as_ref()
                .is_some_and(|e| e.kind == LexicalEntryKind::Other),
            "Incorrect value for top.kind. Expected top.kind to be 'other'."
        );
        let Some(top) = top else { return };
        if top.depth > 0 {
            debug_assert!(self.pending_expressions.borrow().is_empty());
            top.depth -= 1;
        } else {
            let saved = std::mem::take(&mut top.saved_pending_expressions);
            stack.pop();
            drop(stack);
            *self.pending_expressions.borrow_mut() = saved;
            self.update_state();
        }
    }

    /// `(tx *esDecoratorTransformer) visitSourceFile`.
    fn visit_source_file(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.top.borrow_mut().clear();
        self.should_transform_private_static_elements_in_file
            .set(false);
        let visited = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
        let helpers = ec.borrow_mut().read_emit_helpers();
        ec.borrow().add_emit_helper(visited, &helpers);
        if self.should_transform_private_static_elements_in_file.get() {
            ec.borrow()
                .add_emit_flags(visited, EmitFlags::TRANSFORM_PRIVATE_STATIC_ELEMENTS);
            self.should_transform_private_static_elements_in_file
                .set(false);
        }
        visited
    }

    /// `outerThisVisit`.
    fn outer_this_visit(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if subtree_facts(cx, node) & SubtreeFacts::CONTAINS_LEXICAL_THIS == SubtreeFacts::NONE
            && cx.nodes[node].kind != Kind::ThisKeyword
        {
            return Some(node);
        }
        if cx.nodes[node].kind == Kind::ThisKeyword {
            if self.outer_this.get().is_none() {
                let options = AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC,
                    ..Default::default()
                };
                let outer_this =
                    ec.borrow_mut()
                        .factory
                        .new_unique_name_ex(cx.nodes, "_outerThis", &options);
                self.outer_this.set(Some(outer_this));
            }
            return self.outer_this.get();
        }
        visitor_ref!(self, outer_this_visitor)
            .visit_each_child(cx, node)
            .or(Some(node))
    }

    /// `shouldVisitNode`.
    fn should_visit_node(&self, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        let facts = subtree_facts(cx, node);
        facts & SubtreeFacts::CONTAINS_DECORATORS != SubtreeFacts::NONE
            || (self.class_this.get().is_some()
                && facts & SubtreeFacts::CONTAINS_LEXICAL_THIS != SubtreeFacts::NONE)
            || (self.class_this.get().is_some()
                && self.class_super.get().is_some()
                && facts & SubtreeFacts::CONTAINS_LEXICAL_SUPER != SubtreeFacts::NONE)
    }

    /// `(tx *esDecoratorTransformer) visit`.
    pub(crate) fn visit(
        self: &Rc<Self>,
        ec: &Ec,
        _v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].kind == Kind::SourceFile {
            return Some(self.visit_source_file(ec, cx, node));
        }
        if !self.should_visit_node(cx, node) {
            return Some(node);
        }
        match cx.nodes[node].kind {
            // Decorators are elided. In Strada, a separate `modifierVisitor` drops decorators
            // before they reach `visitor` via visitEachChild. Here, `visit` serves as both
            // visitors, so decorators from modifier lists reach it directly.
            Kind::Decorator => None,
            Kind::ClassDeclaration => Some(self.visit_class_declaration(ec, cx, node)),
            Kind::ClassExpression => Some(self.visit_class_expression(ec, cx, node)),
            Kind::Constructor | Kind::PropertyDeclaration | Kind::ClassStaticBlockDeclaration => {
                panic!("Not supported outside of a class. Use 'classElementVisitor' instead.")
            }
            Kind::Parameter => Some(self.visit_parameter_declaration(ec, cx, node)),
            // Support NamedEvaluation to ensure the correct class name for class expressions.
            Kind::BinaryExpression => Some(self.visit_binary_expression(ec, cx, node, false)),
            Kind::PropertyAssignment | Kind::VariableDeclaration | Kind::BindingElement => {
                Some(self.visit_named_evaluation_site(ec, cx, node, cx.nodes[node].initializer()))
            }
            Kind::ExportAssignment => Some(self.visit_export_assignment(ec, cx, node)),
            Kind::ThisKeyword => Some(self.visit_this_expression(cx, node)),
            Kind::ForStatement => Some(self.visit_for_statement(ec, cx, node)),
            Kind::ExpressionStatement => Some(self.visit_expression_statement(cx, node)),
            Kind::ParenthesizedExpression => {
                Some(self.visit_parenthesized_expression(ec, cx, node, false))
            }
            Kind::PartiallyEmittedExpression => {
                Some(self.visit_partially_emitted_expression(ec, cx, node, false))
            }
            Kind::CallExpression => Some(self.visit_call_expression(ec, cx, node)),
            Kind::TaggedTemplateExpression => {
                Some(self.visit_tagged_template_expression(ec, cx, node))
            }
            Kind::PrefixUnaryExpression | Kind::PostfixUnaryExpression => {
                Some(self.visit_pre_or_postfix_unary_expression(ec, cx, node, false))
            }
            Kind::PropertyAccessExpression => {
                Some(self.visit_property_access_expression(ec, cx, node))
            }
            Kind::ElementAccessExpression => {
                Some(self.visit_element_access_expression(ec, cx, node))
            }
            Kind::ComputedPropertyName => Some(self.visit_computed_property_name(ec, cx, node)),
            Kind::MethodDeclaration
            | Kind::SetAccessor
            | Kind::GetAccessor
            | Kind::FunctionExpression
            | Kind::FunctionDeclaration => {
                self.enter_other();
                let result = self.txv(ec).visit_each_child(cx, node).or(Some(node));
                self.exit_other();
                result
            }
            _ => self.txv(ec).visit_each_child(cx, node).or(Some(node)),
        }
    }

    /// `modifierVisitorVisit`.
    fn modifier_visitor_visit(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        if cx.nodes[node].kind == Kind::Decorator {
            return None;
        }
        Some(node)
    }

    /// `classElementVisitorVisit`.
    fn class_element_visitor_visit(
        self: &Rc<Self>,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        match cx.nodes[node].kind {
            Kind::Constructor => self.visit_constructor_declaration(ec, cx, node),
            Kind::MethodDeclaration => Some(self.visit_method_declaration(ec, cx, node)),
            Kind::GetAccessor => Some(self.visit_get_accessor_declaration(ec, cx, node)),
            Kind::SetAccessor => Some(self.visit_set_accessor_declaration(ec, cx, node)),
            Kind::PropertyDeclaration => self.visit_property_declaration(ec, cx, node),
            Kind::ClassStaticBlockDeclaration => {
                Some(self.visit_class_static_block_declaration(ec, cx, node))
            }
            _ => self.visit(ec, v, cx, node),
        }
    }

    /// `discardedValueVisit`.
    fn discarded_value_visit(
        self: &Rc<Self>,
        ec: &Ec,
        v: &NodeVisitor<'a>,
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
            Kind::PartiallyEmittedExpression => {
                Some(self.visit_partially_emitted_expression(ec, cx, node, true))
            }
            _ => self.visit(ec, v, cx, node),
        }
    }

    /// `nonConstructorClassElementVisit`.
    fn non_constructor_class_element_visit(
        self: &Rc<Self>,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if ast::is_constructor_declaration(&cx.nodes[node]) {
            return Some(node); // skip constructors in pass 1
        }
        self.class_element_visitor_visit(ec, v, cx, node)
    }

    /// `constructorClassElementVisit`.
    fn constructor_class_element_visit(
        self: &Rc<Self>,
        ec: &Ec,
        v: &NodeVisitor<'a>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if ast::is_constructor_declaration(&cx.nodes[node]) {
            return self.class_element_visitor_visit(ec, v, cx, node);
        }
        Some(node)
    }

    /// `exportStrippingModifierVisit`.
    fn export_stripping_modifier_visit(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].kind == Kind::ExportKeyword {
            return None;
        }
        self.modifier_visitor_visit(cx, node)
    }

    /// `createHelperVariable`.
    fn create_helper_variable(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        suffix: &str,
    ) -> NodeId {
        let name = get_helper_variable_name(&ec.borrow(), cx, node);
        let options = AutoGenerateOptions {
            flags: GeneratedIdentifierFlags::OPTIMISTIC
                | GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES,
            ..Default::default()
        };
        ec.borrow_mut()
            .factory
            .new_unique_name_ex(cx.nodes, &format!("{name}_{suffix}"), &options)
    }

    /// `createLet`.
    fn create_let(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        initializer: Option<NodeId>,
    ) -> NodeId {
        let decl = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(name),
            None,
            None,
            initializer,
        );
        let decls = ec.borrow_mut().factory.new_node_list([decl]);
        let list = ec.borrow_mut().factory.new_variable_declaration_list(
            cx.nodes,
            Some(decls),
            NodeFlags::LET,
        );
        ec.borrow_mut()
            .factory
            .new_variable_statement(cx.nodes, None, Some(list))
    }

    /// `(tx *esDecoratorTransformer) createClassInfo`.
    fn create_class_info(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Rc<RefCell<ClassInfo>> {
        let options = AutoGenerateOptions {
            flags: GeneratedIdentifierFlags::OPTIMISTIC | GeneratedIdentifierFlags::FILE_LEVEL,
            ..Default::default()
        };
        let metadata_reference =
            ec.borrow_mut()
                .factory
                .new_unique_name_ex(cx.nodes, "_metadata", &options);
        let ci = Rc::new(RefCell::new(ClassInfo {
            class: Some(node),
            metadata_reference: Some(metadata_reference),
            ..Default::default()
        }));

        // Before visiting we perform a first pass to collect information we'll need
        // as we descend.

        // If the class itself is decorated, create a _classThis binding
        if ast::node_is_decorated(false, node, None, None, cx.nodes) {
            let members: Vec<NodeId> = cx.nodes[node]
                .members()
                .map(|m| m.to_vec())
                .unwrap_or_default();
            let needs_unique_class_this = members.iter().any(|&member| {
                (ast::is_private_identifier_class_element_declaration(&cx.nodes[member], cx.nodes)
                    || ast::is_auto_accessor_property_declaration(&cx.nodes[member]))
                    && ast::has_static_modifier(&cx.nodes[member])
            });
            // We do not mark _classThis as FileLevel if it may be reused by class private fields, which
            // requires the ability access the captured `_classThis` of outer scopes.
            let flags = if needs_unique_class_this {
                GeneratedIdentifierFlags::OPTIMISTIC
                    | GeneratedIdentifierFlags::RESERVED_IN_NESTED_SCOPES
            } else {
                GeneratedIdentifierFlags::OPTIMISTIC | GeneratedIdentifierFlags::FILE_LEVEL
            };
            let class_this = ec.borrow_mut().factory.new_unique_name_ex(
                cx.nodes,
                "_classThis",
                &AutoGenerateOptions {
                    flags,
                    ..Default::default()
                },
            );
            ci.borrow_mut().class_this = Some(class_this);
        }

        for member in cx.nodes[node]
            .members()
            .map(|m| m.to_vec())
            .unwrap_or_default()
        {
            if ast::is_method_or_accessor(&cx.nodes[member])
                && ast::node_or_child_is_decorated(false, member, Some(node), None, cx.nodes)
            {
                if ast::has_static_modifier(&cx.nodes[member]) {
                    if ci.borrow().static_method_extra_initializers_name.is_none() {
                        let name = ec.borrow_mut().factory.new_unique_name_ex(
                            cx.nodes,
                            "_staticExtraInitializers",
                            &AutoGenerateOptions {
                                flags: GeneratedIdentifierFlags::OPTIMISTIC
                                    | GeneratedIdentifierFlags::FILE_LEVEL,
                                ..Default::default()
                            },
                        );
                        ci.borrow_mut().static_method_extra_initializers_name = Some(name);
                        let renamed_class_this = match ci.borrow().class_this {
                            Some(class_this) => class_this,
                            None => ec.borrow_mut().factory.new_this_expression(cx.nodes),
                        };
                        let initializer = ec.borrow_mut().factory.new_run_initializers_helper(
                            cx.nodes,
                            renamed_class_this,
                            name,
                            None,
                        );
                        let name_range = cx.nodes[node].name();
                        if let Some(name_range) = name_range {
                            ec.borrow()
                                .set_source_map_range(initializer, cx.nodes[name_range].loc);
                        } else {
                            ec.borrow().set_source_map_range(
                                initializer,
                                transformer_utilities::move_range_past_decorators(cx.nodes, node),
                            );
                        }
                        ci.borrow_mut()
                            .pending_static_initializers
                            .push(initializer);
                    }
                } else if ci
                    .borrow()
                    .instance_method_extra_initializers_name
                    .is_none()
                {
                    let name = ec.borrow_mut().factory.new_unique_name_ex(
                        cx.nodes,
                        "_instanceExtraInitializers",
                        &AutoGenerateOptions {
                            flags: GeneratedIdentifierFlags::OPTIMISTIC
                                | GeneratedIdentifierFlags::FILE_LEVEL,
                            ..Default::default()
                        },
                    );
                    ci.borrow_mut().instance_method_extra_initializers_name = Some(name);
                    let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
                    let initializer = ec
                        .borrow_mut()
                        .factory
                        .new_run_initializers_helper(cx.nodes, this_expr, name, None);
                    let name_range = cx.nodes[node].name();
                    if let Some(name_range) = name_range {
                        ec.borrow()
                            .set_source_map_range(initializer, cx.nodes[name_range].loc);
                    } else {
                        ec.borrow().set_source_map_range(
                            initializer,
                            transformer_utilities::move_range_past_decorators(cx.nodes, node),
                        );
                    }
                    ci.borrow_mut()
                        .pending_instance_initializers
                        .push(initializer);
                }
            }

            if ast::is_class_static_block_declaration(&cx.nodes[member]) {
                if !is_class_named_evaluation_helper_block(&ec.borrow(), cx.nodes, member) {
                    ci.borrow_mut().has_static_initializers = true;
                }
            } else if ast::is_property_declaration(&cx.nodes[member]) {
                if ast::has_static_modifier(&cx.nodes[member]) {
                    let has = ci.borrow().has_static_initializers
                        || cx.nodes[member].initializer().is_some()
                        || ast::has_decorators(&cx.nodes[member]);
                    ci.borrow_mut().has_static_initializers = has;
                } else {
                    let has = ci.borrow().has_non_ambient_instance_fields
                        || !ast::has_syntactic_modifier(
                            &cx.nodes[member],
                            ast::ModifierFlags::AMBIENT,
                        );
                    ci.borrow_mut().has_non_ambient_instance_fields = has;
                }
            }

            if (ast::is_private_identifier_class_element_declaration(&cx.nodes[member], cx.nodes)
                || ast::is_auto_accessor_property_declaration(&cx.nodes[member]))
                && ast::has_static_modifier(&cx.nodes[member])
            {
                ci.borrow_mut().has_static_private_class_elements = true;
            }

            // exit early if possible
            {
                let cib = ci.borrow();
                if cib.static_method_extra_initializers_name.is_some()
                    && cib.instance_method_extra_initializers_name.is_some()
                    && cib.has_static_initializers
                    && cib.has_non_ambient_instance_fields
                    && cib.has_static_private_class_elements
                {
                    break;
                }
            }
        }

        ci
    }

    /// `(tx *esDecoratorTransformer) transformClassLike`.
    fn transform_class_like(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut node: NodeId,
    ) -> NodeId {
        ec.borrow_mut().start_variable_environment();

        // When a class has class decorators we end up transforming it into a statement that would otherwise give
        // it an assigned name. If the class doesn't have an assigned name, we'll give it an assigned name of `""`.
        if !class_has_declared_or_explicitly_assigned_name(&ec.borrow(), cx.nodes, node)
            && ast::class_or_constructor_parameter_is_decorated(false, node, cx.nodes)
        {
            let empty_name =
                ec.borrow_mut()
                    .factory
                    .new_string_literal(cx.nodes, "", TokenFlags::NONE);
            node = inject_class_named_evaluation_helper_block_if_missing(
                ec, cx, node, empty_name, None,
            );
        }

        let class_reference =
            ec.borrow_mut()
                .factory
                .get_local_name_ex(cx.nodes, Some(node), &Default::default());
        let ci = self.create_class_info(ec, cx, node);
        let mut class_definition_statements: Vec<NodeId> = Vec::new();
        let mut leading_block_statements: Vec<NodeId> = Vec::new();
        let mut trailing_block_statements: Vec<NodeId> = Vec::new();
        let mut synthetic_constructor: Option<NodeId> = None;
        let mut heritage_clauses: Option<NodeList> = None;
        let mut should_transform_private_static_elements_in_class = false;

        // 1. Class decorators are evaluated outside the private name scope of the class.
        //
        // - Since class decorators don't have privileged access to private names defined inside the class,
        //   they must be evaluated outside of the class body.
        // - Since a class decorator can replace the class constructor, we must define a variable to keep track
        //   of the mutated class.
        // - Since a class decorator can add extra initializers, we must define a variable to keep track of
        //   extra initializers.
        let decorators: Vec<NodeId> = cx.nodes[node]
            .decorators(cx.nodes)
            .iter()
            .map(|d| d.id)
            .collect();
        let class_decorators = self.transform_all_decorators_of_declaration(ec, cx, decorators);
        if !class_decorators.is_empty() {
            debug_assert!(ci.borrow().class_this.is_some());

            let class_decorators_name = ec.borrow_mut().factory.new_unique_name_ex(
                cx.nodes,
                "_classDecorators",
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC
                        | GeneratedIdentifierFlags::FILE_LEVEL,
                    ..Default::default()
                },
            );
            let class_descriptor_name = ec.borrow_mut().factory.new_unique_name_ex(
                cx.nodes,
                "_classDescriptor",
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC
                        | GeneratedIdentifierFlags::FILE_LEVEL,
                    ..Default::default()
                },
            );
            let class_extra_initializers_name = ec.borrow_mut().factory.new_unique_name_ex(
                cx.nodes,
                "_classExtraInitializers",
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC
                        | GeneratedIdentifierFlags::FILE_LEVEL,
                    ..Default::default()
                },
            );
            {
                let mut cib = ci.borrow_mut();
                cib.class_decorators_name = Some(class_decorators_name);
                cib.class_descriptor_name = Some(class_descriptor_name);
                cib.class_extra_initializers_name = Some(class_extra_initializers_name);
            }

            // `class_decorators` is inspected again later — clone so the
            // NodeList can own its copy (Go's slice share isn't consumptive).
            let decorators_list = ec
                .borrow_mut()
                .factory
                .new_node_list(class_decorators.clone());
            let decorators_array = ec.borrow_mut().factory.new_array_literal_expression(
                cx.nodes,
                Some(decorators_list),
                false,
            );
            let empty_list = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
            let empty_array = ec.borrow_mut().factory.new_array_literal_expression(
                cx.nodes,
                Some(empty_list),
                false,
            );
            let class_this = ci
                .borrow()
                .class_this
                .expect("class decorators need _classThis");
            class_definition_statements.extend([
                self.create_let(ec, cx, class_decorators_name, Some(decorators_array)),
                self.create_let(ec, cx, class_descriptor_name, None),
                self.create_let(ec, cx, class_extra_initializers_name, Some(empty_array)),
                self.create_let(ec, cx, class_this, None),
            ]);

            if ci.borrow().has_static_private_class_elements {
                should_transform_private_static_elements_in_class = true;
                self.should_transform_private_static_elements_in_file
                    .set(true);
            }
        }

        // 2. ClassHeritage clause is evaluated outside of the private name scope of the class.
        let extends_clause =
            ast::get_heritage_clause(&cx.nodes[node], Kind::ExtendsKeyword, cx.nodes);
        let mut extends_element: Option<NodeId> = None;
        if let Some(extends_clause) = extends_clause {
            let hc = cx.nodes[extends_clause].as_heritage_clause();
            if let Some(types) = &hc.types
                && !types.nodes.is_empty()
            {
                extends_element = Some(types.nodes[0]);
            }
        }
        let mut extends_expression: Option<NodeId> = None;
        if let Some(extends_element) = extends_element {
            let expr = cx.nodes[extends_element]
                .as_expression_with_type_arguments()
                .expression;
            extends_expression = self.txv(ec).visit_node(cx, expr);
        }

        if let Some(extends_expression) = extends_expression {
            // Rewrite `super` in static initializers so that we can use the correct `this`.
            let class_super = ec.borrow_mut().factory.new_unique_name_ex(
                cx.nodes,
                "_classSuper",
                &AutoGenerateOptions {
                    flags: GeneratedIdentifierFlags::OPTIMISTIC
                        | GeneratedIdentifierFlags::FILE_LEVEL,
                    ..Default::default()
                },
            );
            ci.borrow_mut().class_super = Some(class_super);

            // Ensure we do not give the class or function an assigned name due to the variable by prefixing it
            // with `0, `.
            let unwrapped = ast::skip_outer_expressions(
                extends_expression,
                ast::outer_expression_kinds::ALL,
                cx.nodes,
            );
            let mut safe_extends_expression = extends_expression;
            if (ast::is_class_expression(&cx.nodes[unwrapped])
                && cx.nodes[unwrapped].name().is_none())
                || (ast::is_function_expression(&cx.nodes[unwrapped])
                    && cx.nodes[unwrapped].name().is_none())
                || ast::is_arrow_function(&cx.nodes[unwrapped])
            {
                let zero =
                    ec.borrow_mut()
                        .factory
                        .new_numeric_literal(cx.nodes, "0", TokenFlags::NONE);
                safe_extends_expression = ec.borrow_mut().factory.new_comma_expression(
                    cx.nodes,
                    zero,
                    extends_expression,
                );
            }
            class_definition_statements.push(self.create_let(
                ec,
                cx,
                class_super,
                Some(safe_extends_expression),
            ));

            let extends_element = extends_element.expect("extends element");
            let updated_extends_element = ec
                .borrow_mut()
                .factory
                .update_expression_with_type_arguments(
                    cx.nodes,
                    extends_element,
                    Some(class_super),
                    None,
                )
                .unwrap_or(extends_element);
            let hc = cx.nodes[extends_clause.expect("extends clause")].as_heritage_clause();
            let token = hc.token;
            let types = ec
                .borrow_mut()
                .factory
                .new_node_list([updated_extends_element]);
            let updated_extends_clause = ec
                .borrow_mut()
                .factory
                .update_heritage_clause(
                    cx.nodes,
                    extends_clause.expect("extends clause"),
                    token,
                    Some(types),
                )
                .unwrap_or(extends_clause.expect("extends clause"));
            heritage_clauses = Some(
                ec.borrow_mut()
                    .factory
                    .new_node_list([updated_extends_clause]),
            );
        }

        let renamed_class_this = match ci.borrow().class_this {
            Some(class_this) => class_this,
            None => ec.borrow_mut().factory.new_this_expression(cx.nodes),
        };

        // 3. The name of the class is assigned.
        //
        // If the class did not have a name, the caller should have performed injectClassNamedEvaluationHelperBlockIfMissing
        // prior to calling this function if a name was needed.

        // 4. For each member:
        //    a. Member Decorators are evaluated
        //    b. Computed Property Name is evaluated, if present
        //
        // We visit members in two passes:
        // - The first pass visits methods, accessors, and fields to collect decorators and computed property names.
        // - The second pass visits the constructor to add instance initializers.
        //
        // NOTE: If there are no constructors, but there are instance initializers, a synthetic constructor is added.
        self.enter_class(Some(ci.clone()));

        let metadata = self.create_metadata(
            ec,
            cx,
            ci.borrow().metadata_reference.expect("metadata reference"),
            ci.borrow().class_super,
        );
        leading_block_statements.push(metadata);

        // Since the constructor can appear anywhere in the class body and its transform depends on other class
        // elements, we must first visit all non-constructor members, then visit the constructor, all while
        // maintaining document order.
        let member_list = cx.nodes[node].member_list().cloned();
        let members =
            visitor_ref!(self, non_constructor_class_element_visitor).visit_nodes(cx, member_list);
        let members =
            visitor_ref!(self, constructor_class_element_visitor).visit_nodes(cx, members);
        let mut members = members;

        // Handle pending expressions (computed property names and decorator evaluations)
        if !self.pending_expressions.borrow().is_empty() {
            // If a pending expression contains a lexical `this`, we'll need to capture the lexical `this` of the
            // container and transform it in the expression. This ensures we use the correct `this` in the
            // resulting class `static` block. We don't use substitution here because the size of the tree we are
            // visiting is likely to be small and doesn't justify the complexity of introducing substitution.
            self.outer_this.set(None);
            let pending: Vec<NodeId> = self.pending_expressions.borrow().clone();
            for expr in pending {
                // If a pending expression contains lexical `this`, capture it
                let expr = if subtree_facts(cx, expr) & SubtreeFacts::CONTAINS_LEXICAL_THIS
                    != SubtreeFacts::NONE
                {
                    visitor_ref!(self, outer_this_visitor)
                        .visit_node(cx, Some(expr))
                        .unwrap_or(expr)
                } else {
                    expr
                };
                let statement = ec
                    .borrow_mut()
                    .factory
                    .new_expression_statement(cx.nodes, Some(expr));
                leading_block_statements.push(statement);
            }
            if let Some(outer_this) = self.outer_this.get() {
                let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
                let outer_let = self.create_let(ec, cx, outer_this, Some(this_expr));
                class_definition_statements.insert(0, outer_let);
            }
            self.pending_expressions.borrow_mut().clear();
        }
        self.exit_class();

        // If there are instance initializers but no constructor, synthesize one
        if !ci.borrow().pending_instance_initializers.is_empty()
            && ast::get_first_constructor_with_body(&cx.nodes[node], cx.nodes).is_none()
        {
            let initializer_statements = self.prepare_constructor(&ci, ec, cx);
            if !initializer_statements.is_empty() {
                let is_derived_class = extends_element.is_some_and(|extends_element| {
                    let expr = cx.nodes[extends_element]
                        .as_expression_with_type_arguments()
                        .expression
                        .expect("extends expression");
                    let unwrapped = ast::skip_outer_expressions(
                        expr,
                        ast::outer_expression_kinds::ALL,
                        cx.nodes,
                    );
                    cx.nodes[unwrapped].kind != Kind::NullKeyword
                });
                let mut constructor_statements: Vec<NodeId> = Vec::new();
                if is_derived_class {
                    let arguments_ident = ec
                        .borrow_mut()
                        .factory
                        .new_identifier(cx.nodes, "arguments");
                    let spread_arguments = ec
                        .borrow_mut()
                        .factory
                        .new_spread_element(cx.nodes, Some(arguments_ident));
                    let super_keyword = ec
                        .borrow_mut()
                        .factory
                        .new_keyword_expression(cx.nodes, Kind::SuperKeyword);
                    let spread_list = ec.borrow_mut().factory.new_node_list([spread_arguments]);
                    let super_call = ec.borrow_mut().factory.new_call_expression(
                        cx.nodes,
                        Some(super_keyword),
                        None,
                        None,
                        Some(spread_list),
                        NodeFlags::NONE,
                    );
                    let super_stmt = ec
                        .borrow_mut()
                        .factory
                        .new_expression_statement(cx.nodes, Some(super_call));
                    constructor_statements.push(super_stmt);
                }
                constructor_statements.extend(initializer_statements);
                let stmts_list = ec
                    .borrow_mut()
                    .factory
                    .new_node_list(constructor_statements);
                let constructor_body =
                    ec.borrow_mut()
                        .factory
                        .new_block(cx.nodes, Some(stmts_list), true);
                let empty_params = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
                synthetic_constructor = Some(ec.borrow_mut().factory.new_constructor_declaration(
                    cx.nodes,
                    None,
                    None,
                    Some(empty_params),
                    None,
                    None,
                    Some(constructor_body),
                ));
            }
        }

        // Used in class definition steps 5,7,11
        if let Some(static_method_extra_initializers_name) =
            ci.borrow().static_method_extra_initializers_name
        {
            let empty_list = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
            let empty_array = ec.borrow_mut().factory.new_array_literal_expression(
                cx.nodes,
                Some(empty_list),
                false,
            );
            class_definition_statements.push(self.create_let(
                ec,
                cx,
                static_method_extra_initializers_name,
                Some(empty_array),
            ));
        }

        // Used in class definition steps 6,8, and construction
        if let Some(instance_method_extra_initializers_name) =
            ci.borrow().instance_method_extra_initializers_name
        {
            let empty_list = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
            let empty_array = ec.borrow_mut().factory.new_array_literal_expression(
                cx.nodes,
                Some(empty_list),
                false,
            );
            class_definition_statements.push(self.create_let(
                ec,
                cx,
                instance_method_extra_initializers_name,
                Some(empty_array),
            ));
        }

        // Used in class definition steps 7, 8, 12, and construction.
        // Emit member info variable declarations; the reference implementation emits static member vars first, then non-static.
        if ci.borrow().member_infos.size() > 0 {
            class_definition_statements
                .extend(self.emit_member_info_declarations(&ci, ec, cx, true /*is_static*/));
            class_definition_statements
                .extend(self.emit_member_info_declarations(&ci, ec, cx, false /*is_static*/));
        }

        // 5. Static non-field element decorators are applied
        leading_block_statements.extend(
            ci.borrow()
                .static_non_field_decoration_statements
                .iter()
                .copied(),
        );

        // 6. Non-static non-field element decorators are applied
        leading_block_statements.extend(
            ci.borrow()
                .non_static_non_field_decoration_statements
                .iter()
                .copied(),
        );

        // 7. Static field element decorators are applied
        leading_block_statements.extend(
            ci.borrow()
                .static_field_decoration_statements
                .iter()
                .copied(),
        );

        // 8. Non-static field element decorators are applied
        leading_block_statements.extend(
            ci.borrow()
                .non_static_field_decoration_statements
                .iter()
                .copied(),
        );

        // 9. Class decorators are applied
        // 10. Class binding is initialized
        //
        // produces:
        //   __esDecorate(null, _classDescriptor = { value: this }, _classDecorators, { kind: "class", name: this.name, metadata }, null, _classExtraInitializers);
        {
            let (
                class_descriptor_name,
                class_decorators_name,
                class_extra_initializers_name,
                class_this,
            ) = {
                let cib = ci.borrow();
                (
                    cib.class_descriptor_name,
                    cib.class_decorators_name,
                    cib.class_extra_initializers_name,
                    cib.class_this,
                )
            };
            if let (
                Some(class_descriptor_name),
                Some(class_decorators_name),
                Some(class_extra_initializers_name),
                Some(class_this),
            ) = (
                class_descriptor_name,
                class_decorators_name,
                class_extra_initializers_name,
                class_this,
            ) {
                let value_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "value");
                let value_property = ec.borrow_mut().factory.new_property_assignment(
                    cx.nodes,
                    None,
                    Some(value_ident),
                    None,
                    None,
                    Some(renamed_class_this),
                );
                let props = ec.borrow_mut().factory.new_node_list([value_property]);
                let class_descriptor = ec.borrow_mut().factory.new_object_literal_expression(
                    cx.nodes,
                    Some(props),
                    false,
                );
                let class_descriptor_assignment = ec
                    .borrow_mut()
                    .factory
                    .new_assignment_expression(cx.nodes, class_descriptor_name, class_descriptor);
                let name_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "name");
                let class_name_reference = ec.borrow_mut().factory.new_property_access_expression(
                    cx.nodes,
                    Some(renamed_class_this),
                    None,
                    Some(name_ident),
                    NodeFlags::NONE,
                );

                let context_obj = ec
                    .borrow_mut()
                    .factory
                    .new_es_decorate_class_context_object(
                        cx.nodes,
                        class_name_reference,
                        ci.borrow().metadata_reference.expect("metadata reference"),
                    );

                let null1 = ec
                    .borrow_mut()
                    .factory
                    .new_token(cx.nodes, Kind::NullKeyword);
                let null2 = ec
                    .borrow_mut()
                    .factory
                    .new_token(cx.nodes, Kind::NullKeyword);
                let es_decorate_helper = ec.borrow_mut().factory.new_es_decorate_helper(
                    cx.nodes,
                    null1,
                    class_descriptor_assignment,
                    class_decorators_name,
                    context_obj,
                    null2,
                    class_extra_initializers_name,
                );
                let es_decorate_statement = ec
                    .borrow_mut()
                    .factory
                    .new_expression_statement(cx.nodes, Some(es_decorate_helper));
                ec.borrow().set_source_map_range(
                    es_decorate_statement,
                    transformer_utilities::move_range_past_decorators(cx.nodes, node),
                );
                leading_block_statements.push(es_decorate_statement);

                // produces:
                //   C = _classThis = _classDescriptor.value;
                let value_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "value");
                let class_descriptor_value_ref =
                    ec.borrow_mut().factory.new_property_access_expression(
                        cx.nodes,
                        Some(class_descriptor_name),
                        None,
                        Some(value_ident),
                        NodeFlags::NONE,
                    );
                let class_this_assignment = ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    class_this,
                    class_descriptor_value_ref,
                );
                let class_reference_assignment = ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    class_reference,
                    class_this_assignment,
                );
                let stmt = ec
                    .borrow_mut()
                    .factory
                    .new_expression_statement(cx.nodes, Some(class_reference_assignment));
                leading_block_statements.push(stmt);
            }
        }

        // produces:
        //   if (metadata) Object.defineProperty(C, Symbol.metadata, { configurable: true, writable: true, value: metadata });
        let symbol_metadata = self.create_symbol_metadata(
            ec,
            cx,
            renamed_class_this,
            ci.borrow().metadata_reference.expect("metadata reference"),
        );
        leading_block_statements.push(symbol_metadata);

        // 11. Static extra initializers
        // 12. Static fields are initialized
        let pending_static: Vec<NodeId> =
            std::mem::take(&mut ci.borrow_mut().pending_static_initializers);
        for initializer in &pending_static {
            let initializer_statement = ec
                .borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, Some(*initializer));
            let range = ec.borrow().source_map_range(cx.nodes, *initializer);
            ec.borrow()
                .set_source_map_range(initializer_statement, range);
            trailing_block_statements.push(initializer_statement);
        }

        // 13. Class extra initializers
        if let Some(class_extra_initializers_name) = ci.borrow().class_extra_initializers_name {
            let run_class_initializers_helper =
                ec.borrow_mut().factory.new_run_initializers_helper(
                    cx.nodes,
                    renamed_class_this,
                    class_extra_initializers_name,
                    None,
                );
            let run_class_initializers_statement = ec
                .borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, Some(run_class_initializers_helper));
            if let Some(name) = cx.nodes[node].name() {
                ec.borrow()
                    .set_source_map_range(run_class_initializers_statement, cx.nodes[name].loc);
            } else {
                ec.borrow().set_source_map_range(
                    run_class_initializers_statement,
                    transformer_utilities::move_range_past_decorators(cx.nodes, node),
                );
            }
            trailing_block_statements.push(run_class_initializers_statement);
        }

        // If there are no other static initializers to run, combine the leading and trailing block statements
        if !leading_block_statements.is_empty()
            && !trailing_block_statements.is_empty()
            && !ci.borrow().has_static_initializers
        {
            leading_block_statements.extend(trailing_block_statements.iter().copied());
            trailing_block_statements.clear();
        }

        // prepare a leading `static {}` block, if necessary
        //
        // produces:
        //   class C {
        //       static { ... }
        //       ...
        //   }
        let mut leading_static_block: Option<NodeId> = None;
        if !leading_block_statements.is_empty() {
            let stmts = ec
                .borrow_mut()
                .factory
                .new_node_list(leading_block_statements);
            let body = ec
                .borrow_mut()
                .factory
                .new_block(cx.nodes, Some(stmts), true);
            leading_static_block =
                Some(ec.borrow_mut().factory.new_class_static_block_declaration(
                    cx.nodes,
                    None,
                    Some(body),
                ));
        }

        if let Some(leading_static_block) = leading_static_block
            && should_transform_private_static_elements_in_class
        {
            // We use EFTransformPrivateStaticElements as a marker on a class static block
            // to inform the classFields transform that it shouldn't rename `this` to `_classThis` in the
            // transformed class static block.
            ec.borrow().set_emit_flags(
                leading_static_block,
                EmitFlags::TRANSFORM_PRIVATE_STATIC_ELEMENTS,
            );
        }

        // prepare a trailing `static {}` block, if necessary
        //
        // produces:
        //   class C {
        //       ...
        //       static { ... }
        //   }
        let mut trailing_static_block: Option<NodeId> = None;
        if !trailing_block_statements.is_empty() {
            let stmts = ec
                .borrow_mut()
                .factory
                .new_node_list(trailing_block_statements);
            let body = ec
                .borrow_mut()
                .factory
                .new_block(cx.nodes, Some(stmts), true);
            trailing_static_block =
                Some(ec.borrow_mut().factory.new_class_static_block_declaration(
                    cx.nodes,
                    None,
                    Some(body),
                ));
        }

        // Assemble new members list
        if leading_static_block.is_some()
            || synthetic_constructor.is_some()
            || trailing_static_block.is_some()
        {
            let member_ids: Vec<NodeId> = members
                .as_ref()
                .map(|m| m.nodes.to_vec())
                .unwrap_or_default();
            let mut new_members: Vec<NodeId> = Vec::with_capacity(member_ids.len() + 3);

            // Find the existing NamedEvaluation helper block index
            let mut existing_named_evaluation_helper_block_index: i64 = -1;
            for (i, &m) in member_ids.iter().enumerate() {
                if is_class_named_evaluation_helper_block(&ec.borrow(), cx.nodes, m) {
                    existing_named_evaluation_helper_block_index = i as i64;
                    break;
                }
            }

            // add the leading `static {}` block
            if let Some(leading_static_block) = leading_static_block {
                // add the `static {}` block after any existing NamedEvaluation helper block, if one exists.
                let idx = (existing_named_evaluation_helper_block_index + 1) as usize;
                new_members.extend_from_slice(&member_ids[..idx]);
                new_members.push(leading_static_block);
                new_members.extend_from_slice(&member_ids[idx..]);
            } else {
                new_members.extend_from_slice(&member_ids);
            }

            // append the synthetic constructor, if necessary
            if let Some(synthetic_constructor) = synthetic_constructor {
                new_members.push(synthetic_constructor);
            }

            // append a trailing `static {}` block, if necessary
            if let Some(trailing_static_block) = trailing_static_block {
                new_members.push(trailing_static_block);
            }

            let mut members_list = ec.borrow_mut().factory.new_node_list(new_members);
            members_list.loc = members.as_ref().map(|m| m.loc).unwrap_or_default();
            members = Some(members_list);
        }

        let lexical_environment = ec.borrow_mut().end_variable_environment(cx.nodes);

        let mut class_expression;
        if !class_decorators.is_empty() {
            class_expression = ec.borrow_mut().factory.new_class_expression(
                cx.nodes,
                None,
                None,
                None,
                heritage_clauses,
                members,
            );
            ec.borrow().set_original(class_expression, node);
            if let Some(class_this) = ci.borrow().class_this {
                class_expression =
                    inject_class_this_assignment_if_missing(ec, cx, class_expression, class_this);
            }

            // We use `var` instead of `let` so we can leverage NamedEvaluation to define the class name
            // and still be able to ensure it is initialized prior to any use in `static {}`.

            // produces:
            //   (() => {
            //       let _classDecorators = [...];
            //       let _classDescriptor;
            //       let _classExtraInitializers = [];
            //       let _classThis;
            //       ...
            //       var C = class {
            //           static {
            //               __esDecorate(null, _classDescriptor = { value: this }, _classDecorators, ...);
            //               C = _classThis = _classDescriptor.value;
            //           }
            //           static x = 1;
            //           static y = C.x; // `C` will already be defined here.
            //           static { ... }
            //       };
            //       return C;
            //   })();

            let class_reference_declaration = ec.borrow_mut().factory.new_variable_declaration(
                cx.nodes,
                Some(class_reference),
                None,
                None,
                Some(class_expression),
            );
            let decls = ec
                .borrow_mut()
                .factory
                .new_node_list([class_reference_declaration]);
            let class_reference_var_decl_list = ec
                .borrow_mut()
                .factory
                .new_variable_declaration_list(cx.nodes, Some(decls), NodeFlags::NONE);
            let return_expr = if let Some(class_this) = ci.borrow().class_this {
                ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    class_reference,
                    class_this,
                )
            } else {
                class_reference
            };
            let var_statement = ec.borrow_mut().factory.new_variable_statement(
                cx.nodes,
                None,
                Some(class_reference_var_decl_list),
            );
            let return_statement = ec
                .borrow_mut()
                .factory
                .new_return_statement(cx.nodes, Some(return_expr));
            class_definition_statements.extend([var_statement, return_statement]);
        } else {
            // produces:
            //   return <classExpression>;
            let name = cx.nodes[node].name();
            class_expression = ec.borrow_mut().factory.new_class_expression(
                cx.nodes,
                None,
                name,
                None,
                heritage_clauses,
                members,
            );
            ec.borrow().set_original(class_expression, node);
            let return_statement = ec
                .borrow_mut()
                .factory
                .new_return_statement(cx.nodes, Some(class_expression));
            class_definition_statements.push(return_statement);
        }

        if should_transform_private_static_elements_in_class {
            ec.borrow().add_emit_flags(
                class_expression,
                EmitFlags::TRANSFORM_PRIVATE_STATIC_ELEMENTS,
            );
            let member_ids: Vec<NodeId> = cx.nodes[class_expression]
                .members()
                .map(|m| m.to_vec())
                .unwrap_or_default();
            for member in member_ids {
                if (ast::is_private_identifier_class_element_declaration(
                    &cx.nodes[member],
                    cx.nodes,
                ) || ast::is_auto_accessor_property_declaration(&cx.nodes[member]))
                    && ast::has_static_modifier(&cx.nodes[member])
                {
                    ec.borrow()
                        .add_emit_flags(member, EmitFlags::TRANSFORM_PRIVATE_STATIC_ELEMENTS);
                }
            }
        }

        let (merged_statements, _) = ec.borrow_mut().merge_environment(
            cx.nodes,
            &class_definition_statements,
            &lexical_environment,
        );
        ec.borrow_mut()
            .factory
            .new_immediately_invoked_arrow_function(cx.nodes, merged_statements)
    }

    /// `emitMemberInfoDeclarations` — generates let declarations for member
    /// decorator info variables, filtered by static/non-static.
    fn emit_member_info_declarations(
        &self,
        ci: &Rc<RefCell<ClassInfo>>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        is_static: bool,
    ) -> Vec<NodeId> {
        let mut stmts: Vec<NodeId> = Vec::new();
        let entries: Vec<(NodeId, Rc<RefCell<MemberInfo>>)> = ci
            .borrow()
            .member_infos
            .entries()
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        for (member, mi) in entries {
            if ast::is_static(&cx.nodes[member]) != is_static {
                continue;
            }
            let mi = mi.borrow();
            if let Some(member_decorators_name) = mi.member_decorators_name {
                stmts.push(self.create_let(ec, cx, member_decorators_name, None));
            }
            if let Some(member_initializers_name) = mi.member_initializers_name {
                let empty_list = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
                let empty_array = ec.borrow_mut().factory.new_array_literal_expression(
                    cx.nodes,
                    Some(empty_list),
                    false,
                );
                stmts.push(self.create_let(ec, cx, member_initializers_name, Some(empty_array)));
            }
            if let Some(member_extra_initializers_name) = mi.member_extra_initializers_name {
                let empty_list = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
                let empty_array = ec.borrow_mut().factory.new_array_literal_expression(
                    cx.nodes,
                    Some(empty_list),
                    false,
                );
                stmts.push(self.create_let(
                    ec,
                    cx,
                    member_extra_initializers_name,
                    Some(empty_array),
                ));
            }
            if let Some(member_descriptor_name) = mi.member_descriptor_name {
                stmts.push(self.create_let(ec, cx, member_descriptor_name, None));
            }
        }
        stmts
    }

    /// `visitClassDeclaration`.
    fn visit_class_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if is_decorated_class_like(cx, node) {
            let mut statements: Vec<NodeId> = Vec::new();

            let mut original_class = ec.borrow().most_original(Some(node));
            if !original_class.is_some_and(|o| ast::is_class_like(Some(o), cx.nodes)) {
                original_class = Some(node);
            }
            let class_name = if let Some(name) = original_class.and_then(|o| cx.nodes[o].name()) {
                ec.borrow_mut()
                    .factory
                    .new_string_literal_from_node(cx.nodes, name)
            } else {
                ec.borrow_mut()
                    .factory
                    .new_string_literal(cx.nodes, "default", TokenFlags::NONE)
            };

            let is_export =
                ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::EXPORT);
            let is_default =
                ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::DEFAULT);

            let mut class_node = node;
            if cx.nodes[node].name().is_none() {
                class_node = inject_class_named_evaluation_helper_block_if_missing(
                    ec, cx, class_node, class_name, None,
                );
            }

            if is_export && is_default {
                let iife = self.transform_class_like(ec, cx, class_node);
                if cx.nodes[class_node].name().is_some() {
                    // produces:
                    //   let C = (() => { ... })();
                    //   export default C;
                    let local_name = ec
                        .borrow_mut()
                        .factory
                        .get_local_name(cx.nodes, Some(class_node));
                    let var_decl = ec.borrow_mut().factory.new_variable_declaration(
                        cx.nodes,
                        Some(local_name),
                        None,
                        None,
                        Some(iife),
                    );
                    ec.borrow().set_original(var_decl, class_node);
                    let decls = ec.borrow_mut().factory.new_node_list([var_decl]);
                    let var_decls = ec.borrow_mut().factory.new_variable_declaration_list(
                        cx.nodes,
                        Some(decls),
                        NodeFlags::LET,
                    );
                    let var_statement = ec.borrow_mut().factory.new_variable_statement(
                        cx.nodes,
                        None,
                        Some(var_decls),
                    );
                    statements.push(var_statement);

                    let declaration_name = ec
                        .borrow_mut()
                        .factory
                        .get_declaration_name(cx.nodes, Some(class_node));
                    let export_statement = ec
                        .borrow_mut()
                        .factory
                        .new_export_default(cx.nodes, declaration_name);
                    ec.borrow().set_original(export_statement, class_node);
                    ec.borrow()
                        .assign_comment_range(cx.nodes, export_statement, class_node);
                    ec.borrow().set_source_map_range(
                        export_statement,
                        transformer_utilities::move_range_past_decorators(cx.nodes, class_node),
                    );
                    statements.push(export_statement);
                } else {
                    // produces:
                    //   export default (() => { ... })();
                    let export_statement =
                        ec.borrow_mut().factory.new_export_default(cx.nodes, iife);
                    ec.borrow().set_original(export_statement, class_node);
                    ec.borrow()
                        .assign_comment_range(cx.nodes, export_statement, class_node);
                    ec.borrow().set_source_map_range(
                        export_statement,
                        transformer_utilities::move_range_past_decorators(cx.nodes, class_node),
                    );
                    statements.push(export_statement);
                }
            } else {
                debug_assert!(
                    cx.nodes[class_node].name().is_some(),
                    "A class declaration that is not a default export must have a name."
                );
                // produces:
                //   let C = (() => { ... })();
                let iife = self.transform_class_like(ec, cx, class_node);
                let modifiers = visitor_ref!(self, export_stripping_modifier_visitor)
                    .visit_modifiers(cx, cx.nodes[class_node].modifiers().cloned());

                let decl_name = ec.borrow_mut().factory.get_local_name_ex(
                    cx.nodes,
                    Some(class_node),
                    &tsc_printer::AssignedNameOptions {
                        allow_source_maps: true,
                        ..Default::default()
                    },
                );
                let var_decl = ec.borrow_mut().factory.new_variable_declaration(
                    cx.nodes,
                    Some(decl_name),
                    None,
                    None,
                    Some(iife),
                );
                ec.borrow().set_original(var_decl, class_node);
                let decls = ec.borrow_mut().factory.new_node_list([var_decl]);
                let var_decls = ec.borrow_mut().factory.new_variable_declaration_list(
                    cx.nodes,
                    Some(decls),
                    NodeFlags::LET,
                );
                let var_statement = ec.borrow_mut().factory.new_variable_statement(
                    cx.nodes,
                    modifiers,
                    Some(var_decls),
                );
                ec.borrow().set_original(var_statement, class_node);
                ec.borrow()
                    .assign_comment_range(cx.nodes, var_statement, class_node);
                statements.push(var_statement);

                if is_export {
                    // produces:
                    //   export { C };
                    let export_statement = ec
                        .borrow_mut()
                        .factory
                        .new_external_module_export(cx.nodes, decl_name);
                    ec.borrow().set_original(export_statement, class_node);
                    statements.push(export_statement);
                }
            }

            return transformer_utilities::single_or_many(
                &mut ec.borrow_mut().factory,
                cx.nodes,
                Some(statements),
            )
            .unwrap_or(node);
        }

        // Non-decorated class
        let modifiers = visitor_ref!(self, modifier_visitor)
            .visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let heritage = cx.nodes[node]
            .as_class_declaration()
            .class_like_base
            .heritage_clauses
            .clone();
        let heritage_clauses = self.txv(ec).visit_nodes(cx, heritage);
        self.enter_class(None);
        let member_list = cx.nodes[node].member_list().cloned();
        let members = visitor_ref!(self, class_element_visitor).visit_nodes(cx, member_list);
        self.exit_class();
        let name = cx.nodes[node].name();
        ec.borrow_mut()
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
            .unwrap_or(node)
    }

    /// `visitClassExpression`.
    fn visit_class_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if is_decorated_class_like(cx, node) {
            let iife = self.transform_class_like(ec, cx, node);
            ec.borrow().set_original(iife, node);
            return iife;
        }

        let modifiers = visitor_ref!(self, modifier_visitor)
            .visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let heritage = cx.nodes[node]
            .as_class_expression()
            .class_like_base
            .heritage_clauses
            .clone();
        let heritage_clauses = self.txv(ec).visit_nodes(cx, heritage);
        self.enter_class(None);
        let member_list = cx.nodes[node].member_list().cloned();
        let members = visitor_ref!(self, class_element_visitor).visit_nodes(cx, member_list);
        self.exit_class();
        let name = cx.nodes[node].name();
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

    /// `prepareConstructor`.
    fn prepare_constructor(
        &self,
        ci: &Rc<RefCell<ClassInfo>>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
    ) -> Vec<NodeId> {
        // Decorated instance members can add "extra" initializers to the instance. If a class contains any instance
        // fields, we'll inject the `__runInitializers()` call for these extra initializers into the initializer of
        // the first class member that will be initialized. However, if the class does not contain any fields that
        // we can piggyback on, we need to synthesize a `__runInitializers()` call in the constructor instead.
        if ci.borrow().pending_instance_initializers.is_empty() {
            return Vec::new();
        }
        let pending: Vec<NodeId> =
            std::mem::take(&mut ci.borrow_mut().pending_instance_initializers);
        let inlined = ec
            .borrow_mut()
            .factory
            .inline_expressions(cx.nodes, &pending);
        let stmt = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, inlined);
        vec![stmt]
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
    ) -> Vec<NodeId> {
        let super_statement_index = super_path[super_path_depth] as usize;
        // Visit statements before super
        if super_statement_index > statement_offset {
            for &s in &statements_in[statement_offset..super_statement_index] {
                let visited = self.txv(ec).visit_node(cx, Some(s));
                if let Some(visited) = visited {
                    statements_out.push(visited);
                }
            }
        }

        let super_statement = statements_in[super_statement_index];
        if ast::is_try_statement(&cx.nodes[super_statement]) {
            // Recurse into try block
            let (try_block_node, catch_clause, finally_block) = {
                let t = cx.nodes[super_statement].as_try_statement();
                (t.try_block, t.catch_clause, t.finally_block)
            };
            let try_block_node = try_block_node.expect("try block");
            let try_block_statements: Vec<NodeId> = cx.nodes[try_block_node]
                .as_block()
                .statements
                .as_ref()
                .map(|l| l.nodes.to_vec())
                .unwrap_or_default();
            let try_block_statements = self.transform_constructor_body_worker(
                ec,
                cx,
                Vec::new(),
                &try_block_statements,
                0,
                super_path,
                super_path_depth + 1,
                initializer_statements,
            );

            let stmts = ec.borrow_mut().factory.new_node_list(try_block_statements);
            let new_try_block = ec
                .borrow_mut()
                .factory
                .new_block(cx.nodes, Some(stmts), true);
            // Use the original try block's range even though the statements may differ due to
            // injected initializer statements. This preserves source map fidelity for the enclosing
            // try statement.
            cx.nodes[new_try_block].loc = cx.nodes[try_block_node].loc;

            let catch_clause = catch_clause.and_then(|c| self.txv(ec).visit_node(cx, Some(c)));
            let finally_block = finally_block.and_then(|f| self.txv(ec).visit_node(cx, Some(f)));
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
            if let Some(visited) = self.txv(ec).visit_node(cx, Some(super_statement)) {
                statements_out.push(visited);
            }
            statements_out.extend_from_slice(initializer_statements);
        }

        // Visit statements after super
        if super_statement_index + 1 < statements_in.len() {
            for &s in &statements_in[super_statement_index + 1..] {
                let visited = self.txv(ec).visit_node(cx, Some(s));
                if let Some(visited) = visited {
                    statements_out.push(visited);
                }
            }
        }
        statements_out
    }

    /// `visitConstructorDeclaration`.
    fn visit_constructor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        self.enter_class_element(cx, node);
        let modifiers = visitor_ref!(self, modifier_visitor)
            .visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let parameter_list = cx.nodes[node].parameter_list().cloned();
        let parameters = self.txv(ec).visit_nodes(cx, parameter_list);

        let mut body: Option<NodeId> = None;
        let ctor_body = cx.nodes[node].body();
        if let Some(ctor_body_node) = ctor_body
            && let Some(ci) = self.class_info_stack.borrow().clone()
        {
            // If there are instance extra initializers we need to add them to the body along with any
            // field initializers
            let initializer_statements = self.prepare_constructor(&ci, ec, cx);
            if !initializer_statements.is_empty() {
                let mut stmts: Vec<NodeId> = Vec::new();
                let body_statements: Vec<NodeId> = cx.nodes[ctor_body_node]
                    .as_block()
                    .statements
                    .as_ref()
                    .map(|l| l.nodes.to_vec())
                    .unwrap_or_default();
                let (prologue, rest) = ec
                    .borrow()
                    .factory
                    .split_standard_prologue(cx.nodes, &body_statements);
                let (prologue, rest) = (prologue.to_vec(), rest.to_vec());
                stmts.extend(prologue);

                let super_statement_indices =
                    transformer_utilities::find_super_statement_index_path(cx.nodes, &rest, 0);
                if !super_statement_indices.is_empty() {
                    stmts = self.transform_constructor_body_worker(
                        ec,
                        cx,
                        stmts,
                        &rest,
                        0,
                        &super_statement_indices,
                        0,
                        &initializer_statements,
                    );
                } else {
                    stmts.extend_from_slice(&initializer_statements);
                    let visited = self
                        .txv(ec)
                        .visit_slice(cx, &rest)
                        .unwrap_or_else(|| rest.to_vec());
                    stmts.extend(visited);
                }

                let stmt_list = ec.borrow_mut().factory.new_node_list(stmts);
                let new_body = ec
                    .borrow_mut()
                    .factory
                    .new_block(cx.nodes, Some(stmt_list), true);
                ec.borrow().set_original(new_body, ctor_body_node);
                cx.nodes[new_body].loc = cx.nodes[ctor_body_node].loc;
                body = Some(new_body);
            }
        }

        if body.is_none() {
            body = self.txv(ec).visit_node(cx, ctor_body);
        }
        self.exit_class_element();
        Some(
            ec.borrow_mut()
                .factory
                .update_constructor_declaration(
                    cx.nodes, node, modifiers, None, parameters, None, None, body,
                )
                .unwrap_or(node),
        )
    }

    /// `finishClassElement`.
    fn finish_class_element(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        updated: NodeId,
        original: NodeId,
    ) -> NodeId {
        if updated != original {
            // While we emit the source map for the node after skipping decorators and modifiers,
            // we need to emit the comments for the original range.
            ec.borrow()
                .assign_comment_range(cx.nodes, updated, original);
            ec.borrow().set_source_map_range(
                updated,
                transformer_utilities::move_range_past_decorators(cx.nodes, original),
            );
        }
        updated
    }

    /// `createDescriptor` dispatch for `createDescriptorFunc`.
    fn create_descriptor(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        kind: CreateDescriptor,
        member: NodeId,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        match kind {
            CreateDescriptor::Method => {
                self.create_method_descriptor_object(ec, cx, member, modifiers)
            }
            CreateDescriptor::GetAccessor => {
                self.create_get_accessor_descriptor_object(ec, cx, member, modifiers)
            }
            CreateDescriptor::SetAccessor => {
                self.create_set_accessor_descriptor_object(ec, cx, member, modifiers)
            }
            CreateDescriptor::AccessorProperty => {
                self.create_accessor_property_descriptor_object(ec, cx, member, modifiers)
            }
        }
    }

    /// `partialTransformClassElement`.
    fn partial_transform_class_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        member: NodeId,
        ci: Option<Rc<RefCell<ClassInfo>>>,
        create_descriptor: Option<CreateDescriptor>,
    ) -> PartialResult {
        let Some(ci) = ci else {
            let modifiers = visitor_ref!(self, modifier_visitor)
                .visit_modifiers(cx, cx.nodes[member].modifiers().cloned());
            self.enter_name();
            let name = self.visit_property_name(ec, cx, cx.nodes[member].name());
            self.exit_name();
            return PartialResult {
                modifiers,
                name,
                ..Default::default()
            };
        };

        // Member decorators require privileged access to private names. However, computed property
        // evaluation occurs interspersed with decorator evaluation. This means that if we encounter
        // a computed property name we must inline decorator evaluation.

        // Collect decorators for this member. Decorator expressions evaluate outside the class body,
        // so `this` should NOT be replaced with `_classThis`.
        let saved_class_this = self.class_this.replace(None);
        let decorators: Vec<NodeId> = cx.nodes[member]
            .decorators(cx.nodes)
            .iter()
            .map(|d| d.id)
            .collect();
        let member_decorators = self.transform_all_decorators_of_declaration(ec, cx, decorators);
        self.class_this.set(saved_class_this);
        let modifiers = visitor_ref!(self, modifier_visitor)
            .visit_modifiers(cx, cx.nodes[member].modifiers().cloned());

        // `result.modifiers` aliases `modifiers` in Go; clone so the local
        // remains usable below.
        let mut result = PartialResult {
            modifiers: modifiers.clone(),
            ..Default::default()
        };

        if !member_decorators.is_empty() {
            let member_decorators_name = self.create_helper_variable(ec, cx, member, "decorators");
            let decorators_list = ec.borrow_mut().factory.new_node_list(member_decorators);
            let member_decorators_array = ec.borrow_mut().factory.new_array_literal_expression(
                cx.nodes,
                Some(decorators_list),
                false,
            );
            let member_decorators_assignment = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                member_decorators_name,
                member_decorators_array,
            );
            let mi = Rc::new(RefCell::new(MemberInfo {
                member_decorators_name: Some(member_decorators_name),
                ..Default::default()
            }));
            ci.borrow_mut().member_infos.set(member, mi.clone());
            self.pending_expressions
                .borrow_mut()
                .push(member_decorators_assignment);

            // 5. Static non-field (method/getter/setter/auto-accessor) element decorators are applied
            // 6. Non-static non-field (method/getter/setter/auto-accessor) element decorators are applied
            // 7. Static field (excl. auto-accessor) element decorators are applied
            // 8. Non-static field (excl. auto-accessor) element decorators are applied

            // Determine decorator kind
            let kind = if ast::is_get_accessor_declaration(&cx.nodes[member]) {
                "getter"
            } else if ast::is_set_accessor_declaration(&cx.nodes[member]) {
                "setter"
            } else if ast::is_method_declaration(&cx.nodes[member]) {
                "method"
            } else if ast::is_auto_accessor_property_declaration(&cx.nodes[member]) {
                "accessor"
            } else if ast::is_property_declaration(&cx.nodes[member]) {
                "field"
            } else {
                panic!("Unexpected class element kind.")
            };

            // Determine the property name for the context
            let mut property_name_computed = false;
            let mut property_name_expr: Option<NodeId> = None;
            let member_name = cx.nodes[member].name();
            if member_name.is_some_and(|n| {
                ast::is_identifier(&cx.nodes[n]) || ast::is_private_identifier(&cx.nodes[n])
            }) {
                property_name_computed = false;
                property_name_expr = member_name;
            } else if member_name.is_some_and(|n| ast::is_property_name_literal(&cx.nodes[n])) {
                property_name_computed = true;
                property_name_expr = Some(
                    ec.borrow_mut()
                        .factory
                        .new_string_literal_from_node(cx.nodes, member_name.unwrap()),
                );
            } else if member_name.is_some_and(|n| ast::is_computed_property_name(&cx.nodes[n])) {
                let cpn_expression = cx.nodes[member_name.unwrap()]
                    .as_computed_property_name()
                    .expression;
                if cpn_expression.is_some_and(|e| {
                    ast::is_property_name_literal(&cx.nodes[e]) && !ast::is_identifier(&cx.nodes[e])
                }) {
                    property_name_computed = true;
                    property_name_expr = Some(
                        ec.borrow_mut()
                            .factory
                            .new_string_literal_from_node(cx.nodes, cpn_expression.unwrap()),
                    );
                } else {
                    self.enter_name();
                    let (referenced_name, name) =
                        self.visit_referenced_property_name(ec, cx, member_name.unwrap());
                    result.referenced_name = Some(referenced_name);
                    result.name = Some(name);
                    self.exit_name();
                    property_name_computed = true;
                    property_name_expr = Some(referenced_name);
                }
            }

            let context_obj = ec
                .borrow_mut()
                .factory
                .new_es_decorate_class_element_context_object(
                    cx.nodes,
                    kind,
                    property_name_computed,
                    property_name_expr,
                    ast::is_static(&cx.nodes[member]),
                    member_name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])),
                    // 15.7.3 CreateDecoratorAccessObject (kind, name)
                    // 2. If _kind_ is ~field~, ~method~, ~accessor~, or ~getter~, then ...
                    ast::is_property_declaration(&cx.nodes[member])
                        || ast::is_get_accessor_declaration(&cx.nodes[member])
                        || ast::is_method_declaration(&cx.nodes[member]),
                    // 3. If _kind_ is ~field~, ~accessor~, or ~setter~, then ...
                    ast::is_property_declaration(&cx.nodes[member])
                        || ast::is_set_accessor_declaration(&cx.nodes[member]),
                    ci.borrow().metadata_reference.expect("metadata reference"),
                );

            if ast::is_method_or_accessor(&cx.nodes[member]) {
                // produces (public elements):
                //   __esDecorate(this, null, _static_member_decorators, { kind: "method", name: "...", static: true, private: false, access: { ... } }, _staticExtraInitializers);
                //   __esDecorate(this, null, _member_decorators, { kind: "method", name: "...", static: false, private: false, access: { ... } }, _instanceExtraInitializers);
                //   __esDecorate(this, null, _static_member_decorators, { kind: "getter", name: "...", static: true, private: false, access: { ... } }, _staticExtraInitializers);
                //   __esDecorate(this, null, _member_decorators, { kind: "getter", name: "...", static: false, private: false, access: { ... } }, _instanceExtraInitializers);
                //   __esDecorate(this, null, _static_member_decorators, { kind: "setter", name: "...", static: true, private: false, access: { ... } }, _staticExtraInitializers);
                //   __esDecorate(this, null, _member_decorators, { kind: "setter", name: "...", static: false, private: false, access: { ... } }, _instanceExtraInitializers);
                //
                // produces (private elements):
                //   __esDecorate(this, _static_member_descriptor = { value() { ... } }, _static_member_decorators, { kind: "method", name: "...", static: true, private: true, access: { ... } }, _staticExtraInitializers);
                //   __esDecorate(this, _member_descriptor = { value() { ... } }, _member_decorators, { kind: "method", name: "...", static: false, private: true, access: { ... } }, _instanceExtraInitializers);
                //   __esDecorate(this, _static_member_descriptor = { get() { ... } }, _static_member_decorators, { kind: "getter", name: "...", static: true, private: true, access: { ... } }, _staticExtraInitializers);
                //   __esDecorate(this, _member_descriptor = { get() { ... } }, _member_decorators, { kind: "getter", name: "...", static: false, private: true, access: { ... } }, _instanceExtraInitializers);
                //   __esDecorate(this, _static_member_descriptor = { set() { ... } }, _static_member_decorators, { kind: "setter", name: "...", static: true, private: true, access: { ... } }, _staticExtraInitializers);
                //   __esDecorate(this, _member_descriptor = { set() { ... } }, _member_decorators, { kind: "setter", name: "...", static: false, private: true, access: { ... } }, _instanceExtraInitializers);
                let method_extra_initializers_name = if ast::is_static(&cx.nodes[member]) {
                    ci.borrow().static_method_extra_initializers_name
                } else {
                    ci.borrow().instance_method_extra_initializers_name
                };
                debug_assert!(
                    method_extra_initializers_name.is_some(),
                    "methodExtraInitializersName should be defined"
                );

                let descriptor_arg = if ast::is_private_identifier_class_element_declaration(
                    &cx.nodes[member],
                    cx.nodes,
                ) && let Some(create_descriptor) = create_descriptor
                {
                    // For private members, extract the method/accessor body into a descriptor object.
                    // Filter modifiers to only keep async.
                    let async_mods = visitor_ref!(self, async_only_modifier_visitor)
                        .visit_modifiers(cx, modifiers.clone());
                    let descriptor =
                        self.create_descriptor(ec, cx, create_descriptor, member, async_mods);
                    let member_descriptor_name =
                        self.create_helper_variable(ec, cx, member, "descriptor");
                    mi.borrow_mut().member_descriptor_name = Some(member_descriptor_name);
                    result.descriptor_name = Some(member_descriptor_name);
                    ec.borrow_mut().factory.new_assignment_expression(
                        cx.nodes,
                        member_descriptor_name,
                        descriptor,
                    )
                } else {
                    ec.borrow_mut()
                        .factory
                        .new_token(cx.nodes, Kind::NullKeyword)
                };

                let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
                let null = ec
                    .borrow_mut()
                    .factory
                    .new_token(cx.nodes, Kind::NullKeyword);
                let es_decorate_expr = ec.borrow_mut().factory.new_es_decorate_helper(
                    cx.nodes,
                    this_expr,
                    descriptor_arg,
                    member_decorators_name,
                    context_obj,
                    null,
                    method_extra_initializers_name.expect("methodExtraInitializersName"),
                );
                let es_decorate_statement = ec
                    .borrow_mut()
                    .factory
                    .new_expression_statement(cx.nodes, Some(es_decorate_expr));
                ec.borrow().set_source_map_range(
                    es_decorate_statement,
                    transformer_utilities::move_range_past_decorators(cx.nodes, member),
                );
                self.append_decoration_statement(&ci, cx, member, es_decorate_statement);
            } else if ast::is_property_declaration(&cx.nodes[member]) {
                let member_initializers_name =
                    self.create_helper_variable(ec, cx, member, "initializers");
                let member_extra_initializers_name =
                    self.create_helper_variable(ec, cx, member, "extraInitializers");
                {
                    let mut mib = mi.borrow_mut();
                    mib.member_initializers_name = Some(member_initializers_name);
                    mib.member_extra_initializers_name = Some(member_extra_initializers_name);
                }
                result.initializers_name = Some(member_initializers_name);
                result.extra_initializers_name = Some(member_extra_initializers_name);
                if ast::is_static(&cx.nodes[member]) {
                    result.this_arg = ci.borrow().class_this;
                }

                let ctor_arg = if ast::is_auto_accessor_property_declaration(&cx.nodes[member]) {
                    ec.borrow_mut().factory.new_this_expression(cx.nodes)
                } else {
                    ec.borrow_mut()
                        .factory
                        .new_token(cx.nodes, Kind::NullKeyword)
                };

                let descriptor_arg = if ast::is_private_identifier_class_element_declaration(
                    &cx.nodes[member],
                    cx.nodes,
                ) && ast::has_accessor_modifier(&cx.nodes[member])
                    && let Some(create_descriptor) = create_descriptor
                {
                    let descriptor =
                        self.create_descriptor(ec, cx, create_descriptor, member, None);
                    let member_descriptor_name =
                        self.create_helper_variable(ec, cx, member, "descriptor");
                    mi.borrow_mut().member_descriptor_name = Some(member_descriptor_name);
                    result.descriptor_name = Some(member_descriptor_name);
                    ec.borrow_mut().factory.new_assignment_expression(
                        cx.nodes,
                        member_descriptor_name,
                        descriptor,
                    )
                } else {
                    ec.borrow_mut()
                        .factory
                        .new_token(cx.nodes, Kind::NullKeyword)
                };

                // produces:
                //   __esDecorate(null, null, _static_member_decorators, { kind: "field", name: "...", static: true, private: ..., access: { ... } }, _staticExtraInitializers);
                //   __esDecorate(null, null, _member_decorators, { kind: "field", name: "...", static: false, private: ..., access: { ... } }, _instanceExtraInitializers);
                let es_decorate_expr = ec.borrow_mut().factory.new_es_decorate_helper(
                    cx.nodes,
                    ctor_arg,
                    descriptor_arg,
                    member_decorators_name,
                    context_obj,
                    member_initializers_name,
                    member_extra_initializers_name,
                );
                let es_decorate_statement = ec
                    .borrow_mut()
                    .factory
                    .new_expression_statement(cx.nodes, Some(es_decorate_expr));
                ec.borrow().set_source_map_range(
                    es_decorate_statement,
                    transformer_utilities::move_range_past_decorators(cx.nodes, member),
                );
                self.append_decoration_statement(&ci, cx, member, es_decorate_statement);
            }
        }

        if result.name.is_none() {
            self.enter_name();
            result.name = self.visit_property_name(ec, cx, cx.nodes[member].name());
            self.exit_name();
        }

        if modifiers
            .as_ref()
            .map(|m| m.nodes.is_empty())
            .unwrap_or(true)
            && (ast::is_method_declaration(&cx.nodes[member])
                || ast::is_property_declaration(&cx.nodes[member]))
        {
            // Don't emit leading comments on the name for methods and properties without modifiers, otherwise we
            // will end up printing duplicate comments.
            if let Some(name) = result.name {
                ec.borrow()
                    .set_emit_flags(name, EmitFlags::NO_LEADING_COMMENTS);
            }
        }

        result
    }

    /// `appendDecorationStatement` appends an __esDecorate statement to the
    /// appropriate decoration statement list on classInfo based on the
    /// member's kind and static-ness.
    fn append_decoration_statement(
        &self,
        ci: &Rc<RefCell<ClassInfo>>,
        cx: &VisitorCx<'_, '_>,
        member: NodeId,
        stmt: NodeId,
    ) {
        if ast::is_method_or_accessor(&cx.nodes[member])
            || ast::is_auto_accessor_property_declaration(&cx.nodes[member])
        {
            if ast::is_static(&cx.nodes[member]) {
                ci.borrow_mut()
                    .static_non_field_decoration_statements
                    .push(stmt);
            } else {
                ci.borrow_mut()
                    .non_static_non_field_decoration_statements
                    .push(stmt);
            }
        } else if ast::is_property_declaration(&cx.nodes[member])
            && !ast::is_auto_accessor_property_declaration(&cx.nodes[member])
        {
            if ast::is_static(&cx.nodes[member]) {
                ci.borrow_mut()
                    .static_field_decoration_statements
                    .push(stmt);
            } else {
                ci.borrow_mut()
                    .non_static_field_decoration_statements
                    .push(stmt);
            }
        } else {
            panic!("Unexpected class element kind.")
        }
    }

    /// `visitMethodDeclaration`.
    fn visit_method_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.enter_class_element(cx, node);
        let ci = self.class_info_stack.borrow().clone();
        let result =
            self.partial_transform_class_element(ec, cx, node, ci, Some(CreateDescriptor::Method));
        if let Some(descriptor_name) = result.descriptor_name {
            self.exit_class_element();
            let forwarder = self.create_method_descriptor_forwarder(
                cx,
                result.modifiers,
                result.name,
                descriptor_name,
            );
            return self.finish_class_element(ec, cx, forwarder, node);
        }
        let parameter_list = cx.nodes[node].parameter_list().cloned();
        let parameters = self.txv(ec).visit_nodes(cx, parameter_list);
        let body = self.txv(ec).visit_node(cx, cx.nodes[node].body());
        self.exit_class_element();
        let asterisk_token = cx.nodes[node]
            .as_method_declaration()
            .function_like_with_body_base
            .body_base
            .asterisk_token;
        let updated = ec
            .borrow_mut()
            .factory
            .update_method_declaration(
                cx.nodes,
                node,
                result.modifiers,
                asterisk_token,
                result.name,
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

    /// `visitGetAccessorDeclaration`.
    fn visit_get_accessor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.enter_class_element(cx, node);
        let ci = self.class_info_stack.borrow().clone();
        let result = self.partial_transform_class_element(
            ec,
            cx,
            node,
            ci,
            Some(CreateDescriptor::GetAccessor),
        );
        if let Some(descriptor_name) = result.descriptor_name {
            self.exit_class_element();
            let forwarder = self.create_get_accessor_descriptor_forwarder(
                ec,
                cx,
                result.modifiers,
                result.name,
                descriptor_name,
            );
            return self.finish_class_element(ec, cx, forwarder, node);
        }
        let parameter_list = cx.nodes[node].parameter_list().cloned();
        let parameters = self.txv(ec).visit_nodes(cx, parameter_list);
        let body = self.txv(ec).visit_node(cx, cx.nodes[node].body());
        self.exit_class_element();
        let updated = ec
            .borrow_mut()
            .factory
            .update_get_accessor_declaration(
                cx.nodes,
                node,
                result.modifiers,
                result.name,
                None,
                parameters,
                None,
                None,
                body,
            )
            .unwrap_or(node);
        self.finish_class_element(ec, cx, updated, node)
    }

    /// `visitSetAccessorDeclaration`.
    fn visit_set_accessor_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.enter_class_element(cx, node);
        let ci = self.class_info_stack.borrow().clone();
        let result = self.partial_transform_class_element(
            ec,
            cx,
            node,
            ci,
            Some(CreateDescriptor::SetAccessor),
        );
        if let Some(descriptor_name) = result.descriptor_name {
            self.exit_class_element();
            let forwarder = self.create_set_accessor_descriptor_forwarder(
                ec,
                cx,
                result.modifiers,
                result.name,
                descriptor_name,
            );
            return self.finish_class_element(ec, cx, forwarder, node);
        }
        let parameter_list = cx.nodes[node].parameter_list().cloned();
        let parameters = self.txv(ec).visit_nodes(cx, parameter_list);
        let body = self.txv(ec).visit_node(cx, cx.nodes[node].body());
        self.exit_class_element();
        let updated = ec
            .borrow_mut()
            .factory
            .update_set_accessor_declaration(
                cx.nodes,
                node,
                result.modifiers,
                result.name,
                None,
                parameters,
                None,
                None,
                body,
            )
            .unwrap_or(node);
        self.finish_class_element(ec, cx, updated, node)
    }

    /// `visitClassStaticBlockDeclaration`.
    fn visit_class_static_block_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        self.enter_class_element(cx, node);

        let mut result;
        if is_class_named_evaluation_helper_block(&ec.borrow(), cx.nodes, node) {
            result = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
            // Transfer AssignedName metadata to the new node so isClassNamedEvaluationHelperBlock
            // can still find it after visiting (visiting may create a new node when this->_classThis)
            if let Some(assigned_name) = ec.borrow().assigned_name(node)
                && result != node
            {
                ec.borrow().set_assigned_name(result, assigned_name);
            }
        } else if is_class_this_assignment_block(&ec.borrow(), cx.nodes, node) {
            let saved_class_this = self.class_this.replace(None);
            result = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
            self.class_this.set(saved_class_this);
        } else {
            // Use a nested variable environment so temp vars generated during static block
            // content transformation (e.g., super access temps) stay scoped to the static block.
            ec.borrow_mut().start_variable_environment();
            result = self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
            let var_statements = ec.borrow_mut().end_variable_environment(cx.nodes);
            if !var_statements.is_empty() {
                // Inject var declarations at the start of the static block's body
                let block_body = cx.nodes[result]
                    .as_class_static_block_declaration()
                    .body
                    .expect("static block body");
                let mut new_stmts: Vec<NodeId> = Vec::with_capacity(
                    var_statements.len()
                        + cx.nodes[block_body]
                            .statements()
                            .map(|s| s.len())
                            .unwrap_or(0),
                );
                new_stmts.extend(var_statements);
                if let Some(existing) = cx.nodes[block_body].statements() {
                    new_stmts.extend(existing.iter().copied());
                }
                let multi_line = cx.nodes[block_body].as_block().multi_line;
                let stmt_list = ec.borrow_mut().factory.new_node_list(new_stmts);
                let body = ec
                    .borrow_mut()
                    .factory
                    .new_block(cx.nodes, Some(stmt_list), multi_line);
                result = ec.borrow_mut().factory.new_class_static_block_declaration(
                    cx.nodes,
                    None,
                    Some(body),
                );
            }
            if let Some(ci) = self.class_info_stack.borrow().clone() {
                ci.borrow_mut().has_static_initializers = true;
                if !ci.borrow().pending_static_initializers.is_empty() {
                    // If we tried to inject the pending initializers into the current block, we might run into
                    // variable name collisions due to sharing this blocks scope. To avoid this, we inject a new
                    // static block that contains the pending initializers that precedes this block.
                    let mut stmts: Vec<NodeId> = Vec::new();
                    let pending: Vec<NodeId> =
                        std::mem::take(&mut ci.borrow_mut().pending_static_initializers);
                    for init in pending {
                        let init_stmt = ec
                            .borrow_mut()
                            .factory
                            .new_expression_statement(cx.nodes, Some(init));
                        let range = ec.borrow().source_map_range(cx.nodes, init);
                        ec.borrow().set_source_map_range(init_stmt, range);
                        stmts.push(init_stmt);
                    }
                    let stmt_list = ec.borrow_mut().factory.new_node_list(stmts);
                    let body = ec
                        .borrow_mut()
                        .factory
                        .new_block(cx.nodes, Some(stmt_list), true);
                    let static_block = ec.borrow_mut().factory.new_class_static_block_declaration(
                        cx.nodes,
                        None,
                        Some(body),
                    );
                    // Return both the new static block and the original
                    self.exit_class_element();
                    return transformer_utilities::single_or_many(
                        &mut ec.borrow_mut().factory,
                        cx.nodes,
                        Some(vec![static_block, result]),
                    )
                    .unwrap_or(result);
                }
            }
        }

        self.exit_class_element();
        result
    }

    /// `visitPropertyDeclaration`.
    fn visit_property_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let mut node = node;
        {
            let mut pred = |n: NodeId| is_anonymous_class_needing_assigned_name(cx, n);
            if is_named_evaluation_and(&ec.borrow(), cx.nodes, node, Some(&mut pred)) {
                let ignore = can_ignore_empty_string_literal_in_assigned_name(
                    cx,
                    cx.nodes[node].initializer(),
                );
                node = transform_named_evaluation(ec, cx, node, ignore, "");
            }
        }

        self.enter_class_element(cx, node);

        // TODO(rbuckton): We support decorating `declare x` fields with legacyDecorators, but we currently don't
        //                 support them with esDecorators. We need to consider whether we will support them in the
        //                 future, and how. For now, these should be elided by the `ts` transform.
        debug_assert!(
            !ast::has_syntactic_modifier(&cx.nodes[node], ast::ModifierFlags::AMBIENT),
            "Not yet implemented."
        );

        // 10.2.1.3 RS: EvaluateBody
        //   Initializer : `=` AssignmentExpression
        //     ...
        //     3. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true*, then
        //        a. Let _value_ be ? NamedEvaluation of |Initializer| with argument _functionObject_.[[ClassFieldInitializerName]].
        //     ...

        let create_descriptor = if ast::has_accessor_modifier(&cx.nodes[node]) {
            Some(CreateDescriptor::AccessorProperty)
        } else {
            None
        };
        let ci = self.class_info_stack.borrow().clone();
        let result = self.partial_transform_class_element(ec, cx, node, ci, create_descriptor);

        ec.borrow_mut().start_variable_environment();

        let mut initializer = self.txv(ec).visit_node(cx, cx.nodes[node].initializer());
        if let Some(initializers_name) = result.initializers_name {
            let this_arg = match result.this_arg {
                Some(this_arg) => this_arg,
                None => ec.borrow_mut().factory.new_this_expression(cx.nodes),
            };
            let inner = initializer
                .unwrap_or_else(|| ec.borrow_mut().factory.new_void_zero_expression(cx.nodes));
            let run_initializers = ec.borrow_mut().factory.new_run_initializers_helper(
                cx.nodes,
                this_arg,
                initializers_name,
                Some(inner),
            );
            initializer = Some(run_initializers);
        }

        if ast::is_static(&cx.nodes[node])
            && self.class_info_stack.borrow().is_some()
            && initializer.is_some()
        {
            self.class_info_stack
                .borrow()
                .as_ref()
                .expect("classInfoStack")
                .borrow_mut()
                .has_static_initializers = true;
        }

        let declarations = ec.borrow_mut().end_variable_environment(cx.nodes);
        if !declarations.is_empty() {
            let mut stmts: Vec<NodeId> = Vec::with_capacity(declarations.len() + 1);
            stmts.extend(declarations);
            let return_stmt = ec
                .borrow_mut()
                .factory
                .new_return_statement(cx.nodes, initializer);
            stmts.push(return_stmt);
            initializer = Some(
                ec.borrow_mut()
                    .factory
                    .new_immediately_invoked_arrow_function(cx.nodes, stmts),
            );
        }

        if let Some(ci) = self.class_info_stack.borrow().clone() {
            if ast::is_static(&cx.nodes[node]) {
                initializer = self.inject_pending_initializers(ec, &ci, cx, true, initializer);
                if let Some(extra_initializers_name) = result.extra_initializers_name {
                    let this_arg = match ci.borrow().class_this {
                        Some(class_this) => class_this,
                        None => ec.borrow_mut().factory.new_this_expression(cx.nodes),
                    };
                    let helper = ec.borrow_mut().factory.new_run_initializers_helper(
                        cx.nodes,
                        this_arg,
                        extra_initializers_name,
                        None,
                    );
                    ci.borrow_mut().pending_static_initializers.push(helper);
                }
            } else {
                initializer = self.inject_pending_initializers(ec, &ci, cx, false, initializer);
                if let Some(extra_initializers_name) = result.extra_initializers_name {
                    let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
                    let helper = ec.borrow_mut().factory.new_run_initializers_helper(
                        cx.nodes,
                        this_expr,
                        extra_initializers_name,
                        None,
                    );
                    ci.borrow_mut().pending_instance_initializers.push(helper);
                }
            }
        }

        self.exit_class_element();

        if ast::has_accessor_modifier(&cx.nodes[node])
            && let Some(descriptor_name) = result.descriptor_name
        {
            // given:
            //  accessor #x = 1;
            //
            // emits:
            //  static {
            //      _esDecorate(null, _private_x_descriptor = { get() { return this.#x_1; }, set(value) { this.#x_1 = value; } }, ...)
            //  }
            //  ...
            //  #x_1 = 1;
            //  get #x() { return _private_x_descriptor.get.call(this); }
            //  set #x(value) { _private_x_descriptor.set.call(this, value); }

            let comment_range = ec.borrow().comment_range(cx.nodes, node);
            let source_map_range = ec.borrow().source_map_range(cx.nodes, node);

            // Since we're creating two declarations where there was previously one, cache
            // the expression for any computed property names.
            let prop_name = cx.nodes[node].name();
            let mut getter_name = result.name;
            let mut setter_name = result.name;
            if let Some(prop_name) = prop_name
                && ast::is_computed_property_name(&cx.nodes[prop_name])
                && !cx.nodes[prop_name].expression().is_some_and(|e| {
                    transformer_utilities::is_simple_inlineable_expression(&cx.nodes[e])
                })
            {
                let prop_name_expression = cx.nodes[prop_name].expression();
                let cache_assignment =
                    super::classfields::find_computed_property_name_cache_assignment(
                        cx.nodes, prop_name,
                    );
                if let Some(cache_assignment) = cache_assignment {
                    let visited_prop_name_expression =
                        self.txv(ec).visit_node(cx, prop_name_expression);
                    getter_name = Some(
                        ec.borrow_mut()
                            .factory
                            .update_computed_property_name(
                                cx.nodes,
                                prop_name,
                                visited_prop_name_expression,
                            )
                            .unwrap_or(prop_name),
                    );
                    let left = cx.nodes[cache_assignment].as_binary_expression().left;
                    setter_name = Some(
                        ec.borrow_mut()
                            .factory
                            .update_computed_property_name(cx.nodes, prop_name, left)
                            .unwrap_or(prop_name),
                    );
                } else {
                    let temp = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                    if let Some(expr) = prop_name_expression {
                        ec.borrow().set_source_map_range(temp, cx.nodes[expr].loc);
                    }
                    ec.borrow_mut().add_variable_declaration(cx.nodes, temp);
                    let expression = self.txv(ec).visit_node(cx, prop_name_expression);
                    let assignment = ec.borrow_mut().factory.new_assignment_expression(
                        cx.nodes,
                        temp,
                        expression.expect("computed property name expression"),
                    );
                    if let Some(expr) = prop_name_expression {
                        ec.borrow()
                            .set_source_map_range(assignment, cx.nodes[expr].loc);
                    }
                    getter_name = Some(
                        ec.borrow_mut()
                            .factory
                            .update_computed_property_name(cx.nodes, prop_name, Some(assignment))
                            .unwrap_or(prop_name),
                    );
                    setter_name = Some(
                        ec.borrow_mut()
                            .factory
                            .update_computed_property_name(cx.nodes, prop_name, Some(temp))
                            .unwrap_or(prop_name),
                    );
                }
            }

            let modifiers_without_accessor =
                visitor_ref!(self, accessor_stripping_modifier_visitor)
                    .visit_modifiers(cx, result.modifiers);

            let backing_field = create_accessor_property_backing_field(
                ec,
                cx,
                node,
                modifiers_without_accessor.clone(),
                initializer,
            );
            ec.borrow().set_original(backing_field, node);
            ec.borrow()
                .set_emit_flags(backing_field, EmitFlags::NO_COMMENTS);
            ec.borrow()
                .set_source_map_range(backing_field, source_map_range);
            if let Some(name) = cx.nodes[backing_field].name() {
                let range = cx.nodes[node]
                    .name()
                    .map(|n| ec.borrow().source_map_range(cx.nodes, n))
                    .unwrap_or_default();
                ec.borrow().set_source_map_range(name, range);
            }

            let getter = self.create_get_accessor_descriptor_forwarder(
                ec,
                cx,
                modifiers_without_accessor.clone(),
                getter_name,
                descriptor_name,
            );
            ec.borrow().set_original(getter, node);
            ec.borrow().set_comment_range(getter, comment_range);
            ec.borrow().set_source_map_range(getter, source_map_range);

            let setter = self.create_set_accessor_descriptor_forwarder(
                ec,
                cx,
                modifiers_without_accessor,
                setter_name,
                descriptor_name,
            );
            ec.borrow().set_original(setter, node);
            ec.borrow().set_emit_flags(setter, EmitFlags::NO_COMMENTS);
            ec.borrow().set_source_map_range(setter, source_map_range);

            return transformer_utilities::single_or_many(
                &mut ec.borrow_mut().factory,
                cx.nodes,
                Some(vec![backing_field, getter, setter]),
            );
        }

        let updated = ec
            .borrow_mut()
            .factory
            .update_property_declaration(
                cx.nodes,
                node,
                result.modifiers,
                result.name,
                None,
                None,
                initializer,
            )
            .unwrap_or(node);
        Some(self.finish_class_element(ec, cx, updated, node))
    }

    /// `visitThisExpression`.
    fn visit_this_expression(&self, _cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        if let Some(class_this) = self.class_this.get() {
            return class_this;
        }
        node
    }

    /// `visitCallExpression`.
    fn visit_call_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let (expression, arguments) = {
            let call = cx.nodes[node].as_call_expression();
            (call.expression, call.arguments.clone())
        };
        if expression.is_some_and(|e| ast::is_super_property(&cx.nodes[e], cx.nodes))
            && let Some(class_this) = self.class_this.get()
        {
            let expression = self.txv(ec).visit_node(cx, expression);
            let arguments_list = self.txv(ec).visit_nodes(cx, arguments);
            let args: Vec<NodeId> = arguments_list.map(|l| l.nodes.to_vec()).unwrap_or_default();
            let invocation = ec.borrow_mut().factory.new_function_call_call(
                cx.nodes,
                expression.expect("call expression"),
                Some(class_this),
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
        if tag.is_some_and(|t| ast::is_super_property(&cx.nodes[t], cx.nodes))
            && let Some(class_this) = self.class_this.get()
        {
            let tag = self.txv(ec).visit_node(cx, tag);
            let bound_tag = ec.borrow_mut().factory.new_function_bind_call(
                cx.nodes,
                tag.expect("tag"),
                class_this,
                vec![],
            );
            ec.borrow().set_original(bound_tag, node);
            cx.nodes[bound_tag].loc = cx.nodes[node].loc;
            let template = self.txv(ec).visit_node(cx, template);
            return ec
                .borrow_mut()
                .factory
                .update_tagged_template_expression(
                    cx.nodes,
                    node,
                    Some(bound_tag),
                    None,
                    None,
                    template,
                    flags,
                )
                .unwrap_or(node);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitPropertyAccessExpression`.
    fn visit_property_access_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let name = cx.nodes[node].as_property_access_expression().name;
        if ast::is_super_property(&cx.nodes[node], cx.nodes)
            && ast::is_identifier(&cx.nodes[name.expect("property access name")])
            && let (Some(class_this), Some(class_super)) =
                (self.class_this.get(), self.class_super.get())
        {
            let property_name = ec
                .borrow_mut()
                .factory
                .new_string_literal_from_node(cx.nodes, name.expect("property access name"));
            let super_property = ec.borrow_mut().factory.new_reflect_get_call(
                cx.nodes,
                class_super,
                property_name,
                class_this,
            );
            let expression = cx.nodes[node].as_property_access_expression().expression;
            if let Some(expression) = expression {
                ec.borrow().set_original(super_property, expression);
                cx.nodes[super_property].loc = cx.nodes[expression].loc;
            }
            return super_property;
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
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
        if ast::is_super_property(&cx.nodes[node], cx.nodes)
            && let (Some(class_this), Some(class_super)) =
                (self.class_this.get(), self.class_super.get())
        {
            let property_name = self.txv(ec).visit_node(cx, argument_expression);
            let super_property = ec.borrow_mut().factory.new_reflect_get_call(
                cx.nodes,
                class_super,
                property_name.expect("element access argument"),
                class_this,
            );
            if let Some(expression) = expression {
                ec.borrow().set_original(super_property, expression);
                cx.nodes[super_property].loc = cx.nodes[expression].loc;
            }
            return super_property;
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitParameterDeclaration`.
    fn visit_parameter_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let mut node = node;
        {
            let mut pred = |n: NodeId| is_anonymous_class_needing_assigned_name(cx, n);
            if is_named_evaluation_and(&ec.borrow(), cx.nodes, node, Some(&mut pred)) {
                let ignore = can_ignore_empty_string_literal_in_assigned_name(
                    cx,
                    cx.nodes[node].initializer(),
                );
                node = transform_named_evaluation(ec, cx, node, ignore, "");
            }
        }

        let (dot_dot_dot_token, name, initializer) = {
            let p = cx.nodes[node].as_parameter_declaration();
            (p.dot_dot_dot_token, p.name, p.initializer)
        };
        let visited_name = self.txv(ec).visit_node(cx, name);
        let visited_initializer = self.txv(ec).visit_node(cx, initializer);
        let updated = ec
            .borrow_mut()
            .factory
            .update_parameter_declaration(
                cx.nodes,
                node,
                None, // modifiers - strip all modifiers (including decorators)
                dot_dot_dot_token,
                visited_name,
                None, // question_token
                None, // type
                visited_initializer,
            )
            .unwrap_or(node);
        if updated != node {
            // While we emit the source map for the node after skipping decorators and modifiers,
            // we need to emit the comments for the original range.
            ec.borrow().set_comment_range(updated, cx.nodes[node].loc);
            let new_loc = transformer_utilities::move_range_past_modifiers(cx.nodes, node);
            cx.nodes[updated].loc = new_loc;
            ec.borrow().set_source_map_range(updated, new_loc);
            if let Some(name) = cx.nodes[updated].name() {
                ec.borrow()
                    .set_emit_flags(name, EmitFlags::NO_TRAILING_SOURCE_MAP);
            }
        }
        updated
    }

    /// `visitNamedEvaluationSite` replaces Strada's visitPropertyAssignment,
    /// visitVariableDeclaration, and visitBindingElement, which all share the
    /// same logic.
    fn visit_named_evaluation_site(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        class_expr: Option<NodeId>,
    ) -> NodeId {
        let mut node = node;
        {
            let mut pred = |n: NodeId| is_anonymous_class_needing_assigned_name(cx, n);
            if is_named_evaluation_and(&ec.borrow(), cx.nodes, node, Some(&mut pred)) {
                let ignore = can_ignore_empty_string_literal_in_assigned_name(cx, class_expr);
                node = transform_named_evaluation(ec, cx, node, ignore, "");
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
        let visited_initializer = visitor_ref!(self, discarded_visitor).visit_node(cx, initializer);
        let visited_condition = txv.visit_node(cx, condition);
        let visited_incrementor = visitor_ref!(self, discarded_visitor).visit_node(cx, incrementor);
        let visited_statement = ec_visit_iteration_body(&txv, cx, statement);
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
    fn visit_expression_statement(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        visitor_ref!(self, discarded_visitor)
            .visit_each_child(cx, node)
            .unwrap_or(node)
    }

    /// `visitBinaryExpression`.
    fn visit_binary_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        discarded: bool,
    ) -> NodeId {
        let (left, operator_token, right) = {
            let bin = cx.nodes[node].as_binary_expression();
            (bin.left, bin.operator_token, bin.right)
        };

        if ast::is_destructuring_assignment(&cx.nodes[node], cx.nodes) {
            let left = self.visit_assignment_pattern(ec, cx, left.expect("destructuring lhs"));
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

        if ast::is_assignment_expression(&cx.nodes[node], cx.nodes, false) {
            // 13.15.2 RS: Evaluation
            //   AssignmentExpression : LeftHandSideExpression `=` AssignmentExpression
            //     1. If |LeftHandSideExpression| is neither an |ObjectLiteral| nor an |ArrayLiteral|, then
            //        a. Let _lref_ be ? Evaluation of |LeftHandSideExpression|.
            //        b. If IsAnonymousFunctionDefinition(|AssignmentExpression|) and IsIdentifierRef of |LeftHandSideExpression| are both *true*, then
            //           i. Let _rval_ be ? NamedEvaluation of |AssignmentExpression| with argument _lref_.[[ReferencedName]].
            //     ...
            //
            //   AssignmentExpression : LeftHandSideExpression `&&=` AssignmentExpression
            //     ...
            //     5. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true* and IsIdentifierRef of |LeftHandSideExpression| is *true*, then
            //        a. Let _rval_ be ? NamedEvaluation of |AssignmentExpression| with argument _lref_.[[ReferencedName]].
            //     ...
            //
            //   AssignmentExpression : LeftHandSideExpression `||=` AssignmentExpression
            //     ...
            //     5. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true* and IsIdentifierRef of |LeftHandSideExpression| is *true*, then
            //        a. Let _rval_ be ? NamedEvaluation of |AssignmentExpression| with argument _lref_.[[ReferencedName]].
            //     ...
            //
            //   AssignmentExpression : LeftHandSideExpression `??=` AssignmentExpression
            //     ...
            //     4. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true* and IsIdentifierRef of |LeftHandSideExpression| is *true*, then
            //        a. Let _rval_ be ? NamedEvaluation of |AssignmentExpression| with argument _lref_.[[ReferencedName]].
            //     ...

            let mut node = node;
            {
                let mut pred = |n: NodeId| is_anonymous_class_needing_assigned_name(cx, n);
                if is_named_evaluation_and(&ec.borrow(), cx.nodes, node, Some(&mut pred)) {
                    let ignore = can_ignore_empty_string_literal_in_assigned_name(cx, right);
                    node = transform_named_evaluation(ec, cx, node, ignore, "");
                    return self.txv(ec).visit_each_child(cx, node).unwrap_or(node);
                }
            }

            if let (Some(left), Some(class_this), Some(class_super)) =
                (left, self.class_this.get(), self.class_super.get())
                && ast::is_super_property(&cx.nodes[left], cx.nodes)
            {
                let mut setter_name: Option<NodeId> = None;
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
                    setter_name = Some(
                        ec.borrow_mut().factory.new_string_literal_from_node(
                            cx.nodes,
                            cx.nodes[left]
                                .as_property_access_expression()
                                .name
                                .expect("property access name"),
                        ),
                    );
                }
                if let Some(mut setter_name) = setter_name {
                    // super.x = ...
                    // super.x += ...
                    // super[x] = ...
                    // super[x] += ...
                    let mut expression = self.txv(ec).visit_node(cx, right);
                    let operator_kind = operator_token.map(|t| cx.nodes[t].kind);
                    if operator_kind.is_some_and(|k| ast::is_compound_assignment(k)) {
                        let mut getter_name = setter_name;
                        if !transformer_utilities::is_simple_inlineable_expression(
                            &cx.nodes[setter_name],
                        ) {
                            getter_name = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
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
                            class_super,
                            getter_name,
                            class_this,
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
                            .add_variable_declaration(cx.nodes, temp.expect("temp"));
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
                    expression = Some(ec.borrow_mut().factory.new_reflect_set_call(
                        cx.nodes,
                        class_super,
                        setter_name,
                        expression.expect("expression"),
                        class_this,
                    ));
                    let mut expression = expression.expect("expression");
                    ec.borrow().set_original(expression, node);
                    cx.nodes[expression].loc = cx.nodes[node].loc;
                    if let Some(temp) = temp {
                        expression = ec
                            .borrow_mut()
                            .factory
                            .new_comma_expression(cx.nodes, expression, temp);
                        cx.nodes[expression].loc = cx.nodes[node].loc;
                    }
                    return expression;
                }
            }
        }

        if operator_token.map(|t| cx.nodes[t].kind) == Some(Kind::CommaToken) {
            let left = visitor_ref!(self, discarded_visitor).visit_node(cx, left);
            let right = if discarded {
                visitor_ref!(self, discarded_visitor).visit_node(cx, right)
            } else {
                self.txv(ec).visit_node(cx, right)
            };
            return ec
                .borrow_mut()
                .factory
                .update_binary_expression(cx.nodes, node, None, left, None, operator_token, right)
                .unwrap_or(node);
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
        let (operator, operand_node) = if ast::is_prefix_unary_expression(&cx.nodes[node]) {
            let p = cx.nodes[node].as_prefix_unary_expression();
            (p.operator, p.operand)
        } else {
            let p = cx.nodes[node].as_postfix_unary_expression();
            (p.operator, p.operand)
        };

        if operator == Kind::PlusPlusToken || operator == Kind::MinusMinusToken {
            let operand_node = operand_node.expect("unary operand");
            let operand = ast::skip_parentheses(operand_node, cx.nodes);
            if ast::is_super_property(&cx.nodes[operand], cx.nodes)
                && let (Some(class_this), Some(class_super)) =
                    (self.class_this.get(), self.class_super.get())
            {
                let mut setter_name: Option<NodeId> = None;
                if ast::is_element_access_expression(&cx.nodes[operand]) {
                    let arg = cx.nodes[operand]
                        .as_element_access_expression()
                        .argument_expression;
                    setter_name = self.txv(ec).visit_node(cx, arg);
                } else if ast::is_property_access_expression(&cx.nodes[operand])
                    && ast::is_identifier(
                        &cx.nodes[cx.nodes[operand]
                            .as_property_access_expression()
                            .name
                            .expect("property access name")],
                    )
                {
                    setter_name = Some(
                        ec.borrow_mut().factory.new_string_literal_from_node(
                            cx.nodes,
                            cx.nodes[operand]
                                .as_property_access_expression()
                                .name
                                .expect("property access name"),
                        ),
                    );
                }
                if let Some(mut setter_name) = setter_name {
                    let mut getter_name = setter_name;
                    if !transformer_utilities::is_simple_inlineable_expression(
                        &cx.nodes[setter_name],
                    ) {
                        getter_name = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                        ec.borrow_mut()
                            .add_variable_declaration(cx.nodes, getter_name);
                        setter_name = ec.borrow_mut().factory.new_assignment_expression(
                            cx.nodes,
                            getter_name,
                            setter_name,
                        );
                    }

                    let mut expression = ec.borrow_mut().factory.new_reflect_get_call(
                        cx.nodes,
                        class_super,
                        getter_name,
                        class_this,
                    );
                    ec.borrow().set_original(expression, node);
                    cx.nodes[expression].loc = cx.nodes[node].loc;

                    // If the result of this expression is discarded (i.e., it's in a position where the result
                    // will be otherwise unused, such as in an expression statement or the left side of a comma), we
                    // don't need to create an extra temp variable to hold the result:
                    //
                    //  source (discarded):
                    //    super.x++;
                    //  generated:
                    //    _a = Reflect.get(_super, "x"), _a++, Reflect.set(_super, "x", _a);
                    //
                    // Above, the temp variable `_a` is used to perform the correct coercion (i.e., number or
                    // bigint). Since the result of the postfix unary is discarded, we don't need to capture the
                    // result of the expression.
                    //
                    //  source (not discarded):
                    //    y = super.x++;
                    //  generated:
                    //    y = (_a = Reflect.get(_super, "x"), _b = _a++, Reflect.set(_super, "x", _a), _b);
                    //
                    // When the result isn't discarded, we introduce a new temp variable (`_b`) to capture the
                    // result of the operation so that we can provide it to `y` when the assignment is complete.
                    let mut temp: Option<NodeId> = None;
                    if !discarded {
                        temp = Some(ec.borrow_mut().factory.new_temp_variable(cx.nodes));
                        ec.borrow_mut()
                            .add_variable_declaration(cx.nodes, temp.expect("temp"));
                    }

                    expression =
                        super::classfields::expand_pre_or_postfix_increment_or_decrement_expression(
                            ec, cx, node, expression, temp,
                        );

                    expression = ec.borrow_mut().factory.new_reflect_set_call(
                        cx.nodes,
                        class_super,
                        setter_name,
                        expression,
                        class_this,
                    );
                    ec.borrow().set_original(expression, node);
                    cx.nodes[expression].loc = cx.nodes[node].loc;

                    if let Some(temp) = temp {
                        expression = ec
                            .borrow_mut()
                            .factory
                            .new_comma_expression(cx.nodes, expression, temp);
                        cx.nodes[expression].loc = cx.nodes[node].loc;
                    }

                    return expression;
                }
            }
        }

        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitReferencedPropertyName` — returns `(referencedName, name)`.
    fn visit_referenced_property_name(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> (NodeId, NodeId) {
        if ast::is_property_name_literal(&cx.nodes[node])
            || ast::is_private_identifier(&cx.nodes[node])
        {
            let name = ec
                .borrow_mut()
                .factory
                .new_string_literal_from_node(cx.nodes, node);
            let visited = self.txv(ec).visit_node(cx, Some(node)).unwrap_or(node);
            return (name, visited);
        }

        let cpn_expression = cx.nodes[node].as_computed_property_name().expression;
        if cpn_expression.is_some_and(|e| {
            ast::is_property_name_literal(&cx.nodes[e]) && !ast::is_identifier(&cx.nodes[e])
        }) {
            let name = ec.borrow_mut().factory.new_string_literal_from_node(
                cx.nodes,
                cpn_expression.expect("computed name expression"),
            );
            let visited = self.txv(ec).visit_node(cx, Some(node)).unwrap_or(node);
            return (name, visited);
        }

        let referenced_name = ec
            .borrow_mut()
            .factory
            .new_generated_name_for_node(cx.nodes, node);
        ec.borrow_mut()
            .add_variable_declaration(cx.nodes, referenced_name);

        let visited_expression = self.txv(ec).visit_node(cx, cpn_expression);
        let key = ec
            .borrow_mut()
            .factory
            .new_prop_key_helper(cx.nodes, visited_expression.expect("computed key"));
        let assignment =
            ec.borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, referenced_name, key);
        let injected = self.inject_pending_expressions(ec, cx, Some(assignment));
        let updated_name = ec
            .borrow_mut()
            .factory
            .update_computed_property_name(cx.nodes, node, injected)
            .unwrap_or(node);
        (referenced_name, updated_name)
    }

    /// `visitPropertyName`.
    fn visit_property_name(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        if node.is_some_and(|n| ast::is_computed_property_name(&cx.nodes[n])) {
            return Some(self.visit_computed_property_name(ec, cx, node.unwrap()));
        }
        self.txv(ec).visit_node(cx, node)
    }

    /// `visitComputedPropertyName`.
    fn visit_computed_property_name(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let expression = cx.nodes[node].as_computed_property_name().expression;
        let mut expression = self.txv(ec).visit_node(cx, expression);
        if !expression
            .is_some_and(|e| transformer_utilities::is_simple_inlineable_expression(&cx.nodes[e]))
        {
            expression = self.inject_pending_expressions(ec, cx, expression);
        }
        ec.borrow_mut()
            .factory
            .update_computed_property_name(cx.nodes, node, expression)
            .unwrap_or(node)
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

        if ast::is_super_property(&cx.nodes[node], cx.nodes)
            && let (Some(class_this), Some(class_super)) =
                (self.class_this.get(), self.class_super.get())
        {
            let mut property_name: Option<NodeId> = None;
            if ast::is_element_access_expression(&cx.nodes[node]) {
                let arg = cx.nodes[node]
                    .as_element_access_expression()
                    .argument_expression;
                property_name = self.txv(ec).visit_node(cx, arg);
            } else if ast::is_property_access_expression(&cx.nodes[node])
                && ast::is_identifier(
                    &cx.nodes[cx.nodes[node]
                        .as_property_access_expression()
                        .name
                        .expect("property access name")],
                )
            {
                property_name = Some(
                    ec.borrow_mut().factory.new_string_literal_from_node(
                        cx.nodes,
                        cx.nodes[node]
                            .as_property_access_expression()
                            .name
                            .expect("property access name"),
                    ),
                );
            }
            if let Some(property_name) = property_name {
                let param_name = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                let reflect_set = ec.borrow_mut().factory.new_reflect_set_call(
                    cx.nodes,
                    class_super,
                    property_name,
                    param_name,
                    class_this,
                );
                let expression = ec.borrow_mut().factory.new_assignment_target_wrapper(
                    cx.nodes,
                    param_name,
                    reflect_set,
                );
                ec.borrow().set_original(expression, node);
                cx.nodes[expression].loc = cx.nodes[node].loc;
                return expression;
            }
        }

        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitAssignmentElement`.
    fn visit_assignment_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // 13.15.5.5 RS: IteratorDestructuringAssignmentEvaluation
        //   AssignmentElement : DestructuringAssignmentTarget Initializer?
        //     ...
        //     4. If |Initializer| is present and _value_ is *undefined*, then
        //        a. If IsAnonymousFunctionDefinition(|Initializer|) and IsIdentifierRef of |DestructuringAssignmentTarget| are both *true*, then
        //           i. Let _v_ be ? NamedEvaluation of |Initializer| with argument _lref_.[[ReferencedName]].
        //     ...
        if ast::is_assignment_expression(
            &cx.nodes[node],
            cx.nodes,
            true, /*excludeCompoundAssignment*/
        ) {
            let mut node = node;
            {
                let mut pred = |n: NodeId| is_anonymous_class_needing_assigned_name(cx, n);
                if is_named_evaluation_and(&ec.borrow(), cx.nodes, node, Some(&mut pred)) {
                    let right = cx.nodes[node].as_binary_expression().right;
                    let ignore = can_ignore_empty_string_literal_in_assigned_name(cx, right);
                    node = transform_named_evaluation(ec, cx, node, ignore, "");
                }
            }
            let (left, operator_token, right) = {
                let bin = cx.nodes[node].as_binary_expression();
                (bin.left, bin.operator_token, bin.right)
            };
            let assignment_target = self.visit_destructuring_assignment_target(
                ec,
                cx,
                left.expect("assignment target"),
            );
            let initializer = self.txv(ec).visit_node(cx, right);
            return ec
                .borrow_mut()
                .factory
                .update_binary_expression(
                    cx.nodes,
                    node,
                    None,
                    Some(assignment_target),
                    None,
                    operator_token,
                    initializer,
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
            let expression = self.visit_destructuring_assignment_target(
                ec,
                cx,
                expression.expect("spread expression"),
            );
            return ec
                .borrow_mut()
                .factory
                .update_spread_element(cx.nodes, node, Some(expression))
                .unwrap_or(node);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitArrayAssignmentElement` — the `arrayAssignmentVisitor` callback.
    fn visit_array_assignment_element(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        debug_assert!(ast::is_expression(&cx.nodes[node], cx.nodes));
        if ast::is_spread_element(&cx.nodes[node]) {
            return Some(self.visit_assignment_rest_element(ec, cx, node));
        }
        if !ast::is_omitted_expression(&cx.nodes[node]) {
            return Some(self.visit_assignment_element(ec, cx, node));
        }
        self.txv(ec).visit_each_child(cx, node).or(Some(node))
    }

    /// `visitAssignmentPropertyNode`.
    fn visit_assignment_property_node(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // AssignmentProperty : PropertyName `:` AssignmentElement
        // AssignmentElement : DestructuringAssignmentTarget Initializer?

        // 13.15.5.6 RS: KeyedDestructuringAssignmentEvaluation
        //   AssignmentElement : DestructuringAssignmentTarget Initializer?
        //     ...
        //     3. If |Initializer| is present and _v_ is *undefined*, then
        //        a. If IsAnonymousfunctionDefinition(|Initializer|) and IsIdentifierRef of |DestructuringAssignmentTarget| are both *true*, then
        //           i. Let _rhsValue_ be ? NamedEvaluation of |Initializer| with argument _lref_.[[ReferencedName]].
        //     ...

        let (name, initializer) = {
            let pa = cx.nodes[node].as_property_assignment();
            (pa.named_member_base.name, pa.initializer)
        };
        let name = self.txv(ec).visit_node(cx, name);
        if initializer.is_some_and(|i| {
            ast::is_assignment_expression(
                &cx.nodes[i],
                cx.nodes,
                true, /*excludeCompoundAssignment*/
            )
        }) {
            let assignment_element =
                self.visit_assignment_element(ec, cx, initializer.expect("initializer"));
            return ec
                .borrow_mut()
                .factory
                .update_property_assignment(
                    cx.nodes,
                    node,
                    None,
                    name,
                    None,
                    None,
                    Some(assignment_element),
                )
                .unwrap_or(node);
        }
        if initializer.is_some_and(|i| ast::is_left_hand_side_expression(&cx.nodes[i], cx.nodes)) {
            let assignment_element = self.visit_destructuring_assignment_target(
                ec,
                cx,
                initializer.expect("initializer"),
            );
            return ec
                .borrow_mut()
                .factory
                .update_property_assignment(
                    cx.nodes,
                    node,
                    None,
                    name,
                    None,
                    None,
                    Some(assignment_element),
                )
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
        //   AssignmentProperty : IdentifierReference Initializer?
        //     ...
        //     4. If |Initializer?| is present and _v_ is *undefined*, then
        //        a. If IsAnonymousFunctionDefinition(|Initializer|) is *true*, then
        //           i. Set _v_ to ? NamedEvaluation of |Initializer| with argument _P_.
        //     ...
        let mut node = node;
        {
            let mut pred = |n: NodeId| is_anonymous_class_needing_assigned_name(cx, n);
            if is_named_evaluation_and(&ec.borrow(), cx.nodes, node, Some(&mut pred)) {
                let initializer = cx.nodes[node]
                    .as_shorthand_property_assignment()
                    .object_assignment_initializer;
                let ignore = can_ignore_empty_string_literal_in_assigned_name(cx, initializer);
                node = transform_named_evaluation(ec, cx, node, ignore, "");
            }
        }
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
            let expression = self.visit_destructuring_assignment_target(
                ec,
                cx,
                expression.expect("spread expression"),
            );
            return ec
                .borrow_mut()
                .factory
                .update_spread_assignment(cx.nodes, node, Some(expression))
                .unwrap_or(node);
        }
        self.txv(ec).visit_each_child(cx, node).unwrap_or(node)
    }

    /// `visitObjectAssignmentElement` — the `objectAssignmentVisitor` callback.
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
            return Some(self.visit_assignment_property_node(ec, cx, node));
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
            let (elements, multi_line) = {
                let ale = cx.nodes[node].as_array_literal_expression();
                (ale.elements.clone(), ale.multi_line)
            };
            let elements = visitor_ref!(self, array_assignment_visitor).visit_nodes(cx, elements);
            return ec
                .borrow_mut()
                .factory
                .update_array_literal_expression(cx.nodes, node, elements, multi_line)
                .unwrap_or(node);
        }
        let (properties, multi_line) = {
            let ole = cx.nodes[node].as_object_literal_expression();
            (ole.properties.clone(), ole.multi_line)
        };
        let properties = visitor_ref!(self, object_assignment_visitor).visit_nodes(cx, properties);
        ec.borrow_mut()
            .factory
            .update_object_literal_expression(cx.nodes, node, properties, multi_line)
            .unwrap_or(node)
    }

    /// `visitExportAssignment`.
    fn visit_export_assignment(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        // 16.2.3.7 RS: Evaluation
        //   ExportDeclaration : `export` `default` AssignmentExpression `;`
        //     1. If IsAnonymousFunctionDefinition(|AssignmentExpression|) is *true*, then
        //        a. Let _value_ be ? NamedEvaluation of |AssignmentExpression| with argument `"default"`.
        //     ...
        let expression = cx.nodes[node].expression();
        self.visit_named_evaluation_site(ec, cx, node, expression)
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
        //   ParenthesizedExpression : `(` Expression `)`
        //     ...
        //     2. Return ? NamedEvaluation of |Expression| with argument _name_.

        let expression = cx.nodes[node].as_parenthesized_expression().expression;
        let expression = if discarded {
            visitor_ref!(self, discarded_visitor).visit_node(cx, expression)
        } else {
            self.txv(ec).visit_node(cx, expression)
        };
        ec.borrow_mut()
            .factory
            .update_parenthesized_expression(cx.nodes, node, expression)
            .unwrap_or(node)
    }

    /// `visitPartiallyEmittedExpression`.
    fn visit_partially_emitted_expression(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        discarded: bool,
    ) -> NodeId {
        // Emulates 8.4.5 RS: NamedEvaluation
        let expression = cx.nodes[node].as_partially_emitted_expression().expression;
        let expression = if discarded {
            visitor_ref!(self, discarded_visitor).visit_node(cx, expression)
        } else {
            self.txv(ec).visit_node(cx, expression)
        };
        ec.borrow_mut()
            .factory
            .update_partially_emitted_expression(cx.nodes, node, expression)
            .unwrap_or(node)
    }

    /// `prependExpressions` prepends a list of expressions before a target
    /// expression, preserving parenthesization. If expression is nil, the
    /// pending expressions are inlined alone.
    fn prepend_expressions(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        pending: &[NodeId],
        expression: Option<NodeId>,
    ) -> Option<NodeId> {
        if pending.is_empty() {
            return expression;
        }
        let Some(expression) = expression else {
            return ec
                .borrow_mut()
                .factory
                .inline_expressions(cx.nodes, pending);
        };
        if ast::is_parenthesized_expression(&cx.nodes[expression]) {
            let mut exprs: Vec<NodeId> = Vec::with_capacity(pending.len() + 1);
            exprs.extend_from_slice(pending);
            exprs.push(
                cx.nodes[expression]
                    .as_parenthesized_expression()
                    .expression
                    .expect("parenthesized expression"),
            );
            let inlined = ec.borrow_mut().factory.inline_expressions(cx.nodes, &exprs);
            return Some(
                ec.borrow_mut()
                    .factory
                    .update_parenthesized_expression(cx.nodes, expression, inlined)
                    .unwrap_or(expression),
            );
        }
        let mut exprs: Vec<NodeId> = Vec::with_capacity(pending.len() + 1);
        exprs.extend_from_slice(pending);
        exprs.push(expression);
        ec.borrow_mut().factory.inline_expressions(cx.nodes, &exprs)
    }

    /// `injectPendingExpressions`.
    fn inject_pending_expressions(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        expression: Option<NodeId>,
    ) -> Option<NodeId> {
        let pending: Vec<NodeId> = self.pending_expressions.borrow().clone();
        let result = self.prepend_expressions(ec, cx, &pending, expression);
        debug_assert!(result.is_some());
        if result != expression {
            self.pending_expressions.borrow_mut().clear();
        }
        result
    }

    /// `injectPendingInitializers`.
    fn inject_pending_initializers(
        &self,
        ec: &Ec,
        ci: &Rc<RefCell<ClassInfo>>,
        cx: &mut VisitorCx<'_, '_>,
        is_static: bool,
        expression: Option<NodeId>,
    ) -> Option<NodeId> {
        let pending: Vec<NodeId> = if is_static {
            ci.borrow().pending_static_initializers.clone()
        } else {
            ci.borrow().pending_instance_initializers.clone()
        };
        let result = self.prepend_expressions(ec, cx, &pending, expression);
        if result != expression {
            if is_static {
                ci.borrow_mut().pending_static_initializers.clear();
            } else {
                ci.borrow_mut().pending_instance_initializers.clear();
            }
        }
        result
    }

    /// `transformAllDecoratorsOfDeclaration` — transforms all of the
    /// decorators for a declaration into an array of expressions.
    fn transform_all_decorators_of_declaration(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        decorators: Vec<NodeId>,
    ) -> Vec<NodeId> {
        if decorators.is_empty() {
            return Vec::new();
        }
        let mut result = Vec::with_capacity(decorators.len());
        for d in decorators {
            result.push(self.transform_decorator(ec, cx, d));
        }
        result
    }

    /// `transformDecorator` — transforms a decorator into an expression.
    fn transform_decorator(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        decorator: NodeId,
    ) -> NodeId {
        let expression_node = cx.nodes[decorator].as_decorator().expression;
        let expression = self
            .txv(ec)
            .visit_node(cx, expression_node)
            .expect("decorator expression");
        ec.borrow()
            .set_emit_flags(expression, EmitFlags::NO_COMMENTS);

        // preserve the 'this' binding for an access expression
        let inner_expression =
            ast::skip_outer_expressions(expression, ast::outer_expression_kinds::ALL, cx.nodes);
        if ast::is_access_expression(&cx.nodes[inner_expression]) {
            let (target, this_arg) = self.create_call_binding(ec, cx, expression);
            let bind_call =
                ec.borrow_mut()
                    .factory
                    .new_function_bind_call(cx.nodes, target, this_arg, vec![]);
            return ec.borrow_mut().factory.restore_outer_expressions(
                cx.nodes,
                Some(expression),
                bind_call,
                ast::outer_expression_kinds::ALL,
            );
        }
        expression
    }

    /// `createCallBinding` — returns `(target, thisArg)`.
    fn create_call_binding(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        expression: NodeId,
    ) -> (NodeId, NodeId) {
        let callee =
            ast::skip_outer_expressions(expression, ast::outer_expression_kinds::ALL, cx.nodes);
        if ast::is_super_property(&cx.nodes[callee], cx.nodes) {
            let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
            return (callee, this_expr);
        }
        if cx.nodes[callee].kind == Kind::SuperKeyword {
            let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
            return (callee, this_expr);
        }
        if ec.borrow().emit_flags(callee) & EmitFlags::HELPER_NAME != EmitFlags::NONE {
            let void_zero = ec.borrow_mut().factory.new_void_zero_expression(cx.nodes);
            return (callee, void_zero);
        }
        if ast::is_property_access_expression(&cx.nodes[callee]) {
            let (expr, name) = {
                let pa = cx.nodes[callee].as_property_access_expression();
                (pa.expression, pa.name)
            };
            if self.should_be_captured_in_temp_variable(cx, expr.expect("access expression")) {
                let this_arg = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                ec.borrow_mut().add_variable_declaration(cx.nodes, this_arg);
                let assign = ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    this_arg,
                    expr.expect("access expression"),
                );
                cx.nodes[assign].loc = expr.map(|e| cx.nodes[e].loc).unwrap_or_default();
                let target = ec.borrow_mut().factory.new_property_access_expression(
                    cx.nodes,
                    Some(assign),
                    None,
                    name,
                    NodeFlags::NONE,
                );
                cx.nodes[target].loc = cx.nodes[callee].loc;
                return (target, this_arg);
            }
            return (callee, expr.expect("access expression"));
        }
        if ast::is_element_access_expression(&cx.nodes[callee]) {
            let (expr, arg) = {
                let ea = cx.nodes[callee].as_element_access_expression();
                (ea.expression, ea.argument_expression)
            };
            if self.should_be_captured_in_temp_variable(cx, expr.expect("access expression")) {
                let this_arg = ec.borrow_mut().factory.new_temp_variable(cx.nodes);
                ec.borrow_mut().add_variable_declaration(cx.nodes, this_arg);
                let assign = ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    this_arg,
                    expr.expect("access expression"),
                );
                cx.nodes[assign].loc = expr.map(|e| cx.nodes[e].loc).unwrap_or_default();
                let target = ec.borrow_mut().factory.new_element_access_expression(
                    cx.nodes,
                    Some(assign),
                    None,
                    arg,
                    NodeFlags::NONE,
                );
                cx.nodes[target].loc = cx.nodes[callee].loc;
                return (target, this_arg);
            }
            return (callee, expr.expect("access expression"));
        }
        let void_zero = ec.borrow_mut().factory.new_void_zero_expression(cx.nodes);
        (expression, void_zero)
    }

    /// `shouldBeCapturedInTempVariable` — a simplified version of the general
    /// shouldBeCapturedInTempVariable from nodeFactory with
    /// cacheIdentifiers=true, since createCallBinding in this transform
    /// always caches identifiers.
    fn should_be_captured_in_temp_variable(&self, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        let target = ast::skip_parentheses(node, cx.nodes);
        match cx.nodes[target].kind {
            // cacheIdentifiers is always true for this transform's createCallBinding
            Kind::Identifier => true,
            Kind::ThisKeyword
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::StringLiteral => false,
            _ => true,
        }
    }

    /// `createDescriptorMethod` — creates a "value", "get", or "set" method
    /// for a pseudo-PropertyDescriptor object created for a private element.
    fn create_descriptor_method(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        original: NodeId,
        name: NodeId, // PrivateIdentifier
        modifiers: Option<ModifierList>,
        asterisk_token: Option<NodeId>,
        kind: &str,
        parameters: Option<NodeList>,
        body: Option<NodeId>,
    ) -> NodeId {
        let body = match body {
            Some(body) => body,
            None => {
                let empty = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
                ec.borrow_mut()
                    .factory
                    .new_block(cx.nodes, Some(empty), false)
            }
        };

        let func_expr = ec.borrow_mut().factory.new_function_expression(
            cx.nodes,
            modifiers,
            asterisk_token,
            None, // name
            None, // type_parameters
            parameters,
            None, // type
            None, // full_signature
            Some(body),
        );
        ec.borrow().set_original(func_expr, original);
        ec.borrow().set_source_map_range(
            func_expr,
            transformer_utilities::move_range_past_decorators(cx.nodes, original),
        );
        ec.borrow()
            .set_emit_flags(func_expr, EmitFlags::NO_COMMENTS);

        let prefix: &str = if kind == "get" || kind == "set" {
            kind
        } else {
            ""
        };
        let function_name = ec
            .borrow_mut()
            .factory
            .new_string_literal_from_node(cx.nodes, name);
        let named_function = ec.borrow_mut().factory.new_set_function_name_helper(
            cx.nodes,
            func_expr,
            function_name,
            prefix,
        );

        let kind_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, kind);
        let method = ec.borrow_mut().factory.new_property_assignment(
            cx.nodes,
            None,
            Some(kind_ident),
            None,
            None,
            Some(named_function),
        );
        ec.borrow().set_original(method, original);
        ec.borrow().set_source_map_range(
            method,
            transformer_utilities::move_range_past_decorators(cx.nodes, original),
        );
        ec.borrow().set_emit_flags(method, EmitFlags::NO_COMMENTS);
        method
    }

    /// `createMethodDescriptorObject` — creates a pseudo-PropertyDescriptor
    /// object used when decorating a private MethodDeclaration.
    fn create_method_descriptor_object(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        member: NodeId,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let parameter_list = cx.nodes[member].parameter_list().cloned();
        let parameters = self.txv(ec).visit_nodes(cx, parameter_list);
        let body = self.txv(ec).visit_node(cx, cx.nodes[member].body());
        let asterisk_token = cx.nodes[member]
            .as_method_declaration()
            .function_like_with_body_base
            .body_base
            .asterisk_token;
        let name = cx.nodes[member].name().expect("method name");
        let method = self.create_descriptor_method(
            ec,
            cx,
            member,
            name,
            modifiers,
            asterisk_token,
            "value",
            parameters,
            body,
        );
        let props = ec.borrow_mut().factory.new_node_list([method]);
        ec.borrow_mut()
            .factory
            .new_object_literal_expression(cx.nodes, Some(props), false)
    }

    /// `createGetAccessorDescriptorObject` — creates a pseudo-PropertyDescriptor
    /// object used when decorating a private GetAccessor.
    fn create_get_accessor_descriptor_object(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        member: NodeId,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let body = self.txv(ec).visit_node(cx, cx.nodes[member].body());
        let empty_params = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
        let name = cx.nodes[member].name().expect("accessor name");
        let method = self.create_descriptor_method(
            ec,
            cx,
            member,
            name,
            modifiers,
            None,
            "get",
            Some(empty_params),
            body,
        );
        let props = ec.borrow_mut().factory.new_node_list([method]);
        ec.borrow_mut()
            .factory
            .new_object_literal_expression(cx.nodes, Some(props), false)
    }

    /// `createSetAccessorDescriptorObject` — creates a pseudo-PropertyDescriptor
    /// object used when decorating a private SetAccessor.
    fn create_set_accessor_descriptor_object(
        self: &Rc<Self>,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        member: NodeId,
        modifiers: Option<ModifierList>,
    ) -> NodeId {
        let parameter_list = cx.nodes[member].parameter_list().cloned();
        let parameters = self.txv(ec).visit_nodes(cx, parameter_list);
        let body = self.txv(ec).visit_node(cx, cx.nodes[member].body());
        let name = cx.nodes[member].name().expect("accessor name");
        let method = self.create_descriptor_method(
            ec, cx, member, name, modifiers, None, "set", parameters, body,
        );
        let props = ec.borrow_mut().factory.new_node_list([method]);
        ec.borrow_mut()
            .factory
            .new_object_literal_expression(cx.nodes, Some(props), false)
    }

    /// `createAccessorPropertyDescriptorObject` — creates a pseudo-PropertyDescriptor
    /// object used when decorating a private auto-accessor PropertyDeclaration.
    /// The descriptor contains get/set methods that access the generated
    /// backing field.
    fn create_accessor_property_descriptor_object(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        member: NodeId,
        _modifiers: Option<ModifierList>,
    ) -> NodeId {
        //  {
        //      get() { return this.${privateName}; },
        //      set(value) { this.${privateName} = value; },
        //  }
        let member_name = cx.nodes[member].name().expect("member name");
        let options = AutoGenerateOptions {
            suffix: "_accessor_storage".to_string(),
            ..Default::default()
        };
        let backing_field_name = ec
            .borrow_mut()
            .factory
            .new_generated_private_name_for_node_ex(cx.nodes, member_name, &options);

        let empty_params = ec.borrow_mut().factory.new_node_list(Vec::<NodeId>::new());
        let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
        let backing_access = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(this_expr),
            None,
            Some(backing_field_name),
            NodeFlags::NONE,
        );
        let return_stmt = ec
            .borrow_mut()
            .factory
            .new_return_statement(cx.nodes, Some(backing_access));
        let get_body_stmts = ec.borrow_mut().factory.new_node_list([return_stmt]);
        let get_body = ec
            .borrow_mut()
            .factory
            .new_block(cx.nodes, Some(get_body_stmts), false);
        let get_method = self.create_descriptor_method(
            ec,
            cx,
            member,
            member_name,
            None,
            None,
            "get",
            Some(empty_params),
            Some(get_body),
        );

        let value_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "value");
        let set_param = ec.borrow_mut().factory.new_parameter_declaration(
            cx.nodes,
            None,
            None,
            Some(value_ident),
            None,
            None,
            None,
        );
        let set_params = ec.borrow_mut().factory.new_node_list([set_param]);
        let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
        let backing_access = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(this_expr),
            None,
            Some(backing_field_name),
            NodeFlags::NONE,
        );
        let value_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "value");
        let assign = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            backing_access,
            value_ident,
        );
        let set_stmt = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(assign));
        let set_body_stmts = ec.borrow_mut().factory.new_node_list([set_stmt]);
        let set_body = ec
            .borrow_mut()
            .factory
            .new_block(cx.nodes, Some(set_body_stmts), false);
        let set_method = self.create_descriptor_method(
            ec,
            cx,
            member,
            member_name,
            None,
            None,
            "set",
            Some(set_params),
            Some(set_body),
        );

        let props = ec
            .borrow_mut()
            .factory
            .new_node_list([get_method, set_method]);
        ec.borrow_mut()
            .factory
            .new_object_literal_expression(cx.nodes, Some(props), false)
    }

    /// `createMethodDescriptorForwarder` — creates a MethodDeclaration that
    /// forwards its invocation to a PropertyDescriptor object.
    fn create_method_descriptor_forwarder(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        modifiers: Option<ModifierList>,
        name: Option<NodeId>,
        descriptor_name: NodeId,
    ) -> NodeId {
        let static_only =
            visitor_ref!(self, static_only_modifier_visitor).visit_modifiers(cx, modifiers);
        let value_ident = cx.factory.new_identifier(cx.nodes, "value");
        let access = cx.factory.new_property_access_expression(
            cx.nodes,
            Some(descriptor_name),
            None,
            Some(value_ident),
            NodeFlags::NONE,
        );
        let return_stmt = cx.factory.new_return_statement(cx.nodes, Some(access));
        let stmts = cx.factory.new_node_list([return_stmt]);
        let body = cx.factory.new_block(cx.nodes, Some(stmts), false);
        let empty_params = cx.factory.new_node_list(Vec::<NodeId>::new());
        cx.factory.new_get_accessor_declaration(
            cx.nodes,
            static_only,
            name,
            None, // type_parameters
            Some(empty_params),
            None, // type
            None, // full_signature
            Some(body),
        )
    }

    /// `createGetAccessorDescriptorForwarder` — creates a GetAccessor that
    /// forwards its invocation to a PropertyDescriptor object.
    fn create_get_accessor_descriptor_forwarder(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        modifiers: Option<ModifierList>,
        name: Option<NodeId>,
        descriptor_name: NodeId,
    ) -> NodeId {
        let static_only =
            visitor_ref!(self, static_only_modifier_visitor).visit_modifiers(cx, modifiers);
        let get_ident = cx.factory.new_identifier(cx.nodes, "get");
        let access = cx.factory.new_property_access_expression(
            cx.nodes,
            Some(descriptor_name),
            None,
            Some(get_ident),
            NodeFlags::NONE,
        );
        let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
        let call = ec.borrow_mut().factory.new_function_call_call(
            cx.nodes,
            access,
            Some(this_expr),
            vec![],
        );
        let return_stmt = cx.factory.new_return_statement(cx.nodes, Some(call));
        let stmts = cx.factory.new_node_list([return_stmt]);
        let body = cx.factory.new_block(cx.nodes, Some(stmts), false);
        let empty_params = cx.factory.new_node_list(Vec::<NodeId>::new());
        cx.factory.new_get_accessor_declaration(
            cx.nodes,
            static_only,
            name,
            None, // type_parameters
            Some(empty_params),
            None, // type
            None, // full_signature
            Some(body),
        )
    }

    /// `createSetAccessorDescriptorForwarder` — creates a SetAccessor that
    /// forwards its invocation to a PropertyDescriptor object.
    fn create_set_accessor_descriptor_forwarder(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        modifiers: Option<ModifierList>,
        name: Option<NodeId>,
        descriptor_name: NodeId,
    ) -> NodeId {
        let static_only =
            visitor_ref!(self, static_only_modifier_visitor).visit_modifiers(cx, modifiers);
        let set_ident = cx.factory.new_identifier(cx.nodes, "set");
        let access = cx.factory.new_property_access_expression(
            cx.nodes,
            Some(descriptor_name),
            None,
            Some(set_ident),
            NodeFlags::NONE,
        );
        let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
        let value_ident = cx.factory.new_identifier(cx.nodes, "value");
        let call = ec.borrow_mut().factory.new_function_call_call(
            cx.nodes,
            access,
            Some(this_expr),
            vec![value_ident],
        );
        let return_stmt = cx.factory.new_return_statement(cx.nodes, Some(call));
        let stmts = cx.factory.new_node_list([return_stmt]);
        let body = cx.factory.new_block(cx.nodes, Some(stmts), false);
        let value_ident = cx.factory.new_identifier(cx.nodes, "value");
        let param = cx.factory.new_parameter_declaration(
            cx.nodes,
            None,
            None,
            Some(value_ident),
            None,
            None,
            None,
        );
        let params = cx.factory.new_node_list([param]);
        cx.factory.new_set_accessor_declaration(
            cx.nodes,
            static_only,
            name,
            None, // type_parameters
            Some(params),
            None, // type
            None, // full_signature
            Some(body),
        )
    }

    /// `createMetadata`.
    fn create_metadata(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        class_super: Option<NodeId>,
    ) -> NodeId {
        let super_metadata = match class_super {
            Some(class_super) => self.create_symbol_metadata_reference(ec, cx, class_super),
            None => ec
                .borrow_mut()
                .factory
                .new_token(cx.nodes, Kind::NullKeyword),
        };

        let object_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "Object");
        let create_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "create");
        let object_create_access = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(object_ident),
            None,
            Some(create_ident),
            NodeFlags::NONE,
        );
        let args = ec.borrow_mut().factory.new_node_list([super_metadata]);
        let object_create = ec.borrow_mut().factory.new_call_expression(
            cx.nodes,
            Some(object_create_access),
            None,
            None,
            Some(args),
            NodeFlags::NONE,
        );

        let symbol_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "Symbol");
        let symbol_type_check =
            ec.borrow_mut()
                .factory
                .new_type_check(cx.nodes, symbol_ident, "function");
        let symbol_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "Symbol");
        let metadata_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "metadata");
        let symbol_metadata_access = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(symbol_ident),
            None,
            Some(metadata_ident),
            NodeFlags::NONE,
        );
        let symbol_check = ec.borrow_mut().factory.new_logical_and_expression(
            cx.nodes,
            symbol_type_check,
            symbol_metadata_access,
        );

        let question_token = ec
            .borrow_mut()
            .factory
            .new_token(cx.nodes, Kind::QuestionToken);
        let colon_token = ec
            .borrow_mut()
            .factory
            .new_token(cx.nodes, Kind::ColonToken);
        let void_zero = ec.borrow_mut().factory.new_void_zero_expression(cx.nodes);
        let conditional = ec.borrow_mut().factory.new_conditional_expression(
            cx.nodes,
            Some(symbol_check),
            Some(question_token),
            Some(object_create),
            Some(colon_token),
            Some(void_zero),
        );

        let var_decl = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(name),
            None,
            None,
            Some(conditional),
        );
        let decls = ec.borrow_mut().factory.new_node_list([var_decl]);
        let var_decl_list = ec.borrow_mut().factory.new_variable_declaration_list(
            cx.nodes,
            Some(decls),
            NodeFlags::CONST,
        );
        ec.borrow_mut()
            .factory
            .new_variable_statement(cx.nodes, None, Some(var_decl_list))
    }

    /// `createSymbolMetadata`.
    fn create_symbol_metadata(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        target: NodeId,
        value: NodeId,
    ) -> NodeId {
        // Object.defineProperty(target, Symbol.metadata, { configurable: true, writable: true, enumerable: true, value })
        let symbol_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "Symbol");
        let metadata_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "metadata");
        let symbol_metadata = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(symbol_ident),
            None,
            Some(metadata_ident),
            NodeFlags::NONE,
        );

        let mut descriptor_props: Vec<NodeId> = Vec::with_capacity(4);
        for (prop_name, value_expr) in [
            ("enumerable", None),
            ("configurable", None),
            ("writable", None),
            ("value", Some(value)),
        ] {
            let ident = ec.borrow_mut().factory.new_identifier(cx.nodes, prop_name);
            let initializer = match value_expr {
                Some(v) => v,
                None => ec.borrow_mut().factory.new_true_expression(cx.nodes),
            };
            let prop = ec.borrow_mut().factory.new_property_assignment(
                cx.nodes,
                None,
                Some(ident),
                None,
                None,
                Some(initializer),
            );
            descriptor_props.push(prop);
        }
        let props = ec.borrow_mut().factory.new_node_list(descriptor_props);
        let descriptor =
            ec.borrow_mut()
                .factory
                .new_object_literal_expression(cx.nodes, Some(props), false);

        let object_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "Object");
        let define_property_ident = ec
            .borrow_mut()
            .factory
            .new_identifier(cx.nodes, "defineProperty");
        let define_property_access = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(object_ident),
            None,
            Some(define_property_ident),
            NodeFlags::NONE,
        );
        let args = ec
            .borrow_mut()
            .factory
            .new_node_list([target, symbol_metadata, descriptor]);
        let define_property = ec.borrow_mut().factory.new_call_expression(
            cx.nodes,
            Some(define_property_access),
            None,
            None,
            Some(args),
            NodeFlags::NONE,
        );

        let expr_stmt = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(define_property));
        let if_statement =
            ec.borrow_mut()
                .factory
                .new_if_statement(cx.nodes, Some(value), Some(expr_stmt), None);
        ec.borrow()
            .set_emit_flags(if_statement, EmitFlags::SINGLE_LINE);
        if_statement
    }

    /// `createSymbolMetadataReference`.
    fn create_symbol_metadata_reference(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        class_super: NodeId,
    ) -> NodeId {
        let symbol_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "Symbol");
        let metadata_ident = ec.borrow_mut().factory.new_identifier(cx.nodes, "metadata");
        let symbol_metadata = ec.borrow_mut().factory.new_property_access_expression(
            cx.nodes,
            Some(symbol_ident),
            None,
            Some(metadata_ident),
            NodeFlags::NONE,
        );
        let element_access = ec.borrow_mut().factory.new_element_access_expression(
            cx.nodes,
            Some(class_super),
            None,
            Some(symbol_metadata),
            NodeFlags::NONE,
        );
        let qq_token = ec
            .borrow_mut()
            .factory
            .new_token(cx.nodes, Kind::QuestionQuestionToken);
        let null_token = ec
            .borrow_mut()
            .factory
            .new_token(cx.nodes, Kind::NullKeyword);
        ec.borrow_mut().factory.new_binary_expression(
            cx.nodes,
            None,
            Some(element_access),
            None,
            Some(qq_token),
            Some(null_token),
        )
    }
}

/// `getHelperVariableName`.
fn get_helper_variable_name(
    ec: &tsc_printer::EmitContext,
    cx: &VisitorCx<'_, '_>,
    node: NodeId,
) -> String {
    let name = cx.nodes[node].name();
    let mut declaration_name = String::new();
    if let Some(name) = name
        && ast::is_identifier(&cx.nodes[name])
        && !transformer_utilities::is_generated_identifier(ec, name)
    {
        declaration_name = cx.nodes[name].as_identifier().text.clone();
    } else if let Some(name) = name
        && ast::is_private_identifier(&cx.nodes[name])
        && !ec.has_auto_generate_info(Some(name))
    {
        let text = cx.nodes[name].as_private_identifier().text.clone();
        if text.len() > 1 {
            declaration_name = text[1..].to_string();
        }
    } else if let Some(name) = name
        && ast::is_string_literal(&cx.nodes[name])
        && is_identifier_text(
            &cx.nodes[name]
                .as_string_literal()
                .literal_expression_base
                .literal_like_node_base
                .text,
            LanguageVariant::Standard,
        )
    {
        declaration_name = cx.nodes[name]
            .as_string_literal()
            .literal_expression_base
            .literal_like_node_base
            .text
            .clone();
    } else if ast::is_class_like(Some(node), cx.nodes) {
        declaration_name = "class".to_string();
    } else {
        declaration_name = "member".to_string();
    }

    if ast::is_get_accessor_declaration(&cx.nodes[node]) {
        declaration_name = format!("get_{declaration_name}");
    }
    if ast::is_set_accessor_declaration(&cx.nodes[node]) {
        declaration_name = format!("set_{declaration_name}");
    }
    if name.is_some_and(|n| ast::is_private_identifier(&cx.nodes[n])) {
        declaration_name = format!("private_{declaration_name}");
    }
    if ast::is_static(&cx.nodes[node]) {
        declaration_name = format!("static_{declaration_name}");
    }
    format!("_{declaration_name}")
}

/// `isDecoratedClassLike`.
fn is_decorated_class_like(cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
    ast::class_or_constructor_parameter_is_decorated(false, node, cx.nodes)
        // Go passes `nil` for parent; the Rust port requires a `NodeId` —
        // `node` is unused when `useLegacyDecorators` is false.
        || ast::child_is_decorated(false, node, node, cx.nodes)
}

/// `isAnonymousClassNeedingAssignedName`.
fn is_anonymous_class_needing_assigned_name(cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
    ast::is_class_expression(&cx.nodes[node])
        && cx.nodes[node].name().is_none()
        && is_decorated_class_like(cx, node)
}

// The IIFE produced for `(@dec class {})` will result in an assigned name of the form
// `var class_1 = class { };`, and thus the empty string cannot be ignored. However, The IIFE
// produced for `(class { @dec x; })` will not result in an assigned name since it
// transforms to `return class { };`, and thus the empty string *can* be ignored.
/// `canIgnoreEmptyStringLiteralInAssignedName`.
fn can_ignore_empty_string_literal_in_assigned_name(
    cx: &VisitorCx<'_, '_>,
    node: Option<NodeId>,
) -> bool {
    let Some(node) = node else {
        return false;
    };
    let inner_expression =
        ast::skip_outer_expressions(node, ast::outer_expression_kinds::ALL, cx.nodes);
    ast::is_class_expression(&cx.nodes[inner_expression])
        && cx.nodes[inner_expression].name().is_none()
        && !ast::class_or_constructor_parameter_is_decorated(false, inner_expression, cx.nodes)
}

/// `injectClassThisAssignmentIfMissing`.
fn inject_class_this_assignment_if_missing(
    ec: &Ec,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    class_this: NodeId,
) -> NodeId {
    if class_has_class_this_assignment(&ec.borrow(), cx.nodes, node) {
        return node;
    }

    // Create: static { _classThis = this; }
    let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
    let expression = ec
        .borrow_mut()
        .factory
        .new_assignment_expression(cx.nodes, class_this, this_expr);
    let statement = ec
        .borrow_mut()
        .factory
        .new_expression_statement(cx.nodes, Some(expression));
    let stmts = ec.borrow_mut().factory.new_node_list([statement]);
    let body = ec
        .borrow_mut()
        .factory
        .new_block(cx.nodes, Some(stmts), false);
    let static_block =
        ec.borrow_mut()
            .factory
            .new_class_static_block_declaration(cx.nodes, None, Some(body));
    ec.borrow().set_class_this(static_block, class_this);

    if let Some(name) = cx.nodes[node].name() {
        ec.borrow()
            .set_source_map_range(statement, cx.nodes[name].loc);
    }

    let mut new_members: Vec<NodeId> =
        Vec::with_capacity(1 + cx.nodes[node].members().map(|m| m.len()).unwrap_or(0));
    new_members.push(static_block);
    if let Some(members) = cx.nodes[node].members() {
        new_members.extend(members.iter().copied());
    }
    let mut members_list = ec.borrow_mut().factory.new_node_list(new_members);
    members_list.loc = cx.nodes[node]
        .member_list()
        .map(|l| l.loc)
        .unwrap_or_default();

    let updated_node = if ast::is_class_declaration(&cx.nodes[node]) {
        let (modifiers, name, heritage_clauses) = {
            let d = &cx.nodes[node].as_class_declaration().class_like_base;
            (
                d.modifiers_base.modifiers.clone(),
                d.name,
                d.heritage_clauses.clone(),
            )
        };
        ec.borrow_mut()
            .factory
            .update_class_declaration(
                cx.nodes,
                node,
                modifiers,
                name,
                None,
                heritage_clauses,
                Some(members_list),
            )
            .unwrap_or(node)
    } else {
        let (modifiers, name, heritage_clauses) = {
            let d = &cx.nodes[node].as_class_expression().class_like_base;
            (
                d.modifiers_base.modifiers.clone(),
                d.name,
                d.heritage_clauses.clone(),
            )
        };
        ec.borrow_mut()
            .factory
            .update_class_expression(
                cx.nodes,
                node,
                modifiers,
                name,
                None,
                heritage_clauses,
                Some(members_list),
            )
            .unwrap_or(node)
    };
    ec.borrow().set_class_this(updated_node, class_this);
    updated_node
}

/// `newESDecoratorTransformer`.
pub(crate) fn new_es_decorator_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    // When experimentalDecorators is set, the legacy decorator transformer handles all
    // decorators. When targeting ESNext with useDefineForClassFields, there's nothing to
    // transform. In either case every node would be returned unchanged, so skip entirely.
    if let Some(compiler_options) = opts.compiler_options {
        if compiler_options.experimental_decorators == Tristate::True
            || (compiler_options.get_emit_script_target() >= ScriptTarget::ESNext
                && compiler_options.get_use_define_for_class_fields())
        {
            return None;
        }
    }
    let compiler_options = opts.compiler_options;
    make_transformer(opts, |ec| {
        let state = Rc::new(EsDecoratorTransformer {
            compiler_options,
            top: RefCell::new(Vec::new()),
            class_info_stack: RefCell::new(None),
            class_this: Cell::new(None),
            class_super: Cell::new(None),
            pending_expressions: RefCell::new(Vec::new()),
            outer_this: Cell::new(None),
            should_transform_private_static_elements_in_file: Cell::new(false),
            outer_this_visitor: RefCell::new(None),
            discarded_visitor: RefCell::new(None),
            modifier_visitor: RefCell::new(None),
            export_stripping_modifier_visitor: RefCell::new(None),
            class_element_visitor: RefCell::new(None),
            non_constructor_class_element_visitor: RefCell::new(None),
            constructor_class_element_visitor: RefCell::new(None),
            array_assignment_visitor: RefCell::new(None),
            object_assignment_visitor: RefCell::new(None),
            static_only_modifier_visitor: RefCell::new(None),
            async_only_modifier_visitor: RefCell::new(None),
            accessor_stripping_modifier_visitor: RefCell::new(None),
        });
        macro_rules! install {
            ($field:ident, $method:ident, with_v) => {{
                let weak = Rc::downgrade(&state);
                let ec2 = ec.clone();
                let visit: Box<VisitFn<'a>> = Box::new(
                    move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                        let s = weak
                            .upgrade()
                            .expect("esDecoratorTransformer dropped during visit");
                        s.$method(&ec2, v, cx, node)
                    },
                );
                *state.$field.borrow_mut() = Some(ec.borrow().new_node_visitor(visit));
            }};
            ($field:ident, $method:ident) => {{
                let weak = Rc::downgrade(&state);
                let ec2 = ec.clone();
                let visit: Box<VisitFn<'a>> = Box::new(
                    move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                        let s = weak
                            .upgrade()
                            .expect("esDecoratorTransformer dropped during visit");
                        s.$method(&ec2, cx, node)
                    },
                );
                *state.$field.borrow_mut() = Some(ec.borrow().new_node_visitor(visit));
            }};
        }
        install!(outer_this_visitor, outer_this_visit);
        install!(discarded_visitor, discarded_value_visit, with_v);
        install!(class_element_visitor, class_element_visitor_visit, with_v);
        install!(
            non_constructor_class_element_visitor,
            non_constructor_class_element_visit,
            with_v
        );
        install!(
            constructor_class_element_visitor,
            constructor_class_element_visit,
            with_v
        );
        install!(array_assignment_visitor, visit_array_assignment_element);
        install!(object_assignment_visitor, visit_object_assignment_element);
        {
            let weak = Rc::downgrade(&state);
            let visit: Box<VisitFn<'a>> = Box::new(
                move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    let s = weak
                        .upgrade()
                        .expect("esDecoratorTransformer dropped during visit");
                    s.modifier_visitor_visit(cx, node)
                },
            );
            *state.modifier_visitor.borrow_mut() = Some(ec.borrow().new_node_visitor(visit));
        }
        {
            let weak = Rc::downgrade(&state);
            let visit: Box<VisitFn<'a>> = Box::new(
                move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    let s = weak
                        .upgrade()
                        .expect("esDecoratorTransformer dropped during visit");
                    s.export_stripping_modifier_visit(cx, node)
                },
            );
            *state.export_stripping_modifier_visitor.borrow_mut() =
                Some(ec.borrow().new_node_visitor(visit));
        }
        {
            let visit: Box<VisitFn<'a>> = Box::new(
                |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    if cx.nodes[node].kind == Kind::StaticKeyword {
                        return Some(node);
                    }
                    None
                },
            );
            *state.static_only_modifier_visitor.borrow_mut() =
                Some(ec.borrow().new_node_visitor(visit));
        }
        {
            let visit: Box<VisitFn<'a>> = Box::new(
                |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    if cx.nodes[node].kind == Kind::AsyncKeyword {
                        return Some(node);
                    }
                    None
                },
            );
            *state.async_only_modifier_visitor.borrow_mut() =
                Some(ec.borrow().new_node_visitor(visit));
        }
        {
            let visit: Box<VisitFn<'a>> = Box::new(
                |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                    if cx.nodes[node].kind == Kind::AccessorKeyword {
                        return None;
                    }
                    Some(node)
                },
            );
            *state.accessor_stripping_modifier_visitor.borrow_mut() =
                Some(ec.borrow().new_node_visitor(visit));
        }
        Box::new(
            move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, v, cx, node)
            },
        )
    })
}
