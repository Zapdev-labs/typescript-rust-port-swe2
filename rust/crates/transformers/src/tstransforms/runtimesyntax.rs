// Ported from tsc/internal/transformers/tstransforms/runtimesyntax.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Transforms TypeScript-specific runtime syntax (enums, namespaces/modules,
// `import x = ...` aliases, parameter properties, namespace-qualified
// exports) into JavaScript-compatible syntax.
//
// PORT notes:
//   - `parentNode`/`currentNode`/`currentScope`/`currentEnum`/
//     `currentNamespace`/`currentSourceFile` are `Cell<Option<NodeId>>`s on
//     the shared state; `currentScopeFirstDeclarationsOfName` is a
//     `RefCell<Option<FxHashMap<String, NodeId>>>`.
//   - `resolver`/`emitResolver` are `Option<Rc<RefCell<dyn ...>>>` mirroring
//     Go's nilable interfaces; call sites `.expect()` like Go's
//     nil-interface panic.
//   - `ReferenceResolver` methods take `&mut Vec<Symbol>` — the file's bound
//     symbol arena is threaded through `TransformOptions::symbols`
//     (`Option<&'a SymbolArena>`), matching `legacydecorators.rs`
//     (see the module PORT note).

use std::cell::{Cell, RefCell};
use std::rc::{Rc, Weak};

use rustc_hash::FxHashMap;
use tsc_ast::visitor::{NodeVisitor, VisitorCx};
use tsc_ast::{
    self as ast, Kind, ModifierFlags, Node, NodeFlags, NodeId, NodeList, SubtreeFacts, SymbolArena, };
use tsc_binder::referenceresolver::ReferenceResolver;
use tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS;
use tsc_core::core::{coalesce, find};
use tsc_core::options_generated::{CompilerOptions, ModuleKind};
use tsc_core::text::TextRange;
use tsc_evaluator::Value;
use tsc_printer::{AssignedNameOptions, EmitFlags, EmitResolver, NameOptions};

use super::utilities::constant_expression;
use crate::chain::TransformOptions;
use crate::destructuring::{FlattenLevel, flatten_destructuring_assignment};
use crate::estransforms::{Ec, make_transformer, tx_adapter, visit_each_child};
use crate::modifier_visitor::extract_modifiers;
use crate::transformer::Transformer;
use crate::utilities::{
    convert_variable_declaration_to_assignment_expression, find_super_statement_index_path,
    is_generated_identifier, is_identifier_reference, is_local_name,
};

/// `type RuntimeSyntaxTransformer struct`.
pub struct RuntimeSyntaxTransformer<'a> {
    /// `compilerOptions *core.CompilerOptions`
    compiler_options: &'a CompilerOptions,
    /// `parentNode *ast.Node`
    parent_node: Cell<Option<NodeId>>,
    /// `currentNode *ast.Node`
    current_node: Cell<Option<NodeId>>,
    /// `currentSourceFile *ast.Node`
    current_source_file: Cell<Option<NodeId>>,
    /// `currentScope *ast.Node` — SourceFile | Block | ModuleBlock | CaseBlock
    current_scope: Cell<Option<NodeId>>,
    /// `currentScopeFirstDeclarationsOfName map[string]*ast.Node`
    current_scope_first_declarations_of_name: RefCell<Option<FxHashMap<String, NodeId>>>,
    /// `currentEnum *ast.EnumDeclarationNode`
    current_enum: Cell<Option<NodeId>>,
    /// `currentNamespace *ast.ModuleDeclarationNode`
    current_namespace: Cell<Option<NodeId>>,
    /// `resolver binder.ReferenceResolver`
    resolver: Option<Rc<RefCell<dyn ReferenceResolver + 'a>>>,
    /// `emitResolver printer.EmitResolver`
    emit_resolver: Option<Rc<RefCell<dyn EmitResolver + 'a>>>,
    /// Bound `Symbol` arena for `ReferenceResolver` calls, threaded through
    /// `TransformOptions::symbols` — see the module PORT note.
    symbols: Option<&'a SymbolArena>,
    /// `Weak` self-reference used to build the destructuring-flattening
    /// assignment callback (`Box<CreateAssignmentCallback>` cannot capture
    /// `&self`).
    self_ref: RefCell<Weak<Self>>,
}

/// `getInnermostModuleDeclarationFromDottedModule` — walks the `.Body` chain
/// of a dotted `namespace a.b.c {}` to the innermost ModuleDeclaration.
/// `module_declaration` must be a `ModuleDeclaration`; returns its `NodeId`.
pub fn get_innermost_module_declaration_from_dotted_module(
    module_declaration: NodeId,
    nodes: &[Node],
) -> Option<NodeId> {
    let mut module_declaration = module_declaration;
    loop {
        let body = nodes[module_declaration]
            .as_module_declaration()
            .body_base
            .body;
        match body {
            Some(body) if nodes[body].kind == Kind::ModuleDeclaration => {
                module_declaration = body;
            }
            _ => return Some(module_declaration),
        }
    }
}

impl<'a> RuntimeSyntaxTransformer<'a> {
    /// `pushNode`
    fn push_node(&self, node: NodeId) -> Option<NodeId> {
        let grandparent_node = self.parent_node.get();
        self.parent_node.set(self.current_node.get());
        self.current_node.set(Some(node));
        grandparent_node
    }

    /// `popNode`
    fn pop_node(&self, grandparent_node: Option<NodeId>) {
        self.current_node.set(self.parent_node.get());
        self.parent_node.set(grandparent_node);
    }

    /// `pushScope`
    fn push_scope(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> (Option<NodeId>, Option<FxHashMap<String, NodeId>>) {
        let saved_current_scope = self.current_scope.get();
        // Only the scope-resetting kinds save/clear the declaration map —
        // Go's pushScope leaves it untouched for every other kind.
        let saved_first_declarations = match cx.nodes[node].kind {
            Kind::SourceFile => {
                self.current_scope.set(Some(node));
                self.current_source_file.set(Some(node));
                self.current_scope_first_declarations_of_name.take()
            }
            Kind::CaseBlock | Kind::ModuleBlock | Kind::Block => {
                self.current_scope.set(Some(node));
                self.current_scope_first_declarations_of_name.take()
            }
            Kind::FunctionDeclaration | Kind::ClassDeclaration | Kind::VariableStatement => {
                self.record_declaration_in_scope(cx, node);
                None
            }
            _ => None,
        };
        (saved_current_scope, saved_first_declarations)
    }

    /// `popScope`
    fn pop_scope(
        &self,
        saved_current_scope: Option<NodeId>,
        saved_first_declarations: Option<FxHashMap<String, NodeId>>,
    ) {
        if self.current_scope.get() != saved_current_scope {
            // only reset the first declaration for a name if we are exiting
            // the scope in which it was declared
            *self.current_scope_first_declarations_of_name.borrow_mut() = saved_first_declarations;
        }
        self.current_scope.set(saved_current_scope);
    }

    /// `tx.visit`
    fn visit<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let grandparent_node = self.push_node(node);
        let (saved_current_scope, saved_first_declarations) = self.push_scope(cx, node);

        let result = self.visit_inner(ec, v, cx, node);

        self.pop_scope(saved_current_scope, saved_first_declarations);
        self.pop_node(grandparent_node);
        result
    }

    /// The subtree-facts gate and `switch node.Kind` body of `tx.visit`
    /// (split out so `pop_node`/`pop_scope` always run — Go uses `defer`).
    fn visit_inner<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        let facts = cx.nodes[node].subtree_facts(cx.nodes);
        if facts & SubtreeFacts::CONTAINS_TYPE_SCRIPT == SubtreeFacts::NONE
            && ((self.current_namespace.get().is_none() && self.current_enum.get().is_none())
                || facts & SubtreeFacts::CONTAINS_IDENTIFIER == SubtreeFacts::NONE)
        {
            return Some(node);
        }

        match cx.nodes[node].kind {
            // TypeScript parameter property modifiers are elided.
            Kind::PublicKeyword
            | Kind::PrivateKeyword
            | Kind::ProtectedKeyword
            | Kind::ReadonlyKeyword
            | Kind::OverrideKeyword => None,

            Kind::EnumDeclaration => Some(self.visit_enum_declaration(ec, v, cx, node)),
            Kind::ModuleDeclaration => Some(self.visit_module_declaration(ec, v, cx, node)),
            Kind::ClassDeclaration => Some(self.visit_class_declaration(ec, v, cx, node)),
            Kind::ClassExpression => Some(self.visit_class_expression(ec, v, cx, node)),
            Kind::Constructor => Some(self.visit_constructor_declaration(ec, v, cx, node)),
            Kind::FunctionDeclaration => Some(self.visit_function_declaration(ec, v, cx, node)),
            Kind::VariableStatement => Some(self.visit_variable_statement(ec, v, cx, node)),

            Kind::ExportDeclaration | Kind::ImportDeclaration | Kind::ImportClause => {
                if self.current_namespace.get().is_some()
                    && self
                        .current_scope
                        .get()
                        .is_some_and(|s| cx.nodes[s].kind != Kind::Block)
                {
                    // do not emit ES6 imports and exports since they are
                    // illegal inside a namespace
                    None
                } else {
                    Some(visit_each_child(v, cx, node))
                }
            }

            Kind::ImportEqualsDeclaration => {
                let module_reference = cx.nodes[node]
                    .as_import_equals_declaration()
                    .module_reference;
                let is_external = module_reference
                    .is_some_and(|m| cx.nodes[m].kind == Kind::ExternalModuleReference);
                if self.current_namespace.get().is_some()
                    && self
                        .current_scope
                        .get()
                        .is_some_and(|s| cx.nodes[s].kind != Kind::Block)
                    && is_external
                {
                    // do not emit ES6 imports and exports since they are
                    // illegal inside a namespace
                    None
                } else if self.current_namespace.get().is_some()
                    && self
                        .current_scope
                        .get()
                        .is_some_and(|s| cx.nodes[s].kind == Kind::Block)
                    && !is_external
                {
                    // inside a block within a namespace, elide internal
                    // import aliases
                    None
                } else {
                    Some(self.visit_import_equals_declaration(ec, v, cx, node))
                }
            }

            Kind::Identifier => Some(self.visit_identifier(ec, cx, node)),
            Kind::ShorthandPropertyAssignment => {
                Some(self.visit_shorthand_property_assignment(ec, v, cx, node))
            }
            _ => Some(visit_each_child(v, cx, node)),
        }
    }

    /// `recordDeclarationInScope` — records that a declaration was emitted in
    /// the current scope, if it was the first declaration for the provided
    /// symbol.
    fn record_declaration_in_scope(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) {
        match cx.nodes[node].kind {
            Kind::VariableStatement => {
                let decl_list = cx.nodes[node].as_variable_statement().declaration_list;
                if let Some(decl_list) = decl_list {
                    self.record_declaration_in_scope(cx, decl_list);
                }
                return;
            }
            Kind::VariableDeclarationList => {
                let decls = cx.nodes[node]
                    .as_variable_declaration_list()
                    .declarations
                    .clone();
                if let Some(decls) = decls {
                    for decl in decls.nodes.iter().copied() {
                        self.record_declaration_in_scope(cx, decl);
                    }
                }
                return;
            }
            Kind::ArrayBindingPattern | Kind::ObjectBindingPattern => {
                let elements: Vec<NodeId> = cx.nodes[node]
                    .elements()
                    .map(|e| e.to_vec())
                    .unwrap_or_default();
                for element in elements {
                    self.record_declaration_in_scope(cx, element);
                }
                return;
            }
            _ => {}
        }
        if let Some(name) = cx.nodes[node].name() {
            if ast::is_identifier(&cx.nodes[name]) {
                if self
                    .current_scope_first_declarations_of_name
                    .borrow()
                    .is_none()
                {
                    *self.current_scope_first_declarations_of_name.borrow_mut() =
                        Some(FxHashMap::default());
                }
                let text = cx.nodes[name].text(cx.nodes).into_owned();
                self.current_scope_first_declarations_of_name
                    .borrow_mut()
                    .as_mut()
                    .unwrap()
                    .entry(text)
                    .or_insert(node);
            } else if ast::is_binding_pattern(&cx.nodes[name]) {
                self.record_declaration_in_scope(cx, name);
            }
        }
    }

    /// `isFirstDeclarationInScope` — determines whether a declaration is the
    /// first declaration with the same name emitted in the current scope.
    fn is_first_declaration_in_scope(&self, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        if let Some(name) = cx.nodes[node].name() {
            if ast::is_identifier(&cx.nodes[name]) {
                let text = cx.nodes[name].text(cx.nodes).into_owned();
                if let Some(first_declaration) = self
                    .current_scope_first_declarations_of_name
                    .borrow()
                    .as_ref()
                    .and_then(|m| m.get(&text).copied())
                {
                    return first_declaration == node;
                }
            }
        }
        false
    }

    /// `tx.isExportOfNamespace`
    fn is_export_of_namespace(&self, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        self.current_namespace.get().is_some()
            && (self.current_scope.get().is_none()
                || cx.nodes[self.current_scope.get().unwrap()].kind != Kind::Block)
            && cx.nodes[node]
                .modifier_flags()
                .intersects(ModifierFlags::EXPORT)
    }

    /// `tx.getExpressionForPropertyName` — gets an expression that represents
    /// a property name, such as `"foo"` for the identifier `foo`.
    /// `member` must be an `EnumMember`.
    fn get_expression_for_property_name<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        member: NodeId,
    ) -> Option<NodeId> {
        let name = cx.nodes[member].name();
        match name.map(|n| cx.nodes[n].kind) {
            Some(Kind::PrivateIdentifier) => {
                Some(ec.borrow_mut().factory.new_identifier(cx.nodes, ""))
            }
            Some(Kind::ComputedPropertyName) => {
                // enums don't support computed properties so we always
                // generate the 'expression' part of the name as-is.
                let expression = cx.nodes[name.unwrap()]
                    .as_computed_property_name()
                    .expression;
                v.visit_node(cx, expression)
            }
            Some(Kind::Identifier) | Some(Kind::StringLiteral) => {
                // !!! propagate token flags (will produce new diffs)
                let text = cx.nodes[name.unwrap()].text(cx.nodes).into_owned();
                Some(ec.borrow_mut().factory.new_string_literal(
                    cx.nodes,
                    &text,
                    ast::TokenFlags::NONE,
                ))
            }
            Some(Kind::NumericLiteral) => {
                let text = cx.nodes[name.unwrap()].text(cx.nodes).into_owned();
                Some(ec.borrow_mut().factory.new_numeric_literal(
                    cx.nodes,
                    &text,
                    ast::TokenFlags::NONE,
                ))
            }
            _ => name,
        }
    }

    /// `tx.getEnumQualifiedElement` — gets an expression like `E["A"]` that
    /// references an enum member.
    fn get_enum_qualified_element<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        enum_: NodeId,
        member: NodeId,
    ) -> NodeId {
        let ns_name = self.get_namespace_container_name(ec, cx, Some(enum_));
        let prop_name = self.get_expression_for_property_name(ec, v, cx, member);
        let prop = self.get_namespace_qualified_element(ec, cx, ns_name, prop_name);
        ec.borrow().add_emit_flags(
            prop,
            EmitFlags::NO_COMMENTS
                | EmitFlags::NO_NESTED_COMMENTS
                | EmitFlags::NO_SOURCE_MAP
                | EmitFlags::NO_NESTED_SOURCE_MAPS,
        );
        prop
    }

    /// `tx.getNamespaceContainerName` — gets an expression used to refer to a
    /// namespace or enum from within the body of its declaration.
    fn get_namespace_container_name(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> NodeId {
        ec.borrow_mut()
            .factory
            .new_generated_name_for_node(cx.nodes, node.expect("namespace container node"))
    }

    /// `tx.getNamespaceQualifiedProperty` — gets an expression used to refer
    /// to an export of a namespace or a member of an enum by property name.
    fn get_namespace_qualified_property(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        ns: NodeId,
        name: NodeId,
    ) -> NodeId {
        ec.borrow_mut().factory.get_namespace_member_name(
            cx.nodes,
            ns,
            name,
            &NameOptions {
                allow_source_maps: true,
                ..Default::default()
            },
        )
    }

    /// `tx.getNamespaceQualifiedElement` — gets an expression used to refer
    /// to an export of a namespace or a member of an enum by indexed access.
    fn get_namespace_qualified_element(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        ns: NodeId,
        expression: Option<NodeId>,
    ) -> NodeId {
        let qualified_name = ec.borrow_mut().factory.new_element_access_expression(
            cx.nodes,
            Some(ns),
            None, /* questionDotToken */
            expression,
            ast::NodeFlags::NONE,
        );
        if let Some(expression) = expression {
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, qualified_name, expression);
        }
        qualified_name
    }

    /// `tx.getExportQualifiedReferenceToDeclaration` — gets an expression
    /// used within the provided node's container for any exported
    /// references.
    fn get_export_qualified_reference_to_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if self.is_export_of_namespace(cx, node) {
            let ns = self.get_namespace_container_name(ec, cx, self.current_namespace.get());
            return ec
                .borrow_mut()
                .factory
                .get_external_module_or_namespace_export_name(
                    cx.nodes,
                    Some(ns),
                    node,
                    false, /* allowComments */
                    true,  /* allowSourceMaps */
                );
        }
        ec.borrow_mut().factory.get_declaration_name_ex(
            cx.nodes,
            Some(node),
            &NameOptions {
                allow_source_maps: true,
                ..Default::default()
            },
        )
    }

    /// `tx.addVarForDeclaration`
    fn add_var_for_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        node: NodeId,
    ) -> (Vec<NodeId>, bool) {
        self.record_declaration_in_scope(cx, node);
        if !self.is_first_declaration_in_scope(cx, node) {
            return (statements, false);
        }

        // var name;
        let name = ec.borrow_mut().factory.get_local_name_ex(
            cx.nodes,
            Some(node),
            &AssignedNameOptions {
                allow_source_maps: true,
                ..Default::default()
            },
        );
        let var_decl = ec.borrow_mut().factory.new_variable_declaration(
            cx.nodes,
            Some(name),
            None,
            None,
            None,
        );
        let var_flags = if self.current_scope.get() == self.current_source_file.get() {
            NodeFlags::NONE
        } else {
            NodeFlags::LET
        };
        let var_decls_list = ec.borrow_mut().factory.new_node_list([var_decl]);
        let var_decls = ec.borrow_mut().factory.new_variable_declaration_list(
            cx.nodes,
            Some(var_decls_list),
            var_flags,
        );
        // Replicate modifierVisitor: strip decorators, TypeScript modifiers,
        // and export when in namespace.
        let mut modifier_mask = !(ModifierFlags::TYPE_SCRIPT_MODIFIER | ModifierFlags::DECORATOR);
        if self.current_namespace.get().is_some() {
            modifier_mask &= !ModifierFlags::EXPORT;
        }
        let modifiers = extract_modifiers(
            Some(ec),
            cx.nodes,
            cx.nodes[node].modifiers().cloned(),
            modifier_mask,
        );
        let var_statement =
            ec.borrow_mut()
                .factory
                .new_variable_statement(cx.nodes, modifiers, Some(var_decls));

        ec.borrow().set_original(var_decl, node);
        // !!! synthetic comments
        ec.borrow().set_original(var_statement, node);

        // Adjust the source map emit to match the old emitter.
        if ast::is_enum_declaration(&cx.nodes[node]) {
            ec.borrow()
                .set_source_map_range(var_decls, cx.nodes[node].loc);
        } else {
            ec.borrow()
                .set_source_map_range(var_statement, cx.nodes[node].loc);
        }

        // Trailing comments for enum declaration should be emitted after the
        // function closure instead of the variable statement:
        //
        //     /** Leading comment*/
        //     enum E {
        //         A
        //     } // trailing comment
        //
        // Should emit:
        //
        //     /** Leading comment*/
        //     var E;
        //     (function (E) {
        //         E[E["A"] = 0] = "A";
        //     })(E || (E = {})); // trailing comment
        //
        ec.borrow()
            .set_comment_range(var_statement, cx.nodes[node].loc);
        ec.borrow()
            .add_emit_flags(var_statement, EmitFlags::NO_TRAILING_COMMENTS);
        statements.push(var_statement);

        (statements, true)
    }

    /// `tx.visitEnumDeclaration`
    fn visit_enum_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if !self.should_emit_enum_declaration(cx, node) {
            return ec.borrow_mut().new_not_emitted_statement(cx.nodes, node);
        }

        // If needed, we should emit a variable declaration for the enum:
        //  var name;
        let (statements, var_added) = self.add_var_for_declaration(ec, cx, Vec::new(), node);

        // If we emit a leading variable declaration, we should not emit
        // leading comments for the enum body, but we should still emit the
        // comments if we are emitting to a System module.
        let mut emit_flags = EmitFlags::NONE;
        if var_added
            && (self.compiler_options.get_emit_module_kind() != ModuleKind::System
                || self.current_scope.get() != self.current_source_file.get())
        {
            emit_flags |= EmitFlags::NO_LEADING_COMMENTS;
        }

        //  x || (x = {})
        //  exports.x || (exports.x = {})
        let lhs = self.get_export_qualified_reference_to_declaration(ec, cx, node);
        let rhs_target = self.get_export_qualified_reference_to_declaration(ec, cx, node);
        let empty_list = ec.borrow_mut().factory.new_node_list([]);
        let empty_object = ec.borrow_mut().factory.new_object_literal_expression(
            cx.nodes,
            Some(empty_list),
            false,
        );
        let rhs =
            ec.borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, rhs_target, empty_object);
        let mut enum_arg = ec
            .borrow_mut()
            .factory
            .new_logical_or_expression(cx.nodes, lhs, rhs);

        if self.is_export_of_namespace(cx, node) {
            // `local_name` is the expression used within this node's
            // containing scope for any local references.
            let local_name = ec.borrow_mut().factory.get_local_name_ex(
                cx.nodes,
                Some(node),
                &AssignedNameOptions {
                    allow_source_maps: true,
                    ..Default::default()
                },
            );

            //  x = (exports.x || (exports.x = {}))
            enum_arg = ec
                .borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, local_name, enum_arg);
        }

        // (function (name) { ... })(name || (name = {}))
        let enum_param_name = ec
            .borrow_mut()
            .factory
            .new_generated_name_for_node(cx.nodes, node);
        ec.borrow().set_source_map_range(
            enum_param_name,
            cx.nodes[node]
                .name()
                .map(|n| cx.nodes[n].loc)
                .unwrap_or_default(),
        );

        let enum_param = ec.borrow_mut().factory.new_parameter_declaration(
            cx.nodes,
            None,
            None,
            Some(enum_param_name),
            None,
            None,
            None,
        );
        let enum_body = self.transform_enum_body(ec, v, cx, node);
        let enum_params = ec.borrow_mut().factory.new_node_list([enum_param]);
        let enum_func = ec.borrow_mut().factory.new_function_expression(
            cx.nodes,
            None,
            None,
            None,
            None,
            Some(enum_params),
            None,
            None,
            Some(enum_body),
        );
        let enum_func_paren = ec
            .borrow_mut()
            .factory
            .new_parenthesized_expression(cx.nodes, Some(enum_func));
        let enum_args = ec.borrow_mut().factory.new_node_list([enum_arg]);
        let enum_call = ec.borrow_mut().factory.new_call_expression(
            cx.nodes,
            Some(enum_func_paren),
            None,
            None,
            Some(enum_args),
            NodeFlags::NONE,
        );
        let enum_statement = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(enum_call));
        ec.borrow().set_original(enum_statement, node);
        ec.borrow()
            .assign_comment_and_source_map_ranges(cx.nodes, enum_statement, node);
        ec.borrow().add_emit_flags(enum_statement, emit_flags);
        let mut statements = statements;
        statements.push(enum_statement);
        ec.borrow_mut()
            .factory
            .new_syntax_list(cx.nodes, &statements)
    }

    /// `tx.transformEnumBody` — transforms the body of an enum declaration.
    /// Returns a `Block` node.
    fn transform_enum_body<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let saved_current_enum = self.current_enum.get();
        self.current_enum.set(Some(node));

        // visit the children of `node` in advance to capture any references
        // to enum members.
        let node = v.visit_each_child(cx, node).unwrap_or(node);

        let members = cx.nodes[node].as_enum_declaration().members.clone();
        let member_ids: Vec<NodeId> = members
            .as_ref()
            .map(|m| m.nodes.to_vec())
            .unwrap_or_default();
        let members_loc = members.map(|m| m.loc).unwrap_or_default();

        let mut statements: Vec<NodeId> = Vec::new();
        for i in 0..member_ids.len() {
            //  E[E["A"] = 0] = "A";
            statements = self.transform_enum_member(ec, v, cx, statements, node, i);
        }

        let mut statement_list = ec.borrow_mut().factory.new_node_list(statements);
        statement_list.loc = members_loc;

        self.current_enum.set(saved_current_enum);
        ec.borrow_mut()
            .factory
            .new_block(cx.nodes, Some(statement_list), true)
    }

    /// `tx.transformEnumMember` — transforms an enum member into a statement.
    /// It is expected that `enum` has already been visited.
    fn transform_enum_member<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        mut statements: Vec<NodeId>,
        enum_: NodeId,
        index: usize,
    ) -> Vec<NodeId> {
        let member_node = cx.nodes[enum_]
            .as_enum_declaration()
            .members
            .as_ref()
            .unwrap()
            .nodes[index];

        let saved_parent = self.parent_node.get();
        self.parent_node.set(self.current_node.get());
        self.current_node.set(Some(member_node));

        //  E[E["A"] = x] = "A";
        //             ^
        // NOTE: `member.initializer` was already visited by
        // `transform_enum_body`'s `visit_each_child`.
        let mut expression = cx.nodes[member_node].as_enum_member().initializer;

        let use_explicit_reverse_mapping;

        let parse_node = ec.borrow().parse_node(cx.nodes, member_node);
        // PORT: `parseNode` may be `None` for synthesized members; Go passes
        // the nil through to `GetEnumMemberValue`, which no Rust
        // `EmitResolver` signature can express — fall back to the member
        // itself in that case.
        let result = self
            .emit_resolver
            .as_ref()
            .expect("RuntimeSyntaxTransformer requires an emit resolver")
            .borrow()
            .get_enum_member_value(parse_node.unwrap_or(member_node), cx.nodes);
        match &result.value {
            Some(Value::Number(n)) => {
                let n = *n;
                expression = coalesce(
                    constant_expression(&Value::Number(n), &mut ec.borrow_mut().factory, cx.nodes),
                    expression,
                );
                use_explicit_reverse_mapping = true;
            }
            Some(Value::String(s)) => {
                let s = s.clone();
                expression = coalesce(
                    constant_expression(&Value::String(s), &mut ec.borrow_mut().factory, cx.nodes),
                    expression,
                );
                use_explicit_reverse_mapping = false;
            }
            _ => {
                if expression.is_none() {
                    expression = Some(ec.borrow_mut().factory.new_void_zero_expression(cx.nodes));
                }
                use_explicit_reverse_mapping = !result.is_syntactically_string;
            }
        }

        // Define the enum member property:
        //  E[E["A"] = 0] = "A";
        //    ^^^^^^^^--_____
        let target = self.get_enum_qualified_element(ec, v, cx, enum_, member_node);
        let mut expression = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            target,
            expression.expect("enum member value expression"),
        );

        if use_explicit_reverse_mapping {
            //  E[E["A"] = 0] = "A";
            //  ^^--------------^^^^^
            let ns_name = self.get_namespace_container_name(ec, cx, Some(enum_));
            let inner = ec.borrow_mut().factory.new_element_access_expression(
                cx.nodes,
                Some(ns_name),
                None, /* questionDotToken */
                Some(expression),
                ast::NodeFlags::NONE,
            );
            let prop_name = self.get_expression_for_property_name(ec, v, cx, member_node);
            expression = ec.borrow_mut().factory.new_assignment_expression(
                cx.nodes,
                inner,
                prop_name.expect("enum member property name expression"),
            );
        }

        let member_statement = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(expression));
        ec.borrow()
            .assign_comment_and_source_map_ranges(cx.nodes, expression, member_node);
        ec.borrow()
            .assign_comment_and_source_map_ranges(cx.nodes, member_statement, member_node);
        statements.push(member_statement);

        self.current_node.set(self.parent_node.get());
        self.parent_node.set(saved_parent);
        statements
    }
    /// `tx.visitModuleDeclaration`
    fn visit_module_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if !self.should_emit_module_declaration(ec, cx, node) {
            return ec.borrow_mut().new_not_emitted_statement(cx.nodes, node);
        }

        // If needed, we should emit a variable declaration for the module:
        //  var name;
        let (statements, var_added) = self.add_var_for_declaration(ec, cx, Vec::new(), node);

        // If we emit a leading variable declaration, we should not emit
        // leading comments for the module body, but we should still emit the
        // comments if we are emitting to a System module.
        let mut emit_flags = EmitFlags::NONE;
        if var_added
            && (self.compiler_options.get_emit_module_kind() != ModuleKind::System
                || self.current_scope.get() != self.current_source_file.get())
        {
            emit_flags |= EmitFlags::NO_LEADING_COMMENTS;
        }

        //  x || (x = {})
        //  exports.x || (exports.x = {})
        let lhs = self.get_export_qualified_reference_to_declaration(ec, cx, node);
        let rhs_target = self.get_export_qualified_reference_to_declaration(ec, cx, node);
        let empty_list = ec.borrow_mut().factory.new_node_list([]);
        let empty_object = ec.borrow_mut().factory.new_object_literal_expression(
            cx.nodes,
            Some(empty_list),
            false,
        );
        let rhs =
            ec.borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, rhs_target, empty_object);
        let mut module_arg = ec
            .borrow_mut()
            .factory
            .new_logical_or_expression(cx.nodes, lhs, rhs);

        if self.is_export_of_namespace(cx, node) {
            // `local_name` is the expression used within this node's
            // containing scope for any local references.
            let local_name = ec.borrow_mut().factory.get_local_name_ex(
                cx.nodes,
                Some(node),
                &AssignedNameOptions {
                    allow_source_maps: true,
                    ..Default::default()
                },
            );

            //  x = (exports.x || (exports.x = {}))
            module_arg = ec
                .borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, local_name, module_arg);
        }

        // (function (name) { ... })(name || (name = {}))
        let module_param_name = ec
            .borrow_mut()
            .factory
            .new_generated_name_for_node(cx.nodes, node);
        ec.borrow().set_source_map_range(
            module_param_name,
            cx.nodes[node]
                .name()
                .map(|n| cx.nodes[n].loc)
                .unwrap_or_default(),
        );

        let module_param = ec.borrow_mut().factory.new_parameter_declaration(
            cx.nodes,
            None,
            None,
            Some(module_param_name),
            None,
            None,
            None,
        );
        let container_name = self.get_namespace_container_name(ec, cx, Some(node));
        let module_body = self.transform_module_body(ec, v, cx, node, container_name);
        let module_params = ec.borrow_mut().factory.new_node_list([module_param]);
        let module_func = ec.borrow_mut().factory.new_function_expression(
            cx.nodes,
            None,
            None,
            None,
            None,
            Some(module_params),
            None,
            None,
            Some(module_body),
        );
        let module_func_paren = ec
            .borrow_mut()
            .factory
            .new_parenthesized_expression(cx.nodes, Some(module_func));
        let module_args = ec.borrow_mut().factory.new_node_list([module_arg]);
        let module_call = ec.borrow_mut().factory.new_call_expression(
            cx.nodes,
            Some(module_func_paren),
            None,
            None,
            Some(module_args),
            NodeFlags::NONE,
        );
        let module_statement = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(module_call));
        ec.borrow().set_original(module_statement, node);
        ec.borrow()
            .assign_comment_and_source_map_ranges(cx.nodes, module_statement, node);
        ec.borrow().add_emit_flags(module_statement, emit_flags);
        let mut statements = statements;
        statements.push(module_statement);
        ec.borrow_mut()
            .factory
            .new_syntax_list(cx.nodes, &statements)
    }

    /// `tx.transformModuleBody`
    fn transform_module_body<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        _namespace_local_name: NodeId,
    ) -> NodeId {
        let saved_current_namespace = self.current_namespace.get();
        let saved_current_scope = self.current_scope.get();
        let saved_first_declarations = self.current_scope_first_declarations_of_name.take();

        self.current_namespace.set(Some(node));
        // currentScopeFirstDeclarationsOfName := nil (already taken)

        let mut statements: Vec<NodeId> = Vec::new();
        ec.borrow_mut().start_variable_environment();

        let mut statements_location = TextRange::default();
        let mut block_location = TextRange::default();
        let body = cx.nodes[node].as_module_declaration().body_base.body;
        let mut node = node;
        if let Some(body) = body {
            if cx.nodes[body].kind == Kind::ModuleBlock {
                // visit the children of `node` in advance to capture any
                // references to namespace members
                node = v.visit_each_child(cx, node).unwrap_or(node);
                let body = cx.nodes[node].as_module_declaration().body_base.body;
                if let Some(body) = body {
                    let body_block = cx.nodes[body].as_module_block();
                    let stmts = body_block.statements.clone();
                    statements = stmts.as_ref().map(|s| s.nodes.to_vec()).unwrap_or_default();
                    statements_location = stmts.map(|s| s.loc).unwrap_or_default();
                    block_location = cx.nodes[body].loc;
                }
            } else {
                // node.Body.Kind == ast.KindModuleDeclaration
                // !!! Strada didn't do this; why?
                // tx.currentScope = node.AsNode()
                statements = v.visit_slice(cx, &[body]).unwrap_or_else(|| vec![body]);
                let innermost = get_innermost_module_declaration_from_dotted_module(node, cx.nodes)
                    .unwrap_or(node);
                let module_block = cx.nodes[innermost].as_module_declaration().body_base.body;
                statements_location = module_block
                    .and_then(|mb| {
                        cx.nodes[mb]
                            .as_module_block()
                            .statements
                            .as_ref()
                            .map(|s| s.loc)
                    })
                    .unwrap_or_default()
                    .with_pos(-1);
            }
        }

        self.current_namespace.set(saved_current_namespace);
        self.current_scope.set(saved_current_scope);
        *self.current_scope_first_declarations_of_name.borrow_mut() = saved_first_declarations;

        statements = ec
            .borrow_mut()
            .end_and_merge_variable_environment(cx.nodes, &statements);
        let mut statement_list = ec.borrow_mut().factory.new_node_list(statements);
        statement_list.loc = statements_location;
        let block = ec
            .borrow_mut()
            .factory
            .new_block(cx.nodes, Some(statement_list), true);
        cx.nodes[block].loc = block_location;

        // We only want to emit comment on the namespace which contains block
        // body itself, not the containing namespaces.
        let body_is_module_block = cx.nodes[node]
            .as_module_declaration()
            .body_base
            .body
            .is_some_and(|b| cx.nodes[b].kind == Kind::ModuleBlock);
        if !body_is_module_block {
            ec.borrow().add_emit_flags(block, EmitFlags::NO_COMMENTS);
        }
        block
    }

    /// `tx.visitImportEqualsDeclaration`
    fn visit_import_equals_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let module_reference = cx.nodes[node]
            .as_import_equals_declaration()
            .module_reference;
        if module_reference.is_some_and(|m| cx.nodes[m].kind == Kind::ExternalModuleReference) {
            return visit_each_child(v, cx, node);
        }

        let module_reference_expr = ec.borrow_mut().factory.create_expression_from_entity_name(
            cx.nodes,
            module_reference.expect("import equals has no module reference"),
        );
        ec.borrow().set_emit_flags(
            module_reference_expr,
            EmitFlags::NO_COMMENTS | EmitFlags::NO_NESTED_COMMENTS,
        );
        if !self.is_export_of_namespace(cx, node) {
            //  export var ${name} = ${moduleReference};
            //  var ${name} = ${moduleReference};
            let var_decl = ec.borrow_mut().factory.new_variable_declaration(
                cx.nodes,
                cx.nodes[node].name(),
                None,
                None,
                Some(module_reference_expr),
            );
            ec.borrow().set_original(var_decl, node);
            let var_decls_list = ec.borrow_mut().factory.new_node_list([var_decl]);
            let var_list = ec.borrow_mut().factory.new_variable_declaration_list(
                cx.nodes,
                Some(var_decls_list),
                NodeFlags::NONE,
            );
            let var_modifiers = extract_modifiers(
                Some(ec),
                cx.nodes,
                cx.nodes[node].modifiers().cloned(),
                ModifierFlags::EXPORT,
            );
            let var_statement = ec.borrow_mut().factory.new_variable_statement(
                cx.nodes,
                var_modifiers,
                Some(var_list),
            );
            ec.borrow().set_original(var_statement, node);
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, var_statement, node);
            var_statement
        } else {
            // exports.${name} = ${moduleReference};
            let statement = self.create_export_statement(
                ec,
                cx,
                cx.nodes[node].name().expect("import equals has no name"),
                Some(module_reference_expr),
                cx.nodes[node].loc,
                cx.nodes[node].loc,
                node,
            );
            cx.nodes[statement].loc = cx.nodes[node].loc;
            statement
        }
    }

    /// `tx.visitVariableStatement`
    fn visit_variable_statement<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if self.is_export_of_namespace(cx, node) {
            let mut expressions: Vec<NodeId> = Vec::new();
            let decl_ids: Vec<NodeId> = cx.nodes[node]
                .as_variable_statement()
                .declaration_list
                .and_then(|dl| {
                    cx.nodes[dl]
                        .as_variable_declaration_list()
                        .declarations
                        .as_ref()
                        .map(|d| d.nodes.to_vec())
                })
                .unwrap_or_default();
            for declaration in decl_ids {
                if cx.nodes[declaration]
                    .as_variable_declaration()
                    .initializer
                    .is_none()
                {
                    continue;
                }
                let name = cx.nodes[declaration].as_variable_declaration().name;
                if name.is_some_and(|n| ast::is_binding_pattern(&cx.nodes[n])) {
                    let visited = v.visit_node(cx, Some(declaration));
                    if let Some(visited) = visited {
                        // `tx.createNamespaceExportExpression` — the visitor
                        // pair arrives through the callback so no ec borrow
                        // is held across nested visits.
                        let tx2 = self
                            .self_ref
                            .borrow()
                            .upgrade()
                            .expect("transformer state dropped");
                        let ec2 = ec.clone();
                        let adapter = tx_adapter(v, ec);
                        let cb = move |_v2: &NodeVisitor<'_>,
                                       cx2: &mut VisitorCx<'_, '_>,
                                       name: NodeId,
                                       value: Option<NodeId>,
                                       location: &TextRange| {
                            tx2.create_namespace_export_expression(&ec2, cx2, name, value, location)
                        };
                        let expression = flatten_destructuring_assignment(
                            &adapter,
                            cx,
                            visited,
                            false,
                            FlattenLevel::All,
                            Some(Box::new(cb)),
                        );
                        if let Some(expression) = expression {
                            expressions.push(expression);
                        }
                    }
                } else {
                    let expression = convert_variable_declaration_to_assignment_expression(
                        &mut ec.borrow_mut(),
                        cx.nodes,
                        declaration,
                    );
                    if let Some(expression) = expression {
                        expressions.push(expression);
                    }
                }
            }
            if expressions.is_empty() {
                return ec.borrow_mut().new_not_emitted_statement(cx.nodes, node);
            }
            let expression = ec
                .borrow_mut()
                .factory
                .inline_expressions(cx.nodes, &expressions);
            let mut statement = ec
                .borrow_mut()
                .factory
                .new_expression_statement(cx.nodes, expression);
            ec.borrow().set_original(statement, node);
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, statement, node);

            // re-visit as the new node
            let saved_current = self.current_node.get();
            self.current_node.set(Some(statement));
            statement = v.visit_each_child(cx, statement).unwrap_or(statement);
            self.current_node.set(saved_current);
            return statement;
        }
        visit_each_child(v, cx, node)
    }

    /// `tx.createNamespaceExportExpression` — creates an assignment to a
    /// namespace member for use as a callback during destructuring
    /// flattening. Invoked via [`RuntimeSyntaxExportCb`].
    fn create_namespace_export_expression(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        export_name: NodeId,
        export_value: Option<NodeId>,
        location: &TextRange,
    ) -> NodeId {
        let ns = self.get_namespace_container_name(ec, cx, self.current_namespace.get());
        let member_name = self.get_namespace_qualified_property(ec, cx, ns, export_name);
        let expression = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            member_name,
            export_value.expect("namespace export has no value"),
        );
        cx.nodes[expression].loc = *location;
        expression
    }

    /// `tx.visitFunctionDeclaration`
    fn visit_function_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if self.is_export_of_namespace(cx, node) {
            let modifiers = extract_modifiers(
                Some(ec),
                cx.nodes,
                cx.nodes[node].modifiers().cloned(),
                !ModifierFlags::EXPORT,
            );
            let modifiers = v.visit_modifiers(cx, modifiers);
            let asterisk_token = cx.nodes[node]
                .as_function_declaration()
                .function_like_with_body_base
                .body_base
                .asterisk_token;
            let name = v.visit_node(cx, cx.nodes[node].name());
            let parameters = v.visit_nodes(cx, cx.nodes[node].parameter_list().cloned());
            let body = v.visit_node(cx, cx.nodes[node].body());
            let updated = ec.borrow_mut().factory.update_function_declaration(
                cx.nodes,
                node,
                modifiers,
                asterisk_token,
                name,
                None, /* type_parameters */
                parameters,
                None, /* type_node */
                None, /* full_signature */
                body,
            );
            let updated = updated.unwrap_or(node);
            let export = self.create_export_statement_for_declaration(ec, cx, node);
            return ec
                .borrow_mut()
                .factory
                .new_syntax_list(cx.nodes, &[updated, export]);
        }
        visit_each_child(v, cx, node)
    }

    /// `tx.getParameterProperties`
    fn get_parameter_properties(
        &self,
        cx: &VisitorCx<'_, '_>,
        constructor: Option<NodeId>,
    ) -> Vec<NodeId> {
        let mut parameter_properties = Vec::new();
        if let Some(constructor) = constructor {
            for &parameter in cx.nodes[constructor].parameters().unwrap_or(&[]) {
                if ast::is_parameter_property_declaration(
                    &cx.nodes[parameter],
                    &cx.nodes[constructor],
                ) {
                    parameter_properties.push(parameter);
                }
            }
        }
        parameter_properties
    }

    /// The parameter-property member synthesis shared by
    /// `visitClassDeclaration` and `visitClassExpression`.
    fn synthesize_parameter_property_members(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        parameter_properties: &[NodeId],
        mut members: Option<NodeList>,
    ) -> Option<NodeList> {
        if parameter_properties.is_empty() {
            return members;
        }
        let mut new_members: Vec<NodeId> = Vec::new();
        for &parameter in parameter_properties {
            let name = cx.nodes[parameter].name();
            if name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
                let cloned_name = ec.borrow_mut().factory.clone_node(cx.nodes, name.unwrap());
                let parameter_property = ec.borrow_mut().factory.new_property_declaration(
                    cx.nodes,
                    None, /* modifiers */
                    Some(cloned_name),
                    None, /* question_or_exclamation_token */
                    None, /* type */
                    None, /* initializer */
                );
                ec.borrow().set_original(parameter_property, parameter);
                new_members.push(parameter_property);
            }
        }
        if !new_members.is_empty() {
            if let Some(members) = members.as_mut() {
                new_members.extend_from_slice(&members.nodes);
                members.nodes = new_members.into_boxed_slice();
                members.loc = cx.nodes[node]
                    .member_list()
                    .map(|m| m.loc)
                    .unwrap_or_default();
            }
        }
        members
    }

    /// `tx.visitClassDeclaration`
    fn visit_class_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let exported = self.is_export_of_namespace(cx, node);
        let modifiers = if exported {
            let extracted = extract_modifiers(
                Some(ec),
                cx.nodes,
                cx.nodes[node].modifiers().cloned(),
                !ModifierFlags::EXPORT_DEFAULT,
            );
            v.visit_modifiers(cx, extracted)
        } else {
            v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned())
        };

        let mut name = v.visit_node(cx, cx.nodes[node].name());
        if name.is_none()
            && (exported
                || super::legacydecorators::child_is_decorated_no_parent(
                    self.compiler_options.experimental_decorators.is_true(),
                    node,
                    cx.nodes,
                ))
        {
            name = Some(
                ec.borrow_mut()
                    .factory
                    .new_generated_name_for_node(cx.nodes, node),
            );
        }
        let heritage_clauses = v.visit_nodes(
            cx,
            cx.nodes[node]
                .as_class_declaration()
                .class_like_base
                .heritage_clauses
                .clone(),
        );
        let members = v.visit_nodes(cx, cx.nodes[node].member_list().cloned());
        let constructor = cx.nodes[node]
            .member_list()
            .and_then(|m| find(&m.nodes, |m| ast::is_constructor_declaration(&cx.nodes[*m])));
        let parameter_properties = self.get_parameter_properties(cx, constructor);
        let members = self.synthesize_parameter_property_members(
            ec,
            cx,
            node,
            &parameter_properties,
            members,
        );

        let updated = ec
            .borrow_mut()
            .factory
            .update_class_declaration(
                cx.nodes,
                node,
                modifiers,
                name,
                None, /* type_parameters */
                heritage_clauses,
                members,
            )
            .unwrap_or(node);
        if exported {
            let export = self.create_export_statement_for_declaration(ec, cx, node);
            return ec
                .borrow_mut()
                .factory
                .new_syntax_list(cx.nodes, &[updated, export]);
        }
        updated
    }

    /// `tx.visitClassExpression`
    fn visit_class_expression<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let extracted = extract_modifiers(
            Some(ec),
            cx.nodes,
            cx.nodes[node].modifiers().cloned(),
            !ModifierFlags::EXPORT_DEFAULT,
        );
        let modifiers = v.visit_modifiers(cx, extracted);
        let name = v.visit_node(cx, cx.nodes[node].name());
        let heritage_clauses = v.visit_nodes(
            cx,
            cx.nodes[node]
                .as_class_expression()
                .class_like_base
                .heritage_clauses
                .clone(),
        );
        let members = v.visit_nodes(cx, cx.nodes[node].member_list().cloned());
        let constructor = cx.nodes[node]
            .member_list()
            .and_then(|m| find(&m.nodes, |m| ast::is_constructor_declaration(&cx.nodes[*m])));
        let parameter_properties = self.get_parameter_properties(cx, constructor);
        let members = self.synthesize_parameter_property_members(
            ec,
            cx,
            node,
            &parameter_properties,
            members,
        );

        ec.borrow_mut()
            .factory
            .update_class_expression(
                cx.nodes,
                node,
                modifiers,
                name,
                None, /* type_parameters */
                heritage_clauses,
                members,
            )
            .unwrap_or(node)
    }

    /// `tx.visitConstructorDeclaration`
    fn visit_constructor_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let parameters = crate::estransforms::ec_visit_parameters(
            v,
            cx,
            cx.nodes[node].parameter_list().cloned(),
        );
        let body = self.visit_constructor_body(ec, v, cx, cx.nodes[node].body(), node);
        ec.borrow_mut()
            .factory
            .update_constructor_declaration(
                cx.nodes, node, modifiers, None, /* type_parameters */
                parameters, None, /* type_node */
                None, /* full_signature */
                body,
            )
            .unwrap_or(node)
    }

    /// `tx.visitConstructorBody` — `body` must be a `Block` when `Some`.
    fn visit_constructor_body<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        body: Option<NodeId>,
        constructor: NodeId,
    ) -> Option<NodeId> {
        let parameter_properties = self.get_parameter_properties(cx, Some(constructor));
        if parameter_properties.is_empty() {
            return crate::estransforms::ec_visit_function_body(v, cx, body);
        }
        let body = body?;

        let grandparent_of_body = self.push_node(body);
        let (saved_current_scope, saved_first_declarations) = self.push_scope(cx, body);

        ec.borrow_mut().start_variable_environment();
        let body_statements: Vec<NodeId> = cx.nodes[body]
            .statements()
            .map(|s| s.to_vec())
            .unwrap_or_default();
        let (prologue, rest): (Vec<NodeId>, Vec<NodeId>) = {
            let (prologue, rest) = ec
                .borrow()
                .factory
                .split_standard_prologue(cx.nodes, &body_statements);
            (prologue.to_vec(), rest.to_vec())
        };
        let mut statements = prologue;

        // Transform parameters into property assignments. Transforms this:
        //
        //  constructor (public x, public y) {
        //  }
        //
        // Into this:
        //
        //  constructor (x, y) {
        //      this.x = x;
        //      this.y = y;
        //  }
        //
        let mut parameter_property_assignments: Vec<NodeId> = Vec::new();
        for &parameter in &parameter_properties {
            let name = cx.nodes[parameter].name();
            if name.is_some_and(|n| ast::is_identifier(&cx.nodes[n])) {
                let name = name.unwrap();
                let property_name = ec.borrow_mut().factory.clone_node(cx.nodes, name);
                // PORT: `.Parent` is set so the clone prints back using the
                // original file's text (mirrors the Go `nolint` comment).
                cx.nodes[property_name].parent = cx.nodes[name].parent;
                ec.borrow().add_emit_flags(
                    property_name,
                    EmitFlags::NO_COMMENTS | EmitFlags::NO_SOURCE_MAP,
                );

                let local_name = ec.borrow_mut().factory.clone_node(cx.nodes, name);
                cx.nodes[local_name].parent = cx.nodes[name].parent;
                ec.borrow()
                    .add_emit_flags(local_name, EmitFlags::NO_COMMENTS);

                let this_expr = ec.borrow_mut().factory.new_this_expression(cx.nodes);
                let prop_access = ec.borrow_mut().factory.new_property_access_expression(
                    cx.nodes,
                    Some(this_expr),
                    None, /* question_dot_token */
                    Some(property_name),
                    NodeFlags::NONE,
                );
                let assignment = ec.borrow_mut().factory.new_assignment_expression(
                    cx.nodes,
                    prop_access,
                    local_name,
                );
                let parameter_property = ec
                    .borrow_mut()
                    .factory
                    .new_expression_statement(cx.nodes, Some(assignment));
                ec.borrow().set_original(parameter_property, parameter);
                ec.borrow()
                    .add_emit_flags(parameter_property, EmitFlags::START_ON_NEW_LINE);
                parameter_property_assignments.push(parameter_property);
            }
        }

        let super_path = find_super_statement_index_path(cx.nodes, &rest, 0);

        if !super_path.is_empty() {
            statements.extend(self.transform_constructor_body_worker(
                ec,
                v,
                cx,
                &rest,
                &super_path,
                &parameter_property_assignments,
            ));
        } else {
            statements.extend(parameter_property_assignments.iter().copied());
            statements.extend(
                v.visit_slice(cx, &rest).unwrap_or_else(|| rest.to_vec()),
            );
        }

        let statements = ec
            .borrow_mut()
            .end_and_merge_variable_environment(cx.nodes, &statements);
        let mut statement_list = ec.borrow_mut().factory.new_node_list(statements);
        statement_list.loc = cx.nodes[body]
            .as_block()
            .statements
            .as_ref()
            .map(|s| s.loc)
            .unwrap_or_default();

        self.pop_scope(saved_current_scope, saved_first_declarations);
        self.pop_node(grandparent_of_body);
        let updated = ec
            .borrow_mut()
            .factory
            .new_block(cx.nodes, Some(statement_list), true);
        ec.borrow().set_original(updated, body);
        cx.nodes[updated].loc = cx.nodes[body].loc;
        Some(updated)
    }

    /// `tx.transformConstructorBodyWorker`
    fn transform_constructor_body_worker<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        statements_in: &[NodeId],
        super_path: &[i32],
        initializer_statements: &[NodeId],
    ) -> Vec<NodeId> {
        let mut statements_out: Vec<NodeId> = Vec::new();
        let super_statement_index = super_path[0] as usize;
        let super_statement = statements_in[super_statement_index];

        // visit up to the statement containing `super`
        statements_out.extend(
            v.visit_slice(cx, &statements_in[..super_statement_index])
                .unwrap_or_else(|| statements_in[..super_statement_index].to_vec()),
        );

        // if the statement containing `super` is a `try` statement, transform
        // the body of the `try` block
        if ast::is_try_statement(&cx.nodes[super_statement]) {
            let try_block = cx.nodes[super_statement].as_try_statement().try_block;

            // keep track of hierarchy as we descend
            let grandparent_of_try_statement = self.push_node(super_statement);
            let grandparent_of_try_block = try_block.map(|tb| self.push_node(tb));
            let (saved_current_scope, saved_first_declarations) = match try_block {
                Some(tb) => self.push_scope(cx, tb),
                None => (None, None),
            };

            // visit the `try` block
            let try_block_statements: Vec<NodeId> = try_block
                .and_then(|tb| cx.nodes[tb].statements().map(|s| s.to_vec()))
                .unwrap_or_default();
            let try_block_statements = self.transform_constructor_body_worker(
                ec,
                v,
                cx,
                &try_block_statements,
                &super_path[1..],
                initializer_statements,
            );

            // restore hierarchy as we ascend to the `try` statement
            self.pop_scope(saved_current_scope, saved_first_declarations);
            if grandparent_of_try_block.is_some() {
                self.pop_node(grandparent_of_try_block.unwrap());
            }

            let try_block_node = try_block.expect("try statement has no try block");
            let mut try_block_statement_list =
                ec.borrow_mut().factory.new_node_list(try_block_statements);
            try_block_statement_list.loc = cx.nodes[try_block_node]
                .as_block()
                .statements
                .as_ref()
                .map(|s| s.loc)
                .unwrap_or_default();
            let multi_line = cx.nodes[try_block_node].as_block().multi_line;
            let new_try_block = ec
                .borrow_mut()
                .factory
                .update_block(
                    cx.nodes,
                    try_block_node,
                    Some(try_block_statement_list),
                    multi_line,
                )
                .unwrap_or(try_block_node);
            let catch_clause = v.visit_node(
                cx,
                cx.nodes[super_statement].as_try_statement().catch_clause,
            );
            let finally_block = v.visit_node(
                cx,
                cx.nodes[super_statement].as_try_statement().finally_block,
            );
            let updated_try = ec
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
            statements_out.push(updated_try);

            // restore hierarchy as we ascend to the parent of the `try`
            // statement
            self.pop_node(grandparent_of_try_statement);
        } else {
            // visit the statement containing `super`
            statements_out.extend(
                v.visit_slice(
                    cx,
                    &statements_in[super_statement_index..super_statement_index + 1],
                )
                .unwrap_or_else(|| {
                    statements_in[super_statement_index..super_statement_index + 1].to_vec()
                }),
            );

            // insert the initializer statements
            statements_out.extend_from_slice(initializer_statements);
        }

        // visit the statements after `super`
        statements_out.extend(
            v.visit_slice(cx, &statements_in[super_statement_index + 1..])
                .unwrap_or_else(|| statements_in[super_statement_index + 1..].to_vec()),
        );
        statements_out
    }

    /// `tx.visitShorthandPropertyAssignment`
    fn visit_shorthand_property_assignment<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let name = cx.nodes[node]
            .name()
            .expect("shorthand property has no name");
        let exported_or_imported_name = self.visit_expression_identifier(ec, cx, name);
        if exported_or_imported_name != name {
            let mut expression = exported_or_imported_name;
            let object_assignment_initializer = cx.nodes[node]
                .as_shorthand_property_assignment()
                .object_assignment_initializer;
            if object_assignment_initializer.is_some() {
                let equals_token = cx.nodes[node]
                    .as_shorthand_property_assignment()
                    .equals_token
                    .unwrap_or_else(|| {
                        ec.borrow_mut()
                            .factory
                            .new_token(cx.nodes, Kind::EqualsToken)
                    });
                let right = v.visit_node(cx, object_assignment_initializer);
                expression = ec.borrow_mut().factory.new_binary_expression(
                    cx.nodes,
                    None, /* modifiers */
                    Some(expression),
                    None, /* type_node */
                    Some(equals_token),
                    right,
                );
            }

            let updated = ec.borrow_mut().factory.new_property_assignment(
                cx.nodes,
                None, /* modifiers */
                cx.nodes[node].name(),
                None, /* postfix_token */
                None, /* type_node */
                Some(expression),
            );
            cx.nodes[updated].loc = cx.nodes[node].loc;
            ec.borrow().set_original(updated, node);
            ec.borrow()
                .assign_comment_and_source_map_ranges(cx.nodes, updated, node);
            return updated;
        }
        let object_assignment_initializer = cx.nodes[node]
            .as_shorthand_property_assignment()
            .object_assignment_initializer;
        let visited_initializer = v.visit_node(cx, object_assignment_initializer);
        ec.borrow_mut()
            .factory
            .update_shorthand_property_assignment(
                cx.nodes,
                node,
                None, /* modifiers */
                Some(exported_or_imported_name),
                None, /* postfix_token */
                None, /* type_node */
                cx.nodes[node]
                    .as_shorthand_property_assignment()
                    .equals_token,
                visited_initializer,
            )
            .unwrap_or(node)
    }

    /// `tx.visitIdentifier`
    fn visit_identifier(&self, ec: &Ec, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        if self
            .parent_node
            .get()
            .is_some_and(|p| is_identifier_reference(cx.nodes, node, p))
        {
            return self.visit_expression_identifier(ec, cx, node);
        }
        node
    }

    /// `tx.visitExpressionIdentifier`
    fn visit_expression_identifier(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if (self.current_enum.get().is_some() || self.current_namespace.get().is_some())
            && !is_generated_identifier(&ec.borrow(), node)
            && !is_local_name(&ec.borrow(), node)
        {
            let location = ec.borrow().most_original(Some(node)).unwrap_or(node);
            let container = {
                let resolver = self
                    .resolver
                    .as_ref()
                    .expect("RuntimeSyntaxTransformer requires a reference resolver");
                let symbols = self
                    .symbols
                    .expect("RuntimeSyntaxTransformer requires TransformOptions::symbols");
                resolver.borrow_mut().get_referenced_export_container(
                    location, false, cx.nodes, symbols,
                )
            };
            if let Some(container) = container {
                if ast::is_enum_declaration(&cx.nodes[container])
                    || ast::is_module_declaration(&cx.nodes[container])
                {
                    let container_name = self.get_namespace_container_name(ec, cx, Some(container));

                    let member_name = ec.borrow_mut().factory.clone_node(cx.nodes, node);
                    ec.borrow().set_emit_flags(
                        member_name,
                        EmitFlags::NO_COMMENTS | EmitFlags::NO_SOURCE_MAP,
                    );

                    let expression = ec.borrow_mut().factory.get_namespace_member_name(
                        cx.nodes,
                        container_name,
                        member_name,
                        &NameOptions {
                            allow_source_maps: true,
                            ..Default::default()
                        },
                    );
                    ec.borrow()
                        .assign_comment_and_source_map_ranges(cx.nodes, expression, node);
                    return expression;
                }
            }
        }
        node
    }

    /// `tx.createExportStatementForDeclaration`
    fn create_export_statement_for_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let ns = self.get_namespace_container_name(ec, cx, self.current_namespace.get());
        let export_name = ec
            .borrow_mut()
            .factory
            .get_external_module_or_namespace_export_name(
                cx.nodes,
                Some(ns),
                node,
                false, /* allowComments */
                true,  /* allowSourceMaps */
            );
        let local_name = ec.borrow_mut().factory.get_local_name(cx.nodes, Some(node));
        let expression =
            ec.borrow_mut()
                .factory
                .new_assignment_expression(cx.nodes, export_name, local_name);
        let mut export_assignment_source_map_range = cx.nodes[node].loc;
        if let Some(name) = cx.nodes[node].name() {
            export_assignment_source_map_range =
                export_assignment_source_map_range.with_pos(cx.nodes[name].loc.pos());
        }
        ec.borrow()
            .set_source_map_range(expression, export_assignment_source_map_range);

        let statement = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(expression));
        let export_statement_source_map_range = cx.nodes[node].loc.with_pos(-1);
        ec.borrow()
            .set_source_map_range(statement, export_statement_source_map_range);
        statement
    }

    /// `tx.createExportAssignment`
    fn create_export_assignment(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        expression: Option<NodeId>,
        export_assignment_source_map_range: TextRange,
        original: NodeId,
    ) -> NodeId {
        let ns = self.get_namespace_container_name(ec, cx, self.current_namespace.get());
        let export_name = self.get_namespace_qualified_property(ec, cx, ns, name);
        let export_assignment = ec.borrow_mut().factory.new_assignment_expression(
            cx.nodes,
            export_name,
            expression.expect("export assignment has no expression"),
        );
        ec.borrow().set_original(export_assignment, original);
        ec.borrow()
            .set_source_map_range(export_assignment, export_assignment_source_map_range);
        export_assignment
    }

    /// `tx.createExportStatement`
    fn create_export_statement(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: NodeId,
        expression: Option<NodeId>,
        export_assignment_source_map_range: TextRange,
        export_statement_source_map_range: TextRange,
        original: NodeId,
    ) -> NodeId {
        let assignment = self.create_export_assignment(
            ec,
            cx,
            name,
            expression,
            export_assignment_source_map_range,
            original,
        );
        let export_statement = ec
            .borrow_mut()
            .factory
            .new_expression_statement(cx.nodes, Some(assignment));
        ec.borrow().set_original(export_statement, original);
        ec.borrow()
            .set_source_map_range(export_statement, export_statement_source_map_range);
        export_statement
    }

    /// `tx.shouldEmitEnumDeclaration`
    fn should_emit_enum_declaration(&self, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        !ast::is_enum_const(node, cx.nodes) || self.compiler_options.should_preserve_const_enums()
    }

    /// `tx.shouldEmitModuleDeclaration`
    fn should_emit_module_declaration(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> bool {
        let pn = ec.borrow().parse_node(cx.nodes, node);
        match pn {
            None => {
                // If we can't find a parse tree node, assume the node is
                // instantiated.
                true
            }
            Some(pn) => ast::is_instantiated_module(
                pn,
                self.compiler_options.should_preserve_const_enums(),
                cx.nodes,
            ),
        }
    }
}

/// `NewRuntimeSyntaxTransformer`
#[allow(dead_code)]
pub fn new_runtime_syntax_transformer<'a>(opt: &TransformOptions<'a>) -> Option<Transformer<'a>> {
    let state = Rc::new(RuntimeSyntaxTransformer {
        compiler_options: opt.compiler_options.unwrap_or(&EMPTY_COMPILER_OPTIONS),
        parent_node: Cell::new(None),
        current_node: Cell::new(None),
        current_source_file: Cell::new(None),
        current_scope: Cell::new(None),
        current_scope_first_declarations_of_name: RefCell::new(None),
        current_enum: Cell::new(None),
        current_namespace: Cell::new(None),
        resolver: opt.resolver.clone(),
        emit_resolver: opt.emit_resolver.clone(),
        symbols: opt.symbols,
        self_ref: RefCell::new(Weak::new()),
    });
    *state.self_ref.borrow_mut() = Rc::downgrade(&state);
    make_transformer(opt, move |ec| {
        let state = state.clone();
        Box::new(
            move |_v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, _v, cx, node)
            },
        )
    })
}
