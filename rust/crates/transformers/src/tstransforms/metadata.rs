// Ported from tsc/internal/transformers/tstransforms/metadata.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The decorator-metadata transform — injects synthetic `__metadata("design:*",
// ...)` decorators carrying serialized type information (see
// `typeserializer.rs`).
//
// PORT: `parent`/`currentLexicalScope` are `Cell<Option<NodeId>>`s; the
// `serializer` created per SourceFile visit is `RefCell<Option<...>>` on the
// shared state. `resolver` is `Option<Rc<RefCell<dyn EmitResolver>>>` (Go's
// nilable interface — serialization paths `.expect()` it like Go's
// nil-interface panic). `USE_NEW_TYPE_METADATA_FORMAT` is `false`, as in Go.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use tsc_ast::visitor::{NodeVisitor, VisitFn, VisitorCx};
use tsc_ast::{self as ast, Kind, ModifierList, NodeId, SubtreeFacts};
use tsc_core::compileroptions::EMPTY_COMPILER_OPTIONS;
use tsc_core::core::filter;
use tsc_core::options_generated::ScriptTarget;
use tsc_printer::EmitResolver;

use super::legacydecorators::get_decorators_of_parameters;
use super::typeserializer::{
    MetadataSerializer, MetadataSerializerContext, new_metadata_serializer,
};
use crate::chain::TransformOptions;
use crate::estransforms::{make_transformer, visit_each_child, Ec};
use crate::transformer::Transformer;

/// `const USE_NEW_TYPE_METADATA_FORMAT`.
const USE_NEW_TYPE_METADATA_FORMAT: bool = false;

/// `type MetadataTransformer struct`.
pub struct MetadataTransformer<'a> {
    /// `legacyDecorators bool`
    legacy_decorators: bool,
    /// `resolver printer.EmitResolver`
    resolver: Option<Rc<RefCell<dyn EmitResolver + 'a>>>,

    /// `serializer *metadataSerializer`
    serializer: RefCell<Option<MetadataSerializer<'a>>>,
    /// `languageVersion core.ScriptTarget`
    language_version: ScriptTarget,
    /// `strictNullChecks bool`
    strict_null_checks: bool,
    /// `parent *ast.Node`
    parent: Cell<Option<NodeId>>,
    /// `currentLexicalScope *ast.Node`
    current_lexical_scope: Cell<Option<NodeId>>,
}

impl<'a> MetadataTransformer<'a> {
    /// `tx.visit`
    fn visit<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> Option<NodeId> {
        if cx.nodes[node].subtree_facts(cx.nodes) & SubtreeFacts::CONTAINS_DECORATORS
            == SubtreeFacts::NONE
        {
            return Some(node);
        }

        match cx.nodes[node].kind {
            Kind::ClassDeclaration => Some(self.visit_class_declaration(ec, v, cx, node)),
            Kind::ClassExpression => Some(self.visit_class_expression(ec, v, cx, node)),
            Kind::ObjectLiteralExpression => {
                Some(self.visit_object_literal_expression(v, cx, node))
            }
            Kind::PropertyDeclaration => Some(self.visit_property_declaration(ec, v, cx, node)),
            Kind::MethodDeclaration => Some(self.visit_method_declaration(ec, v, cx, node)),
            Kind::SetAccessor => Some(self.visit_set_accessor(ec, v, cx, node)),
            Kind::GetAccessor => Some(self.visit_get_accessor(ec, v, cx, node)),
            Kind::SourceFile => {
                self.parent.set(None);
                self.current_lexical_scope.set(Some(node));
                *self.serializer.borrow_mut() = Some(new_metadata_serializer(
                    self.resolver.clone(),
                    ec.clone(),
                    self.language_version,
                    self.strict_null_checks,
                ));
                let updated = v.visit_each_child(cx, node).unwrap_or(node);
                let helpers = ec.borrow_mut().read_emit_helpers();
                ec.borrow().add_emit_helper(updated, &helpers);
                self.parent.set(None);
                self.current_lexical_scope.set(None);
                Some(updated)
            }
            Kind::ModuleBlock | Kind::Block | Kind::CaseBlock => {
                let old_scope = self.current_lexical_scope.get();
                self.current_lexical_scope.set(Some(node));
                let updated = v.visit_each_child(cx, node).unwrap_or(node);
                self.current_lexical_scope.set(old_scope);
                Some(updated)
            }
            _ => Some(visit_each_child(v, cx, node)),
        }
    }

    /// `tx.visitObjectLiteralExpression`
    fn visit_object_literal_expression<'v>(
        &self,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let old_parent = self.parent.get();
        self.parent.set(Some(node));
        let updated = v.visit_each_child(cx, node).unwrap_or(node);
        self.parent.set(old_parent);
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
        let old_parent = self.parent.get();
        self.parent.set(Some(node));

        let result = if !ast::class_or_constructor_parameter_is_decorated(
            self.legacy_decorators,
            node,
            cx.nodes,
        ) {
            v.visit_each_child(cx, node).unwrap_or(node)
        } else {
            let visited_modifiers =
                v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
            let modifiers =
                self.inject_class_type_metadata(ec, cx, visited_modifiers, node);
            let name = v.visit_node(cx, cx.nodes[node].name());
            let type_parameters = v.visit_nodes(
                cx,
                cx.nodes[node]
                    .as_class_expression()
                    .class_like_base
                    .type_parameters
                    .clone(),
            );
            let heritage_clauses = v.visit_nodes(
                cx,
                cx.nodes[node]
                    .as_class_expression()
                    .class_like_base
                    .heritage_clauses
                    .clone(),
            );
            let members = v.visit_nodes(cx, cx.nodes[node].member_list().cloned());
            ec.borrow_mut()
                .factory
                .update_class_expression(
                    cx.nodes,
                    node,
                    modifiers,
                    name,
                    type_parameters,
                    heritage_clauses,
                    members,
                )
                .unwrap_or(node)
        };
        self.parent.set(old_parent);
        result
    }

    /// `tx.visitClassDeclaration`
    fn visit_class_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        let old_parent = self.parent.get();
        self.parent.set(Some(node));

        let result = if !ast::class_or_constructor_parameter_is_decorated(
            self.legacy_decorators,
            node,
            cx.nodes,
        ) {
            v.visit_each_child(cx, node).unwrap_or(node)
        } else {
            let visited_modifiers =
                v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
            let modifiers =
                self.inject_class_type_metadata(ec, cx, visited_modifiers, node);
            let name = v.visit_node(cx, cx.nodes[node].name());
            let type_parameters = v.visit_nodes(
                cx,
                cx.nodes[node]
                    .as_class_declaration()
                    .class_like_base
                    .type_parameters
                    .clone(),
            );
            let heritage_clauses = v.visit_nodes(
                cx,
                cx.nodes[node]
                    .as_class_declaration()
                    .class_like_base
                    .heritage_clauses
                    .clone(),
            );
            let members = v.visit_nodes(cx, cx.nodes[node].member_list().cloned());
            ec.borrow_mut()
                .factory
                .update_class_declaration(
                    cx.nodes,
                    node,
                    modifiers,
                    name,
                    type_parameters,
                    heritage_clauses,
                    members,
                )
                .unwrap_or(node)
        };
        self.parent.set(old_parent);
        result
    }

    /// `tx.visitPropertyDeclaration`
    fn visit_property_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if !ast::has_decorators(&cx.nodes[node]) {
            return visit_each_child(v, cx, node);
        }

        let visited_modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let modifiers = self.inject_class_element_type_metadata(
            ec,
            cx,
            visited_modifiers,
            node,
            self.parent.get(),
        );
        let d = cx.nodes[node].as_property_declaration();
        let (name, postfix_token, type_, initializer) = (
            d.named_member_base.name,
            d.named_member_base.postfix_token,
            d.type_,
            d.initializer,
        );
        let name = v.visit_node(cx, name);
        let postfix_token = v.visit_node(cx, postfix_token);
        let type_ = v.visit_node(cx, type_);
        let initializer = v.visit_node(cx, initializer);
        ec.borrow_mut()
            .factory
            .update_property_declaration(
                cx.nodes,
                node,
                modifiers,
                name,
                postfix_token,
                type_,
                initializer,
            )
            .unwrap_or(node)
    }

    /// `tx.visitMethodDeclaration`
    fn visit_method_declaration<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if !ast::has_decorators(&cx.nodes[node])
            && get_decorators_of_parameters(Some(node), cx.nodes).is_empty()
        {
            return visit_each_child(v, cx, node);
        }

        let visited_modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let modifiers = self.inject_class_element_type_metadata(
            ec,
            cx,
            visited_modifiers,
            node,
            self.parent.get(),
        );
        let d = cx.nodes[node].as_method_declaration();
        let (asterisk_token, name, postfix_token, type_parameters, parameters, type_, full_signature, body) = (
            d.function_like_with_body_base.body_base.asterisk_token,
            d.named_member_base.name,
            d.named_member_base.postfix_token,
            d.function_like_with_body_base.function_like_base.type_parameters.clone(),
            d.function_like_with_body_base.function_like_base.parameters.clone(),
            d.function_like_with_body_base.function_like_base.type_,
            d.function_like_with_body_base.function_like_base.full_signature,
            d.function_like_with_body_base.body_base.body,
        );
        let asterisk_token = v.visit_node(cx, asterisk_token);
        let name = v.visit_node(cx, name);
        let postfix_token = v.visit_node(cx, postfix_token);
        let type_parameters = v.visit_nodes(cx, type_parameters);
        let parameters = v.visit_nodes(cx, parameters);
        let type_ = v.visit_node(cx, type_);
        let full_signature = v.visit_node(cx, full_signature);
        let body = v.visit_node(cx, body);
        ec.borrow_mut()
            .factory
            .update_method_declaration(
                cx.nodes,
                node,
                modifiers,
                asterisk_token,
                name,
                postfix_token,
                type_parameters,
                parameters,
                type_,
                full_signature,
                body,
            )
            .unwrap_or(node)
    }

    /// `tx.visitSetAccessor`
    fn visit_set_accessor<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if !ast::has_decorators(&cx.nodes[node])
            && get_decorators_of_parameters(Some(node), cx.nodes).is_empty()
        {
            return visit_each_child(v, cx, node);
        }

        let visited_modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let modifiers = self.inject_class_element_type_metadata(
            ec,
            cx,
            visited_modifiers,
            node,
            self.parent.get(),
        );
        let d = cx.nodes[node].as_set_accessor_declaration();
        let (name, type_parameters, parameters, type_, full_signature, body) = (
            d.accessor_declaration_base.named_member_base.name,
            d.accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .type_parameters
                .clone(),
            d.accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .parameters
                .clone(),
            d.accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .type_,
            d.accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .full_signature,
            d.accessor_declaration_base
                .function_like_with_body_base
                .body_base
                .body,
        );
        let name = v.visit_node(cx, name);
        let type_parameters = v.visit_nodes(cx, type_parameters);
        let parameters = v.visit_nodes(cx, parameters);
        let type_ = v.visit_node(cx, type_);
        let full_signature = v.visit_node(cx, full_signature);
        let body = v.visit_node(cx, body);
        ec.borrow_mut()
            .factory
            .update_set_accessor_declaration(
                cx.nodes,
                node,
                modifiers,
                name,
                type_parameters,
                parameters,
                type_,
                full_signature,
                body,
            )
            .unwrap_or(node)
    }

    /// `tx.visitGetAccessor`
    fn visit_get_accessor<'v>(
        &self,
        ec: &Ec,
        v: &NodeVisitor<'v>,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
    ) -> NodeId {
        if !ast::has_decorators(&cx.nodes[node]) {
            return visit_each_child(v, cx, node);
        }

        let visited_modifiers = v.visit_modifiers(cx, cx.nodes[node].modifiers().cloned());
        let modifiers = self.inject_class_element_type_metadata(
            ec,
            cx,
            visited_modifiers,
            node,
            self.parent.get(),
        );
        let d = cx.nodes[node].as_get_accessor_declaration();
        let (name, type_parameters, parameters, type_, full_signature, body) = (
            d.accessor_declaration_base.named_member_base.name,
            d.accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .type_parameters
                .clone(),
            d.accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .parameters
                .clone(),
            d.accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .type_,
            d.accessor_declaration_base
                .function_like_with_body_base
                .function_like_base
                .full_signature,
            d.accessor_declaration_base
                .function_like_with_body_base
                .body_base
                .body,
        );
        let name = v.visit_node(cx, name);
        let type_parameters = v.visit_nodes(cx, type_parameters);
        let parameters = v.visit_nodes(cx, parameters);
        let type_ = v.visit_node(cx, type_);
        let full_signature = v.visit_node(cx, full_signature);
        let body = v.visit_node(cx, body);
        ec.borrow_mut()
            .factory
            .update_get_accessor_declaration(
                cx.nodes,
                node,
                modifiers,
                name,
                type_parameters,
                parameters,
                type_,
                full_signature,
                body,
            )
            .unwrap_or(node)
    }

    /// `tx.injectClassTypeMetadata`
    fn inject_class_type_metadata(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        list: Option<ModifierList>,
        node: NodeId,
    ) -> Option<ModifierList> {
        let metadata = self.get_type_metadata(ec, cx, node, Some(node));
        if !metadata.is_empty() {
            let original_nodes: Vec<NodeId> = list
                .as_ref()
                .map(|l| l.nodes.to_vec())
                .unwrap_or_default();
            if original_nodes.is_empty() {
                let mut res = ec.borrow_mut().factory.new_modifier_list(cx.nodes, metadata);
                if let Some(list) = &list {
                    res.loc = list.loc;
                }
                return Some(res);
            }
            let mut modifiers_array: Vec<NodeId> = Vec::new();
            if ast::is_modifier(&cx.nodes[original_nodes[0]])
                && (cx.nodes[original_nodes[0]].kind == Kind::DefaultKeyword
                    || cx.nodes[original_nodes[0]].kind == Kind::ExportKeyword)
            {
                modifiers_array.push(original_nodes[0]);
                if original_nodes.len() > 1
                    && (cx.nodes[original_nodes[1]].kind == Kind::DefaultKeyword
                        || cx.nodes[original_nodes[1]].kind == Kind::ExportKeyword)
                {
                    modifiers_array.push(original_nodes[1]);
                }
            }
            let rest_start = modifiers_array.len();
            let decos: Vec<NodeId> = filter(&original_nodes, |&n| {
                ast::is_decorator(&cx.nodes[n])
            })
            .into_owned();
            modifiers_array.extend(decos);
            modifiers_array.extend(metadata);
            let other_modifiers: Vec<NodeId> = filter(&original_nodes[rest_start..], |&n| {
                ast::is_modifier(&cx.nodes[n])
            })
            .into_owned();
            modifiers_array.extend(other_modifiers);
            let mut res = ec
                .borrow_mut()
                .factory
                .new_modifier_list(cx.nodes, modifiers_array);
            res.loc = list.as_ref().map(|l| l.loc).unwrap_or_default();
            return Some(res);
        }
        list
    }

    /// `tx.injectClassElementTypeMetadata`
    fn inject_class_element_type_metadata(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        list: Option<ModifierList>,
        node: NodeId,
        container: Option<NodeId>,
    ) -> Option<ModifierList> {
        if !container.is_some_and(|c| ast::is_class_like(Some(c), cx.nodes)) {
            return list;
        }
        if !ast::class_element_or_class_element_parameter_is_decorated(
            self.legacy_decorators,
            node,
            container.unwrap(),
            cx.nodes,
        ) {
            return list;
        }
        let metadata = self.get_type_metadata(ec, cx, node, container);
        if !metadata.is_empty() {
            let original_nodes: Vec<NodeId> = list
                .as_ref()
                .map(|l| l.nodes.to_vec())
                .unwrap_or_default();
            if original_nodes.is_empty() {
                let mut res = ec.borrow_mut().factory.new_modifier_list(cx.nodes, metadata);
                if let Some(list) = &list {
                    res.loc = list.loc;
                }
                return Some(res);
            }
            let mut modifiers_array: Vec<NodeId> = Vec::new();
            let decos: Vec<NodeId> = filter(&original_nodes, |&n| {
                ast::is_decorator(&cx.nodes[n])
            })
            .into_owned();
            modifiers_array.extend(decos);
            modifiers_array.extend(metadata);
            let modifiers: Vec<NodeId> = filter(&original_nodes, |&n| {
                ast::is_modifier(&cx.nodes[n])
            })
            .into_owned();
            modifiers_array.extend(modifiers);
            let mut res = ec
                .borrow_mut()
                .factory
                .new_modifier_list(cx.nodes, modifiers_array);
            res.loc = list.as_ref().map(|l| l.loc).unwrap_or_default();
            return Some(res);
        }
        list
    }

    /// `tx.getTypeMetadata` — gets optional type metadata for a declaration.
    fn get_type_metadata(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        container: Option<NodeId>,
    ) -> Vec<NodeId> {
        // Decorator metadata is not yet supported for ES decorators.
        if !self.legacy_decorators {
            return Vec::new();
        }
        if USE_NEW_TYPE_METADATA_FORMAT {
            return self.get_new_type_metadata(ec, cx, node, container);
        }
        self.get_old_type_metadata(ec, cx, node, container)
    }

    /// `tx.getOldTypeMetadata`.
    fn get_old_type_metadata(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        container: Option<NodeId>,
    ) -> Vec<NodeId> {
        let mut decorators: Vec<NodeId> = Vec::new();
        if self.should_add_type_metadata(cx, node) {
            let type_metadata = {
                let serializer = self.serializer.borrow();
                let value = serializer
                    .as_ref()
                    .expect("serializer not initialized")
                    .serialize_type_of_node(
                        cx.nodes,
                        MetadataSerializerContext {
                            current_lexical_scope: self.current_lexical_scope.get(),
                            current_name_scope: container,
                            ..Default::default()
                        },
                        node,
                        container,
                    );
                ec.borrow_mut()
                    .factory
                    .new_metadata_helper(cx.nodes, "design:type", value)
            };
            let decorator = ec
                .borrow_mut()
                .factory
                .new_decorator(cx.nodes, Some(type_metadata));
            decorators.push(decorator);
        }
        if self.should_add_param_types_metadata(cx, node) {
            let param_types_metadata = {
                let serializer = self.serializer.borrow();
                let value = serializer
                    .as_ref()
                    .expect("serializer not initialized")
                    .serialize_parameter_types_of_node(
                        cx.nodes,
                        MetadataSerializerContext {
                            current_lexical_scope: self.current_lexical_scope.get(),
                            current_name_scope: container,
                            ..Default::default()
                        },
                        node,
                        container,
                    );
                ec.borrow_mut()
                    .factory
                    .new_metadata_helper(cx.nodes, "design:paramtypes", value)
            };
            let decorator = ec
                .borrow_mut()
                .factory
                .new_decorator(cx.nodes, Some(param_types_metadata));
            decorators.push(decorator);
        }
        if self.should_add_return_type_metadata(cx, node) {
            let return_type_metadata = {
                let serializer = self.serializer.borrow();
                let value = serializer
                    .as_ref()
                    .expect("serializer not initialized")
                    .serialize_return_type_of_node(
                        cx.nodes,
                        MetadataSerializerContext {
                            current_lexical_scope: self.current_lexical_scope.get(),
                            current_name_scope: container,
                            ..Default::default()
                        },
                        node,
                    );
                ec.borrow_mut()
                    .factory
                    .new_metadata_helper(cx.nodes, "design:returntype", value)
            };
            let decorator = ec
                .borrow_mut()
                .factory
                .new_decorator(cx.nodes, Some(return_type_metadata));
            decorators.push(decorator);
        }
        decorators
    }

    /// `tx.getNewTypeMetadata` — dead code while
    /// `USE_NEW_TYPE_METADATA_FORMAT` is `false` (as in Go).
    fn get_new_type_metadata(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        node: NodeId,
        container: Option<NodeId>,
    ) -> Vec<NodeId> {
        let mut properties: Vec<NodeId> = Vec::new();
        if self.should_add_type_metadata(cx, node) {
            let value = {
                let serializer = self.serializer.borrow();
                serializer
                    .as_ref()
                    .expect("serializer not initialized")
                    .serialize_type_of_node(
                        cx.nodes,
                        MetadataSerializerContext {
                            current_lexical_scope: self.current_lexical_scope.get(),
                            current_name_scope: container,
                            ..Default::default()
                        },
                        node,
                        container,
                    )
            };
            properties.push(self.new_metadata_property(
                ec,
                cx,
                "type",
                value,
            ));
        }
        if self.should_add_param_types_metadata(cx, node) {
            let value = {
                let serializer = self.serializer.borrow();
                serializer
                    .as_ref()
                    .expect("serializer not initialized")
                    .serialize_parameter_types_of_node(
                        cx.nodes,
                        MetadataSerializerContext {
                            current_lexical_scope: self.current_lexical_scope.get(),
                            current_name_scope: container,
                            ..Default::default()
                        },
                        node,
                        container,
                    )
            };
            properties.push(self.new_metadata_property(ec, cx, "paramTypes", value));
        }
        if self.should_add_return_type_metadata(cx, node) {
            let value = {
                let serializer = self.serializer.borrow();
                serializer
                    .as_ref()
                    .expect("serializer not initialized")
                    .serialize_return_type_of_node(
                        cx.nodes,
                        MetadataSerializerContext {
                            current_lexical_scope: self.current_lexical_scope.get(),
                            current_name_scope: container,
                            ..Default::default()
                        },
                        node,
                    )
            };
            properties.push(self.new_metadata_property(ec, cx, "returnType", value));
        }
        if !properties.is_empty() {
            let props_list = ec.borrow_mut().factory.new_node_list(properties);
            let object_literal = ec
                .borrow_mut()
                .factory
                .new_object_literal_expression(cx.nodes, Some(props_list), true);
            let type_info_metadata = ec.borrow_mut().factory.new_metadata_helper(
                cx.nodes,
                "design:typeinfo",
                object_literal,
            );
            let decorator = ec
                .borrow_mut()
                .factory
                .new_decorator(cx.nodes, Some(type_info_metadata));
            return vec![decorator];
        }
        Vec::new()
    }

    /// The `NewPropertyAssignment(nil, name, nil, nil, arrowFn)` wrapper
    /// shared by `getNewTypeMetadata`'s three branches.
    fn new_metadata_property(
        &self,
        ec: &Ec,
        cx: &mut VisitorCx<'_, '_>,
        name: &str,
        body: NodeId,
    ) -> NodeId {
        let name_node = ec.borrow_mut().factory.new_identifier(cx.nodes, name);
        let params = ec.borrow_mut().factory.new_node_list([]);
        let arrow_token = ec
            .borrow_mut()
            .factory
            .new_token(cx.nodes, Kind::EqualsGreaterThanToken);
        let arrow = ec.borrow_mut().factory.new_arrow_function(
            cx.nodes,
            None,
            None,
            Some(params),
            None,
            None,
            Some(arrow_token),
            Some(body),
        );
        ec.borrow_mut().factory.new_property_assignment(
            cx.nodes,
            None,
            Some(name_node),
            None,
            None,
            Some(arrow),
        )
    }

    /// `tx.shouldAddTypeMetadata` — determines whether to emit the
    /// "design:type" metadata based on the node's kind.
    fn should_add_type_metadata(&self, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        matches!(
            cx.nodes[node].kind,
            Kind::MethodDeclaration
                | Kind::GetAccessor
                | Kind::SetAccessor
                | Kind::PropertyDeclaration
        )
    }

    /// `tx.shouldAddReturnTypeMetadata` — determines whether to emit the
    /// "design:returntype" metadata based on the node's kind.
    fn should_add_return_type_metadata(&self, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        cx.nodes[node].kind == Kind::MethodDeclaration
    }

    /// `tx.shouldAddParamTypesMetadata` — determines whether to emit the
    /// "design:paramtypes" metadata based on the node's kind.
    fn should_add_param_types_metadata(&self, cx: &VisitorCx<'_, '_>, node: NodeId) -> bool {
        match cx.nodes[node].kind {
            Kind::ClassDeclaration | Kind::ClassExpression => {
                ast::get_first_constructor_with_body(&cx.nodes[node], cx.nodes).is_some()
            }
            Kind::MethodDeclaration | Kind::GetAccessor | Kind::SetAccessor => true,
            _ => false,
        }
    }
}

/// `NewMetadataTransformer`.
#[allow(dead_code)]
pub fn new_metadata_transformer<'a>(
    opts: &TransformOptions<'a>,
) -> Option<Transformer<'a>> {
    let compiler_options = opts.compiler_options.unwrap_or(&EMPTY_COMPILER_OPTIONS);
    let state = Rc::new(MetadataTransformer {
        legacy_decorators: compiler_options.experimental_decorators.is_true(),
        resolver: opts.emit_resolver.clone(),
        serializer: RefCell::new(None),
        language_version: compiler_options.get_emit_script_target(),
        strict_null_checks: compiler_options
            .get_strict_option_value(compiler_options.strict_null_checks),
        parent: Cell::new(None),
        current_lexical_scope: Cell::new(None),
    });
    make_transformer(opts, move |ec| {
        let state = state.clone();
        let visit: Box<VisitFn<'a>> = Box::new(
            move |v: &NodeVisitor<'a>, cx: &mut VisitorCx<'_, '_>, node: NodeId| {
                state.visit(&ec, v, cx, node)
            },
        );
        visit
    })
}
