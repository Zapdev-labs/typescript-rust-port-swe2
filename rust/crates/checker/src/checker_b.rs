// PORT(partial) — `checker.go` lines 8205–16294 @
// ec47d33c23e464a17cdf2475632cba629bee8763 (`isTemplateLiteralContext`
// through `tryGetQualifiedNameAsValue`, the function preceding
// `getSuggestedSymbolForNonexistentModule`).
//
// All `func (c *Checker)` methods become `impl Checker` methods; free
// functions become `pub(crate)` free functions. Cross-file calls are
// written as direct snake_case references — `self.<method>(...)` for
// Checker methods living in checker_a.rs/checker_c.rs/checker_d.rs/
// checker_core.rs, and `crate::<module>::<fn>(...)` for free functions
// owned by other Go files (`crate::utilities`, `crate::grammarchecks`,
// `crate::flow`, `crate::inference`, `crate::checker_a/c/d`,
// `crate::relater`, `crate::exports`). They resolve when the sibling
// files land.
//
// Pointer mapping follows checker_core.rs: `*ast.Node` → `NodeId`
// (`Option<NodeId>` for nil), `*ast.Symbol` → `Option<SymbolId>`,
// `*Type` → `TypeId`/`Option<TypeId>`, `*Signature` →
// `SignatureId`/`Option<SignatureId>`, `*Relation` → `&SharedRelation`,
// `*InferenceContext` → `InferenceContextId`, `*ast.Diagnostic` →
// `Option<DiagnosticRef>`, `*[]*Signature` → `Option<&mut
// Vec<SignatureId>>`, `*[]*ast.Diagnostic` → `Option<&mut
// Vec<DiagnosticRef>>`, `*[]*Type` → `&mut Vec<TypeId>`.

use std::rc::Rc;

use rustc_hash::FxHashSet;
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::{self as ast, NodeId, SymbolId, SymbolTable};
use tsc_core::options_generated::{ModuleKind, ModuleResolutionKind, ScriptTarget};

use crate::checker_core::{
    CheckMode, Checker, InferenceContextId, InferenceFlags, InferencePriority,
};
use crate::checker_types::{
    CachedSignatureKey, CachedTypeKey, CachedTypeKind, InstantiationExpressionKey,
    IterationTypeKind, IterationTypes, IterationUse, MappedTypeModifiers, MappedTypeNameTypeKind,
    PredicateSemantics, ReferenceHint, TypeFacts, TypeSystemEntity, TypeSystemPropertyName,
    UnionReduction,
};
use crate::mapper::TypeMapperId;
use crate::relater::{Comparer, SharedRelation};
use crate::types::{
    AccessFlags, CompositeSignature, ContextFlags, ElementFlags, ExternalEmitHelpers, IndexFlags,
    IndexInfoId, NodeCheckFlags, ObjectFlags, Signature, SignatureFlags, SignatureId,
    SignatureKind, Ternary, TupleElementInfo, TypeFlags, TypeId,
};

impl Checker {
    /// `isTemplateLiteralContext` (checker.go:8205).
    pub(crate) fn is_template_literal_context(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node]
            .parent
            .expect("isTemplateLiteralContext: nil parent");
        (ast::is_parenthesized_expression(&nodes[parent])
            && self.is_template_literal_context(parent))
            || (ast::is_element_access_expression(&nodes[parent])
                && nodes[parent]
                    .as_element_access_expression()
                    .argument_expression
                    == Some(node))
    }

    /// `isTemplateLiteralContextualType` (checker.go:8210).
    pub(crate) fn is_template_literal_contextual_type(&mut self, t: TypeId) -> bool {
        let flags = self.types.get_ref(t).flags;
        flags.intersects(TypeFlags::STRING_LITERAL | TypeFlags::TEMPLATE_LITERAL)
            || flags.intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE) && {
                let base = self
                    .get_base_constraint_of_type(t)
                    .unwrap_or(self.unknown_type);
                self.maybe_type_of_kind(base, TypeFlags::STRING_LIKE)
            }
    }

    /// `checkRegularExpressionLiteral` (checker.go:8214).
    pub(crate) fn check_regular_expression_literal(&mut self, node: NodeId) -> TypeId {
        {
            let node_links = self.node_links.get(node);
            if !node_links.flags.intersects(NodeCheckFlags::TYPE_CHECKED) {
                node_links.flags.insert(NodeCheckFlags::TYPE_CHECKED);
            } else {
                return self.global_reg_exp_type;
            }
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let _ = nodes[node].as_regular_expression_literal();
        self.check_grammar_regular_expression_literal(node);
        self.global_reg_exp_type
    }

    /// `checkArrayLiteral` (checker.go:8223).
    pub(crate) fn check_array_literal(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let elements: Vec<NodeId> = nodes[node].elements().unwrap_or(&[]).to_vec();
        let element_count = elements.len();
        let mut element_types: Vec<TypeId> = vec![self.error_type; element_count];
        let mut element_infos: Vec<TupleElementInfo> =
            vec![TupleElementInfo::default(); element_count];
        self.push_cached_contextual_type(node);
        let in_destructuring_pattern = ast::is_assignment_target(node, &nodes);
        let in_const_context = self.is_const_context(node);
        let contextual_type = self.get_apparent_type_of_contextual_type(node, ContextFlags::NONE);
        let in_tuple_context = is_spread_into_call_or_new(node, &nodes)
            || contextual_type.is_some_and(|ct| {
                crate::checker_d::some_type(self, ct, |c: &mut Checker, t: TypeId| {
                    c.is_tuple_like_type(t)
                        || c.is_generic_mapped_type(t)
                            && c.types.get_ref(t).as_mapped_type().name_type.is_none()
                            && {
                                let __arena___guard_target = c.types.clone();
                                let __guard_target = __arena___guard_target.get(t).clone();
                                let target = __guard_target
                                    .as_mapped_type()
                                    .object_type
                                    .target
                                    .unwrap_or(t);
                                c.get_homomorphic_type_variable(target).is_some()
                            }
                })
            });
        let mut has_omitted_expression = false;
        for (i, &e) in elements.iter().enumerate() {
            if ast::is_spread_element(&nodes[e]) {
                let expr = nodes[e].expression().expect("spread element expression");
                let spread_type = self.check_expression_ex(expr, check_mode);
                if self.is_array_like_type(spread_type) {
                    element_types[i] = spread_type;
                    element_infos[i] = TupleElementInfo {
                        flags: ElementFlags::VARIADIC,
                        ..Default::default()
                    };
                } else if in_destructuring_pattern {
                    // Given the following situation:
                    //    var c: {};
                    //    [...c] = ["", 0];
                    //
                    // c is represented in the tree as a spread element in an
                    // array literal. But c really functions as a rest element,
                    // and its purpose is to provide a contextual type for the
                    // right hand side of the assignment. Therefore, instead of
                    // calling checkExpression on "...c", which will give an
                    // error if c is not iterable/array-like, we need to act as
                    // if we are trying to get the contextual element type from
                    // it. So we do something similar to
                    // getContextualTypeForElementExpression, which will
                    // crucially not error if there is no index type / iterated
                    // type.
                    let mut rest_element_type =
                        self.get_index_type_of_type(spread_type, self.number_type);
                    if rest_element_type.is_none() {
                        rest_element_type = self.get_iterated_type_or_element_type(
                            IterationUse::DESTRUCTURING,
                            spread_type,
                            self.undefined_type,
                            None,  // errorNode
                            false, // checkAssignability
                        );
                        if rest_element_type.is_none() {
                            rest_element_type = Some(self.unknown_type);
                        }
                    }
                    element_types[i] = rest_element_type.unwrap();
                    element_infos[i] = TupleElementInfo {
                        flags: ElementFlags::REST,
                        ..Default::default()
                    };
                } else {
                    element_types[i] = self.check_iterated_type_or_element_type(
                        IterationUse::SPREAD,
                        spread_type,
                        self.undefined_type,
                        Some(expr),
                    );
                    element_infos[i] = TupleElementInfo {
                        flags: ElementFlags::REST,
                        ..Default::default()
                    };
                }
            } else if self.exact_optional_property_types && ast::is_omitted_expression(&nodes[e]) {
                has_omitted_expression = true;
                element_types[i] = self.undefined_or_missing_type;
                element_infos[i] = TupleElementInfo {
                    flags: ElementFlags::OPTIONAL,
                    ..Default::default()
                };
            } else {
                let t = self.check_expression_for_mutable_location(e, check_mode);
                element_types[i] =
                    self.add_optionality_ex(t, true /*isProperty*/, has_omitted_expression);
                element_infos[i] = TupleElementInfo {
                    flags: if has_omitted_expression {
                        ElementFlags::OPTIONAL
                    } else {
                        ElementFlags::REQUIRED
                    },
                    ..Default::default()
                };
                if in_tuple_context
                    && check_mode.intersects(CheckMode::INFERENTIAL)
                    && !check_mode.intersects(CheckMode::SKIP_CONTEXT_SENSITIVE)
                    && self.is_context_sensitive(e)
                {
                    let inference_context = self.get_inference_context(node);
                    // In CheckMode.Inferential we should always have an
                    // inference context.
                    self.add_intra_expression_inference_site(inference_context, e, t);
                }
            }
        }
        self.pop_contextual_type();
        if in_destructuring_pattern {
            return self.create_tuple_type_ex(&element_types, &element_infos, false);
        }
        if check_mode.intersects(CheckMode::FORCE_TUPLE) || in_const_context || in_tuple_context {
            let readonly = in_const_context
                && !contextual_type.is_some_and(|ct| {
                    crate::checker_d::some_type(self, ct, |c: &mut Checker, t: TypeId| {
                        c.is_mutable_array_like_type(t)
                    })
                });
            let tuple_type = self.create_tuple_type_ex(&element_types, &element_infos, readonly);
            return self.create_array_literal_type(tuple_type);
        }
        let element_type: TypeId;
        if !element_types.is_empty() {
            let mut element_types = element_types;
            for i in 0..element_types.len() {
                let e = element_types[i];
                if element_infos[i].flags.intersects(ElementFlags::VARIADIC) {
                    let replacement = self
                        .get_indexed_access_type_or_undefined(
                            e,
                            self.number_type,
                            AccessFlags::NONE,
                            None,
                            None,
                        )
                        .unwrap_or(self.any_type);
                    element_types[i] = replacement;
                }
            }
            element_type =
                self.get_union_type_ex(&element_types, UnionReduction::Subtype, None, None);
        } else {
            element_type = if self.strict_null_checks {
                self.implicit_never_type
            } else {
                self.undefined_widening_type
            };
        }
        let array_type = self.create_array_type_ex(element_type, in_const_context);
        self.create_array_literal_type(array_type)
    }

    /// `createArrayLiteralType` (checker.go:8305).
    pub(crate) fn create_array_literal_type(&mut self, t: TypeId) -> TypeId {
        if !self
            .types_handle()
            .get_ref(t)
            .object_flags
            .intersects(ObjectFlags::REFERENCE)
        {
            return t;
        }
        let key = CachedTypeKey {
            kind: CachedTypeKind::ArrayLiteralType,
            type_id: self.types.get_ref(t).id,
        };
        if let Some(&cached) = self.cached_types.get(&key) {
            return cached;
        }
        let literal_type = self.clone_type_reference(t);
        self.types_handle()
            .get_mut(literal_type)
            .object_flags
            .insert(ObjectFlags::ARRAY_LITERAL | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL);
        self.cached_types.insert(key, literal_type);
        literal_type
    }

    /// `checkQualifiedName` (checker.go:8324).
    pub(crate) fn check_qualified_name(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let left = nodes[node]
            .as_qualified_name()
            .left
            .expect("qualified name left");
        let right = nodes[node]
            .as_qualified_name()
            .right
            .expect("qualified name right");
        let left_type =
            if ast::is_part_of_type_query(node, &nodes) && ast::is_this_identifier(&nodes[left]) {
                let this_type = self.check_this_expression(left);
                self.check_non_null_type(this_type, left)
            } else {
                self.check_non_null_expression(left)
            };
        self.check_property_access_expression_or_qualified_name(
            node, left, left_type, right, check_mode, false,
        )
    }

    /// `checkIndexedAccess` (checker.go:8335).
    pub(crate) fn check_indexed_access(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node].flags.intersects(ast::NodeFlags::OPTIONAL_CHAIN) {
            return self.check_element_access_chain(node, check_mode);
        }
        let expr = nodes[node].expression().expect("indexed access expression");
        let expr_type = self.check_non_null_expression(expr);
        self.check_element_access_expression(node, expr_type, check_mode)
    }

    /// `checkElementAccessChain` (checker.go:8342).
    pub(crate) fn check_element_access_chain(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expr = nodes[node]
            .expression()
            .expect("element access chain expression");
        let expr_type = self.check_expression(expr);
        let non_optional_type = self.get_optional_expression_type(expr_type, expr);
        let object_type = self.check_non_null_type(non_optional_type, expr);
        let access_type = self.check_element_access_expression(node, object_type, check_mode);
        self.propagate_optional_type_marker(access_type, node, non_optional_type != expr_type)
    }

    /// `checkElementAccessExpression` (checker.go:8348).
    pub(crate) fn check_element_access_expression(
        &mut self,
        node: NodeId,
        expr_type: TypeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut object_type = expr_type;
        if crate::utilities::get_assignment_target_kind(node, &nodes)
            != crate::utilities::AssignmentKind::NONE
            || self.is_method_access_for_call(node)
        {
            object_type = self.get_widened_type(object_type);
        }
        let index_expression = nodes[node]
            .as_element_access_expression()
            .argument_expression
            .expect("element access argument expression");
        let index_type = self.check_expression(index_expression);
        if self.is_error_type(object_type) || object_type == self.silent_never_type {
            return object_type;
        }
        if crate::checker_d::is_const_enum_object_type(self, object_type)
            && !ast::is_string_literal_like(&nodes[index_expression])
        {
            self.error(
                Some(index_expression),
                &tsc_diagnostics::A_const_enum_member_can_only_be_accessed_using_a_string_literal,
                &[],
            );
            return self.error_type;
        }
        let mut effective_index_type = index_type;
        if self.is_for_in_variable_for_numeric_property_names(index_expression) {
            effective_index_type = self.number_type;
        }
        let assignment_target_kind = crate::utilities::get_assignment_target_kind(node, &nodes);
        let access_flags = if assignment_target_kind == crate::utilities::AssignmentKind::NONE {
            AccessFlags::EXPRESSION_POSITION
        } else {
            AccessFlags::WRITING
                | if assignment_target_kind == crate::utilities::AssignmentKind::COMPOUND {
                    AccessFlags::EXPRESSION_POSITION
                } else {
                    AccessFlags::NONE
                }
                | if self.is_generic_object_type(object_type)
                    && !crate::utilities::is_this_type_parameter(&self.types, object_type)
                {
                    AccessFlags::NO_INDEX_SIGNATURES
                } else {
                    AccessFlags::NONE
                }
        };
        let indexed_access_type = self
            .get_indexed_access_type_or_undefined(
                object_type,
                effective_index_type,
                access_flags,
                Some(node),
                None,
            )
            .unwrap_or(self.error_type);
        let resolved_symbol = self.get_resolved_symbol_or_nil(node);
        let flow_type = self.get_flow_type_of_access_expression(
            node,
            resolved_symbol,
            Some(indexed_access_type),
            index_expression,
            check_mode,
        );
        self.check_indexed_access_index_type(flow_type, node)
    }

    /// `isForInVariableForNumericPropertyNames` (checker.go:8381).
    pub(crate) fn is_for_in_variable_for_numeric_property_names(&mut self, expr: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((expr).file_index());
        let e = ast::skip_parentheses(expr, &nodes);
        if ast::is_identifier(&nodes[e]) {
            let symbol = self.get_resolved_symbol(e);
            if self.symbol_arena.borrow()[symbol.index()]
                .flags
                .intersects(ast::SymbolFlags::VARIABLE)
            {
                let mut child = expr;
                let mut node = nodes[expr].parent;
                while let Some(n) = node {
                    if ast::is_for_in_statement(&nodes[n])
                        && Some(child) == nodes[n].as_for_in_or_of_statement().statement
                        && self.get_for_in_variable_symbol(n) == Some(symbol)
                        && {
                            let expr_type = self.get_type_of_expression(
                                nodes[n].expression().expect("for-in expression"),
                            );
                            self.has_numeric_property_names(expr_type)
                        }
                    {
                        return true;
                    }
                    child = n;
                    node = nodes[n].parent;
                }
            }
        }
        false
    }

    /// `getForInVariableSymbol` (checker.go:8401).
    pub(crate) fn get_for_in_variable_symbol(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let initializer = nodes[node].initializer();
        if let Some(initializer) = initializer {
            if ast::is_variable_declaration_list(&nodes[initializer]) {
                let declarations: Vec<NodeId> = nodes[initializer]
                    .as_variable_declaration_list()
                    .declarations
                    .as_ref()
                    .map(|l| l.nodes.to_vec())
                    .unwrap_or_default();
                if !declarations.is_empty() {
                    let variable = declarations[0];
                    let name = nodes[variable].name().expect("variable name");
                    if !ast::is_binding_pattern(&nodes[name]) {
                        return self.get_symbol_of_declaration(variable);
                    }
                }
            } else if ast::is_identifier(&nodes[initializer]) {
                return Some(self.get_resolved_symbol(initializer));
            }
        }
        None
    }

    /// `hasNumericPropertyNames` (checker.go:8418).
    pub(crate) fn has_numeric_property_names(&mut self, t: TypeId) -> bool {
        self.get_index_infos_of_type(t).len() == 1
            && self.get_index_info_of_type(t, self.number_type).is_some()
    }

    /// `checkIndexedAccessIndexType` (checker.go:8422).
    pub(crate) fn check_indexed_access_index_type(
        &mut self,
        t: TypeId,
        access_node: NodeId,
    ) -> TypeId {
        if !self
            .types_handle()
            .get_ref(t)
            .flags
            .intersects(TypeFlags::INDEXED_ACCESS)
        {
            return t;
        }
        // Check if the index type is assignable to 'keyof T' for the object
        // type.
        let (object_type, index_type) = {
            let ty = self.types.get_ref(t);
            let ia = ty.as_indexed_access_type();
            (
                ia.object_type.expect("indexed access object type"),
                ia.index_type.expect("indexed access index type"),
            )
        };
        // skip index type deferral on remapping mapped types
        let object_index_type = if self.is_generic_mapped_type(object_type)
            && self.get_mapped_type_name_type_kind(object_type) == MappedTypeNameTypeKind::Remapping
        {
            self.get_index_type_for_mapped_type(object_type, IndexFlags::NONE)
        } else {
            self.get_index_type_ex(object_type, IndexFlags::NONE)
        };
        let has_number_index_info = self
            .get_index_info_of_type(object_type, self.number_type)
            .is_some();
        if crate::checker_d::every_type(self, index_type, |c: &mut Checker, t: TypeId| {
            c.is_type_assignable_to(t, object_index_type)
                || has_number_index_info && c.is_applicable_index_type(t, c.number_type)
        }) {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((access_node).file_index());
            if nodes[access_node].kind == ast::Kind::ElementAccessExpression
                && ast::is_assignment_target(access_node, &nodes)
                && self
                    .types_handle()
                    .get(object_type)
                    .object_flags
                    .intersects(ObjectFlags::MAPPED)
                && crate::checker_d::get_mapped_type_modifiers(self, object_type)
                    .intersects(MappedTypeModifiers::INCLUDE_READONLY)
            {
                let arg = self.type_to_string(object_type);
                self.error(
                    Some(access_node),
                    &tsc_diagnostics::Index_signature_in_type_0_only_permits_reading,
                    &[arg],
                );
            }
            return t;
        }
        if self.is_generic_object_type(object_type) {
            let property_name = self.get_property_name_from_index(index_type, Some(access_node));
            if property_name != ast::INTERNAL_SYMBOL_NAME_MISSING {
                let property_symbol = self.get_constituent_property(object_type, &property_name);
                if let Some(property_symbol) = property_symbol {
                    let modifier_flags =
                        crate::utilities::get_declaration_modifier_flags_from_symbol(
                            self,
                            property_symbol,
                        );
                    if modifier_flags
                        .intersects(ast::ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER)
                    {
                        self.error(
                            Some(access_node),
                            &tsc_diagnostics::Private_or_protected_member_0_cannot_be_accessed_on_a_type_parameter,
                            &[property_name],
                        );
                        return self.error_type;
                    }
                }
            }
        }
        let arg1 = self.type_to_string(index_type);
        let arg2 = self.type_to_string(object_type);
        self.error(
            Some(access_node),
            &tsc_diagnostics::Type_0_cannot_be_used_to_index_type_1,
            &[arg1, arg2],
        );
        self.error_type
    }

    /// `getConstituentProperty` (checker.go:8459).
    pub(crate) fn get_constituent_property(
        &mut self,
        object_type: TypeId,
        property_name: &str,
    ) -> Option<SymbolId> {
        let apparent = self.get_apparent_type(object_type);
        let distributed = self.types.get_ref(apparent).distributed(apparent);
        for t in distributed {
            if let Some(prop) = self.get_property_of_type(t, property_name) {
                return Some(prop);
            }
        }
        None
    }

    /// `checkImportCallExpression` (checker.go:8469).
    pub(crate) fn check_import_call_expression(&mut self, node: NodeId) -> TypeId {
        // Check grammar of dynamic import
        self.check_grammar_import_call_expression(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let args: Vec<NodeId> = nodes[node].arguments().unwrap_or(&[]).to_vec();
        if args.is_empty() {
            // No call arguments exist, so there are no child expressions to
            // check.
            return self.create_promise_return_type(node, self.any_type);
        }
        let specifier = args[0];
        let specifier_type = self.check_expression_cached(specifier);
        let mut options_type: Option<TypeId> = None;
        if args.len() > 1 {
            options_type = Some(self.check_expression_cached(args[1]));
        }
        // Even though multiple arguments is grammatically incorrect,
        // type-check extra arguments for completion
        for &arg in args.iter().skip(2) {
            self.check_expression_cached(arg);
        }
        if self
            .types_handle()
            .get(specifier_type)
            .flags
            .intersects(TypeFlags::NULLABLE)
            || !self.is_type_assignable_to(specifier_type, self.string_type)
        {
            let arg = self.type_to_string(specifier_type);
            self.error(
                Some(specifier),
                &tsc_diagnostics::Dynamic_import_s_specifier_must_be_of_type_string_but_here_has_type_0,
                &[arg],
            );
        }
        let mut import_attributes_type: Option<TypeId> = None;
        if let Some(options_type) = options_type {
            let import_call_options_type = {
                let thunk = self
                    .get_global_import_call_options_type_checked
                    .clone()
                    .expect("getGlobalImportCallOptionsTypeChecked");
                thunk(self)
            };
            if import_call_options_type != self.empty_object_type {
                let nullable =
                    self.get_nullable_type(import_call_options_type, TypeFlags::UNDEFINED);
                self.check_type_assignable_to(options_type, nullable, Some(args[1]), None);
            }
            if ast::is_object_literal_expression(&nodes[args[1]]) {
                let properties: Vec<NodeId> = nodes[args[1]]
                    .as_object_literal_expression()
                    .properties
                    .as_ref()
                    .expect("properties")
                    .nodes
                    .to_vec();
                for prop in properties {
                    let name = nodes[prop].name();
                    if ast::is_property_assignment(&nodes[prop])
                        && name.is_some_and(|n| {
                            ast::is_identifier(&nodes[n]) && &*nodes[n].text(&nodes) == "assert"
                        })
                    {
                        self.error(
                            name,
                            &tsc_diagnostics::Import_assertions_have_been_replaced_by_import_attributes_Use_with_instead_of_assert,
                            &[],
                        );
                        break;
                    }
                }
            }
            import_attributes_type = self.get_type_of_property_of_type(options_type, "with");
        }
        if ast::is_source_phase_import_call(&nodes[node], &nodes) {
            let t = {
                let thunk = self
                    .get_global_abstract_module_source_type
                    .clone()
                    .expect("getGlobalAbstractModuleSourceType");
                thunk(self)
            };
            return self.create_promise_return_type(node, t);
        }
        // resolveExternalModuleName will return undefined if the
        // moduleReferenceExpression is not a string literal
        if let Some(module_symbol) = self.resolve_external_module_name(
            node,
            Some(specifier),
            false, /*ignoreErrors*/
            import_attributes_type,
        ) {
            if let Some(es_module_symbol) = self
                .resolve_external_module_symbol(Some(module_symbol), true /*dontResolveAlias*/)
            {
                let es_type = self.get_type_of_symbol(es_module_symbol);
                let mut synthetic_type = self.get_type_with_synthetic_default_only(
                    es_type,
                    es_module_symbol,
                    Some(module_symbol),
                    specifier,
                    import_attributes_type,
                );
                if synthetic_type.is_none() {
                    let es_type = self.get_type_of_symbol(es_module_symbol);
                    synthetic_type = Some(self.get_type_with_synthetic_default_import_type(
                        es_type,
                        es_module_symbol,
                        Some(module_symbol),
                        specifier,
                    ));
                }
                return self.create_promise_return_type(node, synthetic_type.unwrap());
            }
        }
        self.create_promise_return_type(node, self.any_type)
    }

    /// `checkCallExpression` (checker.go:8529).
    pub(crate) fn check_call_expression(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let type_argument_list = nodes[node].type_argument_list();
        self.check_grammar_type_arguments(node, type_argument_list);
        let signature =
            self.get_resolved_signature(node, None /*candidatesOutArray*/, check_mode);
        if signature == Some(self.resolving_signature) {
            // CheckMode.SkipGenericFunctions is enabled and this is a call to
            // a generic function that returns a function type. We defer
            // checking and return silentNeverType.
            return self.silent_never_type;
        }
        let signature = signature.expect("getResolvedSignature: nil signature");
        self.check_deprecated_signature(signature, node);
        if nodes[node]
            .expression()
            .is_some_and(|e| nodes[e].kind == ast::Kind::SuperKeyword)
        {
            return self.void_type;
        }
        if ast::is_new_expression(&nodes[node]) {
            let declaration = self.signature_arena.get(signature).declaration;
            if declaration.is_some_and(|d| {
                let __program = self.program.clone().expect("program");
                let decl_nodes = __program.nodes((d).file_index());
                !ast::is_constructor_declaration(&decl_nodes[d])
                    && !ast::is_construct_signature_declaration(&decl_nodes[d])
                    && !ast::is_constructor_type_node(&decl_nodes[d])
            }) {
                // When resolved signature is a call signature (and not a
                // construct signature) the result type is any
                if self.no_implicit_any {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::X_new_expression_whose_target_lacks_a_construct_signature_implicitly_has_an_any_type,
                        &[],
                    );
                }
                return self.any_type;
            }
        }
        if ast::is_in_js_file(Some(node), &nodes) && self.is_common_js_require(node) {
            let arg0 = nodes[node].arguments().expect("require arguments")[0];
            return self.resolve_external_module_type_by_literal(arg0);
        }
        let return_type = self.get_return_type_of_signature(signature);
        // Treat any call to the global 'Symbol' function that is part of a
        // const variable or readonly property as a fresh unique symbol
        // literal type.
        if self
            .types_handle()
            .get(return_type)
            .flags
            .intersects(TypeFlags::ES_SYMBOL_LIKE)
            && self.is_symbol_or_symbol_for_call(node)
        {
            let target = ast::walk_up_parenthesized_expressions(
                nodes[node].parent.expect("call parent"),
                &nodes,
            )
            .expect("walkUpParenthesizedExpressions");
            return self.get_es_symbol_like_type_for_node(target);
        }
        if ast::is_call_expression(&nodes[node])
            && nodes[node].question_dot_token().is_none()
            && nodes[node]
                .parent
                .is_some_and(|p| ast::is_expression_statement(&nodes[p]))
            && self
                .types_handle()
                .get(return_type)
                .flags
                .intersects(TypeFlags::VOID)
            && self.get_type_predicate_of_signature(signature).is_some()
        {
            let expr = nodes[node].expression().expect("call expression");
            if !ast::is_dotted_name(&nodes[expr], &nodes) {
                self.error(
                    Some(expr),
                    &tsc_diagnostics::Assertions_require_the_call_target_to_be_an_identifier_or_qualified_name,
                    &[],
                );
            } else if self.get_effects_signature(node).is_none() {
                let diagnostic = self.error(
                    Some(expr),
                    &tsc_diagnostics::Assertions_require_every_name_in_the_call_target_to_be_declared_with_an_explicit_type_annotation,
                    &[],
                );
                self.get_type_of_dotted_name(expr, diagnostic);
            }
        }
        return_type
    }

    /// `checkDeprecatedSignature` (checker.go:8571).
    pub(crate) fn check_deprecated_signature(&mut self, sig: SignatureId, node: NodeId) {
        let declaration = {
            let s = self.signature_arena.get(sig);
            if s.flags
                .intersects(SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE)
            {
                return;
            }
            s.declaration
        };
        if let Some(declaration) = declaration {
            if self.is_deprecated_declaration(declaration) {
                let suggestion_node = self.get_deprecated_suggestion_node(node);
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((node).file_index());
                let invoked =
                    ast::get_invoked_expression(&nodes[node], &nodes).expect("invoked expression");
                let name = crate::utilities::try_get_property_access_or_identifier_to_string(
                    invoked, &nodes,
                );
                let signature_string = self.signature_to_string(sig);
                self.add_deprecated_suggestion_with_signature(
                    Some(suggestion_node),
                    declaration,
                    &name,
                    &signature_string,
                );
            }
        }
    }

    /// `addDeprecatedSuggestionWithSignature` (checker.go:8582).
    pub(crate) fn add_deprecated_suggestion_with_signature(
        &mut self,
        location: Option<NodeId>,
        declaration: NodeId,
        deprecated_entity: &str,
        signature_string: &str,
    ) -> DiagnosticRef {
        let message = if !deprecated_entity.is_empty() {
            &tsc_diagnostics::The_signature_0_of_1_is_deprecated
        } else {
            &tsc_diagnostics::X_0_is_deprecated
        };
        let diagnostic = self.new_diagnostic_for_node(
            location,
            message,
            &[signature_string.to_string(), deprecated_entity.to_string()],
        );
        self.add_deprecated_suggestion_worker(&[declaration], &diagnostic)
    }

    /// `isSymbolOrSymbolForCall` (checker.go:8588).
    pub(crate) fn is_symbol_or_symbol_for_call(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_call_expression(&nodes[node]) {
            return false;
        }
        let mut left = nodes[node].expression().expect("call expression");
        if ast::is_property_access_expression(&nodes[left])
            && nodes[left]
                .name()
                .is_some_and(|n| &*nodes[n].text(&nodes) == "for")
        {
            left = nodes[left]
                .expression()
                .expect("property access expression");
        }
        if !ast::is_identifier(&nodes[left]) || &*nodes[left].text(&nodes) != "Symbol" {
            return false;
        }
        // make sure `Symbol` is the global symbol
        let global_es_symbol = {
            let thunk = self
                .get_global_es_symbol_constructor_symbol_or_nil
                .clone()
                .expect("getGlobalESSymbolConstructorSymbolOrNil");
            thunk(self)
        };
        if global_es_symbol.is_none() {
            return false;
        }
        let resolved = {
            let thunk = self.resolve_name.clone().expect("resolveName");
            thunk(
                self,
                Some(left),
                "Symbol",
                ast::SymbolFlags::VALUE,
                None,  // nameNotFoundMessage
                false, // isUse
                false,
            )
        };
        global_es_symbol == resolved
    }
}

/// `isSpreadIntoCallOrNew` (checker.go:8319).
pub(crate) fn is_spread_into_call_or_new(node: NodeId, nodes: &[ast::Node]) -> bool {
    let parent = ast::walk_up_parenthesized_expressions(
        nodes[node]
            .parent
            .expect("isSpreadIntoCallOrNew: nil parent"),
        nodes,
    )
    .expect("isSpreadIntoCallOrNew: nil parent");
    ast::is_spread_element(&nodes[parent])
        && nodes[parent]
            .parent
            .is_some_and(|p| ast::is_call_or_new_expression(&nodes[p]))
}

impl Checker {
    /// `getResolvedSignature` (checker.go:8614).
    ///
    /// Go returns `*Signature`; `nil` is reachable when
    /// `runWithoutResolvedSignatureCaching` cleared
    /// `links.resolvedSignature`, so the port returns `Option`.
    pub(crate) fn get_resolved_signature(
        &mut self,
        node: NodeId,
        candidates_out_array: Option<&mut Vec<SignatureId>>,
        check_mode: CheckMode,
    ) -> Option<SignatureId> {
        // If getResolvedSignature has already been called, we will have
        // cached the resolvedSignature. However, it is possible that either
        // candidatesOutArray was not passed in the first time, or that a
        // different candidatesOutArray was passed in. Therefore, we need to
        // redo the work to correctly fill the candidatesOutArray.
        let cached = self.signature_links.get(node).resolved_signature;
        if cached.is_some()
            && cached != Some(self.resolving_signature)
            && candidates_out_array.is_none()
        {
            return cached;
        }
        let save_resolution_start = self.resolution_start;
        if cached.is_none() {
            // If we haven't already done so, temporarily reset the
            // resolution stack. This allows us to handle "inverted"
            // situations where, for example, an API client asks for the type
            // of a symbol containined in a function call argument whose
            // contextual type depends on the symbol itself through
            // resolution of the containing function call. By resetting the
            // resolution stack we'll retry the symbol type resolution with
            // the resolvingSignature marker in place to suppress the
            // contextual type circularity.
            self.resolution_start = self.type_resolutions.len() as i32;
        }
        self.signature_links.get(node).resolved_signature = Some(self.resolving_signature);
        let _has_candidates_out_array = candidates_out_array.is_some();
        let result = self.resolve_signature(node, candidates_out_array, check_mode);
        self.resolution_start = save_resolution_start;
        // When CheckMode.SkipGenericFunctions is set we use
        // resolvingSignature to indicate that call resolution should be
        // deferred.
        if result != self.resolving_signature {
            // if the signature resolution originated on a node that itself
            // depends on the contextual type then it's possible that the
            // resolved signature might not be the same as the one that would
            // be computed in source order since resolving such signature
            // leads to resolving the potential outer signature, its
            // arguments and thus the very same signature it's possible that
            // this inner resolution sets the resolvedSignature first.
            // In such a case we ignore the local result and reuse the
            // correct one that was cached.
            let links_signature = self.signature_links.get(node).resolved_signature;
            if links_signature != Some(self.resolving_signature) {
                return links_signature;
            }
            // If signature resolution originated in control flow type
            // analysis (for example to compute the assigned type in a flow
            // assignment) we don't cache the result as it may be based on
            // temporary types from the control flow analysis.
            if self.flow_loop_stack.is_empty() {
                self.signature_links.get(node).resolved_signature = Some(result);
            } else {
                self.signature_links.get(node).resolved_signature = cached;
            }
        }
        Some(result)
    }

    /// `resolveSignature` (checker.go:8660).
    pub(crate) fn resolve_signature(
        &mut self,
        node: NodeId,
        candidates_out_array: Option<&mut Vec<SignatureId>>,
        check_mode: CheckMode,
    ) -> SignatureId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::CallExpression => {
                self.resolve_call_expression(node, candidates_out_array, check_mode)
            }
            ast::Kind::NewExpression => {
                self.resolve_new_expression(node, candidates_out_array, check_mode)
            }
            ast::Kind::TaggedTemplateExpression => {
                self.resolve_tagged_template_expression(node, candidates_out_array, check_mode)
            }
            ast::Kind::Decorator => self.resolve_decorator(node, candidates_out_array, check_mode),
            ast::Kind::JsxOpeningFragment
            | ast::Kind::JsxOpeningElement
            | ast::Kind::JsxSelfClosingElement => {
                self.resolve_jsx_opening_like_element(node, candidates_out_array, check_mode)
            }
            ast::Kind::BinaryExpression => {
                self.resolve_instanceof_expression(node, candidates_out_array, check_mode)
            }
            _ => panic!("Unhandled case in resolveSignature"),
        }
    }

    /// `resolveCallExpression` (checker.go:8678).
    pub(crate) fn resolve_call_expression(
        &mut self,
        node: NodeId,
        candidates_out_array: Option<&mut Vec<SignatureId>>,
        check_mode: CheckMode,
    ) -> SignatureId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expression = nodes[node].expression().expect("call expression");
        if nodes[expression].kind == ast::Kind::SuperKeyword {
            let super_type = self.check_super_expression(expression);
            if crate::utilities::is_type_any(&self.types, super_type) {
                let args: Vec<NodeId> = nodes[node].arguments().unwrap_or(&[]).to_vec();
                for arg in args {
                    // Still visit arguments so they get marked for
                    // visibility, etc.
                    self.check_expression(arg);
                }
                return self.any_signature;
            }
            if !self.is_error_type(super_type) {
                // In super call, the candidate signatures are the matching
                // arity signatures of the base constructor function
                // instantiated with the type arguments specified in the
                // extends clause.
                let containing_class = ast::get_containing_class(node, &nodes);
                let base_type_node = containing_class
                    .and_then(|cc| ast::get_class_extends_heritage_element(&nodes[cc], &nodes));
                if let Some(base_type_node) = base_type_node {
                    let type_arguments: Vec<NodeId> = nodes[base_type_node]
                        .type_arguments()
                        .unwrap_or(&[])
                        .to_vec();
                    let base_constructors = self.get_instantiated_constructors_for_type_arguments(
                        super_type,
                        &type_arguments,
                        base_type_node,
                    );
                    return self.resolve_call(
                        node,
                        base_constructors,
                        candidates_out_array,
                        check_mode,
                        SignatureFlags::NONE,
                        None,
                    );
                }
            }
            return self.resolve_untyped_call(node);
        }
        if ast::is_import_call(&nodes[node], &nodes) {
            return self.resolve_untyped_call(node);
        }
        let mut func_type = self.check_expression(expression);
        let call_chain_flags;
        if crate::utilities::is_call_chain(&nodes[node]) {
            let non_optional_type = self.get_optional_expression_type(func_type, expression);
            if non_optional_type == func_type {
                call_chain_flags = SignatureFlags::NONE;
            } else if ast::is_outermost_optional_chain(&nodes[node], &nodes) {
                call_chain_flags = SignatureFlags::IS_OUTER_CALL_CHAIN;
            } else {
                call_chain_flags = SignatureFlags::IS_INNER_CALL_CHAIN;
            }
            func_type = non_optional_type;
        } else {
            call_chain_flags = SignatureFlags::NONE;
        }
        func_type = self.check_non_null_type_with_reporter(
            func_type,
            expression,
            Self::report_cannot_invoke_possibly_null_or_undefined_error,
        );
        if func_type == self.silent_never_type {
            return self.silent_never_signature;
        }
        let apparent_type = self.get_apparent_type(func_type);
        if self.is_error_type(apparent_type) {
            // Another error has already been reported
            return self.resolve_error_call(node);
        }
        // Technically, this signatures list may be incomplete. We are taking
        // the apparent type, but we are not including call signatures that
        // may have been added to the Object or Function interface, since
        // they have none by default. This is a bit of a leap of faith that
        // the user will not add any.
        let call_signatures = self.get_signatures_of_type(apparent_type, SignatureKind::Call);
        let num_construct_signatures = self
            .get_signatures_of_type(apparent_type, SignatureKind::Construct)
            .len() as i32;
        // TS 1.0 Spec: 4.12
        // In an untyped function call no TypeArgs are permitted, Args can be
        // any argument list, no contextual types are provided for the
        // argument expressions, and the result is always of type Any.
        if self.is_untyped_function_call(
            func_type,
            apparent_type,
            call_signatures.len() as i32,
            num_construct_signatures,
        ) {
            // The unknownType indicates that an error already occurred (and
            // was reported). No need to report another error in this case.
            if !self.is_error_type(func_type) && nodes[node].type_arguments().is_some() {
                self.error(
                    Some(node),
                    &tsc_diagnostics::Untyped_function_calls_may_not_accept_type_arguments,
                    &[],
                );
            }
            return self.resolve_untyped_call(node);
        }
        // If FuncExpr's apparent type(section 3.8.1) is a function type, the
        // call is a typed function call. TypeScript employs overload
        // resolution in typed function calls in order to support functions
        // with multiple call signatures.
        if call_signatures.is_empty() {
            if num_construct_signatures != 0 {
                let arg = self.type_to_string(func_type);
                self.error(
                    Some(node),
                    &tsc_diagnostics::Value_of_type_0_is_not_callable_Did_you_mean_to_include_new,
                    &[arg],
                );
            } else {
                let mut related_information: Option<DiagnosticRef> = None;
                if nodes[node].arguments().is_some_and(|a| a.len() == 1) {
                    let source_file = ast::get_source_file_of_node(Some(node), &nodes)
                        .expect("resolveCallExpression: no source file");
                    let text = nodes[source_file].as_source_file().text().to_string();
                    let options = tsc_scanner::scanner::SkipTriviaOptions {
                        stop_after_line_break: true,
                        ..Default::default()
                    };
                    let pos = tsc_scanner::scanner::skip_trivia_ex(
                        &text,
                        nodes[expression].end(),
                        Some(&options),
                    ) - 1;
                    if tsc_stringutil::is_line_break(text.as_bytes()[pos as usize] as char) {
                        related_information = Some(self.new_diagnostic_for_node(
                            Some(expression),
                            &tsc_diagnostics::Are_you_missing_a_semicolon,
                            &[] as &[String],
                        ));
                    }
                }
                self.invocation_error(
                    expression,
                    apparent_type,
                    SignatureKind::Call,
                    related_information,
                );
            }
            return self.resolve_error_call(node);
        }
        // When a call to a generic function is an argument to an outer call
        // to a generic function for which inference is in process, we have a
        // choice to make. If the inner call relies on inferences made from
        // its contextual type to its return type, deferring the inner call
        // processing allows the best possible contextual type to accumulate.
        // But if the outer call relies on inferences made from the return
        // type of the inner call, the inner call should be processed early.
        // There's no sure way to know which choice is right (only a full
        // unification algorithm can determine that), so we resort to the
        // following heuristic: If no type arguments are specified in the
        // inner call and at least one call signature is generic and returns
        // a function type, we choose to defer processing. This narrowly
        // permits function composition operators to flow inferences through
        // return types, but otherwise processes calls right away. We use the
        // resolvingSignature singleton to indicate that we deferred
        // processing. This result will be propagated out and eventually
        // turned into silentNeverType (a type that is assignable to anything
        // and from which we never make inferences).
        if check_mode.intersects(CheckMode::SKIP_GENERIC_FUNCTIONS)
            && nodes[node].type_arguments().map_or(0, |a| a.len()) == 0
            && call_signatures
                .iter()
                .any(|&s| self.is_generic_function_returning_function(s))
        {
            self.skipped_generic_function(node, check_mode);
            return self.resolving_signature;
        }
        self.resolve_call(
            node,
            call_signatures,
            candidates_out_array,
            check_mode,
            call_chain_flags,
            None,
        )
    }

    /// `resolveNewExpression` (checker.go:8782).
    pub(crate) fn resolve_new_expression(
        &mut self,
        node: NodeId,
        candidates_out_array: Option<&mut Vec<SignatureId>>,
        check_mode: CheckMode,
    ) -> SignatureId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expression = nodes[node].expression().expect("new expression");
        let mut expression_type = self.check_non_null_expression(expression);
        if expression_type == self.silent_never_type {
            return self.silent_never_signature;
        }
        // If expressionType's apparent type(section 3.8.1) is an object type
        // with one or more construct signatures, the expression is processed
        // in the same manner as a function call, but using the construct
        // signatures as the initial set of candidate signatures for overload
        // resolution. The result type of the function call becomes the
        // result type of the operation.
        expression_type = self.get_apparent_type(expression_type);
        if self.is_error_type(expression_type) {
            // Another error has already been reported
            return self.resolve_error_call(node);
        }
        // TS 1.0 spec: 4.11
        // If expressionType is of type Any, Args can be any argument list
        // and the result of the operation is of type Any.
        if crate::utilities::is_type_any(&self.types, expression_type) {
            if !nodes[node].type_arguments().map_or(true, |a| a.is_empty()) {
                self.error(
                    Some(node),
                    &tsc_diagnostics::Untyped_function_calls_may_not_accept_type_arguments,
                    &[],
                );
            }
            return self.resolve_untyped_call(node);
        }
        // Technically, this signatures list may be incomplete. We are taking
        // the apparent type, but we are not including construct signatures
        // that may have been added to the Object or Function interface,
        // since they have none by default. This is a bit of a leap of faith
        // that the user will not add any.
        let construct_signatures =
            self.get_signatures_of_type(expression_type, SignatureKind::Construct);
        if !construct_signatures.is_empty() {
            let accessibility_error = self.get_constructor_accessibility_error(
                node,
                &construct_signatures,
                ast::ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER,
            );
            if let Some(accessibility_error) = accessibility_error {
                if accessibility_error
                    .kind
                    .intersects(ast::ModifierFlags::PRIVATE)
                {
                    let arg = self.type_to_string(accessibility_error.declaring_class);
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Constructor_of_class_0_is_private_and_only_accessible_within_the_class_declaration,
                        &[arg],
                    );
                }
                if accessibility_error
                    .kind
                    .intersects(ast::ModifierFlags::PROTECTED)
                {
                    let arg = self.type_to_string(accessibility_error.declaring_class);
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Constructor_of_class_0_is_protected_and_only_accessible_within_the_class_declaration,
                        &[arg],
                    );
                }
                return self.resolve_error_call(node);
            }
            // If the expression is a class of abstract type, or an abstract
            // construct signature, then it cannot be instantiated. In the
            // case of a merged class-module or class-interface declaration,
            // only the class declaration node will have the Abstract flag
            // set.
            if some_signature(
                self,
                &construct_signatures,
                |c: &mut Checker, sig: SignatureId| {
                    c.signature_arena
                        .get(sig)
                        .flags
                        .intersects(SignatureFlags::ABSTRACT)
                },
            ) {
                self.error(
                    Some(node),
                    &tsc_diagnostics::Cannot_create_an_instance_of_an_abstract_class,
                    &[],
                );
                return self.resolve_error_call(node);
            }
            let symbol = self.types.get_ref(expression_type).symbol;
            if let Some(symbol) = symbol {
                let value_decl = {
                    let arena = self.symbol_arena.borrow();
                    let __program = self.program.clone().expect("program");
                    ast::get_class_like_declaration_of_symbol_with(
                        &arena[symbol.index()],
                        |d| ast::is_class_like(Some(d), &__program.nodes(d.file_index())),
                    )
                };
                if let Some(value_decl) = value_decl {
                    let __program = self.program.clone().expect("program");
                    let decl_nodes = __program.nodes((value_decl).file_index());
                    if ast::has_modifier(&decl_nodes[value_decl], ast::ModifierFlags::ABSTRACT) {
                        self.error(
                            Some(node),
                            &tsc_diagnostics::Cannot_create_an_instance_of_an_abstract_class,
                            &[],
                        );
                        return self.resolve_error_call(node);
                    }
                }
            }
            return self.resolve_call(
                node,
                construct_signatures,
                candidates_out_array,
                check_mode,
                SignatureFlags::NONE,
                None,
            );
        }
        // If expressionType's apparent type is an object type with no
        // construct signatures but one or more call signatures, the
        // expression is processed as a function call. A compile-time error
        // occurs if the result of the function call is not Void. The type of
        // the result of the operation is Any. It is an error to have a Void
        // this type.
        let call_signatures = self.get_signatures_of_type(expression_type, SignatureKind::Call);
        if !call_signatures.is_empty() {
            let signature = self.resolve_call(
                node,
                call_signatures,
                candidates_out_array,
                check_mode,
                SignatureFlags::NONE,
                None,
            );
            if !self.no_implicit_any {
                if self.signature_arena.get(signature).declaration.is_some()
                    && self.get_return_type_of_signature(signature) != self.void_type
                {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Only_a_void_function_can_be_called_with_the_new_keyword,
                        &[],
                    );
                }
                if self.get_this_type_of_signature(signature) == Some(self.void_type) {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::A_function_that_is_called_with_the_new_keyword_cannot_have_a_this_type_that_is_void,
                        &[],
                    );
                }
            }
            return signature;
        }
        self.invocation_error(
            nodes[node].expression().expect("expression"),
            expression_type,
            SignatureKind::Construct,
            None,
        );
        self.resolve_error_call(node)
    }

    /// `getConstructorAccessibilityError` (checker.go:8867).
    pub(crate) fn get_constructor_accessibility_error(
        &mut self,
        node: NodeId,
        signatures: &[SignatureId],
        modifiers_mask: ast::ModifierFlags,
    ) -> Option<ConstructorAccessibilityError> {
        for &signature in signatures {
            let Some(declaration) = self.signature_arena.get(signature).declaration else {
                continue;
            };
            let __program = self.program.clone().expect("program");
            let decl_nodes = __program.nodes((declaration).file_index());
            let modifiers = crate::utilities::get_selected_modifier_flags(
                &decl_nodes[declaration],
                modifiers_mask,
            );
            // (1) Public constructors and (2) constructor functions are
            // always accessible.
            if modifiers.is_empty() || !ast::is_constructor_declaration(&decl_nodes[declaration]) {
                continue;
            }
            let declaring_class_declaration = {
                let parent = decl_nodes[declaration].parent.expect("declaration parent");
                let __program = self.program.clone().expect("program");
                let parent_nodes = __program.nodes((parent).file_index());
                let symbol = parent_nodes[parent].symbol().expect("parent symbol");
                drop(parent_nodes);
                let arena = self.symbol_arena.borrow();
                ast::get_class_like_declaration_of_symbol_with(
                    &arena[symbol.index()],
                    |d| ast::is_class_like(Some(d), &__program.nodes(d.file_index())),
                )
            };
            // A private or protected constructor can only be instantiated
            // within its own class (or a subclass, for protected)
            if !self.is_node_within_class(node, declaring_class_declaration) {
                let containing_class = ast::get_containing_class(node, &decl_nodes);
                if containing_class.is_some() && modifiers.intersects(ast::ModifierFlags::PROTECTED)
                {
                    let containing_class = containing_class.unwrap();
                    let containing_type = self.get_type_of_node(containing_class);
                    let target = {
                        let parent = decl_nodes[declaration].parent.expect("declaration parent");
                        let __program = self.program.clone().expect("program");
                        let parent_nodes = __program.nodes((parent).file_index());
                        parent_nodes[parent].symbol().expect("parent symbol")
                    };
                    if self.type_has_protected_accessible_base(target, containing_type) {
                        continue;
                    }
                }
                let declaring_class = {
                    let parent = decl_nodes[declaration].parent.expect("declaration parent");
                    let __program = self.program.clone().expect("program");
                    let parent_nodes = __program.nodes((parent).file_index());
                    let symbol = parent_nodes[parent].symbol().expect("parent symbol");
                    self.get_declared_type_of_symbol(symbol)
                };
                return Some(ConstructorAccessibilityError {
                    kind: modifiers,
                    declaring_class,
                });
            }
        }
        None
    }

    /// `typeHasProtectedAccessibleBase` (checker.go:8897).
    pub(crate) fn type_has_protected_accessible_base(
        &mut self,
        target: SymbolId,
        t: TypeId,
    ) -> bool {
        let target_type = self.get_target_type(t);
        let base_types = self.get_base_types(target_type);
        if base_types.is_empty() {
            return false;
        }
        let first_base = base_types[0];
        if self
            .types_handle()
            .get_ref(first_base)
            .flags
            .intersects(TypeFlags::INTERSECTION)
        {
            let types: Vec<TypeId> = self.types.get_ref(first_base).types().to_vec();
            let (mixin_flags, _) = self.find_mixins(&types);
            for (i, intersection_member) in types.iter().enumerate() {
                // We want to ignore mixin ctors
                if !mixin_flags.get(i).copied().unwrap_or(false) {
                    let ty = self.types.get_ref(*intersection_member);
                    if ty
                        .object_flags
                        .intersects(ObjectFlags::CLASS | ObjectFlags::INTERFACE)
                    {
                        if ty.symbol == Some(target) {
                            return true;
                        }
                        drop(ty);
                        if self.type_has_protected_accessible_base(target, *intersection_member) {
                            return true;
                        }
                    }
                }
            }
            return false;
        }
        if self.types.get_ref(first_base).symbol == Some(target) {
            return true;
        }
        self.type_has_protected_accessible_base(target, first_base)
    }

    /// `resolveTaggedTemplateExpression` (checker.go:8936).
    pub(crate) fn resolve_tagged_template_expression(
        &mut self,
        node: NodeId,
        candidates_out_array: Option<&mut Vec<SignatureId>>,
        check_mode: CheckMode,
    ) -> SignatureId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let tag = nodes[node]
            .as_tagged_template_expression()
            .tag
            .expect("tagged template tag");
        let tag_type = self.check_expression(tag);
        let apparent_type = self.get_apparent_type(tag_type);
        if self.is_error_type(apparent_type) {
            // Another error has already been reported
            return self.resolve_error_call(node);
        }
        let call_signatures = self.get_signatures_of_type(apparent_type, SignatureKind::Call);
        let num_construct_signatures = self
            .get_signatures_of_type(apparent_type, SignatureKind::Construct)
            .len() as i32;
        if self.is_untyped_function_call(
            tag_type,
            apparent_type,
            call_signatures.len() as i32,
            num_construct_signatures,
        ) {
            return self.resolve_untyped_call(node);
        }
        if call_signatures.is_empty() {
            if nodes[node]
                .parent
                .is_some_and(|p| ast::is_array_literal_expression(&nodes[p]))
            {
                self.error(
                    Some(tag),
                    &tsc_diagnostics::It_is_likely_that_you_are_missing_a_comma_to_separate_these_two_template_expressions_They_form_a_tagged_template_expression_which_cannot_be_invoked,
                    &[],
                );
                return self.resolve_error_call(node);
            }
            self.invocation_error(tag, apparent_type, SignatureKind::Call, None);
            return self.resolve_error_call(node);
        }
        self.resolve_call(
            node,
            call_signatures,
            candidates_out_array,
            check_mode,
            SignatureFlags::NONE,
            None,
        )
    }

    /// `resolveDecorator` (checker.go:8960).
    pub(crate) fn resolve_decorator(
        &mut self,
        node: NodeId,
        candidates_out_array: Option<&mut Vec<SignatureId>>,
        check_mode: CheckMode,
    ) -> SignatureId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent.expect("decorator parent");
        if !ast::can_have_decorators(&nodes[parent]) {
            return self.resolve_error_call(node);
        }
        let expression = nodes[node].expression().expect("decorator expression");
        let func_type = self.check_expression(expression);
        let apparent_type = self.get_apparent_type(func_type);
        if self.is_error_type(apparent_type) {
            return self.resolve_error_call(node);
        }
        let call_signatures = self.get_signatures_of_type(apparent_type, SignatureKind::Call);
        let num_construct_signatures = self
            .get_signatures_of_type(apparent_type, SignatureKind::Construct)
            .len() as i32;
        if self.is_untyped_function_call(
            func_type,
            apparent_type,
            call_signatures.len() as i32,
            num_construct_signatures,
        ) {
            return self.resolve_untyped_call(node);
        }
        if self.is_potentially_uncalled_decorator(node, &call_signatures)
            && !ast::is_parenthesized_expression(&nodes[expression])
        {
            let node_str = tsc_scanner::utilities::get_text_of_node(expression, &nodes);
            self.error(
                Some(node),
                &tsc_diagnostics::X_0_accepts_too_few_arguments_to_be_used_as_a_decorator_here_Did_you_mean_to_call_it_first_and_write_0,
                &[node_str],
            );
            return self.resolve_error_call(node);
        }
        let head_message = self.get_diagnostic_head_message_for_decorator_resolution(node);
        if call_signatures.is_empty() {
            let details =
                self.invocation_error_details(expression, apparent_type, SignatureKind::Call);
            let mut diag = ast::diagnostic::new_diagnostic_chain(
                Some(&details),
                head_message,
                &[] as &[String],
            );
            diag = self.add_diagnostic(&diag);
            self.invocation_error_recovery(apparent_type, SignatureKind::Call, &diag);
            return self.resolve_error_call(node);
        }
        let decorator_signature = self.get_decorator_call_signature(node);
        if decorator_signature.is_none() {
            return self.resolve_error_call(node);
        }
        self.resolve_call(
            node,
            call_signatures,
            candidates_out_array,
            check_mode,
            SignatureFlags::NONE,
            Some(head_message),
        )
    }

    /// `isPotentiallyUncalledDecorator` (checker.go:8996). Sometimes, we
    /// have a decorator that could accept zero arguments, but is receiving
    /// too many arguments as part of the decorator invocation. In those
    /// cases, a user may have meant to *call* the expression before using
    /// it as a decorator.
    pub(crate) fn is_potentially_uncalled_decorator(
        &mut self,
        decorator: NodeId,
        signatures: &[SignatureId],
    ) -> bool {
        !signatures.is_empty()
            && signatures.iter().all(|&sig| {
                let (min_argument_count, parameters_len, has_rest) = {
                    let s = self.signature_arena.get(sig);
                    (
                        s.min_argument_count,
                        s.parameters.len(),
                        crate::checker_c::signature_has_rest_parameter(s),
                    )
                };
                min_argument_count == 0
                    && !has_rest
                    && (parameters_len as i32) < self.get_decorator_argument_count(decorator, sig)
            })
    }

    /// `getDiagnosticHeadMessageForDecoratorResolution` (checker.go:9003).
    /// Gets the localized diagnostic head message to use for errors when
    /// resolving a decorator as a call expression.
    pub(crate) fn get_diagnostic_head_message_for_decorator_resolution(
        &mut self,
        node: NodeId,
    ) -> &'static tsc_diagnostics::Message {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent.expect("decorator parent");
        match nodes[parent].kind {
            ast::Kind::ClassDeclaration | ast::Kind::ClassExpression => {
                &tsc_diagnostics::Unable_to_resolve_signature_of_class_decorator_when_called_as_an_expression
            }
            ast::Kind::Parameter => {
                &tsc_diagnostics::Unable_to_resolve_signature_of_parameter_decorator_when_called_as_an_expression
            }
            ast::Kind::PropertyDeclaration => {
                &tsc_diagnostics::Unable_to_resolve_signature_of_property_decorator_when_called_as_an_expression
            }
            ast::Kind::MethodDeclaration | ast::Kind::GetAccessor | ast::Kind::SetAccessor => {
                &tsc_diagnostics::Unable_to_resolve_signature_of_method_decorator_when_called_as_an_expression
            }
            _ => panic!("Unhandled case in getDiagnosticHeadMessageForDecoratorResolution"),
        }
    }

    /// `resolveInstanceofExpression` (checker.go:9017).
    pub(crate) fn resolve_instanceof_expression(
        &mut self,
        node: NodeId,
        candidates_out_array: Option<&mut Vec<SignatureId>>,
        check_mode: CheckMode,
    ) -> SignatureId {
        // if rightType is an object type with a custom `[Symbol.hasInstance]`
        // method, then it is potentially valid on the right-hand side of the
        // `instanceof` operator. This allows normal `object` types to
        // participate in `instanceof`, as per Step 2 of
        // https://tc39.es/ecma262/#sec-instanceofoperator.
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let right = nodes[node]
            .as_binary_expression()
            .right
            .expect("binary right");
        let right_type = self.check_expression(right);
        if !crate::utilities::is_type_any(&self.types, right_type) {
            if let Some(has_instance_method_type) =
                self.get_symbol_has_instance_method_of_object_type(right_type)
            {
                let apparent_type = self.get_apparent_type(has_instance_method_type);
                if self.is_error_type(apparent_type) {
                    return self.resolve_error_call(node);
                }
                let call_signatures =
                    self.get_signatures_of_type(apparent_type, SignatureKind::Call);
                let construct_signatures =
                    self.get_signatures_of_type(apparent_type, SignatureKind::Construct);
                if self.is_untyped_function_call(
                    has_instance_method_type,
                    apparent_type,
                    call_signatures.len() as i32,
                    construct_signatures.len() as i32,
                ) {
                    return self.resolve_untyped_call(node);
                }
                if !call_signatures.is_empty() {
                    return self.resolve_call(
                        node,
                        call_signatures,
                        candidates_out_array,
                        check_mode,
                        SignatureFlags::NONE,
                        None,
                    );
                }
            } else if !(self.type_has_call_or_construct_signatures(right_type)
                || self.is_type_subtype_of(right_type, self.global_function_type))
            {
                self.error(
                    Some(right),
                    &tsc_diagnostics::The_right_hand_side_of_an_instanceof_expression_must_be_either_of_type_any_a_class_function_or_other_type_assignable_to_the_Function_interface_type_or_an_object_type_with_a_Symbol_hasInstance_method,
                    &[],
                );
                return self.resolve_error_call(node);
            }
        }
        // fall back to a default signature
        self.any_signature
    }

    /// `resolveCall` (checker.go:9061).
    pub(crate) fn resolve_call(
        &mut self,
        node: NodeId,
        signatures: Vec<SignatureId>,
        candidates_out_array: Option<&mut Vec<SignatureId>>,
        check_mode: CheckMode,
        call_chain_flags: SignatureFlags,
        head_message: Option<&'static tsc_diagnostics::Message>,
    ) -> SignatureId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_tagged_template = nodes[node].kind == ast::Kind::TaggedTemplateExpression;
        let is_decorator = nodes[node].kind == ast::Kind::Decorator;
        let is_jsx_opening_or_self_closing_element = ast::is_jsx_opening_like_element(&nodes[node]);
        let is_instanceof = nodes[node].kind == ast::Kind::BinaryExpression;
        let report_errors = !self.is_inference_partially_blocked && candidates_out_array.is_none();
        let mut s = CallState::default();
        s.node = Some(node);
        if !is_decorator
            && !is_instanceof
            && !crate::utilities::is_super_call(node, &nodes)
            && !ast::is_jsx_opening_fragment(&nodes[node])
        {
            s.type_arguments = nodes[node].type_arguments().unwrap_or(&[]).to_vec();
            // We already perform checking on the type arguments on the class
            // declaration itself.
            if is_tagged_template
                || is_jsx_opening_or_self_closing_element
                || nodes[node]
                    .expression()
                    .is_some_and(|e| nodes[e].kind != ast::Kind::SuperKeyword)
            {
                let type_arguments = s.type_arguments.clone();
                self.check_source_elements(&type_arguments);
            }
        }
        s.candidates = self.reorder_candidates(&signatures, call_chain_flags);
        let has_candidates_out_array = candidates_out_array.is_some();
        if let Some(out_array) = candidates_out_array {
            *out_array = s.candidates.clone();
        }
        if s.candidates.is_empty() {
            // In Strada we would error here, but no known repro doesn't have
            // at least one other error in this codepath. Just return
            // instead. See #54442
            return self.unknown_signature;
        }
        s.args = self.get_effective_call_arguments(node);
        // The excludeArgument array contains true for each context sensitive
        // argument (an argument is context sensitive it is susceptible to a
        // one-time permanent contextual typing).
        //
        // The idea is that we will perform type argument inference &
        // assignability checking once without using the susceptible
        // parameters that are functions, and once more for those parameters,
        // contextually typing each as we go along.
        //
        // For a tagged template, then the first argument be 'undefined' if
        // necessary because it represents a TemplateStringsArray.
        //
        // For a decorator, no arguments are susceptible to contextual typing
        // due to the fact decorators are applied to a declaration by the
        // emitter, and not to an expression.
        s.is_single_non_generic_candidate = s.candidates.len() == 1
            && self
                .signature_arena
                .get(s.candidates[0])
                .type_parameters
                .is_empty();
        if !is_decorator
            && !s.is_single_non_generic_candidate
            && s.args.iter().any(|&a| self.is_context_sensitive(a))
        {
            s.arg_check_mode = CheckMode::SKIP_CONTEXT_SENSITIVE;
        } else {
            s.arg_check_mode = CheckMode::NORMAL;
        }
        // The following variables are captured and modified by calls to
        // chooseOverload. If overload resolution or type argument inference
        // fails, we want to report the best error possible. The best error
        // is one which says that an argument was not assignable to a
        // parameter. This implies that everything else about the overload
        // was fine. So if there is any overload that is only incorrect
        // because of an argument, we will report an error on that one.
        //
        //     function foo(s: string): void;
        //     function foo(n: number): void; // Report argument error on this overload
        //     function foo(): void;
        //     foo(true);
        //
        // If none of the overloads even made it that far, there are two
        // possibilities. There was a problem with type arguments for some
        // overload, in which case report an error on that. Or none of the
        // overloads even had correct arity, in which case give an arity
        // error.
        //
        //     function foo<T extends string>(x: T): void; // Report type argument error
        //     function foo(): void;
        //     foo<number>(0);
        //
        // If we are in signature help, a trailing comma indicates that we
        // intend to provide another argument, so we will only accept
        // overloads with arity at least 1 higher than the current number of
        // provided arguments.
        s.signature_help_trailing_comma = check_mode.intersects(CheckMode::IS_FOR_SIGNATURE_HELP)
            && ast::is_call_expression(&nodes[node])
            && nodes[node]
                .argument_list()
                .is_some_and(|l| l.has_trailing_comma(&nodes));
        // Section 4.12.1:
        // if the candidate list contains one or more signatures for which
        // the type of each argument expression is a subtype of each
        // corresponding parameter type, the return type of the first of
        // those signatures becomes the return type of the function call.
        // Otherwise, the return type of the first signature in the candidate
        // list becomes the return type of the function call.
        //
        // Whether the call is an error is determined by assignability of the
        // arguments. The subtype pass is just important for choosing the
        // best signature. So in the case where there is only one signature,
        // the subtype pass is useless. So skipping it is an optimization.
        let mut result: Option<SignatureId> = None;
        s.recursive_resolution = self.call_resolution_stack.contains(&node);
        self.call_resolution_stack.push(node);
        if s.candidates.len() > 1 {
            let relation = self.subtype_relation.clone();
            result = self.choose_overload(&mut s, &relation);
        }
        if result.is_none() {
            let relation = self.assignable_relation.clone();
            result = self.choose_overload(&mut s, &relation);
        }
        self.call_resolution_stack.pop();
        if let Some(result) = result {
            return result;
        }
        let result = self.get_candidate_for_overload_failure(
            node,
            &mut s.candidates,
            &s.args,
            has_candidates_out_array,
            check_mode,
        );
        // Preemptively cache the result; getResolvedSignature will do this
        // after we return, but we need to ensure that the result is present
        // for the error checks below so that if this signature is
        // encountered again, we handle the circularity (rather than
        // producing a different result which may produce no errors and
        // assert). Callers of getResolvedSignature don't hit this issue
        // because they only observe this result after it's had a chance to
        // be cached, but the error reporting code below executes before
        // getResolvedSignature sets resolvedSignature.
        self.signature_links.get(node).resolved_signature = Some(result);
        // No signatures were applicable. Now report errors based on the last
        // applicable signature with no arguments excluded from assignability
        // checks. If candidate is undefined, it means that no candidates had
        // a suitable arity. In that case, skip the checkApplicableSignature
        // check.
        if report_errors {
            // If the call expression is a synthetic call to a
            // `[Symbol.hasInstance]` method then we will produce a head
            // message when reporting diagnostics that explains how we got to
            // `right[Symbol.hasInstance](left)` from `left instanceof
            // right`, as it pertains to "Argument" related messages reported
            // for the call.
            let mut head_message = head_message;
            if head_message.is_none() && is_instanceof {
                head_message = Some(&tsc_diagnostics::The_left_hand_side_of_an_instanceof_expression_must_be_assignable_to_the_first_argument_of_the_right_hand_side_s_Symbol_hasInstance_method);
            }
            self.report_call_resolution_errors(node, &s, &signatures, head_message);
        }
        result
    }

    /// `reorderCandidates` (checker.go:9178).
    pub(crate) fn reorder_candidates(
        &mut self,
        signatures: &[SignatureId],
        call_chain_flags: SignatureFlags,
    ) -> Vec<SignatureId> {
        let mut last_parent: Option<NodeId> = None;
        let mut last_symbol: Option<SymbolId> = None;
        let mut index: usize = 0;
        let mut cutoff_index: usize = 0;
        let mut splice_index: usize;
        let mut specialized_index: i64 = -1;
        let mut result: Vec<SignatureId> = Vec::with_capacity(signatures.len());
        for &signature in signatures {
            let mut symbol: Option<SymbolId> = None;
            let mut parent: Option<NodeId> = None;
            let declaration = self.signature_arena.get(signature).declaration;
            if let Some(declaration) = declaration {
                symbol = self.get_symbol_of_declaration(declaration);
                parent = self.program_nodes(declaration)[declaration].parent;
            }
            if last_symbol.is_none() || symbol == last_symbol {
                if last_parent.is_some() && parent == last_parent {
                    index += 1;
                } else {
                    last_parent = parent;
                    index = cutoff_index;
                }
            } else {
                // current declaration belongs to a different symbol set
                // cutoffIndex so re-orderings in the future won't change
                // result set from 0 to cutoffIndex
                index = result.len();
                cutoff_index = result.len();
                last_parent = parent;
            }
            last_symbol = symbol;
            // specialized signatures always need to be placed before
            // non-specialized signatures regardless of the cutoff position;
            // see GH#1133
            if signature_has_literal_types(self.signature_arena.get(signature)) {
                specialized_index += 1;
                splice_index = specialized_index as usize;
                // The cutoff index always needs to be greater than or equal
                // to the specialized signature index in order to prevent
                // non-specialized signatures from being added before a
                // specialized signature.
                cutoff_index += 1;
            } else {
                splice_index = index;
            }
            let signature = if call_chain_flags.is_empty() {
                signature
            } else {
                self.get_optional_call_signature(signature, call_chain_flags)
            };
            result.insert(splice_index.min(result.len()), signature);
        }
        result
    }

    /// `getOptionalCallSignature` (checker.go:9232).
    pub(crate) fn get_optional_call_signature(
        &mut self,
        signature: SignatureId,
        call_chain_flags: SignatureFlags,
    ) -> SignatureId {
        if self.signature_arena.get(signature).flags & SignatureFlags::CALL_CHAIN_FLAGS
            == call_chain_flags
        {
            return signature;
        }
        let key = CachedSignatureKey {
            sig: Some(signature),
            key: if call_chain_flags == SignatureFlags::IS_INNER_CALL_CHAIN {
                *crate::checker_types::SIGNATURE_KEY_INNER
            } else {
                *crate::checker_types::SIGNATURE_KEY_OUTER
            },
        };
        if let Some(&cached) = self.cached_signatures.get(&key) {
            return cached;
        }
        let result = self.clone_signature(signature);
        self.signature_arena
            .get_mut(result)
            .flags
            .insert(call_chain_flags);
        self.cached_signatures.insert(key, result);
        result
    }

    /// `chooseOverload` (checker.go:9246).
    pub(crate) fn choose_overload(
        &mut self,
        s: &mut CallState,
        relation: &SharedRelation,
    ) -> Option<SignatureId> {
        s.candidates_for_argument_error.clear();
        s.candidate_for_argument_arity_error = None;
        s.candidate_for_type_argument_error = None;
        if s.is_single_non_generic_candidate {
            let candidate = s.candidates[0];
            if !s.type_arguments.is_empty()
                || !self.has_correct_arity(
                    s.node.unwrap(),
                    &s.args,
                    candidate,
                    s.signature_help_trailing_comma,
                )
            {
                return None;
            }
            if !self.is_signature_applicable(
                s.node.unwrap(),
                &s.args,
                candidate,
                relation.clone(),
                CheckMode::NORMAL,
                false, /*reportErrors*/
                None,  /*diagnosticOutput*/
            ) {
                s.candidates_for_argument_error = vec![candidate];
                return None;
            }
            return Some(candidate);
        }
        for candidate_index in 0..s.candidates.len() {
            let candidate = s.candidates[candidate_index];
            if !self.has_correct_type_argument_arity(candidate, &s.type_arguments)
                || !self.has_correct_arity(
                    s.node.unwrap(),
                    &s.args,
                    candidate,
                    s.signature_help_trailing_comma,
                )
            {
                continue;
            }
            let mut check_candidate = candidate;
            let mut inference_context: Option<InferenceContextId> = None;
            let candidate_type_parameters =
                self.signature_arena.get(candidate).type_parameters.clone();
            if !candidate_type_parameters.is_empty() {
                let type_argument_types: Vec<TypeId>;
                if !s.type_arguments.is_empty() {
                    let Some(types) = self.check_type_arguments(
                        candidate,
                        &s.type_arguments,
                        false, /*reportErrors*/
                        None,
                    ) else {
                        s.candidate_for_type_argument_error = Some(candidate);
                        continue;
                    };
                    type_argument_types = types;
                } else {
                    // When we are recursively resolving a call with a single
                    // candidate, we skip constraints checks during type
                    // inference to avoid circularity errors. For example,
                    // see #64192.
                    let in_js_file = s
                        .node
                        .is_some_and(|n| ast::is_in_js_file(Some(n), &self.program_nodes(n)));
                    let inference_flags = (if s.recursive_resolution && s.candidates.len() == 1 {
                        InferenceFlags::NO_CONSTRAINT_CHECKS
                    } else {
                        InferenceFlags::NONE
                    }) | (if in_js_file {
                        InferenceFlags::ANY_DEFAULT
                    } else {
                        InferenceFlags::NONE
                    });
                    let context = self.new_inference_context(
                        &candidate_type_parameters,
                        candidate,
                        inference_flags,
                        None,
                    );
                    inference_context = Some(context);
                    type_argument_types = self.infer_type_arguments(
                        s.node.unwrap(),
                        candidate,
                        &s.args,
                        s.arg_check_mode | CheckMode::SKIP_GENERIC_FUNCTIONS,
                        context,
                    );
                    if self.inference_contexts[context.index()]
                        .flags
                        .intersects(InferenceFlags::SKIPPED_GENERIC_FUNCTION)
                    {
                        s.arg_check_mode.insert(CheckMode::SKIP_GENERIC_FUNCTIONS);
                    }
                }
                let inferred_type_parameters = inference_context.map_or_else(Vec::new, |ic| {
                    self.inference_contexts[ic.index()]
                        .inferred_type_parameters
                        .clone()
                });
                let in_js_file = self
                    .signature_arena
                    .get(candidate)
                    .declaration
                    .is_some_and(|d| ast::is_in_js_file(Some(d), &self.program_nodes(d)));
                check_candidate = self.get_signature_instantiation(
                    candidate,
                    &type_argument_types,
                    in_js_file,
                    Some(&inferred_type_parameters),
                );
                // If the original signature has a generic rest type,
                // instantiation may produce a signature with different arity
                // and we need to perform another arity check.
                if self.get_non_array_rest_type(candidate).is_some()
                    && !self.has_correct_arity(
                        s.node.unwrap(),
                        &s.args,
                        check_candidate,
                        s.signature_help_trailing_comma,
                    )
                {
                    s.candidate_for_argument_arity_error = Some(check_candidate);
                    continue;
                }
            } else {
                check_candidate = candidate;
            }
            if !self.is_signature_applicable(
                s.node.unwrap(),
                &s.args,
                check_candidate,
                relation.clone(),
                s.arg_check_mode,
                false, /*reportErrors*/
                None,  /*diagnosticOutput*/
            ) {
                // Give preference to error candidates that have no rest
                // parameters (as they are more specific)
                s.candidates_for_argument_error.push(check_candidate);
                continue;
            }
            if !s.arg_check_mode.is_empty() {
                // If one or more context sensitive arguments were excluded,
                // we start including them now (and keeping do so for any
                // subsequent candidates) and perform a second round of type
                // inference and applicability checking for this particular
                // candidate.
                s.arg_check_mode = CheckMode::NORMAL;
                if let Some(inference_context) = inference_context {
                    let type_argument_types = self.infer_type_arguments(
                        s.node.unwrap(),
                        candidate,
                        &s.args,
                        s.arg_check_mode,
                        inference_context,
                    );
                    let inferred_type_parameters = self.inference_contexts
                        [inference_context.index()]
                    .inferred_type_parameters
                    .clone();
                    let in_js_file = self
                        .signature_arena
                        .get(candidate)
                        .declaration
                        .is_some_and(|d| ast::is_in_js_file(Some(d), &self.program_nodes(d)));
                    check_candidate = self.get_signature_instantiation(
                        candidate,
                        &type_argument_types,
                        in_js_file,
                        Some(&inferred_type_parameters),
                    );
                    // If the original signature has a generic rest type,
                    // instantiation may produce a signature with different
                    // arity and we need to perform another arity check.
                    if self.get_non_array_rest_type(candidate).is_some()
                        && !self.has_correct_arity(
                            s.node.unwrap(),
                            &s.args,
                            check_candidate,
                            s.signature_help_trailing_comma,
                        )
                    {
                        s.candidate_for_argument_arity_error = Some(check_candidate);
                        continue;
                    }
                }
                if !self.is_signature_applicable(
                    s.node.unwrap(),
                    &s.args,
                    check_candidate,
                    relation.clone(),
                    s.arg_check_mode,
                    false, /*reportErrors*/
                    None,  /*diagnosticOutput*/
                ) {
                    // Give preference to error candidates that have no rest
                    // parameters (as they are more specific)
                    s.candidates_for_argument_error.push(check_candidate);
                    continue;
                }
            }
            s.candidates[candidate_index] = check_candidate;
            return Some(check_candidate);
        }
        None
    }

    /// `hasCorrectArity` (checker.go:9332).
    pub(crate) fn has_correct_arity(
        &mut self,
        node: NodeId,
        args: &[NodeId],
        signature: SignatureId,
        signature_help_trailing_comma: bool,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_jsx_opening_fragment(&nodes[node]) {
            return true;
        }
        let arg_count: usize;
        let mut call_is_incomplete = false;
        // In incomplete call we want to be lenient when we have too few
        // arguments
        let mut effective_parameter_count = self.get_parameter_count(signature);
        let mut effective_minimum_arguments = self.get_min_argument_count(signature);
        if ast::is_tagged_template_expression(&nodes[node]) {
            arg_count = args.len();
            let template = nodes[node]
                .as_tagged_template_expression()
                .template
                .expect("tagged template");
            if ast::is_template_expression(&nodes[template]) {
                // If a tagged template expression lacks a tail literal, the
                // call is incomplete. Specifically, a template only can end
                // in a TemplateTail or a Missing literal.
                // we should always have at least one span.
                let last_span = *nodes[template]
                    .as_template_expression()
                    .template_spans
                    .as_ref()
                    .and_then(|l| l.nodes.last())
                    .expect("template spans");
                let literal = nodes[last_span].as_template_span().literal;
                call_is_incomplete = ast::node_is_missing(literal, &nodes)
                    || literal.is_some_and(|l| ast::is_unterminated_literal(&nodes[l]));
            } else {
                // If the template didn't end in a backtick, or its beginning
                // occurred right prior to EOF, then this might actually turn
                // out to be a TemplateHead in the future; so we consider the
                // call to be incomplete.
                call_is_incomplete = ast::is_unterminated_literal(&nodes[template]);
            }
        } else if ast::is_decorator(&nodes[node]) {
            arg_count = self.get_decorator_argument_count(node, signature) as usize;
        } else if ast::is_binary_expression(&nodes[node]) {
            arg_count = 1;
        } else if ast::is_jsx_opening_like_element(&nodes[node]) {
            let attributes = nodes[node].attributes().expect("jsx attributes");
            call_is_incomplete = nodes[attributes].end() == nodes[node].end();
            if call_is_incomplete {
                return true;
            }
            arg_count = if effective_minimum_arguments == 0 {
                args.len()
            } else {
                1
            };
            // class may have argumentless ctor functions - still resolve
            // ctor and compare vs props member type
            effective_parameter_count = if args.is_empty() {
                effective_parameter_count
            } else {
                1
            };
            // sfc may specify context argument - handled by framework and
            // not typechecked
            effective_minimum_arguments = effective_minimum_arguments.min(1);
        } else if ast::is_new_expression(&nodes[node]) && nodes[node].argument_list().is_none() {
            // This only happens when we have something of the form: 'new C'
            return self.get_min_argument_count(signature) == 0;
        } else {
            if signature_help_trailing_comma {
                arg_count = args.len() + 1;
            } else {
                arg_count = args.len();
            }
            // If we are missing the close parenthesis, the call is
            // incomplete.
            call_is_incomplete = nodes[node]
                .argument_list()
                .is_some_and(|l| l.end() == nodes[node].end());
            // If a spread argument is present, check that it corresponds to
            // a rest parameter or at least that it's in the valid range.
            let spread_arg_index = self.get_spread_argument_index(args);
            if spread_arg_index >= 0 {
                return spread_arg_index >= self.get_min_argument_count(signature)
                    && (self.has_effective_rest_parameter(signature)
                        || spread_arg_index < self.get_parameter_count(signature) as i32);
            }
        }
        // Too many arguments implies incorrect arity.
        if !self.has_effective_rest_parameter(signature) && arg_count > effective_parameter_count {
            return false;
        }
        // If the call is incomplete, we should skip the lower bound check.
        // JSX signatures can have extra parameters provided by the library
        // which we don't check
        if call_is_incomplete || arg_count as i32 >= effective_minimum_arguments {
            return true;
        }
        for i in arg_count..effective_minimum_arguments.max(0) as usize {
            let t = self.get_type_at_position(signature, i);
            let filtered =
                self.filter_type(t, &|c: &mut Checker, t: TypeId| accepts_void(&c.types, t));
            if self
                .types_handle()
                .get_ref(filtered)
                .flags
                .intersects(TypeFlags::NEVER)
            {
                return false;
            }
        }
        true
    }

    /// `getDecoratorArgumentCount` (checker.go:9408).
    pub(crate) fn get_decorator_argument_count(
        &mut self,
        node: NodeId,
        signature: SignatureId,
    ) -> i32 {
        if self.compiler_options.experimental_decorators.is_true() {
            return self.get_legacy_decorator_argument_count(node, signature);
        }
        (self.get_parameter_count(signature) as i32).max(1).min(2)
    }

    /// `getLegacyDecoratorArgumentCount` (checker.go:9418). Returns the
    /// argument count for a decorator node that works like a function
    /// invocation.
    pub(crate) fn get_legacy_decorator_argument_count(
        &mut self,
        node: NodeId,
        signature: SignatureId,
    ) -> i32 {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent.expect("decorator parent");
        match nodes[parent].kind {
            ast::Kind::ClassDeclaration | ast::Kind::ClassExpression => 1,
            ast::Kind::PropertyDeclaration => {
                if ast::has_accessor_modifier(&nodes[parent]) {
                    3
                } else {
                    2
                }
            }
            ast::Kind::MethodDeclaration | ast::Kind::GetAccessor | ast::Kind::SetAccessor => {
                // For decorators with only two parameters we supply only
                // two arguments
                if self.get_parameter_count(signature) <= 2 {
                    2
                } else {
                    3
                }
            }
            ast::Kind::Parameter => 3,
            _ => panic!("Unhandled case in getLegacyDecoratorArgumentCount"),
        }
    }

    /// `hasCorrectTypeArgumentArity` (checker.go:9439).
    pub(crate) fn has_correct_type_argument_arity(
        &mut self,
        signature: SignatureId,
        type_arguments: &[NodeId],
    ) -> bool {
        // If the user supplied type arguments, but the number of type
        // arguments does not match the declared number of type parameters,
        // the call has an incorrect arity.
        let type_parameters = self.signature_arena.get(signature).type_parameters.clone();
        let num_type_parameters = type_parameters.len();
        let min_type_argument_count = self.get_min_type_argument_count(&type_parameters);
        return type_arguments.is_empty()
            || type_arguments.len() >= min_type_argument_count as usize
                && type_arguments.len() <= num_type_parameters;
    }
}

/// `type constructorAccessibilityError struct` (checker.go:8862).
#[derive(Clone, Copy, Default)]
pub(crate) struct ConstructorAccessibilityError {
    /// `kind`.
    pub kind: ast::ModifierFlags,
    /// `declaringClass`.
    pub declaring_class: TypeId,
}

/// `type CallState struct` (checker.go:9047).
#[derive(Default)]
pub(crate) struct CallState {
    /// `node`.
    pub node: Option<NodeId>,
    /// `typeArguments`.
    pub type_arguments: Vec<NodeId>,
    /// `args`.
    pub args: Vec<NodeId>,
    /// `candidates`.
    pub candidates: Vec<SignatureId>,
    /// `argCheckMode`.
    pub arg_check_mode: CheckMode,
    /// `isSingleNonGenericCandidate`.
    pub is_single_non_generic_candidate: bool,
    /// `signatureHelpTrailingComma`.
    pub signature_help_trailing_comma: bool,
    /// `recursiveResolution`.
    pub recursive_resolution: bool,
    /// `candidatesForArgumentError`.
    pub candidates_for_argument_error: Vec<SignatureId>,
    /// `candidateForArgumentArityError`.
    pub candidate_for_argument_arity_error: Option<SignatureId>,
    /// `candidateForTypeArgumentError`.
    pub candidate_for_type_argument_error: Option<SignatureId>,
}

/// `someSignature` (checker.go:8927).
pub(crate) fn some_signature(
    c: &mut Checker,
    signatures: &[SignatureId],
    f: impl Fn(&mut Checker, SignatureId) -> bool,
) -> bool {
    for &sig in signatures {
        let composite = c.signature_arena.get(sig).composite.clone();
        match composite {
            Some(composite) if composite.is_union => {
                let mut some = false;
                for &s in &composite.signatures {
                    if f(c, s) {
                        some = true;
                        break;
                    }
                }
                if some {
                    return true;
                }
            }
            _ => {
                if composite.is_none() && f(c, sig) {
                    return true;
                }
            }
        }
    }
    false
}

/// `signatureHasLiteralTypes` (checker.go:9228).
pub(crate) fn signature_has_literal_types(s: &Signature) -> bool {
    s.flags.intersects(SignatureFlags::HAS_LITERAL_TYPES)
}

/// `acceptsVoid` (checker.go:9404).
pub(crate) fn accepts_void(types: &crate::types::TypeArena, t: TypeId) -> bool {
    types.get_ref(t).flags.intersects(TypeFlags::VOID)
}

impl Checker {
    /// `(c *Checker) checkTypeArguments` (checker.go:9447).
    pub(crate) fn check_type_arguments(
        &mut self,
        signature: SignatureId,
        type_argument_nodes: &[NodeId],
        report_errors: bool,
        head_message: Option<&'static tsc_diagnostics::Message>,
    ) -> Option<Vec<TypeId>> {
        let declaration = self.signature_arena.get(signature).declaration;
        let is_javascript =
            declaration.is_some_and(|d| ast::is_in_js_file(Some(d), &self.program_nodes(d)));
        let type_parameters = self.signature_arena.get(signature).type_parameters.clone();
        let min_type_argument_count = self.get_min_type_argument_count(&type_parameters);
        let type_argument_types_list: Vec<TypeId> = type_argument_nodes
            .iter()
            .map(|&n| self.get_type_from_type_node(n))
            .collect();
        let type_argument_types = self.fill_missing_type_arguments(
            &type_argument_types_list,
            &type_parameters,
            min_type_argument_count,
            is_javascript,
        );
        let mut mapper: Option<TypeMapperId> = None;
        for i in 0..type_argument_nodes.len() {
            debug_assert!(
                i < type_parameters.len(),
                "Should not call checkTypeArguments with too many type arguments"
            );
            let constraint = self.get_constraint_of_type_parameter(type_parameters[i]);
            if let Some(constraint) = constraint {
                let type_argument_head_message = head_message.or(Some(
                    &tsc_diagnostics::Type_0_does_not_satisfy_the_constraint_1,
                ));
                if mapper.is_none() {
                    mapper = Some(crate::mapper::new_type_mapper(
                        self,
                        type_parameters.clone(),
                        type_argument_types.clone(),
                    ));
                }
                let type_argument = type_argument_types[i];
                let error_node = if report_errors {
                    Some(type_argument_nodes[i])
                } else {
                    None
                };
                let mut diags: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
                let instantiated = self.instantiate_type(constraint, mapper);
                let target =
                    self.get_type_with_this_argument(instantiated, Some(type_argument), false);
                if !self.check_type_assignable_to_ex(
                    type_argument,
                    target,
                    error_node,
                    type_argument_head_message,
                    Some(&mut diags),
                ) {
                    if let Some(diagnostic) = diags.into_iter().next() {
                        let diagnostic = if head_message.is_some() {
                            ast::diagnostic::new_diagnostic_chain(
                                Some(&diagnostic),
                                &tsc_diagnostics::Type_0_does_not_satisfy_the_constraint_1,
                                &[] as &[String],
                            )
                        } else {
                            diagnostic
                        };
                        self.add_diagnostic(&diagnostic);
                    }
                    return None;
                }
            }
        }
        Some(type_argument_types)
    }

    /// `(c *Checker) isSignatureApplicable` (checker.go:9481).
    pub(crate) fn is_signature_applicable(
        &mut self,
        node: NodeId,
        args: &[NodeId],
        signature: SignatureId,
        relation: SharedRelation,
        check_mode: CheckMode,
        report_errors: bool,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let mut diagnostic_output = diagnostic_output;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_jsx_call_like(&nodes[node]) {
            return self.check_applicable_signature_for_jsx_call_like_element(
                node,
                signature,
                &relation,
                check_mode,
                report_errors,
                diagnostic_output.as_deref_mut(),
            );
        }
        let this_type = self.get_this_type_of_signature(signature);
        if let Some(this_type) = this_type {
            if this_type != self.void_type
                && !(ast::is_new_expression(&nodes[node])
                    || ast::is_call_expression(&nodes[node])
                        && nodes[node]
                            .expression()
                            .is_some_and(|e| ast::is_super_property(&nodes[e], &nodes)))
            {
                // If the called expression is not of the form `x.f` or `x["f"]`, then sourceType = voidType
                // If the signature's 'this' type is voidType, then the check is skipped -- anything is compatible.
                // If the expression is a new expression or super call expression, then the check is skipped.
                let this_argument_node = self.get_this_argument_of_call(node);
                let this_argument_type = self.get_this_argument_type(this_argument_node);
                let mut error_node = None;
                if report_errors {
                    error_node = this_argument_node;
                    if error_node.is_none() {
                        error_node = Some(node);
                    }
                }
                let head_message =
                    &tsc_diagnostics::The_this_context_of_type_0_is_not_assignable_to_method_s_this_of_type_1;
                if !self.check_type_related_to_ex(
                    this_argument_type,
                    this_type,
                    &relation,
                    error_node,
                    Some(head_message),
                    diagnostic_output.as_deref_mut(),
                ) {
                    return false;
                }
            }
        }
        let head_message =
            &tsc_diagnostics::Argument_of_type_0_is_not_assignable_to_parameter_of_type_1;
        let rest_type = self.get_non_array_rest_type(signature);
        let arg_count = if rest_type.is_some() {
            std::cmp::min(self.get_parameter_count(signature) as usize - 1, args.len())
        } else {
            args.len()
        };
        for i in 0..arg_count {
            let arg = args[i];
            if !ast::is_omitted_expression(&nodes[arg]) {
                let param_type = self.get_type_at_position(signature, i);
                let arg_type =
                    self.check_expression_with_contextual_type(arg, param_type, None, check_mode);
                // If one or more arguments are still excluded (as indicated by CheckMode.SkipContextSensitive),
                // we obtain the regular type of any object literal arguments because we may not have inferred complete
                // parameter types yet and therefore excess property checks may yield false positives (see #17041).
                let check_arg_type = if check_mode.intersects(CheckMode::SKIP_CONTEXT_SENSITIVE) {
                    self.get_regular_type_of_object_literal(arg_type)
                } else {
                    arg_type
                };
                let effective_check_argument_node = self.get_effective_check_node(arg);
                if !self.check_type_related_to_and_optionally_elaborate(
                    check_arg_type,
                    param_type,
                    &relation,
                    if report_errors {
                        Some(effective_check_argument_node)
                    } else {
                        None
                    },
                    Some(effective_check_argument_node),
                    Some(head_message),
                    diagnostic_output.as_deref_mut(),
                ) {
                    self.maybe_add_missing_await_info(
                        Some(arg),
                        check_arg_type,
                        param_type,
                        relation,
                        report_errors,
                        diagnostic_output,
                    );
                    return false;
                }
            }
        }
        if let Some(rest_type) = rest_type {
            let spread_type = self.get_spread_argument_type(
                args,
                arg_count as i32,
                args.len() as i32,
                rest_type,
                None,
                check_mode,
            );
            let rest_arg_count = args.len() - arg_count;
            let mut error_node = None;
            if report_errors {
                match rest_arg_count {
                    0 => error_node = Some(node),
                    1 => error_node = Some(self.get_effective_check_node(args[arg_count])),
                    _ => {
                        let synthetic =
                            self.create_synthetic_expression(node, spread_type, false, None);
                        // `errorNode.Loc = core.NewTextRange(args[argCount].Pos(), args[len(args)-1].End())`
                        let loc = tsc_core::text::TextRange::new(
                            nodes[args[arg_count]].loc.pos(),
                            nodes[args[args.len() - 1]].loc.end(),
                        );
                        self.program_nodes_mut(synthetic.file_index())[synthetic].loc = loc;
                        error_node = Some(synthetic);
                    }
                }
            }
            if !self.check_type_related_to_ex(
                spread_type,
                rest_type,
                &relation,
                error_node,
                Some(head_message),
                diagnostic_output.as_deref_mut(),
            ) {
                self.maybe_add_missing_await_info(
                    error_node,
                    spread_type,
                    rest_type,
                    relation,
                    report_errors,
                    diagnostic_output,
                );
                return false;
            }
        }
        true
    }

    /// `(c *Checker) maybeAddMissingAwaitInfo` (checker.go:9556).
    pub(crate) fn maybe_add_missing_await_info(
        &mut self,
        error_node: Option<NodeId>,
        source: TypeId,
        target: TypeId,
        relation: SharedRelation,
        report_errors: bool,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) {
        let diagnostic_output = match (error_node, diagnostic_output) {
            (Some(error_node), Some(output)) if report_errors && !output.is_empty() => {
                let _ = error_node;
                output
            }
            _ => return,
        };
        let error_node = error_node.unwrap();
        // Bail if target is Promise-like---something else is wrong
        if self.get_awaited_type_of_promise(target).is_some() {
            return;
        }
        let awaited_type_of_source = self.get_awaited_type_of_promise(source);
        if let Some(awaited_type_of_source) = awaited_type_of_source {
            if self.is_type_related_to(awaited_type_of_source, target, &relation) {
                let related = self.new_diagnostic_for_node(
                    Some(error_node),
                    &tsc_diagnostics::Did_you_forget_to_use_await,
                    &[] as &[String],
                );
                ast::diagnostic::lock_diagnostic(&diagnostic_output[0])
                    .add_related_info(Some(related));
            }
        }
    }

    /// `(c *Checker) getThisArgumentOfCall` (checker.go:9570).
    pub(crate) fn get_this_argument_of_call(&mut self, node: NodeId) -> Option<NodeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_binary_expression(&nodes[node]) {
            return nodes[node].as_binary_expression().right;
        }
        let mut expression = None;
        if ast::is_call_expression(&nodes[node]) {
            expression = nodes[node].expression();
        } else if ast::is_tagged_template_expression(&nodes[node]) {
            expression = nodes[node].as_tagged_template_expression().tag;
        } else if ast::is_decorator(&nodes[node]) && !self.legacy_decorators {
            expression = nodes[node].expression();
        }
        if let Some(expression) = expression {
            let callee = ast::utilities::skip_outer_expressions(
                expression,
                ast::utilities::outer_expression_kinds::ALL,
                &nodes,
            );
            if ast::is_access_expression(&nodes[callee]) {
                return nodes[callee].expression();
            }
        }
        None
    }

    /// `(c *Checker) getThisArgumentType` (checker.go:9592).
    pub(crate) fn get_this_argument_type(&mut self, node: Option<NodeId>) -> TypeId {
        let Some(node) = node else {
            return self.void_type;
        };
        let this_argument_type = self.check_expression(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent;
        match parent {
            Some(parent) if ast::is_optional_chain_root(&nodes[parent]) => {
                return self.get_non_nullable_type(this_argument_type);
            }
            Some(parent) if ast::is_optional_chain(&nodes[parent]) => {
                return self.remove_optional_type_marker(this_argument_type);
            }
            _ => {}
        }
        this_argument_type
    }

    /// `(c *Checker) getEffectiveCheckNode` (checker.go:9606).
    pub(crate) fn get_effective_check_node(&mut self, argument: NodeId) -> NodeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((argument).file_index());
        let flags = if ast::is_in_js_file(Some(argument), &nodes) {
            ast::utilities::outer_expression_kinds::PARENTHESES
                | ast::utilities::outer_expression_kinds::SATISFIES
                | ast::utilities::outer_expression_kinds::EXCLUDE_JS_DOC_TYPE_ASSERTION
        } else {
            ast::utilities::outer_expression_kinds::PARENTHESES
                | ast::utilities::outer_expression_kinds::SATISFIES
        };
        ast::utilities::skip_outer_expressions(argument, flags, &nodes)
    }

    /// `(c *Checker) inferTypeArguments` (checker.go:9615).
    pub(crate) fn infer_type_arguments(
        &mut self,
        node: NodeId,
        signature: SignatureId,
        args: &[NodeId],
        check_mode: CheckMode,
        context: InferenceContextId,
    ) -> Vec<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_jsx_opening_like_element(&nodes[node]) {
            return self.infer_jsx_type_arguments(node, signature, check_mode, context);
        }
        // If a contextual type is available, infer from that type to the return type of the call expression. For
        // example, given a 'function wrap<T, U>(cb: (x: T) => U): (x: T) => U' and a call expression
        // 'let f: (x: string) => number = wrap(s => s.length)', we infer from the declared type of 'f' to the
        // return type of 'wrap'.
        if !ast::is_decorator(&nodes[node]) && !ast::is_binary_expression(&nodes[node]) {
            let type_parameters = self.signature_arena.get(signature).type_parameters.clone();
            let skip_binding_patterns = type_parameters
                .iter()
                .all(|&p| self.get_default_from_type_parameter(p).is_some());
            let contextual_type = self.get_contextual_type(
                node,
                if skip_binding_patterns {
                    ContextFlags::SKIP_BINDING_PATTERNS
                } else {
                    ContextFlags::NONE
                },
            );
            if let Some(contextual_type) = contextual_type {
                let inference_target_type = self.get_return_type_of_signature(signature);
                if (self
                    .could_contain_type_variables
                    .clone()
                    .expect("could_contain_type_variables"))(
                    self, inference_target_type
                ) {
                    let outer_context = self.get_inference_context(node);
                    let is_from_binding_pattern = !skip_binding_patterns
                        && self.get_contextual_type(node, ContextFlags::SKIP_BINDING_PATTERNS)
                            != Some(contextual_type);
                    // A return type inference from a binding pattern can be used in instantiating the contextual
                    // type of an argument later in inference, but cannot stand on its own as the final return type.
                    // It is incorporated into `context.returnMapper` which is used in `instantiateContextualType`,
                    // but doesn't need to go into `context.inferences`. This allows a an array binding pattern to
                    // produce a tuple for `T` in
                    //   declare function f<T>(cb: () => T): T;
                    //   const [e1, e2, e3] = f(() => [1, "hi", true]);
                    // but does not produce any inference for `T` in
                    //   declare function f<T>(): T;
                    //   const [e1, e2, e3] = f();
                    if !is_from_binding_pattern {
                        // We clone the inference context to avoid disturbing a resolution in progress for an
                        // outer call expression. Effectively we just want a snapshot of whatever has been
                        // inferred for any outer call expression so far.
                        let cloned_outer_context =
                            self.clone_inference_context(outer_context, InferenceFlags::NO_DEFAULT);
                        let outer_mapper = self.get_mapper_from_context(cloned_outer_context);
                        let instantiated_type =
                            self.instantiate_type(contextual_type, outer_mapper);
                        // If the contextual type is a generic function type with a single call signature, we
                        // instantiate the type with its own type parameters and type arguments. This ensures that
                        // the type parameters are not erased to type any during type inference such that they can
                        // be inferred as actual types from the contextual type. For example:
                        //   declare function arrayMap<T, U>(f: (x: T) => U): (a: T[]) => U[];
                        //   const boxElements: <A>(a: A[]) => { value: A }[] = arrayMap(value => ({ value }));
                        // Above, the type of the 'value' parameter is inferred to be 'A'.
                        let contextual_signature =
                            self.get_single_call_signature(instantiated_type);
                        let inference_source_type =
                            if let Some(contextual_signature) = contextual_signature {
                                let sig_type_params = self
                                    .signature_arena
                                    .get(contextual_signature)
                                    .type_parameters
                                    .clone();
                                if !sig_type_params.is_empty() {
                                    let instantiated = self
                                    .get_signature_instantiation_without_filling_in_type_arguments(
                                        contextual_signature,
                                        &sig_type_params,
                                    );
                                    self.get_or_create_type_from_signature(instantiated)
                                } else {
                                    instantiated_type
                                }
                            } else {
                                instantiated_type
                            };
                        // Inferences made from return types have lower priority than all other inferences.
                        let mut inferences = std::mem::take(
                            &mut self.inference_contexts[context.index()].inferences,
                        );
                        self.infer_types(
                            &mut inferences,
                            inference_source_type,
                            inference_target_type,
                            InferencePriority::RETURN_TYPE,
                            false,
                        );
                        self.inference_contexts[context.index()].inferences = inferences;
                    }
                    // Create a type mapper for instantiating generic contextual types using the inferences made
                    // from the return type. We need a separate inference pass here because (a) instantiation of
                    // the source type uses the outer context's return mapper (which excludes inferences made from
                    // outer arguments), and (b) we don't want any further inferences going into this context.
                    // We use `createOuterReturnMapper` to ensure that all occurrences of outer type parameters are
                    // replaced with inferences produced from the outer return type or preceding outer arguments.
                    // This protects against circular inferences, i.e. avoiding situations where inferences reference
                    // type parameters for which the inferences are being made.
                    let context_flags = self.inference_contexts[context.index()].flags;
                    let return_context =
                        self.new_inference_context(type_parameters, signature, context_flags, None);
                    let mut outer_return_mapper = None;
                    if let Some(outer_context) = outer_context {
                        outer_return_mapper = self.create_outer_return_mapper(outer_context);
                    }
                    let return_source_type =
                        self.instantiate_type(contextual_type, outer_return_mapper);
                    let mut return_inferences = std::mem::take(
                        &mut self.inference_contexts[return_context.index()].inferences,
                    );
                    self.infer_types(
                        &mut return_inferences,
                        return_source_type,
                        inference_target_type,
                        InferencePriority::NONE,
                        false,
                    );
                    self.inference_contexts[return_context.index()].inferences = return_inferences;
                    if self.inference_contexts[return_context.index()]
                        .inferences
                        .iter()
                        .any(crate::inference::has_inference_candidates)
                    {
                        let cloned = self.clone_inferred_part_of_context(return_context);
                        let return_mapper = self.get_mapper_from_context(cloned);
                        self.inference_contexts[context.index()].return_mapper = return_mapper;
                    } else {
                        self.inference_contexts[context.index()].return_mapper = None;
                    }
                }
            }
        }
        let rest_type = self.get_non_array_rest_type(signature);
        let mut arg_count = args.len();
        if rest_type.is_some() {
            arg_count = std::cmp::min(self.get_parameter_count(signature) as usize - 1, arg_count);
        }
        if let Some(rest_type) = rest_type {
            if self
                .types_handle()
                .get_ref(rest_type)
                .flags
                .intersects(TypeFlags::TYPE_PARAMETER)
            {
                let info_index = self.inference_contexts[context.index()]
                    .inferences
                    .iter()
                    .position(|info| info.type_parameter == Some(rest_type));
                if let Some(info_index) = info_index {
                    let has_spread = args[arg_count..]
                        .iter()
                        .any(|&arg| crate::checker_d::is_spread_argument(&nodes, arg));
                    if !has_spread {
                        self.inference_contexts[context.index()].inferences[info_index]
                            .implied_arity = (args.len() - arg_count) as i32;
                    }
                }
            }
        }
        let this_type = self.get_this_type_of_signature(signature);
        if let Some(this_type) = this_type {
            if (self
                .could_contain_type_variables
                .clone()
                .expect("could_contain_type_variables"))(self, this_type)
            {
                let this_argument_node = self.get_this_argument_of_call(node);
                let this_argument_type = self.get_this_argument_type(this_argument_node);
                let mut inferences =
                    std::mem::take(&mut self.inference_contexts[context.index()].inferences);
                self.infer_types(
                    &mut inferences,
                    this_argument_type,
                    this_type,
                    InferencePriority::NONE,
                    false,
                );
                self.inference_contexts[context.index()].inferences = inferences;
            }
        }
        for i in 0..arg_count {
            let arg = args[i];
            if nodes[arg].kind != ast::Kind::OmittedExpression {
                let param_type = self.get_type_at_position(signature, i);
                if (self
                    .could_contain_type_variables
                    .clone()
                    .expect("could_contain_type_variables"))(self, param_type)
                {
                    let arg_type = self.check_expression_with_contextual_type(
                        arg,
                        param_type,
                        Some(context),
                        check_mode,
                    );
                    let mut inferences =
                        std::mem::take(&mut self.inference_contexts[context.index()].inferences);
                    self.infer_types(
                        &mut inferences,
                        arg_type,
                        param_type,
                        InferencePriority::NONE,
                        false,
                    );
                    self.inference_contexts[context.index()].inferences = inferences;
                }
            }
        }
        if let Some(rest_type) = rest_type {
            if (self
                .could_contain_type_variables
                .clone()
                .expect("could_contain_type_variables"))(self, rest_type)
            {
                let spread_type = self.get_spread_argument_type(
                    args,
                    arg_count as i32,
                    args.len() as i32,
                    rest_type,
                    Some(context),
                    check_mode,
                );
                let mut inferences =
                    std::mem::take(&mut self.inference_contexts[context.index()].inferences);
                self.infer_types(
                    &mut inferences,
                    spread_type,
                    rest_type,
                    InferencePriority::NONE,
                    false,
                );
                self.inference_contexts[context.index()].inferences = inferences;
            }
        }
        self.get_inferred_types(context)
    }

    /// `(c *Checker) getCandidateForOverloadFailure` (checker.go:9723).
    /// No signature was applicable. We have already reported the errors for
    /// the invalid signature.
    pub(crate) fn get_candidate_for_overload_failure(
        &mut self,
        node: NodeId,
        candidates: &mut Vec<SignatureId>,
        args: &[NodeId],
        has_candidates_out_array: bool,
        check_mode: CheckMode,
    ) -> SignatureId {
        // Else should not have called this.
        self.check_node_deferred(node);
        // Normally we will combine overloads. Skip this if they have type parameters since that's hard to combine.
        // Don't do this if there is a `candidatesOutArray`,
        // because then we want the chosen best candidate to be one of the overloads, not a combination.
        if has_candidates_out_array
            || candidates.len() == 1
            || candidates
                .iter()
                .any(|&s| !self.signature_arena.get(s).type_parameters.is_empty())
        {
            return self.pick_longest_candidate_signature(node, candidates, args, check_mode);
        }
        self.create_union_of_signatures_for_overload_failure(candidates)
    }

    /// `(c *Checker) pickLongestCandidateSignature` (checker.go:9735).
    pub(crate) fn pick_longest_candidate_signature(
        &mut self,
        node: NodeId,
        candidates: &mut Vec<SignatureId>,
        args: &[NodeId],
        check_mode: CheckMode,
    ) -> SignatureId {
        // Pick the longest signature. This way we can get a contextual type for cases like:
        //     declare function f(a: { xa: number; xb: number; }, b: number);
        //     f({ |
        // Also, use explicitly-supplied type arguments if they are provided, so we can get a contextual signature in cases like:
        //     declare function f<T>(k: keyof T);
        //     f<Foo>("
        let mut arg_count = args.len() as i32;
        if let Some(apparent_argument_count) = self.apparent_argument_count {
            arg_count = apparent_argument_count;
        }
        let best_index = self.get_longest_candidate_index(candidates, arg_count);
        let candidate = candidates[best_index as usize];
        let type_parameters = self.signature_arena.get(candidate).type_parameters.clone();
        if type_parameters.is_empty() {
            return candidate;
        }
        let mut type_argument_nodes: Vec<NodeId> = Vec::new();
        if self.call_like_expression_may_have_type_arguments(node) {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            if let Some(ta) = nodes[node].type_arguments() {
                type_argument_nodes = ta.to_vec();
            }
        }
        let instantiated = if !type_argument_nodes.is_empty() {
            let type_args =
                self.get_type_arguments_from_nodes(&type_argument_nodes, &type_parameters);
            self.create_signature_instantiation(candidate, &type_args)
        } else {
            self.infer_signature_instantiation_for_overload_failure(
                node,
                &type_parameters,
                candidate,
                args,
                check_mode,
            )
        };
        candidates[best_index as usize] = instantiated;
        instantiated
    }

    /// `(c *Checker) getLongestCandidateIndex` (checker.go:9766).
    pub(crate) fn get_longest_candidate_index(
        &mut self,
        candidates: &[SignatureId],
        args_count: i32,
    ) -> i32 {
        let mut max_params_index = -1;
        let mut max_params = -1;
        for (i, &candidate) in candidates.iter().enumerate() {
            let param_count = self.get_parameter_count(candidate) as i32;
            if self.has_effective_rest_parameter(candidate) || param_count >= args_count {
                return i as i32;
            }
            if param_count > max_params {
                max_params = param_count;
                max_params_index = i as i32;
            }
        }
        max_params_index
    }

    /// `(c *Checker) getTypeArgumentsFromNodes` (checker.go:9782).
    pub(crate) fn get_type_arguments_from_nodes(
        &mut self,
        type_argument_nodes: &[NodeId],
        type_parameters: &[TypeId],
    ) -> Vec<TypeId> {
        let type_argument_nodes = if type_argument_nodes.len() > type_parameters.len() {
            &type_argument_nodes[..type_parameters.len()]
        } else {
            type_argument_nodes
        };
        let mut type_arguments: Vec<TypeId> = type_argument_nodes
            .iter()
            .map(|&n| self.get_type_from_type_node(n))
            .collect();
        while type_arguments.len() < type_parameters.len() {
            let mut t = self.get_default_from_type_parameter(type_parameters[type_arguments.len()]);
            if t.is_none() {
                t = self.get_constraint_of_type_parameter(type_parameters[type_arguments.len()]);
                if t.is_none() {
                    t = Some(self.unknown_type);
                }
            }
            type_arguments.push(t.unwrap());
        }
        type_arguments
    }

    /// `(c *Checker) inferSignatureInstantiationForOverloadFailure` (checker.go:9800).
    pub(crate) fn infer_signature_instantiation_for_overload_failure(
        &mut self,
        node: NodeId,
        type_parameters: &[TypeId],
        candidate: SignatureId,
        args: &[NodeId],
        check_mode: CheckMode,
    ) -> SignatureId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let inference_context = self.new_inference_context(
            type_parameters.to_vec(),
            candidate,
            if ast::is_in_js_file(Some(node), &nodes) {
                InferenceFlags::ANY_DEFAULT
            } else {
                InferenceFlags::NONE
            },
            None,
        );
        let type_argument_types = self.infer_type_arguments(
            node,
            candidate,
            args,
            check_mode | CheckMode::SKIP_CONTEXT_SENSITIVE | CheckMode::SKIP_GENERIC_FUNCTIONS,
            inference_context,
        );
        self.create_signature_instantiation(candidate, &type_argument_types)
    }

    /// `(c *Checker) createUnionOfSignaturesForOverloadFailure` (checker.go:9806).
    pub(crate) fn create_union_of_signatures_for_overload_failure(
        &mut self,
        candidates: &[SignatureId],
    ) -> SignatureId {
        let this_parameters: Vec<SymbolId> = candidates
            .iter()
            .filter_map(|&s| self.signature_arena.get(s).this_parameter)
            .collect();
        let mut this_parameter = None;
        if !this_parameters.is_empty() {
            let types: Vec<TypeId> = this_parameters
                .iter()
                .map(|&p| self.get_type_of_parameter(p))
                .collect();
            this_parameter = Some(self.create_combined_symbol_from_types(&this_parameters, types));
        }
        let (min_argument_count, max_non_rest_param) =
            crate::utilities::min_and_max(candidates, |s| {
                crate::utilities::get_non_rest_parameter_count(self.signature_arena.get(s))
            });
        let mut parameters: Vec<SymbolId> = Vec::with_capacity(max_non_rest_param as usize);
        for i in 0..max_non_rest_param {
            let symbols: Vec<SymbolId> = candidates
                .iter()
                .filter_map(|&s| {
                    let sig = self.signature_arena.get(s);
                    if crate::checker_c::signature_has_rest_parameter(sig) {
                        if (i as usize) < sig.parameters.len() - 1 {
                            return Some(sig.parameters[i as usize]);
                        }
                        return sig.parameters.last().copied();
                    }
                    if (i as usize) < sig.parameters.len() {
                        return Some(sig.parameters[i as usize]);
                    }
                    None
                })
                .collect();
            let types: Vec<TypeId> = candidates
                .iter()
                .filter_map(|&s| self.try_get_type_at_position(s, i))
                .collect();
            parameters.push(self.create_combined_symbol_from_types(&symbols, types));
        }
        let rest_parameter_symbols: Vec<SymbolId> = candidates
            .iter()
            .filter_map(|&s| {
                let sig = self.signature_arena.get(s);
                if crate::checker_c::signature_has_rest_parameter(sig) {
                    return sig.parameters.last().copied();
                }
                None
            })
            .collect();
        let mut flags = SignatureFlags::IS_SIGNATURE_CANDIDATE_FOR_OVERLOAD_FAILURE;
        if !rest_parameter_symbols.is_empty() {
            let rest_types: Vec<TypeId> = candidates
                .iter()
                .filter_map(|&s| self.try_get_rest_type_of_signature(s))
                .collect();
            let union = self.get_union_type_ex(&rest_types, UnionReduction::Subtype, None, None);
            let t = self.create_array_type(union);
            parameters
                .push(self.create_combined_symbol_for_overload_failure(&rest_parameter_symbols, t));
            flags |= SignatureFlags::HAS_REST_PARAMETER;
        }
        if candidates
            .iter()
            .any(|&s| signature_has_literal_types(self.signature_arena.get(s)))
        {
            flags |= SignatureFlags::HAS_LITERAL_TYPES;
        }
        let return_types: Vec<TypeId> = candidates
            .iter()
            .map(|&s| self.get_return_type_of_signature(s))
            .collect();
        let return_type = self.get_intersection_type(&return_types);
        self.new_signature(
            flags,
            self.signature_arena.get(candidates[0]).declaration,
            Vec::new(),
            this_parameter,
            parameters,
            Some(return_type),
            None,
            min_argument_count as i32,
        )
    }

    /// `(c *Checker) createCombinedSymbolFromTypes` (checker.go:9847).
    pub(crate) fn create_combined_symbol_from_types(
        &mut self,
        sources: &[SymbolId],
        types: Vec<TypeId>,
    ) -> SymbolId {
        let union = self.get_union_type_ex(&types, UnionReduction::Subtype, None, None);
        self.create_combined_symbol_for_overload_failure(sources, union)
    }

    /// `(c *Checker) createCombinedSymbolForOverloadFailure` (checker.go:9851).
    pub(crate) fn create_combined_symbol_for_overload_failure(
        &mut self,
        sources: &[SymbolId],
        t: TypeId,
    ) -> SymbolId {
        // This function is currently only used for erroneous overloads, so it's good enough to just use the first source.
        self.create_symbol_with_type(sources.first().copied(), Some(t))
    }

    /// `(c *Checker) getRestTypeOfSignature` (checker.go:9856).
    pub fn get_rest_type_of_signature(&mut self, signature: SignatureId) -> TypeId {
        self.try_get_rest_type_of_signature(signature)
            .unwrap_or(self.any_type)
    }

    /// `(c *Checker) tryGetRestTypeOfSignature` (checker.go:9860).
    pub(crate) fn try_get_rest_type_of_signature(
        &mut self,
        signature: SignatureId,
    ) -> Option<TypeId> {
        if !crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(signature)) {
            return None;
        }
        let mut rest_type = self.get_type_of_symbol(
            *self
                .signature_arena
                .get(signature)
                .parameters
                .last()
                .unwrap(),
        );
        if crate::utilities::is_tuple_type(&self.types, rest_type) {
            rest_type = self.get_rest_type_of_tuple_type(rest_type)?;
        }
        self.get_index_type_of_type(rest_type, self.number_type)
    }
}

impl Checker {
    /// `(c *Checker) reportCallResolutionErrors` (checker.go:9874).
    pub(crate) fn report_call_resolution_errors(
        &mut self,
        node: NodeId,
        s: &CallState,
        signatures: &[SignatureId],
        head_message: Option<&'static tsc_diagnostics::Message>,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !s.candidates_for_argument_error.is_empty() {
            let last = *s.candidates_for_argument_error.last().unwrap();
            let mut diags: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
            self.is_signature_applicable(
                s.node.unwrap(),
                &s.args,
                last,
                self.assignable_relation.clone(),
                CheckMode::NORMAL,
                true, /*reportErrors*/
                Some(&mut diags),
            );
            for diagnostic in diags {
                let mut diagnostic = diagnostic;
                if s.candidates_for_argument_error.len() > 1 {
                    diagnostic = ast::diagnostic::new_diagnostic_chain(
                        Some(&diagnostic),
                        &tsc_diagnostics::The_last_overload_gave_the_following_error,
                        &[] as &[String],
                    );
                    diagnostic = ast::diagnostic::new_diagnostic_chain(
                        Some(&diagnostic),
                        &tsc_diagnostics::No_overload_matches_this_call,
                        &[] as &[String],
                    );
                }
                if let Some(head_message) = head_message {
                    diagnostic = ast::diagnostic::new_diagnostic_chain(
                        Some(&diagnostic),
                        head_message,
                        &[] as &[String],
                    );
                }
                let last_declaration = self.signature_arena.get(last).declaration;
                if last_declaration.is_some() && s.candidates_for_argument_error.len() > 1 {
                    let related = self.new_diagnostic_for_node(
                        last_declaration,
                        &tsc_diagnostics::The_last_overload_is_declared_here,
                        &[] as &[String],
                    );
                    ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(related));
                }
                self.add_implementation_success_elaboration(s, last, &diagnostic);
                self.add_diagnostic(&diagnostic);
            }
        } else if let Some(candidate_for_argument_arity_error) =
            s.candidate_for_argument_arity_error
        {
            let diagnostic = self.get_argument_arity_error(
                s.node.unwrap(),
                &[candidate_for_argument_arity_error],
                &s.args,
                head_message,
            );
            self.add_diagnostic(&diagnostic);
        } else if let Some(candidate_for_type_argument_error) = s.candidate_for_type_argument_error
        {
            let type_arguments = s
                .node
                .and_then(|n| {
                    self.program_nodes(n)[n]
                        .type_arguments()
                        .map(|a| a.to_vec())
                })
                .unwrap_or_default();
            self.check_type_arguments(
                candidate_for_type_argument_error,
                &type_arguments,
                true, /*reportErrors*/
                head_message,
            );
        } else if !ast::is_jsx_opening_fragment(&nodes[node]) {
            let signatures_with_correct_type_argument_arity: Vec<SignatureId> = signatures
                .iter()
                .copied()
                .filter(|&sig| self.has_correct_type_argument_arity(sig, &s.type_arguments))
                .collect();
            if signatures_with_correct_type_argument_arity.is_empty() {
                let diagnostic = self.get_type_argument_arity_error(
                    s.node.unwrap(),
                    signatures,
                    &s.type_arguments,
                    head_message,
                );
                self.add_diagnostic(&diagnostic);
            } else {
                let diagnostic = self.get_argument_arity_error(
                    s.node.unwrap(),
                    &signatures_with_correct_type_argument_arity,
                    &s.args,
                    head_message,
                );
                self.add_diagnostic(&diagnostic);
            }
        }
    }

    /// `(c *Checker) addImplementationSuccessElaboration` (checker.go:9910).
    pub(crate) fn add_implementation_success_elaboration(
        &mut self,
        s: &CallState,
        failed: SignatureId,
        diagnostic: &ast::diagnostic::DiagnosticRef,
    ) {
        let declaration = self.signature_arena.get(failed).declaration;
        let Some(declaration) = declaration else {
            return;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((declaration).file_index());
        let Some(symbol) = nodes[declaration].symbol() else {
            return;
        };
        let declarations = self.sym(symbol).declarations.clone();
        if declarations.len() > 1 {
            let implementation = declarations.iter().copied().find(|&d| {
                ast::is_function_like_declaration(Some(d), &nodes)
                    && !ast::node_is_missing(nodes[d].body(), &nodes)
            });
            if let Some(implementation) = implementation {
                let candidate = self.get_signature_from_declaration(implementation);
                let mut local_state = CallState {
                    candidates: vec![candidate],
                    is_single_non_generic_candidate: self
                        .signature_arena
                        .get(candidate)
                        .type_parameters
                        .is_empty(),
                    ..CallState {
                        node: s.node,
                        type_arguments: s.type_arguments.clone(),
                        args: s.args.clone(),
                        candidates: Vec::new(),
                        arg_check_mode: s.arg_check_mode,
                        is_single_non_generic_candidate: false,
                        signature_help_trailing_comma: s.signature_help_trailing_comma,
                        recursive_resolution: s.recursive_resolution,
                        candidates_for_argument_error: Vec::new(),
                        candidate_for_argument_arity_error: None,
                        candidate_for_type_argument_error: None,
                    }
                };
                if self
                    .choose_overload(&mut local_state, &self.assignable_relation.clone())
                    .is_some()
                {
                    let related = self.new_diagnostic_for_node(
                        Some(implementation),
                        &tsc_diagnostics::The_call_would_have_succeeded_against_this_implementation_but_implementation_signatures_of_overloads_are_not_externally_visible,
                        &[] as &[String],
                    );
                    ast::diagnostic::lock_diagnostic(diagnostic).add_related_info(Some(related));
                }
            }
        }
    }

    /// `(c *Checker) getArgumentArityError` (checker.go:9930).
    pub(crate) fn get_argument_arity_error(
        &mut self,
        node: NodeId,
        signatures: &[SignatureId],
        args: &[NodeId],
        head_message: Option<&'static tsc_diagnostics::Message>,
    ) -> ast::diagnostic::DiagnosticRef {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let spread_index = crate::checker_d::get_spread_argument_index(args, &nodes);
        if spread_index > -1 {
            return self.new_diagnostic_for_node(
                Some(args[spread_index as usize]),
                &tsc_diagnostics::A_spread_argument_must_either_have_a_tuple_type_or_be_passed_to_a_rest_parameter,
                &[] as &[String],
            );
        }
        let mut min_count = i32::MAX; // smallest parameter count
        let mut max_count = i32::MIN; // largest parameter count
        let mut max_below = i32::MIN; // largest parameter count that is smaller than the number of arguments
        let mut min_above = i32::MAX; // smallest parameter count that is larger than the number of arguments
        let mut closest_signature = None;
        for &sig in signatures {
            let min_parameter = self.get_min_argument_count(sig);
            let max_parameter = self.get_parameter_count(sig) as i32;
            // smallest/largest parameter counts
            if min_parameter < min_count {
                min_count = min_parameter;
                closest_signature = Some(sig);
            }
            max_count = max_count.max(max_parameter);
            // shortest parameter count *longer than the call*/longest parameter count *shorter than the call*
            if min_parameter < args.len() as i32 && min_parameter > max_below {
                max_below = min_parameter;
            }
            if (args.len() as i32) < max_parameter && max_parameter < min_above {
                min_above = max_parameter;
            }
        }
        let has_rest_parameter = signatures
            .iter()
            .any(|&s| self.has_effective_rest_parameter(s));
        let parameter_range = if has_rest_parameter {
            min_count.to_string()
        } else if min_count < max_count {
            format!("{}-{}", min_count, max_count)
        } else {
            min_count.to_string()
        };
        let is_void_promise_error = !has_rest_parameter
            && parameter_range == "1"
            && args.is_empty()
            && self.is_promise_resolve_arity_error(node);
        let error_node = get_error_node_for_call_node(node, &nodes);
        if is_void_promise_error && ast::is_in_js_file(Some(node), &nodes) {
            return self.new_diagnostic_for_node(
                Some(error_node),
                &tsc_diagnostics::Expected_1_argument_but_got_0_new_Promise_needs_a_JSDoc_hint_to_produce_a_resolve_that_can_be_called_without_arguments,
                &[] as &[String],
            );
        }
        let message = if ast::is_decorator(&nodes[node]) {
            if has_rest_parameter {
                &tsc_diagnostics::The_runtime_will_invoke_the_decorator_with_1_arguments_but_the_decorator_expects_at_least_0
            } else {
                &tsc_diagnostics::The_runtime_will_invoke_the_decorator_with_1_arguments_but_the_decorator_expects_0
            }
        } else if has_rest_parameter {
            &tsc_diagnostics::Expected_at_least_0_arguments_but_got_1
        } else if is_void_promise_error {
            &tsc_diagnostics::Expected_0_arguments_but_got_1_Did_you_forget_to_include_void_in_your_type_argument_to_Promise
        } else {
            &tsc_diagnostics::Expected_0_arguments_but_got_1
        };
        if min_count < args.len() as i32 && (args.len() as i32) < max_count {
            // between min and max, but with no matching overload
            let diagnostic = self.new_diagnostic_for_node(
                Some(error_node),
                &tsc_diagnostics::No_overload_expects_0_arguments_but_overloads_do_exist_that_expect_either_1_or_2_arguments,
                &[args.len().to_string(), max_below.to_string(), min_above.to_string()],
            );
            if let Some(head_message) = head_message {
                return ast::diagnostic::new_diagnostic_chain(
                    Some(&diagnostic),
                    head_message,
                    &[] as &[String],
                );
            }
            return diagnostic;
        }
        if (args.len() as i32) < min_count {
            // too short: put the error span on the call expression, not any of the args
            let diagnostic = self.new_diagnostic_for_node(
                Some(error_node),
                message,
                &[parameter_range, args.len().to_string()],
            );
            let diagnostic = if let Some(head_message) = head_message {
                ast::diagnostic::new_diagnostic_chain(
                    Some(&diagnostic),
                    head_message,
                    &[] as &[String],
                )
            } else {
                diagnostic
            };
            let mut parameter = None;
            if let Some(closest_signature) = closest_signature {
                if let Some(closest_declaration) =
                    self.signature_arena.get(closest_signature).declaration
                {
                    let __program = self.program.clone().expect("program");
                    let decl_nodes = __program.nodes((closest_declaration).file_index());
                    let index = args.len()
                        + if self
                            .signature_arena
                            .get(closest_signature)
                            .this_parameter
                            .is_some()
                        {
                            1
                        } else {
                            0
                        };
                    if let Some(params) = decl_nodes[closest_declaration].parameters() {
                        parameter = params.get(index).copied();
                    }
                }
            }
            if let Some(parameter) = parameter {
                let __program = self.program.clone().expect("program");
                let param_nodes = __program.nodes((parameter).file_index());
                let related = if param_nodes[parameter]
                    .name()
                    .is_some_and(|n| ast::is_binding_pattern(&param_nodes[n]))
                {
                    self.new_diagnostic_for_node(
                        Some(parameter),
                        &tsc_diagnostics::An_argument_matching_this_binding_pattern_was_not_provided,
                        &[] as &[String],
                    )
                } else if crate::utilities::is_rest_parameter(&param_nodes[parameter], &param_nodes)
                {
                    self.new_diagnostic_for_node(
                        Some(parameter),
                        &tsc_diagnostics::Arguments_for_the_rest_parameter_0_were_not_provided,
                        &[param_nodes[parameter]
                            .name()
                            .map(|n| param_nodes[n].text(&param_nodes).into_owned())
                            .unwrap_or_default()],
                    )
                } else {
                    self.new_diagnostic_for_node(
                        Some(parameter),
                        &tsc_diagnostics::An_argument_for_0_was_not_provided,
                        &[param_nodes[parameter]
                            .name()
                            .map(|n| param_nodes[n].text(&param_nodes).into_owned())
                            .unwrap_or_default()],
                    )
                };
                ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(related));
            }
            return diagnostic;
        }
        // Guard against out-of-bounds access when maxCount >= len(args).
        // This can happen when we reach this fallback error path but the argument
        // count actually matches the parameter count (e.g., due to trailing commas
        // causing signature resolution to fail for other reasons).
        if max_count >= args.len() as i32 {
            let diagnostic = self.new_diagnostic_for_node(
                Some(error_node),
                message,
                &[parameter_range, args.len().to_string()],
            );
            if let Some(head_message) = head_message {
                return ast::diagnostic::new_diagnostic_chain(
                    Some(&diagnostic),
                    head_message,
                    &[] as &[String],
                );
            }
            return diagnostic;
        }
        let source_file = ast::get_source_file_of_node(Some(node), &nodes);
        let mut pos = nodes[args[max_count as usize]].loc.pos();
        let mut end = nodes[args[args.len() - 1]].loc.end();
        if end == pos {
            end += 1;
        }
        let file_text = source_file
            .map(|sf| nodes[sf].as_source_file().text().to_string())
            .unwrap_or_default();
        pos = tsc_scanner::scanner::skip_trivia(&file_text, pos);
        if end < pos {
            end = pos;
        }
        let diagnostic = ast::diagnostic::new_diagnostic(
            source_file.map(|sf| ast::diagnostic::DiagnosticFile::from_node(sf, &nodes)),
            tsc_core::text::TextRange::new(pos, end),
            message,
            &[parameter_range, args.len().to_string()],
        );
        if let Some(head_message) = head_message {
            return ast::diagnostic::new_diagnostic_chain(
                Some(&diagnostic),
                head_message,
                &[] as &[String],
            );
        }
        diagnostic
    }

    /// `(c *Checker) isPromiseResolveArityError` (checker.go:10048).
    pub(crate) fn is_promise_resolve_arity_error(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_call_expression(&nodes[node])
            || !nodes[node]
                .expression()
                .is_some_and(|e| ast::is_identifier(&nodes[e]))
        {
            return false;
        }
        let expression = nodes[node].expression().unwrap();
        let resolve = self
            .resolve_name
            .clone()
            .expect("resolveName not initialized");
        let symbol = resolve(
            self,
            Some(expression),
            &nodes[expression].text(&nodes),
            ast::SymbolFlags::VALUE,
            None,
            false,
            false,
        );
        let Some(symbol) = symbol else {
            return false;
        };
        let decl = self.sym(symbol).value_declaration;
        let Some(decl) = decl else {
            return false;
        };
        let __program = self.program.clone().expect("program");
        let decl_nodes = __program.nodes((decl).file_index());
        if !ast::is_parameter_declaration(&decl_nodes[decl])
            || !decl_nodes[decl]
                .parent
                .is_some_and(|p| ast::is_function_expression_or_arrow_function(&decl_nodes[p]))
            || !decl_nodes[decl]
                .parent
                .and_then(|p| decl_nodes[p].parent)
                .is_some_and(|pp| ast::is_new_expression(&decl_nodes[pp]))
            || !decl_nodes[decl]
                .parent
                .and_then(|p| decl_nodes[p].parent)
                .and_then(|pp| decl_nodes[pp].expression())
                .is_some_and(|e| ast::is_identifier(&decl_nodes[e]))
        {
            return false;
        }
        let global_promise_symbol = self
            .get_global_promise_constructor_symbol_or_nil
            .clone()
            .and_then(|thunk| thunk(self));
        let Some(global_promise_symbol) = global_promise_symbol else {
            return false;
        };
        let new_expr_expr = decl_nodes[decl]
            .parent
            .and_then(|p| decl_nodes[p].parent)
            .and_then(|pp| decl_nodes[pp].expression())
            .unwrap();
        let constructor_symbol = self.get_resolved_symbol(new_expr_expr);
        constructor_symbol == global_promise_symbol
    }
}

/// `getErrorNodeForCallNode` (checker.go:10068).
pub(crate) fn get_error_node_for_call_node(node: NodeId, nodes: &[ast::Node]) -> NodeId {
    let mut node = node;
    if ast::is_call_expression(&nodes[node]) {
        node = nodes[node].expression().expect("call expression");
        if ast::is_property_access_expression(&nodes[node]) {
            node = nodes[node].name().expect("property access name");
        }
    }
    node
}

/// `c.resolveName(...)` — invoke the binder name-resolver thunk stored in
/// `Checker::resolve_name`. PORT: identical to checker_a's private
/// `call_resolve_name`; duplicated here because module-private helpers are
/// not shared across files.
#[inline]
fn call_resolve_name(
    c: &mut Checker,
    location: Option<NodeId>,
    name: &str,
    meaning: ast::SymbolFlags,
    name_not_found_message: Option<&'static tsc_diagnostics::Message>,
    is_use: bool,
    exclude_globals: bool,
    live_nodes: Option<&[ast::Node]>,
) -> Option<SymbolId> {
    if live_nodes.is_some() {
        return c.resolve_name_via_binder_live(
            location,
            name,
            meaning,
            name_not_found_message,
            is_use,
            exclude_globals,
            live_nodes,
        );
    }
    let f = c.resolve_name.clone().expect("Checker::resolve_name");
    f(
        c,
        location,
        name,
        meaning,
        name_not_found_message,
        is_use,
        exclude_globals,
    )
}

impl Checker {
    /// `(c *Checker) getTypeArgumentArityError` (checker.go:10078).
    pub(crate) fn get_type_argument_arity_error(
        &mut self,
        node: NodeId,
        signatures: &[SignatureId],
        type_arguments: &[NodeId],
        head_message: Option<&'static tsc_diagnostics::Message>,
    ) -> ast::diagnostic::DiagnosticRef {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let arg_count = type_arguments.len() as i32;
        let source_file = ast::get_source_file_of_node(Some(node), &nodes);
        let type_argument_list = nodes[node].type_argument_list();
        let file_text = source_file
            .map(|sf| nodes[sf].as_source_file().text().to_string())
            .unwrap_or_default();
        let loc = tsc_core::text::TextRange::new(
            tsc_scanner::scanner::skip_trivia(&file_text, type_argument_list.unwrap().loc.pos()),
            type_argument_list.unwrap().loc.end(),
        );
        let diagnostic;
        if signatures.len() == 1 {
            // No overloads exist
            let sig = signatures[0];
            let type_parameters = self.signature_arena.get(sig).type_parameters.clone();
            let min_count = self.get_min_type_argument_count(&type_parameters) as i32;
            let max_count = type_parameters.len() as i32;
            let mut expected = min_count.to_string();
            if min_count < max_count {
                expected = format!("{}-{}", expected, max_count);
            }
            diagnostic = ast::diagnostic::new_diagnostic(
                source_file.map(|sf| ast::diagnostic::DiagnosticFile::from_node(sf, &nodes)),
                loc,
                &tsc_diagnostics::Expected_0_type_arguments_but_got_1,
                &[expected, arg_count.to_string()],
            );
        } else {
            // Overloads exist
            let mut below_arg_count = i32::MIN;
            let mut above_arg_count = i32::MAX;
            for &sig in signatures {
                let type_parameters = self.signature_arena.get(sig).type_parameters.clone();
                let min_count = self.get_min_type_argument_count(&type_parameters) as i32;
                let max_count = type_parameters.len() as i32;
                if min_count > arg_count {
                    above_arg_count = above_arg_count.min(min_count);
                } else if max_count < arg_count {
                    below_arg_count = below_arg_count.max(max_count);
                }
            }
            if below_arg_count != i32::MIN && above_arg_count != i32::MAX {
                diagnostic = ast::diagnostic::new_diagnostic(
                    source_file
                        .map(|sf| ast::diagnostic::DiagnosticFile::from_node(sf, &nodes)),
                    loc,
                    &tsc_diagnostics::No_overload_expects_0_type_arguments_but_overloads_do_exist_that_expect_either_1_or_2_type_arguments,
                    &[
                        arg_count.to_string(),
                        below_arg_count.to_string(),
                        above_arg_count.to_string(),
                    ],
                );
            } else {
                diagnostic = ast::diagnostic::new_diagnostic(
                    source_file.map(|sf| ast::diagnostic::DiagnosticFile::from_node(sf, &nodes)),
                    loc,
                    &tsc_diagnostics::Expected_0_type_arguments_but_got_1,
                    &[
                        if below_arg_count == i32::MIN {
                            above_arg_count.to_string()
                        } else {
                            below_arg_count.to_string()
                        },
                        arg_count.to_string(),
                    ],
                );
            }
        }
        if let Some(head_message) = head_message {
            return ast::diagnostic::new_diagnostic_chain(
                Some(&diagnostic),
                head_message,
                &[] as &[String],
            );
        }
        diagnostic
    }

    /// `(c *Checker) reportCannotInvokePossiblyNullOrUndefinedError` (checker.go:10119).
    pub(crate) fn report_cannot_invoke_possibly_null_or_undefined_error(
        &mut self,
        node: NodeId,
        facts: TypeFacts,
    ) {
        self.error(
            Some(node),
            if facts.intersects(TypeFacts::IS_UNDEFINED) {
                if facts.intersects(TypeFacts::IS_NULL) {
                    &tsc_diagnostics::Cannot_invoke_an_object_which_is_possibly_null_or_undefined
                } else {
                    &tsc_diagnostics::Cannot_invoke_an_object_which_is_possibly_undefined
                }
            } else {
                &tsc_diagnostics::Cannot_invoke_an_object_which_is_possibly_null
            },
            &[] as &[String],
        );
    }

    /// `(c *Checker) resolveUntypedCall` (checker.go:10127).
    pub(crate) fn resolve_untyped_call(&mut self, node: NodeId) -> SignatureId {
        if self.call_like_expression_may_have_type_arguments(node) {
            // Check type arguments even though we will give an error that untyped calls may not accept type arguments.
            // This gets us diagnostics for the type arguments and marks them as referenced.
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let type_arguments = nodes[node].type_arguments().map(|a| a.to_vec());
            if let Some(type_arguments) = type_arguments {
                self.check_source_elements(&type_arguments);
            }
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::TaggedTemplateExpression => {
                let template = nodes[node].as_tagged_template_expression().template;
                if let Some(template) = template {
                    self.check_expression(template);
                }
            }
            ast::Kind::JsxOpeningElement | ast::Kind::JsxSelfClosingElement => {
                if let Some(attributes) = nodes[node].attributes() {
                    self.check_expression(attributes);
                }
            }
            ast::Kind::BinaryExpression => {
                let left = nodes[node].as_binary_expression().left;
                if let Some(left) = left {
                    self.check_expression(left);
                }
            }
            ast::Kind::CallExpression | ast::Kind::NewExpression => {
                if let Some(arguments) = nodes[node].arguments().map(|a| a.to_vec()) {
                    for argument in arguments {
                        self.check_expression(argument);
                    }
                }
            }
            _ => {}
        }
        self.any_signature
    }

    /// `(c *Checker) resolveErrorCall` (checker.go:10148).
    pub(crate) fn resolve_error_call(&mut self, node: NodeId) -> SignatureId {
        self.resolve_untyped_call(node);
        self.unknown_signature
    }

    /// `(c *Checker) isUntypedFunctionCall` (checker.go:10158).
    /// TS 1.0 spec: 4.12
    /// If FuncExpr is of type Any, or of an object type that has no call or construct signatures
    /// but is a subtype of the Function interface, the call is an untyped function call.
    pub(crate) fn is_untyped_function_call(
        &mut self,
        func_type: TypeId,
        apparent_func_type: TypeId,
        num_call_signatures: i32,
        num_construct_signatures: i32,
    ) -> bool {
        // We exclude union types because we may have a union of function types that happen to have no common signatures.
        crate::types::is_type_any(&self.types, func_type)
            || crate::types::is_type_any(&self.types, apparent_func_type)
                && self
                    .types_handle()
                    .get(func_type)
                    .flags
                    .intersects(TypeFlags::TYPE_PARAMETER)
            || num_call_signatures == 0
                && num_construct_signatures == 0
                && !self
                    .types_handle()
                    .get(apparent_func_type)
                    .flags
                    .intersects(TypeFlags::UNION)
                && {
                    let reduced = self.get_reduced_type(apparent_func_type);
                    !self
                        .types_handle()
                        .get(reduced)
                        .flags
                        .intersects(TypeFlags::NEVER)
                }
                && self.is_type_assignable_to(func_type, self.global_function_type)
    }

    /// `(c *Checker) invocationErrorDetails` (checker.go:10165).
    pub(crate) fn invocation_error_details(
        &mut self,
        error_target: NodeId,
        apparent_type: TypeId,
        kind: SignatureKind,
    ) -> ast::diagnostic::DiagnosticRef {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((error_target).file_index());
        let mut diagnostic: Option<ast::diagnostic::DiagnosticRef> = None;
        let is_call = kind == SignatureKind::Call;
        let awaited_type = self.get_awaited_type(apparent_type);
        let maybe_missing_await =
            awaited_type.is_some_and(|t| !self.get_signatures_of_type(t, kind).is_empty());
        let mut target = error_target;
        if ast::is_property_access_expression(&nodes[error_target])
            && nodes[error_target]
                .parent
                .is_some_and(|p| ast::is_call_expression(&nodes[p]))
        {
            target = nodes[error_target].name().unwrap_or(error_target);
        }
        if self
            .types_handle()
            .get_ref(apparent_type)
            .flags
            .intersects(TypeFlags::UNION)
        {
            let types = self.types.get_ref(apparent_type).types().to_vec();
            let mut has_signatures = false;
            for constituent in types {
                let signatures = self.get_signatures_of_type(constituent, kind);
                if !signatures.is_empty() {
                    has_signatures = true;
                    if diagnostic.is_some() {
                        // Bail early if we already have an error, no chance of "No constituent of type is callable"
                        break;
                    }
                } else {
                    // Error on the first non callable constituent only
                    if diagnostic.is_none() {
                        let constituent_string = self.type_to_string(constituent);
                        let apparent_string = self.type_to_string(apparent_type);
                        let d = self.new_diagnostic_for_node(
                            Some(target),
                            if is_call {
                                &tsc_diagnostics::Type_0_has_no_call_signatures
                            } else {
                                &tsc_diagnostics::Type_0_has_no_construct_signatures
                            },
                            &[constituent_string],
                        );
                        diagnostic = Some(self.new_diagnostic_chain_for_node(
                            Some(d),
                            Some(target),
                            if is_call {
                                &tsc_diagnostics::Not_all_constituents_of_type_0_are_callable
                            } else {
                                &tsc_diagnostics::Not_all_constituents_of_type_0_are_constructable
                            },
                            &[apparent_string],
                        ));
                    }
                    if has_signatures {
                        // Bail early if we already found a signature, no chance of "No constituent of type is callable"
                        break;
                    }
                }
            }
            if !has_signatures {
                let apparent_string = self.type_to_string(apparent_type);
                diagnostic = Some(self.new_diagnostic_for_node(
                    Some(target),
                    if is_call {
                        &tsc_diagnostics::No_constituent_of_type_0_is_callable
                    } else {
                        &tsc_diagnostics::No_constituent_of_type_0_is_constructable
                    },
                    &[apparent_string],
                ));
            }
            if diagnostic.is_none() {
                let apparent_string = self.type_to_string(apparent_type);
                diagnostic = Some(self.new_diagnostic_for_node(
                    Some(target),
                    if is_call {
                        &tsc_diagnostics::Each_member_of_the_union_type_0_has_signatures_but_none_of_those_signatures_are_compatible_with_each_other
                    } else {
                        &tsc_diagnostics::Each_member_of_the_union_type_0_has_construct_signatures_but_none_of_those_signatures_are_compatible_with_each_other
                    },
                    &[apparent_string],
                ));
            }
        } else {
            let apparent_string = self.type_to_string(apparent_type);
            diagnostic = Some(self.new_diagnostic_chain_for_node(
                diagnostic.clone(),
                Some(target),
                if is_call {
                    &tsc_diagnostics::Type_0_has_no_call_signatures
                } else {
                    &tsc_diagnostics::Type_0_has_no_construct_signatures
                },
                &[apparent_string],
            ));
        }
        let mut head_message = if is_call {
            &tsc_diagnostics::This_expression_is_not_callable
        } else {
            &tsc_diagnostics::This_expression_is_not_constructable
        };
        // Diagnose get accessors incorrectly called as functions
        if nodes[error_target]
            .parent
            .is_some_and(|p| ast::is_call_expression(&nodes[p]))
            && nodes[nodes[error_target].parent.unwrap()]
                .arguments()
                .is_some_and(|a| a.is_empty())
        {
            let resolved_symbol = self.get_resolved_symbol_or_nil(error_target);
            if resolved_symbol
                .is_some_and(|s| self.sym(s).flags.intersects(ast::SymbolFlags::GET_ACCESSOR))
            {
                head_message = &tsc_diagnostics::This_expression_is_not_callable_because_it_is_a_get_accessor_Did_you_mean_to_use_it_without;
            }
        }
        let diagnostic = self.new_diagnostic_chain_for_node(
            diagnostic.clone(),
            Some(target),
            head_message,
            &[] as &[String],
        );
        if maybe_missing_await {
            let related = self.new_diagnostic_for_node(
                Some(error_target),
                &tsc_diagnostics::Did_you_forget_to_use_await,
                &[] as &[String],
            );
            ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(related));
        }
        diagnostic
    }

    /// `(c *Checker) invocationError` (checker.go:10221).
    pub(crate) fn invocation_error(
        &mut self,
        error_target: NodeId,
        apparent_type: TypeId,
        kind: SignatureKind,
        related_information: Option<ast::diagnostic::DiagnosticRef>,
    ) {
        let diagnostic = self.invocation_error_details(error_target, apparent_type, kind);
        if let Some(related_information) = related_information {
            ast::diagnostic::lock_diagnostic(&diagnostic)
                .add_related_info(Some(related_information));
        }
        let diagnostic = self.add_diagnostic(&diagnostic);
        self.invocation_error_recovery(apparent_type, kind, &diagnostic);
    }

    /// `(c *Checker) invocationErrorRecovery` (checker.go:10230).
    pub(crate) fn invocation_error_recovery(
        &mut self,
        apparent_type: TypeId,
        kind: SignatureKind,
        diagnostic: &ast::diagnostic::DiagnosticRef,
    ) {
        let Some(symbol) = self.types.get_ref(apparent_type).symbol else {
            return;
        };
        let import_node = self.export_type_links.get(symbol).originating_import;
        // Create a diagnostic on the originating import if possible onto which we can attach a quickfix
        //  An import call expression cannot be rewritten into another form to correct the error - the only solution is to use `.default` at the use-site
        if let Some(import_node) = import_node {
            let __program = self.program.clone().expect("program");
            let import_nodes = __program.nodes((import_node).file_index());
            if !ast::is_import_call(&import_nodes[import_node], &import_nodes) {
                let target = self.export_type_links.get(symbol).target;
                if let Some(target) = target {
                    let target_type = self.get_type_of_symbol(target);
                    let sigs = self.get_signatures_of_type(target_type, kind);
                    if sigs.is_empty() {
                        return;
                    }
                    let related = self.new_diagnostic_for_node(
                        Some(import_node),
                        &tsc_diagnostics::Type_originates_at_this_import_A_namespace_style_import_cannot_be_called_or_constructed_and_will_cause_a_failure_at_runtime_Consider_using_a_default_import_or_import_require_here_instead,
                        &[] as &[String],
                    );
                    ast::diagnostic::lock_diagnostic(diagnostic).add_related_info(Some(related));
                }
            }
        }
    }

    /// `(c *Checker) isGenericFunctionReturningFunction` (checker.go:10246).
    pub(crate) fn is_generic_function_returning_function(
        &mut self,
        signature: SignatureId,
    ) -> bool {
        !self
            .signature_arena
            .get(signature)
            .type_parameters
            .is_empty()
            && {
                let return_type = self.get_return_type_of_signature(signature);
                self.is_function_type(return_type)
            }
    }

    /// `(c *Checker) skippedGenericFunction` (checker.go:10250).
    pub(crate) fn skipped_generic_function(&mut self, node: NodeId, check_mode: CheckMode) {
        if check_mode.intersects(CheckMode::INFERENTIAL) {
            // We have skipped a generic function during inferential typing. Obtain the inference context and
            // indicate this has occurred such that we know a second pass of inference is be needed.
            let context = self.get_inference_context(node);
            if let Some(context) = context {
                self.inference_contexts[context.index()].flags |=
                    InferenceFlags::SKIPPED_GENERIC_FUNCTION;
            }
        }
    }

    /// `(c *Checker) checkTaggedTemplateExpression` (checker.go:10259).
    pub(crate) fn check_tagged_template_expression(&mut self, node: NodeId) -> TypeId {
        if !self.check_grammar_tagged_template_chain(node) {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let type_argument_list = nodes[node].type_argument_list();
            self.check_grammar_type_arguments(node, type_argument_list);
        }
        let signature = self
            .get_resolved_signature(node, None, CheckMode::NORMAL)
            .expect("getResolvedSignature");
        self.check_deprecated_signature(signature, node);
        self.get_return_type_of_signature(signature)
    }

    /// `(c *Checker) checkParenthesizedExpression` (checker.go:10268).
    pub(crate) fn check_parenthesized_expression(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_expression_ex(nodes[node].expression().unwrap(), check_mode)
    }

    /// `(c *Checker) checkClassExpression` (checker.go:10272).
    pub(crate) fn check_class_expression(&mut self, node: NodeId) -> TypeId {
        self.check_class_like_declaration(node);
        self.check_node_deferred(node);
        self.check_class_expression_external_helpers(node);
        let symbol = self
            .get_symbol_of_declaration(node)
            .expect("getSymbolOfDeclaration");
        self.get_type_of_symbol(symbol)
    }

    /// `(c *Checker) getFirstTransformableStaticClassElement` (checker.go:10279).
    pub(crate) fn get_first_transformable_static_class_element(
        &mut self,
        node: NodeId,
    ) -> Option<NodeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let will_transform_static_elements_of_decorated_class = !self.legacy_decorators
            && self.language_version
                < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.class_and_class_element_decorators
            && ast::class_or_constructor_parameter_is_decorated(false, node, &nodes);
        let will_transform_private_elements_or_class_static_blocks = self.language_version
            < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.private_names_and_class_static_blocks
            || self.language_version
                < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.class_and_class_element_decorators;
        let will_transform_initializers = !self.emit_standard_class_fields;
        if will_transform_static_elements_of_decorated_class
            || will_transform_private_elements_or_class_static_blocks
        {
            if let Some(members) = nodes[node].members().map(|m| m.to_vec()) {
                for member in members {
                    if will_transform_static_elements_of_decorated_class
                        && ast::class_element_or_class_element_parameter_is_decorated(
                            false, member, node, &nodes,
                        )
                    {
                        if let Some(first_decorator) =
                            nodes[node].decorators(&nodes).first().map(|d| d.id)
                        {
                            return Some(first_decorator);
                        }
                        return Some(node);
                    } else if will_transform_private_elements_or_class_static_blocks {
                        if ast::is_class_static_block_declaration(&nodes[member]) {
                            return Some(member);
                        } else if ast::is_static(&nodes[member])
                            && (ast::is_private_identifier_class_element_declaration(
                                &nodes[member],
                                &nodes,
                            ) || will_transform_initializers
                                && ast::is_initialized_property(&nodes[member]))
                        {
                            return Some(member);
                        }
                    }
                }
            }
        }
        None
    }

    /// `(c *Checker) checkClassExpressionExternalHelpers` (checker.go:10306).
    pub(crate) fn check_class_expression_external_helpers(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node].name().is_some() {
            return;
        }
        let parent = crate::utilities::walk_up_outer_expressions(node, &nodes);
        let Some(parent) = parent else {
            return;
        };
        if !ast::is_named_evaluation_source(&nodes[parent], &nodes) {
            return;
        }

        let will_transform_es_decorators = !self.legacy_decorators
            && self.language_version
                < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.class_and_class_element_decorators;
        let location;
        if will_transform_es_decorators
            && ast::class_or_constructor_parameter_is_decorated(false, node, &nodes)
        {
            location = nodes[node]
                .decorators(&nodes)
                .first()
                .map(|d| d.id)
                .or(Some(node));
        } else {
            location = self.get_first_transformable_static_class_element(node);
        }

        if let Some(location) = location {
            self.check_external_emit_helpers(location, ExternalEmitHelpers::SET_FUNCTION_NAME);
            if (ast::is_property_assignment(&nodes[parent])
                || ast::is_property_declaration(&nodes[parent])
                || ast::is_binding_element(&nodes[parent]))
                && nodes[parent]
                    .name()
                    .is_some_and(|n| ast::is_computed_property_name(&nodes[n]))
            {
                self.check_external_emit_helpers(location, ExternalEmitHelpers::PROP_KEY);
            }
        }
    }

    /// `(c *Checker) checkClassExpressionDeferred` (checker.go:10334).
    pub(crate) fn check_class_expression_deferred(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let members = nodes[node].members().map(|m| m.to_vec());
        self.check_source_elements(members.as_deref().unwrap_or(&[]));
        self.check_constructor_declared_properties(node);
        self.register_for_unused_identifiers_check(node);
    }

    /// `(c *Checker) checkFunctionExpressionOrObjectLiteralMethod` (checker.go:10340).
    pub(crate) fn check_function_expression_or_object_literal_method(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        self.check_node_deferred(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(full_signature) = nodes[node]
            .function_like_data()
            .and_then(|d| d.full_signature)
        {
            self.check_source_element(Some(full_signature));
        }
        if ast::is_function_expression(&nodes[node]) {
            let name = nodes[node].name();
            self.check_collisions_for_declaration_name(node, name);
        }
        if check_mode.intersects(CheckMode::SKIP_CONTEXT_SENSITIVE)
            && self.is_context_sensitive(node)
        {
            // Skip parameters, return signature with return type that retains noncontextual parts so inferences can still be drawn in an early stage
            if nodes[node].type_().is_none()
                && !ast::has_context_sensitive_parameters(&nodes[node], &nodes)
            {
                // Return plain anyFunctionType if there is no possibility we'll make inferences from the return type
                let contextual_signature = self.get_contextual_signature(node);
                if let Some(contextual_signature) = contextual_signature {
                    let return_type = self.get_return_type_of_signature(contextual_signature);
                    if (self
                        .could_contain_type_variables
                        .clone()
                        .expect("could_contain_type_variables"))(
                        self, return_type
                    ) {
                        if let Some(&cached) = self.context_free_types.get(&node) {
                            return cached;
                        }
                        let return_type = self.get_return_type_from_body(node, check_mode);
                        let return_only_signature = self.new_signature(
                            SignatureFlags::IS_NON_INFERRABLE,
                            None,
                            Vec::new(), /*typeParameters*/
                            None,       /*thisParameter*/
                            Vec::new(),
                            Some(return_type),
                            None, /*resolvedTypePredicate*/
                            0,
                        );
                        let node_symbol = nodes[node].symbol();
                        let return_only_type = self.new_anonymous_type(
                            node_symbol,
                            SymbolTable::default(),
                            &[return_only_signature],
                            &[],
                            &[],
                        );
                        self.types_handle().get_mut(return_only_type).object_flags |=
                            ObjectFlags::NON_INFERRABLE_TYPE;
                        self.context_free_types.insert(node, return_only_type);
                        return return_only_type;
                    }
                }
            }
            return self.any_function_type;
        }
        // Grammar checking
        let has_grammar_error = self.check_grammar_function_like_declaration(node);
        if !has_grammar_error && ast::is_function_expression(&nodes[node]) {
            self.check_grammar_for_generator(node);
        }
        if let Some(full_signature) = nodes[node]
            .function_like_data()
            .and_then(|d| d.full_signature)
        {
            let t = self.get_type_from_type_node(full_signature);
            if self.get_contextual_call_signature(t, node).is_none() {
                self.error(
                    Some(full_signature),
                    &tsc_diagnostics::A_JSDoc_type_tag_on_a_function_must_have_a_signature_with_the_correct_number_of_arguments,
                    &[] as &[String],
                );
            }
        }
        self.contextually_check_function_expression_or_object_literal_method(node, check_mode);
        let symbol = self
            .get_symbol_of_declaration(node)
            .expect("getSymbolOfDeclaration");
        self.get_type_of_symbol(symbol)
    }

    /// `(c *Checker) contextuallyCheckFunctionExpressionOrObjectLiteralMethod` (checker.go:10381).
    pub(crate) fn contextually_check_function_expression_or_object_literal_method(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) {
        // Check if function expression is contextually typed and assign parameter types if so.
        if !self
            .node_links
            .get(node)
            .flags
            .intersects(NodeCheckFlags::CONTEXT_CHECKED)
        {
            let contextual_signature = self.get_contextual_signature(node);
            // If a type check is started at a function expression that is an argument of a function call, obtaining the
            // contextual type may recursively get back to here during overload resolution of the call. If so, we will have
            // already assigned contextual types.
            if !self
                .node_links
                .get(node)
                .flags
                .intersects(NodeCheckFlags::CONTEXT_CHECKED)
            {
                self.node_links.get(node).flags |= NodeCheckFlags::CONTEXT_CHECKED;
                let symbol = self.get_symbol_of_declaration(node);
                let symbol_type = self.get_type_of_symbol(symbol.expect("symbol"));
                let signatures = self.get_signatures_of_type(symbol_type, SignatureKind::Call);
                let Some(&signature) = signatures.first() else {
                    return;
                };
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((node).file_index());
                if self.is_context_sensitive(node) {
                    if let Some(contextual_signature) = contextual_signature {
                        let inference_context = self.get_inference_context(node);
                        let mut instantiated_contextual_signature = None;
                        if check_mode.intersects(CheckMode::INFERENTIAL) {
                            self.infer_from_annotated_parameters_and_return(
                                signature,
                                contextual_signature,
                                inference_context,
                            );
                            let rest_type = self.get_effective_rest_type(contextual_signature);
                            if rest_type.is_some_and(|t| {
                                self.types_handle()
                                    .get(t)
                                    .flags
                                    .intersects(TypeFlags::TYPE_PARAMETER)
                            }) {
                                let non_fixing_mapper = inference_context
                                    .map(|c| self.inference_contexts[c.index()].non_fixing_mapper);
                                instantiated_contextual_signature =
                                    Some(self.instantiate_signature(
                                        contextual_signature,
                                        non_fixing_mapper.flatten(),
                                    ));
                            }
                        }
                        if instantiated_contextual_signature.is_none() {
                            if let Some(inference_context) = inference_context {
                                let mapper =
                                    self.inference_contexts[inference_context.index()].mapper;
                                instantiated_contextual_signature =
                                    Some(self.instantiate_signature(contextual_signature, mapper));
                            } else {
                                instantiated_contextual_signature = Some(contextual_signature);
                            }
                        }
                        self.assign_contextual_parameter_types(
                            signature,
                            instantiated_contextual_signature.unwrap(),
                        );
                    } else {
                        // Force resolution of all parameter types such that the absence of a contextual type is consistently reflected.
                        self.assign_non_contextual_parameter_types(signature);
                    }
                } else if contextual_signature.is_some()
                    && nodes[node].type_parameters().is_none()
                    && self
                        .signature_arena
                        .get(contextual_signature.unwrap())
                        .parameters
                        .len()
                        > nodes[node].parameters().map(|p| p.len()).unwrap_or(0)
                {
                    let inference_context = self.get_inference_context(node);
                    if check_mode.intersects(CheckMode::INFERENTIAL) {
                        self.infer_from_annotated_parameters_and_return(
                            signature,
                            contextual_signature.unwrap(),
                            inference_context,
                        );
                    }
                }
                if contextual_signature.is_some()
                    && self.get_return_type_from_annotation(node).is_none()
                    && self
                        .signature_arena
                        .get(signature)
                        .resolved_return_type
                        .is_none()
                {
                    // resolvedReturnType is cached indefinitely, so the return type here has to be computed without CheckModeSkipContextSensitive;
                    // otherwise anyFunctionType could leak as part of the computed (and cached) return type.
                    let return_type = self.get_return_type_from_body(
                        node,
                        check_mode & !CheckMode::SKIP_CONTEXT_SENSITIVE,
                    );
                    if self
                        .signature_arena
                        .get(signature)
                        .resolved_return_type
                        .is_none()
                    {
                        self.signature_arena.get_mut(signature).resolved_return_type =
                            Some(return_type);
                    }
                }
                self.check_signature_declaration(node);
            }
        }
    }

    /// `(c *Checker) checkFunctionExpressionOrObjectLiteralMethodDeferred` (checker.go:10437).
    pub(crate) fn check_function_expression_or_object_literal_method_deferred(
        &mut self,
        node: NodeId,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let function_flags = ast::get_function_flags(Some(&nodes[node]));
        let return_type = self.get_return_type_from_annotation(node);
        self.check_all_code_paths_in_non_void_function_return_or_throw(node, return_type);
        if let Some(body) = nodes[node].body() {
            if nodes[node].type_().is_none() {
                // There are some checks that are only performed in getReturnTypeFromBody, that may produce errors
                // we need. An example is the noImplicitAny errors resulting from widening the return expression
                // of a function. Because checking of function expression bodies is deferred, there was never an
                // appropriate time to do this during the main walk of the file (see the comment at the top of
                // checkFunctionExpressionBodies). So it must be done now.
                let signature = self.get_signature_from_declaration(node);
                self.get_return_type_of_signature(signature);
            }
            if ast::is_block(&nodes[body]) {
                self.check_source_element(Some(body));
            } else {
                // From within an async function you can return either a non-promise value or a promise. Any
                // Promise/A+ compatible implementation will always assimilate any foreign promise, so we
                // should not be checking assignability of a promise to the return type. Instead, we need to
                // check assignability of the awaited type of the expression body against the promised type of
                // its return type annotation.
                let expr_type = self.check_expression(body);
                if let Some(return_type) = return_type {
                    if let Some(return_or_promised_type) =
                        self.unwrap_return_type(return_type, function_flags)
                    {
                        self.check_return_expression(
                            node,
                            return_or_promised_type,
                            body,
                            Some(body),
                            expr_type,
                            false,
                        );
                    }
                }
            }
        }
    }

    /// `(c *Checker) inferFromAnnotatedParametersAndReturn` (checker.go:10470).
    pub(crate) fn infer_from_annotated_parameters_and_return(
        &mut self,
        sig: SignatureId,
        context: SignatureId,
        inference_context: Option<InferenceContextId>,
    ) {
        let parameters = self.signature_arena.get(sig).parameters.clone();
        let has_rest =
            crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(sig));
        let length = parameters.len() - if has_rest { 1 } else { 0 };
        for i in 0..length {
            let declaration = self.sym(parameters[i]).value_declaration;
            let Some(declaration) = declaration else {
                continue;
            };
            let __program = self.program.clone().expect("program");
            let decl_nodes = __program.nodes((declaration).file_index());
            if let Some(type_node) = decl_nodes[declaration].type_() {
                let type_from_node = self.get_type_from_type_node(type_node);
                let source = self.add_optionality_ex(
                    type_from_node,
                    false, /*isProperty*/
                    crate::utilities::is_optional_declaration(
                        &decl_nodes[declaration],
                        &decl_nodes,
                    ),
                );
                let target = self.get_type_at_position(context, i);
                if let Some(inference_context) = inference_context {
                    let mut inferences = std::mem::take(
                        &mut self.inference_contexts[inference_context.index()].inferences,
                    );
                    self.infer_types(
                        &mut inferences,
                        source,
                        target,
                        InferencePriority::NONE,
                        false,
                    );
                    self.inference_contexts[inference_context.index()].inferences = inferences;
                }
            }
        }
        if let Some(declaration) = self.signature_arena.get(sig).declaration {
            let __program = self.program.clone().expect("program");
            let decl_nodes = __program.nodes((declaration).file_index());
            if let Some(return_type_node) = decl_nodes[declaration].type_() {
                let source = self.get_type_from_type_node(return_type_node);
                let target = self.get_return_type_of_signature(context);
                if let Some(inference_context) = inference_context {
                    let mut inferences = std::mem::take(
                        &mut self.inference_contexts[inference_context.index()].inferences,
                    );
                    self.infer_types(
                        &mut inferences,
                        source,
                        target,
                        InferencePriority::NONE,
                        false,
                    );
                    self.inference_contexts[inference_context.index()].inferences = inferences;
                }
            }
        }
    }

    /// `(c *Checker) getContextualSignature` (checker.go:10495).
    /// Return the contextual signature for a given expression node. A contextual type provides a
    /// contextual signature if it has a single call signature and if that call signature is non-generic.
    /// If the contextual type is a union type, get the signature from each type possible and if they are
    /// all identical ignoring their return type, the result is same signature but with return type as
    /// union type of return types from these signatures
    pub(crate) fn get_contextual_signature(&mut self, node: NodeId) -> Option<SignatureId> {
        let t = self.get_apparent_type_of_contextual_type(node, ContextFlags::SIGNATURE)?;
        if !self
            .types_handle()
            .get_ref(t)
            .flags
            .intersects(TypeFlags::UNION)
        {
            return self.get_contextual_call_signature(t, node);
        }
        let mut signature_list: Vec<SignatureId> = Vec::new();
        let types = self.types.get_ref(t).types().to_vec();
        for current in types {
            if let Some(signature) = self.get_contextual_call_signature(current, node) {
                if !signature_list.is_empty() {
                    let first = signature_list[0];
                    if self.compare_signatures_identical(
                        first,
                        signature,
                        false, /*partialMatch*/
                        true,  /*ignoreThisTypes*/
                        true,  /*ignoreReturnTypes*/
                        Comparer::Identical,
                        &mut None,
                    ) == Ternary::FALSE
                    {
                        // Signatures aren't identical, do not use
                        return None;
                    }
                }
                // Use this signature for contextual union signature
                signature_list.push(signature);
            }
        }
        match signature_list.len() {
            0 => None,
            1 => Some(signature_list[0]),
            _ => Some(self.create_union_signature(signature_list[0], signature_list)),
        }
    }

    /// `(c *Checker) createUnionSignature` (checker.go:10526).
    pub(crate) fn create_union_signature(
        &mut self,
        sig: SignatureId,
        union_signatures: Vec<SignatureId>,
    ) -> SignatureId {
        let result = self.clone_signature(sig);
        self.signature_arena.get_mut(result).composite = Some(Box::new(CompositeSignature {
            is_union: true,
            signatures: union_signatures,
        }));
        self.signature_arena.get_mut(result).target = None;
        self.signature_arena.get_mut(result).mapper = None;
        result
    }

    /// `(c *Checker) getContextualCallSignature` (checker.go:10536).
    /// If the given type is an object or union type with a single signature, and if that signature has at
    /// least as many parameters as the given function, return the signature. Otherwise return undefined.
    pub(crate) fn get_contextual_call_signature(
        &mut self,
        t: TypeId,
        node: NodeId,
    ) -> Option<SignatureId> {
        let signatures = self.get_signatures_of_type(t, SignatureKind::Call);
        let applicable_by_arity: Vec<SignatureId> = signatures
            .iter()
            .copied()
            .filter(|&s| !self.is_arity_smaller(s, node))
            .collect();
        if applicable_by_arity.len() == 1 {
            return Some(applicable_by_arity[0]);
        }
        self.get_intersected_signatures(&applicable_by_arity)
    }

    /// `(c *Checker) getIntersectedSignatures` (checker.go:10545).
    pub(crate) fn get_intersected_signatures(
        &mut self,
        signatures: &[SignatureId],
    ) -> Option<SignatureId> {
        if !self.no_implicit_any {
            return None;
        }
        let mut combined = None;
        for &sig in signatures {
            match combined {
                None => combined = Some(sig),
                Some(c) if c == sig => {}
                Some(c) => {
                    let combined_type_parameters =
                        self.signature_arena.get(c).type_parameters.clone();
                    let sig_type_parameters = self.signature_arena.get(sig).type_parameters.clone();
                    if self.compare_type_parameters_identical(
                        &combined_type_parameters,
                        &sig_type_parameters,
                    ) {
                        combined = Some(self.combine_union_or_intersection_member_signatures(
                            c, sig, false, /*isUnion*/
                        ));
                    } else {
                        return None;
                    }
                }
            }
        }
        combined
    }

    /// `(c *Checker) isAritySmaller` (checker.go:10564).
    /// If the contextual signature has fewer parameters than the function
    /// expression, do not use it
    pub(crate) fn is_arity_smaller(&mut self, signature: SignatureId, target: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((target).file_index());
        let parameters = nodes[target]
            .parameters()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        let mut target_parameter_count = 0i32;
        while (target_parameter_count as usize) < parameters.len() {
            let param = parameters[target_parameter_count as usize];
            if nodes[param].initializer().is_some()
                || nodes[param].question_token(&nodes).is_some()
                || crate::utilities::has_dot_dot_dot_token(&nodes[param], &nodes)
            {
                break;
            }
            target_parameter_count += 1;
        }
        if !parameters.is_empty() && ast::is_this_parameter(&nodes[parameters[0]], &nodes) {
            target_parameter_count -= 1;
        }
        !self.has_effective_rest_parameter(signature)
            && (self.get_parameter_count(signature) as i32) < target_parameter_count
    }

    /// `(c *Checker) assignContextualParameterTypes` (checker.go:10580).
    pub(crate) fn assign_contextual_parameter_types(
        &mut self,
        sig: SignatureId,
        context: SignatureId,
    ) {
        let context_type_parameters = self.signature_arena.get(context).type_parameters.clone();
        if !context_type_parameters.is_empty() {
            if !self.signature_arena.get(sig).type_parameters.is_empty() {
                // This signature has already has a contextual inference performed and cached on it
                return;
            }
            self.signature_arena.get_mut(sig).type_parameters = context_type_parameters;
        }
        if let Some(context_this_parameter) = self.signature_arena.get(context).this_parameter {
            let parameter = self.signature_arena.get(sig).this_parameter;
            let needs_assignment = match parameter {
                None => true,
                Some(p) => {
                    let value_declaration = self.sym(p).value_declaration;
                    value_declaration.is_some_and(|d| self.program_nodes(d)[d].type_().is_none())
                }
            };
            if needs_assignment {
                if parameter.is_none() {
                    let this_parameter =
                        self.create_symbol_with_type(Some(context_this_parameter), None);
                    self.signature_arena.get_mut(sig).this_parameter = Some(this_parameter);
                }
                let this_parameter = self.signature_arena.get(sig).this_parameter.unwrap();
                let t = self.get_type_of_symbol(context_this_parameter);
                self.assign_parameter_type(this_parameter, Some(t));
            }
        }
        let parameters = self.signature_arena.get(sig).parameters.clone();
        let has_rest =
            crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(sig));
        let length = parameters.len() - if has_rest { 1 } else { 0 };
        for i in 0..length {
            let parameter = parameters[i];
            let declaration = self.sym(parameter).value_declaration;
            let Some(declaration) = declaration else {
                continue;
            };
            let __program = self.program.clone().expect("program");
            let decl_nodes = __program.nodes((declaration).file_index());
            if decl_nodes[declaration].type_().is_none() {
                let mut t = self.try_get_type_at_position(context, i);
                if t.is_some() && decl_nodes[declaration].initializer().is_some() {
                    let mut initializer_type =
                        self.check_declaration_initializer(declaration, CheckMode::NORMAL, None);
                    if !self.is_type_assignable_to(initializer_type, t.unwrap()) {
                        initializer_type = self
                            .widen_type_inferred_from_initializer(declaration, initializer_type);
                        if self.is_type_assignable_to(t.unwrap(), initializer_type) {
                            t = Some(initializer_type);
                        }
                    }
                }
                self.assign_parameter_type(parameter, t);
            }
        }
        if has_rest {
            // parameter might be a transient symbol generated by use of `arguments` in the function body.
            let parameter = parameters.last().copied();
            if let Some(parameter) = parameter {
                let value_declaration = self.sym(parameter).value_declaration;
                let check_flags = self.sym(parameter).check_flags;
                if value_declaration.is_some_and(|d| self.program_nodes(d)[d].type_().is_none())
                    || value_declaration.is_none()
                        && check_flags.intersects(ast::checkflags::CheckFlags::DEFERRED_TYPE)
                {
                    let contextual_parameter_type =
                        self.get_rest_type_at_position(context, length, false);
                    self.assign_parameter_type(parameter, contextual_parameter_type);
                }
            }
        }
    }

    /// `(c *Checker) assignNonContextualParameterTypes` (checker.go:10626).
    pub(crate) fn assign_non_contextual_parameter_types(&mut self, signature: SignatureId) {
        if let Some(this_parameter) = self.signature_arena.get(signature).this_parameter {
            self.assign_parameter_type(this_parameter, None);
        }
        let parameters = self.signature_arena.get(signature).parameters.clone();
        for parameter in parameters {
            self.assign_parameter_type(parameter, None);
        }
    }

    /// `(c *Checker) assignParameterType` (checker.go:10635).
    pub(crate) fn assign_parameter_type(
        &mut self,
        parameter: SymbolId,
        contextual_type: Option<TypeId>,
    ) {
        if self
            .value_symbol_links
            .get(parameter)
            .resolved_type
            .is_some()
        {
            return;
        }
        let declaration = self.sym(parameter).value_declaration;
        let mut t = contextual_type;
        if t.is_none() {
            if let Some(declaration) = declaration {
                t = Some(self.get_widened_type_for_variable_like_declaration(
                    declaration,
                    true, /*reportErrors*/
                ));
            } else {
                t = Some(self.get_type_of_symbol(parameter));
            }
        }
        let resolved_type = self.add_optionality_ex(
            t.unwrap(),
            false,
            declaration.is_some_and(|d| {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((d).file_index());
                nodes[d].initializer().is_none()
                    && crate::utilities::is_optional_declaration(&nodes[d], &nodes)
            }),
        );
        self.value_symbol_links.get(parameter).resolved_type = Some(resolved_type);
        if let Some(declaration) = declaration {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((declaration).file_index());
            let name = nodes[declaration].name();
            if name.is_some_and(|n| !ast::is_identifier(&nodes[n])) {
                // if inference didn't come up with anything but unknown, fall back to the binding pattern if present.
                let resolved = self
                    .value_symbol_links
                    .get(parameter)
                    .resolved_type
                    .unwrap();
                if resolved == self.unknown_type {
                    let binding_type =
                        self.get_type_from_binding_pattern(name.unwrap(), false, false);
                    self.value_symbol_links.get(parameter).resolved_type = Some(binding_type);
                }
                let resolved = self
                    .value_symbol_links
                    .get(parameter)
                    .resolved_type
                    .unwrap();
                self.assign_binding_element_types(name.unwrap(), resolved);
            }
        }
    }

    /// `(c *Checker) assignBindingElementTypes` (checker.go:10661).
    /// When contextual typing assigns a type to a parameter that contains a binding pattern, we also need to push
    /// the destructured type into the contained binding elements.
    pub(crate) fn assign_binding_element_types(&mut self, pattern: NodeId, parent_type: TypeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((pattern).file_index());
        let elements = nodes[pattern]
            .elements()
            .map(|e| e.to_vec())
            .unwrap_or_default();
        for element in elements {
            if let Some(name) = nodes[element].name() {
                let t = self.get_binding_element_type_from_parent_type(
                    element,
                    parent_type,
                    false, /*noTupleBoundsCheck*/
                );
                if ast::is_identifier(&nodes[name]) {
                    let symbol = self.get_symbol_of_declaration(element).expect("symbol");
                    self.value_symbol_links.get(symbol).resolved_type = Some(t);
                } else {
                    self.assign_binding_element_types(name, t);
                }
            }
        }
    }

    /// `(c *Checker) checkCollisionsForDeclarationName` (checker.go:10675).
    pub(crate) fn check_collisions_for_declaration_name(
        &mut self,
        node: NodeId,
        name: Option<NodeId>,
    ) {
        let Some(name) = name else {
            return;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        self.check_collision_with_require_exports_in_generated_code(node, Some(name));
        self.check_collision_with_global_object_in_generated_code(node, Some(name));
        self.check_collision_with_global_promise_in_generated_code(node, Some(name));
        self.record_potential_collision_with_weak_map_set_in_generated_code(node, Some(name));
        self.record_potential_collision_with_reflect_in_generated_code(node, Some(name));
        if ast::is_class_like(Some(node), &nodes) {
            self.check_type_name_is_reserved(name, &tsc_diagnostics::Class_name_cannot_be_0);
            if !nodes[node].flags.intersects(ast::NodeFlags::AMBIENT) {
                self.check_class_name_collision_with_object(name);
            }
        } else if ast::is_enum_declaration(&nodes[node]) {
            self.check_type_name_is_reserved(name, &tsc_diagnostics::Enum_name_cannot_be_0);
        }
    }

    /// `(c *Checker) checkCollisionWithRequireExportsInGeneratedCode` (checker.go:10694).
    pub(crate) fn check_collision_with_require_exports_in_generated_code(
        &mut self,
        node: NodeId,
        name: Option<NodeId>,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // No need to check for require or exports for ES6 modules and later
        let source_file = ast::get_source_file_of_node(Some(node), &nodes);
        if let Some(source_file) = source_file {
            let format = self
                .program
                .as_ref()
                .expect("program")
                .get_emit_module_format_of_file(nodes[source_file].as_source_file());
            if format >= tsc_core::options_generated::ModuleKind::ES2015 {
                return;
            }
        }
        if name.is_none()
            || !self.need_collision_check_for_identifier(node, name, "require")
                && !self.need_collision_check_for_identifier(node, name, "exports")
        {
            return;
        }
        // Uninstantiated modules shouldnt do this check
        if ast::is_module_declaration(&nodes[node])
            && ast::get_module_instance_state(node, &nodes)
                != ast::ModuleInstanceState::Instantiated
        {
            return;
        }
        // In case of variable declaration, node.parent is variable statement so look at the variable statement's parent
        if let Some(parent) = ast::get_declaration_container(node, &nodes) {
            if ast::is_source_file(&nodes[parent])
                && crate::utilities::is_external_or_common_js_module(nodes[parent].as_source_file())
            {
                // If the declaration happens to be in external module, report error that require and exports are reserved keywords
                let name_text = name
                    .map(|n| tsc_scanner::utilities::declaration_name_to_string(Some(n), &nodes));
                self.error_skipped_on_no_emit(
                    name,
                    &tsc_diagnostics::Duplicate_identifier_0_Compiler_reserves_name_1_in_top_level_scope_of_a_module,
                    &[name_text.clone().unwrap_or_default(), name_text.unwrap_or_default()],
                );
            }
        }
    }

    /// `(c *Checker) checkCollisionWithGlobalObjectInGeneratedCode` (checker.go:10714).
    pub(crate) fn check_collision_with_global_object_in_generated_code(
        &mut self,
        node: NodeId,
        name: Option<NodeId>,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if name.is_none()
            || ast::is_class_like(Some(node), &nodes)
            || !self.need_collision_check_for_identifier(node, name, "Object")
        {
            return;
        }
        // Uninstantiated modules shouldn't do this check
        if ast::is_module_declaration(&nodes[node])
            && ast::get_module_instance_state(node, &nodes)
                != ast::ModuleInstanceState::Instantiated
        {
            return;
        }
        // In case of variable declaration, node.parent is variable statement so look at the variable statement's parent
        if let Some(parent) = ast::get_declaration_container(node, &nodes) {
            if ast::is_source_file(&nodes[parent])
                && crate::utilities::is_external_or_common_js_module(nodes[parent].as_source_file())
            {
                let format = self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_emit_module_format_of_file(nodes[parent].as_source_file());
                if format == tsc_core::options_generated::ModuleKind::CommonJS {
                    // If the declaration happens to be in external module, report error that Object is a reserved identifier.
                    let name_text = name.map(|n| {
                        tsc_scanner::utilities::declaration_name_to_string(Some(n), &nodes)
                    });
                    self.error_skipped_on_no_emit(
                        name,
                        &tsc_diagnostics::Duplicate_identifier_0_Compiler_reserves_name_1_in_top_level_scope_of_a_module,
                        &[
                            name_text.clone().unwrap_or_default(),
                            name_text.unwrap_or_default(),
                        ],
                    );
                }
            }
        }
    }

    /// `(c *Checker) needCollisionCheckForIdentifier` (checker.go:10730).
    pub(crate) fn need_collision_check_for_identifier(
        &mut self,
        node: NodeId,
        identifier: Option<NodeId>,
        name: &str,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(identifier) = identifier {
            if nodes[identifier].text(&nodes) != name {
                return false;
            }
        }
        match nodes[node].kind {
            ast::Kind::PropertyDeclaration
            | ast::Kind::PropertySignature
            | ast::Kind::MethodDeclaration
            | ast::Kind::MethodSignature
            | ast::Kind::GetAccessor
            | ast::Kind::SetAccessor
            | ast::Kind::PropertyAssignment => {
                // it is ok to have member named '_super', '_this', `Promise`, etc. - member access is always qualified
                return false;
            }
            _ => {}
        }
        if nodes[node].flags.intersects(ast::NodeFlags::AMBIENT) {
            // ambient context - no codegen impact
            return false;
        }
        if ast::is_import_clause(&nodes[node])
            || ast::is_import_equals_declaration(&nodes[node])
            || ast::is_import_specifier(&nodes[node])
        {
            // type-only imports do not require collision checks against runtime values.
            if ast::is_type_only_import_or_export_declaration(node, &nodes) {
                return false;
            }
        }
        let root = ast::get_root_declaration(node, &nodes);
        if ast::is_parameter_declaration(&nodes[root])
            && ast::node_is_missing(nodes[root].parent.and_then(|p| nodes[p].body()), &nodes)
        {
            // just an overload - no codegen impact
            return false;
        }
        true
    }

    /// `(c *Checker) setNodeLinksForPrivateIdentifierScope` (checker.go:10758).
    pub(crate) fn set_node_links_for_private_identifier_scope(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(name) = nodes[node].name() {
            if ast::is_private_identifier(&nodes[name]) {
                if self.language_version
                    < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET
                        .private_names_and_class_static_blocks
                    || self.language_version
                        < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET
                            .class_and_class_element_decorators
                    || !self.compiler_options.get_use_define_for_class_fields()
                {
                    let mut lexical_scope = ast::get_enclosing_block_scope_container(node, &nodes);
                    while let Some(scope) = lexical_scope {
                        self.node_links.get(scope).flags |=
                            NodeCheckFlags::CONTAINS_CLASS_WITH_PRIVATE_IDENTIFIERS;
                        lexical_scope = ast::get_enclosing_block_scope_container(scope, &nodes);
                    }
                }
            }
        }
    }

    /// `(c *Checker) recordPotentialCollisionWithWeakMapSetInGeneratedCode` (checker.go:10770).
    pub(crate) fn record_potential_collision_with_weak_map_set_in_generated_code(
        &mut self,
        node: NodeId,
        name: Option<NodeId>,
    ) {
        if self.language_version <= tsc_core::options_generated::ScriptTarget::ES2021
            && (self.need_collision_check_for_identifier(node, name, "WeakMap")
                || self.need_collision_check_for_identifier(node, name, "WeakSet"))
        {
            self.add_deferred_diagnostic(Box::new(move |c: &mut Checker| {
                c.check_weak_map_set_collision(node);
            }));
        }
    }

    /// `(c *Checker) checkWeakMapSetCollision` (checker.go:10779).
    pub(crate) fn check_weak_map_set_collision(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let enclosing_block_scope = ast::get_enclosing_block_scope_container(node, &nodes);
        if let Some(enclosing_block_scope) = enclosing_block_scope {
            if self
                .node_links
                .get(enclosing_block_scope)
                .flags
                .intersects(NodeCheckFlags::CONTAINS_CLASS_WITH_PRIVATE_IDENTIFIERS)
            {
                if let Some(name) = nodes[node].name() {
                    if ast::is_identifier(&nodes[name]) {
                        let name_text = nodes[name].text(&nodes).into_owned();
                        self.error_skipped_on_no_emit(
                            Some(node),
                            &tsc_diagnostics::Compiler_reserves_name_0_when_emitting_private_identifier_downlevel,
                            &[name_text],
                        );
                    }
                }
            }
        }
    }

    /// `(c *Checker) checkCollisionWithGlobalPromiseInGeneratedCode` (checker.go:10789).
    pub(crate) fn check_collision_with_global_promise_in_generated_code(
        &mut self,
        node: NodeId,
        name: Option<NodeId>,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if name.is_none()
            || self.language_version >= tsc_core::options_generated::ScriptTarget::ES2017
            || !self.need_collision_check_for_identifier(node, name, "Promise")
        {
            return;
        }
        // Uninstantiated modules shouldn't do this check
        if ast::is_module_declaration(&nodes[node])
            && ast::get_module_instance_state(node, &nodes)
                != ast::ModuleInstanceState::Instantiated
        {
            return;
        }
        // In case of variable declaration, node.parent is variable statement so look at the variable statement's parent
        if let Some(parent) = ast::get_declaration_container(node, &nodes) {
            if ast::is_source_file(&nodes[parent])
                && crate::utilities::is_external_or_common_js_module(nodes[parent].as_source_file())
                && nodes[parent]
                    .flags
                    .intersects(ast::NodeFlags::HAS_ASYNC_FUNCTIONS)
            {
                // If the declaration happens to be in external module, report error that Promise is a reserved identifier.
                let name_text = name
                    .map(|n| tsc_scanner::utilities::declaration_name_to_string(Some(n), &nodes));
                self.error_skipped_on_no_emit(
                    name,
                    &tsc_diagnostics::Duplicate_identifier_0_Compiler_reserves_name_1_in_top_level_scope_of_a_module_containing_async_functions,
                    &[
                        name_text.clone().unwrap_or_default(),
                        name_text.unwrap_or_default(),
                    ],
                );
            }
        }
    }

    /// `(c *Checker) recordPotentialCollisionWithReflectInGeneratedCode` (checker.go:10805).
    pub(crate) fn record_potential_collision_with_reflect_in_generated_code(
        &mut self,
        node: NodeId,
        name: Option<NodeId>,
    ) {
        if name.is_some()
            && self.language_version <= tsc_core::options_generated::ScriptTarget::ES2021
            && self.need_collision_check_for_identifier(node, name, "Reflect")
        {
            self.add_deferred_diagnostic(Box::new(move |c: &mut Checker| {
                c.check_reflect_collision(node);
            }));
        }
    }

    /// `(c *Checker) checkReflectCollision` (checker.go:10813).
    pub(crate) fn check_reflect_collision(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut has_collision = false;
        if ast::is_class_expression(&nodes[node]) {
            // ClassExpression names don't contribute to their containers, but do matter for any of their block-scoped members.
            if let Some(members) = nodes[node].members().map(|m| m.to_vec()) {
                for member in members {
                    if self
                        .node_links
                        .get(member)
                        .flags
                        .intersects(NodeCheckFlags::CONTAINS_SUPER_PROPERTY_IN_STATIC_INITIALIZER)
                    {
                        has_collision = true;
                        break;
                    }
                }
            }
        } else if ast::is_function_expression(&nodes[node]) {
            // FunctionExpression names don't contribute to their containers, but do matter for their contents
            if self
                .node_links
                .get(node)
                .flags
                .intersects(NodeCheckFlags::CONTAINS_SUPER_PROPERTY_IN_STATIC_INITIALIZER)
            {
                has_collision = true;
            }
        } else {
            let container = ast::get_enclosing_block_scope_container(node, &nodes);
            if let Some(container) = container {
                if self
                    .node_links
                    .get(container)
                    .flags
                    .intersects(NodeCheckFlags::CONTAINS_SUPER_PROPERTY_IN_STATIC_INITIALIZER)
                {
                    has_collision = true;
                }
            }
        }
        if has_collision {
            if let Some(name) = nodes[node].name() {
                if ast::is_identifier(&nodes[name]) {
                    let name_text =
                        tsc_scanner::utilities::declaration_name_to_string(Some(name), &nodes);
                    self.error_skipped_on_no_emit(
                        Some(node),
                        &tsc_diagnostics::Duplicate_identifier_0_Compiler_reserves_name_1_when_emitting_super_references_in_static_initializers,
                        &[name_text, "Reflect".to_string()],
                    );
                }
            }
        }
    }

    /// `(c *Checker) checkClassNameCollisionWithObject` (checker.go:10842).
    pub(crate) fn check_class_name_collision_with_object(&mut self, name: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((name).file_index());
        if nodes[name].text(&nodes) == "Object" {
            let source_file = ast::get_source_file_of_node(Some(name), &nodes);
            if let Some(source_file) = source_file {
                let format = self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_emit_module_format_of_file(nodes[source_file].as_source_file());
                if format < tsc_core::options_generated::ModuleKind::ES2015 {
                    self.error(
                        Some(name),
                        &tsc_diagnostics::Class_name_cannot_be_Object_when_targeting_ES5_and_above_with_module_0,
                        &[self.module_kind.to_string()],
                    );
                }
            }
        }
    }

    /// `(c *Checker) checkTypeOfExpression` (checker.go:10848).
    pub(crate) fn check_type_of_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(expr) = nodes[node].expression() {
            self.check_expression(expr);
        }
        self.typeof_type
    }

    /// `(c *Checker) checkNonNullAssertion` (checker.go:10853).
    pub(crate) fn check_non_null_assertion(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node].flags.intersects(ast::NodeFlags::OPTIONAL_CHAIN) {
            // checkNonNullChain checks the same operand expression (node.Expression()),
            // so the child is still visited on this branch.
            return self.check_non_null_chain(node); //nolint:customlint // checkNonNullChain checks the operand
        }
        let expr = nodes[node].expression().unwrap();
        let t = self.check_expression(expr);
        self.get_non_nullable_type(t)
    }

    /// `(c *Checker) checkNonNullChain` (checker.go:10862).
    pub(crate) fn check_non_null_chain(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expr = nodes[node].expression().unwrap();
        let left_type = self.check_expression(expr);
        let non_optional_type = self.get_optional_expression_type(left_type, expr);
        let t = self.get_non_nullable_type(non_optional_type);
        self.propagate_optional_type_marker(t, node, non_optional_type != left_type)
    }

    /// `(c *Checker) checkExpressionWithTypeArguments` (checker.go:10868).
    pub(crate) fn check_expression_with_type_arguments(&mut self, node: NodeId) -> TypeId {
        self.check_grammar_expression_with_type_arguments(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let type_arguments = nodes[node].type_arguments().map(|a| a.to_vec());
        self.check_source_elements(type_arguments.as_deref().unwrap_or(&[]));
        if ast::is_expression_with_type_arguments(&nodes[node]) {
            let parent =
                ast::walk_up_parenthesized_expressions(nodes[node].parent.unwrap(), &nodes);
            if let Some(parent) = parent {
                if ast::is_binary_expression(&nodes[parent])
                    && nodes[parent]
                        .as_binary_expression()
                        .operator_token
                        .is_some_and(|t| nodes[t].kind == ast::Kind::InstanceOfKeyword)
                    && let Some(right) = nodes[parent].as_binary_expression().right
                {
                    if crate::utilities::is_node_descendant_of(node, right, &nodes) {
                        self.error(
                            Some(node),
                            &tsc_diagnostics::The_right_hand_side_of_an_instanceof_expression_must_not_be_an_instantiation_expression,
                            &[] as &[String],
                        );
                    }
                }
            }
        }
        let expr_type;
        if ast::is_expression_with_type_arguments(&nodes[node]) {
            expr_type = self.check_expression(nodes[node].expression().unwrap());
        } else {
            let expr_name = nodes[node].as_type_query_node().expr_name;
            if let Some(expr_name) = expr_name {
                if ast::is_this_identifier(&nodes[expr_name]) {
                    expr_type = self.check_this_expression(expr_name);
                } else {
                    expr_type = self.check_expression(expr_name);
                }
            } else {
                expr_type = self.error_type;
            }
        }
        self.get_instantiation_expression_type(expr_type, node)
    }

    /// `(c *Checker) getInstantiationExpressionType` (checker.go:10891).
    pub(crate) fn get_instantiation_expression_type(
        &mut self,
        expr_type: TypeId,
        node: NodeId,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let type_arguments = nodes[node].type_argument_list();
        if expr_type == self.silent_never_type
            || self.is_error_type(expr_type)
            || type_arguments.is_none()
        {
            return expr_type;
        }
        let key = InstantiationExpressionKey {
            node_id: ast::get_node_id(&nodes[node]),
            type_id: expr_type,
        };
        if let Some(&cached) = self.instantiation_expression_types.get(&key) {
            return cached;
        }
        let type_argument_nodes = type_arguments
            .map(|l| l.nodes().to_vec())
            .unwrap_or_default();
        let mut has_some_applicable_signature = false;
        let mut non_applicable_type: Option<TypeId> = None;
        let mut has_signatures_flag = std::cell::Cell::new(false);
        let mut has_applicable_signature_flag = std::cell::Cell::new(false);
        let result = self.get_instantiated_type(
            node,
            &type_argument_nodes,
            expr_type,
            &mut has_signatures_flag,
            &mut has_applicable_signature_flag,
            &mut has_some_applicable_signature,
            &mut non_applicable_type,
        );
        self.instantiation_expression_types.insert(key, result);
        let error_type = if has_some_applicable_signature {
            non_applicable_type
        } else {
            Some(expr_type)
        };
        if let Some(error_type) = error_type {
            let source_file = ast::get_source_file_of_node(Some(node), &nodes);
            let file_text = source_file
                .map(|sf| nodes[sf].as_source_file().text().to_string())
                .unwrap_or_default();
            let loc = tsc_core::text::TextRange::new(
                tsc_scanner::scanner::skip_trivia(&file_text, type_arguments.unwrap().loc.pos()),
                type_arguments.unwrap().loc.end(),
            );
            let error_string = self.type_to_string(error_type);
            let diagnostic = ast::diagnostic::new_diagnostic(
                source_file.map(|sf| ast::diagnostic::DiagnosticFile::from_node(sf, &nodes)),
                loc,
                &tsc_diagnostics::Type_0_has_no_signatures_for_which_the_type_argument_list_is_applicable,
                &[error_string],
            );
            self.add_diagnostic(&diagnostic);
        }
        result
    }

    /// `(c *Checker) getInstantiatedSignatures` — inner closure of
    /// `getInstantiationExpressionType` (checker.go:10902).
    pub(crate) fn get_instantiated_signatures(
        &mut self,
        signatures: &[SignatureId],
        type_argument_nodes: &[NodeId],
    ) -> Vec<SignatureId> {
        let applicable_signatures: Vec<SignatureId> = signatures
            .iter()
            .copied()
            .filter(|&sig| {
                !self.signature_arena.get(sig).type_parameters.is_empty()
                    && self.has_correct_type_argument_arity(sig, type_argument_nodes)
            })
            .collect();
        let mut result = Vec::with_capacity(applicable_signatures.len());
        for (i, &sig) in applicable_signatures.iter().enumerate() {
            let type_argument_types = self.check_type_arguments(
                sig,
                type_argument_nodes,
                true, /*reportErrors*/
                None,
            );
            if let Some(type_argument_types) = type_argument_types {
                let in_js_file = self
                    .signature_arena
                    .get(sig)
                    .declaration
                    .is_some_and(|d| ast::is_in_js_file(Some(d), &self.program_nodes(d)));
                result.push(self.get_signature_instantiation(
                    sig,
                    &type_argument_types,
                    in_js_file,
                    None,
                ));
            } else {
                result.push(applicable_signatures[i]);
            }
        }
        // `core.SameMap` — preserves the input slice when nothing changed.
        // The input here is `applicable_signatures` (already filtered), not
        // `signatures` — returning the unfiltered list would make filtered-out
        // non-generic signatures look applicable.
        result
    }

    /// `(c *Checker) getInstantiatedType`/`getInstantiatedTypePart` — inner
    /// recursive closures of `getInstantiationExpressionType` (checker.go:10914).
    pub(crate) fn get_instantiated_type_part(
        &mut self,
        node: NodeId,
        type_argument_nodes: &[NodeId],
        t: TypeId,
        has_signatures: &mut std::cell::Cell<bool>,
        has_applicable_signature: &mut std::cell::Cell<bool>,
        has_some_applicable_signature: &mut bool,
        non_applicable_type: &mut Option<TypeId>,
    ) -> TypeId {
        let result = self.get_instantiated_type_part_worker(
            node,
            type_argument_nodes,
            t,
            has_signatures,
            has_applicable_signature,
            has_some_applicable_signature,
            non_applicable_type,
        );
        result
    }

    /// Worker for `get_instantiated_type_part` — the Go `getInstantiatedTypePart`
    /// inner closure (checker.go:10918).
    pub(crate) fn get_instantiated_type_part_worker(
        &mut self,
        node: NodeId,
        type_argument_nodes: &[NodeId],
        t: TypeId,
        has_signatures: &mut std::cell::Cell<bool>,
        has_applicable_signature: &mut std::cell::Cell<bool>,
        has_some_applicable_signature: &mut bool,
        non_applicable_type: &mut Option<TypeId>,
    ) -> TypeId {
        let flags = self.types.get_ref(t).flags;
        if flags.intersects(TypeFlags::OBJECT) {
            let resolved = self.resolve_structured_type_members(t);
            let resolved_call_signatures = self.types.get_ref(resolved)
                .data
                .as_structured_type()
                .expect("resolved structured type")
                .call_signatures()
                .to_vec();
            let resolved_construct_signatures = self.types.get_ref(resolved)
                .data
                .as_structured_type()
                .expect("resolved structured type")
                .construct_signatures()
                .to_vec();
            let call_signatures =
                self.get_instantiated_signatures(&resolved_call_signatures, type_argument_nodes);
            let construct_signatures = self
                .get_instantiated_signatures(&resolved_construct_signatures, type_argument_nodes);
            has_signatures.set(
                has_signatures.get()
                    || !resolved_call_signatures.is_empty()
                    || !resolved_construct_signatures.is_empty(),
            );
            has_applicable_signature.set(
                has_applicable_signature.get()
                    || !call_signatures.is_empty()
                    || !construct_signatures.is_empty(),
            );
            if call_signatures != resolved_call_signatures
                || construct_signatures != resolved_construct_signatures
            {
                let symbol = self.new_symbol(
                    ast::SymbolFlags::NONE,
                    ast::INTERNAL_SYMBOL_NAME_INSTANTIATION_EXPRESSION,
                );
                debug_assert!(
                    self.types.get_ref(t).symbol.is_some(),
                    "Instantiation expression source type must have a symbol"
                );
                let source_symbol = self.types.get_ref(t).symbol.unwrap();
                let declarations = self.sym(source_symbol).declarations.clone();
                self.sym_mut(symbol).declarations = declarations;
                let result = self.new_object_type(
                    ObjectFlags::ANONYMOUS | ObjectFlags::INSTANTIATION_EXPRESSION_TYPE,
                    Some(symbol),
                );
                let __arena_members = self.types.clone();
                let members = __arena_members
                    .get(resolved)
                    .data
                    .as_structured_type()
                    .expect("resolved structured type")
                    .members
                    .clone();
                let index_infos: Vec<IndexInfoId> = self
                    .types_handle()
                    .get(resolved)
                    .data
                    .as_structured_type()
                    .expect("resolved structured type")
                    .index_infos
                    .clone()
                    .into_iter()
                    .map(|info| self.index_info_arena.alloc(info))
                    .collect();
                self.set_structured_type_members(
                    result,
                    members,
                    &call_signatures,
                    &construct_signatures,
                    &index_infos,
                );
                self.types_handle()
                    .get_mut(result)
                    .as_instantiation_expression_type_mut()
                    .node = Some(node);
                return result;
            }
        } else if flags.intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE) {
            if let Some(constraint) = self.get_base_constraint_of_type(t) {
                let instantiated = self.get_instantiated_type_part(
                    node,
                    type_argument_nodes,
                    constraint,
                    has_signatures,
                    has_applicable_signature,
                    has_some_applicable_signature,
                    non_applicable_type,
                );
                if instantiated != constraint {
                    return instantiated;
                }
            }
        } else if flags.intersects(TypeFlags::UNION) {
            // `c.mapType(t, getInstantiatedType)` — the closure tracks the
            // aggregate flags on each constituent call.
            let types = self.types.get_ref(t).types().to_vec();
            let mut mapped = Vec::with_capacity(types.len());
            for constituent in types {
                mapped.push(self.get_instantiated_type(
                    node,
                    type_argument_nodes,
                    constituent,
                    has_signatures,
                    has_applicable_signature,
                    has_some_applicable_signature,
                    non_applicable_type,
                ));
            }
            return self.get_union_type(&mapped);
        } else if flags.intersects(TypeFlags::INTERSECTION) {
            let __arena___guard_types = self.types.clone();
            let __guard_types = __arena___guard_types.get(t).clone();
            let types = __guard_types
                .as_intersection_type()
                .union_or_intersection
                .types
                .clone();
            let mut mapped = Vec::with_capacity(types.len());
            for constituent in types {
                mapped.push(self.get_instantiated_type_part(
                    node,
                    type_argument_nodes,
                    constituent,
                    has_signatures,
                    has_applicable_signature,
                    has_some_applicable_signature,
                    non_applicable_type,
                ));
            }
            return self.get_intersection_type(&mapped);
        }
        t
    }

    /// `(c *Checker) getInstantiatedType` — outer closure of
    /// `getInstantiationExpressionType` (checker.go:10914).
    pub(crate) fn get_instantiated_type(
        &mut self,
        node: NodeId,
        type_argument_nodes: &[NodeId],
        t: TypeId,
        has_signatures: &mut std::cell::Cell<bool>,
        has_applicable_signature: &mut std::cell::Cell<bool>,
        has_some_applicable_signature: &mut bool,
        non_applicable_type: &mut Option<TypeId>,
    ) -> TypeId {
        let mut local_signatures = std::cell::Cell::new(false);
        let mut local_applicable = std::cell::Cell::new(false);
        let result = self.get_instantiated_type_part(
            node,
            type_argument_nodes,
            t,
            &mut local_signatures,
            &mut local_applicable,
            has_some_applicable_signature,
            non_applicable_type,
        );
        has_signatures.set(has_signatures.get() || local_signatures.get());
        has_applicable_signature.set(has_applicable_signature.get() || local_applicable.get());
        *has_some_applicable_signature = *has_some_applicable_signature || local_applicable.get();
        if local_signatures.get() && !local_applicable.get() && non_applicable_type.is_none() {
            *non_applicable_type = Some(t);
        }
        result
    }

    /// `(c *Checker) checkSatisfiesExpression` (checker.go:10975).
    pub(crate) fn check_satisfies_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let type_node = nodes[node].type_().unwrap();
        self.check_source_element(Some(type_node));
        let expr_type = self.check_expression(nodes[node].expression().unwrap());
        let target_type = self.get_type_from_type_node(type_node);
        if self.is_error_type(target_type) {
            return target_type;
        }
        self.check_type_assignable_to_and_optionally_elaborate(
            expr_type,
            target_type,
            Some(node),
            nodes[node].expression(),
            Some(&tsc_diagnostics::Type_0_does_not_satisfy_the_expected_type_1),
            None,
        );
        expr_type
    }

    /// `(c *Checker) checkMetaProperty` (checker.go:10987).
    pub(crate) fn check_meta_property(&mut self, node: NodeId) -> TypeId {
        self.check_grammar_meta_property(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].as_meta_property().keyword_token {
            ast::Kind::NewKeyword => self.check_new_target_meta_property(node),
            ast::Kind::ImportKeyword => {
                if ast::is_import_phase_meta_property(&nodes[node], &nodes) {
                    if nodes[node]
                        .parent
                        .is_some_and(|p| ast::is_call_expression(&nodes[p]))
                    {
                        debug_assert!(
                            nodes[nodes[node].parent.unwrap()].expression() != Some(node),
                            "Trying to get the type of a phase import meta-property in its call"
                        );
                    }
                    return self.error_type;
                }
                self.check_import_meta_property(node)
            }
            _ => panic!("Unhandled case in checkMetaProperty"),
        }
    }

    /// `(c *Checker) checkNewTargetMetaProperty` (checker.go:11004).
    pub(crate) fn check_new_target_meta_property(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let container = ast::get_new_target_container(node, &nodes);
        let Some(container) = container else {
            self.error(
                Some(node),
                &tsc_diagnostics::Meta_property_0_is_only_allowed_in_the_body_of_a_function_declaration_function_expression_or_constructor,
                &["new.target".to_string()],
            );
            return self.error_type;
        };
        let __program = self.program.clone().expect("program");
        let container_nodes = __program.nodes((container).file_index());
        if ast::is_constructor_declaration(&container_nodes[container]) {
            let symbol = self.get_symbol_of_declaration(container_nodes[container].parent.unwrap());
            return self.get_type_of_symbol(symbol.expect("symbol"));
        }
        let symbol = self.get_symbol_of_declaration(container).expect("symbol");
        self.get_type_of_symbol(symbol)
    }

    /// `(c *Checker) checkImportMetaProperty` (checker.go:11018).
    pub(crate) fn check_import_meta_property(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if tsc_core::options_generated::ModuleKind::Node16 <= self.module_kind
            && self.module_kind <= tsc_core::options_generated::ModuleKind::NodeNext
        {
            let source_file = ast::get_source_file_of_node(Some(node), &nodes);
            if let Some(source_file) = source_file {
                let source_file_meta_data = self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_source_file_meta_data(nodes[source_file].as_source_file().path_key());
                if source_file_meta_data.implied_node_format
                    != tsc_core::options_generated::ModuleKind::ESNext
                {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::The_import_meta_meta_property_is_not_allowed_in_files_which_will_build_into_CommonJS_output,
                        &[] as &[String],
                    );
                }
            }
        } else if self.module_kind < tsc_core::options_generated::ModuleKind::ES2020
            && self.module_kind != tsc_core::options_generated::ModuleKind::System
        {
            self.error(
                Some(node),
                &tsc_diagnostics::The_import_meta_meta_property_is_only_allowed_when_the_module_option_is_es2020_es2022_esnext_system_node16_node18_node20_or_nodenext,
                &[] as &[String],
            );
        }
        let file = ast::get_source_file_of_node(Some(node), &nodes);
        debug_assert!(
            file.is_some_and(|f| nodes[f]
                .flags
                .intersects(ast::NodeFlags::POSSIBLY_CONTAINS_IMPORT_META)),
            "Containing file is missing import meta node flag."
        );
        if nodes[node]
            .name()
            .is_some_and(|n| nodes[n].text(&nodes) == "meta")
        {
            return self.get_global_import_meta_type();
        }
        self.error_type
    }

    /// `(c *Checker) checkMetaPropertyKeyword` (checker.go:11035).
    pub(crate) fn check_meta_property_keyword(&mut self, _node: NodeId) -> TypeId {
        // !!! This is effectively a helper for GetSymbolAtLocation and GetTypeAtLocation
        self.error_type
    }

    /// `(c *Checker) checkDeleteExpression` (checker.go:11040).
    pub(crate) fn check_delete_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(expr) = nodes[node].expression() {
            self.check_expression(expr);
        }
        let expr = ast::skip_parentheses(nodes[node].expression().unwrap(), &nodes);
        if !ast::is_access_expression(&nodes[expr]) {
            self.error(
                Some(expr),
                &tsc_diagnostics::The_operand_of_a_delete_operator_must_be_a_property_reference,
                &[] as &[String],
            );
            return self.boolean_type;
        }
        if ast::is_property_access_expression(&nodes[expr])
            && nodes[expr]
                .name()
                .is_some_and(|n| ast::is_private_identifier(&nodes[n]))
        {
            self.error(
                Some(expr),
                &tsc_diagnostics::The_operand_of_a_delete_operator_cannot_be_a_private_identifier,
                &[] as &[String],
            );
        }
        let symbol = self
            .get_resolved_symbol_or_nil(expr)
            .and_then(|s| self.get_export_symbol_of_value_symbol_if_exported(Some(s)));
        if let Some(symbol) = symbol {
            if self.is_readonly_symbol(symbol) {
                self.error(
                    Some(expr),
                    &tsc_diagnostics::The_operand_of_a_delete_operator_cannot_be_a_read_only_property,
                    &[] as &[String],
                );
            } else {
                self.check_delete_expression_must_be_optional(expr, symbol);
            }
        }
        self.boolean_type
    }

    /// `(c *Checker) checkDeleteExpressionMustBeOptional` (checker.go:11061).
    pub(crate) fn check_delete_expression_must_be_optional(
        &mut self,
        expr: NodeId,
        symbol: SymbolId,
    ) {
        let t = self.get_type_of_symbol(symbol);
        if self.strict_null_checks
            && !self
                .types_handle()
                .get_ref(t)
                .flags
                .intersects(TypeFlags::ANY_OR_UNKNOWN | TypeFlags::NEVER)
        {
            let is_optional = if self.exact_optional_property_types {
                self.sym(symbol)
                    .flags
                    .intersects(ast::SymbolFlags::OPTIONAL)
            } else {
                self.has_type_facts(t, TypeFacts::IS_UNDEFINED)
            };
            if !is_optional {
                self.error(
                    Some(expr),
                    &tsc_diagnostics::The_operand_of_a_delete_operator_must_be_optional,
                    &[] as &[String],
                );
            }
        }
    }

    /// `(c *Checker) checkVoidExpression` (checker.go:11076).
    pub(crate) fn check_void_expression(&mut self, node: NodeId) -> TypeId {
        self.check_node_deferred(node);
        self.undefined_widening_type
    }

    /// `(c *Checker) checkAwaitExpression` (checker.go:11081).
    pub(crate) fn check_await_expression(&mut self, node: NodeId) -> TypeId {
        self.check_grammar_await_or_await_using(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let operand_type = self.check_expression(nodes[node].expression().unwrap());
        let awaited_type = self.check_awaited_type(
            operand_type,
            true, /*withAlias*/
            Some(node),
            &tsc_diagnostics::Type_of_await_operand_must_either_be_a_valid_promise_or_must_not_contain_a_callable_then_member,
            &[] as &[String],
        );
        if awaited_type == operand_type
            && !self.is_error_type(awaited_type)
            && !self
                .types_handle()
                .get_ref(operand_type)
                .flags
                .intersects(TypeFlags::ANY_OR_UNKNOWN)
        {
            let diagnostic = self.new_diagnostic_for_node(
                Some(node),
                &tsc_diagnostics::X_await_has_no_effect_on_the_type_of_this_expression,
                &[] as &[String],
            );
            self.add_error_or_suggestion(false, &diagnostic);
        }
        awaited_type
    }
}

impl Checker {
    /// `(c *Checker) checkPrefixUnaryExpression` (checker.go:11091).
    pub(crate) fn check_prefix_unary_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expr = nodes[node].as_prefix_unary_expression().clone();
        let operand_type = self.check_expression(expr.operand.unwrap());
        if operand_type == self.silent_never_type {
            return self.silent_never_type;
        }
        match nodes[expr.operand.unwrap()].kind {
            ast::Kind::NumericLiteral => match expr.operator {
                ast::Kind::MinusToken => {
                    let value = tsc_jsnum::from_string(&nodes[expr.operand.unwrap()].text(&nodes));
                    let t = self.get_number_literal_type(-value);
                    return self.get_fresh_type_of_literal_type(t);
                }
                ast::Kind::PlusToken => {
                    let value = tsc_jsnum::from_string(&nodes[expr.operand.unwrap()].text(&nodes));
                    let t = self.get_number_literal_type(value);
                    return self.get_fresh_type_of_literal_type(t);
                }
                _ => {}
            },
            ast::Kind::BigIntLiteral => {
                if expr.operator == ast::Kind::MinusToken {
                    let text = nodes[expr.operand.unwrap()].text(&nodes).into_owned();
                    let parsed = tsc_jsnum::parse_pseudo_big_int(&text);
                    let bigint = tsc_jsnum::new_pseudo_big_int(&parsed, true /*negative*/);
                    let t = self.get_big_int_literal_type(bigint);
                    return self.get_fresh_type_of_literal_type(t);
                }
            }
            _ => {}
        }
        match expr.operator {
            ast::Kind::PlusToken | ast::Kind::MinusToken | ast::Kind::TildeToken => {
                self.check_non_null_type(operand_type, expr.operand.unwrap());
                if self.maybe_type_of_kind_considering_base_constraint(
                    operand_type,
                    TypeFlags::ES_SYMBOL_LIKE,
                ) {
                    self.error(
                        expr.operand,
                        &tsc_diagnostics::The_0_operator_cannot_be_applied_to_type_symbol,
                        &[tsc_scanner::scanner::token_to_string(expr.operator).to_string()],
                    );
                }
                if expr.operator == ast::Kind::PlusToken {
                    if self.maybe_type_of_kind_considering_base_constraint(
                        operand_type,
                        TypeFlags::BIG_INT_LIKE,
                    ) {
                        let base = self.get_base_type_of_literal_type(operand_type);
                        let base_string = self.type_to_string(base);
                        self.error(
                            expr.operand,
                            &tsc_diagnostics::Operator_0_cannot_be_applied_to_type_1,
                            &[
                                tsc_scanner::scanner::token_to_string(expr.operator).to_string(),
                                base_string,
                            ],
                        );
                    }
                    return self.number_type;
                }
                return self.get_unary_result_type(operand_type);
            }
            ast::Kind::ExclamationToken => {
                self.check_truthiness_of_type(operand_type, expr.operand.unwrap());
                let facts = self.get_type_facts(operand_type, TypeFacts::TRUTHY | TypeFacts::FALSY);
                if facts == TypeFacts::TRUTHY {
                    return self.false_type;
                } else if facts == TypeFacts::FALSY {
                    return self.true_type;
                } else {
                    return self.boolean_type;
                }
            }
            ast::Kind::PlusPlusToken | ast::Kind::MinusMinusToken => {
                let non_null = self.check_non_null_type(operand_type, expr.operand.unwrap());
                let ok = self.check_arithmetic_operand_type(
                    expr.operand.unwrap(),
                    non_null,
                    &tsc_diagnostics::An_arithmetic_operand_must_be_of_type_any_number_bigint_or_an_enum_type,
                    false,
                );
                if ok {
                    // run check only if former checks succeeded to avoid reporting cascading errors
                    self.check_reference_expression(
                        expr.operand.unwrap(),
                        &tsc_diagnostics::The_operand_of_an_increment_or_decrement_operator_must_be_a_variable_or_a_property_access,
                        &tsc_diagnostics::The_operand_of_an_increment_or_decrement_operator_may_not_be_an_optional_property_access,
                    );
                }
                return self.get_unary_result_type(operand_type);
            }
            _ => {}
        }
        self.error_type
    }

    /// `(c *Checker) checkPostfixUnaryExpression` (checker.go:11145).
    pub(crate) fn check_postfix_unary_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expr = nodes[node].as_postfix_unary_expression().clone();
        let operand_type = self.check_expression(expr.operand.unwrap());
        if operand_type == self.silent_never_type {
            return self.silent_never_type;
        }
        let non_null = self.check_non_null_type(operand_type, expr.operand.unwrap());
        let ok = self.check_arithmetic_operand_type(
            expr.operand.unwrap(),
            non_null,
            &tsc_diagnostics::An_arithmetic_operand_must_be_of_type_any_number_bigint_or_an_enum_type,
            false,
        );
        if ok {
            // run check only if former checks succeeded to avoid reporting cascading errors
            self.check_reference_expression(
                expr.operand.unwrap(),
                &tsc_diagnostics::The_operand_of_an_increment_or_decrement_operator_must_be_a_variable_or_a_property_access,
                &tsc_diagnostics::The_operand_of_an_increment_or_decrement_operator_may_not_be_an_optional_property_access,
            );
        }
        self.get_unary_result_type(operand_type)
    }

    /// `(c *Checker) getUnaryResultType` (checker.go:11159).
    pub(crate) fn get_unary_result_type(&mut self, operand_type: TypeId) -> TypeId {
        if self.maybe_type_of_kind(operand_type, TypeFlags::BIG_INT_LIKE) {
            if self.is_type_assignable_to_kind(operand_type, TypeFlags::ANY_OR_UNKNOWN)
                || self.maybe_type_of_kind(operand_type, TypeFlags::NUMBER_LIKE)
            {
                return self.number_or_big_int_type;
            }
            return self.bigint_type;
        }
        // If it's not a bigint type, implicit coercion will result in a number
        self.number_type
    }

    /// `(c *Checker) checkConditionalExpression` (checker.go:11170).
    pub(crate) fn check_conditional_expression(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let cond = nodes[node].as_conditional_expression().clone();
        let t = self.check_truthiness_expression(cond.condition.unwrap(), check_mode);
        self.check_testing_known_truthy_callable_or_awaitable_or_enum_member_type(
            cond.condition.unwrap(),
            t,
            cond.when_true,
        );
        let type1 = self.check_expression_ex(cond.when_true.unwrap(), check_mode);
        let type2 = self.check_expression_ex(cond.when_false.unwrap(), check_mode);
        self.get_union_type_ex(&[type1, type2], UnionReduction::Subtype, None, None)
    }

    /// `(c *Checker) checkTruthinessExpression` (checker.go:11179).
    pub(crate) fn check_truthiness_expression(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let t = self.check_expression_ex(node, check_mode);
        self.check_truthiness_of_type(t, node)
    }

    /// `(c *Checker) checkSpreadExpression` (checker.go:11183).
    pub(crate) fn check_spread_expression(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expr = nodes[node].expression().unwrap();
        let array_or_iterable_type = self.check_expression_ex(expr, check_mode);
        self.check_iterated_type_or_element_type(
            IterationUse::SPREAD,
            array_or_iterable_type,
            self.undefined_type,
            Some(expr),
        )
    }

    /// `(c *Checker) checkYieldExpression` (checker.go:11188).
    pub(crate) fn check_yield_expression(&mut self, node: NodeId) -> TypeId {
        self.check_grammar_yield_expression(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Always check the operand so its identifiers are resolved even when the yield is
        // outside a generator, keeping diagnostics stable regardless of traversal order.
        let yield_expression_type = if let Some(expr) = nodes[node].expression() {
            self.check_expression(expr)
        } else {
            self.undefined_widening_type
        };
        let fn_ = ast::get_containing_function(node, &nodes);
        let Some(fn_) = fn_ else {
            return self.any_type;
        };
        let __program = self.program.clone().expect("program");
        let fn_nodes = __program.nodes((fn_).file_index());
        let function_flags = ast::get_function_flags(Some(&fn_nodes[fn_]));
        if !function_flags.intersects(ast::FunctionFlags::GENERATOR) {
            // If the user's code is syntactically correct, the func should always have a star. After all, we are in a yield context.
            return self.any_type;
        }
        let is_async = function_flags.intersects(ast::FunctionFlags::ASYNC);
        if nodes[node].as_yield_expression().asterisk_token.is_some() {
            // Async generator functions prior to ES2018 require the __await, __asyncDelegator,
            // and __asyncValues helpers
            if is_async
                && self.language_version
                    < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.async_generators
            {
                self.check_external_emit_helpers(
                    node,
                    ExternalEmitHelpers::ASYNC_DELEGATOR_INCLUDES,
                );
            }
        }
        // There is no point in doing an assignability check if the function
        // has no explicit return type because the return type is directly computed
        // from the yield expressions.
        let mut return_type = self.get_return_type_from_annotation(fn_);
        if let Some(rt) = return_type {
            if self
                .types_handle()
                .get_ref(rt)
                .flags
                .intersects(TypeFlags::UNION)
            {
                return_type = Some(self.filter_type(rt, &|c: &mut Checker, t: TypeId| {
                    c.check_generator_instantiation_assignability_to_return_type(
                        t,
                        function_flags,
                        None, /*errorNode*/
                    )
                }));
            }
        }
        let mut iteration_types = IterationTypes::default();
        if let Some(rt) = return_type {
            iteration_types =
                self.get_iteration_types_of_generator_function_return_type(rt, is_async);
        }
        let signature_yield_type = iteration_types.yield_type.unwrap_or(self.any_type);
        let signature_next_type = iteration_types.next_type.unwrap_or(self.any_type);
        let yielded_type = self.get_yielded_type_of_yield_expression(
            node,
            yield_expression_type,
            signature_next_type,
            is_async,
        );
        if return_type.is_some() && yielded_type.is_some() {
            self.check_type_assignable_to_and_optionally_elaborate(
                yielded_type.unwrap(),
                signature_yield_type,
                nodes[node].expression().or(Some(node)),
                nodes[node].expression(),
                Some(&tsc_diagnostics::Type_0_is_not_assignable_to_type_1),
                None,
            );
        }
        if nodes[node].as_yield_expression().asterisk_token.is_some() {
            let use_ = if is_async {
                IterationUse::ASYNC_YIELD_STAR
            } else {
                IterationUse::YIELD_STAR
            };
            return self
                .get_iteration_type_of_iterable(
                    use_,
                    IterationTypeKind::Return,
                    yield_expression_type,
                    nodes[node].expression(),
                )
                .unwrap_or(self.any_type);
        }
        if let Some(rt) = return_type {
            return self
                .get_iteration_type_of_generator_function_return_type(
                    IterationTypeKind::Next,
                    rt,
                    is_async,
                )
                .unwrap_or(self.any_type);
        }
        let mut t = self.get_contextual_iteration_type(IterationTypeKind::Next, fn_);
        if t.is_none() {
            t = Some(self.any_type);
            if self.no_implicit_any
                && !crate::utilities::expression_result_is_unused(&nodes[node], &nodes)
            {
                let contextual_type = self.get_contextual_type(node, ContextFlags::NONE);
                if contextual_type.is_none()
                    || contextual_type.is_some_and(|ct| crate::types::is_type_any(&self.types, ct))
                {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::X_yield_expression_implicitly_results_in_an_any_type_because_its_containing_generator_lacks_a_return_type_annotation,
                        &[] as &[String],
                    );
                }
            }
        }
        t.unwrap()
    }

    /// `(c *Checker) getYieldedTypeOfYieldExpression` (checker.go:11254).
    pub(crate) fn get_yielded_type_of_yield_expression(
        &mut self,
        node: NodeId,
        expression_type: TypeId,
        sent_type: TypeId,
        is_async: bool,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let error_node = nodes[node].expression().or(Some(node));
        let is_yield_star = nodes[node].as_yield_expression().asterisk_token.is_some();
        // A `yield*` expression effectively yields everything that its operand yields
        let mut yielded_type = expression_type;
        if is_yield_star {
            yielded_type = self.check_iterated_type_or_element_type(
                if is_async {
                    IterationUse::ASYNC_YIELD_STAR
                } else {
                    IterationUse::YIELD_STAR
                },
                expression_type,
                sent_type,
                error_node,
            );
        }
        if !is_async {
            return Some(yielded_type);
        }
        self.get_awaited_type_ex(
            yielded_type,
            error_node,
            Some(if is_yield_star {
                &tsc_diagnostics::Type_of_iterated_elements_of_a_yield_Asterisk_operand_must_either_be_a_valid_promise_or_must_not_contain_a_callable_then_member
            } else {
                &tsc_diagnostics::Type_of_yield_operand_in_an_async_generator_must_either_be_a_valid_promise_or_must_not_contain_a_callable_then_member
            }),
            &[],
        )
    }

    /// `(c *Checker) checkSyntheticExpression` (checker.go:11270).
    pub(crate) fn check_synthetic_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let t = TypeId(nodes[node].as_synthetic_expression().type_.unwrap_or(0) as u32);
        if nodes[node].as_synthetic_expression().is_spread {
            return self.get_indexed_access_type(t, self.number_type);
        }
        t
    }

    /// `(c *Checker) checkIdentifier` (checker.go:11278).
    pub(crate) fn check_identifier(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_this_in_type_query(node, &nodes) {
            return self.check_this_expression(node);
        }
        let symbol = self.get_resolved_symbol(node);
        if symbol == self.unknown_symbol {
            return self.error_type;
        }
        if symbol == self.arguments_symbol {
            if self.is_in_property_initializer_or_class_static_block(
                node, true, /*ignoreArrowFunctions*/
            ) {
                self.error(
                    Some(node),
                    &tsc_diagnostics::X_arguments_cannot_be_referenced_in_property_initializers_or_class_static_initialization_blocks,
                    &[] as &[String],
                );
                return self.error_type;
            }
            return self.get_type_of_symbol(symbol);
        }
        if crate::checker_d::should_mark_identifier_alias_referenced(&nodes, node) {
            self.mark_linked_references(
                node,
                ReferenceHint::Identifier,
                None, /*propSymbol*/
                None, /*parentType*/
            
                None,
            );
        }
        let local_or_export_symbol = self
            .get_export_symbol_of_value_symbol_if_exported(Some(symbol))
            .expect("localOrExportSymbol");
        let target_symbol = self.resolve_alias_with_deprecation_check(local_or_export_symbol, node);
        let target_declarations = self.sym(target_symbol).declarations.clone();
        if !target_declarations.is_empty()
            && self.is_deprecated_symbol(target_symbol)
            && self.is_uncalled_function_reference(node, target_symbol)
        {
            let name = nodes[node].text(&nodes).into_owned();
            self.add_deprecated_suggestion(node, &target_declarations, &name);
        }
        let mut declaration = self.sym(local_or_export_symbol).value_declaration;
        let immediate_declaration = declaration;
        // If the identifier is declared in a binding pattern for which we're currently computing the implied type and the
        // reference occurs with the same binding pattern, return the non-inferrable any type. This for example occurs in
        // 'const [a, b = a + 1] = [2]' when we're computing the contextual type for the array literal '[2]'.
        if let Some(declaration_id) = declaration {
            let __program = self.program.clone().expect("program");
            let decl_nodes = __program.nodes((declaration_id).file_index());
            if decl_nodes[declaration_id].kind == ast::Kind::BindingElement
                && decl_nodes[declaration_id]
                    .parent
                    .is_some_and(|p| self.contextual_binding_patterns.contains(&p))
                && ast::find_ancestor(Some(node), &decl_nodes, &mut |parent, _| {
                    Some(parent.id) == decl_nodes[declaration_id].parent
                })
                .is_some()
            {
                return self.non_inferrable_any_type;
            }
        }
        let t = self.get_narrowed_type_of_symbol(local_or_export_symbol, node);
        let assignment_kind = crate::utilities::get_assignment_target_kind(node, &nodes);
        if assignment_kind != crate::utilities::AssignmentKind::NONE {
            if !self
                .sym(local_or_export_symbol)
                .flags
                .intersects(ast::SymbolFlags::VARIABLE)
                && !(ast::is_in_js_file(Some(node), &nodes)
                    && self
                        .sym(local_or_export_symbol)
                        .flags
                        .intersects(ast::SymbolFlags::VALUE_MODULE))
            {
                let flags = self.sym(local_or_export_symbol).flags;
                let assignment_error = if flags.intersects(ast::SymbolFlags::ENUM) {
                    &tsc_diagnostics::Cannot_assign_to_0_because_it_is_an_enum
                } else if flags.intersects(ast::SymbolFlags::CLASS) {
                    &tsc_diagnostics::Cannot_assign_to_0_because_it_is_a_class
                } else if flags.intersects(ast::SymbolFlags::MODULE) {
                    &tsc_diagnostics::Cannot_assign_to_0_because_it_is_a_namespace
                } else if flags.intersects(ast::SymbolFlags::FUNCTION) {
                    &tsc_diagnostics::Cannot_assign_to_0_because_it_is_a_function
                } else if flags.intersects(ast::SymbolFlags::ALIAS) {
                    &tsc_diagnostics::Cannot_assign_to_0_because_it_is_an_import
                } else {
                    &tsc_diagnostics::Cannot_assign_to_0_because_it_is_not_a_variable
                };
                let symbol_string = self.symbol_to_string(symbol);
                self.error(Some(node), assignment_error, &[symbol_string]);
                return self.error_type;
            }
            if self.is_readonly_symbol(local_or_export_symbol) {
                let symbol_string = self.symbol_to_string(symbol);
                if self
                    .sym(local_or_export_symbol)
                    .flags
                    .intersects(ast::SymbolFlags::VARIABLE)
                {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Cannot_assign_to_0_because_it_is_a_constant,
                        &[symbol_string],
                    );
                } else {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Cannot_assign_to_0_because_it_is_a_read_only_property,
                        &[symbol_string],
                    );
                }
                return self.error_type;
            }
        }
        let is_alias = self
            .sym(local_or_export_symbol)
            .flags
            .intersects(ast::SymbolFlags::ALIAS);
        // We only narrow variables and parameters occurring in a non-assignment position. For all other
        // entities we simply return the declared type.
        if self
            .sym(local_or_export_symbol)
            .flags
            .intersects(ast::SymbolFlags::VARIABLE)
        {
            if assignment_kind == crate::utilities::AssignmentKind::DEFINITE {
                if crate::utilities::is_in_compound_like_assignment(node, &nodes) {
                    return self.get_base_type_of_literal_type(t);
                }
                return t;
            }
        } else if is_alias {
            declaration = self.get_declaration_of_alias_symbol(symbol);
        } else {
            return t;
        }
        let Some(declaration) = declaration else {
            return t;
        };
        let t = self.get_narrowable_type_for_reference(t, node, check_mode);
        // The declaration container is the innermost function that encloses the declaration of the variable
        // or parameter. The flow container is the innermost function starting with which we analyze the control
        // flow graph to determine the control flow based type.
        let __program = self.program.clone().expect("program");
        let decl_nodes = __program.nodes((declaration).file_index());
        let is_parameter = decl_nodes[ast::get_root_declaration(declaration, &decl_nodes)].kind
            == ast::Kind::Parameter;
        let declaration_container = self.get_control_flow_container(declaration);
        let mut flow_container = self.get_control_flow_container(node);
        let is_outer_variable = flow_container != declaration_container;
        let is_spread_destructuring_assignment_target = nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .is_some_and(|pp| {
                nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_spread_assignment(&nodes[p]))
                    && self.is_destructuring_assignment_target(&nodes, pp)
            });
        let is_module_exports = self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::MODULE_EXPORTS);
        let type_is_automatic = t == self.auto_type || t == self.auto_array_type;
        let is_automatic_type_in_non_null = type_is_automatic
            && nodes[node]
                .parent
                .is_some_and(|p| nodes[p].kind == ast::Kind::NonNullExpression);
        // When the control flow originates in a function expression, arrow function, method, or accessor, and
        // we are referencing a closed-over const variable or parameter or mutable local variable past its last
        // assignment, we extend the origin of the control flow analysis to include the immediately enclosing
        // control flow container.
        while flow_container != declaration_container
            && flow_container.is_some_and(|fc| {
                let __program = self.program.clone().expect("program");
                let fc_nodes = __program.nodes((fc).file_index());
                ast::is_function_expression_or_arrow_function(&fc_nodes[fc])
                    || ast::is_object_literal_or_class_expression_method_or_accessor(fc, &fc_nodes)
            })
            && (self.is_constant_variable(local_or_export_symbol) && t != self.auto_array_type
                || self.is_parameter_or_mutable_local_variable(local_or_export_symbol)
                    && self.is_past_last_assignment(local_or_export_symbol, Some(node)))
        {
            flow_container = self.get_control_flow_container(flow_container.unwrap());
        }
        // We only look for uninitialized variables in strict null checking mode, and only when we can analyze
        // the entire control flow graph from the variable's declaration (i.e. when the flow container and
        // declaration container are the same).
        let is_never_initialized = immediate_declaration.is_some_and(|d| {
            let __program = self.program.clone().expect("program");
            let d_nodes = __program.nodes((d).file_index());
            ast::is_variable_declaration(&d_nodes[d])
                && !d_nodes[d]
                    .parent
                    .and_then(|p| d_nodes[p].parent)
                    .is_some_and(|pp| ast::is_for_in_or_of_statement(Some(pp), &d_nodes))
                && d_nodes[d].initializer().is_none()
                && d_nodes[d]
                    .as_variable_declaration()
                    .exclamation_token
                    .is_none()
                && self.is_mutable_local_variable_declaration(d)
                && !self.is_symbol_assigned_definitely(symbol)
        });
        let assume_initialized = is_parameter
            || is_alias
            || (is_outer_variable && !is_never_initialized)
            || is_spread_destructuring_assignment_target
            || is_module_exports
            || self.is_same_scoped_binding_element(node, declaration)
            || t != self.auto_type
                && t != self.auto_array_type
                && (!self.strict_null_checks
                    || self
                        .types_handle()
                        .get(t)
                        .flags
                        .intersects(TypeFlags::ANY_OR_UNKNOWN | TypeFlags::VOID)
                    || crate::utilities::is_in_type_query(node, &nodes)
                    || self.is_in_ambient_or_type_node(node)
                    || nodes[node]
                        .parent
                        .is_some_and(|p| nodes[p].kind == ast::Kind::ExportSpecifier))
            || nodes[node]
                .parent
                .is_some_and(|p| ast::is_non_null_expression(&nodes[p]))
            || ast::is_variable_declaration(&decl_nodes[declaration])
                && decl_nodes[declaration]
                    .as_variable_declaration()
                    .exclamation_token
                    .is_some()
            || decl_nodes[declaration]
                .flags
                .intersects(ast::NodeFlags::AMBIENT);
        let initial_type = if is_automatic_type_in_non_null {
            self.undefined_type
        } else if assume_initialized && is_parameter {
            self.remove_optionality_from_declared_type(t, declaration)
        } else if assume_initialized {
            t
        } else if type_is_automatic {
            self.undefined_type
        } else {
            self.get_optional_type(t, false /*isProperty*/)
        };
        let flow_type = if is_automatic_type_in_non_null {
            let t2 = self.get_flow_type_of_reference_ex(
                node,
                t,
                Some(initial_type),
                flow_container,
                None,
            );
            self.get_non_nullable_type(t2)
        } else {
            self.get_flow_type_of_reference_ex(node, t, Some(initial_type), flow_container, None)
        };
        // A variable is considered uninitialized when it is possible to analyze the entire control flow graph
        // from declaration to use, and when the variable's declared type doesn't include undefined but the
        // control flow based type does include undefined.
        if !self.is_evolving_array_operation_target(&nodes, node)
            && (t == self.auto_type || t == self.auto_array_type)
        {
            if flow_type == self.auto_type || flow_type == self.auto_array_type {
                if self.no_implicit_any {
                    let symbol_string = self.symbol_to_string(symbol);
                    let flow_string = self.type_to_string(flow_type);
                    let name_of_declaration =
                        ast::get_name_of_declaration(Some(declaration), &decl_nodes);
                    self.error(
                        name_of_declaration,
                        &tsc_diagnostics::Variable_0_implicitly_has_type_1_in_some_locations_where_its_type_cannot_be_determined,
                        &[symbol_string.clone(), flow_string.clone()],
                    );
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Variable_0_implicitly_has_an_1_type,
                        &[symbol_string, flow_string],
                    );
                }
                return self.convert_auto_to_any(flow_type);
            }
        } else if !assume_initialized
            && !self.contains_undefined_type(t)
            && self.contains_undefined_type(flow_type)
        {
            let symbol_string = self.symbol_to_string(symbol);
            self.error(
                Some(node),
                &tsc_diagnostics::Variable_0_is_used_before_being_assigned,
                &[symbol_string],
            );
            // Return the declared type to reduce follow-on errors
            return t;
        }
        if assignment_kind != crate::utilities::AssignmentKind::NONE {
            // Identifier is target of a compound assignment
            return self.get_base_type_of_literal_type(flow_type);
        }
        flow_type
    }

    /// `(c *Checker) isSameScopedBindingElement` (checker.go:11438).
    pub(crate) fn is_same_scoped_binding_element(
        &mut self,
        node: NodeId,
        declaration: NodeId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if ast::is_binding_element(&nodes[declaration]) {
            let binding_element =
                ast::find_ancestor(Some(node), &nodes, &mut |n, _| ast::is_binding_element(n));
            return binding_element.is_some_and(|b| {
                ast::get_root_declaration(b, &nodes)
                    == ast::get_root_declaration(declaration, &nodes)
            });
        }
        false
    }

    /// `(c *Checker) removeOptionalityFromDeclaredType` (checker.go:11447).
    /// Remove undefined from the annotated type of a parameter when there is
    /// an initializer (that doesn't include undefined)
    pub(crate) fn remove_optionality_from_declared_type(
        &mut self,
        declared_type: TypeId,
        declaration: NodeId,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((declaration).file_index());
        let remove_undefined = self.strict_null_checks
            && ast::is_parameter_declaration(&nodes[declaration])
            && nodes[declaration].initializer().is_some()
            && self.has_type_facts(declared_type, TypeFacts::IS_UNDEFINED)
            && !self.parameter_initializer_contains_undefined(declaration);
        if remove_undefined {
            return self.get_type_with_facts(declared_type, TypeFacts::NE_UNDEFINED);
        }
        declared_type
    }

    /// `(c *Checker) parameterInitializerContainsUndefined` (checker.go:11455).
    pub(crate) fn parameter_initializer_contains_undefined(&mut self, declaration: NodeId) -> bool {
        if !self
            .node_links
            .get(declaration)
            .flags
            .intersects(NodeCheckFlags::INITIALIZER_IS_UNDEFINED_COMPUTED)
        {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((declaration).file_index());
            let symbol = nodes[declaration].symbol().expect("declaration symbol");
            if !self.push_type_resolution(
                TypeSystemEntity::Node(declaration),
                TypeSystemPropertyName::InitializerIsUndefined,
            ) {
                self.report_circularity_error(symbol);
                return true;
            }
            let t = self.check_declaration_initializer(declaration, CheckMode::NORMAL, None);
            let contains_undefined = self.has_type_facts(t, TypeFacts::IS_UNDEFINED);
            if !self.pop_type_resolution() {
                self.report_circularity_error(symbol);
                return true;
            }
            if !self
                .node_links
                .get(declaration)
                .flags
                .intersects(NodeCheckFlags::INITIALIZER_IS_UNDEFINED_COMPUTED)
            {
                self.node_links.get(declaration).flags |=
                    NodeCheckFlags::INITIALIZER_IS_UNDEFINED_COMPUTED
                        | if contains_undefined {
                            NodeCheckFlags::INITIALIZER_IS_UNDEFINED
                        } else {
                            NodeCheckFlags::NONE
                        };
            }
        }
        self.node_links
            .get(declaration)
            .flags
            .intersects(NodeCheckFlags::INITIALIZER_IS_UNDEFINED)
    }

    /// `(c *Checker) isInAmbientOrTypeNode` (checker.go:11474).
    pub(crate) fn is_in_ambient_or_type_node(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        nodes[node].flags.intersects(ast::NodeFlags::AMBIENT)
            || ast::find_ancestor(Some(node), &nodes, &mut |n, _| {
                ast::is_interface_declaration(n)
                    || ast::is_type_alias_declaration(n)
                    || ast::is_js_type_alias_declaration(n)
                    || ast::is_type_literal_node(n)
            })
            .is_some()
    }

    /// `(c *Checker) checkPropertyAccessExpression` (checker.go:11480).
    pub(crate) fn check_property_access_expression(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
        write_only: bool,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node].flags.intersects(ast::NodeFlags::OPTIONAL_CHAIN) {
            return self.check_property_access_chain(node, check_mode);
        }
        let expr = nodes[node]
            .expression()
            .expect("property access expression");
        let left_type = self.check_non_null_expression(expr);
        let right = nodes[node]
            .as_property_access_expression()
            .name
            .expect("property access name");
        self.check_property_access_expression_or_qualified_name(
            node, expr, left_type, right, check_mode, write_only,
        )
    }

    /// `(c *Checker) checkPropertyAccessChain` (checker.go:11488).
    pub(crate) fn check_property_access_chain(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expr = nodes[node]
            .expression()
            .expect("property access expression");
        let left_type = self.check_expression(expr);
        let non_optional_type = self.get_optional_expression_type(left_type, expr);
        let object_type = self.check_non_null_type(non_optional_type, expr);
        let name = nodes[node].name().expect("property access name");
        let t = self.check_property_access_expression_or_qualified_name(
            node,
            expr,
            object_type,
            name,
            check_mode,
            false,
        );
        self.propagate_optional_type_marker(t, node, non_optional_type != left_type)
    }

    /// `(c *Checker) checkPropertyAccessExpressionOrQualifiedName` (checker.go:11494).
    pub(crate) fn check_property_access_expression_or_qualified_name(
        &mut self,
        node: NodeId,
        left: NodeId,
        left_type: TypeId,
        right: NodeId,
        check_mode: CheckMode,
        write_only: bool,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent_symbol = self.get_resolved_symbol_or_nil(left);
        let assignment_kind = crate::utilities::get_assignment_target_kind(node, &nodes);
        let mut widened_type = left_type;
        if assignment_kind != crate::utilities::AssignmentKind::NONE
            || self.is_method_access_for_call(node)
        {
            widened_type = self.get_widened_type(left_type);
        }
        let apparent_type = self.get_apparent_type(widened_type);
        let is_any_like = crate::utilities::is_type_any(&self.types, apparent_type)
            || apparent_type == self.silent_never_type;
        let mut prop: Option<SymbolId> = None;
        let right_text = nodes[right].text(&nodes).into_owned();
        if ast::is_private_identifier(&nodes[right]) {
            if self.language_version
                < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET
                    .private_names_and_class_static_blocks
                || self.language_version
                    < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET
                        .class_and_class_element_decorators
                || !self.compiler_options.get_use_define_for_class_fields()
            {
                if assignment_kind != crate::utilities::AssignmentKind::NONE {
                    self.check_external_emit_helpers(
                        node,
                        ExternalEmitHelpers::CLASS_PRIVATE_FIELD_SET,
                    );
                }
                if assignment_kind != crate::utilities::AssignmentKind::DEFINITE {
                    self.check_external_emit_helpers(
                        node,
                        ExternalEmitHelpers::CLASS_PRIVATE_FIELD_GET,
                    );
                }
            }
            let lexically_scoped_symbol =
                self.lookup_symbol_for_private_identifier_declaration(&right_text, right);
            if assignment_kind != crate::utilities::AssignmentKind::NONE
                && lexically_scoped_symbol.is_some_and(|s| {
                    self.sym(s)
                        .value_declaration
                        .is_some_and(|d| ast::is_method_declaration(&self.program_nodes(d)[d]))
                })
            {
                self.grammar_error_on_node(
                    right,
                    &tsc_diagnostics::Cannot_assign_to_private_method_0_Private_methods_are_not_writable,
                    &[right_text.clone()],
                );
            }
            if is_any_like {
                if lexically_scoped_symbol.is_some() {
                    if self.is_error_type(apparent_type) {
                        return self.error_type;
                    }
                    return apparent_type;
                }
                if crate::utilities::get_containing_class_excluding_class_decorators(right, &nodes)
                    .is_none()
                {
                    self.grammar_error_on_node(
                        right,
                        &tsc_diagnostics::Private_identifiers_are_not_allowed_outside_class_bodies,
                        &[],
                    );
                    return self.any_type;
                }
            }
            if let Some(lss) = lexically_scoped_symbol {
                prop = self.get_private_identifier_property_of_type(left_type, lss);
            }
            if prop.is_none() {
                // Check for private-identifier-specific shadowing and
                // lexical-scoping errors.
                if self.check_private_identifier_property_access(
                    left_type,
                    right,
                    lexically_scoped_symbol,
                ) {
                    return self.error_type;
                }
                let containing_class =
                    crate::utilities::get_containing_class_excluding_class_decorators(
                        right, &nodes,
                    );
                if let Some(containing_class) = containing_class {
                    let __program = self.program.clone().expect("program");
                    let cc_nodes = __program.nodes((containing_class).file_index());
                    let source_file =
                        ast::get_source_file_of_node(Some(containing_class), &cc_nodes);
                    if ast::is_plain_js_file(
                        source_file.map(|sf| cc_nodes[sf].as_source_file()),
                        self.compiler_options.check_js,
                    ) {
                        self.grammar_error_on_node(
                            right,
                            &tsc_diagnostics::Private_field_0_must_be_declared_in_an_enclosing_class,
                            &[right_text.clone()],
                        );
                    }
                }
            } else {
                let prop_flags = self.sym(prop.unwrap()).flags;
                let is_setonly_accessor = prop_flags.intersects(ast::SymbolFlags::SET_ACCESSOR)
                    && !prop_flags.intersects(ast::SymbolFlags::GET_ACCESSOR);
                if is_setonly_accessor
                    && assignment_kind != crate::utilities::AssignmentKind::DEFINITE
                {
                    self.error(
                        Some(node),
                        &tsc_diagnostics::Private_accessor_was_defined_without_a_getter,
                        &[],
                    );
                }
            }
        } else {
            if is_any_like {
                if ast::is_identifier(&nodes[left]) && parent_symbol.is_some() {
                    self.mark_linked_references(
                        node,
                        ReferenceHint::Property,
                        None, /* propSymbol */
                        Some(left_type),
                    
                None,
            );
                }
                if self.is_error_type(apparent_type) {
                    return self.error_type;
                }
                return apparent_type;
            }
            prop = self.get_property_of_type_ex(
                apparent_type,
                &right_text,
                crate::checker_d::is_const_enum_object_type(self, apparent_type), /* skipObjectFunctionPropertyAugment */
                nodes[node].kind == ast::Kind::QualifiedName, /* includeTypeOnlyMembers */
            );
        }
        self.mark_linked_references(node, ReferenceHint::Property, prop, Some(left_type), None);
        let prop_type: Option<TypeId>;
        if prop.is_none() {
            let mut index_info: Option<IndexInfoId> = None;
            if !ast::is_private_identifier(&nodes[right])
                && (assignment_kind == crate::utilities::AssignmentKind::NONE
                    || !self.is_generic_object_type(left_type)
                    || crate::utilities::is_this_type_parameter(&self.types, left_type))
            {
                index_info = self.get_applicable_index_info_for_name(apparent_type, &right_text);
            }
            let Some(index_info) = index_info else {
                let is_unchecked_js = self.is_unchecked_js_suggestion(
                    Some(node),
                    self.types_handle().get(left_type).symbol(),
                    true, /* excludeClasses */
                );
                if !is_unchecked_js && self.is_js_literal_type(left_type) {
                    return self.any_type;
                }
                if self.types.get_ref(left_type).symbol() == Some(self.global_this_symbol) {
                    let global_symbol = self
                        .sym(self.global_this_symbol)
                        .exports
                        .get(right_text.as_str())
                        .copied();
                    if global_symbol.is_some_and(|gs| {
                        self.sym(gs)
                            .flags
                            .intersects(ast::SymbolFlags::BLOCK_SCOPED)
                    }) {
                        let lt = self.type_to_string(left_type);

                        self.error(
                            Some(right),
                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                            &[right_text.clone(), lt],
                        );
                    } else if self.no_implicit_any {
                        let lt = self.type_to_string(left_type);

                        self.error(
                            Some(right),
                            &tsc_diagnostics::Element_implicitly_has_an_any_type_because_type_0_has_no_index_signature,
                            &[lt],
                        );
                    }
                    return self.any_type;
                }
                if !right_text.is_empty()
                    && !self.check_and_report_error_for_extending_interface(Some(node))
                {
                    // must be deferred because reporting this error can cause us
                    // to materialize the containing type completely (to print
                    // it), leading to erroneous circularity errors
                    let report_type = tsc_core::core::if_else(
                        crate::utilities::is_this_type_parameter(&self.types, left_type),
                        apparent_type,
                        left_type,
                    );
                    self.add_deferred_diagnostic(Box::new(move |c: &mut Checker| {
                        c.report_nonexistent_property(right, report_type, is_unchecked_js);
                    }));
                }
                return self.error_type;
            };
            if self.index_info_arena.get(index_info).is_readonly
                && (ast::is_assignment_target(node, &nodes)
                    || crate::utilities::is_delete_target(node, &nodes))
            {
                let at = self.type_to_string(apparent_type);

                self.error(
                    Some(node),
                    &tsc_diagnostics::Index_signature_in_type_0_only_permits_reading,
                    &[at],
                );
            }
            let mut pt = self.index_info_arena.get(index_info).value_type;
            if self.compiler_options.no_unchecked_indexed_access == tsc_core::tristate::TS_TRUE
                && crate::utilities::get_assignment_target_kind(node, &nodes)
                    != crate::utilities::AssignmentKind::DEFINITE
            {
                pt = Some(self.get_union_type(&[pt.unwrap_or(self.error_type), self.missing_type]));
            }
            prop_type = pt;
            if self
                .compiler_options
                .no_property_access_from_index_signature
                == tsc_core::tristate::TS_TRUE
                && ast::is_property_access_expression(&nodes[node])
            {
                self.error(
                    Some(right),
                    &tsc_diagnostics::Property_0_comes_from_an_index_signature_so_it_must_be_accessed_with_0,
                    &[right_text.clone()],
                );
            }
            if let Some(declaration) = self.index_info_arena.get(index_info).declaration {
                if self.is_deprecated_declaration(declaration) {
                    self.add_deprecated_suggestion(right, &[declaration], &right_text);
                }
            }
        } else {
            let prop = prop.unwrap();
            let target_prop_symbol = self.resolve_alias_with_deprecation_check(prop, right);
            if self.is_deprecated_symbol(target_prop_symbol)
                && self.is_uncalled_function_reference(node, target_prop_symbol)
                && !self.sym(target_prop_symbol).declarations.is_empty()
            {
                let declarations = self.sym(target_prop_symbol).declarations.clone();
                self.add_deprecated_suggestion(right, &declarations, &right_text);
            }
            self.check_property_not_used_before_declaration(prop, node, right);
            let self_ty = self.is_self_type_access(left, parent_symbol);

            self.mark_property_as_referenced(prop, Some(node), self_ty);
            self.symbol_node_links.get(node).resolved_symbol = Some(prop);
            self.check_property_accessibility(
                node,
                nodes[left].kind == ast::Kind::SuperKeyword,
                ast::is_write_access(node, &nodes),
                apparent_type,
                prop,
            );
            if self.is_assignment_to_readonly_entity(node, prop, assignment_kind) {
                self.error(
                    Some(right),
                    &tsc_diagnostics::Cannot_assign_to_0_because_it_is_a_read_only_property,
                    &[right_text.clone()],
                );
                return self.error_type;
            }
            prop_type = if self.is_this_property_access_in_constructor(node, prop) {
                Some(self.auto_type)
            } else if write_only || ast::is_write_only_access(node, &nodes) {
                Some(self.get_write_type_of_symbol(prop))
            } else {
                Some(self.get_type_of_symbol(prop))
            };
        }
        self.get_flow_type_of_access_expression(node, prop, prop_type, right, check_mode)
    }

    /// `(c *Checker) getFlowTypeOfAccessExpression` (checker.go:11628).
    pub(crate) fn get_flow_type_of_access_expression(
        &mut self,
        node: NodeId,
        prop: Option<SymbolId>,
        prop_type: Option<TypeId>,
        error_node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        // Only compute control flow type if this is a property access
        // expression that isn't an assignment target, and the referenced
        // property was declared as a variable, property, accessor, or optional
        // method.
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let assignment_kind = crate::utilities::get_assignment_target_kind(node, &nodes);
        let mut prop_type = prop_type.unwrap_or(self.error_type);
        if assignment_kind == crate::utilities::AssignmentKind::DEFINITE {
            return self.remove_missing_type(
                prop_type,
                prop.is_some_and(|p| self.sym(p).flags.intersects(ast::SymbolFlags::OPTIONAL)),
            );
        }
        if let Some(prop) = prop {
            let prop_flags = self.sym(prop).flags;
            if !prop_flags.intersects(
                ast::SymbolFlags::VARIABLE
                    | ast::SymbolFlags::PROPERTY
                    | ast::SymbolFlags::ACCESSOR,
            ) && !(prop_flags.intersects(ast::SymbolFlags::METHOD)
                && self
                    .types_handle()
                    .get(prop_type)
                    .flags
                    .intersects(TypeFlags::UNION))
            {
                return prop_type;
            }
        }
        if prop_type == self.auto_type {
            return self.get_flow_type_of_property(node, prop);
        }
        prop_type = self.get_narrowable_type_for_reference(prop_type, node, check_mode);
        // If strict null checks and strict property initialization checks are
        // enabled, if we have a this.xxx property access, if the property is an
        // instance property without an initializer, and if we are in a
        // constructor of the same class as the property declaration, assume
        // that the property is uninitialized at the top of the control flow.
        let mut assume_uninitialized = false;
        if self.strict_null_checks {
            if let Some(prop) = prop {
                let declaration = self.sym(prop).value_declaration;
                if let Some(declaration) = declaration {
                    let __program = self.program.clone().expect("program");
                    let decl_nodes = __program.nodes((declaration).file_index());
                    if self.strict_property_initialization
                        && ast::is_access_expression(&nodes[node])
                        && nodes[node]
                            .expression()
                            .is_some_and(|e| nodes[e].kind == ast::Kind::ThisKeyword)
                    {
                        if self.is_property_without_initializer(declaration)
                            && !ast::is_static(&decl_nodes[declaration])
                        {
                            let flow_container = self.get_control_flow_container(node);
                            if flow_container.is_some_and(|fc| {
                                ast::is_constructor_declaration(&nodes[fc])
                                    && nodes[fc].parent == decl_nodes[declaration].parent
                            }) && !decl_nodes[declaration]
                                .flags
                                .intersects(ast::NodeFlags::AMBIENT)
                            {
                                assume_uninitialized = true;
                            }
                        }
                    } else if ast::is_binary_expression(&decl_nodes[declaration])
                        && decl_nodes[declaration]
                            .as_binary_expression()
                            .left
                            .is_some_and(|l| ast::is_property_access_expression(&decl_nodes[l]))
                        && self.get_control_flow_container(node)
                            == self.get_control_flow_container(declaration)
                    {
                        assume_uninitialized = true;
                    }
                }
            }
        }
        let initial_type = self.add_optionality_ex(prop_type, false, assume_uninitialized);
        let flow_type =
            self.get_flow_type_of_reference_ex(node, prop_type, Some(initial_type), None, None);
        if assume_uninitialized
            && !self.contains_undefined_type(prop_type)
            && self.contains_undefined_type(flow_type)
        {
            let s = self.symbol_to_string(prop.unwrap());

            self.error(
                Some(error_node),
                &tsc_diagnostics::Property_0_is_used_before_being_assigned,
                &[s],
            );
            // Return the declared type to reduce follow-on errors
            return prop_type;
        }
        if assignment_kind != crate::utilities::AssignmentKind::NONE {
            return self.get_base_type_of_literal_type(flow_type);
        }
        flow_type
    }

    /// `(c *Checker) getControlFlowContainer` (checker.go:11675).
    pub(crate) fn get_control_flow_container(&mut self, node: NodeId) -> Option<NodeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        ast::find_ancestor(nodes[node].parent, &nodes, &mut |n, ns| {
            ast::is_function_like(Some(n.id), ns)
                && ast::get_immediately_invoked_function_expression(n.id, ns).is_none()
                || ast::is_module_block(n)
                || ast::is_source_file(n)
                || ast::is_property_declaration(n)
        })
    }

    /// `(c *Checker) getFlowTypeOfProperty` (checker.go:11681).
    pub(crate) fn get_flow_type_of_property(
        &mut self,
        reference: NodeId,
        prop: Option<SymbolId>,
    ) -> TypeId {
        let mut initial_type = self.undefined_type;
        if let Some(prop) = prop {
            let value_declaration = self.sym(prop).value_declaration;
            if let Some(vd) = value_declaration {
                let __program = self.program.clone().expect("program");
                let vd_nodes = __program.nodes((vd).file_index());
                if !self.is_auto_typed_property(prop)
                    || vd_nodes[vd]
                        .modifier_flags()
                        .intersects(ast::ModifierFlags::AMBIENT)
                {
                    if let Some(base_type) = self.get_type_of_property_in_base_class(prop) {
                        initial_type = base_type;
                    }
                }
            }
        }
        self.get_flow_type_of_reference_ex(
            reference,
            self.auto_type,
            Some(initial_type),
            None,
            None,
        )
    }

    /// `(c *Checker) getTypeOfPropertyInBaseClass` (checker.go:11692).
    /// Return the inherited type of the given property or undefined if
    /// property doesn't exist in a base class.
    pub(crate) fn get_type_of_property_in_base_class(
        &mut self,
        property: SymbolId,
    ) -> Option<TypeId> {
        let class_type = self.get_declaring_class(property);
        if let Some(class_type) = class_type {
            let base_class_types = self.get_base_types(class_type);
            if !base_class_types.is_empty() {
                let name = self.sym(property).name.clone();
                return self.get_type_of_property_of_type(base_class_types[0], &name);
            }
        }
        None
    }

    /// `(c *Checker) isMethodAccessForCall` (checker.go:11703).
    pub(crate) fn is_method_access_for_call(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut node = node;
        while nodes[node]
            .parent
            .is_some_and(|p| ast::is_parenthesized_expression(&nodes[p]))
        {
            node = nodes[node].parent.unwrap();
        }
        nodes[node].parent.is_some_and(|p| {
            ast::is_call_or_new_expression(&nodes[p]) && nodes[p].expression() == Some(node)
        })
    }

    /// `(c *Checker) lookupSymbolForPrivateIdentifierDeclaration` (checker.go:11711).
    /// Lookup the private identifier lexically.
    pub(crate) fn lookup_symbol_for_private_identifier_declaration(
        &mut self,
        prop_name: &str,
        location: NodeId,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((location).file_index());
        let mut containing_class =
            crate::utilities::get_containing_class_excluding_class_decorators(location, &nodes);
        while let Some(class) = containing_class {
            let symbol = nodes[class].symbol().expect("class symbol");
            let name =
                tsc_binder::binder::get_symbol_name_for_private_identifier(symbol, prop_name);
            if let Some(&prop) = self.sym(symbol).members.get(name.as_str()) {
                return Some(prop);
            }
            if let Some(&prop) = self.sym(symbol).exports.get(name.as_str()) {
                return Some(prop);
            }
            containing_class = ast::get_containing_class(class, &nodes);
        }
        None
    }

    /// `(c *Checker) getPrivateIdentifierPropertyOfType` (checker.go:11727).
    pub(crate) fn get_private_identifier_property_of_type(
        &mut self,
        left_type: TypeId,
        lexically_scoped_identifier: SymbolId,
    ) -> Option<SymbolId> {
        let name = self.sym(lexically_scoped_identifier).name.clone();
        self.get_property_of_type(left_type, &name)
    }

    /// `(c *Checker) checkPrivateIdentifierPropertyAccess` (checker.go:11731).
    pub(crate) fn check_private_identifier_property_access(
        &mut self,
        left_type: TypeId,
        right: NodeId,
        lexically_scoped_identifier: Option<SymbolId>,
    ) -> bool {
        // Either the identifier could not be looked up in the lexical scope OR
        // the lexically scoped identifier did not exist on the type.
        // Find a private identifier with the same description on the type.
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((right).file_index());
        let properties = self.get_properties_of_type(left_type);
        let mut property_on_type: Option<SymbolId> = None;
        let right_text = nodes[right].text(&nodes).into_owned();
        for symbol in properties {
            if let Some(decl) = self.sym(symbol).value_declaration {
                let __program = self.program.clone().expect("program");
                let decl_nodes = __program.nodes((decl).file_index());
                if decl_nodes[decl].name().is_some_and(|n| {
                    ast::is_private_identifier(&decl_nodes[n])
                        && decl_nodes[n].text(&decl_nodes) == right_text.as_str()
                }) {
                    property_on_type = Some(symbol);
                    break;
                }
            }
        }
        let diag_name = tsc_scanner::utilities::declaration_name_to_string(Some(right), &nodes);
        if let Some(property_on_type) = property_on_type {
            let type_value_decl = self
                .sym(property_on_type)
                .value_declaration
                .expect("propertyOnType.valueDeclaration");
            let __program = self.program.clone().expect("program");
            let tv_nodes = __program.nodes((type_value_decl).file_index());
            let type_class = ast::get_containing_class(type_value_decl, &tv_nodes);
            // We found a private identifier property with the same description.
            // Either:
            // - There is a lexically scoped private identifier AND it shadows
            //   the one we found on the type.
            // - It is an attempt to access the private identifier outside of
            //   the class.
            if let Some(lexically_scoped_identifier) = lexically_scoped_identifier {
                let lexical_value_decl =
                    { self.sym(lexically_scoped_identifier).value_declaration };
                if let Some(lexical_value_decl) = lexical_value_decl {
                    let __program = self.program.clone().expect("program");
                    let lv_nodes = __program.nodes((lexical_value_decl).file_index());
                    let lexical_class = ast::get_containing_class(lexical_value_decl, &lv_nodes);
                    let shadowed = ast::find_ancestor(lexical_class, &lv_nodes, &mut |n, _| {
                        Some(n.id) == type_class
                    })
                    .is_some();
                    if shadowed {
                        let __h7292_50 = self.type_to_string(left_type);

                        let diagnostic = self.error(
                            Some(right),
                            &tsc_diagnostics::The_property_0_cannot_be_accessed_on_type_1_within_this_class_because_it_is_shadowed_by_another_private_identifier_with_the_same_spelling,
                            &[
diag_name.clone(), __h7292_50],
                        );
                        if let Some(diagnostic) = diagnostic {
                            let related1 = create_diagnostic_for_node(
                                Some(lexical_value_decl),
                                &nodes,
                                &tsc_diagnostics::The_shadowing_declaration_of_0_is_defined_here,
                                &[diag_name.clone()],
                            );
                            let related2 = create_diagnostic_for_node(
                                Some(type_value_decl),
                                &nodes,
                                &tsc_diagnostics::The_declaration_of_0_that_you_probably_intended_to_use_is_defined_here,
                                &[diag_name.clone()],
                            );
                            ast::diagnostic::lock_diagnostic(&diagnostic)
                                .add_related_info(Some(related1))
                                .add_related_info(Some(related2));
                        }
                        return true;
                    }
                }
            }
            let class_symbol = type_class.and_then(|tc| tv_nodes[tc].symbol());
            let type_name = self.symbol_to_string(class_symbol.unwrap_or(SymbolId::NONE));
            self.error(
                Some(right),
                &tsc_diagnostics::Property_0_is_not_accessible_outside_class_1_because_it_has_a_private_identifier,
                &[diag_name, type_name],
            );
            return true;
        }
        false
    }

    /// `(c *Checker) reportNonexistentProperty` (checker.go:11767).
    pub(crate) fn report_nonexistent_property(
        &mut self,
        prop_node: NodeId,
        containing_type: TypeId,
        is_unchecked_js: bool,
    ) {
        let key = crate::checker_types::NonExistentPropertyKey {
            prop_node,
            containing_type,
            is_unchecked_js,
        };
        if self.non_existent_properties.has(&key) {
            return;
        }
        self.non_existent_properties.add(key);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((prop_node).file_index());
        {
            let links = self.node_links.get(prop_node);
            if links.flags.intersects(NodeCheckFlags::TYPE_CHECKED) {
                return; // error already made/in progress
            }
            links.flags |= NodeCheckFlags::TYPE_CHECKED;
        }
        if ast::is_js_doc_name_reference_context(prop_node, &nodes) {
            return;
        }
        let mut diagnostic: Option<DiagnosticRef> = None;
        let prop_text = nodes[prop_node].text(&nodes).into_owned();
        if !ast::is_private_identifier(&nodes[prop_node])
            && self
                .types_handle()
                .get_ref(containing_type)
                .flags
                .intersects(TypeFlags::UNION)
            && !self
                .types_handle()
                .get_ref(containing_type)
                .flags
                .intersects(TypeFlags::PRIMITIVE)
        {
            let subtypes = self.types.get_ref(containing_type).types().to_vec();
            for subtype in subtypes {
                if self.get_property_of_type(subtype, &prop_text).is_none()
                    && self
                        .get_applicable_index_info_for_name(subtype, &prop_text)
                        .is_none()
                {
                    let __h7380_29 = self.type_to_string(subtype);

                    diagnostic = Some(self.new_diagnostic_chain_for_node(
                        diagnostic,
                        Some(prop_node),
                        &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                        &[
                            tsc_scanner::utilities::declaration_name_to_string(
                                Some(prop_node),
                                &nodes,
                            ),
                            __h7380_29,
                        ],
                    ));
                    break;
                }
            }
        }
        if self.type_has_static_property(&prop_text, containing_type) {
            let prop_name =
                tsc_scanner::utilities::declaration_name_to_string(Some(prop_node), &nodes);
            let type_name = self.type_to_string(containing_type);
            diagnostic = Some(self.new_diagnostic_chain_for_node(
                diagnostic,
                Some(prop_node),
                &tsc_diagnostics::Property_0_does_not_exist_on_type_1_Did_you_mean_to_access_the_static_member_2_instead,
                &[
                    prop_name.clone(),
                    type_name.clone(),
                    format!("{type_name}.{prop_name}"),
                ],
            ));
        } else {
            let promised_type = self.get_promised_type_of_promise(containing_type);
            if promised_type.is_some_and(|pt| self.get_property_of_type(pt, &prop_text).is_some()) {
                let __h7410_25 = self.type_to_string(containing_type);

                diagnostic = Some(self.new_diagnostic_chain_for_node(
                    diagnostic,
                    Some(prop_node),
                    &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                    &[
                        tsc_scanner::utilities::declaration_name_to_string(Some(prop_node), &nodes),
                        __h7410_25,
                    ],
                ));
                let related = self.new_diagnostic_for_node(
                    Some(prop_node),
                    &tsc_diagnostics::Did_you_forget_to_use_await,
                    &[] as &[String],
                );
                if let Some(d) = &diagnostic {
                    ast::diagnostic::lock_diagnostic(d).add_related_info(Some(related));
                }
            } else {
                let missing_property =
                    tsc_scanner::utilities::declaration_name_to_string(Some(prop_node), &nodes);
                let container = self.type_to_string(containing_type);
                let lib_suggestion = self.get_suggested_lib_for_non_existent_property(
                    &missing_property,
                    containing_type,
                );
                if !lib_suggestion.is_empty() {
                    diagnostic = Some(self.new_diagnostic_chain_for_node(
                        diagnostic,
                        Some(prop_node),
                        &tsc_diagnostics::Property_0_does_not_exist_on_type_1_Do_you_need_to_change_your_target_library_Try_changing_the_lib_compiler_option_to_2_or_later,
                        &[missing_property.clone(), container.clone(), lib_suggestion],
                    ));
                } else {
                    let suggestion = self
                        .get_suggested_symbol_for_nonexistent_property(prop_node, containing_type);
                    if let Some(suggestion) = suggestion {
                        // The suggested symbol's value declaration can live
                        // in another file (e.g. a lib .d.ts) — `symbol_name`
                        // must read it through its own arena.
                        let decl_arena = match self.sym(suggestion).value_declaration {
                            Some(vd) => {
                                crate::printer_util::resolve_arena_for(&__program, &nodes, vd)
                            }
                            None => crate::printer_util::ArenaView::Working(&nodes),
                        };
                        let suggested_name =
                            ast::symbol_name(&self.sym(suggestion), &decl_arena).into_owned();
                        let message = tsc_core::core::if_else(
                            is_unchecked_js,
                            &tsc_diagnostics::Property_0_may_not_exist_on_type_1_Did_you_mean_2,
                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1_Did_you_mean_2,
                        );
                        diagnostic = Some(self.new_diagnostic_chain_for_node(
                            diagnostic,
                            Some(prop_node),
                            message,
                            &[
                                missing_property.clone(),
                                container.clone(),
                                suggested_name.clone(),
                            ],
                        ));
                        if let Some(vd) = self.sym(suggestion).value_declaration {
                            let related = self.new_diagnostic_for_node(
                                Some(vd),
                                &tsc_diagnostics::X_0_is_declared_here,
                                &[suggested_name],
                            );
                            if let Some(d) = &diagnostic {
                                ast::diagnostic::lock_diagnostic(d).add_related_info(Some(related));
                            }
                        }
                    } else {
                        diagnostic = self.elaborate_never_intersection(
                            diagnostic,
                            Some(prop_node),
                            containing_type,
                        );
                        let message = if self
                            .container_seems_to_be_empty_dom_element(containing_type)
                        {
                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1_Try_changing_the_lib_compiler_option_to_include_dom
                        } else {
                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1
                        };
                        diagnostic = Some(self.new_diagnostic_chain_for_node(
                            diagnostic,
                            Some(prop_node),
                            message,
                            &[missing_property, container],
                        ));
                    }
                }
            }
        }
        let diagnostic = diagnostic.expect("reportNonexistentProperty: diagnostic");
        let is_error = !is_unchecked_js
            || ast::diagnostic::lock_diagnostic(&diagnostic).code()
                != tsc_diagnostics::Property_0_may_not_exist_on_type_1_Did_you_mean_2.code();
        self.add_error_or_suggestion(is_error, &diagnostic);
    }

    /// `(c *Checker) getSuggestedLibForNonExistentProperty` (checker.go:11830).
    pub(crate) fn get_suggested_lib_for_non_existent_property(
        &mut self,
        missing_property: &str,
        containing_type: TypeId,
    ) -> String {
        let __arena_container = self.types.clone();
        let container = __arena_container
            .get_ref(self.get_apparent_type(containing_type))
            .symbol();
        if let Some(container) = container {
            let container_name = self.sym(container).name.clone();
            let feature_map = crate::utilities::get_feature_map();
            if let Some(type_features) = feature_map.get(&container_name) {
                for entry in type_features {
                    if entry.props.iter().any(|p| p == missing_property) {
                        return entry.lib.clone();
                    }
                }
            }
        }
        String::new()
    }

    /// `(c *Checker) getSuggestedSymbolForNonexistentProperty` (checker.go:11845).
    pub(crate) fn get_suggested_symbol_for_nonexistent_property(
        &mut self,
        name: NodeId,
        containing_type: TypeId,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((name).file_index());
        let props = self.get_properties_of_type(containing_type);
        let parent = nodes[name].parent.expect("name parent");
        let props = if ast::is_property_access_expression(&nodes[parent]) {
            props
                .into_iter()
                .filter(|&prop| {
                    self.is_valid_property_access_for_completions(parent, containing_type, prop)
                })
                .collect::<Vec<_>>()
        } else {
            props
        };
        self.get_spelling_suggestion_for_name(
            &nodes[name].text(&nodes),
            props,
            ast::SymbolFlags::VALUE,
        )
    }

    /// `(c *Checker) isValidPropertyAccessForCompletions` (checker.go:11864).
    /// Checks if an existing property access is valid for completions purposes.
    pub fn is_valid_property_access_for_completions(
        &mut self,
        node: NodeId,
        t: TypeId,
        property: SymbolId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_super = ast::is_property_access_expression(&nodes[node])
            && nodes[node]
                .expression()
                .is_some_and(|e| nodes[e].kind == ast::Kind::SuperKeyword);
        // Previously we validated the 'this' type of methods but this
        // adversely affected performance. See #31377 for more context.
        self.is_property_accessible(node, is_super, false /* isWrite */, t, property)
    }

    /// `(c *Checker) isPropertyAccessible` (checker.go:11877).
    /// Checks if a property can be accessed in a location.
    pub fn is_property_accessible(
        &mut self,
        node: NodeId,
        is_super: bool,
        is_write: bool,
        containing_type: TypeId,
        property: SymbolId,
    ) -> bool {
        // Short-circuiting for improved performance.
        if crate::utilities::is_type_any(&self.types, containing_type) {
            return true;
        }
        // A #private property access in an optional chain is an error dealt
        // with by the parser. The checker does not check for it, so we need to
        // do our own check here.
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(value_declaration) = self.sym(property).value_declaration {
            let __program = self.program.clone().expect("program");
            let vd_nodes = __program.nodes((value_declaration).file_index());
            if ast::is_private_identifier_class_element_declaration(
                &vd_nodes[value_declaration],
                &vd_nodes,
            ) {
                let decl_class = ast::get_containing_class(value_declaration, &vd_nodes);
                return !ast::is_optional_chain(&nodes[node])
                    && ast::is_node_descendant_of(Some(node), decl_class, &nodes);
            }
        }
        self.check_property_accessibility_at_location(
            node,
            is_super,
            is_write,
            containing_type,
            property,
            None,
        )
    }

    /// `(c *Checker) containerSeemsToBeEmptyDomElement` (checker.go:11891).
    pub(crate) fn container_seems_to_be_empty_dom_element(
        &mut self,
        containing_type: TypeId,
    ) -> bool {
        !self
            .compiler_options
            .lib
            .as_ref()
            .is_some_and(|libs| libs.iter().any(|l| l == "lib.dom.d.ts"))
            && crate::checker_d::every_contained_type(&self.types, containing_type, |t: TypeId| {
                has_common_dom_type_name(self, t)
            })
            && self.is_empty_object_type(containing_type)
    }

    // __APPEND__
}

/// `hasCommonDomTypeName` (checker.go:11895).
pub(crate) fn has_common_dom_type_name(c: &Checker, t: TypeId) -> bool {
    let Some(symbol) = c.types.get_ref(t).symbol() else {
        return false;
    };
    let name = &c.sym(symbol).name;
    name == "EventTarget"
        || name == "Node"
        || name == "Element"
        || (name.starts_with("HTML") && name.ends_with("Element"))
}

impl Checker {
    /// `NewDiagnosticChainForNode` (utilities.go:31) — file-private helper
    /// pending `crate::utilities`; Go body reproduced verbatim.
    fn new_diagnostic_chain_for_node(
        &mut self,
        chain: Option<DiagnosticRef>,
        node: Option<NodeId>,
        message: &'static tsc_diagnostics::Message,
        args: &[String],
    ) -> DiagnosticRef {
        if let Some(chain) = chain {
            return ast::diagnostic::new_diagnostic_chain(Some(&chain), message, args);
        }
        self.new_diagnostic_for_node(node, message, args)
    }

    /// `(c *Checker) checkAndReportErrorForExtendingInterface` (checker.go:11903).
    pub(crate) fn check_and_report_error_for_extending_interface(
        &mut self,
        error_location: Option<NodeId>,
    ) -> bool {
        let Some(error_location) = error_location else {
            return false;
        };
        let expression = self.get_entity_name_for_extending_interface(error_location);
        if let Some(expression) = expression {
            if self
                .resolve_entity_name(
                    Some(expression),
                    ast::SymbolFlags::INTERFACE,
                    true, /* ignoreErrors */
                    false,
                    None,
                )
                .is_some()
            {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((expression).file_index());
                let text = tsc_scanner::utilities::get_text_of_node(expression, &nodes);
                self.error(
                    Some(error_location),
                    &tsc_diagnostics::Cannot_extend_an_interface_0_Did_you_mean_implements,
                    &[text],
                );
                return true;
            }
        }
        false
    }

    /// `(c *Checker) getEntityNameForExtendingInterface` (checker.go:11915).
    /// Climbs up parents to a heritage clause element and returns its entity
    /// name.
    pub(crate) fn get_entity_name_for_extending_interface(
        &mut self,
        node: NodeId,
    ) -> Option<NodeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::Identifier
            | ast::Kind::QualifiedName
            | ast::Kind::PropertyAccessExpression => {
                if nodes[node].parent.is_some() {
                    return self
                        .get_entity_name_for_extending_interface(nodes[node].parent.unwrap());
                }
            }
            ast::Kind::TypeReference => {
                return nodes[node].as_type_reference_node().type_name;
            }
            ast::Kind::ExpressionWithTypeArguments => {
                let expression = nodes[node].expression();
                if expression.is_some_and(|e| ast::is_entity_name_expression(&nodes[e], &nodes)) {
                    return expression;
                }
            }
            _ => {}
        }
        None
    }

    /// `(c *Checker) isUncalledFunctionReference` (checker.go:11931).
    pub(crate) fn is_uncalled_function_reference(
        &mut self,
        node: NodeId,
        symbol: SymbolId,
    ) -> bool {
        if self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::FUNCTION | ast::SymbolFlags::METHOD)
        {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let mut parent = ast::find_ancestor(nodes[node].parent, &nodes, &mut |n, _| {
                !ast::is_access_expression(n)
            });
            if parent.is_none() {
                parent = nodes[node].parent;
            }
            let Some(parent) = parent else {
                return true;
            };
            if ast::is_call_like_expression(&nodes[parent], &nodes) {
                return ast::is_call_or_new_expression(&nodes[parent])
                    && ast::is_identifier(&nodes[node])
                    && self.has_matching_argument(&nodes, parent, node);
            }
            let declarations = self.sym(symbol).declarations.clone();
            return tsc_core::core::every(&declarations, |d| {
                !ast::is_function_like(Some(*d), &self.program_nodes(*d))
                    || self.is_deprecated_declaration(*d)
            });
        }
        true
    }

    /// `(c *Checker) checkPropertyNotUsedBeforeDeclaration` (checker.go:11947).
    pub(crate) fn check_property_not_used_before_declaration(
        &mut self,
        prop: SymbolId,
        node: NodeId,
        right: NodeId,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let value_declaration = self.sym(prop).value_declaration;
        let Some(value_declaration) = value_declaration else {
            return;
        };
        let __program = self.program.clone().expect("program");
        let vd_nodes = __program.nodes((value_declaration).file_index());
        if ast::get_source_file_of_node(Some(node), &nodes)
            .is_some_and(|sf| nodes[sf].as_source_file().is_declaration_file)
        {
            return;
        }
        let mut diagnostic: Option<DiagnosticRef> = None;
        let declaration_name = nodes[right].text(&nodes).into_owned();
        if self.is_in_property_initializer_or_class_static_block(
            node, false, /* ignoreArrowFunctions */
        ) && !self.is_optional_property_declaration(value_declaration)
            && !(ast::is_access_expression(&nodes[node])
                && nodes[node]
                    .expression()
                    .is_some_and(|e| ast::is_access_expression(&nodes[e])))
            && !self.is_block_scoped_name_declared_before_use(value_declaration, right)
            && !(ast::is_method_declaration(&vd_nodes[value_declaration])
                && self
                    .get_combined_modifier_flags_cached(value_declaration)
                    .intersects(ast::ModifierFlags::STATIC))
            && (self.compiler_options.get_use_define_for_class_fields()
                || !self.is_property_declared_in_ancestor_class(prop))
        {
            diagnostic = self.error(
                Some(right),
                &tsc_diagnostics::Property_0_is_used_before_its_initialization,
                &[declaration_name.clone()],
            );
        } else if ast::is_class_declaration(&vd_nodes[value_declaration])
            && !nodes[node]
                .parent
                .is_some_and(|p| ast::is_type_reference_node(&nodes[p]))
            && !vd_nodes[value_declaration]
                .flags
                .intersects(ast::NodeFlags::AMBIENT)
            && !self.is_block_scoped_name_declared_before_use(value_declaration, right)
        {
            diagnostic = self.error(
                Some(right),
                &tsc_diagnostics::Class_0_used_before_its_declaration,
                &[declaration_name.clone()],
            );
        }
        if let Some(diagnostic) = diagnostic {
            let related = self.new_diagnostic_for_node(
                Some(value_declaration),
                &tsc_diagnostics::X_0_is_declared_here,
                &[declaration_name],
            );
            ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(related));
        }
    }

    /// `(c *Checker) isOptionalPropertyDeclaration` (checker.go:11969).
    pub(crate) fn is_optional_property_declaration(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        ast::is_property_declaration(&nodes[node])
            && !ast::has_accessor_modifier(&nodes[node])
            && ast::is_question_token(nodes[node].postfix_token(), &nodes)
    }

    /// `(c *Checker) isPropertyDeclaredInAncestorClass` (checker.go:11973).
    pub(crate) fn is_property_declared_in_ancestor_class(&mut self, prop: SymbolId) -> bool {
        let parent = self.sym(prop).parent;
        if let Some(parent) = parent {
            if self.sym(parent).flags.intersects(ast::SymbolFlags::CLASS) {
                let __h7826_54 = self.get_declared_type_of_symbol(parent);

                let base_types = self.get_base_types(__h7826_54);
                if !base_types.is_empty() {
                    let name = self.sym(prop).name.clone();
                    let super_property = self.get_property_of_type(base_types[0], &name);
                    return super_property
                        .is_some_and(|sp| self.sym(sp).value_declaration.is_some());
                }
            }
        }
        false
    }

    /// `(c *Checker) checkPropertyAccessibility` (checker.go:11991).
    /// Check whether the requested property access is valid. Returns true if
    /// node is a valid property access, and false otherwise.
    pub(crate) fn check_property_accessibility(
        &mut self,
        node: NodeId,
        is_super: bool,
        writing: bool,
        t: TypeId,
        prop: SymbolId,
    ) -> bool {
        self.check_property_accessibility_ex(
            node, is_super, writing, t, prop, true, /* reportError */
        )
    }

    /// `(c *Checker) checkPropertyAccessibilityEx` (checker.go:11995).
    pub(crate) fn check_property_accessibility_ex(
        &mut self,
        node: NodeId,
        is_super: bool,
        writing: bool,
        t: TypeId,
        prop: SymbolId,
        report_error: bool,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut error_node: Option<NodeId> = None;
        if report_error {
            error_node = match nodes[node].kind {
                ast::Kind::PropertyAccessExpression => {
                    nodes[node].as_property_access_expression().name
                }
                ast::Kind::QualifiedName => nodes[node].as_qualified_name().right,
                ast::Kind::ImportType => Some(node),
                ast::Kind::BindingElement => {
                    crate::utilities::get_binding_element_property_name(&nodes[node])
                }
                _ => nodes[node].name(),
            };
        }
        self.check_property_accessibility_at_location(node, is_super, writing, t, prop, error_node)
    }

    /// `(c *Checker) checkPropertyAccessibilityAtLocation` (checker.go:12024).
    /// Check whether the requested property can be accessed at the requested
    /// location. Returns true if node is a valid property access, and false
    /// otherwise.
    pub(crate) fn check_property_accessibility_at_location(
        &mut self,
        location: NodeId,
        is_super: bool,
        writing: bool,
        containing_type: TypeId,
        prop: SymbolId,
        error_node: Option<NodeId>,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((location).file_index());
        let flags =
            crate::utilities::get_declaration_modifier_flags_from_symbol_ex(self, prop, writing);
        let mut containing_type = containing_type;
        if is_super {
            // TS 1.0 spec (April 2014): 4.8.2 — a super property access must
            // specify a public instance member function of the base class.
            if flags.intersects(ast::ModifierFlags::ABSTRACT) {
                // A method cannot be accessed in a super property access if the
                // method is abstract. This error could mask a private property
                // access error. But, a member cannot simultaneously be private
                // and abstract, so this will trigger an additional error
                // elsewhere.
                if let Some(error_node) = error_node {
                    let declaring_class = self.get_declaring_class(prop);
                    let __h7914_29 = self.symbol_to_string(prop);
                    let decl_t = declaring_class.unwrap_or(self.error_type);
                    let __h7915_29 = self.type_to_string(decl_t);

                    self.error(
                        Some(error_node),
                        &tsc_diagnostics::Abstract_method_0_in_class_1_cannot_be_accessed_via_super_expression,
                        &[__h7914_29, __h7915_29],
                    );
                }
                return false;
            }
            // A class field cannot be accessed via super.* from a derived
            // class. This is true for both [[Set]] (old) and [[Define]] (ES
            // spec) semantics.
            if !flags.intersects(ast::ModifierFlags::STATIC)
                && tsc_core::core::some(&self.sym(prop).declarations, |d| {
                    crate::utilities::is_class_instance_property(*d, &self.program_nodes(*d))
                })
            {
                if let Some(error_node) = error_node {
                    let __h7935_27 = self.symbol_to_string(prop);

                    self.error(
                        Some(error_node),
                        &tsc_diagnostics::Class_field_0_defined_by_the_parent_class_is_not_accessible_in_the_child_class_via_super,
                        &[__h7935_27],
                    );
                }
                return false;
            }
        }
        // Referencing abstract properties within their own constructors is not
        // allowed
        if flags.intersects(ast::ModifierFlags::ABSTRACT)
            && self.symbol_has_non_method_declaration(prop)
            && (crate::utilities::is_this_property(location, &nodes)
                || crate::utilities::is_this_initialized_object_binding_expression(
                    location, &nodes,
                )
                || (nodes[location]
                    .parent
                    .is_some_and(|p| ast::is_object_binding_pattern(&nodes[p]))
                    && nodes[location]
                        .parent
                        .and_then(|p| nodes[p].parent)
                        .is_some_and(|pp| {
                            crate::utilities::is_this_initialized_declaration(pp, &nodes)
                        })))
        {
            let parent_symbol = self.get_parent_of_symbol(prop);
            if parent_symbol
                .is_some_and(|ps| self.sym(ps).flags.intersects(ast::SymbolFlags::CLASS))
                && self.is_node_used_during_class_initialization(location)
            {
                if let Some(error_node) = error_node {
                    let a = self.symbol_to_string(prop);
                    let b = self.symbol_to_string(parent_symbol.unwrap());

                    self.error(
                        Some(error_node),
                        &tsc_diagnostics::Abstract_property_0_in_class_1_cannot_be_accessed_in_the_constructor,
                        &[
                            a,
                            b,
                        ],
                    );
                }
                return false;
            }
        }
        // Public properties are otherwise accessible.
        if !flags.intersects(ast::ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER) {
            return true;
        }
        // Property is known to be private or protected at this point.
        // Private property is accessible if the property is within the
        // declaring class.
        if flags.intersects(ast::ModifierFlags::PRIVATE) {
            let mut declaring_class_declaration: Option<NodeId> = None;
            if let Some(parent) = self.get_parent_of_symbol(prop) {
                {
                    let __program = self.program.clone().expect("program");
                    declaring_class_declaration =
                        ast::get_class_like_declaration_of_symbol_with(
                            &self.sym(parent),
                            |d| ast::is_class_like(Some(d), &__program.nodes(d.file_index())),
                        );
                }
            }
            if declaring_class_declaration.is_none()
                || !self.is_node_within_class(location, declaring_class_declaration)
            {
                if let Some(error_node) = error_node {
                    let class = tsc_core::core::or_else(
                        self.get_declaring_class(prop),
                        Some(containing_type),
                    );
                    let a = self.symbol_to_string(prop);
                    let b = self.type_to_string(class.unwrap_or(self.error_type));

                    self.error(
                        Some(error_node),
                        &tsc_diagnostics::Property_0_is_private_and_only_accessible_within_class_1,
                        &[a, b],
                    );
                }
                return false;
            }
            return true;
        }
        // Property is known to be protected at this point. All protected
        // properties of a supertype are accessible in a super access.
        if is_super {
            return true;
        }
        // Find the first enclosing class that has the declaring classes of the
        // protected constituents of the property as base classes.
        let mut enclosing_class: Option<TypeId> = None;
        let mut container = ast::get_containing_class(location, &nodes);
        while let Some(c) = container {
            let class_symbol = self.get_symbol_of_declaration(c);
            let class = self.get_declared_type_of_symbol(class_symbol.unwrap_or(SymbolId::NONE));
            if self.is_class_derived_from_declaring_classes(class, prop, writing) {
                enclosing_class = Some(class);
                break;
            }
            container = ast::get_containing_class(c, &nodes);
        }
        // A protected property is accessible if the property is within the
        // declaring class or classes derived from it.
        if enclosing_class.is_none() {
            // allow PropertyAccessibility if context is in function with this
            // parameter; static member access is disallowed
            let class = self.get_enclosing_class_from_this_parameter(location);
            if class.is_some_and(|c| self.is_class_derived_from_declaring_classes(c, prop, writing))
            {
                enclosing_class = class;
            }
            if flags.intersects(ast::ModifierFlags::STATIC) || enclosing_class.is_none() {
                if let Some(error_node) = error_node {
                    let class = tsc_core::core::or_else(
                        self.get_declaring_class(prop),
                        Some(containing_type),
                    );
                    let a = self.symbol_to_string(prop);
                    let b = self.type_to_string(class.unwrap_or(self.error_type));

                    self.error(
                        Some(error_node),
                        &tsc_diagnostics::Property_0_is_protected_and_only_accessible_within_class_1_and_its_subclasses,
                        &[
                            a,
                            b,
                        ],
                    );
                }
                return false;
            }
        }
        // No further restrictions for static properties.
        if flags.intersects(ast::ModifierFlags::STATIC) {
            return true;
        }
        if self
            .types_handle()
            .get_ref(containing_type)
            .flags
            .intersects(TypeFlags::TYPE_PARAMETER)
        {
            // get the original type -- represented as the type constraint of
            // the 'this' type
            if self
                .types_handle()
                .get_ref(containing_type)
                .as_type_parameter()
                .is_this_type
            {
                containing_type = self
                    .get_constraint_of_type_parameter(containing_type)
                    .unwrap_or(containing_type);
            } else {
                containing_type = self
                    .get_base_constraint_of_type(containing_type)
                    .unwrap_or(self.unknown_type);
            }
        }
        if !self.has_base_type(containing_type, enclosing_class) {
            if error_node.is_some() {
                let a = self.symbol_to_string(prop);
                let b = self.type_to_string(enclosing_class.unwrap_or(self.error_type));
                let ct = self.type_to_string(containing_type);

                self.error(
                    error_node,
                    &tsc_diagnostics::Property_0_is_protected_and_only_accessible_through_an_instance_of_class_1_This_is_an_instance_of_class_2,
                    &[
                        a,
                        b,
                        ct,
                    ],
                );
            }
            return false;
        }
        true
    }

    /// `(c *Checker) symbolHasNonMethodDeclaration` (checker.go:12139).
    pub(crate) fn symbol_has_non_method_declaration(&mut self, symbol: SymbolId) -> bool {
        self.for_each_property(symbol, &mut |c: &mut Checker, prop: SymbolId| {
            !c.sym(prop).flags.intersects(ast::SymbolFlags::METHOD)
        })
    }

    /// `(c *Checker) forEachProperty` (checker.go:12145).
    /// Invoke the callback for each underlying property symbol of the given
    /// symbol and return the first value that isn't undefined.
    // PORT: Go's function-value parameter recurses through `&mut callback`;
    // `impl FnMut` would monomorphize a new `for_each_property::<&mut F>` per
    // level (infinite type recursion), so the callback is a trait object.
    pub(crate) fn for_each_property(
        &mut self,
        prop: SymbolId,
        callback: &mut dyn FnMut(&mut Checker, SymbolId) -> bool,
    ) -> bool {
        if !self
            .sym(prop)
            .check_flags
            .intersects(ast::checkflags::CheckFlags::SYNTHETIC)
        {
            return callback(self, prop);
        }
        let containing_type = self
            .value_symbol_links
            .get(prop)
            .containing_type
            .expect("ValueSymbolLinks.containingType");
        let types = self.types.get_ref(containing_type).types().to_vec();
        for t in types {
            let name = self.sym(prop).name.clone();
            if let Some(p) = self.get_property_of_type(t, &name) {
                if self.for_each_property(p, callback) {
                    return true;
                }
            }
        }
        false
    }

    /// `(c *Checker) getDeclaringClass` (checker.go:12159).
    /// Return the declaring class type of a property or undefined if property
    /// not declared in class.
    pub(crate) fn get_declaring_class(&mut self, prop: SymbolId) -> Option<TypeId> {
        let parent_sym = self.sym(prop).parent;
        if let Some(parent) = parent_sym {
            let is_class = self.sym(parent).flags.intersects(ast::SymbolFlags::CLASS);
            if is_class {
                let parent = self.get_parent_of_symbol(prop);
                return Some(self.get_declared_type_of_symbol(parent.unwrap_or(SymbolId::NONE)));
            }
        }
        None
    }

    /// `(c *Checker) isValidOverrideOf` (checker.go:12167).
    /// Return true if source property is a valid override of protected parts
    /// of target property.
    pub(crate) fn is_valid_override_of(
        &mut self,
        source_prop: SymbolId,
        target_prop: SymbolId,
    ) -> bool {
        !self.for_each_property(target_prop, &mut |c: &mut Checker, tp: SymbolId| {
            let modifier_flags =
                crate::utilities::get_declaration_modifier_flags_from_symbol(c, tp);
            if modifier_flags.intersects(ast::ModifierFlags::PROTECTED) {
                let declaring = c.get_declaring_class(tp);
                return !c.is_property_in_class_derived_from(source_prop, declaring);
            }
            false
        })
    }

    /// `(c *Checker) isPropertyInClassDerivedFrom` (checker.go:12178).
    /// Return true if some underlying source property is declared in a class
    /// that derives from the given base class.
    pub(crate) fn is_property_in_class_derived_from(
        &mut self,
        prop: SymbolId,
        base_class: Option<TypeId>,
    ) -> bool {
        self.for_each_property(prop, &mut |c: &mut Checker, sp: SymbolId| {
            if let Some(source_class) = c.get_declaring_class(sp) {
                return c.has_base_type(source_class, base_class);
            }
            false
        })
    }

    /// `(c *Checker) isNodeUsedDuringClassInitialization` (checker.go:12188).
    pub(crate) fn is_node_used_during_class_initialization(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        ast::find_ancestor_or_quit(Some(node), &nodes, &mut |element, ns| {
            if ast::is_constructor_declaration(element) && ast::node_is_present(element.body(), ns)
                || ast::is_property_declaration(element)
            {
                return ast::FindAncestorResult::True;
            } else if ast::is_class_like(Some(element.id), ns)
                || ast::is_function_like_declaration(Some(element.id), ns)
            {
                return ast::FindAncestorResult::Quit;
            }
            ast::FindAncestorResult::False
        })
        .is_some()
    }

    /// `(c *Checker) isNodeWithinClass` (checker.go:12199).
    pub(crate) fn is_node_within_class(
        &mut self,
        node: NodeId,
        class_declaration: Option<NodeId>,
    ) -> bool {
        self.for_each_enclosing_class(node, |_: &mut Checker, n: NodeId| {
            Some(n) == class_declaration
        })
    }

    /// `(c *Checker) forEachEnclosingClass` (checker.go:12203).
    pub(crate) fn for_each_enclosing_class(
        &mut self,
        node: NodeId,
        mut callback: impl FnMut(&mut Checker, NodeId) -> bool,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut containing_class = ast::get_containing_class(node, &nodes);
        while let Some(class) = containing_class {
            if callback(self, class) {
                return true;
            }
            containing_class = ast::get_containing_class(class, &nodes);
        }
        false
    }

    /// `(c *Checker) isClassDerivedFromDeclaringClasses` (checker.go:12217).
    /// Return true if the given class derives from each of the declaring
    /// classes of the protected constituents of the given property.
    pub(crate) fn is_class_derived_from_declaring_classes(
        &mut self,
        check_class: TypeId,
        prop: SymbolId,
        writing: bool,
    ) -> bool {
        !self.for_each_property(prop, &mut |c: &mut Checker, p: SymbolId| {
            let modifier_flags =
                crate::utilities::get_declaration_modifier_flags_from_symbol_ex(c, p, writing);
            if modifier_flags.intersects(ast::ModifierFlags::PROTECTED) {
                let declaring = c.get_declaring_class(p);
                return !c.has_base_type(check_class, declaring);
            }
            false
        })
    }

    /// `(c *Checker) getEnclosingClassFromThisParameter` (checker.go:12226).
    pub(crate) fn get_enclosing_class_from_this_parameter(
        &mut self,
        node: NodeId,
    ) -> Option<TypeId> {
        // 'this' type for a node comes from, in priority order...
        // 1. The type of a syntactic 'this' parameter in the enclosing
        //    function scope
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let this_parameter = get_this_parameter_from_node_context(node, &nodes);
        let mut this_type: Option<TypeId> = None;
        if let Some(this_parameter) = this_parameter {
            if let Some(tp) = nodes[this_parameter].type_() {
                this_type = Some(self.get_type_from_type_node(tp));
            }
        }
        if let Some(tt) = this_type {
            // 2. The constraint of a type parameter used for an explicit 'this'
            //    parameter
            if self
                .types_handle()
                .get_ref(tt)
                .flags
                .intersects(TypeFlags::TYPE_PARAMETER)
            {
                this_type = self.get_constraint_of_type_parameter(tt);
            }
        } else {
            // 3. The 'this' parameter of a contextual type
            let this_container = ast::get_this_container(
                node, &nodes, false, /* includeArrowFunctions */
                false, /* includeClassComputedPropertyName */
            );
            if ast::is_function_like(Some(this_container), &nodes) {
                this_type = self.get_contextual_this_parameter_type(this_container);
            }
        }
        if let Some(this_type) = this_type {
            if self
                .types_handle()
                .get_ref(this_type)
                .object_flags
                .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE)
            {
                return Some(crate::checker_c::get_target_type(&self.types, this_type));
            }
        }
        None
    }
}

/// `getThisParameterFromNodeContext` (checker.go:12252).
pub(crate) fn get_this_parameter_from_node_context(
    node: NodeId,
    nodes: &[ast::Node],
) -> Option<NodeId> {
    let this_container = ast::get_this_container(
        node, nodes, false, /* includeArrowFunctions */
        false, /* includeClassComputedPropertyName */
    );
    if ast::is_function_like(Some(this_container), nodes) {
        return ast::get_this_parameter(&nodes[this_container], nodes);
    }
    None
}

impl Checker {
    /// `(c *Checker) getContextualThisParameterType` (checker.go:12260).
    pub(crate) fn get_contextual_this_parameter_type(&mut self, fn_: NodeId) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((fn_).file_index());
        if ast::is_arrow_function(&nodes[fn_]) {
            return None;
        }
        if self.is_context_sensitive_function_or_object_literal_method(fn_) {
            let contextual_signature = self.get_contextual_signature(fn_);
            if let Some(contextual_signature) = contextual_signature {
                let this_parameter = self
                    .signature_arena
                    .get(contextual_signature)
                    .this_parameter;
                if let Some(this_parameter) = this_parameter {
                    return Some(self.get_type_of_symbol(this_parameter));
                }
            }
        }
        let in_js = ast::is_in_js_file(Some(fn_), &nodes);
        if self.no_implicit_this || in_js {
            let containing_literal = crate::utilities::get_containing_object_literal(fn_, &nodes);
            if let Some(containing_literal) = containing_literal {
                // We have an object literal method. Check if the containing
                // object literal has a contextual type that includes a
                // ThisType<T>. If so, T is the contextual type for 'this'. We
                // continue looking in any directly enclosing object literals.
                let contextual_type = self
                    .get_apparent_type_of_contextual_type(containing_literal, ContextFlags::NONE);
                let mut this_type = self.get_this_type_of_object_literal_from_contextual_type(
                    containing_literal,
                    contextual_type,
                );
                if let Some(tt) = this_type {
                    let context = self.get_inference_context(containing_literal);
                    let mapper = context.and_then(|n| self.get_mapper_from_context(n));
                    return Some(self.instantiate_type(tt, mapper));
                }
                // There was no contextual ThisType<T> for the containing object
                // literal, so the contextual type for 'this' is the non-null
                // form of the contextual type for the containing object literal
                // or the type of the object literal itself.
                if let Some(contextual_type) = contextual_type {
                    this_type = Some(self.get_non_nullable_type(contextual_type));
                } else {
                    this_type = Some(self.check_expression_cached(containing_literal));
                }
                return Some(self.get_widened_type(this_type.unwrap()));
            }
            // In an assignment of the form 'obj.xxx = function(...)' or
            // 'obj[xxx] = function(...)', the contextual type for 'this' is
            // 'obj'.
            let parent = ast::walk_up_parenthesized_expressions(
                nodes[fn_].parent.expect("fn parent"),
                &nodes,
            )
            .expect("walked-up parent");
            if ast::is_assignment_expression(&nodes[parent], &nodes, false) {
                let target = nodes[parent].as_binary_expression().left;
                if let Some(target) = target {
                    if ast::is_access_expression(&nodes[target]) {
                        let expression = nodes[target].expression().expect("access expression");
                        // Don't contextually type `this` as `exports` in
                        // `exports.Point = function(x, y) { this.x = x; this.y = y; }`
                        if in_js && ast::is_identifier(&nodes[expression]) {
                            let source_file = ast::get_source_file_of_node(Some(parent), &nodes);
                            if source_file.is_some_and(|sf| {
                                nodes[sf]
                                    .as_source_file()
                                    .common_js_module_indicator
                                    .is_some()
                            }) && {
                                let rs = self.get_resolved_symbol(expression);
                                self.sym(rs)
                                    .flags
                                    .intersects(ast::SymbolFlags::MODULE_EXPORTS)
                            } {
                                return None;
                            }
                        }
                        let expr_ty = self.check_expression_cached(expression);
                        return Some(self.get_widened_type(expr_ty));
                    }
                }
            }
        }
        None
    }

    /// `(c *Checker) checkThisExpression` (checker.go:12316).
    pub(crate) fn check_this_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Stop at the first arrow function so that we can
        // tell whether 'this' needs to be captured.
        let mut container = ast::get_this_container(
            node, &nodes, true, /* includeArrowFunctions */
            true, /* includeClassComputedPropertyName */
        );
        let mut captured_by_arrow_function = false;
        let mut this_in_computed_property_name = false;
        if ast::is_constructor_declaration(&nodes[container]) {
            self.check_this_before_super(
                node,
                container,
                &tsc_diagnostics::X_super_must_be_called_before_accessing_this_in_the_constructor_of_a_derived_class,
            );
        }
        loop {
            // Now skip arrow functions to get the "real" owner of 'this'.
            if ast::is_arrow_function(&nodes[container]) {
                container = ast::get_this_container(
                    container,
                    &nodes,
                    false, /* includeArrowFunctions */
                    !this_in_computed_property_name,
                );
                captured_by_arrow_function = true;
            }
            if ast::is_computed_property_name(&nodes[container]) {
                container = ast::get_this_container(
                    container,
                    &nodes,
                    !captured_by_arrow_function,
                    false, /* includeClassComputedPropertyName */
                );
                this_in_computed_property_name = true;
                continue;
            }
            break;
        }
        self.check_this_in_static_class_field_initializer_in_decorated_class(node, container);
        if this_in_computed_property_name {
            self.error(
                Some(node),
                &tsc_diagnostics::X_this_cannot_be_referenced_in_a_computed_property_name,
                &[],
            );
        } else {
            match nodes[container].kind {
                ast::Kind::ModuleDeclaration => {
                    // do not return here so in case if lexical this is captured
                    // - it will be reflected in flags on NodeLinks
                    self.error(
                        Some(node),
                        &tsc_diagnostics::X_this_cannot_be_referenced_in_a_module_or_namespace_body,
                        &[],
                    );
                }
                ast::Kind::EnumDeclaration => {
                    // do not return here so in case if lexical this is captured
                    // - it will be reflected in flags on NodeLinks
                    self.error(
                        Some(node),
                        &tsc_diagnostics::X_this_cannot_be_referenced_in_current_location,
                        &[],
                    );
                }
                _ => {}
            }
        }
        let t =
            self.try_get_this_type_at_ex(node, true /* includeGlobalThis */, Some(container));
        if self.no_implicit_this {
            let global_this_type = self.get_type_of_symbol(self.global_this_symbol);
            if t == Some(global_this_type) && captured_by_arrow_function {
                self.error(
                    Some(node),
                    &tsc_diagnostics::The_containing_arrow_function_captures_the_global_value_of_this,
                    &[],
                );
            } else if t.is_none() {
                // With noImplicitThis, functions may not reference 'this' if it
                // has type 'any'
                let diag = self.error(
                    Some(node),
                    &tsc_diagnostics::X_this_implicitly_has_type_any_because_it_does_not_have_a_type_annotation,
                    &[],
                );
                if !ast::is_source_file(&nodes[container]) {
                    let outside_this = self.try_get_this_type_at(container);
                    if outside_this.is_some() && outside_this != Some(global_this_type) {
                        if let Some(diag) = diag {
                            let related = create_diagnostic_for_node(
                                Some(container),
                                &nodes,
                                &tsc_diagnostics::An_outer_value_of_this_is_shadowed_by_this_container,
                                &[],
                            );
                            ast::diagnostic::lock_diagnostic(&diag).add_related_info(Some(related));
                        }
                    }
                }
            }
        }
        t.unwrap_or(self.any_type)
    }

    /// `(c *Checker) tryGetThisTypeAt` (checker.go:12373).
    pub(crate) fn try_get_this_type_at(&mut self, node: NodeId) -> Option<TypeId> {
        self.try_get_this_type_at_ex(
            node, true, /* includeGlobalThis */
            None, /* container */
        )
    }

    /// `(c *Checker) TryGetThisTypeAtEx` (checker.go:12377) — exported in Go.
    pub fn try_get_this_type_at_ex_exported(
        &mut self,
        node: NodeId,
        include_global_this: bool,
        container: Option<NodeId>,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let reparsed = ast::get_reparsed_node_for_node(node, &nodes);
        let __program = self.program.clone().expect("program");
        let rnodes = __program.nodes((reparsed).file_index());
        if rnodes[reparsed].flags.intersects(ast::NodeFlags::JSDOC)
            && !rnodes[reparsed].flags.intersects(ast::NodeFlags::REPARSED)
        {
            return None; // Binder doesn't process non-reparsed JSDoc nodes
        }
        let reparsed_container =
            container.map(|c| ast::get_reparsed_node_for_node(c, &self.program_nodes(c)));
        self.try_get_this_type_at_ex(reparsed, include_global_this, reparsed_container)
    }

    /// `(c *Checker) tryGetThisTypeAtEx` (checker.go:12385).
    pub(crate) fn try_get_this_type_at_ex(
        &mut self,
        node: NodeId,
        include_global_this: bool,
        container: Option<NodeId>,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let container = container.unwrap_or_else(|| {
            self.get_this_container(
                node, false, /* includeArrowFunctions */
                false, /* includeClassComputedPropertyName */
            )
        });
        if ast::is_function_like(Some(container), &nodes)
            && (!self.is_in_parameter_initializer_before_containing_function(node)
                || ast::get_this_parameter(&nodes[container], &nodes).is_some())
        {
            let mut sig = self.get_signature_of_full_signature_type(container);
            if sig.is_none() {
                sig = Some(self.get_signature_from_declaration(container));
            }
            let mut this_type = sig.and_then(|s| self.get_this_type_of_signature(s));
            // Note: a parameter initializer should refer to class-this unless
            // function-this is explicitly annotated.
            // If this is a function in a JS file, it might be a class method.
            if this_type.is_none() {
                this_type = self.get_contextual_this_parameter_type(container);
            }
            if let Some(this_type) = this_type {
                return Some(self.get_flow_type_of_reference(node, this_type));
            }
        }
        if nodes[container]
            .parent
            .is_some_and(|p| ast::is_class_like(Some(p), &nodes))
        {
            let parent = nodes[container].parent.unwrap();
            let symbol = self
                .get_symbol_of_declaration(parent)
                .unwrap_or(SymbolId::NONE);
            let t = if ast::is_static(&nodes[container]) {
                self.get_type_of_symbol(symbol)
            } else {
                self.types_handle()
                    .get({
                        let dt = self.get_declared_type_of_symbol(symbol);
                        dt
                    })
                    .as_interface_type()
                    .expect("class instance type")
                    .this_type
                    .expect("interface thisType")
            };
            return Some(self.get_flow_type_of_reference(node, t));
        }
        if ast::is_source_file(&nodes[container]) {
            // look up in the source file's locals or exports
            if nodes[container]
                .as_source_file()
                .external_module_indicator
                .is_some()
            {
                // TODO: Maybe issue a better error than 'object is possibly
                // undefined'
                return Some(self.undefined_type);
            }
            if include_global_this {
                return Some(self.get_type_of_symbol(self.global_this_symbol));
            }
        }
        None
    }

    /// `(c *Checker) getThisContainer` (checker.go:12427) — the Checker
    /// method, distinct from `ast::get_this_container` (decorator handling).
    pub(crate) fn get_this_container(
        &mut self,
        node: NodeId,
        include_arrow_functions: bool,
        include_class_computed_property_name: bool,
    ) -> NodeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut node = node;
        loop {
            node = nodes[node]
                .parent
                // If we never pass in a SourceFile, this should be
                // unreachable, since we'll stop when we reach that.
                .expect("No parent in getThisContainer");
            match nodes[node].kind {
                ast::Kind::ComputedPropertyName => {
                    // If the grandparent node is an object literal (as opposed
                    // to a class), then the computed property is not a 'this'
                    // container. A computed property name in a class needs to
                    // be a this container so that we can error on it.
                    if include_class_computed_property_name
                        && nodes[node]
                            .parent
                            .and_then(|p| nodes[p].parent)
                            .is_some_and(|gp| ast::is_class_like(Some(gp), &nodes))
                    {
                        return node;
                    }
                    // If this is a computed property, then the parent should
                    // not make it a this container. The parent might be a
                    // property in an object literal, like a method or accessor.
                    // But in order for such a parent to be a this container,
                    // the reference must be in the *body* of the container.
                    node = nodes[node]
                        .parent
                        .and_then(|p| nodes[p].parent)
                        .expect("getThisContainer: nil grandparent");
                }
                ast::Kind::Decorator => {
                    // Decorators are always applied outside of the body of a
                    // class or method.
                    let parent = nodes[node].parent.expect("decorator parent");
                    if nodes[parent].kind == ast::Kind::Parameter
                        && nodes[parent]
                            .parent
                            .is_some_and(|gp| ast::is_class_element(&nodes[gp]))
                    {
                        // If the decorator's parent is a Parameter, we resolve
                        // the this container from the grandparent class
                        // declaration.
                        node = nodes[parent].parent.unwrap();
                    } else if ast::is_class_element(&nodes[parent]) {
                        // If the decorator's parent is a class element, we
                        // resolve the 'this' container from the parent class
                        // declaration.
                        node = parent;
                    }
                }
                ast::Kind::ArrowFunction => {
                    if !include_arrow_functions {
                        continue;
                    }
                    return node;
                }
                ast::Kind::FunctionDeclaration
                | ast::Kind::FunctionExpression
                | ast::Kind::ModuleDeclaration
                | ast::Kind::ClassStaticBlockDeclaration
                | ast::Kind::PropertyDeclaration
                | ast::Kind::PropertySignature
                | ast::Kind::MethodDeclaration
                | ast::Kind::MethodSignature
                | ast::Kind::Constructor
                | ast::Kind::GetAccessor
                | ast::Kind::SetAccessor
                | ast::Kind::CallSignature
                | ast::Kind::ConstructSignature
                | ast::Kind::IndexSignature
                | ast::Kind::EnumDeclaration
                | ast::Kind::SourceFile => {
                    return node;
                }
                _ => {}
            }
        }
    }

    /// `(c *Checker) isInParameterInitializerBeforeContainingFunction` (checker.go:12474).
    pub(crate) fn is_in_parameter_initializer_before_containing_function(
        &mut self,
        node: NodeId,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut in_binding_initializer = false;
        let mut node = node;
        while let Some(parent) = nodes[node].parent {
            if ast::is_function_like(Some(parent), &nodes) {
                break;
            }
            if ast::is_parameter_declaration(&nodes[parent]) {
                if in_binding_initializer || nodes[parent].initializer() == Some(node) {
                    return true;
                }
            }
            if ast::is_binding_element(&nodes[parent]) && nodes[parent].initializer() == Some(node)
            {
                in_binding_initializer = true;
            }
            node = parent;
        }
        false
    }

    /// `(c *Checker) checkThisInStaticClassFieldInitializerInDecoratedClass` (checker.go:12493).
    pub(crate) fn check_this_in_static_class_field_initializer_in_decorated_class(
        &mut self,
        this_expression: NodeId,
        container: NodeId,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((this_expression).file_index());
        if ast::is_property_declaration(&nodes[container])
            && ast::has_static_modifier(&nodes[container])
            && self.legacy_decorators
        {
            if let Some(initializer) = nodes[container].initializer() {
                if nodes[initializer]
                    .loc
                    .contains_inclusive(nodes[this_expression].pos())
                    && nodes[container]
                        .parent
                        .is_some_and(|p| ast::has_decorators(&nodes[p]))
                {
                    self.error(
                        Some(this_expression),
                        &tsc_diagnostics::Cannot_use_this_in_a_static_property_initializer_of_a_decorated_class,
                        &[],
                    );
                }
            }
        }
    }

    /// `(c *Checker) checkThisBeforeSuper` (checker.go:12502).
    pub(crate) fn check_this_before_super(
        &mut self,
        node: NodeId,
        container: NodeId,
        diagnostic_message: &'static tsc_diagnostics::Message,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let containing_class_decl = nodes[container].parent.expect("container parent");
        let base_type_node =
            ast::get_class_extends_heritage_element(&nodes[containing_class_decl], &nodes);
        // If a containing class does not have extends clause or the class
        // extends null, skip checking whether super statement is called before
        // "this" accessing.
        if base_type_node.is_some() && !self.class_declaration_extends_null(containing_class_decl) {
            if let Some(flow_node) = nodes[node].flow_node_data().and_then(|d| d.flow_node) {
                if !self.is_post_super_flow_node(node, flow_node, false /* noCacheCheck */) {
                    self.error(Some(node), diagnostic_message, &[]);
                }
            }
        }
    }

    /// `(c *Checker) classDeclarationExtendsNull` (checker.go:12519).
    /// Check if the given class-declaration extends null then return true.
    /// Otherwise, return false.
    pub(crate) fn class_declaration_extends_null(&mut self, class_decl: NodeId) -> bool {
        let class_symbol = self
            .get_symbol_of_declaration(class_decl)
            .unwrap_or(SymbolId::NONE);
        let class_instance_type = self.get_declared_type_of_symbol(class_symbol);
        let base_constructor_type = self.get_base_constructor_type_of_class(class_instance_type);
        base_constructor_type == self.null_widening_type
    }

    /// `(c *Checker) checkAssertion` (checker.go:12526).
    pub(crate) fn check_assertion(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node].kind == ast::Kind::TypeAssertionExpression {
            let file = ast::get_source_file_of_node(Some(node), &nodes);
            if let Some(file) = file {
                if tsc_tspath::extension_is_one_of(
                    nodes[file].as_source_file().file_name().extension(),
                    &[tsc_tspath::EXTENSION_MTS, tsc_tspath::EXTENSION_CTS],
                ) {
                    self.grammar_error_on_node(
                        node,
                        &tsc_diagnostics::This_syntax_is_reserved_in_files_with_the_mts_or_cts_extension_Use_an_as_expression_instead,
                        &[],
                    );
                }
            }
            if self.should_check_erasable_syntax(node) {
                let file = ast::get_source_file_of_node(Some(node), &nodes);
                let (file_text, expr_pos) = if let Some(file) = file {
                    (
                        nodes[file].as_source_file().text.clone(),
                        nodes[node]
                            .expression()
                            .map(|e| nodes[e].pos())
                            .unwrap_or_default(),
                    )
                } else {
                    (String::new(), Default::default())
                };
                let start = tsc_scanner::scanner::skip_trivia(&file_text, nodes[node].pos());
                let loc = tsc_core::text::TextRange::new(start, expr_pos);
                let diagnostic_file =
                    file.map(|f| ast::diagnostic::DiagnosticFile::from_node(f, &nodes));
                let diagnostic = ast::diagnostic::new_diagnostic(
                    diagnostic_file,
                    loc,
                    &tsc_diagnostics::This_syntax_is_not_allowed_when_erasableSyntaxOnly_is_enabled,
                    &[] as &[String],
                );
                self.add_diagnostic(&diagnostic);
            }
        }
        let type_node = nodes[node].type_().expect("assertion type node");
        let expression = nodes[node].expression().expect("assertion expression");
        let expr_type = self.check_expression_ex(expression, check_mode);
        // Always check the type node so its identifiers are resolved.
        // resolveName knows not to resolve (or report an error for) the
        // `const` in a `const` assertion, so this is safe even for
        // `x as const` and keeps diagnostics stable regardless of traversal
        // order.
        self.check_source_element(Some(type_node));
        if crate::utilities::is_const_type_reference(type_node, &nodes) {
            if !self.is_valid_const_assertion_argument(expression) {
                self.error(
                    Some(expression),
                    &tsc_diagnostics::A_const_assertion_can_only_be_applied_to_references_to_enum_members_or_string_number_boolean_array_or_object_literals,
                    &[],
                );
            }
            return self.get_regular_type_of_literal_type(expr_type);
        }
        self.assertion_links.get(node).expr_type = Some(expr_type);
        self.check_node_deferred(node);
        self.get_type_from_type_node(type_node)
    }

    /// `(c *Checker) checkAssertionDeferred` (checker.go:12554).
    pub(crate) fn check_assertion_deferred(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let type_node = nodes[node].type_().expect("assertion type node");
        let stored_expr_type = self
            .assertion_links
            .get(node)
            .expr_type
            .unwrap_or(self.error_type);
        let base_expr_type = self.get_base_type_of_literal_type(stored_expr_type);
        let expr_type = self.get_regular_type_of_object_literal(base_expr_type);
        let target_type = self.get_type_from_type_node(type_node);
        if !self.is_error_type(target_type) {
            let widened_type = self.get_widened_type(expr_type);
            if !self.is_type_comparable_to(target_type, widened_type) {
                let mut err_node = node;
                if nodes[type_node].flags.intersects(ast::NodeFlags::REPARSED) {
                    err_node = type_node;
                }
                self.check_type_comparable_to(
                    expr_type,
                    target_type,
                    Some(err_node),
                    Some(&tsc_diagnostics::Conversion_of_type_0_to_type_1_may_be_a_mistake_because_neither_type_sufficiently_overlaps_with_the_other_If_this_was_intentional_convert_the_expression_to_unknown_first),
                );
            }
        }
    }

    /// `func (c *Checker) checkBinaryExpression` (checker.go:12570).
    pub(crate) fn check_binary_expression(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let binary = nodes[node].as_binary_expression();
        let left = binary.left.expect("binary left");
        let operator_token = binary.operator_token.expect("binary operator");
        let right = binary.right.expect("binary right");
        self.check_binary_like_expression(left, operator_token, right, check_mode, node)
    }

    /// `func (c *Checker) checkBinaryLikeExpression` (checker.go:12575).
    pub(crate) fn check_binary_like_expression(
        &mut self,
        left: NodeId,
        operator_token: NodeId,
        right: NodeId,
        check_mode: CheckMode,
        error_node: NodeId,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((error_node).file_index());
        let operator = nodes[operator_token].kind;
        if operator == ast::Kind::EqualsToken
            && (nodes[left].kind == ast::Kind::ObjectLiteralExpression
                || nodes[left].kind == ast::Kind::ArrayLiteralExpression)
        {
            let right_type = self.check_expression_ex(right, check_mode);
            return self.check_destructuring_assignment(
                left,
                right_type,
                check_mode,
                nodes[right].kind == ast::Kind::ThisKeyword,
            );
        }
        let mut left_type = self.check_expression_ex(left, check_mode);
        let mut right_type = self.check_expression_ex(right, check_mode);
        if ast::is_logical_or_coalescing_binary_operator(operator) {
            let mut parent = nodes[left].parent.and_then(|p| nodes[p].parent);
            while let Some(p) = parent {
                if !ast::is_parenthesized_expression(&nodes[p])
                    && !ast::is_logical_or_coalescing_binary_expression(&nodes[p], &nodes)
                {
                    break;
                }
                parent = nodes[p].parent;
            }
            if operator == ast::Kind::AmpersandAmpersandToken
                || parent.is_some_and(|p| ast::is_if_statement(&nodes[p]))
            {
                let body = parent.and_then(|p| {
                    if ast::is_if_statement(&nodes[p]) {
                        nodes[p].as_if_statement().then_statement
                    } else {
                        None
                    }
                });
                self.check_testing_known_truthy_callable_or_awaitable_or_enum_member_type(
                    left, left_type, body,
                );
            }
            if ast::is_logical_binary_operator(operator) {
                self.check_truthiness_of_type(left_type, left);
            }
        }
        match operator {
            ast::Kind::AsteriskToken
            | ast::Kind::AsteriskAsteriskToken
            | ast::Kind::AsteriskEqualsToken
            | ast::Kind::AsteriskAsteriskEqualsToken
            | ast::Kind::SlashToken
            | ast::Kind::SlashEqualsToken
            | ast::Kind::PercentToken
            | ast::Kind::PercentEqualsToken
            | ast::Kind::MinusToken
            | ast::Kind::MinusEqualsToken
            | ast::Kind::LessThanLessThanToken
            | ast::Kind::LessThanLessThanEqualsToken
            | ast::Kind::GreaterThanGreaterThanToken
            | ast::Kind::GreaterThanGreaterThanEqualsToken
            | ast::Kind::GreaterThanGreaterThanGreaterThanToken
            | ast::Kind::GreaterThanGreaterThanGreaterThanEqualsToken
            | ast::Kind::BarToken
            | ast::Kind::BarEqualsToken
            | ast::Kind::CaretToken
            | ast::Kind::CaretEqualsToken
            | ast::Kind::AmpersandToken
            | ast::Kind::AmpersandEqualsToken => {
                if left_type == self.silent_never_type || right_type == self.silent_never_type {
                    return self.silent_never_type;
                }
                left_type = self.check_non_null_type(left_type, left);
                right_type = self.check_non_null_type(right_type, right);
                // if a user tries to apply a bitwise operator to 2 boolean operands
                // try and return them a helpful suggestion
                if self
                    .types_handle()
                    .get(left_type)
                    .flags
                    .intersects(TypeFlags::BOOLEAN_LIKE)
                    && self
                        .types_handle()
                        .get(right_type)
                        .flags
                        .intersects(TypeFlags::BOOLEAN_LIKE)
                {
                    let suggested_operator = self.get_suggested_boolean_operator(operator);
                    if suggested_operator != ast::Kind::Unknown {
                        self.error(
                            Some(operator_token),
                            &tsc_diagnostics::The_0_operator_is_not_allowed_for_boolean_types_Consider_using_1_instead,
                            &[
                                tsc_scanner::scanner::token_to_string(nodes[operator_token].kind).to_string(),
                                tsc_scanner::scanner::token_to_string(suggested_operator).to_string(),
                            ],
                        );
                        return self.number_type;
                    }
                }
                // otherwise just check each operand separately and report errors as normal
                let left_ok = self.check_arithmetic_operand_type(
                    left,
                    left_type,
                    &tsc_diagnostics::The_left_hand_side_of_an_arithmetic_operation_must_be_of_type_any_number_bigint_or_an_enum_type,
                    true, /*isAwaitValid*/
                );
                let right_ok = self.check_arithmetic_operand_type(
                    right,
                    right_type,
                    &tsc_diagnostics::The_right_hand_side_of_an_arithmetic_operation_must_be_of_type_any_number_bigint_or_an_enum_type,
                    true, /*isAwaitValid*/
                );
                let result_type;
                // If both are any or unknown, allow operation; assume it will resolve to number
                if (self.is_type_assignable_to_kind(left_type, TypeFlags::ANY_OR_UNKNOWN)
                    && self.is_type_assignable_to_kind(right_type, TypeFlags::ANY_OR_UNKNOWN))
                    || (!self.maybe_type_of_kind(left_type, TypeFlags::BIG_INT_LIKE)
                        && !self.maybe_type_of_kind(right_type, TypeFlags::BIG_INT_LIKE))
                {
                    result_type = self.number_type;
                } else if self.both_are_big_int_like(left_type, right_type) {
                    match operator {
                        ast::Kind::GreaterThanGreaterThanGreaterThanToken
                        | ast::Kind::GreaterThanGreaterThanGreaterThanEqualsToken => {
                            self.report_operator_error(
                                left_type, operator, right_type, error_node, None,
                            );
                        }
                        ast::Kind::AsteriskAsteriskToken
                        | ast::Kind::AsteriskAsteriskEqualsToken => {
                            if self.language_version < ScriptTarget::ES2016 {
                                self.error(
                                    Some(error_node),
                                    &tsc_diagnostics::Exponentiation_cannot_be_performed_on_bigint_values_unless_the_target_option_is_set_to_es2016_or_later,
                                    &[],
                                );
                            }
                        }
                        _ => {}
                    }
                    result_type = self.bigint_type;
                } else {
                    self.report_operator_error(
                        left_type,
                        operator,
                        right_type,
                        error_node,
                        Some(&|c: &mut Checker, l: TypeId, r: TypeId| {
                            c.both_are_big_int_like(l, r)
                        }),
                    );
                    result_type = self.error_type;
                }
                if left_ok && right_ok {
                    self.check_assignment_operator(left, operator, right, left_type, result_type);
                    match operator {
                        ast::Kind::LessThanLessThanToken
                        | ast::Kind::LessThanLessThanEqualsToken
                        | ast::Kind::GreaterThanGreaterThanToken
                        | ast::Kind::GreaterThanGreaterThanEqualsToken
                        | ast::Kind::GreaterThanGreaterThanGreaterThanToken
                        | ast::Kind::GreaterThanGreaterThanGreaterThanEqualsToken => {
                            let rhs_eval = self.evaluate_call(right, Some(right), &nodes);
                            if let Some(tsc_evaluator::Value::Number(num_value)) = rhs_eval.value
                                && num_value.abs().0 >= 32.0
                            {
                                // Elevate from suggestion to error within an enum member
                                let grandparent = nodes[right].parent.and_then(|p| nodes[p].parent);
                                let is_enum_member = grandparent.is_some_and(|gp| {
                                    ast::walk_up_parenthesized_expressions(gp, &nodes)
                                        .is_some_and(|w| ast::is_enum_member(&nodes[w]))
                                });
                                let text = tsc_scanner::utilities::get_text_of_node(left, &nodes);
                                let op_text = tsc_scanner::scanner::token_to_string(operator);
                                let rem = num_value.remainder(tsc_jsnum::Number(32.0));
                                self.error_or_suggestion(
                                    is_enum_member,
                                    Some(error_node),
                                    &tsc_diagnostics::This_operation_can_be_simplified_This_shift_is_identical_to_0_1_2,
                                    &[text.to_string(), op_text.to_string(), rem.string()],
                                );
                            }
                        }
                        _ => {}
                    }
                }
                return result_type;
            }
            ast::Kind::PlusToken | ast::Kind::PlusEqualsToken => {
                if left_type == self.silent_never_type || right_type == self.silent_never_type {
                    return self.silent_never_type;
                }
                if !self.is_type_assignable_to_kind(left_type, TypeFlags::STRING_LIKE)
                    && !self.is_type_assignable_to_kind(right_type, TypeFlags::STRING_LIKE)
                {
                    left_type = self.check_non_null_type(left_type, left);
                    right_type = self.check_non_null_type(right_type, right);
                }
                let mut result_type: Option<TypeId> = None;
                if self.is_type_assignable_to_kind_ex(left_type, TypeFlags::NUMBER_LIKE, true)
                    && self.is_type_assignable_to_kind_ex(right_type, TypeFlags::NUMBER_LIKE, true)
                {
                    // Operands of an enum type are treated as having the primitive type Number.
                    // If both operands are of the Number primitive type, the result is of the Number primitive type.
                    result_type = Some(self.number_type);
                } else if self.is_type_assignable_to_kind_ex(
                    left_type,
                    TypeFlags::BIG_INT_LIKE,
                    true,
                ) && self.is_type_assignable_to_kind_ex(
                    right_type,
                    TypeFlags::BIG_INT_LIKE,
                    true,
                ) {
                    // If both operands are of the BigInt primitive type, the result is of the BigInt primitive type.
                    result_type = Some(self.bigint_type);
                } else if self.is_type_assignable_to_kind_ex(
                    left_type,
                    TypeFlags::STRING_LIKE,
                    true,
                ) || self.is_type_assignable_to_kind_ex(
                    right_type,
                    TypeFlags::STRING_LIKE,
                    true,
                ) {
                    // If one or both operands are of the String primitive type, the result is of the String primitive type.
                    result_type = Some(self.string_type);
                } else if crate::checker_core::is_type_any(&self.types, left_type)
                    || crate::checker_core::is_type_any(&self.types, right_type)
                {
                    // Otherwise, the result is of type Any.
                    // NOTE: unknown type here denotes error type. Old compiler treated this case as any type so do we.
                    if self.is_error_type(left_type) || self.is_error_type(right_type) {
                        result_type = Some(self.error_type);
                    } else {
                        result_type = Some(self.any_type);
                    }
                }
                // Symbols are not allowed at all in arithmetic expressions
                if let Some(result) = result_type
                    && !self.check_for_disallowed_es_symbol_operand(
                        left, right, left_type, right_type, operator,
                    )
                {
                    return result;
                }
                let Some(result_type) = result_type else {
                    // Types that have a reasonably good chance of being a valid operand type.
                    // If both types have an awaited type of one of these, we'll assume the user
                    // might be missing an await without doing an exhaustive check that inserting
                    // await(s) will actually be a completely valid binary expression.
                    let close_enough_kind = TypeFlags::NUMBER_LIKE
                        | TypeFlags::BIG_INT_LIKE
                        | TypeFlags::STRING_LIKE
                        | TypeFlags::ANY_OR_UNKNOWN;
                    self.report_operator_error(
                        left_type,
                        operator,
                        right_type,
                        error_node,
                        Some(&move |c: &mut Checker, l: TypeId, r: TypeId| {
                            c.is_type_assignable_to_kind(l, close_enough_kind)
                                && c.is_type_assignable_to_kind(r, close_enough_kind)
                        }),
                    );
                    return self.any_type;
                };
                if operator == ast::Kind::PlusEqualsToken {
                    self.check_assignment_operator(left, operator, right, left_type, result_type);
                }
                return result_type;
            }
            ast::Kind::LessThanToken
            | ast::Kind::GreaterThanToken
            | ast::Kind::LessThanEqualsToken
            | ast::Kind::GreaterThanEqualsToken => {
                if self.check_for_disallowed_es_symbol_operand(
                    left, right, left_type, right_type, operator,
                ) {
                    let __h9214_25 = self.check_non_null_type(left_type, left);
                    left_type = self.get_base_type_of_literal_type_for_comparison(__h9214_25);
                    let __h9217_25 = self.check_non_null_type(right_type, right);
                    right_type = self.get_base_type_of_literal_type_for_comparison(__h9217_25);
                    self.report_operator_error_unless(
                        left_type,
                        operator,
                        right_type,
                        error_node,
                        &|c: &mut Checker, left: TypeId, right: TypeId| {
                            if crate::checker_core::is_type_any(&c.types, left)
                                || crate::checker_core::is_type_any(&c.types, right)
                            {
                                return true;
                            }
                            let left_assignable_to_number =
                                c.is_type_assignable_to(left, c.number_or_big_int_type);
                            let right_assignable_to_number =
                                c.is_type_assignable_to(right, c.number_or_big_int_type);
                            (left_assignable_to_number && right_assignable_to_number)
                                || (!left_assignable_to_number
                                    && !right_assignable_to_number
                                    && c.are_types_comparable(left, right))
                        },
                    );
                }
                return self.boolean_type;
            }
            ast::Kind::EqualsEqualsToken
            | ast::Kind::ExclamationEqualsToken
            | ast::Kind::EqualsEqualsEqualsToken
            | ast::Kind::ExclamationEqualsEqualsToken => {
                // We suppress errors in CheckMode.TypeOnly (meaning the invocation came from getTypeOfExpression). During
                // control flow analysis it is possible for operands to temporarily have narrower types, and those narrower
                // types may cause the operands to not be comparable. We don't want such errors reported (see #46475).
                if !check_mode.intersects(CheckMode::TYPE_ONLY) {
                    if (crate::utilities::is_literal_expression_of_object(left, &nodes)
                        || crate::utilities::is_literal_expression_of_object(right, &nodes))
                        // only report for === and !== in JS, not == or !=
                        && (!ast::is_in_js_file(Some(left), &nodes)
                            || (operator == ast::Kind::EqualsEqualsEqualsToken
                                || operator == ast::Kind::ExclamationEqualsEqualsToken))
                    {
                        let eq_type = operator == ast::Kind::EqualsEqualsToken
                            || operator == ast::Kind::EqualsEqualsEqualsToken;
                        self.error(
                            Some(error_node),
                            &tsc_diagnostics::This_condition_will_always_return_0_since_JavaScript_compares_objects_by_reference_not_value,
                            &[if eq_type { "false".to_string() } else { "true".to_string() }],
                        );
                    }
                    self.check_nan_equality(error_node, operator, left, right);
                    self.report_operator_error_unless(
                        left_type,
                        operator,
                        right_type,
                        error_node,
                        &|c: &mut Checker, left: TypeId, right: TypeId| {
                            c.is_type_equality_comparable_to(left, right)
                                || c.is_type_equality_comparable_to(right, left)
                        },
                    );
                }
                return self.boolean_type;
            }
            ast::Kind::InstanceOfKeyword => {
                return self
                    .check_instance_of_expression(left, right, left_type, right_type, check_mode);
            }
            ast::Kind::InKeyword => {
                return self.check_in_expression(left, right, left_type, right_type);
            }
            ast::Kind::AmpersandAmpersandToken | ast::Kind::AmpersandAmpersandEqualsToken => {
                let mut result_type = left_type;
                if self.has_type_facts(left_type, TypeFacts::TRUTHY) {
                    let mut t = left_type;
                    if !self.strict_null_checks {
                        t = self.get_base_type_of_literal_type(right_type);
                    }
                    let falsy_part = self.extract_definitely_falsy_types(t);
                    result_type = self.get_union_type(&[falsy_part, right_type]);
                }
                if operator == ast::Kind::AmpersandAmpersandEqualsToken {
                    self.check_assignment_operator(left, operator, right, left_type, right_type);
                }
                return result_type;
            }
            ast::Kind::BarBarToken | ast::Kind::BarBarEqualsToken => {
                let mut result_type = left_type;
                if self.has_type_facts(left_type, TypeFacts::FALSY) {
                    let no_falsy = self.remove_definitely_falsy_types(left_type);
                    let nn = self.get_non_nullable_type(no_falsy);
                    result_type = self.get_union_type_ex(
                        &[nn, right_type],
                        UnionReduction::Subtype,
                        None,
                        None,
                    );
                }
                if operator == ast::Kind::BarBarEqualsToken {
                    self.check_assignment_operator(left, operator, right, left_type, right_type);
                }
                return result_type;
            }
            ast::Kind::QuestionQuestionToken | ast::Kind::QuestionQuestionEqualsToken => {
                if operator == ast::Kind::QuestionQuestionToken {
                    self.check_nullish_coalesce_operands(left, right);
                }
                let mut result_type = left_type;
                if self.has_type_facts(left_type, TypeFacts::EQ_UNDEFINED_OR_NULL) {
                    let nn_left = self.get_non_nullable_type(left_type);
                    result_type = self.get_union_type_ex(
                        &[nn_left, right_type],
                        UnionReduction::Subtype,
                        None,
                        None,
                    );
                }
                if operator == ast::Kind::QuestionQuestionEqualsToken {
                    self.check_assignment_operator(left, operator, right, left_type, right_type);
                }
                return result_type;
            }
            ast::Kind::EqualsToken => {
                self.check_assignment_operator(left, operator, right, left_type, right_type);
                return right_type;
            }
            ast::Kind::CommaToken => {
                if !self.compiler_options.allow_unreachable_code.is_true()
                    && self.is_side_effect_free(left)
                    && !self.is_indirect_call(nodes[left].parent)
                {
                    let sf = ast::get_source_file_of_node(Some(left), &nodes);
                    let start = sf.map(|sf| {
                        tsc_scanner::scanner::skip_trivia(
                            nodes[sf].as_source_file().text(),
                            nodes[left].pos(),
                        )
                    });
                    let is_in_diag_2657 = sf.is_some_and(|sf| {
                        nodes[sf].as_source_file().diagnostics().iter().any(|d| {
                            if ast::diagnostic::lock_diagnostic(d).code()
                                != tsc_diagnostics::JSX_expressions_must_have_one_parent_element
                                    .code()
                            {
                                return false;
                            }
                            start.is_some_and(|start| {
                                ast::diagnostic::lock_diagnostic(d).loc().contains(start)
                            })
                        })
                    });
                    if !is_in_diag_2657 {
                        self.error(
                            Some(left),
                            &tsc_diagnostics::Left_side_of_comma_operator_is_unused_and_has_no_side_effects,
                            &[],
                        );
                    }
                }
                return right_type;
            }
            _ => {}
        }
        panic!("Unhandled case in check_binary_like_expression")
    }

    /// `func (c *Checker) checkDestructuringAssignment` (checker.go:12791).
    pub(crate) fn check_destructuring_assignment(
        &mut self,
        node: NodeId,
        mut source_type: TypeId,
        check_mode: CheckMode,
        right_is_this: bool,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let target;
        if ast::is_shorthand_property_assignment(&nodes[node]) {
            let initializer = nodes[node]
                .as_shorthand_property_assignment()
                .object_assignment_initializer;
            if let Some(initializer) = initializer {
                let init_ty = self.check_expression(initializer);

                // In strict null checking mode, if a default value of a non-undefined type is specified, remove
                // undefined from the final type.
                if self.strict_null_checks && !self.has_type_facts(init_ty, TypeFacts::IS_UNDEFINED)
                {
                    source_type = self.get_type_with_facts(source_type, TypeFacts::NE_UNDEFINED);
                }
                let name = nodes[node].name();
                let equals_token = nodes[node].as_shorthand_property_assignment().equals_token;
                self.check_binary_like_expression(
                    name.expect("shorthand property assignment name"),
                    equals_token.expect("shorthand property assignment equals token"),
                    initializer,
                    check_mode,
                    node,
                );
            }
            target = nodes[node]
                .name()
                .expect("shorthand property assignment name");
        } else {
            target = node;
        }
        let mut target = target;
        if ast::is_binary_expression(&nodes[target])
            && nodes[target]
                .as_binary_expression()
                .operator_token
                .is_some_and(|t| nodes[t].kind == ast::Kind::EqualsToken)
        {
            self.check_binary_expression(target, check_mode);
            target = nodes[target]
                .as_binary_expression()
                .left
                .expect("binary left");
            // A default value is specified, so remove undefined from the final type.
            if self.strict_null_checks {
                source_type = self.get_type_with_facts(source_type, TypeFacts::NE_UNDEFINED);
            }
        }
        if ast::is_object_literal_expression(&nodes[target]) {
            return self.check_object_literal_assignment(target, source_type, right_is_this);
        }
        if ast::is_array_literal_expression(&nodes[target]) {
            return self.check_array_literal_assignment(target, source_type, check_mode);
        }
        self.check_reference_assignment(target, source_type, check_mode)
    }

    /// `func (c *Checker) checkObjectLiteralAssignment` (checker.go:12820).
    pub(crate) fn check_object_literal_assignment(
        &mut self,
        node: NodeId,
        source_type: TypeId,
        right_is_this: bool,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let properties_len = nodes[node]
            .property_list()
            .map(|l| l.nodes.len())
            .unwrap_or(0);
        if self.strict_null_checks && properties_len == 0 {
            return self.check_non_null_type(source_type, node);
        }
        for i in 0..properties_len {
            self.check_object_literal_destructuring_property_assignment(
                node,
                source_type,
                i,
                true,
                right_is_this,
            );
        }
        source_type
    }

    /// `func (c *Checker) checkObjectLiteralDestructuringPropertyAssignment`
    /// (checker.go:12830). PORT: `allProperties *ast.NodeList` becomes
    /// `has_all_properties: bool` — when set, `node.PropertyList()` supplies the
    /// sibling list (the only Go caller that passes a list passes the node's own
    /// property list).
    pub(crate) fn check_object_literal_destructuring_property_assignment(
        &mut self,
        node: NodeId,
        object_literal_type: TypeId,
        property_index: usize,
        has_all_properties: bool,
        right_is_this: bool,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let properties: Vec<NodeId> = nodes[node]
            .properties()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        if property_index >= properties.len() {
            return None;
        }
        let property = properties[property_index];
        if ast::is_property_assignment(&nodes[property])
            || ast::is_shorthand_property_assignment(&nodes[property])
        {
            let name = nodes[property].name();

            if let Some(name) = name
                && ast::is_private_identifier(&nodes[name])
            {
                self.grammar_error_on_node(
                    name,
                    &tsc_diagnostics::Private_identifiers_cannot_be_used_in_destructuring_patterns,
                    &[],
                );
            }

            let expr_type = self.get_literal_type_from_property_name(name.expect("name"));
            if crate::utilities::is_type_usable_as_property_name(&self.types, expr_type) {
                let text = crate::utilities::get_property_name_from_type(&self.types, expr_type);
                if let Some(prop) = self.get_property_of_type(object_literal_type, &text) {
                    self.mark_property_as_referenced(prop, Some(property), right_is_this);
                    self.check_property_accessibility(
                        property,
                        false, /*isSuper*/
                        true,  /*writing*/
                        object_literal_type,
                        prop,
                    );
                }
            }
            let hdv = self.has_default_value(property);

            let element_type = self.get_indexed_access_type_ex(
                object_literal_type,
                expr_type,
                AccessFlags::EXPRESSION_POSITION
                    | if hdv {
                        AccessFlags::ALLOW_MISSING
                    } else {
                        AccessFlags::NONE
                    },
                name,
                None,
            );
            let t = self.get_flow_type_of_destructuring(property, element_type);
            let expr = if ast::is_property_assignment(&nodes[property]) {
                nodes[property]
                    .initializer()
                    .expect("property assignment initializer")
            } else {
                property
            };
            return Some(self.check_destructuring_assignment(expr, t, CheckMode::NORMAL, false));
        }
        if ast::is_spread_assignment(&nodes[property]) {
            if property_index < properties.len() - 1 {
                self.error(
                    Some(property),
                    &tsc_diagnostics::A_rest_element_must_be_last_in_a_destructuring_pattern,
                    &[],
                );
                return None;
            }
            if self.language_version
                < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET.object_spread_rest
            {
                self.check_external_emit_helpers(property, ExternalEmitHelpers::REST);
            }
            let mut non_rest_names: Vec<NodeId> = Vec::new();
            if has_all_properties {
                let all: Vec<NodeId> = nodes[node]
                    .property_list()
                    .map(|l| l.nodes.to_vec())
                    .unwrap_or_default();
                for other_property in all {
                    if !ast::is_spread_assignment(&nodes[other_property])
                        && let Some(name) = nodes[other_property].name()
                    {
                        non_rest_names.push(name);
                    }
                }
            }
            let symbol = self.types.get_ref(object_literal_type).symbol;
            let t = self.get_rest_type(object_literal_type, &non_rest_names, symbol);
            // PORT: clone the `*ast.NodeList` — the arena borrow ends before
            // the `&mut self` grammar check call.
            let all_properties_list = nodes[node].property_list().cloned();
            self.check_grammar_for_disallowed_trailing_comma(
                all_properties_list.as_ref(),
                &tsc_diagnostics::A_rest_parameter_or_binding_pattern_may_not_have_a_trailing_comma,
                &nodes,
            );
            return Some(
                self.check_destructuring_assignment(
                    nodes[property]
                        .expression()
                        .expect("spread assignment expression"),
                    t,
                    CheckMode::NORMAL,
                    false,
                ),
            );
        }
        self.error(
            Some(property),
            &tsc_diagnostics::Property_assignment_expected,
            &[],
        );
        None
    }

    /// `func (c *Checker) checkArrayLiteralAssignment` (checker.go:12878).
    pub(crate) fn check_array_literal_assignment(
        &mut self,
        node: NodeId,
        source_type: TypeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let elements: Vec<NodeId> = nodes[node]
            .elements()
            .map(|e| e.to_vec())
            .unwrap_or_default();
        // This elementType will be used if the specific property corresponding to this index is not
        // present (aka the tuple element property). This call also checks that the parentType is in
        // fact an iterable or array (depending on target language).
        let possibly_out_of_bounds_type = self.check_iterated_type_or_element_type(
            IterationUse(IterationUse::DESTRUCTURING.0 | IterationUse::POSSIBLY_OUT_OF_BOUNDS.0),
            source_type,
            self.undefined_type,
            Some(node),
        );
        let mut in_bounds_type = if self.compiler_options.no_unchecked_indexed_access
            == tsc_core::tristate::Tristate::True
        {
            None
        } else {
            Some(possibly_out_of_bounds_type)
        };
        for (i, &element) in elements.iter().enumerate() {
            let mut t = possibly_out_of_bounds_type;
            if nodes[element].kind == ast::Kind::SpreadElement {
                if in_bounds_type.is_none() {
                    in_bounds_type = Some(self.check_iterated_type_or_element_type(
                        IterationUse::DESTRUCTURING,
                        source_type,
                        self.undefined_type,
                        Some(node),
                    ));
                }
                t = in_bounds_type.unwrap();
            }
            self.check_array_literal_destructuring_element_assignment(
                node,
                source_type,
                i,
                t,
                check_mode,
            );
        }
        source_type
    }

    /// `func (c *Checker) checkArrayLiteralDestructuringElementAssignment`
    /// (checker.go:12900).
    pub(crate) fn check_array_literal_destructuring_element_assignment(
        &mut self,
        node: NodeId,
        source_type: TypeId,
        element_index: usize,
        element_type: TypeId,
        check_mode: CheckMode,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let elements: Vec<NodeId> = nodes[node]
            .element_list()
            .map(|l| l.nodes.to_vec())
            .unwrap_or_default();
        if element_index >= elements.len() {
            return None;
        }
        let element = elements[element_index];
        if !ast::is_omitted_expression(&nodes[element]) {
            if !ast::is_spread_element(&nodes[element]) {
                let index_type =
                    self.get_number_literal_type(tsc_jsnum::Number(element_index as f64));
                if self.is_array_like_type(source_type) {
                    // We create a synthetic expression so that getIndexedAccessType doesn't get confused
                    // when the element is a SyntaxKind.ElementAccessExpression.
                    let access_flags = AccessFlags::EXPRESSION_POSITION
                        | if self.has_default_value(element) {
                            AccessFlags::ALLOW_MISSING
                        } else {
                            AccessFlags::NONE
                        };
                    let synthetic =
                        self.create_synthetic_expression(element, index_type, false, None);
                    let element_type = self
                        .get_indexed_access_type_or_undefined(
                            source_type,
                            index_type,
                            access_flags,
                            Some(synthetic),
                            None,
                        )
                        .unwrap_or(self.error_type);
                    let mut assigned_type = element_type;
                    if self.has_default_value(element) {
                        assigned_type =
                            self.get_type_with_facts(element_type, TypeFacts::NE_UNDEFINED);
                    }
                    let t = self.get_flow_type_of_destructuring(element, assigned_type);
                    return Some(
                        self.check_destructuring_assignment(element, t, check_mode, false),
                    );
                }
                return Some(self.check_destructuring_assignment(
                    element,
                    element_type,
                    check_mode,
                    false,
                ));
            }
            if element_index < elements.len() - 1 {
                self.error(
                    Some(element),
                    &tsc_diagnostics::A_rest_element_must_be_last_in_a_destructuring_pattern,
                    &[],
                );
            } else {
                let rest_expression = nodes[element]
                    .expression()
                    .expect("spread element expression");
                if ast::is_binary_expression(&nodes[rest_expression])
                    && nodes[rest_expression]
                        .as_binary_expression()
                        .operator_token
                        .is_some_and(|t| nodes[t].kind == ast::Kind::EqualsToken)
                {
                    let op = nodes[rest_expression]
                        .as_binary_expression()
                        .operator_token
                        .unwrap();
                    self.error(
                        Some(op),
                        &tsc_diagnostics::A_rest_element_cannot_have_an_initializer,
                        &[],
                    );
                } else {
                    let element_list = nodes[node].element_list().cloned();
                    self.check_grammar_for_disallowed_trailing_comma(
                        element_list.as_ref(),
                        &tsc_diagnostics::A_rest_parameter_or_binding_pattern_may_not_have_a_trailing_comma,
                        &nodes,
                    );
                    let t;
                    if self.every_type_is_tuple(source_type) {
                        t = self.map_type(
                            source_type,
                            Rc::new(move |c: &mut Checker, t: TypeId| {
                                c.slice_tuple_type(t, element_index, 0)
                            }),
                        );
                    } else {
                        t = self.create_array_type(element_type);
                    }
                    return Some(self.check_destructuring_assignment(
                        rest_expression,
                        t,
                        check_mode,
                        false,
                    ));
                }
            }
        }
        None
    }

    /// `everyType(sourceType, isTupleType)` inline — `everyType` is a free
    /// function in checker.go owned by the checker_d range.
    fn every_type_is_tuple(&self, source_type: TypeId) -> bool {
        let t = self.types.get_ref(source_type);
        if t.flags.intersects(TypeFlags::UNION) {
            t.as_union_type()
                .union_or_intersection
                .types
                .iter()
                .all(|&m| crate::checker_core::is_tuple_type(&self.types, m))
        } else {
            crate::checker_core::is_tuple_type(&self.types, source_type)
        }
    }

    /// `func (c *Checker) checkReferenceAssignment` (checker.go:12950).
    pub(crate) fn check_reference_assignment(
        &mut self,
        target: NodeId,
        source_type: TypeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let target_type = self.check_expression_ex(target, check_mode);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((target).file_index());
        let is_spread_parent = nodes[target]
            .parent
            .is_some_and(|p| ast::is_spread_assignment(&nodes[p]));
        let message = if is_spread_parent {
            &tsc_diagnostics::The_target_of_an_object_rest_assignment_must_be_a_variable_or_a_property_access
        } else {
            &tsc_diagnostics::The_left_hand_side_of_an_assignment_expression_must_be_a_variable_or_a_property_access
        };
        let optional_message = if is_spread_parent {
            &tsc_diagnostics::The_target_of_an_object_rest_assignment_may_not_be_an_optional_property_access
        } else {
            &tsc_diagnostics::The_left_hand_side_of_an_assignment_expression_may_not_be_an_optional_property_access
        };
        if self.check_reference_expression(target, message, optional_message) {
            self.check_type_assignable_to_and_optionally_elaborate(
                source_type,
                target_type,
                Some(target),
                Some(target),
                None,
                None,
            );
        }
        source_type
    }

    /// `func (c *Checker) reportOperatorError` (checker.go:12964). PORT: the
    /// `isRelated` callback takes `&mut Checker` as its first parameter so the
    /// closure can call back into checker methods without capturing `self`.
    pub(crate) fn report_operator_error(
        &mut self,
        left_type: TypeId,
        operator: ast::Kind,
        right_type: TypeId,
        error_node: NodeId,
        is_related: Option<&dyn Fn(&mut Checker, TypeId, TypeId) -> bool>,
    ) {
        let mut would_work_with_await = false;
        if let Some(is_related) = is_related {
            let awaited_left_type = self.get_awaited_type_no_alias(left_type);
            let awaited_right_type = self.get_awaited_type_no_alias(right_type);
            would_work_with_await = !(awaited_left_type == Some(left_type)
                && awaited_right_type == Some(right_type))
                && awaited_left_type.is_some()
                && awaited_right_type.is_some()
                && is_related(
                    self,
                    awaited_left_type.unwrap(),
                    awaited_right_type.unwrap(),
                );
        }
        let mut effective_left = left_type;
        let mut effective_right = right_type;
        if !would_work_with_await && is_related.is_some() {
            let (l, r) =
                self.get_base_types_if_unrelated(left_type, right_type, is_related.unwrap());
            effective_left = l;
            effective_right = r;
        }
        let (left_str, right_str) =
            self.get_type_names_for_error_display(effective_left, effective_right);
        match operator {
            ast::Kind::EqualsEqualsEqualsToken
            | ast::Kind::EqualsEqualsToken
            | ast::Kind::ExclamationEqualsEqualsToken
            | ast::Kind::ExclamationEqualsToken => {
                self.error_and_maybe_suggest_await(
                    error_node,
                    would_work_with_await,
                    &tsc_diagnostics::This_comparison_appears_to_be_unintentional_because_the_types_0_and_1_have_no_overlap,
                    &[left_str, right_str],
                );
            }
            _ => {
                self.error_and_maybe_suggest_await(
                    error_node,
                    would_work_with_await,
                    &tsc_diagnostics::Operator_0_cannot_be_applied_to_types_1_and_2,
                    &[
                        tsc_scanner::scanner::token_to_string(operator).to_string(),
                        left_str,
                        right_str,
                    ],
                );
            }
        }
    }

    /// `func (c *Checker) reportOperatorErrorUnless` (checker.go:12983).
    pub(crate) fn report_operator_error_unless(
        &mut self,
        left_type: TypeId,
        operator: ast::Kind,
        right_type: TypeId,
        error_node: NodeId,
        types_are_compatible: &dyn Fn(&mut Checker, TypeId, TypeId) -> bool,
    ) {
        if !types_are_compatible(self, left_type, right_type) {
            self.report_operator_error(
                left_type,
                operator,
                right_type,
                error_node,
                Some(types_are_compatible),
            );
        }
    }

    /// `func (c *Checker) getBaseTypesIfUnrelated` (checker.go:12989).
    pub(crate) fn get_base_types_if_unrelated(
        &mut self,
        left_type: TypeId,
        right_type: TypeId,
        is_related: &dyn Fn(&mut Checker, TypeId, TypeId) -> bool,
    ) -> (TypeId, TypeId) {
        let mut effective_left = left_type;
        let mut effective_right = right_type;
        let left_base = self.get_base_type_of_literal_type(left_type);
        let right_base = self.get_base_type_of_literal_type(right_type);
        if !is_related(self, left_base, right_base) {
            effective_left = left_base;
            effective_right = right_base;
        }
        (effective_left, effective_right)
    }

    /// `func (c *Checker) checkAssignmentOperator` (checker.go:13001).
    pub(crate) fn check_assignment_operator(
        &mut self,
        left: NodeId,
        operator: ast::Kind,
        right: NodeId,
        mut left_type: TypeId,
        right_type: TypeId,
    ) {
        if operator.is_assignment_operator() {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((left).file_index());
            // We ignore assignments of undefined to CommonJS exports when there are multiple assignment declarations
            if nodes[left].parent.is_some_and(|p| {
                ast::is_declaration_node(&nodes[p])
                    && ast::get_assignment_declaration_kind(p, &nodes)
                        == ast::JsDeclarationKind::ExportsProperty
            }) {
                let symbol = self.symbol_node_links.get(left).resolved_symbol;
                if let Some(symbol) = symbol
                    && self.sym(symbol).declarations.len() > 1
                    && self
                        .types_handle()
                        .get(right_type)
                        .flags
                        .intersects(TypeFlags::UNDEFINED)
                {
                    return;
                }
            }
            // getters can be a subtype of setters, so to check for assignability we use the setter's type instead
            if ast::is_compound_assignment(operator)
                && ast::is_property_access_expression(&nodes[left])
            {
                left_type = self.check_property_access_expression(left, CheckMode::NORMAL, true);
            }
            if self.check_reference_expression(
                left,
                &tsc_diagnostics::The_left_hand_side_of_an_assignment_expression_must_be_a_variable_or_a_property_access,
                &tsc_diagnostics::The_left_hand_side_of_an_assignment_expression_may_not_be_an_optional_property_access,
            ) {
                let mut head_message: Option<&'static tsc_diagnostics::Message> = None;
                if self.exact_optional_property_types
                    && ast::is_property_access_expression(&nodes[left])
                    && self.maybe_type_of_kind(right_type, TypeFlags::UNDEFINED)
                {
                    let expr = nodes[left].expression().expect("property access expression");
                    let prop_name = nodes[left]
                        .name()
                        .map(|n| nodes[n].text(&nodes).into_owned());
                    let expr_ty = self.get_type_of_expression(expr);
                    let target = prop_name.and_then(|name| {
                        self.get_type_of_property_of_type(expr_ty, &name)
                    });
                    if self.is_exact_optional_property_mismatch(Some(right_type), target) {
                        head_message = Some(&tsc_diagnostics::Type_0_is_not_assignable_to_type_1_with_exactOptionalPropertyTypes_Colon_true_Consider_adding_undefined_to_the_type_of_the_target);
                    }
                }
                // to avoid cascading errors check assignability only if 'isReference' check succeeded and no errors were reported
                self.check_type_assignable_to_and_optionally_elaborate(
                    right_type,
                    left_type,
                    Some(left),
                    Some(right),
                    head_message,
                    None,
                );
            }
        }
    }

    /// `func (c *Checker) bothAreBigIntLike` (checker.go:13028).
    pub(crate) fn both_are_big_int_like(&mut self, left: TypeId, right: TypeId) -> bool {
        self.is_type_assignable_to_kind(left, TypeFlags::BIG_INT_LIKE)
            && self.is_type_assignable_to_kind(right, TypeFlags::BIG_INT_LIKE)
    }

    /// `func (c *Checker) getSuggestedBooleanOperator` (checker.go:13032).
    pub(crate) fn get_suggested_boolean_operator(&mut self, operator: ast::Kind) -> ast::Kind {
        match operator {
            ast::Kind::BarToken | ast::Kind::BarEqualsToken => ast::Kind::BarBarToken,
            ast::Kind::CaretToken | ast::Kind::CaretEqualsToken => {
                ast::Kind::ExclamationEqualsEqualsToken
            }
            ast::Kind::AmpersandToken | ast::Kind::AmpersandEqualsToken => {
                ast::Kind::AmpersandAmpersandToken
            }
            _ => ast::Kind::Unknown,
        }
    }

    /// `func (c *Checker) checkArithmeticOperandType` (checker.go:13045).
    pub(crate) fn check_arithmetic_operand_type(
        &mut self,
        operand: NodeId,
        t: TypeId,
        diagnostic: &'static tsc_diagnostics::Message,
        is_await_valid: bool,
    ) -> bool {
        if !self.is_type_assignable_to(t, self.number_or_big_int_type) {
            let awaited_type = if is_await_valid {
                self.get_awaited_type_of_promise(t)
            } else {
                None
            };
            let a_ok = awaited_type
                .is_some_and(|a| self.is_type_assignable_to(a, self.number_or_big_int_type));
            self.error_and_maybe_suggest_await(operand, a_ok, diagnostic, &[]);
            return false;
        }
        true
    }
    /// `func (c *Checker) checkForDisallowedESSymbolOperand` (checker.go:13056).
    pub(crate) fn check_for_disallowed_es_symbol_operand(
        &mut self,
        left: NodeId,
        right: NodeId,
        left_type: TypeId,
        right_type: TypeId,
        operator: ast::Kind,
    ) -> bool {
        let mut offending_symbol_operand: Option<NodeId> = None;
        if self.maybe_type_of_kind_considering_base_constraint(left_type, TypeFlags::ES_SYMBOL_LIKE)
        {
            offending_symbol_operand = Some(left);
        } else if self
            .maybe_type_of_kind_considering_base_constraint(right_type, TypeFlags::ES_SYMBOL_LIKE)
        {
            offending_symbol_operand = Some(right);
        }
        if let Some(offending) = offending_symbol_operand {
            self.error(
                Some(offending),
                &tsc_diagnostics::The_0_operator_cannot_be_applied_to_type_symbol,
                &[tsc_scanner::scanner::token_to_string(operator).to_string()],
            );
            return false;
        }
        true
    }

    /// `func (c *Checker) checkNaNEquality` (checker.go:13071).
    pub(crate) fn check_nan_equality(
        &mut self,
        error_node: NodeId,
        operator: ast::Kind,
        left: NodeId,
        right: NodeId,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((error_node).file_index());
        let is_left_nan = self.is_global_nan(ast::skip_parentheses(left, &nodes));
        let is_right_nan = self.is_global_nan(ast::skip_parentheses(right, &nodes));
        if is_left_nan || is_right_nan {
            let err = self.error(
                Some(error_node),
                &tsc_diagnostics::This_condition_will_always_return_0,
                &[tsc_scanner::scanner::token_to_string(
                    if operator == ast::Kind::EqualsEqualsEqualsToken
                        || operator == ast::Kind::EqualsEqualsToken
                    {
                        ast::Kind::FalseKeyword
                    } else {
                        ast::Kind::TrueKeyword
                    },
                )
                .to_string()],
            );
            if is_left_nan && is_right_nan {
                return;
            }
            let mut operator_string = String::new();
            if operator == ast::Kind::ExclamationEqualsEqualsToken
                || operator == ast::Kind::ExclamationEqualsToken
            {
                operator_string =
                    tsc_scanner::scanner::token_to_string(ast::Kind::ExclamationToken).to_string();
            }
            let mut location = left;
            if is_left_nan {
                location = right;
            }
            let expression = ast::skip_parentheses(location, &nodes);
            let mut entity_name = "...".to_string();
            if ast::is_entity_name_expression(&nodes[expression], &nodes) {
                entity_name = ast::entity_name_to_string(expression, &nodes, None);
            }
            let suggestion = format!("{operator_string}Number.isNaN({entity_name})");
            if let Some(err) = err {
                ast::diagnostic::lock_diagnostic(&err).add_related_info(Some(
                    create_diagnostic_for_node(
                        Some(location),
                        &nodes,
                        &tsc_diagnostics::Did_you_mean_0,
                        &[suggestion],
                    ),
                ));
            }
        }
    }

    /// `func (c *Checker) isGlobalNaN` (checker.go:13097).
    pub(crate) fn is_global_nan(&mut self, expr: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((expr).file_index());
        if ast::is_identifier(&nodes[expr]) && nodes[expr].text(&nodes) == "NaN" {
            let global_nan_symbol = self
                .get_global_nan_symbol_or_nil
                .clone()
                .map(|thunk| thunk(self))
                .flatten();
            return global_nan_symbol.is_some()
                && global_nan_symbol == Some(self.get_resolved_symbol(expr));
        }
        false
    }

    /// `func (c *Checker) isTypeEqualityComparableTo` (checker.go:13105).
    pub(crate) fn is_type_equality_comparable_to(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> bool {
        self.types_handle()
            .get(target)
            .flags
            .intersects(TypeFlags::NULLABLE)
            || self.is_type_comparable_to(source, target)
    }

    /// `func (c *Checker) checkTruthinessOfType` (checker.go:13109).
    pub(crate) fn check_truthiness_of_type(&mut self, t: TypeId, node: NodeId) -> TypeId {
        if self.types.get_ref(t).flags.intersects(TypeFlags::VOID) {
            self.error(
                Some(node),
                &tsc_diagnostics::An_expression_of_type_void_cannot_be_tested_for_truthiness,
                &[],
            );
            return t;
        }
        let semantics = self.get_syntactic_truthy_semantics(node);
        if semantics != PredicateSemantics::SOMETIMES {
            self.error(
                Some(node),
                if semantics == PredicateSemantics::ALWAYS {
                    &tsc_diagnostics::This_kind_of_expression_is_always_truthy
                } else {
                    &tsc_diagnostics::This_kind_of_expression_is_always_falsy
                },
                &[],
            );
        }
        t
    }

    /// `func (c *Checker) getSyntacticTruthySemantics` (checker.go:13130).
    pub(crate) fn get_syntactic_truthy_semantics(&mut self, node: NodeId) -> PredicateSemantics {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let node = ast::skip_outer_expressions(node, ast::outer_expression_kinds::ALL, &nodes);
        match nodes[node].kind {
            ast::Kind::NumericLiteral => {
                // Allow `while(0)` or `while(1)`
                let text = nodes[node].text(&nodes);
                if text == "0" || text == "1" {
                    return PredicateSemantics::SOMETIMES;
                }
                return PredicateSemantics::ALWAYS;
            }
            ast::Kind::ArrayLiteralExpression
            | ast::Kind::ArrowFunction
            | ast::Kind::BigIntLiteral
            | ast::Kind::ClassExpression
            | ast::Kind::FunctionExpression
            | ast::Kind::JsxElement
            | ast::Kind::JsxSelfClosingElement
            | ast::Kind::ObjectLiteralExpression
            | ast::Kind::RegularExpressionLiteral => {
                return PredicateSemantics::ALWAYS;
            }
            ast::Kind::VoidExpression | ast::Kind::NullKeyword => {
                return PredicateSemantics::NEVER;
            }
            ast::Kind::NoSubstitutionTemplateLiteral | ast::Kind::StringLiteral => {
                if nodes[node].text(&nodes) != "" {
                    return PredicateSemantics::ALWAYS;
                }
                return PredicateSemantics::NEVER;
            }
            ast::Kind::ConditionalExpression => {
                let conditional = nodes[node].as_conditional_expression();
                let when_true = conditional.when_true.expect("conditional whenTrue");
                let when_false = conditional.when_false.expect("conditional whenFalse");
                return self.get_syntactic_truthy_semantics(when_true)
                    | self.get_syntactic_truthy_semantics(when_false);
            }
            ast::Kind::Identifier => {
                if self.get_resolved_symbol(node) == self.undefined_symbol {
                    return PredicateSemantics::NEVER;
                }
            }
            _ => {}
        }
        PredicateSemantics::SOMETIMES
    }

    /// `func (c *Checker) checkNullishCoalesceOperands` (checker.go:13159).
    pub(crate) fn check_nullish_coalesce_operands(&mut self, left: NodeId, right: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((left).file_index());
        let grandparent = nodes[left].parent.and_then(|p| nodes[p].parent);
        if let Some(gp) = grandparent
            && ast::is_binary_expression(&nodes[gp])
        {
            let grandparent_left = nodes[gp].as_binary_expression().left;
            let grandparent_operator_token = nodes[gp].as_binary_expression().operator_token;
            if let (Some(gl), Some(got)) = (grandparent_left, grandparent_operator_token)
                && ast::is_binary_expression(&nodes[gl])
                && nodes[got].kind == ast::Kind::BarBarToken
            {
                self.grammar_error_on_node(
                    gl,
                    &tsc_diagnostics::X_0_and_1_operations_cannot_be_mixed_without_parentheses,
                    &[
                        tsc_scanner::scanner::token_to_string(ast::Kind::QuestionQuestionToken)
                            .to_string(),
                        tsc_scanner::scanner::token_to_string(nodes[got].kind).to_string(),
                    ],
                );
            }
        } else if ast::is_binary_expression(&nodes[left]) {
            let operator_token = nodes[left].as_binary_expression().operator_token;
            if let Some(ot) = operator_token
                && (nodes[ot].kind == ast::Kind::BarBarToken
                    || nodes[ot].kind == ast::Kind::AmpersandAmpersandToken)
            {
                self.grammar_error_on_node(
                    left,
                    &tsc_diagnostics::X_0_and_1_operations_cannot_be_mixed_without_parentheses,
                    &[
                        tsc_scanner::scanner::token_to_string(nodes[ot].kind).to_string(),
                        tsc_scanner::scanner::token_to_string(ast::Kind::QuestionQuestionToken)
                            .to_string(),
                    ],
                );
            }
        } else if ast::is_binary_expression(&nodes[right]) {
            let operator_token = nodes[right].as_binary_expression().operator_token;
            if let Some(ot) = operator_token
                && nodes[ot].kind == ast::Kind::AmpersandAmpersandToken
            {
                self.grammar_error_on_node(
                    right,
                    &tsc_diagnostics::X_0_and_1_operations_cannot_be_mixed_without_parentheses,
                    &[
                        tsc_scanner::scanner::token_to_string(ast::Kind::QuestionQuestionToken)
                            .to_string(),
                        tsc_scanner::scanner::token_to_string(nodes[ot].kind).to_string(),
                    ],
                );
            }
        }
        self.check_nullish_coalesce_operand_left(left);
    }

    /// `func (c *Checker) checkNullishCoalesceOperandLeft` (checker.go:13180).
    pub(crate) fn check_nullish_coalesce_operand_left(&mut self, left: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((left).file_index());
        let left_target =
            ast::skip_outer_expressions(left, ast::outer_expression_kinds::ALL, &nodes);
        let nullish_semantics = self.get_syntactic_nullishness_semantics(left_target);
        if nullish_semantics != PredicateSemantics::SOMETIMES {
            if nullish_semantics == PredicateSemantics::ALWAYS {
                self.error(
                    Some(left_target),
                    &tsc_diagnostics::This_expression_is_always_nullish,
                    &[],
                );
            } else {
                self.error(
                    Some(left_target),
                    &tsc_diagnostics::Right_operand_of_is_unreachable_because_the_left_operand_is_never_nullish,
                    &[],
                );
            }
        }
    }

    /// `func (c *Checker) getSyntacticNullishnessSemantics` (checker.go:13192).
    pub(crate) fn get_syntactic_nullishness_semantics(
        &mut self,
        node: NodeId,
    ) -> PredicateSemantics {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let node = ast::skip_outer_expressions(node, ast::outer_expression_kinds::ALL, &nodes);
        match nodes[node].kind {
            ast::Kind::AwaitExpression
            | ast::Kind::CallExpression
            | ast::Kind::TaggedTemplateExpression
            | ast::Kind::ElementAccessExpression
            | ast::Kind::MetaProperty
            | ast::Kind::NewExpression
            | ast::Kind::PropertyAccessExpression
            | ast::Kind::YieldExpression
            | ast::Kind::ThisKeyword => {
                return PredicateSemantics::SOMETIMES;
            }
            ast::Kind::BinaryExpression => {
                // List of operators that can produce null/undefined:
                // || ||= && &&= ?? ??=
                let binary = nodes[node].as_binary_expression();
                let operator_kind = binary
                    .operator_token
                    .map(|t| nodes[t].kind)
                    .unwrap_or(ast::Kind::Unknown);
                match operator_kind {
                    ast::Kind::BarBarToken
                    | ast::Kind::BarBarEqualsToken
                    | ast::Kind::AmpersandAmpersandToken
                    | ast::Kind::AmpersandAmpersandEqualsToken => {
                        return PredicateSemantics::SOMETIMES;
                    }
                    // For these operator kinds, the right operand is effectively controlling
                    ast::Kind::CommaToken | ast::Kind::EqualsToken => {
                        let right = binary.right.expect("binary right");
                        return self.get_syntactic_nullishness_semantics(right);
                    }
                    // For nullish coalescing: result is the left operand when left is non-null,
                    // or the right operand when left is null/undefined. The nullishness of the
                    // result combines both paths: the left's non-null path contributes Never,
                    // and when left can be null, the right's semantics are also included.
                    ast::Kind::QuestionQuestionToken | ast::Kind::QuestionQuestionEqualsToken => {
                        let left = binary.left.expect("binary left");
                        let right = binary.right.expect("binary right");
                        let left_semantics = self.get_syntactic_nullishness_semantics(left);
                        // The non-null path (left is non-null): left branch taken, result has Never bit
                        let mut result = left_semantics & PredicateSemantics::NEVER;
                        // The null path (left is null/undefined): right branch taken, result inherits right's semantics
                        if left_semantics.intersects(PredicateSemantics::ALWAYS) {
                            result = result | self.get_syntactic_nullishness_semantics(right);
                        }
                        return result;
                    }
                    _ => {}
                }
                return PredicateSemantics::NEVER;
            }
            ast::Kind::ConditionalExpression => {
                let conditional = nodes[node].as_conditional_expression();
                let when_true = conditional.when_true.expect("conditional whenTrue");
                let when_false = conditional.when_false.expect("conditional whenFalse");
                return self.get_syntactic_nullishness_semantics(when_true)
                    | self.get_syntactic_nullishness_semantics(when_false);
            }
            ast::Kind::NullKeyword => {
                return PredicateSemantics::ALWAYS;
            }
            ast::Kind::Identifier => {
                if self.get_resolved_symbol(node) == self.undefined_symbol {
                    return PredicateSemantics::ALWAYS;
                }
                return PredicateSemantics::SOMETIMES;
            }
            _ => {}
        }
        PredicateSemantics::NEVER
    }

    /// `func (c *Checker) isSideEffectFree` (checker.go:13255).
    pub(crate) fn is_side_effect_free(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let node = ast::skip_parentheses(node, &nodes);
        match nodes[node].kind {
            ast::Kind::Identifier
            | ast::Kind::StringLiteral
            | ast::Kind::RegularExpressionLiteral
            | ast::Kind::TaggedTemplateExpression
            | ast::Kind::TemplateExpression
            | ast::Kind::NoSubstitutionTemplateLiteral
            | ast::Kind::NumericLiteral
            | ast::Kind::BigIntLiteral
            | ast::Kind::TrueKeyword
            | ast::Kind::FalseKeyword
            | ast::Kind::NullKeyword
            | ast::Kind::UndefinedKeyword
            | ast::Kind::FunctionExpression
            | ast::Kind::ClassExpression
            | ast::Kind::ArrowFunction
            | ast::Kind::ArrayLiteralExpression
            | ast::Kind::ObjectLiteralExpression
            | ast::Kind::TypeOfExpression
            | ast::Kind::NonNullExpression
            | ast::Kind::JsxSelfClosingElement
            | ast::Kind::JsxElement => {
                return true;
            }
            ast::Kind::ConditionalExpression => {
                let conditional = nodes[node].as_conditional_expression();
                let when_true = conditional.when_true.expect("conditional whenTrue");
                let when_false = conditional.when_false.expect("conditional whenFalse");
                return self.is_side_effect_free(when_true) && self.is_side_effect_free(when_false);
            }
            ast::Kind::BinaryExpression => {
                let binary = nodes[node].as_binary_expression();
                if binary
                    .operator_token
                    .is_some_and(|t| nodes[t].kind.is_assignment_operator())
                {
                    return false;
                }
                let left = binary.left.expect("binary left");
                let right = binary.right.expect("binary right");
                return self.is_side_effect_free(left) && self.is_side_effect_free(right);
            }
            ast::Kind::PrefixUnaryExpression => {
                // Unary operators ~, !, +, and - have no side effects.
                // The rest do.
                match nodes[node].as_prefix_unary_expression().operator {
                    ast::Kind::ExclamationToken
                    | ast::Kind::PlusToken
                    | ast::Kind::MinusToken
                    | ast::Kind::TildeToken => {
                        return true;
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        false
    }

    /// `func (c *Checker) isIndirectCall` (checker.go:13283). Return true for
    /// "indirect calls", (i.e. `(0, x.f)(...)` or `(0, eval)(...)`), which
    /// prevents passing `this`.
    pub(crate) fn is_indirect_call(&mut self, node: Option<NodeId>) -> bool {
        let Some(node) = node else {
            return false;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_binary_expression(&nodes[node]) {
            return false;
        }
        let left = nodes[node].as_binary_expression().left;
        let right = nodes[node].as_binary_expression().right;
        let parent = nodes[node].parent;
        let Some(parent) = parent else {
            return false;
        };
        if !ast::is_parenthesized_expression(&nodes[parent]) {
            return false;
        }
        let Some(left) = left else {
            return false;
        };
        if !ast::is_numeric_literal(&nodes[left]) || nodes[left].text(&nodes) != "0" {
            return false;
        }
        let grandparent = nodes[parent].parent;
        let Some(grandparent) = grandparent else {
            return false;
        };
        let is_call_or_tagged = (ast::is_call_expression(&nodes[grandparent])
            && nodes[grandparent].expression() == Some(parent))
            || ast::is_tagged_template_expression(&nodes[grandparent]);
        if !is_call_or_tagged {
            return false;
        }
        let Some(right) = right else {
            return false;
        };
        ast::is_access_expression(&nodes[right])
            || (ast::is_identifier(&nodes[right]) && nodes[right].text(&nodes) == "eval")
    }

    /// `func (c *Checker) checkInstanceOfExpression` (checker.go:13291).
    pub(crate) fn check_instance_of_expression(
        &mut self,
        left: NodeId,
        right: NodeId,
        left_type: TypeId,
        right_type: TypeId,
        check_mode: CheckMode,
    ) -> TypeId {
        if left_type == self.silent_never_type || right_type == self.silent_never_type {
            return self.silent_never_type;
        }
        // TypeScript 1.0 spec (April 2014): 4.15.4
        // The instanceof operator requires the left operand to be of type Any, an object type, or a type parameter type,
        // and the right operand to be of type Any, a subtype of the 'Function' interface type, or have a call or construct signature.
        // The result is always of the Boolean primitive type.
        // NOTE: do not raise error if leftType is unknown as related error was already reported
        if !crate::checker_core::is_type_any(&self.types, left_type)
            && self.all_types_assignable_to_kind(left_type, TypeFlags::PRIMITIVE)
        {
            self.error(
                Some(left),
                &tsc_diagnostics::The_left_hand_side_of_an_instanceof_expression_must_be_of_type_any_an_object_type_or_a_type_parameter,
                &[],
            );
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((left).file_index());
        let signature = self.get_resolved_signature(
            nodes[left].parent.expect("instanceof parent"),
            None, /*candidatesOutArray*/
            check_mode,
        );
        if signature == Some(self.resolving_signature) {
            // CheckMode.SkipGenericFunctions is enabled and this is a call to a generic function that
            // returns a function type. We defer checking and return silentNeverType.
            return self.silent_never_type;
        }
        let signature = signature.expect("getResolvedSignature");
        // If rightType has a `[Symbol.hasInstance]` method that is not `(value: unknown) => boolean`, we
        // must check the expression as if it were a call to `right[Symbol.hasInstance](left)`. The call to
        // `getResolvedSignature`, below, will check that leftType is assignable to the type of the first
        // parameter.
        let return_type = self.get_return_type_of_signature(signature);
        // We also verify that the return type of the `[Symbol.hasInstance]` method is assignable to
        // `boolean`. According to the spec, the runtime will actually perform `ToBoolean` on the result,
        // but this is more type-safe.
        self.check_type_assignable_to(
            return_type,
            self.boolean_type,
            Some(right),
            Some(&tsc_diagnostics::An_object_s_Symbol_hasInstance_method_must_return_a_boolean_value_for_it_to_be_used_on_the_right_hand_side_of_an_instanceof_expression),
        );
        self.boolean_type
    }

    /// `func (c *Checker) checkInExpression` (checker.go:13321).
    pub(crate) fn check_in_expression(
        &mut self,
        left: NodeId,
        right: NodeId,
        left_type: TypeId,
        right_type: TypeId,
    ) -> TypeId {
        if left_type == self.silent_never_type || right_type == self.silent_never_type {
            return self.silent_never_type;
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((left).file_index());
        if ast::is_private_identifier(&nodes[left]) {
            if self.language_version
                < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET
                    .private_names_and_class_static_blocks
                || self.language_version
                    < crate::types::LANGUAGE_FEATURE_MINIMUM_TARGET
                        .class_and_class_element_decorators
                || !self.compiler_options.get_use_define_for_class_fields()
            {
                self.check_external_emit_helpers(left, ExternalEmitHelpers::CLASS_PRIVATE_FIELD_IN);
            }
            // Unlike in 'checkPrivateIdentifierExpression' we now have access to the RHS type
            // which provides us with the opportunity to emit more detailed errors
            if self.symbol_node_links.get(left).resolved_symbol.is_none()
                && ast::get_containing_class(left, &nodes).is_some()
            {
                let right_symbol = self.types.get_ref(right_type).symbol;
                let is_unchecked_js = self.is_unchecked_js_suggestion(
                    Some(left),
                    right_symbol,
                    true, /*excludeClasses*/
                );
                self.report_nonexistent_property(left, right_type, is_unchecked_js);
            }
        } else {
            // The type of the left operand must be assignable to string, number, or symbol.
            let non_null = self.check_non_null_type(left_type, left);
            self.check_type_assignable_to(
                non_null,
                self.string_number_symbol_type,
                Some(left),
                None,
            );
        }
        // The type of the right operand must be assignable to 'object'.
        let non_null_right = self.check_non_null_type(right_type, right);
        if self.check_type_assignable_to(non_null_right, self.non_primitive_type, Some(right), None)
        {
            // The {} type is assignable to the object type, yet {} might represent a primitive type. Here we
            // detect and error on {} that results from narrowing the unknown type, as well as intersections
            // that include {} (we know that the other types in such intersections are assignable to object
            // since we already checked for that).
            if self.has_empty_object_intersection(right_type) {
                let type_str = self.type_to_string(right_type);
                self.error(
                    Some(right),
                    &tsc_diagnostics::Type_0_may_represent_a_primitive_value_which_is_not_permitted_as_the_right_operand_of_the_in_operator,
                    &[type_str],
                );
            }
        }
        // The result is always of the Boolean primitive type.
        self.boolean_type
    }

    /// `func (c *Checker) hasEmptyObjectIntersection` (checker.go:13355).
    /// PORT: `someType(t, f)` is inlined — union constituents or the type
    /// itself.
    pub(crate) fn has_empty_object_intersection(&mut self, t: TypeId) -> bool {
        let constituents: Vec<TypeId> = {
            let ty = self.types.get_ref(t);
            if ty.flags.intersects(TypeFlags::UNION) {
                ty.as_union_type().union_or_intersection.types.to_vec()
            } else {
                vec![t]
            }
        };
        constituents.iter().any(|&t| {
            t == self.unknown_empty_object_type
                || (self
                    .types_handle()
                    .get(t)
                    .flags
                    .intersects(TypeFlags::INTERSECTION)
                    && {
                        let constraint = self.get_base_constraint_or_type(t);
                        self.is_empty_anonymous_object_type(constraint)
                    })
        })
    }

    /// `func (c *Checker) getExactOptionalUnassignableProperties` (checker.go:13361).
    pub(crate) fn get_exact_optional_unassignable_properties(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Vec<SymbolId> {
        if crate::checker_core::is_tuple_type(&self.types, source)
            && crate::checker_core::is_tuple_type(&self.types, target)
        {
            return Vec::new();
        }
        let props: Vec<SymbolId> = self.get_properties_of_type(target).to_vec();
        props
            .into_iter()
            .filter(|&target_prop| {
                let name = self.sym(target_prop).name.clone();
                let source_prop_type = self.get_type_of_property_of_type(source, &name);
                let target_type = self.get_type_of_symbol(target_prop);
                self.is_exact_optional_property_mismatch(source_prop_type, Some(target_type))
            })
            .collect()
    }

    /// `func (c *Checker) isExactOptionalPropertyMismatch` (checker.go:13370).
    pub(crate) fn is_exact_optional_property_mismatch(
        &mut self,
        source: Option<TypeId>,
        target: Option<TypeId>,
    ) -> bool {
        source.is_some()
            && target.is_some()
            && self.maybe_type_of_kind(source.unwrap(), TypeFlags::UNDEFINED)
            && (self
                .contains_missing_type
                .clone()
                .expect("contains_missing_type"))(self, target.unwrap())
    }

    /// `func (c *Checker) checkReferenceExpression` (checker.go:13374).
    pub(crate) fn check_reference_expression(
        &mut self,
        expr: NodeId,
        invalid_reference_message: &'static tsc_diagnostics::Message,
        invalid_optional_chain_message: &'static tsc_diagnostics::Message,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((expr).file_index());
        // References are combinations of identifiers, parentheses, and property accesses.
        let node = ast::skip_outer_expressions(
            expr,
            ast::outer_expression_kinds::ASSERTIONS | ast::outer_expression_kinds::PARENTHESES,
            &nodes,
        );
        if nodes[node].kind != ast::Kind::Identifier && !ast::is_access_expression(&nodes[node]) {
            self.error(Some(expr), invalid_reference_message, &[]);
            return false;
        }
        if nodes[node].flags.intersects(ast::NodeFlags::OPTIONAL_CHAIN) {
            self.error(Some(expr), invalid_optional_chain_message, &[]);
            return false;
        }
        true
    }
    /// `createObjectLiteralType` closure inside `checkObjectLiteral`
    /// (checker.go:13432). PORT: the Go closure captures the loop state; the
    /// port passes it explicitly.
    #[allow(clippy::too_many_arguments)]
    fn create_object_literal_type_for_check(
        &mut self,
        node: NodeId,
        properties_table: ast::SymbolTable,
        properties_array: &[SymbolId],
        offset: usize,
        object_flags: ObjectFlags,
        contextual_type: Option<TypeId>,
        in_destructuring_pattern: bool,
        pattern_with_computed_properties: bool,
        has_computed_string_property: bool,
        has_computed_number_property: bool,
        has_computed_symbol_property: bool,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut index_infos: Vec<IndexInfoId> = Vec::new();
        let is_readonly = self.is_const_context(node);
        if has_computed_string_property {
            let info = self.get_object_literal_index_info(
                is_readonly,
                &properties_array[offset.min(properties_array.len())..],
                self.string_type,
            );
            index_infos.push(self.index_info_arena.alloc(info));
        }
        if has_computed_number_property {
            let info = self.get_object_literal_index_info(
                is_readonly,
                &properties_array[offset.min(properties_array.len())..],
                self.number_type,
            );
            index_infos.push(self.index_info_arena.alloc(info));
        }
        if has_computed_symbol_property {
            let info = self.get_object_literal_index_info(
                is_readonly,
                &properties_array[offset.min(properties_array.len())..],
                self.es_symbol_type,
            );
            index_infos.push(self.index_info_arena.alloc(info));
        }
        let result = self.new_anonymous_type(
            nodes[node].symbol(),
            properties_table,
            &[],
            &[],
            &index_infos,
        );
        self.types_handle().get_mut(result).object_flags |= object_flags
            | ObjectFlags::OBJECT_LITERAL
            | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
        if contextual_type.is_none()
            && ast::is_in_js_file(Some(node), &nodes)
            && !ast::is_in_json_file(&nodes[node])
        {
            self.types_handle().get_mut(result).object_flags |= ObjectFlags::JS_LITERAL;
        }
        if pattern_with_computed_properties {
            self.types_handle().get_mut(result).object_flags |=
                ObjectFlags::OBJECT_LITERAL_PATTERN_WITH_COMPUTED_PROPERTIES;
        }
        if in_destructuring_pattern {
            self.pattern_for_type.write().unwrap().insert(result, node);
        }
        result
    }

    /// `func (c *Checker) checkObjectLiteral` (checker.go:13388).
    pub(crate) fn check_object_literal(&mut self, node: NodeId, check_mode: CheckMode) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Expando object literals have empty properties but filled exports
        let node_symbol = nodes[node].symbol();
        if nodes[node]
            .properties()
            .map(|p| p.is_empty())
            .unwrap_or(true)
            && node_symbol.is_some_and(|s| !self.sym(s).exports.is_empty())
        {
            let exports = self.sym(node_symbol.unwrap()).exports.clone();
            let result = self.new_anonymous_type(node_symbol, exports, &[], &[], &[]);
            if ast::is_in_js_file(Some(node), &nodes) && !ast::is_in_json_file(&nodes[node]) {
                self.types_handle().get_mut(result).object_flags |= ObjectFlags::JS_LITERAL;
            }
            // An expando object literal has no property children (len == 0), so there
            // is nothing to check here.
            return result;
        }
        self.check_node_deferred(node);
        let in_destructuring_pattern = ast::is_assignment_target(node, &nodes);
        // Grammar checking
        self.check_grammar_object_literal_expression(node, in_destructuring_pattern);
        let mut all_properties_table: Option<ast::SymbolTable> = None;
        if self.strict_null_checks {
            all_properties_table = Some(ast::SymbolTable::default());
        }
        let mut properties_table = ast::SymbolTable::default();
        let mut properties_array: Vec<SymbolId> = Vec::new();
        let mut spread = self.empty_object_type;
        self.push_cached_contextual_type(node);
        let contextual_type = self.get_apparent_type_of_contextual_type(node, ContextFlags::NONE);
        let mut contextual_type_has_pattern = false;
        if let Some(contextual_type) = contextual_type {
            if let Some(&pattern) = self.pattern_for_type.read().unwrap().get(&contextual_type)
                && (ast::is_object_binding_pattern(&nodes[pattern])
                    || ast::is_object_literal_expression(&nodes[pattern]))
            {
                contextual_type_has_pattern = true;
            }
        }
        let in_const_context = self.is_const_context(node);
        let mut check_flags = ast::checkflags::CheckFlags::NONE;
        if in_const_context {
            check_flags = ast::checkflags::CheckFlags::READONLY;
        }
        let mut object_flags = ObjectFlags::FRESH_LITERAL;
        let mut pattern_with_computed_properties = false;
        let mut has_computed_string_property = false;
        let mut has_computed_number_property = false;
        let mut has_computed_symbol_property = false;
        // Spreads may cause an early bail; ensure computed names are always checked (this is cached)
        // As otherwise they may not be checked until exports for the type at this position are retrieved,
        // which may never occur.
        let node_properties: Vec<NodeId> = nodes[node]
            .properties()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        for &elem in &node_properties {
            if let Some(name) = nodes[elem].name()
                && ast::is_computed_property_name(&nodes[name])
            {
                self.check_computed_property_name(name);
            }
        }
        let mut offset = 0usize;
        for &member_decl in &node_properties {
            // Go: `member` may be nil for spread assignments — those branches
            // never dereference it.
            let mut member = self.get_symbol_of_declaration(member_decl);
            let mut computed_name_type: Option<TypeId> = None;
            if let Some(name) = nodes[member_decl].name()
                && nodes[name].kind == ast::Kind::ComputedPropertyName
            {
                computed_name_type = Some(self.check_computed_property_name(name));
            }
            if ast::is_property_assignment(&nodes[member_decl])
                || ast::is_shorthand_property_assignment(&nodes[member_decl])
                || ast::is_object_literal_method(member_decl, &nodes)
            {
                let t = match nodes[member_decl].kind {
                    ast::Kind::PropertyAssignment => {
                        self.check_property_assignment(member_decl, check_mode)
                    }
                    ast::Kind::ShorthandPropertyAssignment => self
                        .check_shorthand_property_assignment(
                            member_decl,
                            in_destructuring_pattern,
                            check_mode,
                        ),
                    _ => self.check_object_literal_method(member_decl, check_mode),
                };
                object_flags |=
                    self.types.get_ref(t).object_flags & ObjectFlags::PROPAGATING_FLAGS;
                let mut name_type: Option<TypeId> = None;
                if let Some(computed) = computed_name_type
                    && crate::utilities::is_type_usable_as_property_name(&self.types, computed)
                {
                    name_type = Some(computed);
                }
                let member_flags = self.sym(member.expect("object literal member symbol")).flags;
                let member_name = self.sym(member.expect("object literal member symbol")).name.clone();
                let prop = if let Some(name_type) = name_type {
                    let text =
                        crate::utilities::get_property_name_from_type(&self.types, name_type);
                    self.new_symbol_ex(
                        ast::SymbolFlags::PROPERTY | member_flags,
                        &text,
                        check_flags | ast::checkflags::CheckFlags::LATE,
                    )
                } else {
                    self.new_symbol_ex(
                        ast::SymbolFlags::PROPERTY | member_flags,
                        &member_name,
                        check_flags,
                    )
                };
                if let Some(name_type) = name_type {
                    self.value_symbol_links.get(prop).name_type = Some(name_type);
                }
                if in_destructuring_pattern && self.has_default_value(member_decl) {
                    // If object literal is an assignment pattern and if the assignment pattern specifies a default value
                    // for the property, make the property optional.
                    self.sym_mut(prop).flags |= ast::SymbolFlags::OPTIONAL;
                } else if contextual_type_has_pattern
                    && !self
                        .types_handle()
                        .get(contextual_type.unwrap())
                        .object_flags
                        .intersects(ObjectFlags::OBJECT_LITERAL_PATTERN_WITH_COMPUTED_PROPERTIES)
                {
                    // If object literal is contextually typed by the implied type of a binding pattern, and if the
                    // binding pattern specifies a default value for the property, make the property optional.
                    let implied_prop =
                        self.get_property_of_type(contextual_type.unwrap(), &member_name);
                    if let Some(implied_prop) = implied_prop {
                        let implied_flags = self.sym(implied_prop).flags;
                        self.sym_mut(prop).flags |= implied_flags & ast::SymbolFlags::OPTIONAL;
                    } else if self
                        .get_index_info_of_type(contextual_type.unwrap(), self.string_type)
                        .is_none()
                    {
                        let member_str =
                            self.symbol_to_string(member.expect("object literal member symbol"));
                        let contextual_str = self.type_to_string(contextual_type.unwrap());
                        self.error(
                            nodes[member_decl].name(),
                            &tsc_diagnostics::Object_literal_may_only_specify_known_properties_and_0_does_not_exist_in_type_1,
                            &[member_str, contextual_str],
                        );
                    }
                }
                let member_declarations =
                    self.sym(member.expect("object literal member symbol")).declarations.clone();
                let member_parent = self.sym(member.expect("object literal member symbol")).parent;
                let member_value_declaration =
                    self.sym(member.expect("object literal member symbol")).value_declaration;
                self.sym_mut(prop).declarations = member_declarations;
                self.sym_mut(prop).parent = member_parent;
                self.sym_mut(prop).value_declaration = member_value_declaration;
                self.value_symbol_links.get(prop).resolved_type = Some(t);
                self.value_symbol_links.get(prop).target = member;
                member = Some(prop);
                if let Some(table) = all_properties_table.as_mut() {
                    table.set(member_name.clone().into(), prop);
                }
                if contextual_type.is_some()
                    && check_mode.intersects(CheckMode::INFERENTIAL)
                    && !check_mode.intersects(CheckMode::SKIP_CONTEXT_SENSITIVE)
                    && (ast::is_property_assignment(&nodes[member_decl])
                        || ast::is_method_declaration(&nodes[member_decl]))
                    && self.is_context_sensitive(member_decl)
                {
                    let inference_context = self.get_inference_context(node);
                    // In CheckMode.Inferential we should always have an inference context
                    let inference_node = if ast::is_property_assignment(&nodes[member_decl]) {
                        nodes[member_decl]
                            .initializer()
                            .expect("property assignment initializer")
                    } else {
                        member_decl
                    };
                    self.add_intra_expression_inference_site(inference_context, inference_node, t);
                }
            } else if nodes[member_decl].kind == ast::Kind::SpreadAssignment {
                if !properties_array.is_empty() {
                    let literal_type = self.create_object_literal_type_for_check(
                        node,
                        properties_table,
                        &properties_array,
                        offset,
                        object_flags,
                        contextual_type,
                        in_destructuring_pattern,
                        pattern_with_computed_properties,
                        has_computed_string_property,
                        has_computed_number_property,
                        has_computed_symbol_property,
                    );
                    spread = self.get_spread_type(
                        spread,
                        literal_type,
                        nodes[node].symbol(),
                        object_flags,
                        in_const_context,
                    );
                    properties_array = Vec::new();
                    properties_table = ast::SymbolTable::default();
                    has_computed_string_property = false;
                    has_computed_number_property = false;
                    has_computed_symbol_property = false;
                }
                let expr = nodes[member_decl]
                    .expression()
                    .expect("spread assignment expression");
                let expr_type = self.check_expression_ex(expr, check_mode & CheckMode::INFERENTIAL);
                let t = self.get_reduced_type(expr_type);
                if self.is_valid_spread_type(t) {
                    let merged_type =
                        self.try_merge_union_of_object_type_and_empty_object(t, in_const_context);
                    if let Some(table) = all_properties_table.as_ref() {
                        self.check_spread_prop_overrides(merged_type, table.clone(), member_decl);
                    }
                    offset = properties_array.len();
                    if self.is_error_type(spread) {
                        continue;
                    }
                    spread = self.get_spread_type(
                        spread,
                        merged_type,
                        nodes[node].symbol(),
                        object_flags,
                        in_const_context,
                    );
                } else {
                    self.error(
                        Some(member_decl),
                        &tsc_diagnostics::Spread_types_may_only_be_created_from_object_types,
                        &[],
                    );
                    spread = self.error_type;
                }
                continue;
            } else {
                // TypeScript 1.0 spec (April 2014)
                // A get accessor declaration is processed in the same manner as
                // an ordinary function declaration(section 6.1) with no parameters.
                // A set accessor declaration is processed in the same manner
                // as an ordinary function declaration with a single parameter and a Void return type.
                debug_assert!(
                    nodes[member_decl].kind == ast::Kind::GetAccessor
                        || nodes[member_decl].kind == ast::Kind::SetAccessor
                );
                self.check_node_deferred(member_decl);
            }
            if let Some(computed) = computed_name_type
                && !self
                    .types_handle()
                    .get(computed)
                    .flags
                    .intersects(TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE)
            {
                if self.is_type_assignable_to(computed, self.string_number_symbol_type) {
                    if self.is_type_assignable_to(computed, self.number_type) {
                        has_computed_number_property = true;
                    } else if self.is_type_assignable_to(computed, self.es_symbol_type) {
                        has_computed_symbol_property = true;
                    } else {
                        has_computed_string_property = true;
                    }
                    if in_destructuring_pattern {
                        pattern_with_computed_properties = true;
                    }
                }
            } else {
                let member = member.expect("object literal member symbol");
                properties_table.set(self.sym(member).name.clone().into(), member);
            }
            properties_array.push(member.expect("object literal member symbol"));
        }
        self.pop_contextual_type();
        if self.is_error_type(spread) {
            return self.error_type;
        }
        if spread != self.empty_object_type {
            if !properties_array.is_empty() {
                let literal_type = self.create_object_literal_type_for_check(
                    node,
                    properties_table,
                    &properties_array,
                    offset,
                    object_flags,
                    contextual_type,
                    in_destructuring_pattern,
                    pattern_with_computed_properties,
                    has_computed_string_property,
                    has_computed_number_property,
                    has_computed_symbol_property,
                );
                spread = self.get_spread_type(
                    spread,
                    literal_type,
                    nodes[node].symbol(),
                    object_flags,
                    in_const_context,
                );
                properties_array = Vec::new();
                properties_table = ast::SymbolTable::default();
                has_computed_string_property = false;
                has_computed_number_property = false;
            }
            // remap the raw emptyObjectType fed in at the top into a fresh empty object literal type, unique to this use site
            let empty_object_type = self.empty_object_type;
            // PORT: the Go `createObjectLiteralType` closure reads the (now
            // reset) loop state at call time; clone the captured state for the
            // `Rc<dyn Fn(&mut Checker, ..)>` mapper.
            let captured_table = properties_table.clone();
            let captured_array = properties_array.clone();
            let captured_object_flags = object_flags;
            return self.map_type(
                spread,
                Rc::new(move |c: &mut Checker, t: TypeId| {
                    if t == empty_object_type {
                        c.create_object_literal_type_for_check(
                            node,
                            captured_table.clone(),
                            &captured_array,
                            offset,
                            captured_object_flags,
                            contextual_type,
                            in_destructuring_pattern,
                            pattern_with_computed_properties,
                            has_computed_string_property,
                            has_computed_number_property,
                            has_computed_symbol_property,
                        )
                    } else {
                        t
                    }
                }),
            );
        }
        self.create_object_literal_type_for_check(
            node,
            properties_table,
            &properties_array,
            offset,
            object_flags,
            contextual_type,
            in_destructuring_pattern,
            pattern_with_computed_properties,
            has_computed_string_property,
            has_computed_number_property,
            has_computed_symbol_property,
        )
    }

    /// `func (c *Checker) checkContextualDeprecations` (checker.go:13600).
    pub(crate) fn check_contextual_deprecations(&mut self, node: NodeId) {
        let contextual_type = self.get_apparent_type_of_contextual_type(node, ContextFlags::NONE);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let properties: Vec<NodeId> = nodes[node]
            .properties()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        for property in properties {
            if self.is_canceled() {
                return;
            }
            if let Some(name) = nodes[property].name()
                && !ast::is_computed_property_name(&nodes[name])
            {
                self.check_deprecated_property(name, contextual_type);
            }
        }
    }

    /// `func (c *Checker) checkDeprecatedProperty` (checker.go:13612).
    pub(crate) fn check_deprecated_property(
        &mut self,
        name: NodeId,
        contextual_type: Option<TypeId>,
    ) {
        let Some(contextual_type) = contextual_type else {
            return;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((name).file_index());
        let name_text = nodes[name].text(&nodes).into_owned();
        let prop = self.get_property_of_type(contextual_type, &name_text);
        let Some(prop) = prop else {
            return;
        };
        if self.sym(prop).declarations.is_empty() {
            return;
        }
        if self.is_deprecated_symbol(prop) {
            let declarations = self.sym(prop).declarations.clone();
            self.add_deprecated_suggestion(name, &declarations, &name_text);
        }
    }

    /// `func (c *Checker) checkSpreadPropOverrides` (checker.go:13625).
    pub(crate) fn check_spread_prop_overrides(
        &mut self,
        t: TypeId,
        props: ast::SymbolTable,
        spread: NodeId,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((spread).file_index());
        let rights: Vec<SymbolId> = self.get_properties_of_type(t).to_vec();
        for right in rights {
            let right_flags = self.sym(right).flags;
            let right_check_flags = self.sym(right).check_flags;
            if !right_flags.intersects(ast::SymbolFlags::OPTIONAL)
                && !right_check_flags.intersects(ast::checkflags::CheckFlags::PARTIAL)
            {
                let right_name = self.sym(right).name.clone();
                if let Some(&left) = props.get(right_name.as_str()) {
                    let value_declaration = self.sym(left).value_declaration;
                    let left_name = self.sym(left).name.clone();
                    if let Some(diagnostic) = self.error(
                        value_declaration,
                        &tsc_diagnostics::X_0_is_specified_more_than_once_so_this_usage_will_be_overwritten,
                        &[left_name],
                    ) {
                        ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(
                            Some(create_diagnostic_for_node(
                                Some(spread),
                                &nodes,
                                &tsc_diagnostics::This_spread_always_overwrites_this_property,
                                &[],
                            )),
                        );
                    }
                }
            }
        }
    }

    /// `func (c *Checker) getSpreadType` (checker.go:13641).
    pub(crate) fn get_spread_type(
        &mut self,
        left: TypeId,
        right: TypeId,
        symbol: Option<SymbolId>,
        object_flags: ObjectFlags,
        readonly: bool,
    ) -> TypeId {
        if self
            .types_handle()
            .get_ref(left)
            .flags
            .intersects(TypeFlags::ANY)
            || self
                .types_handle()
                .get_ref(right)
                .flags
                .intersects(TypeFlags::ANY)
        {
            return self.any_type;
        }
        if self
            .types_handle()
            .get_ref(left)
            .flags
            .intersects(TypeFlags::UNKNOWN)
            || self
                .types_handle()
                .get_ref(right)
                .flags
                .intersects(TypeFlags::UNKNOWN)
        {
            return self.unknown_type;
        }
        if self
            .types_handle()
            .get_ref(left)
            .flags
            .intersects(TypeFlags::NEVER)
        {
            return right;
        }
        if self
            .types_handle()
            .get_ref(right)
            .flags
            .intersects(TypeFlags::NEVER)
        {
            return left;
        }
        let left = self.try_merge_union_of_object_type_and_empty_object(left, readonly);
        if self
            .types_handle()
            .get_ref(left)
            .flags
            .intersects(TypeFlags::UNION)
        {
            if self.check_cross_product_union(&[left, right]) {
                return self.map_type(
                    left,
                    Rc::new(move |c: &mut Checker, t: TypeId| {
                        c.get_spread_type(t, right, symbol, object_flags, readonly)
                    }),
                );
            }
            return self.error_type;
        }
        let right = self.try_merge_union_of_object_type_and_empty_object(right, readonly);
        if self
            .types_handle()
            .get_ref(right)
            .flags
            .intersects(TypeFlags::UNION)
        {
            if self.check_cross_product_union(&[left, right]) {
                return self.map_type(
                    right,
                    Rc::new(move |c: &mut Checker, t: TypeId| {
                        c.get_spread_type(left, t, symbol, object_flags, readonly)
                    }),
                );
            }
            return self.error_type;
        }
        if self.types.get_ref(right).flags.intersects(
            TypeFlags::BOOLEAN_LIKE
                | TypeFlags::NUMBER_LIKE
                | TypeFlags::BIG_INT_LIKE
                | TypeFlags::STRING_LIKE
                | TypeFlags::ENUM_LIKE
                | TypeFlags::NON_PRIMITIVE
                | TypeFlags::INDEX,
        ) {
            return left;
        }
        if self.is_generic_object_type(left) || self.is_generic_object_type(right) {
            if self.is_empty_object_type(left) {
                return right;
            }
            // When the left type is an intersection, we may need to merge the last constituent of the
            // intersection with the right type. For example when the left type is 'T & { a: string }'
            // and the right type is '{ b: string }' we produce 'T & { a: string, b: string }'.
            if self
                .types_handle()
                .get_ref(left)
                .flags
                .intersects(TypeFlags::INTERSECTION)
            {
                let types: Vec<TypeId> = self.types.get_ref(left).types().to_vec();
                let last_left = *types.last().expect("intersection constituents");
                if self.is_non_generic_object_type(last_left)
                    && self.is_non_generic_object_type(right)
                {
                    let mut new_types = types.clone();
                    let last = new_types.len() - 1;
                    new_types[last] =
                        self.get_spread_type(last_left, right, symbol, object_flags, readonly);
                    return self.get_intersection_type(&new_types);
                }
            }
            return self.get_intersection_type(&[left, right]);
        }
        let mut members = ast::SymbolTable::default();
        let mut skipped_private_members: rustc_hash::FxHashSet<String> =
            rustc_hash::FxHashSet::default();
        let index_infos: Vec<IndexInfoId> = if left == self.empty_object_type {
            self.get_index_infos_of_type(right)
        } else {
            self.get_union_index_infos(&[left, right])
        };
        let right_props: Vec<SymbolId> = self.get_properties_of_type(right).to_vec();
        for right_prop in right_props {
            let right_name = self.sym(right_prop).name.clone();
            if crate::utilities::get_declaration_modifier_flags_from_symbol(self, right_prop)
                .intersects(ast::ModifierFlags::PRIVATE | ast::ModifierFlags::PROTECTED)
            {
                skipped_private_members.insert(right_name);
            } else if self.is_spreadable_property(right_prop) {
                let spread_symbol = self.get_spread_symbol(right_prop, readonly);
                members.set(right_name.into(), spread_symbol);
            }
        }

        let left_props: Vec<SymbolId> = self.get_properties_of_type(left).to_vec();
        for left_prop in left_props {
            let left_name = self.sym(left_prop).name.clone();
            if skipped_private_members.contains(&left_name)
                || !self.is_spreadable_property(left_prop)
            {
                continue;
            }
            if let Some(&right_prop) = members.get(left_name.as_str()) {
                let right_type = self.get_type_of_symbol(right_prop);
                if self
                    .sym(right_prop)
                    .flags
                    .intersects(ast::SymbolFlags::OPTIONAL)
                {
                    let declarations = {
                        let mut d = self.sym(left_prop).declarations.clone();
                        d.extend(self.sym(right_prop).declarations.iter().copied());
                        d
                    };
                    let flags = ast::SymbolFlags::PROPERTY
                        | (self.sym(left_prop).flags & ast::SymbolFlags::OPTIONAL);
                    let result = self.new_symbol(flags, &left_name);
                    // Optimization: avoid calculating the union type if spreading into the exact same type.
                    // This is common, e.g. spreading one options bag into another where the bags have the
                    // same type, or have properties which overlap. If the unions are large, it may turn out
                    // to be expensive to perform subtype reduction.
                    let left_type = self.get_type_of_symbol(left_prop);
                    let left_type_without_undefined =
                        self.remove_missing_or_undefined_type(left_type);
                    let right_type_without_undefined =
                        self.remove_missing_or_undefined_type(right_type);
                    let resolved_type =
                        if left_type_without_undefined == right_type_without_undefined {
                            left_type
                        } else {
                            self.get_union_type_ex(
                                &[left_type, right_type_without_undefined],
                                UnionReduction::Subtype,
                                None,
                                None,
                            )
                        };
                    self.value_symbol_links.get(result).resolved_type = Some(resolved_type);
                    self.spread_links.get(result).left_spread = Some(left_prop);
                    self.spread_links.get(result).right_spread = Some(right_prop);
                    self.sym_mut(result).declarations = declarations;
                    let name_type = self.value_symbol_links.get(left_prop).name_type;
                    self.value_symbol_links.get(result).name_type = name_type;
                    members.set(left_name.clone().into(), result);
                }
            } else {
                let spread_symbol = self.get_spread_symbol(left_prop, readonly);
                members.set(left_name.into(), spread_symbol);
            }
        }
        // `core.SameMap(indexInfos, f)` — maps each info through
        // getIndexInfoWithReadonly; identity is preserved since the port maps
        // IndexInfo ids.
        let spread_index_infos: Vec<IndexInfoId> = index_infos
            .iter()
            .map(|&info| self.get_index_info_with_readonly(info, readonly))
            .collect();
        let spread = self.new_anonymous_type(symbol, members, &[], &[], &spread_index_infos);
        self.types_handle().get_mut(spread).object_flags |= ObjectFlags::OBJECT_LITERAL
            | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL
            | ObjectFlags::CONTAINS_SPREAD
            | object_flags;
        spread
    }

    /// `func (c *Checker) getIndexInfoWithReadonly` (checker.go:13751).
    pub(crate) fn get_index_info_with_readonly(
        &mut self,
        info: IndexInfoId,
        readonly: bool,
    ) -> IndexInfoId {
        let (is_readonly, key_type, value_type, declaration, components) = {
            let info = self.index_info_arena.get(info);
            (
                info.is_readonly,
                info.key_type,
                info.value_type,
                info.declaration,
                info.components.clone(),
            )
        };
        if is_readonly != readonly {
            return self.new_index_info(
                key_type.expect("index info key type"),
                value_type.expect("index info value type"),
                readonly,
                declaration,
                components,
            );
        }
        info
    }

    /// `func (c *Checker) isValidSpreadType` (checker.go:13758).
    pub(crate) fn is_valid_spread_type(&mut self, t: TypeId) -> bool {
        let mapped = self.map_type(
            t,
            Rc::new(|c: &mut Checker, t: TypeId| c.get_base_constraint_or_type(t)),
        );
        let s = self.remove_definitely_falsy_types(mapped);
        let s_flags = self.types.get_ref(s).flags;
        if s_flags.intersects(
            TypeFlags::ANY
                | TypeFlags::NON_PRIMITIVE
                | TypeFlags::OBJECT
                | TypeFlags::INSTANTIABLE_NON_PRIMITIVE,
        ) {
            return true;
        }
        if s_flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
            let types: Vec<TypeId> = self.types.get_ref(s).types().to_vec();
            return types.iter().all(|&t| self.is_valid_spread_type(t));
        }
        false
    }

    /// `func (c *Checker) getUnionIndexInfos` (checker.go:13764).
    pub(crate) fn get_union_index_infos(&mut self, types: &[TypeId]) -> Vec<IndexInfoId> {
        let source_infos = self.get_index_infos_of_type(types[0]);
        let mut result: Vec<IndexInfoId> = Vec::new();
        for info in source_infos {
            let index_type = self.index_info_arena.get(info).key_type;
            let Some(index_type) = index_type else {
                continue;
            };
            if types
                .iter()
                .all(|&t| self.get_index_info_of_type(t, index_type).is_some())
            {
                let value_types: Vec<TypeId> = types
                    .iter()
                    .map(|&t| {
                        self.get_index_type_of_type(t, index_type)
                            .unwrap_or(self.error_type)
                    })
                    .collect();
                let value_type = self.get_union_type(&value_types);
                let is_readonly = types.iter().any(|&t| {
                    self.get_index_info_of_type(t, index_type)
                        .is_some_and(|i| self.index_info_arena.get(i).is_readonly)
                });
                let info =
                    self.new_index_info(index_type, value_type, is_readonly, None, Vec::new());
                result.push(info);
            }
        }
        result
    }

    /// `func (c *Checker) isNonGenericObjectType` (checker.go:13780).
    pub(crate) fn is_non_generic_object_type(&mut self, t: TypeId) -> bool {
        self.types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::OBJECT)
            && !self.is_generic_mapped_type(t)
    }

    /// `func (c *Checker) tryMergeUnionOfObjectTypeAndEmptyObject` (checker.go:13784).
    pub(crate) fn try_merge_union_of_object_type_and_empty_object(
        &mut self,
        t: TypeId,
        readonly: bool,
    ) -> TypeId {
        if !self
            .types_handle()
            .get_ref(t)
            .flags
            .intersects(TypeFlags::UNION)
        {
            return t;
        }
        let types: Vec<TypeId> = self.types.get_ref(t).types().to_vec();
        if types
            .iter()
            .all(|&s| self.is_empty_object_type_or_spreads_into_empty_object(s))
        {
            if let Some(&empty) = types.iter().find(|&&s| self.is_empty_object_type(s)) {
                return empty;
            }
            return self.empty_object_type;
        }
        let first_type = types
            .iter()
            .copied()
            .find(|&s| !self.is_empty_object_type_or_spreads_into_empty_object(s));
        let Some(first_type) = first_type else {
            return t;
        };
        let second_type = types.iter().copied().find(|&s| {
            s != first_type && !self.is_empty_object_type_or_spreads_into_empty_object(s)
        });
        if second_type.is_some() {
            return t;
        }
        // gets the type as if it had been spread, but where everything in the spread is made optional
        let mut members = ast::SymbolTable::default();
        let props: Vec<SymbolId> = self.get_properties_of_type(first_type).to_vec();
        for prop in props {
            if crate::utilities::get_declaration_modifier_flags_from_symbol(self, prop)
                .intersects(ast::ModifierFlags::PRIVATE | ast::ModifierFlags::PROTECTED)
            {
                // do nothing, skip privates
            } else if self.is_spreadable_property(prop) {
                let prop_flags = self.sym(prop).flags;
                let is_setonly_accessor = prop_flags.intersects(ast::SymbolFlags::SET_ACCESSOR)
                    && !prop_flags.intersects(ast::SymbolFlags::GET_ACCESSOR);
                let flags = ast::SymbolFlags::PROPERTY | ast::SymbolFlags::OPTIONAL;
                let check_flags = self.sym(prop).check_flags & ast::checkflags::CheckFlags::LATE
                    | if readonly {
                        ast::checkflags::CheckFlags::READONLY
                    } else {
                        ast::checkflags::CheckFlags::NONE
                    };
                let prop_name = self.sym(prop).name.clone();
                let result = self.new_symbol_ex(flags, &prop_name, check_flags);
                if is_setonly_accessor {
                    self.value_symbol_links.get(result).resolved_type = Some(self.undefined_type);
                } else {
                    let prop_type = self.get_type_of_symbol(prop);
                    let resolved = self.add_optionality_ex(
                        prop_type, true, /*isProperty*/ true, /*isOptional*/
                    );
                    self.value_symbol_links.get(result).resolved_type = Some(resolved);
                }
                let declarations = self.sym(prop).declarations.clone();
                self.sym_mut(result).declarations = declarations;
                let name_type = self.value_symbol_links.get(prop).name_type;
                self.value_symbol_links.get(result).name_type = name_type;
                self.mapped_symbol_links.get(result).synthetic_origin = Some(prop);
                members.set(prop_name.into(), result);
            }
        }
        let first_symbol = self.types.get_ref(first_type).symbol;
        let index_infos = self.get_index_infos_of_type(first_type);
        let spread = self.new_anonymous_type(first_symbol, members, &[], &[], &index_infos);
        self.types_handle().get_mut(spread).object_flags |=
            ObjectFlags::OBJECT_LITERAL | ObjectFlags::CONTAINS_OBJECT_OR_ARRAY_LITERAL;
        spread
    }

    /// `func (c *Checker) isSpreadableProperty` (checker.go:13834). We
    /// approximate own properties as non-methods plus methods that are inside
    /// the object literal.
    pub(crate) fn is_spreadable_property(&mut self, prop: SymbolId) -> bool {
        let (flags, declarations) = {
            let s = self.sym(prop);
            (s.flags, s.declarations.clone())
        };
        (!declarations.iter().any(|&d| {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((d).file_index());

            ast::is_private_identifier_class_element_declaration(&nodes[d], &nodes)
        }) && !flags.intersects(
            ast::SymbolFlags::METHOD
                | ast::SymbolFlags::GET_ACCESSOR
                | ast::SymbolFlags::SET_ACCESSOR,
        )) || !declarations.iter().any(|&d| {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((d).file_index());
            ast::is_class_like(nodes[d].parent, &nodes)
        })
    }

    /// `func (c *Checker) getSpreadSymbol` (checker.go:13839).
    pub(crate) fn get_spread_symbol(&mut self, prop: SymbolId, readonly: bool) -> SymbolId {
        let prop_flags = self.sym(prop).flags;
        let is_setonly_accessor = prop_flags.intersects(ast::SymbolFlags::SET_ACCESSOR)
            && !prop_flags.intersects(ast::SymbolFlags::GET_ACCESSOR);
        if !is_setonly_accessor && readonly == self.is_readonly_symbol(prop) {
            return prop;
        }
        let flags = ast::SymbolFlags::PROPERTY | (prop_flags & ast::SymbolFlags::OPTIONAL);
        let check_flags = self.sym(prop).check_flags & ast::checkflags::CheckFlags::LATE
            | if readonly {
                ast::checkflags::CheckFlags::READONLY
            } else {
                ast::checkflags::CheckFlags::NONE
            };
        let prop_name = self.sym(prop).name.clone();
        let result = self.new_symbol_ex(flags, &prop_name, check_flags);
        if is_setonly_accessor {
            self.value_symbol_links.get(result).resolved_type = Some(self.undefined_type);
        } else {
            let prop_type = self.get_type_of_symbol(prop);
            self.value_symbol_links.get(result).resolved_type = Some(prop_type);
        }
        let declarations = self.sym(prop).declarations.clone();
        self.sym_mut(result).declarations = declarations;
        let name_type = self.value_symbol_links.get(prop).name_type;
        self.value_symbol_links.get(result).name_type = name_type;
        self.mapped_symbol_links.get(result).synthetic_origin = Some(prop);
        result
    }

    /// `func (c *Checker) isEmptyObjectTypeOrSpreadsIntoEmptyObject` (checker.go:13858).
    pub(crate) fn is_empty_object_type_or_spreads_into_empty_object(&mut self, t: TypeId) -> bool {
        self.is_empty_object_type(t)
            || self.types.get_ref(t).flags.intersects(
                TypeFlags::NULL
                    | TypeFlags::UNDEFINED
                    | TypeFlags::BOOLEAN_LIKE
                    | TypeFlags::NUMBER_LIKE
                    | TypeFlags::BIG_INT_LIKE
                    | TypeFlags::STRING_LIKE
                    | TypeFlags::ENUM_LIKE
                    | TypeFlags::NON_PRIMITIVE
                    | TypeFlags::INDEX,
            )
    }

    /// `func (c *Checker) hasDefaultValue` (checker.go:13862).
    pub(crate) fn has_default_value(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        (ast::is_binding_element(&nodes[node]) && nodes[node].initializer().is_some())
            || (ast::is_property_assignment(&nodes[node])
                && nodes[node]
                    .initializer()
                    .is_some_and(|i| self.has_default_value(i)))
            || (ast::is_shorthand_property_assignment(&nodes[node])
                && nodes[node]
                    .as_shorthand_property_assignment()
                    .object_assignment_initializer
                    .is_some())
            || (ast::is_binary_expression(&nodes[node])
                && nodes[node]
                    .as_binary_expression()
                    .operator_token
                    .is_some_and(|t| nodes[t].kind == ast::Kind::EqualsToken))
    }

    /// `func (c *Checker) isConstContext` (checker.go:13869).
    pub(crate) fn is_const_context(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent;
        let parent_is =
            |kinds: &[ast::Kind]| parent.is_some_and(|p| kinds.contains(&nodes[p].kind));

        parent.is_some_and(|p| ast::is_const_assertion(&nodes[p], &nodes))
            || self.is_inline_import_attributes(node)
            || (self.is_valid_const_assertion_argument(node) && {
                let ct = self.get_contextual_type(node, ContextFlags::NONE);
                self.is_const_type_variable(ct, 0)
            })
            || (parent_is(&[
                ast::Kind::ParenthesizedExpression,
                ast::Kind::ArrayLiteralExpression,
                ast::Kind::SpreadElement,
            ]) && self.is_const_context(parent.unwrap()))
            || (parent_is(&[
                ast::Kind::PropertyAssignment,
                ast::Kind::ShorthandPropertyAssignment,
                ast::Kind::TemplateSpan,
            ]) && nodes[parent.unwrap()]
                .parent
                .is_some_and(|gp| self.is_const_context(gp)))
    }

    /// `func (c *Checker) isInlineImportAttributes` (checker.go:13878).
    pub(crate) fn is_inline_import_attributes(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_object_literal_expression(&nodes[node]) {
            return false;
        }
        let Some(property) = nodes[node].parent else {
            return false;
        };
        if !ast::is_property_assignment(&nodes[property])
            || nodes[property].initializer() != Some(node)
        {
            return false;
        }
        let Some(name) = nodes[property].name() else {
            return false;
        };
        if (!ast::is_identifier(&nodes[name]) && !ast::is_string_literal_like(&nodes[name]))
            || nodes[name].text(&nodes).as_ref() != "with"
        {
            return false;
        }
        let Some(options) = nodes[property].parent else {
            return false;
        };
        if !ast::is_object_literal_expression(&nodes[options]) {
            return false;
        }
        let import_call = ast::find_ancestor(
            Some(options),
            &nodes,
            &mut |n: &ast::Node, nodes: &[ast::Node]| ast::is_import_call(n, nodes),
        );
        import_call.is_some_and(|import_call| {
            nodes[import_call].arguments().is_some_and(|args| {
                args.len() > 1 && ast::skip_parentheses(args[1], &nodes) == options
            })
        })
    }

    /// `func (c *Checker) isValidConstAssertionArgument` (checker.go:13894).
    pub(crate) fn is_valid_const_assertion_argument(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::StringLiteral
            | ast::Kind::NoSubstitutionTemplateLiteral
            | ast::Kind::NumericLiteral
            | ast::Kind::BigIntLiteral
            | ast::Kind::TrueKeyword
            | ast::Kind::FalseKeyword
            | ast::Kind::ArrayLiteralExpression
            | ast::Kind::ObjectLiteralExpression
            | ast::Kind::TemplateExpression => true,
            ast::Kind::ParenthesizedExpression => {
                let expr = nodes[node].expression().expect("parenthesized expression");
                self.is_valid_const_assertion_argument(expr)
            }
            ast::Kind::PrefixUnaryExpression => {
                let unary = nodes[node].as_prefix_unary_expression();
                let op = unary.operator;
                let arg = unary.operand.expect("unary operand");
                (op == ast::Kind::MinusToken
                    && (nodes[arg].kind == ast::Kind::NumericLiteral
                        || nodes[arg].kind == ast::Kind::BigIntLiteral))
                    || (op == ast::Kind::PlusToken && nodes[arg].kind == ast::Kind::NumericLiteral)
            }
            ast::Kind::PropertyAccessExpression | ast::Kind::ElementAccessExpression => {
                let expr = ast::skip_parentheses(
                    nodes[node].expression().expect("access expression"),
                    &nodes,
                );
                let symbol = if ast::is_entity_name_expression(&nodes[expr], &nodes) {
                    self.resolve_entity_name(
                        Some(expr),
                        ast::SymbolFlags::VALUE,
                        true, /*ignoreErrors*/
                        false,
                        None,
                    )
                } else {
                    None
                };
                symbol.is_some_and(|s| self.sym(s).flags.intersects(ast::SymbolFlags::ENUM))
            }
            _ => false,
        }
    }

    /// `func (c *Checker) isConstTypeVariable` (checker.go:13916).
    pub(crate) fn is_const_type_variable(&mut self, t: Option<TypeId>, depth: usize) -> bool {
        let Some(t) = t else {
            return false;
        };
        if depth >= 5 {
            return false;
        }
        let flags = self.types.get_ref(t).flags;
        if flags.intersects(TypeFlags::TYPE_PARAMETER) {
            let Some(symbol) = self.types.get_ref(t).symbol else {
                return false;
            };
            let declarations = self.sym(symbol).declarations.clone();
            return declarations.iter().any(|&d| {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((d).file_index());
                ast::has_syntactic_modifier(&nodes[d], ast::ModifierFlags::CONST)
            });
        }
        if flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
            let types: Vec<TypeId> = self.types.get_ref(t).types().to_vec();
            return types
                .iter()
                .any(|&s| self.is_const_type_variable(Some(s), depth));
        }
        if flags.intersects(TypeFlags::INDEXED_ACCESS) {
            let __arena___guard_object_type = self.types.clone();
            let __guard_object_type = __arena___guard_object_type.get(t).clone();
            let object_type = __guard_object_type.as_indexed_access_type().object_type;
            return self.is_const_type_variable(object_type, depth + 1);
        }
        if flags.intersects(TypeFlags::CONDITIONAL) {
            let constraint = self.get_constraint_of_conditional_type(t);
            return self.is_const_type_variable(constraint, depth + 1);
        }
        if flags.intersects(TypeFlags::SUBSTITUTION) {
            let __arena___guard_base_type = self.types.clone();
            let __guard_base_type = __arena___guard_base_type.get(t).clone();
            let base_type = __guard_base_type.as_substitution_type().base_type;
            return self.is_const_type_variable(base_type, depth);
        }
        if self
            .types_handle()
            .get_ref(t)
            .object_flags
            .intersects(ObjectFlags::MAPPED)
        {
            let type_variable = self.get_homomorphic_type_variable(t);
            return type_variable.is_some_and(|v| self.is_const_type_variable(Some(v), depth));
        }
        if self.is_generic_tuple_type(t) {
            let element_types = self.get_element_types(t);
            let element_infos: Vec<TupleElementInfo> = self
                .types_handle()
                .get_ref(self.types_handle().target_tuple_type(t).unwrap())
                .as_tuple_type()
                .element_infos
                .to_vec();
            for (i, &s) in element_types.iter().enumerate() {
                if element_infos
                    .get(i)
                    .is_some_and(|info| info.flags.intersects(ElementFlags::VARIADIC))
                    && self.is_const_type_variable(Some(s), depth)
                {
                    return true;
                }
            }
        }
        false
    }
    /// `func (c *Checker) checkPropertyAssignment` (checker.go:13944).
    pub(crate) fn check_property_assignment(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        // Do not use hasDynamicName here, because that returns false for well known symbols.
        // We want to perform checkComputedPropertyName for all computed properties, including
        // well known symbols.
        if let Some(name) = nodes[node].name()
            && ast::is_computed_property_name(&nodes[name])
        {
            self.check_computed_property_name(name);
        }
        let initializer = nodes[node]
            .initializer()
            .expect("property assignment initializer");
        let initializer_type = self.check_expression_for_mutable_location(initializer, check_mode);
        if let Some(type_node) = nodes[node].type_() {
            let t = self.get_type_from_type_node(type_node);
            self.check_type_assignable_to_and_optionally_elaborate(
                initializer_type,
                t,
                Some(node),
                Some(initializer),
                None, /*headMessage*/
                None,
            );
            return t;
        }
        initializer_type
    }

    /// `func (c *Checker) checkShorthandPropertyAssignment` (checker.go:13960).
    pub(crate) fn check_shorthand_property_assignment(
        &mut self,
        node: NodeId,
        in_destructuring_pattern: bool,
        check_mode: CheckMode,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut expr: Option<NodeId> = None;
        if !in_destructuring_pattern {
            expr = nodes[node]
                .as_shorthand_property_assignment()
                .object_assignment_initializer;
        }
        let expr = expr.or_else(|| nodes[node].name()).expect("shorthand name");
        let expression_type = self.check_expression_for_mutable_location(expr, check_mode);
        if let Some(type_node) = nodes[node].type_() {
            let t = self.get_type_from_type_node(type_node);
            self.check_type_assignable_to_and_optionally_elaborate(
                expression_type,
                t,
                Some(node),
                Some(expr),
                None, /*headMessage*/
                None,
            );
            return t;
        }
        expression_type
    }

    /// `func (c *Checker) isInPropertyInitializerOrClassStaticBlock` (checker.go:13977).
    pub(crate) fn is_in_property_initializer_or_class_static_block(
        &mut self,
        node: NodeId,
        ignore_arrow_functions: bool,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        ast::find_ancestor_or_quit(
            Some(node),
            &nodes,
            &mut |n: &ast::Node, nodes: &[ast::Node]| match n.kind {
                ast::Kind::PropertyDeclaration | ast::Kind::ClassStaticBlockDeclaration => {
                    ast::FindAncestorResult::True
                }
                ast::Kind::TypeQuery | ast::Kind::JsxClosingElement => {
                    ast::FindAncestorResult::Quit
                }
                ast::Kind::ArrowFunction => {
                    if ignore_arrow_functions {
                        ast::FindAncestorResult::False
                    } else {
                        ast::FindAncestorResult::Quit
                    }
                }
                ast::Kind::Block => {
                    let parent_is_function_like = n.parent.is_some_and(|p| {
                        ast::is_function_like_declaration(Some(p), nodes)
                            && nodes[p].kind != ast::Kind::ArrowFunction
                    });
                    if parent_is_function_like {
                        ast::FindAncestorResult::Quit
                    } else {
                        ast::FindAncestorResult::False
                    }
                }
                _ => ast::FindAncestorResult::False,
            },
        )
        .is_some()
    }

    /// `func (c *Checker) getNarrowedTypeOfSymbol` (checker.go:13994).
    pub(crate) fn get_narrowed_type_of_symbol(
        &mut self,
        symbol: SymbolId,
        location: NodeId,
    ) -> TypeId {
        let mut t = self.get_type_of_symbol(symbol);
        let declaration = self.sym(symbol).value_declaration;
        if let Some(declaration) = declaration {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((declaration).file_index());
            // If we have a non-rest binding element with no initializer declared as a const variable or a const-like
            // parameter (a parameter for which there are no assignments in the function body), and if the parent type
            // for the destructuring is a union type, one or more of the binding elements may represent discriminant
            // properties, and we want the effects of conditional checks on such discriminants to affect the types of
            // other binding elements from the same destructuring. Consider:
            //
            //   type Action =
            //       | { kind: 'A', payload: number }
            //       | { kind: 'B', payload: string };
            //
            //   function f({ kind, payload }: Action) {
            //       if (kind === 'A') {
            //           payload.toFixed();
            //       }
            //       if (kind === 'B') {
            //           payload.toUpperCase();
            //       }
            //   }
            //
            // Above, we want the conditional checks on 'kind' to affect the type of 'payload'. To facilitate this, we use
            // the binding pattern AST instance for '{ kind, payload }' as a pseudo-reference and narrow this reference
            // as if it occurred in the specified location. We then recompute the narrowed binding element type by
            // destructuring from the narrowed parent type.
            if ast::is_binding_element(&nodes[declaration])
                && nodes[declaration].initializer().is_none()
                && !crate::utilities::has_dot_dot_dot_token(&nodes[declaration], &nodes)
                && nodes[declaration]
                    .parent
                    .is_some_and(|p| nodes[p].elements().is_some_and(|e| e.len() >= 2))
            {
                let root_declaration = ast::get_root_declaration(declaration, &nodes);
                let root_initializer = nodes[root_declaration].initializer();
                // `location` can be in a different file than `declaration` —
                // resolve it in its own arena for the descendant walk.
                let loc_nodes = __program.nodes((location).file_index());
                // Avoid declaration circularity without blocking binding defaults or nested callbacks.
                let is_descendant_of_initializer = root_initializer.is_some()
                    && ast::is_node_descendant_of(Some(location), root_initializer, &loc_nodes)
                    && self.get_control_flow_container(declaration)
                        == self.get_control_flow_container(location);
                if !is_descendant_of_initializer {
                    let parent = nodes[declaration].parent.and_then(|p| nodes[p].parent);
                    let is_var_or_param = (ast::is_variable_declaration(&nodes[root_declaration])
                        && self
                            .get_combined_node_flags_cached(root_declaration)
                            .intersects(ast::NodeFlags::CONSTANT))
                        || ast::is_parameter_declaration(&nodes[root_declaration]);
                    if let (Some(parent), true) = (parent, is_var_or_param) {
                        let links_flags = self.node_links.get(parent).flags;
                        if !links_flags.intersects(NodeCheckFlags::IN_CHECK_IDENTIFIER) {
                            self.node_links
                                .get(parent)
                                .flags
                                .insert(NodeCheckFlags::IN_CHECK_IDENTIFIER);
                            let parent_type =
                                self.get_type_for_binding_element_parent(parent, CheckMode::NORMAL);
                            let parent_type_constraint = parent_type.map(|pt| {
                                self.map_type(
                                    pt,
                                    Rc::new(|c: &mut Checker, t: TypeId| {
                                        c.get_base_constraint_or_type(t)
                                    }),
                                )
                            });
                            // Guard parent-type resolution only; flow analysis should allow re-entrant narrowing
                            self.node_links
                                .get(parent)
                                .flags
                                .remove(NodeCheckFlags::IN_CHECK_IDENTIFIER);
                            if let Some(constraint) = parent_type_constraint
                                && self
                                    .types_handle()
                                    .get(constraint)
                                    .flags
                                    .intersects(TypeFlags::UNION)
                                && !(ast::is_parameter_declaration(&nodes[root_declaration])
                                    && self.is_some_symbol_assigned(root_declaration))
                            {
                                let pattern = nodes[declaration].parent.expect("binding parent");
                                // The flow graph lives in `location`'s file;
                                // the pattern is a pseudo-reference in the
                                // declaration's file.
                                let flow_node =
                                    crate::flow::get_flow_node_of_node(&loc_nodes, location);
                                let narrowed_type = self.get_flow_type_of_reference_ex_ctx(
                                    pattern,
                                    constraint,
                                    Some(constraint),
                                    None, /*flowContainer*/
                                    flow_node,
                                    Some(location),
                                );
                                if self
                                    .types_handle()
                                    .get(narrowed_type)
                                    .flags
                                    .intersects(TypeFlags::NEVER)
                                {
                                    t = self.never_type;
                                } else {
                                    // Destructurings are validated against the parent type elsewhere. Here we disable tuple bounds
                                    // checks because the narrowed type may have lower arity than the full parent type. For example,
                                    // for the declaration [x, y]: [1, 2] | [3], we may have narrowed the parent type to just [3].
                                    t = self.get_binding_element_type_from_parent_type(
                                        declaration,
                                        narrowed_type,
                                        true, /*noTupleBoundsCheck*/
                                    );
                                }
                            }
                        }
                    }
                }
            // If we have a const-like parameter with no type annotation or initializer, and if the parameter is contextually
            // typed by a signature with a single rest parameter of a union of tuple types, one or more of the parameters may
            // represent discriminant tuple elements, and we want the effects of conditional checks on such discriminants to
            // affect the types of other parameters in the same parameter list. Consider:
            //
            //   type Action = [kind: 'A', payload: number] | [kind: 'B', payload: string];
            //
            //   const f: (...args: Action) => void = (kind, payload) => {
            //       if (kind === 'A') {
            //           payload.toFixed();
            //       }
            //       if (kind === 'B') {
            //           payload.toUpperCase();
            //       }
            //   }
            //
            // Above, we want the conditional checks on 'kind' to affect the type of 'payload'. To facilitate this, we use
            // the arrow function AST node for '(kind, payload) => ...' as a pseudo-reference and narrow this reference as
            // if it occurred in the specified location. We then recompute the narrowed parameter type by indexing into the
            // narrowed tuple type.
            } else if ast::is_parameter_declaration(&nodes[declaration])
                && nodes[declaration].type_().is_none()
                && nodes[declaration].initializer().is_none()
                && !crate::utilities::has_dot_dot_dot_token(&nodes[declaration], &nodes)
            {
                let fn_node = nodes[declaration].parent.expect("parameter parent");
                let fn_params: Vec<NodeId> = nodes[fn_node]
                    .parameters()
                    .map(|p| p.to_vec())
                    .unwrap_or_default();
                if fn_params.len() >= 2
                    && self.is_context_sensitive_function_or_object_literal_method(fn_node)
                {
                    let contextual_signature = self.get_contextual_signature(fn_node);
                    let context_sensitive = contextual_signature.is_some_and(|sig| {
                        let s = self.signature_arena.get(sig);
                        s.parameters().len() == 1
                            && crate::checker_c::signature_has_rest_parameter(s)
                    });
                    if let (Some(contextual_signature), true) =
                        (contextual_signature, context_sensitive)
                    {
                        let context = self.get_inference_context(fn_node);
                        let mapper = context
                            .and_then(|ctx| self.inference_contexts[ctx.index()].non_fixing_mapper);
                        let rest_param_symbol =
                            self.signature_arena.get(contextual_signature).parameters()[0];
                        let rest_sym_ty = self.get_type_of_symbol(rest_param_symbol);
                        let rest_inst = self.instantiate_type(rest_sym_ty, mapper);
                        let rest_type = self.get_reduced_apparent_type(rest_inst);
                        let rest_is_union_of_tuples = {
                            let rt = self.types.get_ref(rest_type);
                            rt.flags.intersects(TypeFlags::UNION)
                                && rt
                                    .types()
                                    .iter()
                                    .all(|&s| crate::checker_core::is_tuple_type(&self.types, s))
                        };
                        let any_param_assigned =
                            fn_params.iter().any(|&p| self.is_some_symbol_assigned(p));
                        if rest_is_union_of_tuples && !any_param_assigned {
                            // The flow graph lives in `location`'s file;
                            // `fn_node` is a pseudo-reference in the
                            // declaration's file.
                            let loc_nodes = __program.nodes((location).file_index());
                            let flow_node =
                                crate::flow::get_flow_node_of_node(&loc_nodes, location);
                            let narrowed_type = self.get_flow_type_of_reference_ex_ctx(
                                fn_node,
                                rest_type,
                                Some(rest_type),
                                None, /*flowContainer*/
                                flow_node,
                                Some(location),
                            );
                            let index = fn_params
                                .iter()
                                .position(|&p| p == declaration)
                                .map(|i| i as i64)
                                .unwrap_or(-1)
                                - if ast::get_this_parameter(&nodes[fn_node], &nodes).is_some() {
                                    1
                                } else {
                                    0
                                };
                            let index_type =
                                self.get_number_literal_type(tsc_jsnum::Number(index as f64));
                            t = self.get_indexed_access_type(narrowed_type, index_type);
                        }
                    }
                }
            }
        }
        t
    }

    /// `func (c *Checker) isReadonlyAssignmentDeclaration` (checker.go:14100).
    pub(crate) fn is_readonly_assignment_declaration(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_call_expression(&nodes[node]) {
            return false;
        }
        let args: Vec<NodeId> = nodes[node]
            .arguments()
            .map(|a| a.to_vec())
            .unwrap_or_default();
        let property_descriptor_type = self.check_expression_cached(args[2]);
        if let Some(value_type) =
            self.get_type_of_property_of_type(property_descriptor_type, "value")
        {
            let _ = value_type;
            if let Some(writable_prop) =
                self.get_property_of_type(property_descriptor_type, "writable")
            {
                let writable_type;
                let value_declaration = self.sym(writable_prop).value_declaration;
                if let Some(vd) = value_declaration
                    && ast::is_property_assignment(&self.program_nodes(vd)[vd])
                {
                    let __program = self.program.clone().expect("program");
                    let initializer = __program.nodes((vd).file_index())[vd]
                        .initializer()
                        .expect("property assignment initializer");
                    writable_type = self.check_expression(initializer);
                } else {
                    writable_type = self.get_type_of_symbol(writable_prop);
                }
                return self
                    .types_handle()
                    .get(writable_type)
                    .flags
                    .intersects(TypeFlags::BOOLEAN_LITERAL)
                    && !crate::checker_d::get_boolean_literal_value(&self.types, writable_type);
            }
            return true;
        }
        self.get_type_of_property_of_type(property_descriptor_type, "set")
            .is_none()
    }

    /// `func (c *Checker) isReadonlySymbol` (checker.go:14120).
    ///
    /// The following symbols are considered read-only:
    /// Properties with a 'readonly' modifier
    /// Variables declared with 'const'
    /// Get accessors without matching set accessors
    /// Enum members
    /// Object.defineProperty assignments with writable false or no setter
    /// Unions and intersections of the above (unions and intersections eagerly set isReadonly on creation)
    pub fn is_readonly_symbol(&mut self, symbol: SymbolId) -> bool {
        let (flags, check_flags, declarations) = {
            let s = self.sym(symbol);
            (s.flags, s.check_flags, s.declarations.clone())
        };
        check_flags.intersects(ast::checkflags::CheckFlags::READONLY)
            || (flags.intersects(ast::SymbolFlags::PROPERTY)
                && crate::utilities::get_declaration_modifier_flags_from_symbol(self, symbol)
                    .intersects(ast::ModifierFlags::READONLY))
            || (flags.intersects(ast::SymbolFlags::VARIABLE)
                && self
                    .get_declaration_node_flags_from_symbol(symbol)
                    .intersects(ast::NodeFlags::CONSTANT))
            || (flags.intersects(ast::SymbolFlags::ACCESSOR)
                && !flags.intersects(ast::SymbolFlags::SET_ACCESSOR))
            || flags.intersects(ast::SymbolFlags::ENUM_MEMBER)
            || declarations
                .iter()
                .any(|&d| self.is_readonly_assignment_declaration(d))
    }

    /// `func (c *Checker) checkObjectLiteralMethod` (checker.go:14136).
    pub(crate) fn check_object_literal_method(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        // Grammar checking
        self.check_grammar_method(node);
        // Do not use hasDynamicName here, because that returns false for well known symbols.
        // We want to perform checkComputedPropertyName for all computed properties, including
        // well known symbols.
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(name) = nodes[node].name()
            && ast::is_computed_property_name(&nodes[name])
        {
            self.check_computed_property_name(name);
        }
        let uninstantiated_type =
            self.check_function_expression_or_object_literal_method(node, check_mode);
        self.instantiate_type_with_single_generic_call_signature(
            node,
            uninstantiated_type,
            check_mode,
        )
    }

    /// `func (c *Checker) checkExpressionForMutableLocation` (checker.go:14149).
    pub(crate) fn check_expression_for_mutable_location(
        &mut self,
        node: NodeId,
        check_mode: CheckMode,
    ) -> TypeId {
        let t = self.check_expression_ex(node, check_mode);
        if self.is_const_context(node) {
            return self.get_regular_type_of_literal_type(t);
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if crate::utilities::is_type_assertion(node, &nodes) {
            return t;
        }
        let contextual = self.get_contextual_type(node, ContextFlags::NONE);
        let instantiated = self.instantiate_contextual_type(contextual, node, ContextFlags::NONE);
        self.get_widened_literal_like_type_for_contextual_type(t, instantiated)
    }

    /// `func (c *Checker) getResolvedSymbol` (checker.go:14161).
    pub fn get_resolved_symbol(&mut self, node: NodeId) -> SymbolId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if self.symbol_node_links.get(node).resolved_symbol.is_none() {
            let mut symbol: Option<SymbolId> = None;
            if !ast::node_is_missing(Some(node), &nodes) {
                let text = nodes[node].text(&nodes).into_owned();
                let diagnostic = self.get_cannot_find_name_diagnostic_for_name(node);
                let is_use = !ast::is_write_only_access(node, &nodes);
                symbol = call_resolve_name(
                    self,
                    Some(node),
                    &text,
                    ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE,
                    diagnostic,
                    is_use,
                    false, /*excludeGlobals*/
                 None,
                );
            }
            self.symbol_node_links.get(node).resolved_symbol =
                Some(symbol.unwrap_or(self.unknown_symbol));
        }
        self.symbol_node_links
            .get(node)
            .resolved_symbol
            .expect("resolved symbol")
    }

    /// `func (c *Checker) getResolvedSymbolOrNil` (checker.go:14174).
    pub(crate) fn get_resolved_symbol_or_nil(&mut self, node: NodeId) -> Option<SymbolId> {
        self.symbol_node_links.get(node).resolved_symbol
    }

    /// `func (c *Checker) getReferencedValueOrAliasSymbol` (checker.go:14178).
    pub(crate) fn get_referenced_value_or_alias_symbol(
        &mut self,
        reference: NodeId,
        live_nodes: Option<&[ast::Node]>,
    ) -> Option<SymbolId> {
        let resolved_symbol = self.symbol_node_links.get(reference).resolved_symbol;
        if let Some(resolved) = resolved_symbol
            && resolved != self.unknown_symbol
        {
            return Some(resolved);
        }
        let __program = self.program.clone().expect("program");
        let nodes = crate::printer_util::resolve_arena_for(
            &__program,
            live_nodes.unwrap_or(&[]),
            reference,
        );
        let text = nodes[reference].text(&nodes).into_owned();
        call_resolve_name(
            self,
            Some(reference),
            &text,
            ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE | ast::SymbolFlags::ALIAS,
            None,
            false, /*isUse*/
            false, /*excludeGlobals*/
         live_nodes,
        )
    }

    /// `func (c *Checker) getCannotFindNameDiagnosticForName` (checker.go:14186).
    pub(crate) fn get_cannot_find_name_diagnostic_for_name(
        &mut self,
        node: NodeId,
    ) -> Option<&'static tsc_diagnostics::Message> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let text = nodes[node].text(&nodes);
        match text.as_ref() {
            "document" | "console" => {
                Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_change_your_target_library_Try_changing_the_lib_compiler_option_to_include_dom)
            }
            "$" => {
                if self.compiler_options.uses_wildcard_types() {
                    Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_jQuery_Try_npm_i_save_dev_types_Slashjquery)
                } else {
                    Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_jQuery_Try_npm_i_save_dev_types_Slashjquery_and_then_add_jquery_to_the_types_field_in_your_tsconfig)
                }
            }
            "beforeEach" | "describe" | "suite" | "it" | "test" => {
                if self.compiler_options.uses_wildcard_types() {
                    Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_a_test_runner_Try_npm_i_save_dev_types_Slashjest_or_npm_i_save_dev_types_Slashmocha)
                } else {
                    Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_a_test_runner_Try_npm_i_save_dev_types_Slashjest_or_npm_i_save_dev_types_Slashmocha_and_then_add_jest_or_mocha_to_the_types_field_in_your_tsconfig)
                }
            }
            "process" | "require" | "Buffer" | "module" | "NodeJS" => {
                if self.compiler_options.uses_wildcard_types() {
                    Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_node_Try_npm_i_save_dev_types_Slashnode)
                } else {
                    Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_node_Try_npm_i_save_dev_types_Slashnode_and_then_add_node_to_the_types_field_in_your_tsconfig)
                }
            }
            "Bun" => {
                if self.compiler_options.uses_wildcard_types() {
                    Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_Bun_Try_npm_i_save_dev_types_Slashbun)
                } else {
                    Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_Bun_Try_npm_i_save_dev_types_Slashbun_and_then_add_bun_to_the_types_field_in_your_tsconfig)
                }
            }
            "Map" | "Set" | "Promise" | "ast.Symbol" | "WeakMap" | "WeakSet"
            | "Iterator" | "AsyncIterator" | "SharedArrayBuffer" | "Atomics"
            | "AsyncIterable" | "AsyncIterableIterator" | "AsyncGenerator"
            | "AsyncGeneratorFunction" | "BigInt" | "Reflect" | "BigInt64Array"
            | "BigUint64Array" => {
                Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_change_your_target_library_Try_changing_the_lib_compiler_option_to_1_or_later)
            }
            "await" => {
                if nodes[node]
                    .parent
                    .is_some_and(|p| ast::is_call_expression(&nodes[p]))
                {
                    return Some(&tsc_diagnostics::Cannot_find_name_0_Did_you_mean_to_write_this_in_an_async_function);
                }
                // fallthrough
                if nodes[node]
                    .parent
                    .is_some_and(|p| nodes[p].kind == ast::Kind::ShorthandPropertyAssignment)
                {
                    return Some(&tsc_diagnostics::No_value_exists_in_scope_for_the_shorthand_property_0_Either_declare_one_or_provide_an_initializer);
                }
                Some(&tsc_diagnostics::Cannot_find_name_0)
            }
            _ => {
                if nodes[node]
                    .parent
                    .is_some_and(|p| nodes[p].kind == ast::Kind::ShorthandPropertyAssignment)
                {
                    return Some(&tsc_diagnostics::No_value_exists_in_scope_for_the_shorthand_property_0_Either_declare_one_or_provide_an_initializer);
                }
                Some(&tsc_diagnostics::Cannot_find_name_0)
            }
        }
    }
    /// `func (c *Checker) GetDiagnostics` (checker.go:14222). Public API.
    pub fn get_diagnostics(
        &mut self,
        ctx: tsc_core::context::Context,
        source_file: NodeId,
    ) -> Vec<DiagnosticRef> {
        // `DiagnosticsCollection` clones share state (Go shares by pointer),
        // so diagnostics added during `check_source_file` remain visible.
        let diagnostics = self.diagnostics.clone();
        self.get_diagnostics_worker(ctx, source_file, &diagnostics, false)
    }

    /// `func (c *Checker) GetSuggestionDiagnostics` (checker.go:14226). Public API.
    pub fn get_suggestion_diagnostics(
        &mut self,
        ctx: tsc_core::context::Context,
        source_file: NodeId,
    ) -> Vec<DiagnosticRef> {
        let collection = self.suggestion_diagnostics.clone();
        self.get_diagnostics_worker(ctx, source_file, &collection, true)
    }

    /// `func (c *Checker) getDiagnostics` (checker.go:14230). The cloned
    /// `DiagnosticsCollection` shares state with `self.diagnostics`, so
    /// diagnostics added by `check_source_file` below are read back here.
    fn get_diagnostics_worker(
        &mut self,
        ctx: tsc_core::context::Context,
        source_file: NodeId,
        collection: &ast::diagnostic::DiagnosticsCollection,
        is_suggestion_collection: bool,
    ) -> Vec<DiagnosticRef> {
        self.check_not_canceled();
        let check_unused = self.compiler_options.no_unused_locals.is_true()
            || self.compiler_options.no_unused_parameters.is_true()
            || is_suggestion_collection;
        self.check_source_file(ctx, source_file, check_unused);
        if self.was_canceled {
            return Vec::new();
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((source_file).file_index());
        collection.get_diagnostics_for_file(&ast::diagnostic::DiagnosticFile::from_node(
            source_file,
            &nodes,
        ))
    }

    /// `func (c *Checker) GetGlobalDiagnostics` (checker.go:14240). Public API.
    pub fn get_global_diagnostics(&mut self) -> Vec<DiagnosticRef> {
        self.check_not_canceled();
        self.produce_deferred_diagnostics();
        self.diagnostics.get_global_diagnostics()
    }

    /// `func (c *Checker) addDeferredDiagnostic` (checker.go:14246).
    pub(crate) fn add_deferred_diagnostic(
        &mut self,
        callback: crate::checker_types::DeferredDiagnosticCallback<'static>,
    ) {
        self.deferred_diagnostic_callbacks.push(callback);
    }

    /// `func (c *Checker) produceDeferredDiagnostics` (checker.go:14250).
    pub(crate) fn produce_deferred_diagnostics(&mut self) {
        // PORT: `mem::take` then run — matching Go, callbacks registered while
        // running are dropped when the list is discarded.
        let callbacks = std::mem::take(&mut self.deferred_diagnostic_callbacks);
        for cb in callbacks {
            cb(self);
        }
    }

    /// `func (c *Checker) addDiagnostic` (checker.go:14257).
    pub(crate) fn add_diagnostic(&mut self, diagnostic: &DiagnosticRef) -> DiagnosticRef {
        // Discard diagnostics created while at the maximum number of recursive TypeToString invocations.
        if self.serialization_level < crate::checker_types::MAX_SERIALIZATION_LEVEL {
            return self.diagnostics.add(diagnostic);
        }
        diagnostic.clone()
    }

    /// `func (c *Checker) addSuggestionDiagnostic` (checker.go:14265).
    pub(crate) fn add_suggestion_diagnostic(
        &mut self,
        diagnostic: &DiagnosticRef,
    ) -> DiagnosticRef {
        // Discard diagnostics created while at the maximum number of recursive TypeToString invocations.
        if self.serialization_level < crate::checker_types::MAX_SERIALIZATION_LEVEL {
            return self.suggestion_diagnostics.add(diagnostic);
        }
        diagnostic.clone()
    }

    /// `func (c *Checker) errorSkippedOnNoEmit` (checker.go:14277).
    /// (`c.error`/`c.errorOrSuggestion` live in checker_core.rs.)
    pub(crate) fn error_skipped_on_no_emit(
        &mut self,
        location: Option<NodeId>,
        message: &'static tsc_diagnostics::Message,
        args: &[String],
    ) -> Option<DiagnosticRef> {
        let diagnostic = self.error(location, message, args);
        if let Some(d) = &diagnostic {
            ast::diagnostic::lock_diagnostic(d).set_skipped_on_no_emit();
        }
        diagnostic
    }

    /// `func (c *Checker) errorAndMaybeSuggestAwait` (checker.go:14287).
    pub(crate) fn error_and_maybe_suggest_await(
        &mut self,
        location: NodeId,
        maybe_missing_await: bool,
        message: &'static tsc_diagnostics::Message,
        args: &[String],
    ) -> Option<DiagnosticRef> {
        let diagnostic = self.error(Some(location), message, args);
        if maybe_missing_await {
            if let Some(d) = &diagnostic {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((location).file_index());
                let related = create_diagnostic_for_node(
                    Some(location),
                    &nodes,
                    &tsc_diagnostics::Did_you_forget_to_use_await,
                    &[],
                );
                ast::diagnostic::lock_diagnostic(d).add_related_info(Some(related));
            }
        }
        diagnostic
    }

    /// `func (c *Checker) addErrorOrSuggestion` (checker.go:14295).
    pub(crate) fn add_error_or_suggestion(&mut self, is_error: bool, diagnostic: &DiagnosticRef) {
        if is_error {
            self.add_diagnostic(&diagnostic);
        } else {
            let mut suggestion = ast::diagnostic::lock_diagnostic(diagnostic).clone();
            suggestion.set_category(tsc_diagnostics::Category::Suggestion);
            let suggestion: DiagnosticRef = std::sync::Arc::new(std::sync::Mutex::new(suggestion));
            self.add_suggestion_diagnostic(&suggestion);
        }
    }

    /// `func (c *Checker) IsDeprecatedDeclaration` (checker.go:14305).
    /// Public API.
    pub fn is_deprecated_declaration(&mut self, declaration: NodeId) -> bool {
        let combined_flags = self.get_combined_node_flags_cached(declaration);
        let __program = self.program.clone().expect("program");
        // Lazy JSDoc parsing mutates the arena; run in place when the arena
        // is unshared. When snapshots are held, use the checker's per-file
        // scratch clone (cloned once per file — the deprecated-tag reads only
        // touch parse-stable fields).
        let arena = __program.nodes_handle(declaration.file_index());
        if !arena.is_shared() {
            let mut nodes = arena.cow();
            return crate::jsdoc::is_deprecated_declaration_with_cached_flags(
                &mut nodes,
                declaration,
                combined_flags,
            );
        }
        let scratch = self
            .jsdoc_scratch_arenas
            .entry(declaration.file_index())
            .or_insert_with(|| arena.snapshot().to_vec());
        crate::jsdoc::is_deprecated_declaration_with_cached_flags(
            scratch,
            declaration,
            combined_flags,
        )
    }

    /// `func (c *Checker) addDeprecatedSuggestion` (checker.go:14309).
    pub(crate) fn add_deprecated_suggestion(
        &mut self,
        location: NodeId,
        declarations: &[NodeId],
        deprecated_entity: &str,
    ) -> DiagnosticRef {
        let diagnostic = self.new_diagnostic_for_node(
            Some(location),
            &tsc_diagnostics::X_0_is_deprecated,
            &[deprecated_entity.to_string()],
        );
        self.add_deprecated_suggestion_worker(declarations, &diagnostic)
    }

    /// `func (c *Checker) addDeprecatedSuggestionWorker` (checker.go:14314).
    pub(crate) fn add_deprecated_suggestion_worker(
        &mut self,
        declarations: &[NodeId],
        diagnostic: &DiagnosticRef,
    ) -> DiagnosticRef {
        for &declaration in declarations {
            let __program = self.program.clone().expect("program");
            // In-place when the arena is free; per-file scratch clone when a
            // caller holds a `Ref` (see `is_deprecated_declaration`). The tag
            // id's arena membership is transient — `create_diagnostic_for_node`
            // resolves file/span eagerly — so scratch ids never escape.
            let arena = __program.nodes_handle(declaration.file_index());
            let unshared = !arena.is_shared();
            let mut guard;
            let mut owned;
            let nodes: &mut Vec<ast::Node> = if unshared {
                guard = arena.cow();
                &mut guard
            } else {
                owned = self.jsdoc_scratch_arenas.entry(declaration.file_index());
                owned.or_insert_with(|| arena.snapshot().to_vec())
            };
            let deprecated_tag = crate::jsdoc::get_jsdoc_deprecated_tag(nodes, declaration);
            if let Some(deprecated_tag) = deprecated_tag {
                let related = create_diagnostic_for_node(
                    Some(deprecated_tag),
                    &*nodes,
                    &tsc_diagnostics::The_declaration_was_marked_as_deprecated_here,
                    &[],
                );
                ast::diagnostic::lock_diagnostic(diagnostic).add_related_info(Some(related));
                break;
            }
        }
        self.add_suggestion_diagnostic(diagnostic)
    }

    /// `func (c *Checker) isDeprecatedSymbol` (checker.go:14325).
    pub(crate) fn is_deprecated_symbol(&mut self, symbol: SymbolId) -> bool {
        let parent_symbol = self.get_parent_of_symbol(symbol);
        let (declarations, value_declaration) = {
            let s = self.sym(symbol);
            (s.declarations.clone(), s.value_declaration)
        };
        if let Some(parent_symbol) = parent_symbol
            && declarations.len() > 1
        {
            if self
                .sym(parent_symbol)
                .flags
                .intersects(ast::SymbolFlags::INTERFACE)
            {
                return declarations
                    .iter()
                    .any(|&d| self.is_deprecated_declaration(d));
            } else {
                return declarations
                    .iter()
                    .all(|&d| self.is_deprecated_declaration(d));
            }
        }
        (value_declaration.is_some_and(|d| self.is_deprecated_declaration(d)))
            || (!declarations.is_empty()
                && declarations
                    .iter()
                    .all(|&d| self.is_deprecated_declaration(d)))
    }

    /// `func (c *Checker) hasParseDiagnostics` (checker.go:14337). Go takes
    /// `*ast.SourceFile`; the port passes the `SourceFile`'s `NodeId`.
    pub(crate) fn has_parse_diagnostics(&mut self, source_file: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((source_file).file_index());
        !nodes[source_file].as_source_file().diagnostics().is_empty()
    }
    /// `func (c *Checker) combineSymbolTables` (checker.go:14367).
    pub(crate) fn combine_symbol_tables(
        &mut self,
        first: ast::SymbolTable,
        second: ast::SymbolTable,
    ) -> ast::SymbolTable {
        if first.is_empty() {
            return second;
        }
        if second.is_empty() {
            return first;
        }
        let mut combined = ast::SymbolTable::default();
        self.merge_symbol_table(&mut combined, &first, false, None);
        self.merge_symbol_table(&mut combined, &second, false, None);
        combined
    }

    /// `func (c *Checker) mergeSymbolTable` (checker.go:14380). PORT:
    /// `target`/`source` are `ast.SymbolTable` maps passed by reference.
    pub(crate) fn merge_symbol_table(
        &mut self,
        target: &mut ast::SymbolTable,
        source: &ast::SymbolTable,
        unidirectional: bool,
        merged_parent: Option<SymbolId>,
    ) {
        for (id, &source_symbol) in source.entries() {
            let target_symbol = target.get(id).copied();
            let merged = if let Some(target_symbol) = target_symbol {
                self.merge_symbol(target_symbol, source_symbol, unidirectional)
            } else {
                self.get_merged_symbol(source_symbol)
            };
            if merged_parent.is_some() && target_symbol.is_some() {
                // If a merge was performed on the target symbol, set its parent to the merged parent that initiated the merge
                // of its exports. Otherwise, `merged` came only from `sourceSymbol` and can keep its parent:
                //
                // // a.ts
                // export interface A { x: number; }
                //
                // // b.ts
                // declare module "./a" {
                //   interface A { y: number; }
                //   interface B {}
                // }
                //
                // When merging the module augmentation into a.ts, the symbol for `A` will itself be merged, so its parent
                // should be the merged module symbol. But the symbol for `B` has only one declaration, so its parent should
                // be the module augmentation symbol, which contains its only declaration.
                if self
                    .sym(merged)
                    .flags
                    .intersects(ast::SymbolFlags::TRANSIENT)
                {
                    self.sym_mut(merged).parent = merged_parent;
                }
            }
            target.set(id.clone(), merged);
        }
    }

    /// `func (c *Checker) reportMergeSymbolError` (checker.go:14472).
    /// (`mergeSymbol`/`getMergedSymbol`/`getSymbolOfDeclaration` are stubbed
    /// in checker_core.rs — `PORT(deferred)` per that file's notes.)
    pub(crate) fn report_merge_symbol_error(&mut self, target: SymbolId, source: SymbolId) {
        let target_flags = self.sym(target).flags;
        let source_flags = self.sym(source).flags;
        let is_either_enum = target_flags.intersects(ast::SymbolFlags::ENUM)
            || source_flags.intersects(ast::SymbolFlags::ENUM);
        let is_either_block_scoped = target_flags
            .intersects(ast::SymbolFlags::BLOCK_SCOPED_VARIABLE)
            || source_flags.intersects(ast::SymbolFlags::BLOCK_SCOPED_VARIABLE);
        let message = if is_either_enum {
            &tsc_diagnostics::Enum_declarations_can_only_merge_with_namespace_or_other_enum_declarations
        } else if is_either_block_scoped {
            &tsc_diagnostics::Cannot_redeclare_block_scoped_variable_0
        } else {
            &tsc_diagnostics::Duplicate_identifier_0
        };
        let source_symbol_file = get_first_declaration(self, source)
            .and_then(|d| ast::get_source_file_of_node(Some(d), &self.program_nodes(d)));
        let target_symbol_file = get_first_declaration(self, target)
            .and_then(|d| ast::get_source_file_of_node(Some(d), &self.program_nodes(d)));
        let is_source_plain_js = source_symbol_file.is_some_and(|sf| {
            ast::is_plain_js_file(
                Some(self.program_nodes(sf)[sf].as_source_file()),
                self.compiler_options.check_js,
            )
        });
        let is_target_plain_js = target_symbol_file.is_some_and(|sf| {
            ast::is_plain_js_file(
                Some(self.program_nodes(sf)[sf].as_source_file()),
                self.compiler_options.check_js,
            )
        });
        let symbol_name = self.symbol_to_string(source);
        if !is_source_plain_js {
            self.add_duplicate_declaration_errors_for_symbols(
                source,
                message,
                &symbol_name,
                target,
            );
        }
        if !is_target_plain_js {
            self.add_duplicate_declaration_errors_for_symbols(
                target,
                message,
                &symbol_name,
                source,
            );
        }
    }

    /// `func (c *Checker) addDuplicateDeclarationErrorsForSymbols` (checker.go:14497).
    pub(crate) fn add_duplicate_declaration_errors_for_symbols(
        &mut self,
        target: SymbolId,
        message: &'static tsc_diagnostics::Message,
        symbol_name: &str,
        source: SymbolId,
    ) {
        let target_declarations = self.sym(target).declarations.clone();
        let related = self.sym(source).declarations.clone();
        for node in target_declarations {
            self.add_duplicate_declaration_error(node, message, symbol_name, &related);
        }
    }

    /// `func (c *Checker) addDuplicateDeclarationError` (checker.go:14503).
    pub(crate) fn add_duplicate_declaration_error(
        &mut self,
        node: NodeId,
        message: &'static tsc_diagnostics::Message,
        symbol_name: &str,
        related_nodes: &[NodeId],
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let error_node = get_adjusted_node_for_error(node, &nodes).unwrap_or(node);
        let err = self.lookup_or_issue_error(Some(error_node), message, &[symbol_name.to_string()]);
        for &related_node in related_nodes {
            let __program = self.program.clone().expect("program");
            let related_nodes_arena = __program.nodes((related_node).file_index());
            let adjusted_node = get_adjusted_node_for_error(related_node, &related_nodes_arena)
                .unwrap_or(related_node);
            if adjusted_node == error_node {
                continue;
            }
            let leading_message = create_diagnostic_for_node(
                Some(adjusted_node),
                &related_nodes_arena,
                &tsc_diagnostics::X_0_was_also_declared_here,
                &[symbol_name.to_string()],
            );
            let follow_on_message = create_diagnostic_for_node(
                Some(adjusted_node),
                &related_nodes_arena,
                &tsc_diagnostics::X_and_here,
                &[],
            );
            if let Some(err) = &err {
                let (related_len, has_duplicate) = {
                    let guard = ast::diagnostic::lock_diagnostic(err);
                    (
                        guard.related_information().len(),
                        guard.related_information().iter().any(|d| {
                            ast::diagnostic::compare_diagnostics(d, &follow_on_message) == 0
                                || ast::diagnostic::compare_diagnostics(d, &leading_message) == 0
                        }),
                    )
                };
                if related_len >= 5 || has_duplicate {
                    continue;
                }
                if related_len == 0 {
                    ast::diagnostic::lock_diagnostic(err).add_related_info(Some(leading_message));
                } else {
                    ast::diagnostic::lock_diagnostic(err).add_related_info(Some(follow_on_message));
                }
            }
        }
    }

    /// `func (c *Checker) lookupOrIssueError` (checker.go:14541).
    pub(crate) fn lookup_or_issue_error(
        &mut self,
        location: Option<NodeId>,
        message: &'static tsc_diagnostics::Message,
        args: &[String],
    ) -> Option<DiagnosticRef> {
        let diagnostic = self.new_diagnostic_for_node(location, message, args);
        Some(self.add_diagnostic(&diagnostic))
    }

    /// `func (c *Checker) cloneSymbol` (checker.go:14608).
    pub(crate) fn clone_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        let (flags, name, parent, value_declaration, members, exports, declarations) = {
            let s = self.sym(symbol);
            (
                s.flags,
                s.name.clone(),
                s.parent,
                s.value_declaration,
                s.members.clone(),
                s.exports.clone(),
                s.declarations.clone(),
            )
        };
        let result = self.new_symbol(flags, &name);
        // Force reallocation if anything is ever appended to declarations
        // (Go `result.Declarations = symbol.Declarations[0:len:len]` — the
        // cloned Vec is already an independent allocation).
        self.sym_mut(result).declarations = declarations;
        self.sym_mut(result).parent = parent;
        self.sym_mut(result).value_declaration = value_declaration;
        self.sym_mut(result).members = members;
        self.sym_mut(result).exports = exports;
        self.record_merged_symbol(result, symbol);
        result
    }

    /// `func (c *Checker) getParentOfSymbol` (checker.go:14630).
    pub fn get_parent_of_symbol(&mut self, symbol: SymbolId) -> Option<SymbolId> {
        let parent = self.sym(symbol).parent;
        parent.map(|p| {
            let late_bound = self.get_late_bound_symbol(p);
            self.get_merged_symbol(late_bound)
        })
    }

    /// `func (c *Checker) recordMergedSymbol` (checker.go:14637).
    pub(crate) fn record_merged_symbol(&mut self, target: SymbolId, source: SymbolId) {
        self.merged_symbols.insert(source, target);
    }

    /// `func (c *Checker) getResolvedTarget` (checker.go:14641).
    pub(crate) fn get_resolved_target(&mut self, symbol: SymbolId) -> SymbolId {
        let merged = self.get_merged_symbol(symbol);
        let resolved = self.resolve_symbol(merged);
        self.get_merged_symbol(resolved)
    }

    /// `func (c *Checker) getSymbolIfSameReference` (checker.go:14645).
    pub(crate) fn get_symbol_if_same_reference(
        &mut self,
        s1: SymbolId,
        s2: SymbolId,
    ) -> Option<SymbolId> {
        if self.get_resolved_target(s1) == self.get_resolved_target(s2) {
            return Some(s1);
        }
        None
    }

    /// `func (c *Checker) getExportSymbolOfValueSymbolIfExported` (checker.go:14652).
    pub(crate) fn get_export_symbol_of_value_symbol_if_exported(
        &mut self,
        symbol: Option<SymbolId>,
    ) -> Option<SymbolId> {
        let mut symbol = symbol;
        if let Some(s) = symbol
            && self.sym(s).flags.intersects(ast::SymbolFlags::EXPORT_VALUE)
            && let Some(export_symbol) = self.sym(s).export_symbol
        {
            symbol = Some(export_symbol);
        }
        symbol.map(|s| self.get_merged_symbol(s))
    }

    /// `func (c *Checker) getSymbolOfNode` (checker.go:14669).
    /// PORT: `node.DeclarationData().Symbol` — Go's DeclarationData covers
    /// declaration nodes carrying a `symbol`; `Node::symbol()` already
    /// returns the bound symbol for such nodes.
    pub fn get_symbol_of_node(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let symbol = nodes[node].symbol();
        symbol.map(|s| {
            let late_bound = self.get_late_bound_symbol(s);
            self.get_merged_symbol(late_bound)
        })
    }

    /// `func (c *Checker) getLateBoundSymbol` (checker.go:14677).
    pub(crate) fn get_late_bound_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        let (flags, name) = {
            let s = self.sym(symbol);
            (s.flags, s.name.clone())
        };
        if !flags.intersects(ast::SymbolFlags::CLASS_MEMBER)
            || name != ast::symbol::INTERNAL_SYMBOL_NAME_COMPUTED
        {
            return symbol;
        }
        if self.late_bound_links.get(symbol).late_symbol.is_none() {
            let declarations = self.sym(symbol).declarations.clone();
            if declarations.iter().any(|&d| self.has_late_bindable_name(d)) {
                // force late binding of members/exports. This will set the late-bound symbol
                let parent_raw = self.sym(symbol).parent;
                let parent = parent_raw.map(|p| self.get_merged_symbol(p));
                let has_static = declarations.iter().any(|&d| {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((d).file_index());
                    ast::has_static_modifier(&nodes[d])
                });
                if let Some(parent) = parent {
                    if has_static {
                        self.get_exports_of_symbol(parent);
                    } else {
                        self.get_members_of_symbol(parent);
                    }
                }
            }
        }
        if self.late_bound_links.get(symbol).late_symbol.is_none() {
            self.late_bound_links.get(symbol).late_symbol = Some(symbol);
        }
        self.late_bound_links
            .get(symbol)
            .late_symbol
            .expect("late symbol")
    }

    /// `func (c *Checker) resolveSymbol` (checker.go:14697).
    pub(crate) fn resolve_symbol(&mut self, symbol: SymbolId) -> SymbolId {
        self.resolve_symbol_ex(symbol, false /*dontResolveAlias*/)
    }

    /// `func (c *Checker) resolveSymbolEx` (checker.go:14701).
    pub(crate) fn resolve_symbol_ex(
        &mut self,
        symbol: SymbolId,
        dont_resolve_alias: bool,
    ) -> SymbolId {
        let is_non_local_alias = {
            let s = self.sym(symbol);
            ast::is_non_local_alias(
                Some(&*s),
                ast::SymbolFlags::VALUE | ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE,
            )
        };
        if !dont_resolve_alias && is_non_local_alias {
            return self.resolve_alias(symbol);
        }
        symbol
    }
    /// `func (c *Checker) getTargetOfImportEqualsDeclaration` (checker.go:14708).
    /// Node is ImportEqualsDeclaration | VariableDeclaration.
    pub(crate) fn get_target_of_import_equals_declaration(
        &mut self,
        node: NodeId,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_var_or_external_module_reference = ast::is_variable_declaration(&nodes[node])
            || nodes[node]
                .as_import_equals_declaration()
                .module_reference
                .is_some_and(|mr| nodes[mr].kind == ast::Kind::ExternalModuleReference);
        if is_var_or_external_module_reference {
            let mut module_reference = get_external_module_require_argument(node, &nodes);
            if module_reference.is_none() {
                module_reference = ast::get_external_module_import_equals_declaration_expression(
                    &nodes[node],
                    &nodes,
                );
            }
            let immediate = self.resolve_external_module_name(node, module_reference, false, None);
            let resolved = self.resolve_external_module_symbol(immediate, true);
            if let Some(resolved) = resolved
                && (ModuleKind::Node20..=ModuleKind::NodeNext).contains(&self.module_kind)
            {
                let module_exports = self.get_export_of_module(
                    resolved,
                    ast::symbol::INTERNAL_SYMBOL_NAME_MODULE_EXPORTS,
                    Some(node),
                    true,
                );
                if module_exports.is_some() {
                    return module_exports;
                }
            }
            self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
            return resolved;
        }
        let module_reference = nodes[node]
            .as_import_equals_declaration()
            .module_reference
            .expect("import equals module reference");
        let resolved =
            self.get_symbol_of_part_of_right_hand_side_of_import_equals(module_reference);
        self.check_and_report_error_for_resolving_import_alias_to_type_only_symbol(node, resolved);
        resolved
    }

    /// `func (c *Checker) resolveExternalModuleTypeByLiteral` (checker.go:14731).
    pub(crate) fn resolve_external_module_type_by_literal(&mut self, name: NodeId) -> TypeId {
        if let Some(module_sym) = self.resolve_external_module_name(name, Some(name), false, None) {
            if let Some(resolved_module_symbol) =
                self.resolve_external_module_symbol(Some(module_sym), false)
            {
                return self.get_type_of_symbol(resolved_module_symbol);
            }
        }
        self.any_type
    }

    /// `func (c *Checker) getSymbolOfPartOfRightHandSideOfImportEquals`
    /// (checker.go:14743). This function is only for imports with entity
    /// names.
    pub(crate) fn get_symbol_of_part_of_right_hand_side_of_import_equals(
        &mut self,
        entity_name: NodeId,
    ) -> Option<SymbolId> {
        // There are three things we might try to look for. In the following examples,
        // the search term is enclosed in |...|:
        //
        //     import a = |b|; // Namespace
        //     import a = |b.c|; // Value, type, namespace
        //     import a = |b.c|.d; // Namespace
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((entity_name).file_index());
        let mut entity_name = entity_name;
        if nodes[entity_name].kind == ast::Kind::Identifier
            && ast::is_right_side_of_qualified_name_or_property_access(entity_name, &nodes)
        {
            entity_name = nodes[entity_name].parent.expect("qualified name parent"); // QualifiedName
        }
        // Check for case 1 and 3 in the above example
        if nodes[entity_name].kind == ast::Kind::Identifier
            || nodes[entity_name]
                .parent
                .is_some_and(|p| nodes[p].kind == ast::Kind::QualifiedName)
        {
            return self.resolve_entity_name(
                Some(entity_name),
                ast::SymbolFlags::NAMESPACE,
                false, /*ignoreErrors*/
                true,  /*dontResolveAlias*/
                None,  /*location*/
            );
        }
        // Case 2 in above example
        // entityName.kind could be a QualifiedName or a Missing identifier
        debug_assert!(
            nodes[entity_name]
                .parent
                .is_some_and(|p| nodes[p].kind == ast::Kind::ImportEqualsDeclaration)
        );
        self.resolve_entity_name(
            Some(entity_name),
            ast::SymbolFlags::VALUE | ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE,
            false, /*ignoreErrors*/
            true,  /*dontResolveAlias*/
            None,  /*location*/
        )
    }

    /// `func (c *Checker) checkAndReportErrorForResolvingImportAliasToTypeOnlySymbol`
    /// (checker.go:14763).
    pub(crate) fn check_and_report_error_for_resolving_import_alias_to_type_only_symbol(
        &mut self,
        node: NodeId,
        _resolved: Option<SymbolId>,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let decl_module_reference = nodes[node].as_import_equals_declaration().module_reference;
        let mut name = decl_module_reference;
        loop {
            if let Some(type_only_declaration) =
                name.and_then(|n| self.get_type_only_declaration_of_entity_name(n))
            {
                let __program = self.program.clone().expect("program");
                let tn = __program.nodes((type_only_declaration).file_index());
                let is_export = matches!(
                    tn[type_only_declaration].kind,
                    ast::Kind::ExportSpecifier | ast::Kind::ExportDeclaration
                );
                let message = if is_export {
                    &tsc_diagnostics::An_import_alias_cannot_reference_a_declaration_that_was_exported_using_export_type
                } else {
                    &tsc_diagnostics::An_import_alias_cannot_reference_a_declaration_that_was_imported_using_import_type
                };
                let related_message = if is_export {
                    &tsc_diagnostics::X_0_was_exported_here
                } else {
                    &tsc_diagnostics::X_0_was_imported_here
                };
                // TODO: how to get name for export *?
                let related_name = if !ast::is_export_declaration(&tn[type_only_declaration]) {
                    tn[type_only_declaration]
                        .name()
                        .map(|n| tn[n].text(&tn).into_owned())
                        .unwrap_or_else(|| "*".to_string())
                } else {
                    "*".to_string()
                };
                let related = create_diagnostic_for_node(
                    Some(type_only_declaration),
                    &tn,
                    related_message,
                    &[related_name],
                );
                if let Some(d) = self.error(decl_module_reference, message, &[]) {
                    ast::diagnostic::lock_diagnostic(&d).add_related_info(Some(related));
                }
                break;
            }
            let Some(n) = name else { break };
            if ast::is_identifier(&nodes[n]) {
                break;
            }
            name = nodes[n].as_qualified_name().left;
        }
    }

    /// `func (c *Checker) getTypeOnlyDeclarationOfEntityName` (checker.go:14790).
    pub(crate) fn get_type_only_declaration_of_entity_name(
        &mut self,
        name: NodeId,
    ) -> Option<NodeId> {
        let symbol = self.resolve_entity_name(
            Some(name),
            ast::SymbolFlags::VALUE | ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE,
            true, /*ignoreErrors*/
            true, /*dontResolveAlias*/
            None, /*location*/
        )?;
        self.get_type_only_alias_declaration(symbol)
    }

    /// `func (c *Checker) getTargetOfImportClause` (checker.go:14797).
    pub(crate) fn get_target_of_import_clause(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node].as_import_clause().phase_modifier == ast::Kind::SourceKeyword {
            let name_text = nodes[node]
                .name()
                .map(|n| nodes[n].text(&nodes).into_owned())
                .unwrap_or_default();
            if let Some(alias) = self.get_symbol_of_declaration(node) {
                if self
                    .alias_symbol_links
                    .get(alias)
                    .immediate_target
                    .is_none()
                {
                    let symbol =
                        self.new_symbol(ast::SymbolFlags::FUNCTION_SCOPED_VARIABLE, &name_text);
                    let alias_declarations = self.sym(alias).declarations.clone();
                    self.sym_mut(symbol).declarations = alias_declarations;
                    let t = {
                        let thunk = self
                            .get_global_abstract_module_source_type
                            .clone()
                            .expect("getGlobalAbstractModuleSourceType");
                        thunk(self)
                    };
                    self.value_symbol_links.get(symbol).resolved_type = Some(t);
                    self.alias_symbol_links.get(alias).immediate_target = Some(symbol);
                }
                return self.alias_symbol_links.get(alias).immediate_target;
            }
            // Go stores the created symbol in a fresh nil-keyed links object:
            // it is returned but not cached.
            let symbol = self.new_symbol(ast::SymbolFlags::FUNCTION_SCOPED_VARIABLE, &name_text);
            let t = {
                let thunk = self
                    .get_global_abstract_module_source_type
                    .clone()
                    .expect("getGlobalAbstractModuleSourceType");
                thunk(self)
            };
            self.value_symbol_links.get(symbol).resolved_type = Some(t);
            return Some(symbol);
        }
        let parent = nodes[node].parent.expect("import clause parent");
        let module_specifier = get_module_specifier_from_node(parent, &nodes);
        let import_attributes_type =
            self.get_type_from_import_attributes(ast::get_import_attributes(&nodes[parent]));
        let module_symbol = self.resolve_external_module_name(
            node,
            module_specifier,
            false,
            import_attributes_type,
        )?;
        self.get_target_of_module_default(module_symbol, node, true)
    }

    /// `func (c *Checker) getTargetOfModuleDefault` (checker.go:14816).
    pub(crate) fn get_target_of_module_default(
        &mut self,
        module_symbol: SymbolId,
        node: NodeId,
        dont_resolve_alias: bool,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let file = {
            let declarations = self.sym(module_symbol).declarations.clone();
            declarations.iter().copied().find(|&d| {
                let __program = self.program.clone().expect("program");
                let dn = __program.nodes((d).file_index());
                ast::is_source_file(&dn[d])
            })
        };
        let specifier = self.get_module_specifier_for_import_or_export(node);
        let export_default_symbol;
        let mut export_module_dot_exports_symbol = None;
        if is_shorthand_ambient_module_symbol(self, module_symbol) {
            // !!! exportDefaultSymbol = moduleSymbol
            // Does nothing?
        } else if file.is_some()
            && specifier.is_some()
            && (ModuleKind::Node20..=ModuleKind::NodeNext).contains(&self.module_kind)
            && self.get_emit_syntax_for_module_specifier_expression(specifier.unwrap())
                == ModuleKind::CommonJS
            && self
                .program
                .as_ref()
                .expect("program")
                .get_implied_node_format_for_emit(
                    self.program_nodes(file.unwrap())[file.unwrap()].as_source_file(),
                )
                == ModuleKind::ESNext
        {
            export_module_dot_exports_symbol = self.resolve_export_by_name(
                module_symbol,
                ast::symbol::INTERNAL_SYMBOL_NAME_MODULE_EXPORTS,
                Some(node),
                dont_resolve_alias,
            );
        }
        if export_module_dot_exports_symbol.is_some() {
            // We have a transpiled default import where the `require` resolves to an ES module with a `module.exports` named
            // export. With `esModuleInterop` (always enabled), this will work:
            //
            // const dep_1 = __importDefault(require("./dep.mjs")); // wraps like { default: require("./dep.mjs") }
            // dep_1.default; // require("./dep.mjs") -> the `module.exports` export value
            self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
            return export_module_dot_exports_symbol;
        } else {
            export_default_symbol = self.resolve_export_by_name(
                module_symbol,
                ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT,
                Some(node),
                dont_resolve_alias,
            );
        }
        let Some(specifier) = specifier else {
            return export_default_symbol;
        };
        // node is ImportClause | ImportSpecifier | ExportSpecifier
        let attributes = if ast::is_import_clause(&nodes[node]) {
            nodes[node]
                .parent
                .and_then(|p| ast::get_import_attributes(&nodes[p]))
        } else if ast::is_import_specifier(&nodes[node]) {
            nodes[node]
                .parent
                .and_then(|p| nodes[p].parent)
                .and_then(|p| nodes[p].parent)
                .and_then(|p| ast::get_import_attributes(&nodes[p]))
        } else if ast::is_export_specifier(&nodes[node]) {
            nodes[node]
                .parent
                .and_then(|p| nodes[p].parent)
                .and_then(|p| ast::get_import_attributes(&nodes[p]))
        } else {
            None
        };
        let import_attributes_type = self.get_type_from_import_attributes(attributes);
        let has_default_only = self.is_only_importable_as_default(
            specifier,
            Some(module_symbol),
            import_attributes_type,
        );
        let has_synthetic_default =
            self.can_have_synthetic_default(file, module_symbol, dont_resolve_alias, specifier);
        if export_default_symbol.is_none() && !has_synthetic_default && !has_default_only {
            if ast::is_import_clause(&nodes[node]) {
                self.report_non_default_export(module_symbol, node);
            } else {
                let name = if ast::is_import_or_export_specifier(&nodes[node]) {
                    nodes[node].property_name_or_name()
                } else {
                    nodes[node].name()
                };
                self.error_no_module_member_symbol(
                    module_symbol,
                    Some(module_symbol),
                    node,
                    name.expect("import/export member name"),
                );
            }
        } else if has_synthetic_default || has_default_only {
            // per emit behavior, a synthetic default overrides a "real" .default member if `__esModule` is not present
            let mut resolved =
                self.resolve_external_module_symbol(Some(module_symbol), dont_resolve_alias);
            if resolved.is_none() {
                resolved = Some(self.resolve_symbol_ex(module_symbol, dont_resolve_alias));
            }
            self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
            return resolved;
        }
        self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
        export_default_symbol
    }

    /// `func (c *Checker) reportNonDefaultExport` (checker.go:14880).
    pub(crate) fn report_non_default_export(&mut self, module_symbol: SymbolId, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let node_symbol = nodes[node].symbol();
        let node_symbol_name = node_symbol.map(|s| self.sym(s).name.clone());
        let exports_has_named = node_symbol_name
            .as_ref()
            .is_some_and(|name| self.sym(module_symbol).exports.get(name.as_str()).is_some());
        if exports_has_named {
            let module_name = self.symbol_to_string(module_symbol);
            let sym_name = node_symbol
                .map(|s| self.symbol_to_string(s))
                .unwrap_or_default();
            self.error(
                Some(node),
                &tsc_diagnostics::Module_0_has_no_default_export_Did_you_mean_to_use_import_1_from_0_instead,
                &[module_name, sym_name],
            );
        } else {
            let module_name = self.symbol_to_string(module_symbol);
            let diagnostic = self.error(
                nodes[node].name(),
                &tsc_diagnostics::Module_0_has_no_default_export,
                &[module_name],
            );
            let export_star = self
                .sym(module_symbol)
                .exports
                .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_STAR)
                .copied();
            if let Some(export_star) = export_star {
                let export_star_declarations = self.sym(export_star).declarations.clone();
                let default_export = export_star_declarations.iter().copied().find(|&decl| {
                    let __program = self.program.clone().expect("program");
                    let dn = __program.nodes((decl).file_index());
                    if !(ast::is_export_declaration(&dn[decl])
                        && dn[decl].module_specifier().is_some())
                    {
                        return false;
                    }
                    let attrs =
                        self.get_type_from_import_attributes(ast::get_import_attributes(&dn[decl]));

                    let resolved_external_module_name = self.resolve_external_module_name(
                        decl,
                        dn[decl].module_specifier(),
                        false, /*ignoreErrors*/
                        attrs,
                    );
                    resolved_external_module_name.is_some_and(|m| {
                        self.sym(m)
                            .exports
                            .get(ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT)
                            .is_some()
                    })
                });
                if let Some(default_export) = default_export {
                    if let Some(d) = &diagnostic {
                        let __program = self.program.clone().expect("program");
                        let dn = __program.nodes((default_export).file_index());
                        ast::diagnostic::lock_diagnostic(d).add_related_info(Some(
                            create_diagnostic_for_node(
                                Some(default_export),
                                &dn,
                                &tsc_diagnostics::X_export_Asterisk_does_not_re_export_a_default,
                                &[],
                            ),
                        ));
                    }
                }
            }
        }
    }

    /// `func (c *Checker) resolveExportByName` (checker.go:14904).
    pub(crate) fn resolve_export_by_name(
        &mut self,
        module_symbol: SymbolId,
        name: &str,
        source_node: Option<NodeId>,
        dont_resolve_alias: bool,
    ) -> Option<SymbolId> {
        let export_value = self
            .sym(module_symbol)
            .exports
            .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
            .copied();
        let export_symbol = if let Some(export_value) = export_value {
            let t = self.get_type_of_symbol(export_value);
            self.get_property_of_type_ex(
                t, name, true,  /*skipObjectFunctionPropertyAugment*/
                false, /*includeTypeOnlyMembers*/
            )
        } else {
            self.sym(module_symbol).exports.get(name).copied()
        };
        let resolved = export_symbol.map(|s| self.resolve_symbol_ex(s, dont_resolve_alias));
        self.mark_symbol_of_alias_declaration_if_type_only(source_node, None);
        resolved
    }

    /// `func (c *Checker) getTargetOfNamespaceImport` (checker.go:14917).
    pub(crate) fn get_target_of_namespace_import(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let module_specifier = self.get_module_specifier_for_import_or_export(node);
        let import_attributes = nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .and_then(|p| ast::get_import_attributes(&nodes[p]));
        let import_attributes_type = self.get_type_from_import_attributes(import_attributes);
        let immediate = self.resolve_external_module_name(
            node,
            module_specifier,
            false, /*ignoreErrors*/
            import_attributes_type,
        );
        let resolved = self.resolve_es_module_symbol(immediate, node, module_specifier);
        self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
        resolved
    }

    /// `func (c *Checker) getTargetOfNamespaceExport` (checker.go:14925).
    pub(crate) fn get_target_of_namespace_export(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let module_specifier = self.get_module_specifier_for_import_or_export(node);
        if let Some(module_specifier) = module_specifier {
            let import_attributes = nodes[node]
                .parent
                .and_then(|p| ast::get_import_attributes(&nodes[p]));
            let import_attributes_type = self.get_type_from_import_attributes(import_attributes);
            let immediate = self.resolve_external_module_name(
                node,
                Some(module_specifier),
                false, /*ignoreErrors*/
                import_attributes_type,
            );
            let resolved = self.resolve_es_module_symbol(immediate, node, Some(module_specifier));
            self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
            return resolved;
        }
        None
    }

    /// `func (c *Checker) getTargetOfImportSpecifier` (checker.go:14936).
    pub(crate) fn get_target_of_import_specifier(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let name = nodes[node].property_name_or_name();
        if ast::is_import_specifier(&nodes[node])
            && name.is_some_and(|n| ast::module_export_name_is_default(&nodes[n], &nodes))
        {
            if let Some(specifier) = self.get_module_specifier_for_import_or_export(node) {
                let import_declaration = nodes[node]
                    .parent
                    .and_then(|p| nodes[p].parent)
                    .and_then(|p| nodes[p].parent);
                let import_attributes =
                    import_declaration.and_then(|d| ast::get_import_attributes(&nodes[d]));
                let import_attributes_type =
                    self.get_type_from_import_attributes(import_attributes);
                if let Some(module_symbol) = self.resolve_external_module_name(
                    node,
                    Some(specifier),
                    false, /*ignoreErrors*/
                    import_attributes_type,
                ) {
                    return self.get_target_of_module_default(module_symbol, node, true);
                }
            }
        }
        let mut root = nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .and_then(|p| nodes[p].parent)
            .expect("import declaration");
        if ast::is_binding_element(&nodes[node]) {
            root = ast::get_root_declaration(node, &nodes);
        }
        let resolved = self.get_external_module_member(root, node, true);
        self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
        resolved
    }

    /// `func (c *Checker) getExternalModuleMember` (checker.go:14956).
    /// node is ImportDeclaration | ExportDeclaration | VariableDeclaration;
    /// specifier is ImportSpecifier | ExportSpecifier | BindingElement |
    /// PropertyAccessExpression.
    pub(crate) fn get_external_module_member(
        &mut self,
        node: NodeId,
        specifier: NodeId,
        dont_resolve_alias: bool,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let mut module_specifier = get_external_module_require_argument(node, &nodes);
        if module_specifier.is_none() {
            module_specifier = ast::get_external_module_name(&nodes[node], &nodes);
        }
        let attributes = if ast::has_import_attributes(&nodes[node]) {
            ast::get_import_attributes(&nodes[node])
        } else {
            None
        };
        let import_attributes_type = self.get_type_from_import_attributes(attributes);
        let module_symbol = self.resolve_external_module_name(
            node,
            module_specifier,
            false, /*ignoreErrors*/
            import_attributes_type,
        );
        let __program = self.program.clone().expect("program");
        let snodes = __program.nodes((specifier).file_index());
        let name = if !ast::is_property_access_expression(&snodes[specifier]) {
            snodes[specifier].property_name_or_name()
        } else {
            snodes[specifier].name()
        };
        let Some(name) = name else {
            return None;
        };
        if !ast::is_identifier(&snodes[name]) && !ast::is_string_literal(&snodes[name]) {
            return None;
        }
        let name_text = snodes[name].text(&snodes).into_owned();
        let target_symbol =
            self.resolve_es_module_symbol(module_symbol, specifier, module_specifier);
        let Some(target_symbol) = target_symbol else {
            return None;
        };
        // Note: The empty string is a valid module export name:
        //
        //   import { "" as foo } from "./foo";
        //   export { foo as "" };
        //
        if name_text.is_empty() && snodes[name].kind != ast::Kind::StringLiteral {
            return None;
        }
        if module_symbol.is_some_and(|ms| is_shorthand_ambient_module_symbol(self, ms)) {
            return module_symbol;
        }
        // First check if module was specified with "export=". If so, get the member from the resolved type
        let has_export_equals = module_symbol.is_some_and(|ms| {
            self.sym(ms)
                .exports
                .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                .is_some()
        });
        let mut symbol_from_variable = if has_export_equals {
            let t = self.get_type_of_symbol(target_symbol);
            self.get_property_of_type_ex(
                t, &name_text, true,  /*skipObjectFunctionPropertyAugment*/
                false, /*includeTypeOnlyMembers*/
            )
        } else {
            self.get_property_of_variable(target_symbol, &name_text)
        };
        // if symbolFromVariable is export - get its final target
        symbol_from_variable =
            symbol_from_variable.map(|s| self.resolve_symbol_ex(s, dont_resolve_alias));
        let export_container = if has_export_equals {
            // For `export =` modules, supplemental type/namespace exports live on the original module symbol.
            module_symbol.expect("module symbol")
        } else {
            target_symbol
        };
        let mut symbol_from_module = self.get_export_of_module(
            export_container,
            &name_text,
            Some(specifier),
            dont_resolve_alias,
        );
        if symbol_from_module.is_none() && name_text == ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT {
            let file = module_symbol.and_then(|ms| {
                let declarations = self.sym(ms).declarations.clone();
                declarations.iter().copied().find(|&d| {
                    let __program = self.program.clone().expect("program");
                    let dn = __program.nodes((d).file_index());
                    ast::is_source_file(&dn[d])
                })
            });
            let usage = module_specifier.expect("module specifier");
            if self.is_only_importable_as_default(usage, module_symbol, import_attributes_type)
                || self.can_have_synthetic_default(
                    file,
                    module_symbol.expect("module symbol"),
                    dont_resolve_alias,
                    usage,
                )
            {
                symbol_from_module =
                    self.resolve_external_module_symbol(module_symbol, dont_resolve_alias);
                if symbol_from_module.is_none() {
                    symbol_from_module =
                        module_symbol.map(|ms| self.resolve_symbol_ex(ms, dont_resolve_alias));
                }
            }
        }
        let mut symbol = symbol_from_variable;
        if let Some(sfm) = symbol_from_module {
            symbol = Some(sfm);
            if let Some(sfv) = symbol_from_variable {
                symbol = Some(self.combine_value_and_type_symbols(sfv, sfm));
            }
        }
        if ast::is_import_or_export_specifier(&snodes[specifier])
            && module_specifier.is_some_and(|usage| {
                self.is_only_importable_as_default(usage, module_symbol, import_attributes_type)
            })
            && name_text != ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT
        {
            let arg = format!("{}", self.module_kind);
            self.error(
                Some(name),
                &tsc_diagnostics::Named_imports_from_a_JSON_file_into_an_ECMAScript_module_are_not_allowed_when_module_is_set_to_0,
                &[arg],
            );
        } else if symbol.is_none() {
            self.error_no_module_member_symbol(
                module_symbol.expect("module symbol"),
                Some(target_symbol),
                node,
                name,
            );
        }
        symbol
    }

    /// `func (c *Checker) getPropertyOfVariable` (checker.go:15032).
    pub(crate) fn get_property_of_variable(
        &mut self,
        symbol: SymbolId,
        name: &str,
    ) -> Option<SymbolId> {
        if self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::VARIABLE)
        {
            let type_annotation = self.sym(symbol).value_declaration.and_then(|vd| {
                let __program = self.program.clone().expect("program");
                let vn = __program.nodes((vd).file_index());
                vn[vd].type_()
            });
            if let Some(type_annotation) = type_annotation {
                let t = self.get_type_from_type_node(type_annotation);
                let prop = self.get_property_of_type(t, name);
                return prop.map(|p| self.resolve_symbol(p));
            }
        }
        None
    }

    /// `func (c *Checker) combineValueAndTypeSymbols` (checker.go:15060).
    /// Creates a synthetic symbol that combines the value side of one symbol
    /// with the type/namespace side of another symbol.
    pub(crate) fn combine_value_and_type_symbols(
        &mut self,
        value_symbol: SymbolId,
        type_symbol: SymbolId,
    ) -> SymbolId {
        if value_symbol == self.unknown_symbol && type_symbol == self.unknown_symbol {
            return self.unknown_symbol;
        }
        if self
            .sym(type_symbol)
            .flags
            .intersects(ast::SymbolFlags::VALUE)
        {
            return type_symbol;
        }
        if self
            .sym(value_symbol)
            .flags
            .intersects(ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE)
        {
            return value_symbol;
        }
        let (
            value_flags,
            value_name,
            value_declarations,
            value_parent,
            value_declaration,
            value_exports,
        ) = {
            let s = self.sym(value_symbol);
            (
                s.flags,
                s.name.clone(),
                s.declarations.clone(),
                s.parent,
                s.value_declaration,
                s.exports.clone(),
            )
        };
        let (type_flags, type_declarations, type_parent, type_members) = {
            let s = self.sym(type_symbol);
            (s.flags, s.declarations.clone(), s.parent, s.members.clone())
        };
        let result = self.new_symbol(value_flags | type_flags, &value_name);
        debug_assert!(!value_declarations.is_empty() || !type_declarations.is_empty());
        let mut declarations = value_declarations;
        declarations.extend(type_declarations);
        declarations.dedup();
        self.sym_mut(result).declarations = declarations;
        self.sym_mut(result).parent = value_parent.or(type_parent);
        self.sym_mut(result).value_declaration = value_declaration;
        self.sym_mut(result).members = type_members;
        self.sym_mut(result).exports = value_exports;
        result
    }

    /// `func (c *Checker) getExportOfModule` (checker.go:15083).
    pub(crate) fn get_export_of_module(
        &mut self,
        symbol: SymbolId,
        name_text: &str,
        specifier: Option<NodeId>,
        dont_resolve_alias: bool,
    ) -> Option<SymbolId> {
        if self.sym(symbol).flags.intersects(ast::SymbolFlags::MODULE) {
            let exports = self.get_exports_of_symbol(symbol);
            let export_symbol = exports.get(name_text).copied();
            let resolved = export_symbol.map(|s| self.resolve_symbol_ex(s, dont_resolve_alias));
            let export_star_declaration = self
                .module_symbol_links
                .get(symbol)
                .type_only_export_star_map
                .get(name_text)
                .copied();
            self.mark_symbol_of_alias_declaration_if_type_only(specifier, export_star_declaration);
            return resolved;
        }
        None
    }

    /// `func (c *Checker) isOnlyImportableAsDefault` (checker.go:15094).
    pub(crate) fn is_only_importable_as_default(
        &mut self,
        usage: NodeId,
        resolved_module: Option<SymbolId>,
        import_attributes_type: Option<TypeId>,
    ) -> bool {
        // In Node.js, JSON modules don't get named exports
        if !(ModuleKind::Node16..=ModuleKind::NodeNext).contains(&self.module_kind) {
            return false;
        }
        let usage_mode = self.get_emit_syntax_for_module_specifier_expression(usage);
        if usage_mode != ModuleKind::ESNext {
            return false;
        }
        let resolved_module = match resolved_module {
            Some(rm) => Some(rm),
            None => self.resolve_external_module_name(
                usage,
                Some(usage),
                true, /*ignoreErrors*/
                import_attributes_type,
            ),
        };
        let target_file = resolved_module.and_then(|rm| {
            let anchor = {
                let s = self.sym(rm);
                s.value_declaration
                    .or_else(|| s.declarations.first().copied())
            };
            anchor.and_then(|d| {
                let __program = self.program.clone().expect("program");
                let dn = __program.nodes((d).file_index());
                ast::get_source_file_of_module(&self.sym(rm), &dn)
            })
        });
        target_file.is_some_and(|tf| {
            let __program = self.program.clone().expect("program");
            let tn = __program.nodes((tf).file_index());
            let sf = tn[tf].as_source_file();
            ast::is_json_source_file(sf)
                || sf.file_name().declaration_file_extension() == ".d.json.ts"
        })
    }

    /// `func (c *Checker) canHaveSyntheticDefault` (checker.go:15112).
    pub(crate) fn can_have_synthetic_default(
        &mut self,
        file: Option<NodeId>,
        module_symbol: SymbolId,
        dont_resolve_alias: bool,
        usage: NodeId,
    ) -> bool {
        let mut usage_mode = tsc_core::compileroptions::RESOLUTION_MODE_NONE;
        if file.is_some() {
            usage_mode = self.get_emit_syntax_for_module_specifier_expression(usage);
        }
        if let Some(file) = file
            && usage_mode != ModuleKind::None
        {
            let __program = self.program.clone().expect("program");
            let file_nodes = __program.nodes((file).file_index());
            let mut target_mode = self
                .program
                .as_ref()
                .expect("program")
                .get_implied_node_format_for_emit(file_nodes[file].as_source_file());
            if usage_mode == ModuleKind::ESNext
                && target_mode == ModuleKind::CommonJS
                && (ModuleKind::Node16..=ModuleKind::NodeNext).contains(&self.module_kind)
            {
                // In Node.js, CommonJS modules always have a synthetic default when imported into ESM
                return true;
            }
            if usage_mode == ModuleKind::ESNext && target_mode == ModuleKind::ESNext {
                // No matter what the `module` setting is, if we're confident that both files
                // are ESM, there cannot be a synthetic default.
                return false;
            }
            // For other files (not node16/nodenext with impliedNodeFormat), check if we can determine
            // the module format from project references
            if target_mode == ModuleKind::None
                && file_nodes[file].as_source_file().is_declaration_file
            {
                // Try to get the project reference - try both source file mapping and output file mapping
                // since declaration files can be mapped either way depending on how they're resolved
                if self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_redirect_for_resolution(file_nodes[file].as_source_file())
                    .is_some()
                    || self
                        .program
                        .as_ref()
                        .expect("program")
                        .get_project_reference_from_output_dts(
                            file_nodes[file].as_source_file().path_key(),
                        )
                        .is_some()
                {
                    // This is a declaration file from a project reference, so we can determine
                    // its module format from the referenced project's options
                    target_mode = self
                        .program
                        .as_ref()
                        .expect("program")
                        .get_emit_module_format_of_file(file_nodes[file].as_source_file());
                    if usage_mode == ModuleKind::ESNext
                        && (ModuleKind::ES2015..=ModuleKind::ESNext).contains(&target_mode)
                    {
                        return false;
                    }
                }
            }
        }
        // Declaration files (and ambient modules)
        if file.is_none() || {
            let file = file.unwrap();
            let __program = self.program.clone().expect("program");
            let file_nodes = __program.nodes((file).file_index());
            file_nodes[file].as_source_file().is_declaration_file
        } {
            // Definitely cannot have a synthetic default if they have a syntactic default member specified
            let default_export_symbol = self.resolve_export_by_name(
                module_symbol,
                ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT,
                None, /*sourceNode*/
                true, /*dontResolveAlias*/
            ); // Dont resolve alias because we want the immediately exported symbol's declaration
            if let Some(default_export_symbol) = default_export_symbol {
                let declarations = self.sym(default_export_symbol).declarations.clone();
                if tsc_core::core::some(&declarations, |&d| {
                    let __program = self.program.clone().expect("program");
                    let dn = __program.nodes((d).file_index());
                    is_syntactic_default(d, &dn)
                }) {
                    return false;
                }
            }
            // It _might_ still be incorrect to assume there is no __esModule marker on the import at runtime, even if there is no `default` member
            // So we check a bit more,
            if self
                .resolve_export_by_name(
                    module_symbol,
                    "__esModule",
                    None, /*sourceNode*/
                    dont_resolve_alias,
                )
                .is_some()
            {
                // If there is an `__esModule` specified in the declaration (meaning someone explicitly added it or wrote it in their code),
                // it definitely is a module and does not have a synthetic default
                return false;
            }
            // There are _many_ declaration files not written with esmodules in mind that still get compiled into a format with __esModule set
            // Meaning there may be no default at runtime - however to be on the permissive side, we allow access to a synthetic default member
            // as there is no marker to indicate if the accompanying JS has `__esModule` or not, or is even native esm
            return true;
        }
        let file = file.unwrap();
        let __program = self.program.clone().expect("program");
        let file_nodes = __program.nodes((file).file_index());
        // TypeScript files never have a synthetic default (as they are always emitted with an __esModule marker) _unless_ they contain an export= statement
        if !ast::is_in_js_file(Some(file), &file_nodes) {
            return has_export_assignment_symbol(self, module_symbol);
        }

        // JS files have a synthetic default if they do not contain ES2015+ module syntax (export = is not valid in js) _and_ do not have an __esModule marker
        let external_module_indicator = file_nodes[file].as_source_file().external_module_indicator;
        (external_module_indicator.is_none() || external_module_indicator == Some(file))
            && self
                .resolve_export_by_name(
                    module_symbol,
                    "__esModule",
                    None, /*sourceNode*/
                    dont_resolve_alias,
                )
                .is_none()
    }

    /// `func (c *Checker) getEmitSyntaxForModuleSpecifierExpression` (checker.go:15171).
    pub(crate) fn get_emit_syntax_for_module_specifier_expression(
        &mut self,
        usage: NodeId,
    ) -> tsc_core::compileroptions::ResolutionMode {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((usage).file_index());
        if ast::is_string_literal_like(&nodes[usage]) {
            let source_file =
                ast::get_source_file_of_node(Some(usage), &nodes).expect("source file");
            return self
                .program
                .as_ref()
                .expect("program")
                .get_emit_syntax_for_usage_location(nodes[source_file].as_source_file(), usage);
        }
        ModuleKind::None
    }

    /// `func (c *Checker) errorNoModuleMemberSymbol` (checker.go:15178).
    pub(crate) fn error_no_module_member_symbol(
        &mut self,
        module_symbol: SymbolId,
        target_symbol: Option<SymbolId>,
        node: NodeId,
        name: NodeId,
    ) {
        if self.compiler_options.no_check.is_true() {
            return;
        }
        let module_name = self.get_fully_qualified_name(module_symbol, Some(node));
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((name).file_index());
        let declaration_name =
            tsc_scanner::utilities::declaration_name_to_string(Some(name), &nodes);
        let mut suggestion = None;
        if ast::is_identifier(&nodes[name]) {
            suggestion = target_symbol
                .and_then(|t| self.get_suggested_symbol_for_nonexistent_module(name, t));
        }
        if let Some(suggestion) = suggestion {
            let suggestion_name = self.symbol_to_string(suggestion);
            let diagnostic = self.error(
                Some(name),
                &tsc_diagnostics::X_0_has_no_exported_member_named_1_Did_you_mean_2,
                &[module_name, declaration_name, suggestion_name.clone()],
            );
            if let Some(d) = &diagnostic {
                if let Some(value_declaration) = self.sym(suggestion).value_declaration {
                    let __program = self.program.clone().expect("program");
                    let dn = __program.nodes((value_declaration).file_index());
                    ast::diagnostic::lock_diagnostic(d).add_related_info(Some(
                        create_diagnostic_for_node(
                            Some(value_declaration),
                            &dn,
                            &tsc_diagnostics::X_0_is_declared_here,
                            &[suggestion_name],
                        ),
                    ));
                }
            }
        } else {
            let has_default = self
                .sym(module_symbol)
                .exports
                .get(ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT)
                .is_some();
            if has_default {
                self.error(
                    Some(name),
                    &tsc_diagnostics::Module_0_has_no_exported_member_1_Did_you_mean_to_use_import_1_from_0_instead,
                    &[module_name, declaration_name],
                );
            } else {
                self.report_non_exported_member(
                    name,
                    &declaration_name,
                    module_symbol,
                    &module_name,
                );
            }
        }
    }

    /// `func (c *Checker) reportNonExportedMember` (checker.go:15203).
    pub(crate) fn report_non_exported_member(
        &mut self,
        name: NodeId,
        declaration_name: &str,
        module_symbol: SymbolId,
        module_name: &str,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((name).file_index());
        let name_text = nodes[name].text(&nodes).into_owned();
        let (value_declaration, exports) = {
            let s = self.sym(module_symbol);
            (s.value_declaration, s.exports.clone())
        };
        let local_symbol = value_declaration.and_then(|vd| {
            let __program = self.program.clone().expect("program");
            let vn = __program.nodes((vd).file_index());
            vn[vd]
                .locals()
                .and_then(|locals| locals.get(name_text.as_str()).copied())
        });
        if let Some(local_symbol) = local_symbol {
            if let Some(exported_equals_symbol) = exports
                .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                .copied()
            {
                if self
                    .get_symbol_if_same_reference(exported_equals_symbol, local_symbol)
                    .is_some()
                {
                    self.report_invalid_import_equals_export_member(
                        name,
                        declaration_name,
                        module_name,
                    );
                } else {
                    self.error(
                        Some(name),
                        &tsc_diagnostics::Module_0_has_no_exported_member_1,
                        &[module_name.to_string(), declaration_name.to_string()],
                    );
                }
            } else {
                let exported_symbol = find_in_map(&exports, |s| {
                    self.get_symbol_if_same_reference(s, local_symbol).is_some()
                });
                let diagnostic = if let Some(exported_symbol) = exported_symbol {
                    let es = self.symbol_to_string(exported_symbol);

                    self.error(
                        Some(name),
                        &tsc_diagnostics::Module_0_declares_1_locally_but_it_is_exported_as_2,
                        &[module_name.to_string(), declaration_name.to_string(), es],
                    )
                } else {
                    self.error(
                        Some(name),
                        &tsc_diagnostics::Module_0_declares_1_locally_but_it_is_not_exported,
                        &[module_name.to_string(), declaration_name.to_string()],
                    )
                };
                if let Some(d) = &diagnostic {
                    let local_declarations = self.sym(local_symbol).declarations.clone();
                    for (i, decl) in local_declarations.iter().enumerate() {
                        let __program = self.program.clone().expect("program");
                        let dn = __program.nodes((*decl).file_index());
                        let message = if i == 0 {
                            &tsc_diagnostics::X_0_is_declared_here
                        } else {
                            &tsc_diagnostics::X_and_here
                        };
                        ast::diagnostic::lock_diagnostic(d).add_related_info(Some(
                            create_diagnostic_for_node(
                                Some(*decl),
                                &dn,
                                message,
                                &[declaration_name.to_string()],
                            ),
                        ));
                    }
                }
            }
        } else {
            self.error(
                Some(name),
                &tsc_diagnostics::Module_0_has_no_exported_member_1,
                &[module_name.to_string(), declaration_name.to_string()],
            );
        }
    }

    /// `func (c *Checker) reportInvalidImportEqualsExportMember` (checker.go:15235).
    pub(crate) fn report_invalid_import_equals_export_member(
        &mut self,
        name: NodeId,
        declaration_name: &str,
        module_name: &str,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((name).file_index());
        if self.module_kind >= ModuleKind::ES2015 {
            self.error(
                Some(name),
                &tsc_diagnostics::X_0_can_only_be_imported_by_using_a_default_import,
                &[declaration_name.to_string()],
            );
        } else if ast::is_in_js_file(Some(name), &nodes) {
            self.error(
                Some(name),
                &tsc_diagnostics::X_0_can_only_be_imported_by_using_a_require_call_or_by_using_a_default_import,
                &[declaration_name.to_string()],
            );
        } else {
            self.error(
                Some(name),
                &tsc_diagnostics::X_0_can_only_be_imported_by_using_import_1_require_2_or_a_default_import,
                &[
                    declaration_name.to_string(),
                    declaration_name.to_string(),
                    module_name.to_string(),
                ],
            );
        }
    }

    /// `func (c *Checker) getTargetOfExportSpecifier` (checker.go:15245).
    pub(crate) fn get_target_of_export_specifier(
        &mut self,
        node: NodeId,
        meaning: ast::SymbolFlags,
        dont_resolve_alias: bool,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let name = nodes[node].property_name_or_name();
        if name.is_some_and(|n| ast::module_export_name_is_default(&nodes[n], &nodes)) {
            if let Some(specifier) = self.get_module_specifier_for_import_or_export(node) {
                let export_declaration = nodes[node].parent.and_then(|p| nodes[p].parent);
                let import_attributes =
                    export_declaration.and_then(|d| ast::get_import_attributes(&nodes[d]));
                let import_attributes_type =
                    self.get_type_from_import_attributes(import_attributes);
                if let Some(module_symbol) = self.resolve_external_module_name(
                    node,
                    Some(specifier),
                    false, /*ignoreErrors*/
                    import_attributes_type,
                ) {
                    return self.get_target_of_module_default(
                        module_symbol,
                        node,
                        dont_resolve_alias,
                    );
                }
            }
        }
        let export_declaration = nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .expect("export declaration");
        let resolved = if nodes[export_declaration].module_specifier().is_some() {
            self.get_external_module_member(export_declaration, node, dont_resolve_alias)
        } else if name.is_some_and(|n| ast::is_string_literal(&nodes[n])) {
            None
        } else {
            self.resolve_entity_name(name, meaning, false, dont_resolve_alias, None)
        };
        self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
        resolved
    }

    /// `func (c *Checker) getTargetOfExportAssignment` (checker.go:15270).
    /// An `export =` / `export default` inside a namespace/module block is a
    /// grammar error; mirror checkExportAssignment's bail-out (using the same
    /// container computation) so alias resolution triggered by the emit
    /// resolver does not resolve — and report "Cannot find name" diagnostics
    /// on — the expression.
    pub(crate) fn get_target_of_export_assignment(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if is_contained_by_namespace(node, &nodes) {
            return None;
        }
        let expression = nodes[node]
            .expression()
            .expect("export assignment expression");
        let resolved = self.get_target_of_alias_like_expression(expression);
        self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
        resolved
    }

    /// `func (c *Checker) getTargetOfBinaryExpression` (checker.go:15284).
    pub(crate) fn get_target_of_binary_expression(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let right = nodes[node]
            .as_binary_expression()
            .right
            .expect("binary expression right");
        let resolved = self.get_target_of_alias_like_expression(right);
        self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
        resolved
    }

    /// `func (c *Checker) getTargetOfAliasLikeExpression` (checker.go:15290).
    pub(crate) fn get_target_of_alias_like_expression(
        &mut self,
        expression: NodeId,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((expression).file_index());
        if ast::is_class_expression(&nodes[expression]) {
            let t = self.check_expression_cached(expression);
            return self.types.get_ref(t).symbol;
        }
        if !ast::is_entity_name(&nodes[expression])
            && !ast::is_entity_name_expression(&nodes[expression], &nodes)
        {
            return None;
        }
        if let Some(alias_like) = self.resolve_entity_name(
            Some(expression),
            ast::SymbolFlags::VALUE | ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE,
            true, /*ignoreErrors*/
            true, /*dontResolveAlias*/
            None, /*location*/
        ) {
            return Some(alias_like);
        }
        self.check_expression_cached(expression);
        self.get_resolved_symbol_or_nil(expression)
    }

    /// `func (c *Checker) getTargetOfNamespaceExportDeclaration` (checker.go:15305).
    pub(crate) fn get_target_of_namespace_export_declaration(
        &mut self,
        node: NodeId,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(parent) = nodes[node].parent
            && ast::can_have_symbol(&nodes[parent])
        {
            let resolved = nodes[parent]
                .symbol()
                .and_then(|s| self.resolve_external_module_symbol(Some(s), true));
            self.mark_symbol_of_alias_declaration_if_type_only(Some(node), None);
            return resolved;
        }
        None
    }

    /// `func (c *Checker) getTargetOfAccessExpression` (checker.go:15314).
    pub(crate) fn get_target_of_access_expression(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(parent) = nodes[node].parent
            && ast::is_binary_expression(&nodes[parent])
        {
            let expr = nodes[parent].as_binary_expression();
            if expr.left == Some(node)
                && expr
                    .operator_token
                    .is_some_and(|t| nodes[t].kind == ast::Kind::EqualsToken)
            {
                return self.get_target_of_alias_like_expression(expr.right.expect("binary right"));
            }
        }
        None
    }

    /// `func (c *Checker) getModuleSpecifierForImportOrExport` (checker.go:15324).
    pub(crate) fn get_module_specifier_for_import_or_export(
        &mut self,
        node: NodeId,
    ) -> Option<NodeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::ImportClause => nodes[node]
                .parent
                .and_then(|p| get_module_specifier_from_node(p, &nodes)),
            ast::Kind::ImportEqualsDeclaration => {
                let module_reference = nodes[node].as_import_equals_declaration().module_reference;
                if module_reference.is_some_and(|mr| ast::is_external_module_reference(&nodes[mr]))
                {
                    module_reference.and_then(|mr| nodes[mr].expression())
                } else {
                    None
                }
            }
            ast::Kind::NamespaceImport => nodes[node]
                .parent
                .and_then(|p| nodes[p].parent)
                .and_then(|p| get_module_specifier_from_node(p, &nodes)),
            ast::Kind::ImportSpecifier => nodes[node]
                .parent
                .and_then(|p| nodes[p].parent)
                .and_then(|p| nodes[p].parent)
                .and_then(|p| get_module_specifier_from_node(p, &nodes)),
            ast::Kind::NamespaceExport => nodes[node]
                .parent
                .and_then(|p| get_module_specifier_from_node(p, &nodes)),
            ast::Kind::ExportSpecifier => nodes[node]
                .parent
                .and_then(|p| nodes[p].parent)
                .and_then(|p| get_module_specifier_from_node(p, &nodes)),
            other => panic!("Unhandled case in getModuleSpecifierForImportOrExport: {other:?}"),
        }
    }

    /// `func (c *Checker) markSymbolOfAliasDeclarationIfTypeOnly` (checker.go:15377).
    /// Marks a symbol as type-only if its declaration is syntactically type-only.
    /// If it is not itself marked type-only, but resolves to a type-only alias
    /// somewhere in its resolution chain, save a reference to the type-only alias
    /// declaration so the alias _not_ marked type-only can be identified as
    /// _transitively_ type-only.
    pub(crate) fn mark_symbol_of_alias_declaration_if_type_only(
        &mut self,
        alias_declaration: Option<NodeId>,
        export_star_declaration: Option<NodeId>,
    ) -> bool {
        let Some(alias_declaration) = alias_declaration else {
            return false;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((alias_declaration).file_index());
        if !ast::is_declaration_node(&nodes[alias_declaration]) {
            return false;
        }
        // If the declaration itself is type-only, mark it and return. No need to check what it resolves to.
        let source_symbol = self.get_symbol_of_declaration(alias_declaration);
        let type_only_declaration =
            source_symbol.and_then(|s| self.alias_symbol_links.get(s).type_only_declaration);
        if type_only_declaration.is_none()
            && ast::is_type_only_import_or_export_declaration(alias_declaration, &nodes)
        {
            if let Some(s) = source_symbol {
                self.alias_symbol_links.get(s).type_only_declaration = Some(alias_declaration);
            }
            return true;
        }
        if type_only_declaration.is_none() && export_star_declaration.is_some() {
            if let Some(s) = source_symbol {
                self.alias_symbol_links.get(s).type_only_declaration = export_star_declaration;
            }
            return true;
        }
        type_only_declaration.is_some()
    }

    /// `func (c *Checker) resolveExternalModuleName` (checker.go:15395).
    pub(crate) fn resolve_external_module_name(
        &mut self,
        location: NodeId,
        module_reference_expression: Option<NodeId>,
        ignore_errors: bool,
        import_attributes_type: Option<TypeId>,
    ) -> Option<SymbolId> {
        self.resolve_external_module_name_live(
            location,
            module_reference_expression,
            ignore_errors,
            import_attributes_type,
            None,
        )
    }

    /// `resolve_external_module_name` with the caller's live (checked-out)
    /// node buffer so `location`/`module_reference_expression` resolve against
    /// the arena that actually owns them.
    pub(crate) fn resolve_external_module_name_live(
        &mut self,
        location: NodeId,
        module_reference_expression: Option<NodeId>,
        ignore_errors: bool,
        import_attributes_type: Option<TypeId>,
        live_nodes: Option<&[ast::Node]>,
    ) -> Option<SymbolId> {
        let error_message = self
            .get_cannot_resolve_module_name_error_for_specific_module(module_reference_expression);
        let error_message = error_message.or(Some(
            &tsc_diagnostics::Cannot_find_module_0_or_its_corresponding_type_declarations,
        ));
        let ignore_errors = ignore_errors || self.compiler_options.no_check.is_true();
        self.resolve_external_module_name_worker_live(
            location,
            module_reference_expression,
            if ignore_errors { None } else { error_message },
            ignore_errors,
            false, /*isForAugmentation*/
            import_attributes_type,
            live_nodes,
        )
    }

    /// `func (c *Checker) getCannotResolveModuleNameErrorForSpecificModule` (checker.go:15404).
    pub(crate) fn get_cannot_resolve_module_name_error_for_specific_module(
        &mut self,
        module_name: Option<NodeId>,
    ) -> Option<&'static tsc_diagnostics::Message> {
        if let Some(module_name) = module_name {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((module_name).file_index());
            if ast::is_string_literal(&nodes[module_name])
                && tsc_core::nodemodules::NODE_CORE_MODULES
                    .contains(nodes[module_name].text(&nodes).as_ref())
            {
                if self.compiler_options.uses_wildcard_types() {
                    return Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_node_Try_npm_i_save_dev_types_Slashnode);
                }
                return Some(&tsc_diagnostics::Cannot_find_name_0_Do_you_need_to_install_type_definitions_for_node_Try_npm_i_save_dev_types_Slashnode_and_then_add_node_to_the_types_field_in_your_tsconfig);
            }
        }
        None
    }

    /// `func (c *Checker) resolveExternalModuleNameWorker` (checker.go:15416).
    pub(crate) fn resolve_external_module_name_worker(
        &mut self,
        location: NodeId,
        module_reference_expression: Option<NodeId>,
        module_not_found_error: Option<&'static tsc_diagnostics::Message>,
        ignore_errors: bool,
        is_for_augmentation: bool,
        import_attributes_type: Option<TypeId>,
    ) -> Option<SymbolId> {
        self.resolve_external_module_name_worker_live(
            location,
            module_reference_expression,
            module_not_found_error,
            ignore_errors,
            is_for_augmentation,
            import_attributes_type,
            None,
        )
    }

    /// `resolve_external_module_name_worker` with the caller's live node buffer.
    pub(crate) fn resolve_external_module_name_worker_live(
        &mut self,
        location: NodeId,
        module_reference_expression: Option<NodeId>,
        module_not_found_error: Option<&'static tsc_diagnostics::Message>,
        ignore_errors: bool,
        is_for_augmentation: bool,
        import_attributes_type: Option<TypeId>,
        live_nodes: Option<&[ast::Node]>,
    ) -> Option<SymbolId> {
        let module_reference_expression = module_reference_expression?;
        let __program = self.program.clone().expect("program");
        let nodes = crate::printer_util::arena_view(
            &__program,
            live_nodes.unwrap_or(&[]),
            (module_reference_expression).file_index(),
        );
        if !ast::is_string_literal_like(&nodes[module_reference_expression]) {
            return None;
        }
        if nodes[module_reference_expression]
            .parent
            .is_some_and(|p| ast::is_source_phase_import(&nodes[p], &nodes))
        {
            return None;
        }
        let module_reference = nodes[module_reference_expression].text(&nodes).into_owned();
        self.resolve_external_module_live(
            location,
            &module_reference,
            module_not_found_error,
            if !ignore_errors {
                Some(module_reference_expression)
            } else {
                None
            },
            is_for_augmentation,
            import_attributes_type,
            live_nodes,
        )
    }

    /// `func (c *Checker) getExternalModuleFileFromDeclaration` (checker.go:15426).
    /// `*ast.SourceFile` → the source-file `NodeId`.
    pub(crate) fn get_external_module_file_from_declaration(
        &mut self,
        declaration: NodeId,
    ) -> Option<NodeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((declaration).file_index());
        let specifier = if nodes[declaration].kind == ast::Kind::ModuleDeclaration {
            let name = nodes[declaration].name();
            if name.is_some_and(|n| ast::is_string_literal(&nodes[n])) {
                name
            } else {
                None
            }
        } else {
            ast::get_external_module_name(&nodes[declaration], &nodes)
        };
        let import_attributes_type = if ast::has_import_attributes(&nodes[declaration]) {
            self.get_type_from_import_attributes(ast::get_import_attributes(&nodes[declaration]))
        } else {
            None
        };
        // This is only used by emit and type printing, after checking has already reported any
        // resolution errors for this specifier. Resolve with ignoreErrors so that these queries
        // don't add new diagnostics (e.g. an implicit-any-module suggestion) as a side effect.
        let module_symbol = specifier.and_then(|specifier| {
            self.resolve_external_module_name_worker(
                specifier,
                Some(specifier),
                None,  /*moduleNotFoundError*/
                true,  /*ignoreErrors*/
                false, /*isForAugmentation*/
                import_attributes_type,
            )
        })?;
        // `ast.GetDeclarationOfKind(moduleSymbol, KindSourceFile)` — the
        // declarations may live in different files, so each is looked up in
        // its own arena (mirrors the helper's per-declaration kind test).
        let declarations = self.sym(module_symbol).declarations.clone();
        declarations.iter().copied().find(|&d| {
            let __program = self.program.clone().expect("program");
            let dn = __program.nodes((d).file_index());
            dn[d].kind == ast::Kind::SourceFile
        })
    }

    /// `func (c *Checker) resolveExternalModule` (checker.go:15453).
    pub(crate) fn resolve_external_module(
        &mut self,
        location: NodeId,
        module_reference: &str,
        module_not_found_error: Option<&'static tsc_diagnostics::Message>,
        error_node: Option<NodeId>,
        is_for_augmentation: bool,
        import_attributes_type: Option<TypeId>,
    ) -> Option<SymbolId> {
        self.resolve_external_module_live(
            location,
            module_reference,
            module_not_found_error,
            error_node,
            is_for_augmentation,
            import_attributes_type,
            None,
        )
    }

    /// `resolve_external_module` with the caller's live node buffer.
    pub(crate) fn resolve_external_module_live(
        &mut self,
        location: NodeId,
        module_reference: &str,
        module_not_found_error: Option<&'static tsc_diagnostics::Message>,
        error_node: Option<NodeId>,
        is_for_augmentation: bool,
        import_attributes_type: Option<TypeId>,
        live_nodes: Option<&[ast::Node]>,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = crate::printer_util::resolve_arena_for(
            &__program,
            live_nodes.unwrap_or(&[]),
            location,
        );
        if error_node.is_some() && module_reference.starts_with("@types/") {
            let without_at_type_prefix = &module_reference["@types/".len()..];
            self.error(
                error_node,
                &tsc_diagnostics::Cannot_import_type_declaration_files_Consider_importing_0_instead_of_1,
                &[
                    without_at_type_prefix.to_string(),
                    module_reference.to_string(),
                ],
            );
        }
        let import_attributes_type = import_attributes_type.unwrap_or(self.empty_object_type);

        if let Some(ambient_module) =
            self.try_find_ambient_module(module_reference, true /*withAugmentations*/)
        {
            return self.try_resolve_pattern_ambient_module(
                Some(ambient_module),
                module_reference,
                import_attributes_type,
            );
        }

        let importing_source_file =
            crate::printer_util::get_source_file_of_node_resolved(
                &__program,
                live_nodes.unwrap_or(&[]),
                Some(location),
            )
            .expect("source file");
        let live = live_nodes.unwrap_or(&[]);
        // `importing_source_file` can carry a foreign `file_index` (the
        // enclosing chain crosses arenas via fake scopes / scratch clones) —
        // index it through the arena that actually owns it.
        let isf_nodes =
            crate::printer_util::resolve_arena_for(&__program, live, importing_source_file);
        let context_specifier: Option<NodeId>;
        if ast::is_string_literal_like(&nodes[location])
            || nodes[location].parent.is_some_and(|p| {
                let pn = crate::printer_util::resolve_arena_for(&__program, live, p);
                ast::is_module_declaration(&pn[p]) && pn[p].name() == Some(location)
            })
        {
            context_specifier = Some(location);
        } else if ast::is_module_declaration(&nodes[location]) {
            context_specifier = nodes[location].name();
        } else if ast::is_literal_import_type_node(&nodes[location], &nodes) {
            context_specifier = nodes[location]
                .as_import_type_node()
                .argument
                .and_then(|a| nodes[a].as_literal_type_node().literal);
        } else if ast::is_variable_declaration_initialized_to_bare_or_accessed_require(
            location, &nodes,
        ) {
            context_specifier =
                ast::get_module_specifier_of_bare_or_accessed_require(location, &nodes);
        } else {
            let mut context = None;
            let mut ancestor = crate::printer_util::find_ancestor_resolved(
                &__program,
                live,
                Some(location),
                &mut |n, nodes| ast::is_import_call(n, nodes),
            );
            if let Some(a) = ancestor {
                let an = crate::printer_util::resolve_arena_for(&__program, live, a);
                context = an[a].arguments().and_then(|args| args.first().copied());
            }
            if ancestor.is_none() {
                ancestor = crate::printer_util::find_ancestor_resolved(
                    &__program,
                    live,
                    Some(location),
                    &mut |n, _| {
                        ast::is_import_declaration(n) || ast::is_js_import_declaration(n)
                    },
                );
                if let Some(a) = ancestor {
                    let an = crate::printer_util::resolve_arena_for(&__program, live, a);
                    context = an[a].module_specifier();
                }
            }
            if ancestor.is_none() {
                ancestor = crate::printer_util::find_ancestor_resolved(
                    &__program,
                    live,
                    Some(location),
                    &mut |n, _| ast::is_export_declaration(n),
                );
                if let Some(a) = ancestor {
                    let an = crate::printer_util::resolve_arena_for(&__program, live, a);
                    context = an[a].module_specifier();
                }
            }
            if ancestor.is_none() {
                ancestor = crate::printer_util::find_ancestor_resolved(
                    &__program,
                    live,
                    Some(location),
                    &mut |n, _| ast::is_import_equals_declaration(n),
                );
                if let Some(a) = ancestor {
                    let an = crate::printer_util::resolve_arena_for(&__program, live, a);
                    if let Some(module_reference) =
                        an[a].as_import_equals_declaration().module_reference
                        && an[module_reference].kind == ast::Kind::ExternalModuleReference
                    {
                        context = an[module_reference].expression();
                    }
                }
            }
            context_specifier = context;
        }

        let mode = if context_specifier.is_some_and(|cs| {
            let csn = crate::printer_util::resolve_arena_for(&__program, live, cs);
            ast::is_string_literal_like(&csn[cs])
        }) {
            self.program
                .as_ref()
                .expect("program")
                .get_mode_for_usage_location(
                    isf_nodes[importing_source_file].as_source_file(),
                    context_specifier.unwrap(),
                )
        } else {
            self.program
                .as_ref()
                .expect("program")
                .get_default_resolution_mode_for_file(isf_nodes[importing_source_file].as_source_file())
        };

        let resolved_module = self.program.as_ref().expect("program").get_resolved_module(
            isf_nodes[importing_source_file].as_source_file(),
            module_reference,
            mode,
        );

        let mut resolution_diagnostic: Option<&'static tsc_diagnostics::Message> = None;
        if error_node.is_some() && resolved_module.as_ref().is_some_and(|r| r.is_resolved()) {
            resolution_diagnostic = tsc_module::get_resolution_diagnostic(
                self.compiler_options.as_ref(),
                resolved_module.as_ref().unwrap(),
                isf_nodes[importing_source_file].as_source_file(),
            );
        }

        let mut source_file: Option<NodeId> = None;
        if resolved_module.as_ref().is_some_and(|r| r.is_resolved())
            && (resolution_diagnostic.is_none()
                || resolution_diagnostic.is_some_and(|d| {
                    std::ptr::eq(
                        d,
                        &tsc_diagnostics::Module_0_was_resolved_to_1_but_jsx_is_not_set,
                    )
                }))
        {
            source_file = self
                .program
                .as_ref()
                .expect("program")
                .get_source_file_for_resolved_module(resolved_module.as_ref().unwrap());
        }

        if let Some(source_file) = source_file {
            // `source_file` is a foreign NodeId — index it via its own arena.
            let source_file_nodes = __program.nodes(source_file.file_index());
            // If there's a resolutionDiagnostic we need to report it even if a sourceFile is found.
            if let Some(resolution_diagnostic) = resolution_diagnostic {
                self.error(
                    error_node,
                    resolution_diagnostic,
                    &[
                        module_reference.to_string(),
                        resolved_module
                            .as_ref()
                            .unwrap()
                            .resolved_file_name
                            .as_string()
                            .to_string(),
                    ],
                );
            }

            if let Some(error_node) = error_node
                && !resolved_module.as_ref().unwrap().is_custom_resolution
            {
                let resolved = resolved_module.as_ref().unwrap();
                if resolved.resolved_using_ts_extension
                    && tsc_tspath::is_declaration_file_name(module_reference)
                {
                    if crate::printer_util::find_ancestor_resolved(
                        &__program,
                        live,
                        Some(location),
                        &mut |n, nodes| ast::is_emittable_import(n, nodes),
                    )
                    .is_some()
                    {
                        let ts_extension =
                            tsc_tspath::try_extract_ts_extension(module_reference).to_string();
                        if ts_extension.is_empty() {
                            panic!(
                                "should be able to extract TS extension from string that passes IsDeclarationFileName"
                            );
                        }
                        let suggested_source =
                            self.get_suggested_import_source(module_reference, &ts_extension, mode);
                        self.error(
                            Some(error_node),
                            &tsc_diagnostics::A_declaration_file_cannot_be_imported_without_import_type_Did_you_mean_to_import_an_implementation_file_0_instead,
                            &[suggested_source],
                        );
                    }
                } else if resolved.resolved_using_ts_extension
                    && !self.compiler_options.allow_importing_ts_extensions_from(
                        isf_nodes[importing_source_file].as_source_file().file_name(),
                    )
                {
                    if crate::printer_util::find_ancestor_resolved(
                        &__program,
                        live,
                        Some(location),
                        &mut |n, nodes| {
                        ast::is_emittable_import(n, nodes)
                    })
                    .is_some()
                    {
                        let mut ts_extension =
                            tsc_tspath::try_extract_ts_extension(module_reference).to_string();
                        if ts_extension.is_empty() {
                            // Fallback: do a best-effort extraction using strings.Contains.
                            // This handles cases where a wildcard pattern matches a TS extension that's
                            // not at the end of the module specifier, e.g., "#/foo.ts.omg" through "#/*.omg": "./src/*"
                            for ext in tsc_tspath::SUPPORTED_TS_EXTENSIONS_FLAT {
                                if module_reference.contains(ext) {
                                    ts_extension = ext.to_string();
                                    break;
                                }
                            }
                        }
                        if ts_extension.is_empty() {
                            panic!(
                                "should be able to extract TS extension from string when resolvedUsingTsExtension is true"
                            );
                        }
                        self.error(
                            Some(error_node),
                            &tsc_diagnostics::An_import_path_can_only_end_with_a_0_extension_when_allowImportingTsExtensions_is_enabled,
                            &[ts_extension],
                        );
                    }
                } else if self
                    .compiler_options
                    .rewrite_relative_import_extensions
                    .is_true()
                    && !nodes[location].flags.intersects(ast::NodeFlags::AMBIENT)
                    && !tsc_tspath::is_declaration_file_name(module_reference)
                    && !ast::is_literal_import_type_node(&nodes[location], &nodes)
                    && !ast::is_part_of_type_only_import_or_export_declaration(location, &nodes)
                {
                    let should_rewrite = tsc_core::core::should_rewrite_module_specifier(
                        module_reference,
                        self.compiler_options.as_ref(),
                    );
                    if !resolved.resolved_using_ts_extension && should_rewrite {
                        let mut relative_to_source_file =
                            resolved.resolved_file_name.as_string().to_string();
                        if let Some(relative_path) = self
                            .program
                            .as_ref()
                            .expect("program")
                            .case_sensitivity()
                            .relative_path_from_file(
                                isf_nodes[importing_source_file].as_source_file().file_name(),
                                &resolved.resolved_file_name,
                            )
                        {
                            relative_to_source_file =
                                relative_path.as_module_specifier().as_string().to_string();
                        }

                        self.error(
                            Some(error_node),
                            &tsc_diagnostics::This_relative_import_path_is_unsafe_to_rewrite_because_it_looks_like_a_file_name_but_actually_resolves_to_0,
                            &[relative_to_source_file],
                        );
                    } else if resolved.resolved_using_ts_extension
                        && !should_rewrite
                        && self
                            .program
                            .as_ref()
                            .expect("program")
                            .source_file_may_be_emitted(source_file, false)
                    {
                        self.error(
                            Some(error_node),
                            &tsc_diagnostics::This_import_uses_a_0_extension_to_resolve_to_an_input_TypeScript_file_but_will_not_be_rewritten_during_emit_because_it_is_not_a_relative_path,
                            &[tsc_tspath::get_any_extension_from_path(
                                module_reference,
                                &[],
                                tsc_tspath::CaseSensitivity::CaseSensitive,
                            )
                            .to_string()],
                        );
                    } else if resolved.resolved_using_ts_extension && should_rewrite {
                        if let Some(redirect) = self
                            .program
                            .as_ref()
                            .expect("program")
                            .get_redirect_for_resolution(
                                source_file_nodes[source_file].as_source_file(),
                            )
                        {
                            let own_root_dir =
                                crate::checker_types::Program::common_source_directory(
                                    self.program.as_ref().expect("program").as_ref(),
                                );
                            let other_root_dir = redirect.common_source_directory();

                            let case_sensitivity =
                                self.program.as_ref().expect("program").case_sensitivity();

                            let root_dir_path = case_sensitivity.relative_path_from_directory(
                                &own_root_dir,
                                &tsc_tspath::rooted_file_path_from_path(other_root_dir.as_path()),
                            );
                            let roots_compatible = root_dir_path.is_some();

                            // Get outDir paths, defaulting to root directories if not specified
                            let own_out_dir =
                                if self.compiler_options.out_dir.as_string().is_empty() {
                                    own_root_dir.clone()
                                } else {
                                    self.compiler_options.out_dir.clone()
                                };
                            let other_out_dir = redirect
                                .compiler_options()
                                .map(|o| o.out_dir.clone())
                                .filter(|d| !d.as_string().is_empty())
                                .unwrap_or_else(|| other_root_dir.clone());
                            let out_dir_path = case_sensitivity.relative_path_from_directory(
                                &own_out_dir,
                                &tsc_tspath::rooted_file_path_from_path(other_out_dir.as_path()),
                            );
                            let out_dirs_compatible = out_dir_path.is_some();

                            if !roots_compatible
                                || !out_dirs_compatible
                                || root_dir_path != out_dir_path
                            {
                                self.error(
                                    Some(error_node),
                                    &tsc_diagnostics::This_import_path_is_unsafe_to_rewrite_because_it_resolves_to_another_project_and_the_relative_path_between_the_projects_output_files_is_not_the_same_as_the_relative_path_between_its_input_files,
                                    &[],
                                );
                            }
                        }
                    }
                }
            }

            if source_file_nodes[source_file].symbol().is_some() {
                if let Some(error_node) = error_node {
                    let resolved = resolved_module.as_ref().unwrap();
                    if resolved.is_external_library_import
                        && !resolution_extension_is_ts_or_json(&resolved.extension)
                    {
                        self.error_on_implicit_any_module(
                            false, /*isError*/
                            error_node,
                            mode,
                            resolved,
                            module_reference,
                        );
                    }
                    if self.module_kind == ModuleKind::Node16
                        || self.module_kind == ModuleKind::Node18
                    {
                        let is_sync_import = (self
                            .program
                            .as_ref()
                            .expect("program")
                            .get_default_resolution_mode_for_file(
                                isf_nodes[importing_source_file].as_source_file(),
                            )
                            == ModuleKind::CommonJS
                            && crate::printer_util::find_ancestor_resolved(
                                &__program,
                                live,
                                Some(location),
                                &mut |n, nodes| ast::is_import_call(n, nodes),
                            )
                            .is_none())
                            || crate::printer_util::find_ancestor_resolved(
                                &__program,
                                live,
                                Some(location),
                                &mut |n, _| ast::is_import_equals_declaration(n),
                            )
                            .is_some();
                        let override_host = crate::printer_util::find_ancestor_resolved(
                            &__program,
                            live,
                            Some(location),
                            &mut |n, nodes| {
                                ast::is_resolution_mode_override_host(Some(n.id), nodes)
                            },
                        );
                        let __program = self.program.clone().expect("program");
                        let source_file_nodes = __program.nodes(source_file.file_index());
                        if is_sync_import
                            && self
                                .program
                                .as_ref()
                                .expect("program")
                                .get_default_resolution_mode_for_file(
                                    source_file_nodes[source_file].as_source_file(),
                                )
                                == ModuleKind::ESNext
                            && !override_host.is_some_and(|oh| {
                                let ohn =
                                    crate::printer_util::resolve_arena_for(&__program, live, oh);
                                ast::has_resolution_mode_override(Some(oh), &ohn)
                            })
                        {
                            if crate::printer_util::find_ancestor_resolved(
                                &__program,
                                live,
                                Some(location),
                                &mut |n, _| n.kind == ast::Kind::ImportEqualsDeclaration,
                            )
                            .is_some()
                            {
                                // ImportEquals in an ESM file resolving to another ESM file
                                self.error(
                                    Some(error_node),
                                    &tsc_diagnostics::Module_0_cannot_be_imported_using_this_construct_The_specifier_only_resolves_to_an_ES_module_which_cannot_be_imported_with_require_Use_an_ECMAScript_import_instead,
                                    &[module_reference.to_string()],
                                );
                            } else {
                                // CJS file resolving to an ESM file
                                let mut diagnostic_details = None;
                                let ext = isf_nodes[importing_source_file]
                                    .as_source_file()
                                    .file_name()
                                    .extension();
                                if ext == tsc_tspath::EXTENSION_TS
                                    || ext == tsc_tspath::EXTENSION_JS
                                    || ext == tsc_tspath::EXTENSION_TSX
                                    || ext == tsc_tspath::EXTENSION_JSX
                                {
                                    diagnostic_details = Some(self.create_mode_mismatch_details(
                                        importing_source_file,
                                        error_node,
                                    ));
                                }

                                let message = if override_host.is_some_and(|oh| {
                                    let ohn = crate::printer_util::resolve_arena_for(
                                        &__program, live, oh,
                                    );
                                    ohn[oh].kind == ast::Kind::ImportDeclaration
                                        && ohn[oh]
                                            .import_clause()
                                            .is_some_and(|ic| ohn[ic].is_type_only())
                                }) {
                                    &tsc_diagnostics::Type_only_import_of_an_ECMAScript_module_from_a_CommonJS_module_must_have_a_resolution_mode_attribute
                                } else if override_host.is_some_and(|oh| {
                                    let ohn = crate::printer_util::resolve_arena_for(
                                        &__program, live, oh,
                                    );
                                    ohn[oh].kind == ast::Kind::ImportType
                                }) {
                                    &tsc_diagnostics::Type_import_of_an_ECMAScript_module_from_a_CommonJS_module_must_have_a_resolution_mode_attribute
                                } else {
                                    &tsc_diagnostics::The_current_file_is_a_CommonJS_module_whose_imports_will_produce_require_calls_however_the_referenced_file_is_an_ECMAScript_module_and_cannot_be_imported_with_require_Consider_writing_a_dynamic_import_0_call_instead
                                };

                                let diagnostic = self.new_diagnostic_chain_for_node(
                                    diagnostic_details,
                                    Some(error_node),
                                    message,
                                    &[module_reference.to_string()],
                                );
                                self.add_diagnostic(&diagnostic);
                            }
                        }
                    }
                }
                let source_file_symbol = source_file_nodes[source_file].symbol();
                let merged_symbol = source_file_symbol.map(|s| self.get_merged_symbol(s));
                return self.try_resolve_pattern_ambient_module(
                    merged_symbol,
                    module_reference,
                    import_attributes_type,
                );
            }
            let pattern_ambient_module = self.try_resolve_pattern_ambient_module(
                None, /*resolvedSymbol*/
                module_reference,
                import_attributes_type,
            );
            if pattern_ambient_module.is_some() {
                return pattern_ambient_module;
            }
            if let Some(error_node) = error_node
                && module_not_found_error.is_some()
                && !is_side_effect_import(
                    error_node,
                    &crate::printer_util::resolve_arena_for(&__program, live, error_node),
                )
            {
                self.error(
                    Some(error_node),
                    &tsc_diagnostics::File_0_is_not_a_module,
                    &[resolved_module
                        .as_ref()
                        .unwrap()
                        .resolved_file_name
                        .as_string()
                        .to_string()],
                );
            }
            return None;
        }

        let pattern_ambient_module = self.try_resolve_pattern_ambient_module(
            None, /*resolvedSymbol*/
            module_reference,
            import_attributes_type,
        );
        if pattern_ambient_module.is_some() {
            return pattern_ambient_module;
        }

        let Some(error_node) = error_node else {
            return None;
        };

        if (resolved_module.as_ref().is_some_and(|r| r.is_resolved())
            && !resolution_extension_is_ts_or_json(
                &resolved_module.as_ref().unwrap().extension,
            )
            && resolution_diagnostic.is_none())
            || resolution_diagnostic.is_some_and(|d| {
                std::ptr::eq(
                    d,
                    &tsc_diagnostics::Could_not_find_a_declaration_file_for_module_0_1_implicitly_has_an_any_type,
                )
            })
        {
            if is_for_augmentation {
                self.error(
                    Some(error_node),
                    &tsc_diagnostics::Invalid_module_name_in_augmentation_Module_0_resolves_to_an_untyped_module_at_1_which_cannot_be_augmented,
                    &[
                        module_reference.to_string(),
                        resolved_module
                            .as_ref()
                            .map(|r| r.resolved_file_name.as_string().to_string())
                            .unwrap_or_default(),
                    ],
                );
            } else {
                self.error_on_implicit_any_module(
                    self.no_implicit_any && module_not_found_error.is_some(),
                    error_node,
                    mode,
                    resolved_module.as_ref().unwrap(),
                    module_reference,
                );
            }
            return None;
        }

        if let Some(module_not_found_error) = module_not_found_error {
            // See if this was possibly a projectReference redirect
            if resolved_module.as_ref().is_some_and(|r| r.is_resolved()) {
                let resolved = resolved_module.as_ref().unwrap();
                let redirect = self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_project_reference_from_source(&resolved.resolved_path);
                if let Some(redirect) = redirect
                    && !redirect.output_dts.as_string().is_empty()
                {
                    self.error(
                        Some(error_node),
                        &tsc_diagnostics::Output_file_0_has_not_been_built_from_source_file_1,
                        &[
                            redirect.output_dts.as_string().to_string(),
                            resolved.resolved_file_name.as_string().to_string(),
                        ],
                    );
                    return None;
                }
            }

            if let Some(resolution_diagnostic) = resolution_diagnostic {
                self.error(
                    Some(error_node),
                    resolution_diagnostic,
                    &[
                        module_reference.to_string(),
                        resolved_module
                            .as_ref()
                            .map(|r| r.resolved_file_name.as_string().to_string())
                            .unwrap_or_default(),
                    ],
                );
            } else {
                let is_extensionless_relative_path_import =
                    tsc_tspath::path_is_relative(module_reference)
                        && !tsc_tspath::has_extension(module_reference);
                let resolution_is_node16_or_next = self.module_resolution_kind
                    == ModuleResolutionKind::Node16
                    || self.module_resolution_kind == ModuleResolutionKind::NodeNext;
                if !self.compiler_options.get_resolve_json_module()
                    && tsc_tspath::file_extension_is(module_reference, tsc_tspath::EXTENSION_JSON)
                {
                    self.error(
                        Some(error_node),
                        &tsc_diagnostics::Cannot_find_module_0_Consider_using_resolveJsonModule_to_import_module_with_json_extension,
                        &[module_reference.to_string()],
                    );
                } else if mode == ModuleKind::ESNext
                    && resolution_is_node16_or_next
                    && is_extensionless_relative_path_import
                {
                    let mut suggested_ext = String::new();
                    if !tsc_tspath::has_trailing_directory_separator(module_reference) {
                        let absolute_ref = isf_nodes[importing_source_file]
                            .as_source_file()
                            .file_name()
                            .directory()
                            .resolve_file(module_reference);
                        suggested_ext = self.get_suggested_import_extension(&absolute_ref);
                    }
                    if !suggested_ext.is_empty() {
                        self.error(
                            Some(error_node),
                            &tsc_diagnostics::Relative_import_paths_need_explicit_file_extensions_in_ECMAScript_imports_when_moduleResolution_is_node16_or_nodenext_Did_you_mean_0,
                            &[format!("{module_reference}{suggested_ext}")],
                        );
                    } else {
                        self.error(
                            Some(error_node),
                            &tsc_diagnostics::Relative_import_paths_need_explicit_file_extensions_in_ECMAScript_imports_when_moduleResolution_is_node16_or_nodenext_Consider_adding_an_extension_to_the_import_path,
                            &[],
                        );
                    }
                } else if resolved_module
                    .as_ref()
                    .is_some_and(|r| !r.alternate_result.as_string().is_empty())
                {
                    let resolved = resolved_module.as_ref().unwrap();
                    let error_info = self.create_module_not_found_chain(
                        resolved,
                        error_node,
                        module_reference,
                        mode,
                        module_reference,
                    );
                    let diagnostic = self.new_diagnostic_chain_for_node(
                        Some(error_info),
                        Some(error_node),
                        module_not_found_error,
                        &[module_reference.to_string()],
                    );
                    self.add_diagnostic(&diagnostic);
                } else {
                    self.error(
                        Some(error_node),
                        module_not_found_error,
                        &[module_reference.to_string()],
                    );
                }
            }
        }

        None
    }

    /// `func (c *Checker) tryResolvePatternAmbientModule` (checker.go:15759).
    /// Resolves the module reference to a pattern ambient module, if one exists.
    /// If a resolved symbol from regular module resolution exists and we have an
    /// empty import attributes type, we prefer the resolved symbol.
    pub(crate) fn try_resolve_pattern_ambient_module(
        &mut self,
        resolved_symbol: Option<SymbolId>,
        module_reference: &str,
        import_attributes_type: TypeId,
    ) -> Option<SymbolId> {
        if self.is_empty_object_type(import_attributes_type) && resolved_symbol.is_some() {
            return resolved_symbol;
        }
        if !self.pattern_ambient_modules.is_empty() {
            let pattern_ambient_modules = self.pattern_ambient_modules.clone();
            let candidates: Vec<ast::PatternAmbientModule> =
                tsc_core::core::filter(&pattern_ambient_modules, |v| {
                    let Some(symbol) = v.symbol else { return false };
                    let module_attributes_type = self.get_type_of_module_import_attributes(symbol);
                    v.pattern.matches(module_reference)
                        && self
                            .is_type_assignable_to(import_attributes_type, module_attributes_type)
                })
                .into_owned();

            if !candidates.is_empty() {
                let augmentation = self
                    .pattern_ambient_module_augmentations
                    .get(module_reference)
                    .copied();
                let augmentation_target = self
                    .pattern_ambient_module_augmentation_targets
                    .get(module_reference)
                    .copied();

                if candidates.len() == 1 {
                    let merged_candidate = candidates[0].symbol.map(|s| self.get_merged_symbol(s));
                    if augmentation.is_some() && augmentation_target == merged_candidate {
                        return augmentation.map(|a| self.get_merged_symbol(a));
                    }
                    return merged_candidate;
                }

                let mut best_type_candidates: Vec<ast::PatternAmbientModule> = Vec::new();
                'outer: for (i, candidate) in candidates.iter().enumerate() {
                    let candidate_type = self.get_type_of_module_import_attributes(
                        candidate.symbol.expect("pattern ambient module symbol"),
                    );
                    for (j, other) in candidates.iter().enumerate() {
                        let other_type = self.get_type_of_module_import_attributes(
                            other.symbol.expect("pattern ambient module symbol"),
                        );
                        if i != j
                            && self.is_type_strict_subtype_of(other_type, candidate_type)
                            && !self.is_type_identical_to(other_type, candidate_type)
                        {
                            continue 'outer;
                        }
                    }
                    best_type_candidates.push(candidate.clone());
                }
                if best_type_candidates.len() == 1 {
                    let merged_candidate = best_type_candidates[0]
                        .symbol
                        .map(|s| self.get_merged_symbol(s));
                    if augmentation.is_some() && augmentation_target == merged_candidate {
                        return augmentation.map(|a| self.get_merged_symbol(a));
                    }
                    return merged_candidate;
                }
                let pattern = tsc_core::pattern::find_best_pattern_match(
                    &best_type_candidates,
                    |v| v.pattern.clone(),
                    module_reference,
                );
                let merged_candidate =
                    pattern.and_then(|p| p.symbol.map(|s| self.get_merged_symbol(s)));
                if augmentation.is_some() && augmentation_target == merged_candidate {
                    return augmentation.map(|a| self.get_merged_symbol(a));
                }
                return merged_candidate;
            }
        }
        resolved_symbol
    }

    /// `func (c *Checker) getSuggestedImportSource` (checker.go:15815).
    pub(crate) fn get_suggested_import_source(
        &mut self,
        module_reference: &str,
        ts_extension: &str,
        mode: tsc_core::compileroptions::ResolutionMode,
    ) -> String {
        let import_source_without_extension =
            tsc_tspath::remove_extension(module_reference, ts_extension);

        // Direct users to import source with .js extension if outputting an ES module.
        // @see https://github.com/microsoft/TypeScript/issues/42151
        if self.module_kind.is_non_node_esm() || mode == ModuleKind::ESNext {
            let prefer_ts = tsc_tspath::is_declaration_file_name(module_reference)
                && self.compiler_options.get_allow_importing_ts_extensions();
            let ext = if ts_extension == tsc_tspath::EXTENSION_MTS
                || ts_extension == tsc_tspath::EXTENSION_DMTS
            {
                if prefer_ts { ".mts" } else { ".mjs" }
            } else if ts_extension == tsc_tspath::EXTENSION_CTS
                || ts_extension == tsc_tspath::EXTENSION_DCTS
            {
                if prefer_ts { ".cts" } else { ".cjs" }
            } else if prefer_ts {
                ".ts"
            } else {
                ".js"
            };
            return format!("{import_source_without_extension}{ext}");
        }

        import_source_without_extension.to_string()
    }

    /// `func (c *Checker) getSuggestedImportExtension` (checker.go:15838).
    pub(crate) fn get_suggested_import_extension(
        &mut self,
        extensionless_import_path: &tsc_tspath::RootedFilePath,
    ) -> String {
        let program = self.program.as_ref().expect("program").clone();
        if crate::checker_types::Program::file_exists(
            program.as_ref(),
            &extensionless_import_path.append_suffix(".mts"),
        ) {
            return ".mjs".to_string();
        }
        if crate::checker_types::Program::file_exists(
            program.as_ref(),
            &extensionless_import_path.append_suffix(".ts"),
        ) {
            return ".js".to_string();
        }
        if crate::checker_types::Program::file_exists(
            program.as_ref(),
            &extensionless_import_path.append_suffix(".cts"),
        ) {
            return ".cjs".to_string();
        }
        if crate::checker_types::Program::file_exists(
            program.as_ref(),
            &extensionless_import_path.append_suffix(".mjs"),
        ) {
            return ".mjs".to_string();
        }
        if crate::checker_types::Program::file_exists(
            program.as_ref(),
            &extensionless_import_path.append_suffix(".js"),
        ) {
            return ".js".to_string();
        }
        if crate::checker_types::Program::file_exists(
            program.as_ref(),
            &extensionless_import_path.append_suffix(".cjs"),
        ) {
            return ".cjs".to_string();
        }
        if crate::checker_types::Program::file_exists(
            program.as_ref(),
            &extensionless_import_path.append_suffix(".tsx"),
        ) {
            return if self.compiler_options.jsx == tsc_core::options_generated::JsxEmit::Preserve {
                ".jsx".to_string()
            } else {
                ".js".to_string()
            };
        }
        if crate::checker_types::Program::file_exists(
            program.as_ref(),
            &extensionless_import_path.append_suffix(".jsx"),
        ) {
            return ".jsx".to_string();
        }
        if crate::checker_types::Program::file_exists(
            program.as_ref(),
            &extensionless_import_path.append_suffix(".json"),
        ) {
            return ".json".to_string();
        }
        String::new()
    }

    /// `func (c *Checker) errorOnImplicitAnyModule` (checker.go:15862).
    pub(crate) fn error_on_implicit_any_module(
        &mut self,
        is_error: bool,
        error_node: NodeId,
        mode: tsc_core::compileroptions::ResolutionMode,
        resolved_module: &tsc_module::ResolvedModule,
        module_reference: &str,
    ) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((error_node).file_index());
        if is_side_effect_import(error_node, &nodes) {
            return;
        }

        let mut error_info = None;
        if !tsc_tspath::is_external_module_name_relative(module_reference)
            && !resolved_module.package_id.name.is_empty()
        {
            error_info = Some(self.create_module_not_found_chain(
                resolved_module,
                error_node,
                module_reference,
                mode,
                &resolved_module.package_id.name.clone(),
            ));
        }
        let diagnostic = self.new_diagnostic_chain_for_node(
            error_info,
            Some(error_node),
            &tsc_diagnostics::Could_not_find_a_declaration_file_for_module_0_1_implicitly_has_an_any_type,
            &[
                module_reference.to_string(),
                resolved_module.resolved_file_name.as_string().to_string(),
            ],
        );
        self.add_error_or_suggestion(is_error, &diagnostic);
    }

    /// `func (c *Checker) createModuleNotFoundChain` (checker.go:15883).
    pub(crate) fn create_module_not_found_chain(
        &mut self,
        resolved_module: &tsc_module::ResolvedModule,
        error_node: NodeId,
        module_reference: &str,
        mode: tsc_core::compileroptions::ResolutionMode,
        package_name: &str,
    ) -> DiagnosticRef {
        let _ = resolved_module;
        // Store the original packageName for repopulateInfo before any modifications
        let stored_package_name = if package_name == module_reference {
            String::new()
        } else {
            package_name.to_string()
        };

        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((error_node).file_index());
        let source_file =
            ast::get_source_file_of_node(Some(error_node), &nodes).expect("source file");
        let details = crate::utilities::create_module_not_found_chain(
            self.program.as_ref().expect("program").as_ref(),
            nodes[source_file].as_source_file(),
            module_reference,
            mode,
            package_name,
        );
        let result = self.new_diagnostic_for_node(Some(error_node), details.message, &details.args);
        ast::diagnostic::lock_diagnostic(&result).set_repopulate_info(Some(
            ast::diagnostic::RepopulateDiagnosticInfo {
                kind: ast::diagnostic::RepopulateDiagnosticKind::ModuleNotFound,
                module_reference: module_reference.to_string(),
                mode,
                package_name: stored_package_name,
            },
        ));
        result
    }

    /// `func (c *Checker) createModeMismatchDetails` (checker.go:15901).
    /// `sourceFile` is the source-file `NodeId` (Go's `*ast.SourceFile`).
    pub(crate) fn create_mode_mismatch_details(
        &mut self,
        source_file: NodeId,
        error_node: NodeId,
    ) -> DiagnosticRef {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((source_file).file_index());
        let details = crate::utilities::create_mode_mismatch_details(
            self.program.as_ref().expect("program").as_ref(),
            nodes[source_file].as_source_file(),
        );
        let result = self.new_diagnostic_for_node(Some(error_node), details.message, &details.args);
        ast::diagnostic::lock_diagnostic(&result).set_repopulate_info(Some(
            ast::diagnostic::RepopulateDiagnosticInfo {
                kind: ast::diagnostic::RepopulateDiagnosticKind::ModeMismatch,
                ..Default::default()
            },
        ));
        result
    }

    /// `func (c *Checker) tryFindAmbientModule` (checker.go:15910).
    pub(crate) fn try_find_ambient_module(
        &mut self,
        module_name: &str,
        with_augmentations: bool,
    ) -> Option<SymbolId> {
        if tsc_tspath::is_external_module_name_relative(module_name) {
            return None;
        }
        let globals = self.globals.borrow().clone();
        let symbol = self.get_symbol(
            &globals,
            &format!("\"{module_name}\""),
            ast::SymbolFlags::VALUE_MODULE,
        );
        // merged symbol is module declaration symbol combined with all augmentations
        if with_augmentations {
            return symbol.map(|s| self.get_merged_symbol(s));
        }
        symbol
    }

    /// `func (c *Checker) GetAmbientModules` (checker.go:15922). Public API.
    pub fn get_ambient_modules(&mut self) -> Vec<SymbolId> {
        if !self.ambient_modules_once.is_completed() {
            // `sync.Once` body — computed into locals because the
            // `ambient_modules`/`globals` writes can't borrow `self` through
            // `Once::call_once`'s closure.
            let mut ambient_modules = Vec::new();
            let mut seen: FxHashSet<SymbolId> = FxHashSet::default();
            let globals = self.globals.borrow().clone();
            for (name, &global) in globals.entries() {
                if ast::symbol::is_ambient_module_symbol_name(name) {
                    ambient_modules.push(global);
                    seen.insert(global);
                }
            }
            let pattern_ambient_modules = self.pattern_ambient_modules.clone();
            for module in &pattern_ambient_modules {
                if let Some(module_symbol) = module.symbol {
                    let symbol = self.get_merged_symbol(module_symbol);
                    if !seen.contains(&symbol) {
                        ambient_modules.push(symbol);
                        seen.insert(symbol);
                    }
                }
            }
            self.ambient_modules = ambient_modules;
            self.ambient_modules_once.call_once(|| {});
        }
        self.ambient_modules.clone()
    }

    /// `func (c *Checker) resolveExternalModuleSymbol` (checker.go:15942).
    pub fn resolve_external_module_symbol(
        &mut self,
        module_symbol: Option<SymbolId>,
        dont_resolve_alias: bool,
    ) -> Option<SymbolId> {
        if let Some(module_symbol) = module_symbol {
            let export_equals = self
                .sym(module_symbol)
                .exports
                .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
                .copied();
            let export_equals =
                export_equals.map(|s| self.resolve_symbol_ex(s, dont_resolve_alias));
            if let Some(export_equals) = export_equals {
                return Some(self.get_merged_symbol(export_equals));
            }
        }
        module_symbol
    }

    /// `func (c *Checker) resolveESModuleSymbol` (checker.go:15954).
    /// Resolves the given external module symbol, possibly removing call and
    /// construct signatures or creating a wrapper module with a synthetic
    /// default.
    pub(crate) fn resolve_es_module_symbol(
        &mut self,
        module_symbol: Option<SymbolId>,
        node: NodeId,
        module_specifier: Option<NodeId>,
    ) -> Option<SymbolId> {
        let mut symbol = self.resolve_external_module_symbol(module_symbol, true);
        let is_non_local = {
            let arena = self.symbol_arena.borrow();
            ast::is_non_local_alias(
                symbol.map(|s| &arena[s.index()]),
                ast::SymbolFlags::VALUE | ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE,
            )
        };
        if is_non_local {
            // When the module has an export= with a pure alias, we transitively resolve and propagate any typeOnlyDeclaration
            let target = symbol.unwrap();
            symbol = Some(match self.get_symbol_of_declaration(node) {
                Some(source) => {
                    let indir = self.resolve_indirection_alias(source, target);
                    self.get_merged_symbol(indir)
                }
                None => {
                    let tgt = self.resolve_alias(target);
                    self.get_merged_symbol(tgt)
                }
            });
        }
        let symbol = symbol?;
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let reference_parent = module_specifier.and_then(|ms| nodes[ms].parent);
        let mut namespace_import = None;
        if let Some(rp) = reference_parent
            && ast::is_import_declaration(&nodes[rp])
        {
            namespace_import = ast::get_namespace_declaration_node(&nodes[rp], &nodes);
        }
        if namespace_import.is_some()
            || reference_parent.is_some_and(|rp| ast::is_import_call(&nodes[rp], &nodes))
        {
            let reference_parent = reference_parent.unwrap();
            let reference = if ast::is_import_call(&nodes[reference_parent], &nodes) {
                nodes[reference_parent]
                    .arguments()
                    .and_then(|a| a.first().copied())
                    .expect("import call argument")
            } else {
                nodes[reference_parent]
                    .module_specifier()
                    .expect("module specifier")
            };
            let typ = self.get_type_of_symbol(symbol);
            let import_attributes_type =
                self.get_import_attributes_type_for_module_specifier(reference);
            if let Some(default_only_type) = self.get_type_with_synthetic_default_only(
                typ,
                symbol,
                module_symbol,
                reference,
                import_attributes_type,
            ) {
                return Some(self.clone_type_as_module_type(
                    symbol,
                    default_only_type,
                    Some(reference_parent),
                ));
            }

            let target_file = {
                let declarations = self
                    .sym(module_symbol.expect("module symbol"))
                    .declarations
                    .clone();
                declarations.iter().copied().find(|&d| {
                    let __program = self.program.clone().expect("program");
                    let dn = __program.nodes((d).file_index());
                    ast::is_source_file(&dn[d])
                })
            };
            let usage_mode = self.get_emit_syntax_for_module_specifier_expression(reference);
            let mut export_module_dot_exports_symbol = None;
            if namespace_import.is_some()
                && target_file.is_some()
                && (ModuleKind::Node20..=ModuleKind::NodeNext).contains(&self.module_kind)
                && usage_mode == ModuleKind::CommonJS
                && self
                    .program
                    .as_ref()
                    .expect("program")
                    .get_implied_node_format_for_emit(
                        self.program_nodes(target_file.unwrap())[target_file.unwrap()]
                            .as_source_file(),
                    )
                    == ModuleKind::ESNext
            {
                export_module_dot_exports_symbol = self.get_export_of_module(
                    symbol,
                    ast::symbol::INTERNAL_SYMBOL_NAME_MODULE_EXPORTS,
                    namespace_import,
                    true,
                );
            }
            if let Some(export_module_dot_exports_symbol) = export_module_dot_exports_symbol {
                if self.has_signatures(typ) {
                    return Some(self.clone_type_as_module_type(
                        export_module_dot_exports_symbol,
                        typ,
                        Some(reference_parent),
                    ));
                }
                return Some(export_module_dot_exports_symbol);
            }

            let is_esm_cjs_ref = target_file.is_some()
                && is_esm_format_import_importing_commonjs_format_file(
                    usage_mode,
                    self.program
                        .as_ref()
                        .expect("program")
                        .get_implied_node_format_for_emit(
                            self.program_nodes(target_file.unwrap())[target_file.unwrap()]
                                .as_source_file(),
                        ),
                );
            if self.has_signatures(typ)
                || self
                    .get_property_of_type_ex(
                        typ,
                        ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT,
                        true,  /*skipObjectFunctionPropertyAugment*/
                        false, /*includeTypeOnlyMembers*/
                    )
                    .is_some()
                || is_esm_cjs_ref
            {
                let module_type = if self
                    .types_handle()
                    .get(typ)
                    .flags
                    .intersects(TypeFlags::STRUCTURED_TYPE)
                {
                    self.get_type_with_synthetic_default_import_type(
                        typ,
                        symbol,
                        module_symbol,
                        reference,
                    )
                } else {
                    {
                        let parent = self.sym(symbol).parent;
                        self.create_default_property_wrapper_for_module(symbol, parent, None)
                    }
                };
                return Some(self.clone_type_as_module_type(
                    symbol,
                    module_type,
                    Some(reference_parent),
                ));
            }
        }
        Some(symbol)
    }

    /// `func (c *Checker) hasSignatures` (checker.go:16010).
    pub(crate) fn has_signatures(&mut self, t: TypeId) -> bool {
        !self
            .get_signatures_of_structured_type(t, SignatureKind::Call)
            .is_empty()
            || !self
                .get_signatures_of_structured_type(t, SignatureKind::Construct)
                .is_empty()
    }

    /// `func (c *Checker) getTypeWithSyntheticDefaultOnly` (checker.go:16018).
    pub(crate) fn get_type_with_synthetic_default_only(
        &mut self,
        t: TypeId,
        symbol: SymbolId,
        original_symbol: Option<SymbolId>,
        module_specifier: NodeId,
        import_attributes_type: Option<TypeId>,
    ) -> Option<TypeId> {
        let has_default_only =
            self.is_only_importable_as_default(module_specifier, None, import_attributes_type);
        if has_default_only && !self.is_error_type(t) {
            let key = CachedTypeKey {
                kind: CachedTypeKind::DefaultOnlyType,
                type_id: self.types.get_ref(t).id,
            };
            if let Some(&cached) = self.cached_types.get(&key) {
                return Some(cached);
            }
            let result =
                self.create_default_property_wrapper_for_module(symbol, original_symbol, None);
            self.cached_types.insert(key, result);
            return Some(result);
        }
        None
    }

    /// `func (c *Checker) getTypeWithSyntheticDefaultImportType` (checker.go:16032).
    pub(crate) fn get_type_with_synthetic_default_import_type(
        &mut self,
        t: TypeId,
        symbol: SymbolId,
        original_symbol: Option<SymbolId>,
        module_specifier: NodeId,
    ) -> TypeId {
        if !self.is_error_type(t) {
            let key = CachedTypeKey {
                kind: CachedTypeKind::SyntheticType,
                type_id: self.types.get_ref(t).id,
            };
            if let Some(&cached) = self.cached_types.get(&key) {
                return cached;
            }
            let file = {
                let declarations = self
                    .sym(original_symbol.expect("originalSymbol"))
                    .declarations
                    .clone();
                declarations.iter().copied().find(|&d| {
                    let __program = self.program.clone().expect("program");
                    let dn = __program.nodes((d).file_index());
                    ast::is_source_file(&dn[d])
                })
            };
            let has_synthetic_default = self.can_have_synthetic_default(
                file,
                original_symbol.expect("originalSymbol"),
                false, /*dontResolveAlias*/
                module_specifier,
            );
            let synthetic_type = if has_synthetic_default {
                let anonymous_symbol = self.new_symbol(
                    ast::SymbolFlags::TYPE_LITERAL,
                    ast::symbol::INTERNAL_SYMBOL_NAME_TYPE,
                );
                let declarations = self
                    .sym(original_symbol.expect("originalSymbol"))
                    .declarations
                    .clone();
                self.sym_mut(anonymous_symbol).declarations = declarations;
                let default_containing_object = self.create_default_property_wrapper_for_module(
                    symbol,
                    original_symbol,
                    Some(anonymous_symbol),
                );
                self.value_symbol_links.get(anonymous_symbol).resolved_type =
                    Some(default_containing_object);
                if self.is_valid_spread_type(t) {
                    self.get_spread_type(
                        t,
                        default_containing_object,
                        Some(anonymous_symbol),
                        ObjectFlags::NONE,
                        false, /*readonly*/
                    )
                } else {
                    default_containing_object
                }
            } else {
                t
            };
            self.cached_types.insert(key, synthetic_type);
            return synthetic_type;
        }
        t
    }

    /// `func (c *Checker) isCommonJSRequire` (checker.go:16060).
    pub(crate) fn is_common_js_require(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if !ast::is_require_call(
            &nodes[node],
            true, /*requireStringLiteralLikeArgument*/
            &nodes,
        ) {
            return false;
        }
        let expression = nodes[node].expression();
        if !expression.is_some_and(|e| ast::is_identifier(&nodes[e])) {
            panic!("Expected identifier for require call");
        }
        // Make sure require is not a local function
        let expression = expression.unwrap();
        let text = nodes[expression].text(&nodes).into_owned();
        let resolved_require = call_resolve_name(
            self,
            Some(expression),
            &text,
            ast::SymbolFlags::VALUE,
            None,  /*nameNotFoundMessage*/
            true,  /*isUse*/
            false, /*excludeGlobals*/
         None,
        );
        if resolved_require == Some(self.require_symbol) {
            return true;
        }
        // project includes symbol named 'require' - make sure that it is ambient and local non-alias
        let Some(resolved_require) = resolved_require else {
            return false;
        };
        if self
            .sym(resolved_require)
            .flags
            .intersects(ast::SymbolFlags::ALIAS)
        {
            return false;
        }

        let target_declaration_kind = {
            let flags = self.sym(resolved_require).flags;
            if flags.intersects(ast::SymbolFlags::FUNCTION) {
                ast::Kind::FunctionDeclaration
            } else if flags.intersects(ast::SymbolFlags::VARIABLE) {
                ast::Kind::VariableDeclaration
            } else {
                ast::Kind::Unknown
            }
        };
        if target_declaration_kind != ast::Kind::Unknown {
            // `ast.GetDeclarationOfKind(resolvedRequire, targetDeclarationKind)`
            // — declarations may live in different files, so each is checked
            // in its own arena.
            let declarations = self.sym(resolved_require).declarations.clone();
            let decl = declarations.iter().copied().find(|&d| {
                let __program = self.program.clone().expect("program");
                let dn = __program.nodes((d).file_index());
                dn[d].kind == target_declaration_kind
            });
            // function/variable declaration should be ambient
            return decl.is_some_and(|d| {
                let __program = self.program.clone().expect("program");
                let dn = __program.nodes((d).file_index());
                dn[d].flags.intersects(ast::NodeFlags::AMBIENT)
            });
        }
        false
    }

    /// `func (c *Checker) createDefaultPropertyWrapperForModule` (checker.go:16093).
    pub(crate) fn create_default_property_wrapper_for_module(
        &mut self,
        symbol: SymbolId,
        original_symbol: Option<SymbolId>,
        anonymous_symbol: Option<SymbolId>,
    ) -> TypeId {
        let mut member_table = SymbolTable::default();
        let new_symbol = self.new_symbol(
            ast::SymbolFlags::ALIAS,
            ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT,
        );
        self.sym_mut(new_symbol).parent = original_symbol;
        let name_type = self.get_string_literal_type("default");
        self.value_symbol_links.get(new_symbol).name_type = Some(name_type);
        let target = self.resolve_symbol(symbol);
        self.alias_symbol_links.get(new_symbol).alias_target = Some(target);
        member_table.set(
            ast::symbol::INTERNAL_SYMBOL_NAME_DEFAULT.into(),
            new_symbol,
        );
        let anonymous_symbol = match anonymous_symbol {
            Some(s) => Some(s),
            None => original_symbol.map(|original_symbol| {
                let anonymous_symbol = self.new_symbol(
                    ast::SymbolFlags::OBJECT_LITERAL,
                    ast::symbol::INTERNAL_SYMBOL_NAME_OBJECT,
                );
                let declarations = self.sym(original_symbol).declarations.clone();
                self.sym_mut(anonymous_symbol).declarations = declarations;
                anonymous_symbol
            }),
        };
        self.new_anonymous_type(anonymous_symbol, member_table, &[], &[], &[])
    }

    /// `func (c *Checker) cloneTypeAsModuleType` (checker.go:16107).
    pub(crate) fn clone_type_as_module_type(
        &mut self,
        symbol: SymbolId,
        module_type: TypeId,
        reference_parent: Option<NodeId>,
    ) -> SymbolId {
        let (flags, name, declarations, value_declaration, members, exports, parent) = {
            let s = self.sym(symbol);
            (
                s.flags,
                s.name.clone(),
                s.declarations.clone(),
                s.value_declaration,
                s.members.clone(),
                s.exports.clone(),
                s.parent,
            )
        };
        let result = self.new_symbol(flags, &name);
        self.sym_mut(result).declarations = declarations;
        self.sym_mut(result).value_declaration = value_declaration;
        self.sym_mut(result).members = members;
        self.sym_mut(result).exports = exports;
        self.sym_mut(result).parent = parent;
        self.export_type_links.get(result).target = Some(symbol);
        self.export_type_links.get(result).originating_import = reference_parent;
        let resolved_module_type = self.resolve_structured_type_members(module_type);
        let (members, index_infos) = {
            let guard = self.types.get_ref(resolved_module_type);
            let resolved = guard.as_structured_type().expect("resolved module type");
            (resolved.members.clone(), resolved.index_infos.clone())
        };
        // StructuredType stores `Vec<IndexInfo>` inline; `newAnonymousType`
        // takes arena `IndexInfoId`s — re-allocate each info.
        let index_infos: Vec<IndexInfoId> = index_infos
            .iter()
            .map(|info| self.index_info_arena.alloc(info.clone()))
            .collect();
        self.value_symbol_links.get(result).resolved_type =
            Some(self.new_anonymous_type(Some(result), members, &[], &[], &index_infos));
        result
    }

    /// `func (c *Checker) getTargetOfAliasDeclaration` (checker.go:16122).
    pub(crate) fn get_target_of_alias_declaration(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::ImportEqualsDeclaration | ast::Kind::VariableDeclaration => {
                self.get_target_of_import_equals_declaration(node)
            }
            ast::Kind::ImportClause => self.get_target_of_import_clause(node),
            ast::Kind::NamespaceImport => self.get_target_of_namespace_import(node),
            ast::Kind::NamespaceExport => self.get_target_of_namespace_export(node),
            ast::Kind::ImportSpecifier | ast::Kind::BindingElement => {
                self.get_target_of_import_specifier(node)
            }
            ast::Kind::ExportSpecifier => self.get_target_of_export_specifier(
                node,
                ast::SymbolFlags::VALUE | ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE,
                true, /*dontRecursivelyResolve*/
            ),
            ast::Kind::ExportAssignment => self.get_target_of_export_assignment(node),
            ast::Kind::BinaryExpression => self.get_target_of_binary_expression(node),
            ast::Kind::NamespaceExportDeclaration => {
                self.get_target_of_namespace_export_declaration(node)
            }
            ast::Kind::ShorthandPropertyAssignment => {
                let name = nodes[node]
                    .as_shorthand_property_assignment()
                    .named_member_base
                    .name
                    .expect("shorthand property name");
                self.resolve_entity_name(
                    Some(name),
                    ast::SymbolFlags::VALUE | ast::SymbolFlags::TYPE | ast::SymbolFlags::NAMESPACE,
                    true, /*ignoreErrors*/
                    true, /*dontRecursivelyResolve*/
                    None, /*location*/
                )
            }
            ast::Kind::PropertyAssignment => {
                let initializer = nodes[node]
                    .initializer()
                    .expect("property assignment initializer");
                self.get_target_of_alias_like_expression(initializer)
            }
            ast::Kind::ElementAccessExpression | ast::Kind::PropertyAccessExpression => {
                self.get_target_of_access_expression(node)
            }
            other => panic!("Unhandled case in getTargetOfAliasDeclaration: {other:?}"),
        }
    }

    /// `func (c *Checker) resolveEntityName` (checker.go:16158).
    /// Resolves a qualified name and any involved aliases.
    pub(crate) fn resolve_entity_name(
        &mut self,
        name: Option<NodeId>,
        meaning: ast::SymbolFlags,
        ignore_errors: bool,
        dont_resolve_alias: bool,
        location: Option<NodeId>,
    ) -> Option<SymbolId> {
        self.resolve_entity_name_live(
            name,
            meaning,
            ignore_errors,
            dont_resolve_alias,
            location,
            None,
        )
    }

    /// `resolve_entity_name` with a live-arena override for the checked-out
    /// working buffer — see [`crate::printer_util::arena_view`].
    pub(crate) fn resolve_entity_name_live(
        &mut self,
        name: Option<NodeId>,
        meaning: ast::SymbolFlags,
        ignore_errors: bool,
        dont_resolve_alias: bool,
        location: Option<NodeId>,
        live_nodes: Option<&[ast::Node]>,
    ) -> Option<SymbolId> {
        let name = name?;
        let __program = self.program.clone().expect("program");
        let nodes = crate::printer_util::arena_view(
            &__program,
            live_nodes.unwrap_or(&[]),
            name.file_index(),
        );
        if ast::node_is_missing(Some(name), &nodes) {
            return None;
        }
        let mut symbol: Option<SymbolId>;
        match nodes[name].kind {
            ast::Kind::Identifier => {
                let mut message: Option<&'static tsc_diagnostics::Message> = None;
                if !ignore_errors {
                    if meaning == ast::SymbolFlags::NAMESPACE
                        || ast::node_is_synthesized(&nodes[name])
                    {
                        message = Some(&tsc_diagnostics::Cannot_find_namespace_0);
                    } else {
                        let first_identifier = ast::get_first_identifier(name, &nodes);
                        message = self.get_cannot_find_name_diagnostic_for_name(first_identifier);
                    }
                }
                let resolve_location = location.or(Some(name));
                let name_text = nodes[name].text(&nodes).into_owned();
                if meaning == ast::SymbolFlags::NAMESPACE {
                    symbol = call_resolve_name(
                        self,
                        resolve_location,
                        &name_text,
                        meaning,
                        None,
                        true,  /*isUse*/
                        false, /*excludeGlobals*/
                     live_nodes,
                    )
                    .map(|s| self.get_merged_symbol(s));
                    if symbol.is_none() {
                        let alias = call_resolve_name(
                            self,
                            resolve_location,
                            &name_text,
                            ast::SymbolFlags::ALIAS,
                            None,
                            true,  /*isUse*/
                            false, /*excludeGlobals*/
                         live_nodes,
                        )
                        .map(|s| self.get_merged_symbol(s));
                        if let Some(alias) = alias
                            && self.sym(alias).name
                                == ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                        {
                            // resolve typedefs exported from commonjs, stored on the module symbol
                            symbol = self.sym(alias).parent;
                        }
                    }
                    if symbol.is_none() && message.is_some() {
                        call_resolve_name(
                            self,
                            resolve_location,
                            &name_text,
                            meaning,
                            message,
                            true,  /*isUse*/
                            false, /*excludeGlobals*/
                         live_nodes,
                        );
                    }
                } else {
                    symbol = call_resolve_name(
                        self,
                        resolve_location,
                        &name_text,
                        meaning,
                        message,
                        true,  /*isUse*/
                        false, /*excludeGlobals*/
                     live_nodes,
                    )
                    .map(|s| self.get_merged_symbol(s));
                }
            }
            ast::Kind::QualifiedName => {
                let (left, right) = {
                    let qualified = nodes[name].as_qualified_name();
                    (qualified.left, qualified.right)
                };
                symbol = self.resolve_qualified_name(
                    name,
                    left.expect("qualified name left"),
                    right.expect("qualified name right"),
                    meaning,
                    ignore_errors,
                    location,
                    live_nodes,
                );
            }
            ast::Kind::PropertyAccessExpression => {
                let (expression, right) = {
                    let access = nodes[name].as_property_access_expression();
                    (access.expression, access.name)
                };
                symbol = self.resolve_qualified_name(
                    name,
                    expression.expect("property access expression"),
                    right.expect("property access name"),
                    meaning,
                    ignore_errors,
                    location,
                    live_nodes,
                );
            }
            _ => panic!("Unknown entity name kind {:?} for node {:?}", nodes[name].kind, name),
        }
        if let Some(mut sym) = symbol
            && sym != self.unknown_symbol
        {
            if !ast::node_is_synthesized(&nodes[name])
                && ast::is_entity_name(&nodes[name])
                && (self.sym(sym).flags.intersects(ast::SymbolFlags::ALIAS)
                    || nodes[name]
                        .parent
                        .is_some_and(|p| nodes[p].kind == ast::Kind::ExportAssignment))
            {
                let alias_declaration = get_alias_declaration_from_name(name, &nodes);
                self.mark_symbol_of_alias_declaration_if_type_only(alias_declaration, None);
            }
            // We know a symbol with the given meaning exists along the alias chain, so resolve until we find it.
            while !self.sym(sym).flags.intersects(meaning)
                && !dont_resolve_alias
                && self.sym(sym).flags.intersects(ast::SymbolFlags::ALIAS)
            {
                sym = self.resolve_alias(sym);
            }
            return Some(sym);
        }
        symbol
    }

    /// `func (c *Checker) resolveQualifiedName` (checker.go:16214).
    pub(crate) fn resolve_qualified_name(
        &mut self,
        name: NodeId,
        left: NodeId,
        right: NodeId,
        meaning: ast::SymbolFlags,
        ignore_errors: bool,
        location: Option<NodeId>,
        live_nodes: Option<&[ast::Node]>,
    ) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = crate::printer_util::arena_view(
            &__program,
            live_nodes.unwrap_or(&[]),
            name.file_index(),
        );
        let namespace = self.resolve_entity_name_live(
            Some(left),
            ast::SymbolFlags::NAMESPACE,
            ignore_errors,
            false, /*dontResolveAlias*/
            location,
            live_nodes,
        );
        let Some(mut namespace) = namespace else {
            return None;
        };
        if ast::node_is_missing(Some(right), &nodes) {
            return None;
        }
        if namespace == self.unknown_symbol {
            return Some(namespace);
        }
        let namespace_value_declaration = self.sym(namespace).value_declaration;
        if let Some(vd) = namespace_value_declaration {
            let __program = self.program.clone().expect("program");
            let vdn = crate::printer_util::arena_view(
                &__program,
                live_nodes.unwrap_or(&[]),
                vd.file_index(),
            );
            if ast::is_in_js_file(Some(vd), &vdn)
                && self.compiler_options.get_module_resolution_kind()
                    != ModuleResolutionKind::Bundler
                && ast::is_variable_declaration(&vdn[vd])
                && vdn[vd]
                    .initializer()
                    .is_some_and(|initializer| self.is_common_js_require(initializer))
            {
                let initializer = vdn[vd].initializer().unwrap();
                let __program = self.program.clone().expect("program");
                let init_nodes = crate::printer_util::arena_view(
                    &__program,
                    live_nodes.unwrap_or(&[]),
                    initializer.file_index(),
                );
                if let Some(module_name) = init_nodes[initializer]
                    .arguments()
                    .and_then(|a| a.first().copied())
                {
                    if let Some(module_sym) = self.resolve_external_module_name(
                        module_name,
                        Some(module_name),
                        false, /*ignoreErrors*/
                        None,
                    ) {
                        if let Some(resolved_module_symbol) =
                            self.resolve_external_module_symbol(Some(module_sym), false)
                        {
                            namespace = resolved_module_symbol;
                        }
                    }
                }
            }
        }
        let text = nodes[right].text(&nodes).into_owned();
        let mut symbol = {
            let exports = self.get_exports_of_symbol(namespace);
            self.get_symbol(&exports, &text, meaning)
                .map(|s| self.get_merged_symbol(s))
        };
        if symbol.is_none()
            && self
                .sym(namespace)
                .flags
                .intersects(ast::SymbolFlags::ALIAS)
        {
            // `namespace` can be resolved further if there was a symbol merge with a re-export
            let resolved_namespace = self.resolve_alias(namespace);
            let exports = self.get_exports_of_symbol(resolved_namespace);
            symbol = self
                .get_symbol(&exports, &text, meaning)
                .map(|s| self.get_merged_symbol(s));
        }
        if symbol.is_none() {
            if !ignore_errors {
                let namespace_name = self.get_fully_qualified_name(namespace, None);
                let declaration_name =
                    tsc_scanner::utilities::declaration_name_to_string(Some(right), &nodes);
                let suggestion_for_nonexistent_module =
                    self.get_suggested_symbol_for_nonexistent_module(right, namespace);
                if let Some(suggestion_for_nonexistent_module) = suggestion_for_nonexistent_module {
                    let suggestion_name = self.symbol_to_string(suggestion_for_nonexistent_module);
                    self.error(
                        Some(right),
                        &tsc_diagnostics::X_0_has_no_exported_member_named_1_Did_you_mean_2,
                        &[namespace_name, declaration_name, suggestion_name],
                    );
                    return None;
                }
                let mut containing_qualified_name = None;
                if ast::is_qualified_name(&nodes[name]) {
                    containing_qualified_name =
                        Some(get_containing_qualified_name_node(name, &nodes));
                }
                let can_suggest_typeof = self.global_object_type != TypeId::NONE
                    && meaning.intersects(ast::SymbolFlags::TYPE)
                    && containing_qualified_name.is_some()
                    && !nodes[containing_qualified_name.unwrap()]
                        .parent
                        .is_some_and(|p| ast::is_type_of_expression(&nodes[p]))
                    && self
                        .try_get_qualified_name_as_value(containing_qualified_name.unwrap())
                        .is_some();
                if can_suggest_typeof {
                    let suggestion = ast::entity_name_to_string(
                        containing_qualified_name.unwrap(),
                        &nodes,
                        None,
                    );
                    self.error(
                        containing_qualified_name,
                        &tsc_diagnostics::X_0_refers_to_a_value_but_is_being_used_as_a_type_here_Did_you_mean_typeof_0,
                        &[suggestion],
                    );
                    return None;
                }
                if meaning.intersects(ast::SymbolFlags::NAMESPACE) {
                    if let Some(parent) = nodes[name].parent
                        && ast::is_qualified_name(&nodes[parent])
                    {
                        let exports = self.get_exports_of_symbol(namespace);
                        let exported_type_symbol = self
                            .get_symbol(&exports, &text, ast::SymbolFlags::TYPE)
                            .map(|s| self.get_merged_symbol(s));
                        if let Some(exported_type_symbol) = exported_type_symbol {
                            let qualified = nodes[parent].as_qualified_name();
                            let right_name = qualified
                                .right
                                .map(|r| nodes[r].text(&nodes).into_owned())
                                .unwrap_or_default();
                            let symbol_name = self.symbol_to_string(exported_type_symbol);
                            self.error(
                                qualified.right,
                                &tsc_diagnostics::Cannot_access_0_1_because_0_is_a_type_but_not_a_namespace_Did_you_mean_to_retrieve_the_type_of_the_property_1_in_0_with_0_1,
                                &[symbol_name, right_name],
                            );
                            return None;
                        }
                    }
                }
                self.error(
                    Some(right),
                    &tsc_diagnostics::Namespace_0_has_no_exported_member_1,
                    &[namespace_name, declaration_name],
                );
            }
        }
        symbol
    }

    /// `func (c *Checker) tryGetQualifiedNameAsValue` (checker.go:16277).
    pub(crate) fn try_get_qualified_name_as_value(&mut self, node: NodeId) -> Option<SymbolId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let id = ast::get_first_identifier(node, &nodes);
        let text = nodes[id].text(&nodes).into_owned();
        let mut symbol = call_resolve_name(
            self,
            Some(id),
            &text,
            ast::SymbolFlags::VALUE,
            None,  /*nameNotFoundMessage*/
            true,  /*isUse*/
            false, /*excludeGlobals*/
         None,
        )?;
        let mut n = id;
        while let Some(parent) = nodes[n].parent {
            if !ast::is_qualified_name(&nodes[parent]) {
                break;
            }
            let t = self.get_type_of_symbol(symbol);
            let right_text = nodes[parent]
                .as_qualified_name()
                .right
                .map(|r| nodes[r].text(&nodes).into_owned())
                .unwrap_or_default();
            symbol = self.get_property_of_type(t, &right_text)?;
            n = parent;
        }
        Some(symbol)
    }
    // __APPEND2__
}

/// `isContainedByNamespace` (checker.go) — file-local helper for
/// `getTargetOfExportAssignment`; duplicates the `checker_a` copy since it is
/// module-private there.
fn is_contained_by_namespace(node: NodeId, nodes: &[ast::Node]) -> bool {
    let mut container = nodes[node].parent;
    if !container.is_some_and(|c| ast::is_source_file(&nodes[c])) {
        container = container.and_then(|c| nodes[c].parent);
    }
    container.is_some_and(|c| {
        ast::is_module_declaration(&nodes[c]) && !ast::is_ambient_module(&nodes[c], nodes)
    })
}

/// `getExternalModuleRequireArgument` (checker.go:14475).
fn get_external_module_require_argument(node: NodeId, nodes: &[ast::Node]) -> Option<NodeId> {
    if ast::is_variable_declaration_initialized_to_require(node, nodes) {
        return nodes[node]
            .initializer()
            .and_then(|i| nodes[i].arguments().and_then(|a| a.first().copied()));
    }
    None
}

/// `getModuleSpecifierFromNode` (checker.go:14484).
pub(crate) fn get_module_specifier_from_node(node: NodeId, nodes: &[ast::Node]) -> Option<NodeId> {
    match nodes[node].kind {
        ast::Kind::ImportDeclaration
        | ast::Kind::JSImportDeclaration
        | ast::Kind::ExportDeclaration => nodes[node].module_specifier(),
        ast::Kind::ImportEqualsDeclaration => {
            let module_reference = nodes[node].as_import_equals_declaration().module_reference;
            if module_reference.is_some_and(|mr| ast::is_external_module_reference(&nodes[mr])) {
                module_reference.and_then(|mr| nodes[mr].expression())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `isSideEffectImport` (checker.go:14950).
fn is_side_effect_import(node: NodeId, nodes: &[ast::Node]) -> bool {
    let ancestor = ast::find_ancestor(Some(node), nodes, &mut |n, _| ast::is_import_declaration(n));
    ancestor.is_some_and(|a| nodes[a].import_clause().is_none())
}

/// `resolutionExtensionIsTSOrJson` (checker.go:15776).
/// `ResolvedModule.extension` is a plain `String` in the port (Go's
/// `tspath.Extension`), so this takes `&str`.
fn resolution_extension_is_ts_or_json(ext: &str) -> bool {
    tsc_tspath::extension_is_ts(ext) || ext == tsc_tspath::EXTENSION_JSON || ext == ".d.json.ts"
}

/// `isShorthandAmbientModuleSymbol` (checker.go:14804) — delegates to
/// `isShorthandAmbientModule` (utilities.go:197).
fn is_shorthand_ambient_module_symbol(c: &Checker, module_symbol: SymbolId) -> bool {
    let value_declaration = c.sym(module_symbol).value_declaration;
    value_declaration.is_some_and(|vd| {
        let __program = c.program.clone().expect("program");
        let nodes = __program.nodes((vd).file_index());
        nodes[vd].kind == ast::Kind::ModuleDeclaration && nodes[vd].body().is_none()
    })
}

/// `isSyntacticDefault` (checker.go:15104).
fn is_syntactic_default(node: NodeId, nodes: &[ast::Node]) -> bool {
    (ast::is_export_assignment(&nodes[node])
        && !nodes[node].as_export_assignment().is_export_equals)
        || ast::has_syntactic_modifier(&nodes[node], ast::ModifierFlags::DEFAULT)
        || ast::is_export_specifier(&nodes[node])
        || ast::is_namespace_export(&nodes[node])
}

/// `hasExportAssignmentSymbol` (checker.go:15163).
fn has_export_assignment_symbol(c: &Checker, module_symbol: SymbolId) -> bool {
    c.sym(module_symbol)
        .exports
        .get(ast::symbol::INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
        .is_some()
}

/// `isESMFormatImportImportingCommonjsFormatFile` (checker.go:16006).
fn is_esm_format_import_importing_commonjs_format_file(
    usage_mode: tsc_core::compileroptions::ResolutionMode,
    target_mode: tsc_core::compileroptions::ResolutionMode,
) -> bool {
    usage_mode == ModuleKind::ESNext && target_mode == ModuleKind::CommonJS
}

/// `getAliasDeclarationFromName` (checker.go:16208).
fn get_alias_declaration_from_name(node: NodeId, nodes: &[ast::Node]) -> Option<NodeId> {
    match nodes[node].parent.map(|p| nodes[p].kind) {
        Some(
            ast::Kind::ImportClause
            | ast::Kind::ImportSpecifier
            | ast::Kind::NamespaceImport
            | ast::Kind::ExportSpecifier
            | ast::Kind::ExportAssignment
            | ast::Kind::ImportEqualsDeclaration
            | ast::Kind::NamespaceExport,
        ) => nodes[node].parent,
        Some(ast::Kind::QualifiedName) => nodes[node]
            .parent
            .and_then(|p| get_alias_declaration_from_name(p, nodes)),
        _ => None,
    }
}

/// `getContainingQualifiedNameNode` (checker.go:16270).
fn get_containing_qualified_name_node(mut node: NodeId, nodes: &[ast::Node]) -> NodeId {
    while let Some(parent) = nodes[node].parent {
        if !ast::is_qualified_name(&nodes[parent]) {
            break;
        }
        node = parent;
    }
    node
}

/// `collections.FindInMap` — first value satisfying `pred` (insertion order).
fn find_in_map(map: &SymbolTable, mut pred: impl FnMut(SymbolId) -> bool) -> Option<SymbolId> {
    map.values().copied().find(|s| pred(*s))
}

/// `createDiagnosticForNode` (checker.go:14529). PORT: gains the `nodes`
/// arena parameter (needed to compute the error range without a checker).
pub(crate) fn create_diagnostic_for_node(
    node: Option<NodeId>,
    nodes: &[ast::Node],
    message: &'static tsc_diagnostics::Message,
    args: &[String],
) -> DiagnosticRef {
    crate::utilities::new_diagnostic_for_node(node, nodes, message, args)
}

/// `getAdjustedNodeForError` (checker.go:14533).
pub(crate) fn get_adjusted_node_for_error(node: NodeId, nodes: &[ast::Node]) -> Option<NodeId> {
    if let Some(name) = ast::get_name_of_declaration(Some(node), nodes) {
        return Some(name);
    }
    Some(node)
}

/// `getFirstDeclaration` (checker.go:14545).
pub(crate) fn get_first_declaration(c: &Checker, symbol: SymbolId) -> Option<NodeId> {
    let declarations = &c.sym(symbol).declarations;
    if !declarations.is_empty() {
        return Some(declarations[0]);
    }
    None
}

/// `getExcludedSymbolFlags` (checker.go:14552).
pub(crate) fn get_excluded_symbol_flags(flags: ast::SymbolFlags) -> ast::SymbolFlags {
    use ast::SymbolFlags as S;
    let mut result = S::NONE;
    if flags.intersects(S::BLOCK_SCOPED_VARIABLE) {
        result |= S::BLOCK_SCOPED_VARIABLE_EXCLUDES;
    }
    if flags.intersects(S::FUNCTION_SCOPED_VARIABLE) {
        result |= S::FUNCTION_SCOPED_VARIABLE_EXCLUDES;
    }
    if flags.intersects(S::PROPERTY) {
        result |= S::PROPERTY_EXCLUDES;
    }
    if flags.intersects(S::ENUM_MEMBER) {
        result |= S::ENUM_MEMBER_EXCLUDES;
    }
    if flags.intersects(S::FUNCTION) {
        result |= S::FUNCTION_EXCLUDES;
    }
    if flags.intersects(S::CLASS) {
        result |= S::CLASS_EXCLUDES;
    }
    if flags.intersects(S::INTERFACE) {
        result |= S::INTERFACE_EXCLUDES;
    }
    if flags.intersects(S::REGULAR_ENUM) {
        result |= S::REGULAR_ENUM_EXCLUDES;
    }
    if flags.intersects(S::CONST_ENUM) {
        result |= S::CONST_ENUM_EXCLUDES;
    }
    if flags.intersects(S::VALUE_MODULE) {
        result |= S::VALUE_MODULE_EXCLUDES;
    }
    if flags.intersects(S::METHOD) {
        result |= S::METHOD_EXCLUDES;
    }
    if flags.intersects(S::GET_ACCESSOR) {
        result |= S::GET_ACCESSOR_EXCLUDES;
    }
    if flags.intersects(S::SET_ACCESSOR) {
        result |= S::SET_ACCESSOR_EXCLUDES;
    }
    if flags.intersects(S::TYPE_PARAMETER) {
        result |= S::TYPE_PARAMETER_EXCLUDES;
    }
    if flags.intersects(S::TYPE_ALIAS) {
        result |= S::TYPE_ALIAS_EXCLUDES;
    }
    if flags.intersects(S::ALIAS) {
        result |= S::ALIAS_EXCLUDES;
    }
    if flags.intersects(S::REPLACEABLE_BY_METHOD) {
        result = S(result.0 & !S::METHOD.0);
    }
    result
}
