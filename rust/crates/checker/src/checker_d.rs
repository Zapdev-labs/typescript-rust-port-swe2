// Ported from `tsc/internal/checker/checker.go` lines 24558–32722 (EOF)
// @ ec47d33c23e464a17cdf2475632cba629bee8763 — `checker_d.rs`.
//
// Range contents (Go declaration order):
//   - `evaluateEntity` / `evaluateEnumMember` — enum/entity compile-time
//     evaluation entry points (`evaluateEntity` itself is already declared
//     in `checker_core.rs` as a `PORT(deferred)` stub; this file ports the
//     *body* it defers to — `evaluate_enum_member` — plus everything after).
//   - Type-node readers (`getTypeFrom*TypeNode`) and the conditional-type
//     engine (`getConditionalType`, `getTailRecursionRoot`, …).
//   - Tuple type creation (`getTupleTargetType`, `createTupleType*`, the
//     `TupleTargetInfo` analysis) and generic-type predicates.
//   - Literal/union/intersection construction and reduction
//     (`getUnionTypeEx`, `getIntersectionTypeEx`, `removeSubtypes`, …).
//   - Indexed-access machinery (`getIndexedAccessType*`,
//     `getPropertyTypeForIndexType`, `getApplicableIndexInfos`).
//   - Contextual typing (`getContextualType*` family), `TypeFacts`,
//     awaited-type machinery, `getTypeOfNode`, `getSymbolAtLocation`, and
//     the per-file `checkSourceFile*` orchestration tail through EOF.
//
// Conventions (shared with checker_core.rs / checker_a/b):
//   `*Type` → `TypeId`, `*Signature` → `SignatureId`, `*ast.Node` → `NodeId`,
//   `*ast.Symbol` → `SymbolId`, `*TypeMapper` → `TypeMapperId`,
//   `*InferenceContext` → `InferenceContextId`, `*IndexInfo` → `IndexInfoId`.
//   Go `nil` → `Option<…>` (or `TypeId::NONE`-style sentinels for the
//   always-populated `Checker` fields).
//
// Cross-file references resolve by snake_case name to sibling ports
// (`checker_a/b/c.rs`, `relater.rs`, `flow.rs`, `inference.rs`,
// `utilities.rs`, `grammarchecks.rs`, `jsx.rs`, `services.rs`,
// `nodebuilder*.rs`, `emitresolver.rs`). Unresolved names are EXPECTED until
// those files land.
//
// Functions from this Go range already declared in `checker_core.rs` —
// `evaluate_entity`, `new_type`, `new_intrinsic_type{,_ex}`,
// `create_widening_type`, `create_unknown_union_type`, `new_literal_type`,
// `new_unique_es_symbol_type`, `new_object_type`, `new_anonymous_type`,
// `set_structured_type_members`, `new_type_parameter`,
// `get_propagating_flags_of_types`, `new_union_type`,
// `new_intersection_type`, `new_indexed_access_type`, `new_index_type`,
// `new_template_literal_type`, `new_string_mapping_type`,
// `new_substitution_type`, `new_signature`, `new_index_info`,
// `get_regular_type_of_literal_type`, `get_fresh_type_of_literal_type`,
// `get_string_literal_type`, `get_number_literal_type`,
// `get_big_int_literal_type`, `parse_big_int_literal_type`,
// `try_create_type_reference`, `create_type_reference{,_ex}`,
// `clone_type_reference`, `create_type_from_generic_global_type`,
// `get_global_strict_function_type`,
// `get_global_import_meta_expression_type`, `create_array_type{,_ex}`,
// `get_union_type`, `get_template_literal_type`, `map_type`,
// `get_awaited_type_ex`, `is_empty_anonymous_object_type`,
// `is_string_index_signature_only_type_worker`,
// `get_restrictive_type_parameter`, `restrictive_mapper_worker`,
// `permissive_mapper_worker`, `get_unique_literal_type_for_type_parameter`,
// `get_modifiers_type_from_mapped_type`, `contains_arguments_reference`,
// `is_array_type` — are NOT redeclared here (E0592). Several remain
// `unimplemented!` stubs in `checker_core.rs`; bodies land there when the
// wave-1 skeleton is filled in (this file calls them normally).
//
// `*ConditionalRoot` is `Box<ConditionalRoot>` inside `ConditionalType`
// (types.rs). Go shares the `instantiations` map across conditionals that
// share a root (tail recursion); the port clones roots value-wise — see
// `clone_conditional_root` and `get_tail_recursion_root`.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::{FxHashMap, FxHashSet};
use tsc_ast::checkflags::CheckFlags;
use tsc_ast::{self as ast, NodeId, SymbolId, SymbolTable};
use tsc_collections::OrderedSet;
use tsc_core::context::Context;
use tsc_core::core;
use tsc_core::options_generated::{ModuleKind, ScriptTarget};
use tsc_core::tristate::Tristate;
use tsc_evaluator as evaluator;
use tsc_jsnum::{self as jsnum, Number, PseudoBigInt};
use tsc_scanner::scanner;

use crate::checker_core::{
    as_recursion_id_type, get_recursion_identity, CacheHashKey, CheckMode, Checker,
    InferenceContext, InferenceContextId, InferenceContextInfo, InferenceFlags, InferenceInfo,
    InferencePriority, RecursionId,
};
use crate::checker_types::{
    get_indexed_access_key, CachedTypeKind, CachedTypeKey, ContextualInfo, IntersectionFlags,
    IterationTypeKind, MappedTypeModifiers, MappedTypeNameTypeKind, ReferenceHint,
    IntrinsicTypeKind, SubstitutionTypeKey, ThisAssignmentDeclarationKind, TypeFacts,
    TypeSystemPropertyName, UnionReduction,
};
use crate::mapper::{self, TypeMapperId};
use crate::types::{
    AccessFlags, TypeArena, ConditionalRoot, ConditionalType, ContextFlags, ElementFlags, ExternalEmitHelpers,
    IndexFlags, IndexInfo, IndexInfoId, IndexKind, IntersectionType, LiteralType, ObjectFlags,
    Signature, SignatureFlags, SignatureId, SignatureKind, SubstitutionType, Ternary,
    TupleElementInfo, TupleType, Type, TypeAlias, TypeData, TypeFlags, TypeId, TypePredicate,
    UnionType,
};

// ---------------------------------------------------------------------------
// PORT helpers — file-local TypeData mutable accessors (types.rs exposes
// `as_*_mut` only for the embedded-base accessors).
// ---------------------------------------------------------------------------

/// `t.AsConditionalType()` mutable — Go mutates resolution caches through
/// the `*ConditionalType` pointer.
#[track_caller]
fn as_conditional_type_mut(t: &mut Type) -> &mut ConditionalType {
    match &mut t.data {
        TypeData::Conditional(d) => d,
        _ => panic!("AsConditionalType: not a conditional type"),
    }
}

/// `t.AsUnionType()` mutable.
#[track_caller]
fn as_union_type_mut(t: &mut Type) -> &mut UnionType {
    match &mut t.data {
        TypeData::Union(d) => d,
        _ => panic!("AsUnionType: not a union type"),
    }
}

/// `t.AsIntersectionType()` mutable.
#[track_caller]
fn as_intersection_type_mut(t: &mut Type) -> &mut IntersectionType {
    match &mut t.data {
        TypeData::Intersection(d) => d,
        _ => panic!("AsIntersectionType: not an intersection type"),
    }
}

/// `t.AsSubstitutionType()` mutable.
#[track_caller]
fn as_substitution_type_mut(t: &mut Type) -> &mut SubstitutionType {
    match &mut t.data {
        TypeData::Substitution(d) => d,
        _ => panic!("AsSubstitutionType: not a substitution type"),
    }
}

/// `t.AsLiteralType()` mutable.
#[track_caller]
fn as_literal_type_mut(t: &mut Type) -> &mut LiteralType {
    match &mut t.data {
        TypeData::Literal(d) => d,
        _ => panic!("AsLiteralType: not a literal type"),
    }
}

/// `t.AsObjectType()` mutable.
#[track_caller]
fn as_object_type_data_mut(t: &mut Type) -> &mut crate::types::ObjectType {
    match &mut t.data {
        TypeData::Object(d) => d,
        _ => panic!("AsObjectType: not an anonymous object type"),
    }
}

// `maxTemplateLiteralTypeLength` / `maxTemplateLiteralTypeSpans`
// (checker.go:29677).
const MAX_TEMPLATE_LITERAL_TYPE_LENGTH: usize = 50_000_000;
const MAX_TEMPLATE_LITERAL_TYPE_SPANS: usize = 100_000;

/// `node.AsUnionTypeNode().Types.Nodes` / `AsIntersectionTypeNode().Types.Nodes`.
fn union_or_intersection_types(n: &ast::Node) -> &[NodeId] {
    let list = match n.kind {
        ast::Kind::UnionType => {
            &n.as_union_type_node()
                .union_or_intersection_type_node_base
                .types
        }
        ast::Kind::IntersectionType => {
            &n.as_intersection_type_node()
                .union_or_intersection_type_node_base
                .types
        }
        _ => panic!("union_or_intersection_types on kind {:?}", n.kind),
    };
    list.as_ref().map_or(&[], |l| l.nodes())
}

/// `type TupleTargetInfo struct` (checker.go:25296) — scratch accumulator
/// built by `getTupleTargetType`.
#[derive(Default)]
pub(crate) struct TupleTargetInfo {
    /// `readonly`.
    pub(crate) readonly: bool,
    /// `elementFlags` — ElementFlags for each element.
    pub(crate) element_flags: Vec<ElementFlags>,
    /// `minLength` — number of required or variadic elements.
    pub(crate) min_length: usize,
    /// `fixedLength` — number of initial required or optional elements.
    pub(crate) fixed_length: usize,
    /// `combinedFlags`.
    pub(crate) combined_flags: ElementFlags,
    /// `hasVariadicElement` — true if tuple has any variadic elements.
    pub(crate) has_variadic_element: bool,
    /// `labeledElementDeclarations` — labeled elements `(label: type)`.
    /// `*ast.NamedTupleMember | *ast.ParameterDeclaration` → `NodeId`.
    pub(crate) labeled_element_declarations: Vec<Option<NodeId>>,
}

/// `(c *Checker) cloneConditionalRoot`-equivalent: Go threads
/// `*ConditionalRoot` pointers through `getTailRecursionRoot` so that a
/// deferred conditional created mid-resolution shares the pre-existing
/// root's `instantiations` cache. `Box<ConditionalRoot>` ownership in the
/// arena prevents that sharing; the port copies the root value-wise
/// (`instantiations` is cloned — a snapshot rather than a live view).
/// PORT(divergence): see `get_tail_recursion_root`.
pub(crate) fn clone_conditional_root(root: &ConditionalRoot) -> ConditionalRoot {
    ConditionalRoot {
        node: root.node,
        check_type: root.check_type,
        extends_type: root.extends_type,
        is_distributive: root.is_distributive,
        infer_type_parameters: root.infer_type_parameters.clone(),
        outer_type_parameters: root.outer_type_parameters.clone(),
        instantiations: root.instantiations.clone(),
        alias: root.alias.clone(),
    }
}

impl Checker {
    /// `c.evaluate(expr, location)` — invoke the `evaluator.Evaluator`
    /// thunk stored in `self.evaluate`. The `Box` is taken out for the
    /// duration of the call so the thunk can take `&mut self`.
    pub(crate) fn evaluate_call(
        &mut self,
        expr: NodeId,
        location: Option<NodeId>,
        nodes: &[ast::Node],
    ) -> evaluator::Result {
        let thunk = self.evaluate.take().expect("evaluate: uninitialized");
        let result = thunk(self, expr, location, nodes);
        self.evaluate = Some(thunk);
        result
    }

    /// `symbol.Flags` — read via the checker's symbol arena.
    #[inline]
    pub(crate) fn sym_flags(&self, s: SymbolId) -> ast::SymbolFlags {
        self.symbol_arena.borrow()[s.index()].flags
    }

    /// `symbol.Name` — clone of the symbol's name string.
    #[inline]
    pub(crate) fn sym_name(&self, s: SymbolId) -> String {
        self.symbol_arena.borrow()[s.index()].name.clone()
    }

    /// `*InferenceContext` dereference (`self.inference_contexts[id]`).
    #[inline]
    pub(crate) fn inference_context(&self, id: InferenceContextId) -> &InferenceContext {
        &self.inference_contexts[id.index()]
    }

    /// Mutable `*InferenceContext` dereference.
    #[inline]
    pub(crate) fn inference_context_mut(&mut self, id: InferenceContextId) -> &mut InferenceContext {
        &mut self.inference_contexts[id.index()]
    }

    // ==== checker.go:24558 `evaluateEntity` ================================
    // `evaluate_entity` is declared `pub fn` in `checker_core.rs` as a
    // PORT(deferred) stub (it needs `resolve_entity_name` from
    // checker_a/b/c). The full body for that Go function is ported here in
    // comment-equivalent form via `evaluate_enum_member` below; when core's
    // stub is filled in it will call into these methods.

    /// `(c *Checker) evaluateEnumMember` (checker.go:24611). `location` is
    /// non-None at all Go call sites (guarded by `location != nil`).
    pub(crate) fn evaluate_enum_member(
        &mut self,
        expr: NodeId,
        symbol: SymbolId,
        location: NodeId,
    ) -> evaluator::Result {
        let declaration = self.symbol_arena.borrow()[symbol.index()].value_declaration;
        if declaration.is_none() || declaration == Some(location) {
            let name = self.symbol_to_string(symbol);
            self.error(
                Some(expr),
                &tsc_diagnostics::Property_0_is_used_before_being_assigned,
                &[name],
            );
            return evaluator::new_result(None, false, false, false);
        }
        let declaration = declaration.unwrap();
        if !self.is_block_scoped_name_declared_before_use(declaration, location) {
            self.error(
                Some(expr),
                &tsc_diagnostics::A_member_initializer_in_a_enum_declaration_cannot_reference_members_declared_after_it_including_members_defined_in_other_enums,
                &[],
            );
            return evaluator::new_result(
                Some(evaluator::Value::Number(Number(0.0))),
                false,
                false,
                false,
            );
        }
        let value = self.get_enum_member_value(declaration);
        let loc_nodes = self.program_nodes(location);
        let decl_nodes = self.program_nodes(declaration);
        if loc_nodes[location].parent != decl_nodes[declaration].parent {
            return evaluator::new_result(
                value.value,
                value.is_syntactically_string,
                value.resolved_other_files,
                true,
            );
        }
        value
    }

    /// `(c *Checker) getDeclaredTypeOfAlias` (checker.go:24628).
    pub(crate) fn get_declared_type_of_alias(&mut self, symbol: SymbolId) -> TypeId {
        if self.declared_type_links.get(symbol).declared_type.is_none() {
            let resolved = self.resolve_alias(symbol).unwrap_or(SymbolId::NONE);
            let declared = self.get_declared_type_of_symbol(resolved);
            self.declared_type_links.get(symbol).declared_type = Some(declared);
        }
        self.declared_type_links.get(symbol).declared_type.unwrap()
    }

    /// `(c *Checker) getTypeFromTypeQueryNode` (checker.go:24636).
    pub(crate) fn get_type_from_type_query_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            // TypeScript 1.0 spec (April 2014): 3.6.3
            // The expression is processed as an identifier expression (section 4.3)
            // or property access expression(section 4.10),
            // the widened type(section 3.9) of which becomes the result.
            let t = self.check_expression_with_type_arguments(node);
            let t = self.get_regular_type_of_literal_type(self.get_widened_type(t));
            self.type_node_links.get(node).resolved_type = Some(t);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getTypeFromArrayOrTupleTypeNode` (checker.go:24649).
    pub(crate) fn get_type_from_array_or_tuple_type_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let nodes = self.program_nodes(node);
            let target = self.get_array_or_tuple_target_type(node);
            let resolved;
            if target == self.empty_generic_type {
                resolved = self.empty_object_type;
            } else if !(nodes[node].kind == ast::Kind::TupleType
                && core::some(nodes[node].elements().unwrap_or(&[]), |&e| {
                    self.is_variadic_tuple_element(e)
                }))
                && self.is_deferred_type_reference_node(node, false)
            {
                if nodes[node].kind == ast::Kind::TupleType
                    && nodes[node].elements().unwrap_or(&[]).is_empty()
                {
                    resolved = target;
                } else {
                    resolved = self.create_deferred_type_reference(target, node, None, None);
                }
            } else {
                let element_types: Vec<TypeId> = if nodes[node].kind == ast::Kind::ArrayType {
                    vec![self.get_type_from_type_node(
                        nodes[node].as_array_type_node().element_type.unwrap(),
                    )]
                } else {
                    core::map(nodes[node].elements().unwrap_or(&[]), |&e| {
                        self.get_type_from_type_node(e)
                    })
                };
                if self.types.get(target).object_flags.intersects(ObjectFlags::TUPLE) {
                    resolved = self.create_normalized_tuple_type_ex(
                        target,
                        &element_types,
                        ObjectFlags::FROM_TYPE_NODE,
                    );
                } else {
                    resolved = self.create_type_reference_ex(
                        target,
                        &element_types,
                        ObjectFlags::FROM_TYPE_NODE,
                    );
                }
            }
            self.type_node_links.get(node).resolved_type = Some(resolved);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) isVariadicTupleElement` (checker.go:24678).
    pub(crate) fn is_variadic_tuple_element(&mut self, node: NodeId) -> bool {
        self.get_tuple_element_flags(node)
            .intersects(ElementFlags::VARIADIC)
    }

    /// `(c *Checker) getArrayOrTupleTargetType` (checker.go:24682).
    pub(crate) fn get_array_or_tuple_target_type(&mut self, node: NodeId) -> TypeId {
        let nodes = self.program_nodes(node);
        let readonly = nodes[node]
            .parent
            .is_some_and(|p| self.is_readonly_type_operator(p));
        if let Some(element_type) = self.get_array_element_type_node(Some(node)) {
            if readonly {
                return self.global_readonly_array_type;
            }
            return self.global_array_type;
        }
        let element_infos = core::map(nodes[node].elements().unwrap_or(&[]), |&e| {
            self.get_tuple_element_info(e)
        });
        self.get_tuple_target_type(&element_infos, readonly)
    }

    /// `(c *Checker) isReadonlyTypeOperator` (checker.go:24694).
    pub(crate) fn is_readonly_type_operator(&self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        ast::is_type_operator_node(&nodes[node])
            && nodes[node].as_type_operator_node().operator == ast::Kind::ReadonlyKeyword
    }

    /// `(c *Checker) getTypeFromNamedTupleTypeNode` (checker.go:24698).
    pub(crate) fn get_type_from_named_tuple_type_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let nodes = self.program_nodes(node);
            let resolved;
            if nodes[node].as_named_tuple_member().dot_dot_dot_token.is_some() {
                resolved = self.get_type_from_rest_type_node(node);
            } else {
                let t = self.get_type_from_type_node(nodes[node].type_().unwrap());
                resolved =
                    self.add_optionality_ex(t, true, nodes[node].question_token(&nodes).is_some());
            }
            self.type_node_links.get(node).resolved_type = Some(resolved);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getTypeFromRestTypeNode` (checker.go:24710).
    pub(crate) fn get_type_from_rest_type_node(&mut self, node: NodeId) -> TypeId {
        let nodes = self.program_nodes(node);
        let mut type_node = nodes[node].type_().expect("getTypeFromRestTypeNode: nil type");
        if let Some(element_type_node) = self.get_array_element_type_node(Some(type_node)) {
            type_node = element_type_node;
        }
        self.get_type_from_type_node(type_node)
    }

    /// `(c *Checker) getArrayElementTypeNode` (checker.go:24719).
    /// `nil` → `None`.
    pub(crate) fn get_array_element_type_node(&self, node: Option<NodeId>) -> Option<NodeId> {
        let mut node = node?;
        let nodes = self.program_nodes(node);
        match nodes[node].kind {
            ast::Kind::ParenthesizedType => {
                return self.get_array_element_type_node(nodes[node].type_());
            }
            ast::Kind::TupleType => {
                if nodes[node].elements().unwrap_or(&[]).len() == 1 {
                    node = nodes[node].elements().unwrap()[0];
                    if nodes[node].kind == ast::Kind::RestType {
                        return self.get_array_element_type_node(nodes[node].type_());
                    }
                    if nodes[node].kind == ast::Kind::NamedTupleMember
                        && nodes[node].as_named_tuple_member().dot_dot_dot_token.is_some()
                    {
                        return self.get_array_element_type_node(nodes[node].type_());
                    }
                }
            }
            ast::Kind::ArrayType => return nodes[node].as_array_type_node().element_type,
            _ => {}
        }
        None
    }

    /// `(c *Checker) getTypeFromOptionalTypeNode` (checker.go:24739).
    pub(crate) fn get_type_from_optional_type_node(&mut self, node: NodeId) -> TypeId {
        let nodes = self.program_nodes(node);
        let t = self.get_type_from_type_node(nodes[node].type_().unwrap());
        self.add_optionality_ex(t, true /*isProperty*/, true /*isOptional*/)
    }

    /// `(c *Checker) getTypeFromUnionTypeNode` (checker.go:24743).
    pub(crate) fn get_type_from_union_type_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let alias = self.get_alias_for_type_node(node);
            let nodes = self.program_nodes(node);
            let types = core::map(union_or_intersection_types(&nodes[node]), |&t| {
                self.get_type_from_type_node(t)
            });
            let resolved = self.get_union_type_ex(&types, UnionReduction::Literal, alias, None);
            self.type_node_links.get(node).resolved_type = Some(resolved);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getTypeFromIntersectionTypeNode` (checker.go:24752).
    pub(crate) fn get_type_from_intersection_type_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let alias = self.get_alias_for_type_node(node);
            let nodes = self.program_nodes(node);
            let types = core::map(union_or_intersection_types(&nodes[node]), |&t| {
                self.get_type_from_type_node(t)
            });
            // We perform no supertype reduction for X & {} or {} & X, where X is one of string, number, bigint,
            // or a pattern literal template type. This enables union types like "a" | "b" | string & {} or
            // "aa" | "ab" | `a${string}` which preserve the literal types for purposes of statement completion.
            let mut no_supertype_reduction = false;
            if types.len() == 2 {
                let empty_index = types.iter().position(|&t| t == self.empty_type_literal_type);
                if let Some(empty_index) = empty_index {
                    let t = types[1 - empty_index];
                    let flags = self.types.get(t).flags;
                    no_supertype_reduction = flags.intersects(
                        TypeFlags::STRING | TypeFlags::NUMBER | TypeFlags::BIG_INT,
                    ) || flags.intersects(TypeFlags::TEMPLATE_LITERAL)
                        && self.is_pattern_literal_type(t);
                }
            }
            let resolved = self.get_intersection_type_ex(
                &types,
                if no_supertype_reduction {
                    IntersectionFlags::NO_SUPERTYPE_REDUCTION
                } else {
                    IntersectionFlags::NONE
                },
                alias,
            );
            self.type_node_links.get(node).resolved_type = Some(resolved);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getTypeFromTemplateTypeNode` (checker.go:24773).
    pub(crate) fn get_type_from_template_type_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let nodes = self.program_nodes(node);
            let spans = nodes[node].as_template_literal_type_node().template_spans.clone();
            let mut texts = Vec::with_capacity(spans.as_ref().map_or(1, |s| s.nodes().len() + 1));
            let mut types = Vec::with_capacity(spans.as_ref().map_or(0, |s| s.nodes().len()));
            texts.push(
                nodes[nodes[node].as_template_literal_type_node().head.unwrap()]
                    .text(&nodes)
                    .into_owned(),
            );
            for &span in spans.iter().flat_map(|s| s.nodes().iter()) {
                texts.push(
                    nodes[nodes[span].as_template_literal_type_span().literal.unwrap()]
                        .text(&nodes)
                        .into_owned(),
                );
                types.push(
                    self.get_type_from_type_node(nodes[span].type_().expect("template span type")),
                );
            }
            let resolved = self.get_template_literal_type(&texts, &types);
            self.type_node_links.get(node).resolved_type = Some(resolved);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getTypeFromMappedTypeNode` (checker.go:24789).
    pub(crate) fn get_type_from_mapped_type_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let symbol = self.program_nodes(node)[node].symbol();
            let t = self.new_object_type(ObjectFlags::MAPPED, symbol);
            self.types.get_mut(t).as_mapped_type_mut().declaration = Some(node);
            let alias = self.get_alias_for_type_node(node);
            self.types.get_mut(t).alias = alias;
            self.type_node_links.get(node).resolved_type = Some(t);
            // Eagerly resolve the constraint type which forces an error if the constraint type circularly
            // references itself through one or more type aliases.
            self.get_constraint_type_from_mapped_type(t);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getTypeFromConditionalTypeNode` (checker.go:24803).
    pub(crate) fn get_type_from_conditional_type_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let nodes = self.program_nodes(node);
            let check_type = self.get_type_from_type_node(
                nodes[node].as_conditional_type_node().check_type.unwrap(),
            );
            let alias = self.get_alias_for_type_node(node);
            let all_outer_type_parameters = self.get_outer_type_parameters(node, true);
            // `var outerTypeParameters []*Type` — nil iff `allOuterTypeParameters`
            // is nil/empty (both branches then produce nil/empty and Go's
            // `!= nil` post-pass is skipped); otherwise the alias/filtered
            // result (Go `core.Filter` always returns non-nil for non-nil
            // input).
            let outer_type_parameters: Option<Vec<TypeId>> = if all_outer_type_parameters.is_empty()
            {
                None
            } else if alias.as_ref().is_some_and(|a| !a.type_arguments.is_empty()) {
                Some(all_outer_type_parameters)
            } else {
                Some(
                    core::filter(&all_outer_type_parameters, |&tp| {
                        self.is_type_parameter_possibly_referenced(tp, node)
                    })
                    .into_owned(),
                )
            };
            let mut root = ConditionalRoot {
                node: Some(node),
                check_type: Some(check_type),
                extends_type: Some(self.get_type_from_type_node(
                    nodes[node].as_conditional_type_node().extends_type.unwrap(),
                )),
                is_distributive: self
                    .types
                    .get(check_type)
                    .flags
                    .intersects(TypeFlags::TYPE_PARAMETER),
                infer_type_parameters: self.get_infer_type_parameters(node),
                outer_type_parameters: outer_type_parameters.clone().unwrap_or_default(),
                instantiations: FxHashMap::default(),
                alias,
            };
            let resolved = self.get_conditional_type(&mut root, None, false, None);
            if let Some(outer_type_parameters) = &outer_type_parameters {
                let key =
                    crate::checker_c::get_conditional_type_key(outer_type_parameters, None, false);
                root.instantiations.insert(key, resolved);
                // Write-through: Go shares `root` with `resolved`'s
                // `AsConditionalType().root`; the port stores an owning
                // `Box`, so mirror the insert on the stored copy.
                if self.types.get(resolved).flags.intersects(TypeFlags::CONDITIONAL) {
                    let mut g = self.types.get_mut(resolved);
                    if let Some(stored) = as_conditional_type_mut(&mut g).root.as_mut() {
                        stored.instantiations.insert(key, resolved);
                    }
                }
            }
            self.type_node_links.get(node).resolved_type = Some(resolved);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getConditionalType` (checker.go:24834).
    ///
    /// PORT: `root` is taken by `&mut ConditionalRoot` — Go's shared
    /// `*ConditionalRoot` cell is approximated by cloning (the stored
    /// `Box<ConditionalRoot>` on `ConditionalType` is a snapshot; see the
    /// file-header PORT(divergence) note). Tail-recursion rebinds `root` to
    /// a `clone_conditional_root` of the deferred conditional's stored root.
    pub(crate) fn get_conditional_type(
        &mut self,
        root: &mut ConditionalRoot,
        mut mapper: Option<TypeMapperId>,
        for_constraint: bool,
        mut alias: Option<TypeAlias>,
    ) -> TypeId {
        let mut result: TypeId;
        let mut extra_types: Vec<TypeId> = Vec::new();
        let mut tail_count = 0;
        let mut root_cell = clone_conditional_root(root);
        // We loop here for an immediately nested conditional type in the false position, effectively treating
        // types of the form 'A extends B ? X : C extends D ? Y : E extends F ? Z : ...' as a single construct for
        // purposes of resolution. We also loop here when resolution of a conditional type ends in resolution of
        // another (or, through recursion, possibly the same) conditional type. In the potentially tail-recursive
        // cases we increment the tail recursion counter and stop after 1000 iterations.
        loop {
            let root = &mut root_cell;
            if tail_count == 1000 {
                self.error(
                    self.current_node,
                    &tsc_diagnostics::Type_instantiation_is_excessively_deep_and_possibly_infinite,
                    &[],
                );
                return self.error_type;
            }
            let check_type = self.instantiate_type(
                self.get_actual_type_variable(root.check_type.unwrap_or(TypeId::NONE)),
                mapper,
            );
            let extends_type =
                self.instantiate_type(root.extends_type.unwrap_or(TypeId::NONE), mapper);
            if check_type == self.error_type || extends_type == self.error_type {
                return self.error_type;
            }
            if check_type == self.wildcard_type || extends_type == self.wildcard_type {
                return self.wildcard_type;
            }
            let root_node = root.node.expect("getConditionalType: nil root.node");
            let nodes = self.program_nodes(root_node);
            let (cond_check, cond_extends, cond_true, cond_false) = {
                let cnd = nodes[root_node].as_conditional_type_node();
                (cnd.check_type, cnd.extends_type, cnd.true_type, cnd.false_type)
            };
            let check_type_node = ast::skip_type_parentheses(cond_check.unwrap(), &nodes);
            let extends_type_node = ast::skip_type_parentheses(cond_extends.unwrap(), &nodes);
            // When the check and extends types are simple tuple types of the same arity, we defer resolution of the
            // conditional type when any tuple elements are generic. This is such that non-distributable conditional
            // types can be written `[X] extends [Y] ? ...` and be deferred similarly to `X extends Y ? ...`.
            let check_tuples = self.is_simple_tuple_type(check_type_node)
                && self.is_simple_tuple_type(extends_type_node)
                && nodes[check_type_node].elements().unwrap_or(&[]).len()
                    == nodes[extends_type_node].elements().unwrap_or(&[]).len();
            let check_type_deferred = self.is_deferred_type(check_type, check_tuples);
            let mut combined_mapper: Option<TypeMapperId> = None;
            if !root.infer_type_parameters.is_empty() {
                // When we're looking at making an inference for an infer type, when we get its constraint, it'll automagically be
                // instantiated with the context, so it doesn't need the mapper for the inference context - however the constraint
                // may refer to another _root_, _uncloned_ `infer` type parameter [1], or to something mapped by `mapper` [2].
                // [1] Eg, if we have `Foo<T, U extends T>` and `Foo<number, infer B>` - `B` is constrained to `T`, which, in turn, has been instantiated
                // as `number`
                // Conversely, if we have `Foo<infer A, infer B>`, `B` is still constrained to `T` and `T` is instantiated as `A`
                // [2] Eg, if we have `Foo<T, U extends T>` and `Foo<Q, infer B>` where `Q` is mapped by `mapper` into `number` - `B` is constrained to `T`
                // which is in turn instantiated as `Q`, which is in turn instantiated as `number`.
                // So we need to:
                //    * combine `context.nonFixingMapper` with `mapper` so their constraints can be instantiated in the context of `mapper` (otherwise they'd only get inference context information)
                //    * incorporate all of the component mappers into the combined mapper for the true and false members
                // This means we have two mappers that need applying:
                //    * The original `mapper` used to create this conditional
                //    * The mapper that maps the infer type parameter to its inference result (`context.mapper`)
                let context = self.new_inference_context(
                    root.infer_type_parameters.clone(),
                    None,
                    InferenceFlags(0),
                    None,
                );
                if let Some(m) = mapper {
                    let nfm = self.inference_context(context).non_fixing_mapper;
                    self.inference_context_mut(context).non_fixing_mapper =
                        Some(self.combine_type_mappers(nfm, m));
                }
                if !check_type_deferred {
                    // We don't want inferences from constraints as they may cause us to eagerly resolve the
                    // conditional type instead of deferring resolution. Also, we always want strict function
                    // types rules (i.e. proper contravariance) for inferences.
                    let inferences = std::mem::take(&mut self.inference_context_mut(context).inferences);
                    self.infer_types(
                        inferences,
                        check_type,
                        extends_type,
                        InferencePriority::NO_CONSTRAINTS | InferencePriority::ALWAYS_STRICT,
                        false,
                    );
                    self.inference_context_mut(context).inferences = inferences;
                }
                // It's possible for 'infer T' type parameters to be given uninstantiated constraints when the
                // those type parameters are used in type references (see getInferredTypeParameterConstraint). For
                // that reason we need context.mapper to be first in the combined mapper. See #42636 for examples.
                if let Some(m) = mapper {
                    let cm = self.inference_context(context).mapper;
                    combined_mapper = Some(self.combine_type_mappers(cm, m));
                } else {
                    combined_mapper = self.inference_context(context).mapper;
                }
            }
            // Instantiate the extends type including inferences for 'infer T' type parameters
            let inferred_extends_type = if let Some(cm) = combined_mapper {
                self.instantiate_type(root.extends_type.unwrap_or(TypeId::NONE), Some(cm))
            } else {
                extends_type
            };
            // We attempt to resolve the conditional type only when the check and extends types are non-generic
            if !check_type_deferred && !self.is_deferred_type(inferred_extends_type, check_tuples) {
                // Return falseType for a definitely false extends check. We check an instantiations of the two
                // types with type parameters mapped to the wildcard type, the most permissive instantiations
                // possible (the wildcard type is assignable to and from all types). If those are not related,
                // then no instantiations will be and we can just return the false branch type.
                if !self
                    .types
                    .get(inferred_extends_type)
                    .flags
                    .intersects(TypeFlags::ANY_OR_UNKNOWN)
                    && (self.types.get(check_type).flags.intersects(TypeFlags::ANY)
                        || !self.is_type_assignable_to(
                            self.get_permissive_instantiation(check_type),
                            self.get_permissive_instantiation(inferred_extends_type),
                        ))
                {
                    // Return union of trueType and falseType for 'any' since it matches anything. Furthermore, for a
                    // distributive conditional type applied to the constraint of a type variable, include trueType if
                    // there are possible values of the check type that are also possible values of the extends type.
                    // We use a reverse assignability check as it is less expensive than the comparable relationship
                    // and avoids false positives of a non-empty intersection check.
                    if self.types.get(check_type).flags.intersects(TypeFlags::ANY)
                        || for_constraint
                            && !self
                                .types
                                .get(inferred_extends_type)
                                .flags
                                .intersects(TypeFlags::NEVER)
                            && {
                                let permissive =
                                    self.get_permissive_instantiation(inferred_extends_type);
                                some_type(&mut *self, permissive, |c, t| {
                                    let check = c.get_permissive_instantiation(check_type);
                                    c.is_type_assignable_to(t, check)
                                })
                            }
                    {
                        let true_type_node = cond_true.unwrap();
                        extra_types.push(self.instantiate_type(
                            self.get_type_from_type_node(true_type_node),
                            combined_mapper.or(mapper),
                        ));
                    }
                    // If falseType is an immediately nested conditional type that isn't distributive or has an
                    // identical checkType, switch to that type and loop.
                    let false_type = self.get_type_from_type_node(cond_false.unwrap());
                    if self
                        .types
                        .get(false_type)
                        .flags
                        .intersects(TypeFlags::CONDITIONAL)
                    {
                        let new_root_box = self
                            .types
                            .get(false_type)
                            .as_conditional_type()
                            .root
                            .as_ref()
                            .expect("conditional root")
                            .clone();
                        let new_root_node = new_root_box.node;
                        let parent_of_new_root = new_root_node.and_then(|n| {
                            self.program_nodes(n)[n].parent
                        });
                        if parent_of_new_root == Some(root_node)
                            && (!new_root_box.is_distributive
                                || new_root_box.check_type == root.check_type)
                        {
                            *root = *new_root_box;
                            continue;
                        }
                        if let Some((new_root, new_root_mapper)) =
                            self.get_tail_recursion_root(false_type, mapper)
                        {
                            *root = new_root;
                            mapper = new_root_mapper;
                            alias = None;
                            if root.alias.is_some() {
                                tail_count += 1;
                            }
                            continue;
                        }
                    }
                    result = self.instantiate_type(false_type, mapper);
                    break;
                }
                // Return trueType for a definitely true extends check. We check instantiations of the two
                // types with type parameters mapped to their restrictive form, i.e. a form of the type parameter
                // that has no constraint. This ensures that, for example, the type
                //   type Foo<T extends { x: any }> = T extends { x: string } ? string : number
                // doesn't immediately resolve to 'string' instead of being deferred.
                if self
                    .types
                    .get(inferred_extends_type)
                    .flags
                    .intersects(TypeFlags::ANY_OR_UNKNOWN)
                    || self.is_type_assignable_to(
                        self.get_restrictive_instantiation(check_type),
                        self.get_restrictive_instantiation(inferred_extends_type),
                    )
                {
                    let true_type = self.get_type_from_type_node(cond_true.unwrap());
                    let true_mapper = combined_mapper.or(mapper);
                    if let Some((new_root, new_root_mapper)) =
                        self.get_tail_recursion_root(true_type, true_mapper)
                    {
                        *root = new_root;
                        mapper = new_root_mapper;
                        alias = None;
                        if root.alias.is_some() {
                            tail_count += 1;
                        }
                        continue;
                    }
                    result = self.instantiate_type(true_type, true_mapper);
                    break;
                }
            }
            // Return a deferred type for a check that is neither definitely true nor definitely false
            result = self.new_conditional_type(root, mapper, combined_mapper);
            if let Some(a) = alias {
                self.types.get_mut(result).alias = Some(a);
            } else {
                self.types.get_mut(result).alias =
                    self.instantiate_type_alias(root.alias.as_ref(), mapper);
            }
            break;
        }
        if !extra_types.is_empty() {
            extra_types.push(result);
            return self.get_union_type(&extra_types);
        }
        result
    }
}

impl Checker {
    /// `(c *Checker) getTailRecursionRoot` (checker.go:24985).
    ///
    /// Go returns `(*ConditionalRoot, *TypeMapper)` — `(None, _)` models
    /// `nil, nil`. The returned root is a snapshot clone of the deferred
    /// conditional's stored root (see file-header PORT(divergence)).
    pub(crate) fn get_tail_recursion_root(
        &mut self,
        new_type: TypeId,
        new_mapper: Option<TypeMapperId>,
    ) -> Option<(ConditionalRoot, Option<TypeMapperId>)> {
        if self
            .types
            .get(new_type)
            .flags
            .intersects(TypeFlags::CONDITIONAL)
            && new_mapper.is_some()
        {
            let new_root = clone_conditional_root(
                self.types
                    .get(new_type)
                    .as_conditional_type()
                    .root
                    .as_ref()
                    .expect("getTailRecursionRoot: nil root"),
            );
            if !new_root.outer_type_parameters.is_empty() {
                let cond_mapper = self.types.get(new_type).as_conditional_type().mapper;
                let type_param_mapper =
                    self.combine_type_mappers(cond_mapper, new_mapper.unwrap());
                let mappers = self.type_mappers.clone();
                let type_arguments: Vec<TypeId> = new_root
                    .outer_type_parameters
                    .iter()
                    .map(|&t| mappers.map(&mut *self, type_param_mapper, t))
                    .collect();
                let new_root_mapper = mapper::new_type_mapper(
                    self,
                    new_root.outer_type_parameters.clone(),
                    type_arguments,
                );
                let mut new_check_type: Option<TypeId> = None;
                if new_root.is_distributive {
                    new_check_type = Some(mapper::get_mapped_type(
                        self,
                        new_root.check_type.unwrap_or(TypeId::NONE),
                        new_root_mapper,
                    ));
                }
                let flags = new_check_type.map(|t| self.types.get(t).flags);
                if new_check_type.is_none()
                    || new_check_type == new_root.check_type
                    || !flags
                        .unwrap_or_default()
                        .intersects(TypeFlags::UNION | TypeFlags::NEVER)
                {
                    return Some((new_root, Some(new_root_mapper)));
                }
            }
        }
        None
    }

    /// `(c *Checker) isSimpleTupleType` (checker.go:25003).
    pub(crate) fn is_simple_tuple_type(&self, node: NodeId) -> bool {
        let nodes = self.program_nodes(node);
        ast::is_tuple_type_node(&nodes[node])
            && !nodes[node].elements().unwrap_or(&[]).is_empty()
            && !core::some(nodes[node].elements().unwrap_or(&[]), |&e| {
                ast::is_optional_type_node(&nodes[e])
                    || ast::is_rest_type_node(&nodes[e])
                    || ast::is_named_tuple_member(&nodes[e])
                        && (nodes[e].question_token(&nodes).is_some()
                            || nodes[e].as_named_tuple_member().dot_dot_dot_token.is_some())
            })
    }

    /// `(c *Checker) isDeferredType` (checker.go:25009).
    pub(crate) fn is_deferred_type(&mut self, t: TypeId, check_tuples: bool) -> bool {
        self.is_generic_type(t)
            || check_tuples
                && crate::checker_core::is_tuple_type(&self.types, t)
                && core::some(&self.get_element_types(t), |&e| self.is_generic_type(e))
    }

    /// `(c *Checker) getPermissiveInstantiation` (checker.go:25013).
    pub(crate) fn get_permissive_instantiation(&mut self, t: TypeId) -> TypeId {
        if self.types.get(t).flags.intersects(
            TypeFlags::PRIMITIVE | TypeFlags::ANY_OR_UNKNOWN | TypeFlags::NEVER,
        ) {
            return t;
        }
        let key = CachedTypeKey {
            kind: CachedTypeKind::PermissiveInstantiation,
            type_id: t,
        };
        if let Some(&cached) = self.cached_types.get(&key) {
            return cached;
        }
        let permissive_mapper = self.permissive_mapper;
        let result = self.instantiate_type(t, Some(permissive_mapper));
        self.cached_types.insert(key, result);
        result
    }

    /// `(c *Checker) getRestrictiveInstantiation` (checker.go:25026).
    pub(crate) fn get_restrictive_instantiation(&mut self, t: TypeId) -> TypeId {
        if self.types.get(t).flags.intersects(
            TypeFlags::PRIMITIVE | TypeFlags::ANY_OR_UNKNOWN | TypeFlags::NEVER,
        ) {
            return t;
        }
        let key = CachedTypeKey {
            kind: CachedTypeKind::RestrictiveInstantiation,
            type_id: t,
        };
        if let Some(&cached) = self.cached_types.get(&key) {
            return cached;
        }
        let restrictive_mapper = self.restrictive_mapper;
        let result = self.instantiate_type(t, Some(restrictive_mapper));
        self.cached_types.insert(key, result);
        // We set the following so we don't attempt to set the restrictive instance of a restrictive instance
        // which is redundant - we'll produce new type identities, but all type params have already been mapped.
        // This also gives us a way to detect restrictive instances upon comparisons and _disable_ the "distributeive constraint"
        // assignability check for them, which is distinctly unsafe, as once you have a restrctive instance, all the type parameters
        // are constrained to `unknown` and produce tons of false positives/negatives!
        self.cached_types.insert(
            CachedTypeKey {
                kind: CachedTypeKind::RestrictiveInstantiation,
                type_id: result,
            },
            result,
        );
        result
    }

    // `getRestrictiveTypeParameter` (checker.go:25045) — checker_core.rs.
    // `restrictiveMapperWorker` (checker.go:25059) — checker_core.rs.
    // `permissiveMapperWorker` (checker.go:25066) — checker_core.rs.

    /// `(c *Checker) getTrueTypeFromConditionalType` (checker.go:25073).
    pub(crate) fn get_true_type_from_conditional_type(&mut self, t: TypeId) -> TypeId {
        let (root_node, mapper) = {
            let g = self.types.get(t);
            let d = g.as_conditional_type();
            if let Some(resolved) = d.resolved_true_type {
                return resolved;
            }
            (
                d.root.as_ref().expect("nil root").node,
                d.mapper,
            )
        };
        let nodes = self.program_nodes(root_node.expect("nil root.node"));
        let true_type_node = nodes[root_node.unwrap()]
            .as_conditional_type_node()
            .true_type
            .unwrap();
        let resolved =
            self.instantiate_type(self.get_type_from_type_node(true_type_node), mapper);
        let mut g = self.types.get_mut(t);
        as_conditional_type_mut(&mut g).resolved_true_type = Some(resolved);
        resolved
    }

    /// `(c *Checker) getFalseTypeFromConditionalType` (checker.go:25081).
    pub(crate) fn get_false_type_from_conditional_type(&mut self, t: TypeId) -> TypeId {
        let (root_node, mapper) = {
            let g = self.types.get(t);
            let d = g.as_conditional_type();
            if let Some(resolved) = d.resolved_false_type {
                return resolved;
            }
            (
                d.root.as_ref().expect("nil root").node,
                d.mapper,
            )
        };
        let nodes = self.program_nodes(root_node.expect("nil root.node"));
        let false_type_node = nodes[root_node.unwrap()]
            .as_conditional_type_node()
            .false_type
            .unwrap();
        let resolved =
            self.instantiate_type(self.get_type_from_type_node(false_type_node), mapper);
        let mut g = self.types.get_mut(t);
        as_conditional_type_mut(&mut g).resolved_false_type = Some(resolved);
        resolved
    }

    /// `(c *Checker) getInferredTrueTypeFromConditionalType` (checker.go:25089).
    pub(crate) fn get_inferred_true_type_from_conditional_type(&mut self, t: TypeId) -> TypeId {
        let (root_node, combined_mapper) = {
            let g = self.types.get(t);
            let d = g.as_conditional_type();
            if let Some(resolved) = d.resolved_inferred_true_type {
                return resolved;
            }
            (
                d.root.as_ref().expect("nil root").node,
                d.combined_mapper,
            )
        };
        let resolved = if combined_mapper.is_some() {
            let nodes = self.program_nodes(root_node.expect("nil root.node"));
            let true_type_node = nodes[root_node.unwrap()]
                .as_conditional_type_node()
                .true_type
                .unwrap();
            self.instantiate_type(
                self.get_type_from_type_node(true_type_node),
                combined_mapper,
            )
        } else {
            self.get_true_type_from_conditional_type(t)
        };
        let mut g = self.types.get_mut(t);
        as_conditional_type_mut(&mut g).resolved_inferred_true_type = Some(resolved);
        resolved
    }

    /// `(c *Checker) getTypeFromInferTypeNode` (checker.go:25101).
    pub(crate) fn get_type_from_infer_type_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let nodes = self.program_nodes(node);
            let param = nodes[node].as_infer_type_node().type_parameter.unwrap();
            let symbol = self.get_symbol_of_declaration(param);
            let resolved =
                self.get_declared_type_of_type_parameter(symbol.unwrap_or(SymbolId::NONE));
            self.type_node_links.get(node).resolved_type = Some(resolved);
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getTypeFromImportTypeNode` (checker.go:25109).
    pub(crate) fn get_type_from_import_type_node(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.get(node).resolved_type.is_none() {
            let nodes = self.program_nodes(node);
            if !ast::is_literal_import_type_node(&nodes[node], &nodes) {
                let argument = nodes[node].as_import_type_node().argument;
                self.error(argument, &tsc_diagnostics::String_literal_expected, &[]);
                self.symbol_node_links.get(node).resolved_symbol = self.unknown_symbol;
                self.type_node_links.get(node).resolved_type = Some(self.error_type);
                return self.error_type;
            }
            let n_is_type_of = nodes[node].as_import_type_node().is_type_of;
            let target_meaning = if n_is_type_of {
                ast::SymbolFlags::VALUE
            } else {
                ast::SymbolFlags::TYPE
            };
            // TODO: Future work: support unions/generics/whatever via a deferred import-type
            let n_argument = nodes[node].as_import_type_node().argument.unwrap();
            let import_attributes_type = self.get_type_from_import_attributes(
                ast::get_import_attributes(&nodes[node]),
            );
            let literal = nodes[n_argument].as_literal_type_node().literal.unwrap();
            let inner_module_symbol = self.resolve_external_module_name(
                node,
                literal,
                false, /*ignoreErrors*/
                import_attributes_type,
            );
            let Some(inner_module_symbol) = inner_module_symbol else {
                self.symbol_node_links.get(node).resolved_symbol = self.unknown_symbol;
                self.type_node_links.get(node).resolved_type = Some(self.error_type);
                return self.error_type;
            };
            let module_symbol =
                self.resolve_external_module_symbol(inner_module_symbol, false);
            let n_qualifier = nodes[node].as_import_type_node().qualifier;
            if !ast::node_is_missing(n_qualifier, &nodes) {
                let name_chain = self.get_identifier_chain(n_qualifier.unwrap());
                let mut current_namespace = module_symbol;
                for (i, &current) in name_chain.iter().enumerate() {
                    let mut meaning = ast::SymbolFlags::NAMESPACE;
                    if i == name_chain.len() - 1 {
                        meaning = target_meaning;
                    }
                    // typeof a.b.c is normally resolved using `checkExpression` which in turn defers to `checkQualifiedName`
                    // That, in turn, ultimately uses `getPropertyOfType` on the type of the symbol, which differs slightly from
                    // the `exports` lookup process that only looks up namespace members which is used for most type references
                    let merged_resolved_symbol =
                        self.get_merged_symbol(self.resolve_symbol(current_namespace));
                    let mut symbol_from_variable: Option<SymbolId> = None;
                    let mut symbol_from_module: Option<SymbolId> = None;
                    if n_is_type_of {
                        let t = self.get_type_of_symbol(merged_resolved_symbol);
                        symbol_from_variable = self.get_property_of_type_ex(
                            t,
                            &nodes[current].text(&nodes),
                            false, /*skipObjectFunctionPropertyAugment*/
                            true,  /*includeTypeOnlyMembers*/
                        );
                    } else {
                        let exports = self.get_exports_of_symbol(merged_resolved_symbol);
                        symbol_from_module =
                            self.get_symbol(&exports, &nodes[current].text(&nodes), meaning);
                        if symbol_from_module.is_none() {
                            // a CommonJS module might have typedefs exported alongside an export=
                            // !!!
                            let immediate_module_symbol =
                                self.resolve_external_module_symbol(inner_module_symbol, true);
                            if let Some(immediate) = immediate_module_symbol {
                                let decls =
                                    self.symbol_arena.borrow()[immediate.index()]
                                        .declarations
                                        .clone();
                                if core::some(&decls, |&d| {
                                    let d_nodes = self.program_nodes(d);
                                    ast::get_assignment_declaration_kind(d, &d_nodes)
                                        == ast::JsDeclarationKind::ModuleExports
                                }) {
                                    let parent = self.symbol_arena.borrow()[immediate.index()]
                                        .parent
                                        .unwrap_or(SymbolId::NONE);
                                    let exports = self.get_exports_of_symbol(parent);
                                    symbol_from_module = self.get_symbol(
                                        &exports,
                                        &nodes[current].text(&nodes),
                                        meaning,
                                    );
                                }
                            }
                        }
                    }
                    let Some(next) = symbol_from_module.or(symbol_from_variable) else {
                        let fqn = self.get_fully_qualified_name(current_namespace, None);
                        let decl_name = scanner::declaration_name_to_string(
                            Some(current),
                            &nodes,
                        );
                        self.error(
                            Some(current),
                            &tsc_diagnostics::Namespace_0_has_no_exported_member_1,
                            &[fqn, decl_name],
                        );
                        self.type_node_links.get(node).resolved_type = Some(self.error_type);
                        return self.error_type;
                    };
                    self.symbol_node_links.get(current).resolved_symbol = Some(next);
                    let parent = nodes[current].parent;
                    if let Some(parent) = parent {
                        self.symbol_node_links.get(parent).resolved_symbol = Some(next);
                    }
                    current_namespace = next;
                }
                let resolved =
                    self.resolve_import_symbol_type(node, current_namespace, target_meaning);
                self.type_node_links.get(node).resolved_type = Some(resolved);
            } else {
                if self
                    .get_symbol_flags(module_symbol)
                    .intersects(target_meaning)
                {
                    let resolved =
                        self.resolve_import_symbol_type(node, module_symbol, target_meaning);
                    self.type_node_links.get(node).resolved_type = Some(resolved);
                } else {
                    let message = if target_meaning == ast::SymbolFlags::VALUE {
                        &tsc_diagnostics::Module_0_does_not_refer_to_a_value_but_is_used_as_a_value_here
                    } else {
                        &tsc_diagnostics::Module_0_does_not_refer_to_a_type_but_is_used_as_a_type_here_Did_you_mean_typeof_import_0
                    };
                    let lit_text = nodes[literal].text(&nodes).into_owned();
                    self.error(Some(node), message, &[lit_text]);
                    self.symbol_node_links.get(node).resolved_symbol = self.unknown_symbol;
                    self.type_node_links.get(node).resolved_type = Some(self.error_type);
                }
            }
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) getIdentifierChain` (checker.go:25184).
    pub(crate) fn get_identifier_chain(&self, node: NodeId) -> Vec<NodeId> {
        let nodes = self.program_nodes(node);
        if ast::is_identifier(&nodes[node]) {
            return vec![node];
        }
        let q = nodes[node].as_qualified_name();
        let mut chain = self.get_identifier_chain(q.left.unwrap());
        chain.push(q.right.unwrap());
        chain
    }

    /// `(c *Checker) resolveImportSymbolType` (checker.go:25191).
    pub(crate) fn resolve_import_symbol_type(
        &mut self,
        node: NodeId,
        symbol: SymbolId,
        meaning: ast::SymbolFlags,
    ) -> TypeId {
        let resolved_symbol = self.resolve_symbol(symbol);
        self.symbol_node_links.get(node).resolved_symbol = Some(resolved_symbol);
        if meaning == ast::SymbolFlags::VALUE {
            // intentionally doesn't use resolved symbol so type is cached as expected on the alias
            return self.get_instantiation_expression_type(self.get_type_of_symbol(symbol), node);
        }
        // getTypeReferenceType doesn't handle aliases - it must get the resolved symbol
        self.get_type_reference_type(node, resolved_symbol)
    }

    // `createTypeFromGenericGlobalType` (checker.go:25202) — checker_core.rs.
    // `getGlobalStrictFunctionType` (checker.go:25209) — checker_core.rs.
    // `getGlobalImportMetaExpressionType` (checker.go:25216) — checker_core.rs.

    /// `(c *Checker) createIterableType` (checker.go:25231).
    pub(crate) fn create_iterable_type(&mut self, iterated_type: TypeId) -> TypeId {
        let global = self.call_type_thunk(&self.get_global_iterable_type_checked.clone());
        let args = vec![iterated_type, self.void_type, self.undefined_type];
        self.create_type_from_generic_global_type(global, &args)
    }

    // `createArrayType` (checker.go:25235) — checker_core.rs.
    // `createArrayTypeEx` (checker.go:25239) — checker_core.rs.

    /// `(c *Checker) getTupleElementFlags` (checker.go:25243).
    pub(crate) fn get_tuple_element_flags(&mut self, node: NodeId) -> ElementFlags {
        let nodes = self.program_nodes(node);
        match nodes[node].kind {
            ast::Kind::OptionalType => ElementFlags::OPTIONAL,
            ast::Kind::RestType => {
                if self.get_array_element_type_node(nodes[node].type_()).is_some() {
                    ElementFlags::REST
                } else {
                    ElementFlags::VARIADIC
                }
            }
            ast::Kind::NamedTupleMember => {
                let named = nodes[node].as_named_tuple_member();
                if named.question_token.is_some() {
                    return ElementFlags::OPTIONAL;
                }
                if named.dot_dot_dot_token.is_some() {
                    if self.get_array_element_type_node(named.type_).is_some() {
                        return ElementFlags::REST;
                    }
                    return ElementFlags::VARIADIC;
                }
                ElementFlags::REQUIRED
            }
            _ => ElementFlags::REQUIRED,
        }
    }

    /// `(c *Checker) getTupleElementInfo` (checker.go:25262).
    pub(crate) fn get_tuple_element_info(&mut self, node: NodeId) -> TupleElementInfo {
        let nodes = self.program_nodes(node);
        let labeled = if ast::is_named_tuple_member(&nodes[node])
            || ast::is_parameter_declaration(&nodes[node])
        {
            Some(node)
        } else {
            None
        };
        TupleElementInfo {
            flags: self.get_tuple_element_flags(node),
            labeled_declaration: labeled,
        }
    }

    /// `(c *Checker) createTupleType` (checker.go:25269).
    pub(crate) fn create_tuple_type(&mut self, element_types: &[TypeId]) -> TypeId {
        let element_infos: Vec<TupleElementInfo> = element_types
            .iter()
            .map(|_| TupleElementInfo {
                flags: ElementFlags::REQUIRED,
                labeled_declaration: None,
            })
            .collect();
        self.create_tuple_type_ex(element_types, &element_infos, false)
    }

    /// `(c *Checker) createTupleTypeEx` (checker.go:25274).
    pub(crate) fn create_tuple_type_ex(
        &mut self,
        element_types: &[TypeId],
        element_infos: &[TupleElementInfo],
        readonly: bool,
    ) -> TypeId {
        let tuple_target = self.get_tuple_target_type(element_infos, readonly);
        if tuple_target == self.empty_generic_type {
            self.empty_object_type
        } else if !element_types.is_empty() {
            self.create_normalized_type_reference(tuple_target, element_types)
        } else {
            tuple_target
        }
    }

    /// `(c *Checker) getTupleTargetType` (checker.go:25285).
    pub(crate) fn get_tuple_target_type(
        &mut self,
        element_infos: &[TupleElementInfo],
        readonly: bool,
    ) -> TypeId {
        if element_infos.len() == 1
            && element_infos[0].flags.intersects(ElementFlags::REST)
        {
            // [...X[]] is equivalent to just X[]
            if readonly {
                return self.global_readonly_array_type;
            }
            return self.global_array_type;
        }
        let key = crate::checker_types::get_tuple_key(element_infos, readonly);
        if let Some(&t) = self.tuple_types.get(&key) {
            return t;
        }
        let t = self.create_tuple_target_type(element_infos, readonly);
        self.tuple_types.insert(key, t);
        t
    }

    // We represent tuple types as type references to synthesized generic interface types created by
    // this function. The types are of the form:
    //
    //	interface Tuple<T0, T1, T2, ...> extends Array<T0 | T1 | T2 | ...> { 0: T0, 1: T1, 2: T2, ... }
    //
    // Note that the generic type created by this function has no symbol associated with it. The same
    // is true for each of the synthesized type parameters.

    /// `(c *Checker) createTupleTargetType` (checker.go:25307).
    pub(crate) fn create_tuple_target_type(
        &mut self,
        element_infos: &[TupleElementInfo],
        readonly: bool,
    ) -> TypeId {
        let arity = element_infos.len();
        let min_length = element_infos
            .iter()
            .filter(|e| {
                e.flags
                    .intersects(ElementFlags::REQUIRED | ElementFlags::VARIADIC)
            })
            .count();
        let mut type_parameters: Vec<TypeId> = Vec::new();
        let mut members = SymbolTable::new();
        let mut combined_flags = ElementFlags::NONE;
        if arity != 0 {
            type_parameters = Vec::with_capacity(arity);
            for i in 0..arity {
                let type_parameter = self.new_type_parameter(None);
                type_parameters.push(type_parameter);
                let flags = element_infos[i].flags;
                combined_flags |= flags;
                if !combined_flags.intersects(ElementFlags::VARIABLE) {
                    let property = self.new_symbol_ex(
                        ast::SymbolFlags::PROPERTY
                            | if flags.intersects(ElementFlags::OPTIONAL) {
                                ast::SymbolFlags::OPTIONAL
                            } else {
                                ast::SymbolFlags::NONE
                            },
                        &i.to_string(),
                        if readonly {
                            CheckFlags::READONLY
                        } else {
                            CheckFlags::NONE
                        },
                    );
                    self.value_symbol_links.get(property).resolved_type = Some(type_parameter);
                    // `valueSymbolLinks.get(property).tupleLabelDeclaration = elementInfos[i].labeledDeclaration`
                    let name = self.symbol_arena.borrow()[property.index()].name.clone();
                    members.set(name, property);
                }
            }
        }
        let fixed_length = members.size();
        let length_symbol = self.new_symbol_ex(
            ast::SymbolFlags::PROPERTY,
            "length",
            if readonly {
                CheckFlags::READONLY
            } else {
                CheckFlags::NONE
            },
        );
        if combined_flags.intersects(ElementFlags::VARIABLE) {
            self.value_symbol_links.get(length_symbol).resolved_type = Some(self.number_type);
        } else {
            let mut literal_types = Vec::new();
            for i in min_length..=arity {
                literal_types.push(self.get_number_literal_type(Number(i as f64)));
            }
            self.value_symbol_links.get(length_symbol).resolved_type =
                Some(self.get_union_type(&literal_types));
        }
        let length_name = self.symbol_arena.borrow()[length_symbol.index()].name.clone();
        members.set(length_name, length_symbol);
        let t = self.new_object_type(ObjectFlags::TUPLE | ObjectFlags::REFERENCE, None);
        // `d := t.AsTupleType()`
        let this_type = self.new_type_parameter(None);
        {
            // `d.thisType.AsTypeParameter().isThisType = true; constraint = t`
            let mut tg = self.types.get_mut(this_type);
            match &mut tg.data {
                TypeData::TypeParameter(tp) => {
                    tp.is_this_type = true;
                    tp.constraint = Some(t);
                }
                _ => panic!("newTypeParameter: not a type parameter"),
            }
        }
        let mut g = self.types.get_mut(t);
        let d = match &mut g.data {
            TypeData::Tuple(d) => d,
            _ => panic!("createTupleTargetType: not a tuple type"),
        };
        d.interface_type.this_type = Some(this_type);
        let mut all = type_parameters.clone();
        all.push(this_type);
        d.interface_type.all_type_parameters = all;
        let tp_key = crate::checker_types::get_type_list_key(d.interface_type.type_parameters());
        d.interface_type
            .type_reference
            .object_type
            .instantiations
            .insert(tp_key, t);
        d.interface_type.type_reference.object_type.target = Some(t);
        d.interface_type.type_reference.resolved_type_arguments =
            d.interface_type.type_parameters().to_vec();
        d.interface_type.declared_members_resolved = true;
        d.interface_type.declared_members = members;
        d.element_infos = element_infos.to_vec();
        d.min_length = min_length;
        d.fixed_length = fixed_length;
        d.combined_flags = combined_flags;
        d.readonly = readonly;
        drop(g);
        t
    }
}

impl Checker {
    /// `(c *Checker) getElementTypeOfSliceOfTupleType` (checker.go:25364).
    /// Go `int` → `usize`; `nil` → `None`.
    pub(crate) fn get_element_type_of_slice_of_tuple_type(
        &mut self,
        t: TypeId,
        index: usize,
        end_skip_count: usize,
        writing: bool,
        no_reductions: bool,
    ) -> Option<TypeId> {
        let length = self.get_type_reference_arity(t) - end_skip_count;
        let element_infos = self
            .types
            .get(self.types.target_tuple_type(t).unwrap())
            .as_tuple_type()
            .element_infos
            .clone();
        if index < length {
            let type_arguments = self.get_type_arguments(t);
            let mut element_types = Vec::new();
            for i in index..length {
                let mut e = type_arguments[i];
                if element_infos[i].flags.intersects(ElementFlags::VARIADIC) {
                    e = self.get_indexed_access_type(e, self.number_type);
                }
                element_types.push(e);
            }
            if writing {
                return Some(self.get_intersection_type(&element_types));
            }
            return Some(self.get_union_type_ex(
                &element_types,
                if no_reductions {
                    UnionReduction::None
                } else {
                    UnionReduction::Literal
                },
                None,
                None,
            ));
        }
        None
    }

    /// `(c *Checker) getRestTypeOfTupleType` (checker.go:25385).
    pub(crate) fn get_rest_type_of_tuple_type(&mut self, t: TypeId) -> Option<TypeId> {
        let fixed_length = self
            .types
            .get(self.types.target_tuple_type(t).unwrap())
            .as_tuple_type()
            .fixed_length;
        self.get_element_type_of_slice_of_tuple_type(t, fixed_length, 0, false, false)
    }

    /// `(c *Checker) getTupleElementTypeOutOfStartCount` (checker.go:25389).
    pub(crate) fn get_tuple_element_type_out_of_start_count(
        &mut self,
        t: TypeId,
        index: Number,
        undefined_like_type: Option<TypeId>,
    ) -> TypeId {
        self.map_type(t, Rc::new(move |c: &mut Checker, t: TypeId| -> TypeId {
            let Some(rest_type) = c.get_rest_type_of_tuple_type(t) else {
                return c.undefined_type;
            };
            if let Some(undefined_like_type) = undefined_like_type {
                let target = c.types.target_tuple_type(t).unwrap();
                let fixed = crate::checker_c::get_total_fixed_element_count(
                    c.types.get(target).as_tuple_type(),
                );
                if index >= Number(fixed as f64) {
                    return c.get_union_type(&[rest_type, undefined_like_type]);
                }
            }
            rest_type
        }))
    }

    /// `(c *Checker) isGenericType` (checker.go:25402).
    pub(crate) fn is_generic_type(&mut self, t: TypeId) -> bool {
        !self.get_generic_object_flags(t).is_empty()
    }

    /// `(c *Checker) isGenericObjectType` (checker.go:25406).
    pub(crate) fn is_generic_object_type(&mut self, t: TypeId) -> bool {
        self.get_generic_object_flags(t)
            .intersects(ObjectFlags::IS_GENERIC_OBJECT_TYPE)
    }

    /// `(c *Checker) isGenericIndexType` (checker.go:25410).
    pub(crate) fn is_generic_index_type(&mut self, t: TypeId) -> bool {
        self.get_generic_object_flags(t)
            .intersects(ObjectFlags::IS_GENERIC_INDEX_TYPE)
    }

    /// `(c *Checker) getGenericObjectFlags` (checker.go:25414).
    pub(crate) fn get_generic_object_flags(&mut self, t: TypeId) -> ObjectFlags {
        let mut combined_flags = ObjectFlags::NONE;
        if self
            .types
            .get(t)
            .flags
            .intersects(TypeFlags::UNION_OR_INTERSECTION | TypeFlags::SUBSTITUTION)
        {
            if !self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::IS_GENERIC_TYPE_COMPUTED)
            {
                if self
                    .types
                    .get(t)
                    .flags
                    .intersects(TypeFlags::UNION_OR_INTERSECTION)
                {
                    let types = self.types.get(t).types().to_vec();
                    for u in types {
                        combined_flags |= self.get_generic_object_flags(u);
                    }
                } else {
                    let (base_type, constraint) = {
                        let g = self.types.get(t);
                        let d = g.as_substitution_type();
                        (d.base_type, d.constraint)
                    };
                    combined_flags = self.get_generic_object_flags(base_type)
                        | self.get_generic_object_flags(constraint);
                }
                self.types.get_mut(t).object_flags |=
                    ObjectFlags::IS_GENERIC_TYPE_COMPUTED | combined_flags;
            }
            return self.types.get(t).object_flags & ObjectFlags::IS_GENERIC_TYPE;
        }
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE)
            || self.is_generic_mapped_type(t)
            || self.is_generic_tuple_type(t)
        {
            combined_flags.insert(ObjectFlags::IS_GENERIC_OBJECT_TYPE);
        }
        if flags.intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE | TypeFlags::INDEX)
            || self.is_generic_string_like_type(t)
        {
            combined_flags.insert(ObjectFlags::IS_GENERIC_INDEX_TYPE);
        }
        combined_flags
    }

    /// `(c *Checker) isGenericTupleType` (checker.go:25438).
    pub(crate) fn is_generic_tuple_type(&mut self, t: TypeId) -> bool {
        crate::checker_core::is_tuple_type(&self.types, t)
            && self
                .types
                .get(self.types.target_tuple_type(t).unwrap())
                .as_tuple_type()
                .combined_flags
                .intersects(ElementFlags::VARIADIC)
    }

    /// `(c *Checker) isGenericMappedType` (checker.go:25442).
    pub(crate) fn is_generic_mapped_type(&mut self, t: TypeId) -> bool {
        if self
            .types
            .get(t)
            .object_flags
            .intersects(ObjectFlags::MAPPED)
        {
            let constraint = self.get_constraint_type_from_mapped_type(t);
            if self.is_generic_index_type(constraint.unwrap_or(TypeId::NONE)) {
                return true;
            }
            // A mapped type is generic if the 'as' clause references generic types other than the iteration type.
            // To determine this, we substitute the constraint type (that we now know isn't generic) for the iteration
            // type and check whether the resulting type is generic.
            let name_type = self.get_name_type_from_mapped_type(t);
            if let Some(name_type) = name_type {
                let tp = self.get_type_parameter_from_mapped_type(t);
                let m = mapper::new_simple_type_mapper(
                    self,
                    tp.unwrap_or(TypeId::NONE),
                    constraint.unwrap_or(TypeId::NONE),
                );
                if self.is_generic_index_type(self.instantiate_type(name_type, Some(m))) {
                    return true;
                }
            }
        }
        false
    }

    /// A union type which is reducible upon instantiation (meaning some members are removed under certain instantiations)
    /// must be kept generic, as that instantiation information needs to flow through the type system. By replacing all
    /// type parameters in the union with a special never type that is treated as a literal in `getReducedType`, we can cause
    /// the `getReducedType` logic to reduce the resulting type if possible (since only intersections with conflicting
    /// literal-typed properties are reducible).
    ///
    /// `(c *Checker) isGenericReducibleType` (checker.go:25466).
    pub(crate) fn is_generic_reducible_type(&mut self, t: TypeId) -> bool {
        self.types.get(t).flags.intersects(TypeFlags::UNION)
            && self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::CONTAINS_INTERSECTIONS)
            && {
                let types = self.types.get(t).types().to_vec();
                core::some(&types, |&u| self.is_generic_reducible_type(u))
            }
            || self.types.get(t).flags.intersects(TypeFlags::INTERSECTION)
                && self.is_reducible_intersection(t)
    }

    /// `(c *Checker) isReducibleIntersection` (checker.go:25471).
    pub(crate) fn is_reducible_intersection(&mut self, t: TypeId) -> bool {
        let unique_literal_filled_instantiation = {
            let g = self.types.get(t);
            g.as_intersection_type().unique_literal_filled_instantiation
        };
        let instantiation = match unique_literal_filled_instantiation {
            Some(t) => t,
            None => {
                let unique_literal_mapper = self.unique_literal_mapper;
                let instantiation = self.instantiate_type(t, Some(unique_literal_mapper));
                let mut g = self.types.get_mut(t);
                as_intersection_type_mut(&mut g).unique_literal_filled_instantiation =
                    Some(instantiation);
                instantiation
            }
        };
        self.get_reduced_type(instantiation) != instantiation
    }

    // `getUniqueLiteralTypeForTypeParameter` (checker.go:25479) — checker_core.rs.

    /// `(c *Checker) getConditionalFlowTypeOfType` (checker.go:25486).
    pub(crate) fn get_conditional_flow_type_of_type(
        &mut self,
        t: TypeId,
        node: NodeId,
    ) -> TypeId {
        let mut constraints: Vec<TypeId> = Vec::new();
        let mut covariant = true;
        let mut node = Some(node);
        while let Some(n) = node {
            let nodes = self.program_nodes(n);
            if ast::is_statement(n, &nodes) || nodes[n].kind == ast::Kind::JSDoc {
                break;
            }
            let Some(parent) = nodes[n].parent else {
                break;
            };
            // only consider variance flipped by parameter locations - `keyof` types would usually be considered variance inverting, but
            // often get used in indexed accesses where they behave sortof invariantly, but our checking is lax
            if ast::is_parameter_declaration(&nodes[parent]) {
                covariant = !covariant;
            }
            let t_flags = self.types.get(t).flags;
            // Always substitute on type parameters, regardless of variance, since even
            // in contravariant positions, they may rely on substituted constraints to be valid
            if (covariant || t_flags.intersects(TypeFlags::TYPE_VARIABLE))
                && ast::is_conditional_type_node(&nodes[parent])
                && Some(n)
                    == nodes[parent]
                        .as_conditional_type_node()
                        .true_type
            {
                let check_node = nodes[parent]
                    .as_conditional_type_node()
                    .check_type
                    .unwrap();
                let extends_node = nodes[parent]
                    .as_conditional_type_node()
                    .extends_type
                    .unwrap();
                if let Some(constraint) =
                    self.get_implied_constraint(t, check_node, extends_node)
                {
                    constraints.push(constraint);
                }
            } else if t_flags.intersects(TypeFlags::TYPE_PARAMETER)
                && ast::is_mapped_type_node(&nodes[parent])
                && nodes[parent].as_mapped_type_node().name_type.is_none()
                && Some(n) == nodes[parent].type_()
            {
                let mapped_type = self.get_type_from_type_node(parent);
                if self.get_type_parameter_from_mapped_type(mapped_type)
                    == Some(self.get_actual_type_variable(t))
                {
                    if let Some(type_parameter) =
                        self.get_homomorphic_type_variable(mapped_type)
                    {
                        if let Some(constraint) =
                            self.get_constraint_of_type_parameter(type_parameter)
                        {
                            if every_type(&mut *self, constraint, |c, t| {
                                c.is_array_or_tuple_type(t)
                            }) {
                                constraints.push(self.get_union_type(&[
                                    self.number_type,
                                    self.numeric_string_type,
                                ]));
                            }
                        }
                    }
                }
            }
            node = Some(parent);
        }
        if !constraints.is_empty() {
            return self.get_substitution_type(t, self.get_intersection_type(&constraints));
        }
        t
    }

    /// `(c *Checker) getImpliedConstraint` (checker.go:25523).
    pub(crate) fn get_implied_constraint(
        &mut self,
        t: TypeId,
        check_node: NodeId,
        extends_node: NodeId,
    ) -> Option<TypeId> {
        let check_elements = {
            let nodes = self.program_nodes(check_node);
            if is_unary_tuple_type_node(&nodes[check_node]) {
                let e_nodes = self.program_nodes(extends_node);
                if is_unary_tuple_type_node(&e_nodes[extends_node]) {
                    Some((
                        nodes[check_node].elements().unwrap()[0],
                        e_nodes[extends_node].elements().unwrap()[0],
                    ))
                } else {
                    None
                }
            } else {
                None
            }
        };
        if let Some((check_el, extends_el)) = check_elements {
            return self.get_implied_constraint(t, check_el, extends_el);
        }
        if self.get_actual_type_variable(self.get_type_from_type_node(check_node))
            == self.get_actual_type_variable(t)
        {
            return Some(self.get_type_from_type_node(extends_node));
        }
        None
    }
}

/// `isUnaryTupleTypeNode` (checker.go:25533) — package-level.
pub(crate) fn is_unary_tuple_type_node(node: &ast::Node) -> bool {
    ast::is_tuple_type_node(node) && node.elements().map_or(0, |e| e.len()) == 1
}

impl Checker {
    /// `(c *Checker) newConditionalType` (checker.go:25764).
    pub(crate) fn new_conditional_type(
        &mut self,
        root: ConditionalRoot,
        mapper: Option<TypeMapperId>,
        combined_mapper: Option<TypeMapperId>,
    ) -> TypeId {
        let check_type =
            self.instantiate_type(root.check_type.unwrap_or(TypeId::NONE), mapper);
        let extends_type =
            self.instantiate_type(root.extends_type.unwrap_or(TypeId::NONE), mapper);
        self.new_type(
            TypeFlags::CONDITIONAL,
            ObjectFlags::NONE,
            TypeData::Conditional(ConditionalType {
                root: Some(Box::new(root)),
                check_type: Some(check_type),
                extends_type: Some(extends_type),
                mapper,
                combined_mapper,
                ..Default::default()
            }),
        )
    }

    /// `(c *Checker) getRegularTypeOfLiteralType` — checker_core.rs.
    /// `(c *Checker) getFreshTypeOfLiteralType` — checker_core.rs.

    /// `(c *Checker) getEnumLiteralType` (checker.go:25896). Go `value any`
    /// → `evaluator::Value`; the `enum_symbol` key is `Option` because the
    /// key struct models Go's nilable pointer.
    pub(crate) fn get_enum_literal_type(
        &mut self,
        value: evaluator::Value,
        enum_symbol: SymbolId,
        symbol: SymbolId,
    ) -> TypeId {
        let flags;
        match &value {
            evaluator::Value::String(_) => {
                flags = TypeFlags::ENUM_LITERAL | TypeFlags::STRING_LITERAL;
            }
            evaluator::Value::Number(v) => {
                flags = TypeFlags::ENUM_LITERAL | TypeFlags::NUMBER_LITERAL;
                // NaN cannot be used as a Go map key because NaN != NaN in IEEE 754,
                // so Go map lookups for NaN always miss. Cache NaN enum types separately by enum symbol.
                if v.is_nan() {
                    if let Some(&t) = self.enum_nan_literal_types.get(&enum_symbol) {
                        return t;
                    }
                    let t = self.new_literal_type(flags, Some(value.clone()), None);
                    self.types.get_mut(t).symbol = Some(symbol);
                    self.enum_nan_literal_types.insert(enum_symbol, t);
                    return t;
                }
            }
            _ => panic!("Unhandled case in getEnumLiteralType"),
        }
        let key = crate::checker_core::EnumLiteralKey {
            enum_symbol: Some(enum_symbol),
            value: Some(value.clone()),
        };
        if let Some(&t) = self.enum_literal_types.get(&key) {
            return t;
        }
        let t = self.new_literal_type(flags, Some(value), None);
        self.types.get_mut(t).symbol = Some(symbol);
        self.enum_literal_types.insert(key, t);
        t
    }

    /// `(c *Checker) isUnitLikeType` (checker.go:25948).
    pub(crate) fn is_unit_like_type(&mut self, t: TypeId) -> bool {
        // Intersections that reduce to 'never' (e.g. 'T & null' where 'T extends {}') are not unit types.
        let t = self.get_base_constraint_or_type(t);
        // Scan intersections such that tagged literal types are considered unit types.
        if self.types.get(t).flags.intersects(TypeFlags::INTERSECTION) {
            let types = self.types.get(t).types().to_vec();
            return core::some(&types, |&t| is_unit_type(&self.types, t));
        }
        is_unit_type(&self.types, t)
    }

    /// `(c *Checker) extractUnitType` (checker.go:25958).
    pub(crate) fn extract_unit_type(&mut self, t: TypeId) -> TypeId {
        if self.types.get(t).flags.intersects(TypeFlags::INTERSECTION) {
            let types = self.types.get(t).types().to_vec();
            if let Some(u) = types
                .iter()
                .copied()
                .find(|&t| is_unit_type(&self.types, t))
            {
                return u;
            }
        }
        t
    }

    /// `(c *Checker) getBaseTypeOfLiteralType` (checker.go:25968).
    pub(crate) fn get_base_type_of_literal_type(&mut self, t: TypeId) -> TypeId {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::ENUM_LIKE) {
            return self.get_base_type_of_enum_like_type(t);
        }
        if flags.intersects(
            TypeFlags::STRING_LITERAL
                | TypeFlags::TEMPLATE_LITERAL
                | TypeFlags::STRING_MAPPING,
        ) {
            return self.string_type;
        }
        if flags.intersects(TypeFlags::NUMBER_LITERAL) {
            return self.number_type;
        }
        if flags.intersects(TypeFlags::BIG_INT_LITERAL) {
            return self.bigint_type;
        }
        if flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
            return self.boolean_type;
        }
        if flags.intersects(TypeFlags::UNION) {
            return self.get_base_type_of_literal_type_union(t);
        }
        t
    }

    /// This like getBaseTypeOfLiteralType, but instead treats enum literals as strings/numbers instead
    /// of returning their enum base type (which depends on the types of other literals in the enum).
    ///
    /// `(c *Checker) getBaseTypeOfLiteralTypeForComparison` (checker.go:25988).
    pub(crate) fn get_base_type_of_literal_type_for_comparison(&mut self, t: TypeId) -> TypeId {
        let flags = self.types.get(t).flags;
        if flags.intersects(
            TypeFlags::STRING_LITERAL
                | TypeFlags::TEMPLATE_LITERAL
                | TypeFlags::STRING_MAPPING,
        ) {
            return self.string_type;
        }
        if flags.intersects(TypeFlags::NUMBER_LITERAL | TypeFlags::ENUM) {
            return self.number_type;
        }
        if flags.intersects(TypeFlags::BIG_INT_LITERAL) {
            return self.bigint_type;
        }
        if flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
            return self.boolean_type;
        }
        if flags.intersects(TypeFlags::UNION) {
            return self.map_type(
                t,
                Rc::new(|c: &mut Checker, t| c.get_base_type_of_literal_type_for_comparison(t)),
            );
        }
        t
    }

    /// `(c *Checker) getBaseTypeOfEnumLikeType` (checker.go:26004).
    pub(crate) fn get_base_type_of_enum_like_type(&mut self, t: TypeId) -> TypeId {
        let symbol = self.types.get(t).symbol;
        if self.types.get(t).flags.intersects(TypeFlags::ENUM_LIKE)
            && symbol.is_some()
            && self
                .sym_flags(symbol.unwrap())
                .intersects(ast::SymbolFlags::ENUM_MEMBER)
        {
            return self.get_declared_type_of_symbol(
                self.get_parent_of_symbol(symbol.unwrap()),
            );
        }
        t
    }

    /// `(c *Checker) getBaseTypeOfLiteralTypeUnion` (checker.go:26011).
    pub(crate) fn get_base_type_of_literal_type_union(&mut self, t: TypeId) -> TypeId {
        let key = CachedTypeKey {
            kind: CachedTypeKind::LiteralUnionBaseType,
            type_id: t,
        };
        if let Some(&cached) = self.cached_types.get(&key) {
            return cached;
        }
        let result = self.map_type(
            t,
            Rc::new(|c: &mut Checker, t| c.get_base_type_of_literal_type(t)),
        );
        self.cached_types.insert(key, result);
        result
    }
}

/// `isFreshLiteralType` (checker.go:25835) — package-level.
pub(crate) fn is_fresh_literal_type(types: &TypeArena, t: TypeId) -> bool {
    let ty = types.get(t);
    ty.flags.intersects(TypeFlags::FRESHABLE)
        && ty.as_literal_type().fresh_type == Some(t)
}

/// `getStringLiteralValue` (checker.go:25880) — package-level.
pub(crate) fn get_string_literal_value(types: &TypeArena, t: TypeId) -> String {
    match types.get(t).as_literal_type().value.as_ref().expect("literal value") {
        evaluator::Value::String(s) => s.clone(),
        _ => panic!("getStringLiteralValue: not a string"),
    }
}

/// `getNumberLiteralValue` (checker.go:25884) — package-level.
pub(crate) fn get_number_literal_value(types: &TypeArena, t: TypeId) -> Number {
    match types.get(t).as_literal_type().value.as_ref().expect("literal value") {
        evaluator::Value::Number(n) => *n,
        _ => panic!("getNumberLiteralValue: not a number"),
    }
}

/// `getBigIntLiteralValue` (checker.go:25888) — package-level.
pub(crate) fn get_big_int_literal_value(types: &TypeArena, t: TypeId) -> PseudoBigInt {
    match types.get(t).as_literal_type().value.as_ref().expect("literal value") {
        evaluator::Value::PseudoBigInt(n) => n.clone(),
        _ => panic!("getBigIntLiteralValue: not a bigint"),
    }
}

/// `getBooleanLiteralValue` (checker.go:25892) — package-level.
pub(crate) fn get_boolean_literal_value(types: &TypeArena, t: TypeId) -> bool {
    match types.get(t).as_literal_type().value.as_ref().expect("literal value") {
        evaluator::Value::Bool(b) => *b,
        _ => panic!("getBooleanLiteralValue: not a bool"),
    }
}

/// `isLiteralType` (checker.go:25927) — package-level.
pub(crate) fn is_literal_type(types: &TypeArena, t: TypeId) -> bool {
    let ty = types.get(t);
    if ty.flags.intersects(TypeFlags::BOOLEAN) {
        return true;
    }
    if ty.flags.intersects(TypeFlags::UNION) {
        if ty.flags.intersects(TypeFlags::ENUM_LITERAL) {
            return true;
        }
        return ty.types().iter().all(|&u| {
            types.get(u).flags.intersects(TypeFlags::UNIT)
        });
    }
    ty.flags.intersects(TypeFlags::UNIT)
}

/// `isNeitherUnitTypeNorNever` (checker.go:25940) — package-level.
pub(crate) fn is_neither_unit_type_nor_never(types: &TypeArena, t: TypeId) -> bool {
    !types.get(t).flags.intersects(TypeFlags::UNIT | TypeFlags::NEVER)
}

/// `isUnitType` (checker.go:25944) — package-level.
pub(crate) fn is_unit_type(types: &TypeArena, t: TypeId) -> bool {
    types.get(t).flags.intersects(TypeFlags::UNIT)
}

impl Checker {
    /// `(c *Checker) getWidenedLiteralType` (checker.go:26021).
    pub(crate) fn get_widened_literal_type(&mut self, t: TypeId) -> TypeId {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::ENUM_LIKE) && is_fresh_literal_type(&self.types, t) {
            return self.get_base_type_of_enum_like_type(t);
        }
        if flags.intersects(TypeFlags::STRING_LITERAL) && is_fresh_literal_type(&self.types, t) {
            return self.string_type;
        }
        if flags.intersects(TypeFlags::NUMBER_LITERAL) && is_fresh_literal_type(&self.types, t) {
            return self.number_type;
        }
        if flags.intersects(TypeFlags::BIG_INT_LITERAL) && is_fresh_literal_type(&self.types, t) {
            return self.bigint_type;
        }
        if flags.intersects(TypeFlags::BOOLEAN_LITERAL) && is_fresh_literal_type(&self.types, t) {
            return self.boolean_type;
        }
        if flags.intersects(TypeFlags::UNION) {
            return self.map_type(
                t,
                Rc::new(|c: &mut Checker, t| c.get_widened_literal_type(t)),
            );
        }
        t
    }

    /// `(c *Checker) getWidenedUniqueESSymbolType` (checker.go:26039).
    pub(crate) fn get_widened_unique_es_symbol_type(&mut self, t: TypeId) -> TypeId {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
            return self.es_symbol_type;
        }
        if flags.intersects(TypeFlags::UNION) {
            return self.map_type(
                t,
                Rc::new(|c: &mut Checker, t| c.get_widened_unique_es_symbol_type(t)),
            );
        }
        t
    }

    /// `(c *Checker) getWidenedLiteralLikeTypeForContextualType` (checker.go:26049).
    pub(crate) fn get_widened_literal_like_type_for_contextual_type(
        &mut self,
        t: TypeId,
        contextual_type: Option<TypeId>,
    ) -> TypeId {
        let mut t = t;
        if !self.is_literal_of_contextual_type(t, contextual_type) {
            t = self.get_widened_unique_es_symbol_type(self.get_widened_literal_type(t));
        }
        self.get_regular_type_of_literal_type(t)
    }

    /// `(c *Checker) isLiteralOfContextualType` (checker.go:26056).
    pub(crate) fn is_literal_of_contextual_type(
        &mut self,
        candidate_type: TypeId,
        contextual_type: Option<TypeId>,
    ) -> bool {
        let Some(contextual_type) = contextual_type else {
            return false;
        };
        let contextual_flags = self.types.get(contextual_type).flags;
        if contextual_flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
            let types = self.types.get(contextual_type).types().to_vec();
            return core::some(&types, |&t| {
                self.is_literal_of_contextual_type(candidate_type, Some(t))
            });
        }
        if contextual_flags.intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE) {
            // If the contextual type is a type variable constrained to a primitive type, consider
            // this a literal context for literals of that primitive type. For example, given a
            // type parameter 'T extends string', infer string literal types for T.
            let constraint = self
                .get_base_constraint_of_type(contextual_type)
                .unwrap_or(self.unknown_type);
            return self.maybe_type_of_kind(constraint, TypeFlags::STRING)
                && self.maybe_type_of_kind(candidate_type, TypeFlags::STRING_LITERAL)
                || self.maybe_type_of_kind(constraint, TypeFlags::NUMBER)
                    && self.maybe_type_of_kind(candidate_type, TypeFlags::NUMBER_LITERAL)
                || self.maybe_type_of_kind(constraint, TypeFlags::BIG_INT)
                    && self.maybe_type_of_kind(candidate_type, TypeFlags::BIG_INT_LITERAL)
                || self.maybe_type_of_kind(constraint, TypeFlags::ES_SYMBOL)
                    && self.maybe_type_of_kind(candidate_type, TypeFlags::UNIQUE_ES_SYMBOL)
                || self.is_literal_of_contextual_type(candidate_type, Some(constraint));
        }
        // If the contextual type is a literal of a particular primitive type, we consider this a
        // literal context for all literals of that primitive type.
        contextual_flags.intersects(
            TypeFlags::STRING_LITERAL
                | TypeFlags::INDEX
                | TypeFlags::TEMPLATE_LITERAL
                | TypeFlags::STRING_MAPPING,
        ) && self.maybe_type_of_kind(candidate_type, TypeFlags::STRING_LITERAL)
            || contextual_flags.intersects(TypeFlags::NUMBER_LITERAL)
                && self.maybe_type_of_kind(candidate_type, TypeFlags::NUMBER_LITERAL)
            || contextual_flags.intersects(TypeFlags::BIG_INT_LITERAL)
                && self.maybe_type_of_kind(candidate_type, TypeFlags::BIG_INT_LITERAL)
            || contextual_flags.intersects(TypeFlags::BOOLEAN_LITERAL)
                && self.maybe_type_of_kind(candidate_type, TypeFlags::BOOLEAN_LITERAL)
            || contextual_flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL)
                && self.maybe_type_of_kind(candidate_type, TypeFlags::UNIQUE_ES_SYMBOL)
    }

    /// `(c *Checker) mapTypeWithAlias` (checker.go:26088).
    ///
    /// PORT: the Go `f` can return nil; here `f` returning `TypeId::NONE`
    /// models that (see `map_type_ex`).
    pub(crate) fn map_type_with_alias(
        &mut self,
        t: TypeId,
        f: Rc<dyn Fn(&mut Checker, TypeId) -> TypeId>,
        alias: &Option<TypeAlias>,
    ) -> Option<TypeId> {
        if self.types.get(t).flags.intersects(TypeFlags::UNION) && alias.is_some() {
            let types = self.types.get(t).types().to_vec();
            let mapped: Vec<TypeId> = types
                .iter()
                .map(|&t| f(self, t))
                .collect();
            return Some(self.get_union_type_ex(
                &mapped,
                UnionReduction::Literal,
                alias.clone(),
                None,
            ));
        }
        self.map_type_ex(t, f, false)
    }

    /// `(c *Checker) mapTypeEx` (checker.go:26099).
    ///
    /// PORT: `f` returning `TypeId::NONE` models Go `mapped == nil`. Returns
    /// `None` where Go returns nil (empty `mappedTypes` after a change).
    pub(crate) fn map_type_ex(
        &mut self,
        t: TypeId,
        f: Rc<dyn Fn(&mut Checker, TypeId) -> TypeId>,
        no_reductions: bool,
    ) -> Option<TypeId> {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::NEVER) {
            return Some(t);
        }
        if !flags.intersects(TypeFlags::UNION) {
            let mapped = f(self, t);
            return if mapped == TypeId::NONE { None } else { Some(mapped) };
        }
        let (types, origin) = {
            let g = self.types.get(t);
            let u = g.as_union_type();
            let mut types = u.union_or_intersection.types.clone();
            if let Some(origin) = u.origin {
                if self
                    .types
                    .get(origin)
                    .flags
                    .intersects(TypeFlags::UNION)
                {
                    types = self.types.get(origin).types().to_vec();
                }
            }
            (types, u.origin)
        };
        let _ = origin;
        let mut mapped_types: Vec<TypeId> = Vec::with_capacity(16);
        let mut changed = false;
        for s in types {
            let mapped = if self.types.get(s).flags.intersects(TypeFlags::UNION) {
                self.map_type_ex(s, f.clone(), no_reductions)
                    .unwrap_or(TypeId::NONE)
            } else {
                f(self, s)
            };
            if mapped != s {
                changed = true;
            }
            if mapped != TypeId::NONE {
                mapped_types.push(mapped);
            }
        }
        if changed {
            if mapped_types.is_empty() {
                return None;
            }
            return Some(self.get_union_type_ex(
                &mapped_types,
                if no_reductions {
                    UnionReduction::None
                } else {
                    UnionReduction::Literal
                },
                None, /*alias*/
                None, /*origin*/
            ));
        }
        Some(t)
    }

    /// `(c *Checker) getUnionOrIntersectionType` (checker.go:26144).
    pub(crate) fn get_union_or_intersection_type(
        &mut self,
        types: &[TypeId],
        is_union: bool,
        union_reduction: UnionReduction,
    ) -> TypeId {
        if is_union {
            return self.get_union_type_ex(types, union_reduction, None, None);
        }
        self.get_intersection_type(types)
    }
}

impl Checker {
    // `getUnionType` (checker.go:26151) — checker_core.rs.

    // We sort and deduplicate the constituent types based on object identity. If the subtypeReduction
    // flag is specified we also reduce the constituent type set to only include types that aren't subtypes
    // of other types. Subtype reduction is expensive for large union types and is possible only when union
    // types are known not to circularly reference themselves (as is the case with union types created by
    // expression constructs such as array literals and the || and ?: operators). Named types can
    // circularly reference themselves and therefore cannot be subtype reduced during their declaration.
    // For example, "type Item = string | (() => Item" is a named type that circularly references itself.

    /// `(c *Checker) getUnionTypeEx` (checker.go:26162). `alias`/`origin` are
    /// `*TypeAlias`/`*Type` → `Option`.
    pub(crate) fn get_union_type_ex(
        &mut self,
        types: &[TypeId],
        union_reduction: UnionReduction,
        alias: Option<TypeAlias>,
        origin: Option<TypeId>,
    ) -> TypeId {
        if types.is_empty() {
            return self.never_type;
        }
        if types.len() == 1 {
            return types[0];
        }
        // We optimize for the common case of unioning a union type with some other type (such as `undefined`).
        if types.len() == 2
            && origin.is_none()
            && (self.types.get(types[0]).flags.intersects(TypeFlags::UNION)
                || self.types.get(types[1]).flags.intersects(TypeFlags::UNION))
        {
            let mut id1 = types[0];
            let mut id2 = types[1];
            if id1 > id2 {
                std::mem::swap(&mut id1, &mut id2);
            }
            let key = crate::checker_types::UnionOfUnionKey {
                id1,
                id2,
                r: union_reduction,
                a: crate::checker_types::get_alias_key(alias.as_ref()),
            };
            if let Some(&t) = self.union_of_union_types.get(&key) {
                return t;
            }
            let t = self.get_union_type_worker(types, union_reduction, alias, None);
            self.union_of_union_types.insert(key, t);
            return t;
        }
        self.get_union_type_worker(types, union_reduction, alias, origin)
    }

    /// `(c *Checker) getUnionTypeWorker` (checker.go:26187).
    pub(crate) fn get_union_type_worker(
        &mut self,
        types: &[TypeId],
        union_reduction: UnionReduction,
        alias: Option<TypeAlias>,
        origin: Option<TypeId>,
    ) -> TypeId {
        let (mut type_set, includes) = self.add_types_to_union(types);
        if union_reduction != UnionReduction::None {
            if includes.intersects(TypeFlags::ANY_OR_UNKNOWN) {
                if includes.intersects(TypeFlags::ANY) {
                    if includes.intersects(TypeFlags::INCLUDES_WILDCARD) {
                        return self.wildcard_type;
                    }
                    if includes.intersects(TypeFlags::INCLUDES_ERROR) {
                        return self.error_type;
                    }
                    return self.any_type;
                }
                return self.unknown_type;
            }
            if includes.intersects(TypeFlags::UNDEFINED) {
                // If type set contains both undefinedType and missingType, remove missingType
                if type_set.len() >= 2
                    && type_set[0] == self.undefined_type
                    && type_set[1] == self.missing_type
                {
                    type_set.remove(1);
                }
            }
            if includes.intersects(
                TypeFlags::ENUM
                    | TypeFlags::LITERAL
                    | TypeFlags::UNIQUE_ES_SYMBOL
                    | TypeFlags::TEMPLATE_LITERAL
                    | TypeFlags::STRING_MAPPING,
            ) || includes.intersects(TypeFlags::VOID)
                && includes.intersects(TypeFlags::UNDEFINED)
            {
                type_set = self.remove_redundant_literal_types(
                    &type_set,
                    includes,
                    union_reduction == UnionReduction::Subtype,
                );
            }
            if includes.intersects(TypeFlags::STRING_LITERAL)
                && includes
                    .intersects(TypeFlags::TEMPLATE_LITERAL | TypeFlags::STRING_MAPPING)
            {
                type_set = self.remove_string_literals_matched_by_template_literals(&type_set);
            }
            if includes.intersects(TypeFlags::INCLUDES_CONSTRAINED_TYPE_VARIABLE) {
                type_set = self.remove_constrained_type_variables(&type_set);
            }
            if union_reduction == UnionReduction::Subtype {
                let reduced =
                    self.remove_subtypes(&type_set, includes.intersects(TypeFlags::OBJECT));
                let Some(reduced) = reduced else {
                    return self.error_type;
                };
                type_set = reduced;
            }
            if type_set.is_empty() {
                if includes.intersects(TypeFlags::NULL) {
                    if includes.intersects(TypeFlags::INCLUDES_NON_WIDENING_TYPE) {
                        return self.null_type;
                    }
                    return self.null_widening_type;
                }
                if includes.intersects(TypeFlags::UNDEFINED) {
                    if includes.intersects(TypeFlags::INCLUDES_NON_WIDENING_TYPE) {
                        return self.undefined_type;
                    }
                    return self.undefined_widening_type;
                }
                return self.never_type;
            }
        }
        let mut origin = origin;
        if origin.is_none() && includes.intersects(TypeFlags::UNION) {
            let named_unions = self.add_named_unions(Vec::new(), types);
            let mut reduced_types: Vec<TypeId> = Vec::new();
            for &t in &type_set {
                let contained = named_unions.iter().any(|&u| {
                    let u_types = self.types.get(u).types();
                    contains_type(&self.types, u_types, t)
                });
                if !contained {
                    reduced_types.push(t);
                }
            }
            if alias.is_none() && named_unions.len() == 1 && reduced_types.is_empty() {
                return named_unions[0];
            }
            // We create a denormalized origin type only when the union was created from one or more named unions
            // (unions with alias symbols or origins) and when there is no overlap between those named unions.
            let mut named_types_count = 0;
            for &u in &named_unions {
                named_types_count += self.types.get(u).types().len();
            }
            if named_types_count + reduced_types.len() == type_set.len() {
                for &t in &named_unions {
                    insert_type(&self.types, &mut reduced_types, t);
                }
                origin = Some(self.new_union_type(ObjectFlags::NONE, reduced_types));
            }
        }
        let object_flags = if includes.intersects(TypeFlags::NOT_PRIMITIVE_UNION) {
            ObjectFlags::NONE
        } else {
            ObjectFlags::PRIMITIVE_UNION
        } | if includes.intersects(TypeFlags::INTERSECTION) {
            ObjectFlags::CONTAINS_INTERSECTIONS
        } else {
            ObjectFlags::NONE
        };
        self.get_union_type_from_sorted_list(&type_set, object_flags, alias, origin)
    }

    /// This function assumes the constituent type list is sorted and deduplicated.
    ///
    /// `(c *Checker) getUnionTypeFromSortedList` (checker.go:26270).
    pub(crate) fn get_union_type_from_sorted_list(
        &mut self,
        types: &[TypeId],
        precomputed_object_flags: ObjectFlags,
        alias: Option<TypeAlias>,
        origin: Option<TypeId>,
    ) -> TypeId {
        if types.is_empty() {
            return self.never_type;
        }
        if types.len() == 1 {
            return types[0];
        }
        let key =
            crate::checker_types::get_union_key(&self.types, types, origin, alias.as_ref());
        if let Some(&t) = self.union_types.get(&key) {
            return t;
        }
        let propagating =
            self.get_propagating_flags_of_types(types, TypeFlags::NULLABLE);
        let t = self.new_union_type(
            precomputed_object_flags | propagating,
            types.to_vec(),
        );
        {
            let mut g = self.types.get_mut(t);
            as_union_type_mut(&mut g).origin = origin;
        }
        self.types.get_mut(t).alias = alias.clone();
        if types.len() == 2
            && self
                .types
                .get(types[0])
                .flags
                .intersects(TypeFlags::BOOLEAN_LITERAL)
            && self
                .types
                .get(types[1])
                .flags
                .intersects(TypeFlags::BOOLEAN_LITERAL)
        {
            self.types.get_mut(t).flags |= TypeFlags::BOOLEAN;
        }
        self.union_types.insert(key, t);
        t
    }

    /// `(c *Checker) UnionTypes` (checker.go:26291) — Go returns
    /// `iter.Seq[*Type]` over `c.unionTypes` values; the port returns a
    /// collecting `Vec` snapshot so the arena isn't borrowed by callers.
    pub(crate) fn union_types_iter(&self) -> Vec<TypeId> {
        self.union_types.values().copied().collect()
    }

    /// `(c *Checker) addTypesToUnion` (checker.go:26295). Go returns
    /// `([]*Type, TypeFlags)` — the set is sorted+deduplicated by type id
    /// ordering (`CompareTypes`).
    pub(crate) fn add_types_to_union(&mut self, source_types: &[TypeId]) -> (Vec<TypeId>, TypeFlags) {
        let mut types: Vec<TypeId> = Vec::with_capacity(source_types.len());
        let mut includes = TypeFlags::NONE;
        // `addType` closure.
        macro_rules! add_type {
            ($t:expr) => {{
                let t: TypeId = $t;
                let ty = self.types.get(t);
                let flags = ty.flags;
                let object_flags = ty.object_flags;
                let is_wildcard = t == self.wildcard_type;
                drop(ty);
                // We ignore 'never' types in unions
                if !flags.intersects(TypeFlags::NEVER) {
                    includes |= flags & TypeFlags::INCLUDES_MASK;
                    if flags.intersects(TypeFlags::INSTANTIABLE) {
                        includes |= TypeFlags::INCLUDES_INSTANTIABLE;
                    }
                    if flags.intersects(TypeFlags::INTERSECTION)
                        && object_flags.intersects(ObjectFlags::IS_CONSTRAINED_TYPE_VARIABLE)
                    {
                        includes |= TypeFlags::INCLUDES_CONSTRAINED_TYPE_VARIABLE;
                    }
                    if is_wildcard {
                        includes |= TypeFlags::INCLUDES_WILDCARD;
                    }
                    if self.is_error_type(t) {
                        includes |= TypeFlags::INCLUDES_ERROR;
                    }
                    if !self.strict_null_checks && flags.intersects(TypeFlags::NULLABLE) {
                        if !object_flags.intersects(ObjectFlags::CONTAINS_WIDENING_TYPE) {
                            includes |= TypeFlags::INCLUDES_NON_WIDENING_TYPE;
                        }
                    } else {
                        types.push(t);
                    }
                }
            }};
        }
        let mut last_type: Option<TypeId> = None;
        for &t in source_types {
            if Some(t) != last_type {
                if self.types.get(t).flags.intersects(TypeFlags::UNION) {
                    let (t_alias, u_origin, u_types) = {
                        let g = self.types.get(t);
                        let u = g.as_union_type();
                        (g.alias.is_some(), u.origin, u.union_or_intersection.types.clone())
                    };
                    if t_alias || u_origin.is_some() {
                        includes |= TypeFlags::UNION;
                    }
                    for s in u_types {
                        add_type!(s);
                    }
                } else {
                    add_type!(t);
                }
                last_type = Some(t);
            }
        }
        if types.len() >= 2 {
            // Sort and deduplicate types
            let types_arena = &self.types;
            types.sort_by(|&a, &b| {
                crate::utilities::compare_types(types_arena, a, b).cmp(&0)
            });
            let mut unique = 1;
            for i in 1..types.len() {
                let t = types[i];
                if t != types[unique - 1] {
                    types[unique] = t;
                    unique += 1;
                }
            }
            types.truncate(unique);
        }
        (types, includes)
    }

    /// `(c *Checker) addNamedUnions` (checker.go:26358).
    pub(crate) fn add_named_unions(
        &mut self,
        mut named_unions: Vec<TypeId>,
        types: &[TypeId],
    ) -> Vec<TypeId> {
        for &t in types {
            if self.types.get(t).flags.intersects(TypeFlags::UNION) {
                let (t_alias, u_origin, origin_is_union) = {
                    let g = self.types.get(t);
                    let u = g.as_union_type();
                    (
                        g.alias.is_some(),
                        u.origin,
                        u.origin.is_some_and(|o| {
                            self.types.get(o).flags.intersects(TypeFlags::UNION)
                        }),
                    )
                };
                if t_alias || u_origin.is_some() && !origin_is_union {
                    named_unions = core::append_if_unique(&named_unions, t).into_owned();
                } else if u_origin.is_some() && origin_is_union {
                    let origin_types = self.types.get(u_origin.unwrap()).types().to_vec();
                    named_unions = self.add_named_unions(named_unions, &origin_types);
                }
            }
        }
        named_unions
    }

    /// `(c *Checker) removeRedundantLiteralTypes` (checker.go:26372).
    pub(crate) fn remove_redundant_literal_types(
        &mut self,
        types: &[TypeId],
        includes: TypeFlags,
        reduce_void_undefined: bool,
    ) -> Vec<TypeId> {
        let mut types = types.to_vec();
        let mut i = types.len();
        while i > 0 {
            i -= 1;
            let t = types[i];
            let flags = self.types.get(t).flags;
            let regular_type = self.types.get(t).as_literal_type().regular_type;
            let is_fresh = is_fresh_literal_type(&self.types, t);
            let remove = flags.intersects(
                TypeFlags::STRING_LITERAL
                    | TypeFlags::TEMPLATE_LITERAL
                    | TypeFlags::STRING_MAPPING,
            ) && includes.intersects(TypeFlags::STRING)
                || flags.intersects(TypeFlags::NUMBER_LITERAL)
                    && includes.intersects(TypeFlags::NUMBER)
                || flags.intersects(TypeFlags::BIG_INT_LITERAL)
                    && includes.intersects(TypeFlags::BIG_INT)
                || flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL)
                    && includes.intersects(TypeFlags::ES_SYMBOL)
                || reduce_void_undefined
                    && flags.intersects(TypeFlags::UNDEFINED)
                    && includes.intersects(TypeFlags::VOID)
                || is_fresh
                    && regular_type.is_some_and(|r| contains_type(&self.types, &types, r));
            if remove {
                types.remove(i);
            }
        }
        types
    }

    /// `(c *Checker) removeStringLiteralsMatchedByTemplateLiterals` (checker.go:26391).
    pub(crate) fn remove_string_literals_matched_by_template_literals(
        &mut self,
        types: &[TypeId],
    ) -> Vec<TypeId> {
        let templates: Vec<TypeId> = types
            .iter()
            .copied()
            .filter(|&t| self.is_pattern_literal_type(t))
            .collect();
        let mut types = types.to_vec();
        if !templates.is_empty() {
            let mut i = types.len();
            while i > 0 {
                i -= 1;
                let t = types[i];
                if self.types.get(t).flags.intersects(TypeFlags::STRING_LITERAL)
                    && templates.iter().any(|&template| {
                        self.is_type_matched_by_template_literal_or_string_mapping(t, template)
                    })
                {
                    types.remove(i);
                }
            }
        }
        types
    }

    /// `(c *Checker) isTypeMatchedByTemplateLiteralOrStringMapping` (checker.go:26408).
    pub(crate) fn is_type_matched_by_template_literal_or_string_mapping(
        &mut self,
        t: TypeId,
        template: TypeId,
    ) -> bool {
        if self
            .types
            .get(template)
            .flags
            .intersects(TypeFlags::TEMPLATE_LITERAL)
        {
            return self.is_type_matched_by_template_literal_type(
                t,
                template,
                None,
                crate::relater::Comparer::Assignable,
            );
        }
        self.is_member_of_string_mapping(t, template)
    }
}

impl Checker {
    /// `(c *Checker) removeConstrainedTypeVariables` (checker.go:26415).
    pub(crate) fn remove_constrained_type_variables(&mut self, types: &[TypeId]) -> Vec<TypeId> {
        let mut type_variables: Vec<TypeId> = Vec::new();
        let mut types = types.to_vec();
        // First collect a list of the type variables occurring in constraining intersections.
        for &t in &types {
            let ty = self.types.get(t);
            if ty.flags.intersects(TypeFlags::INTERSECTION)
                && ty.object_flags.intersects(ObjectFlags::IS_CONSTRAINED_TYPE_VARIABLE)
            {
                let it = ty.as_intersection_type().union_or_intersection.types.clone();
                drop(ty);
                let index = if !self
                    .types
                    .get(it[0])
                    .flags
                    .intersects(TypeFlags::TYPE_VARIABLE)
                {
                    1
                } else {
                    0
                };
                type_variables =
                    core::append_if_unique(&type_variables, it[index]).into_owned();
            }
        }
        // For each type variable, check if the constraining intersections for that type variable fully
        // cover the constraint of the type variable; if so, remove the constraining intersections and
        // substitute the type variable.
        for type_variable in type_variables {
            let mut primitives: Vec<TypeId> = Vec::new();
            // First collect the primitive types from the constraining intersections.
            for &t in &types {
                let ty = self.types.get(t);
                if ty.flags.intersects(TypeFlags::INTERSECTION)
                    && ty.object_flags.intersects(ObjectFlags::IS_CONSTRAINED_TYPE_VARIABLE)
                {
                    let it = ty.as_intersection_type().union_or_intersection.types.clone();
                    drop(ty);
                    let index = if !self
                        .types
                        .get(it[0])
                        .flags
                        .intersects(TypeFlags::TYPE_VARIABLE)
                    {
                        1
                    } else {
                        0
                    };
                    if it[index] == type_variable {
                        insert_type(&self.types, &mut primitives, it[1 - index]);
                    }
                }
            }
            // If every constituent in the type variable's constraint is covered by an intersection of the type
            // variable and that constituent, remove those intersections and substitute the type variable.
            let constraint = self.get_base_constraint_of_type(type_variable);
            if let Some(constraint) = constraint {
                if every_type(self, constraint, |_c, t| contains_type(&self.types, &primitives, t)) {
                    let mut i = types.len();
                    while i > 0 {
                        i -= 1;
                        let t = types[i];
                        let ty = self.types.get(t);
                        if ty.flags.intersects(TypeFlags::INTERSECTION)
                            && ty.object_flags.intersects(ObjectFlags::IS_CONSTRAINED_TYPE_VARIABLE)
                        {
                            let it =
                                ty.as_intersection_type().union_or_intersection.types.clone();
                            drop(ty);
                            let index = if !self
                                .types
                                .get(it[0])
                                .flags
                                .intersects(TypeFlags::TYPE_VARIABLE)
                            {
                                1
                            } else {
                                0
                            };
                            if it[index] == type_variable
                                && contains_type(&self.types, &primitives, it[1 - index])
                            {
                                types.remove(i);
                            }
                        }
                    }
                    insert_type(&self.types, &mut types, type_variable);
                }
            }
        }
        types
    }

    /// `(c *Checker) removeSubtypes` (checker.go:26468). `None` models the Go
    /// nil return (union too complex).
    pub(crate) fn remove_subtypes(
        &mut self,
        types: &[TypeId],
        has_object_types: bool,
    ) -> Option<Vec<TypeId>> {
        // [] and [T] immediately reduce to [] and [T] respectively
        if types.len() < 2 {
            return Some(types.to_vec());
        }
        let key = crate::checker_types::get_type_list_key(types);
        if let Some(cached) = self.subtype_reduction_cache.get(&key) {
            return Some(cached.clone());
        }
        // We assume that redundant primitive types have already been removed from the types array and that there
        // are no any and unknown types in the array. Thus, the only possible supertypes for primitive types are empty
        // object types, and if none of those are present we can exclude primitive types from the subtype check.
        let has_empty_object = has_object_types && {
            let mut found = false;
            for &t in types {
                if self.types.get(t).flags.intersects(TypeFlags::OBJECT)
                    && !self.is_generic_mapped_type(t)
                {
                    let resolved = self.resolve_structured_type_members(t);
                    if self.is_empty_resolved_type(resolved) {
                        found = true;
                        break;
                    }
                }
            }
            found
        };
        let length = types.len();
        let mut i = length;
        let mut count = 0usize;
        let mut types = types.to_vec();
        while i > 0 {
            i -= 1;
            let source = types[i];
            let source_flags = self.types.get(source).flags;
            if has_empty_object
                || source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
            {
                // A type parameter with a union constraint may be a subtype of some union, but not a subtype of the
                // individual constituents of that union. For example, `T extends A | B` is a subtype of `A | B`, but not
                // a subtype of just `A` or just `B`. When we encounter such a type parameter, we therefore check if the
                // type parameter is a subtype of a union of all the other types.
                if source_flags.intersects(TypeFlags::TYPE_PARAMETER)
                    && self
                        .types
                        .get(self.get_base_constraint_or_type(source).unwrap_or(TypeId::NONE))
                        .flags
                        .intersects(TypeFlags::UNION)
                {
                    let union_of_others: Vec<TypeId> = types
                        .iter()
                        .map(|&t| if t == source { self.never_type } else { t })
                        .collect();
                    let relation = self.strict_subtype_relation.clone();
                    if self.is_type_related_to(
                        source,
                        self.get_union_type(&union_of_others),
                        &relation,
                    ) {
                        types.remove(i);
                    }
                    continue;
                }
                // Find the first property with a unit type, if any. When constituents have a property by the same name
                // but of a different unit type, we can quickly disqualify them from subtype checks. This helps subtype
                // reduction of large discriminated union types.
                let mut key_property: Option<SymbolId> = None;
                let mut key_property_type: Option<TypeId> = None;
                if source_flags.intersects(
                    TypeFlags::OBJECT
                        | TypeFlags::INTERSECTION
                        | TypeFlags::INSTANTIABLE_NON_PRIMITIVE,
                ) {
                    let props = self.get_properties_of_type(source);
                    key_property = props.iter().copied().find(|&p| {
                        let t = self.get_type_of_symbol(p);
                        is_unit_type(&self.types, t)
                    });
                }
                if let Some(key_property) = key_property {
                    key_property_type = Some(
                        self.get_regular_type_of_literal_type(
                            self.get_type_of_symbol(key_property),
                        ),
                    );
                }
                let mut j = 0;
                while j < types.len() {
                    let target = types[j];
                    j += 1;
                    if source != target {
                        if count == 100000 {
                            // After 100000 subtype checks we estimate the remaining amount of work by assuming the
                            // same ratio of checks per element. If the estimated number of remaining type checks is
                            // greater than 1M we deem the union type too complex to represent. This for example
                            // caps union types at 1000 unique object types.
                            let estimated_count = (count / (length - i)) * length;
                            if estimated_count > 1000000 {
                                if let Some(tr) = &self.tracer {
                                    tr.instant(
                                        tsc_tracing::PHASE_CHECK_TYPES,
                                        "removeSubtypes_DepthLimit",
                                        &tsc_tracing::trace_args(&[(
                                            "estimatedCount",
                                            (estimated_count as i64).into(),
                                        )]),
                                    );
                                }
                                self.error(
                                    self.current_node,
                                    &tsc_diagnostics::Expression_produces_a_union_type_that_is_too_complex_to_represent,
                                    &[],
                                );
                                return None;
                            }
                        }
                        count += 1;
                        let target_flags = self.types.get(target).flags;
                        if key_property.is_some()
                            && target_flags.intersects(
                                TypeFlags::OBJECT
                                    | TypeFlags::INTERSECTION
                                    | TypeFlags::INSTANTIABLE_NON_PRIMITIVE,
                            )
                        {
                            let name = self.sym_name(key_property.unwrap());
                            if let Some(t) = self.get_type_of_property_of_type(target, &name)
                            {
                                if is_unit_type(&self.types, t)
                                    && Some(self.get_regular_type_of_literal_type(t))
                                        != key_property_type
                                {
                                    continue;
                                }
                            }
                        }
                        if (source == self.empty_object_type
                            || source == self.unknown_empty_object_type)
                            && self.types.get(target).symbol.is_some()
                            && self.is_empty_anonymous_object_type(target)
                        {
                            continue;
                        }
                        let relation = self.strict_subtype_relation.clone();
                        if self.is_type_related_to(source, target, &relation)
                            && (!self
                                .types
                                .get(self.get_target_type(source))
                                .object_flags
                                .intersects(ObjectFlags::CLASS)
                                || !self
                                    .types
                                    .get(self.get_target_type(target))
                                    .object_flags
                                    .intersects(ObjectFlags::CLASS)
                                || self.is_type_derived_from(source, target))
                        {
                            types.remove(i);
                            break;
                        }
                    }
                }
            }
        }
        self.subtype_reduction_cache.insert(key, types.clone());
        Some(types)
    }

    /// `(c *Checker) intersectTypes` (checker.go:26558).
    pub(crate) fn intersect_types(
        &mut self,
        type1: Option<TypeId>,
        type2: Option<TypeId>,
    ) -> Option<TypeId> {
        match (type1, type2) {
            (None, _) => type2,
            (_, None) => type1,
            (Some(t1), Some(t2)) => Some(self.get_intersection_type(&[t1, t2])),
        }
    }

    /// `(c *Checker) getIntersectionType` (checker.go:26586).
    pub(crate) fn get_intersection_type(&mut self, types: &[TypeId]) -> TypeId {
        self.get_intersection_type_ex(types, IntersectionFlags::NONE, None)
    }

    /// `(c *Checker) getIntersectionTypeEx` (checker.go:26590).
    pub(crate) fn get_intersection_type_ex(
        &mut self,
        types: &[TypeId],
        flags: IntersectionFlags,
        alias: Option<TypeAlias>,
    ) -> TypeId {
        let mut ordered_types = OrderedSet::with_size_hint(types.len());
        let includes = self.add_types_to_intersection(&mut ordered_types, TypeFlags::NONE, types);
        let mut type_set: Vec<TypeId> = ordered_types.values().copied().collect();
        let mut object_flags = ObjectFlags::NONE;
        // An intersection type is considered empty if it contains
        // the type never, or
        // more than one unit type or,
        // an object type and a nullable type (null or undefined), or
        // a string-like type and a type known to be non-string-like, or
        // a number-like type and a type known to be non-number-like, or
        // a symbol-like type and a type known to be non-symbol-like, or
        // a void-like type and a type known to be non-void-like, or
        // a non-primitive type and a type known to be primitive.
        if includes.intersects(TypeFlags::NEVER) {
            if type_set.contains(&self.silent_never_type) {
                return self.silent_never_type;
            }
            return self.never_type;
        }
        if self.strict_null_checks
            && includes.intersects(TypeFlags::NULLABLE)
            && includes.intersects(
                TypeFlags::OBJECT
                    | TypeFlags::NON_PRIMITIVE
                    | TypeFlags::INCLUDES_EMPTY_OBJECT,
            )
            || includes.intersects(TypeFlags::NON_PRIMITIVE)
                && includes
                    .intersects(TypeFlags::DISJOINT_DOMAINS.without(TypeFlags::NON_PRIMITIVE))
            || includes.intersects(TypeFlags::STRING_LIKE)
                && includes
                    .intersects(TypeFlags::DISJOINT_DOMAINS.without(TypeFlags::STRING_LIKE))
            || includes.intersects(TypeFlags::NUMBER_LIKE)
                && includes
                    .intersects(TypeFlags::DISJOINT_DOMAINS.without(TypeFlags::NUMBER_LIKE))
            || includes.intersects(TypeFlags::BIG_INT_LIKE)
                && includes
                    .intersects(TypeFlags::DISJOINT_DOMAINS.without(TypeFlags::BIG_INT_LIKE))
            || includes.intersects(TypeFlags::ES_SYMBOL_LIKE)
                && includes
                    .intersects(TypeFlags::DISJOINT_DOMAINS.without(TypeFlags::ES_SYMBOL_LIKE))
            || includes.intersects(TypeFlags::VOID_LIKE)
                && includes
                    .intersects(TypeFlags::DISJOINT_DOMAINS.without(TypeFlags::VOID_LIKE))
        {
            return self.never_type;
        }
        if includes.intersects(TypeFlags::TEMPLATE_LITERAL | TypeFlags::STRING_MAPPING)
            && includes.intersects(TypeFlags::STRING_LITERAL)
        {
            let (ts, is_empty_set) = self.extract_redundant_template_literals(type_set);
            type_set = ts;
            if is_empty_set {
                return self.never_type;
            }
        }
        if includes.intersects(TypeFlags::ANY) {
            if includes.intersects(TypeFlags::INCLUDES_WILDCARD) {
                return self.wildcard_type;
            }
            if includes.intersects(TypeFlags::INCLUDES_ERROR) {
                return self.error_type;
            }
            return self.any_type;
        }
        if !self.strict_null_checks && includes.intersects(TypeFlags::NULLABLE) {
            if includes.intersects(TypeFlags::INCLUDES_EMPTY_OBJECT) {
                return self.never_type;
            }
            if includes.intersects(TypeFlags::UNDEFINED) {
                return self.undefined_type;
            }
            return self.null_type;
        }
        if includes.intersects(TypeFlags::STRING)
            && includes.intersects(
                TypeFlags::STRING_LITERAL
                    | TypeFlags::TEMPLATE_LITERAL
                    | TypeFlags::STRING_MAPPING,
            )
            || includes.intersects(TypeFlags::NUMBER)
                && includes.intersects(TypeFlags::NUMBER_LITERAL)
            || includes.intersects(TypeFlags::BIG_INT)
                && includes.intersects(TypeFlags::BIG_INT_LITERAL)
            || includes.intersects(TypeFlags::ES_SYMBOL)
                && includes.intersects(TypeFlags::UNIQUE_ES_SYMBOL)
            || includes.intersects(TypeFlags::VOID) && includes.intersects(TypeFlags::UNDEFINED)
            || includes.intersects(TypeFlags::INCLUDES_EMPTY_OBJECT)
                && includes.intersects(TypeFlags::DEFINITELY_NON_NULLABLE)
        {
            if !flags.intersects(IntersectionFlags::NO_SUPERTYPE_REDUCTION) {
                type_set = self.remove_redundant_supertypes(&type_set, includes);
            }
        }
        if includes.intersects(TypeFlags::INCLUDES_MISSING_TYPE) {
            let pos = type_set.iter().position(|&t| t == self.undefined_type);
            if let Some(pos) = pos {
                type_set[pos] = self.missing_type;
            }
        }
        if type_set.is_empty() {
            return self.unknown_type;
        }
        if type_set.len() == 1 {
            return type_set[0];
        }
        if type_set.len() == 2 && !flags.intersects(IntersectionFlags::NO_CONSTRAINT_REDUCTION) {
            let type_var_index = if !self
                .types
                .get(type_set[0])
                .flags
                .intersects(TypeFlags::TYPE_VARIABLE)
            {
                1
            } else {
                0
            };
            let type_variable = type_set[type_var_index];
            let primitive_type = type_set[1 - type_var_index];
            let type_variable_is_tv = self
                .types
                .get(type_variable)
                .flags
                .intersects(TypeFlags::TYPE_VARIABLE);
            let primitive_flags = self.types.get(primitive_type).flags;
            if type_variable_is_tv
                && (primitive_flags
                    .intersects(TypeFlags::PRIMITIVE | TypeFlags::NON_PRIMITIVE)
                    && !self.is_generic_string_like_type(primitive_type)
                    || includes.intersects(TypeFlags::INCLUDES_EMPTY_OBJECT))
            {
                // We have an intersection T & P or P & T, where T is a type variable and P is a primitive type, the object type, or {}.
                let constraint = self.get_base_constraint_of_type(type_variable);
                // Check that T's constraint is similarly composed of primitive types, the object type, or {}.
                if let Some(constraint) = constraint {
                    if every_type(self, constraint, |c, t| {
                        c.is_primitive_or_object_or_empty_type(t)
                    }) {
                        // If T's constraint is a subtype of P, simply return T. For example, given `T extends "a" | "b"`,
                        // the intersection `T & string` reduces to just T.
                        if self.is_type_strict_subtype_of(constraint, primitive_type) {
                            return type_variable;
                        }
                        let constraint_is_union = self
                            .types
                            .get(constraint)
                            .flags
                            .intersects(TypeFlags::UNION);
                        if !(constraint_is_union
                            && some_type(self, constraint, |c, n| {
                                c.is_type_strict_subtype_of(n, primitive_type)
                            }))
                        {
                            // No constituent of T's constraint is a subtype of P. If P is also not a subtype of T's constraint,
                            // then the constraint and P are unrelated, and the intersection reduces to never. For example, given
                            // `T extends "a" | "b"`, the intersection `T & number` reduces to never.
                            if !self.is_type_strict_subtype_of(primitive_type, constraint) {
                                return self.never_type;
                            }
                        }
                        // Some constituent of T's constraint is a subtype of P, or P is a subtype of T's constraint. Thus,
                        // the intersection further constrains the type variable. For example, given `T extends string | number`,
                        // the intersection `T & "a"` is marked as a constrained type variable. Likewise, given `T extends "a" | 1`,
                        // the intersection `T & number` is marked as a constrained type variable.
                        object_flags = ObjectFlags::IS_CONSTRAINED_TYPE_VARIABLE;
                    }
                }
            }
        }
        let key = crate::checker_types::get_intersection_key(&type_set, flags, alias.as_ref());
        if let Some(&result) = self.intersection_types.get(&key) {
            return result;
        }
        let result: TypeId;
        if includes.intersects(TypeFlags::UNION) {
            let reduced;
            let (ts, r) = self.intersect_unions_of_primitive_types(type_set);
            type_set = ts;
            reduced = r;
            if reduced {
                // When the intersection creates a reduced set (which might mean that *all* union types have
                // disappeared), we restart the operation to get a new set of combined flags. Once we have
                // reduced we'll never reduce again, so this occurs at most once.
                result = self.get_intersection_type_ex(&type_set, flags, alias);
            } else if type_set
                .iter()
                .all(|&t| is_union_with_undefined(&self.types, t))
            {
                let contained_undefined_type = if type_set
                    .iter()
                    .any(|&t| self.contains_missing_type(t))
                {
                    self.missing_type
                } else {
                    self.undefined_type
                };
                self.filter_types(&mut type_set, |t| is_not_undefined_type(&self.types, t));
                let inner = self.get_intersection_type_ex(&type_set, flags, None);
                result = self.get_union_type_ex(
                    &[inner, contained_undefined_type],
                    UnionReduction::Literal,
                    alias.clone(),
                    None, /*origin*/
                );
            } else if type_set
                .iter()
                .all(|&t| is_union_with_null(&self.types, t))
            {
                self.filter_types(&mut type_set, |t| is_not_null_type(&self.types, t));
                let inner = self.get_intersection_type_ex(&type_set, flags, None);
                result = self.get_union_type_ex(
                    &[inner, self.null_type],
                    UnionReduction::Literal,
                    alias.clone(),
                    None, /*origin*/
                );
            } else if type_set.len() >= 3 && types.len() > 2 {
                // When we have three or more constituents, more than two inputs (to head off infinite reexpansion), some of which are unions, we employ a "divide and conquer" strategy
                // where A & B & C & D is processed as (A & B) & (C & D). Since intersections of unions often produce far smaller
                // unions of intersections than the full cartesian product (due to some intersections becoming `never`), this can
                // dramatically reduce the overall work.
                let middle = type_set.len() / 2;
                let first = self.get_intersection_type_ex(&type_set[..middle], flags, None);
                let second = self.get_intersection_type_ex(&type_set[middle..], flags, None);
                result = self.get_intersection_type_ex(&[first, second], flags, alias);
            } else {
                // We are attempting to construct a type of the form X & (A | B) & (C | D). Transform this into a type of
                // the form X & A & C | X & A & D | X & B & C | X & B & D. If the estimated size of the resulting union type
                // exceeds 100000 constituents, report an error.
                if !self.check_cross_product_union(&type_set) {
                    return self.error_type;
                }
                let constituents = self.get_cross_product_intersections(&type_set, flags);
                // We attach a denormalized origin type when at least one constituent of the cross-product union is an
                // intersection (i.e. when the intersection didn't just reduce one or more unions to smaller unions) and
                // the denormalized origin has fewer constituents than the union itself.
                let mut origin: Option<TypeId> = None;
                if constituents
                    .iter()
                    .any(|&t| is_intersection_type(&self.types, t))
                    && get_constituent_count_of_types(&self.types, &constituents)
                        > get_constituent_count_of_types(&self.types, &type_set)
                {
                    origin = Some(self.new_intersection_type(ObjectFlags::NONE, type_set.clone()));
                }
                result = self.get_union_type_ex(
                    &constituents,
                    UnionReduction::Literal,
                    alias.clone(),
                    origin,
                );
            }
        } else {
            let propagating =
                self.get_propagating_flags_of_types(types, TypeFlags::NULLABLE);
            result =
                self.new_intersection_type(object_flags | propagating, type_set.clone());
            self.types.get_mut(result).alias = alias.clone();
        }
        self.intersection_types.insert(key, result);
        result
    }

    // Add the given types to the given type set. Order is preserved, freshness is removed from literal
    // types, duplicates are removed, and nested types of the given kind are flattened into the set.

    /// `(c *Checker) addTypesToIntersection` (checker.go:26785).
    pub(crate) fn add_types_to_intersection(
        &mut self,
        type_set: &mut OrderedSet<TypeId>,
        mut includes: TypeFlags,
        types: &[TypeId],
    ) -> TypeFlags {
        for &t in types {
            let regular = self.get_regular_type_of_literal_type(t);
            includes = self.add_type_to_intersection(type_set, includes, regular);
        }
        includes
    }

    /// `(c *Checker) addTypeToIntersection` (checker.go:26792).
    pub(crate) fn add_type_to_intersection(
        &mut self,
        type_set: &mut OrderedSet<TypeId>,
        mut includes: TypeFlags,
        mut t: TypeId,
    ) -> TypeFlags {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::INTERSECTION) {
            let types = self.types.get(t).types().to_vec();
            return self.add_types_to_intersection(type_set, includes, &types);
        }
        if self.is_empty_anonymous_object_type(t) {
            if !includes.intersects(TypeFlags::INCLUDES_EMPTY_OBJECT) {
                includes |= TypeFlags::INCLUDES_EMPTY_OBJECT;
                type_set.add(t);
            }
        } else {
            if flags.intersects(TypeFlags::ANY_OR_UNKNOWN) {
                if t == self.wildcard_type {
                    includes |= TypeFlags::INCLUDES_WILDCARD;
                }
                if self.is_error_type(t) {
                    includes |= TypeFlags::INCLUDES_ERROR;
                }
            } else if self.strict_null_checks || !flags.intersects(TypeFlags::NULLABLE) {
                if t == self.missing_type {
                    includes |= TypeFlags::INCLUDES_MISSING_TYPE;
                    t = self.undefined_type;
                }
                if !type_set.has(&t) {
                    if self.types.get(t).flags.intersects(TypeFlags::UNIT)
                        && includes.intersects(TypeFlags::UNIT)
                    {
                        // We have seen two distinct unit types which means we should reduce to an
                        // empty intersection. Adding TypeFlags.NonPrimitive causes that to happen.
                        includes |= TypeFlags::NON_PRIMITIVE;
                    }
                    type_set.add(t);
                }
            }
            includes |= flags & TypeFlags::INCLUDES_MASK;
        }
        includes
    }

    /// `(c *Checker) removeRedundantSupertypes` (checker.go:26829).
    pub(crate) fn remove_redundant_supertypes(
        &mut self,
        types: &[TypeId],
        includes: TypeFlags,
    ) -> Vec<TypeId> {
        let mut types = types.to_vec();
        let mut i = types.len();
        while i > 0 {
            i -= 1;
            let t = types[i];
            let flags = self.types.get(t).flags;
            let remove = flags.intersects(TypeFlags::STRING)
                && includes.intersects(
                    TypeFlags::STRING_LITERAL
                        | TypeFlags::TEMPLATE_LITERAL
                        | TypeFlags::STRING_MAPPING,
                )
                || flags.intersects(TypeFlags::NUMBER)
                    && includes.intersects(TypeFlags::NUMBER_LITERAL)
                || flags.intersects(TypeFlags::BIG_INT)
                    && includes.intersects(TypeFlags::BIG_INT_LITERAL)
                || flags.intersects(TypeFlags::ES_SYMBOL)
                    && includes.intersects(TypeFlags::UNIQUE_ES_SYMBOL)
                || flags.intersects(TypeFlags::VOID)
                    && includes.intersects(TypeFlags::UNDEFINED)
                || self.is_empty_anonymous_object_type(t)
                    && includes.intersects(TypeFlags::DEFINITELY_NON_NULLABLE);
            if remove {
                types.remove(i);
            }
        }
        types
    }

    /// Returns true if the intersection of the template literals and string literals is the empty set,
    /// for example `get${string}` & "setX", and should reduce to never.
    ///
    /// `(c *Checker) extractRedundantTemplateLiterals` (checker.go:26851).
    pub(crate) fn extract_redundant_template_literals(
        &mut self,
        types: Vec<TypeId>,
    ) -> (Vec<TypeId>, bool) {
        let literals: Vec<TypeId> = types
            .iter()
            .copied()
            .filter(|&t| self.types.get(t).flags.intersects(TypeFlags::STRING_LITERAL))
            .collect();
        let mut types = types;
        let mut i = types.len();
        while i > 0 {
            i -= 1;
            let t = types[i];
            if !self
                .types
                .get(t)
                .flags
                .intersects(TypeFlags::TEMPLATE_LITERAL | TypeFlags::STRING_MAPPING)
            {
                continue;
            }
            for &t2 in &literals {
                if self.is_type_subtype_of(t2, t) {
                    // For example, `get${T}` & "getX" is just "getX", and Lowercase<string> & "foo" is just "foo"
                    types.remove(i);
                    break;
                }
                if self.is_pattern_literal_type(t) {
                    return (types, true);
                }
            }
        }
        (types, false)
    }

    /// If the given list of types contains more than one union of primitive types, replace the
    /// first with a union containing an intersection of those primitive types, then remove the
    /// other unions and return true. Otherwise, do nothing and return false.
    ///
    /// `(c *Checker) intersectUnionsOfPrimitiveTypes` (checker.go:26877).
    pub(crate) fn intersect_unions_of_primitive_types(
        &mut self,
        types: Vec<TypeId>,
    ) -> (Vec<TypeId>, bool) {
        let mut types = types;
        let Some(index) = types
            .iter()
            .position(|&t| is_primitive_union(&self.types, t))
        else {
            return (types, false);
        };
        // Remove all but the first union of primitive types and collect them in
        // the unionTypes array.
        let mut i = index + 1;
        let mut union_types: Vec<TypeId> = vec![types[index]];
        while i < types.len() {
            let t = types[i];
            if self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::PRIMITIVE_UNION)
            {
                union_types.push(t);
                types.remove(i);
            } else {
                i += 1;
            }
        }
        // Return false if there was only one union of primitive types
        if union_types.len() == 1 {
            return (types, false);
        }
        // We have more than one union of primitive types, now intersect them. For each
        // type in each union we check if the type is matched in every union and if so
        // we include it in the result.
        let mut checked: Vec<TypeId> = Vec::new();
        let mut result: Vec<TypeId> = Vec::new();
        for &u in &union_types {
            let u_types = self.types.get(u).types().to_vec();
            for t in u_types {
                if insert_type(&self.types, &mut checked, t) {
                    if self.each_union_contains(&union_types, t) {
                        // undefinedType/missingType are always sorted first so we leverage that here
                        if t == self.undefined_type
                            && !result.is_empty()
                            && result[0] == self.missing_type
                        {
                            continue;
                        }
                        if t == self.missing_type
                            && !result.is_empty()
                            && result[0] == self.undefined_type
                        {
                            result[0] = self.missing_type;
                            continue;
                        }
                        insert_type(&self.types, &mut result, t);
                    }
                }
            }
        }
        // Finally replace the first union with the result
        types[index] = self.get_union_type_from_sorted_list(
            &result,
            ObjectFlags::PRIMITIVE_UNION,
            None, /*alias*/
            None, /*origin*/
        );
        (types, true)
    }

    /// Check that the given type has a match in every union. A given type is matched by
    /// an identical type, and a literal type is additionally matched by its corresponding
    /// primitive type, and missingType is matched by undefinedType (and vice versa).
    ///
    /// `(c *Checker) eachUnionContains` (checker.go:26930).
    pub(crate) fn each_union_contains(&mut self, union_types: &[TypeId], t: TypeId) -> bool {
        for &u in union_types {
            if !self.union_contains_type(u, t, true /*matchSymbol*/) {
                return false;
            }
        }
        true
    }

    /// `(c *Checker) unionContainsType` (checker.go:26939).
    pub(crate) fn union_contains_type(
        &mut self,
        union: TypeId,
        t: TypeId,
        match_symbol: bool,
    ) -> bool {
        let types = self.types.get(union).types().to_vec();
        if contains_type(&self.types, &types, t) {
            return true;
        }
        if t == self.missing_type {
            return contains_type(&self.types, &types, self.undefined_type);
        }
        if t == self.undefined_type {
            return contains_type(&self.types, &types, self.missing_type);
        }
        let t_flags = self.types.get(t).flags;
        let primitive: Option<TypeId> = if t_flags.intersects(TypeFlags::STRING_LITERAL) {
            Some(self.string_type)
        } else if t_flags.intersects(TypeFlags::ENUM | TypeFlags::NUMBER_LITERAL) {
            Some(self.number_type)
        } else if t_flags.intersects(TypeFlags::BIG_INT_LITERAL) {
            Some(self.bigint_type)
        } else if t_flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) && match_symbol {
            Some(self.es_symbol_type)
        } else {
            None
        };
        primitive.is_some_and(|p| contains_type(&self.types, &types, p))
    }

    /// `(c *Checker) getCrossProductIntersections` (checker.go:26964).
    pub(crate) fn get_cross_product_intersections(
        &mut self,
        types: &[TypeId],
        flags: IntersectionFlags,
    ) -> Vec<TypeId> {
        let count = self.get_cross_product_union_size(types);
        let mut intersections: Vec<TypeId> = Vec::new();
        for i in 0..count {
            let mut constituents = types.to_vec();
            let mut n = i;
            for j in (0..types.len()).rev() {
                if self
                    .types
                    .get(types[j])
                    .flags
                    .intersects(TypeFlags::UNION)
                {
                    let source_types = self.types.get(types[j]).types().to_vec();
                    let length = source_types.len();
                    constituents[j] = source_types[n % length];
                    n /= length;
                }
            }
            let t = self.get_intersection_type_ex(&constituents, flags, None);
            if !self.types.get(t).flags.intersects(TypeFlags::NEVER) {
                intersections.push(t);
            }
        }
        intersections
    }

    /// `(c *Checker) filterTypes` (checker.go:27004) — mutates `types` in
    /// place via `filterType`.
    pub(crate) fn filter_types(
        &mut self,
        types: &mut [TypeId],
        predicate: impl Fn(&mut Checker, TypeId) -> bool,
    ) {
        for t in types.iter_mut() {
            *t = self.filter_type(*t, &predicate);
        }
    }

    // `IsEmptyAnonymousObjectType` (checker.go:27010) — checker_core.rs.

    /// `(c *Checker) isEmptyResolvedType` (checker.go:27015). Go takes
    /// `*StructuredType`; the port takes the owning `TypeId` so the
    /// `t.AsType() != c.anyFunctionType` identity check survives the
    /// arena representation.
    pub(crate) fn is_empty_resolved_type(&self, t: TypeId) -> bool {
        if t == self.any_function_type {
            return false;
        }
        let Some(st) = self.types.get(t).as_structured_type() else {
            return false;
        };
        st.properties.is_empty() && st.signatures.is_empty() && st.index_infos.is_empty()
    }
}

/// `isUnionWithUndefined` (checker.go:26759) — package-level.
pub(crate) fn is_union_with_undefined(types: &TypeArena, t: TypeId) -> bool {
    let ty = types.get(t);
    ty.flags.intersects(TypeFlags::UNION)
        && types
            .get(ty.types()[0])
            .flags
            .intersects(TypeFlags::UNDEFINED)
}

/// `isUnionWithNull` (checker.go:26763) — package-level.
pub(crate) fn is_union_with_null(types: &TypeArena, t: TypeId) -> bool {
    let ty = types.get(t);
    ty.flags.intersects(TypeFlags::UNION)
        && (types
            .get(ty.types()[0])
            .flags
            .intersects(TypeFlags::NULL)
            || types
                .get(ty.types()[1])
                .flags
                .intersects(TypeFlags::NULL))
}

/// `isIntersectionType` (checker.go:26767) — package-level.
pub(crate) fn is_intersection_type(types: &TypeArena, t: TypeId) -> bool {
    types.get(t).flags.intersects(TypeFlags::INTERSECTION)
}

/// `isPrimitiveUnion` (checker.go:26771) — package-level.
pub(crate) fn is_primitive_union(types: &TypeArena, t: TypeId) -> bool {
    types
        .get(t)
        .object_flags
        .intersects(ObjectFlags::PRIMITIVE_UNION)
}

/// `isNotUndefinedType` (checker.go:26775) — package-level.
pub(crate) fn is_not_undefined_type(types: &TypeArena, t: TypeId) -> bool {
    !types.get(t).flags.intersects(TypeFlags::UNDEFINED)
}

/// `isNotNullType` (checker.go:26779) — package-level.
pub(crate) fn is_not_null_type(types: &TypeArena, t: TypeId) -> bool {
    !types.get(t).flags.intersects(TypeFlags::NULL)
}

/// `getConstituentCount` (checker.go:26986) — package-level.
pub(crate) fn get_constituent_count(types: &TypeArena, t: TypeId) -> usize {
    let ty = types.get(t);
    if !ty.flags.intersects(TypeFlags::UNION_OR_INTERSECTION) || ty.alias.is_some() {
        return 1;
    }
    if ty.flags.intersects(TypeFlags::UNION) {
        if let Some(origin) = ty.as_union_type().origin {
            return get_constituent_count(types, origin);
        }
    }
    get_constituent_count_of_types(types, ty.types())
}

/// `getConstituentCountOfTypes` (checker.go:26996) — package-level.
pub(crate) fn get_constituent_count_of_types(types: &TypeArena, types_list: &[TypeId]) -> usize {
    let mut n = 0;
    for &t in types_list {
        n += get_constituent_count(types, t);
    }
    n
}

impl Checker {
    /// `(c *Checker) isEmptyObjectType` (checker.go:27019).
    pub(crate) fn is_empty_object_type(&mut self, t: TypeId) -> bool {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::OBJECT) {
            let resolved = self.resolve_structured_type_members(t);
            return !self.is_generic_mapped_type(t) && self.is_empty_resolved_type(resolved);
        }
        if flags.intersects(TypeFlags::NON_PRIMITIVE) {
            return true;
        }
        if flags.intersects(TypeFlags::UNION) {
            let types = self.types.get(t).types().to_vec();
            return core::some(&types, |&t| self.is_empty_object_type(t));
        }
        if flags.intersects(TypeFlags::INTERSECTION) {
            let types = self.types.get(t).types().to_vec();
            return core::every(&types, |&t| self.is_empty_object_type(t));
        }
        false
    }

    /// `(c *Checker) isPatternLiteralPlaceholderType` (checker.go:27033).
    pub(crate) fn is_pattern_literal_placeholder_type(&mut self, t: TypeId) -> bool {
        if self.types.get(t).flags.intersects(TypeFlags::INTERSECTION) {
            // Return true if the intersection consists of one or more placeholders and zero or
            // more object type tags.
            let mut seen_placeholder = false;
            let types = self.types.get(t).types().to_vec();
            for s in types {
                let s_flags = self.types.get(s).flags;
                if s_flags.intersects(TypeFlags::LITERAL | TypeFlags::NULLABLE)
                    || self.is_pattern_literal_placeholder_type(s)
                {
                    seen_placeholder = true;
                } else if !s_flags.intersects(TypeFlags::OBJECT) {
                    return false;
                }
            }
            return seen_placeholder;
        }
        self.types.get(t).flags.intersects(
            TypeFlags::ANY | TypeFlags::STRING | TypeFlags::NUMBER | TypeFlags::BIG_INT,
        ) || self.is_pattern_literal_type(t)
    }

    /// `(c *Checker) isPatternLiteralType` (checker.go:27050).
    pub(crate) fn is_pattern_literal_type(&mut self, t: TypeId) -> bool {
        // A pattern literal type is a template literal or a string mapping type that contains only
        // non-generic pattern literal placeholders.
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            let tl_types = self.types.get(t).as_template_literal_type().types.clone();
            return core::every(&tl_types, |&u| self.is_pattern_literal_placeholder_type(u));
        }
        if flags.intersects(TypeFlags::STRING_MAPPING) {
            let target = self.types.get(t).target().unwrap_or(TypeId::NONE);
            return self.is_pattern_literal_placeholder_type(target);
        }
        false
    }

    /// `(c *Checker) isGenericStringLikeType` (checker.go:27057).
    pub(crate) fn is_generic_string_like_type(&mut self, t: TypeId) -> bool {
        self.types
            .get(t)
            .flags
            .intersects(TypeFlags::TEMPLATE_LITERAL | TypeFlags::STRING_MAPPING)
            && !self.is_pattern_literal_type(t)
    }

    /// `(c *Checker) filterType` (checker.go:27092).
    pub(crate) fn filter_type(
        &mut self,
        t: TypeId,
        f: &(dyn Fn(&mut Checker, TypeId) -> bool),
    ) -> TypeId {
        if self.types.get(t).flags.intersects(TypeFlags::UNION) {
            let types = self.types.get(t).types().to_vec();
            let filtered: Vec<TypeId> = types
                .iter()
                .copied()
                .filter(|&u| f(self, u))
                .collect();
            if core::same(&types, &filtered) {
                return t;
            }
            let (origin, union_object_flags) = {
                let g = self.types.get(t);
                let u = g.as_union_type();
                (u.origin, g.object_flags)
            };
            let mut new_origin: Option<TypeId> = None;
            if let Some(origin) = origin {
                if self
                    .types
                    .get(origin)
                    .flags
                    .intersects(TypeFlags::UNION)
                {
                    // If the origin type is a (denormalized) union type, filter its non-union constituents. If that ends
                    // up removing a smaller number of types than in the normalized constituent set (meaning some of the
                    // filtered types are within nested unions in the origin), then we can't construct a new origin type.
                    // Otherwise, if we have exactly one type left in the origin set, return that as the filtered type.
                    // Otherwise, construct a new filtered origin type.
                    let origin_types = self.types.get(origin).types().to_vec();
                    let origin_filtered: Vec<TypeId> = origin_types
                        .iter()
                        .copied()
                        .filter(|&u| {
                            self.types.get(u).flags.intersects(TypeFlags::UNION) || f(self, u)
                        })
                        .collect();
                    if origin_types.len() - origin_filtered.len() == types.len() - filtered.len() {
                        if origin_filtered.len() == 1 {
                            return origin_filtered[0];
                        }
                        new_origin = Some(self.new_union_type(ObjectFlags::NONE, origin_filtered));
                    }
                }
            }
            // filtering could remove intersections so `ContainsIntersections` might be forwarded "incorrectly"
            // it is purely an optimization hint so there is no harm in accidentally forwarding it
            return self.get_union_type_from_sorted_list(
                &filtered,
                union_object_flags
                    & (ObjectFlags::PRIMITIVE_UNION | ObjectFlags::CONTAINS_INTERSECTIONS),
                None, /*alias*/
                new_origin,
            );
        }
        if self.types.get(t).flags.intersects(TypeFlags::NEVER) || f(self, t) {
            return t;
        }
        self.never_type
    }

    /// `(c *Checker) removeType` (checker.go:27128).
    pub(crate) fn remove_type(&mut self, t: TypeId, target_type: TypeId) -> TypeId {
        if !self.types.get(t).flags.intersects(TypeFlags::UNION) {
            if t == target_type {
                return self.never_type;
            }
            return t;
        }
        let (origin, union_object_flags) = {
            let g = self.types.get(t);
            (g.as_union_type().origin, g.object_flags)
        };
        if let Some(origin) = origin {
            if self.types.get(origin).flags.intersects(TypeFlags::UNION)
                && contains_type(&self.types, self.types.get(origin).types(), target_type)
            {
                return self.filter_type(t, &|_c, t| t != target_type);
            }
        }
        let types = self.types.get(t).types().to_vec();
        let arena = &self.types;
        if let Ok(i) = types.binary_search_by(|&u| {
            crate::utilities::compare_types(arena, u, target_type).cmp(&0)
        }) {
            if types.len() == 2 {
                return types[1 - i];
            }
            // Remove the target type from the slice.
            let mut filtered = types.clone();
            filtered.remove(i);
            return self.get_union_type_from_sorted_list(
                &filtered,
                union_object_flags
                    & (ObjectFlags::PRIMITIVE_UNION | ObjectFlags::CONTAINS_INTERSECTIONS),
                None, /*alias*/
                None, /*origin*/
            );
        }
        t
    }

    /// `(c *Checker) isErrorType` (checker.go:27172).
    pub(crate) fn is_error_type(&self, t: TypeId) -> bool {
        // The only 'any' types that have alias symbols are those manufactured by getTypeFromTypeAliasReference for
        // a reference to an unresolved symbol. We want those to behave like the errorType.
        let ty = self.types.get(t);
        t == self.error_type
            || ty.flags.intersects(TypeFlags::ANY) && ty.alias.is_some()
    }

    /// `(c *Checker) checkCrossProductUnion` (checker.go:27182).
    pub(crate) fn check_cross_product_union(&mut self, types: &[TypeId]) -> bool {
        let size = self.get_cross_product_union_size(types);
        if size >= 100_000 {
            if let Some(tr) = &self.tracer {
                tr.instant(
                    tsc_tracing::PHASE_CHECK_TYPES,
                    "checkCrossProductUnion_DepthLimit",
                    &tsc_tracing::trace_args(&[("size", (size as i64).into())]),
                );
            }
            self.error(
                self.current_node,
                &tsc_diagnostics::Expression_produces_a_union_type_that_is_too_complex_to_represent,
                &[],
            );
            return false;
        }
        true
    }

    /// `(c *Checker) getCrossProductUnionSize` (checker.go:27194).
    pub(crate) fn get_cross_product_union_size(&mut self, types: &[TypeId]) -> usize {
        let mut size: usize = 1;
        for &t in types {
            let flags = self.types.get(t).flags;
            if flags.intersects(TypeFlags::UNION) {
                let n = self.types.get(t).types().len();
                // Cap the result to avoid integer overflow when computing the cross product of many large unions.
                // In TypeScript, number overflow produces Infinity which naturally exceeds the limit check;
                // in Go, we must guard against int wrapping to zero or negative.
                if n > 0 && size > usize::MAX / n {
                    return usize::MAX;
                }
                size *= n;
            } else if flags.intersects(TypeFlags::NEVER) {
                return 0;
            }
        }
        size
    }
}

/// `forEachType` (checker.go:27061) — package-level. `f` gets `&mut Checker`
/// since Go `f` closes over `c` in callers.
pub(crate) fn for_each_type(
    c: &mut Checker,
    types: &TypeArena,
    t: TypeId,
    mut f: impl FnMut(&mut Checker, TypeId),
) {
    if types.get(t).flags.intersects(TypeFlags::UNION) {
        for &u in types.get(t).types() {
            f(c, u);
        }
    } else {
        f(c, t);
    }
}

/// `someType` (checker.go:27071) — package-level.
pub(crate) fn some_type(
    c: &mut Checker,
    t: TypeId,
    mut f: impl FnMut(&mut Checker, TypeId) -> bool,
) -> bool {
    if c.types.get(t).flags.intersects(TypeFlags::UNION) {
        let types = c.types.get(t).types().to_vec();
        return types.iter().any(|&u| f(c, u));
    }
    f(c, t)
}

/// `everyType` (checker.go:27078) — package-level.
pub(crate) fn every_type(
    c: &mut Checker,
    t: TypeId,
    mut f: impl FnMut(&mut Checker, TypeId) -> bool,
) -> bool {
    if c.types.get(t).flags.intersects(TypeFlags::UNION) {
        let types = c.types.get(t).types().to_vec();
        return types.iter().all(|&u| f(c, u));
    }
    f(c, t)
}

/// `everyContainedType` (checker.go:27085) — package-level. PORT: takes the
/// type arena first (the constituents need dereferencing); callers that only
/// hold `&mut Checker` pass `&c.types` — see `has_common_dom_type_name` users.
pub(crate) fn every_contained_type(
    types: &TypeArena,
    t: TypeId,
    mut f: impl FnMut(TypeId) -> bool,
) -> bool {
    let ty = types.get(t);
    if ty.flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
        return ty.types().iter().all(|&u| f(u));
    }
    f(t)
}

/// `containsType` (checker.go:27150) — package-level. Sorted-slice binary
/// search by `CompareTypes` (sort-order flags, then id) — needs the arena.
pub(crate) fn contains_type(arena: &TypeArena, types: &[TypeId], t: TypeId) -> bool {
    types
        .binary_search_by(|&u| crate::utilities::compare_types(arena, u, t).cmp(&0))
        .is_ok()
}

/// `insertType` (checker.go:27155) — package-level. Returns whether the
/// element was inserted (Go returns `(slice, bool)`; the port mutates).
pub(crate) fn insert_type(arena: &TypeArena, types: &mut Vec<TypeId>, t: TypeId) -> bool {
    match types.binary_search_by(|&u| crate::utilities::compare_types(arena, u, t).cmp(&0)) {
        Err(i) => {
            types.insert(i, t);
            true
        }
        Ok(_) => false,
    }
}

/// `countTypes` (checker.go:27162) — package-level.
pub(crate) fn count_types(types: &TypeArena, t: TypeId) -> usize {
    let ty = types.get(t);
    if ty.flags.intersects(TypeFlags::UNION) {
        return ty.types().len();
    }
    if ty.flags.intersects(TypeFlags::NEVER) {
        return 0;
    }
    1
}

/// `compareTypeIds` (checker.go:27178) — package-level.
pub(crate) fn compare_type_ids(t1: TypeId, t2: TypeId) -> i64 {
    t1.0 as i64 - t2.0 as i64
}

impl Checker {
    /// `(c *Checker) getIndexType` (checker.go:27214).
    pub(crate) fn get_index_type(&mut self, t: TypeId) -> TypeId {
        self.get_index_type_ex(t, IndexFlags::NONE)
    }

    /// `(c *Checker) getIndexTypeEx` (checker.go:27218).
    pub(crate) fn get_index_type_ex(&mut self, t: TypeId, index_flags: IndexFlags) -> TypeId {
        let t = self.get_reduced_type(t);
        let t_flags = self.types.get(t).flags;
        let t_object_flags = self.types.get(t).object_flags;
        if self.is_no_infer_type(t) {
            let base_type = self.types.get(t).as_substitution_type().base_type;
            let inner = self.get_index_type_ex(base_type, index_flags);
            return self.get_no_infer_type(inner);
        }
        if self.should_defer_index_type(t, index_flags) {
            return self.get_index_type_for_generic_type(t, index_flags);
        }
        if t_flags.intersects(TypeFlags::UNION) {
            let types = self.types.get(t).types().to_vec();
            let mapped: Vec<TypeId> = types
                .iter()
                .map(|&u| self.get_index_type_ex(u, index_flags))
                .collect();
            return self.get_intersection_type(&mapped);
        }
        if t_flags.intersects(TypeFlags::INTERSECTION) {
            let types = self.types.get(t).types().to_vec();
            let mapped: Vec<TypeId> = types
                .iter()
                .map(|&u| self.get_index_type_ex(u, index_flags))
                .collect();
            return self.get_union_type(&mapped);
        }
        if t_object_flags.intersects(ObjectFlags::MAPPED) {
            return self.get_index_type_for_mapped_type(t, index_flags);
        }
        if t == self.wildcard_type {
            return self.wildcard_type;
        }
        if t_flags.intersects(TypeFlags::UNKNOWN) {
            return self.never_type;
        }
        if t_flags.intersects(TypeFlags::ANY | TypeFlags::NEVER) {
            return self.string_number_symbol_type;
        }
        let include = if index_flags.intersects(IndexFlags::NO_INDEX_SIGNATURES) {
            TypeFlags::STRING_LITERAL
        } else {
            TypeFlags::STRING_LIKE
        } | if index_flags.intersects(IndexFlags::STRINGS_ONLY) {
            TypeFlags::NONE
        } else {
            TypeFlags::NUMBER_LIKE | TypeFlags::ES_SYMBOL_LIKE
        };
        self.get_literal_type_from_properties(t, include, index_flags == IndexFlags::NONE)
    }

    /// `(c *Checker) getExtractStringType` (checker.go:27243).
    pub(crate) fn get_extract_string_type(&mut self, t: TypeId) -> TypeId {
        if let Some(extract_type_alias) = self.get_global_extract_symbol() {
            return self.get_type_alias_instantiation(
                extract_type_alias,
                &[t, self.string_type],
                None,
            );
        }
        self.string_type
    }

    /// `(c *Checker) getLiteralTypeFromProperties` (checker.go:27251).
    pub(crate) fn get_literal_type_from_properties(
        &mut self,
        t: TypeId,
        include: TypeFlags,
        include_origin: bool,
    ) -> TypeId {
        let key = crate::checker_types::PropertiesTypesKey {
            type_id: t,
            include,
            include_origin,
        };
        if let Some(&cached) = self.properties_types.get(&key) {
            return cached;
        }
        let mut origin: Option<TypeId> = None;
        if include_origin
            && self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::CLASS_OR_INTERFACE | ObjectFlags::REFERENCE)
            || self.types.get(t).alias.is_some()
        {
            origin = Some(self.new_index_type(t, IndexFlags::NONE));
        }
        let props = self.get_properties_of_type(t);
        let index_infos = self.get_index_infos_of_type(t);
        let mut types: Vec<TypeId> = Vec::with_capacity(props.len() + index_infos.len());
        for &prop in &props {
            types.push(self.get_literal_type_from_property(prop, include, false));
        }
        for &info in &index_infos {
            let (info_key_type, is_enum_index) = {
                let arena = self.index_info_arena.borrow();
                (
                    arena[info.index()].key_type,
                    info == self.enum_number_index_info,
                )
            };
            if !is_enum_index && self.is_key_type_included(info_key_type, include) {
                if info_key_type == self.string_type
                    && include.intersects(TypeFlags::NUMBER)
                {
                    types.push(self.string_or_number_type);
                } else {
                    types.push(info_key_type);
                }
            }
        }
        let result = self.get_union_type_ex(&types, UnionReduction::Literal, None, origin);
        self.properties_types.insert(key, result);
        result
    }

    /// `(c *Checker) getLiteralTypeFromProperty` (checker.go:27280).
    pub(crate) fn get_literal_type_from_property(
        &mut self,
        prop: SymbolId,
        include: TypeFlags,
        include_non_public: bool,
    ) -> TypeId {
        let modifier_flags = {
            let arena = self.symbol_arena.borrow();
            crate::utilities::get_declaration_modifier_flags_from_symbol(
                &arena[prop.index()],
                &self.program_nodes_for_symbol(prop),
            )
        };
        if include_non_public
            || !modifier_flags
                .intersects(ast::ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER)
        {
            let late_bound = self.get_late_bound_symbol(prop);
            let mut t = self.value_symbol_links.get(late_bound).name_type;
            if t.is_none() {
                if self.sym_name(prop) == ast::INTERNAL_SYMBOL_NAME_DEFAULT {
                    t = Some(self.get_string_literal_type("default"));
                } else {
                    let value_declaration =
                        self.symbol_arena.borrow()[prop.index()].value_declaration;
                    if let Some(vd) = value_declaration {
                        let nodes = self.program_nodes(vd);
                        if let Some(name) = ast::get_name_of_declaration(Some(vd), &nodes) {
                            t = Some(self.get_literal_type_from_property_name(name));
                        }
                    }
                    if t.is_none() && !crate::utilities::is_known_symbol(&mut *self, prop) {
                        let sym_name = {
                            let arena = self.symbol_arena.borrow();
                            ast::symbol::symbol_name(
                                &arena[prop.index()],
                                &self.program_nodes_for_symbol(prop),
                            )
                            .into_owned()
                        };
                        t = Some(self.get_string_literal_type(&sym_name));
                    }
                }
            }
            if let Some(t) = t {
                if self.types.get(t).flags.intersects(include) {
                    return t;
                }
            }
        }
        self.never_type
    }

    /// `(c *Checker) getLiteralTypeFromPropertyName` (checker.go:27303).
    pub(crate) fn get_literal_type_from_property_name(&mut self, name: NodeId) -> TypeId {
        let nodes = self.program_nodes(name);
        if ast::is_private_identifier(&nodes[name]) {
            return self.never_type;
        }
        if ast::is_numeric_literal(&nodes[name]) {
            let checked = self.check_expression(name);
            return self.get_regular_type_of_literal_type(checked);
        }
        if ast::is_computed_property_name(&nodes[name]) {
            let checked = self.check_computed_property_name(name);
            return self.get_regular_type_of_literal_type(checked);
        }
        let property_name = ast::get_property_name_for_property_name_node(name, &nodes);
        if property_name != ast::INTERNAL_SYMBOL_NAME_MISSING {
            return self.get_string_literal_type(&property_name);
        }
        if ast::is_expression(name, &nodes) {
            let checked = self.check_expression(name);
            return self.get_regular_type_of_literal_type(checked);
        }
        self.never_type
    }

    /// `(c *Checker) isKeyTypeIncluded` (checker.go:27323).
    pub(crate) fn is_key_type_included(&mut self, key_type: TypeId, include: TypeFlags) -> bool {
        if self.types.get(key_type).flags.intersects(include) {
            return true;
        }
        if self
            .types
            .get(key_type)
            .flags
            .intersects(TypeFlags::INTERSECTION)
        {
            let types = self.types.get(key_type).types().to_vec();
            return core::some(&types, |&t| self.is_key_type_included(t, include));
        }
        false
    }

    /// `(c *Checker) checkComputedPropertyName` (checker.go:27336).
    pub(crate) fn check_computed_property_name(&mut self, node: NodeId) -> TypeId {
        let links = self.type_node_links.get(node);
        if links.resolved_type.is_none() {
            links.resolved_type = Some(self.circular_constraint_type);
            let nodes = self.program_nodes(node);
            if is_invalid_computed_property_name(&nodes[node], &nodes) {
                links.resolved_type = Some(self.error_type);
                return self.error_type;
            }
            let expr = nodes[node].expression();
            let resolved = self.check_expression(expr.unwrap());
            links.resolved_type = Some(resolved);
            // This will allow types number, string, symbol or any. It will also allow enums, the unknown
            // type, and any union of these types (like string | number).
            if self
                .types
                .get(resolved)
                .flags
                .intersects(TypeFlags::NULLABLE)
                || !self.is_type_assignable_to_kind(
                    resolved,
                    TypeFlags::STRING_LIKE | TypeFlags::NUMBER_LIKE | TypeFlags::ES_SYMBOL_LIKE,
                ) && !self.is_type_assignable_to(resolved, self.string_number_symbol_type)
            {
                self.error(
                    Some(node),
                    &tsc_diagnostics::A_computed_property_name_must_be_of_type_string_number_symbol_or_any,
                    &[],
                );
            }
        }
        self.type_node_links.get(node).resolved_type.unwrap()
    }

    /// `(c *Checker) isNoInferType` (checker.go:27356).
    pub(crate) fn is_no_infer_type(&self, t: TypeId) -> bool {
        // A NoInfer<T> type is represented as a substitution type with a TypeFlags.Unknown constraint.
        let ty = self.types.get(t);
        ty.flags.intersects(TypeFlags::SUBSTITUTION)
            && self
                .types
                .get(ty.as_substitution_type().constraint)
                .flags
                .intersects(TypeFlags::UNKNOWN)
    }

    /// `(c *Checker) getSubstitutionIntersection` (checker.go:27361).
    pub(crate) fn get_substitution_intersection(&mut self, t: TypeId) -> TypeId {
        let (base_type, constraint) = {
            let g = self.types.get(t);
            let d = g.as_substitution_type();
            (d.base_type, d.constraint)
        };
        if self.is_no_infer_type(t) {
            return base_type;
        }
        self.get_intersection_type(&[constraint, base_type])
    }

    /// `(c *Checker) shouldDeferIndexType` (checker.go:27368).
    pub(crate) fn should_defer_index_type(&mut self, t: TypeId, index_flags: IndexFlags) -> bool {
        let flags = self.types.get(t).flags;
        flags.intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE)
            || self.is_generic_tuple_type(t)
            || self.is_generic_mapped_type(t)
                && self.get_name_type_from_mapped_type(t).is_some()
            || flags.intersects(TypeFlags::UNION)
                && !index_flags.intersects(IndexFlags::NO_REDUCIBLE_CHECK)
                && self.is_generic_reducible_type(t)
            || flags.intersects(TypeFlags::INTERSECTION)
                && self.maybe_type_of_kind(t, TypeFlags::INSTANTIABLE)
                && {
                    let types = self.types.get(t).types().to_vec();
                    core::some(&types, |&u| self.is_empty_anonymous_object_type(u))
                }
    }

    /// `(c *Checker) getMappedTypeNameTypeKind` (checker.go:27376).
    pub(crate) fn get_mapped_type_name_type_kind(&mut self, t: TypeId) -> MappedTypeNameTypeKind {
        let Some(name_type) = self.get_name_type_from_mapped_type(t) else {
            return MappedTypeNameTypeKind::NONE;
        };
        let tp = self.get_type_parameter_from_mapped_type(t);
        if self.is_type_assignable_to(name_type, tp.unwrap_or(TypeId::NONE)) {
            return MappedTypeNameTypeKind::FILTERING;
        }
        MappedTypeNameTypeKind::REMAPPING
    }

    /// `(c *Checker) getIndexTypeForGenericType` (checker.go:27387).
    pub(crate) fn get_index_type_for_generic_type(
        &mut self,
        t: TypeId,
        index_flags: IndexFlags,
    ) -> TypeId {
        let key = CachedTypeKey {
            kind: if index_flags.intersects(IndexFlags::STRINGS_ONLY) {
                CachedTypeKind::StringIndexType
            } else {
                CachedTypeKind::IndexType
            },
            type_id: t,
        };
        if let Some(&index_type) = self.cached_types.get(&key) {
            return index_type;
        }
        let index_type = self.new_index_type(t, index_flags & IndexFlags::STRINGS_ONLY);
        self.cached_types.insert(key, index_type);
        index_type
    }

    /// This roughly mirrors `resolveMappedTypeMembers` in the nongeneric case, except only reports a union of the keys calculated,
    /// rather than manufacturing the properties. We can't just fetch the `constraintType` since that would ignore mappings
    /// and mapping the `constraintType` directly ignores how mapped types map _properties_ and not keys (thus ignoring subtype
    /// reduction in the constraintType) when possible.
    /// @param noIndexSignatures Indicates if _string_ index signatures should be elided. (other index signatures are always reported)
    ///
    /// `(c *Checker) getIndexTypeForMappedType` (checker.go:27405).
    pub(crate) fn get_index_type_for_mapped_type(
        &mut self,
        t: TypeId,
        index_flags: IndexFlags,
    ) -> TypeId {
        let type_parameter = self.get_type_parameter_from_mapped_type(t);
        let constraint_type = self.get_constraint_type_from_mapped_type(t);
        let mapped_target = self
            .types
            .get(t)
            .as_mapped_type()
            .target
            .unwrap_or(t);
        let name_type = self.get_name_type_from_mapped_type(mapped_target);
        if name_type.is_none() && !index_flags.intersects(IndexFlags::NO_INDEX_SIGNATURES) {
            // no mapping and no filtering required, just quickly bail to returning the constraint in the common case
            return constraint_type.unwrap_or(TypeId::NONE);
        }
        let t_mapper = self.types.get(t).as_mapped_type().mapper;
        let mut key_types: Vec<TypeId> = Vec::new();
        // `addMemberForKeyType` closure.
        let mut add_member_for_key_type = |c: &mut Checker, key_type: TypeId| {
            let mut prop_name_type = key_type;
            if let Some(name_type) = name_type {
                let m = mapper::append_type_mapping(
                    c,
                    t_mapper,
                    type_parameter.unwrap_or(TypeId::NONE),
                    key_type,
                );
                prop_name_type = c.instantiate_type(name_type, m);
            }
            // `keyof` currently always returns `string | number` for concrete `string` index signatures - the below ternary keeps that behavior for mapped types
            // See `getLiteralTypeFromProperties` where there's a similar ternary to cause the same behavior.
            key_types.push(if prop_name_type == c.string_type {
                c.string_or_number_type
            } else {
                prop_name_type
            });
        };
        let _ = &mut add_member_for_key_type;
        // Calling getApparentType on the `T` of a `keyof T` in the constraint type of a generic mapped type can
        // trigger a circularity. For example, `T extends { [P in keyof T & string as Captitalize<P>]: any }` is
        // a circular definition. For this reason, we only eagerly manifest the keys if the constraint is non-generic.
        let constraint_type = constraint_type.unwrap_or(TypeId::NONE);
        if self.is_generic_index_type(constraint_type) {
            if self.is_mapped_type_with_keyof_constraint_declaration(t) {
                // We have a generic index and a homomorphic mapping and a key remapping - we need to defer
                // the whole `keyof whatever` for later since it's not safe to resolve the shape of modifier type.
                return self.get_index_type_for_generic_type(t, index_flags);
            }
            // Include the generic component in the resulting type.
            for_each_type(self, &self.types.clone(), constraint_type, |c, t| {
                add_member_for_key_type(c, t)
            });
        } else if self.is_mapped_type_with_keyof_constraint_declaration(t) {
            let modifiers_type = self.get_modifiers_type_from_mapped_type(t);
            let modifiers_type = self.get_apparent_type(modifiers_type);
            // The 'T' in 'keyof T'
            self.for_each_mapped_type_property_key_type_and_index_signature_key_type(
                modifiers_type,
                TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE,
                index_flags.intersects(IndexFlags::STRINGS_ONLY),
                &mut add_member_for_key_type,
            );
        } else {
            let lower = self.get_lower_bound_of_key_type(constraint_type);
            for_each_type(self, &self.types.clone(), lower, |c, t| {
                add_member_for_key_type(c, t)
            });
        }
        // We had to pick apart the constraintType to potentially map/filter it - compare the final resulting list with the
        // original constraintType, so we can return the union that preserves aliases/origin data if possible.
        let result = if index_flags.intersects(IndexFlags::NO_INDEX_SIGNATURES) {
            let union = self.get_union_type(&key_types);
            self.filter_type(union, &|c, t| {
                !c.types.get(t).flags.intersects(TypeFlags::ANY | TypeFlags::STRING)
            })
        } else {
            self.get_union_type(&key_types)
        };
        if self.types.get(result).flags.intersects(TypeFlags::UNION)
            && self
                .types
                .get(constraint_type)
                .flags
                .intersects(TypeFlags::UNION)
            && crate::checker_types::get_type_list_key(self.types.get(result).types())
                == crate::checker_types::get_type_list_key(
                    self.types.get(constraint_type).types(),
                )
        {
            return constraint_type;
        }
        result
    }

    /// `(c *Checker) getIndexedAccessType` (checker.go:27457).
    pub(crate) fn get_indexed_access_type(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
    ) -> TypeId {
        self.get_indexed_access_type_ex(object_type, index_type, AccessFlags::NONE, None, None)
    }

    /// `(c *Checker) createDeferredTypeReference` (checker.go:25655).
    /// Go `*TypeMapper` → `Option<TypeMapperId>`; `*TypeAlias` → `Option<TypeAlias>`.
    pub(crate) fn create_deferred_type_reference(
        &mut self,
        target: TypeId,
        node: Option<NodeId>,
        mapper: Option<TypeMapperId>,
        mut alias: Option<TypeAlias>,
    ) -> TypeId {
        if alias.is_none() {
            alias = node.and_then(|n| self.get_alias_for_type_node(n));
            if let (Some(a), Some(mapper)) = (alias.as_mut(), mapper) {
                a.type_arguments = self.instantiate_types(&a.type_arguments, Some(mapper));
            }
        }
        let symbol = self.types.get(target).symbol;
        let t = self.new_object_type(ObjectFlags::REFERENCE, symbol);
        self.types.get_mut(t).alias = alias.clone();
        {
            let d = self.types.get_mut(t).as_type_reference_mut();
            d.target = Some(target);
            d.mapper = mapper;
            d.node = node;
        }
        t
    }

    /// `(c *Checker) getIndexedAccessTypeEx` (checker.go:27461).
    /// Go `(aliasSymbol, aliasTypeArguments)` → `alias: Option<TypeAlias>`.
    pub(crate) fn get_indexed_access_type_ex(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
        access_flags: AccessFlags,
        access_node: Option<NodeId>,
        alias: Option<TypeAlias>,
    ) -> TypeId {
        let result = self.get_indexed_access_type_or_undefined(
            object_type,
            index_type,
            access_flags,
            access_node,
            alias,
        );
        match result {
            Some(result) => result,
            None => {
                if access_node.is_some() {
                    self.error_type
                } else {
                    self.unknown_type
                }
            }
        }
    }

    /// `(c *Checker) getIndexedAccessTypeOrUndefined` (checker.go:27469).
    pub(crate) fn get_indexed_access_type_or_undefined(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
        mut access_flags: AccessFlags,
        access_node: Option<NodeId>,
        alias: Option<TypeAlias>,
    ) -> Option<TypeId> {
        if object_type == self.wildcard_type || index_type == self.wildcard_type {
            return Some(self.wildcard_type);
        }
        let object_type = self.get_reduced_type(object_type);
        let mut index_type = index_type;
        // If the object type has a string index signature and no other members we know that the result will
        // always be the type of that index signature and we can simplify accordingly.
        if self.is_string_index_signature_only_type_worker(object_type)
            && !self.types.get(index_type).flags.intersects(TypeFlags::NULLABLE)
            && self.is_type_assignable_to_kind(
                index_type,
                TypeFlags::STRING | TypeFlags::NUMBER,
            )
        {
            index_type = self.string_type;
        }
        // In noUncheckedIndexedAccess mode, indexed access operations that occur in an expression in a read position and resolve to
        // an index signature have 'undefined' included in their type.
        if self.compiler_options.no_unchecked_indexed_access == tsc_core::tristate::TS_TRUE
            && access_flags.intersects(AccessFlags::EXPRESSION_POSITION)
        {
            access_flags |= AccessFlags::INCLUDE_UNDEFINED;
        }
        // If the index type is generic, or if the object type is generic and doesn't originate in an expression and
        // the operation isn't exclusively indexing the fixed (non-variadic) portion of a tuple type, we are performing
        // a higher-order index access where we cannot meaningfully access the properties of the object type. Note that
        // for a generic T and a non-generic K, we eagerly resolve T[K] if it originates in an expression. This is to
        // preserve backwards compatibility. For example, an element access 'this["foo"]' has always been resolved
        // eagerly using the constraint type of 'this' at the given location.
        if self.should_defer_indexed_access_type(object_type, index_type, access_node) {
            if self
                .types
                .get(object_type)
                .flags
                .intersects(TypeFlags::ANY_OR_UNKNOWN)
            {
                return Some(object_type);
            }
            // Defer the operation by creating an indexed access type.
            let persistent_access_flags = access_flags & AccessFlags::PERSISTENT;
            let key = get_indexed_access_key(
                object_type,
                index_type,
                access_flags,
                alias.as_ref(),
            );
            let t = match self.indexed_access_types.get(&key) {
                Some(&t) => t,
                None => {
                    let t = self.new_indexed_access_type(
                        object_type,
                        index_type,
                        persistent_access_flags,
                    );
                    self.types.get_mut(t).alias = alias.clone();
                    self.indexed_access_types.insert(key, t);
                    t
                }
            };
            return Some(t);
        }
        // In the following we resolve T[K] to the type of the property in T selected by K.
        // We treat boolean as different from other unions to improve errors;
        // skipping straight to getPropertyTypeForIndexType gives errors with 'boolean' instead of 'true'.
        let apparent_object_type = self.get_reduced_apparent_type(object_type);
        let index_flags = self.types.get(index_type).flags;
        if index_flags.intersects(TypeFlags::UNION)
            && !index_flags.intersects(TypeFlags::BOOLEAN)
        {
            let mut prop_types = Vec::new();
            let mut was_missing_prop = false;
            for &t in &self.types.get(index_type).types().to_vec()
            {
                let flags = if was_missing_prop {
                    access_flags | AccessFlags::SUPPRESS_NO_IMPLICIT_ANY_ERROR
                } else {
                    access_flags
                };
                let prop_type = self.get_property_type_for_index_type(
                    object_type,
                    apparent_object_type,
                    t,
                    index_type,
                    access_node,
                    flags,
                );
                if let Some(prop_type) = prop_type {
                    prop_types.push(prop_type);
                } else if access_node.is_none() {
                    // If there's no error node, we can immediately stop, since error reporting is off
                    return None;
                } else {
                    // Otherwise we set a flag and return at the end of the loop so we still mark all errors
                    was_missing_prop = true;
                }
            }
            if was_missing_prop {
                return None;
            }
            if access_flags.intersects(AccessFlags::WRITING) {
                return Some(self.get_intersection_type_ex(
                    &prop_types,
                    IntersectionFlags::NONE,
                    alias,
                ));
            }
            return Some(self.get_union_type_ex(
                &prop_types,
                UnionReduction::LITERAL,
                alias,
                None,
            ));
        }
        self.get_property_type_for_index_type(
            object_type,
            apparent_object_type,
            index_type,
            index_type,
            access_node,
            access_flags | AccessFlags::CACHE_SYMBOL | AccessFlags::REPORT_DEPRECATED,
        )
    }

    /// `(c *Checker) getPropertyTypeForIndexType` (checker.go:27535).
    pub(crate) fn get_property_type_for_index_type(
        &mut self,
        original_object_type: TypeId,
        object_type: TypeId,
        index_type: TypeId,
        full_index_type: TypeId,
        access_node: Option<NodeId>,
        access_flags: AccessFlags,
    ) -> Option<TypeId> {
        let access_expression = access_node.filter(|&n| {
            ast::is_element_access_expression(&self.program_nodes(n)[n])
        });
        let mut prop_name = String::new();
        let mut has_prop_name = false;
        if !access_node.is_some_and(|n| {
            ast::is_private_identifier(&self.program_nodes(n)[n])
        }) {
            prop_name = self.get_property_name_from_index(index_type, access_node);
            has_prop_name = prop_name != ast::symbol::INTERNAL_SYMBOL_NAME_MISSING;
        }
        if has_prop_name {
            if access_flags.intersects(AccessFlags::CONTEXTUAL) {
                let t = self
                    .get_type_of_property_of_contextual_type(object_type, &prop_name)
                    .unwrap_or(self.any_type);
                return Some(t);
            }
            if let Some(prop) = self.get_property_of_type(object_type, &prop_name) {
                if access_flags.intersects(AccessFlags::REPORT_DEPRECATED)
                    && access_node.is_some()
                    && !self.sym(prop).declarations.is_empty()
                    && self.is_deprecated_symbol(prop)
                    && self.is_uncalled_function_reference(access_node.unwrap(), prop)
                {
                    let deprecated_node = if let Some(access_expression) = access_expression {
                        self.program_nodes(access_expression)[access_expression]
                            .as_element_access_expression()
                            .argument_expression
                            .unwrap()
                    } else if ast::is_indexed_access_type_node(
                        &self.program_nodes(access_node.unwrap())[access_node.unwrap()],
                    ) {
                        self.program_nodes(access_node.unwrap())[access_node.unwrap()]
                            .as_indexed_access_type_node()
                            .index_type
                            .unwrap()
                    } else {
                        access_node.unwrap()
                    };
                    self.add_deprecated_suggestion(
                        deprecated_node,
                        &self.sym(prop).declarations.clone(),
                        &prop_name,
                    );
                }
                if let Some(access_expression) = access_expression {
                    let expression = self.program_nodes(access_expression)[access_expression]
                        .expression()
                        .unwrap();
                    let object_symbol = self.types.get(object_type).symbol;
                    self.mark_property_as_referenced(
                        prop,
                        Some(access_expression),
                        self.is_self_type_access(expression, object_symbol),
                    );
                    let assignment_kind = crate::utilities::get_assignment_target_kind(
                        access_expression,
                        &self.program_nodes(access_expression),
                    );
                    if self.is_assignment_to_readonly_entity(
                        access_expression,
                        prop,
                        assignment_kind,
                    ) {
                        let argument_expression = self.program_nodes(access_expression)
                            [access_expression]
                            .as_element_access_expression()
                            .argument_expression;
                        self.error(
                            argument_expression,
                            &tsc_diagnostics::Cannot_assign_to_0_because_it_is_a_read_only_property,
                            &[self.symbol_to_string(prop)],
                        );
                        return None;
                    }
                    if access_flags.intersects(AccessFlags::CACHE_SYMBOL) {
                        self.symbol_node_links
                            .get(access_node.unwrap())
                            .resolved_symbol = Some(prop);
                    }
                    if self.is_this_property_access_in_constructor(access_expression, prop) {
                        return Some(self.auto_type);
                    }
                }
                let prop_type = if access_flags.intersects(AccessFlags::WRITING) {
                    self.get_write_type_of_symbol(prop)
                } else {
                    self.get_type_of_symbol(prop)
                };
                if let Some(access_expression) = access_expression {
                    if crate::utilities::get_assignment_target_kind(
                        access_expression,
                        &self.program_nodes(access_expression),
                    ) != crate::utilities::AssignmentKind::DEFINITE
                    {
                        return Some(self.get_flow_type_of_reference(access_expression, prop_type));
                    }
                }
                if access_node.is_some_and(|n| {
                    ast::is_indexed_access_type_node(&self.program_nodes(n)[n])
                }) && self.contains_missing_type(prop_type)
                {
                    return Some(self.get_union_type(&[prop_type, self.undefined_type]));
                }
                return Some(prop_type);
            }
            if every_type(self, object_type, |c: &mut Checker, t: TypeId| {
                crate::checker_core::is_tuple_type(&c.types, t)
            }) && crate::utilities::is_numeric_literal_name(&prop_name)
            {
                let index = tsc_jsnum::from_string(&prop_name);
                if access_node.is_some()
                    && every_type(self, object_type, |c: &mut Checker, t: TypeId| {
                        !c.types
                            .get(c.types.target_tuple_type(t).unwrap())
                            .as_tuple_type()
                            .combined_flags
                            .intersects(ElementFlags::VARIABLE)
                    })
                    && !access_flags.intersects(AccessFlags::ALLOW_MISSING)
                {
                    let index_node =
                        get_index_node_for_access_expression(access_node.unwrap(), self);
                    if crate::checker_core::is_tuple_type(&self.types, object_type) {
                        if index < tsc_jsnum::Number(0.0) {
                            self.error(
                                Some(index_node),
                                &tsc_diagnostics::A_tuple_type_cannot_be_indexed_with_a_negative_value,
                                &[],
                            );
                            return Some(self.undefined_type);
                        }
                        self.error(
                            Some(index_node),
                            &tsc_diagnostics::Tuple_type_0_of_length_1_has_no_element_at_index_2,
                            &[
                                self.type_to_string(object_type),
                                self.get_type_reference_arity(object_type).to_string(),
                                prop_name.clone(),
                            ],
                        );
                    } else {
                        self.error(
                            Some(index_node),
                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                            &[prop_name.clone(), self.type_to_string(object_type)],
                        );
                    }
                }
                if index >= tsc_jsnum::Number(0.0) {
                    let index_info = self.get_index_info_of_type(object_type, self.number_type);
                    self.error_if_writing_to_readonly_index(
                        index_info,
                        object_type,
                        access_expression,
                    );
                    let undefined_like_type = if access_flags
                        .intersects(AccessFlags::INCLUDE_UNDEFINED)
                    {
                        Some(self.missing_type)
                    } else {
                        None
                    };
                    return Some(self.get_tuple_element_type_out_of_start_count(
                        object_type,
                        index,
                        undefined_like_type,
                    ));
                }
            }
        }
        if !self.types.get(index_type).flags.intersects(TypeFlags::NULLABLE)
            && self.is_type_assignable_to_kind(
                index_type,
                TypeFlags::STRING_LIKE
                    | TypeFlags::NUMBER_LIKE
                    | TypeFlags::ES_SYMBOL_LIKE,
            )
        {
            if self
                .types
                .get(object_type)
                .flags
                .intersects(TypeFlags::ANY | TypeFlags::NEVER)
            {
                return Some(object_type);
            }
            // If no index signature is applicable, we default to the string index signature. In effect, this means the string
            // index signature applies even when accessing with a symbol-like type.
            let mut index_info = self.get_applicable_index_info(object_type, index_type);
            if index_info.is_none() {
                index_info = self.get_index_info_of_type(object_type, self.string_type);
            }
            if let Some(index_info_id) = index_info {
                let (key_type, value_type) = {
                    let info = self.index_info_arena.get(index_info_id);
                    (info.key_type, info.value_type)
                };
                if access_flags.intersects(AccessFlags::NO_INDEX_SIGNATURES)
                    && key_type != Some(self.number_type)
                {
                    if let Some(access_expression) = access_expression {
                        if access_flags.intersects(AccessFlags::WRITING) {
                            self.error(
                                Some(access_expression),
                                &tsc_diagnostics::Type_0_is_generic_and_can_only_be_indexed_for_reading,
                                &[self.type_to_string(original_object_type)],
                            );
                        } else {
                            self.error(
                                Some(access_expression),
                                &tsc_diagnostics::Type_0_cannot_be_used_to_index_type_1,
                                &[
                                    self.type_to_string(index_type),
                                    self.type_to_string(original_object_type),
                                ],
                            );
                        }
                    }
                    return None;
                }
                if access_node.is_some()
                    && key_type == Some(self.string_type)
                    && !self.is_type_assignable_to_kind(
                        index_type,
                        TypeFlags::STRING | TypeFlags::NUMBER,
                    )
                {
                    let index_node =
                        get_index_node_for_access_expression(access_node.unwrap(), self);
                    self.error(
                        Some(index_node),
                        &tsc_diagnostics::Type_0_cannot_be_used_as_an_index_type,
                        &[self.type_to_string(index_type)],
                    );
                    if access_flags.intersects(AccessFlags::INCLUDE_UNDEFINED) {
                        return Some(self.get_union_type(&[
                            value_type.unwrap_or(self.error_type),
                            self.missing_type,
                        ]));
                    }
                    return Some(value_type.unwrap_or(self.error_type));
                }
                self.error_if_writing_to_readonly_index(
                    Some(index_info_id),
                    object_type,
                    access_expression,
                );
                // When accessing an enum object with its own type,
                // e.g. E[E.A] for enum E { A }, undefined shouldn't
                // be included in the result type
                if access_flags.intersects(AccessFlags::INCLUDE_UNDEFINED) && {
                    let object_symbol = self.types.get(object_type).symbol;
                    !(object_symbol.is_some_and(|s| {
                        self.sym(s)
                            .flags
                            .intersects(ast::SymbolFlags::REGULAR_ENUM | ast::SymbolFlags::CONST_ENUM)
                    }) && {
                        let index_symbol = self.types.get(index_type).symbol;
                        index_symbol.is_some_and(|s| {
                            self.types
                                .get(index_type)
                                .flags
                                .intersects(TypeFlags::ENUM_LITERAL)
                                && self.get_parent_of_symbol(s) == object_symbol
                        })
                    })
                } {
                    return Some(self.get_union_type(&[
                        value_type.unwrap_or(self.error_type),
                        self.missing_type,
                    ]));
                }
                return Some(value_type.unwrap_or(self.error_type));
            }
            if self.types.get(index_type).flags.intersects(TypeFlags::NEVER) {
                return Some(self.never_type);
            }
            if self.is_js_literal_type(object_type) {
                return Some(self.any_type);
            }
            if let Some(access_expression) = access_expression {
                if !is_const_enum_object_type(self, object_type) {
                    if crate::utilities::is_object_literal_type(&self.types, object_type) {
                        if self.no_implicit_any
                            && self.types.get(index_type).flags.intersects(
                                TypeFlags::STRING_LITERAL | TypeFlags::NUMBER_LITERAL,
                            )
                        {
                            let value = self
                                .types
                                .get(index_type)
                                .as_literal_type()
                                .value
                                .to_string();
                            let diagnostic = self.new_diagnostic_for_node(
                                Some(access_expression),
                                &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                                &[value, self.type_to_string(object_type)],
                            );
                            self.add_diagnostic(&diagnostic);
                            return Some(self.undefined_type);
                        } else if self.types.get(index_type).flags.intersects(
                            TypeFlags::NUMBER | TypeFlags::STRING,
                        ) {
                            let properties = self
                                .types
                                .get(object_type)
                                .as_object_type_data()
                                .map(|d| d.properties.clone())
                                .unwrap_or_default();
                            let mut types: Vec<TypeId> = properties
                                .iter()
                                .map(|&prop| self.get_type_of_symbol(prop))
                                .collect();
                            types.push(self.undefined_type);
                            return Some(self.get_union_type(&types));
                        }
                    }
                    if self.types.get(object_type).symbol == Some(self.global_this_symbol)
                        && has_prop_name
                        && self
                            .sym(self.global_this_symbol)
                            .exports
                            .get(&prop_name)
                            .is_some_and(|s| {
                                self.sym(s).flags.intersects(ast::SymbolFlags::BLOCK_SCOPED)
                            })
                    {
                        self.error(
                            Some(access_expression),
                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                            &[prop_name.clone(), self.type_to_string(object_type)],
                        );
                    } else if self.no_implicit_any
                        && !access_flags
                            .intersects(AccessFlags::SUPPRESS_NO_IMPLICIT_ANY_ERROR)
                    {
                        if has_prop_name && self.type_has_static_property(&prop_name, object_type)
                        {
                            let type_name = self.type_to_string(object_type);
                            let argument_expression = self.program_nodes(access_expression)
                                [access_expression]
                                .as_element_access_expression()
                                .argument_expression
                                .unwrap();
                            let text = tsc_scanner::utilities::get_text_of_node(
                                argument_expression,
                                &self.program_nodes(argument_expression),
                            );
                            self.error(
                                Some(access_expression),
                                &tsc_diagnostics::Property_0_does_not_exist_on_type_1_Did_you_mean_to_access_the_static_member_2_instead,
                                &[
                                    prop_name.clone(),
                                    type_name.clone(),
                                    format!("{}[{}]", type_name, text),
                                ],
                            );
                        } else if self
                            .get_index_type_of_type(object_type, self.number_type)
                            .is_some()
                        {
                            let argument_expression = self.program_nodes(access_expression)
                                [access_expression]
                                .as_element_access_expression()
                                .argument_expression;
                            self.error(
                                argument_expression,
                                &tsc_diagnostics::Element_implicitly_has_an_any_type_because_index_expression_is_not_of_type_number,
                                &[],
                            );
                        } else {
                            let mut suggestion = String::new();
                            if has_prop_name {
                                suggestion = self.get_suggestion_for_nonexistent_property(
                                    &prop_name,
                                    object_type,
                                );
                            }
                            if !suggestion.is_empty() {
                                let argument_expression = self.program_nodes(access_expression)
                                    [access_expression]
                                    .as_element_access_expression()
                                    .argument_expression;
                                self.error(
                                    argument_expression,
                                    &tsc_diagnostics::Property_0_does_not_exist_on_type_1_Did_you_mean_2,
                                    &[
                                        prop_name.clone(),
                                        self.type_to_string(object_type),
                                        suggestion,
                                    ],
                                );
                            } else {
                                suggestion = self.get_suggestion_for_nonexistent_index_signature(
                                    object_type,
                                    access_expression,
                                    index_type,
                                );
                                if !suggestion.is_empty() {
                                    self.error(
                                        Some(access_expression),
                                        &tsc_diagnostics::Element_implicitly_has_an_any_type_because_type_0_has_no_index_signature_Did_you_mean_to_call_1,
                                        &[self.type_to_string(object_type), suggestion],
                                    );
                                } else {
                                    let index_flags = self.types.get(index_type).flags;
                                    let diagnostic = if index_flags
                                        .intersects(TypeFlags::ENUM_LITERAL)
                                    {
                                        self.new_diagnostic_for_node(
                                            Some(access_expression),
                                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                                            &[
                                                format!("[{}]", self.type_to_string(index_type)),
                                                self.type_to_string(object_type),
                                            ],
                                        )
                                    } else if index_flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
                                        let index_symbol =
                                            self.types.get(index_type).symbol.unwrap();
                                        let symbol_name = self.get_fully_qualified_name(
                                            index_symbol,
                                            Some(access_expression),
                                        );
                                        self.new_diagnostic_for_node(
                                            Some(access_expression),
                                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                                            &[
                                                format!("[{}]", symbol_name),
                                                self.type_to_string(object_type),
                                            ],
                                        )
                                    } else if index_flags.intersects(TypeFlags::STRING_LITERAL)
                                        || index_flags.intersects(TypeFlags::NUMBER_LITERAL)
                                    {
                                        let value = self
                                            .types
                                            .get(index_type)
                                            .as_literal_type()
                                            .value
                                            .to_string();
                                        self.new_diagnostic_for_node(
                                            Some(access_expression),
                                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                                            &[value, self.type_to_string(object_type)],
                                        )
                                    } else {
                                        self.new_diagnostic_for_node(
                                            Some(access_expression),
                                            &tsc_diagnostics::No_index_signature_with_a_parameter_of_type_0_was_found_on_type_1,
                                            &[
                                                self.type_to_string(index_type),
                                                self.type_to_string(object_type),
                                            ],
                                        )
                                    };
                                    let diagnostic = crate::utilities::new_diagnostic_chain_for_node(
                                        self,
                                        Some(diagnostic),
                                        access_expression,
                                        &tsc_diagnostics::Element_implicitly_has_an_any_type_because_expression_of_type_0_can_t_be_used_to_index_type_1,
                                        &[
                                            self.type_to_string(full_index_type),
                                            self.type_to_string(object_type),
                                        ],
                                    );
                                    self.add_diagnostic(&diagnostic);
                                }
                            }
                        }
                    }
                }
            }
            return None;
        }
        if access_flags.intersects(AccessFlags::ALLOW_MISSING)
            && crate::utilities::is_object_literal_type(&self.types, object_type)
        {
            return Some(self.undefined_type);
        }
        if self.is_js_literal_type(object_type) {
            return Some(self.any_type);
        }
        if let Some(access_node) = access_node {
            let index_node = get_index_node_for_access_expression(access_node, self);
            let index_flags = self.types.get(index_type).flags;
            if self.program_nodes(index_node)[index_node].kind != ast::Kind::BigIntLiteral
                && index_flags.intersects(TypeFlags::STRING_LITERAL | TypeFlags::NUMBER_LITERAL)
            {
                let value = self
                    .types
                    .get(index_type)
                    .as_literal_type()
                    .value
                    .to_string();
                self.error(
                    Some(index_node),
                    &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                    &[value, self.type_to_string(object_type)],
                );
            } else if index_flags.intersects(TypeFlags::STRING | TypeFlags::NUMBER) {
                self.error(
                    Some(index_node),
                    &tsc_diagnostics::Type_0_has_no_matching_index_signature_for_type_1,
                    &[
                        self.type_to_string(object_type),
                        self.type_to_string(index_type),
                    ],
                );
            } else {
                let type_string = if self.program_nodes(index_node)[index_node].kind
                    == ast::Kind::BigIntLiteral
                {
                    "bigint".to_string()
                } else {
                    self.type_to_string(index_type)
                };
                self.error(
                    Some(index_node),
                    &tsc_diagnostics::Type_0_cannot_be_used_as_an_index_type,
                    &[type_string],
                );
            }
        }
        if crate::utilities::is_type_any(&self.types, index_type) {
            return Some(index_type);
        }
        None
    }

    /// `(c *Checker) typeHasStaticProperty` (checker.go:27749).
    pub(crate) fn type_has_static_property(
        &mut self,
        prop_name: &str,
        containing_type: TypeId,
    ) -> bool {
        if let Some(symbol) = self.types.get(containing_type).symbol {
            let t = self.get_type_of_symbol(symbol);
            if let Some(prop) = self.get_property_of_type(t, prop_name) {
                let value_declaration = self.sym(prop).value_declaration;
                return value_declaration.is_some_and(|d| {
                    ast::is_static(&self.program_nodes(d)[d])
                });
            }
        }
        false
    }

    /// `(c *Checker) getSuggestionForNonexistentProperty` (checker.go:27759).
    pub(crate) fn get_suggestion_for_nonexistent_property(
        &mut self,
        name: &str,
        containing_type: TypeId,
    ) -> String {
        let properties = self.get_properties_of_type(containing_type);
        if let Some(symbol) = self.get_spelling_suggestion_for_name(
            name,
            properties.into_iter(),
            ast::SymbolFlags::VALUE,
        ) {
            return self.sym(symbol).name.clone();
        }
        String::new()
    }

    /// `(c *Checker) getSuggestionForNonexistentIndexSignature` (checker.go:27767).
    pub(crate) fn get_suggestion_for_nonexistent_index_signature(
        &mut self,
        object_type: TypeId,
        expr: NodeId,
        keyed_type: TypeId,
    ) -> String {
        // check if object type has setter or getter
        let has_prop = |c: &mut Checker, name: &str| -> bool {
            if let Some(prop) = c.get_property_of_object_type(object_type, name) {
                let prop_type = c.get_type_of_symbol(prop);
                if let Some(s) = c.get_single_call_signature(prop_type) {
                    return c.get_min_argument_count(s) >= 1
                        && c.is_type_assignable_to(
                            keyed_type,
                            c.get_type_at_position(s, 0),
                        );
                }
            }
            false
        };
        let nodes = self.program_nodes(expr);
        let suggested_method = if ast::is_assignment_target(expr, &nodes) {
            "set"
        } else {
            "get"
        };
        if !has_prop(self, suggested_method) {
            return String::new();
        }
        let expression = self.program_nodes(expr)[expr].expression();
        let suggestion = expression
            .and_then(|e| {
                crate::utilities::try_get_property_access_or_identifier_to_string(
                    e,
                    &self.program_nodes(e),
                )
            })
            .unwrap_or_default();
        if suggestion.is_empty() {
            return suggested_method.to_string();
        }
        format!("{}.{}", suggestion, suggested_method)
    }

    /// `(c *Checker) getSuggestedTypeForNonexistentStringLiteralType` (checker.go:27786).
    /// Go returns `*Type`; the literal `value` of the candidate is used by callers.
    pub(crate) fn get_suggested_type_for_nonexistent_string_literal_type(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Option<TypeId> {
        let candidates: Vec<TypeId> = self.types.get(target).types()
            .to_vec()
            .iter()
            .copied()
            .filter(|&t| {
                self.types.get(t).flags.intersects(TypeFlags::STRING_LITERAL)
            })
            .collect();
        let source_value = get_string_literal_value(&self.types, source);
        tsc_core::get_spelling_suggestion_with_max_candidate_count(
            &source_value,
            &candidates,
            |&t| get_string_literal_value(&self.types, t),
            |a, b| compare_types(&self.types, a, b),
            1000,
        )
    }

    /// `(c *Checker) errorIfWritingToReadonlyIndex` (checker.go:27796).
    pub(crate) fn error_if_writing_to_readonly_index(
        &mut self,
        index_info: Option<IndexInfoId>,
        object_type: TypeId,
        access_expression: Option<NodeId>,
    ) {
        let Some(access_expression) = access_expression else {
            return;
        };
        let Some(index_info) = index_info else {
            return;
        };
        if !self.index_info_arena.get(index_info).is_readonly {
            return;
        }
        let nodes = self.program_nodes(access_expression);
        if ast::is_assignment_target(access_expression, &nodes)
            || crate::utilities::is_delete_target(access_expression, &nodes)
        {
            self.error(
                Some(access_expression),
                &tsc_diagnostics::Index_signature_in_type_0_only_permits_reading,
                &[self.type_to_string(object_type)],
            );
        }
    }

    /// `(c *Checker) isSelfTypeAccess` (checker.go:27803).
    /// Go `*ast.Symbol` → `Option<SymbolId>`.
    pub(crate) fn is_self_type_access(
        &mut self,
        name: NodeId,
        parent: Option<SymbolId>,
    ) -> bool {
        let nodes = self.program_nodes(name);
        if nodes[name].kind == ast::Kind::ThisKeyword {
            return true;
        }
        if let Some(parent) = parent {
            if ast::is_entity_name_expression(&nodes[name], &nodes) {
                let first = ast::get_first_identifier(name, &nodes);
                return Some(parent) == self.get_resolved_symbol(first);
            }
        }
        false
    }

    /// `(c *Checker) isAssignmentToReadonlyEntity` (checker.go:27807).
    pub(crate) fn is_assignment_to_readonly_entity(
        &mut self,
        expr: NodeId,
        symbol: SymbolId,
        assignment_kind: crate::utilities::AssignmentKind,
    ) -> bool {
        if assignment_kind == crate::utilities::AssignmentKind::NONE {
            // no assignment means it doesn't matter whether the entity is readonly
            return false;
        }
        let nodes = self.program_nodes(expr);
        if ast::is_access_expression(&nodes[expr], &nodes) {
            let node = ast::skip_parentheses(nodes[expr].expression().unwrap(), &nodes);
            if ast::is_identifier(&nodes[node]) {
                if let Some(expression_symbol) = self.get_resolved_symbol(node) {
                    // CommonJS module.exports is never readonly
                    if self
                        .sym(expression_symbol)
                        .flags
                        .intersects(ast::SymbolFlags::MODULE_EXPORTS)
                    {
                        return false;
                    }
                }
            }
        }
        if self.is_readonly_symbol(symbol) {
            // Allow assignments to readonly properties within constructors of the same class declaration.
            if self.sym(symbol).flags.intersects(ast::SymbolFlags::PROPERTY)
                && ast::is_access_expression(&nodes[expr], &nodes)
                && nodes[nodes[expr].expression().unwrap()].kind == ast::Kind::ThisKeyword
            {
                // Look for if this is the constructor for the class that `symbol` is a property of.
                let ctor = self.get_control_flow_container(expr);
                if ctor.is_none_or(|c| !ast::is_constructor_declaration(&nodes[c])) {
                    return true;
                }
                let ctor = ctor.unwrap();
                if let Some(value_declaration) = self.sym(symbol).value_declaration {
                    let is_assignment_declaration =
                        ast::is_binary_expression(&nodes[value_declaration]);
                    let is_local_property_declaration = nodes[ctor].parent
                        == nodes[value_declaration].parent;
                    let is_local_parameter_property = Some(ctor) == nodes[value_declaration].parent;
                    let is_local_this_property_assignment = is_assignment_declaration
                        && self
                            .sym(symbol)
                            .parent
                            .and_then(|p| self.sym(p).value_declaration)
                            == nodes[ctor].parent;
                    let is_local_this_property_assignment_constructor_function =
                        is_assignment_declaration
                            && self
                                .sym(symbol)
                                .parent
                                .and_then(|p| self.sym(p).value_declaration)
                                == Some(ctor);
                    let is_writeable_symbol = is_local_property_declaration
                        || is_local_parameter_property
                        || is_local_this_property_assignment
                        || is_local_this_property_assignment_constructor_function;
                    return !is_writeable_symbol;
                }
            }
            return true;
        }
        if ast::is_access_expression(&nodes[expr], &nodes) {
            // references through namespace import should be readonly
            let node = ast::skip_parentheses(nodes[expr].expression().unwrap(), &nodes);
            if ast::is_identifier(&nodes[node]) {
                if let Some(expression_symbol) = self.get_resolved_symbol(node) {
                    if self
                        .sym(expression_symbol)
                        .flags
                        .intersects(ast::SymbolFlags::ALIAS)
                    {
                        let declaration = self.get_declaration_of_alias_symbol(expression_symbol);
                        return declaration.is_some_and(|d| {
                            ast::is_namespace_import(&self.program_nodes(d)[d])
                        });
                    }
                }
            }
        }
        false
    }

    /// `(c *Checker) isThisPropertyAccessInConstructor` (checker.go:27850).
    pub(crate) fn is_this_property_access_in_constructor(
        &mut self,
        node: NodeId,
        prop: SymbolId,
    ) -> bool {
        let mut constructor = None;
        let (kind, location) = self.is_constructor_declared_this_property(prop);
        if kind == ThisAssignmentDeclarationKind::Constructor {
            constructor = location;
        } else {
            let nodes = self.program_nodes(node);
            if crate::utilities::is_this_property(node, &nodes) && self.is_auto_typed_property(prop)
            {
                constructor = self.get_declaring_constructor(prop);
            }
        }
        let nodes = self.program_nodes(node);
        Some(ast::get_this_container(
            node,
            &nodes,
            true,  /*includeArrowFunctions*/
            false, /*includeClassComputedPropertyName*/
        )) == constructor
    }

    /// `(c *Checker) isAutoTypedProperty` (checker.go:27860).
    pub(crate) fn is_auto_typed_property(&mut self, symbol: SymbolId) -> bool {
        // A property is auto-typed when its declaration has no type annotation or initializer and we're in
        // noImplicitAny mode or a .js file.
        let declaration = self.sym(symbol).value_declaration;
        declaration.is_some_and(|d| {
            let nodes = self.program_nodes(d);
            ast::is_property_declaration(&nodes[d])
                && nodes[d].type_().is_none()
                && nodes[d].initializer().is_none()
                && self.no_implicit_any
        })
    }

    /// `(c *Checker) getDeclaringConstructor` (checker.go:27866).
    pub(crate) fn get_declaring_constructor(&mut self, symbol: SymbolId) -> Option<NodeId> {
        for &declaration in &self.sym(symbol).declarations.clone() {
            let nodes = self.program_nodes(declaration);
            let container = ast::get_this_container(
                declaration,
                &nodes,
                false, /*includeArrowFunctions*/
                false, /*includeClassComputedPropertyName*/
            );
            if ast::is_constructor_declaration(&nodes[container]) {
                return Some(container);
            }
        }
        None
    }

    /// `(c *Checker) getPropertyNameFromIndex` (checker.go:27875).
    pub(crate) fn get_property_name_from_index(
        &mut self,
        index_type: TypeId,
        access_node: Option<NodeId>,
    ) -> String {
        if crate::utilities::is_type_usable_as_property_name(&self.types, index_type) {
            return crate::utilities::get_property_name_from_type(&self.types, index_type);
        }
        if let Some(access_node) = access_node {
            let nodes = self.program_nodes(access_node);
            if ast::is_property_name(&nodes[access_node]) {
                return ast::get_property_name_for_property_name_node(access_node, &nodes);
            }
        }
        ast::symbol::INTERNAL_SYMBOL_NAME_MISSING.to_string()
    }

    /// `(c *Checker) shouldDeferIndexedAccessType` (checker.go:27891).
    pub(crate) fn should_defer_indexed_access_type(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
        access_node: Option<NodeId>,
    ) -> bool {
        if self.is_generic_index_type(index_type) {
            return true;
        }
        if access_node.is_some_and(|n| {
            !ast::is_indexed_access_type_node(&self.program_nodes(n)[n])
        }) {
            return self.is_generic_tuple_type(object_type)
                && !index_type_less_than(
                    self,
                    index_type,
                    crate::utilities::get_total_fixed_element_count(
                        &self.types,
                        self.types.target_tuple_type(object_type).unwrap(),
                    ),
                );
        }
        self.is_generic_object_type(object_type)
            && !(crate::checker_core::is_tuple_type(&self.types, object_type)
                && index_type_less_than(
                    self,
                    index_type,
                    crate::utilities::get_total_fixed_element_count(
                        &self.types,
                        self.types.target_tuple_type(object_type).unwrap(),
                    ),
                ))
            || self.is_generic_reducible_type(object_type)
    }

    /// `(c *Checker) getNoInferType` (checker.go:27927).
    pub(crate) fn get_no_infer_type(&mut self, t: TypeId) -> TypeId {
        if self.is_no_infer_target_type(t) {
            return self.get_or_create_substitution_type(t, self.unknown_type);
        }
        t
    }

    /// `(c *Checker) isNoInferTargetType` (checker.go:27934).
    pub(crate) fn is_no_infer_target_type(&mut self, t: TypeId) -> bool {
        // This is effectively a more conservative and predictable form of couldContainTypeVariables. We want to
        // preserve NoInfer<T> only for types that could contain type variables, but we don't want to exhaustively
        // examine all object type members.
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::UNION_OR_INTERSECTION)
            && self
                .types
                .get(t)
                .as_union_or_intersection_type()
                .map(|u| u.types.clone())
                .unwrap_or_default()
                .iter()
                .any(|&m| self.is_no_infer_target_type(m))
        {
            return true;
        }
        if flags.intersects(TypeFlags::SUBSTITUTION)
            && !self.is_no_infer_type(t)
            && self.is_no_infer_target_type(self.types.get(t).as_substitution_type().base_type.unwrap())
        {
            return true;
        }
        if flags.intersects(TypeFlags::OBJECT) && !self.is_empty_anonymous_object_type(t) {
            return true;
        }
        flags.intersects(TypeFlags::INSTANTIABLE.without(TypeFlags::SUBSTITUTION))
            && !self.is_pattern_literal_type(t)
    }

    /// `(c *Checker) getSubstitutionType` (checker.go:27944).
    pub(crate) fn get_substitution_type(&mut self, base_type: TypeId, constraint: TypeId) -> TypeId {
        if self
            .types
            .get(constraint)
            .flags
            .intersects(TypeFlags::ANY_OR_UNKNOWN)
            || constraint == base_type
            || self.types.get(base_type).flags.intersects(TypeFlags::ANY)
        {
            return base_type;
        }
        self.get_or_create_substitution_type(base_type, constraint)
    }

    /// `(c *Checker) getOrCreateSubstitutionType` (checker.go:27951).
    pub(crate) fn get_or_create_substitution_type(
        &mut self,
        base_type: TypeId,
        constraint: TypeId,
    ) -> TypeId {
        let key = SubstitutionTypeKey {
            base_id: base_type,
            constraint_id: constraint,
        };
        if let Some(&cached) = self.substitution_types.get(&key) {
            return cached;
        }
        let result = self.new_substitution_type(base_type, constraint);
        self.substitution_types.insert(key, result);
        result
    }

    /// `(c *Checker) getBaseConstraintOrType` (checker.go:27962).
    pub(crate) fn get_base_constraint_or_type(&mut self, t: TypeId) -> TypeId {
        self.get_base_constraint_of_type(t).unwrap_or(t)
    }

    /// `(c *Checker) getBaseConstraintOfType` (checker.go:27970).
    pub(crate) fn get_base_constraint_of_type(&mut self, t: TypeId) -> Option<TypeId> {
        if self.types.get(t).flags.intersects(
            TypeFlags::INSTANTIABLE_NON_PRIMITIVE
                | TypeFlags::UNION_OR_INTERSECTION
                | TypeFlags::TEMPLATE_LITERAL
                | TypeFlags::STRING_MAPPING
                | TypeFlags::INDEX,
        ) || self.is_generic_tuple_type(t)
        {
            let constraint = self.get_resolved_base_constraint(t, &mut Vec::new());
            if constraint != self.no_constraint_type && constraint != self.circular_constraint_type
            {
                return Some(constraint);
            }
            return None;
        }
        None
    }

    /// `(c *Checker) getResolvedBaseConstraint` (checker.go:27981).
    /// Go `stack []RecursionId` → `&mut Vec<RecursionId>`.
    pub(crate) fn get_resolved_base_constraint(
        &mut self,
        t: TypeId,
        stack: &mut Vec<RecursionId>,
    ) -> TypeId {
        if self.types.get(t).as_constrained_type().is_none() {
            return t;
        }
        if let Some(resolved) = self
            .types
            .get(t)
            .as_constrained_type()
            .and_then(|c| c.resolved_base_constraint)
        {
            return resolved;
        }
        if !self.push_type_resolution(t, TypeSystemPropertyName::ResolvedBaseConstraint) {
            return self.circular_constraint_type;
        }
        let mut constraint = None;
        // We always explore at least 10 levels of nested constraints. Thereafter, we continue to explore
        // up to 50 levels of nested constraints provided there are no "deeply nested" types on the stack
        // (i.e. no types for which five instantiations have been recorded on the stack). If we reach 50
        // levels of nesting, we are presumably exploring a repeating pattern with a long cycle that hasn't
        // yet triggered the deeply nested limiter. We have no test cases that actually get to 50 levels of
        // nesting, so it is effectively just a safety stop.
        let identity = get_recursion_identity(self, t);
        if stack.len() < 10 || stack.len() < 50 && !stack.contains(&identity) {
            stack.push(identity);
            let simplified = self.get_simplified_type(t, false);
            constraint = Some(self.compute_base_constraint(simplified, stack));
            stack.pop();
        }
        if !self.pop_type_resolution() {
            if self.types.get(t).flags.intersects(TypeFlags::TYPE_PARAMETER) {
                if let Some(error_node) = self.get_constraint_declaration(t) {
                    let diagnostic = self.error(
                        Some(error_node),
                        &tsc_diagnostics::Type_parameter_0_has_a_circular_constraint,
                        &[self.type_to_string(t)],
                    );
                    if let (Some(diagnostic), Some(current_node)) = (diagnostic, self.current_node)
                    {
                        let error_nodes = self.program_nodes(error_node);
                        let current_nodes = self.program_nodes(current_node);
                        if !ast::is_node_descendant_of(
                            Some(error_node),
                            Some(current_node),
                            &error_nodes,
                        ) && !ast::is_node_descendant_of(
                            Some(current_node),
                            Some(error_node),
                            &current_nodes,
                        ) {
                            let related = self.new_diagnostic_for_node(
                                Some(current_node),
                                &tsc_diagnostics::Circularity_originates_in_type_at_this_location,
                                &[],
                            );
                            diagnostic
                                .lock()
                                .unwrap()
                                .add_related_info(Some(related));
                        }
                    }
                }
            }
            constraint = Some(self.circular_constraint_type);
        }
        let constraint = constraint.unwrap_or(self.no_constraint_type);
        {
            let ty = self.types.get_mut(t);
            if let Some(constrained) = ty.as_constrained_type_mut() {
                if constrained.resolved_base_constraint.is_none() {
                    constrained.resolved_base_constraint = Some(constraint);
                }
            }
        }
        constraint
    }

    /// `(c *Checker) computeBaseConstraint` (checker.go:28022).
    pub(crate) fn compute_base_constraint(
        &mut self,
        t: TypeId,
        stack: &mut Vec<RecursionId>,
    ) -> TypeId {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::TYPE_PARAMETER) {
            let constraint = self.get_constraint_from_type_parameter(t);
            if self.types.get(t).as_type_parameter().is_this_type {
                return constraint;
            }
            return self.get_next_base_constraint(Some(constraint), stack)
                .unwrap_or(self.no_constraint_type);
        }
        if flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
            let types = self.types.get(t).types().to_vec();
            let mut constraints = Vec::with_capacity(types.len());
            let mut different = false;
            for &s in &types {
                if let Some(constraint) = self.get_next_base_constraint(Some(s), stack) {
                    if constraint != s {
                        different = true;
                    }
                    constraints.push(constraint);
                } else {
                    different = true;
                }
            }
            if !different {
                return t;
            }
            if flags.intersects(TypeFlags::UNION) && constraints.len() == types.len() {
                return self.get_union_type(&constraints);
            }
            if flags.intersects(TypeFlags::INTERSECTION) && !constraints.is_empty() {
                return self.get_intersection_type(&constraints);
            }
            return self.no_constraint_type;
        }
        if flags.intersects(TypeFlags::INDEX) {
            let target = self.types.get(t).as_index_type().target.unwrap();
            if self.is_generic_mapped_type(target) {
                let mapped_type = target;
                if self.get_name_type_from_mapped_type(mapped_type).is_some()
                    && !self.is_mapped_type_with_keyof_constraint_declaration(mapped_type)
                {
                    let index_type =
                        self.get_index_type_for_mapped_type(mapped_type, IndexFlags::NONE);
                    return self
                        .get_next_base_constraint(Some(index_type), stack)
                        .unwrap_or(self.no_constraint_type);
                }
            }
            return self.string_number_symbol_type;
        }
        if flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            let types = self.types.get(t).types().to_vec();
            let mut constraints = Vec::with_capacity(types.len());
            for &s in &types {
                if let Some(constraint) = self.get_next_base_constraint(Some(s), stack) {
                    constraints.push(constraint);
                }
            }
            if constraints.len() == types.len() {
                let texts = self
                    .types
                    .get(t)
                    .as_template_literal_type()
                    .texts
                    .clone();
                return self.get_template_literal_type(&texts, &constraints);
            }
            return self.string_type;
        }
        if flags.intersects(TypeFlags::STRING_MAPPING) {
            let target = self.types.target(t).unwrap();
            let constraint = self.get_next_base_constraint(Some(target), stack);
            if constraint.is_some_and(|c| c != target) {
                let symbol = self.types.get(t).symbol;
                return self.get_string_mapping_type(symbol, constraint.unwrap());
            }
            return self.string_type;
        }
        if flags.intersects(TypeFlags::INDEXED_ACCESS) {
            let (object_type, index_type, access_flags) = {
                let iat = self.types.get(t).as_indexed_access_type();
                (
                    iat.object_type.unwrap(),
                    iat.index_type.unwrap(),
                    iat.access_flags,
                )
            };
            if self.is_mapped_type_generic_indexed_access(t) {
                // For indexed access types of the form { [P in K]: E }[X], where K is non-generic and X is generic,
                // we substitute an instantiation of E where P is replaced with X.
                let substituted = self.substitute_indexed_mapped_type(object_type, index_type);
                return self
                    .get_next_base_constraint(Some(substituted), stack)
                    .unwrap_or(self.no_constraint_type);
            }
            let base_object_type = self.get_next_base_constraint(Some(object_type), stack);
            let base_index_type = self.get_next_base_constraint(Some(index_type), stack);
            if base_object_type.is_none() || base_index_type.is_none() {
                return self.no_constraint_type;
            }
            let indexed = self.get_indexed_access_type_or_undefined(
                base_object_type.unwrap(),
                base_index_type.unwrap(),
                access_flags,
                None,
                None,
            );
            return self
                .get_next_base_constraint(indexed, stack)
                .unwrap_or(self.no_constraint_type);
        }
        if flags.intersects(TypeFlags::CONDITIONAL) {
            if self.conditional_constraint_depth >= 100 {
                return self.no_constraint_type;
            }
            self.conditional_constraint_depth += 1;
            let constraint = self.get_constraint_from_conditional_type(t);
            self.conditional_constraint_depth -= 1;
            return self
                .get_next_base_constraint(constraint, stack)
                .unwrap_or(self.no_constraint_type);
        }
        if flags.intersects(TypeFlags::SUBSTITUTION) {
            let intersection = self.get_substitution_intersection(t);
            return self
                .get_next_base_constraint(Some(intersection), stack)
                .unwrap_or(self.no_constraint_type);
        }
        if self.is_generic_tuple_type(t) {
            // We substitute constraints for variadic elements only when the constraints are array types or
            // non-variadic tuple types as we want to avoid further (possibly unbounded) recursion.
            let element_types = self.get_element_types(t);
            let element_infos = self
                .types
                .get(self.types.target_tuple_type(t).unwrap())
                .as_tuple_type()
                .element_infos
                .clone();
            let readonly = self
                .types
                .get(self.types.target_tuple_type(t).unwrap())
                .as_tuple_type()
                .readonly;
            let mut new_elements = Vec::with_capacity(element_types.len());
            for (i, &v) in element_types.iter().enumerate() {
                let mut new_element = v;
                if self.types.get(v).flags.intersects(TypeFlags::TYPE_PARAMETER)
                    && element_infos[i].flags.intersects(ElementFlags::VARIADIC)
                {
                    if let Some(constraint) = self.get_next_base_constraint(Some(v), stack) {
                        if constraint != v
                            && every_type(self, constraint, |c: &mut Checker, n: TypeId| {
                                c.is_array_or_tuple_type(n) && !c.is_generic_tuple_type(n)
                            })
                        {
                            new_element = constraint;
                        }
                    }
                }
                new_elements.push(new_element);
            }
            return self.create_tuple_type_ex(&new_elements, &element_infos, readonly);
        }
        t
    }

    /// `(c *Checker) getNextBaseConstraint` (checker.go:28132).
    /// Go `*Type` → `Option<TypeId>`; `nil` → `None`.
    pub(crate) fn get_next_base_constraint(
        &mut self,
        t: Option<TypeId>,
        stack: &mut Vec<RecursionId>,
    ) -> Option<TypeId> {
        let t = t?;
        let constraint = self.get_resolved_base_constraint(t, stack);
        if constraint == self.no_constraint_type || constraint == self.circular_constraint_type {
            return None;
        }
        Some(constraint)
    }

    /// `(c *Checker) maybeTypeOfKind` (checker.go:28144).
    /// A union or intersection type might be of a given kind if at least one
    /// constituent type is of the given kind.
    pub(crate) fn maybe_type_of_kind(&mut self, t: TypeId, kind: TypeFlags) -> bool {
        if self.types.get(t).flags.intersects(kind) {
            return true;
        }
        if self
            .types
            .get(t)
            .flags
            .intersects(TypeFlags::UNION_OR_INTERSECTION)
        {
            for &t in self.types.get(t).types().iter() {
                if self.maybe_type_of_kind(t, kind) {
                    return true;
                }
            }
        }
        false
    }

    /// `(c *Checker) maybeTypeOfKindConsideringBaseConstraint` (checker.go:28157).
    pub(crate) fn maybe_type_of_kind_considering_base_constraint(
        &mut self,
        t: TypeId,
        kind: TypeFlags,
    ) -> bool {
        if self.maybe_type_of_kind(t, kind) {
            return true;
        }
        let base_constraint = self.get_base_constraint_or_type(t);
        self.maybe_type_of_kind(base_constraint, kind)
    }

    /// `(c *Checker) allTypesAssignableToKind` (checker.go:28161).
    pub(crate) fn all_types_assignable_to_kind(
        &mut self,
        source: TypeId,
        kind: TypeFlags,
    ) -> bool {
        self.all_types_assignable_to_kind_ex(source, kind, false)
    }

    /// `(c *Checker) allTypesAssignableToKindEx` (checker.go:28165).
    pub(crate) fn all_types_assignable_to_kind_ex(
        &mut self,
        source: TypeId,
        kind: TypeFlags,
        strict_null_checks: bool,
    ) -> bool {
        if self
            .types
            .get(source)
            .flags
            .intersects(TypeFlags::UNION)
        {
            let types = self.types.get(source).types().to_vec();
            types
                .iter()
                .all(|&t| self.all_types_assignable_to_kind_ex(t, kind, strict_null_checks))
        } else {
            self.is_type_assignable_to_kind_ex(source, kind, strict_null_checks)
        }
    }

    /// `(c *Checker) isTypeAssignableToKind` (checker.go:28175).
    pub(crate) fn is_type_assignable_to_kind(
        &mut self,
        source: TypeId,
        kind: TypeFlags,
    ) -> bool {
        self.is_type_assignable_to_kind_ex(source, kind, false)
    }

    /// `(c *Checker) isTypeAssignableToKindEx` (checker.go:28179).
    pub(crate) fn is_type_assignable_to_kind_ex(
        &mut self,
        source: TypeId,
        kind: TypeFlags,
        strict: bool,
    ) -> bool {
        let source_flags = self.types.get(source).flags;
        if source_flags.intersects(kind) {
            return true;
        }
        if strict
            && source_flags.intersects(
                TypeFlags::ANY_OR_UNKNOWN
                    | TypeFlags::VOID
                    | TypeFlags::UNDEFINED
                    | TypeFlags::NULL,
            )
        {
            return false;
        }
        kind.intersects(TypeFlags::NUMBER_LIKE) && self.is_type_assignable_to(source, self.number_type)
            || kind.intersects(TypeFlags::BIG_INT_LIKE)
                && self.is_type_assignable_to(source, self.bigint_type)
            || kind.intersects(TypeFlags::STRING_LIKE)
                && self.is_type_assignable_to(source, self.string_type)
            || kind.intersects(TypeFlags::BOOLEAN_LIKE)
                && self.is_type_assignable_to(source, self.boolean_type)
            || kind.intersects(TypeFlags::VOID) && self.is_type_assignable_to(source, self.void_type)
            || kind.intersects(TypeFlags::NEVER)
                && self.is_type_assignable_to(source, self.never_type)
            || kind.intersects(TypeFlags::NULL) && self.is_type_assignable_to(source, self.null_type)
            || kind.intersects(TypeFlags::UNDEFINED)
                && self.is_type_assignable_to(source, self.undefined_type)
            || kind.intersects(TypeFlags::ES_SYMBOL)
                && self.is_type_assignable_to(source, self.es_symbol_type)
            || kind.intersects(TypeFlags::NON_PRIMITIVE)
                && self.is_type_assignable_to(source, self.non_primitive_type)
    }

    /// `(c *Checker) compareProperties` (checker.go:28206).
    /// Go `compareTypes func(source, target *Type) Ternary` →
    /// `compare_types: &mut dyn FnMut(&mut Checker, TypeId, TypeId) -> Ternary`.
    pub(crate) fn compare_properties(
        &mut self,
        source_prop: SymbolId,
        target_prop: SymbolId,
        compare_types: &mut dyn FnMut(&mut Checker, TypeId, TypeId) -> Ternary,
    ) -> Ternary {
        // Two members are considered identical when
        // - they are public properties with identical names, optionality, and types,
        // - they are private or protected properties originating in the same declaration and having identical types
        if source_prop == target_prop {
            return Ternary::TRUE;
        }
        let source_prop_accessibility =
            crate::utilities::get_declaration_modifier_flags_from_symbol(self, source_prop)
                & ast::ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER;
        let target_prop_accessibility =
            crate::utilities::get_declaration_modifier_flags_from_symbol(self, target_prop)
                & ast::ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER;
        if source_prop_accessibility != target_prop_accessibility {
            return Ternary::FALSE;
        }
        if source_prop_accessibility != ast::ModifierFlags::NONE {
            if self.get_target_symbol(source_prop) != self.get_target_symbol(target_prop) {
                return Ternary::FALSE;
            }
        } else if (self.sym(source_prop).flags & ast::SymbolFlags::OPTIONAL)
            != (self.sym(target_prop).flags & ast::SymbolFlags::OPTIONAL)
        {
            return Ternary::FALSE;
        }
        if self.is_readonly_symbol(source_prop) != self.is_readonly_symbol(target_prop) {
            return Ternary::FALSE;
        }
        let source_type = self.get_non_missing_type_of_symbol(source_prop);
        let target_type = self.get_non_missing_type_of_symbol(target_prop);
        compare_types(self, source_type, target_type)
    }
}

/// `isInvalidComputedPropertyName` (checker.go:27330). Free function in Go.
fn is_invalid_computed_property_name(c: &Checker, node: NodeId) -> bool {
    let nodes = c.program_nodes(node);
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    let Some(grandparent) = nodes[parent].parent else {
        return false;
    };
    (ast::is_type_literal_node(&nodes[grandparent])
        || ast::is_class_like(Some(grandparent), &nodes)
        || ast::is_interface_declaration(&nodes[grandparent]))
        && nodes[node].expression().is_some_and(|e| {
            ast::is_binary_expression(&nodes[e])
                && nodes[e].as_binary_expression().operator_token.kind == ast::Kind::InKeyword
        })
        && !ast::is_accessor(&nodes[parent])
}

/// `getIndexNodeForAccessExpression` (checker.go:27791). Free function in Go.
fn get_index_node_for_access_expression(access_node: NodeId, c: &Checker) -> NodeId {
    let nodes = c.program_nodes(access_node);
    match nodes[access_node].kind {
        ast::Kind::ElementAccessExpression => nodes[access_node]
            .as_element_access_expression()
            .argument_expression
            .unwrap_or(access_node),
        ast::Kind::IndexedAccessType => nodes[access_node]
            .as_indexed_access_type_node()
            .index_type
            .unwrap_or(access_node),
        ast::Kind::ComputedPropertyName => {
            nodes[access_node].expression().unwrap_or(access_node)
        }
        _ => access_node,
    }
}

/// `indexTypeLessThan` (checker.go:27915). Free function in Go.
fn index_type_less_than(c: &Checker, index_type: TypeId, limit: usize) -> bool {
    every_type(c, index_type, |c: &mut Checker, t: TypeId| {
        if c
            .types
            .get(t)
            .flags
            .intersects(TypeFlags::STRING_OR_NUMBER_LITERAL)
        {
            let prop_name = crate::utilities::get_property_name_from_type(&c.types, t);
            if crate::utilities::is_numeric_literal_name(&prop_name) {
                let index = tsc_jsnum::from_string(&prop_name);
                return index >= tsc_jsnum::Number(0.0)
                    && index < tsc_jsnum::Number(limit as f64);
            }
        }
        false
    })
}

/// `isConstEnumObjectType` (checker.go:28198). Free function in Go.
/// PORT(note): `crate::utilities::is_const_enum_object_type` also exists for
/// other modules; this mirrors the Go definition that lives in checker.go.
fn is_const_enum_object_type(c: &Checker, t: TypeId) -> bool {
    c.types.get(t).object_flags.intersects(ObjectFlags::ANONYMOUS)
        && c.types.get(t).symbol.is_some_and(|s| is_const_enum_symbol(c, s))
}

/// `isConstEnumSymbol` (checker.go:28202). Free function in Go.
pub(crate) fn is_const_enum_symbol(c: &Checker, symbol: SymbolId) -> bool {
    c.sym(symbol).flags.intersects(ast::SymbolFlags::CONST_ENUM)
}

/// `compareTypesEqual` (checker.go:28233). Free function in Go.
/// Go compares `*Type` pointers; canonicalized `TypeId` equality is the
/// port's equivalent.
fn compare_types_equal(s: TypeId, t: TypeId) -> Ternary {
    if s == t {
        return Ternary::TRUE;
    }
    Ternary::FALSE
}

/// `isRestParameter` (checker.go:28326). Free function in Go; mirrors
/// `crate::utilities::is_rest_parameter`.
fn is_rest_parameter(c: &Checker, param: NodeId) -> bool {
    let nodes = c.program_nodes(param);
    nodes[param]
        .as_parameter_declaration()
        .dot_dot_dot_token
        .is_some()
}

/// `getNameFromIndexInfo` (checker.go:28330). Free function in Go.
fn get_name_from_index_info(c: &Checker, info: IndexInfoId) -> String {
    if let Some(declaration) = c.index_info_arena.get(info).declaration {
        let nodes = c.program_nodes(declaration);
        if let Some(first_param) = nodes[declaration].parameters().and_then(|p| p.first()) {
            if let Some(name) = nodes[*first_param].name() {
                return tsc_scanner::utilities::declaration_name_to_string(name, &nodes);
            }
        }
    }
    "x".to_string()
}

impl Checker {
    /// `(c *Checker) markPropertyAsReferenced` (checker.go:28240).
    pub(crate) fn mark_property_as_referenced(
        &mut self,
        prop: SymbolId,
        node_for_check_write_only: Option<NodeId>,
        is_self_type_access: bool,
    ) {
        let (flags, value_declaration, check_flags) = {
            let sym = self.sym(prop);
            (sym.flags, sym.value_declaration, sym.check_flags)
        };
        if !flags.intersects(ast::SymbolFlags::CLASS_MEMBER) || value_declaration.is_none() {
            return;
        }
        let value_declaration = value_declaration.unwrap();
        let decl_nodes = self.program_nodes(value_declaration);
        let has_private_modifier =
            ast::has_modifier(&decl_nodes[value_declaration], ast::ModifierFlags::PRIVATE);
        let has_private_identifier = decl_nodes[value_declaration]
            .name()
            .is_some_and(|n| ast::is_private_identifier(&decl_nodes[n]));
        if !has_private_modifier && !has_private_identifier {
            return;
        }
        if let Some(node) = node_for_check_write_only {
            let nodes = self.program_nodes(node);
            if ast::is_write_only_access(node, &nodes)
                && !flags.intersects(ast::SymbolFlags::SET_ACCESSOR)
            {
                return;
            }
        }
        if is_self_type_access {
            // Find any FunctionLikeDeclaration because those create a new 'this' binding. But this should only matter for methods (or getters/setters).
            let nodes = node_for_check_write_only.map(|n| self.program_nodes(n));
            let containing_method = ast::find_ancestor(
                node_for_check_write_only,
                nodes.as_deref().unwrap_or(&[]),
                &mut |n, nodes| ast::is_function_like_declaration(Some(n.id), nodes),
            );
            if containing_method.is_some_and(|m| {
                self.program_nodes(m)[m].symbol() == Some(prop)
            }) {
                return;
            }
        }
        let mut target = prop;
        if check_flags.intersects(CheckFlags::INSTANTIATED) {
            if let Some(t) = self.value_symbol_links.get(prop).target {
                target = t;
            }
        }
        self.symbol_reference_links
            .get(target)
            .reference_kinds |= ast::SymbolFlags::ALL;
    }

    /// `(c *Checker) expandSignatureParametersWithTupleMembers` (checker.go:28266).
    /// Go `*TypeReference` → `TypeId` (the tuple type reference).
    pub(crate) fn expand_signature_parameters_with_tuple_members(
        &mut self,
        signature: SignatureId,
        rest_type: TypeId,
        rest_index: usize,
        rest_symbol: Option<SymbolId>,
    ) -> Vec<SymbolId> {
        let element_types = self.get_type_arguments(rest_type);
        let element_infos = self
            .types
            .get(self.types.target_tuple_type(rest_type).unwrap())
            .as_tuple_type()
            .element_infos
            .clone();
        let associated_names =
            self.get_uniq_associated_names_from_tuple_type(rest_type, rest_symbol);
        let mut expanded: Vec<SymbolId> = self.signature_arena.get(signature).parameters
            [..rest_index.min(self.signature_arena.get(signature).parameters.len())]
            .to_vec();
        for (i, &t) in element_types.iter().enumerate() {
            let flags = element_infos[i].flags;
            let check_flags = if flags.intersects(ElementFlags::VARIABLE) {
                CheckFlags::REST_PARAMETER
            } else if flags.intersects(ElementFlags::OPTIONAL) {
                CheckFlags::OPTIONAL_PARAMETER
            } else {
                CheckFlags::NONE
            };
            let symbol = self.new_symbol_ex(
                ast::SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                &associated_names[i],
                check_flags,
            );
            let links = self.value_symbol_links.get(symbol);
            if flags.intersects(ElementFlags::REST) {
                let array_type = self.create_array_type(t);
                links.resolved_type = Some(array_type);
            } else {
                links.resolved_type = Some(t);
            }
            expanded.push(symbol);
        }
        expanded
    }

    /// `(c *Checker) getUniqAssociatedNamesFromTupleType` (checker.go:28292).
    pub(crate) fn get_uniq_associated_names_from_tuple_type(
        &mut self,
        t: TypeId,
        rest_symbol: Option<SymbolId>,
    ) -> Vec<String> {
        let element_infos = self
            .types
            .get(self.types.target_tuple_type(t).unwrap())
            .as_tuple_type()
            .element_infos
            .clone();
        let mut names = vec![String::new(); element_infos.len()];
        let mut counters: FxHashMap<String, i32> = FxHashMap::default();
        for (i, info) in element_infos.iter().enumerate() {
            names[i] = self.get_tuple_element_label(*info, rest_symbol, i);
            // count duplicates using negative values
            *counters.entry(names[i].clone()).or_insert(0) -= 1;
        }
        for (i, name) in names.iter().enumerate() {
            if counters[name.as_str()] == -1 {
                continue;
            }
            loop {
                let mut counter = *counters.get(name.as_str()).unwrap_or(&0);
                if counter < 0 {
                    // switch to a positive suffix counter
                    counter = 0;
                }
                counter += 1;
                counters.insert(name.clone(), counter);
                let candidate_name = format!("{}_{}", name, counter);
                if counters.get(&candidate_name).copied().unwrap_or(0) == 0 {
                    names[i] = candidate_name;
                    break;
                }
            }
        }
        names
    }

    /// `(c *Checker) isUnknownLikeUnionType` (checker.go:28337).
    pub(crate) fn is_unknown_like_union_type(&mut self, t: TypeId) -> bool {
        if self.strict_null_checks
            && self.types.get(t).flags.intersects(TypeFlags::UNION)
        {
            if !self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED)
            {
                self.types.get_mut(t).object_flags |=
                    ObjectFlags::IS_UNKNOWN_LIKE_UNION_COMPUTED;
                let types = self.types.get(t).types().to_vec();
                if types.len() >= 3
                    && self
                        .types
                        .get(types[0])
                        .flags
                        .intersects(TypeFlags::UNDEFINED)
                    && self.types.get(types[1]).flags.intersects(TypeFlags::NULL)
                    && types.iter().any(|&m| self.is_empty_anonymous_object_type(m))
                {
                    self.types.get_mut(t).object_flags |=
                        ObjectFlags::IS_UNKNOWN_LIKE_UNION;
                }
            }
            return self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::IS_UNKNOWN_LIKE_UNION);
        }
        false
    }

    /// `(c *Checker) isUniformUnionType` (checker.go:28354).
    /// Return true the given type is a primitive union type where no two literal type constituents are
    /// comparable. Specifically, that means (a) the union doesn't contain literals from different enum
    /// types, and (b) the union doesn't contain both enum literals and string or number literals.
    pub(crate) fn is_uniform_union_type(&mut self, t: TypeId) -> bool {
        if self
            .types
            .get(t)
            .object_flags
            .intersects(ObjectFlags::PRIMITIVE_UNION)
        {
            if !self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::IS_UNIFORM_ENUM_COMPUTED)
            {
                let types = self.types.get(t).types().to_vec();
                let uniform = self.compute_is_uniform_union_type(&types);
                let ty = self.types.get_mut(t);
                ty.object_flags |= ObjectFlags::IS_UNIFORM_ENUM_COMPUTED
                    | if uniform {
                        ObjectFlags::IS_UNIFORM_ENUM
                    } else {
                        ObjectFlags::NONE
                    };
            }
            return self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::IS_UNIFORM_ENUM);
        }
        false
    }

    /// `(c *Checker) computeIsUniformUnionType` (checker.go:28364).
    pub(crate) fn compute_is_uniform_union_type(&mut self, types: &[TypeId]) -> bool {
        let mut enum_symbol: Option<SymbolId> = None;
        let mut has_string_or_number_literal = false;
        for &t in types {
            let flags = self.types.get(t).flags;
            if flags.intersects(TypeFlags::ENUM_LIKE) {
                if has_string_or_number_literal {
                    return false;
                }
                let parent = self
                    .types
                    .get(t)
                    .symbol
                    .and_then(|s| self.get_parent_of_symbol(s));
                if enum_symbol.is_none() {
                    enum_symbol = parent;
                } else if enum_symbol != parent {
                    return false;
                }
            } else if flags.intersects(TypeFlags::STRING_OR_NUMBER_LITERAL) {
                if enum_symbol.is_some() {
                    return false;
                }
                has_string_or_number_literal = true;
            }
        }
        true
    }

    /// `(c *Checker) containsUndefinedType` (checker.go:28388).
    pub(crate) fn contains_undefined_type(&mut self, t: TypeId) -> bool {
        let mut t = t;
        if self.types.get(t).flags.intersects(TypeFlags::UNION) {
            t = self.types.get(t).types().to_vec()[0];
        }
        self.types.get(t).flags.intersects(TypeFlags::UNDEFINED)
    }

    /// `(c *Checker) typeHasCallOrConstructSignatures` (checker.go:28395).
    pub(crate) fn type_has_call_or_construct_signatures(&mut self, t: TypeId) -> bool {
        if !self
            .types
            .get(t)
            .flags
            .intersects(TypeFlags::STRUCTURED_TYPE)
        {
            return false;
        }
        let resolved = self.resolve_structured_type_members(t);
        self.types
            .get(resolved)
            .as_structured_type()
            .is_some_and(|r| !r.signatures.is_empty())
    }

    /// `(c *Checker) getNormalizedType` (checker.go:28399).
    pub(crate) fn get_normalized_type(&mut self, t: TypeId, writing: bool) -> TypeId {
        let mut t = t;
        loop {
            let n;
            if is_fresh_literal_type(&self.types, t) {
                n = self.types.get(t).as_literal_type().regular_type;
            } else if self.is_generic_tuple_type(t) {
                n = self.get_normalized_tuple_type(t, writing);
            } else if self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::REFERENCE)
            {
                if self.types.get(t).as_type_reference().node.is_some() {
                    let target = self.types.target(t).unwrap();
                    let type_arguments = self.get_type_arguments(t);
                    n = self.create_type_reference(target, &type_arguments);
                } else {
                    n = self.get_single_base_for_non_augmenting_subtype(t).unwrap_or(t);
                }
            } else if self
                .types
                .get(t)
                .flags
                .intersects(TypeFlags::UNION_OR_INTERSECTION)
            {
                n = self.get_normalized_union_or_intersection_type(t, writing);
            } else if self.types.get(t).flags.intersects(TypeFlags::SUBSTITUTION) {
                if writing {
                    n = self.types.get(t).as_substitution_type().base_type.unwrap();
                } else {
                    n = self.get_substitution_intersection(t);
                }
            } else if self.types.get(t).flags.intersects(TypeFlags::SIMPLIFIABLE) {
                n = self.get_simplified_type(t, writing);
            } else {
                return t;
            }
            if n == t {
                return n;
            }
            t = n;
        }
    }

    /// `(c *Checker) getSimplifiedType` (checker.go:28436).
    pub(crate) fn get_simplified_type(&mut self, t: TypeId, writing: bool) -> TypeId {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::INDEXED_ACCESS) {
            return self.get_simplified_indexed_access_type(t, writing);
        }
        if flags.intersects(TypeFlags::CONDITIONAL) {
            return self.get_simplified_conditional_type(t, writing);
        }
        t
    }

    /// `(c *Checker) getSimplifiedIndexedAccessType` (checker.go:28449).
    /// Transform an indexed access to a simpler form, if possible. Return the simpler form, or return
    /// the type itself if no transformation is possible. The writing flag indicates that the type is
    /// the target of an assignment.
    pub(crate) fn get_simplified_indexed_access_type(
        &mut self,
        t: TypeId,
        writing: bool,
    ) -> TypeId {
        let key = CachedTypeKey {
            kind: if writing {
                CachedTypeKind::IndexedAccessForWriting
            } else {
                CachedTypeKind::IndexedAccessForReading
            },
            type_id: t,
        };
        if let Some(&cached) = self.cached_types.get(&key) {
            return if cached == self.circular_constraint_type {
                t
            } else {
                cached
            };
        }
        self.cached_types.insert(key, t);
        let mut result = self.get_simplified_indexed_access_type_worker(t, writing);
        if result != t {
            // If the simplification is a union type that includes t, remove t from the type.
            result = self.remove_type(result, t);
            self.cached_types.insert(key, result);
        }
        result
    }

    /// `(c *Checker) getSimplifiedIndexedAccessTypeWorker` (checker.go:28464).
    pub(crate) fn get_simplified_indexed_access_type_worker(
        &mut self,
        t: TypeId,
        writing: bool,
    ) -> TypeId {
        // We recursively simplify the object type as it may in turn be an indexed access type. For example, with
        // '{ [P in T]: { [Q in U]: number } }[T][U]' we want to first simplify the inner indexed access type.
        let (object_type, index_type) = {
            let iat = self.types.get(t).as_indexed_access_type();
            (iat.object_type.unwrap(), iat.index_type.unwrap())
        };
        let object_type = self.get_simplified_type(object_type, writing);
        let index_type = self.get_simplified_type(index_type, writing);
        // T[A | B] -> T[A] | T[B] (reading)
        // T[A | B] -> T[A] & T[B] (writing)
        if let Some(distributed) =
            self.distribute_object_over_index_type(object_type, index_type, writing)
        {
            return distributed;
        }
        // Only do the inner distributions if the index can no longer be instantiated to cause index distribution again
        if !self
            .types
            .get(index_type)
            .flags
            .intersects(TypeFlags::INSTANTIABLE)
        {
            // (T | U)[K] -> T[K] | U[K] (reading)
            // (T | U)[K] -> T[K] & U[K] (writing)
            // (T & U)[K] -> T[K] & U[K]
            if let Some(distributed) =
                self.distribute_index_over_object_type(object_type, index_type, writing)
            {
                return distributed;
            }
        }
        // So ultimately (reading):
        // ((A & B) | C)[K1 | K2] -> ((A & B) | C)[K1] | ((A & B) | C)[K2] -> (A & B)[K1] | C[K1] | (A & B)[K2] | C[K2] -> (A[K1] & B[K1]) | C[K1] | (A[K2] & B[K2]) | C[K2]
        // A generic tuple type indexed by a number exists only when the index type doesn't select a
        // fixed element. We simplify to either the combined type of all elements (when the index type
        // the actual number type) or to the combined type of all non-fixed elements.
        if self.is_generic_tuple_type(object_type)
            && self
                .types
                .get(index_type)
                .flags
                .intersects(TypeFlags::NUMBER_LIKE)
        {
            let index = if self
                .types
                .get(index_type)
                .flags
                .intersects(TypeFlags::NUMBER)
            {
                0
            } else {
                self.types
                    .get(self.types.target_tuple_type(object_type).unwrap())
                    .as_tuple_type()
                    .fixed_length
            };
            if let Some(element_type) = self.get_element_type_of_slice_of_tuple_type(
                object_type,
                index,
                0, /*endSkipCount*/
                writing,
                false,
            ) {
                return element_type;
            }
        }
        // If the object type is a mapped type { [P in K]: E }, where K is generic, or { [P in K as N]: E }, where
        // K is generic and N is assignable to P, instantiate E using a mapper that substitutes the index type for P.
        // For example, for an index access { [P in K]: Box<T[P]> }[X], we construct the type Box<T[X]>.
        if self.is_generic_mapped_type(object_type) {
            if self.get_mapped_type_name_type_kind(object_type)
                != MappedTypeNameTypeKind::Remapping
            {
                let substituted =
                    self.substitute_indexed_mapped_type(object_type, index_type);
                return self.map_type(
                    substituted,
                    Rc::new(move |c: &mut Checker, t: TypeId| -> TypeId {
                        c.get_simplified_type(t, writing)
                    }),
                );
            }
        }
        t
    }

    /// `(c *Checker) distributeObjectOverIndexType` (checker.go:28509).
    pub(crate) fn distribute_object_over_index_type(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
        writing: bool,
    ) -> Option<TypeId> {
        // T[A | B] -> T[A] | T[B] (reading)
        // T[A | B] -> T[A] & T[B] (writing)
        if self.types.get(index_type).flags.intersects(TypeFlags::UNION) {
            let types: Vec<TypeId> = self.types.get(index_type).types()
                .to_vec()
                .iter()
                .map(|&t| {
                    let indexed = self.get_indexed_access_type(object_type, t);
                    self.get_simplified_type(indexed, writing)
                })
                .collect();
            if writing {
                return Some(self.get_intersection_type(&types));
            }
            return Some(self.get_union_type(&types));
        }
        None
    }

    /// `(c *Checker) distributeIndexOverObjectType` (checker.go:28524).
    pub(crate) fn distribute_index_over_object_type(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
        writing: bool,
    ) -> Option<TypeId> {
        // (T | U)[K] -> T[K] | U[K] (reading)
        // (T | U)[K] -> T[K] & U[K] (writing)
        // (T & U)[K] -> T[K] & U[K]
        let object_flags = self.types.get(object_type).flags;
        if object_flags.intersects(TypeFlags::UNION)
            || object_flags.intersects(TypeFlags::INTERSECTION)
                && !self.should_defer_index_type(object_type, IndexFlags::NONE)
        {
            let types: Vec<TypeId> = self.types.get(object_type).types()
                .to_vec()
                .iter()
                .map(|&t| {
                    let indexed = self.get_indexed_access_type(t, index_type);
                    self.get_simplified_type(indexed, writing)
                })
                .collect();
            if object_flags.intersects(TypeFlags::INTERSECTION) || writing {
                return Some(self.get_intersection_type(&types));
            }
            return Some(self.get_union_type(&types));
        }
        None
    }

    /// `(c *Checker) getSimplifiedConditionalType` (checker.go:28540).
    pub(crate) fn get_simplified_conditional_type(
        &mut self,
        t: TypeId,
        writing: bool,
    ) -> TypeId {
        let (check_type, extends_type) = {
            let cond = self.types.get(t).as_conditional_type();
            (cond.check_type.unwrap(), cond.extends_type.unwrap())
        };
        let true_type = self.get_true_type_from_conditional_type(t);
        let false_type = self.get_false_type_from_conditional_type(t);
        // Simplifications for types of the form `T extends U ? T : never` and `T extends U ? never : T`.
        if self.types.get(false_type).flags.intersects(TypeFlags::NEVER)
            && self.get_actual_type_variable(true_type) == self.get_actual_type_variable(check_type)
        {
            let restrictive_check = self.get_restrictive_instantiation(check_type);
            let restrictive_extends = self.get_restrictive_instantiation(extends_type);
            if self.types.get(check_type).flags.intersects(TypeFlags::ANY)
                || self.is_type_assignable_to(restrictive_check, restrictive_extends)
            {
                return self.get_simplified_type(true_type, writing);
            } else if self.is_intersection_empty(check_type, extends_type) {
                return self.never_type;
            }
        } else if self.types.get(true_type).flags.intersects(TypeFlags::NEVER)
            && self.get_actual_type_variable(false_type)
                == self.get_actual_type_variable(check_type)
        {
            let restrictive_check = self.get_restrictive_instantiation(check_type);
            let restrictive_extends = self.get_restrictive_instantiation(extends_type);
            if !self.types.get(check_type).flags.intersects(TypeFlags::ANY)
                && self.is_type_assignable_to(restrictive_check, restrictive_extends)
            {
                return self.never_type;
            } else if self.types.get(check_type).flags.intersects(TypeFlags::ANY)
                || self.is_intersection_empty(check_type, extends_type)
            {
                return self.get_simplified_type(false_type, writing);
            }
        }
        t
    }

    /// `(c *Checker) isIntersectionEmpty` (checker.go:28563).
    /// Invokes union simplification logic to determine if an intersection is considered empty as a union constituent
    pub(crate) fn is_intersection_empty(&mut self, type1: TypeId, type2: TypeId) -> bool {
        let intersection = self
            .intersect_types(Some(type1), Some(type2))
            .unwrap_or(self.never_type);
        let union = self.get_union_type(&[intersection, self.never_type]);
        self.types.get(union).flags.intersects(TypeFlags::NEVER)
    }

    /// `(c *Checker) getSimplifiedTypeOrConstraint` (checker.go:28567).
    pub(crate) fn get_simplified_type_or_constraint(&mut self, t: TypeId) -> Option<TypeId> {
        let simplified = self.get_simplified_type(t, false /*writing*/);
        if simplified != t {
            return Some(simplified);
        }
        self.get_constraint_of_type(t)
    }

    /// `(c *Checker) getNormalizedUnionOrIntersectionType` (checker.go:28574).
    pub(crate) fn get_normalized_union_or_intersection_type(
        &mut self,
        t: TypeId,
        writing: bool,
    ) -> TypeId {
        let reduced = self.get_reduced_type(t);
        if reduced != t {
            return reduced;
        }
        if self.types.get(t).flags.intersects(TypeFlags::INTERSECTION)
            && self.should_normalize_intersection(t)
        {
            // Normalization handles cases like
            // Partial<T>[K] & ({} | null) ==>
            // Partial<T>[K] & {} | Partial<T>[K} & null ==>
            // (T[K] | undefined) & {} | (T[K] | undefined) & null ==>
            // T[K] & {} | undefined & {} | T[K] & null | undefined & null ==>
            // T[K] & {} | T[K] & null
            let types = self.types.get(t).types().to_vec();
            let normalized_types: Vec<TypeId> = types
                .iter()
                .map(|&u| self.get_normalized_type(u, writing))
                .collect();
            if normalized_types != types {
                return self.get_intersection_type(&normalized_types);
            }
        }
        t
    }

    /// `(c *Checker) shouldNormalizeIntersection` (checker.go:28594).
    pub(crate) fn should_normalize_intersection(&mut self, t: TypeId) -> bool {
        let mut has_instantiable = false;
        let mut has_nullable_or_empty = false;
        for &t in &self.types.get(t).types().to_vec() {
            has_instantiable = has_instantiable
                || self.types.get(t).flags.intersects(TypeFlags::INSTANTIABLE);
            has_nullable_or_empty = has_nullable_or_empty
                || self.types.get(t).flags.intersects(TypeFlags::NULLABLE)
                || self.is_empty_anonymous_object_type(t);
            if has_instantiable && has_nullable_or_empty {
                return true;
            }
        }
        false
    }

    /// `(c *Checker) getNormalizedTupleType` (checker.go:28607).
    pub(crate) fn get_normalized_tuple_type(&mut self, t: TypeId, writing: bool) -> TypeId {
        let elements = self.get_element_types(t);
        let normalized_elements: Vec<TypeId> = elements
            .iter()
            .map(|&t| {
                if self.types.get(t).flags.intersects(TypeFlags::SIMPLIFIABLE) {
                    self.get_simplified_type(t, writing)
                } else {
                    t
                }
            })
            .collect();
        if normalized_elements != elements {
            let target = self.types.target(t).unwrap();
            return self.create_normalized_tuple_type(target, &normalized_elements);
        }
        t
    }

    /// `(c *Checker) getSingleBaseForNonAugmentingSubtype` (checker.go:28621).
    pub(crate) fn get_single_base_for_non_augmenting_subtype(
        &mut self,
        t: TypeId,
    ) -> Option<TypeId> {
        if !self
            .types
            .get(t)
            .object_flags
            .intersects(ObjectFlags::REFERENCE)
            || !self
                .types
                .get(self.types.target(t).unwrap())
                .object_flags
                .intersects(ObjectFlags::CLASS_OR_INTERFACE)
        {
            return None;
        }
        let key = CachedTypeKey {
            kind: CachedTypeKind::EquivalentBaseType,
            type_id: t,
        };
        if self
            .types
            .get(t)
            .object_flags
            .intersects(ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED)
        {
            return self.cached_types.get(&key).copied();
        }
        self.types.get_mut(t).object_flags |= ObjectFlags::IDENTICAL_BASE_TYPE_CALCULATED;
        let target = self.types.target(t).unwrap();
        if self
            .types
            .get(target)
            .object_flags
            .intersects(ObjectFlags::CLASS)
        {
            let base_type_node = crate::utilities::get_base_type_node_of_class(target);
            // A base type expression may circularly reference the class itself (e.g. as an argument to function call), so we only
            // check for base types specified as simple qualified names.
            if let Some(base_type_node) = base_type_node {
                let nodes = self.program_nodes(base_type_node);
                if let Some(expression) = nodes[base_type_node].expression() {
                    if !ast::is_identifier(&nodes[expression])
                        && !ast::is_property_access_expression(&nodes[expression])
                    {
                        return None;
                    }
                }
            }
        }
        let bases = self.get_base_types(target);
        if bases.len() != 1 {
            return None;
        }
        if let Some(symbol) = self.types.get(t).symbol {
            if !self.get_members_of_symbol(symbol).is_empty() {
                // If the interface has any members, they may subtype members in the base, so we should do a full structural comparison
                return None;
            }
        }
        let type_parameters = self
            .types
            .get(target)
            .as_interface_type()
            .type_parameters()
            .to_vec();
        let mut instantiated_base;
        if type_parameters.is_empty() {
            instantiated_base = bases[0];
        } else {
            let type_arguments = self.get_type_arguments(t);
            let mapper = crate::mapper::new_type_mapper(
                self,
                type_parameters,
                type_arguments[..type_parameters.len()].to_vec(),
            );
            instantiated_base = self.instantiate_type(bases[0], Some(mapper));
        }
        let type_arguments = self.get_type_arguments(t);
        if type_arguments.len() > type_parameters.len() {
            instantiated_base = self.get_type_with_this_argument(
                instantiated_base,
                type_arguments.last().copied(),
                false,
            );
        }
        self.cached_types.insert(key, instantiated_base);
        Some(instantiated_base)
    }

    /// `(c *Checker) extractTypesOfKind` (checker.go:28689).
    pub(crate) fn extract_types_of_kind(&mut self, t: TypeId, kind: TypeFlags) -> TypeId {
        self.filter_type(t, move |c: &mut Checker, t: TypeId| {
            c.types.get(t).flags.intersects(kind)
        })
    }

    /// `(c *Checker) getRegularTypeOfObjectLiteral` (checker.go:28693).
    pub(crate) fn get_regular_type_of_object_literal(&mut self, t: TypeId) -> TypeId {
        if !(crate::utilities::is_object_literal_type(&self.types, t)
            && self
                .types
                .get(t)
                .object_flags
                .intersects(ObjectFlags::FRESH_LITERAL))
        {
            return t;
        }
        let key = CachedTypeKey {
            kind: CachedTypeKind::RegularObjectLiteral,
            type_id: t,
        };
        if let Some(&cached) = self.cached_types.get(&key) {
            return cached;
        }
        let resolved = self.resolve_structured_type_members(t);
        let members = self.transform_type_of_members(t, &mut |c: &mut Checker, t: TypeId| {
            c.get_regular_type_of_object_literal(t)
        });
        let symbol = self.types.get(t).symbol;
        let regular = self.new_anonymous_type(
            symbol,
            members,
            resolved.call_signatures(),
            resolved.construct_signatures(),
            resolved.index_infos(),
        );
        {
            let resolved_flags = resolved.flags();
            let resolved_object_flags = resolved.object_flags();
            let ty = self.types.get_mut(regular);
            ty.flags = resolved_flags;
            ty.object_flags |= resolved_object_flags.without(ObjectFlags::FRESH_LITERAL);
        }
        self.cached_types.insert(key, regular);
        regular
    }

    /// `(c *Checker) transformTypeOfMembers` (checker.go:28710).
    /// Go `f func(propertyType *Type) *Type` → `&mut dyn FnMut(&mut Checker, TypeId) -> TypeId`.
    pub(crate) fn transform_type_of_members(
        &mut self,
        t: TypeId,
        f: &mut dyn FnMut(&mut Checker, TypeId) -> TypeId,
    ) -> SymbolTable {
        let mut members = SymbolTable::default();
        for property in self.get_properties_of_object_type(t) {
            let original = self.get_type_of_symbol(property);
            let updated = f(self, original);
            let property = if updated != original {
                self.create_symbol_with_type(property, updated)
            } else {
                property
            };
            let name = self.sym(property).name.clone();
            members.set(name, property);
        }
        members
    }
}

impl Checker {
    /// `(c *Checker) markLinkedReferences` (checker.go:28723).
    pub(crate) fn mark_linked_references(
        &mut self,
        location: NodeId,
        hint: ReferenceHint,
        prop_symbol: Option<SymbolId>,
        parent_type: Option<TypeId>,
    ) {
        if !self.can_collect_symbol_alias_accessibility_data {
            return;
        }
        let nodes = self.program_nodes(location);
        if nodes[location].flags.intersects(ast::NodeFlags::AMBIENT)
            && !ast::is_property_signature_declaration(&nodes[location])
            && !ast::is_property_declaration(&nodes[location])
        {
            // References within types and declaration files are never going to contribute to retaining a JS import,
            // except for properties (which can be decorated).
            return;
        }
        match hint {
            ReferenceHint::Identifier => {
                self.mark_identifier_alias_referenced(location);
            }
            ReferenceHint::Property => {
                self.mark_property_alias_referenced(location, prop_symbol, parent_type);
            }
            ReferenceHint::ExportAssignment => {
                self.mark_export_assignment_alias_referenced(location);
            }
            ReferenceHint::Jsx => {
                self.mark_jsx_alias_referenced(location);
            }
            ReferenceHint::ExportImportEquals => {
                self.mark_import_equals_alias_referenced(location);
            }
            ReferenceHint::ExportSpecifier => {
                self.mark_export_specifier_alias_referenced(location);
            }
            ReferenceHint::Decorator => {
                self.mark_decorator_alias_referenced(location);
            }
            ReferenceHint::Unspecified => {
                if nodes[location]
                    .flags
                    .intersects(ast::NodeFlags::IN_WITH_STATEMENT)
                {
                    // We cannot answer semantic questions within a with block, do not proceed any further
                    return;
                }
                if ast::is_jsx_tag_name(location, &nodes)
                    && crate::utilities::is_jsx_intrinsic_tag_name(location, &nodes)
                {
                    // builtin JSX tag names aren't real type refs by most metrics, but are expressions, so must be filtered
                    return;
                }
                if ast::is_identifier(&nodes[location]) {
                    // A shorthand property with an object-assignment-initializer (e.g. `{ s = 5 }`) is only valid inside a
                    // destructuring assignment target. When it appears in an ordinary object literal expression, the checker
                    // checks the initializer and never resolves the property name, so resolving it here would report a spurious
                    // "No value exists in scope for the shorthand property" diagnostic. Skip such names to match checking.
                    if let Some(parent) = nodes[location].parent {
                        if ast::is_shorthand_property_assignment(&nodes[parent])
                            && nodes[parent].name() == Some(location)
                            && nodes[parent]
                                .as_shorthand_property_assignment()
                                .object_assignment_initializer
                                .is_some()
                            && !nodes[parent]
                                .parent
                                .is_some_and(|gp| ast::is_assignment_target(gp, &nodes))
                        {
                            return;
                        }
                    }
                    let res = ast::find_many_ancestors(
                        Some(location),
                        &nodes,
                        &mut [
                            &mut |n: &ast::Node| ast::is_meta_property(n),
                            &mut |n: &ast::Node| ast::is_decorator(n),
                            &mut |n: &ast::Node| {
                                ast::is_for_in_or_of_statement(Some(n.id), &nodes)
                            },
                            &mut |n: &ast::Node| ast::is_computed_property_name(n),
                            &mut |n: &ast::Node| ast::is_heritage_clause(n),
                        ],
                    );
                    let meta_property = res[0];
                    let decorator = res[1];
                    let for_node = res[2];
                    let computed_name = res[3];
                    let heritage_clause = res[4];
                    if meta_property.is_some() {
                        // identifiers in meta properties shouldn't be resolved, but are expressions, so must be filtered
                        return;
                    }
                    if let Some(decorator) = decorator {
                        // Decorators on nodes that cannot be decorated (e.g. class expressions, static blocks,
                        // `this` parameters) are never resolved during normal checking, so resolving them here would
                        // report spurious diagnostics. Only bail out for such invalid-position decorators; valid
                        // decorator expressions must still be resolved and marked for emit.
                        if let Some(decorated) = nodes[decorator].parent {
                            let decorated_parent = nodes[decorated].parent;
                            let decorated_grandparent =
                                decorated_parent.and_then(|p| nodes[p].parent);
                            if !ast::node_can_be_decorated(
                                self.legacy_decorators,
                                decorated,
                                decorated_parent,
                                decorated_grandparent,
                                &nodes,
                            ) {
                                return;
                            }
                        }
                    }
                    // The right-hand side of a 'for-in'/'for-of' statement whose initializer is an empty variable
                    // declaration list (a grammar error, e.g. `for (var of X)`) is never checked, because the RHS
                    // is only checked while inferring the type of a variable declaration and there is none here.
                    // Resolving identifiers in the RHS here would report spurious diagnostics.
                    if let Some(for_node) = for_node {
                        let data = nodes[for_node].as_for_in_or_of_statement();
                        let initializer = data.initializer;
                        if initializer.is_some_and(|i| {
                            nodes[i].kind == ast::Kind::VariableDeclarationList
                        }) && initializer
                            .map(|i| {
                                nodes[i]
                                    .as_variable_declaration_list()
                                    .declarations
                                    .nodes
                                    .is_empty()
                            })
                            .unwrap_or(false)
                            && data.expression.is_some()
                            && (Some(location) == data.expression
                                || ast::is_node_descendant_of(
                                    Some(location),
                                    data.expression,
                                    &nodes,
                                ))
                        {
                            return;
                        }
                    }
                    if let Some(computed_name) = computed_name {
                        if is_invalid_computed_property_name(self, computed_name) {
                            return;
                        }
                    }
                    if let Some(heritage_clause) = heritage_clause {
                        let heritage_parent = nodes[heritage_clause].parent;
                        // extends heritage clauses on interfaces are not expressions and are unchecked if they are
                        if heritage_parent.is_some_and(|p| {
                            ast::is_interface_declaration(&nodes[p])
                        }) {
                            return;
                        }
                        // On a class, only the first `extends` type is resolved as a value (the base class); any
                        // additional `extends` types are grammar errors (e.g. `class C extends A extends B` or
                        // `class C extends A, B`) and are never resolved during checking.
                        if heritage_parent.is_some_and(|p| ast::is_class_like(Some(p), &nodes))
                            && nodes[heritage_clause].as_heritage_clause().token
                                == ast::Kind::ExtendsKeyword
                        {
                            if let Some(first_extends) = ast::get_class_extends_heritage_element(
                                &nodes[heritage_parent.unwrap()],
                                &nodes,
                            ) {
                                if location != first_extends
                                    && !ast::is_node_descendant_of(
                                        Some(location),
                                        Some(first_extends),
                                        &nodes,
                                    )
                                {
                                    return;
                                }
                            }
                        }
                    }
                    // Identifiers in expression contexts are emitted, so we need to follow their referenced aliases and mark them as used
                    // Some non-expression identifiers are also treated as expression identifiers for this purpose, eg, `a` in `b = {a}` or `q` in `import r = q`
                    // This is the exception, rather than the rule - most non-expression identifiers are declaration names.
                    if (ast::is_expression_node(location, &nodes)
                        || nodes[location].parent.is_some_and(|p| {
                            ast::is_shorthand_property_assignment(&nodes[p])
                        }))
                        && should_mark_identifier_alias_referenced(&nodes, location)
                    {
                        if let Some(parent) = nodes[location].parent {
                            if ast::is_property_access_or_qualified_name(&nodes[parent]) {
                                let left = if ast::is_property_access_expression(&nodes[parent]) {
                                    nodes[parent].expression()
                                } else {
                                    nodes[parent].as_qualified_name().left
                                };
                                if left != Some(location) {
                                    // Only mark the LHS (the RHS is a property lookup)
                                    return;
                                }
                            }
                        }
                        self.mark_identifier_alias_referenced(location);
                        return;
                    }
                }
                if ast::is_property_access_or_qualified_name(&nodes[location]) {
                    let mut top_prop = location;
                    while ast::is_property_access_or_qualified_name(&nodes[top_prop]) {
                        // Names in an import type's qualifier (`ns.y` in `typeof import("./b").ns.y`) are exports of the imported module, not references to this file's imports
                        if ast::is_part_of_type_node(top_prop, &nodes)
                            || crate::utilities::is_import_type_qualifier_part(top_prop, &nodes)
                                .is_some()
                        {
                            return;
                        }
                        match nodes[top_prop].parent {
                            Some(parent) => top_prop = parent,
                            None => break,
                        }
                    }
                    self.mark_property_alias_referenced(location, None, None);
                    return;
                }
                if ast::is_export_assignment(&nodes[location]) {
                    self.mark_export_assignment_alias_referenced(location);
                    return;
                }
                if ast::is_jsx_opening_like_element(&nodes[location])
                    || ast::is_jsx_opening_fragment(&nodes[location])
                {
                    self.mark_jsx_alias_referenced(location);
                    return;
                }
                if ast::is_import_equals_declaration(&nodes[location]) {
                    if is_internal_module_import_equals_declaration(&nodes, location)
                        || self.check_external_import_or_export_declaration(location)
                    {
                        self.mark_import_equals_alias_referenced(location);
                    }
                    return;
                }
                if ast::is_export_specifier(&nodes[location]) {
                    self.mark_export_specifier_alias_referenced(location);
                    return;
                }
                if !self.compiler_options.emit_decorator_metadata.is_true() {
                    return;
                }
                if !ast::can_have_decorators(&nodes[location])
                    || !ast::has_decorators(&nodes[location])
                    || nodes[location].modifiers().is_none()
                    || !ast::node_can_be_decorated(
                        self.legacy_decorators,
                        location,
                        nodes[location].parent,
                        nodes[location].parent.and_then(|p| nodes[p].parent),
                        &nodes,
                    )
                {
                    return;
                }
                self.mark_decorator_alias_referenced(location);
            }
            _ => panic!("Unhandled reference hint"),
        }
    }

    /// `(c *Checker) markIdentifierAliasReferenced` (checker.go:28926).
    pub(crate) fn mark_identifier_alias_referenced(&mut self, location: NodeId) {
        let nodes = self.program_nodes(location);
        if ast::is_this_in_type_query(location, &nodes) {
            return;
        }
        if let Some(symbol) = self.get_resolved_symbol(location) {
            if symbol != self.arguments_symbol && symbol != self.unknown_symbol {
                self.mark_alias_referenced(symbol, location);
            }
        }
    }

    /// `(c *Checker) markPropertyAliasReferenced` (checker.go:28936).
    /// Go location is `PropertyAccessExpression | QualifiedName`.
    pub(crate) fn mark_property_alias_referenced(
        &mut self,
        location: NodeId,
        prop_symbol: Option<SymbolId>,
        parent_type: Option<TypeId>,
    ) {
        let nodes = self.program_nodes(location);
        if is_part_of_import_equals_module_reference(&nodes, location) {
            return;
        }
        let left = if ast::is_property_access_expression(&nodes[location]) {
            nodes[location].expression()
        } else {
            nodes[location].as_qualified_name().left
        };
        let Some(left) = left else {
            return;
        };
        if ast::is_this_identifier(&nodes[left]) || !ast::is_identifier(&nodes[left]) {
            return;
        }
        let Some(parent_symbol) = self.get_resolved_symbol(left) else {
            return;
        };
        if parent_symbol == self.unknown_symbol {
            return;
        }
        // In `Foo.Bar.Baz`, 'Foo' is not referenced if 'Bar' is a const enum or a module containing only const enums.
        // `Foo` is also not referenced in `enum FooCopy { Bar = Foo.Bar }`, because the enum member value gets inlined
        // here even if `Foo` is not a const enum.
        //
        // The exceptions are:
        //   1. if 'isolatedModules' is enabled, because the const enum value will not be inlined, and
        //   2. if 'preserveConstEnums' is enabled and the expression is itself an export, e.g. `export = Foo.Bar.Baz`.
        //
        // The property lookup is deferred as much as possible, in as many situations as possible, to avoid alias marking
        // pulling on types/symbols it doesn't strictly need to.
        if self.compiler_options.get_isolated_modules()
            || (self.compiler_options.should_preserve_const_enums()
                && is_export_or_export_expression(&nodes, location))
        {
            self.mark_alias_referenced(parent_symbol, location);
            return;
        }
        // Hereafter, this relies on type checking - but every check prior to this only used symbol information
        let left_type = match parent_type {
            Some(t) => t,
            None => self.check_expression_cached(left),
        };
        if crate::utilities::is_type_any(&self.types, left_type)
            || left_type == self.silent_never_type
        {
            self.mark_alias_referenced(parent_symbol, location);
            return;
        }
        let mut prop = prop_symbol;
        if prop.is_none() && parent_type.is_none() {
            let right = if ast::is_property_access_expression(&nodes[location]) {
                nodes[location].as_property_access_expression().name
            } else {
                nodes[location].as_qualified_name().right
            };
            let Some(right) = right else {
                self.mark_alias_referenced(parent_symbol, location);
                return;
            };
            let mut lexically_scoped_symbol: Option<SymbolId> = None;
            if ast::is_private_identifier(&nodes[right]) {
                lexically_scoped_symbol = self.lookup_symbol_for_private_identifier_declaration(
                    &nodes[right].text(&nodes),
                    right,
                );
            }
            let assignment_kind =
                crate::utilities::get_assignment_target_kind(location, &nodes);
            let apparent_type = if assignment_kind != crate::utilities::AssignmentKind::NONE
                || self.is_method_access_for_call(location)
            {
                let widened = self.get_widened_type(left_type);
                self.get_apparent_type(widened)
            } else {
                self.get_apparent_type(left_type)
            };
            if ast::is_private_identifier(&nodes[right]) {
                if let Some(lexically_scoped_symbol) = lexically_scoped_symbol {
                    prop = self.get_private_identifier_property_of_type(
                        apparent_type,
                        lexically_scoped_symbol,
                    );
                }
            } else {
                prop = self.get_property_of_type(apparent_type, &nodes[right].text(&nodes));
            }
        }
        if !prop.is_some_and(|prop| {
            crate::utilities::is_const_enum_or_const_enum_only_module(self, prop)
                || self.sym(prop).flags.intersects(ast::SymbolFlags::ENUM_MEMBER)
                    && self
                        .program_nodes(location)[location]
                        .parent
                        .is_some_and(|p| {
                            self.program_nodes(p)[p].kind == ast::Kind::EnumMember
                        })
        }) {
            self.mark_alias_referenced(parent_symbol, location);
        }
    }

    /// `(c *Checker) markExportAssignmentAliasReferenced` (checker.go:29021).
    /// Go location is `ExportAssignment`.
    pub(crate) fn mark_export_assignment_alias_referenced(&mut self, location: NodeId) {
        let nodes = self.program_nodes(location);
        let Some(id) = nodes[location].expression() else {
            return;
        };
        if ast::is_identifier(&nodes[id]) {
            let resolved = self.resolve_entity_name(
                id,
                ast::SymbolFlags::ALL,
                true, /*ignoreErrors*/
                true, /*dontResolveAlias*/
                Some(location),
            );
            if let Some(sym) = self.get_export_symbol_of_value_symbol_if_exported(resolved) {
                self.mark_alias_referenced(sym, id);
            }
        }
    }

    /// `(c *Checker) markJsxAliasReferenced` (checker.go:29031).
    /// Go node is `JsxOpeningLikeElement | JsxOpeningFragment`.
    pub(crate) fn mark_jsx_alias_referenced(&mut self, node: NodeId) {
        if self.get_jsx_namespace_container_for_implicit_import(node).is_some() {
            return;
        }
        // The reactNamespace/jsxFactory's root symbol should be marked as 'used' so we don't incorrectly elide its import.
        // And if there is no reactNamespace/jsxFactory's symbol in scope when targeting React emit, we should issue an error.
        let jsx_factory_ref_err: Option<&'static tsc_diagnostics::Message> =
            if self.compiler_options.jsx == tsc_core::options_generated::JsxEmit::React {
                Some(
                    &tsc_diagnostics::This_JSX_tag_requires_0_to_be_in_scope_but_it_could_not_be_found,
                )
            } else {
                None
            };
        let jsx_factory_namespace = self.get_jsx_namespace(node);
        let nodes = self.program_nodes(node);
        let jsx_factory_location = if ast::is_jsx_opening_like_element(&nodes[node]) {
            nodes[node].tag_name().unwrap_or(node)
        } else {
            node
        };
        let should_factory_ref_err =
            self.compiler_options.jsx != tsc_core::options_generated::JsxEmit::Preserve
                && self.compiler_options.jsx != tsc_core::options_generated::JsxEmit::ReactNative;
        // #38720/60122, allow null as jsxFragmentFactory
        let mut jsx_factory_sym: Option<SymbolId> = None;
        if !(ast::is_jsx_opening_fragment(&nodes[node]) && jsx_factory_namespace == "null") {
            let mut flags = ast::SymbolFlags::VALUE;
            if !should_factory_ref_err {
                flags = flags.without(ast::SymbolFlags::ENUM);
            }
            let resolve_name = self.resolve_name.clone().expect("Checker::resolve_name");
            jsx_factory_sym = resolve_name(
                self,
                Some(jsx_factory_location),
                &jsx_factory_namespace,
                flags,
                jsx_factory_ref_err,
                true,  /*isUse*/
                false, /*excludeGlobals*/
            );
        }
        if let Some(jsx_factory_sym) = jsx_factory_sym {
            // Mark local symbol as referenced here because it might not have been marked
            // if jsx emit was not jsxFactory as there wont be error being emitted
            self.symbol_referenced(jsx_factory_sym, ast::SymbolFlags::ALL);
            // If react/jsxFactory symbol is alias, mark it as referenced
            if self.can_collect_symbol_alias_accessibility_data
                && self.sym(jsx_factory_sym).flags.intersects(ast::SymbolFlags::ALIAS)
                && self.get_type_only_alias_declaration(jsx_factory_sym).is_none()
            {
                self.mark_alias_symbol_as_referenced(jsx_factory_sym);
            }
        }
        // if JsxFragment, additionally mark jsx pragma as referenced, since `getJsxNamespace` above would have resolved to only the fragment factory if they are distinct
        if ast::is_jsx_opening_fragment(&nodes[node]) {
            let file = ast::get_source_file_of_node(Some(node), &nodes);
            if let Some(entity) = file.and_then(|f| self.get_jsx_factory_entity(f)) {
                let entity_nodes = self.program_nodes(entity);
                let first = ast::get_first_identifier(entity, &entity_nodes);
                let local_jsx_namespace = entity_nodes[first].text(&entity_nodes).to_string();
                let mut flags = ast::SymbolFlags::VALUE;
                if !should_factory_ref_err {
                    flags = flags.without(ast::SymbolFlags::ENUM);
                }
                let resolve_name = self.resolve_name.clone().expect("Checker::resolve_name");
                resolve_name(
                    self,
                    Some(jsx_factory_location),
                    &local_jsx_namespace,
                    flags,
                    jsx_factory_ref_err,
                    true,  /*isUse*/
                    false, /*excludeGlobals*/
                );
            }
        }
    }

    /// `(c *Checker) markImportEqualsAliasReferenced` (checker.go:29077).
    /// Go location is `ImportEqualsDeclaration`.
    pub(crate) fn mark_import_equals_alias_referenced(&mut self, location: NodeId) {
        let nodes = self.program_nodes(location);
        if ast::has_syntactic_modifier(&nodes[location], ast::ModifierFlags::EXPORT) {
            self.mark_export_as_referenced(location);
        }
    }

    /// `(c *Checker) markExportSpecifierAliasReferenced` (checker.go:29083).
    /// Go location is `ExportSpecifier`.
    pub(crate) fn mark_export_specifier_alias_referenced(&mut self, location: NodeId) {
        let nodes = self.program_nodes(location);
        let grandparent = nodes[location].parent.and_then(|p| nodes[p].parent);
        if grandparent
            .is_some_and(|gp| nodes[gp].module_specifier().is_none())
            && !nodes[location].is_type_only()
            && !grandparent.is_some_and(|gp| nodes[gp].is_type_only())
        {
            let Some(exported_name) = nodes[location].property_name_or_name() else {
                return;
            };
            if nodes[exported_name].kind == ast::Kind::StringLiteral {
                // Skip for invalid syntax like this: export { "x" }
                return;
            }
            let exported_name_text = nodes[exported_name].text(&nodes).to_string();
            let resolve_name = self.resolve_name.clone().expect("Checker::resolve_name");
            let symbol = resolve_name(
                self,
                Some(exported_name),
                &exported_name_text,
                ast::SymbolFlags::VALUE
                    | ast::SymbolFlags::TYPE
                    | ast::SymbolFlags::NAMESPACE
                    | ast::SymbolFlags::ALIAS,
                None, /*nameNotFoundMessage*/
                true,  /*isUse*/
                false, /*excludeGlobals*/
            );
            if symbol.is_some_and(|symbol| {
                symbol == self.undefined_symbol
                    || symbol == self.global_this_symbol
                    || self.sym(symbol).declarations.first().is_some_and(|&d| {
                        let container = ast::get_declaration_container(d, &self.program_nodes(d));
                        container.is_some_and(|c| {
                            ast::is_global_source_file(&self.program_nodes(c)[c], &self.program_nodes(c))
                        })
                    })
            }) {
                // Do nothing, non-local symbol
            } else {
                let mut target = symbol;
                if target.is_some_and(|t| {
                    self.sym(t).flags.intersects(ast::SymbolFlags::ALIAS)
                }) {
                    target = target.map(|t| self.resolve_alias(t));
                }
                if target.is_none()
                    || self
                        .get_symbol_flags(target.unwrap())
                        .intersects(ast::SymbolFlags::VALUE)
                {
                    // marks export as used
                    self.mark_export_as_referenced(location);
                    // marks target of export as used
                    self.mark_identifier_alias_referenced(exported_name);
                }
            }
        }
    }

    /// `(c *Checker) checkExternalEmitHelpers` (checker.go:29105).
    pub(crate) fn check_external_emit_helpers(
        &mut self,
        location: NodeId,
        helpers: ExternalEmitHelpers,
    ) {
        if !self.compiler_options.import_helpers.is_true() {
            return;
        }
        let nodes = self.program_nodes(location);
        let Some(source_file) = ast::get_source_file_of_node(Some(location), &nodes) else {
            return;
        };
        if !ast::is_effective_external_module(
            nodes[source_file].as_source_file(),
            &self.compiler_options,
        ) || nodes[location].flags.intersects(ast::NodeFlags::AMBIENT)
        {
            return;
        }
        let Some(helpers_module) = self.resolve_helpers_module(source_file, location) else {
            return;
        };
        if helpers_module == self.unknown_symbol {
            return;
        }
        if !(self.source_file_links.get(source_file).requested_external_emit_helpers & helpers)
            == helpers
        {
            let unchecked_helpers = helpers.without(
                self.source_file_links
                    .get(source_file)
                    .requested_external_emit_helpers,
            );
            let mut helper = ExternalEmitHelpers::FIRST_EMIT_HELPER;
            while helper <= ExternalEmitHelpers::LAST_EMIT_HELPER {
                if unchecked_helpers.intersects(helper) {
                    for name in self.get_helper_names(helper) {
                        let exports = self.get_exports_of_module(helpers_module);
                        let symbol = self
                            .get_symbol(&exports, &name, ast::SymbolFlags::VALUE)
                            .map(|s| self.resolve_symbol(s));
                        match symbol {
                            None => {
                                self.error(
                                    Some(location),
                                    &tsc_diagnostics::This_syntax_requires_an_imported_helper_named_1_which_does_not_exist_in_0_Consider_upgrading_your_version_of_0,
                                    &[
                                        EXTERNAL_HELPERS_MODULE_NAME_TEXT.to_string(),
                                        name.clone(),
                                    ],
                                );
                            }
                            Some(symbol) => {
                                if helper.intersects(ExternalEmitHelpers::CLASS_PRIVATE_FIELD_GET)
                                    && !self.has_signature_with_arity_greater_than(symbol, 3)
                                {
                                    self.error(
                                        Some(location),
                                        &tsc_diagnostics::This_syntax_requires_an_imported_helper_named_1_with_2_parameters_which_is_not_compatible_with_the_one_in_0_Consider_upgrading_your_version_of_0,
                                        &[
                                            EXTERNAL_HELPERS_MODULE_NAME_TEXT.to_string(),
                                            name.clone(),
                                            "4".to_string(),
                                        ],
                                    );
                                } else if helper.intersects(
                                    ExternalEmitHelpers::CLASS_PRIVATE_FIELD_SET,
                                ) && !self.has_signature_with_arity_greater_than(symbol, 4)
                                {
                                    self.error(
                                        Some(location),
                                        &tsc_diagnostics::This_syntax_requires_an_imported_helper_named_1_with_2_parameters_which_is_not_compatible_with_the_one_in_0_Consider_upgrading_your_version_of_0,
                                        &[
                                            EXTERNAL_HELPERS_MODULE_NAME_TEXT.to_string(),
                                            name.clone(),
                                            "5".to_string(),
                                        ],
                                    );
                                }
                            }
                        }
                    }
                }
                helper = ExternalEmitHelpers(helper.0 << 1);
            }
        }
        self.source_file_links
            .get(source_file)
            .requested_external_emit_helpers |= helpers;
    }

    /// `(c *Checker) hasSignatureWithArityGreaterThan` (checker.go:29143).
    pub(crate) fn has_signature_with_arity_greater_than(
        &mut self,
        symbol: SymbolId,
        arity: usize,
    ) -> bool {
        for signature in self.get_signatures_of_symbol(symbol) {
            if self.get_parameter_count(signature) > arity {
                return true;
            }
        }
        false
    }

    /// `(c *Checker) getHelperNames` (checker.go:29152).
    pub(crate) fn get_helper_names(&self, helper: ExternalEmitHelpers) -> Vec<String> {
        let names: &[&str] = if helper == ExternalEmitHelpers::REST {
            &["__rest"]
        } else if helper == ExternalEmitHelpers::DECORATE {
            if self.legacy_decorators {
                &["__decorate"]
            } else {
                &["__esDecorate", "__runInitializers"]
            }
        } else if helper == ExternalEmitHelpers::METADATA {
            &["__metadata"]
        } else if helper == ExternalEmitHelpers::PARAM {
            &["__param"]
        } else if helper == ExternalEmitHelpers::AWAITER {
            &["__awaiter"]
        } else if helper == ExternalEmitHelpers::AWAIT {
            &["__await"]
        } else if helper == ExternalEmitHelpers::ASYNC_GENERATOR {
            &["__asyncGenerator"]
        } else if helper == ExternalEmitHelpers::ASYNC_DELEGATOR {
            &["__asyncDelegator"]
        } else if helper == ExternalEmitHelpers::ASYNC_VALUES {
            &["__asyncValues"]
        } else if helper == ExternalEmitHelpers::EXPORT_STAR {
            &["__exportStar"]
        } else if helper == ExternalEmitHelpers::IMPORT_STAR {
            &["__importStar"]
        } else if helper == ExternalEmitHelpers::IMPORT_DEFAULT {
            &["__importDefault"]
        } else if helper == ExternalEmitHelpers::MAKE_TEMPLATE_OBJECT {
            &["__makeTemplateObject"]
        } else if helper == ExternalEmitHelpers::CLASS_PRIVATE_FIELD_GET {
            &["__classPrivateFieldGet"]
        } else if helper == ExternalEmitHelpers::CLASS_PRIVATE_FIELD_SET {
            &["__classPrivateFieldSet"]
        } else if helper == ExternalEmitHelpers::CLASS_PRIVATE_FIELD_IN {
            &["__classPrivateFieldIn"]
        } else if helper == ExternalEmitHelpers::SET_FUNCTION_NAME {
            &["__setFunctionName"]
        } else if helper == ExternalEmitHelpers::PROP_KEY {
            &["__propKey"]
        } else if helper == ExternalEmitHelpers::ADD_DISPOSABLE_RESOURCE_AND_DISPOSE_RESOURCES {
            &["__addDisposableResource", "__disposeResources"]
        } else if helper == ExternalEmitHelpers::REWRITE_RELATIVE_IMPORT_EXTENSION {
            &["__rewriteRelativeImportExtension"]
        } else {
            panic!("Unrecognized helper")
        };
        names.iter().map(|s| s.to_string()).collect()
    }

    /// `(c *Checker) resolveHelpersModule` (checker.go:29202).
    /// Go `file *ast.SourceFile` → `NodeId` of the SourceFile node.
    pub(crate) fn resolve_helpers_module(
        &mut self,
        file: NodeId,
        error_node: NodeId,
    ) -> Option<SymbolId> {
        if self
            .source_file_links
            .get(file)
            .external_helpers_module
            .is_none()
        {
            let file_nodes = self.program_nodes(file);
            let path_key = file_nodes[file].as_source_file().path_key().clone();
            let location = self.program.get_import_helpers_import_specifier(&path_key);
            let mut helpers_module = location.and_then(|location| {
                self.resolve_external_module(
                    location,
                    EXTERNAL_HELPERS_MODULE_NAME_TEXT,
                    Some(
                        &tsc_diagnostics::This_syntax_requires_an_imported_helper_but_module_0_cannot_be_found,
                    ),
                    Some(error_node),
                    false, /*isForAugmentation*/
                    None,  /*importAttributesType*/
                )
            });
            if helpers_module.is_none() {
                helpers_module = Some(self.unknown_symbol);
            }
            self.source_file_links.get(file).external_helpers_module = helpers_module;
        }
        self.source_file_links.get(file).external_helpers_module
    }

    /// `(c *Checker) markDecoratorAliasReferenced` (checker.go:29215).
    /// Go node is `HasDecorators`.
    pub(crate) fn mark_decorator_alias_referenced(&mut self, node: NodeId) {
        if self.compiler_options.emit_decorator_metadata.is_false_or_unknown() {
            return;
        }
        let nodes = self.program_nodes(node);
        let decorators = nodes[node].decorators(&nodes);
        let Some(&first_decorator) = decorators.first().map(|d| &d.id) else {
            return;
        };
        self.check_external_emit_helpers(first_decorator, ExternalEmitHelpers::METADATA);
        // we only need to perform these checks if we are emitting serialized type metadata for the target of a decorator.
        match nodes[node].kind {
            ast::Kind::ClassDeclaration => {
                if let Some(ctor) = ast::get_first_constructor_with_body(&nodes[node], &nodes) {
                    for &p in nodes[ctor].parameters().unwrap_or(&[]) {
                        let type_node = self.get_parameter_type_node_for_decorator_check(p);
                        self.mark_decorator_metadata_type_node_as_referenced(type_node);
                    }
                }
            }
            ast::Kind::GetAccessor | ast::Kind::SetAccessor => {
                let other_kind = if nodes[node].kind == ast::Kind::SetAccessor {
                    ast::Kind::GetAccessor
                } else {
                    ast::Kind::SetAccessor
                };
                let other_accessor = self
                    .get_symbol_of_declaration(node)
                    .and_then(|s| {
                        ast::get_declaration_of_kind(&self.sym(s), other_kind, &nodes)
                    });
                let mut annotation = self.get_annotated_accessor_type_node(node);
                if annotation.is_none() {
                    if let Some(other_accessor) = other_accessor {
                        annotation = self.get_annotated_accessor_type_node(other_accessor);
                    }
                }
                self.mark_decorator_metadata_type_node_as_referenced(annotation);
            }
            ast::Kind::MethodDeclaration => {
                for &p in nodes[node].parameters().unwrap_or(&[]) {
                    let type_node = self.get_parameter_type_node_for_decorator_check(p);
                    self.mark_decorator_metadata_type_node_as_referenced(type_node);
                }
                self.mark_decorator_metadata_type_node_as_referenced(nodes[node].type_());
            }
            ast::Kind::PropertyDeclaration => {
                self.mark_decorator_metadata_type_node_as_referenced(nodes[node].type_());
            }
            ast::Kind::Parameter => {
                let type_node = self.get_parameter_type_node_for_decorator_check(node);
                self.mark_decorator_metadata_type_node_as_referenced(type_node);
                let containing_signature = nodes[node].parent.unwrap();
                for &p in nodes[containing_signature].parameters().unwrap_or(&[]) {
                    let type_node = self.get_parameter_type_node_for_decorator_check(p);
                    self.mark_decorator_metadata_type_node_as_referenced(type_node);
                }
                self.mark_decorator_metadata_type_node_as_referenced(
                    nodes[containing_signature].type_(),
                );
            }
            _ => {}
        }
    }

    /// `(c *Checker) getParameterTypeNodeForDecoratorCheck` (checker.go:29263).
    /// Go node is `ParameterDeclaration`.
    pub(crate) fn get_parameter_type_node_for_decorator_check(
        &mut self,
        node: NodeId,
    ) -> Option<NodeId> {
        let nodes = self.program_nodes(node);
        let type_node = nodes[node].type_();
        if nodes[node].as_parameter_declaration().dot_dot_dot_token.is_some() {
            return ast::get_rest_parameter_element_type(type_node, &nodes);
        }
        type_node
    }

    /// `(c *Checker) markDecoratorMedataDataTypeNodeAsReferenced` (checker.go:29271).
    /// Go node is `TypeNode`.
    pub(crate) fn mark_decorator_metadata_type_node_as_referenced(
        &mut self,
        node: Option<NodeId>,
    ) {
        if let Some(entity_name) = self.get_entity_name_for_decorator_metadata(node) {
            let nodes = self.program_nodes(entity_name);
            if ast::is_entity_name(&nodes[entity_name]) {
                self.mark_entity_name_or_entity_expression_as_reference(
                    Some(entity_name),
                    true,
                );
            }
        }
    }

    /// `(c *Checker) getEntityNameForDecoratorMetadata` (checker.go:29278).
    pub(crate) fn get_entity_name_for_decorator_metadata(
        &mut self,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        let node = node?;
        let nodes = self.program_nodes(node);
        match nodes[node].kind {
            ast::Kind::IntersectionType => self
                .get_entity_name_for_decorator_metadata_from_type_list(
                    &nodes[node]
                        .as_intersection_type_node()
                        .union_or_intersection_type_node_base
                        .types
                        .nodes
                        .clone(),
                ),
            ast::Kind::UnionType => self
                .get_entity_name_for_decorator_metadata_from_type_list(
                    &nodes[node]
                        .as_union_type_node()
                        .union_or_intersection_type_node_base
                        .types
                        .nodes
                        .clone(),
                ),
            ast::Kind::ConditionalType => {
                let cond = nodes[node].as_conditional_type_node();
                let type_nodes =
                    vec![cond.true_type.unwrap(), cond.false_type.unwrap()];
                self.get_entity_name_for_decorator_metadata_from_type_list(&type_nodes)
            }
            ast::Kind::ParenthesizedType => self.get_entity_name_for_decorator_metadata(
                nodes[node].as_parenthesized_type_node().type_,
            ),
            ast::Kind::NamedTupleMember => self.get_entity_name_for_decorator_metadata(
                nodes[node].as_named_tuple_member().type_,
            ),
            ast::Kind::TypeReference => {
                nodes[node].as_type_reference_node().type_name
            }
            _ => None,
        }
    }

    /// `(c *Checker) getEntityNameForDecoratorMetadataFromTypeList` (checker.go:29299).
    pub(crate) fn get_entity_name_for_decorator_metadata_from_type_list(
        &mut self,
        type_nodes: &[NodeId],
    ) -> Option<NodeId> {
        let mut common_entity_name: Option<NodeId> = None;
        for &type_node in type_nodes {
            let nodes = self.program_nodes(type_node);
            if nodes[type_node].kind == ast::Kind::NeverKeyword {
                // Always elide `never` from the union/intersection if possible
                continue;
            }
            if !self.strict_null_checks
                && (nodes[type_node].kind == ast::Kind::LiteralType
                    && nodes[nodes[type_node]
                        .as_literal_type_node()
                        .literal
                        .unwrap()]
                    .kind
                        == ast::Kind::NullKeyword
                    || nodes[type_node].kind == ast::Kind::UndefinedKeyword)
            {
                // Elide null and undefined from unions for metadata, just like what we did prior to the implementation of strict null checks
                continue;
            }
            let Some(individual_entity_name) =
                self.get_entity_name_for_decorator_metadata(Some(type_node))
            else {
                // Individual is something like string number
                // So it would be serialized to either that type or object
                // Safe to return here
                return None;
            };
            if common_entity_name.is_none() {
                common_entity_name = Some(individual_entity_name);
            } else {
                // Note this is in sync with the transformation that happens for type node.
                // Keep this in sync with serializeUnionOrIntersectionType
                // Verify if they refer to same entity and is identifier
                // return undefined if they dont match because we would emit object
                let common = common_entity_name.unwrap();
                let common_nodes = self.program_nodes(common);
                let individual_nodes = self.program_nodes(individual_entity_name);
                if !ast::is_identifier(&common_nodes[common])
                    || !ast::is_identifier(&individual_nodes[individual_entity_name])
                    || common_nodes[common].as_identifier().text
                        != individual_nodes[individual_entity_name].as_identifier().text
                {
                    return None;
                }
            }
        }
        common_entity_name
    }

    /// `(c *Checker) markAliasReferenced` (checker.go:29331).
    pub(crate) fn mark_alias_referenced(&mut self, symbol: SymbolId, location: NodeId) {
        if !self.can_collect_symbol_alias_accessibility_data {
            return;
        }
        let nodes = self.program_nodes(location);
        if ast::is_non_local_alias(Some(&self.sym(symbol)), ast::SymbolFlags::VALUE /*excludes*/)
            && !crate::utilities::is_in_type_query(location, &nodes)
        {
            let target = self.resolve_alias(symbol);
            if self
                .get_symbol_flags_ex(symbol, true /*excludeTypeOnlyMeanings*/, false /*excludeLocalMeanings*/)
                .intersects(ast::SymbolFlags::VALUE | ast::SymbolFlags::EXPORT_VALUE)
            {
                // An alias resolving to a const enum cannot be elided if (1) 'isolatedModules' is enabled
                // (because the const enum value will not be inlined), or if (2) the alias is an export
                // of a const enum declaration that will be preserved.
                if self.compiler_options.get_isolated_modules()
                    || self.compiler_options.should_preserve_const_enums()
                        && is_export_or_export_expression(&nodes, location)
                    || !crate::utilities::is_const_enum_or_const_enum_only_module(
                        self,
                        self.get_export_symbol_of_value_symbol_if_exported(target),
                    )
                {
                    self.mark_alias_symbol_as_referenced(symbol);
                }
            }
        }
    }

    /// `(c *Checker) markAliasSymbolAsReferenced` (checker.go:29353).
    /// When an alias symbol is referenced, we need to mark the entity it references as referenced and in turn repeat that until
    /// we reach a non-alias or an exported entity (which is always considered referenced). We do this by checking the target of
    /// the alias as an expression (which recursively takes us back here if the target references another alias).
    pub(crate) fn mark_alias_symbol_as_referenced(&mut self, symbol: SymbolId) {
        let links = self.alias_symbol_links.get(symbol);
        if !links.referenced {
            links.referenced = true;
            let node = self.get_declaration_of_alias_symbol(symbol);
            let Some(node) = node else {
                panic!("Unexpected nil in markAliasSymbolAsReferenced")
            };
            let nodes = self.program_nodes(node);
            // We defer checking of the reference of an `import =` until the import itself is referenced,
            // This way a chain of imports can be elided if ultimately the final input is only used in a type
            // position.
            if ast::is_import_equals_declaration(&nodes[node])
                && nodes[node]
                    .as_import_equals_declaration()
                    .module_reference
                    .is_some_and(|m| nodes[m].kind != ast::Kind::ExternalModuleReference)
            {
                let resolved = self.resolve_symbol(symbol);
                if resolved.is_some_and(|r| {
                    self.get_symbol_flags(r).intersects(ast::SymbolFlags::VALUE)
                }) {
                    // import foo = <symbol>
                    let module_reference = nodes[node]
                        .as_import_equals_declaration()
                        .module_reference
                        .unwrap();
                    let left = ast::get_first_identifier(module_reference, &nodes);
                    self.mark_identifier_alias_referenced(left);
                }
            }
        }
    }

    /// `(c *Checker) markExportAsReferenced` (checker.go:29374).
    /// Go node is `ImportEqualsDeclaration | ExportSpecifier`.
    pub(crate) fn mark_export_as_referenced(&mut self, node: NodeId) {
        let symbol = self.get_symbol_of_declaration(node);
        if let Some(symbol) = symbol {
            let target = self.resolve_alias(symbol);
            let mark_alias = target == self.unknown_symbol
                || (self
                    .get_symbol_flags_ex(
                        symbol,
                        true,  /*excludeTypeOnlyMeanings*/
                        false, /*excludeLocalMeanings*/
                    )
                    .intersects(ast::SymbolFlags::VALUE)
                    && !crate::utilities::is_const_enum_or_const_enum_only_module(self, target));
            if mark_alias {
                self.mark_alias_symbol_as_referenced(symbol);
            }
        }
    }

    /// `(c *Checker) markEntityNameOrEntityExpressionAsReference` (checker.go:29386).
    /// Go typeName is `EntityNameOrEntityNameExpression | nil`.
    pub(crate) fn mark_entity_name_or_entity_expression_as_reference(
        &mut self,
        type_name: Option<NodeId>,
        for_decorator_metadata: bool,
    ) {
        let Some(type_name) = type_name else {
            return;
        };
        let nodes = self.program_nodes(type_name);
        let root_name = ast::get_first_identifier(type_name, &nodes);
        let meaning = if nodes[type_name].kind == ast::Kind::Identifier {
            ast::SymbolFlags::TYPE
        } else {
            ast::SymbolFlags::NAMESPACE
        } | ast::SymbolFlags::ALIAS;
        let root_name_text = nodes[root_name].text(&nodes).to_string();
        let resolve_name = self.resolve_name.clone().expect("Checker::resolve_name");
        let root_symbol = resolve_name(
            self,
            Some(root_name),
            &root_name_text,
            meaning,
            None,  /*nameNotFoundMessage*/
            true,  /*isUse*/
            false, /*excludeGlobals*/
        );
        if let Some(root_symbol) = root_symbol {
            if self.sym(root_symbol).flags.intersects(ast::SymbolFlags::ALIAS) {
                if self.can_collect_symbol_alias_accessibility_data
                    && self.symbol_is_value(root_symbol)
                    && !crate::utilities::is_const_enum_or_const_enum_only_module(
                        self,
                        self.resolve_alias(root_symbol),
                    )
                    && self.get_type_only_alias_declaration(root_symbol).is_none()
                {
                    self.mark_alias_symbol_as_referenced(root_symbol);
                } else if for_decorator_metadata
                    && self.compiler_options.get_isolated_modules()
                    && self.compiler_options.get_emit_module_kind()
                        >= tsc_core::options_generated::ModuleKind::ES2015
                    && !self.symbol_is_value(root_symbol)
                    && !self.sym(root_symbol).declarations.iter().any(|&d| {
                        ast::is_type_only_import_or_export_declaration(
                            d,
                            &self.program_nodes(d),
                        )
                    })
                {
                    let diag = self.error(
                        Some(type_name),
                        &tsc_diagnostics::A_type_referenced_in_a_decorated_signature_must_be_imported_with_import_type_or_a_namespace_import_when_isolatedModules_and_emitDecoratorMetadata_are_enabled,
                        &[],
                    );
                    let mut alias_declaration: Option<NodeId> = None;
                    for &decl in &self.sym(root_symbol).declarations.clone() {
                        if ast::is_alias_symbol_declaration(decl, &self.program_nodes(decl)) {
                            alias_declaration = Some(decl);
                            break;
                        }
                    }
                    if let (Some(diag), Some(alias_declaration)) = (diag, alias_declaration) {
                        let related = self.new_diagnostic_for_node(
                            Some(alias_declaration),
                            &tsc_diagnostics::X_0_was_imported_here,
                            &[root_name_text.clone()],
                        );
                        diag.lock().unwrap().set_related_info(vec![related]);
                    }
                }
            }
        }
    }

    /// `(c *Checker) markTypeNodeAsReferenced` (checker.go:29442).
    /// If a TypeNode can be resolved to a value symbol imported from an external module, it is
    /// marked as referenced to prevent import elision.
    pub(crate) fn mark_type_node_as_referenced(&mut self, node: Option<NodeId>) {
        if let Some(node) = node {
            let entity_name = get_entity_name_from_type_node(self, node);
            self.mark_entity_name_or_entity_expression_as_reference(
                entity_name,
                false, /*forDecoratorMetadata*/
            );
        }
    }
}

/// `isExportOrExportExpression` (checker.go:28885). Free function in Go.
fn is_export_or_export_expression(nodes: &[ast::Node], location: NodeId) -> bool {
    ast::find_ancestor(Some(location), nodes, &mut |n, nodes| {
        if let Some(parent) = n.parent {
            if ast::is_export_assignment(&nodes[parent]) {
                return nodes[parent].expression() == Some(n.id)
                    && ast::is_entity_name_expression(&nodes[n.id], nodes);
            }
            if ast::is_export_specifier(&nodes[parent]) {
                return nodes[parent].name() == Some(n.id)
                    || nodes[parent].property_name() == Some(n.id);
            }
        }
        false
    })
    .is_some()
}

/// `shouldMarkIdentifierAliasReferenced` (checker.go:28900). Free function in Go.
fn should_mark_identifier_alias_referenced(nodes: &[ast::Node], node: NodeId) -> bool {
    if let Some(parent) = nodes[node].parent {
        // A property access expression LHS? checkPropertyAccessExpression will handle that.
        if ast::is_property_access_expression(&nodes[parent])
            && nodes[parent].expression() == Some(node)
        {
            return false;
        }
        // Next two check for an identifier inside a type only export.
        if ast::is_export_specifier(&nodes[parent]) && nodes[parent].is_type_only() {
            return false;
        }
        if let Some(grandparent) = nodes[parent].parent {
            if let Some(great_grandparent) = nodes[grandparent].parent {
                if ast::is_export_declaration(&nodes[great_grandparent])
                    && nodes[great_grandparent].is_type_only()
                {
                    return false;
                }
            }
        }
    }
    true
}

/// `isInternalModuleImportEqualsDeclaration` (checker.go:28921). Free function in Go.
fn is_internal_module_import_equals_declaration(nodes: &[ast::Node], node: NodeId) -> bool {
    nodes[node].kind == ast::Kind::ImportEqualsDeclaration
        && nodes[node]
            .as_import_equals_declaration()
            .module_reference
            .is_some_and(|m| nodes[m].kind != ast::Kind::ExternalModuleReference)
}

/// `isPartOfImportEqualsModuleReference` (checker.go:29008). Free function in Go.
fn is_part_of_import_equals_module_reference(nodes: &[ast::Node], location: NodeId) -> bool {
    let Some(import_equals) =
        ast::find_ancestor_kind(Some(location), ast::Kind::ImportEqualsDeclaration, nodes)
    else {
        return false;
    };
    let mut node = Some(location);
    while let Some(n) = node {
        if n == import_equals {
            break;
        }
        if Some(n) == nodes[import_equals].as_import_equals_declaration().module_reference {
            return true;
        }
        node = nodes[n].parent;
    }
    false
}

/// `getEntityNameFromTypeNode` (checker.go:29421). Free function in Go.
fn get_entity_name_from_type_node(c: &Checker, node: NodeId) -> Option<NodeId> {
    let nodes = c.program_nodes(node);
    match nodes[node].kind {
        ast::Kind::TypeReference => nodes[node].as_type_reference_node().type_name,
        ast::Kind::ExpressionWithTypeArguments => {
            let expression = nodes[node].expression()?;
            if ast::is_entity_name_expression(&nodes[expression], &nodes) {
                return Some(expression);
            }
            None
        }
        // These aren't valid TypeNodes, but we treat them as such because of `isPartOfTypeNode`, which returns `true` for things that aren't `TypeNode`s.
        ast::Kind::Identifier | ast::Kind::QualifiedName => Some(node),
        _ => None,
    }
}

impl Checker {
    /// `(c *Checker) GetPromisedTypeOfPromise` (checker.go:29448).
    pub fn get_promised_type_of_promise(&mut self, t: TypeId) -> Option<TypeId> {
        self.get_promised_type_of_promise_ex(t, None, None)
    }

    /// `(c *Checker) getPromisedTypeOfPromiseEx` (checker.go:29455).
    /// Gets the "promised type" of a promise.
    /// The "promised type" of a type is the type of the "value" parameter of the
    /// "onfulfilled" callback. Go `thisTypeForErrorOut **Type` →
    /// `Option<&mut Option<TypeId>>`.
    pub(crate) fn get_promised_type_of_promise_ex(
        &mut self,
        t: TypeId,
        error_node: Option<NodeId>,
        mut this_type_for_error_out: Option<&mut Option<TypeId>>,
    ) -> Option<TypeId> {
        if crate::utilities::is_type_any(&self.types, t) {
            return None;
        }
        let key = CachedTypeKey {
            kind: CachedTypeKind::PromisedTypeOfPromise,
            type_id: t,
        };
        if let Some(&cached) = self.cached_types.get(&key) {
            return Some(cached);
        }
        let global_promise_type =
            self.get_global_promise_type.clone().expect("get_global_promise_type")(self);
        if self.is_reference_to_type(t, global_promise_type) {
            let result = self.get_type_arguments(t)[0];
            self.cached_types.insert(key, result);
            return Some(result);
        }
        // primitives with a `{ then() }` won't be unwrapped/adopted.
        if self.all_types_assignable_to_kind(
            self.get_base_constraint_or_type(t),
            TypeFlags::PRIMITIVE | TypeFlags::NEVER,
        ) {
            return None;
        }
        let then_function = self.get_type_of_property_of_type(t, "then");
        // TODO: GH#18217
        if then_function.is_some_and(|f| crate::utilities::is_type_any(&self.types, f)) {
            return None;
        }
        let mut then_signatures: Vec<SignatureId> = Vec::new();
        if let Some(then_function) = then_function {
            then_signatures = self.get_signatures_of_type(then_function, SignatureKind::CALL);
        }
        if then_signatures.is_empty() {
            if error_node.is_some() {
                self.error(
                    error_node,
                    &tsc_diagnostics::A_promise_must_have_a_then_method,
                    &[],
                );
            }
            return None;
        }
        let mut this_type_for_error: Option<TypeId> = None;
        let mut candidates: Vec<SignatureId> = Vec::new();
        let subtype_relation = self.subtype_relation.clone();
        for &then_signature in &then_signatures {
            if let Some(this_type) = self.get_this_type_of_signature(then_signature) {
                if this_type != self.void_type
                    && !self.is_type_related_to(t, this_type, &subtype_relation)
                {
                    this_type_for_error = Some(this_type);
                    continue;
                }
            }
            candidates.push(then_signature);
        }
        if candidates.is_empty() {
            debug_assert!(this_type_for_error.is_some());
            if let Some(out) = this_type_for_error_out.as_deref_mut() {
                *out = this_type_for_error;
            }
            if error_node.is_some() {
                self.error(
                    error_node,
                    &tsc_diagnostics::The_this_context_of_type_0_is_not_assignable_to_method_s_this_of_type_1,
                    &[
                        self.type_to_string(t),
                        self.type_to_string(this_type_for_error.unwrap_or(self.error_type)),
                    ],
                );
            }
            return None;
        }
        let candidate_types: Vec<TypeId> = candidates
            .iter()
            .map(|&s| self.get_type_of_first_parameter_of_signature(s))
            .collect();
        let onfulfilled_parameter_type = self.get_type_with_facts(
            self.get_union_type(&candidate_types),
            TypeFacts::NE_UNDEFINED_OR_NULL,
        );
        if crate::utilities::is_type_any(&self.types, onfulfilled_parameter_type) {
            return None;
        }
        let onfulfilled_parameter_signatures =
            self.get_signatures_of_type(onfulfilled_parameter_type, SignatureKind::CALL);
        if onfulfilled_parameter_signatures.is_empty() {
            if error_node.is_some() {
                self.error(
                    error_node,
                    &tsc_diagnostics::The_first_parameter_of_the_then_method_of_a_promise_must_be_a_callback,
                    &[],
                );
            }
            return None;
        }
        let param_types: Vec<TypeId> = onfulfilled_parameter_signatures
            .iter()
            .map(|&s| self.get_type_of_first_parameter_of_signature(s))
            .collect();
        let result = self.get_union_type_ex(&param_types, UnionReduction::SUBTYPE, None, None);
        self.cached_types.insert(key, result);
        Some(result)
    }

    /// `(c *Checker) getTypeOfFirstParameterOfSignature` (checker.go:29530).
    pub(crate) fn get_type_of_first_parameter_of_signature(
        &mut self,
        signature: SignatureId,
    ) -> TypeId {
        self.get_type_of_first_parameter_of_signature_with_fallback(signature, self.never_type)
    }

    /// `(c *Checker) getTypeOfFirstParameterOfSignatureWithFallback` (checker.go:29534).
    pub(crate) fn get_type_of_first_parameter_of_signature_with_fallback(
        &mut self,
        signature: SignatureId,
        fallback_type: TypeId,
    ) -> TypeId {
        if !self.signature_arena.get(signature).parameters.is_empty() {
            return self.get_type_at_position(signature, 0);
        }
        fallback_type
    }

    /// `(c *Checker) getCombinedMappedTypeOptionality` (checker.go:29569).
    /// Return -1, 0, or 1, for stripped, unchanged, or added optionality respectively. When a homomorphic mapped type doesn't
    /// modify optionality, recursively consult the optionality of the type being mapped over to see if it strips or adds optionality.
    /// For intersections, return -1 or 1 when all constituents strip or add optionality, otherwise return 0.
    pub(crate) fn get_combined_mapped_type_optionality(&mut self, t: TypeId) -> i32 {
        if self
            .types
            .get(t)
            .object_flags
            .intersects(ObjectFlags::MAPPED)
        {
            let optionality = get_mapped_type_optionality(self, t);
            if optionality != 0 {
                return optionality;
            }
            let modifiers_type = self.get_modifiers_type_from_mapped_type(t);
            return self.get_combined_mapped_type_optionality(modifiers_type);
        }
        if self.types.get(t).flags.intersects(TypeFlags::INTERSECTION) {
            let types = self.types.get(t).types().to_vec();
            let optionality = self.get_combined_mapped_type_optionality(types[0]);
            for &t in &types[1..] {
                if self.get_combined_mapped_type_optionality(t) != optionality {
                    return 0;
                }
            }
            return optionality;
        }
        0
    }

    /// `(c *Checker) getOptionalExpressionType` (checker.go:29593).
    pub(crate) fn get_optional_expression_type(
        &mut self,
        expr_type: TypeId,
        expression: NodeId,
    ) -> TypeId {
        let nodes = self.program_nodes(expression);
        if ast::is_expression_of_optional_chain_root(expression, &nodes) {
            self.get_non_nullable_type(expr_type)
        } else if ast::is_optional_chain(&nodes[expression]) {
            self.remove_optional_type_marker(expr_type)
        } else {
            expr_type
        }
    }

    /// `(c *Checker) removeOptionalTypeMarker` (checker.go:29604).
    pub(crate) fn remove_optional_type_marker(&mut self, t: TypeId) -> TypeId {
        if self.strict_null_checks {
            return self.remove_type(t, self.optional_type);
        }
        t
    }

    /// `(c *Checker) propagateOptionalTypeMarker` (checker.go:29611).
    pub(crate) fn propagate_optional_type_marker(
        &mut self,
        t: TypeId,
        node: NodeId,
        was_optional: bool,
    ) -> TypeId {
        if was_optional {
            let nodes = self.program_nodes(node);
            if ast::is_outermost_optional_chain(&nodes[node], &nodes) {
                return self.get_optional_type(t, false);
            }
            return self.add_optional_type_marker(t);
        }
        t
    }

    /// `(c *Checker) removeMissingType` (checker.go:29621).
    pub(crate) fn remove_missing_type(&mut self, t: TypeId, is_optional: bool) -> TypeId {
        if self.exact_optional_property_types && is_optional {
            return self.remove_type(t, self.missing_type);
        }
        t
    }

    /// `(c *Checker) removeMissingOrUndefinedType` (checker.go:29628).
    pub(crate) fn remove_missing_or_undefined_type(&mut self, t: TypeId) -> TypeId {
        if self.exact_optional_property_types {
            return self.remove_type(t, self.missing_type);
        }
        self.get_type_with_facts(t, TypeFacts::NE_UNDEFINED)
    }

    /// `(c *Checker) removeDefinitelyFalsyTypes` (checker.go:29635).
    pub(crate) fn remove_definitely_falsy_types(&mut self, t: TypeId) -> TypeId {
        self.filter_type(t, |c: &mut Checker, t: TypeId| {
            c.has_type_facts(t, TypeFacts::TRUTHY)
        })
    }

    /// `(c *Checker) extractDefinitelyFalsyTypes` (checker.go:29639).
    pub(crate) fn extract_definitely_falsy_types(&mut self, t: TypeId) -> TypeId {
        self.map_type(
            t,
            Rc::new(|c: &mut Checker, t: TypeId| c.get_definitely_falsy_part_of_type(t)),
        )
    }

    /// `(c *Checker) getDefinitelyFalsyPartOfType` (checker.go:29643).
    pub(crate) fn get_definitely_falsy_part_of_type(&mut self, t: TypeId) -> TypeId {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::STRING) {
            return self.empty_string_type;
        }
        if flags.intersects(TypeFlags::NUMBER) {
            return self.zero_type;
        }
        if flags.intersects(TypeFlags::BIG_INT) {
            return self.zero_big_int_type;
        }
        if t == self.regular_false_type
            || t == self.false_type
            || flags.intersects(
                TypeFlags::VOID | TypeFlags::UNDEFINED | TypeFlags::NULL | TypeFlags::ANY_OR_UNKNOWN,
            )
            || flags.intersects(TypeFlags::STRING_LITERAL)
                && get_string_literal_value(&self.types, t).is_empty()
            || flags.intersects(TypeFlags::NUMBER_LITERAL)
                && get_number_literal_value(&self.types, t) == Number(0.0)
            || flags.intersects(TypeFlags::BIG_INT_LITERAL)
                && is_zero_big_int(get_big_int_literal_value(&self.types, t))
        {
            return t;
        }
        self.never_type
    }

    /// `(c *Checker) getConstraintDeclaration` (checker.go:29661).
    pub(crate) fn get_constraint_declaration(&mut self, t: TypeId) -> Option<NodeId> {
        if let Some(symbol) = self.types.get(t).symbol {
            for &d in &self.sym(symbol).declarations.clone() {
                let nodes = self.program_nodes(d);
                if ast::is_type_parameter_declaration(&nodes[d]) {
                    if let Some(constraint) =
                        nodes[d].as_type_parameter_declaration().constraint
                    {
                        return Some(constraint);
                    }
                }
            }
        }
        None
    }

    /// `(c *Checker) getTemplateStringForType` (checker.go:29761).
    pub(crate) fn get_template_string_for_type(&mut self, t: TypeId) -> String {
        let flags = self.types.get(t).flags;
        if flags.intersects(
            TypeFlags::STRING_LITERAL
                | TypeFlags::NUMBER_LITERAL
                | TypeFlags::BOOLEAN_LITERAL
                | TypeFlags::BIG_INT_LITERAL,
        ) {
            return evaluator::any_to_string(
                &self.types.get(t).as_literal_type().value,
            );
        }
        if flags.intersects(TypeFlags::NULLABLE) {
            return self
                .types
                .get(t)
                .as_intrinsic_type()
                .intrinsic_name
                .clone();
        }
        String::new()
    }

    /// `(c *Checker) getStringMappingType` (checker.go:29771).
    /// Go `symbol *ast.Symbol` → `SymbolId` (non-nil at call sites).
    pub(crate) fn get_string_mapping_type(&mut self, symbol: Option<SymbolId>, t: TypeId) -> TypeId {
        let flags = self.types.get(t).flags;
        if flags.intersects(TypeFlags::UNION | TypeFlags::NEVER) {
            return self.map_type(
                t,
                Rc::new(move |c: &mut Checker, t: TypeId| c.get_string_mapping_type(symbol, t)),
            );
        }
        if flags.intersects(TypeFlags::STRING_LITERAL) {
            let value = get_string_literal_value(&self.types, t);
            let mapped = apply_string_mapping(self, symbol, &value);
            return self.get_string_literal_type(&mapped);
        }
        if flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            let (texts, types) = {
                let tl = self.types.get(t).as_template_literal_type();
                (tl.texts.clone(), tl.types.clone())
            };
            let (texts, types) = self.apply_template_string_mapping(symbol, &texts, &types);
            return self.get_template_literal_type(&texts, &types);
        }
        if flags.intersects(TypeFlags::STRING_MAPPING) && self.types.get(t).symbol == symbol {
            return t;
        }
        if flags.intersects(TypeFlags::ANY | TypeFlags::STRING | TypeFlags::STRING_MAPPING)
            || self.is_generic_index_type(t)
        {
            return self.get_string_mapping_type_for_generic_type(symbol, t);
        }
        if self.is_pattern_literal_placeholder_type(t) {
            let template =
                self.get_template_literal_type(&[String::new(), String::new()], &[t]);
            return self.get_string_mapping_type_for_generic_type(symbol, template);
        }
        t
    }

    /// `(c *Checker) applyTemplateStringMapping` (checker.go:29806).
    pub(crate) fn apply_template_string_mapping(
        &mut self,
        symbol: Option<SymbolId>,
        texts: &[String],
        types: &[TypeId],
    ) -> (Vec<String>, Vec<TypeId>) {
        let name = symbol.map(|s| self.sym(s).name.clone()).unwrap_or_default();
        match crate::checker_types::intrinsic_type_kind(&name) {
            Some(IntrinsicTypeKind::Uppercase) | Some(IntrinsicTypeKind::Lowercase) => {
                let new_texts: Vec<String> = texts
                    .iter()
                    .map(|t| apply_string_mapping(self, symbol, t))
                    .collect();
                let new_types: Vec<TypeId> = types
                    .iter()
                    .map(|&t| self.get_string_mapping_type(symbol, t))
                    .collect();
                (new_texts, new_types)
            }
            Some(IntrinsicTypeKind::Capitalize) | Some(IntrinsicTypeKind::Uncapitalize) => {
                if !texts[0].is_empty() {
                    let mut new_texts = texts.to_vec();
                    new_texts[0] = apply_string_mapping(self, symbol, &new_texts[0]);
                    (new_texts, types.to_vec())
                } else {
                    let mut new_types = types.to_vec();
                    new_types[0] = self.get_string_mapping_type(symbol, new_types[0]);
                    (texts.to_vec(), new_types)
                }
            }
            _ => (texts.to_vec(), types.to_vec()),
        }
    }

    /// `(c *Checker) getStringMappingTypeForGenericType` (checker.go:29824).
    pub(crate) fn get_string_mapping_type_for_generic_type(
        &mut self,
        symbol: Option<SymbolId>,
        t: TypeId,
    ) -> TypeId {
        let key = StringMappingKey {
            s: symbol.unwrap_or(self.unknown_symbol),
            t,
        };
        if let Some(&result) = self.string_mapping_types.get(&key) {
            return result;
        }
        let result = self.new_string_mapping_type(symbol, t);
        self.string_mapping_types.insert(key, result);
        result
    }

    /// `(c *Checker) substituteIndexedMappedType` (checker.go:29839).
    /// Given an indexed access on a mapped type of the form { [P in K]: E }[X], return an instantiation of E where P is
    /// replaced with X. Since this simplification doesn't account for mapped type modifiers, add 'undefined' to the
    /// resulting type if the mapped type includes a '?' modifier or if the modifiers type indicates that some properties
    /// are optional. If the modifiers type is generic, conservatively estimate optionality by recursively looking for
    /// mapped types that include '?' modifiers.
    pub(crate) fn substitute_indexed_mapped_type(
        &mut self,
        object_type: TypeId,
        index: TypeId,
    ) -> TypeId {
        let type_parameter = self.get_type_parameter_from_mapped_type(object_type);
        let mapper = crate::mapper::new_simple_type_mapper(self, type_parameter.unwrap(), index);
        let object_mapper = self.types.get(object_type).as_mapped_type().mapper;
        let template_mapper = self.combine_type_mappers(object_mapper, mapper);
        let target = self
            .types
            .get(object_type)
            .as_mapped_type()
            .target
            .unwrap_or(object_type);
        let template_type = self.get_template_type_from_mapped_type(target);
        let instantiated_template_type =
            self.instantiate_type(template_type.unwrap(), Some(template_mapper));
        let mut is_optional = get_mapped_type_optionality(self, object_type) > 0;
        if !is_optional {
            if self.is_generic_type(object_type) {
                let modifiers_type = self.get_modifiers_type_from_mapped_type(object_type);
                is_optional =
                    self.get_combined_mapped_type_optionality(modifiers_type) > 0;
            } else {
                is_optional = self.could_access_optional_property(object_type, index);
            }
        }
        self.add_optionality_ex(instantiated_template_type, true /*isProperty*/, is_optional)
    }

    /// `(c *Checker) couldAccessOptionalProperty` (checker.go:29855).
    /// Return true if an indexed access with the given object and index types could access an optional property.
    pub(crate) fn could_access_optional_property(
        &mut self,
        object_type: TypeId,
        index_type: TypeId,
    ) -> bool {
        let Some(index_constraint) = self.get_base_constraint_of_type(index_type) else {
            return false;
        };
        let properties = self.get_properties_of_type(object_type);
        for p in properties {
            if self.sym(p).flags.intersects(ast::SymbolFlags::OPTIONAL) {
                let lit = self.get_literal_type_from_property(
                    p,
                    TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE,
                    false,
                );
                if self.is_type_assignable_to(lit, index_constraint) {
                    return true;
                }
            }
        }
        false
    }

    /// `(c *Checker) getTypeOfPropertyOrIndexSignatureOfType` (checker.go:29862).
    pub(crate) fn get_type_of_property_or_index_signature_of_type(
        &mut self,
        t: TypeId,
        name: &str,
    ) -> Option<TypeId> {
        if let Some(prop_type) = self.get_type_of_property_of_type(t, name) {
            return Some(prop_type);
        }
        if let Some(index_info) = self.get_applicable_index_info_for_name(t, name) {
            let value_type = self.index_info_arena.get(index_info).value_type;
            return Some(self.add_optionality_ex(
                value_type.unwrap_or(self.error_type),
                true, /*isProperty*/
                true, /*isOptional*/
            ));
        }
        None
    }
}

/// `getMappedTypeModifiers` (checker.go:29541). Free function in Go.
fn get_mapped_type_modifiers(c: &Checker, t: TypeId) -> MappedTypeModifiers {
    let Some(declaration) = c.types.get(t).as_mapped_type().declaration else {
        return MappedTypeModifiers::NONE;
    };
    let nodes = c.program_nodes(declaration);
    let declaration = &nodes[declaration];
    let mut modifiers = MappedTypeModifiers::NONE;
    if let Some(readonly_token) = declaration.as_mapped_type_node().readonly_token {
        modifiers |= if nodes[readonly_token].kind == ast::Kind::MinusToken {
            MappedTypeModifiers::EXCLUDE_READONLY
        } else {
            MappedTypeModifiers::INCLUDE_READONLY
        };
    }
    if let Some(question_token) = declaration.as_mapped_type_node().question_token {
        modifiers |= if nodes[question_token].kind == ast::Kind::MinusToken {
            MappedTypeModifiers::EXCLUDE_OPTIONAL
        } else {
            MappedTypeModifiers::INCLUDE_OPTIONAL
        };
    }
    modifiers
}

/// `getMappedTypeOptionality` (checker.go:29555). Free function in Go.
/// Return -1, 0, or 1, where -1 means optionality is stripped (i.e. -?), 0 means
/// optionality is unchanged, and 1 means optionality is added (i.e. +?).
fn get_mapped_type_optionality(c: &Checker, t: TypeId) -> i32 {
    let modifiers = get_mapped_type_modifiers(c, t);
    if modifiers.intersects(MappedTypeModifiers::EXCLUDE_OPTIONAL) {
        return -1;
    }
    if modifiers.intersects(MappedTypeModifiers::INCLUDE_OPTIONAL) {
        return 1;
    }
    0
}

/// `isPartialMappedType` (checker.go:29589). Free function in Go.
fn is_partial_mapped_type(c: &Checker, t: TypeId) -> bool {
    c.types.get(t).object_flags.intersects(ObjectFlags::MAPPED)
        && get_mapped_type_modifiers(c, t).intersects(MappedTypeModifiers::INCLUDE_OPTIONAL)
}

/// `applyStringMapping` (checker.go:29790). Free function in Go.
fn apply_string_mapping(c: &Checker, symbol: Option<SymbolId>, str_: &str) -> String {
    let name = symbol.map(|s| c.sym(s).name.clone()).unwrap_or_default();
    match crate::checker_types::intrinsic_type_kind(&name) {
        Some(IntrinsicTypeKind::Uppercase) => {
            String::from_utf8_lossy(&tsc_stringutil::to_upper_js(str_.as_bytes())).into_owned()
        }
        Some(IntrinsicTypeKind::Lowercase) => {
            String::from_utf8_lossy(&tsc_stringutil::to_lower_js(str_.as_bytes())).into_owned()
        }
        Some(IntrinsicTypeKind::Capitalize) => {
            let (_, size) = tsc_stringutil::decode_js_string_rune(str_.as_bytes());
            let size = size as usize;
            format!(
                "{}{}",
                String::from_utf8_lossy(&tsc_stringutil::to_upper_js(str_[..size].as_bytes())),
                &str_[size..]
            )
        }
        Some(IntrinsicTypeKind::Uncapitalize) => {
            let (_, size) = tsc_stringutil::decode_js_string_rune(str_.as_bytes());
            let size = size as usize;
            format!(
                "{}{}",
                String::from_utf8_lossy(&tsc_stringutil::to_lower_js(str_[..size].as_bytes())),
                &str_[size..]
            )
        }
        _ => str_.to_string(),
    }
}
