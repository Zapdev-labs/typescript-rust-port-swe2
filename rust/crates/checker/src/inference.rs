// Ported from tsc/internal/checker/inference.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — type inference. `InferenceFlags`/
// `InferenceContext`/`InferenceInfo`/`InferencePriority`/`InferenceContextId`
// live in checker_core.rs (foundation-phase port).
//
// PORT notes:
// - Go's `[]*InferenceInfo` aliases the owning `InferenceContext.inferences`
//   slice (writes propagate). Here `infer_types` takes `&mut Vec<InferenceInfo>`
//   and `InferenceState.inferences` swaps with the caller's vector, which
//   preserves write-through behavior without shared pointers.
// - `*Type` → `TypeId`, `*Signature` → `SignatureId`, `*ast.Symbol` →
//   `SymbolId`, `*InferenceContext` → `InferenceContextId`, `*TypeMapper` →
//   `TypeMapperId`; Go nils become `Option`/`TypeId::NONE`.
// - Go `func(c *Checker, n *InferenceState, source, target *Type)` action
//   values become `fn(&mut Checker, &mut InferenceState, TypeId, TypeId)`
//   method pointers; `func(c, s, t) bool` similarly becomes a `fn` item.
// - `get_inferred_type`/`infer_from_intra_expression_sites` are top-level
//   functions here (not methods); the `Checker` methods of the same names in
//   checker_core.rs delegate to them.

use std::cmp::{max, min};
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, NodeId, SymbolId};
use tsc_core::core;

use crate::checker_core::{
    Checker, InferenceContext, InferenceContextId, InferenceFlags, InferenceInfo,
    InferencePriority, IntraExpressionInferenceSite, clear_cached_inferences,
    get_non_distributed_type_parameter, is_object_or_array_literal_type, is_tuple_type,
};
use crate::checker_types::{MappedTypeModifiers, ReverseMappedTypeKey, UnionReduction};
use crate::mapper::{self, TypeMapperId};
use crate::relater::{Comparer, ExpandingFlags};
use crate::types::{
    ElementFlags, IndexFlags, IndexInfoId, ObjectFlags, SignatureFlags, SignatureId, SignatureKind,
    TemplateLiteralType, Ternary, TupleType, TypeArena, TypeComparer, TypeFlags, TypeId,
};

/// `type InferenceKey struct` (inference.go). Go's `TypeId` fields are the
/// type ids — the port's `TypeId` is the same identity.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct InferenceKey {
    /// `source`.
    pub source: TypeId,
    /// `target`.
    pub target: TypeId,
    /// `priority`.
    pub priority: InferencePriority,
    /// `contravariant`.
    pub contravariant: bool,
    /// `bivariant`.
    pub bivariant: bool,
}

/// `type InferenceState struct` (inference.go) — Go's
/// `inferences []*InferenceInfo` aliases the `InferenceContext.inferences`
/// slice (writes propagate). Here it is an owned `Vec` that `infer_types`
/// swaps with the caller's vector, which preserves write-through behavior.
#[derive(Default)]
pub struct InferenceState {
    /// `inferences`.
    pub inferences: Vec<InferenceInfo>,
    /// `originalSource`.
    pub original_source: Option<TypeId>,
    /// `originalTarget`.
    pub original_target: Option<TypeId>,
    /// `priority`.
    pub priority: InferencePriority,
    /// `inferencePriority`.
    pub inference_priority: InferencePriority,
    /// `contravariant`.
    pub contravariant: bool,
    /// `bivariant`.
    pub bivariant: bool,
    /// `expandingFlags`.
    pub expanding_flags: ExpandingFlags,
    /// `propagationType`.
    pub propagation_type: Option<TypeId>,
    /// `visited`.
    pub visited: FxHashMap<InferenceKey, InferencePriority>,
    /// `sourceStack`.
    pub source_stack: Vec<TypeId>,
    /// `targetStack`.
    pub target_stack: Vec<TypeId>,
    /// `next` — free-list link (`Checker::free_inference_state`).
    pub next: Option<Box<InferenceState>>,
}

impl Checker {
    /// `(c *Checker) getInferenceState` (inference.go).
    pub fn get_inference_state(&mut self) -> Box<InferenceState> {
        let mut n = self
            .free_inference_state
            .take()
            .unwrap_or_else(|| Box::new(InferenceState::default()));
        self.free_inference_state = n.next.take();
        n
    }

    /// `(c *Checker) putInferenceState` (inference.go). Go keeps the
    /// backing arrays (`n.inferences[:0]` etc.) and clears `visited`.
    pub fn put_inference_state(&mut self, mut n: Box<InferenceState>) {
        let mut reused = InferenceState::default();
        reused.inferences = std::mem::take(&mut n.inferences);
        reused.inferences.clear();
        reused.visited = std::mem::take(&mut n.visited);
        reused.visited.clear();
        reused.source_stack = std::mem::take(&mut n.source_stack);
        reused.source_stack.clear();
        reused.target_stack = std::mem::take(&mut n.target_stack);
        reused.target_stack.clear();
        reused.next = self.free_inference_state.take();
        *n = reused;
        self.free_inference_state = Some(n);
    }

    /// `(c *Checker) inferTypes` (inference.go). PORT: `[]*InferenceInfo`
    /// becomes `&mut Vec<InferenceInfo>` — the state's `inferences` swaps with
    /// the caller's vector so mutations write through like Go's slice alias.
    pub fn infer_types(
        &mut self,
        inferences: &mut Vec<InferenceInfo>,
        original_source: TypeId,
        original_target: TypeId,
        priority: InferencePriority,
        contravariant: bool,
    ) {
        let mut n = self.get_inference_state();
        std::mem::swap(&mut n.inferences, inferences);
        n.original_source = Some(original_source);
        n.original_target = Some(original_target);
        n.priority = priority;
        n.inference_priority = InferencePriority::MAX_VALUE;
        n.contravariant = contravariant;
        self.infer_from_types(n.as_mut(), original_source, original_target);
        std::mem::swap(&mut n.inferences, inferences);
        self.put_inference_state(n);
    }

    /// `(c *Checker) inferFromTypes` (inference.go).
    pub(crate) fn infer_from_types(
        &mut self,
        n: &mut InferenceState,
        mut source: TypeId,
        mut target: TypeId,
    ) {
        if !(self
            .could_contain_type_variables
            .clone()
            .expect("could_contain_type_variables"))(self, target)
            || self.is_no_infer_type(target)
        {
            return;
        }
        if source == self.wildcard_type || source == self.blocked_string_type {
            // We are inferring from an 'any' type. We want to infer this type
            // for every type parameter referenced in the target type, so we
            // record it as the propagation type and infer from the target to
            // itself. Then, as we find candidates we substitute the
            // propagation type.
            let save_propagation_type = n.propagation_type;
            n.propagation_type = Some(source);
            self.infer_from_types(n, target, target);
            n.propagation_type = save_propagation_type;
            return;
        }
        {
            let (
                source_alias_symbol,
                source_alias_has_args,
                target_alias_symbol,
                target_alias_has_args,
            ) = {
                let __arena_source_ty = self.types.clone();
                let source_ty = __arena_source_ty.get(source);
                let __arena_target_ty = self.types.clone();
                let target_ty = __arena_target_ty.get(target);
                (
                    source_ty.alias().map(|a| a.symbol),
                    source_ty
                        .alias()
                        .is_some_and(|a| !a.type_arguments.is_empty()),
                    target_ty.alias().map(|a| a.symbol),
                    target_ty
                        .alias()
                        .is_some_and(|a| !a.type_arguments.is_empty()),
                )
            };
            if source_alias_symbol.is_some()
                && target_alias_symbol.is_some()
                && source_alias_symbol == target_alias_symbol
            {
                if source_alias_has_args || target_alias_has_args {
                    self.invoke_once(n, source, target, Self::infer_from_alias_type_arguments);
                }
                // And if there weren't any type arguments, there's no reason
                // to run inference as the types must be the same.
                return;
            }
        }
        if source == target
            && self
                .types_handle()
                .get(source)
                .flags
                .intersects(TypeFlags::UNION_OR_INTERSECTION)
        {
            // When source and target are the same union or intersection type,
            // just relate each constituent type to itself.
            let __arena_types = self.types.clone();
            let types = __arena_types.get(source).types().to_vec();
            for t in types {
                self.infer_from_types(n, t, t);
            }
            return;
        }
        if self
            .types_handle()
            .get(target)
            .flags
            .intersects(TypeFlags::UNION)
        {
            let source_types: Vec<TypeId> = if self
                .types_handle()
                .get(source)
                .flags
                .intersects(TypeFlags::UNION)
            {
                self.types_handle().get(source).types().to_vec()
            } else {
                vec![source]
            };
            let __arena_target_types = self.types.clone();
            let target_types = __arena_target_types.get(target).types().to_vec();
            // First, infer between identically matching source and target
            // constituents and remove the matching types.
            let (temp_sources, temp_targets) = self.infer_from_matching_types(
                n,
                source_types,
                target_types,
                Self::is_type_or_base_identical_to,
                false, /*sort*/
            );
            // Next, infer between closely matching source and target
            // constituents and remove the matching types. Types closely match
            // when they are instantiations of the same object type or
            // instantiations of the same type alias.
            let (sources, targets) = self.infer_from_matching_types(
                n,
                temp_sources,
                temp_targets,
                Self::is_type_closely_matched_by,
                true, /*sort*/
            );
            if targets.is_empty() {
                return;
            }
            target = self.get_union_type(&targets);
            if sources.is_empty() {
                // All source constituents have been matched and there is
                // nothing further to infer from. However, simply making no
                // inferences is undesirable because it could ultimately mean
                // inferring a type parameter constraint. Instead, make a lower
                // priority inference from the full source to whatever remains
                // in the target. For example, when inferring from string to
                // 'string | T', make a lower priority inference of string for
                // T.
                self.infer_with_priority(n, source, target, InferencePriority::NAKED_TYPE_VARIABLE);
                return;
            }
            source = self.get_union_type(&sources);
        } else if self
            .types_handle()
            .get(target)
            .flags
            .intersects(TypeFlags::INTERSECTION)
            && {
                let __arena_ts = self.types.clone();
                let ts = __arena_ts.get(target).types().to_vec();
                !core::every(&ts, |&t| self.is_non_generic_object_type(t))
            }
        {
            // We reduce intersection types unless they're simple combinations
            // of object types. For example, when inferring from
            // 'string[] & { extra: any }' to 'string[] & T' we want to remove
            // string[] and infer { extra: any } for T. But when inferring to
            // 'string[] & Iterable<T>' we want to keep the string[] on the
            // source side and infer string for T.
            if !self
                .types_handle()
                .get(source)
                .flags
                .intersects(TypeFlags::UNION)
            {
                let source_types: Vec<TypeId> = if self
                    .types_handle()
                    .get(source)
                    .flags
                    .intersects(TypeFlags::INTERSECTION)
                {
                    self.types_handle().get(source).types().to_vec()
                } else {
                    vec![source]
                };
                let __arena_target_types = self.types.clone();
                let target_types = __arena_target_types.get(target).types().to_vec();
                // Infer between identically matching source and target
                // constituents and remove the matching types.
                let (sources, targets) = self.infer_from_matching_types(
                    n,
                    source_types,
                    target_types,
                    Self::is_type_identical_to,
                    false, /*sort*/
                );
                if sources.is_empty() || targets.is_empty() {
                    return;
                }
                source = self.get_intersection_type(&sources);
                target = self.get_intersection_type(&targets);
            }
        }
        if self
            .types_handle()
            .get(target)
            .flags
            .intersects(TypeFlags::INDEXED_ACCESS | TypeFlags::SUBSTITUTION)
        {
            if self.is_no_infer_type(target) {
                return;
            }
            target = self.get_actual_type_variable(target);
        }
        if self
            .types_handle()
            .get(target)
            .flags
            .intersects(TypeFlags::TYPE_VARIABLE)
        {
            // Skip inference if the source is "blocked", which is used by the
            // language service to prevent inference on nodes currently being
            // edited.
            if self.is_from_inference_blocked_source(source) {
                return;
            }
            if let Some(index) = get_inference_info_for_type(&self.types, n, target) {
                // If target is a type parameter, make an inference, unless the
                // source type contains a "non-inferrable" type. Types with this
                // flag set are markers used to prevent inference.
                //
                // For example:
                //     - anyFunctionType is a wildcard type that's used to avoid
                //       contextually typing functions; it's internal, so should
                //       not be exposed to the user by adding it as a candidate.
                //     - autoType (and autoArrayType) is a special "any" used in
                //       control flow; like anyFunctionType, it's internal and
                //       should not be observable.
                //     - silentNeverType is returned by getInferredType when
                //       instantiating a generic function for inference (and a
                //       type variable has no mapping).
                //
                // This flag is infectious; if we produce Box<never> (where
                // never is silentNeverType), Box<never> is also non-inferrable.
                //
                // As a special case, also ignore nonInferrableAnyType, which is
                // a special form of the any type used as a stand-in for binding
                // elements when they are being inferred.
                if self
                    .types_handle()
                    .get(source)
                    .object_flags
                    .intersects(ObjectFlags::NON_INFERRABLE_TYPE)
                    || source == self.non_inferrable_any_type
                {
                    return;
                }
                if !n.inferences[index].is_fixed {
                    let candidate = n.propagation_type.unwrap_or(source);
                    if candidate == self.blocked_string_type {
                        return;
                    }
                    if n.priority.0 < n.inferences[index].priority.0 {
                        let inference = &mut n.inferences[index];
                        inference.candidates.clear();
                        inference.contra_candidates.clear();
                        inference.top_level = true;
                        inference.priority = n.priority;
                    }
                    if n.priority == n.inferences[index].priority {
                        // We make contravariant inferences only if we are in a
                        // pure contravariant position, i.e. only if we have not
                        // descended into a bivariant position.
                        if n.contravariant && !n.bivariant {
                            if !n.inferences[index].contra_candidates.contains(&candidate) {
                                n.inferences[index].contra_candidates.push(candidate);
                                clear_cached_inferences(&mut n.inferences);
                            }
                        } else if !n.inferences[index].candidates.contains(&candidate) {
                            n.inferences[index].candidates.push(candidate);
                            clear_cached_inferences(&mut n.inferences);
                        }
                    }
                    if !n.priority.intersects(InferencePriority::RETURN_TYPE)
                        && self
                            .types_handle()
                            .get(target)
                            .flags
                            .intersects(TypeFlags::TYPE_PARAMETER)
                        && n.inferences[index].top_level
                        && !self.is_type_parameter_at_top_level(
                            n.original_target.expect("originalTarget"),
                            target,
                            0,
                        )
                    {
                        n.inferences[index].top_level = false;
                        clear_cached_inferences(&mut n.inferences);
                    }
                }
                n.inference_priority = InferencePriority(n.inference_priority.0.min(n.priority.0));
                return;
            }
            // Infer to the simplified version of an indexed access, if
            // possible, to (hopefully) expose more bare type parameters to the
            // inference engine.
            let simplified = self.get_simplified_type(target, false /*writing*/);
            if simplified != target {
                self.infer_from_types(n, source, simplified);
            } else if self
                .types_handle()
                .get(target)
                .flags
                .intersects(TypeFlags::INDEXED_ACCESS)
            {
                let (index_type, object_type) = {
                    let __arena_t = self.types.clone();
                    let t = __arena_t.get(target);
                    let ia = t.as_indexed_access_type();
                    (ia.index_type, ia.object_type)
                };
                let index_type = self
                    .get_simplified_type(index_type.expect("indexType"), false /*writing*/);
                // Generally simplifications of instantiable indexes are avoided
                // to keep relationship checking correct, however if our target
                // is an access, we can consider that key of that access to be
                // "instantiated", since we're looking to find the inference
                // goal in any way we can.
                if self
                    .types_handle()
                    .get(index_type)
                    .flags
                    .intersects(TypeFlags::INSTANTIABLE)
                {
                    let object_type = self.get_simplified_type(
                        object_type.expect("objectType"),
                        false, /*writing*/
                    );
                    let simplified = self.distribute_index_over_object_type(
                        object_type,
                        index_type,
                        false, /*writing*/
                    );
                    if let Some(simplified) = simplified {
                        if simplified != target {
                            self.infer_from_types(n, source, simplified);
                        }
                    }
                }
            }
        }
        let __arena_source_flags = self.types.clone();
        let source_flags = __arena_source_flags.get(source).flags;
        let __arena_source_object_flags = self.types.clone();
        let source_object_flags = __arena_source_object_flags.get(source).object_flags;
        let __arena_target_flags = self.types.clone();
        let target_flags = __arena_target_flags.get(target).flags;
        let __arena_target_object_flags = self.types.clone();
        let target_object_flags = __arena_target_object_flags.get(target).object_flags;
        if source_object_flags.intersects(ObjectFlags::REFERENCE)
            && target_object_flags.intersects(ObjectFlags::REFERENCE)
            && (self.types_handle().get(source).target()
                == self.types_handle().get(target).target()
                || self.is_array_type(source) && self.is_array_type(target))
            && !(self
                .types_handle()
                .get(source)
                .as_type_reference()
                .node
                .is_some()
                && self
                    .types_handle()
                    .get(target)
                    .as_type_reference()
                    .node
                    .is_some())
        {
            // If source and target are references to the same generic type,
            // infer from type arguments.
            self.invoke_once(n, source, target, Self::infer_from_reference_type_arguments);
        } else if source_flags.intersects(TypeFlags::INDEX)
            && target_flags.intersects(TypeFlags::INDEX)
        {
            let __arena___guard_source_target = self.types.clone();
            let __guard_source_target = __arena___guard_source_target.get(source).clone();
            let source_target = __guard_source_target
                .as_index_type()
                .target
                .expect("index target");
            let __arena___guard_target_target = self.types.clone();
            let __guard_target_target = __arena___guard_target_target.get(target).clone();
            let target_target = __guard_target_target
                .as_index_type()
                .target
                .expect("index target");
            self.infer_from_contravariant_types(n, source_target, target_target);
        } else if (crate::checker_d::is_literal_type(&self.types, source)
            || source_flags.intersects(TypeFlags::STRING))
            && target_flags.intersects(TypeFlags::INDEX)
        {
            let empty = self.create_empty_object_type_from_string_literal(source);
            let __arena___guard_target_target = self.types.clone();
            let __guard_target_target = __arena___guard_target_target.get(target).clone();
            let target_target = __guard_target_target
                .as_index_type()
                .target
                .expect("index target");
            self.infer_from_contravariant_types_with_priority(
                n,
                empty,
                target_target,
                InferencePriority::LITERAL_KEYOF,
            );
        } else if source_flags.intersects(TypeFlags::INDEXED_ACCESS)
            && target_flags.intersects(TypeFlags::INDEXED_ACCESS)
        {
            let (source_object_type, source_index_type) = {
                let __arena_t = self.types.clone();
                let t = __arena_t.get(source);
                let ia = t.as_indexed_access_type();
                (ia.object_type, ia.index_type)
            };
            let (target_object_type, target_index_type) = {
                let __arena_t = self.types.clone();
                let t = __arena_t.get(target);
                let ia = t.as_indexed_access_type();
                (ia.object_type, ia.index_type)
            };
            self.infer_from_types(
                n,
                source_object_type.expect("objectType"),
                target_object_type.expect("objectType"),
            );
            self.infer_from_types(
                n,
                source_index_type.expect("indexType"),
                target_index_type.expect("indexType"),
            );
        } else if source_flags.intersects(TypeFlags::STRING_MAPPING)
            && target_flags.intersects(TypeFlags::STRING_MAPPING)
        {
            let __arena_source_symbol = self.types.clone();
            let source_symbol = __arena_source_symbol.get(source).symbol;
            let __arena_target_symbol = self.types.clone();
            let target_symbol = __arena_target_symbol.get(target).symbol;
            if source_symbol == target_symbol {
                let __arena___guard_source_target = self.types.clone();
                let __guard_source_target = __arena___guard_source_target.get(source).clone();
                let source_target = __guard_source_target
                    .as_string_mapping_type()
                    .target
                    .expect("string mapping target");
                let __arena___guard_target_target = self.types.clone();
                let __guard_target_target = __arena___guard_target_target.get(target).clone();
                let target_target = __guard_target_target
                    .as_string_mapping_type()
                    .target
                    .expect("string mapping target");
                self.infer_from_types(n, source_target, target_target);
            }
        } else if source_flags.intersects(TypeFlags::SUBSTITUTION) {
            let __arena___guard_base_type = self.types.clone();
            let __guard_base_type = __arena___guard_base_type.get(source).clone();
            let base_type = __guard_base_type
                .as_substitution_type()
                .base_type
                .expect("substitution baseType");
            self.infer_from_types(n, base_type, target);
            // Make substitute inference at a lower priority.
            let substitution = self.get_substitution_intersection(source);
            self.infer_with_priority(
                n,
                substitution,
                target,
                InferencePriority::SUBSTITUTE_SOURCE,
            );
        } else if target_flags.intersects(TypeFlags::CONDITIONAL) {
            self.invoke_once(n, source, target, Self::infer_to_conditional_type);
        } else if target_flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
            let __arena_targets = self.types.clone();
            let targets = __arena_targets.get(target).types().to_vec();
            self.infer_to_multiple_types(n, source, &targets, target_flags);
        } else if source_flags.intersects(TypeFlags::UNION) {
            // Source is a union or intersection type, infer from each
            // constituent type.
            let __arena_sources = self.types.clone();
            let sources = __arena_sources.get(source).types().to_vec();
            for source_type in sources {
                self.infer_from_types(n, source_type, target);
            }
        } else if target_flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            self.infer_to_template_literal_type(n, source, target);
        } else {
            source = self.get_reduced_type(source);
            if self.is_generic_mapped_type(source) && self.is_generic_mapped_type(target) {
                self.invoke_once(n, source, target, Self::infer_from_generic_mapped_types);
            }
            let __arena_source_flags = self.types.clone();
            let source_flags = __arena_source_flags.get(source).flags;
            if !(n.priority.intersects(InferencePriority::NO_CONSTRAINTS)
                && source_flags.intersects(TypeFlags::INTERSECTION | TypeFlags::INSTANTIABLE))
            {
                let apparent_source = self.get_apparent_type(source);
                // getApparentType can return _any_ type, since an indexed
                // access or conditional may simplify to any other type. If
                // that occurs and it doesn't simplify to an object or
                // intersection, we'll need to restart `inferFromTypes` with
                // the simplified source.
                let __arena_apparent_flags = self.types.clone();
                let apparent_flags = __arena_apparent_flags.get(apparent_source).flags;
                if apparent_source != source
                    && !apparent_flags.intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION)
                {
                    self.infer_from_types(n, apparent_source, target);
                    return;
                }
                source = apparent_source;
            }
            if self
                .types_handle()
                .get(source)
                .flags
                .intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION)
            {
                self.invoke_once(n, source, target, Self::infer_from_object_types);
            }
        }
    }

    /// `(c *Checker) inferFromAliasTypeArguments` (inference.go).
    fn infer_from_alias_type_arguments(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
    ) {
        // Source and target are types originating in the same generic type
        // alias declaration. Simply infer from source type arguments to
        // target type arguments, with defaults applied.
        let (source_alias, target_alias) = {
            let __arena_s = self.types.clone();
            let s = __arena_s.get(source);
            let __arena_t = self.types.clone();
            let t = __arena_t.get(target);
            (s.alias().cloned(), t.alias().cloned())
        };
        let source_alias = source_alias.expect("source alias");
        let target_alias = target_alias.expect("target alias");
        let symbol = source_alias.symbol.expect("alias symbol");
        let params = self.type_alias_links.get(symbol).type_parameters.clone();
        let min_params = self.get_min_type_argument_count(&params);
        let node_is_in_js_file = {
            let value_declaration = self.sym(symbol).value_declaration;
            match value_declaration {
                Some(d) => ast::is_in_js_file(Some(d), &self.program_nodes(d)),
                None => ast::is_in_js_file(None, &[]),
            }
        };
        let source_types = self.fill_missing_type_arguments(
            &source_alias.type_arguments,
            &params,
            min_params,
            node_is_in_js_file,
        );
        let target_types = self.fill_missing_type_arguments(
            &target_alias.type_arguments,
            &params,
            min_params,
            node_is_in_js_file,
        );
        let variances = self.get_alias_variances(symbol);
        self.infer_from_type_arguments(n, &source_types, &target_types, &variances);
    }

    /// `(c *Checker) inferFromReferenceTypeArguments` (inference.go).
    fn infer_from_reference_type_arguments(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
    ) {
        let source_types = self.get_type_arguments(source);
        let target_types = self.get_type_arguments(target);
        let __arena___guard_target_target = self.types.clone();
        let __guard_target_target = __arena___guard_target_target.get(target).clone();
        let target_target = __guard_target_target
            .as_type_reference()
            .object_type
            .target
            .expect("reference target");
        let variances = self.get_variances(target_target);
        self.infer_from_type_arguments(n, &source_types, &target_types, &variances);
    }

    /// `(c *Checker) inferFromTypeArguments` (inference.go).
    fn infer_from_type_arguments(
        &mut self,
        n: &mut InferenceState,
        source_types: &[TypeId],
        target_types: &[TypeId],
        variances: &[crate::types::VarianceFlags],
    ) {
        for i in 0..min(source_types.len(), target_types.len()) {
            if i < variances.len()
                && (variances[i] & crate::types::VarianceFlags::VARIANCE_MASK)
                    == crate::types::VarianceFlags::CONTRAVARIANT
            {
                self.infer_from_contravariant_types(n, source_types[i], target_types[i]);
            } else {
                self.infer_from_types(n, source_types[i], target_types[i]);
            }
        }
    }

    /// `(c *Checker) inferWithPriority` (inference.go).
    fn infer_with_priority(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
        new_priority: InferencePriority,
    ) {
        let save_priority = n.priority;
        n.priority |= new_priority;
        self.infer_from_types(n, source, target);
        n.priority = save_priority;
    }

    /// `(c *Checker) inferFromContravariantTypesWithPriority` (inference.go).
    fn infer_from_contravariant_types_with_priority(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
        new_priority: InferencePriority,
    ) {
        let save_priority = n.priority;
        n.priority |= new_priority;
        self.infer_from_contravariant_types(n, source, target);
        n.priority = save_priority;
    }

    /// `(c *Checker) inferFromContravariantTypes` (inference.go).
    fn infer_from_contravariant_types(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
    ) {
        n.contravariant = !n.contravariant;
        self.infer_from_types(n, source, target);
        n.contravariant = !n.contravariant;
    }

    /// `(c *Checker) inferFromContravariantTypesIfStrictFunctionTypes`
    /// (inference.go).
    fn infer_from_contravariant_types_if_strict_function_types(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
    ) {
        if self.strict_function_types || n.priority.intersects(InferencePriority::ALWAYS_STRICT) {
            self.infer_from_contravariant_types(n, source, target);
        } else {
            self.infer_from_types(n, source, target);
        }
    }

    /// `(c *Checker) invokeOnce` (inference.go). Ensure an inference action
    /// is performed only once for the given source and target types. This
    /// includes two things: avoiding inferring between the same pair of
    /// source and target types, and avoiding circularly inferring between
    /// source and target types. For an example of the last, consider if we
    /// are inferring between source type `type Deep<T> = { next:
    /// Deep<Deep<T>> }` and target type `type Loop<U> = { next: Loop<U> }`.
    /// We would then infer between the types of the `next` property:
    /// `Deep<Deep<T>>` = `{ next: Deep<Deep<Deep<T>>> }` and `Loop<U>` = `{
    /// next: Loop<U> }`. We will then infer again between the types of the
    /// `next` property: `Deep<Deep<Deep<T>>>` and `Loop<U>`, and so on, such
    /// that we would be forever inferring between instantiations of the same
    /// types `Deep` and `Loop`. In particular, we would be inferring from
    /// increasingly deep instantiations of `Deep` to `Loop`, such that we
    /// would go on inferring forever, even though we would never infer
    /// between the same pair of types.
    fn invoke_once(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
        action: fn(&mut Checker, &mut InferenceState, TypeId, TypeId),
    ) {
        let key = InferenceKey {
            source,
            target,
            priority: n.priority,
            contravariant: n.contravariant,
            bivariant: n.bivariant,
        };
        if let Some(&status) = n.visited.get(&key) {
            n.inference_priority = InferencePriority(n.inference_priority.0.min(status.0));
            return;
        }
        n.visited.insert(key, InferencePriority::CIRCULARITY);
        let save_inference_priority = n.inference_priority;
        n.inference_priority = InferencePriority::MAX_VALUE;
        // We stop inferring and report a circularity if we encounter
        // duplicate recursion identities on both the source side and the
        // target side.
        let save_expanding_flags = n.expanding_flags;
        n.source_stack.push(source);
        n.target_stack.push(target);
        if self.is_deeply_nested_type(source, &n.source_stack, 2) {
            n.expanding_flags |= ExpandingFlags::SOURCE;
        }
        if self.is_deeply_nested_type(target, &n.target_stack, 2) {
            n.expanding_flags |= ExpandingFlags::TARGET;
        }
        if n.expanding_flags != ExpandingFlags::BOTH {
            action(self, n, source, target);
        } else {
            n.inference_priority = InferencePriority::CIRCULARITY;
        }
        n.target_stack.pop();
        n.source_stack.pop();
        n.expanding_flags = save_expanding_flags;
        n.visited.insert(key, n.inference_priority);
        n.inference_priority =
            InferencePriority(n.inference_priority.0.min(save_inference_priority.0));
    }

    /// `(c *Checker) inferFromMatchingTypes` (inference.go).
    fn infer_from_matching_types(
        &mut self,
        n: &mut InferenceState,
        sources: Vec<TypeId>,
        targets: Vec<TypeId>,
        matches: fn(&mut Checker, TypeId, TypeId) -> bool,
        sort: bool,
    ) -> (Vec<TypeId>, Vec<TypeId>) {
        let mut matched_sources: Vec<TypeId> = Vec::new();
        let mut matched_targets: Vec<TypeId> = Vec::new();
        for &t in &targets {
            for &s in &sources {
                if matches(self, s, t) {
                    if !sort {
                        self.infer_from_types(n, s, t);
                    }
                    if !matched_sources.contains(&s) {
                        matched_sources.push(s);
                    }
                    if !matched_targets.contains(&t) {
                        matched_targets.push(t);
                    }
                }
            }
        }
        if sort {
            // Sort target types by decreasing depth of generic instantiations.
            // Intuitively, a successful inference from a type argument with
            // deeper nesting is of higher quality because we've stripped away
            // more layers of type instantiations that otherwise might skew the
            // results. For example, when inferring from string[] | string[][]
            // to T[] | T[][], the inference of string we make from relating
            // string[][] to T[][] is of higher quality than the inference of
            // string[] we make relating string[][] to T[].
            matched_targets.sort_by(|&a, &b| compare_types_and_depth(self, a, b).cmp(&0));
            for &t in &matched_targets {
                for &s in &matched_sources {
                    if matches(self, s, t) {
                        self.infer_from_types(n, s, t);
                    }
                }
            }
        }
        let mut sources = sources;
        let mut targets = targets;
        if !matched_sources.is_empty() {
            sources = core::filter(&sources, |t| !matched_sources.contains(t)).into_owned();
        }
        if !matched_targets.is_empty() {
            targets = core::filter(&targets, |t| !matched_targets.contains(t)).into_owned();
        }
        (sources, targets)
    }

    /// `(c *Checker) inferToMultipleTypes` (inference.go).
    fn infer_to_multiple_types(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        targets: &[TypeId],
        target_flags: TypeFlags,
    ) {
        let mut type_variable_count = 0;
        if target_flags.intersects(TypeFlags::UNION) {
            let mut naked_type_variable: Option<TypeId> = None;
            let sources: Vec<TypeId> = if self
                .types_handle()
                .get(source)
                .flags
                .intersects(TypeFlags::UNION)
            {
                self.types_handle().get(source).types().to_vec()
            } else {
                vec![source]
            };
            let mut matched = vec![false; sources.len()];
            let mut inference_circularity = false;
            // First infer to types that are not naked type variables. For each
            // source type we track whether inferences were made from that
            // particular type to some target with equal priority (i.e. of
            // equal quality) to what we would infer for a naked type
            // parameter.
            for &t in targets {
                if get_inference_info_for_type(&self.types, n, t).is_some() {
                    naked_type_variable = Some(t);
                    type_variable_count += 1;
                } else {
                    for i in 0..sources.len() {
                        let save_inference_priority = n.inference_priority;
                        n.inference_priority = InferencePriority::MAX_VALUE;
                        self.infer_from_types(n, sources[i], t);
                        if n.inference_priority == n.priority {
                            matched[i] = true;
                        }
                        inference_circularity = inference_circularity
                            || n.inference_priority == InferencePriority::CIRCULARITY;
                        n.inference_priority = InferencePriority(
                            n.inference_priority.0.min(save_inference_priority.0),
                        );
                    }
                }
            }
            if type_variable_count == 0 {
                // If every target is an intersection of types containing a
                // single naked type variable, make a lower priority inference
                // to that type variable. This handles inferring from 'A | B'
                // to 'T & (X | Y)' where we want to infer 'A | B' for T.
                if let Some(intersection_type_variable) =
                    get_single_type_variable_from_intersection_types(&self.types, n, targets)
                {
                    self.infer_with_priority(
                        n,
                        source,
                        intersection_type_variable,
                        InferencePriority::NAKED_TYPE_VARIABLE,
                    );
                }
                return;
            }
            // If the target has a single naked type variable and no inference
            // circularities were encountered above (meaning we explored the
            // types fully), create a union of the source types from which no
            // inferences have been made so far and infer from that union to
            // the naked type variable.
            if type_variable_count == 1 && !inference_circularity {
                let mut unmatched: Vec<TypeId> = Vec::new();
                for (i, &s) in sources.iter().enumerate() {
                    if !matched[i] {
                        unmatched.push(s);
                    }
                }
                if !unmatched.is_empty() {
                    let union = self.get_union_type(&unmatched);
                    self.infer_from_types(
                        n,
                        union,
                        naked_type_variable.expect("nakedTypeVariable"),
                    );
                    return;
                }
            }
        } else {
            // We infer from types that are not naked type variables first so
            // that inferences we make from nested naked type variables are
            // given slightly higher priority by virtue of being first in the
            // candidates array.
            for &t in targets {
                if get_inference_info_for_type(&self.types, n, t).is_some() {
                    type_variable_count += 1;
                } else {
                    self.infer_from_types(n, source, t);
                }
            }
        }
        // Inferences directly to naked type variables are given lower priority
        // as they are less specific. For example, when inferring from
        // Promise<string> to T | Promise<T>, we want to infer string for T,
        // not Promise<string> | string. For intersection types we only infer
        // to single naked type variables.
        if target_flags.intersects(TypeFlags::INTERSECTION) && type_variable_count == 1
            || !target_flags.intersects(TypeFlags::INTERSECTION) && type_variable_count > 0
        {
            for &t in targets {
                if get_inference_info_for_type(&self.types, n, t).is_some() {
                    self.infer_with_priority(n, source, t, InferencePriority::NAKED_TYPE_VARIABLE);
                }
            }
        }
    }

    /// `(c *Checker) inferToMultipleTypesWithPriority` (inference.go).
    fn infer_to_multiple_types_with_priority(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        targets: &[TypeId],
        target_flags: TypeFlags,
        new_priority: InferencePriority,
    ) {
        let save_priority = n.priority;
        n.priority |= new_priority;
        self.infer_to_multiple_types(n, source, targets, target_flags);
        n.priority = save_priority;
    }

    /// `(c *Checker) inferToConditionalType` (inference.go).
    fn infer_to_conditional_type(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
    ) {
        if self
            .types_handle()
            .get(source)
            .flags
            .intersects(TypeFlags::CONDITIONAL)
        {
            let (source_check_type, source_extends_type) = {
                let __arena_guard = self.types.clone();
                let guard = __arena_guard.get(source);
                let c = guard.as_conditional_type();
                (c.check_type, c.extends_type)
            };
            let (target_check_type, target_extends_type) = {
                let __arena_guard = self.types.clone();
                let guard = __arena_guard.get(target);
                let c = guard.as_conditional_type();
                (c.check_type, c.extends_type)
            };
            self.infer_from_types(
                n,
                get_non_distributed_type_parameter(
                    &self.types,
                    source_check_type.expect("checkType"),
                ),
                target_check_type.expect("checkType"),
            );
            self.infer_from_types(
                n,
                get_non_distributed_type_parameter(
                    &self.types,
                    source_extends_type.expect("extendsType"),
                ),
                target_extends_type.expect("extendsType"),
            );
            let source_true = self.get_true_type_from_conditional_type(source);
            let target_true = self.get_true_type_from_conditional_type(target);
            self.infer_from_types(
                n,
                get_non_distributed_type_parameter(&self.types, source_true),
                target_true,
            );
            let source_false = self.get_false_type_from_conditional_type(source);
            let target_false = self.get_false_type_from_conditional_type(target);
            self.infer_from_types(
                n,
                get_non_distributed_type_parameter(&self.types, source_false),
                target_false,
            );
        } else {
            let true_type = self.get_true_type_from_conditional_type(target);
            let false_type = self.get_false_type_from_conditional_type(target);
            let target_types = vec![true_type, false_type];
            let __arena_target_flags = self.types.clone();
            let target_flags = __arena_target_flags.get(target).flags;
            self.infer_to_multiple_types_with_priority(
                n,
                source,
                &target_types,
                target_flags,
                core::if_else(
                    n.contravariant,
                    InferencePriority::CONTRAVARIANT_CONDITIONAL,
                    InferencePriority::NONE_PRIORITY,
                ),
            );
        }
    }

    /// `(c *Checker) inferToTemplateLiteralType` (inference.go). PORT: Go's
    /// `target *TemplateLiteralType` becomes `target: TypeId` (the arena id);
    /// the `TemplateLiteralType` snapshot is cloned out of the arena up front.
    fn infer_to_template_literal_type(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
    ) {
        let target_data: TemplateLiteralType =
            (*self.types_handle().get(target).as_template_literal_type()).clone();
        let matches = self
            .infer_types_from_template_literal_type(source, &target_data, &mut None, Comparer::Assignable)
            .unwrap_or_default();
        let types = target_data.types.clone();
        // When the target template literal contains only placeholders (meaning
        // that inference is intended to extract single characters and
        // remainder strings) and inference fails to produce matches, we want
        // to infer 'never' for each placeholder such that instantiation with
        // the inferred value(s) produces 'never', a type for which an
        // assignment check will fail. If we make no inferences, we'll likely
        // end up with the constraint 'string' which, upon instantiation, would
        // collapse all the placeholders to just 'string', and an assignment
        // check might succeed. That would be a pointless and confusing
        // outcome.
        if !matches.is_empty() || target_data.texts.iter().all(|s| s.is_empty()) {
            for (i, &target_t) in types.iter().enumerate() {
                let source_t = if !matches.is_empty() {
                    matches[i]
                } else {
                    self.never_type
                };
                // If we are inferring from a string literal type to a type
                // variable whose constraint includes one of the allowed
                // template literal placeholder types, infer from a literal
                // type corresponding to the constraint.
                if self
                    .types_handle()
                    .get(source_t)
                    .flags
                    .intersects(TypeFlags::STRING_LITERAL)
                    && self
                        .types_handle()
                        .get(target_t)
                        .flags
                        .intersects(TypeFlags::TYPE_VARIABLE)
                {
                    if let Some(index) = get_inference_info_for_type(&self.types, n, target_t) {
                        let type_parameter = n.inferences[index].type_parameter;
                        if let Some(constraint) =
                            type_parameter.and_then(|tp| self.get_base_constraint_of_type(tp))
                        {
                            if !crate::utilities::is_type_any(&self.types, constraint) {
                                let mut all_type_flags = TypeFlags::NONE;
                                let __arena_distributed = self.types.clone();
                                let distributed =
                                    __arena_distributed.get(constraint).distributed(constraint);
                                for &t in &distributed {
                                    all_type_flags |= self.types_handle().get(t).flags;
                                }
                                // If the constraint contains `string`, we don't
                                // need to look for a more preferred type.
                                if !all_type_flags.intersects(TypeFlags::STRING) {
                                    let str_ = crate::checker_d::get_string_literal_value(
                                        &self.types,
                                        source_t,
                                    );
                                    // If the type contains `number` or a number
                                    // literal and the string isn't a valid
                                    // number, exclude numbers.
                                    if all_type_flags.intersects(TypeFlags::NUMBER_LIKE)
                                        && !crate::utilities::is_valid_number_string(&str_, true)
                                    {
                                        all_type_flags.remove(TypeFlags::NUMBER_LIKE);
                                    }
                                    // If the type contains `bigint` or a bigint
                                    // literal and the string isn't a valid
                                    // bigint, exclude bigints.
                                    if all_type_flags.intersects(TypeFlags::BIG_INT_LIKE)
                                        && !crate::utilities::is_valid_big_int_string(&str_, true)
                                    {
                                        all_type_flags.remove(TypeFlags::BIG_INT_LIKE);
                                    }
                                    // `choose` is a nested func in Go; here a
                                    // closure capturing `source_t`, `str_` and
                                    // `all_type_flags`.
                                    let choose =
                                        |c: &mut Checker, left: TypeId, right: TypeId| -> TypeId {
                                            let __arena_left_flags = c.types.clone();
                                            let left_flags = __arena_left_flags.get(left).flags;
                                            let __arena_right_flags = c.types.clone();
                                            let right_flags = __arena_right_flags.get(right).flags;
                                            if (right_flags.0 & all_type_flags.0) == 0 {
                                                return left;
                                            }
                                            if left_flags.intersects(TypeFlags::STRING) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::STRING) {
                                                return source_t;
                                            }
                                            if left_flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::TEMPLATE_LITERAL)
                                                && c.is_type_matched_by_template_literal_type(
                                                    source_t,
                                                    right,
                                                    None,
                                                    Comparer::Assignable,
                                                )
                                            {
                                                return source_t;
                                            }
                                            if left_flags.intersects(TypeFlags::STRING_MAPPING) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::STRING_MAPPING)
                                                && str_
                                                    == crate::checker_d::apply_string_mapping(
                                                        c,
                                                        c.types_handle().get(right).symbol,
                                                        &str_,
                                                    )
                                            {
                                                return source_t;
                                            }
                                            if left_flags.intersects(TypeFlags::STRING_LITERAL) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::STRING_LITERAL)
                                                && crate::checker_d::get_string_literal_value(
                                                    &c.types, right,
                                                ) == str_
                                            {
                                                return right;
                                            }
                                            if left_flags.intersects(TypeFlags::NUMBER) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::NUMBER) {
                                                return c.get_number_literal_type(
                                                    tsc_jsnum::from_string(&str_),
                                                );
                                            }
                                            if left_flags.intersects(TypeFlags::ENUM) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::ENUM) {
                                                return c.get_number_literal_type(
                                                    tsc_jsnum::from_string(&str_),
                                                );
                                            }
                                            if left_flags.intersects(TypeFlags::NUMBER_LITERAL) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::NUMBER_LITERAL)
                                                && crate::checker_d::get_number_literal_value(
                                                    &c.types, right,
                                                ) == tsc_jsnum::from_string(&str_)
                                            {
                                                return right;
                                            }
                                            if left_flags.intersects(TypeFlags::BIG_INT) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::BIG_INT) {
                                                return c.parse_big_int_literal_type(&str_);
                                            }
                                            if left_flags.intersects(TypeFlags::BIG_INT_LITERAL) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::BIG_INT_LITERAL)
                                                && crate::utilities::pseudo_big_int_to_string(
                                                    crate::checker_d::get_big_int_literal_value(
                                                        &c.types, right,
                                                    ),
                                                ) == str_
                                            {
                                                return right;
                                            }
                                            if left_flags.intersects(TypeFlags::BOOLEAN) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::BOOLEAN) {
                                                if str_ == "true" {
                                                    return c.true_type;
                                                } else if str_ == "false" {
                                                    return c.false_type;
                                                } else {
                                                    return c.boolean_type;
                                                }
                                            }
                                            if left_flags.intersects(TypeFlags::BOOLEAN_LITERAL) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::BOOLEAN_LITERAL)
                                                && core::if_else(
                                                    crate::checker_d::get_boolean_literal_value(
                                                        &c.types, right,
                                                    ),
                                                    "true",
                                                    "false",
                                                ) == str_
                                            {
                                                return right;
                                            }
                                            if left_flags.intersects(TypeFlags::UNDEFINED) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::UNDEFINED)
                                                && c.types_handle()
                                                    .get(right)
                                                    .as_intrinsic_type()
                                                    .intrinsic_name
                                                    == str_
                                            {
                                                return right;
                                            }
                                            if left_flags.intersects(TypeFlags::NULL) {
                                                return left;
                                            }
                                            if right_flags.intersects(TypeFlags::NULL)
                                                && c.types_handle()
                                                    .get(right)
                                                    .as_intrinsic_type()
                                                    .intrinsic_name
                                                    == str_
                                            {
                                                return right;
                                            }
                                            left
                                        };
                                    let mut matching_type = self.never_type;
                                    for &t in &distributed {
                                        matching_type = choose(self, matching_type, t);
                                    }
                                    if !self
                                        .types_handle()
                                        .get(matching_type)
                                        .flags
                                        .intersects(TypeFlags::NEVER)
                                    {
                                        self.infer_from_types(n, matching_type, target_t);
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
                self.infer_from_types(n, source_t, target_t);
            }
        }
    }

    /// `(c *Checker) inferFromGenericMappedTypes` (inference.go). The source
    /// and target types are generic types `{ [P in S]: X }` and `{ [P in T]:
    /// Y }`, so we infer from S to T and from X to Y.
    fn infer_from_generic_mapped_types(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
    ) {
        let source_constraint = self
            .get_constraint_type_from_mapped_type(source)
            .unwrap_or(self.never_type);
        let target_constraint = self
            .get_constraint_type_from_mapped_type(target)
            .unwrap_or(self.never_type);
        self.infer_from_types(n, source_constraint, target_constraint);
        let source_template = self
            .get_template_type_from_mapped_type(source)
            .unwrap_or(self.never_type);
        let target_template = self
            .get_template_type_from_mapped_type(target)
            .unwrap_or(self.never_type);
        self.infer_from_types(n, source_template, target_template);
        let source_name_type = self.get_name_type_from_mapped_type(source);
        let target_name_type = self.get_name_type_from_mapped_type(target);
        if let (Some(source_name_type), Some(target_name_type)) =
            (source_name_type, target_name_type)
        {
            self.infer_from_types(n, source_name_type, target_name_type);
        }
    }

    /// `(c *Checker) inferFromObjectTypes` (inference.go).
    fn infer_from_object_types(&mut self, n: &mut InferenceState, source: TypeId, target: TypeId) {
        let __arena_source_object_flags = self.types.clone();
        let source_object_flags = __arena_source_object_flags.get(source).object_flags;
        let __arena_target_object_flags = self.types.clone();
        let target_object_flags = __arena_target_object_flags.get(target).object_flags;
        if source_object_flags.intersects(ObjectFlags::REFERENCE)
            && target_object_flags.intersects(ObjectFlags::REFERENCE)
            && (self.types_handle().get(source).target()
                == self.types_handle().get(target).target()
                || self.is_array_type(source) && self.is_array_type(target))
        {
            // If source and target are references to the same generic type,
            // infer from type arguments.
            self.infer_from_reference_type_arguments(n, source, target);
            return;
        }
        if self.is_generic_mapped_type(source) && self.is_generic_mapped_type(target) {
            self.infer_from_generic_mapped_types(n, source, target);
        }
        if self
            .types_handle()
            .get(target)
            .object_flags
            .intersects(ObjectFlags::MAPPED)
            && !self.mapped_type_declaration_has_name_type(target)
        {
            let constraint_type = self
                .get_constraint_type_from_mapped_type(target)
                .unwrap_or(self.never_type);
            if self.infer_to_mapped_type(n, source, target, constraint_type) {
                return;
            }
        }
        // Infer from the members of source and target only if the two types
        // are possibly related.
        if self.types_definitely_unrelated(source, target) {
            return;
        }
        if self.is_array_or_tuple_type(source) {
            if is_tuple_type(&self.types, target) {
                let source_arity = self.get_type_reference_arity(source);
                let target_arity = self.get_type_reference_arity(target);
                let element_types = self.get_type_arguments(target);
                let __arena_target_tuple = self.types.clone();
                let target_tuple = __arena_target_tuple
                    .target_tuple_type(target)
                    .expect("target tuple type");
                let __arena___guard_element_infos = self.types.clone();
                let __guard_element_infos = __arena___guard_element_infos.get(target_tuple).clone();
                let element_infos = __guard_element_infos.as_tuple_type().element_infos.clone();
                let source_type_arguments = self.get_type_arguments(source);
                // When source and target are tuple types with the same
                // structure (fixed, variadic, and rest are matched to the same
                // kind in each position), simply infer between the element
                // types.
                if is_tuple_type(&self.types, source)
                    && self.is_tuple_type_structure_matching(source, target)
                {
                    for i in 0..target_arity {
                        self.infer_from_types(n, source_type_arguments[i], element_types[i]);
                    }
                    return;
                }
                let mut start_length = 0usize;
                let mut end_length = 0usize;
                let source_tuple_target = if is_tuple_type(&self.types, source) {
                    self.types_handle().target_tuple_type(source)
                } else {
                    None
                };
                if let Some(source_tuple) = source_tuple_target {
                    let __arena_source_fixed_length = self.types.clone();
                    let source_fixed_length = __arena_source_fixed_length
                        .get(source_tuple)
                        .as_tuple_type()
                        .fixed_length;
                    start_length = min(
                        source_fixed_length,
                        self.types_handle()
                            .get(target_tuple)
                            .as_tuple_type()
                            .fixed_length,
                    );
                    if self
                        .types_handle()
                        .get(target_tuple)
                        .as_tuple_type()
                        .combined_flags
                        .intersects(ElementFlags::VARIABLE)
                    {
                        end_length = min(
                            get_end_element_count(
                                self.types_handle().get(source_tuple).as_tuple_type(),
                                ElementFlags::FIXED,
                            ),
                            get_end_element_count(
                                self.types_handle().get(target_tuple).as_tuple_type(),
                                ElementFlags::FIXED,
                            ),
                        );
                    }
                }
                // Infer between starting fixed elements.
                for i in 0..start_length {
                    self.infer_from_types(n, source_type_arguments[i], element_types[i]);
                }
                let source_is_tuple = source_tuple_target.is_some();
                let source_has_single_rest_after_start =
                    if let Some(source_tuple) = source_tuple_target {
                        source_arity
                            .saturating_sub(start_length)
                            .saturating_sub(end_length)
                            == 1
                            && self
                                .types_handle()
                                .get(source_tuple)
                                .as_tuple_type()
                                .element_infos[start_length]
                                .flags
                                .intersects(ElementFlags::REST)
                    } else {
                        false
                    };
                if !source_is_tuple || source_has_single_rest_after_start {
                    // Single rest element remains in source, infer from that
                    // to every element in target.
                    let rest_type = source_type_arguments[start_length];
                    for i in start_length..(target_arity - end_length) {
                        let mut t = rest_type;
                        if element_infos[i].flags.intersects(ElementFlags::VARIADIC) {
                            t = self.create_array_type(t);
                        }
                        self.infer_from_types(n, t, element_types[i]);
                    }
                } else {
                    let middle_length = target_arity
                        .saturating_sub(start_length)
                        .saturating_sub(end_length);
                    if middle_length == 2 {
                        if (element_infos[start_length].flags
                            & element_infos[start_length + 1].flags)
                            .intersects(ElementFlags::VARIADIC)
                        {
                            // Middle of target is [...T, ...U] and source is
                            // tuple type.
                            if let Some(target_index) = get_inference_info_for_type(
                                &self.types,
                                n,
                                element_types[start_length],
                            ) {
                                let implied_arity = n.inferences[target_index].implied_arity;
                                if implied_arity >= 0 {
                                    // Infer slices from source based on
                                    // implied arity of T.
                                    let first = self.slice_tuple_type(
                                        source,
                                        start_length,
                                        (end_length + source_arity) as i32 - implied_arity,
                                    );
                                    self.infer_from_types(n, first, element_types[start_length]);
                                    let second = self.slice_tuple_type(
                                        source,
                                        start_length + implied_arity as usize,
                                        end_length as i32,
                                    );
                                    self.infer_from_types(
                                        n,
                                        second,
                                        element_types[start_length + 1],
                                    );
                                }
                            }
                        } else if element_infos[start_length]
                            .flags
                            .intersects(ElementFlags::VARIADIC)
                            && element_infos[start_length + 1]
                                .flags
                                .intersects(ElementFlags::REST)
                        {
                            // Middle of target is [...T, ...rest] and source is
                            // tuple type — if T is constrained by a fixed-size
                            // tuple we might be able to use its arity to infer
                            // T.
                            if let Some(info) = get_inference_info_for_type(
                                &self.types,
                                n,
                                element_types[start_length],
                            ) {
                                let constraint = n.inferences[info]
                                    .type_parameter
                                    .and_then(|tp| self.get_base_constraint_of_type(tp));
                                if let Some(constraint) = constraint {
                                    if is_tuple_type(&self.types, constraint) {
                                        let __arena_constraint_tuple = self.types.clone();
                                        let constraint_tuple = __arena_constraint_tuple
                                            .target_tuple_type(constraint)
                                            .expect("constraint tuple");
                                        if !self
                                            .types_handle()
                                            .get(constraint_tuple)
                                            .as_tuple_type()
                                            .combined_flags
                                            .intersects(ElementFlags::VARIABLE)
                                        {
                                            let __arena___guard_implied_arity = self.types.clone();
                                            let __guard_implied_arity =
                                                __arena___guard_implied_arity
                                                    .get(constraint_tuple)
                                                    .clone();
                                            let implied_arity =
                                                __guard_implied_arity.as_tuple_type().fixed_length;
                                            let first = self.slice_tuple_type(
                                                source,
                                                start_length,
                                                (source_arity
                                                    .saturating_sub(start_length + implied_arity))
                                                    as i32,
                                            );
                                            self.infer_from_types(
                                                n,
                                                first,
                                                element_types[start_length],
                                            );
                                            if let Some(rest_type) = self
                                                .get_element_type_of_slice_of_tuple_type(
                                                    source,
                                                    start_length + implied_arity,
                                                    end_length,
                                                    false,
                                                    false,
                                                )
                                            {
                                                self.infer_from_types(
                                                    n,
                                                    rest_type,
                                                    element_types[start_length + 1],
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        } else if element_infos[start_length]
                            .flags
                            .intersects(ElementFlags::REST)
                            && element_infos[start_length + 1]
                                .flags
                                .intersects(ElementFlags::VARIADIC)
                        {
                            // Middle of target is [...rest, ...T] and source is
                            // tuple type — if T is constrained by a fixed-size
                            // tuple we might be able to use its arity to infer
                            // T.
                            if let Some(info) = get_inference_info_for_type(
                                &self.types,
                                n,
                                element_types[start_length + 1],
                            ) {
                                let constraint = n.inferences[info]
                                    .type_parameter
                                    .and_then(|tp| self.get_base_constraint_of_type(tp));
                                if let Some(constraint) = constraint {
                                    if is_tuple_type(&self.types, constraint) {
                                        let __arena_constraint_tuple = self.types.clone();
                                        let constraint_tuple = __arena_constraint_tuple
                                            .target_tuple_type(constraint)
                                            .expect("constraint tuple");
                                        if !self
                                            .types_handle()
                                            .get(constraint_tuple)
                                            .as_tuple_type()
                                            .combined_flags
                                            .intersects(ElementFlags::VARIABLE)
                                        {
                                            let __arena___guard_implied_arity = self.types.clone();
                                            let __guard_implied_arity =
                                                __arena___guard_implied_arity
                                                    .get(constraint_tuple)
                                                    .clone();
                                            let implied_arity =
                                                __guard_implied_arity.as_tuple_type().fixed_length;
                                            let end_index = source_arity as isize
                                                - get_end_element_count(
                                                    self.types_handle()
                                                        .get(target_tuple)
                                                        .as_tuple_type(),
                                                    ElementFlags::FIXED,
                                                )
                                                    as isize;
                                            let start_index = end_index - implied_arity as isize;
                                            if start_index >= start_length as isize {
                                                let start_index = start_index as usize;
                                                let end_index = end_index as usize;
                                                let source_tuple =
                                                    source_tuple_target.expect("source tuple");
                                                let __arena___guard_source_element_infos =
                                                    self.types.clone();
                                                let __guard_source_element_infos =
                                                    __arena___guard_source_element_infos
                                                        .get(source_tuple);
                                                let source_element_infos =
                                                    __guard_source_element_infos
                                                        .as_tuple_type()
                                                        .element_infos
                                                        .clone();
                                                let trailing_slice = self.create_tuple_type_ex(
                                                    &source_type_arguments[start_index..end_index],
                                                    &source_element_infos[start_index..end_index],
                                                    false, /*readonly*/
                                                );
                                                if let Some(rest_type) = self
                                                    .get_element_type_of_slice_of_tuple_type(
                                                        source,
                                                        start_length,
                                                        end_length + implied_arity,
                                                        false,
                                                        false,
                                                    )
                                                {
                                                    self.infer_from_types(
                                                        n,
                                                        rest_type,
                                                        element_types[start_length],
                                                    );
                                                }
                                                self.infer_from_types(
                                                    n,
                                                    trailing_slice,
                                                    element_types[start_length + 1],
                                                );
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else if middle_length == 1
                        && element_infos[start_length]
                            .flags
                            .intersects(ElementFlags::VARIADIC)
                    {
                        // Middle of target is exactly one variadic element.
                        // Infer the slice between the fixed parts in the
                        // source. If target ends in optional element(s), make
                        // a lower priority a speculative inference.
                        let priority = core::if_else(
                            element_infos[target_arity - 1]
                                .flags
                                .intersects(ElementFlags::OPTIONAL),
                            InferencePriority::SPECULATIVE_TUPLE,
                            InferencePriority::NONE_PRIORITY,
                        );
                        let source_slice =
                            self.slice_tuple_type(source, start_length, end_length as i32);
                        self.infer_with_priority(
                            n,
                            source_slice,
                            element_types[start_length],
                            priority,
                        );
                    } else if middle_length == 1
                        && element_infos[start_length]
                            .flags
                            .intersects(ElementFlags::REST)
                    {
                        // Middle of target is exactly one rest element. If
                        // middle of source is not empty, infer union of middle
                        // element types.
                        if let Some(rest_type) = self.get_element_type_of_slice_of_tuple_type(
                            source,
                            start_length,
                            end_length,
                            false,
                            false,
                        ) {
                            self.infer_from_types(n, rest_type, element_types[start_length]);
                        }
                    }
                }
                // Infer between ending fixed elements.
                for i in 0..end_length {
                    self.infer_from_types(
                        n,
                        source_type_arguments[source_arity - i - 1],
                        element_types[target_arity - i - 1],
                    );
                }
                return;
            }
            if self.is_array_type(target) {
                self.infer_from_index_types(n, source, target);
                return;
            }
        }
        self.infer_from_properties(n, source, target);
        self.infer_from_signatures(n, source, target, SignatureKind::Call);
        self.infer_from_signatures(n, source, target, SignatureKind::Construct);
        self.infer_from_index_types(n, source, target);
    }

    /// Whether the mapped type's declaration has a `nameType` — Go reads
    /// `target.AsMappedType().declaration.NameType == nil`.
    fn mapped_type_declaration_has_name_type(&self, target: TypeId) -> bool {
        let __arena___guard_declaration = self.types.clone();
        let __guard_declaration = __arena___guard_declaration.get(target).clone();
        let declaration = __guard_declaration
            .as_mapped_type()
            .declaration
            .expect("mapped type declaration");
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((declaration).file_index());
        nodes[declaration].as_mapped_type_node().name_type.is_some()
    }

    /// `(c *Checker) inferFromProperties` (inference.go).
    fn infer_from_properties(&mut self, n: &mut InferenceState, source: TypeId, target: TypeId) {
        let properties = self.get_properties_of_object_type(target);
        for target_prop in properties {
            let name = self.sym(target_prop).name.clone();
            if let Some(source_prop) = self.get_property_of_type(source, &name) {
                let declarations = self.sym(source_prop).declarations.clone();
                let mut skip = false;
                for d in &declarations {
                    if self.is_skip_direct_inference_node(*d) {
                        skip = true;
                        break;
                    }
                }
                if !skip {
                    let source_prop_type = self.get_type_of_symbol(source_prop);
                    let source_optional = self
                        .sym(source_prop)
                        .flags
                        .intersects(ast::SymbolFlags::OPTIONAL);
                    let source_type = self.remove_missing_type(source_prop_type, source_optional);
                    let target_prop_type = self.get_type_of_symbol(target_prop);
                    let target_optional = self
                        .sym(target_prop)
                        .flags
                        .intersects(ast::SymbolFlags::OPTIONAL);
                    let target_type = self.remove_missing_type(target_prop_type, target_optional);
                    self.infer_from_types(n, source_type, target_type);
                }
            }
        }
    }

    /// `(c *Checker) inferFromSignatures` (inference.go).
    fn infer_from_signatures(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
        kind: SignatureKind,
    ) {
        let source_signatures = self.get_signatures_of_type(source, kind);
        let source_len = source_signatures.len();
        if source_len > 0 {
            // We match source and target signatures from the bottom up, and if
            // the source has fewer signatures than the target, we infer from
            // the first source signature to the excess target signatures.
            let target_signatures = self.get_signatures_of_type(target, kind);
            let target_len = target_signatures.len();
            for i in 0..target_len {
                let source_index =
                    max(source_len as i64 - target_len as i64 + i as i64, 0) as usize;
                let source_signature = self.get_base_signature(source_signatures[source_index]);
                let target_signature = self.get_erased_signature(target_signatures[i]);
                self.infer_from_signature(n, source_signature, target_signature);
            }
        }
    }

    /// `(c *Checker) inferFromSignature` (inference.go).
    fn infer_from_signature(
        &mut self,
        n: &mut InferenceState,
        source: SignatureId,
        target: SignatureId,
    ) {
        if !self
            .signature_arena
            .get(source)
            .flags
            .intersects(SignatureFlags::IS_NON_INFERRABLE)
        {
            let save_bivariant = n.bivariant;
            let kind = self
                .signature_arena
                .get(target)
                .declaration
                .map(|d| self.program_nodes(d)[d].kind)
                .unwrap_or(ast::Kind::Unknown);
            // Once we descend into a bivariant signature we remain bivariant
            // for all nested inferences.
            n.bivariant = n.bivariant
                || kind == ast::Kind::MethodDeclaration
                || kind == ast::Kind::MethodSignature
                || kind == ast::Kind::Constructor;
            self.apply_to_parameter_types(source, target, |c: &mut Checker, s, t| {
                c.infer_from_contravariant_types_if_strict_function_types(n, s, t)
            });
            n.bivariant = save_bivariant;
        }
        self.apply_to_return_types(source, target, |c: &mut Checker, s, t| {
            c.infer_from_types(n, s, t)
        });
    }

    /// `(c *Checker) applyToParameterTypes` (inference.go). PORT: the Go
    /// `func(s, t *Type)` callback takes the checker explicitly here.
    pub(crate) fn apply_to_parameter_types(
        &mut self,
        source: SignatureId,
        target: SignatureId,
        mut callback: impl FnMut(&mut Checker, TypeId, TypeId),
    ) {
        let source_count = self.get_parameter_count(source);
        let target_count = self.get_parameter_count(target);
        let source_rest_type = self.get_effective_rest_type(source);
        let target_rest_type = self.get_effective_rest_type(target);
        let mut target_non_rest_count = target_count;
        if target_rest_type.is_some() {
            target_non_rest_count -= 1;
        }
        let mut param_count = target_non_rest_count;
        if source_rest_type.is_none() {
            param_count = min(source_count, target_non_rest_count);
        }
        let source_this_type = self.get_this_type_of_signature(source);
        if let Some(source_this_type) = source_this_type {
            if let Some(target_this_type) = self.get_this_type_of_signature(target) {
                callback(self, source_this_type, target_this_type);
            }
        }
        for i in 0..param_count {
            let s = self.get_type_at_position(source, i);
            let t = self.get_type_at_position(target, i);
            callback(self, s, t);
        }
        if let Some(target_rest_type) = target_rest_type {
            let readonly = self.is_const_type_variable(Some(target_rest_type), 0)
                && !crate::checker_d::some_type(self, target_rest_type, |c, t| {
                    c.is_mutable_array_like_type(t)
                });
            // PORT: Go getRestTypeAtPosition always returns a type; the Rust
            // port wraps it in Option, so unwrap preserves Go semantics.
            let rest = self
                .get_rest_type_at_position(source, param_count, readonly)
                .expect("getRestTypeAtPosition never returns nil in Go");
            callback(self, rest, target_rest_type);
        }
    }

    /// `(c *Checker) applyToReturnTypes` (inference.go).
    pub(crate) fn apply_to_return_types(
        &mut self,
        source: SignatureId,
        target: SignatureId,
        mut callback: impl FnMut(&mut Checker, TypeId, TypeId),
    ) {
        if let Some(target_type_predicate) = self.get_type_predicate_of_signature(target) {
            if let Some(source_type_predicate) = self.get_type_predicate_of_signature(source) {
                if self.type_predicate_kinds_match(&source_type_predicate, &target_type_predicate)
                    && source_type_predicate.t.is_some()
                    && target_type_predicate.t.is_some()
                {
                    callback(
                        self,
                        source_type_predicate.t.unwrap(),
                        target_type_predicate.t.unwrap(),
                    );
                    return;
                }
            }
        }
        let target_return_type = self.get_return_type_of_signature(target);
        if (self
            .could_contain_type_variables
            .clone()
            .expect("could_contain_type_variables"))(self, target_return_type)
        {
            let source_return_type = self.get_return_type_of_signature(source);
            callback(self, source_return_type, target_return_type);
        }
    }

    /// `(c *Checker) inferFromIndexTypes` (inference.go). Inferences across
    /// mapped type index signatures are pretty much the same as inferences to
    /// homomorphic variables.
    fn infer_from_index_types(&mut self, n: &mut InferenceState, source: TypeId, target: TypeId) {
        let mut priority = InferencePriority::NONE_PRIORITY;
        if (self.types_handle().get(source).object_flags
            & self.types_handle().get(target).object_flags)
            .intersects(ObjectFlags::MAPPED)
        {
            priority = InferencePriority::HOMOMORPHIC_MAPPED_TYPE;
        }
        let index_infos = self.get_index_infos_of_type(target);
        if self.is_object_type_with_inferable_index(source) {
            for &target_info in &index_infos {
                let target_key_type = self
                    .index_info_arena
                    .get(target_info)
                    .key_type
                    .expect("keyType");
                let mut prop_types: Vec<TypeId> = Vec::new();
                let props = self.get_properties_of_type(source);
                for prop in props {
                    let literal_type = self.get_literal_type_from_property(
                        prop,
                        TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE,
                        false,
                    );
                    if self.is_applicable_index_type(literal_type, target_key_type) {
                        let mut prop_type = self.get_type_of_symbol(prop);
                        if self.sym(prop).flags.intersects(ast::SymbolFlags::OPTIONAL) {
                            prop_type = self.remove_missing_or_undefined_type(prop_type);
                        }
                        prop_types.push(prop_type);
                    }
                }
                let source_infos = self.get_index_infos_of_type(source);
                for info in source_infos {
                    let info_key_type = self.index_info_arena.get(info).key_type.expect("keyType");
                    if self.is_applicable_index_type(info_key_type, target_key_type) {
                        prop_types.push(
                            self.index_info_arena
                                .get(info)
                                .value_type
                                .expect("valueType"),
                        );
                    }
                }
                if !prop_types.is_empty() {
                    let union = self.get_union_type(&prop_types);
                    let target_value_type = self
                        .index_info_arena
                        .get(target_info)
                        .value_type
                        .expect("valueType");
                    self.infer_with_priority(n, union, target_value_type, priority);
                }
            }
        }
        for &target_info in &index_infos {
            let target_key_type = self
                .index_info_arena
                .get(target_info)
                .key_type
                .expect("keyType");
            if let Some(source_info) = self.get_applicable_index_info(source, target_key_type) {
                let source_value_type = self
                    .index_info_arena
                    .get(source_info)
                    .value_type
                    .expect("valueType");
                let target_value_type = self
                    .index_info_arena
                    .get(target_info)
                    .value_type
                    .expect("valueType");
                self.infer_with_priority(n, source_value_type, target_value_type, priority);
            }
        }
    }

    /// `(c *Checker) inferToMappedType` (inference.go).
    fn infer_to_mapped_type(
        &mut self,
        n: &mut InferenceState,
        source: TypeId,
        target: TypeId,
        constraint_type: TypeId,
    ) -> bool {
        let __arena_constraint_flags = self.types.clone();
        let constraint_flags = __arena_constraint_flags.get(constraint_type).flags;
        if constraint_flags.intersects(TypeFlags::UNION)
            || constraint_flags.intersects(TypeFlags::INTERSECTION)
        {
            let mut result = false;
            let __arena_constraint_types = self.types.clone();
            let constraint_types = __arena_constraint_types
                .get(constraint_type)
                .types()
                .to_vec();
            for t in constraint_types {
                let r = self.infer_to_mapped_type(n, source, target, t);
                result = r || result;
            }
            return result;
        }
        if constraint_flags.intersects(TypeFlags::INDEX) {
            // We're inferring from some source type S to a homomorphic mapped
            // type { [P in keyof T]: X }, where T is a type variable. Use
            // inferTypeForHomomorphicMappedType to infer a suitable source type
            // and then make a secondary inference from that type to T. We make
            // a secondary inference such that direct inferences to T get
            // priority over inferences to Partial<T>, for example.
            let __arena___guard_index_target = self.types.clone();
            let __guard_index_target = __arena___guard_index_target.get(constraint_type).clone();
            let index_target = __guard_index_target
                .as_index_type()
                .target
                .expect("index target");
            if let Some(index) = get_inference_info_for_type(&self.types, n, index_target) {
                if !n.inferences[index].is_fixed && !self.is_from_inference_blocked_source(source) {
                    if let Some(inferred_type) =
                        self.infer_type_for_homomorphic_mapped_type(source, target, constraint_type)
                    {
                        // We assign a lower priority to inferences made from
                        // types containing non-inferrable types because we may
                        // only have a partial result (i.e. we may have failed
                        // to make reverse inferences for some properties).
                        let type_parameter =
                            n.inferences[index].type_parameter.expect("typeParameter");
                        let priority = core::if_else(
                            self.types_handle()
                                .get(source)
                                .object_flags
                                .intersects(ObjectFlags::NON_INFERRABLE_TYPE),
                            InferencePriority::PARTIAL_HOMOMORPHIC_MAPPED_TYPE,
                            InferencePriority::HOMOMORPHIC_MAPPED_TYPE,
                        );
                        self.infer_with_priority(n, inferred_type, type_parameter, priority);
                    }
                }
            }
            return true;
        }
        if constraint_flags.intersects(TypeFlags::TYPE_PARAMETER) {
            // We're inferring from some source type S to a mapped type { [P in
            // K]: X }, where K is a type parameter. First infer from 'keyof S'
            // to K.
            let index_flags = core::if_else(
                self.pattern_for_type.read().unwrap().contains_key(&source),
                IndexFlags::NO_INDEX_SIGNATURES,
                IndexFlags::NONE,
            );
            let index_type = self.get_index_type_ex(source, index_flags);
            self.infer_with_priority(
                n,
                index_type,
                constraint_type,
                InferencePriority::MAPPED_TYPE_CONSTRAINT,
            );
            // If K is constrained to a type C, also infer to C. Thus, for a
            // mapped type { [P in K]: X }, where K extends keyof T, we make the
            // same inferences as for a homomorphic mapped type { [P in keyof
            // T]: X }. This enables us to make meaningful inferences when the
            // target is a Pick<T, K>.
            if let Some(extended_constraint) = self.get_constraint_of_type(constraint_type) {
                if self.infer_to_mapped_type(n, source, target, extended_constraint) {
                    return true;
                }
            }
            // If no inferences can be made to K's constraint, infer from a
            // union of the property types in the source to the template type
            // X.
            let props = self.get_properties_of_type(source);
            let prop_types: Vec<TypeId> = core::map(&props, |&p| self.get_type_of_symbol(p));
            let infos = self.get_index_infos_of_type(source);
            let index_types: Vec<TypeId> = core::map(&infos, |&info| {
                if info != self.enum_number_index_info {
                    self.index_info_arena
                        .get(info)
                        .value_type
                        .expect("valueType")
                } else {
                    self.never_type
                }
            });
            let union = self.get_union_type(&core::concatenate(&prop_types, &index_types));
            let template_type = self
                .get_template_type_from_mapped_type(target)
                .unwrap_or(self.never_type);
            self.infer_from_types(n, union, template_type);
            return true;
        }
        false
    }

    /// `(c *Checker) inferTypeForHomomorphicMappedType` (inference.go). Infer
    /// a suitable input type for a homomorphic mapped type `{ [P in keyof T]:
    /// X }`. We construct an object type with the same set of properties as
    /// the source type, where the type of each property is computed by
    /// inferring from the source property type to X for the type variable
    /// `T[P]` (i.e. we treat the type `T[P]` as the type variable we're
    /// inferring for).
    pub(crate) fn infer_type_for_homomorphic_mapped_type(
        &mut self,
        source: TypeId,
        target: TypeId,
        constraint: TypeId,
    ) -> Option<TypeId> {
        let key = ReverseMappedTypeKey {
            source_id: source,
            target_id: target,
            constraint_id: constraint,
        };
        if let Some(&cached) = self.reverse_homomorphic_mapped_cache.get(&key) {
            // PORT: cache stores `TypeId::NONE` for Go's nil entry.
            if cached != TypeId::NONE {
                return Some(cached);
            }
        }
        let t = self.create_reverse_mapped_type(source, target, constraint);
        self.reverse_homomorphic_mapped_cache
            .insert(key, t.unwrap_or(TypeId::NONE));
        t
    }

    /// `(c *Checker) createReverseMappedType` (inference.go).
    fn create_reverse_mapped_type(
        &mut self,
        source: TypeId,
        target: TypeId,
        constraint: TypeId,
    ) -> Option<TypeId> {
        // We consider a source type reverse mappable if it has a string index
        // signature or if it has one or more properties and is of a partially
        // inferable type.
        if !(self
            .get_index_info_of_type(source, self.string_type)
            .is_some()
            || !self.get_properties_of_type(source).is_empty()
                && self.is_partially_inferable_type(source))
        {
            return None;
        }
        // For arrays and tuples we infer new arrays and tuples where the
        // reverse mapping has been applied to the element type(s).
        if self.is_array_type(source) {
            let source_args = self.get_type_arguments(source);
            let element_type = self.infer_reverse_mapped_type(source_args[0], target, constraint);
            let element_type = element_type?;
            return Some(
                self.create_array_type_ex(element_type, self.is_readonly_array_type(source)),
            );
        }
        if is_tuple_type(&self.types, source) {
            let element_types_source = self.get_element_types(source);
            let mut element_types: Vec<TypeId> = Vec::with_capacity(element_types_source.len());
            for t in element_types_source {
                element_types.push(self.infer_reverse_mapped_type(t, target, constraint)?);
            }
            let __arena_source_tuple = self.types.clone();
            let source_tuple = __arena_source_tuple
                .target_tuple_type(source)
                .expect("tuple target");
            let __arena_element_infos = self.types.clone();
            let mut element_infos = __arena_element_infos
                .get(source_tuple)
                .as_tuple_type()
                .element_infos
                .clone();
            if crate::checker_d::get_mapped_type_modifiers(self, target)
                .intersects(MappedTypeModifiers::INCLUDE_OPTIONAL)
            {
                element_infos = core::same_map(&element_infos, |info| {
                    if info.flags.intersects(ElementFlags::OPTIONAL) {
                        crate::types::TupleElementInfo {
                            flags: ElementFlags::REQUIRED,
                            labeled_declaration: info.labeled_declaration,
                        }
                    } else {
                        info.clone()
                    }
                })
                .into_owned();
            }
            let __arena___guard_readonly = self.types.clone();
            let __guard_readonly = __arena___guard_readonly.get(source_tuple).clone();
            let readonly = __guard_readonly.as_tuple_type().readonly;
            return Some(self.create_tuple_type_ex(&element_types, &element_infos, readonly));
        }
        // For all other object types we infer a new object type where the
        // reverse mapping has been applied to the type of each property.
        let reversed = self.new_object_type(
            ObjectFlags::REVERSE_MAPPED | ObjectFlags::ANONYMOUS,
            None, /*symbol*/
        );
        {
            let __arena_t = self.types.clone();
            let mut t = __arena_t.get_mut(reversed);
            if let crate::types::TypeData::ReverseMapped(r) = &mut t.data {
                r.source = Some(source);
                r.mapped_type = Some(target);
                r.constraint_type = Some(constraint);
            }
        }
        Some(reversed)
    }

    /// `(c *Checker) isPartiallyInferableType` (inference.go). We consider a
    /// type to be partially inferable if it isn't marked non-inferable or if
    /// it is an object literal type with at least one property of an inferable
    /// type. For example, an object literal { a: 123, b: x => true } is
    /// marked non-inferable because it contains a context sensitive arrow
    /// function, but is considered partially inferable because property 'a'
    /// has an inferable type.
    fn is_partially_inferable_type(&mut self, t: TypeId) -> bool {
        !self
            .types_handle()
            .get(t)
            .object_flags
            .intersects(ObjectFlags::NON_INFERRABLE_TYPE)
            || crate::checker_c::is_object_literal_type(&self.types, t) && {
                let props = self.get_properties_of_type(t);
                core::some(&props, |&prop| {
                    let prop_type = self.get_type_of_symbol(prop);
                    self.is_partially_inferable_type(prop_type)
                })
            }
            || is_tuple_type(&self.types, t) && {
                let element_types = self.get_element_types(t);
                core::some(&element_types, |&e| self.is_partially_inferable_type(e))
            }
    }

    /// `(c *Checker) inferReverseMappedType` (inference.go).
    fn infer_reverse_mapped_type(
        &mut self,
        source: TypeId,
        target: TypeId,
        constraint: TypeId,
    ) -> Option<TypeId> {
        let key = ReverseMappedTypeKey {
            source_id: source,
            target_id: target,
            constraint_id: constraint,
        };
        if let Some(&cached) = self.reverse_mapped_cache.get(&key) {
            // `core.OrElse(cached, c.unknownType)` — `TypeId::NONE` is nil.
            return Some(if cached == TypeId::NONE {
                self.unknown_type
            } else {
                cached
            });
        }
        self.reverse_mapped_source_stack.push(source);
        self.reverse_mapped_target_stack.push(target);
        let save_expanding_flags = self.reverse_expanding_flags;
        // PORT(borrow): `is_deeply_nested_type` needs `&mut self`, so the
        // stacks are cloned out rather than borrowed in place.
        let source_stack = self.reverse_mapped_source_stack.clone();
        let target_stack = self.reverse_mapped_target_stack.clone();
        if self.is_deeply_nested_type(source, &source_stack, 2) {
            self.reverse_expanding_flags |= ExpandingFlags::SOURCE;
        }
        if self.is_deeply_nested_type(target, &target_stack, 2) {
            self.reverse_expanding_flags |= ExpandingFlags::TARGET;
        }
        let mut t = None;
        if self.reverse_expanding_flags != ExpandingFlags::BOTH {
            t = self.infer_reverse_mapped_type_worker(source, target, constraint);
        }
        self.reverse_mapped_source_stack.pop();
        self.reverse_mapped_target_stack.pop();
        self.reverse_expanding_flags = save_expanding_flags;
        // Go stores the possibly-nil `*Type`; `TypeId::NONE` is the sentinel.
        self.reverse_mapped_cache
            .insert(key, t.unwrap_or(TypeId::NONE));
        t
    }

    /// `(c *Checker) inferReverseMappedTypeWorker` (inference.go).
    fn infer_reverse_mapped_type_worker(
        &mut self,
        source: TypeId,
        target: TypeId,
        constraint: TypeId,
    ) -> Option<TypeId> {
        let __arena___guard_index_target = self.types.clone();
        let __guard_index_target = __arena___guard_index_target.get(constraint).clone();
        let index_target = __guard_index_target
            .as_index_type()
            .target
            .expect("index target");
        let type_parameter_from_mapped = self
            .get_type_parameter_from_mapped_type(target)
            .expect("typeParameterFromMappedType");
        let type_parameter = self.get_indexed_access_type(index_target, type_parameter_from_mapped);
        let template_type = self
            .get_template_type_from_mapped_type(target)
            .unwrap_or(self.never_type);
        let inference = new_inference_info(Some(type_parameter));
        let mut inferences = vec![inference];
        self.infer_types(
            &mut inferences,
            source,
            template_type,
            InferencePriority::NONE_PRIORITY,
            false,
        );
        let inferred = self
            .get_type_from_inference(inferences.first().expect("inferences"))
            .unwrap_or(self.unknown_type);
        Some(self.get_widened_type(inferred))
    }

    /// `(c *Checker) resolveReverseMappedTypeMembers` (inference.go).
    pub(crate) fn resolve_reverse_mapped_type_members(&mut self, t: TypeId) {
        let (r_source, r_mapped_type, r_constraint_type) = {
            let __arena_guard = self.types.clone();
            let guard = __arena_guard.get(t);
            let r = guard.as_reverse_mapped_type();
            (
                r.source.expect("reverse mapped source"),
                r.mapped_type.expect("reverse mapped mappedType"),
                r.constraint_type.expect("reverse mapped constraintType"),
            )
        };
        let index_info = self.get_index_info_of_type(r_source, self.string_type);
        let modifiers = crate::checker_d::get_mapped_type_modifiers(self, r_mapped_type);
        let readonly_mask = !modifiers.intersects(MappedTypeModifiers::INCLUDE_READONLY);
        let optional_mask = core::if_else(
            modifiers.intersects(MappedTypeModifiers::INCLUDE_OPTIONAL),
            ast::SymbolFlags::NONE,
            ast::SymbolFlags::OPTIONAL,
        );
        let mut index_infos: Vec<IndexInfoId> = Vec::new();
        if let Some(index_info) = index_info {
            let (value_type, is_readonly) = {
                let info = self.index_info_arena.get(index_info);
                (info.value_type.expect("valueType"), info.is_readonly)
            };
            let inferred = self
                .infer_reverse_mapped_type(value_type, r_mapped_type, r_constraint_type)
                .unwrap_or(self.unknown_type);
            let info_id = self.new_index_info(
                self.string_type,
                inferred,
                readonly_mask && is_readonly,
                None,
                Vec::new(),
            );
            index_infos.push(info_id);
        }
        let mut members = ast::SymbolTable::new();
        let limited_constraint = self.get_limited_constraint(t);
        let props = self.get_properties_of_type(r_source);
        for prop in props {
            // In case of a reverse mapped type with an intersection
            // constraint, if we were able to extract the filtering type
            // literals we skip those properties that are not assignable to
            // them, because the extra properties wouldn't get through the
            // application of the mapped type anyway.
            if let Some(limited_constraint) = limited_constraint {
                let property_name_type = self.get_literal_type_from_property(
                    prop,
                    TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE,
                    false,
                );
                if !self.is_type_assignable_to(property_name_type, limited_constraint) {
                    continue;
                }
            }
            let prop_flags = self.sym(prop).flags;
            let prop_name = self.sym(prop).name.clone();
            let check_flags = ast::checkflags::CheckFlags::REVERSE_MAPPED
                | core::if_else(
                    readonly_mask && self.is_readonly_symbol(prop),
                    ast::checkflags::CheckFlags::READONLY,
                    ast::checkflags::CheckFlags::NONE,
                );
            let inferred_prop = self.new_symbol_ex(
                ast::SymbolFlags::PROPERTY | (prop_flags & optional_mask),
                &prop_name,
                check_flags,
            );
            let prop_declarations = self.sym(prop).declarations.clone();
            self.symbol_arena.borrow_mut()[inferred_prop.index()].declarations = prop_declarations;
            let name_type = self.value_symbol_links.get(prop).name_type;
            self.value_symbol_links.get(inferred_prop).name_type = name_type;
            let property_type = self.get_type_of_symbol(prop);
            let __arena___guard_constraint_target = self.types.clone();
            let __guard_constraint_target = __arena___guard_constraint_target
                .get(r_constraint_type)
                .clone();
            let constraint_target = __guard_constraint_target
                .as_index_type()
                .target
                .expect("constraint target");
            let constraint_target_indexed = {
                let __arena_ct = self.types.clone();
                let ct = __arena_ct.get(constraint_target);
                if ct.flags.intersects(TypeFlags::INDEXED_ACCESS) {
                    let ia = ct.as_indexed_access_type();
                    Some((ia.object_type, ia.index_type))
                } else {
                    None
                }
            };
            let (mapped_type, links_constraint_type) =
                if let Some((object_type, index_type)) = constraint_target_indexed {
                    if object_type.is_some_and(|o| {
                        self.types_handle()
                            .get(o)
                            .flags
                            .intersects(TypeFlags::TYPE_PARAMETER)
                    }) && index_type.is_some_and(|i| {
                        self.types_handle()
                            .get(i)
                            .flags
                            .intersects(TypeFlags::TYPE_PARAMETER)
                    }) {
                        // A reverse mapping of `{[K in keyof T[K_1]]: T[K_1]}` is
                        // the same as that of `{[K in keyof T]: T}`, since all we
                        // care about is inferring to the "type parameter" (or
                        // indexed access) shared by the constraint and template.
                        // So, to reduce the number of type identities produced, we
                        // simplify such indexed access occurrences.
                        let new_type_param = object_type.expect("objectType");
                        let new_mapped_type = self.replace_indexed_access(
                            r_mapped_type,
                            constraint_target,
                            new_type_param,
                        );
                        let index_type = self.get_index_type(new_type_param);
                        (new_mapped_type, index_type)
                    } else {
                        (r_mapped_type, r_constraint_type)
                    }
                } else {
                    (r_mapped_type, r_constraint_type)
                };
            {
                let links = self.reverse_mapped_symbol_links.get(inferred_prop);
                links.property_type = Some(property_type);
                links.mapped_type = Some(mapped_type);
                links.constraint_type = Some(links_constraint_type);
            }
            members.set(prop_name.into(), inferred_prop);
        }
        self.set_structured_type_members(t, members, &[], &[], &index_infos);
    }

    /// `(c *Checker) getTypeOfReverseMappedSymbol` (inference.go).
    pub(crate) fn get_type_of_reverse_mapped_symbol(&mut self, symbol: SymbolId) -> TypeId {
        if self.value_symbol_links.get(symbol).resolved_type.is_none() {
            let (property_type, mapped_type, constraint_type) = {
                let links = self.reverse_mapped_symbol_links.get(symbol);
                (
                    links.property_type.expect("propertyType"),
                    links.mapped_type.expect("mappedType"),
                    links.constraint_type.expect("constraintType"),
                )
            };
            let resolved = self
                .infer_reverse_mapped_type(property_type, mapped_type, constraint_type)
                .unwrap_or(self.unknown_type);
            self.value_symbol_links.get(symbol).resolved_type = Some(resolved);
        }
        self.value_symbol_links
            .get(symbol)
            .resolved_type
            .expect("resolvedType")
    }

    /// `(c *Checker) getLimitedConstraint` (inference.go). If the original
    /// mapped type had an intersection constraint we extract its components,
    /// and we make an attempt to do so even if the intersection has been
    /// reduced to a union. This entire process allows us to possibly retrieve
    /// the filtering type literals. e.g. `{ [K in keyof U & ("a" | "b") ] }`
    /// -> `"a" | "b"`.
    fn get_limited_constraint(&mut self, t: TypeId) -> Option<TypeId> {
        let __arena___guard_mapped_type = self.types.clone();
        let __guard_mapped_type = __arena___guard_mapped_type.get(t).clone();
        let mapped_type = __guard_mapped_type
            .as_reverse_mapped_type()
            .mapped_type
            .expect("mappedType");
        let constraint = self.get_constraint_type_from_mapped_type(mapped_type)?;
        let __arena_constraint_flags = self.types.clone();
        let constraint_flags = __arena_constraint_flags.get(constraint).flags;
        if !(constraint_flags.intersects(TypeFlags::UNION)
            || constraint_flags.intersects(TypeFlags::INTERSECTION))
        {
            return None;
        }
        let mut origin = constraint;
        if constraint_flags.intersects(TypeFlags::UNION) {
            origin = self.types_handle().get(constraint).as_union_type().origin?;
        }
        if !self
            .types_handle()
            .get(origin)
            .flags
            .intersects(TypeFlags::INTERSECTION)
        {
            return None;
        }
        let __arena___guard_constraint_type = self.types.clone();
        let __guard_constraint_type = __arena___guard_constraint_type.get(t).clone();
        let constraint_type = __guard_constraint_type
            .as_reverse_mapped_type()
            .constraint_type
            .expect("constraintType");
        let __arena_origin_types = self.types.clone();
        let origin_types = __arena_origin_types.get(origin).types().to_vec();
        let filtered = core::filter(&origin_types, |&t| t != constraint_type);
        let limited_constraint = self.get_intersection_type(&filtered);
        if limited_constraint != self.never_type {
            return Some(limited_constraint);
        }
        None
    }

    /// `(c *Checker) replaceIndexedAccess` (inference.go). Map
    /// `type.indexType` to `0` and `type.objectType` to `[TReplacement]`,
    /// thus making the indexed access `[TReplacement][0]` or `TReplacement`.
    fn replace_indexed_access(
        &mut self,
        instantiable: TypeId,
        t: TypeId,
        replacement: TypeId,
    ) -> TypeId {
        let (index_type, object_type) = {
            let __arena_guard = self.types.clone();
            let guard = __arena_guard.get(t);
            let ia = guard.as_indexed_access_type();
            (
                ia.index_type.expect("indexType"),
                ia.object_type.expect("objectType"),
            )
        };
        let zero = self.get_number_literal_type(tsc_jsnum::Number(0.0));
        let tuple = self.create_tuple_type(&[replacement]);
        let mapper =
            mapper::new_type_mapper(self, vec![index_type, object_type], vec![zero, tuple]);
        self.instantiate_type(instantiable, Some(mapper))
    }

    /// `(c *Checker) typesDefinitelyUnrelated` (inference.go). Two tuple
    /// types with incompatible arities are definitely unrelated. Two object
    /// types that each have a property that is unmatched in the other are
    /// definitely unrelated.
    fn types_definitely_unrelated(&mut self, source: TypeId, target: TypeId) -> bool {
        if is_tuple_type(&self.types, source) && is_tuple_type(&self.types, target) {
            return tuple_types_definitely_unrelated(&self.types, source, target);
        }
        self.get_unmatched_property(
            source, target, false, /*requireOptionalProperties*/
            true,  /*matchDiscriminantProperties*/
        )
        .is_some()
            && self
                .get_unmatched_property(
                    target, source, false, /*requireOptionalProperties*/
                    false, /*matchDiscriminantProperties*/
                )
                .is_some()
    }

    /// `(c *Checker) isTupleTypeStructureMatching` (inference.go).
    fn is_tuple_type_structure_matching(&mut self, t1: TypeId, t2: TypeId) -> bool {
        if self.get_type_reference_arity(t1) != self.get_type_reference_arity(t2) {
            return false;
        }
        let __arena___guard_t1_infos = self.types.clone();
        let __guard_t1_infos = __arena___guard_t1_infos
            .get(self.types_handle().target_tuple_type(t1).expect("tuple"))
            .clone();
        let t1_infos = __guard_t1_infos.as_tuple_type().element_infos.clone();
        let __arena___guard_t2_infos = self.types.clone();
        let __guard_t2_infos = __arena___guard_t2_infos
            .get(self.types_handle().target_tuple_type(t2).expect("tuple"))
            .clone();
        let t2_infos = __guard_t2_infos.as_tuple_type().element_infos.clone();
        for (i, e) in t1_infos.iter().enumerate() {
            if e.flags & ElementFlags::VARIABLE != t2_infos[i].flags & ElementFlags::VARIABLE {
                return false;
            }
        }
        true
    }

    /// `(c *Checker) isTypeOrBaseIdenticalTo` (inference.go).
    pub(crate) fn is_type_or_base_identical_to(&mut self, s: TypeId, t: TypeId) -> bool {
        if t == self.missing_type {
            return s == t;
        }
        self.is_type_identical_to(s, t)
            || self
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::STRING)
                && self
                    .types_handle()
                    .get(s)
                    .flags
                    .intersects(TypeFlags::STRING_LITERAL)
            || self
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::NUMBER)
                && self
                    .types_handle()
                    .get(s)
                    .flags
                    .intersects(TypeFlags::NUMBER_LITERAL)
    }

    /// `(c *Checker) isTypeCloselyMatchedBy` (inference.go).
    pub(crate) fn is_type_closely_matched_by(&mut self, s: TypeId, t: TypeId) -> bool {
        let __arena_s_ty = self.types.clone();
        let s_ty = __arena_s_ty.get(s);
        let __arena_t_ty = self.types.clone();
        let t_ty = __arena_t_ty.get(t);
        s_ty.flags.intersects(TypeFlags::OBJECT)
            && t_ty.flags.intersects(TypeFlags::OBJECT)
            && s_ty.symbol.is_some()
            && s_ty.symbol == t_ty.symbol
            || s_ty.alias().is_some()
                && t_ty.alias().is_some()
                && !s_ty.alias().expect("alias").type_arguments.is_empty()
                && s_ty.alias().expect("alias").symbol == t_ty.alias().expect("alias").symbol
    }

    /// `(c *Checker) createEmptyObjectTypeFromStringLiteral` (inference.go).
    /// Create an object with properties named in the string literal type.
    /// Every property has type `any`.
    fn create_empty_object_type_from_string_literal(&mut self, t: TypeId) -> TypeId {
        let mut members = ast::SymbolTable::new();
        let __arena_constituents = self.types.clone();
        let constituents = __arena_constituents.get(t).distributed(t);
        for constituent in constituents {
            if !self
                .types_handle()
                .get(constituent)
                .flags
                .intersects(TypeFlags::STRING_LITERAL)
            {
                continue;
            }
            let name = crate::checker_d::get_string_literal_value(&self.types, constituent);
            let literal_prop = self.new_symbol(ast::SymbolFlags::PROPERTY, &name);
            self.value_symbol_links.get(literal_prop).resolved_type = Some(self.any_type);
            if let Some(symbol) = self.types_handle().get(constituent).symbol {
                let (declarations, value_declaration) = {
                    let s = self.sym(symbol);
                    (s.declarations.clone(), s.value_declaration)
                };
                let mut arena = self.symbol_arena.borrow_mut();
                arena[literal_prop.index()].declarations = declarations;
                arena[literal_prop.index()].value_declaration = value_declaration;
            }
            members.set(name.into(), literal_prop);
        }
        let mut index_infos: Vec<IndexInfoId> = Vec::new();
        if self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::STRING)
        {
            index_infos.push(self.new_index_info(
                self.string_type,
                self.empty_object_type,
                false, /*isReadonly*/
                None,
                Vec::new(),
            ));
        }
        self.new_anonymous_type(None, members, &[], &[], &index_infos)
    }

    /// `(c *Checker) newInferenceContext` (inference.go). PORT: `signature`
    /// accepts both `SignatureId` and `Option<SignatureId>` (Go `*Signature`
    /// nil-able) via `Into<Option<SignatureId>>`; `compareTypes` is
    /// `Option<Box<TypeComparer>>` — `None` defaults to the checker's
    /// `compare_types_assignable`, re-boxed around its `Rc`.
    /// PORT: `type_parameters` is `impl AsRef<[TypeId]>` so callers can pass
    /// either an owned `Vec<TypeId>` or a borrow (Go passes a slice).
    pub fn new_inference_context(
        &mut self,
        type_parameters: impl AsRef<[TypeId]>,
        signature: impl Into<Option<SignatureId>>,
        flags: InferenceFlags,
        compare_types: Option<Box<TypeComparer<'static>>>,
    ) -> InferenceContextId {
        let compare_types = compare_types.or_else(|| {
            self.compare_types_assignable.clone().map(|f| {
                Box::new(
                    move |c: &mut Checker, s: TypeId, t: TypeId, report_errors: bool| {
                        f(c, s, t, report_errors)
                    },
                ) as Box<TypeComparer<'static>>
            })
        });
        let inferences = core::map(type_parameters.as_ref(), |&tp| new_inference_info(Some(tp)));
        self.new_inference_context_worker(inferences, signature.into(), flags, compare_types)
    }

    /// `(c *Checker) cloneInferenceContext` (inference.go).
    pub(crate) fn clone_inference_context(
        &mut self,
        n: impl Into<Option<InferenceContextId>>,
        extra_flags: InferenceFlags,
    ) -> Option<InferenceContextId> {
        let n = n.into()?;
        let inferences = core::map(&self.inference_contexts[n.index()].inferences, |i| {
            clone_inference_info(i)
        });
        let signature = self.inference_contexts[n.index()].signature;
        let flags = self.inference_contexts[n.index()].flags | extra_flags;
        let compare_types = share_compare_types(self, n);
        Some(self.new_inference_context_worker(inferences, signature, flags, compare_types))
    }

    /// `(c *Checker) cloneInferredPartOfContext` (inference.go).
    pub(crate) fn clone_inferred_part_of_context(
        &mut self,
        n: InferenceContextId,
    ) -> Option<InferenceContextId> {
        let inferences: Vec<InferenceInfo> = self.inference_contexts[n.index()]
            .inferences
            .iter()
            .filter(|i| has_inference_candidates(i))
            .map(|i| clone_inference_info(i))
            .collect();
        if inferences.is_empty() {
            return None;
        }
        let signature = self.inference_contexts[n.index()].signature;
        let flags = self.inference_contexts[n.index()].flags;
        let compare_types = share_compare_types(self, n);
        Some(self.new_inference_context_worker(inferences, signature, flags, compare_types))
    }

    /// `(c *Checker) newInferenceContextWorker` (inference.go). PORT:
    /// allocates the context in `self.inference_contexts` and then creates
    /// the fixing/non-fixing mappers referencing the `InferenceContextId`.
    fn new_inference_context_worker(
        &mut self,
        inferences: Vec<InferenceInfo>,
        signature: Option<SignatureId>,
        flags: InferenceFlags,
        compare_types: Option<Box<TypeComparer<'static>>>,
    ) -> InferenceContextId {
        let n = InferenceContextId(self.inference_contexts.len() as u32);
        self.inference_contexts.push(InferenceContext {
            inferences,
            signature,
            flags,
            compare_types,
            ..Default::default()
        });
        let mapper = self.new_inference_type_mapper(n, true /*fixing*/);
        self.inference_contexts[n.index()].mapper = Some(mapper);
        let non_fixing_mapper = self.new_inference_type_mapper(n, false /*fixing*/);
        self.inference_contexts[n.index()].non_fixing_mapper = Some(non_fixing_mapper);
        n
    }

    /// `(c *Checker) addIntraExpressionInferenceSite` (inference.go).
    pub(crate) fn add_intra_expression_inference_site(
        &mut self,
        n: impl Into<Option<InferenceContextId>>,
        node: NodeId,
        t: TypeId,
    ) {
        let n = n.into().expect("inference context");
        self.inference_contexts[n.index()]
            .intra_expression_inference_sites
            .push(IntraExpressionInferenceSite {
                node: Some(node),
                t: Some(t),
            });
    }

    /// `(c *Checker) getInferredTypes` (inference.go).
    pub(crate) fn get_inferred_types(&mut self, n: InferenceContextId) -> Vec<TypeId> {
        let len = self.inference_contexts[n.index()].inferences.len();
        let mut result = Vec::with_capacity(len);
        for i in 0..len {
            result.push(get_inferred_type(self, n, i));
        }
        result
    }

    /// `(c *Checker) getMapperFromContext` (inference.go). PORT: `n` accepts
    /// `InferenceContextId` or `Option<InferenceContextId>` (Go nil-able
    /// `*InferenceContext`).
    pub(crate) fn get_mapper_from_context(
        &mut self,
        n: impl Into<Option<InferenceContextId>>,
    ) -> Option<TypeMapperId> {
        n.into()
            .and_then(|id| self.inference_contexts[id.index()].mapper)
    }

    /// `(c *Checker) createOuterReturnMapper` (inference.go). Return a type
    /// mapper that combines the context's return mapper with a mapper that
    /// erases any additional type parameters to their inferences at the time
    /// of creation.
    pub(crate) fn create_outer_return_mapper(
        &mut self,
        context: InferenceContextId,
    ) -> Option<TypeMapperId> {
        if self.inference_contexts[context.index()]
            .outer_return_mapper
            .is_none()
        {
            let cloned = self.clone_inference_context(context, InferenceFlags::NONE);
            let mut mapper = self.get_mapper_from_context(cloned);
            if let Some(return_mapper) = self.inference_contexts[context.index()].return_mapper {
                mapper = Some(mapper::new_merged_type_mapper(
                    self,
                    return_mapper,
                    mapper.expect("cloned inference context mapper"),
                ));
            }
            self.inference_contexts[context.index()].outer_return_mapper = mapper;
        }
        self.inference_contexts[context.index()].outer_return_mapper
    }

    /// `(c *Checker) getCovariantInference` (inference.go).
    fn get_covariant_inference(
        &mut self,
        inference: &InferenceInfo,
        signature: SignatureId,
    ) -> TypeId {
        // Extract all object and array literal types and replace them with a
        // single widened and normalized type.
        let candidates = self.union_object_and_array_literal_candidates(&inference.candidates);
        // We widen inferred literal types if
        //   all inferences were made to top-level occurrences of the type
        //   parameter, and
        //   the type parameter has no constraint or its constraint includes no
        //   primitive or literal types, and
        //   the type parameter was fixed during inference or does not occur at
        //   top-level in the return type.
        let type_parameter = inference.type_parameter.expect("typeParameter");
        let primitive_constraint = self.has_primitive_constraint(type_parameter)
            || self.is_const_type_variable(inference.type_parameter, 0);
        let widen_literal_types = !primitive_constraint
            && inference.top_level
            && (inference.is_fixed
                || !self.is_type_parameter_at_top_level_in_return_type(signature, type_parameter));
        let base_candidates: Vec<TypeId> = if primitive_constraint {
            core::same_map(&candidates, |&t| self.get_regular_type_of_literal_type(t)).into_owned()
        } else if widen_literal_types {
            core::same_map(&candidates, |&t| self.get_widened_literal_type(t)).into_owned()
        } else {
            candidates
        };
        // If all inferences were made from a position that implies a combined
        // result, infer a union type. Otherwise, infer a common supertype.
        let unwidened_type = if inference
            .priority
            .intersects(InferencePriority::PRIORITY_IMPLIES_COMBINATION)
        {
            self.get_union_type_ex(&base_candidates, UnionReduction::Subtype, None, None)
        } else {
            self.get_common_supertype(&base_candidates)
        };
        self.get_widened_type(unwidened_type)
    }

    /// `(c *Checker) getContravariantInference` (inference.go).
    fn get_contravariant_inference(&mut self, inference: &InferenceInfo) -> Option<TypeId> {
        if inference
            .priority
            .intersects(InferencePriority::PRIORITY_IMPLIES_COMBINATION)
        {
            return Some(self.get_intersection_type(&inference.contra_candidates));
        }
        self.get_common_subtype(&inference.contra_candidates)
    }

    /// `(c *Checker) unionObjectAndArrayLiteralCandidates` (inference.go).
    fn union_object_and_array_literal_candidates(&mut self, candidates: &[TypeId]) -> Vec<TypeId> {
        if candidates.len() > 1 {
            let object_literals: Vec<TypeId> = candidates
                .iter()
                .copied()
                .filter(|&t| is_object_or_array_literal_type(&self.types_handle().get(t)))
                .collect();
            if !object_literals.is_empty() {
                let literals_type =
                    self.get_union_type_ex(&object_literals, UnionReduction::Subtype, None, None);
                let non_literal_types: Vec<TypeId> = candidates
                    .iter()
                    .copied()
                    .filter(|&t| !is_object_or_array_literal_type(&self.types_handle().get(t)))
                    .collect();
                return core::concatenate(&non_literal_types, &[literals_type]).into_owned();
            }
        }
        candidates.to_vec()
    }

    /// `(c *Checker) hasPrimitiveConstraint` (inference.go).
    fn has_primitive_constraint(&mut self, t: TypeId) -> bool {
        if let Some(mut constraint) = self.get_constraint_of_type_parameter(t) {
            if self
                .types_handle()
                .get(constraint)
                .flags
                .intersects(TypeFlags::CONDITIONAL)
            {
                constraint = self.get_default_constraint_of_conditional_type(constraint);
            }
            return self.maybe_type_of_kind(
                constraint,
                TypeFlags::PRIMITIVE
                    | TypeFlags::INDEX
                    | TypeFlags::TEMPLATE_LITERAL
                    | TypeFlags::STRING_MAPPING,
            );
        }
        false
    }

    /// `(c *Checker) isTypeParameterAtTopLevel` (inference.go).
    fn is_type_parameter_at_top_level(&mut self, t: TypeId, tp: TypeId, depth: usize) -> bool {
        if t == tp {
            return true;
        }
        let __arena_flags = self.types.clone();
        let flags = __arena_flags.get(t).flags;
        if flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
            let __arena_types = self.types.clone();
            let types = __arena_types.get(t).types().to_vec();
            return core::some(&types, |t| {
                self.is_type_parameter_at_top_level(*t, tp, depth)
            });
        }
        if depth < 3 && flags.intersects(TypeFlags::CONDITIONAL) {
            let true_t = self.get_true_type_from_conditional_type(t);
            if self.is_type_parameter_at_top_level(true_t, tp, depth + 1) {
                return true;
            }
            let false_t = self.get_false_type_from_conditional_type(t);
            return self.is_type_parameter_at_top_level(false_t, tp, depth + 1);
        }
        false
    }

    /// `(c *Checker) isTypeParameterAtTopLevelInReturnType` (inference.go).
    fn is_type_parameter_at_top_level_in_return_type(
        &mut self,
        signature: SignatureId,
        type_parameter: TypeId,
    ) -> bool {
        if let Some(type_predicate) = self.get_type_predicate_of_signature(signature) {
            return type_predicate
                .t
                .is_some_and(|t| self.is_type_parameter_at_top_level(t, type_parameter, 0));
        }
        let return_type = self.get_return_type_of_signature(signature);
        self.is_type_parameter_at_top_level(return_type, type_parameter, 0)
    }

    /// `(c *Checker) getTypeFromInference` (inference.go).
    pub(crate) fn get_type_from_inference(&mut self, inference: &InferenceInfo) -> Option<TypeId> {
        if !inference.candidates.is_empty() {
            return Some(self.get_union_type_ex(
                &inference.candidates,
                UnionReduction::Subtype,
                None,
                None,
            ));
        }
        if !inference.contra_candidates.is_empty() {
            return Some(self.get_intersection_type(&inference.contra_candidates));
        }
        None
    }

    /// `(c *Checker) getCommonSupertype` (inference.go).
    pub(crate) fn get_common_supertype(&mut self, types: &[TypeId]) -> TypeId {
        if types.len() == 1 {
            return types[0];
        }
        // Remove nullable types from each of the candidates.
        let mut primary_types: std::borrow::Cow<'_, [TypeId]> = std::borrow::Cow::Borrowed(types);
        if self.strict_null_checks {
            primary_types = core::same_map(types, |&t| {
                self.filter_type(t, &|c: &mut Checker, u: TypeId| {
                    !c.types_handle()
                        .get(u)
                        .flags
                        .intersects(TypeFlags::NULLABLE)
                })
            });
        }
        // When the candidate types are all literal types with the same base
        // type, return a union of those literal types. Otherwise, return the
        // leftmost type for which no type to the right is a supertype.
        let supertype = if self.literal_types_with_same_base_type(&primary_types) {
            self.get_union_type(&primary_types)
        } else {
            self.get_single_common_supertype(&primary_types)
        };
        // Add any nullable types that occurred in the candidates back to the
        // result.
        if core::same(&primary_types, types) {
            return supertype;
        }
        let combined_flags = self.get_combined_type_flags(types) & TypeFlags::NULLABLE;
        self.get_nullable_type(supertype, combined_flags)
    }

    /// `(c *Checker) getSingleCommonSupertype` (inference.go). First, find
    /// the leftmost type for which no type to the right is a strict
    /// supertype, and if that type is a strict supertype of all other
    /// candidates, return it. Otherwise, return the leftmost type for which
    /// no type to the right is a (regular) supertype.
    fn get_single_common_supertype(&mut self, types: &[TypeId]) -> TypeId {
        let candidate = self.find_leftmost_type(types, Self::is_type_strict_subtype_of);
        if core::every(types, |&t| {
            t == candidate || self.is_type_strict_subtype_of(t, candidate)
        }) {
            return candidate;
        }
        self.find_leftmost_type(types, Self::is_type_subtype_of)
    }

    /// `(c *Checker) findLeftmostType` (inference.go). PORT: Go's `f func(c,
    /// s, t) bool` becomes a `fn` item.
    fn find_leftmost_type(
        &mut self,
        types: &[TypeId],
        f: fn(&mut Checker, TypeId, TypeId) -> bool,
    ) -> TypeId {
        let mut candidate: Option<TypeId> = None;
        for &t in types {
            if candidate.is_none() || f(self, candidate.unwrap(), t) {
                candidate = Some(t);
            }
        }
        candidate.expect("findLeftmostType of empty slice")
    }

    /// `(c *Checker) getCommonSubtype` (inference.go). Return the leftmost
    /// type for which no type to the right is a subtype.
    fn get_common_subtype(&mut self, types: &[TypeId]) -> Option<TypeId> {
        let mut subtype: Option<TypeId> = None;
        for &t in types {
            if subtype.is_none() || self.is_type_subtype_of(t, subtype.unwrap()) {
                subtype = Some(t);
            }
        }
        subtype
    }

    /// `(c *Checker) getCombinedTypeFlags` (inference.go).
    fn get_combined_type_flags(&mut self, types: &[TypeId]) -> TypeFlags {
        let mut flags = TypeFlags::NONE;
        for &t in types {
            let __arena_t_flags = self.types.clone();
            let t_flags = __arena_t_flags.get(t).flags;
            if t_flags.intersects(TypeFlags::UNION) {
                let __arena_constituents = self.types.clone();
                let constituents = __arena_constituents.get(t).types().to_vec();
                flags |= self.get_combined_type_flags(&constituents);
            } else {
                flags |= t_flags;
            }
        }
        flags
    }

    /// `(c *Checker) literalTypesWithSameBaseType` (inference.go).
    fn literal_types_with_same_base_type(&mut self, types: &[TypeId]) -> bool {
        let mut common_base_type: Option<TypeId> = None;
        for &t in types {
            if !self
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::NEVER)
            {
                let base_type = self.get_base_type_of_literal_type(t);
                if common_base_type.is_none() {
                    common_base_type = Some(base_type);
                }
                if base_type == t || Some(base_type) != common_base_type {
                    return false;
                }
            }
        }
        true
    }

    /// `(c *Checker) isFromInferenceBlockedSource` (inference.go).
    fn is_from_inference_blocked_source(&mut self, t: TypeId) -> bool {
        let __arena_symbol = self.types.clone();
        let symbol = __arena_symbol.get(t).symbol;
        if let Some(symbol) = symbol {
            let declarations = self.sym(symbol).declarations.clone();
            return core::some(&declarations, |&d| self.is_skip_direct_inference_node(d));
        }
        false
    }

    /// `(c *Checker) isSkipDirectInferenceNode` (inference.go).
    pub(crate) fn is_skip_direct_inference_node(&mut self, node: NodeId) -> bool {
        self.skip_direct_inference_nodes.has(&node)
    }

    /// `(c *Checker) mergeInferences` (inference.go). PORT: Go assigns the
    /// `*InferenceInfo` pointer (`target[i] = source[i]`, creating an alias);
    /// `Vec<InferenceInfo>` has no aliasing, so the entry is cloned — the
    /// source vector is a temporary at every call site.
    pub(crate) fn merge_inferences(
        &mut self,
        target: &mut Vec<InferenceInfo>,
        source: &[InferenceInfo],
    ) {
        for i in 0..target.len() {
            if !has_inference_candidates(&target[i]) && has_inference_candidates(&source[i]) {
                target[i] = clone_inference_info(&source[i]);
            }
        }
    }

    /// `hasTypeParameterDefault` (inference.go). PORT: free fn in Go; the
    /// port needs the type/symbol/node arenas, so it's a method.
    pub(crate) fn has_type_parameter_default(&self, tp: TypeId) -> bool {
        if let Some(symbol) = self.types_handle().get(tp).symbol {
            let declarations = self.symbol_arena.borrow()[symbol.index()]
                .declarations
                .clone();
            for d in declarations {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((d).file_index());
                if ast::is_type_parameter_declaration(&nodes[d])
                    && nodes[d]
                        .as_type_parameter_declaration()
                        .default_type
                        .is_some()
                {
                    return true;
                }
            }
        }
        false
    }

    /// `hasInferenceCandidatesOrDefault` (inference.go). PORT: free fn in
    /// Go; needs `has_type_parameter_default`, so it's a method.
    pub(crate) fn has_inference_candidates_or_default(&self, info: &InferenceInfo) -> bool {
        has_inference_candidates(info)
            || info
                .type_parameter
                .is_some_and(|tp| self.has_type_parameter_default(tp))
    }
}

/// `compareTypesAndDepth` (inference.go) — compare two types first by depth
/// and then by the regular type ordering. PORT: Go reads `t.checker` for
/// `getTypeArguments`; the checker is passed explicitly.
fn compare_types_and_depth(c: &mut Checker, t1: TypeId, t2: TypeId) -> i32 {
    let d1 = get_type_depth(c, t1, 3);
    let d2 = get_type_depth(c, t2, 3);
    if d1 != d2 {
        return d2 - d1; // Largest depth sorts first
    }
    crate::utilities::compare_types(&c.types, c.symbol_arena.as_ref(), &c.type_mappers, c.program.as_ref(), t1, t2)
}

/// `getTypeDepth` (inference.go) — return the depth of the given type up to
/// the given maximum depth. For generic aliased types and type references,
/// the depth is one plus the largest type argument depth. For union and
/// intersection types, the depth is the largest constituent type depth. For
/// all other types, the depth is zero. The maximum depth limits infinite
/// recursion of circular types.
fn get_type_depth(c: &mut Checker, t: TypeId, max_depth: i32) -> i32 {
    if max_depth != 0 {
        let (alias_args, is_reference, union_or_intersection_types) = {
            let __arena_ty = c.types.clone();
            let ty = __arena_ty.get(t);
            (
                ty.alias().map(|a| a.type_arguments.clone()),
                ty.object_flags.intersects(ObjectFlags::REFERENCE),
                if ty.flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
                    Some(ty.types().to_vec())
                } else {
                    None
                },
            )
        };
        if let Some(alias_args) = alias_args {
            if !alias_args.is_empty() {
                return get_type_list_depth(c, &alias_args, max_depth - 1) + 1;
            }
        }
        if is_reference {
            let type_arguments = c.get_type_arguments(t);
            if !type_arguments.is_empty() {
                return get_type_list_depth(c, &type_arguments, max_depth - 1) + 1;
            }
        }
        if let Some(types) = union_or_intersection_types {
            return get_type_list_depth(c, &types, max_depth);
        }
    }
    0
}

/// `getTypeListDepth` (inference.go).
fn get_type_list_depth(c: &mut Checker, types: &[TypeId], max_depth: i32) -> i32 {
    let mut depth = 0;
    for &t in types {
        depth = max(depth, get_type_depth(c, t, max_depth));
    }
    depth
}

/// `getSingleTypeVariableFromIntersectionTypes` (inference.go).
fn get_single_type_variable_from_intersection_types(
    types_arena: &TypeArena,
    n: &InferenceState,
    types: &[TypeId],
) -> Option<TypeId> {
    let mut type_variable: Option<TypeId> = None;
    for &t in types {
        if !types_arena.get(t).flags.intersects(TypeFlags::INTERSECTION) {
            return None;
        }
        let v = types_arena
            .get(t)
            .types()
            .iter()
            .copied()
            .find(|&t| get_inference_info_for_type(types_arena, n, t).is_some());
        if v.is_none() || type_variable.is_some() && v != type_variable {
            return None;
        }
        type_variable = v;
    }
    type_variable
}

/// `getEndElementCount` (checker.go). PORT(stopgap): declared in checker.go,
/// inlined here so `inferFromObjectTypes` compiles while checker.go is
/// unported; remove in favor of the real port when it lands.
fn get_end_element_count(t: &TupleType, flags: ElementFlags) -> usize {
    for i in (1..=t.element_infos.len()).rev() {
        if !t.element_infos[i - 1].flags.intersects(flags) {
            return t.element_infos.len() - i;
        }
    }
    t.element_infos.len()
}

/// `tupleTypesDefinitelyUnrelated` (inference.go).
fn tuple_types_definitely_unrelated(types: &TypeArena, source: TypeId, target: TypeId) -> bool {
    let s = types.get(types.target_tuple_type(source).expect("tuple"));
    let t = types.get(types.target_tuple_type(target).expect("tuple"));
    let s = s.as_tuple_type();
    let t = t.as_tuple_type();
    !t.combined_flags.intersects(ElementFlags::VARIADIC) && t.min_length > s.min_length
        || !t.combined_flags.intersects(ElementFlags::VARIABLE)
            && (s.combined_flags.intersects(ElementFlags::VARIABLE)
                || t.fixed_length < s.fixed_length)
}

/// `(c *Checker) inferFromIntraExpressionSites` (inference.go). PORT: free
/// function because `Checker::infer_from_intra_expression_sites` already
/// exists as a `PORT(deferred)` stub in checker_core.rs — the stub should
/// delegate here once checker_core.rs is unlocked.
///
/// We collect intra-expression inference sites within object and array
/// literals to handle cases where inferred types flow between context
/// sensitive element expressions. For example:
///
/// ```text
/// declare function foo<T>(arg: [(n: number) => T, (x: T) => void]): void;
/// foo([_a => 0, n => n.toFixed()]);
/// ```
///
/// Above, both arrow functions in the tuple argument are context sensitive,
/// thus both are omitted from the pass that collects inferences from the
/// non-context sensitive parts of the arguments. In the subsequent pass where
/// nothing is omitted, we need to commit to an inference for T in order to
/// contextually type the parameter in the second arrow function, but we want
/// to first infer from the return type of the first arrow function. This
/// happens automatically when the arrow functions are discrete arguments
/// (because we infer from each argument before processing the next), but when
/// the arrow functions are elements of an object or array literal, we need to
/// perform intra-expression inferences early.
pub(crate) fn infer_from_intra_expression_sites(c: &mut Checker, n: InferenceContextId) {
    let sites =
        std::mem::take(&mut c.inference_contexts[n.index()].intra_expression_inference_sites);
    for site in sites {
        let node = site.node.expect("intraExpressionInferenceSite.node");
        let contextual_type = {
            let __program = c.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            if ast::is_method_declaration(&nodes[node]) {
                drop(nodes);
                c.get_contextual_type_for_object_literal_method(
                    node,
                    crate::types::ContextFlags::NO_CONSTRAINTS,
                )
            } else {
                drop(nodes);
                c.get_contextual_type(node, crate::types::ContextFlags::NO_CONSTRAINTS)
            }
        };
        if let Some(contextual_type) = contextual_type {
            let mut inferences = std::mem::take(&mut c.inference_contexts[n.index()].inferences);
            c.infer_types(
                &mut inferences,
                site.t.expect("intraExpressionInferenceSite.t"),
                contextual_type,
                InferencePriority::NONE_PRIORITY,
                false,
            );
            c.inference_contexts[n.index()].inferences = inferences;
        }
    }
}

/// `(c *Checker) getInferredType` (inference.go). PORT: free function for the
/// same reason as `infer_from_intra_expression_sites` (checker_core.rs stub).
pub(crate) fn get_inferred_type(c: &mut Checker, n: InferenceContextId, index: usize) -> TypeId {
    if c.inference_contexts[n.index()].inferences[index]
        .inferred_type
        .is_none()
    {
        // Snapshot the InferenceInfo — it lives in `c.inference_contexts`, so
        // it can't be borrowed across `&mut c` calls. Fields are written back
        // through `c.inference_contexts[n.index()].inferences[index]`.
        let inference = clone_inference_info(&c.inference_contexts[n.index()].inferences[index]);
        if inference.type_parameter == Some(c.error_type) {
            return c.error_type;
        }
        let mut inferred_type: Option<TypeId> = None;
        let mut fallback_type: Option<TypeId> = None;
        let signature = c.inference_contexts[n.index()].signature;
        if let Some(signature) = signature {
            let mut inferred_covariant_type: Option<TypeId> = None;
            if !inference.candidates.is_empty() {
                inferred_covariant_type = Some(c.get_covariant_inference(&inference, signature));
            }
            let mut inferred_contravariant_type: Option<TypeId> = None;
            if !inference.contra_candidates.is_empty() {
                inferred_contravariant_type = c.get_contravariant_inference(&inference);
            }
            if inferred_covariant_type.is_some() || inferred_contravariant_type.is_some() {
                // If we have both co- and contra-variant inferences, we prefer
                // the co-variant inference if it is not 'never', all
                // co-variant inferences are assignable to it (i.e. it isn't
                // one of a conflicting set of candidates), it is assignable to
                // some contra-variant inference, and no other type parameter
                // is constrained to this type parameter and has inferences
                // that would conflict. Otherwise, we prefer the
                // contra-variant inference. Similarly ignore co-variant `any`
                // inference when both are available as almost everything is
                // assignable to it and it would spoil the overall inference.
                let others: Vec<InferenceInfo> = c.inference_contexts[n.index()]
                    .inferences
                    .iter()
                    .map(clone_inference_info)
                    .collect();
                let prefer_covariant_type = inferred_covariant_type.is_some()
                    && (inferred_contravariant_type.is_none() || {
                        let covariant = inferred_covariant_type.unwrap();
                        !c.types_handle()
                            .get(covariant)
                            .flags
                            .intersects(TypeFlags::NEVER | TypeFlags::ANY)
                            && core::some(&inference.contra_candidates, |&t| {
                                c.is_type_assignable_to(covariant, t)
                            })
                            && others.iter().enumerate().all(|(i, other)| {
                                (i != index
                                    && c.get_constraint_of_type_parameter(
                                        other.type_parameter.expect("typeParameter"),
                                    ) != inference.type_parameter)
                                    || other
                                        .candidates
                                        .iter()
                                        .all(|&t| c.is_type_assignable_to(t, covariant))
                            })
                    });
                if prefer_covariant_type {
                    inferred_type = inferred_covariant_type;
                    fallback_type = inferred_contravariant_type;
                } else {
                    inferred_type = inferred_contravariant_type;
                    fallback_type = inferred_covariant_type;
                }
            } else if c.inference_contexts[n.index()]
                .flags
                .intersects(InferenceFlags::NO_DEFAULT)
            {
                // We use silentNeverType as the wildcard that signals no
                // inferences.
                inferred_type = Some(c.silent_never_type);
            } else {
                // Infer either the default or the empty object type when no
                // inferences were made. It is important to remember that in
                // this case, inference still succeeds, meaning there is no
                // error for not having inference candidates. An inference
                // error only occurs when there are *conflicting* candidates,
                // i.e. candidates with no common supertype.
                if let Some(default_type) = c.get_default_from_type_parameter(
                    inference.type_parameter.expect("typeParameter"),
                ) {
                    // Instantiate the default type. Any forward reference to a
                    // type parameter should be instantiated to the empty
                    // object type.
                    let backreference = c.new_backreference_mapper(n, index);
                    let non_fixing_mapper = c.inference_contexts[n.index()].non_fixing_mapper;
                    let merged = mapper::merge_type_mappers(
                        c,
                        Some(backreference),
                        non_fixing_mapper.expect("nonFixingMapper"),
                    );
                    inferred_type = Some(c.instantiate_type(default_type, Some(merged)));
                }
            }
        } else {
            inferred_type = c.get_type_from_inference(&inference);
        }
        c.inference_contexts[n.index()].inferences[index].inferred_type = inferred_type;
        if c.inference_contexts[n.index()].inferences[index]
            .inferred_type
            .is_none()
        {
            let default = core::if_else(
                c.inference_contexts[n.index()]
                    .flags
                    .intersects(InferenceFlags::ANY_DEFAULT),
                c.any_type,
                c.unknown_type,
            );
            c.inference_contexts[n.index()].inferences[index].inferred_type = Some(default);
        }
        if let Some(constraint) =
            c.get_constraint_of_type_parameter(inference.type_parameter.expect("typeParameter"))
        {
            let non_fixing_mapper = c.inference_contexts[n.index()].non_fixing_mapper;
            let instantiated_constraint = c.instantiate_type(constraint, non_fixing_mapper);
            // A pure return type inference is still filtered in a recursive
            // call resolution, whose result can become the type of the
            // enclosing declaration.
            if inferred_type.is_some()
                && (!c.inference_contexts[n.index()]
                    .flags
                    .intersects(InferenceFlags::NO_CONSTRAINT_CHECKS)
                    || inference.priority == InferencePriority::RETURN_TYPE)
            {
                let constraint_with_this =
                    c.get_type_with_this_argument(instantiated_constraint, inferred_type, false);
                if context_compare(c, n, inferred_type.unwrap(), constraint_with_this, false)
                    == Ternary::FALSE
                {
                    let mut filtered_by_constraint: Option<TypeId> = None;
                    if inference.priority == InferencePriority::RETURN_TYPE {
                        // If we have a pure return type inference, we may
                        // succeed by removing constituents of the inferred
                        // type that aren't assignable to the constraint type
                        // (pure return type inferences are speculation
                        // anyway).
                        filtered_by_constraint = Some(c.map_type(
                            inferred_type.unwrap(),
                            Rc::new(move |c: &mut Checker, t: TypeId| {
                                core::if_else(
                                    context_compare(c, n, t, constraint_with_this, false)
                                        != Ternary::FALSE,
                                    t,
                                    c.never_type,
                                )
                            }),
                        ));
                    }
                    inferred_type = core::if_else(
                        filtered_by_constraint.is_some_and(|f| {
                            !c.types_handle().get(f).flags.intersects(TypeFlags::NEVER)
                        }),
                        filtered_by_constraint,
                        None,
                    );
                }
            }
            if inferred_type.is_none() {
                // If the fallback type satisfies the constraint, we pick it.
                // Otherwise, we pick the constraint.
                let fallback_satisfies = fallback_type.is_some_and(|f| {
                    let with_this =
                        c.get_type_with_this_argument(instantiated_constraint, Some(f), false);
                    context_compare(c, n, f, with_this, false) != Ternary::FALSE
                });
                inferred_type = Some(core::if_else(
                    fallback_satisfies,
                    fallback_type.unwrap_or(c.never_type),
                    instantiated_constraint,
                ));
            }
            c.inference_contexts[n.index()].inferences[index].inferred_type = inferred_type;
        }
        c.clear_active_mapper_caches();
    }
    c.inference_contexts[n.index()].inferences[index]
        .inferred_type
        .expect("inferredType")
}

/// Invoke the context's `compareTypes` comparer. The `Box<TypeComparer>` is
/// taken out of the context for the duration of the call (Go stores a plain
/// func value).
fn context_compare(
    c: &mut Checker,
    n: InferenceContextId,
    s: TypeId,
    t: TypeId,
    report_errors: bool,
) -> Ternary {
    let compare = c.inference_contexts[n.index()]
        .compare_types
        .take()
        .expect("compareTypes");
    let result = compare(c, s, t, report_errors);
    c.inference_contexts[n.index()].compare_types = Some(compare);
    result
}

/// Take the context's `compareTypes` and re-share it: the original box is
/// wrapped in `Rc` so the context keeps a forwarding comparer and the clone
/// gets one too (Go assigns the same func value to both contexts).
fn share_compare_types(
    c: &mut Checker,
    n: InferenceContextId,
) -> Option<Box<TypeComparer<'static>>> {
    let compare = c.inference_contexts[n.index()].compare_types.take()?;
    let shared = Rc::new(compare);
    let for_context = shared.clone();
    c.inference_contexts[n.index()].compare_types = Some(Box::new(
        move |c: &mut Checker, s: TypeId, t: TypeId, report_errors: bool| {
            (*for_context)(c, s, t, report_errors)
        },
    ));
    Some(Box::new(
        move |c: &mut Checker, s: TypeId, t: TypeId, report_errors: bool| {
            (*shared)(c, s, t, report_errors)
        },
    ))
}

/// `getInferenceInfoForType` (inference.go). PORT: returns the index into
/// `n.inferences` (Go returns `*InferenceInfo`).
pub(crate) fn get_inference_info_for_type(
    types: &TypeArena,
    n: &InferenceState,
    t: TypeId,
) -> Option<usize> {
    if types.get(t).flags.intersects(TypeFlags::TYPE_VARIABLE) {
        let t = get_non_distributed_type_parameter(types, t);
        return n
            .inferences
            .iter()
            .position(|inference| inference.type_parameter == Some(t));
    }
    None
}

/// `newInferenceInfo` (inference.go).
pub(crate) fn new_inference_info(type_parameter: Option<TypeId>) -> InferenceInfo {
    InferenceInfo {
        type_parameter,
        priority: InferencePriority::MAX_VALUE,
        top_level: true,
        implied_arity: -1,
        ..Default::default()
    }
}

/// `cloneInferenceInfo` (inference.go).
pub(crate) fn clone_inference_info(info: &InferenceInfo) -> InferenceInfo {
    InferenceInfo {
        type_parameter: info.type_parameter,
        candidates: info.candidates.clone(),
        contra_candidates: info.contra_candidates.clone(),
        inferred_type: info.inferred_type,
        priority: info.priority,
        top_level: info.top_level,
        is_fixed: info.is_fixed,
        implied_arity: info.implied_arity,
    }
}

/// `hasInferenceCandidates` (inference.go).
pub(crate) fn has_inference_candidates(info: &InferenceInfo) -> bool {
    !info.candidates.is_empty() || !info.contra_candidates.is_empty()
}

/// `hasOverlappingInferences` (inference.go).
pub(crate) fn has_overlapping_inferences(a: &[InferenceInfo], b: &[InferenceInfo]) -> bool {
    for i in 0..a.len() {
        if has_inference_candidates(&a[i]) && has_inference_candidates(&b[i]) {
            return true;
        }
    }
    false
}
