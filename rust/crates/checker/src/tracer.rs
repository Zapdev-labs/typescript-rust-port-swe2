// Ported from tsc/internal/checker/tracer.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `Tracer` records types and trace events during type checking. Go's nil
// `*Tracer` becomes `Option<Tracer>` on the checker — call sites gate with
// `if let Some(tr) = &c.tracer`.
//
// PORT notes:
//
// - `tracing *tracing.Tracing` → `Arc<tracing::Tracing>` (the Rust session
//   is `Arc`-managed); `recorder tracing.Tracer` → `Arc<dyn
//   tracing::Tracer>` (a `TypeTracer`).
// - `Push` returns `Box<dyn FnOnce()>` like `tracing::Tracing::push` —
//   single-threaded (Go's checker is), so no `Send`.
//   Go's `temporarilyAddCheckerIndex` mutates the caller's `map[string]any`
//   in place and the deferred pop re-reads the *same map* — the Rust tracing
//   `push` takes `TraceArgs` by value, so the begin/end events capture the
//   args snapshot at push time. The `checkerId` add/restore on the caller's
//   map is preserved exactly; post-push caller mutations would not be seen
//   (call sites do not mutate between push and pop).
// - `tracedTypeAdapter.checker *Checker` (used by `Pattern`,
//   `RecursionIdentity`, `Display`) cannot be a `&mut Checker` — recorded
//   types outlive checker borrows. The
//   port stores shareable handles (`TypeArena` clone, `pattern_for_type`
//   `Arc`) and resolves `RecursionIdentity` eagerly in
//   `Checker::trace_record_type` where `&mut Checker` is available —
//   recursion-identity inputs (reference node, symbol, object flags,
//   conditional root) are creation-time fields. `Display` needs the deferred
//   `Checker::type_to_string` (nodebuilderimpl.go), so it returns "" until
//   that lands — PORT(deferred). Nested adapters produced by `wrap_type`
//   inside accessors have `recursion_identity: None` (Go resolves theirs
//   lazily too; the port can't without `&mut Checker`).

use std::rc::Rc;
use std::sync::{Arc, RwLock};

use rustc_hash::FxHashMap;
use tsc_ast::{NodeId, SymbolId};
use tsc_tracing::{self as tracing, Phase, RecursionIdentity, TraceArgs, TracedType, TypeTracer};
// `record_type` is a `tracing::Tracer` trait method on `TypeTracer`.
use tsc_tracing::Tracer as _;

use crate::types::{ObjectFlags, TypeArena, TypeFlags, TypeId, format_type_flags};

/// `type Tracer struct` — per-checker recorder. A `None` `Option<Tracer>` is
/// Go's valid no-op nil `*Tracer`.
pub struct Tracer {
    /// `tracing`.
    tracing: Arc<tracing::Tracing>,
    /// `recorder` (`tracing.Tracer` — a `*TypeTracer` in practice).
    recorder: Arc<TypeTracer>,
    /// `checkerIndex`.
    checker_index: i32,
}

impl Tracer {
    /// `NewTracer` — creates a `Tracer` for the given checker index that
    /// records both type-creation events and trace events through the
    /// provided tracing session.
    pub fn new(tr: &Arc<tracing::Tracing>, checker_index: i32) -> Tracer {
        Tracer {
            tracing: tr.clone(),
            recorder: tr.new_type_tracer(checker_index),
            checker_index,
        }
    }

    /// `t.recorder` — the `TypeTracer` (Go callers hold it in the
    /// `tracing.Tracer` interface field).
    pub fn recorder(&self) -> &Arc<TypeTracer> {
        &self.recorder
    }

    /// `(t *Tracer) RecordType` — records a type for later dumping. PORT:
    /// the adapter is built by `Checker::trace_record_type` (it needs `&mut
    /// Checker` for the recursion identity); this is the bare record step.
    pub fn record_type(&self, t: Rc<dyn TracedType>) {
        self.recorder.record_type(t);
    }

    /// `(t *Tracer) Push` — starts a trace event block.
    ///
    /// `args` is the caller's `TraceArgs`; `checkerId` is temporarily added
    /// for `separate_begin_and_end` events exactly as Go's
    /// `temporarilyAddCheckerIndex`/`restore` pair does.
    pub fn push(
        &self,
        phase: Phase,
        name: &str,
        args: &mut TraceArgs,
        separate_begin_and_end: bool,
    ) -> Box<dyn FnOnce()> {
        if !separate_begin_and_end {
            return self.tracing.push(
                phase,
                name,
                self.copy_with_checker_index(args),
                separate_begin_and_end,
            );
        }

        // `temporarilyAddCheckerIndex(args)` — insert, push, restore.
        let checker_id = serde_json::Value::from(self.checker_index);
        let previous = args.insert("checkerId".to_string(), checker_id);
        let pop = self
            .tracing
            .push(phase, name, args.clone(), separate_begin_and_end);
        match previous {
            Some(previous) => {
                args.insert("checkerId".to_string(), previous);
            }
            None => {
                args.remove("checkerId");
            }
        }

        // Go's returned closure re-adds `checkerId` to the caller's map then
        // pops; `Tracing::push` already captured the (checkerId-bearing)
        // args for the end event — see the file header.
        pop
    }

    /// `(t *Tracer) Instant` — records an instant event.
    pub fn instant(&self, phase: Phase, name: &str, args: &TraceArgs) {
        self.tracing
            .instant(phase, name, self.copy_with_checker_index(args));
    }

    /// `(t *Tracer) copyWithCheckerIndex`.
    fn copy_with_checker_index(&self, args: &TraceArgs) -> TraceArgs {
        let mut with_checker_index = args.clone();
        with_checker_index.insert(
            "checkerId".to_string(),
            serde_json::Value::from(self.checker_index),
        );
        with_checker_index
    }
}

/// `type tracedTypeAdapter struct` — adapts a `TypeId` + shared `TypeArena`
/// to `tracing::TracedType`.
///
/// PORT: Go stores `t *Type` and `checker *Checker`. Here `t` is the arena
/// id and `types`/`pattern_for_type` are `Arc`-shared handles into checker
/// state; `recursion_identity` is computed eagerly by the checker before
/// recording (see header). `!Send`/`!Sync` — `types` is `Rc<RefCell<..>>`,
/// matching Go's single-threaded checker.
pub struct TracedTypeAdapter {
    /// `a.t`.
    pub t: TypeId,
    /// The owning checker's type arena (Go: `a.t` dereferences).
    pub types: TypeArena,
    /// `a.checker.patternForType` (Go: `a.checker` field access).
    pub pattern_for_type: Arc<RwLock<FxHashMap<TypeId, NodeId>>>,
    /// `getRecursionIdentity(a.t).value` — computed eagerly at record time
    /// (see header); `None` for nested adapters wrapped by accessors.
    pub recursion_identity: Option<RecursionIdentity>,
}

impl TracedTypeAdapter {
    /// `wrapType` / `wrapTypes` — nested adapters share the arena handles
    /// and carry no precomputed recursion identity (see header).
    fn wrap_type(&self, t: Option<TypeId>) -> Option<Rc<dyn TracedType>> {
        t.map(|t| -> Rc<dyn TracedType> {
            Rc::new(TracedTypeAdapter {
                t,
                types: self.types.clone(),
                pattern_for_type: self.pattern_for_type.clone(),
                recursion_identity: None,
            })
        })
    }

    /// `wrapTypes`.
    fn wrap_types(&self, types: &[TypeId]) -> Vec<Option<Rc<dyn TracedType>>> {
        if types.is_empty() {
            return Vec::new();
        }
        types.iter().map(|&t| self.wrap_type(Some(t))).collect()
    }
}

impl TracedType for TracedTypeAdapter {
    /// `(a *tracedTypeAdapter) Id`.
    fn id(&self) -> u32 {
        self.t.0
    }

    /// `FormatFlags`.
    fn format_flags(&self) -> Vec<String> {
        format_type_flags(self.types.get(self.t).flags)
    }

    /// `IsConditional`.
    fn is_conditional(&self) -> bool {
        self.types
            .get(self.t)
            .flags
            .intersects(TypeFlags::CONDITIONAL)
    }

    /// `Symbol`.
    fn symbol(&self) -> Option<SymbolId> {
        self.types.get(self.t).symbol
    }

    /// `AliasSymbol`.
    fn alias_symbol(&self) -> Option<SymbolId> {
        self.types
            .get(self.t)
            .alias
            .as_ref()
            .and_then(|a| a.symbol())
    }

    /// `AliasTypeArguments`.
    fn alias_type_arguments(&self) -> Vec<Option<Rc<dyn TracedType>>> {
        let args = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            match &ty.alias {
                Some(alias) => alias.type_arguments().to_vec(),
                None => Vec::new(),
            }
        };
        self.wrap_types(&args)
    }

    /// `IntrinsicName`.
    fn intrinsic_name(&self) -> String {
        let __arena_ty = self.types.clone();
        let ty = __arena_ty.get(self.t);
        if !ty.flags.intersects(TypeFlags::INTRINSIC) {
            return String::new();
        }
        match &ty.data {
            crate::types::TypeData::Intrinsic(d) => d.intrinsic_name.clone(),
            _ => String::new(),
        }
    }

    /// `UnionTypes`.
    fn union_types(&self) -> Vec<Option<Rc<dyn TracedType>>> {
        let types = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::UNION) {
                Vec::new()
            } else {
                ty.as_union_type().union_or_intersection.types().to_vec()
            }
        };
        self.wrap_types(&types)
    }

    /// `IntersectionTypes`.
    fn intersection_types(&self) -> Vec<Option<Rc<dyn TracedType>>> {
        let types = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::INTERSECTION) {
                Vec::new()
            } else {
                ty.as_intersection_type()
                    .union_or_intersection
                    .types()
                    .to_vec()
            }
        };
        self.wrap_types(&types)
    }

    /// `IndexType`.
    fn index_type(&self) -> Option<Rc<dyn TracedType>> {
        let target = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::INDEX) {
                None
            } else {
                ty.as_index_type().target
            }
        };
        self.wrap_type(target)
    }

    /// `IndexedAccessObjectType`.
    fn indexed_access_object_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::INDEXED_ACCESS) {
                None
            } else {
                ty.as_indexed_access_type().object_type
            }
        };
        self.wrap_type(t)
    }

    /// `IndexedAccessIndexType`.
    fn indexed_access_index_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::INDEXED_ACCESS) {
                None
            } else {
                ty.as_indexed_access_type().index_type
            }
        };
        self.wrap_type(t)
    }

    /// `ConditionalCheckType`.
    fn conditional_check_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::CONDITIONAL) {
                None
            } else {
                ty.as_conditional_type().check_type
            }
        };
        self.wrap_type(t)
    }

    /// `ConditionalExtendsType`.
    fn conditional_extends_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::CONDITIONAL) {
                None
            } else {
                ty.as_conditional_type().extends_type
            }
        };
        self.wrap_type(t)
    }

    /// `ConditionalTrueType`.
    fn conditional_true_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::CONDITIONAL) {
                None
            } else {
                ty.as_conditional_type().resolved_true_type
            }
        };
        self.wrap_type(t)
    }

    /// `ConditionalFalseType`.
    fn conditional_false_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::CONDITIONAL) {
                None
            } else {
                ty.as_conditional_type().resolved_false_type
            }
        };
        self.wrap_type(t)
    }

    /// `SubstitutionBaseType`.
    fn substitution_base_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::SUBSTITUTION) {
                None
            } else {
                ty.as_substitution_type().base_type
            }
        };
        self.wrap_type(t)
    }

    /// `SubstitutionConstraintType`.
    fn substitution_constraint_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::SUBSTITUTION) {
                None
            } else {
                ty.as_substitution_type().constraint
            }
        };
        self.wrap_type(t)
    }

    /// `ReferenceTarget`.
    fn reference_target(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::OBJECT)
                || !ty.object_flags.intersects(ObjectFlags::REFERENCE)
            {
                None
            } else {
                ty.target()
            }
        };
        self.wrap_type(t)
    }

    /// `ReferenceTypeArguments`.
    fn reference_type_arguments(&self) -> Vec<Option<Rc<dyn TracedType>>> {
        let args = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::OBJECT)
                || !ty.object_flags.intersects(ObjectFlags::REFERENCE)
            {
                Vec::new()
            } else {
                ty.as_type_reference().resolved_type_arguments.to_vec()
            }
        };
        self.wrap_types(&args)
    }

    /// `ReferenceNode`.
    fn reference_node(&self) -> Option<NodeId> {
        let __arena_ty = self.types.clone();
        let ty = __arena_ty.get(self.t);
        if !ty.flags.intersects(TypeFlags::OBJECT)
            || !ty.object_flags.intersects(ObjectFlags::REFERENCE)
        {
            return None;
        }
        ty.as_type_reference().node
    }

    /// `ReverseMappedSourceType`.
    fn reverse_mapped_source_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::OBJECT)
                || !ty.object_flags.intersects(ObjectFlags::REVERSE_MAPPED)
            {
                None
            } else {
                ty.as_reverse_mapped_type().source
            }
        };
        self.wrap_type(t)
    }

    /// `ReverseMappedMappedType`.
    fn reverse_mapped_mapped_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::OBJECT)
                || !ty.object_flags.intersects(ObjectFlags::REVERSE_MAPPED)
            {
                None
            } else {
                ty.as_reverse_mapped_type().mapped_type
            }
        };
        self.wrap_type(t)
    }

    /// `ReverseMappedConstraintType`.
    fn reverse_mapped_constraint_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::OBJECT)
                || !ty.object_flags.intersects(ObjectFlags::REVERSE_MAPPED)
            {
                None
            } else {
                ty.as_reverse_mapped_type().constraint_type
            }
        };
        self.wrap_type(t)
    }

    /// `EvolvingArrayElementType`.
    fn evolving_array_element_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::OBJECT)
                || !ty.object_flags.intersects(ObjectFlags::EVOLVING_ARRAY)
            {
                None
            } else {
                ty.as_evolving_array_type().element_type
            }
        };
        self.wrap_type(t)
    }

    /// `EvolvingArrayFinalType`.
    fn evolving_array_final_type(&self) -> Option<Rc<dyn TracedType>> {
        let t = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get(self.t);
            if !ty.flags.intersects(TypeFlags::OBJECT)
                || !ty.object_flags.intersects(ObjectFlags::EVOLVING_ARRAY)
            {
                None
            } else {
                ty.as_evolving_array_type().final_array_type
            }
        };
        self.wrap_type(t)
    }

    /// `IsTuple`.
    fn is_tuple(&self) -> bool {
        self.types
            .get(self.t)
            .object_flags
            .intersects(ObjectFlags::TUPLE)
    }

    /// `Pattern` — `a.checker.patternForType[a.t]` through the shared map.
    fn pattern(&self) -> Option<NodeId> {
        self.pattern_for_type.read().unwrap().get(&self.t).copied()
    }

    /// `RecursionIdentity` — resolved eagerly at record time (see header).
    fn recursion_identity(&self) -> Option<RecursionIdentity> {
        self.recursion_identity.clone()
    }

    /// `Display` — Go calls `a.checker.TypeToString(a.t)` with a panic
    /// guard for incomplete types. PORT(deferred): `Checker::type_to_string`
    /// lands with nodebuilderimpl.go; returning "" matches Go's recovered-
    /// panic path.
    fn display(&self) -> String {
        String::new()
    }
}
