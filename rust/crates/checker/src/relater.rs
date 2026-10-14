// Ported from tsc/internal/checker/relater.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the complete file: every
// `func`, `type`, and `const` from the Go source, in declaration order.
//
// PORT notes:
//
// - `*Type` → `TypeId`, `*Signature` → `SignatureId`, `*ast.Node` →
//   `NodeId`, `*ast.Symbol` → `SymbolId`, `*IndexInfo` → `IndexInfoId`,
//   `*TypeMapper` → `TypeMapperId`, `*TypePredicate` → `TypePredicate` (an
//   arena-less value type; Go passes it by pointer — the port passes
//   `Option<&TypePredicate>`/`Box<TypePredicate>`).
// - `*Relation` → `SharedRelation = Rc<RefCell<Relation>>` — the checker's
//   relation fields and `Relater::relation` alias the same map, matching
//   Go's shared `*Relation`.
// - `Relater` drops the `c *Checker` back-pointer; its methods take an
//   explicit `&mut Checker` first parameter. Go method values bound to a
//   `*Relater` (`r.reportError`, `r.isRelatedToSimple`,
//   `r.isRelatedToWorker`, and the `isRelatedToWorker` closure built in
//   `signatureRelatedTo`) can't be cloned into `dyn Fn`/`Rc` receivers, so
//   they travel as the `Comparer`/`ErrorReporter` tags below and are
//   re-resolved against the `&mut Relater` threaded through the call —
//   `None` mirrors Go's `nil` reporter/comparer.
// - `*TypePredicate` sentinel `c.noTypePredicate` is cloned (not shared by
//   pointer) into `Signature::resolved_type_predicate`; identity checks
//   degrade to structural comparison via `is_no_type_predicate` — sound
//   because `parameterName == "<<unresolved>>"` never arises from a
//   user-declared predicate.
// - `VarianceLinks::variances` is a bare `Vec` (no nil/empty tri-state):
//   this file observes Go's `links.variances == nil` as "the
//   `variance_links` entry does not exist yet" — entries are only created
//   when a result (non-empty or the empty uncomputable marker) is stored.
// - Cross-file calls resolve by snake_case name to sibling ports
//   (`crate::checker_{a..d}` for checker.go, `crate::utilities` for
//   utilities.go, `crate::inference`, `crate::flow`, `crate::jsx`,
//   `crate::grammarchecks`); unresolved symbols are expected until those
//   files land.
// - `RecursionId` and `get_recursion_identity` already live in
//   checker_core.rs (mirrored for tracer.rs). `get_recursion_identity_target`/
//   `get_recursion_identity_from_target`/`as_recursion_id_*` are private
//   there, so `hasMatchingRecursionIdentity`/`isDeeplyNestedType` use the
//   PORT(mirrored) copies below.
// - `c.compareTypesAssignableWorker` was previously stubbed `PORT(deferred)`
//   in checker_core.rs; the real body lives here (the stub is gone).
// - `c.enumRelation` in checker_core.rs is keyed by `EnumRelationKey`,
//   matching Go (was briefly `EnumLiteralKey`; corrected).

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, NodeId, SymbolId};
use tsc_collections::{OrderedSet, Set};
use tsc_core::core;
use tsc_tracing::TraceArgs;

use crate::checker_core::{
    CacheHashKey, CheckMode, Checker, InferenceFlags, InferencePriority, RecursionId,
    is_object_or_array_literal_type, is_tuple_type, value_to_string,
};
use crate::checker_types::{
    EnumRelationKey, MappedTypeModifiers, TypeSystemPropertyName, VarianceStackEntry,
};
use crate::flagdef::flag_type;
use crate::mapper::TypeMapperId;
use crate::types::{
    AccessFlags, ElementFlags, IndexFlags, IndexInfoId, ObjectFlags, SignatureFlags, SignatureId,
    SignatureKind, Ternary, TypeFlags, TypeId, TypePredicate, TypePredicateKind, VarianceFlags,
};

// SignatureCheckMode

flag_type! {
    /// `type SignatureCheckMode uint32` (relater.go).
    pub struct SignatureCheckMode(pub u32);
}

impl SignatureCheckMode {
    /// `SignatureCheckModeBivariantCallback`.
    pub const BIVARIANT_CALLBACK: SignatureCheckMode = SignatureCheckMode(1 << 0);
    /// `SignatureCheckModeStrictCallback`.
    pub const STRICT_CALLBACK: SignatureCheckMode = SignatureCheckMode(1 << 1);
    /// `SignatureCheckModeIgnoreReturnTypes`.
    pub const IGNORE_RETURN_TYPES: SignatureCheckMode = SignatureCheckMode(1 << 2);
    /// `SignatureCheckModeStrictArity`.
    pub const STRICT_ARITY: SignatureCheckMode = SignatureCheckMode(1 << 3);
    /// `SignatureCheckModeStrictTopSignature`.
    pub const STRICT_TOP_SIGNATURE: SignatureCheckMode = SignatureCheckMode(1 << 4);
    /// `SignatureCheckModeCallback`.
    pub const CALLBACK: SignatureCheckMode =
        SignatureCheckMode(Self::BIVARIANT_CALLBACK.0 | Self::STRICT_CALLBACK.0);
}

// MinArgumentCountFlags

flag_type! {
    /// `type MinArgumentCountFlags uint32` (relater.go).
    pub struct MinArgumentCountFlags(pub u32);
}

impl MinArgumentCountFlags {
    /// `MinArgumentCountFlagsStrongArityForUntypedJS`.
    pub const STRONG_ARITY_FOR_UNTYPED_JS: MinArgumentCountFlags = MinArgumentCountFlags(1 << 0);
    /// `MinArgumentCountFlagsVoidIsNonOptional`.
    pub const VOID_IS_NON_OPTIONAL: MinArgumentCountFlags = MinArgumentCountFlags(1 << 1);
}

// IntersectionState

flag_type! {
    /// `type IntersectionState uint32` (relater.go).
    pub struct IntersectionState(pub u32);
}

impl IntersectionState {
    /// `IntersectionStateSource` — source type is a constituent of an outer
    /// intersection.
    pub const SOURCE: IntersectionState = IntersectionState(1 << 0);
    /// `IntersectionStateTarget` — target type is a constituent of an outer
    /// intersection.
    pub const TARGET: IntersectionState = IntersectionState(1 << 1);
}

// RecursionFlags

flag_type! {
    /// `type RecursionFlags uint32` (relater.go).
    pub struct RecursionFlags(pub u32);
}

impl RecursionFlags {
    /// `RecursionFlagsSource`.
    pub const SOURCE: RecursionFlags = RecursionFlags(1 << 0);
    /// `RecursionFlagsTarget`.
    pub const TARGET: RecursionFlags = RecursionFlags(1 << 1);
    /// `RecursionFlagsBoth`.
    pub const BOTH: RecursionFlags = RecursionFlags(Self::SOURCE.0 | Self::TARGET.0);
}

// ExpandingFlags

flag_type! {
    /// `type ExpandingFlags uint8` (relater.go).
    pub struct ExpandingFlags(pub u8);
}

impl ExpandingFlags {
    /// `ExpandingFlagsSource`.
    pub const SOURCE: ExpandingFlags = ExpandingFlags(1 << 0);
    /// `ExpandingFlagsTarget`.
    pub const TARGET: ExpandingFlags = ExpandingFlags(1 << 1);
    /// `ExpandingFlagsBoth`.
    pub const BOTH: ExpandingFlags = ExpandingFlags(Self::SOURCE.0 | Self::TARGET.0);
}

// RelationComparisonResult

flag_type! {
    /// `type RelationComparisonResult uint32` (relater.go).
    pub struct RelationComparisonResult(pub u32);
}

impl RelationComparisonResult {
    /// `RelationComparisonResultSucceeded`.
    pub const SUCCEEDED: RelationComparisonResult = RelationComparisonResult(1 << 0);
    /// `RelationComparisonResultFailed`.
    pub const FAILED: RelationComparisonResult = RelationComparisonResult(1 << 1);
    /// `RelationComparisonResultReportsUnmeasurable`.
    pub const REPORTS_UNMEASURABLE: RelationComparisonResult = RelationComparisonResult(1 << 3);
    /// `RelationComparisonResultReportsUnreliable`.
    pub const REPORTS_UNRELIABLE: RelationComparisonResult = RelationComparisonResult(1 << 4);
    /// `RelationComparisonResultComplexityOverflow`.
    pub const COMPLEXITY_OVERFLOW: RelationComparisonResult = RelationComparisonResult(1 << 5);
    /// `RelationComparisonResultReportsMask`.
    pub const REPORTS_MASK: RelationComparisonResult =
        RelationComparisonResult(Self::REPORTS_UNMEASURABLE.0 | Self::REPORTS_UNRELIABLE.0);
    /// `RelationComparisonResultOverflow` — `relater.go` uses the
    /// `ComplexityOverflow` name; `checker.go` reads `.Overflow` via
    /// `RelationComparisonResult` flags — same bit.
    pub const OVERFLOW: RelationComparisonResult = Self::COMPLEXITY_OVERFLOW;
}

// DiagnosticAndArguments

/// `type DiagnosticAndArguments struct` (relater.go). `arguments []any` →
/// `Vec<String>` per this port's diagnostic-args convention (Go args are
/// strings, ints, and `*Type`-derived strings — all stringified at
/// construction).
#[derive(Default)]
pub struct DiagnosticAndArguments {
    /// `message`.
    pub message: Option<&'static tsc_diagnostics::Message>,
    /// `arguments`.
    pub arguments: Vec<String>,
}

// ErrorOutputContainer

/// `type ErrorOutputContainer struct` (relater.go).
#[derive(Default)]
pub struct ErrorOutputContainer {
    /// `errors`.
    pub errors: Vec<ast::diagnostic::DiagnosticRef>,
    /// `skipLogging`.
    pub skip_logging: bool,
}

// ErrorReporter

/// `type ErrorReporter func(message *diagnostics.Message, args ...any)`
/// (relater.go). The only non-nil reporter ever passed is the method value
/// `r.reportError`; a `&mut` method receiver can't be cloned into a
/// `dyn FnMut`, so the port passes `Option<&mut Relater>` — `Some` invokes
/// [`Relater::report_error`], `None` is Go's `nil`.
pub type ErrorReporter<'a> = Option<&'a mut Relater>;

/// Run `f` on the `Relater` a `Comparer` should dispatch to: the in-scope
/// reporter when present, else a snapshot of the relater active on an
/// enclosing `check_type_related_to_ex` frame, popped from
/// `Checker::relater_stack` for the duration of the call and pushed back
/// after (Go comparer closures capture the live `r`; a popped snapshot is
/// the closest safe equivalent — `relation` is `Rc`-shared so the results
/// cache stays coherent).
fn run_comparer_relater<R>(
    c: &mut Checker,
    r: &mut ErrorReporter<'_>,
    f: impl FnOnce(&mut Relater, &mut Checker) -> R,
) -> R {
    if let Some(rr) = r.as_deref_mut() {
        return f(rr, c);
    }
    let mut rr = c.relater_pool.pop().unwrap_or_else(|| {
        c.relater_seed
            .as_ref()
            .expect("relater comparer invoked outside a relation")
            .snapshot()
    });
    let out = f(&mut rr, c);
    c.relater_pool.push(rr);
    out
}

// Comparer

/// Go `TypeComparer` (`func(s,t *Type, reportErrors bool) Ternary`) and
/// `func(s, t *Type) Ternary` parameters in this file are always one of a
/// fixed set of method values bound to either `*Checker` or the active
/// `*Relater`. A `&mut` receiver can't be cloned into a callback, so the
/// callee receives the relater separately (the `ErrorReporter`/`&mut
/// Relater` parameter is also the receiver the `IsRelated*` variants run
/// against — every call site that passes a `Relater*` comparer also passes
/// a non-nil reporter bound to the same relater) and this tag selects the
/// comparison. `Checker*` variants never need the relater.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Comparer {
    /// `c.compareTypesAssignable` — the checker's `TypeComparer` field (3-arg).
    Assignable,
    /// `c.compareTypesIdentical` (2-arg; `reportErrors` ignored).
    Identical,
    /// `c.compareTypesSubtypeOf` (2-arg; `reportErrors` ignored).
    SubtypeOf,
    /// `c.compareTypesAssignableSimple` (2-arg; `reportErrors` ignored).
    AssignableSimple,
    /// `r.isRelatedToSimple` — `is_related_to_ex(BOTH, false, None, NONE)`.
    IsRelatedToSimple,
    /// `r.isRelatedToWorker` — `is_related_to_ex(BOTH, reportErrors, None, NONE)`.
    IsRelatedToWorker,
    /// `signatureRelatedTo`'s `isRelatedToWorker` closure —
    /// `is_related_to_ex(BOTH, reportErrors, None, intersection_state)`.
    IsRelatedToEx(IntersectionState),
}

/// Invoke a `Comparer` (Go's `compareTypes(s, t)` /
/// `compareTypes(s, t, reportErrors)` / `isRelatedTo(s, t)` call sites).
fn compare_via(
    c: &mut Checker,
    r: &mut ErrorReporter<'_>,
    comparer: Comparer,
    s: TypeId,
    t: TypeId,
    report_errors: bool,
) -> Ternary {
    match comparer {
        Comparer::Assignable => {
            let f = c
                .compare_types_assignable
                .clone()
                .expect("compareTypesAssignable is initialized by new_checker");
            f(c, s, t, report_errors)
        }
        Comparer::Identical => c.compare_types_identical(s, t),
        Comparer::SubtypeOf => c.compare_types_subtype_of(s, t),
        Comparer::AssignableSimple => c.compare_types_assignable_simple(s, t),
        Comparer::IsRelatedToSimple => {
            run_comparer_relater(c, r, |rr, c| rr.is_related_to_simple(c, s, t))
        }
        Comparer::IsRelatedToWorker => {
            run_comparer_relater(c, r, |rr, c| rr.is_related_to_worker(c, s, t, report_errors))
        }
        Comparer::IsRelatedToEx(state) => run_comparer_relater(c, r, |rr, c| {
            rr.is_related_to_ex(c, s, t, RecursionFlags::BOTH, report_errors, None, state)
        }),
    }
}

/// `errorReporter(message, args...)` — Go guards every call with
/// `errorReporter != nil`; `Some(r)` runs `r.report_error`.
fn report_via(
    c: &mut Checker,
    reporter: &mut ErrorReporter<'_>,
    message: &'static tsc_diagnostics::Message,
    args: &[String],
) {
    if let Some(r) = reporter.as_deref_mut() {
        r.report_error(c, message, args);
    }
}

// RecursionId helpers (mirrored)

// `AsRecursionId` — PORT(mirrored) copies of checker_core.rs's private
// `as_recursion_id_*`/tag constants (relater.go's `asRecursionId`). Needed
// here because `hasMatchingRecursionIdentity`/`isDeeplyNestedType` build
// identities directly.
const RECURSION_ID_SYMBOL_TAG: u64 = 1 << 62;
const RECURSION_ID_TYPE_TAG: u64 = 2 << 62;

/// `asRecursionId` for `*ast.Node` (relater.go). PORT(mirrored).
fn as_recursion_id_node(node: NodeId) -> RecursionId {
    RecursionId {
        value: tsc_tracing::RecursionIdentity::Object(node.0),
    }
}

/// `asRecursionId` for `*ast.Symbol` (relater.go). PORT(mirrored).
fn as_recursion_id_symbol(symbol: SymbolId) -> RecursionId {
    RecursionId {
        value: tsc_tracing::RecursionIdentity::Object(RECURSION_ID_SYMBOL_TAG | symbol.0 as u64),
    }
}

/// `asRecursionId` for `*Type` (relater.go). PORT(mirrored).
fn as_recursion_id_type(t: TypeId) -> RecursionId {
    RecursionId {
        value: tsc_tracing::RecursionIdentity::Object(RECURSION_ID_TYPE_TAG | t.0 as u64),
    }
}

// Relation

/// `type Relation struct` (relater.go). Go's `results` map is allocated
/// lazily by `set`; here it starts empty (same observable state).
#[derive(Default)]
pub struct Relation {
    /// `results`.
    pub results: FxHashMap<CacheHashKey, RelationComparisonResult>,
}

/// `Rc<RefCell<Relation>>` — the shape stored on `Checker` (subtypeRelation
/// etc.) and borrowed by `Relater::relation`. The interior mutability
/// mirrors Go aliasing the same `*Relation` from both.
pub type SharedRelation = Rc<RefCell<Relation>>;

impl Relation {
    /// `(r *Relation) get`.
    pub fn get(&self, key: CacheHashKey) -> RelationComparisonResult {
        self.results.get(&key).copied().unwrap_or_default()
    }

    /// `(r *Relation) set`.
    pub fn set(&mut self, key: CacheHashKey, result: RelationComparisonResult) {
        self.results.insert(key, result);
    }

    /// `(r *Relation) size`.
    pub fn size(&self) -> usize {
        self.results.len()
    }
}

// errorState / ErrorChain

/// `type errorState struct` (relater.go) — the `(errorChain, relatedInfo)`
/// pair `recursiveTypeRelatedTo` snapshots for error reporting.
#[derive(Clone, Default)]
pub struct ErrorState {
    /// `errorChain`.
    pub error_chain: Option<Box<ErrorChain>>,
    /// `relatedInfo`.
    pub related_info: Vec<ast::diagnostic::DiagnosticRef>,
}

/// `type ErrorChain struct` (relater.go).
#[derive(Clone, Default)]
pub struct ErrorChain {
    /// `next`.
    pub next: Option<Box<ErrorChain>>,
    /// `message`.
    pub message: Option<&'static tsc_diagnostics::Message>,
    /// `args` — `[]any` → `Vec<String>`.
    pub args: Vec<String>,
}

// Relater

/// `type Relater struct` (relater.go). The `c *Checker` back-pointer is
/// dropped (methods take `&mut Checker`), and `relation` is the shared
/// `Rc<RefCell<Relation>>` also stored on the checker — Go aliases the same
/// `*Relation`. `next` links the `Checker::free_relater` freelist.
#[derive(Default)]
pub struct Relater {
    /// `relation`.
    pub relation: Option<SharedRelation>,
    /// `errorNode`.
    pub error_node: Option<NodeId>,
    /// `errorChain`.
    pub error_chain: Option<Box<ErrorChain>>,
    /// `relatedInfo`.
    pub related_info: Vec<ast::diagnostic::DiagnosticRef>,
    /// `maybeKeys`.
    pub maybe_keys: Vec<CacheHashKey>,
    /// `maybeKeysSet`.
    pub maybe_keys_set: OrderedSet<CacheHashKey>,
    /// `sourceStack`.
    pub source_stack: Vec<TypeId>,
    /// `targetStack`.
    pub target_stack: Vec<TypeId>,
    /// `maybeCount`.
    pub maybe_count: i32,
    /// `sourceDepth`.
    pub source_depth: i32,
    /// `targetDepth`.
    pub target_depth: i32,
    /// `expandingFlags`.
    pub expanding_flags: ExpandingFlags,
    /// `overflow`.
    pub overflow: bool,
    /// `relationCount`.
    pub relation_count: i32,
    /// `next` — free-list link (`Checker::free_relater`).
    pub next: Option<Box<Relater>>,
}

impl Relater {
    /// `r.relation` — the active `*Relation`. Every entry point stores a
    /// relation before use (Go relies on the same invariant).
    #[inline]
    fn relation(&self) -> SharedRelation {
        self.relation
            .clone()
            .expect("relater has an active relation")
    }

    /// Copy of the relater's comparison state for use as a comparer target
    /// (see `Checker::relater_stack`). `relation` is `Rc`-shared with the
    /// original — the results cache stays coherent — while the in-flight
    /// keys/stacks carry the entry-time state for cycle detection. `next`
    /// (the freelist link) is not part of Go state and is not copied.
    fn snapshot(&self) -> Relater {
        Relater {
            relation: self.relation.clone(),
            error_node: self.error_node,
            error_chain: self.error_chain.clone(),
            related_info: self.related_info.clone(),
            maybe_keys: self.maybe_keys.clone(),
            maybe_keys_set: self.maybe_keys_set.clone(),
            source_stack: self.source_stack.clone(),
            target_stack: self.target_stack.clone(),
            maybe_count: self.maybe_count,
            source_depth: self.source_depth,
            target_depth: self.target_depth,
            expanding_flags: self.expanding_flags,
            overflow: self.overflow,
            relation_count: self.relation_count,
            next: None,
        }
    }
}

// Basic relation entry points

impl Checker {
    /// `(c *Checker) isTypeIdenticalTo`.
    pub(crate) fn is_type_identical_to(&mut self, source: TypeId, target: TypeId) -> bool {
        let relation = self.identity_relation.clone();
        self.is_type_related_to(source, target, &relation)
    }

    /// `(c *Checker) compareTypesIdentical`.
    pub(crate) fn compare_types_identical(&mut self, source: TypeId, target: TypeId) -> Ternary {
        if self.is_type_identical_to(source, target) {
            return Ternary::TRUE;
        }
        Ternary::FALSE
    }

    /// `(c *Checker) compareTypesAssignableSimple`.
    pub(crate) fn compare_types_assignable_simple(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> Ternary {
        let relation = self.assignable_relation.clone();
        if self.is_type_related_to(source, target, &relation) {
            return Ternary::TRUE;
        }
        Ternary::FALSE
    }

    /// `(c *Checker) compareTypesAssignableWorker`. The real body replaces
    /// the `PORT(deferred)` stub in checker_core.rs.
    pub(crate) fn compare_types_assignable_worker(
        &mut self,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
    ) -> Ternary {
        let _ = report_errors;
        let relation = self.assignable_relation.clone();
        if self.is_type_related_to(source, target, &relation) {
            return Ternary::TRUE;
        }
        Ternary::FALSE
    }

    /// `(c *Checker) compareTypesSubtypeOf`.
    pub(crate) fn compare_types_subtype_of(&mut self, source: TypeId, target: TypeId) -> Ternary {
        let relation = self.subtype_relation.clone();
        if self.is_type_related_to(source, target, &relation) {
            return Ternary::TRUE;
        }
        Ternary::FALSE
    }

    /// `(c *Checker) isTypeAssignableTo`.
    pub fn is_type_assignable_to(&mut self, source: TypeId, target: TypeId) -> bool {
        let relation = self.assignable_relation.clone();
        self.is_type_related_to(source, target, &relation)
    }

    /// `(c *Checker) isTypeSubtypeOf`.
    pub(crate) fn is_type_subtype_of(&mut self, source: TypeId, target: TypeId) -> bool {
        let relation = self.subtype_relation.clone();
        self.is_type_related_to(source, target, &relation)
    }

    /// `(c *Checker) isTypeStrictSubtypeOf`.
    pub(crate) fn is_type_strict_subtype_of(&mut self, source: TypeId, target: TypeId) -> bool {
        let relation = self.strict_subtype_relation.clone();
        self.is_type_related_to(source, target, &relation)
    }

    /// `(c *Checker) isTypeComparableTo`.
    pub(crate) fn is_type_comparable_to(&mut self, source: TypeId, target: TypeId) -> bool {
        let relation = self.comparable_relation.clone();
        self.is_type_related_to(source, target, &relation)
    }

    /// `(c *Checker) areTypesComparable`.
    pub(crate) fn are_types_comparable(&mut self, type1: TypeId, type2: TypeId) -> bool {
        self.is_type_comparable_to(type1, type2) || self.is_type_comparable_to(type2, type1)
    }

    /// `(c *Checker) isTypeRelatedTo`.
    pub(crate) fn is_type_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
    ) -> bool {
        let mut source = source;
        let mut target = target;
        if crate::checker_d::is_fresh_literal_type(&self.types, source) {
            source = self
                .types_handle()
                .get_ref(source)
                .as_literal_type()
                .regular_type()
                .expect("fresh literal type has regularType");
        }
        if crate::checker_d::is_fresh_literal_type(&self.types, target) {
            target = self
                .types_handle()
                .get_ref(target)
                .as_literal_type()
                .regular_type()
                .expect("fresh literal type has regularType");
        }
        if source == target {
            return true;
        }
        let (source_flags, target_flags) = {
            let __arena_s = self.types.clone();
            let s = __arena_s.get_ref(source);
            let __arena_t = self.types.clone();
            let t = __arena_t.get_ref(target);
            (s.flags, t.flags)
        };
        if !Rc::ptr_eq(relation, &self.identity_relation) {
            if Rc::ptr_eq(relation, &self.comparable_relation)
                && !target_flags.intersects(TypeFlags::NEVER)
                && self.is_simple_type_related_to(target, source, relation, None)
                || self.is_simple_type_related_to(source, target, relation, None)
            {
                return true;
            }
        } else {
            if !(source_flags | target_flags).intersects(
                TypeFlags::UNION_OR_INTERSECTION
                    | TypeFlags::INDEXED_ACCESS
                    | TypeFlags::CONDITIONAL
                    | TypeFlags::SUBSTITUTION,
            ) {
                // We have excluded types that may simplify to other forms, so
                // types must have identical flags.
                if source_flags != target_flags {
                    return false;
                }
                if source_flags.intersects(TypeFlags::SINGLETON) {
                    return true;
                }
            }
        }
        let (source_flags, target_flags) = {
            let __arena_s = self.types.clone();
            let s = __arena_s.get_ref(source);
            let __arena_t = self.types.clone();
            let t = __arena_t.get_ref(target);
            (s.flags, t.flags)
        };
        if source_flags.intersects(TypeFlags::OBJECT) && target_flags.intersects(TypeFlags::OBJECT)
        {
            let (id, _) = crate::checker_c::get_relation_key(
                self,
                source,
                target,
                IntersectionState::NONE,
                Rc::ptr_eq(relation, &self.identity_relation),
                false,
            );
            let related = relation.borrow().get(id);
            if related != RelationComparisonResult::default() {
                return related.intersects(RelationComparisonResult::SUCCEEDED);
            }
        }
        if source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
            || target_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
        {
            return self.check_type_related_to(source, target, relation, None);
        }
        false
    }

    /// `(c *Checker) isSimpleTypeRelatedTo`.
    pub(crate) fn is_simple_type_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        mut reporter: ErrorReporter<'_>,
    ) -> bool {
        let (s, t) = {
            let __arena_src = self.types.clone();
            let src = __arena_src.get_ref(source);
            let __arena_tgt = self.types.clone();
            let tgt = __arena_tgt.get_ref(target);
            (src.flags, tgt.flags)
        };
        if t.intersects(TypeFlags::ANY)
            || s.intersects(TypeFlags::NEVER)
            || source == self.wildcard_type
        {
            return true;
        }
        if t.intersects(TypeFlags::UNKNOWN)
            && !(Rc::ptr_eq(relation, &self.strict_subtype_relation)
                && s.intersects(TypeFlags::ANY))
        {
            return true;
        }
        if t.intersects(TypeFlags::NEVER) {
            return false;
        }
        if s.intersects(TypeFlags::STRING_LIKE) && t.intersects(TypeFlags::STRING) {
            return true;
        }
        if s.intersects(TypeFlags::STRING_LITERAL)
            && s.intersects(TypeFlags::ENUM_LITERAL)
            && t.intersects(TypeFlags::STRING_LITERAL)
            && !t.intersects(TypeFlags::ENUM_LITERAL)
            && self.types_handle().get_ref(source).as_literal_type().value
                == self.types_handle().get_ref(target).as_literal_type().value
        {
            return true;
        }
        if s.intersects(TypeFlags::NUMBER_LIKE) && t.intersects(TypeFlags::NUMBER) {
            return true;
        }
        if s.intersects(TypeFlags::NUMBER_LITERAL)
            && s.intersects(TypeFlags::ENUM_LITERAL)
            && t.intersects(TypeFlags::NUMBER_LITERAL)
            && !t.intersects(TypeFlags::ENUM_LITERAL)
            && self.types_handle().get_ref(source).as_literal_type().value
                == self.types_handle().get_ref(target).as_literal_type().value
        {
            return true;
        }
        if s.intersects(TypeFlags::BIG_INT_LIKE) && t.intersects(TypeFlags::BIG_INT) {
            return true;
        }
        if s.intersects(TypeFlags::BOOLEAN_LIKE) && t.intersects(TypeFlags::BOOLEAN) {
            return true;
        }
        if s.intersects(TypeFlags::ES_SYMBOL_LIKE) && t.intersects(TypeFlags::ES_SYMBOL) {
            return true;
        }
        if s.intersects(TypeFlags::ENUM) && t.intersects(TypeFlags::ENUM) {
            let (source_symbol, target_symbol) = {
                let __arena_src = self.types.clone();
                let src = __arena_src.get_ref(source);
                let __arena_tgt = self.types.clone();
                let tgt = __arena_tgt.get_ref(target);
                (src.symbol, tgt.symbol)
            };
            if let (Some(source_symbol), Some(target_symbol)) = (source_symbol, target_symbol) {
                let same_name = self.sym(source_symbol).name == self.sym(target_symbol).name;
                if same_name
                    && self.is_enum_type_related_to(
                        source_symbol,
                        target_symbol,
                        reporter.as_deref_mut(),
                    )
                {
                    return true;
                }
            }
        }
        if s.intersects(TypeFlags::ENUM_LITERAL) && t.intersects(TypeFlags::ENUM_LITERAL) {
            let (source_symbol, target_symbol) = {
                let __arena_src = self.types.clone();
                let src = __arena_src.get_ref(source);
                let __arena_tgt = self.types.clone();
                let tgt = __arena_tgt.get_ref(target);
                (src.symbol, tgt.symbol)
            };
            if s.intersects(TypeFlags::UNION)
                && t.intersects(TypeFlags::UNION)
                && self.is_enum_type_related_to(
                    source_symbol.expect("enum literal type has a symbol"),
                    target_symbol.expect("enum literal type has a symbol"),
                    reporter.as_deref_mut(),
                )
            {
                return true;
            }
            if s.intersects(TypeFlags::LITERAL)
                && t.intersects(TypeFlags::LITERAL)
                && self.types_handle().get(source).as_literal_type().value
                    == self.types_handle().get(target).as_literal_type().value
                && self.is_enum_type_related_to(
                    source_symbol.expect("enum literal type has a symbol"),
                    target_symbol.expect("enum literal type has a symbol"),
                    reporter.as_deref_mut(),
                )
            {
                return true;
            }
        }
        // In non-strictNullChecks mode, `undefined` and `null` are assignable
        // to anything except `never`. Since unions and intersections may
        // reduce to `never`, we exclude them here.
        if s.intersects(TypeFlags::UNDEFINED)
            && (!self.strict_null_checks && !t.intersects(TypeFlags::UNION_OR_INTERSECTION)
                || t.intersects(TypeFlags::UNDEFINED | TypeFlags::VOID))
        {
            return true;
        }
        if s.intersects(TypeFlags::NULL)
            && (!self.strict_null_checks && !t.intersects(TypeFlags::UNION_OR_INTERSECTION)
                || t.intersects(TypeFlags::NULL))
        {
            return true;
        }
        if s.intersects(TypeFlags::OBJECT)
            && t.intersects(TypeFlags::NON_PRIMITIVE)
            && !(Rc::ptr_eq(relation, &self.strict_subtype_relation)
                && self.is_empty_anonymous_object_type(source)
                && !self
                    .types_handle()
                    .get(source)
                    .object_flags
                    .intersects(ObjectFlags::FRESH_LITERAL))
        {
            return true;
        }
        if Rc::ptr_eq(relation, &self.assignable_relation)
            || Rc::ptr_eq(relation, &self.comparable_relation)
        {
            if s.intersects(TypeFlags::ANY) {
                return true;
            }
            // Type number is assignable to any computed numeric enum type or
            // any numeric enum literal type, and a numeric literal type is
            // assignable any computed numeric enum type or any numeric enum
            // literal type with a matching value. These rules exist such that
            // enums can be used for bit-flag purposes.
            if s.intersects(TypeFlags::NUMBER)
                && (t.intersects(TypeFlags::ENUM)
                    || t.intersects(TypeFlags::NUMBER_LITERAL)
                        && t.intersects(TypeFlags::ENUM_LITERAL))
            {
                return true;
            }
            if s.intersects(TypeFlags::NUMBER_LITERAL)
                && !s.intersects(TypeFlags::ENUM_LITERAL)
                && (t.intersects(TypeFlags::ENUM)
                    || t.intersects(TypeFlags::NUMBER_LITERAL)
                        && t.intersects(TypeFlags::ENUM_LITERAL)
                        && self.types_handle().get_ref(source).as_literal_type().value
                            == self.types_handle().get_ref(target).as_literal_type().value)
            {
                return true;
            }
            // Anything is assignable to a union containing undefined, null,
            // and {}.
            if self.is_unknown_like_union_type(target) {
                return true;
            }
        }
        false
    }
}

impl Checker {
    /// `(c *Checker) isEnumTypeRelatedTo`. `reporter` is Go's
    /// `errorReporter` (`nil` or `r.reportError`).
    pub(crate) fn is_enum_type_related_to(
        &mut self,
        source: SymbolId,
        target: SymbolId,
        mut reporter: ErrorReporter<'_>,
    ) -> bool {
        // Go `core.IfElse` evaluates both arms eagerly — `getParentOfSymbol`
        // runs (and may resolve the parent) even when the member flag is
        // unset.
        let source_parent = self.get_parent_of_symbol(source);
        let source_symbol = if self
            .sym(source)
            .flags
            .intersects(ast::SymbolFlags::ENUM_MEMBER)
        {
            source_parent
        } else {
            Some(source)
        };
        let target_parent = self.get_parent_of_symbol(target);
        let target_symbol = if self
            .sym(target)
            .flags
            .intersects(ast::SymbolFlags::ENUM_MEMBER)
        {
            target_parent
        } else {
            Some(target)
        };
        if source_symbol.is_none() || target_symbol.is_none() {
            // Go: `sourceSymbol == targetSymbol` is nil==nil → true only when
            // both are nil.
            return source_symbol == target_symbol;
        }
        let source_symbol = source_symbol.unwrap();
        let target_symbol = target_symbol.unwrap();
        if source_symbol == target_symbol {
            return true;
        }
        {
            let (source_name, source_flags) = {
                let s = self.sym(source_symbol);
                (s.name.clone(), s.flags)
            };
            let (target_name, target_flags) = {
                let t = self.sym(target_symbol);
                (t.name.clone(), t.flags)
            };
            if source_name != target_name
                || !source_flags.intersects(ast::SymbolFlags::REGULAR_ENUM)
                || !target_flags.intersects(ast::SymbolFlags::REGULAR_ENUM)
            {
                return false;
            }
        }
        let key = EnumRelationKey {
            source_id: source_symbol,
            target_id: target_symbol,
        };
        // PORT: `c.enumRelation` is keyed by `EnumLiteralKey` in
        // checker_core.rs — a field-type bug; Go keys by `EnumRelationKey`.
        if let Some(entry) = self.enum_relation.get(&key).copied() {
            if entry != RelationComparisonResult::default()
                && !(entry.intersects(RelationComparisonResult::FAILED) && reporter.is_some())
            {
                return entry.intersects(RelationComparisonResult::SUCCEEDED);
            }
        }
        let target_enum_type = self.get_type_of_symbol(target_symbol);
        let source_enum_type = self.get_type_of_symbol(source_symbol);
        for source_property in self.get_properties_of_type(source_enum_type) {
            if !self
                .sym(source_property)
                .flags
                .intersects(ast::SymbolFlags::ENUM_MEMBER)
            {
                continue;
            }
            let source_property_name = self.sym_name_rc(source_property);
            let target_property =
                self.get_property_of_type(target_enum_type, &source_property_name);
            let target_is_enum_member = target_property
                .is_some_and(|p| self.sym(p).flags.intersects(ast::SymbolFlags::ENUM_MEMBER));
            if target_property.is_none() || !target_is_enum_member {
                let __h861_25 = self.symbol_to_string(source_property);
                let __h863_29 = self.get_declared_type_of_symbol(target_symbol);
                let __h862_25 = self.type_to_string_ex(
                    __h863_29,
                    None,
                    crate::types::TypeFormatFlags::USE_FULLY_QUALIFIED_TYPE,
                    None,
                );
                report_via(
                    self,
                    &mut reporter,
                    &tsc_diagnostics::Property_0_is_missing_in_type_1,
                    &[__h861_25, __h862_25],
                );
                self.enum_relation
                    .insert(key, RelationComparisonResult::FAILED);
                return false;
            }
            let target_property = target_property.unwrap();
            let source_value = {
                let decl_nodes = self
                    .sym(source_property)
                    .value_declaration
                    .map(|d| self.program_nodes(d));
                let decl = decl_nodes.as_deref().and_then(|nodes| {
                    ast::get_declaration_of_kind(
                        &self.sym(source_property),
                        ast::Kind::EnumMember,
                        nodes,
                    )
                });
                // PORT(borrowck): drop the arena `Ref` before the `&mut self`
                // `get_enum_member_value` call.
                drop(decl_nodes);
                decl.and_then(|d| self.get_enum_member_value(d).value.clone())
            };
            let target_value = {
                let decl_nodes = self
                    .sym(target_property)
                    .value_declaration
                    .map(|d| self.program_nodes(d));
                let decl = decl_nodes.as_deref().and_then(|nodes| {
                    ast::get_declaration_of_kind(
                        &self.sym(target_property),
                        ast::Kind::EnumMember,
                        nodes,
                    )
                });
                drop(decl_nodes);
                decl.and_then(|d| self.get_enum_member_value(d).value.clone())
            };
            if source_value != target_value {
                // If we have 2 enums with *known* values that differ, they
                // are incompatible.
                if source_value.is_some() && target_value.is_some() {
                    let __h912_29 = self.symbol_to_string(target_symbol);
                    let __h913_29 = self.symbol_to_string(target_property);
                    report_via(
                        self,
                        &mut reporter,
                        &tsc_diagnostics::Each_declaration_of_0_1_differs_in_its_value_where_2_was_expected_but_3_was_given,
                        &[
                            __h912_29,
                            __h913_29,
                            value_to_string(target_value.as_ref()),
                            value_to_string(source_value.as_ref()),
                        ],
                    );
                    self.enum_relation
                        .insert(key, RelationComparisonResult::FAILED);
                    return false;
                }
                // At this point we know that at least one of the values is
                // 'undefined'. This may mean that we have an opaque member
                // from an ambient enum declaration, or that we were not able
                // to calculate it (which is basically an error).
                //
                // Either way, we can assume that it's numeric. If the other
                // is a string, we have a mismatch in types.
                let source_is_string =
                    matches!(source_value, Some(tsc_evaluator::Value::String(_)));
                let target_is_string =
                    matches!(target_value, Some(tsc_evaluator::Value::String(_)));
                if source_is_string || target_is_string {
                    let known_string_value = core::coalesce(source_value, target_value);
                    let __h940_29 = self.symbol_to_string(target_symbol);
                    let __h941_29 = self.symbol_to_string(target_property);
                    report_via(
                        self,
                        &mut reporter,
                        &tsc_diagnostics::One_value_of_0_1_is_the_string_2_and_the_other_is_assumed_to_be_an_unknown_numeric_value,
                        &[
                            __h940_29,
                            __h941_29,
                            value_to_string(known_string_value.as_ref()),
                        ],
                    );
                    self.enum_relation
                        .insert(key, RelationComparisonResult::FAILED);
                    return false;
                }
            }
        }
        self.enum_relation
            .insert(key, RelationComparisonResult::SUCCEEDED);
        true
    }

    /// `(c *Checker) checkTypeAssignableTo`.
    pub(crate) fn check_type_assignable_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        error_node: Option<NodeId>,
        head_message: Option<&'static tsc_diagnostics::Message>,
    ) -> bool {
        let relation = self.assignable_relation.clone();
        self.check_type_related_to_ex(source, target, &relation, error_node, head_message, None)
    }

    /// `(c *Checker) checkTypeAssignableToEx`.
    pub(crate) fn check_type_assignable_to_ex(
        &mut self,
        source: TypeId,
        target: TypeId,
        error_node: Option<NodeId>,
        head_message: Option<&'static tsc_diagnostics::Message>,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let relation = self.assignable_relation.clone();
        self.check_type_related_to_ex(
            source,
            target,
            &relation,
            error_node,
            head_message,
            diagnostic_output,
        )
    }

    /// `(c *Checker) checkTypeComparableTo`.
    pub(crate) fn check_type_comparable_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        error_node: Option<NodeId>,
        head_message: Option<&'static tsc_diagnostics::Message>,
    ) -> bool {
        let relation = self.comparable_relation.clone();
        self.check_type_related_to_ex(source, target, &relation, error_node, head_message, None)
    }

    /// `(c *Checker) checkTypeRelatedTo`.
    pub(crate) fn check_type_related_to(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        error_node: Option<NodeId>,
    ) -> bool {
        self.check_type_related_to_ex(source, target, relation, error_node, None, None)
    }

    /// `(c *Checker) checkTypeRelatedToEx` — check that source is related to
    /// target according to the given relation. When errorNode is non-nil,
    /// errors are reported to the checker's diagnostic collection or through
    /// diagnosticOutput when non-nil. Callers can assume that this function
    /// only reports zero or one error to diagnosticOutput (unlike
    /// checkTypeRelatedToAndOptionallyElaborate).
    pub(crate) fn check_type_related_to_ex(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        mut error_node: Option<NodeId>,
        head_message: Option<&'static tsc_diagnostics::Message>,
        mut diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let mut r = self.get_relater();
        r.relation = Some(relation.clone());
        r.error_node = error_node;
        r.relation_count = ((16_000_000i64 - relation.borrow().size() as i64) / 8) as i32;
        // Comparer closures (e.g. inference's `context_compare`) need to
        // re-enter the live relater; `&mut` can't be captured, so seed a
        // pool of snapshot relaters they fall back to via `compare_via`.
        let saved_relater_seed = self.relater_seed.replace(r.snapshot());
        self.relater_pool.clear();
        let result = r.is_related_to_ex(
            self,
            source,
            target,
            RecursionFlags::BOTH,
            error_node.is_some(),
            head_message,
            IntersectionState::NONE,
        );
        self.relater_seed = saved_relater_seed;
        self.relater_pool.clear();
        if r.overflow {
            // Record this relation as having failed such that we don't
            // attempt the overflowing operation again.
            let (id, _) = crate::checker_c::get_relation_key(
                self,
                source,
                target,
                IntersectionState::NONE,
                Rc::ptr_eq(relation, &self.identity_relation),
                false,
            );
            relation.borrow_mut().set(
                id,
                RelationComparisonResult::FAILED | RelationComparisonResult::COMPLEXITY_OVERFLOW,
            );
            if let Some(tr) = &self.tracer {
                let mut args = TraceArgs::new();
                args.insert("sourceId".to_string(), source.0.into());
                args.insert("targetId".to_string(), target.0.into());
                args.insert("depth".to_string(), (r.source_stack.len() as i64).into());
                args.insert(
                    "targetDepth".to_string(),
                    (r.target_stack.len() as i64).into(),
                );
                tr.instant(
                    tsc_tracing::PHASE_CHECK_TYPES,
                    "checkTypeRelatedTo_DepthLimit",
                    &args,
                );
            }
            if error_node.is_none() {
                error_node = self.current_node;
            }
            let source_str = self.type_to_string(source);
            let target_str = self.type_to_string(target);
            let diagnostic = self.new_diagnostic_for_node(
                error_node,
                &tsc_diagnostics::Excessive_complexity_comparing_types_0_and_1,
                &[source_str, target_str],
            );
            self.report_diagnostic(Some(diagnostic), diagnostic_output.as_deref_mut());
        } else if r.error_chain.is_some() {
            // Check if we should issue an extra diagnostic to produce a
            // quickfix for a slightly incorrect import statement.
            let __arena_source_symbol = self.types.clone();
            let source_symbol = __arena_source_symbol.get_ref(source).symbol;
            if head_message.is_some()
                && error_node.is_some()
                && result == Ternary::FALSE
                && source_symbol.is_some()
                && self.export_type_links.has(&source_symbol.unwrap())
            {
                let (originating_import, links_target) = {
                    let symbol = source_symbol.unwrap();
                    let links = self.export_type_links.get(symbol);
                    (links.originating_import, links.target)
                };
                if originating_import.is_some()
                    && !ast::is_import_call(
                        &self.program_nodes(originating_import.unwrap())
                            [originating_import.unwrap()],
                        &self.program_nodes(originating_import.unwrap()),
                    )
                {
                    let helpful_retry = {
                        let type_of_target = links_target
                            .map(|s| self.get_type_of_symbol(s))
                            .unwrap_or(TypeId::NONE);
                        self.check_type_related_to(type_of_target, target, relation, None)
                    };
                    if helpful_retry {
                        // Likely an incorrect import. Issue a helpful
                        // diagnostic to produce a quickfix to change the
                        // import.
                        let info = self.new_diagnostic_for_node(
                            originating_import,
                            &tsc_diagnostics::Type_originates_at_this_import_A_namespace_style_import_cannot_be_called_or_constructed_and_will_cause_a_failure_at_runtime_Consider_using_a_default_import_or_import_require_here_instead,
                            &[] as &[String],
                        );
                        r.related_info.push(info);
                    }
                }
            }
            let diagnostic = create_diagnostic_chain_from_error_chain(
                self,
                r.error_chain.take(),
                r.error_node,
                &r.related_info,
            );
            self.report_diagnostic(diagnostic, diagnostic_output.as_deref_mut());
        }
        self.put_relater(r);
        result != Ternary::FALSE
    }

    /// `(c *Checker) reportDiagnostic`.
    pub(crate) fn report_diagnostic(
        &mut self,
        diagnostic: Option<ast::diagnostic::DiagnosticRef>,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) {
        if let Some(diagnostic) = diagnostic {
            if let Some(output) = diagnostic_output {
                output.push(diagnostic);
            } else {
                self.add_diagnostic(&diagnostic);
            }
        }
    }

    /// `(c *Checker) checkTypeAssignableToAndOptionallyElaborate`.
    pub(crate) fn check_type_assignable_to_and_optionally_elaborate(
        &mut self,
        source: TypeId,
        target: TypeId,
        error_node: Option<NodeId>,
        expr: Option<NodeId>,
        head_message: Option<&'static tsc_diagnostics::Message>,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let relation = self.assignable_relation.clone();
        self.check_type_related_to_and_optionally_elaborate(
            source,
            target,
            &relation,
            error_node,
            expr,
            head_message,
            diagnostic_output,
        )
    }

    /// `(c *Checker) checkTypeRelatedToAndOptionallyElaborate`.
    pub(crate) fn check_type_related_to_and_optionally_elaborate(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        error_node: Option<NodeId>,
        expr: Option<NodeId>,
        head_message: Option<&'static tsc_diagnostics::Message>,
        mut diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        if self.is_type_related_to(source, target, relation) {
            return true;
        }
        if error_node.is_some()
            && !self.elaborate_error(
                expr,
                source,
                target,
                relation,
                head_message,
                diagnostic_output.as_deref_mut(),
            )
        {
            return self.check_type_related_to_ex(
                source,
                target,
                relation,
                error_node,
                head_message,
                diagnostic_output,
            );
        }
        false
    }

    /// `(c *Checker) elaborateError`.
    pub(crate) fn elaborate_error(
        &mut self,
        node: Option<NodeId>,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        head_message: Option<&'static tsc_diagnostics::Message>,
        mut diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let Some(node) = node else {
            return false;
        };
        if self.is_or_has_generic_conditional(target) {
            return false;
        }
        if self.compiler_options.no_check.is_true() {
            return false;
        }
        if self.elaborate_did_you_mean_to_call_or_construct(
            node,
            source,
            target,
            relation,
            SignatureKind::Construct,
            head_message,
            diagnostic_output.as_deref_mut(),
        ) || self.elaborate_did_you_mean_to_call_or_construct(
            node,
            source,
            target,
            relation,
            SignatureKind::Call,
            head_message,
            diagnostic_output.as_deref_mut(),
        ) {
            return true;
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            ast::Kind::AsExpression => {
                if !ast::is_const_assertion(&nodes[node], &nodes) {
                    return false;
                }
                // fallthrough
                self.elaborate_error(
                    nodes[node].expression(),
                    source,
                    target,
                    relation,
                    head_message,
                    diagnostic_output,
                )
            }
            ast::Kind::JsxExpression | ast::Kind::ParenthesizedExpression => self.elaborate_error(
                nodes[node].expression(),
                source,
                target,
                relation,
                head_message,
                diagnostic_output,
            ),
            ast::Kind::BinaryExpression => {
                let operator_kind = nodes[node]
                    .as_binary_expression()
                    .operator_token
                    .map(|t| nodes[t].kind);
                match operator_kind {
                    Some(ast::Kind::EqualsToken) | Some(ast::Kind::CommaToken) => {
                        let right = nodes[node].as_binary_expression().right;
                        self.elaborate_error(
                            right,
                            source,
                            target,
                            relation,
                            head_message,
                            diagnostic_output,
                        )
                    }
                    _ => false,
                }
            }
            ast::Kind::ObjectLiteralExpression => {
                self.elaborate_object_literal(node, source, target, relation, diagnostic_output)
            }
            ast::Kind::ArrayLiteralExpression => {
                self.elaborate_array_literal(node, source, target, relation, diagnostic_output)
            }
            ast::Kind::ArrowFunction => {
                self.elaborate_arrow_function(node, source, target, relation, diagnostic_output)
            }
            ast::Kind::JsxAttributes => {
                self.elaborate_jsx_components(node, source, target, relation, diagnostic_output)
            }
            _ => false,
        }
    }

    /// `(c *Checker) isOrHasGenericConditional`.
    pub(crate) fn is_or_has_generic_conditional(&mut self, t: TypeId) -> bool {
        let __arena_ty = self.types.clone();
        let ty = __arena_ty.get_ref(t);
        if ty.flags.intersects(TypeFlags::CONDITIONAL) {
            return true;
        }
        if ty.flags.intersects(TypeFlags::INTERSECTION) {
            let types = ty.types().to_vec();
            drop(ty);
            return types.iter().any(|&t| self.is_or_has_generic_conditional(t));
        }
        false
    }

    /// `(c *Checker) elaborateDidYouMeanToCallOrConstruct`.
    pub(crate) fn elaborate_did_you_mean_to_call_or_construct(
        &mut self,
        node: NodeId,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        kind: SignatureKind,
        head_message: Option<&'static tsc_diagnostics::Message>,
        diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let signatures = self.get_signatures_of_type(source, kind);
        let mut found_match = false;
        for s in signatures {
            let return_type = self.get_return_type_of_signature(s);
            if !self
                .types_handle()
                .get(return_type)
                .flags
                .intersects(TypeFlags::ANY | TypeFlags::NEVER)
                && self.check_type_related_to(return_type, target, relation, None)
            {
                found_match = true;
                break;
            }
        }
        if found_match {
            let mut diags = Vec::new();
            if !self.check_type_related_to_ex(
                source,
                target,
                relation,
                Some(node),
                head_message,
                Some(&mut diags),
            ) {
                let diagnostic = diags.remove(0);
                let message = if kind == SignatureKind::Construct {
                    &tsc_diagnostics::Did_you_mean_to_use_new_with_this_expression
                } else {
                    &tsc_diagnostics::Did_you_mean_to_call_this_expression
                };
                let info = self.new_diagnostic_for_node(Some(node), message, &[] as &[String]);
                ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(info));
                self.report_diagnostic(Some(diagnostic), diagnostic_output);
                return true;
            }
        }
        false
    }

    /// `(c *Checker) elaborateObjectLiteral`.
    pub(crate) fn elaborate_object_literal(
        &mut self,
        node: NodeId,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        mut diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        if self
            .types_handle()
            .get_ref(target)
            .flags
            .intersects(TypeFlags::PRIMITIVE | TypeFlags::NEVER)
        {
            return false;
        }
        let mut reported_error = false;
        let __program = self.program.clone().expect("program");
        let properties = __program.nodes((node).file_index())[node]
            .properties()
            .map(|p| p.to_vec())
            .unwrap_or_default();
        for prop in properties {
            let __program = self.program.clone().expect("program");
            let prop_nodes = __program.nodes((prop).file_index());
            if ast::is_spread_assignment(&prop_nodes[prop]) {
                continue;
            }
            let symbol = self.get_symbol_of_declaration(prop);
            let name_type = self.get_literal_type_from_property(
                symbol.expect("prop symbol"),
                TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE,
                false,
            );
            if name_type.is_none()
                || self
                    .types_handle()
                    .get(name_type)
                    .flags
                    .intersects(TypeFlags::NEVER)
            {
                continue;
            }
            match prop_nodes[prop].kind {
                ast::Kind::SetAccessor
                | ast::Kind::GetAccessor
                | ast::Kind::MethodDeclaration
                | ast::Kind::ShorthandPropertyAssignment => {
                    reported_error = self.elaborate_element(
                        source,
                        target,
                        relation,
                        prop_nodes[prop].name(),
                        None,
                        name_type,
                        None,
                        None,
                        diagnostic_output.as_deref_mut(),
                    ) || reported_error;
                }
                ast::Kind::PropertyAssignment => {
                    let message = if ast::is_computed_non_literal_name(
                        &prop_nodes[prop_nodes[prop].name().unwrap()],
                        &prop_nodes,
                    ) {
                        Some(&tsc_diagnostics::Type_of_computed_property_s_value_is_0_which_is_not_assignable_to_type_1)
                    } else {
                        None
                    };
                    reported_error = self.elaborate_element(
                        source,
                        target,
                        relation,
                        prop_nodes[prop].name(),
                        prop_nodes[prop].initializer(),
                        name_type,
                        message,
                        None,
                        diagnostic_output.as_deref_mut(),
                    ) || reported_error;
                }
                _ => {}
            }
        }
        reported_error
    }

    /// `(c *Checker) elaborateArrayLiteral`.
    pub(crate) fn elaborate_array_literal(
        &mut self,
        node: NodeId,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        mut diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        if self
            .types_handle()
            .get_ref(target)
            .flags
            .intersects(TypeFlags::PRIMITIVE | TypeFlags::NEVER)
        {
            return false;
        }
        let mut source = source;
        if !self.is_tuple_like_type(source) {
            self.push_contextual_type(node, Some(target), false);
            source = self.check_array_literal(node, CheckMode::CONTEXTUAL | CheckMode::FORCE_TUPLE);
            self.pop_contextual_type();
            if !self.is_tuple_like_type(source) {
                return false;
            }
        }
        let mut reported_error = false;
        let __program = self.program.clone().expect("program");
        let elements = __program.nodes((node).file_index())[node]
            .elements()
            .map(|e| e.to_vec())
            .unwrap_or_default();
        for (i, element) in elements.iter().enumerate() {
            let element = *element;
            let __program = self.program.clone().expect("program");
            let element_nodes = __program.nodes((element).file_index());
            if ast::is_omitted_expression(&element_nodes[element])
                || self.is_tuple_like_type(target)
                    && self
                        .get_property_of_type(target, &tsc_jsnum::Number(i as f64).to_string())
                        .is_none()
            {
                continue;
            }
            let name_type = self.get_number_literal_type(tsc_jsnum::Number(i as f64));
            let check_node = self.get_effective_check_node(element);
            reported_error = self.elaborate_element(
                source,
                target,
                relation,
                Some(check_node),
                Some(check_node),
                name_type,
                None,
                None,
                diagnostic_output.as_deref_mut(),
            ) || reported_error;
        }
        reported_error
    }
}

/// `createDiagnosticChainFromErrorChain` (relater.go).
pub(crate) fn create_diagnostic_chain_from_error_chain(
    c: &Checker,
    chain: Option<Box<ErrorChain>>,
    error_node: Option<NodeId>,
    related_info: &[ast::diagnostic::DiagnosticRef],
) -> Option<ast::diagnostic::DiagnosticRef> {
    let mut chain = chain;
    loop {
        match &chain {
            Some(ch)
                if ch
                    .message
                    .is_some_and(|m| m.elided_in_compatibility_pyramid()) =>
            {
                chain = chain.unwrap().next;
            }
            _ => break,
        }
    }
    let chain = chain?;
    let next = create_diagnostic_chain_from_error_chain(c, chain.next, error_node, related_info);
    if next.is_none() {
        let diagnostic = c.new_diagnostic_for_node(error_node, chain.message.unwrap(), &chain.args);
        ast::diagnostic::lock_diagnostic(&diagnostic).set_related_info(related_info.to_vec());
        return Some(diagnostic);
    }
    Some(ast::diagnostic::new_diagnostic_chain(
        next.as_ref(),
        chain.message.unwrap(),
        &chain.args,
    ))
}

impl Checker {
    /// `(c *Checker) elaborateElement`. `diagnostic_factory` is Go's
    /// `diagnosticFactory func(prop *ast.Node) *ast.Diagnostic` (nil-able).
    pub(crate) fn elaborate_element(
        &mut self,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        prop: Option<NodeId>,
        next: Option<NodeId>,
        name_type: TypeId,
        error_message: Option<&'static tsc_diagnostics::Message>,
        mut diagnostic_factory: Option<
            &mut (
                     dyn FnMut(&mut Checker, Option<NodeId>) -> ast::diagnostic::DiagnosticRef
                         + 'static
                 ),
        >,
        mut diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        let target_prop_type =
            self.get_best_match_indexed_access_type_or_undefined(source, target, name_type);
        if target_prop_type.is_none()
            || self
                .types_handle()
                .get_ref(target_prop_type.unwrap())
                .flags
                .intersects(TypeFlags::INDEXED_ACCESS)
        {
            // Don't elaborate on indexes on generic variables.
            return false;
        }
        let mut target_prop_type = target_prop_type.unwrap();
        let mut source_prop_type = self.get_indexed_access_type_or_undefined(
            source,
            name_type,
            crate::types::AccessFlags::NONE,
            None,
            None,
        );
        if source_prop_type.is_none()
            || self.check_type_related_to(
                source_prop_type.unwrap(),
                target_prop_type,
                relation,
                None,
            )
        {
            // Don't elaborate on indexes on generic variables or when types
            // match.
            return false;
        }
        if next.is_some()
            && self.elaborate_error(
                next,
                source_prop_type.unwrap(),
                target_prop_type,
                relation,
                None,
                diagnostic_output.as_deref_mut(),
            )
        {
            return true;
        }
        // Issue error on the prop itself, since the prop couldn't elaborate
        // the error.
        let mut diags: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
        // Use the expression type, if available.
        let mut specific_source = source_prop_type.unwrap();
        if next.is_some() {
            specific_source = self.check_expression_for_mutable_location_with_contextual_type(
                next.unwrap(),
                specific_source,
            );
        }
        if let Some(factory) = diagnostic_factory.as_deref_mut() {
            // Use the custom diagnostic factory if provided (e.g., for JSX
            // text children with dynamic error messages).
            diags.push(factory(self, prop));
        } else if self.exact_optional_property_types
            && self
                .is_exact_optional_property_mismatch(Some(specific_source), Some(target_prop_type))
        {
            let source_str = self.type_to_string(specific_source);
            let target_str = self.type_to_string(target_prop_type);
            diags.push(self.new_diagnostic_for_node(
                prop,
                &tsc_diagnostics::Type_0_is_not_assignable_to_type_1_with_exactOptionalPropertyTypes_Colon_true_Consider_adding_undefined_to_the_type_of_the_target,
                &[source_str, target_str],
            ));
        } else {
            let prop_name = self.get_property_name_from_index(name_type, None);
            let target_is_optional = self
                .get_property_of_type(target, &prop_name)
                .or(Some(self.unknown_symbol))
                .is_some_and(|s| self.sym(s).flags.intersects(ast::SymbolFlags::OPTIONAL));
            let source_is_optional = self
                .get_property_of_type(source, &prop_name)
                .or(Some(self.unknown_symbol))
                .is_some_and(|s| self.sym(s).flags.intersects(ast::SymbolFlags::OPTIONAL));
            target_prop_type = self.remove_missing_type(target_prop_type, target_is_optional);
            source_prop_type = Some(self.remove_missing_type(
                source_prop_type.unwrap(),
                target_is_optional && source_is_optional,
            ));
            let result = self.check_type_related_to_ex(
                specific_source,
                target_prop_type,
                relation,
                prop,
                error_message,
                Some(&mut diags),
            );
            if result && specific_source != source_prop_type.unwrap() {
                // If for whatever reason the expression type doesn't yield an
                // error, make sure we still issue an error on the
                // sourcePropType.
                self.check_type_related_to_ex(
                    source_prop_type.unwrap(),
                    target_prop_type,
                    relation,
                    prop,
                    error_message,
                    Some(&mut diags),
                );
            }
        }
        if diags.is_empty() {
            return false;
        }
        let diagnostic = diags[0].clone();
        let mut property_name = String::new();
        let mut target_prop: Option<SymbolId> = None;
        if crate::utilities::is_type_usable_as_property_name(&self.types, name_type) {
            property_name = crate::utilities::get_property_name_from_type(&self.types, name_type);
            target_prop = self.get_property_of_type(target, &property_name);
        }
        let mut issued_elaboration = false;
        if target_prop.is_none() {
            let index_info = self.get_applicable_index_info(target, name_type);
            if let Some(index_info) = index_info {
                if let Some(declaration) = self.index_info_arena.get(index_info).declaration {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((declaration).file_index());
                    let source_file = ast::get_source_file_of_node(Some(declaration), &nodes);
                    let path_key =
                        source_file.map(|f| nodes[f].as_source_file().path_key().clone());
                    let is_default_library = path_key.is_some_and(|key| {
                        self.program
                            .as_ref()
                            .expect("program")
                            .is_source_file_default_library(&key)
                    });
                    if !is_default_library {
                        issued_elaboration = true;
                        let info = self.new_diagnostic_for_node(
                            Some(declaration),
                            &tsc_diagnostics::The_expected_type_comes_from_this_index_signature,
                            &[] as &[String],
                        );
                        ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(info));
                    }
                }
            }
        }
        let (target_prop_declarations, target_symbol_declarations) = {
            let prop_decls = target_prop
                .map(|s| self.sym(s).declarations.clone())
                .unwrap_or_default();
            let __arena_symbol_decls = self.types.clone();
            let symbol_decls = __arena_symbol_decls
                .get_ref(target)
                .symbol
                .map(|s| self.sym(s).declarations.clone())
                .unwrap_or_default();
            (prop_decls, symbol_decls)
        };
        if !issued_elaboration
            && (!target_prop_declarations.is_empty() || !target_symbol_declarations.is_empty())
        {
            let target_node = if !target_prop_declarations.is_empty() {
                target_prop_declarations[0]
            } else {
                target_symbol_declarations[0]
            };
            if property_name.is_empty()
                || self
                    .types_handle()
                    .get(name_type)
                    .flags
                    .intersects(TypeFlags::UNIQUE_ES_SYMBOL)
            {
                property_name = self.type_to_string(name_type);
            }
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((target_node).file_index());
            let source_file = ast::get_source_file_of_node(Some(target_node), &nodes);
            let path_key = source_file.map(|f| nodes[f].as_source_file().path_key().clone());
            let is_default_library = path_key.is_some_and(|key| {
                self.program
                    .as_ref()
                    .expect("program")
                    .is_source_file_default_library(&key)
            });
            if !is_default_library {
                let target_str = self.type_to_string(target);
                let info = self.new_diagnostic_for_node(
                    Some(target_node),
                    &tsc_diagnostics::The_expected_type_comes_from_property_0_which_is_declared_here_on_type_1,
                    &[property_name, target_str],
                );
                ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(info));
            }
        }
        self.report_diagnostic(Some(diagnostic), diagnostic_output);
        true
    }

    /// `(c *Checker) getBestMatchIndexedAccessTypeOrUndefined`.
    pub(crate) fn get_best_match_indexed_access_type_or_undefined(
        &mut self,
        source: TypeId,
        target: TypeId,
        name_type: TypeId,
    ) -> Option<TypeId> {
        let idx = self.get_indexed_access_type_or_undefined(
            target,
            name_type,
            crate::types::AccessFlags::NONE,
            None,
            None,
        );
        if idx.is_some() {
            return idx;
        }
        if self
            .types_handle()
            .get_ref(target)
            .flags
            .intersects(TypeFlags::UNION)
        {
            let best =
                self.get_best_matching_type(source, target, None, Comparer::AssignableSimple);
            if let Some(best) = best {
                return self.get_indexed_access_type_or_undefined(
                    best,
                    name_type,
                    crate::types::AccessFlags::NONE,
                    None,
                    None,
                );
            }
        }
        None
    }

    /// `(c *Checker) checkExpressionForMutableLocationWithContextualType`.
    pub(crate) fn check_expression_for_mutable_location_with_contextual_type(
        &mut self,
        next: NodeId,
        source_prop_type: TypeId,
    ) -> TypeId {
        self.push_contextual_type(next, Some(source_prop_type), false);
        let result = self.check_expression_for_mutable_location(next, CheckMode::CONTEXTUAL);
        self.pop_contextual_type();
        result
    }

    /// `(c *Checker) elaborateArrowFunction`.
    pub(crate) fn elaborate_arrow_function(
        &mut self,
        node: NodeId,
        source: TypeId,
        target: TypeId,
        relation: &SharedRelation,
        mut diagnostic_output: Option<&mut Vec<ast::diagnostic::DiagnosticRef>>,
    ) -> bool {
        // Don't elaborate blocks or functions with annotated parameter types.
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let body = nodes[node].body();
        if body.is_some_and(|b| ast::is_block(&nodes[b])) {
            return false;
        }
        let parameters_have_types = nodes[node]
            .parameters()
            .map(|params| params.to_vec())
            .unwrap_or_default()
            .iter()
            .any(|&p| crate::utilities::has_type(&nodes[p]));
        if parameters_have_types {
            return false;
        }
        let source_sig = self.get_single_call_signature(source);
        if source_sig.is_none() {
            return false;
        }
        let source_sig = source_sig.unwrap();
        let target_signatures = self.get_signatures_of_type(target, SignatureKind::Call);
        if target_signatures.is_empty() {
            return false;
        }
        let return_expression = nodes[node].body();
        let source_return = self.get_return_type_of_signature(source_sig);
        let target_returns = target_signatures
            .iter()
            .map(|&s| self.get_return_type_of_signature(s))
            .collect::<Vec<_>>();
        let target_return = self.get_union_type(&target_returns);
        if self.check_type_related_to(source_return, target_return, relation, None) {
            return false;
        }
        if return_expression.is_some()
            && self.elaborate_error(
                return_expression,
                source_return,
                target_return,
                relation,
                None,
                diagnostic_output.as_deref_mut(),
            )
        {
            return true;
        }
        let mut diags = Vec::new();
        self.check_type_related_to_ex(
            source_return,
            target_return,
            relation,
            return_expression,
            None,
            Some(&mut diags),
        );
        if !diags.is_empty() {
            let diagnostic = diags[0].clone();
            let __arena_target_symbol_declarations = self.types.clone();
            let target_symbol_declarations = __arena_target_symbol_declarations
                .get_ref(target)
                .symbol
                .map(|s| self.sym(s).declarations.clone())
                .unwrap_or_default();
            if !target_symbol_declarations.is_empty() {
                let info = self.new_diagnostic_for_node(
                    Some(target_symbol_declarations[0]),
                    &tsc_diagnostics::The_expected_type_comes_from_the_return_type_of_this_signature,
                    &[] as &[String],
                );
                ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(info));
            }
            let then_prop = self.get_type_of_property_of_type(source_return, "then");
            let promise_related = then_prop.is_none() && {
                let promise = self.create_promise_type(source_return);
                self.check_type_related_to(promise, target_return, relation, None)
            };
            if !ast::functionflags::get_function_flags(Some(&nodes[node]))
                .intersects(ast::functionflags::FunctionFlags::ASYNC)
                && promise_related
            {
                let info = self.new_diagnostic_for_node(
                    Some(node),
                    &tsc_diagnostics::Did_you_mean_to_mark_this_function_as_async,
                    &[] as &[String],
                );
                ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(info));
            }
            self.report_diagnostic(Some(diagnostic), diagnostic_output);
            return true;
        }
        false
    }

    /// `(c *Checker) isWeakType` — a type is 'weak' if it is an object type
    /// with at least one optional property and no required properties,
    /// call/construct signatures or index signatures.
    pub(crate) fn is_weak_type(&mut self, t: TypeId) -> bool {
        let __arena_ty = self.types.clone();
        let ty = __arena_ty.get_ref(t);
        let flags = ty.flags;
        drop(ty);
        if flags.intersects(TypeFlags::OBJECT) {
            let resolved = self.resolve_structured_type_members(t);
            let __arena_resolved_ty = self.types.clone();
            let resolved_ty = __arena_resolved_ty.get_ref(resolved);
            let resolved_members = resolved_ty
                .as_structured_type()
                .expect("resolved structured type");
            let no_members =
                resolved_members.signatures.is_empty() && resolved_members.index_infos.is_empty();
            let properties = resolved_members.properties.clone();
            drop(resolved_ty);
            return no_members
                && !properties.is_empty()
                && properties
                    .iter()
                    .all(|&p| self.sym(p).flags.intersects(ast::SymbolFlags::OPTIONAL));
        }
        if flags.intersects(TypeFlags::SUBSTITUTION) {
            let __arena___guard_base_type = self.types.clone();
            let __guard_base_type = __arena___guard_base_type.get(t).clone();
            let base_type = __guard_base_type
                .as_substitution_type()
                .base_type()
                .expect("substitution baseType");
            return self.is_weak_type(base_type);
        }
        if flags.intersects(TypeFlags::INTERSECTION) {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(t).types().to_vec();
            return types.iter().all(|&t| self.is_weak_type(t));
        }
        false
    }

    /// `(c *Checker) hasCommonProperties`.
    pub(crate) fn has_common_properties(
        &mut self,
        source: TypeId,
        target: TypeId,
        is_comparing_jsx_attributes: bool,
    ) -> bool {
        for prop in self.get_properties_of_type(source) {
            let name = self.sym_name_rc(prop);
            if self.is_known_property(target, &name, is_comparing_jsx_attributes) {
                return true;
            }
        }
        false
    }

    /// `(c *Checker) isKnownProperty` — check if a property with the given
    /// name is known anywhere in the given type.
    pub(crate) fn is_known_property(
        &mut self,
        target_type: TypeId,
        name: &str,
        is_comparing_jsx_attributes: bool,
    ) -> bool {
        let __arena_flags = self.types.clone();
        let flags = __arena_flags.get_ref(target_type).flags;
        if flags.intersects(TypeFlags::OBJECT) {
            // For backwards compatibility a symbol-named property is
            // satisfied by a string index signature. This is incorrect and
            // inconsistent with element access expressions, where it is an
            // error, so eventually we should remove this exception.
            if self
                .get_property_of_object_type(target_type, name)
                .is_some()
                || self
                    .get_applicable_index_info_for_name(target_type, name)
                    .is_some()
                || crate::utilities::is_late_bound_name(name)
                    && self
                        .get_index_info_of_type(target_type, self.string_type)
                        .is_some()
                || is_comparing_jsx_attributes && is_hyphenated_jsx_name(name)
            {
                // For JSXAttributes, if the attribute has a hyphenated name,
                // consider that the attribute to be known.
                return true;
            }
        }
        if flags.intersects(TypeFlags::SUBSTITUTION) {
            let __arena___guard_base_type = self.types.clone();
            let __guard_base_type = __arena___guard_base_type.get(target_type).clone();
            let base_type = __guard_base_type
                .as_substitution_type()
                .base_type()
                .expect("substitution baseType");
            return self.is_known_property(base_type, name, is_comparing_jsx_attributes);
        }
        if flags.intersects(TypeFlags::UNION_OR_INTERSECTION)
            && is_excess_property_check_target(&self.types, target_type)
        {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(target_type).types().to_vec();
            for t in types {
                if self.is_known_property(t, name, is_comparing_jsx_attributes) {
                    return true;
                }
            }
        }
        false
    }
}

/// `isHyphenatedJsxName` (relater.go).
pub(crate) fn is_hyphenated_jsx_name(name: &str) -> bool {
    name.contains('-')
}

/// `isExcessPropertyCheckTarget` (relater.go).
pub(crate) fn is_excess_property_check_target(types: &crate::types::TypeArena, t: TypeId) -> bool {
    let ty = types.get_ref(t);
    let flags = ty.flags;
    let object_flags = ty.object_flags;
    if flags.intersects(TypeFlags::OBJECT)
        && !object_flags.intersects(ObjectFlags::OBJECT_LITERAL_PATTERN_WITH_COMPUTED_PROPERTIES)
    {
        return true;
    }
    if flags.intersects(TypeFlags::NON_PRIMITIVE) {
        return true;
    }
    if flags.intersects(TypeFlags::SUBSTITUTION) {
        let base_type = ty
            .as_substitution_type()
            .base_type()
            .expect("substitution baseType");
        drop(ty);
        if is_excess_property_check_target(types, base_type) {
            return true;
        }
    } else {
        drop(ty);
    }
    if flags.intersects(TypeFlags::UNION) {
        let constituents = types.get_ref(t).types().to_vec();
        if constituents
            .iter()
            .any(|&t| is_excess_property_check_target(types, t))
        {
            return true;
        }
    }
    if flags.intersects(TypeFlags::INTERSECTION) {
        let constituents = types.get_ref(t).types().to_vec();
        if constituents
            .iter()
            .all(|&t| is_excess_property_check_target(types, t))
        {
            return true;
        }
    }
    false
}

// Deeply-nested / recursion identity helpers

/// `getRecursionIdentityTarget` (relater.go) — PORT(mirrored) of the private
/// checker_core.rs copy: recursively (a) obtain the target object type of an
/// indexed access (i.e. the T in T[K]), and (b) unwrap nested homomorphic
/// mapped types and return the deepest target type that has a symbol.
fn get_recursion_identity_target(c: &mut Checker, t: TypeId) -> TypeId {
    let __arena_ty = c.types.clone();
    let ty = __arena_ty.get_ref(t);
    if ty.flags.intersects(TypeFlags::INDEXED_ACCESS) {
        let object_type = ty.as_indexed_access_type().object_type;
        drop(ty);
        return get_recursion_identity_target(c, object_type.unwrap());
    }
    // `declaration.is_some()` gates the mapped branch: `trace_record_type`
    // fires inside `new_object_type` before `instantiate_anonymous_type`
    // copies `declaration`/`target`/`mapper` onto the fresh type, so a
    // mid-construction INSTANTIATED_MAPPED type reaches us with `None`.
    // Go never sees that window — its `RecursionIdentity` read is lazy
    // (dump-time). Fall through to the type-identity default instead of
    // calling `get_modifiers_type_from_mapped_type`, which caches
    // `modifiers_type` on the type and must never run half-constructed.
    if ty.object_flags.contains(ObjectFlags::INSTANTIATED_MAPPED)
        && ty.as_mapped_type().declaration.is_some()
    {
        drop(ty);
        let target = c.get_modifiers_type_from_mapped_type(t);
        if let Some(target) = target {
            // Stage `target`'s symbol/types before the nested `types.get` —
            // no read guard may be held across another arena read.
            let (has_symbol, constituents_have_symbol) = {
                let __arena_tt = c.types.clone();
                let tt = __arena_tt.get_ref(target);
                let has_symbol = tt.symbol.is_some();
                let constituents_have_symbol = tt.flags.intersects(TypeFlags::INTERSECTION) && {
                    let types = tt.types().to_vec();
                    drop(tt);
                    types
                        .iter()
                        .any(|&s| c.types_handle().get_ref(s).symbol.is_some())
                };
                (has_symbol, constituents_have_symbol)
            };
            if has_symbol || constituents_have_symbol {
                return get_recursion_identity_target(c, target);
            }
        }
    }
    t
}

/// `getRecursionIdentityFromTarget` (relater.go) — PORT(mirrored) of the
/// private checker_core.rs copy. The recursion identity of a type is an
/// object identity that is shared among multiple instantiations of the
/// type.
fn get_recursion_identity_from_target(c: &mut Checker, t: TypeId) -> RecursionId {
    // Stage the fields Go reads off `t` before nested arena lookups.
    let (flags, object_flags, symbol, ref_node, cond_root_node) = {
        let __arena_ty = c.types.clone();
        let ty = __arena_ty.get_ref(t);
        let ref_node = if ty.object_flags.intersects(ObjectFlags::REFERENCE) {
            ty.data.as_type_reference().and_then(|r| r.node)
        } else {
            None
        };
        let cond_root_node = if ty.flags.intersects(TypeFlags::CONDITIONAL) {
            ty.as_conditional_type()
                .root
                .as_ref()
                .and_then(|root| root.node)
        } else {
            None
        };
        (
            ty.flags,
            ty.object_flags,
            ty.symbol,
            ref_node,
            cond_root_node,
        )
    };
    // Object and array literals are known not to contain recursive
    // references and don't need a recursion identity.
    if flags.intersects(TypeFlags::OBJECT)
        && !is_object_or_array_literal_type(&c.types_handle().get(t))
    {
        if let Some(node) = ref_node {
            // Deferred type references are tracked through their associated
            // AST node. This gives us finer granularity than using their
            // associated target because each manifest type reference has a
            // unique AST node.
            return as_recursion_id_node(node);
        }
        if let Some(symbol) = symbol {
            // We track object types that have a symbol by that symbol
            // (representing the origin of the type), but exclude the static
            // sides of classes (since they share their symbols with the
            // instance sides) and type references that originate in
            // resolution of AST type nodes (since such type nodes cannot be
            // the source of generative recursion without first being
            // instantiated).
            let sym_is_class = c.symbol_arena.borrow()[symbol.index()]
                .flags
                .intersects(ast::SymbolFlags::CLASS);
            if !(object_flags.intersects(ObjectFlags::ANONYMOUS) && sym_is_class)
                && !object_flags.intersects(ObjectFlags::FROM_TYPE_NODE)
            {
                return as_recursion_id_symbol(symbol);
            }
        }
        if is_tuple_type(&c.types, t) && !object_flags.intersects(ObjectFlags::FROM_TYPE_NODE) {
            if let Some(target) = c.types_handle().get(t).target() {
                return as_recursion_id_type(target);
            }
        }
    }
    if flags.intersects(TypeFlags::TYPE_PARAMETER) && symbol.is_some() {
        // We use the symbol of the type parameter such that all "fresh"
        // instantiations of that type parameter have the same recursion
        // identity.
        return as_recursion_id_symbol(symbol.unwrap());
    }
    if flags.intersects(TypeFlags::CONDITIONAL) {
        // The root object represents the origin of the conditional type.
        if let Some(node) = cond_root_node {
            return as_recursion_id_node(node);
        }
    }
    as_recursion_id_type(t)
}

/// `getRecursionIdentity` (relater.go). PORT(mirrored): checker_core.rs
/// carries the same free function for tracer.rs.
pub(crate) fn get_recursion_identity(c: &mut Checker, t: TypeId) -> RecursionId {
    let target = get_recursion_identity_target(c, t);
    get_recursion_identity_from_target(c, target)
}

/// `hasMatchingRecursionIdentity` (relater.go).
pub(crate) fn has_matching_recursion_identity(
    c: &mut Checker,
    t: TypeId,
    identity: &RecursionId,
) -> bool {
    let target = get_recursion_identity_target(c, t);
    if c.types_handle()
        .get_ref(target)
        .flags
        .intersects(TypeFlags::INTERSECTION)
    {
        let __arena_types = c.types.clone();
        let types = __arena_types.get_ref(target).types().to_vec();
        for t in types {
            if has_matching_recursion_identity(c, t, identity) {
                return true;
            }
        }
        return false;
    }
    get_recursion_identity_from_target(c, target) == *identity
}

impl Checker {
    /// `(c *Checker) isDeeplyNestedType` — return true if the given type is
    /// deeply nested; we consider this to be the case when the given stack
    /// contains maxDepth or more occurrences of types with the same
    /// recursion identity as the given type.
    pub(crate) fn is_deeply_nested_type(
        &mut self,
        t: TypeId,
        stack: &[TypeId],
        max_depth: usize,
    ) -> bool {
        if stack.len() >= max_depth {
            let target = get_recursion_identity_target(self, t);
            if self
                .types_handle()
                .get_ref(target)
                .flags
                .intersects(TypeFlags::INTERSECTION)
            {
                let __arena_types = self.types.clone();
                let types = __arena_types.get_ref(target).types().to_vec();
                for t in types {
                    if self.is_deeply_nested_type(t, stack, max_depth) {
                        return true;
                    }
                }
            } else {
                let identity = get_recursion_identity_from_target(self, target);
                let mut count = 0usize;
                let mut last_type_id = TypeId(0);
                for &t in stack {
                    if has_matching_recursion_identity(self, t, &identity) {
                        // We only count occurrences with a higher type id
                        // than the previous occurrence, since higher type
                        // ids are an indicator of newer instantiations
                        // caused by recursion.
                        if t.0 >= last_type_id.0 {
                            count += 1;
                            if count >= max_depth {
                                return true;
                            }
                        }
                        last_type_id = t;
                    }
                }
            }
        }
        false
    }

    /// `(c *Checker) getBestMatchingType`.
    pub(crate) fn get_best_matching_type(
        &mut self,
        source: TypeId,
        target: TypeId,
        mut r: ErrorReporter<'_>,
        is_related_to: Comparer,
    ) -> Option<TypeId> {
        if let Some(t) =
            self.find_matching_discriminant_type(source, target, r.as_deref_mut(), is_related_to)
        {
            return Some(t);
        }
        if let Some(t) = self.find_matching_type_reference_or_type_alias_reference(source, target) {
            return Some(t);
        }
        if let Some(t) = self.find_best_type_for_object_literal(source, target) {
            return Some(t);
        }
        if let Some(t) = self.find_best_type_for_invokable(source, target, SignatureKind::Call) {
            return Some(t);
        }
        if let Some(t) = self.find_best_type_for_invokable(source, target, SignatureKind::Construct)
        {
            return Some(t);
        }
        self.find_most_overlappy_type(source, target)
    }

    /// `(c *Checker) findMatchingTypeReferenceOrTypeAliasReference`.
    pub(crate) fn find_matching_type_reference_or_type_alias_reference(
        &mut self,
        source: TypeId,
        union_target: TypeId,
    ) -> Option<TypeId> {
        let __arena_source_object_flags = self.types.clone();
        let source_object_flags = __arena_source_object_flags.get_ref(source).object_flags;
        if source_object_flags.intersects(ObjectFlags::REFERENCE | ObjectFlags::ANONYMOUS)
            && self
                .types_handle()
                .get_ref(union_target)
                .flags
                .intersects(TypeFlags::UNION)
        {
            let (source_target, source_alias_symbol) = {
                let __arena_s = self.types.clone();
                let s = __arena_s.get_ref(source);
                (s.target(), s.alias.as_ref().and_then(|a| a.symbol))
            };
            let __arena_targets = self.types.clone();
            let targets = __arena_targets.get_ref(union_target).types().to_vec();
            for target in targets {
                let (target_flags, target_object_flags) = {
                    let __arena_t = self.types.clone();
                    let t = __arena_t.get_ref(target);
                    (t.flags, t.object_flags)
                };
                if target_flags.intersects(TypeFlags::OBJECT) {
                    let overlap_obj_flags = source_object_flags & target_object_flags;
                    if overlap_obj_flags.intersects(ObjectFlags::REFERENCE)
                        && source_target.is_some()
                        && source_target
                            == self.types_handle().get_ref(target).target()
                    {
                        return Some(target);
                    }
                    if overlap_obj_flags.intersects(ObjectFlags::ANONYMOUS)
                        && source_alias_symbol.is_some()
                        && source_alias_symbol
                            == self
                                .types_handle()
                                .get(target)
                                .alias
                                .as_ref()
                                .and_then(|a| a.symbol)
                    {
                        return Some(target);
                    }
                }
            }
        }
        None
    }

    /// `(c *Checker) findBestTypeForInvokable`.
    pub(crate) fn find_best_type_for_invokable(
        &mut self,
        source: TypeId,
        union_target: TypeId,
        kind: SignatureKind,
    ) -> Option<TypeId> {
        if !self.get_signatures_of_type(source, kind).is_empty() {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(union_target).types().to_vec();
            return core::find(&types, |&t| {
                !self.get_signatures_of_type(t, kind).is_empty()
            });
        }
        None
    }

    /// `(c *Checker) findMostOverlappyType`.
    pub(crate) fn find_most_overlappy_type(
        &mut self,
        source: TypeId,
        union_target: TypeId,
    ) -> Option<TypeId> {
        let mut best_match: Option<TypeId> = None;
        if !self
            .types_handle()
            .get_ref(source)
            .flags
            .intersects(TypeFlags::PRIMITIVE | TypeFlags::INSTANTIABLE_PRIMITIVE)
        {
            let mut matching_count: i32 = 0;
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(union_target).types().to_vec();
            for target in types {
                if !self
                    .types_handle()
                    .get(target)
                    .flags
                    .intersects(TypeFlags::PRIMITIVE | TypeFlags::INSTANTIABLE_PRIMITIVE)
                {
                    let source_index = self.get_index_type(source);
                    let target_index = self.get_index_type(target);
                    let overlap = self.get_intersection_type(&[source_index, target_index]);
                    if self
                        .types_handle()
                        .get(overlap)
                        .flags
                        .intersects(TypeFlags::INDEX)
                    {
                        // Perfect overlap of keys.
                        return Some(target);
                    } else if crate::checker_d::is_unit_type(&self.types, overlap)
                        || self
                            .types_handle()
                            .get(overlap)
                            .flags
                            .intersects(TypeFlags::UNION)
                    {
                        // We only want to account for literal types
                        // otherwise. If we have a union of index types, it
                        // seems likely that we needed to elaborate between
                        // two generic mapped types anyway.
                        let mut length = 1;
                        if self
                            .types_handle()
                            .get(overlap)
                            .flags
                            .intersects(TypeFlags::UNION)
                        {
                            let __arena_overlap_types = self.types.clone();
                            let overlap_types = __arena_overlap_types.get_ref(overlap).types().to_vec();
                            length = core::count_where(&overlap_types, |&t| {
                                crate::checker_d::is_unit_type(&self.types, t)
                            });
                        }
                        if length >= matching_count {
                            best_match = Some(target);
                            matching_count = length;
                        }
                    }
                }
            }
        }
        best_match
    }

    /// `(c *Checker) findBestTypeForObjectLiteral`.
    pub(crate) fn find_best_type_for_object_literal(
        &mut self,
        source: TypeId,
        union_target: TypeId,
    ) -> Option<TypeId> {
        if self
            .types_handle()
            .get(source)
            .object_flags
            .intersects(ObjectFlags::OBJECT_LITERAL)
            && crate::checker_d::some_type(self, union_target, |c, t| c.is_array_like_type(t))
        {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(union_target).types().to_vec();
            return core::find(&types, |&t| !self.is_array_like_type(t));
        }
        None
    }

    /// `(c *Checker) shouldReportUnmatchedPropertyError`.
    pub(crate) fn should_report_unmatched_property_error(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> bool {
        let type_call_signatures =
            self.get_signatures_of_structured_type(source, SignatureKind::Call);
        let type_construct_signatures =
            self.get_signatures_of_structured_type(source, SignatureKind::Construct);
        let type_properties = self.get_properties_of_object_type(source);
        if (!type_call_signatures.is_empty() || !type_construct_signatures.is_empty())
            && type_properties.is_empty()
        {
            if !self
                .get_signatures_of_type(target, SignatureKind::Call)
                .is_empty()
                && !type_call_signatures.is_empty()
                || !self
                    .get_signatures_of_type(target, SignatureKind::Construct)
                    .is_empty()
                    && !type_construct_signatures.is_empty()
            {
                // Target has similar signature kinds to source, still focus
                // on the unmatched property.
                return true;
            }
            return false;
        }
        true
    }

    /// `(c *Checker) getUnmatchedProperty`.
    pub(crate) fn get_unmatched_property(
        &mut self,
        source: TypeId,
        target: TypeId,
        require_optional_properties: bool,
        match_discriminant_properties: bool,
    ) -> Option<SymbolId> {
        self.get_unmatched_properties_worker(
            source,
            target,
            require_optional_properties,
            match_discriminant_properties,
            None,
        )
    }

    /// `(c *Checker) getUnmatchedProperties`.
    pub(crate) fn get_unmatched_properties(
        &mut self,
        source: TypeId,
        target: TypeId,
        require_optional_properties: bool,
        match_discriminant_properties: bool,
    ) -> Vec<SymbolId> {
        let mut props = Vec::new();
        self.get_unmatched_properties_worker(
            source,
            target,
            require_optional_properties,
            match_discriminant_properties,
            Some(&mut props),
        );
        props
    }

    /// `(c *Checker) getUnmatchedPropertiesWorker`.
    pub(crate) fn get_unmatched_properties_worker(
        &mut self,
        source: TypeId,
        target: TypeId,
        require_optional_properties: bool,
        match_discriminant_properties: bool,
        mut props_out: Option<&mut Vec<SymbolId>>,
    ) -> Option<SymbolId> {
        let properties = self.get_properties_of_type(target);
        for target_prop in properties {
            // TODO: remove this when we support static private identifier
            // fields and find other solutions to get
            // privateNamesAndStaticFields test to pass.
            if crate::utilities::is_static_private_identifier_property(self, target_prop) {
                continue;
            }
            let (target_flags, target_check_flags) = {
                let p = self.sym(target_prop);
                (p.flags, p.check_flags)
            };
            let target_name = self.sym_name_rc(target_prop);
            if require_optional_properties
                || !target_flags.intersects(ast::SymbolFlags::OPTIONAL)
                    && !target_check_flags.intersects(ast::checkflags::CheckFlags::PARTIAL)
            {
                let source_prop = self.get_property_of_type(source, &target_name);
                if source_prop.is_none() {
                    if props_out.is_none() {
                        return Some(target_prop);
                    }
                    props_out.as_deref_mut().unwrap().push(target_prop);
                } else if match_discriminant_properties {
                    let target_type = self.get_type_of_symbol(target_prop);
                    if self
                        .types_handle()
                        .get(target_type)
                        .flags
                        .intersects(TypeFlags::UNIT)
                    {
                        let source_type = self.get_type_of_symbol(source_prop.unwrap());
                        let __arena_source_is_matching = self.types.clone();
                        let source_is_matching = __arena_source_is_matching
                            .get(source_type)
                            .flags
                            .intersects(TypeFlags::ANY)
                            || self.get_regular_type_of_literal_type(source_type)
                                == self.get_regular_type_of_literal_type(target_type);
                        if !source_is_matching {
                            if props_out.is_none() {
                                return Some(target_prop);
                            }
                            props_out.as_deref_mut().unwrap().push(target_prop);
                        }
                    }
                }
            }
        }
        None
    }
}

/// `excludeProperties` (relater.go). `excludedProperties` is a read-only
/// `collections.Set[string]` → `&Set<String>`; `slices.Clip` copies the
/// prefix (Go shares the backing array — the port clones since callers
/// don't mutate the result through the alias).
pub(crate) fn exclude_properties(
    c: &Checker,
    properties: &[SymbolId],
    excluded_properties: &Set<String>,
) -> Vec<SymbolId> {
    if excluded_properties.has(&String::new()) && false {
        // unreachable — see below; `excluded_properties` may be a nil-map
        // `Set` in Go, which reads as empty.
    }
    if excluded_properties.len() == 0 || properties.is_empty() {
        return properties.to_vec();
    }
    let mut reduced: Option<Vec<SymbolId>> = None;
    for (i, &prop) in properties.iter().enumerate() {
        let name = c.sym_name_rc(prop);
        if !excluded_properties.has(&*name) {
            if let Some(reduced) = reduced.as_mut() {
                reduced.push(prop);
            }
        } else if reduced.is_none() {
            reduced = Some(properties[..i].to_vec());
        }
    }
    reduced.unwrap_or_else(|| properties.to_vec())
}

// TypeDiscriminator

/// `type Discriminator interface` (relater.go) — the `len`/`name`/`matches`
//   triple consumed by `discriminate_type_by_discriminable_items`. Go's two
//   implementations are `TypeDiscriminator` (here) and
//   `ObjectLiteralDiscriminator` (checker.go). Methods take `&mut Checker`
//   explicitly — the Go structs capture a `c *Checker` the port cannot.
pub(crate) trait Discriminator {
    /// `len()` — number of discriminant properties.
    fn len(&self) -> usize;
    /// `name(index)` — property name of index-th discriminator.
    fn name(&mut self, c: &mut Checker, index: usize) -> String;
    /// `matches(index, t)` — true if index-th discriminator matches the
    /// given type. `r` is the relater the `isRelatedTo` comparer runs
    /// against (Go's `d.isRelatedTo` method values).
    fn matches(
        &mut self,
        c: &mut Checker,
        r: &mut ErrorReporter<'_>,
        index: usize,
        t: TypeId,
    ) -> bool;
}

/// `type TypeDiscriminator struct` (relater.go). The `c *Checker` field is
//   threaded through the trait methods instead.
pub(crate) struct TypeDiscriminator {
    /// `props`.
    pub props: Vec<SymbolId>,
    /// `isRelatedTo` — the `func(*Type, *Type) Ternary` callback.
    pub is_related_to: Comparer,
}

impl Discriminator for TypeDiscriminator {
    /// `(d *TypeDiscriminator) len`.
    fn len(&self) -> usize {
        self.props.len()
    }

    /// `(d *TypeDiscriminator) name`.
    fn name(&mut self, c: &mut Checker, index: usize) -> String {
        c.sym(self.props[index]).name.clone()
    }

    /// `(d *TypeDiscriminator) matches`.
    fn matches(
        &mut self,
        c: &mut Checker,
        r: &mut ErrorReporter<'_>,
        index: usize,
        t: TypeId,
    ) -> bool {
        let prop_type = c.get_type_of_symbol(self.props[index]);
        let distributed: Vec<TypeId> = c.types_handle().get_ref(prop_type).distributed(prop_type);
        for s in distributed {
            if compare_via(c, r, self.is_related_to, s, t, false) != Ternary::FALSE {
                return true;
            }
        }
        false
    }
}

impl Checker {
    /// `(c *Checker) findMatchingDiscriminantType` — keep this up-to-date
    /// with the same logic within `getApparentTypeOfContextualType`, since
    /// they should behave similarly.
    pub(crate) fn find_matching_discriminant_type(
        &mut self,
        source: TypeId,
        target: TypeId,
        mut r: ErrorReporter<'_>,
        is_related_to: Comparer,
    ) -> Option<TypeId> {
        let (source_flags, target_is_union) = {
            let __arena_s = self.types.clone();
            let s = __arena_s.get_ref(source);
            (
                s.flags,
                self.types_handle()
                    .get(target)
                    .flags
                    .intersects(TypeFlags::UNION),
            )
        };
        if target_is_union && source_flags.intersects(TypeFlags::INTERSECTION | TypeFlags::OBJECT) {
            if let Some(matched) = self.get_matching_union_constituent_for_type(target, source) {
                return Some(matched);
            }
            let source_properties = self.get_properties_of_type(source);
            let discriminant_properties =
                self.find_discriminant_properties(&source_properties, target);
            if !discriminant_properties.is_empty() {
                let mut discriminator = TypeDiscriminator {
                    props: discriminant_properties,
                    is_related_to,
                };
                let discriminated = self.discriminate_type_by_discriminable_items(
                    target,
                    r.as_deref_mut(),
                    &mut discriminator,
                );
                if discriminated != target {
                    return Some(discriminated);
                }
            }
        }
        None
    }

    /// `(c *Checker) findDiscriminantProperties`.
    pub(crate) fn find_discriminant_properties(
        &mut self,
        source_properties: &[SymbolId],
        target: TypeId,
    ) -> Vec<SymbolId> {
        let mut result = Vec::new();
        for &source_property in source_properties {
            let name = self.sym_name_rc(source_property);
            if self.is_discriminant_property(target, &name) {
                result.push(source_property);
            }
        }
        result
    }

    /// `(c *Checker) isDiscriminantProperty`.
    pub(crate) fn is_discriminant_property(&mut self, t: TypeId, name: &str) -> bool {
        if self
            .types_handle()
            .get_ref(t)
            .flags
            .intersects(TypeFlags::UNION)
        {
            if let Some(prop) = self.get_union_or_intersection_property(t, name, false) {
                if self
                    .sym(prop)
                    .check_flags
                    .intersects(ast::checkflags::CheckFlags::SYNTHETIC_PROPERTY)
                {
                    if !self
                        .sym(prop)
                        .check_flags
                        .intersects(ast::checkflags::CheckFlags::IS_DISCRIMINANT_COMPUTED)
                    {
                        self.sym_mut(prop)
                            .check_flags
                            .insert(ast::checkflags::CheckFlags::IS_DISCRIMINANT_COMPUTED);
                        let __h2695_54 = self.get_type_of_symbol(prop);

                        if self
                            .sym(prop)
                            .check_flags
                            .contains(ast::checkflags::CheckFlags::NON_UNIFORM_AND_LITERAL)
                            && !self.is_generic_type(__h2695_54)
                        {
                            self.sym_mut(prop)
                                .check_flags
                                .insert(ast::checkflags::CheckFlags::IS_DISCRIMINANT);
                        }
                    }
                    return self
                        .sym(prop)
                        .check_flags
                        .intersects(ast::checkflags::CheckFlags::IS_DISCRIMINANT);
                }
            }
        }
        false
    }

    /// `(c *Checker) getMatchingUnionConstituentForType`.
    pub(crate) fn get_matching_union_constituent_for_type(
        &mut self,
        union_type: TypeId,
        t: TypeId,
    ) -> Option<TypeId> {
        let key_property_name = self.get_key_property_name(union_type);
        if key_property_name.is_empty() {
            return None;
        }
        let prop_type = self.get_type_of_property_of_type(t, &key_property_name)?;
        self.get_constituent_type_for_key_type(union_type, prop_type)
    }

    /// `(c *Checker) getKeyPropertyName` — return the name of a discriminant
    /// property for which it was possible and feasible to construct a map of
    /// constituent types keyed by the literal types of the property by that
    /// name in each constituent type. Return an empty string if no such
    /// discriminant property exists.
    pub(crate) fn get_key_property_name(&mut self, t: TypeId) -> String {
        if self
            .types_handle()
            .get_ref(t)
            .as_union_type()
            .key_property_name
            .is_empty()
        {
            let (name, map) = self.compute_key_property_name_and_map(t);
            let __arena_g = self.types.clone();
            let mut g = __arena_g.get_mut(t);
            if let crate::types::TypeData::Union(u) = &mut g.data {
                u.key_property_name = name;
                u.constituent_map = map;
            }
            drop(g);
        }
        let __arena___guard_name = self.types.clone();
        let __guard_name = __arena___guard_name.get(t).clone();
        let name = __guard_name.as_union_type().key_property_name.clone();
        if name == ast::symbol::INTERNAL_SYMBOL_NAME_MISSING {
            return String::new();
        }
        name
    }

    /// `(c *Checker) getConstituentTypeForKeyType` — given a union type for
    /// which `getKeyPropertyName` returned a non-empty string, return the
    /// constituent that corresponds to the given key type for that property
    /// name.
    pub(crate) fn get_constituent_type_for_key_type(
        &mut self,
        t: TypeId,
        key_type: TypeId,
    ) -> Option<TypeId> {
        let regular = self.get_regular_type_of_literal_type(key_type);
        let __arena___guard_result = self.types.clone();
        let __guard_result = __arena___guard_result.get(t).clone();
        let result = __guard_result
            .as_union_type()
            .constituent_map
            .get(&regular)
            .copied();
        if result != Some(self.unknown_type) {
            return result;
        }
        None
    }

    /// `(c *Checker) computeKeyPropertyNameAndMap`.
    fn compute_key_property_name_and_map(
        &mut self,
        t: TypeId,
    ) -> (String, FxHashMap<TypeId, TypeId>) {
        let (types, is_primitive_union) = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get_ref(t);
            (
                ty.types().to_vec(),
                ty.object_flags.intersects(ObjectFlags::PRIMITIVE_UNION),
            )
        };
        if types.len() < 10
            || is_primitive_union
            || core::count_where(&types, |&t| {
                is_object_or_instantiable_non_primitive(&self.types, t)
            }) < 10
        {
            return (
                ast::symbol::INTERNAL_SYMBOL_NAME_MISSING.to_string(),
                FxHashMap::default(),
            );
        }
        let key_property_name = self.get_key_property_candidate_name(&types);
        if key_property_name.is_empty() {
            return (
                ast::symbol::INTERNAL_SYMBOL_NAME_MISSING.to_string(),
                FxHashMap::default(),
            );
        }
        let Some(map_by_key_property) = self.map_types_by_key_property(&types, &key_property_name)
        else {
            return (
                ast::symbol::INTERNAL_SYMBOL_NAME_MISSING.to_string(),
                FxHashMap::default(),
            );
        };
        (key_property_name, map_by_key_property)
    }

    /// `(c *Checker) getKeyPropertyCandidateName`.
    fn get_key_property_candidate_name(&mut self, types: &[TypeId]) -> String {
        for &t in types {
            if self
                .types_handle()
                .get_ref(t)
                .flags
                .intersects(TypeFlags::OBJECT | TypeFlags::INSTANTIABLE_NON_PRIMITIVE)
            {
                for p in self.get_properties_of_type(t) {
                    let ty = self.get_type_of_symbol(p);
                    if crate::checker_d::is_unit_type(&self.types, ty) {
                        return self.sym(p).name.clone();
                    }
                }
            }
        }
        String::new()
    }

    /// `(c *Checker) mapTypesByKeyProperty` — given a set of constituent
    /// types and a property name, create and return a map keyed by the
    /// literal types of the property by that name in each constituent type.
    /// No map is returned if some key property has a non-literal type or if
    /// less than 10 or less than 50% of the constituents have a unique key.
    /// Entries with duplicate keys have `unknown_type` as the value.
    fn map_types_by_key_property(
        &mut self,
        types: &[TypeId],
        key_property_name: &str,
    ) -> Option<FxHashMap<TypeId, TypeId>> {
        let mut types_by_key: FxHashMap<TypeId, TypeId> = FxHashMap::default();
        let mut count = 0usize;
        for &t in types {
            if self.types_handle().get_ref(t).flags.intersects(
                TypeFlags::OBJECT | TypeFlags::INTERSECTION | TypeFlags::INSTANTIABLE_NON_PRIMITIVE,
            ) {
                let discriminant = self.get_type_of_property_of_type(t, key_property_name);
                if discriminant.is_none()
                    || !crate::checker_d::is_literal_type(&self.types, discriminant.unwrap())
                {
                    return None;
                }
                let discriminant = discriminant.unwrap();
                let mut duplicate = false;
                let disc_types: Vec<TypeId> = self
                    .types_handle()
                    .get(discriminant)
                    .distributed(discriminant);
                for d in disc_types {
                    let key = self.get_regular_type_of_literal_type(d);
                    match types_by_key.get(&key) {
                        None => {
                            types_by_key.insert(key, t);
                        }
                        Some(&existing) if existing != self.unknown_type => {
                            types_by_key.insert(key, self.unknown_type);
                            duplicate = true;
                        }
                        _ => {}
                    }
                }
                if !duplicate {
                    count += 1;
                }
            }
        }
        if count >= 10 && count * 2 >= types.len() {
            return Some(types_by_key);
        }
        None
    }

    /// `(c *Checker) discriminateTypeByDiscriminableItems`.
    pub(crate) fn discriminate_type_by_discriminable_items(
        &mut self,
        target: TypeId,
        mut r: ErrorReporter<'_>,
        discriminator: &mut dyn Discriminator,
    ) -> TypeId {
        let __arena_types = self.types.clone();
        let types = __arena_types.get_ref(target).types().to_vec();
        let mut include = vec![Ternary::default(); types.len()];
        for (i, &t) in types.iter().enumerate() {
            if !self
                .types_handle()
                .get_ref(t)
                .flags
                .intersects(TypeFlags::PRIMITIVE)
            {
                let reduced = self.get_reduced_type(t);
                if !self
                    .types_handle()
                    .get(reduced)
                    .flags
                    .intersects(TypeFlags::NEVER)
                {
                    include[i] = Ternary::TRUE;
                }
            }
        }
        for n in 0..discriminator.len() {
            // If the remaining target types include at least one with a
            // matching discriminant, eliminate those that have non-matching
            // discriminants. This ensures that we ignore erroneous
            // discriminators and gradually refine the target set without
            // eliminating every constituent (which would lead to `never`).
            let mut matched = false;
            let name = discriminator.name(self, n);
            for (i, &t) in types.iter().enumerate() {
                if include[i] != Ternary::FALSE {
                    let target_type =
                        self.get_type_of_property_or_index_signature_of_type(t, &name);
                    if let Some(target_type) = target_type {
                        if discriminator.matches(self, &mut r, n, target_type) {
                            matched = true;
                        } else {
                            include[i] = Ternary::MAYBE;
                        }
                    }
                }
            }
            // Turn each Ternary.Maybe into Ternary.False if there was a
            // match. Otherwise, revert to Ternary.True.
            for inc in include.iter_mut() {
                if *inc == Ternary::MAYBE {
                    *inc = if matched {
                        Ternary::FALSE
                    } else {
                        Ternary::TRUE
                    };
                }
            }
        }
        if include.contains(&Ternary::FALSE) {
            let filtered_types: Vec<TypeId> = types
                .iter()
                .zip(include.iter())
                .filter(|&(_, inc)| *inc == Ternary::TRUE)
                .map(|(&t, _)| t)
                .collect();
            let filtered = self.get_union_type_ex(
                &filtered_types,
                crate::checker_types::UnionReduction::None,
                None,
                None,
            );
            if !self
                .types_handle()
                .get_ref(filtered)
                .flags
                .intersects(TypeFlags::NEVER)
            {
                return filtered;
            }
        }
        target
    }

    /// `(c *Checker) filterPrimitivesIfContainsNonPrimitive`.
    pub(crate) fn filter_primitives_if_contains_non_primitive(
        &mut self,
        union_type: TypeId,
    ) -> TypeId {
        if self.maybe_type_of_kind(union_type, TypeFlags::NON_PRIMITIVE) {
            let result = self.filter_type(union_type, &mut |c: &mut Checker, t: TypeId| {
                is_non_primitive_type(&c.types, t)
            });
            if !self
                .types_handle()
                .get_ref(result)
                .flags
                .intersects(TypeFlags::NEVER)
            {
                return result;
            }
        }
        union_type
    }

    /// `(c *Checker) getTypeNamesForErrorDisplay`.
    pub(crate) fn get_type_names_for_error_display(
        &mut self,
        left: TypeId,
        right: TypeId,
    ) -> (String, String) {
        let __arena_left_symbol = self.types.clone();
        let left_symbol = __arena_left_symbol.get_ref(left).symbol;
        let mut left_str = if self.symbol_value_declaration_is_context_sensitive(left_symbol) {
            let decl = self.sym(left_symbol.unwrap()).value_declaration;
            self.type_to_string_ex(left, decl, crate::types::TypeFormatFlags::NONE, None)
        } else {
            self.type_to_string(left)
        };
        let __arena_right_symbol = self.types.clone();
        let right_symbol = __arena_right_symbol.get_ref(right).symbol;
        let mut right_str = if self.symbol_value_declaration_is_context_sensitive(right_symbol) {
            let decl = self.sym(right_symbol.unwrap()).value_declaration;
            self.type_to_string_ex(right, decl, crate::types::TypeFormatFlags::NONE, None)
        } else {
            self.type_to_string(right)
        };
        if left_str == right_str {
            left_str = self.get_type_name_for_error_display(left);
            right_str = self.get_type_name_for_error_display(right);
        }
        (left_str, right_str)
    }

    /// `(c *Checker) getTypeNameForErrorDisplay`.
    pub(crate) fn get_type_name_for_error_display(&mut self, t: TypeId) -> String {
        self.type_to_string_ex(
            t,
            None,
            crate::types::TypeFormatFlags::USE_FULLY_QUALIFIED_TYPE,
            None,
        )
    }

    /// `(c *Checker) symbolValueDeclarationIsContextSensitive`.
    fn symbol_value_declaration_is_context_sensitive(&mut self, symbol: Option<SymbolId>) -> bool {
        if let Some(symbol) = symbol {
            let value_declaration = self.sym(symbol).value_declaration;
            if let Some(decl) = value_declaration {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((decl).file_index());
                return ast::is_expression(&nodes[decl], &nodes)
                    && !self.is_context_sensitive(decl);
            }
        }
        false
    }

    /// `(c *Checker) typeCouldHaveTopLevelSingletonTypes` — okay, yes,
    /// 'boolean' is a union of 'true | false', but that's not useful in
    /// error reporting scenarios. If you need to use this function but that
    /// detail matters, feel free to add a flag.
    pub(crate) fn type_could_have_top_level_singleton_types(&mut self, t: TypeId) -> bool {
        let __arena_flags = self.types.clone();
        let flags = __arena_flags.get_ref(t).flags;
        if flags.intersects(TypeFlags::BOOLEAN) {
            return false;
        }
        if flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(t).types().to_vec();
            return types
                .iter()
                .any(|&t| self.type_could_have_top_level_singleton_types(t));
        }
        if flags.intersects(TypeFlags::INSTANTIABLE) {
            if let Some(constraint) = self.get_constraint_of_type(t) {
                if constraint != t {
                    return self.type_could_have_top_level_singleton_types(constraint);
                }
            }
        }
        crate::checker_d::is_unit_type(&self.types, t)
            || flags.intersects(TypeFlags::TEMPLATE_LITERAL | TypeFlags::STRING_MAPPING)
    }

    /// `(c *Checker) getVariances` — arrays and tuples are known to be
    /// covariant, no need to spend time computing this.
    pub(crate) fn get_variances(&mut self, t: TypeId) -> Vec<VarianceFlags> {
        {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get_ref(t);
            if t == self.global_array_type
                || t == self.global_readonly_array_type
                || ty.object_flags.intersects(ObjectFlags::TUPLE)
            {
                return self.array_variances.clone();
            }
        }
        let (symbol, type_parameters) = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get_ref(t);
            (
                ty.symbol,
                ty.as_interface_type()
                    .map(|i| i.type_parameters().to_vec())
                    .unwrap_or_default(),
            )
        };
        self.get_variances_worker(symbol, &type_parameters)
    }

    /// `(c *Checker) getAliasVariances`.
    pub(crate) fn get_alias_variances(&mut self, symbol: SymbolId) -> Vec<VarianceFlags> {
        let type_parameters = self.type_alias_links.get(symbol).type_parameters.clone();
        self.get_variances_worker(Some(symbol), &type_parameters)
    }

    /// `(c *Checker) getVariancesWorker` — return an array containing the
    /// variance of each type parameter. The variance is effectively a digest
    /// of the type comparisons that occur for each type argument when
    /// instantiations of the generic type are structurally compared. We infer
    /// the variance information by comparing instantiations of the generic
    /// type for type arguments with known relations. The function returns an
    /// empty slice when invoked recursively for the given generic type.
    fn get_variances_worker(
        &mut self,
        symbol: Option<SymbolId>,
        type_parameters: &[TypeId],
    ) -> Vec<VarianceFlags> {
        // `links.variances == nil` ↔ "no `variance_links` entry" (see header
        // PORT note); `get` is reserved for stores. Go keys the store by the
        // symbol pointer — `nil` (anonymous types) shares one entry — which
        // `SymbolId::default()` reproduces.
        let key = symbol.unwrap_or_default();
        if !self.variance_links.has(&key) {
            let mut trace_args = TraceArgs::new();
            let mut pop_fn: Option<Box<dyn FnOnce()>> = None;
            // Compute the id before taking the shared `tr` borrow — the call
            // needs `&mut self` while `tr` holds a shared borrow of
            // `self.tracer` for the whole `if let` scope.
            let declared_id = self.tracer.is_some().then(|| {
                self.get_declared_type_of_symbol(symbol.unwrap_or_default())
                    .0
            });
            if let Some(tr) = &self.tracer {
                trace_args.insert("arity".to_string(), (type_parameters.len() as i64).into());
                let id = declared_id.unwrap_or_default();
                trace_args.insert("id".to_string(), (id as i64).into());
                pop_fn = Some(tr.push(
                    tsc_tracing::PHASE_CHECK_TYPES,
                    "getVariancesWorker",
                    &mut trace_args,
                    true,
                ));
            }
            let result = self.get_variances_worker_computed(symbol, type_parameters);
            if let Some(tr) = &self.tracer {
                let formatted: Vec<String> = self
                    .variance_links
                    .try_get(&symbol.unwrap_or_default())
                    .map(|l| l.variances.iter().map(|v| format!("{}", v)).collect())
                    .unwrap_or_default();
                trace_args.insert("variances".to_string(), serde_json::Value::from(formatted));
                let _ = tr;
            }
            if let Some(pop) = pop_fn {
                pop();
            }
            return result;
        }
        self.variance_links
            .get(symbol.unwrap_or_default())
            .variances
            .clone()
    }

    /// The body of `getVariancesWorker` after the `links.variances == nil`
    /// check — split out so the trace pop can wrap it.
    fn get_variances_worker_computed(
        &mut self,
        symbol: Option<SymbolId>,
        type_parameters: &[TypeId],
    ) -> Vec<VarianceFlags> {
        let stack_index = self.get_variance_stack_index(symbol);
        if stack_index < 0 {
            let save_resolution_start = self.resolution_start;
            if self.variance_stack.is_empty() {
                self.resolution_start = self.type_resolutions.len() as i32;
            }
            self.variance_stack.push(VarianceStackEntry {
                symbol,
                type_parameters: type_parameters.to_vec(),
            });
            let mut variances = vec![VarianceFlags::default(); type_parameters.len()];
            for (i, &tp) in type_parameters.iter().enumerate() {
                let modifiers = self.get_type_parameter_modifiers(tp);
                let mut variance = VarianceFlags::default();
                if modifiers.intersects(ast::ModifierFlags::OUT) {
                    if modifiers.intersects(ast::ModifierFlags::IN) {
                        variance = VarianceFlags::INVARIANT;
                    } else {
                        variance = VarianceFlags::COVARIANT;
                    }
                } else if modifiers.intersects(ast::ModifierFlags::IN) {
                    variance = VarianceFlags::CONTRAVARIANT;
                } else {
                    let save_reliability_flags = self.reliability_flags;
                    self.reliability_flags = RelationComparisonResult::default();
                    // We first compare instantiations where the type
                    // parameter is replaced with marker types that have a
                    // known subtype relationship. From this we can infer
                    // invariance, covariance, contravariance or bivariance.
                    let type_with_super =
                        self.create_marker_type(symbol, tp, self.marker_super_type);
                    let type_with_sub = self.create_marker_type(symbol, tp, self.marker_sub_type);
                    let r1 = self.is_type_assignable_to(type_with_sub, type_with_super);
                    let r2 = self.is_type_assignable_to(type_with_super, type_with_sub);
                    variance = tsc_core::core::if_else(
                        r1,
                        VarianceFlags::COVARIANT,
                        VarianceFlags::default(),
                    ) | tsc_core::core::if_else(
                        r2,
                        VarianceFlags::CONTRAVARIANT,
                        VarianceFlags::default(),
                    );
                    // If the instantiations appear to be related bivariantly
                    // it may be because the type parameter is independent
                    // (i.e. it isn't witnessed anywhere in the generic
                    // type). To determine this we compare instantiations
                    // where the type parameter is replaced with marker types
                    // that are known to be unrelated.
                    if variance == VarianceFlags::BIVARIANT {
                        let other = self.create_marker_type(symbol, tp, self.marker_other_type);
                        if self.is_type_assignable_to(other, type_with_super) {
                            variance = VarianceFlags::INDEPENDENT;
                        }
                    }
                    if self
                        .reliability_flags
                        .intersects(RelationComparisonResult::REPORTS_UNMEASURABLE)
                    {
                        variance.insert(VarianceFlags::UNMEASURABLE);
                    }
                    if self
                        .reliability_flags
                        .intersects(RelationComparisonResult::REPORTS_UNRELIABLE)
                    {
                        variance.insert(VarianceFlags::UNRELIABLE);
                    }
                    self.reliability_flags = save_reliability_flags;
                }
                // If variance computation was restarted due to a circularity
                // we may have already computed variances for this generic
                // type. If so, we exit early.
                if self
                    .variance_links
                    .try_get(&symbol.unwrap_or_default())
                    .map(|l| !l.variances.is_empty())
                    .unwrap_or(false)
                {
                    break;
                }
                variances[i] = variance;
            }
            // Store the results unless a restarted computation has already
            // stored them.
            let links = self.variance_links.get(symbol.unwrap_or_default());
            if links.variances.is_empty() {
                links.variances = variances;
            }
            self.variance_stack.pop();
            if self.variance_stack.is_empty() {
                self.resolution_start = save_resolution_start;
            }
        } else {
            // We've detected a circularity. Since we may compute different
            // variances depending on where we enter a circularity, we find
            // the generic type with the "smallest" symbol in the circular
            // region of the variance stack and restart the computation from
            // there if necessary. This ensures stable results for circular
            // generic types.
            let mut min_index = stack_index as usize;
            for i in min_index + 1..self.variance_stack.len() {
                let compare = self
                    .compare_symbols
                    .clone()
                    .expect("compareSymbols is initialized by new_checker");
                if compare(
                    self,
                    self.variance_stack[i].symbol,
                    self.variance_stack[min_index].symbol,
                ) < 0
                {
                    min_index = i;
                }
            }
            if min_index > stack_index as usize {
                let save_variance_stack = std::mem::take(&mut self.variance_stack);
                self.get_variances_worker(
                    save_variance_stack[min_index].symbol,
                    &save_variance_stack[min_index].type_parameters.clone(),
                );
                self.variance_stack = save_variance_stack;
            }
            // Store an empty slice to mark that we can't compute variances
            // for this type. We treat type parameters as co-variant in this
            // case.
            let links = self.variance_links.get(symbol.unwrap_or_default());
            if links.variances.is_empty() {
                links.variances = Vec::new();
            }
        }
        self.variance_links
            .get(symbol.unwrap_or_default())
            .variances
            .clone()
    }

    /// `(c *Checker) getVarianceStackIndex`.
    fn get_variance_stack_index(&self, symbol: Option<SymbolId>) -> i32 {
        for (i, entry) in self.variance_stack.iter().enumerate() {
            if entry.symbol == symbol {
                return i as i32;
            }
        }
        -1
    }

    /// `(c *Checker) createMarkerType`.
    pub(crate) fn create_marker_type(
        &mut self,
        symbol: Option<SymbolId>,
        source: TypeId,
        target: TypeId,
    ) -> TypeId {
        let symbol = symbol.expect("createMarkerType requires a symbol");
        let mapper = crate::mapper::new_simple_type_mapper(self, source, target);
        let t = self.get_declared_type_of_symbol(symbol);
        if self.is_error_type(t) {
            return t;
        }
        let result;
        if self
            .sym(symbol)
            .flags
            .intersects(ast::SymbolFlags::TYPE_ALIAS)
        {
            let type_parameters = self.type_alias_links.get(symbol).type_parameters.clone();
            let instantiated = self.instantiate_types(&type_parameters, Some(mapper));
            result = self.get_type_alias_instantiation(symbol, &instantiated, None);
        } else {
            let __arena___guard_type_parameters = self.types.clone();
            let __guard_type_parameters = __arena___guard_type_parameters.get(t).clone();
            let type_parameters = __guard_type_parameters
                .as_interface_type()
                .map(|i| i.type_parameters().to_vec())
                .unwrap_or_default();
            let instantiated = self.instantiate_types(&type_parameters, Some(mapper));
            result = self.create_type_reference(t, &instantiated);
        }
        self.marker_types.add(result);
        result
    }

    /// `(c *Checker) isMarkerType`.
    pub(crate) fn is_marker_type(&mut self, t: TypeId) -> bool {
        self.marker_types.has(&t)
    }

    /// `(c *Checker) getTypeParameterModifiers`.
    pub(crate) fn get_type_parameter_modifiers(&mut self, tp: TypeId) -> ast::ModifierFlags {
        let mut flags = ast::ModifierFlags::default();
        if let Some(symbol) = self.types_handle().get(tp).symbol {
            let declarations = self.sym(symbol).declarations.clone();
            for d in declarations {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((d).file_index());
                flags.insert(nodes[d].modifier_flags());
            }
        }
        flags & (ast::ModifierFlags::IN | ast::ModifierFlags::OUT | ast::ModifierFlags::CONST)
    }

    /// `(c *Checker) hasCovariantVoidArgument` — return true if the given
    /// type reference has a 'void' type argument for a covariant type
    /// parameter. See comment at call in `recursiveTypeRelatedTo` for when
    /// this case matters.
    fn has_covariant_void_argument(
        &self,
        type_arguments: &[TypeId],
        variances: &[VarianceFlags],
    ) -> bool {
        for (i, v) in variances.iter().enumerate() {
            if (*v & VarianceFlags::VARIANCE_MASK) == VarianceFlags::COVARIANT
                && self
                    .types_handle()
                    .get(type_arguments[i])
                    .flags
                    .intersects(TypeFlags::VOID)
            {
                return true;
            }
        }
        false
    }

    /// `(c *Checker) isSignatureAssignableTo`.
    pub(crate) fn is_signature_assignable_to(
        &mut self,
        source: SignatureId,
        target: SignatureId,
        ignore_return_types: bool,
    ) -> bool {
        let check_mode = tsc_core::core::if_else(
            ignore_return_types,
            SignatureCheckMode::IGNORE_RETURN_TYPES,
            SignatureCheckMode::NONE,
        );
        self.compare_signatures_related(
            source,
            target,
            check_mode,
            false,
            None,
            Comparer::Assignable,
            None,
        ) != Ternary::FALSE
    }
}

/// `isObjectOrInstantiableNonPrimitive` (relater.go).
pub(crate) fn is_object_or_instantiable_non_primitive(
    types: &crate::types::TypeArena,
    t: TypeId,
) -> bool {
    types
        .get_ref(t)
        .flags
        .intersects(TypeFlags::OBJECT | TypeFlags::INSTANTIABLE_NON_PRIMITIVE)
}

/// `isNonPrimitiveType` (relater.go).
pub(crate) fn is_non_primitive_type(types: &crate::types::TypeArena, t: TypeId) -> bool {
    !types.get_ref(t).flags.intersects(TypeFlags::PRIMITIVE)
}

/// `<<unresolved>>` type predicate — Go's `sig.resolvedTypePredicate ==
/// c.noTypePredicate` pointer check degrades to structural comparison (see
/// header PORT note).
pub(crate) fn is_no_type_predicate(c: &Checker, predicate: &TypePredicate) -> bool {
    let Some(no_predicate) = &c.no_type_predicate else {
        return false;
    };
    predicate.kind == no_predicate.kind
        && predicate.parameter_index == no_predicate.parameter_index
        && predicate.parameter_name == no_predicate.parameter_name
        && predicate.t == no_predicate.t
}

impl Checker {
    /// `(c *Checker) compareSignaturesRelated`. `report_unreliable_markers`
    /// is Go's `reportUnreliableMarkers *TypeMapper`.
    pub(crate) fn compare_signatures_related(
        &mut self,
        mut source: SignatureId,
        mut target: SignatureId,
        check_mode: SignatureCheckMode,
        report_errors: bool,
        mut reporter: ErrorReporter<'_>,
        compare_types: Comparer,
        report_unreliable_markers: Option<TypeMapperId>,
    ) -> Ternary {
        if source == target {
            return Ternary::TRUE;
        }
        if !(check_mode.intersects(SignatureCheckMode::STRICT_TOP_SIGNATURE)
            && self.is_top_signature(source))
            && self.is_top_signature(target)
        {
            return Ternary::TRUE;
        }
        if check_mode.intersects(SignatureCheckMode::STRICT_TOP_SIGNATURE)
            && self.is_top_signature(source)
            && !self.is_top_signature(target)
        {
            return Ternary::FALSE;
        }
        let target_count = self.get_parameter_count(target);
        let mut source_has_more_parameters = false;
        if !self.has_effective_rest_parameter(target) {
            if check_mode.intersects(SignatureCheckMode::STRICT_ARITY) {
                source_has_more_parameters = self.has_effective_rest_parameter(source)
                    || self.get_parameter_count(source) > target_count;
            } else {
                source_has_more_parameters =
                    self.get_min_argument_count(source) > target_count as i32;
            }
        }
        if source_has_more_parameters {
            if report_errors && !check_mode.intersects(SignatureCheckMode::STRICT_ARITY) {
                let __h3461_25 = self.get_min_argument_count(source).to_string();

                // the second condition should be redundant, because there is
                // no error reporting when comparing signatures by strict
                // arity since it is only done for subtype reduction
                report_via(
                    self,
                    &mut reporter,
                    &tsc_diagnostics::Target_signature_provides_too_few_arguments_Expected_0_or_more_but_got_1,
                    &[

                        __h3461_25,
                        target_count.to_string(),
                    ],
                );
            }
            return Ternary::FALSE;
        }
        {
            let (source_tps, target_tps) = (
                self.signature_arena.get(source).type_parameters.clone(),
                self.signature_arena.get(target).type_parameters.clone(),
            );
            if !source_tps.is_empty() && !core::same(&source_tps, &target_tps) {
                target = self.get_canonical_signature(target);
                source = self.instantiate_signature_in_context_of(
                    source,
                    target,
                    None,
                    Some(Box::new(
                        move |c: &mut Checker, s: TypeId, t: TypeId, report_errors: bool| {
                            compare_via(c, &mut None, compare_types, s, t, report_errors)
                        },
                    )),
                );
            }
        }
        let source_count = self.get_parameter_count(source);
        let source_rest_type = self.get_non_array_rest_type(source);
        let target_rest_type = self.get_non_array_rest_type(target);
        if source_rest_type.is_some() || target_rest_type.is_some() {
            self.instantiate_type(
                source_rest_type.or(target_rest_type).unwrap(),
                report_unreliable_markers,
            );
        }
        let mut kind = ast::Kind::Unknown;
        if let Some(declaration) = self.signature_arena.get(target).declaration {
            kind = self.program_nodes(declaration)[declaration].kind;
        }
        let strict_variance = !check_mode.intersects(SignatureCheckMode::CALLBACK)
            && self.strict_function_types
            && kind != ast::Kind::MethodDeclaration
            && kind != ast::Kind::MethodSignature
            && kind != ast::Kind::Constructor;
        let mut result = Ternary::TRUE;
        let source_this_type = self.get_this_type_of_signature(source);
        if source_this_type.is_some() && source_this_type != Some(self.void_type) {
            let source_this_type = source_this_type.unwrap();
            if let Some(target_this_type) = self.get_this_type_of_signature(target) {
                // void sources are assignable to anything.
                let mut related = Ternary::default();
                if !strict_variance {
                    related = compare_via(
                        self,
                        &mut reporter,
                        compare_types,
                        source_this_type,
                        target_this_type,
                        false,
                    );
                }
                if related == Ternary::FALSE {
                    related = compare_via(
                        self,
                        &mut reporter,
                        compare_types,
                        target_this_type,
                        source_this_type,
                        report_errors,
                    );
                }
                if related == Ternary::FALSE {
                    if report_errors {
                        report_via(
                            self,
                            &mut reporter,
                            &tsc_diagnostics::The_this_types_of_each_signature_are_incompatible,
                            &[],
                        );
                    }
                    return Ternary::FALSE;
                }
                result = result & related;
            }
        }
        let param_count;
        if source_rest_type.is_some() || target_rest_type.is_some() {
            param_count = std::cmp::min(source_count, target_count);
        } else {
            param_count = std::cmp::max(source_count, target_count);
        }
        let rest_index;
        if source_rest_type.is_some() || target_rest_type.is_some() {
            rest_index = param_count as i32 - 1;
        } else {
            rest_index = -1;
        }
        for i in 0..param_count {
            let source_type;
            if i as i32 == rest_index {
                source_type = self.get_rest_or_any_type_at_position(source, i);
            } else {
                source_type = self.try_get_type_at_position(source, i);
            }
            let target_type;
            if i as i32 == rest_index {
                target_type = self.get_rest_or_any_type_at_position(target, i);
            } else {
                target_type = self.try_get_type_at_position(target, i);
            }
            if source_type.is_some()
                && target_type.is_some()
                && (source_type != target_type
                    || check_mode.intersects(SignatureCheckMode::STRICT_ARITY))
            {
                let source_type = source_type.unwrap();
                let target_type = target_type.unwrap();
                // In order to ensure that any generic type Foo<T> is at
                // least co-variant with respect to T no matter how Foo uses
                // T, we need to relate parameters bi-variantly (given that
                // parameters are input positions, they naturally relate only
                // contra-variantly). However, if the source and target
                // parameters both have function types with a single call
                // signature, we know we are relating two callback
                // parameters. In that case it is sufficient to only relate
                // the parameters of the signatures co-variantly because,
                // similar to return values, callback parameters are output
                // positions. This means that a Promise<T>, where T is used
                // only in callback parameter positions, will be co-variant
                // (as opposed to bi-variant) with respect to T.
                let mut source_sig: Option<SignatureId> = None;
                let mut target_sig: Option<SignatureId> = None;
                if !check_mode.intersects(SignatureCheckMode::CALLBACK)
                    && !self.is_instantiated_generic_parameter(source, i)
                {
                    let nn = self.get_non_nullable_type(source_type);
                    source_sig = self.get_single_call_signature(nn);
                }
                if !check_mode.intersects(SignatureCheckMode::CALLBACK)
                    && !self.is_instantiated_generic_parameter(target, i)
                {
                    let nn = self.get_non_nullable_type(target_type);
                    target_sig = self.get_single_call_signature(nn);
                }
                let callbacks = source_sig.is_some()
                    && target_sig.is_some()
                    && self
                        .get_type_predicate_of_signature(source_sig.unwrap())
                        .is_none()
                    && self
                        .get_type_predicate_of_signature(target_sig.unwrap())
                        .is_none()
                    && self.get_type_facts(
                        source_type,
                        crate::checker_types::TypeFacts::IS_UNDEFINED_OR_NULL,
                    ) == self.get_type_facts(
                        target_type,
                        crate::checker_types::TypeFacts::IS_UNDEFINED_OR_NULL,
                    );
                let mut related = Ternary::default();
                if callbacks {
                    related = self.compare_signatures_related(
                        target_sig.unwrap(),
                        source_sig.unwrap(),
                        (check_mode & SignatureCheckMode::STRICT_ARITY)
                            | tsc_core::core::if_else(
                                strict_variance,
                                SignatureCheckMode::STRICT_CALLBACK,
                                SignatureCheckMode::BIVARIANT_CALLBACK,
                            ),
                        report_errors,
                        reporter.as_deref_mut(),
                        compare_types,
                        report_unreliable_markers,
                    );
                } else {
                    if !check_mode.intersects(SignatureCheckMode::CALLBACK) && !strict_variance {
                        related = compare_via(
                            self,
                            &mut reporter,
                            compare_types,
                            source_type,
                            target_type,
                            false,
                        );
                    }
                    if related == Ternary::FALSE {
                        related = compare_via(
                            self,
                            &mut reporter,
                            compare_types,
                            target_type,
                            source_type,
                            report_errors,
                        );
                    }
                }
                // With strict arity, (x: number | undefined) => void is a
                // subtype of (x?: number | undefined) => void
                if related != Ternary::FALSE
                    && check_mode.intersects(SignatureCheckMode::STRICT_ARITY)
                    && i >= self.get_min_argument_count(source) as usize
                    && (i as i32) < self.get_min_argument_count(target)
                    && compare_via(
                        self,
                        &mut reporter,
                        compare_types,
                        source_type,
                        target_type,
                        false,
                    ) != Ternary::FALSE
                {
                    related = Ternary::FALSE;
                }
                if related == Ternary::FALSE {
                    if report_errors {
                        let source_name = self.get_parameter_name_at_position(source, i);
                        let target_name = self.get_parameter_name_at_position(target, i);
                        report_via(
                            self,
                            &mut reporter,
                            &tsc_diagnostics::Types_of_parameters_0_and_1_are_incompatible,
                            &[source_name, target_name],
                        );
                    }
                    return Ternary::FALSE;
                }
                result = result & related;
            }
        }
        if !check_mode.intersects(SignatureCheckMode::IGNORE_RETURN_TYPES) {
            // If a signature resolution is already in-flight, skip issuing a
            // circularity error here and just use the `any` type directly
            let target_return_type = self.get_non_circular_return_type_of_signature(target);
            if target_return_type == self.void_type || target_return_type == self.any_type {
                return result;
            }
            let source_return_type = self.get_non_circular_return_type_of_signature(source);
            // The following block preserves behavior forbidding boolean
            // returning functions from being assignable to type guard
            // returning functions
            let target_type_predicate = self.get_type_predicate_of_signature(target);
            if let Some(target_type_predicate) = &target_type_predicate {
                let source_type_predicate = self.get_type_predicate_of_signature(source);
                if let Some(source_type_predicate) = &source_type_predicate {
                    result = result
                        & self.compare_type_predicate_related_to(
                            source_type_predicate,
                            target_type_predicate,
                            report_errors,
                            reporter.as_deref_mut(),
                            compare_types,
                        );
                } else if target_type_predicate.kind == TypePredicateKind::Identifier
                    || target_type_predicate.kind == TypePredicateKind::This
                {
                    if report_errors {
                        let sig_str = self.signature_to_string(source);
                        report_via(
                            self,
                            &mut reporter,
                            &tsc_diagnostics::Signature_0_must_be_a_type_predicate,
                            &[sig_str],
                        );
                    }
                    return Ternary::FALSE;
                }
            } else {
                // When relating callback signatures, we still need to relate
                // return types bi-variantly as otherwise the containing type
                // wouldn't be co-variant. For example, interface
                // Foo<T> { add(cb: () => T): void } wouldn't be co-variant
                // for T without this rule.
                let mut related = Ternary::default();
                if check_mode.intersects(SignatureCheckMode::BIVARIANT_CALLBACK) {
                    related = compare_via(
                        self,
                        &mut reporter,
                        compare_types,
                        target_return_type,
                        source_return_type,
                        false,
                    );
                }
                if related == Ternary::FALSE {
                    related = compare_via(
                        self,
                        &mut reporter,
                        compare_types,
                        source_return_type,
                        target_return_type,
                        report_errors,
                    );
                }
                result = result & related;
                if result == Ternary::FALSE && report_errors {
                    // The errors reported here serve as markers that trigger
                    // error chain reduction in the `Relater::report_error`
                    // method. The markers are elided in the final diagnostic
                    // chain and never actually reported.
                    let (source_param_len, target_param_len, source_flags) = {
                        let s = self.signature_arena.get(source);
                        (
                            s.parameters.len(),
                            self.signature_arena.get(target).parameters.len(),
                            s.flags,
                        )
                    };
                    let message: &'static tsc_diagnostics::Message = if source_param_len == 0
                        && target_param_len == 0
                    {
                        if source_flags.intersects(SignatureFlags::CONSTRUCT) {
                            &tsc_diagnostics::Construct_signatures_with_no_arguments_have_incompatible_return_types_0_and_1
                        } else {
                            &tsc_diagnostics::Call_signatures_with_no_arguments_have_incompatible_return_types_0_and_1
                        }
                    } else if source_flags.intersects(SignatureFlags::CONSTRUCT) {
                        &tsc_diagnostics::Construct_signature_return_types_0_and_1_are_incompatible
                    } else {
                        &tsc_diagnostics::Call_signature_return_types_0_and_1_are_incompatible
                    };
                    let source_str = self.type_to_string(source_return_type);
                    let target_str = self.type_to_string(target_return_type);
                    report_via(self, &mut reporter, message, &[source_str, target_str]);
                }
            }
        }
        result
    }

    /// `(c *Checker) compareTypePredicateRelatedTo`.
    fn compare_type_predicate_related_to(
        &mut self,
        source: &TypePredicate,
        target: &TypePredicate,
        report_errors: bool,
        mut reporter: ErrorReporter<'_>,
        compare_types: Comparer,
    ) -> Ternary {
        if source.kind != target.kind {
            if report_errors {
                report_via(
                    self,
                    &mut reporter,
                    &tsc_diagnostics::A_this_based_type_guard_is_not_compatible_with_a_parameter_based_type_guard,
                    &[],
                );
                let source_str = self.type_predicate_to_string(Some(source));
                let target_str = self.type_predicate_to_string(Some(target));
                report_via(
                    self,
                    &mut reporter,
                    &tsc_diagnostics::Type_predicate_0_is_not_assignable_to_1,
                    &[source_str, target_str],
                );
            }
            return Ternary::FALSE;
        }
        if source.kind == TypePredicateKind::Identifier
            || source.kind == TypePredicateKind::AssertsIdentifier
        {
            if source.parameter_index != target.parameter_index {
                if report_errors {
                    report_via(
                        self,
                        &mut reporter,
                        &tsc_diagnostics::Parameter_0_is_not_in_the_same_position_as_parameter_1,
                        &[source.parameter_name.clone(), target.parameter_name.clone()],
                    );
                    let source_str = self.type_predicate_to_string(Some(source));
                    let target_str = self.type_predicate_to_string(Some(target));
                    report_via(
                        self,
                        &mut reporter,
                        &tsc_diagnostics::Type_predicate_0_is_not_assignable_to_1,
                        &[source_str, target_str],
                    );
                }
                return Ternary::FALSE;
            }
        }
        let related;
        if source.t == target.t {
            related = Ternary::TRUE;
        } else if source.t.is_some() && target.t.is_some() {
            related = compare_via(
                self,
                &mut reporter,
                compare_types,
                source.t.unwrap(),
                target.t.unwrap(),
                report_errors,
            );
        } else {
            related = Ternary::FALSE;
        }
        if related == Ternary::FALSE && report_errors {
            let source_str = self.type_predicate_to_string(Some(source));
            let target_str = self.type_predicate_to_string(Some(target));
            report_via(
                self,
                &mut reporter,
                &tsc_diagnostics::Type_predicate_0_is_not_assignable_to_1,
                &[source_str, target_str],
            );
        }
        related
    }

    /// `(c *Checker) isTopSignature` — returns true if `s` is
    /// `(...args: A) => R` where `A` is `any`, `any[]`, `never`, or
    /// `never[]`, and `R` is `any` or `unknown`.
    fn is_top_signature(&mut self, s: SignatureId) -> bool {
        let (type_parameters, this_parameter, parameters) = {
            let sig = self.signature_arena.get(s);
            (
                sig.type_parameters.len(),
                sig.this_parameter,
                sig.parameters.clone(),
            )
        };
        if type_parameters == 0
            && (this_parameter.is_none() || {
                let t = self.get_type_of_parameter(this_parameter.unwrap());
                crate::utilities::is_type_any(&self.types, t)
            })
            && parameters.len() == 1
            && crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(s))
        {
            let param_type = self.get_type_of_parameter(parameters[0]);
            let rest_type;
            if self.is_array_type(param_type) {
                rest_type = self.get_type_arguments(param_type)[0];
            } else {
                rest_type = param_type;
            }
            return self
                .types_handle()
                .get(rest_type)
                .flags
                .intersects(TypeFlags::ANY | TypeFlags::NEVER)
                && self
                    .types_handle()
                    .get({
                        let rt = self.get_return_type_of_signature(s);
                        rt
                    })
                    .flags
                    .intersects(TypeFlags::ANY_OR_UNKNOWN);
        }
        false
    }

    /// `(c *Checker) getParameterCount` — return the number of parameters in
    /// a signature. The rest parameter, if present, counts as one parameter.
    /// For example, the parameter count of `(x: number, y: number, ...z:
    /// string[])` is 3 and the parameter count of `(x: number, ...args:
    /// [number, ...string[], boolean]))` is also 3. In the latter example,
    /// the effective rest type is `[...string[], boolean]`.
    pub(crate) fn get_parameter_count(&mut self, signature: SignatureId) -> usize {
        let length = self.signature_arena.get(signature).parameters.len();
        if crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(signature)) {
            let last = *self
                .signature_arena
                .get(signature)
                .parameters
                .last()
                .unwrap();
            let rest_type = self.get_type_of_symbol(last);
            if is_tuple_type(&self.types, rest_type) {
                let __arena_target = self.types.clone();
                let target = __arena_target.target_tuple_type(rest_type).unwrap();
                let __arena___guard_tuple = self.types.clone();
                let __guard_tuple = __arena___guard_tuple.get(target).clone();
                let tuple = __guard_tuple.as_tuple_type();
                return length + tuple.fixed_length
                    - tsc_core::core::if_else(
                        tuple.combined_flags.intersects(ElementFlags::VARIABLE),
                        0usize,
                        1usize,
                    );
            }
        }
        length
    }

    /// `(c *Checker) getMinArgumentCount`.
    pub(crate) fn get_min_argument_count(&mut self, signature: SignatureId) -> i32 {
        self.get_min_argument_count_ex(signature, MinArgumentCountFlags::NONE)
    }

    /// `(c *Checker) getMinArgumentCountEx`.
    pub(crate) fn get_min_argument_count_ex(
        &mut self,
        signature: SignatureId,
        flags: MinArgumentCountFlags,
    ) -> i32 {
        let strong_arity_for_untyped_js =
            flags & MinArgumentCountFlags::STRONG_ARITY_FOR_UNTYPED_JS;
        let void_is_non_optional = flags & MinArgumentCountFlags::VOID_IS_NON_OPTIONAL;
        if !void_is_non_optional.is_empty()
            || self
                .signature_arena
                .get(signature)
                .resolved_min_argument_count
                == -1
        {
            let mut min_argument_count: i32 = -1;
            if crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(signature)) {
                let last = *self
                    .signature_arena
                    .get(signature)
                    .parameters
                    .last()
                    .unwrap();
                let rest_type = self.get_type_of_symbol(last);
                if is_tuple_type(&self.types, rest_type) {
                    let __arena_target = self.types.clone();
                    let target = __arena_target.target_tuple_type(rest_type).unwrap();
                    let __arena_element_infos = self.types.clone();
                    let element_infos = __arena_element_infos
                        .get(target)
                        .as_tuple_type()
                        .element_infos
                        .clone();
                    let first_optional_index = element_infos
                        .iter()
                        .position(|info| !info.flags.intersects(ElementFlags::REQUIRED))
                        .map(|i| i as i32)
                        .unwrap_or(-1);
                    let mut required_count = first_optional_index;
                    if first_optional_index < 0 {
                        required_count =
                            self.types_handle().get_ref(target).as_tuple_type().fixed_length as i32;
                    }
                    if required_count > 0 {
                        min_argument_count =
                            self.signature_arena.get(signature).parameters.len() as i32 - 1
                                + required_count;
                    }
                }
            }
            if min_argument_count == -1 {
                if strong_arity_for_untyped_js.is_empty()
                    && self
                        .signature_arena
                        .get(signature)
                        .flags
                        .intersects(SignatureFlags::IS_UNTYPED_SIGNATURE_IN_JS_FILE)
                {
                    return 0;
                }
                min_argument_count = self.signature_arena.get(signature).min_argument_count;
            }
            if !void_is_non_optional.is_empty() {
                return min_argument_count;
            }
            for i in (0..min_argument_count).rev() {
                let t = self.get_type_at_position(signature, i as usize);
                if !crate::checker_d::some_type(self, t, |c: &mut Checker, t: TypeId| {
                    c.types_handle().get_ref(t).flags.intersects(TypeFlags::VOID)
                }) {
                    break;
                }
                min_argument_count = i;
            }
            self.signature_arena
                .get_mut(signature)
                .resolved_min_argument_count = min_argument_count;
        }
        self.signature_arena
            .get(signature)
            .resolved_min_argument_count
    }

    /// `(c *Checker) hasEffectiveRestParameter`.
    pub fn has_effective_rest_parameter(&mut self, signature: SignatureId) -> bool {
        if crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(signature)) {
            let last = *self
                .signature_arena
                .get(signature)
                .parameters
                .last()
                .unwrap();
            let rest_type = self.get_type_of_symbol(last);
            return !is_tuple_type(&self.types, rest_type) || {
                let __arena_target = self.types.clone();
                let target = __arena_target.target_tuple_type(rest_type).unwrap();
                self.types_handle()
                    .get(target)
                    .as_tuple_type()
                    .combined_flags
                    .intersects(ElementFlags::VARIABLE)
            };
        }
        false
    }

    /// `(c *Checker) getTypeAtPosition`.
    pub fn get_type_at_position(&mut self, signature: SignatureId, pos: usize) -> TypeId {
        if let Some(t) = self.try_get_type_at_position(signature, pos) {
            return t;
        }
        self.any_type
    }

    /// `(c *Checker) tryGetTypeAtPosition`.
    pub(crate) fn try_get_type_at_position(
        &mut self,
        signature: SignatureId,
        pos: usize,
    ) -> Option<TypeId> {
        let parameters_len = self.signature_arena.get(signature).parameters.len();
        let has_rest =
            crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(signature));
        let param_count = parameters_len - tsc_core::core::if_else(has_rest, 1usize, 0usize);
        if pos < param_count {
            let param = self.signature_arena.get(signature).parameters[pos];
            return Some(self.get_type_of_parameter(param));
        }
        if has_rest {
            // We want to return the value undefined for an out of bounds
            // parameter position, so we need to check bounds here before
            // calling getIndexedAccessType (which otherwise would return the
            // type 'undefined').
            let rest_parameter = self.signature_arena.get(signature).parameters[param_count];
            let rest_type = self.get_type_of_symbol(rest_parameter);
            let index = pos - param_count;
            if !is_tuple_type(&self.types, rest_type) || {
                let __arena_target = self.types.clone();
                let target = __arena_target.target_tuple_type(rest_type).unwrap();
                let __arena___guard_tuple = self.types.clone();
                let __guard_tuple = __arena___guard_tuple.get(target).clone();
                let tuple = __guard_tuple.as_tuple_type();
                tuple.combined_flags.intersects(ElementFlags::VARIABLE)
                    || index < tuple.fixed_length
            } {
                let index_type = self.get_number_literal_type(tsc_jsnum::Number(index as f64));
                return Some(self.get_indexed_access_type(rest_type, index_type));
            }
        }
        None
    }

    /// `(c *Checker) getRestOrAnyTypeAtPosition` — return the rest type at
    /// the given position, transforming `any[]` into just `any`. We do this
    /// because in signatures we want `any[]` in a rest position to be
    /// compatible with anything, but `any[]` isn't assignable to tuple
    /// types with required elements.
    fn get_rest_or_any_type_at_position(
        &mut self,
        source: SignatureId,
        pos: usize,
    ) -> Option<TypeId> {
        let rest_type = self.get_rest_type_at_position(source, pos, false);
        if let Some(rest_type) = rest_type {
            if let Some(element_type) = self.get_element_type_of_array_type(rest_type) {
                if crate::utilities::is_type_any(&self.types, element_type) {
                    return Some(self.any_type);
                }
            }
        }
        rest_type
    }

    /// `(c *Checker) getRestTypeAtPosition`.
    pub(crate) fn get_rest_type_at_position(
        &mut self,
        source: SignatureId,
        pos: usize,
        readonly: bool,
    ) -> Option<TypeId> {
        let parameter_count = self.get_parameter_count(source);
        let min_argument_count = self.get_min_argument_count(source);
        let rest_type = self.get_effective_rest_type(source);
        if rest_type.is_some() && pos >= parameter_count - 1 {
            if pos == parameter_count - 1 {
                return rest_type;
            } else {
                let number_indexed =
                    self.get_indexed_access_type(rest_type.unwrap(), self.number_type);
                return Some(self.create_array_type(number_indexed));
            }
        }
        let length = parameter_count as i32 - pos as i32;
        if length <= 0 {
            return Some(self.create_tuple_type_ex(&[], &[], readonly));
        }
        let length = length as usize;
        let mut types = Vec::with_capacity(length);
        let mut infos = Vec::with_capacity(length);
        for i in 0..length {
            let flags;
            if rest_type.is_none() || i < length - 1 {
                types.push(self.get_type_at_position(source, i + pos));
                flags = tsc_core::core::if_else(
                    ((i + pos) as i32) < min_argument_count,
                    ElementFlags::REQUIRED,
                    ElementFlags::OPTIONAL,
                );
            } else {
                types.push(rest_type.unwrap());
                flags = ElementFlags::VARIADIC;
            }
            infos.push(crate::types::TupleElementInfo {
                flags,
                labeled_declaration: self.get_nameable_declaration_at_position(source, i + pos),
            });
        }
        Some(self.create_tuple_type_ex(&types, &infos, readonly))
    }

    /// `(c *Checker) getNameableDeclarationAtPosition`.
    fn get_nameable_declaration_at_position(
        &mut self,
        signature: SignatureId,
        pos: usize,
    ) -> Option<NodeId> {
        let parameters_len = self.signature_arena.get(signature).parameters.len();
        let has_rest =
            crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(signature));
        let param_count = parameters_len - tsc_core::core::if_else(has_rest, 1usize, 0usize);
        if pos < param_count {
            let param = self.signature_arena.get(signature).parameters[pos];
            let decl = self.sym(param).value_declaration;
            if decl.is_some_and(|d| self.is_valid_declaration_for_tuple_label(d)) {
                return decl;
            }
            return None;
        }
        if has_rest {
            let rest_parameter = self.signature_arena.get(signature).parameters[param_count];
            let rest_type = self.get_type_of_symbol(rest_parameter);
            if is_tuple_type(&self.types, rest_type) {
                let __arena_target = self.types.clone();
                let target = __arena_target.target_tuple_type(rest_type).unwrap();
                let __arena___guard_element_infos = self.types.clone();
                let __guard_element_infos = __arena___guard_element_infos.get(target).clone();
                let element_infos = __guard_element_infos.as_tuple_type().element_infos.clone();
                let index = pos - param_count;
                if index < element_infos.len() {
                    return element_infos[index].labeled_declaration;
                }
                return None;
            }
            let decl = self.sym(rest_parameter).value_declaration;
            if decl.is_some_and(|d| self.is_valid_declaration_for_tuple_label(d)) {
                return decl;
            }
        }
        None
    }

    /// `(c *Checker) isValidDeclarationForTupleLabel`.
    fn is_valid_declaration_for_tuple_label(&mut self, d: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((d).file_index());
        ast::is_named_tuple_member(&nodes[d])
            || (ast::is_parameter_declaration(&nodes[d])
                && nodes[d]
                    .name()
                    .is_some_and(|n| ast::is_identifier(&nodes[n])))
    }

    /// `(c *Checker) getNonArrayRestType`.
    pub(crate) fn get_non_array_rest_type(&mut self, signature: SignatureId) -> Option<TypeId> {
        let rest_type = self.get_effective_rest_type(signature);
        if let Some(rest_type) = rest_type {
            if !self.is_array_type(rest_type)
                && !crate::utilities::is_type_any(&self.types, rest_type)
            {
                return Some(rest_type);
            }
        }
        None
    }

    /// `(c *Checker) getEffectiveRestType`.
    /// PORT(visibility): widened to `pub(crate)` for inference.rs.
    pub(crate) fn get_effective_rest_type(&mut self, signature: SignatureId) -> Option<TypeId> {
        if crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(signature)) {
            let last = *self
                .signature_arena
                .get(signature)
                .parameters
                .last()
                .unwrap();
            let rest_type = self.get_type_of_symbol(last);
            if !is_tuple_type(&self.types, rest_type) {
                if crate::utilities::is_type_any(&self.types, rest_type) {
                    return Some(self.any_array_type);
                }
                return Some(rest_type);
            }
            let __arena_target = self.types.clone();
            let target = __arena_target.target_tuple_type(rest_type).unwrap();
            let (combined_flags, fixed_length) = {
                let __arena___guard_tuple = self.types.clone();
                let __guard_tuple = __arena___guard_tuple.get(target).clone();
                let tuple = __guard_tuple.as_tuple_type();
                (tuple.combined_flags, tuple.fixed_length)
            };
            if combined_flags.intersects(ElementFlags::VARIABLE) {
                return Some(self.slice_tuple_type(rest_type, fixed_length, 0));
            }
        }
        None
    }

    /// `(c *Checker) sliceTupleType`.
    pub(crate) fn slice_tuple_type(
        &mut self,
        t: TypeId,
        index: usize,
        end_skip_count: i32,
    ) -> TypeId {
        let __arena_target_id = self.types.clone();
        let target_id = __arena_target_id.target_tuple_type(t).unwrap();
        let __arena___guard_fixed_length = self.types.clone();
        let __guard_fixed_length = __arena___guard_fixed_length.get(target_id).clone();
        let fixed_length = __guard_fixed_length.as_tuple_type().fixed_length;
        let arity = self.get_type_reference_arity(t) as i32;
        let end_index = arity - std::cmp::max(end_skip_count, 0);
        if index > fixed_length {
            if let Some(rest_array_type) = self.get_rest_array_type_of_tuple_type(t) {
                return rest_array_type;
            }
            return self.create_tuple_type(&[]);
        }
        if index as i32 >= end_index {
            return self.create_tuple_type(&[]);
        }
        let type_arguments = self.get_type_arguments(t);
        let __arena___guard_element_infos = self.types.clone();
        let __guard_element_infos = __arena___guard_element_infos.get(target_id).clone();
        let element_infos = __guard_element_infos.as_tuple_type().element_infos.clone();
        self.create_tuple_type_ex(
            &type_arguments[index..end_index as usize],
            &element_infos[index..end_index as usize],
            false,
        )
    }

    /// `(c *Checker) getKnownKeysOfTupleType`.
    pub(crate) fn get_known_keys_of_tuple_type(&mut self, t: TypeId) -> TypeId {
        let __arena_target_id = self.types.clone();
        let target_id = __arena_target_id.target_tuple_type(t).unwrap();
        let (fixed_length, readonly) = {
            let __arena___guard_tuple = self.types.clone();
            let __guard_tuple = __arena___guard_tuple.get(target_id).clone();
            let tuple = __guard_tuple.as_tuple_type();
            (tuple.fixed_length, tuple.readonly)
        };
        let mut keys = Vec::with_capacity(fixed_length + 1);
        for i in 0..fixed_length {
            keys.push(self.get_string_literal_type(&i.to_string()));
        }
        let index_type = self.get_index_type(tsc_core::core::if_else(
            readonly,
            self.global_readonly_array_type,
            self.global_array_type,
        ));
        keys.push(index_type);
        self.get_union_type(&keys)
    }

    /// `(c *Checker) getRestArrayTypeOfTupleType`.
    fn get_rest_array_type_of_tuple_type(&mut self, t: TypeId) -> Option<TypeId> {
        if let Some(rest_type) = self.get_rest_type_of_tuple_type(t) {
            return Some(self.create_array_type(rest_type));
        }
        None
    }

    /// `(c *Checker) getThisTypeOfSignature`.
    pub(crate) fn get_this_type_of_signature(&mut self, signature: SignatureId) -> Option<TypeId> {
        if let Some(this_parameter) = self.signature_arena.get(signature).this_parameter {
            return Some(self.get_type_of_symbol(this_parameter));
        }
        None
    }

    /// `(c *Checker) isInstantiatedGenericParameter`.
    fn is_instantiated_generic_parameter(&mut self, signature: SignatureId, pos: usize) -> bool {
        let Some(target) = self.signature_arena.get(signature).target else {
            return false;
        };
        let t = self.try_get_type_at_position(target, pos);
        t.is_some_and(|t| self.is_generic_type(t))
    }

    /// `(c *Checker) getParameterNameAtPosition`.
    pub(crate) fn get_parameter_name_at_position(
        &mut self,
        signature: SignatureId,
        pos: usize,
    ) -> String {
        let parameters_len = self.signature_arena.get(signature).parameters.len();
        let has_rest =
            crate::checker_c::signature_has_rest_parameter(self.signature_arena.get(signature));
        let param_count = parameters_len - tsc_core::core::if_else(has_rest, 1usize, 0usize);
        if pos < param_count {
            let param = self.signature_arena.get(signature).parameters[pos];
            return self.sym(param).name.clone();
        }
        let rest_parameter = self.signature_arena.get(signature).parameters[param_count];
        let rest_type = self.get_type_of_symbol(rest_parameter);
        if is_tuple_type(&self.types, rest_type) {
            let __arena_target = self.types.clone();
            let target = __arena_target.target_tuple_type(rest_type).unwrap();
            let __arena___guard_info = self.types.clone();
            let __guard_info = __arena___guard_info.get(target).clone();
            let info = __guard_info.as_tuple_type().element_infos[pos - param_count].clone();
            return self.get_tuple_element_label(info, Some(rest_parameter), pos - param_count);
        }
        self.sym(rest_parameter).name.clone()
    }

    /// `(c *Checker) getTupleElementLabel`.
    pub(crate) fn get_tuple_element_label(
        &mut self,
        element_info: crate::types::TupleElementInfo,
        rest_symbol: Option<SymbolId>,
        index: usize,
    ) -> String {
        if let Some(labeled) = element_info.labeled_declaration {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((labeled).file_index());
            return nodes[labeled]
                .name()
                .map(|n| nodes[n].text(&nodes).to_string())
                .unwrap_or_default();
        }
        if let Some(rest_symbol) = rest_symbol {
            let value_declaration = self.sym(rest_symbol).value_declaration;
            if let Some(decl) = value_declaration {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((decl).file_index());
                if ast::is_parameter_declaration(&nodes[decl]) {
                    return self.get_tuple_element_label_from_binding_element(
                        decl,
                        index,
                        element_info.flags,
                    );
                }
            }
        }
        let root_name = rest_symbol
            .map(|s| self.sym(s).name.clone())
            .unwrap_or_else(|| "arg".to_string());
        format!("{}_{}", root_name, index)
    }

    /// `(c *Checker) getTupleElementLabelFromBindingElement`.
    fn get_tuple_element_label_from_binding_element(
        &mut self,
        node: NodeId,
        index: usize,
        element_flags: ElementFlags,
    ) -> String {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(name) = nodes[node].name() {
            match nodes[name].kind {
                ast::Kind::Identifier => {
                    let name_text = nodes[name].text(&nodes).to_string();
                    if crate::utilities::has_dot_dot_dot_token(&nodes[node], &nodes) {
                        // given
                        //   (...[x, y, ...z]: [number, number, ...number[]]) => ...
                        // this produces
                        //   (x: number, y: number, ...z: number[]) => ...
                        // which preserves rest elements of 'z'
                        //
                        // given
                        //   (...[x, y, ...z]: [number, number, ...[...number[], number]]) => ...
                        // this produces
                        //   (x: number, y: number, ...z: number[], z_1: number) => ...
                        // which preserves rest elements of z but gives
                        // distinct numbers to fixed elements of 'z'
                        if element_flags.intersects(ElementFlags::VARIABLE) {
                            return name_text;
                        }
                        return format!("{}_{}", name_text, index);
                    }
                    // given
                    //   (...[x]: [number]) => ...
                    // this produces
                    //   (x: number) => ...
                    // which preserves fixed elements of 'x'
                    //
                    // given
                    //   (...[x]: ...number[]) => ...
                    // this produces
                    //   (x_0: number) => ...
                    // which numbers fixed elements of 'x' whose tuple
                    // element type is variable
                    if element_flags.intersects(ElementFlags::FIXED) {
                        return name_text;
                    }
                    return format!("{}_n", name_text);
                }
                ast::Kind::ArrayBindingPattern => {
                    if crate::utilities::has_dot_dot_dot_token(&nodes[node], &nodes) {
                        let elements = nodes[name]
                            .elements()
                            .map(|e| e.to_vec())
                            .unwrap_or_default();
                        let last_element = elements.last().copied();
                        let last_element_is_binding_element_rest = last_element.is_some_and(|e| {
                            ast::is_binding_element(&nodes[e])
                                && crate::utilities::has_dot_dot_dot_token(&nodes[e], &nodes)
                        });
                        let element_count = elements.len()
                            - tsc_core::core::if_else(
                                last_element_is_binding_element_rest,
                                1usize,
                                0usize,
                            );
                        if index < element_count {
                            let element = elements[index];
                            if ast::is_binding_element(&nodes[element]) {
                                return self.get_tuple_element_label_from_binding_element(
                                    element,
                                    index,
                                    element_flags,
                                );
                            }
                        } else if last_element_is_binding_element_rest {
                            return self.get_tuple_element_label_from_binding_element(
                                last_element.unwrap(),
                                index - element_count,
                                element_flags,
                            );
                        }
                    }
                }
                _ => {}
            }
        }
        format!("arg_{}", index)
    }

    /// `(c *Checker) getTypePredicateOfSignature`.
    pub fn get_type_predicate_of_signature(&mut self, sig: SignatureId) -> Option<TypePredicate> {
        if self
            .signature_arena
            .get(sig)
            .resolved_type_predicate
            .is_none()
        {
            enum Branch {
                Resolved,
                Composite,
                Default,
            }
            let (target, composite, declaration, resolved_return) = {
                let s = self.signature_arena.get(sig);
                (
                    s.target,
                    s.composite.clone(),
                    s.declaration,
                    s.resolved_return_type,
                )
            };
            let branch = if target.is_some() {
                Branch::Resolved
            } else if composite.is_some() {
                Branch::Composite
            } else {
                Branch::Default
            };
            let mut resolved: Option<TypePredicate> = None;
            match branch {
                Branch::Resolved => {
                    let target_type_predicate =
                        self.get_type_predicate_of_signature(target.unwrap());
                    if let Some(target_type_predicate) = target_type_predicate {
                        let mapper = self.signature_arena.get(sig).mapper;
                        resolved =
                            Some(self.instantiate_type_predicate(&target_type_predicate, mapper));
                    }
                }
                Branch::Composite => {
                    let composite = composite.unwrap();
                    resolved = self.get_union_or_intersection_type_predicate(
                        &composite.signatures,
                        composite.is_union,
                    );
                }
                Branch::Default => {
                    if let Some(declaration) = declaration {
                        let __program = self.program.clone().expect("program");
                        let nodes = __program.nodes((declaration).file_index());
                        let type_node = nodes[declaration].type_();
                        if let Some(type_node) = type_node {
                            if ast::is_type_predicate_node(&nodes[type_node]) {
                                resolved =
                                    Some(self.create_type_predicate_from_type_predicate_node(
                                        type_node, sig,
                                    ));
                            }
                        } else if ast::is_function_like_declaration(Some(declaration), &nodes)
                            && (resolved_return.is_none()
                                || self
                                    .types_handle()
                                    .get(resolved_return.unwrap())
                                    .flags
                                    .intersects(TypeFlags::BOOLEAN))
                            && self.get_parameter_count(sig) > 0
                        {
                            // `sig.resolvedTypePredicate = c.noTypePredicate`
                            // avoids the infinite loop — a provisional clone
                            // of the sentinel, then overwritten.
                            self.signature_arena.get_mut(sig).resolved_type_predicate = self
                                .no_type_predicate
                                .as_ref()
                                .map(|p| Box::new((**p).clone()));
                            resolved = self.get_type_predicate_from_body(declaration);
                        }
                    }
                }
            }
            if resolved.is_none() {
                resolved = self.no_type_predicate.as_ref().map(|p| (**p).clone());
            }
            self.signature_arena.get_mut(sig).resolved_type_predicate = resolved.map(Box::new);
        }
        let predicate = self
            .signature_arena
            .get(sig)
            .resolved_type_predicate
            .clone();
        let predicate = predicate.expect("resolvedTypePredicate just set");
        if is_no_type_predicate(self, &predicate) {
            return None;
        }
        Some(*predicate)
    }

    /// `(c *Checker) getUnionOrIntersectionTypePredicate`.
    fn get_union_or_intersection_type_predicate(
        &mut self,
        signatures: &[SignatureId],
        is_union: bool,
    ) -> Option<TypePredicate> {
        let mut last: Option<TypePredicate> = None;
        let mut types: Vec<TypeId> = Vec::new();
        for &sig in signatures {
            let pred = self.get_type_predicate_of_signature(sig);
            if let Some(pred) = pred {
                // Constituent type predicates must all have matching kinds.
                // We don't create composite type predicates for assertions.
                if pred.kind != TypePredicateKind::This
                    && pred.kind != TypePredicateKind::Identifier
                    || last
                        .as_ref()
                        .is_some_and(|l| !self.type_predicate_kinds_match(l, &pred))
                {
                    return None;
                }
                types.push(pred.t.unwrap_or(TypeId::NONE));
                last = Some(pred);
            } else {
                // In composite union signatures we permit and ignore
                // signatures with a return type `false`.
                let mut return_type: Option<TypeId> = None;
                if is_union {
                    return_type = Some(self.get_return_type_of_signature(sig));
                }
                if return_type != Some(self.false_type)
                    && return_type != Some(self.regular_false_type)
                {
                    return None;
                }
            }
        }
        let last = last?;
        let composite_type = self.get_union_or_intersection_type(
            &types,
            is_union,
            crate::checker_types::UnionReduction::Literal,
        );
        Some(self.new_type_predicate(
            last.kind,
            last.parameter_name,
            last.parameter_index,
            Some(composite_type),
        ))
    }

    /// `(c *Checker) typePredicateKindsMatch`.
    /// PORT(visibility): widened to `pub(crate)` for inference.rs.
    pub(crate) fn type_predicate_kinds_match(
        &mut self,
        a: &TypePredicate,
        b: &TypePredicate,
    ) -> bool {
        a.kind == b.kind && a.parameter_index == b.parameter_index
    }

    /// `(c *Checker) createTypePredicateFromTypePredicateNode`.
    fn create_type_predicate_from_type_predicate_node(
        &mut self,
        node: NodeId,
        signature: SignatureId,
    ) -> TypePredicate {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let predicate_node = nodes[node].as_type_predicate_node();
        let parameter_name_node = predicate_node.parameter_name;
        let type_node = predicate_node.type_;
        let asserts_modifier = predicate_node.asserts_modifier;
        let t = type_node.map(|tn| self.get_type_from_type_node(tn));
        if parameter_name_node.is_some_and(|pn| ast::is_this_type_node(&nodes[pn])) {
            let kind = tsc_core::core::if_else(
                asserts_modifier.is_some(),
                TypePredicateKind::AssertsThis,
                TypePredicateKind::This,
            );
            return self.new_type_predicate(kind, String::new(), 0, t);
        }
        let kind = tsc_core::core::if_else(
            asserts_modifier.is_some(),
            TypePredicateKind::AssertsIdentifier,
            TypePredicateKind::Identifier,
        );
        let name = nodes[parameter_name_node.unwrap()].text(&nodes).to_string();
        let parameters = self.signature_arena.get(signature).parameters.clone();
        let index = parameters
            .iter()
            .position(|&p| self.sym(p).name == name)
            .map(|i| i as i32)
            .unwrap_or(-1);
        self.new_type_predicate(kind, name, index, t)
    }

    /// `(c *Checker) instantiateTypePredicate`.
    pub(crate) fn instantiate_type_predicate(
        &mut self,
        predicate: &TypePredicate,
        mapper: Option<TypeMapperId>,
    ) -> TypePredicate {
        let t = predicate.t.map(|t| self.instantiate_type(t, mapper));
        if t == predicate.t {
            return predicate.clone();
        }
        self.new_type_predicate(
            predicate.kind,
            predicate.parameter_name.clone(),
            predicate.parameter_index,
            t,
        )
    }

    /// `(c *Checker) newTypePredicate`.
    pub(crate) fn new_type_predicate(
        &mut self,
        kind: TypePredicateKind,
        parameter_name: String,
        parameter_index: i32,
        t: Option<TypeId>,
    ) -> TypePredicate {
        TypePredicate {
            kind,
            parameter_index,
            parameter_name,
            t,
        }
    }

    /// `(c *Checker) isResolvingReturnTypeOfSignature`.
    pub(crate) fn is_resolving_return_type_of_signature(&mut self, signature: SignatureId) -> bool {
        {
            let composite = self.signature_arena.get(signature).composite.clone();
            if let Some(composite) = composite {
                if composite
                    .signatures
                    .iter()
                    .any(|&s| self.is_resolving_return_type_of_signature(s))
                {
                    return true;
                }
            }
        }
        self.signature_arena
            .get(signature)
            .resolved_return_type
            .is_none()
            && self.find_resolution_cycle_start_index(
                crate::checker_types::TypeSystemEntity::Signature(signature),
                TypeSystemPropertyName::ResolvedReturnType,
            ) >= 0
    }

    /// `(c *Checker) findMatchingSignatures`.
    pub(crate) fn find_matching_signatures(
        &mut self,
        signature_lists: &[Vec<SignatureId>],
        signature: SignatureId,
        list_index: usize,
    ) -> Option<Vec<SignatureId>> {
        if !self
            .signature_arena
            .get(signature)
            .type_parameters
            .is_empty()
        {
            // We require an exact match for generic signatures, so we only
            // return signatures from the first signature list and only if
            // they have exact matches in the other signature lists.
            if list_index > 0 {
                return None;
            }
            for list in signature_lists.iter().skip(1) {
                if self
                    .find_matching_signature(list, signature, false, false, false)
                    .is_none()
                {
                    return None;
                }
            }
            return Some(vec![signature]);
        }
        let mut result: Vec<SignatureId> = Vec::new();
        for (i, list) in signature_lists.iter().enumerate() {
            // Allow matching non-generic signatures to have excess
            // parameters (as a fallback if exact parameter match is not
            // found) and different return types. Prefer matching this types
            // if possible.
            let mut matched;
            if i == list_index {
                matched = Some(signature);
            } else {
                matched = self.find_matching_signature(list, signature, false, false, true);
                if matched.is_none() {
                    matched = self.find_matching_signature(list, signature, true, false, true);
                }
            }
            let Some(matched) = matched else {
                return None;
            };
            if !result.contains(&matched) {
                result.push(matched);
            }
        }
        Some(result)
    }

    /// `(c *Checker) findMatchingSignature`.
    pub(crate) fn find_matching_signature(
        &mut self,
        signature_list: &[SignatureId],
        signature: SignatureId,
        partial_match: bool,
        ignore_this_types: bool,
        ignore_return_types: bool,
    ) -> Option<SignatureId> {
        let compare_types =
            tsc_core::core::if_else(partial_match, Comparer::SubtypeOf, Comparer::Identical);
        for &s in signature_list {
            if self.compare_signatures_identical(
                s,
                signature,
                partial_match,
                ignore_this_types,
                ignore_return_types,
                compare_types,
                &mut None,
            ) != Ternary::FALSE
            {
                return Some(s);
            }
        }
        None
    }

    /// `(c *Checker) compareSignaturesIdentical` — see `signatureRelatedTo`,
    /// `compareSignaturesIdentical`.
    pub(crate) fn compare_signatures_identical(
        &mut self,
        mut source: SignatureId,
        target: SignatureId,
        partial_match: bool,
        ignore_this_types: bool,
        ignore_return_types: bool,
        compare_types: Comparer,
        reporter: &mut ErrorReporter<'_>,
    ) -> Ternary {
        if source == target {
            return Ternary::TRUE;
        }
        if !self.is_matching_signature(source, target, partial_match) {
            return Ternary::FALSE;
        }
        // Check that the two signatures have the same number of type
        // parameters.
        if self.signature_arena.get(source).type_parameters.len()
            != self.signature_arena.get(target).type_parameters.len()
        {
            return Ternary::FALSE;
        }
        // Check that type parameter constraints and defaults match. If they
        // do, instantiate the source signature with the type parameters of
        // the target signature and continue the comparison.
        let target_params_len = self.signature_arena.get(target).type_parameters.len();
        if target_params_len != 0 {
            let source_params = self.signature_arena.get(source).type_parameters.clone();
            let target_params = self.signature_arena.get(target).type_parameters.clone();
            let mapper =
                crate::mapper::new_type_mapper(self, source_params.clone(), target_params.clone());
            for i in 0..target_params_len {
                let s = source_params[i];
                let t = target_params[i];
                if s == t {
                    continue;
                }
                let s_constraint = self.get_constraint_or_unknown_from_type_parameter(s);
                let instantiated = self.instantiate_type(s_constraint, Some(mapper));
                let t_constraint = self.get_constraint_or_unknown_from_type_parameter(t);
                let s_default = self.get_default_or_unknown_from_type_parameter(s);
                let instantiated_default = self.instantiate_type(s_default, Some(mapper));
                let t_default = self.get_default_or_unknown_from_type_parameter(t);
                if !(compare_via(
                    self,
                    reporter,
                    compare_types,
                    instantiated,
                    t_constraint,
                    false,
                ) != Ternary::FALSE
                    && compare_via(
                        self,
                        reporter,
                        compare_types,
                        instantiated_default,
                        t_default,
                        false,
                    ) != Ternary::FALSE)
                {
                    return Ternary::FALSE;
                }
            }
            source = self.instantiate_signature_ex(source, Some(mapper), true);
        }
        let mut result = Ternary::TRUE;
        if !ignore_this_types {
            let source_this_type = self.get_this_type_of_signature(source);
            if let Some(source_this_type) = source_this_type {
                if let Some(target_this_type) = self.get_this_type_of_signature(target) {
                    let related = compare_via(
                        self,
                        reporter,
                        compare_types,
                        source_this_type,
                        target_this_type,
                        false,
                    );
                    if related == Ternary::FALSE {
                        return Ternary::FALSE;
                    }
                    result = result & related;
                }
            }
        }
        for i in 0..self.get_parameter_count(target) {
            let s = self.get_type_at_position(source, i);
            let t = self.get_type_at_position(target, i);
            let related = compare_via(self, reporter, compare_types, t, s, false);
            if related == Ternary::FALSE {
                return Ternary::FALSE;
            }
            result = result & related;
        }
        if !ignore_return_types {
            let source_type_predicate = self.get_type_predicate_of_signature(source);
            let target_type_predicate = self.get_type_predicate_of_signature(target);
            if source_type_predicate.is_some() || target_type_predicate.is_some() {
                result = result
                    & self.compare_type_predicates_identical(
                        source_type_predicate.as_ref(),
                        target_type_predicate.as_ref(),
                        compare_types,
                    );
            } else {
                let source_return = self.get_return_type_of_signature(source);
                let target_return = self.get_return_type_of_signature(target);
                result = result
                    & compare_via(
                        self,
                        reporter,
                        compare_types,
                        source_return,
                        target_return,
                        false,
                    );
            }
        }
        result
    }

    /// `(c *Checker) isMatchingSignature`.
    fn is_matching_signature(
        &mut self,
        source: SignatureId,
        target: SignatureId,
        partial_match: bool,
    ) -> bool {
        let source_parameter_count = self.get_parameter_count(source);
        let target_parameter_count = self.get_parameter_count(target);
        let source_min_argument_count = self.get_min_argument_count(source);
        let target_min_argument_count = self.get_min_argument_count(target);
        let source_has_rest_parameter = self.has_effective_rest_parameter(source);
        let target_has_rest_parameter = self.has_effective_rest_parameter(target);
        // A source signature matches a target signature if the two
        // signatures have the same number of required, optional, and rest
        // parameters.
        if source_parameter_count == target_parameter_count
            && source_min_argument_count == target_min_argument_count
            && source_has_rest_parameter == target_has_rest_parameter
        {
            return true;
        }
        // A source signature partially matches a target signature if the
        // target signature has no fewer required parameters
        if partial_match && source_min_argument_count <= target_min_argument_count {
            return true;
        }
        false
    }

    /// `(c *Checker) compareTypeParametersIdentical`.
    pub(crate) fn compare_type_parameters_identical(
        &mut self,
        source_params: &[TypeId],
        target_params: &[TypeId],
    ) -> bool {
        if source_params.len() != target_params.len() {
            return false;
        }
        let mapper =
            crate::mapper::new_type_mapper(self, target_params.to_vec(), source_params.to_vec());
        for i in 0..source_params.len() {
            let source = source_params[i];
            let target = target_params[i];
            if source == target {
                continue;
            }
            // We instantiate the target type parameter constraints into the
            // source types so we can recognize `<T, U extends T>` as the
            // same as `<A, B extends A>`
            let source_constraint = self
                .get_constraint_from_type_parameter(source)
                .unwrap_or(self.unknown_type);
            let target_constraint = self
                .get_constraint_from_type_parameter(target)
                .unwrap_or(self.unknown_type);
            let instantiated = self.instantiate_type(target_constraint, Some(mapper));
            if !self.is_type_identical_to(source_constraint, instantiated) {
                return false;
            }
            // We don't compare defaults - we just use the type parameter
            // defaults from the first signature that seems to match. It
            // might make sense to combine these defaults in the future, but
            // doing so intelligently requires knowing if the parameter is
            // used covariantly or contravariantly (so we intersect if it's
            // used like a parameter or union if used like a return type)
            // and, since it's just an inference _default_, just picking one
            // arbitrarily works OK.
        }
        true
    }

    /// `(c *Checker) compareTypePredicatesIdentical`.
    fn compare_type_predicates_identical(
        &mut self,
        source: Option<&TypePredicate>,
        target: Option<&TypePredicate>,
        compare_types: Comparer,
    ) -> Ternary {
        if source.is_none()
            || target.is_none()
            || !self.type_predicate_kinds_match(source.unwrap(), target.unwrap())
        {
            return Ternary::FALSE;
        }
        let source = source.unwrap();
        let target = target.unwrap();
        if source.t == target.t {
            return Ternary::TRUE;
        }
        if source.t.is_some() && target.t.is_some() {
            return compare_via(
                self,
                &mut None,
                compare_types,
                source.t.unwrap(),
                target.t.unwrap(),
                false,
            );
        }
        Ternary::FALSE
    }

    /// `(c *Checker) getEffectiveConstraintOfIntersection`.
    pub(crate) fn get_effective_constraint_of_intersection(
        &mut self,
        types: &[TypeId],
        target_is_union: bool,
    ) -> Option<TypeId> {
        let mut constraints: Vec<TypeId> = Vec::new();
        let mut has_disjoint_domain_type = false;
        for &t in types {
            if self
                .types_handle()
                .get_ref(t)
                .flags
                .intersects(TypeFlags::INSTANTIABLE)
            {
                // We keep following constraints as long as we have an
                // instantiable type that is known not to be circular or
                // infinite (hence we stop on index access types).
                let mut constraint = self.get_constraint_of_type(t);
                while constraint.is_some_and(|con| {
                    self.types_handle().get_ref(con).flags.intersects(
                        TypeFlags::TYPE_PARAMETER | TypeFlags::INDEX | TypeFlags::CONDITIONAL,
                    )
                }) {
                    constraint = self.get_constraint_of_type(constraint.unwrap());
                }
                if let Some(constraint) = constraint {
                    constraints.push(constraint);
                    if target_is_union {
                        constraints.push(t);
                    }
                }
            } else if self
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::DISJOINT_DOMAINS)
                || self.is_empty_anonymous_object_type(t)
            {
                has_disjoint_domain_type = true;
            }
        }
        // If the target is a union type or if we are intersecting with types
        // belonging to one of the disjoint domains, we may end up producing
        // a constraint that hasn't been examined before.
        if !constraints.is_empty() && (target_is_union || has_disjoint_domain_type) {
            if has_disjoint_domain_type {
                // We add any types belong to one of the disjoint domains
                // because they might cause the final intersection operation
                // to reduce the union constraints.
                for &t in types {
                    if self
                        .types_handle()
                        .get(t)
                        .flags
                        .intersects(TypeFlags::DISJOINT_DOMAINS)
                        || self.is_empty_anonymous_object_type(t)
                    {
                        constraints.push(t);
                    }
                }
            }
            // The source types were normalized; ensure the result is
            // normalized too.
            let intersection = self.get_intersection_type_ex(
                &constraints,
                crate::checker_types::IntersectionFlags::NO_CONSTRAINT_REDUCTION,
                None,
            );
            return Some(self.get_normalized_type(intersection, false));
        }
        None
    }

    /// `(c *Checker) templateLiteralTypesDefinitelyUnrelated` — two
    /// template literal types with differences in their starting or ending
    /// text spans are definitely unrelated.
    fn template_literal_types_definitely_unrelated(
        source: &crate::types::TemplateLiteralType,
        target: &crate::types::TemplateLiteralType,
    ) -> bool {
        let source_start = &source.texts[0];
        let target_start = &target.texts[0];
        let source_end = &source.texts[source.texts.len() - 1];
        let target_end = &target.texts[target.texts.len() - 1];
        let start_len = std::cmp::min(source_start.len(), target_start.len());
        let end_len = std::cmp::min(source_end.len(), target_end.len());
        source_start[..start_len] != target_start[..start_len]
            || source_end[source_end.len() - end_len..] != target_end[target_end.len() - end_len..]
    }

    /// `(c *Checker) isTypeMatchedByTemplateLiteralType`.
    pub(crate) fn is_type_matched_by_template_literal_type(
        &mut self,
        source: TypeId,
        target: TypeId,
        mut r: ErrorReporter<'_>,
        compare_types: Comparer,
    ) -> bool {
        // `(*x).clone()` — `as_template_literal_type` returns a reference
        // into the arena guard; dereference before cloning to get an owned
        // `TemplateLiteralType` snapshot (Go reads `target.AsTemplateLiteralType()`).
        let target_data = (*self.types_handle().get_ref(target).as_template_literal_type()).clone();
        let inferences = self.infer_types_from_template_literal_type(
            source,
            &target_data,
            &mut r,
            compare_types,
        );
        if let Some(inferences) = inferences {
            for (i, inference) in inferences.iter().enumerate() {
                if !self.is_valid_type_for_template_literal_placeholder(
                    *inference,
                    target_data.types[i],
                    &mut r,
                    compare_types,
                ) {
                    return false;
                }
            }
            return true;
        }
        false
    }

    /// `(c *Checker) inferTypesFromTemplateLiteralType`.
    /// PORT(visibility): widened to `pub(crate)` for inference.rs.
    pub(crate) fn infer_types_from_template_literal_type(
        &mut self,
        source: TypeId,
        target: &crate::types::TemplateLiteralType,
        r: &mut ErrorReporter<'_>,
        compare_types: Comparer,
    ) -> Option<Vec<TypeId>> {
        let __arena_flags = self.types.clone();
        let flags = __arena_flags.get_ref(source).flags;
        if flags.intersects(TypeFlags::STRING_LITERAL) {
            let value = crate::checker_d::get_string_literal_value(&self.types, source);
            return self.infer_from_literal_parts_to_template_literal(&[value], &[], target);
        }
        if flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            let (texts, types) = {
                let __arena___guard_st = self.types.clone();
                let __guard_st = __arena___guard_st.get(source).clone();
                let st = __guard_st.as_template_literal_type();
                (st.texts.clone(), st.types.clone())
            };
            if texts == target.texts {
                let mut result = Vec::with_capacity(types.len());
                for (i, s) in types.iter().enumerate() {
                    let s_base = self.get_base_constraint_or_type(*s);
                    let t_base = self.get_base_constraint_or_type(target.types[i]);
                    if compare_via(self, r, compare_types, s_base, t_base, false)
                        != Ternary::FALSE
                    {
                        result.push(*s);
                    } else {
                        result.push(self.get_string_like_type_for_type(*s));
                    }
                }
                return Some(result);
            }
            return self.infer_from_literal_parts_to_template_literal(&texts, &types, target);
        }
        None
    }

    /// `(c *Checker) inferFromLiteralPartsToTemplateLiteral` — infers from
    /// the text parts and type parts of a source literal to a target
    /// template literal. The number of text parts is always one more than
    /// the number of type parts, and a source string literal is treated as
    /// a source with one text part and zero type parts. Returns an array of
    /// inferred string or template literal types corresponding to the
    /// placeholders in the target template literal, or `None` if the source
    /// doesn't match the target.
    fn infer_from_literal_parts_to_template_literal(
        &mut self,
        source_texts: &[String],
        source_types: &[TypeId],
        target: &crate::types::TemplateLiteralType,
    ) -> Option<Vec<TypeId>> {
        let last_source_index = source_texts.len() - 1;
        let source_start_text = &source_texts[0];
        let source_end_text = &source_texts[last_source_index];
        let target_texts = &target.texts;
        let last_target_index = target_texts.len() - 1;
        let target_start_text = &target_texts[0];
        let target_end_text = &target_texts[last_target_index];
        if last_source_index == 0
            && source_start_text.len() < target_start_text.len() + target_end_text.len()
            || !source_start_text.starts_with(target_start_text.as_str())
            || !source_end_text.ends_with(target_end_text.as_str())
        {
            return None;
        }
        let remaining_end_text =
            source_end_text[..source_end_text.len() - target_end_text.len()].to_string();
        let mut seg = 0usize;
        let mut pos = target_start_text.len();
        let mut matches: Vec<TypeId> = Vec::new();
        let get_source_text = |index: usize| -> &str {
            if index < last_source_index {
                source_texts[index].as_str()
            } else {
                remaining_end_text.as_str()
            }
        };
        // `addMatch(s, p)` as a macro — needs `&mut self` plus the mutable
        // `seg`/`pos`/`matches`.
        macro_rules! add_match {
            ($self_:ident, $s:expr, $p:expr) => {{
                let s_ = $s;
                let p_ = $p;
                let match_type;
                if s_ == seg {
                    // PORT: `getStringLiteralType` takes `&str` — lone
                    // surrogate sentinels (invalid UTF-8) degrade via
                    // from_utf8_lossy; the decode step above still consumes
                    // whole code points exactly like Go.
                    let text = String::from_utf8_lossy(&tsc_stringutil::combine_surrogate_pairs(
                        get_source_text(s_)[pos..p_].as_bytes(),
                    ))
                    .into_owned();
                    match_type = $self_.get_string_literal_type(&text);
                } else {
                    let mut match_texts = vec![String::new(); s_ - seg + 1];
                    match_texts[0] = source_texts[seg][pos..].to_string();
                    match_texts[1..s_ - seg].clone_from_slice(&source_texts[seg + 1..s_]);
                    match_texts[s_ - seg] = get_source_text(s_)[..p_].to_string();
                    match_type =
                        $self_.get_template_literal_type(&match_texts, &source_types[seg..s_]);
                }
                matches.push(match_type);
                seg = s_;
                pos = p_;
            }};
        }
        for i in 1..last_target_index {
            let delim = &target_texts[i];
            if !delim.is_empty() {
                let mut s = seg;
                let mut p = pos;
                loop {
                    if let Some(d) = get_source_text(s)[p..].find(delim.as_str()) {
                        p += d;
                        break;
                    }
                    s += 1;
                    if s == source_texts.len() {
                        return None;
                    }
                    p = 0;
                }
                add_match!(self, s, p);
                pos += delim.len();
            } else {
                let source_text = get_source_text(seg).to_string();
                if pos < source_text.len() {
                    // Consume one code point at a time, matching the string
                    // iterator (`[x, ..._] = s`) rather than UTF-16
                    // code-unit indexing (`s[0]`). DecodeJSStringRune is
                    // required rather than utf8.DecodeRuneInString because
                    // a lone surrogate is stored as an invalid-UTF-8
                    // sentinel; utf8 would treat that as an error and
                    // advance a single byte, breaking the sentinel into
                    // stray bytes, whereas DecodeJSStringRune pulls the
                    // whole sentinel off as one code point.
                    let (_, size) =
                        tsc_stringutil::decode_js_string_rune(source_text[pos..].as_bytes());
                    add_match!(self, seg, pos + size);
                } else if seg < last_source_index {
                    add_match!(self, seg + 1, 0);
                } else {
                    return None;
                }
            }
        }
        let last_len = get_source_text(last_source_index).len();
        add_match!(self, last_source_index, last_len);
        Some(matches)
    }

    /// `(c *Checker) getStringLikeTypeForType`.
    fn get_string_like_type_for_type(&mut self, t: TypeId) -> TypeId {
        if self
            .types_handle()
            .get_ref(t)
            .flags
            .intersects(TypeFlags::ANY | TypeFlags::STRING_LIKE)
        {
            return t;
        }
        self.get_template_literal_type(&[String::new(), String::new()], &[t])
    }

    /// `(c *Checker) isValidTypeForTemplateLiteralPlaceholder`.
    fn is_valid_type_for_template_literal_placeholder(
        &mut self,
        source: TypeId,
        target: TypeId,
        r: &mut ErrorReporter<'_>,
        compare_types: Comparer,
    ) -> bool {
        let (source_flags, target_flags) = {
            let __arena_s = self.types.clone();
            let s = __arena_s.get_ref(source);
            let __arena_t = self.types.clone();
            let t = __arena_t.get_ref(target);
            (s.flags, t.flags)
        };
        if target_flags.intersects(TypeFlags::INTERSECTION) {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(target).types().to_vec();
            return types.iter().all(|&t| {
                t == self.empty_type_literal_type
                    || self.is_valid_type_for_template_literal_placeholder(
                        source,
                        t,
                        r,
                        compare_types,
                    )
            });
        }
        if target_flags.intersects(TypeFlags::STRING)
            || compare_via(self, r, compare_types, source, target, false) != Ternary::FALSE
        {
            return true;
        }
        if source_flags.intersects(TypeFlags::STRING_LITERAL) {
            let value = crate::checker_d::get_string_literal_value(&self.types, source);
            return target_flags.intersects(TypeFlags::NUMBER)
                && crate::utilities::is_valid_number_string(&value, false)
                || target_flags.intersects(TypeFlags::BIG_INT)
                    && crate::utilities::is_valid_big_int_string(&value, false)
                || target_flags.intersects(TypeFlags::BOOLEAN_LITERAL | TypeFlags::NULLABLE)
                    && value
                        == self
                            .types_handle()
                            .get(target)
                            .as_intrinsic_type()
                            .intrinsic_name
                || target_flags.intersects(TypeFlags::STRING_MAPPING)
                    && self.is_member_of_string_mapping(source, target)
                || target_flags.intersects(TypeFlags::TEMPLATE_LITERAL)
                    && self.is_type_matched_by_template_literal_type(
                        source,
                        target,
                        r.as_deref_mut(),
                        compare_types,
                    );
        }
        if source_flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            let (texts, types) = {
                let __arena___guard_st = self.types.clone();
                let __guard_st = __arena___guard_st.get(source).clone();
                let st = __guard_st.as_template_literal_type();
                (st.texts.clone(), st.types.clone())
            };
            return texts.len() == 2
                && texts[0].is_empty()
                && texts[1].is_empty()
                && compare_via(self, r, compare_types, types[0], target, false)
                    != Ternary::FALSE;
        }
        false
    }

    /// `(c *Checker) isMemberOfStringMapping`.
    pub(crate) fn is_member_of_string_mapping(&mut self, source: TypeId, target: TypeId) -> bool {
        let __arena_target_flags = self.types.clone();
        let target_flags = __arena_target_flags.get_ref(target).flags;
        if target_flags.intersects(TypeFlags::ANY) {
            return true;
        }
        if target_flags.intersects(TypeFlags::STRING | TypeFlags::TEMPLATE_LITERAL) {
            return self.is_type_assignable_to(source, target);
        }
        if target_flags.intersects(TypeFlags::STRING_MAPPING) {
            // We need to see whether applying the same mappings of the
            // target onto the source would produce an identical type *and*
            // that it's compatible with the inner-most non-string-mapped
            // type.
            //
            // The intuition here is that if same mappings don't affect the
            // source at all, and the source is compatible with the unmapped
            // target, then they must still reside in the same domain.
            let (mapped, inner) = self.apply_target_string_mapping_to_source(source, target);
            return mapped == source && self.is_member_of_string_mapping(source, inner);
        }
        false
    }

    /// `(c *Checker) applyTargetStringMappingToSource`.
    fn apply_target_string_mapping_to_source(
        &mut self,
        source: TypeId,
        target: TypeId,
    ) -> (TypeId, TypeId) {
        let mut source = source;
        let __arena_inner = self.types.clone();
        let mut inner = __arena_inner
            .get_ref(target)
            .as_string_mapping_type()
            .target
            .expect("string mapping target");
        if self
            .types_handle()
            .get_ref(inner)
            .flags
            .intersects(TypeFlags::STRING_MAPPING)
        {
            (source, inner) = self.apply_target_string_mapping_to_source(source, inner);
        }
        let __arena_symbol = self.types.clone();
        let symbol = __arena_symbol.get_ref(target).symbol;
        (self.get_string_mapping_type(symbol, source), inner)
    }
}

/// `visibilityToString` (relater.go).
pub(crate) fn visibility_to_string(flags: ast::ModifierFlags) -> &'static str {
    if flags == ast::ModifierFlags::PRIVATE {
        return "private";
    }
    if flags == ast::ModifierFlags::PROTECTED {
        return "protected";
    }
    "public"
}

impl Checker {
    /// `(c *Checker) getRelater`.
    fn get_relater(&mut self) -> Box<Relater> {
        let mut r = self
            .free_relater
            .take()
            .unwrap_or_else(|| Box::new(Relater::default()));
        self.free_relater = r.next.take();
        r
    }

    /// `(c *Checker) putRelater` — keeps `maybeKeys`/`maybeKeysSet`/
    /// `sourceStack`/`targetStack` backing storage like Go's `[:0]` reuse.
    fn put_relater(&mut self, mut r: Box<Relater>) {
        let mut reused = Relater::default();
        r.maybe_keys_set.clear();
        reused.maybe_keys = std::mem::take(&mut r.maybe_keys);
        reused.maybe_keys.clear();
        reused.maybe_keys_set = std::mem::take(&mut r.maybe_keys_set);
        reused.source_stack = std::mem::take(&mut r.source_stack);
        reused.source_stack.clear();
        reused.target_stack = std::mem::take(&mut r.target_stack);
        reused.target_stack.clear();
        reused.next = self.free_relater.take();
        *r = reused;
        self.free_relater = Some(r);
    }
}

impl Relater {
    /// `(r *Relater) isRelatedToSimple`.
    pub(crate) fn is_related_to_simple(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
    ) -> Ternary {
        self.is_related_to_ex(
            c,
            source,
            target,
            RecursionFlags::BOTH,
            false,
            None,
            IntersectionState::NONE,
        )
    }

    /// `(r *Relater) isRelatedToWorker`.
    pub(crate) fn is_related_to_worker(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
    ) -> Ternary {
        self.is_related_to_ex(
            c,
            source,
            target,
            RecursionFlags::BOTH,
            report_errors,
            None,
            IntersectionState::NONE,
        )
    }

    /// `(r *Relater) isRelatedTo`.
    pub(crate) fn is_related_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        recursion_flags: RecursionFlags,
        report_errors: bool,
    ) -> Ternary {
        self.is_related_to_ex(
            c,
            source,
            target,
            recursion_flags,
            report_errors,
            None,
            IntersectionState::NONE,
        )
    }

    /// `(r *Relater) isRelatedToEx`.
    pub(crate) fn is_related_to_ex(
        &mut self,
        c: &mut Checker,
        original_source: TypeId,
        original_target: TypeId,
        recursion_flags: RecursionFlags,
        report_errors: bool,
        head_message: Option<&'static tsc_diagnostics::Message>,
        intersection_state: IntersectionState,
    ) -> Ternary {
        if original_source == original_target {
            return Ternary::TRUE;
        }
        let (original_source_flags, original_target_flags, original_target_alias) = {
            let __arena_s = c.types.clone();
            let s = __arena_s.get_ref(original_source);
            let __arena_t = c.types.clone();
            let t = __arena_t.get_ref(original_target);
            (s.flags, t.flags, t.alias.is_some())
        };
        // Before normalization: if `source` is type an object type, and
        // `target` is primitive, skip all the checks we don't need and just
        // return `isSimpleTypeRelatedTo` result
        if original_source_flags.intersects(TypeFlags::OBJECT)
            && original_target_flags.intersects(TypeFlags::PRIMITIVE)
        {
            let relation = self.relation();
            if Rc::ptr_eq(&relation, &c.comparable_relation)
                && !original_target_flags.intersects(TypeFlags::NEVER)
                && c.is_simple_type_related_to(original_target, original_source, &relation, None)
                || c.is_simple_type_related_to(
                    original_source,
                    original_target,
                    &relation,
                    if report_errors {
                        Some(&mut *self)
                    } else {
                        None
                    },
                )
            {
                return Ternary::TRUE;
            }
            if report_errors {
                self.report_error_results(
                    c,
                    original_source,
                    original_target,
                    original_source,
                    original_target,
                    head_message,
                );
            }
            return Ternary::FALSE;
        }
        // Normalize the source and target types: Turn fresh literal types
        // into regular literal types, turn deferred type references into
        // regular type references, simplify indexed access and conditional
        // types, and resolve substitution types to either the substitution
        // (on the source side) or the type variable (on the target side).
        let source = c.get_normalized_type(original_source, false);
        let mut target = c.get_normalized_type(original_target, true);
        if source == target {
            return Ternary::TRUE;
        }
        if Rc::ptr_eq(&self.relation(), &c.identity_relation) {
            let (source_flags, target_flags) = {
                let __arena_s = c.types.clone();
                let s = __arena_s.get_ref(source);
                (s.flags, c.types_handle().get_ref(target).flags)
            };
            if source_flags != target_flags {
                return Ternary::FALSE;
            }
            if source_flags.intersects(TypeFlags::SINGLETON) {
                return Ternary::TRUE;
            }
            self.trace_unions_or_intersections_too_large(c, source, target);
            return self.recursive_type_related_to(
                c,
                source,
                target,
                false,
                IntersectionState::NONE,
                recursion_flags,
            );
        }
        // We fastpath comparing a type parameter to exactly its constraint,
        // as this is _super_ common, and otherwise, for type parameters in
        // large unions, causes us to need to compare the union to itself, as
        // we break down the _target_ union first, _then_ get the source
        // constraint - so for every member of the target, we attempt to find
        // a match in the source. This avoids that in cases where the target
        // is exactly the constraint.
        if c.types_handle()
            .get(source)
            .flags
            .intersects(TypeFlags::TYPE_PARAMETER)
            && c.get_constraint_of_type(source) == Some(target)
        {
            return Ternary::TRUE;
        }
        // See if we're relating a definitely non-nullable type to a union
        // that includes null and/or undefined plus a single non-nullable
        // type. If so, remove null and/or undefined from the target type.
        {
            let (source_flags, target_flags) = {
                let __arena_s = c.types.clone();
                let s = __arena_s.get_ref(source);
                (s.flags, c.types_handle().get_ref(target).flags)
            };
            if source_flags.intersects(TypeFlags::DEFINITELY_NON_NULLABLE)
                && target_flags.intersects(TypeFlags::UNION)
            {
                let __arena_types = c.types.clone();
                let types = __arena_types.get_ref(target).types().to_vec();
                let mut candidate: Option<TypeId> = None;
                if types.len() == 2
                    && c.types_handle()
                        .get(types[0])
                        .flags
                        .intersects(TypeFlags::NULLABLE)
                {
                    candidate = Some(types[1]);
                } else if types.len() == 3
                    && c.types_handle()
                        .get(types[0])
                        .flags
                        .intersects(TypeFlags::NULLABLE)
                    && c.types_handle()
                        .get(types[1])
                        .flags
                        .intersects(TypeFlags::NULLABLE)
                {
                    candidate = Some(types[2]);
                }
                if candidate.is_some_and(|cand| {
                    !c.types_handle()
                        .get(cand)
                        .flags
                        .intersects(TypeFlags::NULLABLE)
                }) {
                    target = c.get_normalized_type(candidate.unwrap(), true);
                    if source == target {
                        return Ternary::TRUE;
                    }
                }
            }
        }
        {
            let relation = self.relation();
            let __arena_target_flags = c.types.clone();
            let target_flags = __arena_target_flags.get_ref(target).flags;
            if Rc::ptr_eq(&relation, &c.comparable_relation)
                && !target_flags.intersects(TypeFlags::NEVER)
                && c.is_simple_type_related_to(target, source, &relation, None)
                || c.is_simple_type_related_to(
                    source,
                    target,
                    &relation,
                    if report_errors {
                        Some(&mut *self)
                    } else {
                        None
                    },
                )
            {
                return Ternary::TRUE;
            }
        }
        let (source_flags, target_flags) = {
            let __arena_s = c.types.clone();
            let s = __arena_s.get_ref(source);
            (s.flags, c.types_handle().get_ref(target).flags)
        };
        if source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
            || target_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE)
        {
            let is_performing_excess_property_checks = !intersection_state
                .intersects(IntersectionState::TARGET)
                && crate::utilities::is_object_literal_type(&c.types, source)
                && c.types_handle()
                    .get(source)
                    .object_flags
                    .intersects(ObjectFlags::FRESH_LITERAL);
            if is_performing_excess_property_checks {
                if self.has_excess_properties(c, source, target, report_errors) {
                    if report_errors {
                        self.report_relation_error(
                            c,
                            head_message,
                            source,
                            if original_target_alias {
                                original_target
                            } else {
                                target
                            },
                        );
                    }
                    return Ternary::FALSE;
                }
            }
            let is_performing_common_property_checks =
                (!Rc::ptr_eq(&self.relation(), &c.comparable_relation)
                    || crate::checker_d::is_unit_type(&c.types, source))
                    && !intersection_state.intersects(IntersectionState::TARGET)
                    && source_flags.intersects(
                        TypeFlags::PRIMITIVE | TypeFlags::OBJECT | TypeFlags::INTERSECTION,
                    )
                    && source != c.global_object_type
                    && target_flags.intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION)
                    && c.is_weak_type(target)
                    && (!c.get_properties_of_type(source).is_empty()
                        || c.type_has_call_or_construct_signatures(source));
            let __arena_is_comparing_jsx_attributes = c.types.clone();
            let is_comparing_jsx_attributes = __arena_is_comparing_jsx_attributes
                .get_ref(source)
                .object_flags
                .intersects(ObjectFlags::JSX_ATTRIBUTES);
            if is_performing_common_property_checks
                && !c.has_common_properties(source, target, is_comparing_jsx_attributes)
            {
                if report_errors {
                    let source_string = c.type_to_string(
                        if c.types_handle().get(original_source).alias.is_some() {
                            original_source
                        } else {
                            source
                        },
                    );
                    let target_string = c.type_to_string(if original_target_alias {
                        original_target
                    } else {
                        target
                    });
                    let calls = c.get_signatures_of_type(source, SignatureKind::Call);
                    let constructs = c.get_signatures_of_type(source, SignatureKind::Construct);
                    let call_related = !calls.is_empty() && {
                        let rt = c.get_return_type_of_signature(calls[0]);
                        self.is_related_to(c, rt, target, RecursionFlags::SOURCE, false)
                            != Ternary::FALSE
                    };
                    let construct_related = !constructs.is_empty() && {
                        let rt = c.get_return_type_of_signature(constructs[0]);
                        self.is_related_to(c, rt, target, RecursionFlags::SOURCE, false)
                            != Ternary::FALSE
                    };
                    if call_related || construct_related {
                        self.report_error(
                            c,
                            &tsc_diagnostics::Value_of_type_0_has_no_properties_in_common_with_type_1_Did_you_mean_to_call_it,
                            &[source_string, target_string],
                        );
                    } else {
                        self.report_error(
                            c,
                            &tsc_diagnostics::Type_0_has_no_properties_in_common_with_type_1,
                            &[source_string, target_string],
                        );
                    }
                }
                return Ternary::FALSE;
            }
            self.trace_unions_or_intersections_too_large(c, source, target);
            let skip_caching = source_flags.intersects(TypeFlags::UNION)
                && c.types_handle().get_ref(source).types().len() < 4
                && !target_flags.intersects(TypeFlags::UNION)
                || target_flags.intersects(TypeFlags::UNION)
                    && c.types_handle().get_ref(target).types().len() < 4
                    && !source_flags.intersects(TypeFlags::STRUCTURED_OR_INSTANTIABLE);
            let result;
            if skip_caching {
                result = self.union_or_intersection_related_to(
                    c,
                    source,
                    target,
                    report_errors,
                    intersection_state,
                );
            } else {
                result = self.recursive_type_related_to(
                    c,
                    source,
                    target,
                    report_errors,
                    intersection_state,
                    recursion_flags,
                );
            }
            if result != Ternary::FALSE {
                return result;
            }
        }
        if report_errors {
            self.report_error_results(
                c,
                original_source,
                original_target,
                source,
                target,
                head_message,
            );
        }
        Ternary::FALSE
    }

    /// `(r *Relater) hasExcessProperties`.
    fn has_excess_properties(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
    ) -> bool {
        if !is_excess_property_check_target(&c.types, target)
            || !c.no_implicit_any
                && c.types_handle()
                    .get(target)
                    .object_flags
                    .intersects(ObjectFlags::JS_LITERAL)
        {
            // Disable excess property checks on JS literals to simulate
            // having an implicit "index signature" - but only outside of
            // noImplicitAny
            return false;
        }
        let __arena_is_comparing_jsx_attributes = c.types.clone();
        let is_comparing_jsx_attributes = __arena_is_comparing_jsx_attributes
            .get_ref(source)
            .object_flags
            .intersects(ObjectFlags::JSX_ATTRIBUTES);
        if (Rc::ptr_eq(&self.relation(), &c.assignable_relation)
            || Rc::ptr_eq(&self.relation(), &c.comparable_relation))
            && (c.is_type_subset_of(c.global_object_type, target)
                || (!is_comparing_jsx_attributes && c.is_empty_object_type(target)))
        {
            return false;
        }
        let mut reduced_target = target;
        let mut check_types: Option<Vec<TypeId>> = None;
        if c.types_handle()
            .get_ref(target)
            .flags
            .intersects(TypeFlags::UNION)
        {
            reduced_target = c
                .find_matching_discriminant_type(
                    source,
                    target,
                    Some(&mut *self),
                    Comparer::IsRelatedToSimple,
                )
                .unwrap_or_else(|| c.filter_primitives_if_contains_non_primitive(target));
            check_types = Some(
                c.types_handle()
                    .get(reduced_target)
                    .distributed(reduced_target),
            );
        }
        for prop in c.get_properties_of_type(source) {
            let __arena_source_symbol = c.types.clone();
            let source_symbol = __arena_source_symbol.get_ref(source).symbol;
            let prop_name = c.sym_name_rc(prop);
            if should_check_as_excess_property(c, prop, source_symbol)
                && !is_ignored_jsx_property(c, source, prop)
            {
                if !c.is_known_property(reduced_target, &prop_name, is_comparing_jsx_attributes) {
                    if report_errors {
                        // Report error in terms of object types in the target
                        // as those are the only ones we check in
                        // isKnownProperty.
                        let error_target =
                            c.filter_type(reduced_target, &mut |c: &mut Checker, t: TypeId| {
                                is_excess_property_check_target(&c.types, t)
                            });
                        // We know *exactly* where things went wrong when
                        // comparing the types. Use this property as the
                        // error node as this will be more helpful in
                        // reasoning about what went wrong.
                        let mut error_node = self
                            .error_node
                            .expect("No errorNode in hasExcessProperties");
                        let __program = c.program.clone().expect("program");
                        let nodes = __program.nodes((error_node).file_index());
                        if ast::is_jsx_attributes(&nodes[error_node])
                            || ast::is_jsx_opening_like_element(&nodes[error_node])
                            || nodes[error_node]
                                .parent
                                .is_some_and(|p| ast::is_jsx_opening_like_element(&nodes[p]))
                        {
                            // JsxAttributes has an object-literal flag and
                            // undergo same type-assignablity check as normal
                            // object-literal. However, using an
                            // object-literal error message will be very
                            // confusing to the users so we give different a
                            // message.
                            let decl_vd = { c.sym(prop).value_declaration };
                            if let Some(decl) = decl_vd {
                                let __program = c.program.clone().expect("program");
                                let decl_nodes = __program.nodes((decl).file_index());
                                if ast::is_jsx_attribute(&decl_nodes[decl]) {
                                    let name_node = decl_nodes[decl].name();
                                    let same_file =
                                        ast::get_source_file_of_node(Some(error_node), &nodes)
                                            == name_node.and_then(|n| {
                                                ast::get_source_file_of_node(Some(n), &decl_nodes)
                                            });
                                    if same_file {
                                        // Note that extraneous children (as
                                        // in `<NoChild>extra</NoChild>`)
                                        // don't pass this check, since
                                        // `children` is a
                                        // Kind.PropertySignature instead of
                                        // a Kind.JsxAttribute.
                                        if let Some(name_node) = name_node {
                                            error_node = name_node;
                                            self.error_node = Some(error_node);
                                        }
                                    }
                                }
                            }
                            let prop_name = c.symbol_to_string(prop);
                            let suggestion_symbol = c
                                .get_suggested_symbol_for_nonexistent_jsx_attribute(
                                    &prop_name,
                                    error_target,
                                );
                            if let Some(suggestion_symbol) = suggestion_symbol {
                                let target_str = c.type_to_string(error_target);
                                let suggestion_str = c.symbol_to_string(suggestion_symbol);
                                self.report_error(
                                    c,
                                    &tsc_diagnostics::Property_0_does_not_exist_on_type_1_Did_you_mean_2,
                                    &[prop_name, target_str, suggestion_str],
                                );
                            } else {
                                let target_str = c.type_to_string(error_target);
                                self.report_error(
                                    c,
                                    &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                                    &[prop_name, target_str],
                                );
                            }
                        } else {
                            // use the property's value declaration if the
                            // property is assigned inside the literal itself
                            let mut object_literal_declaration: Option<NodeId> = None;
                            if let Some(symbol) = source_symbol {
                                object_literal_declaration =
                                    c.sym(symbol).declarations.clone().first().copied();
                            }
                            let mut suggestion = String::new();
                            let decl_vd = { c.sym(prop).value_declaration };
                            if let Some(decl) = decl_vd {
                                let __program = c.program.clone().expect("program");
                                let decl_nodes = __program.nodes((decl).file_index());
                                if ast::is_object_literal_element(&decl_nodes[decl])
                                    && ast::find_ancestor(Some(decl), &decl_nodes, &mut |d, _| {
                                        Some(d.id) == object_literal_declaration
                                    })
                                    .is_some()
                                    && ast::get_source_file_of_node(
                                        object_literal_declaration,
                                        &decl_nodes,
                                    ) == ast::get_source_file_of_node(Some(error_node), &nodes)
                                {
                                    if let Some(name) = decl_nodes[decl].name() {
                                        error_node = name;
                                        self.error_node = Some(error_node);
                                        if ast::is_identifier(&decl_nodes[name]) {
                                            suggestion = c.get_suggestion_for_nonexistent_property(
                                                decl_nodes[name].text(&decl_nodes).as_ref(),
                                                error_target,
                                            );
                                        }
                                    }
                                }
                            }
                            if !suggestion.is_empty() {
                                let prop_str = c.symbol_to_string(prop);
                                let target_str = c.type_to_string(error_target);
                                self.report_error(
                                    c,
                                    &tsc_diagnostics::Object_literal_may_only_specify_known_properties_but_0_does_not_exist_in_type_1_Did_you_mean_to_write_2,
                                    &[prop_str, target_str, suggestion],
                                );
                            } else {
                                let prop_str = c.symbol_to_string(prop);
                                let target_str = c.type_to_string(error_target);
                                self.report_error(
                                    c,
                                    &tsc_diagnostics::Object_literal_may_only_specify_known_properties_and_0_does_not_exist_in_type_1,
                                    &[prop_str, target_str],
                                );
                            }
                        }
                    }
                    return true;
                }
                if let Some(check_types) = &check_types {
                    let source_prop_type = c.get_type_of_symbol(prop);
                    let target_prop_type = c.get_type_of_property_in_types(check_types, &prop_name);
                    if self.is_related_to(
                        c,
                        source_prop_type,
                        target_prop_type,
                        RecursionFlags::BOTH,
                        report_errors,
                    ) == Ternary::FALSE
                    {
                        if report_errors {
                            let prop_str = c.symbol_to_string(prop);
                            self.report_error(
                                c,
                                &tsc_diagnostics::Types_of_property_0_are_incompatible,
                                &[prop_str],
                            );
                        }
                        return true;
                    }
                }
            }
        }
        false
    }
}

impl Checker {
    /// `(c *Checker) getTypeOfPropertyInTypes`.
    pub(crate) fn get_type_of_property_in_types(&mut self, types: &[TypeId], name: &str) -> TypeId {
        let mut prop_types = Vec::with_capacity(types.len());
        for &t in types {
            prop_types.push(self.get_type_of_property_in_type(t, name));
        }
        self.get_union_type(&prop_types)
    }

    /// `(c *Checker) getTypeOfPropertyInType`.
    fn get_type_of_property_in_type(&mut self, t: TypeId, name: &str) -> TypeId {
        let t = self.get_apparent_type(t);
        let prop;
        if self
            .types_handle()
            .get_ref(t)
            .flags
            .intersects(TypeFlags::UNION_OR_INTERSECTION)
        {
            prop = self.get_property_of_union_or_intersection_type(t, name, false);
        } else {
            prop = self.get_property_of_object_type(t, name);
        }
        if let Some(prop) = prop {
            return self.get_type_of_symbol(prop);
        }
        if let Some(index_info) = self.get_applicable_index_info_for_name(t, name) {
            return self
                .index_info_arena
                .get(index_info)
                .value_type
                .unwrap_or(self.undefined_type);
        }
        self.undefined_type
    }

    /// `(c *Checker) isTypeSubsetOf`.
    pub(crate) fn is_type_subset_of(&mut self, source: TypeId, target: TypeId) -> bool {
        source == target
            || self
                .types_handle()
                .get(source)
                .flags
                .intersects(TypeFlags::NEVER)
            || self
                .types_handle()
                .get(target)
                .flags
                .intersects(TypeFlags::UNION)
                && self.is_type_subset_of_union(source, target)
    }

    /// `(c *Checker) isTypeSubsetOfUnion`.
    pub(crate) fn is_type_subset_of_union(&mut self, source: TypeId, target: TypeId) -> bool {
        let __arena_source_flags = self.types.clone();
        let source_flags = __arena_source_flags.get_ref(source).flags;
        if source_flags.intersects(TypeFlags::UNION) {
            let __arena_source_types = self.types.clone();
            let source_types = __arena_source_types.get_ref(source).types().to_vec();
            let __arena_target_types = self.types.clone();
            let target_types = __arena_target_types.get_ref(target).types().to_vec();
            for t in source_types {
                if !target_types.contains(&t) {
                    return false;
                }
            }
            return true;
        }
        if source_flags.intersects(TypeFlags::ENUM_LIKE)
            && self.get_base_type_of_enum_like_type(source) == target
        {
            return true;
        }
        self.types_handle().get_ref(target).types().contains(&source)
    }
}

/// `shouldCheckAsExcessProperty` (relater.go).
fn should_check_as_excess_property(
    c: &Checker,
    prop: SymbolId,
    container: Option<SymbolId>,
) -> bool {
    let prop_decl = c.sym(prop).value_declaration;
    let container_decl = container.and_then(|s| c.sym(s).value_declaration);
    prop_decl.is_some() && container_decl.is_some() && {
        let __program = c.program.clone().expect("program");
        let nodes = __program.nodes((prop_decl.unwrap()).file_index());
        nodes[prop_decl.unwrap()].parent == container_decl
    }
}

/// `isIgnoredJsxProperty` (relater.go).
fn is_ignored_jsx_property(c: &Checker, source: TypeId, source_prop: SymbolId) -> bool {
    c.types_handle()
        .get(source)
        .object_flags
        .intersects(ObjectFlags::JSX_ATTRIBUTES)
        && is_hyphenated_jsx_name(&c.sym(source_prop).name)
}

impl Relater {
    /// `(r *Relater) unionOrIntersectionRelatedTo`.
    fn union_or_intersection_related_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        // Note that these checks are specifically ordered to produce correct
        // results. In particular, we need to deconstruct unions before
        // intersections (because unions are always at the top), and we need
        // to handle "each" relations before "some" relations for the same
        // kind of type.
        let mut source = source;
        let (mut source_flags, target_flags) = {
            let __arena_s = c.types.clone();
            let s = __arena_s.get_ref(source);
            (s.flags, c.types_handle().get_ref(target).flags)
        };
        if source_flags.intersects(TypeFlags::UNION) {
            if target_flags.intersects(TypeFlags::UNION) {
                // Intersections of union types are normalized into unions of
                // intersection types, and such normalized unions can get very
                // large and expensive to relate. The following fast path
                // checks if the source union originated in an intersection.
                // If so, and if that intersection contains the target type,
                // then we know the result to be true (for any two types A and
                // B, A & B is related to both A and B).
                let __arena___guard_source_origin = c.types.clone();
                let __guard_source_origin = __arena___guard_source_origin.get(source).clone();
                let source_origin = __guard_source_origin.as_union_type().origin;
                if let Some(origin) = source_origin {
                    if c.types_handle()
                        .get(origin)
                        .flags
                        .intersects(TypeFlags::INTERSECTION)
                        && c.types_handle().get_ref(target).alias.is_some()
                        && c.types_handle().get_ref(origin).types().contains(&target)
                    {
                        return Ternary::TRUE;
                    }
                }
                // Similarly, in unions of unions the we preserve the original
                // list of unions. This original list is often much shorter
                // than the normalized result, so we scan it in the following
                // fast path.
                let __arena___guard_target_origin = c.types.clone();
                let __guard_target_origin = __arena___guard_target_origin.get(target).clone();
                let target_origin = __guard_target_origin.as_union_type().origin;
                if let Some(origin) = target_origin {
                    if c.types_handle()
                        .get(origin)
                        .flags
                        .intersects(TypeFlags::UNION)
                        && c.types_handle().get_ref(source).alias.is_some()
                        && c.types_handle().get_ref(origin).types().contains(&source)
                    {
                        return Ternary::TRUE;
                    }
                }
            }
            if Rc::ptr_eq(&self.relation(), &c.comparable_relation) {
                return self.some_type_related_to_type(
                    c,
                    source,
                    target,
                    report_errors && !source_flags.intersects(TypeFlags::PRIMITIVE),
                    intersection_state,
                );
            }
            return self.each_type_related_to_type(
                c,
                source,
                target,
                report_errors && !source_flags.intersects(TypeFlags::PRIMITIVE),
                intersection_state,
            );
        }
        if target_flags.intersects(TypeFlags::UNION) {
            let regular_source = c.get_regular_type_of_object_literal(source);
            return self.type_related_to_some_type(
                c,
                regular_source,
                target,
                report_errors
                    && !source_flags.intersects(TypeFlags::PRIMITIVE)
                    && !target_flags.intersects(TypeFlags::PRIMITIVE),
                intersection_state,
            );
        }
        if target_flags.intersects(TypeFlags::INTERSECTION) {
            return self.type_related_to_each_type(
                c,
                source,
                target,
                report_errors,
                IntersectionState::TARGET,
            );
        }
        // Source is an intersection. For the comparable relation, if the
        // target is a primitive type we hoist the constraints of all
        // non-primitive types in the source into a new intersection. We do
        // this because the intersection may further constrain the
        // constraints of the non-primitive types. For example, given a type
        // parameter 'T extends 1 | 2', the intersection 'T & 1' should be
        // reduced to '1' such that it doesn't appear to be comparable to '2'.
        if Rc::ptr_eq(&self.relation(), &c.comparable_relation)
            && target_flags.intersects(TypeFlags::PRIMITIVE)
        {
            let __arena_source_types = c.types.clone();
            let source_types = __arena_source_types.get_ref(source).types().to_vec();
            // `core::same_map` equivalent (needs `&mut Checker` inside the
            // mapper, which the std helper cannot borrow).
            let mut constraints = Vec::with_capacity(source_types.len());
            for &t in &source_types {
                if c.types_handle()
                    .get(t)
                    .flags
                    .intersects(TypeFlags::INSTANTIABLE)
                {
                    if let Some(constraint) = c.get_base_constraint_of_type(t) {
                        constraints.push(constraint);
                    } else {
                        constraints.push(c.unknown_type);
                    }
                } else {
                    constraints.push(t);
                }
            }
            if !core::same(&constraints, &source_types) {
                source = c.get_intersection_type(&constraints);
                source_flags = c.types_handle().get_ref(source).flags;
                if source_flags.intersects(TypeFlags::NEVER) {
                    return Ternary::FALSE;
                }
                if !source_flags.intersects(TypeFlags::INTERSECTION) {
                    let result =
                        self.is_related_to(c, source, target, RecursionFlags::SOURCE, false);
                    if result != Ternary::FALSE {
                        return result;
                    }
                    return self.is_related_to(c, target, source, RecursionFlags::SOURCE, false);
                }
            }
        }
        // Check to see if any constituents of the intersection are
        // immediately related to the target. Don't report errors though.
        // Elaborating on whether a source constituent is related to the
        // target is not actually useful and leads to some confusing error
        // messages. Instead, we rely on the caller checking whether the full
        // intersection viewed as an object is related to the target.
        self.some_type_related_to_type(c, source, target, false, IntersectionState::SOURCE)
    }

    /// `(r *Relater) someTypeRelatedToType`.
    fn some_type_related_to_type(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let __arena_source_flags = c.types.clone();
        let source_flags = __arena_source_flags.get_ref(source).flags;
        let __arena_source_types = c.types.clone();
        let source_types = __arena_source_types.get_ref(source).types().to_vec();
        if source_flags.intersects(TypeFlags::UNION) && source_types.contains(&target) {
            return Ternary::TRUE;
        }
        for (i, t) in source_types.iter().enumerate() {
            let related = self.is_related_to_ex(
                c,
                *t,
                target,
                RecursionFlags::SOURCE,
                report_errors && i == source_types.len() - 1,
                None,
                intersection_state,
            );
            if related != Ternary::FALSE {
                return related;
            }
        }
        Ternary::FALSE
    }

    /// `(r *Relater) eachTypeRelatedToType`.
    fn each_type_related_to_type(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let mut result = Ternary::TRUE;
        let __arena_source_types = c.types.clone();
        let source_types = __arena_source_types.get_ref(source).types().to_vec();
        // We strip `undefined` from the target if the `source` trivially
        // doesn't contain it for our correspondence-checking fastpath since
        // `undefined` is frequently added by optionality and would otherwise
        // spoil a potentially useful correspondence
        let stripped_target = self.get_undefined_stripped_target_if_needed(c, source, target);
        let __arena_stripped_is_union = c.types.clone();
        let stripped_is_union = __arena_stripped_is_union
            .get_ref(stripped_target)
            .flags
            .intersects(TypeFlags::UNION);
        // `Types()` is only valid when the stripped target is still a union
        // — Go reads `strippedTarget.Types()` under the same condition.
        let stripped_types = if stripped_is_union {
            let __arena_stripped_types = c.types.clone();
            __arena_stripped_types
                .get_ref(stripped_target)
                .types()
                .to_vec()
        } else {
            Vec::new()
        };
        for (i, source_type) in source_types.iter().enumerate() {
            if stripped_is_union
                && source_types.len() >= stripped_types.len()
                && source_types.len() % stripped_types.len() == 0
            {
                // many unions are mappings of one another; in such cases,
                // simply comparing members at the same index can shortcut the
                // comparison such unions will have identical lengths, and
                // their corresponding elements will match up. Another common
                // scenario is where a large union has a union of objects
                // intersected with it. In such cases, if the input was, eg
                // `("a" | "b" | "c") & (string | boolean | {} | {whatever})`,
                // the result will have the structure
                // `"a" | "b" | "c" | "a" & {} | "b" & {} | "c" & {} | "a" & {whatever} | "b" & {whatever} | "c" & {whatever}`
                // - the resulting union has a length which is a multiple of
                // the original union, and the elements correspond modulo the
                // length of the original union
                let related = self.is_related_to_ex(
                    c,
                    *source_type,
                    stripped_types[i % stripped_types.len()],
                    RecursionFlags::BOTH,
                    false,
                    None,
                    intersection_state,
                );
                if related != Ternary::FALSE {
                    result = result.and(related);
                    continue;
                }
            }
            let related = self.is_related_to_ex(
                c,
                *source_type,
                target,
                RecursionFlags::SOURCE,
                report_errors,
                None,
                intersection_state,
            );
            if related == Ternary::FALSE {
                return Ternary::FALSE;
            }
            result = result.and(related);
        }
        result
    }

    /// `(r *Relater) getUndefinedStrippedTargetIfNeeded`.
    fn get_undefined_stripped_target_if_needed(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
    ) -> TypeId {
        let __arena_source_flags = c.types.clone();
        let source_flags = __arena_source_flags.get_ref(source).flags;
        let __arena_target_flags = c.types.clone();
        let target_flags = __arena_target_flags.get_ref(target).flags;
        if source_flags.intersects(TypeFlags::UNION)
            && target_flags.intersects(TypeFlags::UNION)
            && !c
                .types_handle()
                .get_ref(c.types_handle().get_ref(source).types()[0])
                .flags
                .intersects(TypeFlags::UNDEFINED)
            && c.types_handle()
                .get_ref(c.types_handle().get_ref(target).types()[0])
                .flags
                .intersects(TypeFlags::UNDEFINED)
        {
            return c.extract_types_of_kind(target, !TypeFlags::UNDEFINED);
        }
        target
    }

    /// `(r *Relater) typeRelatedToSomeType`.
    fn type_related_to_some_type(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let __arena_target_types = c.types.clone();
        let target_types = __arena_target_types.get_ref(target).types().to_vec();
        if c.types_handle()
            .get_ref(target)
            .flags
            .intersects(TypeFlags::UNION)
        {
            if target_types.contains(&source) {
                return Ternary::TRUE;
            }
            let __arena_source_flags = c.types.clone();
            let source_flags = __arena_source_flags.get_ref(source).flags;
            if !Rc::ptr_eq(&self.relation(), &c.comparable_relation)
                && c.types_handle()
                    .get(target)
                    .object_flags
                    .intersects(ObjectFlags::PRIMITIVE_UNION)
                && !source_flags.intersects(TypeFlags::ENUM_LITERAL)
                && (source_flags.intersects(
                    TypeFlags::STRING_LITERAL
                        | TypeFlags::BOOLEAN_LITERAL
                        | TypeFlags::BIG_INT_LITERAL,
                ) || (Rc::ptr_eq(&self.relation(), &c.subtype_relation)
                    || Rc::ptr_eq(&self.relation(), &c.strict_subtype_relation))
                    && source_flags.intersects(TypeFlags::NUMBER_LITERAL))
            {
                // When relating a literal type to a union of primitive types,
                // we know the relation is false unless the union contains the
                // base primitive type or the literal type in one of its
                // fresh/regular forms. We exclude numeric literals for
                // non-subtype relations because numeric literals are
                // assignable to numeric enum literals with the same value.
                // Similarly, we exclude enum literal types because
                // identically named enum types are related (see
                // isEnumTypeRelatedTo). We exclude the comparable relation in
                // entirety because it needs to be checked in both directions.
                let alternate_form = if Some(source)
                    == c.types_handle().get_ref(source).as_literal_type().regular_type
                {
                    c.types_handle().get_ref(source).as_literal_type().fresh_type
                } else {
                    c.types_handle().get_ref(source).as_literal_type().regular_type
                };
                let mut primitive: Option<TypeId> = None;
                if source_flags.intersects(TypeFlags::STRING_LITERAL) {
                    primitive = Some(c.string_type);
                } else if source_flags.intersects(TypeFlags::NUMBER_LITERAL) {
                    primitive = Some(c.number_type);
                } else if source_flags.intersects(TypeFlags::BIG_INT_LITERAL) {
                    primitive = Some(c.bigint_type);
                }
                if primitive.is_some_and(|p| target_types.contains(&p))
                    || alternate_form.is_some_and(|f| target_types.contains(&f))
                {
                    return Ternary::TRUE;
                }
                return Ternary::FALSE;
            }
            let matched = c.get_matching_union_constituent_for_type(target, source);
            if let Some(match_) = matched {
                let related = self.is_related_to_ex(
                    c,
                    source,
                    match_,
                    RecursionFlags::TARGET,
                    false,
                    None,
                    intersection_state,
                );
                if related != Ternary::FALSE {
                    return related;
                }
            }
        }
        for t in target_types {
            let related = self.is_related_to_ex(
                c,
                source,
                t,
                RecursionFlags::TARGET,
                false,
                None,
                intersection_state,
            );
            if related != Ternary::FALSE {
                return related;
            }
        }
        if report_errors {
            // Elaborate only if we can find a best matching type in the
            // target union
            let best_matching_type = c.get_best_matching_type(
                source,
                target,
                Some(&mut *self),
                Comparer::IsRelatedToSimple,
            );
            if let Some(best_matching_type) = best_matching_type {
                self.is_related_to_ex(
                    c,
                    source,
                    best_matching_type,
                    RecursionFlags::TARGET,
                    true,
                    None,
                    intersection_state,
                );
            }
        }
        Ternary::FALSE
    }

    /// `(r *Relater) typeRelatedToEachType`.
    fn type_related_to_each_type(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let mut result = Ternary::TRUE;
        let __arena_target_types = c.types.clone();
        let target_types = __arena_target_types.get_ref(target).types().to_vec();
        for target_type in target_types {
            let related = self.is_related_to_ex(
                c,
                source,
                target_type,
                RecursionFlags::TARGET,
                report_errors,
                None,
                intersection_state,
            );
            if related == Ternary::FALSE {
                return Ternary::FALSE;
            }
            result = result.and(related);
        }
        result
    }

    /// `(r *Relater) eachTypeRelatedToSomeType`.
    fn each_type_related_to_some_type(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
    ) -> Ternary {
        let mut result = Ternary::TRUE;
        let __arena_source_types = c.types.clone();
        let source_types = __arena_source_types.get_ref(source).types().to_vec();
        for source_type in source_types {
            let related = self.type_related_to_some_type(
                c,
                source_type,
                target,
                false,
                IntersectionState::NONE,
            );
            if related == Ternary::FALSE {
                return Ternary::FALSE;
            }
            result = result.and(related);
        }
        result
    }

    /// `(r *Relater) recursiveTypeRelatedTo`.
    fn recursive_type_related_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
        intersection_state: IntersectionState,
        recursion_flags: RecursionFlags,
    ) -> Ternary {
        if self.overflow {
            // Note that stack depth overflows can cause _any_ relation
            // involving structured types to become false, so it is important
            // to have well-defined behavior even in cases that shouldn't
            // normally occur.
            return Ternary::FALSE;
        }
        let (id, constrained) = crate::checker_c::get_relation_key(
            c,
            source,
            target,
            intersection_state,
            Rc::ptr_eq(&self.relation(), &c.identity_relation),
            false,
        );
        let entry = self.relation().borrow().get(id);
        if entry != RelationComparisonResult::NONE {
            if report_errors
                && entry.intersects(RelationComparisonResult::FAILED)
                && !entry.intersects(RelationComparisonResult::OVERFLOW)
            {
                // We are elaborating errors and the cached result is a
                // failure not due to a comparison overflow, so we will do the
                // comparison again to generate an error message.
            } else {
                c.reliability_flags |= entry
                    & (RelationComparisonResult::REPORTS_UNMEASURABLE
                        | RelationComparisonResult::REPORTS_UNRELIABLE);
                if report_errors && entry.intersects(RelationComparisonResult::OVERFLOW) {
                    let source_str = c.type_to_string(source);
                    let target_str = c.type_to_string(target);
                    self.report_error(
                        c,
                        &tsc_diagnostics::Excessive_complexity_comparing_types_0_and_1,
                        &[source_str, target_str],
                    );
                }
                if entry.intersects(RelationComparisonResult::SUCCEEDED) {
                    return Ternary::TRUE;
                }
                return Ternary::FALSE;
            }
        }
        if self.relation_count <= 0 {
            self.overflow = true;
            return Ternary::FALSE;
        }
        // If source and target are already being compared, consider them
        // related with assumptions
        if self.maybe_keys_set.has(&id) {
            return Ternary::MAYBE;
        }
        // A constrained key indicates that we have type references that
        // reference constrained type parameters. For such keys we also check
        // against the key we would have gotten if all type parameters were
        // unconstrained.
        if constrained {
            let (broadest_equivalent_id, _) = crate::checker_c::get_relation_key(
                c,
                source,
                target,
                intersection_state,
                Rc::ptr_eq(&self.relation(), &c.identity_relation),
                true,
            );
            if self.maybe_keys_set.has(&broadest_equivalent_id) {
                return Ternary::MAYBE;
            }
        }
        if self.source_stack.len() == 100 || self.target_stack.len() == 100 {
            // We stop relating if we reach 100 levels of nesting. This is a
            // backstop to catch infinite recursion that wasn't caught by
            // isDeeplyNestedType. It will also stop relating types that truly
            // are over 100 levels deep, but those are exceedingly rare.
            return Ternary::MAYBE;
        }
        let maybe_start = self.maybe_keys.len();
        self.maybe_keys.push(id);
        self.maybe_keys_set.add(id);
        let save_expanding_flags = self.expanding_flags;
        if recursion_flags.intersects(RecursionFlags::SOURCE) {
            self.source_stack.push(source);
            if !self.expanding_flags.intersects(ExpandingFlags::SOURCE)
                && c.is_deeply_nested_type(source, &self.source_stack, 3)
            {
                self.expanding_flags |= ExpandingFlags::SOURCE;
            }
        }
        if recursion_flags.intersects(RecursionFlags::TARGET) {
            self.target_stack.push(target);
            if !self.expanding_flags.intersects(ExpandingFlags::TARGET)
                && c.is_deeply_nested_type(target, &self.target_stack, 3)
            {
                self.expanding_flags |= ExpandingFlags::TARGET;
            }
        }
        let save_reliability_flags = c.reliability_flags;
        c.reliability_flags = RelationComparisonResult::NONE;
        let result;
        if self.expanding_flags == ExpandingFlags::BOTH {
            if let Some(tr) = &c.tracer {
                let mut args = TraceArgs::new();
                args.insert("sourceId".to_string(), source.0.into());
                args.insert("targetId".to_string(), target.0.into());
                args.insert("depth".to_string(), (self.source_stack.len() as i64).into());
                args.insert(
                    "targetDepth".to_string(),
                    (self.target_stack.len() as i64).into(),
                );
                tr.instant(
                    tsc_tracing::PHASE_CHECK_TYPES,
                    "recursiveTypeRelatedTo_DepthLimit",
                    &args,
                );
            }
            result = Ternary::MAYBE;
        } else {
            let pop = c.tracer.as_ref().map(|tr| {
                let mut args = TraceArgs::new();
                args.insert("sourceId".to_string(), source.0.into());
                args.insert("targetId".to_string(), target.0.into());
                tr.push(
                    tsc_tracing::PHASE_CHECK_TYPES,
                    "structuredTypeRelatedTo",
                    &mut args,
                    false,
                )
            });
            result = self.structured_type_related_to(
                c,
                source,
                target,
                report_errors,
                intersection_state,
            );
            if let Some(pop) = pop {
                pop();
            }
        }
        let propagating_variance_flags = c.reliability_flags;
        c.reliability_flags |= save_reliability_flags;
        if recursion_flags.intersects(RecursionFlags::SOURCE) {
            self.source_stack.pop();
        }
        if recursion_flags.intersects(RecursionFlags::TARGET) {
            self.target_stack.pop();
        }
        self.expanding_flags = save_expanding_flags;
        if result != Ternary::FALSE {
            if result == Ternary::TRUE
                || (self.source_stack.is_empty() && self.target_stack.is_empty())
            {
                if result == Ternary::TRUE || result == Ternary::MAYBE {
                    // If result is definitely true, record all maybe keys as
                    // having succeeded. Also, record Ternary.Maybe results as
                    // having succeeded once we reach depth 0, but never
                    // record Ternary.Unknown results.
                    self.reset_maybe_stack(maybe_start, propagating_variance_flags, true);
                } else {
                    self.reset_maybe_stack(maybe_start, propagating_variance_flags, false);
                }
            }
            // Note: it's intentional that we don't reset in the else case; we
            // leave them on the stack such that when we hit depth zero above,
            // we can report all of them as successful.
        } else {
            // A false result goes straight into global cache (when something
            // is false under assumptions it will also be false without
            // assumptions)
            self.relation().borrow_mut().set(
                id,
                RelationComparisonResult::FAILED | propagating_variance_flags,
            );
            self.relation_count -= 1;
            self.reset_maybe_stack(maybe_start, propagating_variance_flags, false);
        }
        result
    }

    /// `(r *Relater) resetMaybeStack`.
    fn reset_maybe_stack(
        &mut self,
        maybe_start: usize,
        propagating_variance_flags: RelationComparisonResult,
        mark_all_as_succeeded: bool,
    ) {
        for i in maybe_start..self.maybe_keys.len() {
            let key = self.maybe_keys[i];
            self.maybe_keys_set.delete(&key);
            if mark_all_as_succeeded {
                self.relation().borrow_mut().set(
                    key,
                    RelationComparisonResult::SUCCEEDED | propagating_variance_flags,
                );
                self.relation_count -= 1;
            }
        }
        self.maybe_keys.truncate(maybe_start);
    }

    /// `(r *Relater) getErrorState` / `restoreErrorState`.
    fn get_error_state(&self) -> ErrorState {
        ErrorState {
            error_chain: self.error_chain.clone(),
            related_info: self.related_info.clone(),
        }
    }

    fn restore_error_state(&mut self, e: &ErrorState) {
        self.error_chain = e.error_chain.clone();
        self.related_info = e.related_info.clone();
    }

    /// `(r *Relater) structuredTypeRelatedTo`.
    fn structured_type_related_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let save_error_state = self.get_error_state();
        let mut result = self.structured_type_related_to_worker(
            c,
            source,
            target,
            report_errors,
            intersection_state,
        );
        if !Rc::ptr_eq(&self.relation(), &c.identity_relation) {
            // The combined constraint of an intersection type is the
            // intersection of the constraints of the constituents. When an
            // intersection type contains instantiable types with union type
            // constraints, there are situations where we need to examine the
            // combined constraint. One is when the target is a union type.
            // Another is when the intersection contains types belonging to
            // one of the disjoint domains. For example, given type variables
            // T and U, each with the constraint 'string | number', the
            // combined constraint of 'T & U' is 'string | number' and we need
            // to check this constraint against a union on the target side.
            // Also, given a type variable V constrained to 'string | number',
            // 'V & number' has a combined constraint of 'string & number |
            // number & number' which reduces to just 'number'.
            // This also handles type parameters, as a type parameter with a
            // union constraint compared against a union needs to have its
            // constraint hoisted into an intersection with said type
            // parameter, this way the type param can be compared with itself
            // in the target (with the influence of its constraint to match
            // other parts). For example, if `T extends 1 | 2` and
            // `U extends 2 | 3` and we compare `T & U` to `T & U & (1 | 2 | 3)`
            let (source_flags, target_flags) = {
                let __arena_s = c.types.clone();
                let s = __arena_s.get_ref(source);
                (s.flags, c.types_handle().get_ref(target).flags)
            };
            if result == Ternary::FALSE
                && (source_flags.intersects(TypeFlags::INTERSECTION)
                    || source_flags.intersects(TypeFlags::TYPE_PARAMETER)
                        && target_flags.intersects(TypeFlags::UNION))
            {
                let source_types = if source_flags.intersects(TypeFlags::INTERSECTION) {
                    c.types_handle().get_ref(source).types().to_vec()
                } else {
                    vec![source]
                };
                let constraint = c.get_effective_constraint_of_intersection(
                    &source_types,
                    target_flags.intersects(TypeFlags::UNION),
                );
                if let Some(constraint) = constraint {
                    if crate::checker_d::every_type(c, constraint, |_c, t| t != source) {
                        // TODO: Stack errors so we get a pyramid for the
                        // "normal" comparison above, _and_ a second for this
                        result = self.is_related_to_ex(
                            c,
                            constraint,
                            target,
                            RecursionFlags::SOURCE,
                            false,
                            None,
                            intersection_state,
                        );
                    }
                }
            }
            let (source_flags, target_flags) = {
                let __arena_s = c.types.clone();
                let s = __arena_s.get_ref(source);
                (s.flags, c.types_handle().get_ref(target).flags)
            };
            if result != Ternary::FALSE
                && !intersection_state.intersects(IntersectionState::TARGET)
                && target_flags.intersects(TypeFlags::INTERSECTION)
                && !c.is_generic_object_type(target)
                && source_flags.intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION)
            {
                // When the target is an intersection we need an extra
                // property check in order to detect nested excess properties
                // and nested weak types. The following are motivating
                // examples that all should be errors, but aren't without this
                // extra property check:
                //
                //   let obj: { a: { x: string } } & { c: number } = { a: { x: 'hello', y: 2 }, c: 5 };  // Nested excess property
                //
                //   declare let wrong: { a: { y: string } };
                //   let weak: { a?: { x?: number } } & { c?: string } = wrong;  // Nested weak object type
                result = result.and(self.properties_related_to(
                    c,
                    source,
                    target,
                    report_errors,
                    &Set::new(),
                    false,
                    IntersectionState::NONE,
                ));
                if result != Ternary::FALSE
                    && crate::utilities::is_object_literal_type(&c.types, source)
                    && c.types_handle()
                        .get(source)
                        .object_flags
                        .intersects(ObjectFlags::FRESH_LITERAL)
                {
                    result = result.and(self.index_signatures_related_to(
                        c,
                        source,
                        target,
                        false,
                        report_errors,
                        IntersectionState::NONE,
                    ));
                }
            } else if result != Ternary::FALSE
                && c.is_non_generic_object_type(target)
                && !c.is_array_or_tuple_type(target)
                && self.is_source_intersection_needing_extra_check(c, source, target)
            {
                // When the source is an intersection we need an extra check
                // of any optional properties in the target to detect possible
                // mismatched property types. For example:
                //
                //   function foo<T extends object>(x: { a?: string }, y: T & { a: boolean }) {
                //     x = y;  // Mismatched property in source intersection
                //   }
                result = result.and(self.properties_related_to(
                    c,
                    source,
                    target,
                    report_errors,
                    &Set::new(),
                    true,
                    intersection_state,
                ));
            }
        }
        if result != Ternary::FALSE {
            self.restore_error_state(&save_error_state);
        }
        result
    }

    /// `(r *Relater) isSourceIntersectionNeedingExtraCheck`.
    fn is_source_intersection_needing_extra_check(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
    ) -> bool {
        if !c
            .types_handle()
            .get_ref(source)
            .flags
            .intersects(TypeFlags::INTERSECTION)
        {
            return false;
        }
        let apparent = c.get_apparent_type(source);
        c.types_handle()
                .get_ref(apparent)
                .flags
                .intersects(TypeFlags::STRUCTURED_TYPE)
            && !c.types_handle().get_ref(source).types().iter().any(|&t| {
                t == target
                    || c.types_handle()
                        .get(t)
                        .object_flags
                        .intersects(ObjectFlags::NON_INFERRABLE_TYPE)
            })
    }

    /// `(r *Relater) structuredTypeRelatedToWorker`.
    fn structured_type_related_to_worker(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let mut result = Ternary::FALSE;
        let mut variance_check_failed = false;
        let mut original_error_chain: Option<Box<ErrorChain>> = None;
        let save_error_state = self.get_error_state();
        // `relateVariances` — Go returns `(Ternary, bool)` where `ok` means
        // "the caller returns the result". The macro `return`s directly in
        // that case and falls through otherwise.
        macro_rules! relate_variances {
            ($source_args:expr, $target_args:expr, $variances:expr) => {{
                let variances: &[VarianceFlags] = $variances;
                result = self.type_arguments_related_to(
                    c,
                    $source_args,
                    $target_args,
                    variances,
                    report_errors,
                    intersection_state,
                );
                if result != Ternary::FALSE {
                    return result;
                }
                if variances
                    .iter()
                    .any(|v| v.intersects(VarianceFlags::ALLOWS_STRUCTURAL_FALLBACK))
                {
                    // If some type parameter was `Unmeasurable` or
                    // `Unreliable`, and we couldn't pass by assuming it was
                    // identical, then we have to allow a structural fallback
                    // check. We elide the variance-based error elaborations,
                    // since those might not be too helpful, since we'll
                    // potentially be assuming identity of the type parameter.
                    original_error_chain = None;
                    self.restore_error_state(&save_error_state);
                } else {
                    let allow_structural_fallback =
                        c.has_covariant_void_argument($target_args, variances);
                    variance_check_failed = !allow_structural_fallback;
                    // The type arguments did not relate appropriately, but it
                    // may be because we have no variance information (in
                    // which case typeArgumentsRelatedTo defaulted to
                    // covariance for all type arguments). It might also be
                    // the case that the target type has a 'void' type
                    // argument for a covariant type parameter that is only
                    // used in return positions within the generic type (in
                    // which case any type argument is permitted on the source
                    // side). In those cases we proceed with a structural
                    // comparison. Otherwise, we know for certain the
                    // instantiations aren't related and we can return here.
                    if !variances.is_empty() && !allow_structural_fallback {
                        // In some cases generic types that are covariant in
                        // regular type checking mode become invariant in
                        // --strictFunctionTypes mode because one or more type
                        // parameters are used in both co- and contravariant
                        // positions. In order to make it easier to diagnose
                        // *why* such types are invariant, if any of the type
                        // parameters are invariant we reset the reported
                        // errors and instead force a structural comparison
                        // (which will include elaborations that reveal the
                        // reason).
                        // We can switch on `reportErrors` here, since
                        // varianceCheckFailed guarantees we return `False`,
                        // we can return `False` early here to skip
                        // calculating the structural error message we don't
                        // need.
                        if variance_check_failed
                            && !(report_errors
                                && variances.iter().any(|v| {
                                    (*v & VarianceFlags::VARIANCE_MASK) == VarianceFlags::INVARIANT
                                }))
                        {
                            return Ternary::FALSE;
                        }
                        // We remember the original error information so we
                        // can restore it in case the structural comparison
                        // unexpectedly succeeds. This can happen when the
                        // structural comparison result is a Ternary.Maybe
                        // for example caused by the recursion depth limiter.
                        original_error_chain = self.error_chain.take();
                        self.restore_error_state(&save_error_state);
                    }
                }
            }};
        }
        let (mut source, target) = (source, target);
        let (source_flags, target_flags) = {
            let __arena_s = c.types.clone();
            let s = __arena_s.get_ref(source);
            (s.flags, c.types_handle().get_ref(target).flags)
        };
        if Rc::ptr_eq(&self.relation(), &c.identity_relation) {
            // We've already checked that source.flags and target.flags are
            // identical
            if source_flags.intersects(TypeFlags::UNION_OR_INTERSECTION) {
                result = self.each_type_related_to_some_type(c, source, target);
                if result != Ternary::FALSE {
                    result = result.and(self.each_type_related_to_some_type(c, target, source));
                }
                return result;
            }
            if source_flags.intersects(TypeFlags::INDEX) {
                return self.is_related_to(
                    c,
                    c.types_handle().get(source).target().unwrap_or(source),
                    c.types_handle().get(target).target().unwrap_or(target),
                    RecursionFlags::BOTH,
                    false,
                );
            }
            if source_flags.intersects(TypeFlags::INDEXED_ACCESS) {
                let (s_object, s_index) = {
                    let __arena___guard_i = c.types.clone();
                    let __guard_i = __arena___guard_i.get(source).clone();
                    let i = __guard_i.as_indexed_access_type();
                    (i.object_type, i.index_type)
                };
                let (t_object, t_index) = {
                    let __arena___guard_i = c.types.clone();
                    let __guard_i = __arena___guard_i.get(target).clone();
                    let i = __guard_i.as_indexed_access_type();
                    (i.object_type, i.index_type)
                };
                result = self.is_related_to(
                    c,
                    s_object.unwrap_or(source),
                    t_object.unwrap_or(target),
                    RecursionFlags::BOTH,
                    false,
                );
                if result != Ternary::FALSE {
                    result = result.and(self.is_related_to(
                        c,
                        s_index.unwrap_or(source),
                        t_index.unwrap_or(target),
                        RecursionFlags::BOTH,
                        false,
                    ));
                    if result != Ternary::FALSE {
                        return result;
                    }
                }
            } else if source_flags.intersects(TypeFlags::CONDITIONAL) {
                let (s_root_is_distributive, s_check, s_extends) = {
                    let __arena___guard_ct = c.types.clone();
                    let __guard_ct = __arena___guard_ct.get(source).clone();
                    let ct = __guard_ct.as_conditional_type();
                    (
                        ct.root
                            .as_ref()
                            .map(|r| r.is_distributive)
                            .unwrap_or_default(),
                        ct.check_type,
                        ct.extends_type,
                    )
                };
                let (t_root_is_distributive, t_check, t_extends) = {
                    let __arena___guard_ct = c.types.clone();
                    let __guard_ct = __arena___guard_ct.get(target).clone();
                    let ct = __guard_ct.as_conditional_type();
                    (
                        ct.root
                            .as_ref()
                            .map(|r| r.is_distributive)
                            .unwrap_or_default(),
                        ct.check_type,
                        ct.extends_type,
                    )
                };
                if s_root_is_distributive == t_root_is_distributive {
                    result = self.is_related_to(
                        c,
                        s_check.unwrap_or(source),
                        t_check.unwrap_or(target),
                        RecursionFlags::BOTH,
                        false,
                    );
                    if result != Ternary::FALSE {
                        result = result.and(self.is_related_to(
                            c,
                            s_extends.unwrap_or(source),
                            t_extends.unwrap_or(target),
                            RecursionFlags::BOTH,
                            false,
                        ));
                        if result != Ternary::FALSE {
                            let s_true = c.get_true_type_from_conditional_type(source);
                            let t_true = c.get_true_type_from_conditional_type(target);
                            result = result.and(self.is_related_to(
                                c,
                                s_true,
                                t_true,
                                RecursionFlags::BOTH,
                                false,
                            ));
                            if result != Ternary::FALSE {
                                let s_false = c.get_false_type_from_conditional_type(source);
                                let t_false = c.get_false_type_from_conditional_type(target);
                                result = result.and(self.is_related_to(
                                    c,
                                    s_false,
                                    t_false,
                                    RecursionFlags::BOTH,
                                    false,
                                ));
                                if result != Ternary::FALSE {
                                    return result;
                                }
                            }
                        }
                    }
                }
            } else if source_flags.intersects(TypeFlags::SUBSTITUTION) {
                let (s_base, s_constraint) = {
                    let __arena___guard_st = c.types.clone();
                    let __guard_st = __arena___guard_st.get(source).clone();
                    let st = __guard_st.as_substitution_type();
                    (st.base_type, st.constraint)
                };
                let (t_base, t_constraint) = {
                    let __arena___guard_st = c.types.clone();
                    let __guard_st = __arena___guard_st.get(target).clone();
                    let st = __guard_st.as_substitution_type();
                    (st.base_type, st.constraint)
                };
                result = self.is_related_to(
                    c,
                    s_base.unwrap_or(source),
                    t_base.unwrap_or(target),
                    RecursionFlags::BOTH,
                    false,
                );
                if result != Ternary::FALSE {
                    result = result.and(self.is_related_to(
                        c,
                        s_constraint.unwrap_or(source),
                        t_constraint.unwrap_or(target),
                        RecursionFlags::BOTH,
                        false,
                    ));
                    if result != Ternary::FALSE {
                        return result;
                    }
                }
            } else if source_flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
                let (s_texts, s_types) = {
                    let __arena___guard_tl = c.types.clone();
                    let __guard_tl = __arena___guard_tl.get(source).clone();
                    let tl = __guard_tl.as_template_literal_type();
                    (tl.texts.clone(), tl.types.clone())
                };
                let (t_texts, t_types) = {
                    let __arena___guard_tl = c.types.clone();
                    let __guard_tl = __arena___guard_tl.get(target).clone();
                    let tl = __guard_tl.as_template_literal_type();
                    (tl.texts.clone(), tl.types.clone())
                };
                if s_texts == t_texts {
                    result = Ternary::TRUE;
                    for (i, source_type) in s_types.iter().enumerate() {
                        result = result.and(self.is_related_to(
                            c,
                            *source_type,
                            t_types[i],
                            RecursionFlags::BOTH,
                            false,
                        ));
                        if result == Ternary::FALSE {
                            return result;
                        }
                    }
                    return result;
                }
            } else if source_flags.intersects(TypeFlags::STRING_MAPPING) {
                if c.types_handle().get_ref(source).symbol() == c.types_handle().get_ref(target).symbol() {
                    let __arena___guard_s_target = c.types.clone();
                    let __guard_s_target = __arena___guard_s_target.get(source).clone();
                    let s_target = __guard_s_target.as_string_mapping_type().target;
                    let __arena___guard_t_target = c.types.clone();
                    let __guard_t_target = __arena___guard_t_target.get(target).clone();
                    let t_target = __guard_t_target.as_string_mapping_type().target;
                    return self.is_related_to(
                        c,
                        s_target.unwrap_or(source),
                        t_target.unwrap_or(target),
                        RecursionFlags::BOTH,
                        false,
                    );
                }
            }
            if !source_flags.intersects(TypeFlags::OBJECT) {
                return Ternary::FALSE;
            }
        } else if source_flags.intersects(TypeFlags::UNION_OR_INTERSECTION)
            || target_flags.intersects(TypeFlags::UNION_OR_INTERSECTION)
        {
            result = self.union_or_intersection_related_to(
                c,
                source,
                target,
                report_errors,
                intersection_state,
            );
            if result != Ternary::FALSE {
                return result;
            }
            // The ordered decomposition above doesn't handle all cases.
            // Specifically, we also need to handle:
            // Source is instantiable (e.g. source has union or intersection constraint).
            // Source is an object, target is a union (e.g. { a, b: boolean } <=> { a, b: true } | { a, b: false }).
            // Source is an intersection, target is an object (e.g. { a } & { b } <=> { a, b }).
            // Source is an intersection, target is a union (e.g. { a } & { b: boolean } <=> { a, b: true } | { a, b: false }).
            // Source is an intersection, target instantiable (e.g. string & { tag } <=> T["a"] constrained to string & { tag }).
            if !(source_flags.intersects(TypeFlags::INSTANTIABLE)
                || source_flags.intersects(TypeFlags::OBJECT)
                    && target_flags.intersects(TypeFlags::UNION)
                || source_flags.intersects(TypeFlags::INTERSECTION)
                    && target_flags
                        .intersects(TypeFlags::OBJECT | TypeFlags::UNION | TypeFlags::INSTANTIABLE))
            {
                return Ternary::FALSE;
            }
        }
        // We limit alias variance probing to only object and conditional
        // types since their alias behavior is more predictable than other,
        // interned types, which may or may not have an alias depending on the
        // order in which things were checked.
        {
            let (source_alias, target_alias) = {
                let __arena_s = c.types.clone();
                let s = __arena_s.get_ref(source);
                (s.alias.clone(), c.types_handle().get_ref(target).alias.clone())
            };
            if source_flags.intersects(TypeFlags::OBJECT | TypeFlags::CONDITIONAL)
                && source_alias
                    .as_ref()
                    .is_some_and(|a| !a.type_arguments.is_empty())
                && target_alias.as_ref().is_some()
                && source_alias.as_ref().unwrap().symbol == target_alias.as_ref().unwrap().symbol
                && !(c.is_marker_type(source) || c.is_marker_type(target))
            {
                let variances =
                    c.get_alias_variances(source_alias.as_ref().unwrap().symbol.unwrap());
                if variances.is_empty() {
                    return Ternary::UNKNOWN;
                }
                let params = c
                    .type_alias_links
                    .get(source_alias.as_ref().unwrap().symbol.unwrap())
                    .type_parameters
                    .clone();
                let min_params = c.get_min_type_argument_count(&params);
                let node_is_in_js_file = {
                    let decl = source_alias
                        .as_ref()
                        .unwrap()
                        .symbol
                        .and_then(|s| c.sym(s).value_declaration);
                    decl.is_some_and(|d| {
                        let __program = c.program.clone().expect("program");
                        let nodes = __program.nodes((d).file_index());
                        ast::is_in_js_file(Some(d), &nodes)
                    })
                };
                let source_types = c.fill_missing_type_arguments(
                    &source_alias.as_ref().unwrap().type_arguments,
                    &params,
                    min_params,
                    node_is_in_js_file,
                );
                let target_types = c.fill_missing_type_arguments(
                    &target_alias.as_ref().unwrap().type_arguments,
                    &params,
                    min_params,
                    node_is_in_js_file,
                );
                relate_variances!(&source_types, &target_types, &variances);
            }
        }
        // For a generic type T and a type U that is assignable to T, [...U]
        // is assignable to T, U is assignable to readonly [...T], and U is
        // assignable to [...T] when U is constrained to a mutable array or
        // tuple type.
        if crate::utilities::is_single_element_generic_tuple_type(&c.types, source)
            && !c
                .types_handle()
                .target_tuple_type(source)
                .map(|tt| c.types_handle().get_ref(tt).as_tuple_type().readonly)
                .unwrap_or_default()
        {
            let source_arg = c.get_type_arguments(source)[0];
            result = self.is_related_to(c, source_arg, target, RecursionFlags::SOURCE, false);
            if result != Ternary::FALSE {
                return result;
            }
        }
        if crate::utilities::is_single_element_generic_tuple_type(&c.types, target)
            && (c
                .types_handle()
                .target_tuple_type(target)
                .map(|tt| c.types_handle().get_ref(tt).as_tuple_type().readonly)
                .unwrap_or_default()
                || {
                    let base = c.get_base_constraint_or_type(source);
                    c.is_mutable_array_or_tuple(base)
                })
        {
            let target_arg = c.get_type_arguments(target)[0];
            result = self.is_related_to(c, source, target_arg, RecursionFlags::TARGET, false);
            if result != Ternary::FALSE {
                return result;
            }
        }
        if target_flags.intersects(TypeFlags::TYPE_PARAMETER) {
            // A source type { [P in Q]: X } is related to a target type T if
            // keyof T is related to Q and X is related to T[Q].
            let mapped_has_name_type = {
                let __g = c.types.get_ref(source);

                __g.object_flags.intersects(ObjectFlags::MAPPED)
                    && __g.as_mapped_type().declaration.is_some_and(|d| {
                        c.program_nodes(d)[d]
                            .as_mapped_type_node()
                            .name_type
                            .is_some()
                    })
            };
            // `getConstraintTypeFromMappedType` requires a mapped source —
            // evaluate it only after the `MAPPED` check, as Go's `&&`
            // short-circuit does; a hoisted precompute would call
            // `as_mapped_type()` on e.g. an `Index` type and panic.
            let source_is_mapped = c
                .types_handle()
                .get_ref(source)
                .object_flags
                .intersects(ObjectFlags::MAPPED);
            let __h7348_21 =
                source_is_mapped.then(|| c.get_constraint_type_from_mapped_type(source));
            let __h7347_21 = c.get_index_type(target);

            if source_is_mapped
                && !mapped_has_name_type
                && self.is_related_to(
                    c,
                    __h7347_21,
                    __h7348_21.flatten().unwrap_or(c.never_type),
                    RecursionFlags::BOTH,
                    false,
                ) != Ternary::FALSE
            {
                if !crate::utilities::get_mapped_type_modifiers(c, source)
                    .intersects(MappedTypeModifiers::INCLUDE_OPTIONAL)
                {
                    let template_type = c.get_template_type_from_mapped_type(source);
                    let type_parameter = c.get_type_parameter_from_mapped_type(source);
                    if let (Some(template_type), Some(type_parameter)) =
                        (template_type, type_parameter)
                    {
                        let indexed_access_type = c.get_indexed_access_type(target, type_parameter);
                        result = self.is_related_to(
                            c,
                            template_type,
                            indexed_access_type,
                            RecursionFlags::BOTH,
                            report_errors,
                        );
                        if result != Ternary::FALSE {
                            return result;
                        }
                    }
                }
            }
            if Rc::ptr_eq(&self.relation(), &c.comparable_relation)
                && source_flags.intersects(TypeFlags::TYPE_PARAMETER)
            {
                // This is a carve-out in comparability to essentially forbid
                // comparing a type parameter with another type parameter
                // unless one extends the other. (Remember: comparability is
                // mostly bidirectional!)
                let constraint = c.get_constraint_of_type_parameter(source);
                if let Some(constraint) = constraint {
                    if crate::checker_d::some_type(c, constraint, |c: &mut Checker, t| {
                        c.types_handle()
                            .get(t)
                            .flags
                            .intersects(TypeFlags::TYPE_PARAMETER)
                    }) {
                        return self.is_related_to(
                            c,
                            constraint,
                            target,
                            RecursionFlags::SOURCE,
                            false,
                        );
                    }
                }
                return Ternary::FALSE;
            }
        } else if target_flags.intersects(TypeFlags::INDEXED_ACCESS) {
            if source_flags.intersects(TypeFlags::INDEXED_ACCESS) {
                // Relate components directly before falling back to
                // constraint relationships. A type S[K] is related to a type
                // T[J] if S is related to T and K is related to J.
                let (s_object, s_index) = {
                    let __arena___guard_i = c.types.clone();
                    let __guard_i = __arena___guard_i.get(source).clone();
                    let i = __guard_i.as_indexed_access_type();
                    (i.object_type, i.index_type)
                };
                let (t_object, t_index) = {
                    let __arena___guard_i = c.types.clone();
                    let __guard_i = __arena___guard_i.get(target).clone();
                    let i = __guard_i.as_indexed_access_type();
                    (i.object_type, i.index_type)
                };
                result = self.is_related_to(
                    c,
                    s_object.unwrap_or(source),
                    t_object.unwrap_or(target),
                    RecursionFlags::BOTH,
                    report_errors,
                );
                if result != Ternary::FALSE {
                    result = result.and(self.is_related_to(
                        c,
                        s_index.unwrap_or(source),
                        t_index.unwrap_or(target),
                        RecursionFlags::BOTH,
                        report_errors,
                    ));
                }
                if result != Ternary::FALSE {
                    return result;
                }
                if report_errors {
                    original_error_chain = self.error_chain.clone();
                }
            }
            // A type S is related to a type T[K] if S is related to C, where
            // C is the base constraint of T[K] for writing.
            if Rc::ptr_eq(&self.relation(), &c.assignable_relation)
                || Rc::ptr_eq(&self.relation(), &c.comparable_relation)
            {
                let (object_type, index_type) = {
                    let __arena___guard_i = c.types.clone();
                    let __guard_i = __arena___guard_i.get(target).clone();
                    let i = __guard_i.as_indexed_access_type();
                    (i.object_type, i.index_type)
                };
                if let (Some(object_type), Some(index_type)) = (object_type, index_type) {
                    let base_object_type = c.get_base_constraint_or_type(object_type);
                    let base_index_type = c.get_base_constraint_or_type(index_type);
                    if !c.is_generic_object_type(base_object_type)
                        && !c.is_generic_index_type(base_index_type)
                    {
                        let access_flags = AccessFlags::WRITING
                            | if base_object_type != object_type {
                                AccessFlags::NO_INDEX_SIGNATURES
                            } else {
                                AccessFlags::NONE
                            };
                        if let Some(constraint) = c.get_indexed_access_type_or_undefined(
                            base_object_type,
                            base_index_type,
                            access_flags,
                            None,
                            None,
                        ) {
                            if report_errors && original_error_chain.is_some() {
                                // create a new chain for the constraint error
                                self.restore_error_state(&save_error_state);
                            }
                            result = self.is_related_to_ex(
                                c,
                                source,
                                constraint,
                                RecursionFlags::TARGET,
                                report_errors,
                                None,
                                intersection_state,
                            );
                            if result != Ternary::FALSE {
                                return result;
                            }
                            // prefer the shorter chain of the constraint
                            // comparison chain, and the direct comparison
                            // chain
                            if report_errors
                                && original_error_chain.is_some()
                                && self.error_chain.is_some()
                            {
                                if chain_depth(original_error_chain.as_deref())
                                    <= chain_depth(self.error_chain.as_deref())
                                {
                                    self.error_chain = original_error_chain.take();
                                }
                            }
                        }
                    }
                }
            }
            if report_errors {
                original_error_chain = None;
            }
        } else if target_flags.intersects(TypeFlags::INDEX) {
            let __arena___guard_target_type = c.types.clone();
            let __guard_target_type = __arena___guard_target_type.get(target).clone();
            let target_type = __guard_target_type.as_index_type().target;
            // A keyof S is related to a keyof T if T is related to S.
            if source_flags.intersects(TypeFlags::INDEX) {
                let __arena___guard_source_target = c.types.clone();
                let __guard_source_target = __arena___guard_source_target.get(source).clone();
                let source_target = __guard_source_target.as_index_type().target;
                if let (Some(target_type), Some(source_target)) = (target_type, source_target) {
                    result = self.is_related_to(
                        c,
                        target_type,
                        source_target,
                        RecursionFlags::BOTH,
                        false,
                    );
                    if result != Ternary::FALSE {
                        return result;
                    }
                }
            }
            if let Some(target_type) = target_type {
                if crate::checker_core::is_tuple_type(&c.types, target_type) {
                    // An index type can have a tuple type target when the
                    // tuple type contains variadic elements. Check if the
                    // source is related to the known keys of the tuple type.
                    let keys = c.get_known_keys_of_tuple_type(target_type);
                    result =
                        self.is_related_to(c, source, keys, RecursionFlags::TARGET, report_errors);
                    if result != Ternary::FALSE {
                        return result;
                    }
                } else {
                    // A type S is assignable to keyof T if S is assignable to
                    // keyof C, where C is the simplified form of T or, if T
                    // doesn't simplify, the constraint of T.
                    let constraint = c.get_simplified_type_or_constraint(target_type);
                    if let Some(constraint) = constraint {
                        // We require Ternary.True here such that circular
                        // constraints don't cause false positives. For
                        // example, given 'T extends { [K in keyof T]: string }',
                        // 'keyof T' has itself as its constraint and produces
                        // a Ternary.Maybe when related to other types.
                        let __arena___guard_index_flags = c.types.clone();
                        let __guard_index_flags = __arena___guard_index_flags.get(target).clone();
                        let index_flags = __guard_index_flags.as_index_type().index_flags;
                        let index_t = c.get_index_type_ex(
                            constraint,
                            index_flags | IndexFlags::NO_REDUCIBLE_CHECK,
                        );
                        if self.is_related_to(
                            c,
                            source,
                            index_t,
                            RecursionFlags::TARGET,
                            report_errors,
                        ) == Ternary::TRUE
                        {
                            return Ternary::TRUE;
                        }
                    } else if c.is_generic_mapped_type(target_type) {
                        // generic mapped types that don't simplify or have a
                        // constraint still have a very simple set of keys we
                        // can compare against - their nameType or
                        // constraintType. In many ways, this comparison is a
                        // deferred version of what `getIndexTypeForMappedType`
                        // does to actually resolve the keys for _non_-generic
                        // types
                        let name_type = c.get_name_type_from_mapped_type(target_type);
                        let constraint_type = c.get_constraint_type_from_mapped_type(target_type);
                        let target_keys;
                        if name_type.is_some()
                            && c.is_mapped_type_with_keyof_constraint_declaration(target_type)
                        {
                            // we need to get the apparent mappings and union
                            // them with the generic mappings, since some
                            // properties may be missing from the
                            // `constraintType` which will otherwise be mapped
                            // in the object
                            let mapped_keys =
                                c.get_apparent_mapped_type_keys(name_type.unwrap(), target_type);
                            // We still need to include the non-apparent (and
                            // thus still generic) keys in the target side of
                            // the comparison (in case they're in the source
                            // side)
                            target_keys = c.get_union_type(&[mapped_keys, name_type.unwrap()]);
                        } else if name_type.is_some() {
                            target_keys = name_type.unwrap();
                        } else {
                            target_keys = constraint_type.unwrap_or(c.never_type);
                        }
                        if self.is_related_to(
                            c,
                            source,
                            target_keys,
                            RecursionFlags::TARGET,
                            report_errors,
                        ) == Ternary::TRUE
                        {
                            return Ternary::TRUE;
                        }
                    }
                }
            }
        } else if target_flags.intersects(TypeFlags::CONDITIONAL) {
            // If we reach 10 levels of nesting for the same conditional type,
            // assume it is an infinitely expanding recursive conditional type
            // and bail out with a Ternary.Maybe result.
            if c.is_deeply_nested_type(target, &self.target_stack, 10) {
                return Ternary::MAYBE;
            }
            // We check for a relationship to a conditional type target only
            // when the conditional type has no 'infer' positions, is not
            // distributive or is distributive but doesn't reference the check
            // type parameter in either of the result types, and the source
            // isn't an instantiation of the same conditional type (as happens
            // when computing variance).
            let can_relate = {
                let __arena___guard_ct = c.types.clone();
                let __guard_ct = __arena___guard_ct.get(target).clone();
                let ct = __guard_ct.as_conditional_type();
                let root = ct.root.as_deref();
                let same_root = source_flags.intersects(TypeFlags::CONDITIONAL) && {
                    let __arena___guard_s_root = c.types.clone();
                    let __guard_s_root = __arena___guard_s_root.get(source).clone();
                    let s_root = __guard_s_root.as_conditional_type().root.as_deref();
                    match (s_root, root) {
                        (Some(a), Some(b)) => std::ptr::eq(a, b),
                        _ => false,
                    }
                };
                root.is_some_and(|root| {
                    root.infer_type_parameters.is_empty()
                        && !c.is_distribution_dependent(root)
                        && !same_root
                })
            };
            if can_relate {
                // Check if the conditional is always true or always false but
                // still deferred for distribution purposes.
                let (check_type, extends_type) = {
                    let __arena___guard_ct = c.types.clone();
                    let __guard_ct = __arena___guard_ct.get(target).clone();
                    let ct = __guard_ct.as_conditional_type();

                    (ct.check_type, ct.extends_type)
                };
                let __h7644_21 = c.get_permissive_instantiation(extends_type.unwrap_or(target));
                let __h7643_21 = c.get_permissive_instantiation(check_type.unwrap_or(target));

                let skip_true = !c.is_type_assignable_to(__h7643_21, __h7644_21);
                let __h7649_25 = c.get_restrictive_instantiation(extends_type.unwrap_or(target));
                let __h7648_25 = c.get_restrictive_instantiation(check_type.unwrap_or(target));

                let skip_false = !skip_true && c.is_type_assignable_to(__h7648_25, __h7649_25);
                // TODO: Find a nice way to include potential conditional type
                // breakdowns in error output, if they seem good (they usually
                // don't)
                if skip_true {
                    result = Ternary::TRUE;
                } else {
                    let true_type = c.get_true_type_from_conditional_type(target);
                    result = self.is_related_to_ex(
                        c,
                        source,
                        true_type,
                        RecursionFlags::TARGET,
                        false,
                        None,
                        intersection_state,
                    );
                }
                if result != Ternary::FALSE {
                    if skip_false {
                        result = result.and(Ternary::TRUE);
                    } else {
                        let false_type = c.get_false_type_from_conditional_type(target);
                        result = result.and(self.is_related_to_ex(
                            c,
                            source,
                            false_type,
                            RecursionFlags::TARGET,
                            false,
                            None,
                            intersection_state,
                        ));
                    }
                    if result != Ternary::FALSE {
                        return result;
                    }
                }
            }
        } else if target_flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
            if source_flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
                if Rc::ptr_eq(&self.relation(), &c.comparable_relation) {
                    let definitely_unrelated = Checker::template_literal_types_definitely_unrelated(
                        c.types_handle().get(source).as_template_literal_type(),
                        c.types_handle().get(target).as_template_literal_type(),
                    );
                    if definitely_unrelated {
                        return Ternary::FALSE;
                    }
                    return Ternary::TRUE;
                }
                // Report unreliable variance for type variables referenced in
                // template literal type placeholders. For example,
                // `foo-${number}` is related to `foo-${string}` even though
                // number isn't related to string.
                let mapper = c.report_unreliable_mapper;
                c.instantiate_type(source, Some(mapper));
            }
            if c.is_type_matched_by_template_literal_type(
                source,
                target,
                Some(&mut *self),
                Comparer::IsRelatedToWorker,
            ) {
                return Ternary::TRUE;
            }
        } else if target_flags.intersects(TypeFlags::STRING_MAPPING) {
            if !source_flags.intersects(TypeFlags::STRING_MAPPING)
                && c.is_member_of_string_mapping(source, target)
            {
                return Ternary::TRUE;
            }
        } else if c.is_generic_mapped_type(target)
            && !Rc::ptr_eq(&self.relation(), &c.identity_relation)
        {
            // Check if source type `S` is related to target type
            // `{ [P in Q]: T }` or `{ [P in Q as R]: T}`.
            let __arena___guard_keys_remapped = c.types.clone();
            let __guard_keys_remapped = __arena___guard_keys_remapped.get(target).clone();
            let keys_remapped = __guard_keys_remapped
                .as_mapped_type()
                .declaration
                .is_some_and(|d| {
                    let __program = c.program.clone().expect("program");
                    let nodes = __program.nodes((d).file_index());
                    nodes[d].as_mapped_type_node().name_type.is_some()
                });
            let template_type = c.get_template_type_from_mapped_type(target);
            let modifiers = crate::utilities::get_mapped_type_modifiers(c, target);
            if !modifiers.intersects(MappedTypeModifiers::EXCLUDE_OPTIONAL) {
                // If the mapped type has shape `{ [P in Q]: T[P] }`, source
                // `S` is related to target if `T` = `S`, i.e. `S` is related
                // to `{ [P in Q]: S[P] }`.
                if !keys_remapped
                    && template_type.is_some_and(|tt| {
                        c.types_handle()
                            .get(tt)
                            .flags
                            .intersects(TypeFlags::INDEXED_ACCESS)
                            && c.types_handle()
                                .get(tt)
                                .as_indexed_access_type()
                                .object_type
                                == Some(source)
                            && c.types_handle().get(tt).as_indexed_access_type().index_type
                                == c.get_type_parameter_from_mapped_type(target)
                    })
                {
                    return Ternary::TRUE;
                }
                if !c.is_generic_mapped_type(source) {
                    // If target has shape `{ [P in Q as R]: T}`, then its
                    // keys have type `R`. If target has shape `{ [P in Q]: T
                    // }`, then its keys have type `Q`.
                    let target_keys = if keys_remapped {
                        c.get_name_type_from_mapped_type(target)
                    } else {
                        c.get_constraint_type_from_mapped_type(target)
                    };
                    let target_keys = target_keys.unwrap_or(c.never_type);
                    // Type of the keys of source type `S`, i.e. `keyof S`.
                    let source_keys = c.get_index_type_ex(source, IndexFlags::NO_INDEX_SIGNATURES);
                    let include_optional =
                        modifiers.intersects(MappedTypeModifiers::INCLUDE_OPTIONAL);
                    let mut filtered_by_applicability: Option<TypeId> = None;
                    if include_optional {
                        filtered_by_applicability =
                            c.intersect_types(Some(target_keys), Some(source_keys));
                    }
                    // A source type `S` is related to a target type
                    // `{ [P in Q]: T }` if `Q` is related to `keyof S` and
                    // `S[Q]` is related to `T`.
                    // A source type `S` is related to a target type
                    // `{ [P in Q as R]: T }` if `R` is related to `keyof S`
                    // and `S[R]` is related to `T.
                    // A source type `S` is related to a target type
                    // `{ [P in Q]?: T }` if some constituent `Q'` of `Q` is
                    // related to `keyof S` and `S[Q']` is related to `T`.
                    // A source type `S` is related to a target type
                    // `{ [P in Q as R]?: T }` if some constituent `R'` of `R`
                    // is related to `keyof S` and `S[R']` is related to `T`.
                    if include_optional
                        && !filtered_by_applicability.is_some_and(|f| {
                            c.types_handle().get_ref(f).flags.intersects(TypeFlags::NEVER)
                        })
                        || !include_optional
                            && self.is_related_to(
                                c,
                                target_keys,
                                source_keys,
                                RecursionFlags::BOTH,
                                false,
                            ) != Ternary::FALSE
                    {
                        let template_type = c.get_template_type_from_mapped_type(target);
                        let type_parameter = c.get_type_parameter_from_mapped_type(target);
                        if let (Some(template_type), Some(type_parameter)) =
                            (template_type, type_parameter)
                        {
                            // Fastpath: When the template type has the form
                            // `Obj[P]` where `P` is the mapped type
                            // parameter, directly compare source `S` with
                            // `Obj` to avoid creating the (potentially very
                            // large) number of new intermediate types made by
                            // manufacturing `S[P]`.
                            let non_null_component =
                                c.extract_types_of_kind(template_type, !TypeFlags::NULLABLE);
                            let mut indexing_type = type_parameter;

                            if !keys_remapped
                                && c.types_handle()
                                    .get(non_null_component)
                                    .flags
                                    .intersects(TypeFlags::INDEXED_ACCESS)
                                && c.types_handle()
                                    .get(non_null_component)
                                    .as_indexed_access_type()
                                    .index_type
                                    == Some(type_parameter)
                            {
                                let __arena___guard_object_type = c.types.clone();
                                let __guard_object_type =
                                    __arena___guard_object_type.get(non_null_component).clone();
                                let object_type = __guard_object_type
                                    .as_indexed_access_type()
                                    .object_type
                                    .unwrap_or(c.never_type);
                                result = self.is_related_to(
                                    c,
                                    source,
                                    object_type,
                                    RecursionFlags::TARGET,
                                    report_errors,
                                );
                                if result != Ternary::FALSE {
                                    return result;
                                }
                            } else {
                                // We need to compare the type of a property
                                // on the source type `S` to the type of the
                                // same property on the target type, so we
                                // need to construct an indexing type
                                // representing a property, and then use
                                // indexing type to index the source type for
                                // comparison.
                                // If the target type has shape `{ [P in Q]: T }`,
                                // then a property of the target has type `P`.
                                // If the target type has shape `{ [P in Q]?: T }`,
                                // then a property of the target has type `P`,
                                // but the property is optional, so we only
                                // want to compare properties `P` that are
                                // common between `keyof S` and `Q`.
                                // If the target type has shape `{ [P in Q as R]: T }`,
                                // then a property of the target has type `R`.
                                // If the target type has shape `{ [P in Q as R]?: T }`,
                                // then a property of the target has type `R`,
                                // but the property is optional, so we only
                                // want to compare properties `R` that are
                                // common between `keyof S` and `R`.
                                if keys_remapped {
                                    indexing_type =
                                        filtered_by_applicability.unwrap_or(target_keys);
                                } else if let Some(filtered) = filtered_by_applicability {
                                    indexing_type =
                                        c.get_intersection_type(&[filtered, type_parameter]);
                                }
                                let indexed_access_type =
                                    c.get_indexed_access_type(source, indexing_type);
                                // Compare `S[indexingType]` to `T`, where `T`
                                // is the type of a property of the target
                                // type.
                                result = self.is_related_to(
                                    c,
                                    indexed_access_type,
                                    template_type,
                                    RecursionFlags::BOTH,
                                    report_errors,
                                );
                                if result != Ternary::FALSE {
                                    return result;
                                }
                            }
                        }
                    }
                    original_error_chain = self.error_chain.take();
                    self.restore_error_state(&save_error_state);
                }
            }
        }
        let (source_flags, target_flags) = {
            let __arena_s = c.types.clone();
            let s = __arena_s.get_ref(source);
            (s.flags, c.types_handle().get_ref(target).flags)
        };
        if source_flags.intersects(TypeFlags::TYPE_VARIABLE) {
            // IndexedAccess comparisons are handled above in the
            // `target.flags&TypeFlagsIndexedAccess` branch
            if !source_flags.intersects(TypeFlags::INDEXED_ACCESS)
                || !target_flags.intersects(TypeFlags::INDEXED_ACCESS)
            {
                let constraint = c.get_constraint_of_type(source).unwrap_or(c.unknown_type);
                // hi-speed no-this-instantiation check (less accurate, but
                // avoids costly `this`-instantiation when the constraint will
                // suffice), see #28231 for report on why this is needed
                result = self.is_related_to_ex(
                    c,
                    constraint,
                    target,
                    RecursionFlags::SOURCE,
                    false,
                    None,
                    intersection_state,
                );
                if result != Ternary::FALSE {
                    return result;
                }
                let constraint_with_this =
                    c.get_type_with_this_argument(constraint, Some(source), false);
                result = self.is_related_to_ex(
                    c,
                    constraint_with_this,
                    target,
                    RecursionFlags::SOURCE,
                    report_errors
                        && constraint != c.unknown_type
                        && !target_flags.intersects(source_flags & TypeFlags::TYPE_PARAMETER),
                    None,
                    intersection_state,
                );
                if result != Ternary::FALSE {
                    return result;
                }
                if c.is_mapped_type_generic_indexed_access(source) {
                    // For an indexed access type { [P in K]: E}[X], above we
                    // have already explored an instantiation of E with X
                    // substituted for P. We also want to explore type
                    // { [P in K]: E }[C], where C is the constraint of X.
                    let __arena___guard_index_type = c.types.clone();
                    let __guard_index_type = __arena___guard_index_type.get(source).clone();
                    let index_type = __guard_index_type.as_indexed_access_type().index_type;
                    let index_constraint = index_type.and_then(|i| c.get_constraint_of_type(i));
                    if let Some(index_constraint) = index_constraint {
                        let __arena___guard_object_type = c.types.clone();
                        let __guard_object_type = __arena___guard_object_type.get(source).clone();
                        let object_type = __guard_object_type
                            .as_indexed_access_type()
                            .object_type
                            .unwrap_or(c.never_type);
                        let __h7937_29 = c.get_indexed_access_type(object_type, index_constraint);

                        result = self.is_related_to(
                            c,
                            __h7937_29,
                            target,
                            RecursionFlags::SOURCE,
                            report_errors,
                        );
                        if result != Ternary::FALSE {
                            return result;
                        }
                    }
                }
            }
        } else if source_flags.intersects(TypeFlags::INDEX) {
            let __arena___guard_index_target = c.types.clone();
            let __guard_index_target = __arena___guard_index_target.get(source).clone();
            let index_target = __guard_index_target.as_index_type().target;
            let is_deferred_mapped_index = index_target.is_some_and(|t| {
                c.should_defer_index_type(
                    t,
                    c.types_handle().get(source).as_index_type().index_flags,
                ) && c
                    .types_handle()
                    .get(t)
                    .object_flags
                    .intersects(ObjectFlags::MAPPED)
            });
            result = self.is_related_to(
                c,
                c.string_number_symbol_type,
                target,
                RecursionFlags::SOURCE,
                report_errors && !is_deferred_mapped_index,
            );
            if result != Ternary::FALSE {
                return result;
            }
            if is_deferred_mapped_index {
                let mapped_type = index_target.unwrap();
                let name_type = c.get_name_type_from_mapped_type(mapped_type);
                // Unlike on the target side, on the source side we do *not*
                // include the generic part of the `nameType`, since that
                // comes from a (potentially anonymous) mapped type local type
                // parameter, so that'd never assign outside the mapped type
                // body, but we still want to allow assignments of index types
                // of identical (or similar enough) mapped types.
                // eg, `keyof {[X in keyof A]: Obj[X]}` should be assignable
                // to `keyof {[Y in keyof A]: Tup[Y]}` because both map over
                // the same set of keys (`keyof A`).
                // Without this source-side breakdown, a `keyof {[X in keyof
                // A]: Obj[X]}` style type won't be assignable to anything
                // except itself, which is much too strict.
                let source_mapped_keys = if name_type.is_some()
                    && c.is_mapped_type_with_keyof_constraint_declaration(mapped_type)
                {
                    c.get_apparent_mapped_type_keys(name_type.unwrap(), mapped_type)
                } else if name_type.is_some() {
                    name_type.unwrap()
                } else {
                    c.get_constraint_type_from_mapped_type(mapped_type)
                        .unwrap_or(c.never_type)
                };
                result = self.is_related_to(
                    c,
                    source_mapped_keys,
                    target,
                    RecursionFlags::SOURCE,
                    report_errors,
                );
                if result != Ternary::FALSE {
                    return result;
                }
            }
        } else if source_flags.intersects(TypeFlags::CONDITIONAL) {
            // If we reach 10 levels of nesting for the same conditional type,
            // assume it is an infinitely expanding recursive conditional type
            // and bail out with a Ternary.Maybe result.
            if c.is_deeply_nested_type(source, &self.source_stack, 10) {
                return Ternary::MAYBE;
            }
            if target_flags.intersects(TypeFlags::CONDITIONAL) {
                // Two conditional types 'T1 extends U1 ? X1 : Y1' and
                // 'T2 extends U2 ? X2 : Y2' are related if one of T1 and T2
                // is related to the other, U1 and U2 are identical types, X1
                // is related to X2, and Y1 is related to Y2.
                let (source_params, mut source_extends) = {
                    let __arena___guard_ct = c.types.clone();
                    let __guard_ct = __arena___guard_ct.get(source).clone();
                    let ct = __guard_ct.as_conditional_type();
                    (
                        ct.root
                            .as_ref()
                            .map(|r| r.infer_type_parameters.clone())
                            .unwrap_or_default(),
                        ct.extends_type,
                    )
                };
                let mut mapper: Option<crate::mapper::TypeMapperId> = None;
                if !source_params.is_empty() {
                    // If the source has infer type parameters, we instantiate
                    // them in the context of the target
                    let ctx = {
                        // `r.isRelatedToWorker` — a `TypeComparer` bound to the
                        // live `*Relater` in Go; the port gives the closure a
                        // snapshot so the in-flight recursion stacks,
                        // expanding flags, and maybe-keys carry over (the
                        // `SharedRelation` cache is `Rc`-shared either way).
                        let cell = std::cell::RefCell::new(self.snapshot());
                        let compare: Box<crate::types::TypeComparer<'static>> =
                            Box::new(move |c: &mut Checker, s, t, re| {
                                cell.borrow_mut().is_related_to_worker(c, s, t, re)
                            });
                        c.new_inference_context(
                            &source_params,
                            None,
                            InferenceFlags::default(),
                            Some(compare),
                        )
                    };
                    let mut inferences =
                        std::mem::take(&mut c.inference_contexts[ctx.index()].inferences);
                    let __arena___guard_target_extends = c.types.clone();
                    let __guard_target_extends = __arena___guard_target_extends.get(target).clone();
                    let target_extends = __guard_target_extends
                        .as_conditional_type()
                        .extends_type
                        .unwrap_or(c.never_type);
                    c.infer_types(
                        &mut inferences,
                        target_extends,
                        source_extends.unwrap_or(c.never_type),
                        InferencePriority::NO_CONSTRAINTS | InferencePriority::ALWAYS_STRICT,
                        false,
                    );
                    c.inference_contexts[ctx.index()].inferences = inferences;
                    let ctx_mapper = c.inference_contexts[ctx.index()].mapper;
                    source_extends = Some(
                        c.instantiate_type(source_extends.unwrap_or(c.never_type), ctx_mapper),
                    );
                    mapper = ctx_mapper;
                }
                let (s_check, t_check, t_extends) = {
                    let __arena___guard_s = c.types.clone();
                    let __guard_s = __arena___guard_s.get(source).clone();
                    let s = __guard_s.as_conditional_type();
                    let __arena___guard_t = c.types.clone();
                    let __guard_t = __arena___guard_t.get(target).clone();
                    let t = __guard_t.as_conditional_type();
                    (s.check_type, t.check_type, t.extends_type)
                };
                if let (Some(source_extends), Some(t_extends)) = (source_extends, t_extends) {
                    if c.is_type_identical_to(source_extends, t_extends)
                        && (self.is_related_to(
                            c,
                            s_check.unwrap_or(source),
                            t_check.unwrap_or(target),
                            RecursionFlags::BOTH,
                            false,
                        ) != Ternary::FALSE
                            || self.is_related_to(
                                c,
                                t_check.unwrap_or(target),
                                s_check.unwrap_or(source),
                                RecursionFlags::BOTH,
                                false,
                            ) != Ternary::FALSE)
                    {
                        let __h8095_29 = c.get_true_type_from_conditional_type(source);

                        let s_true = c.instantiate_type(__h8095_29, mapper);
                        let t_true = c.get_true_type_from_conditional_type(target);
                        result = self.is_related_to(
                            c,
                            s_true,
                            t_true,
                            RecursionFlags::BOTH,
                            report_errors,
                        );
                        if result != Ternary::FALSE {
                            let s_false = c.get_false_type_from_conditional_type(source);
                            let t_false = c.get_false_type_from_conditional_type(target);
                            result = result.and(self.is_related_to(
                                c,
                                s_false,
                                t_false,
                                RecursionFlags::BOTH,
                                report_errors,
                            ));
                        }
                        if result != Ternary::FALSE {
                            return result;
                        }
                    }
                }
            }
            // conditionals can be related to one another via normal
            // constraint, as, eg, `A extends B ? O : never` should be
            // assignable to `O` when `O` is a conditional (`never` is
            // trivially assignable to `O`, as is `O`!).
            let default_constraint = c.get_default_constraint_of_conditional_type(source);
            {
                let default_constraint = default_constraint;
                result = self.is_related_to(
                    c,
                    default_constraint,
                    target,
                    RecursionFlags::SOURCE,
                    report_errors,
                );
                if result != Ternary::FALSE {
                    return result;
                }
            }
            // conditionals aren't related to one another via distributive
            // constraint as it is much too inaccurate and allows way more
            // assignments than are desirable (since it maps the source check
            // type to its constraint, it loses information).
            if !target_flags.intersects(TypeFlags::CONDITIONAL)
                && c.has_non_circular_base_constraint(source)
            {
                let distributive_constraint =
                    c.get_constraint_of_distributive_conditional_type(source);
                if let Some(distributive_constraint) = distributive_constraint {
                    self.restore_error_state(&save_error_state);
                    result = self.is_related_to(
                        c,
                        distributive_constraint,
                        target,
                        RecursionFlags::SOURCE,
                        report_errors,
                    );
                    if result != Ternary::FALSE {
                        return result;
                    }
                }
            }
        } else if source_flags.intersects(TypeFlags::TEMPLATE_LITERAL)
            && !target_flags.intersects(TypeFlags::OBJECT)
        {
            if !target_flags.intersects(TypeFlags::TEMPLATE_LITERAL) {
                if let Some(constraint) = c.get_base_constraint_of_type(source) {
                    if constraint != source {
                        result = self.is_related_to(
                            c,
                            constraint,
                            target,
                            RecursionFlags::SOURCE,
                            report_errors,
                        );
                        if result != Ternary::FALSE {
                            return result;
                        }
                    }
                }
            }
        } else if source_flags.intersects(TypeFlags::STRING_MAPPING) {
            if target_flags.intersects(TypeFlags::STRING_MAPPING) {
                if c.types_handle().get_ref(source).symbol() != c.types_handle().get_ref(target).symbol() {
                    return Ternary::FALSE;
                }
                let __arena___guard_s_target = c.types.clone();
                let __guard_s_target = __arena___guard_s_target.get(source).clone();
                let s_target = __guard_s_target.as_string_mapping_type().target;
                let __arena___guard_t_target = c.types.clone();
                let __guard_t_target = __arena___guard_t_target.get(target).clone();
                let t_target = __guard_t_target.as_string_mapping_type().target;
                result = self.is_related_to(
                    c,
                    s_target.unwrap_or(source),
                    t_target.unwrap_or(target),
                    RecursionFlags::BOTH,
                    report_errors,
                );
                if result != Ternary::FALSE {
                    return result;
                }
            } else {
                if let Some(constraint) = c.get_base_constraint_of_type(source) {
                    result = self.is_related_to(
                        c,
                        constraint,
                        target,
                        RecursionFlags::SOURCE,
                        report_errors,
                    );
                    if result != Ternary::FALSE {
                        return result;
                    }
                }
            }
        } else {
            // An empty object type is related to any mapped type that
            // includes a '?' modifier.
            if !Rc::ptr_eq(&self.relation(), &c.subtype_relation)
                && !Rc::ptr_eq(&self.relation(), &c.strict_subtype_relation)
                && crate::utilities::is_partial_mapped_type(c, target)
                && c.is_empty_object_type(source)
            {
                return Ternary::TRUE;
            }
            if c.is_generic_mapped_type(target) {
                if c.is_generic_mapped_type(source) {
                    result = self.mapped_type_related_to(c, source, target, report_errors);
                    if result != Ternary::FALSE {
                        return result;
                    }
                }
                return Ternary::FALSE;
            }
            let source_is_primitive = source_flags.intersects(TypeFlags::PRIMITIVE);
            if !Rc::ptr_eq(&self.relation(), &c.identity_relation) {
                source = c.get_apparent_type(source);
            } else if c.is_generic_mapped_type(source) {
                return Ternary::FALSE;
            }
            let (source_flags, target_flags) = {
                let __arena_s = c.types.clone();
                let s = __arena_s.get_ref(source);
                (s.flags, c.types_handle().get_ref(target).flags)
            };
            let (source_object_flags, target_object_flags) = {
                let __arena_s = c.types.clone();
                let s = __arena_s.get_ref(source);
                (s.object_flags, c.types_handle().get_ref(target).object_flags)
            };
            if source_object_flags.intersects(ObjectFlags::REFERENCE)
                && target_object_flags.intersects(ObjectFlags::REFERENCE)
                && c.types_handle().get(source).target() == c.types_handle().get(target).target()
                && !crate::checker_core::is_tuple_type(&c.types, source)
                && !c.is_marker_type(source)
                && !c.is_marker_type(target)
            {
                // When strictNullChecks is disabled, the element type of the
                // empty array literal is undefinedWideningType, and an empty
                // array literal wouldn't be assignable to a `never[]` without
                // this check.
                if c.is_empty_array_literal_type(source) {
                    return Ternary::TRUE;
                }
                // We have type references to the same generic type, and the
                // type references are not marker type references (which are
                // intended by be compared structurally). Obtain the variance
                // information for the type parameters and relate the type
                // arguments accordingly.
                let variances =
                    c.get_variances(c.types_handle().get(source).target().unwrap_or(source));
                // We return Ternary.Maybe for a recursive invocation of
                // getVariances (signaled by emptyArray). This effectively
                // means we measure variance only from type parameter
                // occurrences that aren't nested in recursive instantiations
                // of the generic type.
                if variances.is_empty() {
                    return Ternary::UNKNOWN;
                }
                let source_args = c.get_type_arguments(source);
                let target_args = c.get_type_arguments(target);
                relate_variances!(&source_args, &target_args, &variances);
            } else if c.is_array_type(target)
                && (c.is_readonly_array_type(target)
                    && crate::checker_d::every_type(c, source, |c: &mut Checker, t| {
                        c.is_array_or_tuple_type(t)
                    })
                    || crate::checker_d::every_type(c, source, |_c, t| {
                        crate::utilities::is_mutable_tuple_type(&_c.types, t)
                    }))
            {
                if !Rc::ptr_eq(&self.relation(), &c.identity_relation) {
                    let s_index = c.get_index_type_of_type_ex(source, c.number_type, c.any_type);
                    let t_index = c.get_index_type_of_type_ex(target, c.number_type, c.any_type);
                    return self.is_related_to(
                        c,
                        s_index,
                        t_index,
                        RecursionFlags::BOTH,
                        report_errors,
                    );
                }
                // By flags alone, we know that the `target` is a readonly
                // array while the source is a normal array or tuple or
                // `target` is an array and source is a tuple - in both cases
                // the types cannot be identical, by construction
                return Ternary::FALSE;
            } else if crate::utilities::is_generic_tuple_type(&c.types, source)
                && crate::checker_core::is_tuple_type(&c.types, target)
                && !crate::utilities::is_generic_tuple_type(&c.types, target)
            {
                let constraint = c.get_base_constraint_or_type(source);
                if constraint != source {
                    return self.is_related_to(
                        c,
                        constraint,
                        target,
                        RecursionFlags::SOURCE,
                        report_errors,
                    );
                }
            } else if (Rc::ptr_eq(&self.relation(), &c.subtype_relation)
                || Rc::ptr_eq(&self.relation(), &c.strict_subtype_relation))
                && c.is_empty_object_type(target)
                && c.types_handle()
                    .get(target)
                    .object_flags
                    .intersects(ObjectFlags::FRESH_LITERAL)
                && !c.is_empty_object_type(source)
            {
                return Ternary::FALSE;
            }
            // Even if relationship doesn't hold for unions, intersections, or
            // generic type references, it may hold in a structural
            // comparison.
            // In a check of the form X = A & B, we will have previously
            // checked if A relates to X or B relates to X. Failing both of
            // those we want to check if the aggregation of A and B's members
            // structurally relates to X. Thus, we include intersection types
            // on the source side here.
            if source_flags.intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION)
                && target_flags.intersects(TypeFlags::OBJECT)
            {
                // Report structural errors only if we haven't reported any
                // errors yet
                let report_structural_errors = report_errors
                    && self.error_chain.as_ref().map(|e| &**e as *const ErrorChain)
                        == save_error_state
                            .error_chain
                            .as_ref()
                            .map(|e| &**e as *const ErrorChain)
                    && !source_is_primitive;
                result = self.properties_related_to(
                    c,
                    source,
                    target,
                    report_structural_errors,
                    &Set::new(),
                    false,
                    intersection_state,
                );
                if result != Ternary::FALSE {
                    result = result.and(self.signatures_related_to(
                        c,
                        source,
                        target,
                        SignatureKind::Call,
                        report_structural_errors,
                        intersection_state,
                    ));
                    if result != Ternary::FALSE {
                        result = result.and(self.signatures_related_to(
                            c,
                            source,
                            target,
                            SignatureKind::Construct,
                            report_structural_errors,
                            intersection_state,
                        ));
                        if result != Ternary::FALSE {
                            result = result.and(self.index_signatures_related_to(
                                c,
                                source,
                                target,
                                source_is_primitive,
                                report_structural_errors,
                                intersection_state,
                            ));
                        }
                    }
                }
                if result != Ternary::FALSE {
                    if !variance_check_failed {
                        return result;
                    }
                    if original_error_chain.is_some() {
                        self.error_chain = original_error_chain.take();
                    } else if self.error_chain.is_none() {
                        self.error_chain = save_error_state.error_chain.clone();
                    }
                    // Use variance error (there is no structural one) and
                    // return false
                }
            }
            // If S is an object type and T is a discriminated union, S may be
            // related to T if there exists a constituent of T for every
            // combination of the discriminants of S with respect to T. We do
            // not report errors here, as we will use the existing error
            // result from checking each constituent of the union.
            if source_flags.intersects(TypeFlags::OBJECT | TypeFlags::INTERSECTION)
                && target_flags.intersects(TypeFlags::UNION)
            {
                let object_only_target = c.extract_types_of_kind(
                    target,
                    TypeFlags::OBJECT | TypeFlags::INTERSECTION | TypeFlags::SUBSTITUTION,
                );
                if c.types_handle()
                    .get(object_only_target)
                    .flags
                    .intersects(TypeFlags::UNION)
                {
                    let result =
                        self.type_related_to_discriminated_type(c, source, object_only_target);
                    if result != Ternary::FALSE {
                        return result;
                    }
                }
            }
        }
        Ternary::FALSE
    }

    /// `(r *Relater) typeArgumentsRelatedTo`.
    fn type_arguments_related_to(
        &mut self,
        c: &mut Checker,
        sources: &[TypeId],
        targets: &[TypeId],
        variances: &[VarianceFlags],
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        if sources.len() != targets.len() && Rc::ptr_eq(&self.relation(), &c.identity_relation) {
            return Ternary::FALSE;
        }
        let length = sources.len().min(targets.len());
        let mut result = Ternary::TRUE;
        for i in 0..length {
            // When variance information isn't available we default to
            // covariance. This happens in the process of computing variance
            // information for recursive types and when comparing 'this' type
            // arguments.
            let variance_flags = if i < variances.len() {
                variances[i]
            } else {
                VarianceFlags::COVARIANT
            };
            let variance = variance_flags & VarianceFlags::VARIANCE_MASK;
            // We ignore arguments for independent type parameters (because
            // they're never witnessed).
            if variance != VarianceFlags::INDEPENDENT {
                let s = sources[i];
                let t = targets[i];
                let related;
                if variance_flags.intersects(VarianceFlags::UNMEASURABLE) {
                    // Even an `Unmeasurable` variance works out without a
                    // structural check if the source and target are
                    // _identical_. We can't simply assume invariance, because
                    // `Unmeasurable` marks nonlinear relations, for example,
                    // a relation tainted by the `-?` modifier in a mapped
                    // type (where, no matter how the inputs are related, the
                    // outputs still might not be)
                    if Rc::ptr_eq(&self.relation(), &c.identity_relation) {
                        related = self.is_related_to(c, s, t, RecursionFlags::BOTH, false);
                    } else {
                        related = c.compare_types_identical(s, t);
                    }
                } else {
                    // Propagate unreliable variance flag in variance
                    // computations
                    if !c.variance_stack.is_empty()
                        && variance_flags.intersects(VarianceFlags::UNRELIABLE)
                    {
                        let mapper = c.report_unreliable_mapper;
                        c.instantiate_type(s, Some(mapper));
                    }
                    if variance == VarianceFlags::COVARIANT {
                        related = self.is_related_to_ex(
                            c,
                            s,
                            t,
                            RecursionFlags::BOTH,
                            report_errors,
                            None,
                            intersection_state,
                        );
                    } else if variance == VarianceFlags::CONTRAVARIANT {
                        related = self.is_related_to_ex(
                            c,
                            t,
                            s,
                            RecursionFlags::BOTH,
                            report_errors,
                            None,
                            intersection_state,
                        );
                    } else if variance == VarianceFlags::BIVARIANT {
                        // In the bivariant case we first compare
                        // contravariantly without reporting errors. Then, if
                        // that doesn't succeed, we compare covariantly with
                        // error reporting. Thus, error elaboration will be
                        // based on the covariant check, which is generally
                        // easier to reason about.
                        let mut related_inner =
                            self.is_related_to(c, t, s, RecursionFlags::BOTH, false);
                        if related_inner == Ternary::FALSE {
                            related_inner = self.is_related_to_ex(
                                c,
                                s,
                                t,
                                RecursionFlags::BOTH,
                                report_errors,
                                None,
                                intersection_state,
                            );
                        }
                        related = related_inner;
                    } else {
                        // In the invariant case we first compare covariantly,
                        // and only when that succeeds do we proceed to
                        // compare contravariantly. Thus, error elaboration
                        // will typically be based on the covariant check.
                        let mut related_inner = self.is_related_to_ex(
                            c,
                            s,
                            t,
                            RecursionFlags::BOTH,
                            report_errors,
                            None,
                            intersection_state,
                        );
                        if related_inner != Ternary::FALSE {
                            related_inner = related_inner.and(self.is_related_to_ex(
                                c,
                                t,
                                s,
                                RecursionFlags::BOTH,
                                report_errors,
                                None,
                                intersection_state,
                            ));
                        }
                        related = related_inner;
                    }
                }
                if related == Ternary::FALSE {
                    return Ternary::FALSE;
                }
                result = result.and(related);
            }
        }
        result
    }

    /// `(r *Relater) mappedTypeRelatedTo` — a type [P in S]: X is related to
    /// a type [Q in T]: Y if T is related to S and X' is related to Y, where
    /// X' is an instantiation of X in which P is replaced with Q. Notice
    /// that S and T are contra-variant whereas X and Y are co-variant.
    fn mapped_type_related_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
    ) -> Ternary {
        let modifiers_related = Rc::ptr_eq(&self.relation(), &c.comparable_relation)
            || Rc::ptr_eq(&self.relation(), &c.identity_relation)
                && crate::utilities::get_mapped_type_modifiers(c, source)
                    == crate::utilities::get_mapped_type_modifiers(c, target)
            || !Rc::ptr_eq(&self.relation(), &c.identity_relation)
                && c.get_combined_mapped_type_optionality(source)
                    <= c.get_combined_mapped_type_optionality(target);
        if modifiers_related {
            if let Some(target_constraint) = c.get_constraint_type_from_mapped_type(target) {
                let source_constraint = {
                    let sc = c.get_constraint_type_from_mapped_type(source);
                    let mapper = if c.get_combined_mapped_type_optionality(source) < 0 {
                        c.report_unmeasurable_mapper
                    } else {
                        c.report_unreliable_mapper
                    };
                    sc.map(|sc| c.instantiate_type(sc, Some(mapper)))
                };
                if let Some(source_constraint) = source_constraint {
                    let result = self.is_related_to(
                        c,
                        target_constraint,
                        source_constraint,
                        RecursionFlags::BOTH,
                        report_errors,
                    );
                    if result != Ternary::FALSE {
                        let (s_param, t_param) = (
                            c.get_type_parameter_from_mapped_type(source),
                            c.get_type_parameter_from_mapped_type(target),
                        );
                        if let (Some(s_param), Some(t_param)) = (s_param, t_param) {
                            let mapper = crate::mapper::new_simple_type_mapper(c, s_param, t_param);
                            let s_name = c
                                .get_name_type_from_mapped_type(source)
                                .map(|n| c.instantiate_type(n, Some(mapper)));
                            let t_name = c
                                .get_name_type_from_mapped_type(target)
                                .map(|n| c.instantiate_type(n, Some(mapper)));
                            if s_name == t_name {
                                let s_template = c
                                    .get_template_type_from_mapped_type(source)
                                    .map(|t| c.instantiate_type(t, Some(mapper)));
                                let t_template = c.get_template_type_from_mapped_type(target);
                                if let (Some(s_template), Some(t_template)) =
                                    (s_template, t_template)
                                {
                                    return result.and(self.is_related_to(
                                        c,
                                        s_template,
                                        t_template,
                                        RecursionFlags::BOTH,
                                        report_errors,
                                    ));
                                }
                            }
                        }
                    }
                }
            }
        }
        Ternary::FALSE
    }

    /// `(r *Relater) typeRelatedToDiscriminatedType`.
    ///
    /// 1. Generate the combinations of discriminant properties & types
    ///    'source' can satisfy.
    ///    a. If the number of combinations is above a set limit, the
    ///       comparison is too complex.
    /// 2. Filter 'target' to the subset of types whose discriminants exist
    ///    in the matrix.
    ///    a. If 'target' does not satisfy all discriminants in the matrix,
    ///       'source' is not related.
    /// 3. For each type in the filtered 'target', determine if all
    ///    non-discriminant properties of 'target' are related to a property
    ///    in 'source'.
    ///
    /// NOTE: See ~/tests/cases/conformance/types/typeRelationships/
    /// assignmentCompatibility/assignmentCompatWithDiscriminatedUnion.ts
    /// for examples.
    fn type_related_to_discriminated_type(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
    ) -> Ternary {
        let source_properties = c.get_properties_of_type(source);
        let source_properties_filtered = c.find_discriminant_properties(&source_properties, target);
        if source_properties_filtered.is_empty() {
            return Ternary::FALSE;
        }
        // Though we could compute the number of combinations as we generate
        // the matrix, this would incur additional memory overhead due to
        // array allocations. To reduce this overhead, we first compute the
        // number of combinations to ensure we will not surpass our fixed
        // limit before incurring the cost of any allocations:
        let mut num_combinations = 1usize;
        for &source_property in &source_properties_filtered {
            let prop_type = c.get_non_missing_type_of_symbol(source_property);
            num_combinations *= crate::checker_d::count_types(&c.types, prop_type);
            if num_combinations > 25 {
                if let Some(tr) = &c.tracer {
                    let mut args = TraceArgs::new();
                    args.insert("sourceId".to_string(), source.0.into());
                    args.insert("targetId".to_string(), target.0.into());
                    args.insert(
                        "numCombinations".to_string(),
                        (num_combinations as i64).into(),
                    );
                    tr.instant(
                        tsc_tracing::PHASE_CHECK_TYPES,
                        "typeRelatedToDiscriminatedType_DepthLimit",
                        &args,
                    );
                }
                return Ternary::FALSE;
            }
            if num_combinations == 0 {
                return Ternary::FALSE;
            }
        }
        // Compute the set of types for each discriminant property.
        let mut source_discriminant_types: Vec<Vec<TypeId>> =
            Vec::with_capacity(source_properties_filtered.len());
        let mut excluded_properties: Set<String> = Set::new();
        for &source_property in &source_properties_filtered {
            let source_property_type = c.get_non_missing_type_of_symbol(source_property);
            source_discriminant_types.push(
                c.types_handle()
                    .get(source_property_type)
                    .distributed(source_property_type),
            );
            excluded_properties.add(c.sym(source_property).name.clone());
        }
        // Build the cartesian product
        let mut discriminant_combinations: Vec<Vec<TypeId>> = Vec::with_capacity(num_combinations);
        for i in 0..num_combinations {
            let mut combination = vec![TypeId::NONE; source_discriminant_types.len()];
            let mut n = i;
            for j in (0..source_discriminant_types.len()).rev() {
                let source_types = &source_discriminant_types[j];
                let length = source_types.len();
                combination[j] = source_types[n % length];
                n /= length;
            }
            discriminant_combinations.push(combination);
        }
        // Match each combination of the cartesian product of discriminant
        // properties to one or more constituents of 'target'. If any
        // combination does not have a match then 'source' is not relatable.
        let mut matching_types: Vec<TypeId> = Vec::new();
        let __arena_target_types = c.types.clone();
        let target_types = __arena_target_types.get_ref(target).types().to_vec();
        'combinations: for combination in &discriminant_combinations {
            let mut has_match = false;
            'outer: for &t in &target_types {
                for i in 0..source_properties_filtered.len() {
                    let source_property = source_properties_filtered[i];
                    let target_property = {
                        let name = c.sym_name_rc(source_property);
                        c.get_property_of_type(t, &name)
                    };
                    let Some(target_property) = target_property else {
                        continue 'outer;
                    };
                    if source_property == target_property {
                        continue;
                    }
                    // We compare the source property to the target in the
                    // context of a single discriminant type.
                    let combination_type = combination[i];
                    let related = self.property_related_to(
                        c,
                        source,
                        target,
                        source_property,
                        target_property,
                        &mut |_: &mut Checker, _: SymbolId| Some(combination_type),
                        false,
                        IntersectionState::NONE,
                        c.strict_null_checks
                            || Rc::ptr_eq(&self.relation(), &c.comparable_relation),
                    );
                    // If the target property could not be found, or if the
                    // properties were not related, then this constituent is
                    // not a match.
                    if related == Ternary::FALSE {
                        continue 'outer;
                    }
                }
                matching_types = core::append_if_unique(&matching_types, t).into_owned();
                has_match = true;
            }
            if !has_match {
                // We failed to match any type for this combination.
                return Ternary::FALSE;
            }
            continue 'combinations;
        }
        // Compare the remaining non-discriminant properties of each match.
        let mut result = Ternary::TRUE;
        for &t in &matching_types {
            result = result.and(self.properties_related_to(
                c,
                source,
                t,
                false,
                &excluded_properties,
                false,
                IntersectionState::NONE,
            ));
            if result != Ternary::FALSE {
                result = result.and(self.signatures_related_to(
                    c,
                    source,
                    t,
                    SignatureKind::Call,
                    false,
                    IntersectionState::NONE,
                ));
                if result != Ternary::FALSE {
                    result = result.and(self.signatures_related_to(
                        c,
                        source,
                        t,
                        SignatureKind::Construct,
                        false,
                        IntersectionState::NONE,
                    ));
                    if result != Ternary::FALSE
                        && !(crate::checker_core::is_tuple_type(&c.types, source)
                            && crate::checker_core::is_tuple_type(&c.types, t))
                    {
                        // Comparing numeric index types when both `source`
                        // and `type` are tuples is unnecessary as the element
                        // types should be sufficiently covered by
                        // `propertiesRelatedTo`. It also causes problems with
                        // index type assignability as the types for the
                        // excluded discriminants are still included in the
                        // index type.
                        result = result.and(self.index_signatures_related_to(
                            c,
                            source,
                            t,
                            false,
                            false,
                            IntersectionState::NONE,
                        ));
                    }
                }
            }
            if result == Ternary::FALSE {
                return result;
            }
        }
        result
    }

    /// `(r *Relater) propertiesRelatedTo`.
    fn properties_related_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
        excluded_properties: &Set<String>,
        optionals_only: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        if Rc::ptr_eq(&self.relation(), &c.identity_relation) {
            return self.properties_identical_to(c, source, target, excluded_properties);
        }
        let mut result = Ternary::TRUE;
        let __arena_source_flags = c.types.clone();
        let _source_flags = __arena_source_flags.get_ref(source).flags;
        if crate::checker_core::is_tuple_type(&c.types, target) {
            if c.is_array_or_tuple_type(source) {
                let __arena_target_tuple = c.types.clone();
                let target_tuple = __arena_target_tuple.target_tuple_type(target).unwrap();
                if !c.types_handle().get(target_tuple).as_tuple_type().readonly
                    && (c.is_readonly_array_type(source)
                        || crate::checker_core::is_tuple_type(&c.types, source)
                            && c.types_handle()
                                .get(c.types_handle().target_tuple_type(source).unwrap())
                                .as_tuple_type()
                                .readonly)
                {
                    return Ternary::FALSE;
                }
                let source_arity = c.get_type_reference_arity(source);
                let target_arity = c.get_type_reference_arity(target);
                let source_rest;
                if crate::checker_core::is_tuple_type(&c.types, source) {
                    source_rest = c
                        .types_handle()
                        .get(c.types_handle().target_tuple_type(source).unwrap())
                        .as_tuple_type()
                        .combined_flags
                        .intersects(ElementFlags::REST);
                } else {
                    source_rest = true;
                }
                let __arena_target_combined_flags = c.types.clone();
                let target_combined_flags = __arena_target_combined_flags
                    .get(target_tuple)
                    .as_tuple_type()
                    .combined_flags;
                let target_has_rest_element = target_combined_flags.intersects(ElementFlags::REST);
                let target_has_variable_element =
                    target_combined_flags.intersects(ElementFlags::VARIABLE);
                let source_min_length = if crate::checker_core::is_tuple_type(&c.types, source) {
                    c.types_handle()
                        .get(c.types_handle().target_tuple_type(source).unwrap())
                        .as_tuple_type()
                        .min_length
                } else {
                    0
                };
                let __arena___guard_target_min_length = c.types.clone();
                let __guard_target_min_length =
                    __arena___guard_target_min_length.get(target_tuple).clone();
                let target_min_length = __guard_target_min_length.as_tuple_type().min_length;
                if !source_rest && source_arity < target_min_length {
                    if report_errors {
                        self.report_error(
                            c,
                            &tsc_diagnostics::Source_has_0_element_s_but_target_requires_1,
                            &[source_arity.to_string(), target_min_length.to_string()],
                        );
                    }
                    return Ternary::FALSE;
                }
                if !target_has_variable_element && target_arity < source_min_length {
                    if report_errors {
                        self.report_error(
                            c,
                            &tsc_diagnostics::Source_has_0_element_s_but_target_allows_only_1,
                            &[source_min_length.to_string(), target_arity.to_string()],
                        );
                    }
                    return Ternary::FALSE;
                }
                if !target_has_variable_element && (source_rest || target_arity < source_arity) {
                    if report_errors {
                        if source_min_length < target_min_length {
                            self.report_error(
                                c,
                                &tsc_diagnostics::Target_requires_0_element_s_but_source_may_have_fewer,
                                &[target_min_length.to_string()],
                            );
                        } else {
                            self.report_error(
                                c,
                                &tsc_diagnostics::Target_allows_only_0_element_s_but_source_may_have_more,
                                &[target_arity.to_string()],
                            );
                        }
                    }
                    return Ternary::FALSE;
                }
                let source_type_arguments = c.get_type_arguments(source);
                let target_type_arguments = c.get_type_arguments(target);
                let target_start_count = crate::utilities::get_start_element_count(
                    c.types_handle().get(target_tuple).as_tuple_type(),
                    ElementFlags::NON_REST,
                );
                let target_end_count = crate::utilities::get_end_element_count(
                    c.types_handle().get_ref(target_tuple).as_tuple_type(),
                    ElementFlags::NON_REST,
                );
                let mut can_exclude_discriminants = excluded_properties.len() != 0;
                for source_position in 0..source_arity {
                    let source_element_flags =
                        if crate::checker_core::is_tuple_type(&c.types, source) {
                            c.types_handle()
                                .get(c.types_handle().target_tuple_type(source).unwrap())
                                .as_tuple_type()
                                .element_infos[source_position]
                                .flags
                        } else {
                            ElementFlags::REST
                        };
                    let source_position_from_end = source_arity - 1 - source_position;
                    let target_position: i64 = if target_has_rest_element
                        && source_position >= target_start_count
                    {
                        (target_arity - 1 - (source_position_from_end.min(target_end_count))) as i64
                    } else {
                        if source_position >= target_arity {
                            if report_errors {
                                self.report_error(
                                    c,
                                    &tsc_diagnostics::Target_allows_only_0_element_s_but_source_may_have_more,
                                    &[target_arity.to_string()],
                                );
                            }
                            return Ternary::FALSE;
                        }
                        source_position as i64
                    };
                    let mut target_element_flags = ElementFlags::NONE;
                    if target_position >= 0 {
                        target_element_flags = c
                            .types_handle()
                            .get(target_tuple)
                            .as_tuple_type()
                            .element_infos[target_position as usize]
                            .flags;
                    }
                    if target_element_flags.intersects(ElementFlags::VARIADIC)
                        && !source_element_flags.intersects(ElementFlags::VARIADIC)
                    {
                        if report_errors {
                            self.report_error(
                                c,
                                &tsc_diagnostics::Source_provides_no_match_for_variadic_element_at_position_0_in_target,
                                &[target_position.to_string()],
                            );
                        }
                        return Ternary::FALSE;
                    }
                    if source_element_flags.intersects(ElementFlags::VARIADIC)
                        && !target_element_flags.intersects(ElementFlags::VARIABLE)
                    {
                        if report_errors {
                            self.report_error(
                                c,
                                &tsc_diagnostics::Variadic_element_at_position_0_in_source_does_not_match_element_at_position_1_in_target,
                                &[source_position.to_string(), target_position.to_string()],
                            );
                        }
                        return Ternary::FALSE;
                    }
                    if target_element_flags.intersects(ElementFlags::REQUIRED)
                        && !source_element_flags.intersects(ElementFlags::REQUIRED)
                    {
                        if report_errors {
                            self.report_error(
                                c,
                                &tsc_diagnostics::Source_provides_no_match_for_required_element_at_position_0_in_target,
                                &[target_position.to_string()],
                            );
                        }
                        return Ternary::FALSE;
                    }
                    // We can only exclude discriminant properties if we have
                    // not yet encountered a variable-length element.
                    if can_exclude_discriminants {
                        if source_element_flags.intersects(ElementFlags::VARIABLE)
                            || target_element_flags.intersects(ElementFlags::VARIABLE)
                        {
                            can_exclude_discriminants = false;
                        }
                        if can_exclude_discriminants
                            && excluded_properties.has(&source_position.to_string())
                        {
                            continue;
                        }
                    }
                    let source_type = c.remove_missing_type(
                        source_type_arguments[source_position],
                        source_element_flags
                            .intersects(target_element_flags & ElementFlags::OPTIONAL),
                    );
                    let target_type = target_type_arguments[target_position as usize];
                    let target_check_type = if source_element_flags
                        .intersects(ElementFlags::VARIADIC)
                        && target_element_flags.intersects(ElementFlags::REST)
                    {
                        c.create_array_type(target_type)
                    } else {
                        c.remove_missing_type(
                            target_type,
                            target_element_flags.intersects(ElementFlags::OPTIONAL),
                        )
                    };
                    let related = self.is_related_to_ex(
                        c,
                        source_type,
                        target_check_type,
                        RecursionFlags::BOTH,
                        report_errors,
                        None,
                        intersection_state,
                    );
                    if related == Ternary::FALSE {
                        if report_errors && (target_arity > 1 || source_arity > 1) {
                            if target_has_rest_element
                                && source_position >= target_start_count
                                && source_position_from_end >= target_end_count
                                && target_start_count != source_arity - target_end_count - 1
                            {
                                self.report_error(
                                    c,
                                    &tsc_diagnostics::Type_at_positions_0_through_1_in_source_is_not_compatible_with_type_at_position_2_in_target,
                                    &[
                                        target_start_count.to_string(),
                                        (source_arity - target_end_count - 1).to_string(),
                                        target_position.to_string(),
                                    ],
                                );
                            } else {
                                self.report_error(
                                    c,
                                    &tsc_diagnostics::Type_at_position_0_in_source_is_not_compatible_with_type_at_position_1_in_target,
                                    &[source_position.to_string(), target_position.to_string()],
                                );
                            }
                        }
                        return Ternary::FALSE;
                    }
                    result = result.and(related);
                }
                return result;
            }
            if c.types_handle()
                .get_ref(c.types_handle().target_tuple_type(target).unwrap())
                .as_tuple_type()
                .combined_flags
                .intersects(ElementFlags::VARIABLE)
            {
                return Ternary::FALSE;
            }
        }
        let require_optional_properties = (Rc::ptr_eq(&self.relation(), &c.subtype_relation)
            || Rc::ptr_eq(&self.relation(), &c.strict_subtype_relation))
            && !crate::utilities::is_object_literal_type(&c.types, source)
            && !c.is_empty_array_literal_type(source)
            && !crate::checker_core::is_tuple_type(&c.types, source);
        let unmatched_property =
            c.get_unmatched_property(source, target, require_optional_properties, false);
        if let Some(unmatched_property) = unmatched_property {
            if report_errors && c.should_report_unmatched_property_error(source, target) {
                self.report_unmatched_property(
                    c,
                    source,
                    target,
                    unmatched_property,
                    require_optional_properties,
                );
            }
            return Ternary::FALSE;
        }
        if crate::utilities::is_object_literal_type(&c.types, target) {
            let source_props = c.get_properties_of_type(source);
            for source_prop in exclude_properties(c, &source_props, excluded_properties) {
                let name = c.sym_name_rc(source_prop);
                if c.get_property_of_object_type(target, &name).is_none() {
                    if report_errors {
                        let prop_str = c.symbol_to_string(source_prop);
                        let target_str = c.type_to_string(target);
                        self.report_error(
                            c,
                            &tsc_diagnostics::Property_0_does_not_exist_on_type_1,
                            &[prop_str, target_str],
                        );
                    }
                    return Ternary::FALSE;
                }
            }
        }
        // We only call this for union target types when we're attempting to
        // do excess property checking - in those cases, we want to get _all
        // possible props_ from the target union, across all members
        let properties = c.get_properties_of_type(target);
        let numeric_names_only = crate::checker_core::is_tuple_type(&c.types, source)
            && crate::checker_core::is_tuple_type(&c.types, target);
        for target_prop in exclude_properties(c, &properties, excluded_properties) {
            let name = c.sym_name_rc(target_prop);
            let target_prop_flags = c.sym(target_prop).flags;
            if !target_prop_flags.intersects(ast::SymbolFlags::PROTOTYPE)
                && (!numeric_names_only
                    || crate::utilities::is_numeric_literal_name(&name)
                    || &*name == "length")
                && (!optionals_only || target_prop_flags.intersects(ast::SymbolFlags::OPTIONAL))
            {
                if let Some(source_prop) = c.get_property_of_type(source, &name) {
                    if source_prop != target_prop {
                        let related = self.property_related_to(
                            c,
                            source,
                            target,
                            source_prop,
                            target_prop,
                            &mut |c: &mut Checker, s: SymbolId| {
                                Some(c.get_non_missing_type_of_symbol(s))
                            },
                            report_errors,
                            intersection_state,
                            Rc::ptr_eq(&self.relation(), &c.comparable_relation),
                        );
                        if related == Ternary::FALSE {
                            return Ternary::FALSE;
                        }
                        result = result.and(related);
                    }
                }
            }
        }
        result
    }

    /// `(r *Relater) propertyRelatedTo`.
    fn property_related_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        source_prop: SymbolId,
        target_prop: SymbolId,
        get_type_of_source_property: &mut dyn FnMut(&mut Checker, SymbolId) -> Option<TypeId>,
        report_errors: bool,
        intersection_state: IntersectionState,
        skip_optional: bool,
    ) -> Ternary {
        let source_prop_flags =
            crate::utilities::get_declaration_modifier_flags_from_symbol(c, source_prop);
        let target_prop_flags =
            crate::utilities::get_declaration_modifier_flags_from_symbol(c, target_prop);
        if source_prop_flags.intersects(ast::ModifierFlags::PRIVATE)
            || target_prop_flags.intersects(ast::ModifierFlags::PRIVATE)
        {
            if c.sym(source_prop).value_declaration != c.sym(target_prop).value_declaration {
                if report_errors {
                    if source_prop_flags.intersects(ast::ModifierFlags::PRIVATE)
                        && target_prop_flags.intersects(ast::ModifierFlags::PRIVATE)
                    {
                        let prop_str = c.symbol_to_string(target_prop);
                        self.report_error(
                            c,
                            &tsc_diagnostics::Types_have_separate_declarations_of_a_private_property_0,
                            &[prop_str],
                        );
                    } else {
                        let prop_str = c.symbol_to_string(target_prop);
                        let t1 = c.type_to_string(tsc_core::core::if_else(
                            source_prop_flags.intersects(ast::ModifierFlags::PRIVATE),
                            source,
                            target,
                        ));
                        let t2 = c.type_to_string(tsc_core::core::if_else(
                            source_prop_flags.intersects(ast::ModifierFlags::PRIVATE),
                            target,
                            source,
                        ));
                        self.report_error(
                            c,
                            &tsc_diagnostics::Property_0_is_private_in_type_1_but_not_in_type_2,
                            &[prop_str, t1, t2],
                        );
                    }
                }
                return Ternary::FALSE;
            }
        } else if target_prop_flags.intersects(ast::ModifierFlags::PROTECTED) {
            if !c.is_valid_override_of(source_prop, target_prop) {
                if report_errors {
                    let source_type = c.get_declaring_class(source_prop).unwrap_or(source);
                    let target_type = c.get_declaring_class(target_prop).unwrap_or(target);
                    let prop_str = c.symbol_to_string(target_prop);
                    let s_str = c.type_to_string(source_type);
                    let t_str = c.type_to_string(target_type);
                    self.report_error(
                        c,
                        &tsc_diagnostics::Property_0_is_protected_but_type_1_is_not_a_class_derived_from_2,
                        &[prop_str, s_str, t_str],
                    );
                }
                return Ternary::FALSE;
            }
        } else if source_prop_flags.intersects(ast::ModifierFlags::PROTECTED) {
            if report_errors {
                let prop_str = c.symbol_to_string(target_prop);
                let s_str = c.type_to_string(source);
                let t_str = c.type_to_string(target);
                self.report_error(
                    c,
                    &tsc_diagnostics::Property_0_is_protected_in_type_1_but_public_in_type_2,
                    &[prop_str, s_str, t_str],
                );
            }
            return Ternary::FALSE;
        }
        // Ensure {readonly a: whatever} is not a subtype of {a: whatever},
        // while {a: whatever} is a subtype of {readonly a: whatever}.
        // This ensures the subtype relationship is ordered, and preventing
        // declaration order from deciding which type "wins" in union subtype
        // reduction.
        // They're still assignable to one another, since `readonly` doesn't
        // affect assignability.
        // This is only applied during the strictSubtypeRelation -- currently
        // used in subtype reduction
        if Rc::ptr_eq(&self.relation(), &c.strict_subtype_relation)
            && c.is_readonly_symbol(source_prop)
            && !c.is_readonly_symbol(target_prop)
        {
            return Ternary::FALSE;
        }
        // If the target comes from a partial union prop, allow `undefined` in
        // the target type
        let related = self.is_property_symbol_type_related(
            c,
            source_prop,
            target_prop,
            get_type_of_source_property,
            report_errors,
            intersection_state,
        );
        if related == Ternary::FALSE {
            if report_errors {
                let prop_str = c.symbol_to_string(target_prop);
                self.report_error(
                    c,
                    &tsc_diagnostics::Types_of_property_0_are_incompatible,
                    &[prop_str],
                );
            }
            return Ternary::FALSE;
        }
        // When checking for comparability, be more lenient with optional
        // properties.
        if !skip_optional
            && c.sym(source_prop)
                .flags
                .intersects(ast::SymbolFlags::OPTIONAL)
            && c.sym(target_prop)
                .flags
                .intersects(ast::SymbolFlags::CLASS_MEMBER)
            && !c
                .sym(target_prop)
                .flags
                .intersects(ast::SymbolFlags::OPTIONAL)
        {
            // TypeScript 1.0 spec (April 2014): 3.8.3
            // S is a subtype of a type T, and T is a supertype of S if ...
            // S' and T are object types and, for each member M in T..
            // M is a property and S' contains a property N where
            // if M is a required property, N is also a required property
            // (M - property in T)
            // (N - property in S)
            if report_errors {
                let prop_str = c.symbol_to_string(target_prop);
                let s_str = c.type_to_string(source);
                let t_str = c.type_to_string(target);
                self.report_error(
                    c,
                    &tsc_diagnostics::Property_0_is_optional_in_type_1_but_required_in_type_2,
                    &[prop_str, s_str, t_str],
                );
            }
            return Ternary::FALSE;
        }
        related
    }

    /// `(r *Relater) isPropertySymbolTypeRelated`.
    fn is_property_symbol_type_related(
        &mut self,
        c: &mut Checker,
        source_prop: SymbolId,
        target_prop: SymbolId,
        get_type_of_source_property: &mut dyn FnMut(&mut Checker, SymbolId) -> Option<TypeId>,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let target_is_optional = c.strict_null_checks
            && c.sym(target_prop)
                .check_flags
                .intersects(ast::checkflags::CheckFlags::PARTIAL);
        let non_missing = c.get_non_missing_type_of_symbol(target_prop);
        let effective_target = c.add_optionality_ex(non_missing, false, target_is_optional);
        // source could resolve to `any` and that's not related to `unknown`
        // target under strict subtype relation
        let any_mask = if Rc::ptr_eq(&self.relation(), &c.strict_subtype_relation) {
            TypeFlags::ANY
        } else {
            TypeFlags::ANY_OR_UNKNOWN
        };
        if c.types_handle()
            .get_ref(effective_target)
            .flags
            .intersects(any_mask)
        {
            return Ternary::TRUE;
        }
        let effective_source = get_type_of_source_property(c, source_prop);
        self.is_related_to_ex(
            c,
            effective_source.unwrap_or(c.undefined_type),
            effective_target,
            RecursionFlags::BOTH,
            report_errors,
            None,
            intersection_state,
        )
    }

    /// `(r *Relater) reportUnmatchedProperty`.
    fn report_unmatched_property(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        unmatched_property: SymbolId,
        require_optional_properties: bool,
    ) {
        // give specific error in case where private names have the same
        // description
        let mut reported = false;
        let __arena_source_symbol = c.types.clone();
        let source_symbol = __arena_source_symbol.get_ref(source).symbol;
        let unmatched_vd = { c.sym(unmatched_property).value_declaration };
        if let Some(value_declaration) = unmatched_vd {
            let __program = c.program.clone().expect("program");
            let decl_nodes = __program.nodes((value_declaration).file_index());
            if let Some(name_node) = decl_nodes[value_declaration].name() {
                if ast::is_private_identifier(&decl_nodes[name_node]) {
                    if let Some(source_symbol) = source_symbol {
                        if c.sym(source_symbol)
                            .flags
                            .intersects(ast::SymbolFlags::CLASS)
                        {
                            let private_identifier_description =
                                decl_nodes[name_node].text(&decl_nodes).to_string();
                            let symbol_table_key =
                                tsc_binder::binder::get_symbol_name_for_private_identifier(
                                    source_symbol,
                                    &private_identifier_description,
                                );
                            if c.get_property_of_type(source, &symbol_table_key).is_some() {
                                let s_str = c.symbol_to_string(source_symbol);
                                let __arena_target_symbol = c.types.clone();
                                let target_symbol =
                                    __arena_target_symbol.get_ref(target).symbol.unwrap();
                                let t_str = c.symbol_to_string(target_symbol);
                                self.report_error(
                                    c,
                                    &tsc_diagnostics::Property_0_in_type_1_refers_to_a_different_member_that_cannot_be_accessed_from_within_type_2,
                                    &[private_identifier_description, s_str, t_str],
                                );
                                reported = true;
                            }
                        }
                    }
                }
            }
        }
        if reported {
            return;
        }
        let props = c.get_unmatched_properties(source, target, require_optional_properties, false);
        if props.len() == 1 {
            let (source_type, target_type) = c.get_type_names_for_error_display(source, target);
            let prop_name = c.symbol_to_string(unmatched_property);
            self.report_error(
                c,
                &tsc_diagnostics::Property_0_is_missing_in_type_1_but_required_in_type_2,
                &[prop_name.clone(), source_type, target_type],
            );
            let declarations = c.sym(unmatched_property).declarations.clone();
            if !declarations.is_empty() {
                let info = c.new_diagnostic_for_node(
                    Some(declarations[0]),
                    &tsc_diagnostics::X_0_is_declared_here,
                    &[prop_name],
                );
                self.related_info.push(info);
            }
        } else if self.try_elaborate_array_like_errors(c, source, target, false) {
            let (source_type, target_type) = c.get_type_names_for_error_display(source, target);
            if props.len() > 5 {
                let prop_names = props[..4]
                    .iter()
                    .map(|&p| c.symbol_to_string(p))
                    .collect::<Vec<_>>()
                    .join(", ");
                self.report_error(
                    c,
                    &tsc_diagnostics::Type_0_is_missing_the_following_properties_from_type_1_Colon_2_and_3_more,
                    &[source_type, target_type, prop_names, (props.len() - 4).to_string()],
                );
            } else {
                let prop_names = props
                    .iter()
                    .map(|&p| c.symbol_to_string(p))
                    .collect::<Vec<_>>()
                    .join(", ");
                self.report_error(
                    c,
                    &tsc_diagnostics::Type_0_is_missing_the_following_properties_from_type_1_Colon_2,
                    &[source_type, target_type, prop_names],
                );
            }
        }
    }

    /// `(r *Relater) tryElaborateArrayLikeErrors`.
    ///
    /// The spec for elaboration is:
    /// - If the source is a readonly tuple and the target is a mutable array
    ///   or tuple, elaborate on mutability and skip property elaborations.
    /// - If the source is a tuple then skip property elaborations if the
    ///   target is an array or tuple.
    /// - If the source is a readonly array and the target is a mutable array
    ///   or tuple, elaborate on mutability and skip property elaborations.
    /// - If the source an array then skip property elaborations if the
    ///   target is a tuple.
    fn try_elaborate_array_like_errors(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        report_errors: bool,
    ) -> bool {
        if crate::checker_core::is_tuple_type(&c.types, source) {
            let __arena___guard_readonly = c.types.clone();
            let __guard_readonly = __arena___guard_readonly
                .get_ref(c.types_handle().target_tuple_type(source).unwrap())
                .clone();
            let readonly = __guard_readonly.as_tuple_type().readonly;
            if readonly && c.is_mutable_array_or_tuple(target) {
                if report_errors {
                    let s_str = c.type_to_string(source);
                    let t_str = c.type_to_string(target);
                    self.report_error(
                        c,
                        &tsc_diagnostics::The_type_0_is_readonly_and_cannot_be_assigned_to_the_mutable_type_1,
                        &[s_str, t_str],
                    );
                }
                return false;
            }
            return c.is_array_or_tuple_type(target);
        }
        if c.is_readonly_array_type(source) && c.is_mutable_array_or_tuple(target) {
            if report_errors {
                let s_str = c.type_to_string(source);
                let t_str = c.type_to_string(target);
                self.report_error(
                    c,
                    &tsc_diagnostics::The_type_0_is_readonly_and_cannot_be_assigned_to_the_mutable_type_1,
                    &[s_str, t_str],
                );
            }
            return false;
        }
        if crate::checker_core::is_tuple_type(&c.types, target) {
            return c.is_array_type(source);
        }
        true
    }

    /// `(r *Relater) tryElaborateErrorsForPrimitivesAndObjects`.
    fn try_elaborate_errors_for_primitives_and_objects(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
    ) {
        let global_es_symbol_type = {
            let thunk = c
                .get_global_es_symbol_type
                .clone()
                .expect("getGlobalESSymbolType");
            thunk(c)
        };
        if (source == c.global_string_type && target == c.string_type)
            || (source == c.global_number_type && target == c.number_type)
            || (source == c.global_boolean_type && target == c.boolean_type)
            || (source == global_es_symbol_type && target == c.es_symbol_type)
        {
            let t_str = c.type_to_string(target);
            let s_str = c.type_to_string(source);
            self.report_error(
                c,
                &tsc_diagnostics::X_0_is_a_primitive_but_1_is_a_wrapper_object_Prefer_using_0_when_possible,
                &[t_str, s_str],
            );
        }
    }

    /// `(r *Relater) propertiesIdenticalTo`.
    fn properties_identical_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        excluded_properties: &Set<String>,
    ) -> Ternary {
        if !c
            .types_handle()
            .get_ref(source)
            .flags
            .intersects(TypeFlags::OBJECT)
            || !c
                .types_handle()
                .get_ref(target)
                .flags
                .intersects(TypeFlags::OBJECT)
        {
            return Ternary::FALSE;
        }
        let source_props = c.get_properties_of_object_type(source);
        let source_properties = exclude_properties(c, &source_props, excluded_properties);
        let target_props = c.get_properties_of_object_type(target);
        let target_properties = exclude_properties(c, &target_props, excluded_properties);
        if source_properties.len() != target_properties.len() {
            return Ternary::FALSE;
        }
        let mut result = Ternary::TRUE;
        for source_prop in source_properties {
            let name = c.sym_name_rc(source_prop);
            let Some(target_prop) = c.get_property_of_object_type(target, &name) else {
                return Ternary::FALSE;
            };
            let related = c.compare_properties(
                source_prop,
                target_prop,
                &mut |c: &mut Checker, s: TypeId, t: TypeId| self.is_related_to_simple(c, s, t),
            );
            if related == Ternary::FALSE {
                return Ternary::FALSE;
            }
            result = result.and(related);
        }
        result
    }

    /// `(r *Relater) signaturesRelatedTo`.
    fn signatures_related_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        kind: SignatureKind,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        if Rc::ptr_eq(&self.relation(), &c.identity_relation) {
            return self.signatures_identical_to(c, source, target, kind);
        }
        // With respect to signatures, the anyFunctionType wildcard is a
        // subtype of every other function type.
        if source == c.any_function_type {
            return Ternary::TRUE;
        }
        if target == c.any_function_type {
            return Ternary::FALSE;
        }
        let source_signatures = c.get_signatures_of_type(source, kind);
        let target_signatures = c.get_signatures_of_type(target, kind);
        if kind == SignatureKind::Construct
            && !source_signatures.is_empty()
            && !target_signatures.is_empty()
        {
            let source_is_abstract = c
                .signature_arena
                .get(source_signatures[0])
                .flags
                .intersects(crate::types::SignatureFlags::ABSTRACT);
            let target_is_abstract = c
                .signature_arena
                .get(target_signatures[0])
                .flags
                .intersects(crate::types::SignatureFlags::ABSTRACT);
            if source_is_abstract && !target_is_abstract {
                // An abstract constructor type is not assignable to a
                // non-abstract constructor type as it would otherwise be
                // possible to new an abstract class. Note that the
                // assignability check we perform for an extends clause
                // excludes construct signatures from the target, so this
                // check never proceeds.
                if report_errors {
                    self.report_error(
                        c,
                        &tsc_diagnostics::Cannot_assign_an_abstract_constructor_type_to_a_non_abstract_constructor_type,
                        &[],
                    );
                }
                return Ternary::FALSE;
            }
            if !self.constructor_visibilities_are_compatible(
                c,
                source_signatures[0],
                target_signatures[0],
                report_errors,
            ) {
                return Ternary::FALSE;
            }
        }
        let mut result = Ternary::TRUE;
        let (source_object_flags, target_object_flags) = {
            let __arena_s = c.types.clone();
            let s = __arena_s.get_ref(source);
            (s.object_flags, c.types_handle().get_ref(target).object_flags)
        };
        let same_anonymous_instantiation = source_object_flags
            .intersects(ObjectFlags::INSTANTIATED)
            && target_object_flags.intersects(ObjectFlags::INSTANTIATED)
            && c.types_handle().get_ref(source).symbol == c.types_handle().get_ref(target).symbol;
        let same_reference = source_object_flags.intersects(ObjectFlags::REFERENCE)
            && target_object_flags.intersects(ObjectFlags::REFERENCE)
            && c.types_handle().get_ref(source).target() == c.types_handle().get_ref(target).target();
        if same_anonymous_instantiation || same_reference {
            // We have instantiations of the same anonymous type (which
            // typically will be the type of a method). Simply do a pairwise
            // comparison of the signatures in the two signature lists instead
            // of the much more expensive N * M comparison matrix we explore
            // below. We erase type parameters as they are known to always be
            // the same.
            for i in 0..target_signatures.len() {
                let related = self.signature_related_to(
                    c,
                    source_signatures[i],
                    target_signatures[i],
                    true,
                    report_errors,
                    intersection_state,
                );
                if related == Ternary::FALSE {
                    return Ternary::FALSE;
                }
                result = result.and(related);
            }
        } else if source_signatures.len() == 1 && target_signatures.len() == 1 {
            // For simple functions (functions with a single signature) we
            // only erase type parameters for the comparable relation.
            // Otherwise, if the source signature is generic, we instantiate
            // it in the context of the target signature before checking the
            // relationship. Ideally we'd do this regardless of the number of
            // signatures, but the potential costs are prohibitive due to the
            // quadratic nature of the logic below.
            let erase_generics = Rc::ptr_eq(&self.relation(), &c.comparable_relation);
            result = self.signature_related_to(
                c,
                source_signatures[0],
                target_signatures[0],
                erase_generics,
                report_errors,
                intersection_state,
            );
        } else {
            'outer: for &t in &target_signatures {
                let save_error_state = self.get_error_state();
                // Only elaborate errors from the first failure
                let mut should_elaborate_errors = report_errors;
                for &s in &source_signatures {
                    let related = self.signature_related_to(
                        c,
                        s,
                        t,
                        true,
                        should_elaborate_errors,
                        intersection_state,
                    );
                    if related != Ternary::FALSE {
                        result = result.and(related);
                        self.restore_error_state(&save_error_state);
                        continue 'outer;
                    }
                    should_elaborate_errors = false;
                }
                if should_elaborate_errors {
                    let s_str = c.type_to_string(source);
                    let t_str = c.signature_to_string(t);
                    self.report_error(
                        c,
                        &tsc_diagnostics::Type_0_provides_no_match_for_the_signature_1,
                        &[s_str, t_str],
                    );
                }
                return Ternary::FALSE;
            }
        }
        result
    }

    /// `(r *Relater) constructorVisibilitiesAreCompatible`.
    fn constructor_visibilities_are_compatible(
        &mut self,
        c: &mut Checker,
        source_signature: SignatureId,
        target_signature: SignatureId,
        report_errors: bool,
    ) -> bool {
        let source_declaration = c.signature_arena.get(source_signature).declaration;
        let target_declaration = c.signature_arena.get(target_signature).declaration;
        let (Some(source_declaration), Some(target_declaration)) =
            (source_declaration, target_declaration)
        else {
            return true;
        };
        let source_accessibility = {
            let __program = c.program.clone().expect("program");
            let nodes = __program.nodes((source_declaration).file_index());
            nodes[source_declaration].modifier_flags()
                & ast::ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER
        };
        let target_accessibility = {
            let __program = c.program.clone().expect("program");
            let nodes = __program.nodes((target_declaration).file_index());
            nodes[target_declaration].modifier_flags()
                & ast::ModifierFlags::NON_PUBLIC_ACCESSIBILITY_MODIFIER
        };
        // A public, protected and private signature is assignable to a
        // private signature.
        if target_accessibility == ast::ModifierFlags::PRIVATE {
            return true;
        }
        // A public and protected signature is assignable to a protected
        // signature.
        if target_accessibility == ast::ModifierFlags::PROTECTED
            && source_accessibility != ast::ModifierFlags::PRIVATE
        {
            return true;
        }
        // Only a public signature is assignable to public signature.
        if target_accessibility != ast::ModifierFlags::PROTECTED
            && source_accessibility == ast::ModifierFlags::NONE
        {
            return true;
        }
        if report_errors {
            self.report_error(
                c,
                &tsc_diagnostics::Cannot_assign_a_0_constructor_type_to_a_1_constructor_type,
                &[
                    visibility_to_string(source_accessibility).to_string(),
                    visibility_to_string(target_accessibility).to_string(),
                ],
            );
        }
        false
    }

    /// `(r *Relater) signatureRelatedTo` — see signatureAssignableTo,
    /// compareSignaturesIdentical.
    fn signature_related_to(
        &mut self,
        c: &mut Checker,
        mut source: SignatureId,
        mut target: SignatureId,
        erase: bool,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let mut check_mode = SignatureCheckMode::NONE;
        if Rc::ptr_eq(&self.relation(), &c.subtype_relation) {
            check_mode = SignatureCheckMode::STRICT_TOP_SIGNATURE;
        } else if Rc::ptr_eq(&self.relation(), &c.strict_subtype_relation) {
            check_mode =
                SignatureCheckMode::STRICT_TOP_SIGNATURE | SignatureCheckMode::STRICT_ARITY;
        }
        if erase {
            source = c.get_erased_signature(source);
            target = c.get_erased_signature(target);
        }
        let report_unreliable_mapper = c.report_unreliable_mapper;
        c.compare_signatures_related(
            source,
            target,
            check_mode,
            report_errors,
            Some(self),
            Comparer::IsRelatedToEx(intersection_state),
            Some(report_unreliable_mapper),
        )
    }

    /// `(r *Relater) signaturesIdenticalTo`.
    fn signatures_identical_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        kind: SignatureKind,
    ) -> Ternary {
        let source_signatures = c.get_signatures_of_type(source, kind);
        let target_signatures = c.get_signatures_of_type(target, kind);
        if source_signatures.len() != target_signatures.len() {
            return Ternary::FALSE;
        }
        let mut result = Ternary::TRUE;
        for i in 0..source_signatures.len() {
            let related = c.compare_signatures_identical(
                source_signatures[i],
                target_signatures[i],
                false,
                false,
                false,
                Comparer::IsRelatedToSimple,
                &mut Some(&mut *self),
            );
            if related == Ternary::FALSE {
                return Ternary::FALSE;
            }
            result = result.and(related);
        }
        result
    }

    /// `(r *Relater) indexSignaturesRelatedTo`.
    fn index_signatures_related_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
        source_is_primitive: bool,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        if Rc::ptr_eq(&self.relation(), &c.identity_relation) {
            return self.index_signatures_identical_to(c, source, target);
        }
        let index_infos = c.get_index_infos_of_type(target);
        let target_has_string_index = index_infos
            .iter()
            .any(|&info| c.index_info_arena.get(info).key_type == Some(c.string_type));
        let mut result = Ternary::TRUE;
        for &target_info in &index_infos {
            let target_value_type = c
                .index_info_arena
                .get(target_info)
                .value_type
                .unwrap_or(c.never_type);
            let related;
            if !Rc::ptr_eq(&self.relation(), &c.strict_subtype_relation)
                && !source_is_primitive
                && target_has_string_index
                && c.types_handle()
                    .get(target_value_type)
                    .flags
                    .intersects(TypeFlags::ANY)
            {
                related = Ternary::TRUE;
            } else if c.is_generic_mapped_type(source) && target_has_string_index {
                let template = c
                    .get_template_type_from_mapped_type(source)
                    .unwrap_or(c.never_type);
                related = self.is_related_to(
                    c,
                    template,
                    target_value_type,
                    RecursionFlags::BOTH,
                    report_errors,
                );
            } else {
                related = self.type_related_to_index_info(
                    c,
                    source,
                    target_info,
                    report_errors,
                    intersection_state,
                );
            }
            if related == Ternary::FALSE {
                return Ternary::FALSE;
            }
            result = result.and(related);
        }
        result
    }

    /// `(r *Relater) typeRelatedToIndexInfo`.
    fn type_related_to_index_info(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target_info: IndexInfoId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let target_key_type = c
            .index_info_arena
            .get(target_info)
            .key_type
            .unwrap_or(c.never_type);
        if let Some(source_info) = c.get_applicable_index_info(source, target_key_type) {
            return self.index_info_related_to(
                c,
                source_info,
                target_info,
                report_errors,
                intersection_state,
            );
        }
        // Intersection constituents are never considered to have an inferred
        // index signature. Also, in the strict subtype relation, only fresh
        // object literals are considered to have inferred index signatures.
        // This ensures { [x: string]: xxx } <: {} but not vice-versa. Without
        // this rule, those types would be mutual strict subtypes.
        if !intersection_state.intersects(IntersectionState::SOURCE)
            && (!Rc::ptr_eq(&self.relation(), &c.strict_subtype_relation)
                || c.types_handle()
                    .get(source)
                    .object_flags
                    .intersects(ObjectFlags::FRESH_LITERAL))
            && c.is_object_type_with_inferable_index(source)
        {
            return self.members_related_to_index_info(
                c,
                source,
                target_info,
                report_errors,
                intersection_state,
            );
        }
        if report_errors {
            let key_str = c.type_to_string(target_key_type);
            let s_str = c.type_to_string(source);
            self.report_error(
                c,
                &tsc_diagnostics::Index_signature_for_type_0_is_missing_in_type_1,
                &[key_str, s_str],
            );
        }
        Ternary::FALSE
    }

    /// `(r *Relater) membersRelatedToIndexInfo`.
    fn members_related_to_index_info(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target_info: IndexInfoId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let mut result = Ternary::TRUE;
        let key_type = c
            .index_info_arena
            .get(target_info)
            .key_type
            .unwrap_or(c.never_type);
        let props = if c
            .types_handle()
            .get_ref(source)
            .flags
            .intersects(TypeFlags::INTERSECTION)
        {
            c.get_properties_of_union_or_intersection_type(source)
        } else {
            c.get_properties_of_object_type(source)
        };
        for prop in props {
            // Skip over ignored JSX and symbol-named members
            if is_ignored_jsx_property(c, source, prop) {
                continue;
            }
            let literal = c.get_literal_type_from_property(
                prop,
                TypeFlags::STRING_OR_NUMBER_LITERAL_OR_UNIQUE,
                false,
            );
            if c.is_applicable_index_type(literal, key_type) {
                let prop_type = c.get_non_missing_type_of_symbol(prop);
                let __arena_prop_type_flags = c.types.clone();
                let prop_type_flags = __arena_prop_type_flags.get_ref(prop_type).flags;
                let t = if c.exact_optional_property_types
                    || prop_type_flags.intersects(TypeFlags::UNDEFINED)
                    || key_type == c.number_type
                    || !c.sym(prop).flags.intersects(ast::SymbolFlags::OPTIONAL)
                {
                    prop_type
                } else {
                    c.get_type_with_facts(prop_type, crate::checker_types::TypeFacts::NE_UNDEFINED)
                };
                let target_value_type = c
                    .index_info_arena
                    .get(target_info)
                    .value_type
                    .unwrap_or(c.never_type);
                let related = self.is_related_to_ex(
                    c,
                    t,
                    target_value_type,
                    RecursionFlags::BOTH,
                    report_errors,
                    None,
                    intersection_state,
                );
                if related == Ternary::FALSE {
                    if report_errors {
                        let prop_str = c.symbol_to_string(prop);
                        self.report_error(
                            c,
                            &tsc_diagnostics::Property_0_is_incompatible_with_index_signature,
                            &[prop_str],
                        );
                    }
                    return Ternary::FALSE;
                }
                result = result.and(related);
            }
        }
        for info in c.get_index_infos_of_type(source) {
            let info_key = c
                .index_info_arena
                .get(info)
                .key_type
                .unwrap_or(c.never_type);
            if c.is_applicable_index_type(info_key, key_type) {
                let related = self.index_info_related_to(
                    c,
                    info,
                    target_info,
                    report_errors,
                    intersection_state,
                );
                if related == Ternary::FALSE {
                    return Ternary::FALSE;
                }
                result = result.and(related);
            }
        }
        result
    }

    /// `(r *Relater) indexInfoRelatedTo`.
    fn index_info_related_to(
        &mut self,
        c: &mut Checker,
        source_info: IndexInfoId,
        target_info: IndexInfoId,
        report_errors: bool,
        intersection_state: IntersectionState,
    ) -> Ternary {
        let (source_value, source_key) = {
            let i = c.index_info_arena.get(source_info);
            (
                i.value_type.unwrap_or(c.never_type),
                i.key_type.unwrap_or(c.never_type),
            )
        };
        let (target_value, target_key) = {
            let i = c.index_info_arena.get(target_info);
            (
                i.value_type.unwrap_or(c.never_type),
                i.key_type.unwrap_or(c.never_type),
            )
        };
        let related = self.is_related_to_ex(
            c,
            source_value,
            target_value,
            RecursionFlags::BOTH,
            report_errors,
            None,
            intersection_state,
        );
        if related == Ternary::FALSE && report_errors {
            if source_key == target_key {
                let key_str = c.type_to_string(source_key);
                self.report_error(
                    c,
                    &tsc_diagnostics::X_0_index_signatures_are_incompatible,
                    &[key_str],
                );
            } else {
                let s_str = c.type_to_string(source_key);
                let t_str = c.type_to_string(target_key);
                self.report_error(
                    c,
                    &tsc_diagnostics::X_0_and_1_index_signatures_are_incompatible,
                    &[s_str, t_str],
                );
            }
        }
        related
    }

    /// `(r *Relater) indexSignaturesIdenticalTo`.
    fn index_signatures_identical_to(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
    ) -> Ternary {
        let source_infos = c.get_index_infos_of_type(source);
        let target_infos = c.get_index_infos_of_type(target);
        if source_infos.len() != target_infos.len() {
            return Ternary::FALSE;
        }
        for target_info in target_infos {
            let target_key = c.index_info_arena.get(target_info).key_type;
            let Some(key) = target_key else {
                return Ternary::FALSE;
            };
            let source_info = c.get_index_info_of_type(source, key);
            let ok = source_info.is_some_and(|si| {
                let si_value = c
                    .index_info_arena
                    .get(si)
                    .value_type
                    .unwrap_or(c.never_type);
                let ti_value = c
                    .index_info_arena
                    .get(target_info)
                    .value_type
                    .unwrap_or(c.never_type);
                self.is_related_to(c, si_value, ti_value, RecursionFlags::BOTH, false)
                    != Ternary::FALSE
                    && c.index_info_arena.get(si).is_readonly
                        == c.index_info_arena.get(target_info).is_readonly
            });
            if !ok {
                return Ternary::FALSE;
            }
        }
        Ternary::TRUE
    }

    /// `(r *Relater) reportErrorResults`.
    fn report_error_results(
        &mut self,
        c: &mut Checker,
        original_source: TypeId,
        original_target: TypeId,
        mut source: TypeId,
        mut target: TypeId,
        head_message: Option<&'static tsc_diagnostics::Message>,
    ) {
        let source_has_base = c.get_single_base_for_non_augmenting_subtype(original_source);
        let target_has_base = c.get_single_base_for_non_augmenting_subtype(original_target);
        if c.types_handle().get_ref(original_source).alias.is_some() || source_has_base.is_some() {
            source = original_source;
        }
        if c.types_handle().get_ref(original_target).alias.is_some() || target_has_base.is_some() {
            target = original_target;
        }
        let (source_flags, target_flags) = {
            let __arena_s = c.types.clone();
            let s = __arena_s.get_ref(source);
            (s.flags, c.types_handle().get_ref(target).flags)
        };
        if source_flags.intersects(TypeFlags::OBJECT) && target_flags.intersects(TypeFlags::OBJECT)
        {
            self.try_elaborate_array_like_errors(c, source, target, true);
        }
        let __arena_original_target_flags = c.types.clone();
        let original_target_flags = __arena_original_target_flags.get_ref(original_target).flags;
        let __arena_source_symbol = c.types.clone();
        let source_symbol = __arena_source_symbol.get_ref(source).symbol;
        if source_flags.intersects(TypeFlags::OBJECT)
            && target_flags.intersects(TypeFlags::PRIMITIVE)
        {
            self.try_elaborate_errors_for_primitives_and_objects(c, source, target);
        } else if source_symbol.is_some()
            && source_flags.intersects(TypeFlags::OBJECT)
            && c.global_object_type == source
        {
            self.report_error(
                c,
                &tsc_diagnostics::The_Object_type_is_assignable_to_very_few_other_types_Did_you_mean_to_use_the_any_type_instead,
                &[],
            );
        } else if c
            .types_handle()
            .get_ref(source)
            .object_flags
            .intersects(ObjectFlags::JSX_ATTRIBUTES)
            && target_flags.intersects(TypeFlags::INTERSECTION)
        {
            let __arena_target_types = c.types.clone();
            let target_types = __arena_target_types.get_ref(target).types().to_vec();
            // `JsxNames.IntrinsicAttributes` / `.IntrinsicClassAttributes`
            // (jsx.go's `JsxNames` is a struct of string constants).
            let intrinsic_attributes = c.get_jsx_type("IntrinsicAttributes", self.error_node);
            let intrinsic_class_attributes =
                c.get_jsx_type("IntrinsicClassAttributes", self.error_node);
            if !c.is_error_type(intrinsic_attributes)
                && !c.is_error_type(intrinsic_class_attributes)
                && (target_types.contains(&intrinsic_attributes)
                    || target_types.contains(&intrinsic_class_attributes))
            {
                return;
            }
        } else if original_target_flags.intersects(TypeFlags::INTERSECTION)
            && c.types_handle()
                .get_ref(original_target)
                .object_flags
                .intersects(ObjectFlags::IS_NEVER_INTERSECTION)
        {
            let mut message = &tsc_diagnostics::The_intersection_0_was_reduced_to_never_because_property_1_has_conflicting_types_in_some_constituents;
            let props = c.get_properties_of_union_or_intersection_type(original_target);
            let mut prop = props
                .iter()
                .copied()
                .find(|&p| c.is_discriminant_with_never_type(p));
            if prop.is_none() {
                message = &tsc_diagnostics::The_intersection_0_was_reduced_to_never_because_property_1_exists_in_multiple_constituents_and_is_private_in_some;
                prop = props
                    .iter()
                    .copied()
                    .find(|&p| crate::checker_c::is_conflicting_private_property(c, p));
            }
            if let Some(prop) = prop {
                let target_str = c.type_to_string_ex(
                    original_target,
                    None,
                    crate::types::TypeFormatFlags::NO_TYPE_REDUCTION,
                    None,
                );
                let prop_str = c.symbol_to_string(prop);
                self.report_error(c, message, &[target_str, prop_str]);
            }
        }
        self.report_relation_error(c, head_message, source, target);
        let source_is_unconstrained_param = {
            let __arena_s = c.types.clone();
            let s = __arena_s.get(source);
            s.flags.intersects(TypeFlags::TYPE_PARAMETER)
                && s.symbol
                    .is_some_and(|sym| !c.sym(sym).declarations.is_empty())
                && c.get_constraint_of_type(source).is_none()
        };
        if source_is_unconstrained_param {
            let synthetic_param = c.clone_type_parameter(source);
            {
                let mapper = crate::mapper::new_simple_type_mapper(c, source, synthetic_param);
                let instantiated = c.instantiate_type(target, Some(mapper));
                c.types_handle()
                    .get_mut(synthetic_param)
                    .as_type_parameter_mut()
                    .constraint = Some(instantiated);
            }
            if c.has_non_circular_base_constraint(synthetic_param) {
                let target_constraint_string = c.type_to_string(target);
                let __arena_sym = c.types.clone();
                let sym = __arena_sym.get_ref(source).symbol.unwrap();
                let decl = c.sym(sym).declarations[0];
                let info = c.new_diagnostic_for_node(
                    Some(decl),
                    &tsc_diagnostics::This_type_parameter_might_need_an_extends_0_constraint,
                    &[target_constraint_string],
                );
                self.related_info.push(info);
            }
        }
    }

    /// `(r *Relater) reportRelationError`.
    fn report_relation_error(
        &mut self,
        c: &mut Checker,
        head_message: Option<&'static tsc_diagnostics::Message>,
        source: TypeId,
        target: TypeId,
    ) {
        let (source_type, target_type) = c.get_type_names_for_error_display(source, target);
        let mut generalized_source = source;
        let mut generalized_source_type = source_type.clone();
        // Don't generalize on 'never' - we really want the original type
        // to be displayed for use-cases like 'assertNever'.
        if !c
            .types_handle()
            .get(target)
            .flags
            .intersects(TypeFlags::NEVER)
            && crate::checker_d::is_literal_type(&c.types, source)
            && !c.type_could_have_top_level_singleton_types(target)
        {
            generalized_source = c.get_base_type_of_literal_type(source);
            generalized_source_type = c.get_type_name_for_error_display(generalized_source);
        }
        // If `target` is of indexed access type (and `source` it is not), we
        // use the object type of `target` for better error reporting
        let __arena_source_flags = c.types.clone();
        let source_flags = __arena_source_flags.get_ref(source).flags;
        let __arena_target_flags = c.types.clone();
        let target_flags = __arena_target_flags.get_ref(target).flags;
        let effective_target_flags = if target_flags.intersects(TypeFlags::INDEXED_ACCESS)
            && !source_flags.intersects(TypeFlags::INDEXED_ACCESS)
        {
            c.types_handle()
                .get_ref(target)
                .as_indexed_access_type()
                .object_type
                .map(|o| c.types_handle().get_ref(o).flags)
                .unwrap_or(target_flags)
        } else {
            target_flags
        };
        if effective_target_flags.intersects(TypeFlags::TYPE_PARAMETER)
            && target != c.marker_super_type_for_check
            && target != c.marker_sub_type_for_check
        {
            let constraint = c.get_base_constraint_of_type(target);
            // `IsDistributedTypeParameter` (exports.go) — inlined; exports.go
            // is a separate port. Bound before the call so the arena guard
            // drops before `&mut c` is needed.
            let is_distributed = {
                let __arena_t = c.types.clone();
                let t = __arena_t.get_ref(target);
                t.flags.intersects(TypeFlags::TYPE_PARAMETER)
                    && t.as_type_parameter().is_distributed
            };
            let is_distributed_ok = is_distributed && {
                let __arena___guard_tp_constraint = c.types.clone();
                let tp_constraint = __arena___guard_tp_constraint
                    .get(target)
                    .as_type_parameter()
                    .constraint
                    .unwrap_or(c.never_type);
                c.is_type_assignable_to(generalized_source, tp_constraint)
            };
            if is_distributed_ok {
                self.report_error(
                    c,
                    &tsc_diagnostics::X_0_is_only_assignable_to_the_non_distributed_1_but_1_has_been_distributed_here,
                    &[generalized_source_type.clone(), target_type.clone()],
                );
            } else if constraint.is_some_and(|con| c.is_type_assignable_to(generalized_source, con))
            {
                let con_str = c.type_to_string(constraint.unwrap());
                self.report_error(
                    c,
                    &tsc_diagnostics::X_0_is_assignable_to_the_constraint_of_type_1_but_1_could_be_instantiated_with_a_different_subtype_of_constraint_2,
                    &[generalized_source_type.clone(), target_type.clone(), con_str],
                );
            } else if constraint.is_some_and(|con| c.is_type_assignable_to(source, con)) {
                let con_str = c.type_to_string(constraint.unwrap());
                self.report_error(
                    c,
                    &tsc_diagnostics::X_0_is_assignable_to_the_constraint_of_type_1_but_1_could_be_instantiated_with_a_different_subtype_of_constraint_2,
                    &[source_type.clone(), target_type.clone(), con_str],
                );
            } else {
                self.error_chain = None; // Only report this error once
                self.report_error(
                    c,
                    &tsc_diagnostics::X_0_could_be_instantiated_with_an_arbitrary_type_which_could_be_unrelated_to_1,
                    &[target_type.clone(), generalized_source_type.clone()],
                );
            }
        }
        let mut message = head_message;
        if message.is_none() {
            if Rc::ptr_eq(&self.relation(), &c.comparable_relation) {
                message = Some(&tsc_diagnostics::Type_0_is_not_comparable_to_type_1);
            } else if source_type == target_type {
                message = Some(&tsc_diagnostics::Type_0_is_not_assignable_to_type_1_Two_different_types_with_this_name_exist_but_they_are_unrelated);
            } else if c.exact_optional_property_types
                && !c
                    .get_exact_optional_unassignable_properties(source, target)
                    .is_empty()
            {
                message = Some(&tsc_diagnostics::Type_0_is_not_assignable_to_type_1_with_exactOptionalPropertyTypes_Colon_true_Consider_adding_undefined_to_the_types_of_the_target_s_properties);
            } else {
                if source_flags.intersects(TypeFlags::STRING_LITERAL)
                    && target_flags.intersects(TypeFlags::UNION)
                {
                    if let Some(suggested_type) =
                        c.get_suggested_type_for_nonexistent_string_literal_type(source, target)
                    {
                        let suggested_str = c.type_to_string(suggested_type);
                        self.report_error(
                            c,
                            &tsc_diagnostics::Type_0_is_not_assignable_to_type_1_Did_you_mean_2,
                            &[
                                generalized_source_type.clone(),
                                target_type.clone(),
                                suggested_str,
                            ],
                        );
                        return;
                    }
                }
                message = Some(&tsc_diagnostics::Type_0_is_not_assignable_to_type_1);
            }
        } else if message.is_some_and(|m| {
            std::ptr::eq(
                m,
                &tsc_diagnostics::Argument_of_type_0_is_not_assignable_to_parameter_of_type_1,
            )
        }) && c.exact_optional_property_types
            && !c
                .get_exact_optional_unassignable_properties(source, target)
                .is_empty()
        {
            message = Some(&tsc_diagnostics::Argument_of_type_0_is_not_assignable_to_parameter_of_type_1_with_exactOptionalPropertyTypes_Colon_true_Consider_adding_undefined_to_the_types_of_the_target_s_properties);
        }
        let message = message.unwrap();
        match self.get_chain_message(0) {
            // Suppress if next message is an excess property error
            Some(m)
                if std::ptr::eq(m, &tsc_diagnostics::Object_literal_may_only_specify_known_properties_and_0_does_not_exist_in_type_1)
                    || std::ptr::eq(m, &tsc_diagnostics::Object_literal_may_only_specify_known_properties_but_0_does_not_exist_in_type_1_Did_you_mean_to_write_2) =>
            {
                return;
            }
            // Suppress if next message is an excessive complexity/stack depth
            // message for source and target or a readonly vs. mutable error
            // for source and target
            Some(m)
                if std::ptr::eq(m, &tsc_diagnostics::Excessive_complexity_comparing_types_0_and_1)
                    || std::ptr::eq(m, &tsc_diagnostics::The_type_0_is_readonly_and_cannot_be_assigned_to_the_mutable_type_1) =>
            {
                if self.chain_args_match(&[
                    Some(generalized_source_type.clone()),
                    Some(target_type.clone()),
                ]) {
                    return;
                }
            }
            // Suppress if next message is a missing property message for
            // source and target and we're not reporting on conversion or
            // interface implementation
            Some(m)
                if std::ptr::eq(m, &tsc_diagnostics::Property_0_is_missing_in_type_1_but_required_in_type_2) =>
            {
                if !is_conversion_or_interface_implementation_message(message)
                    && self.chain_args_match(&[
                        None,
                        Some(generalized_source_type.clone()),
                        Some(target_type.clone()),
                    ])
                {
                    return;
                }
            }
            // Suppress if next message is a missing property message for
            // source and target and we're not reporting on conversion or
            // interface implementation
            Some(m)
                if std::ptr::eq(m, &tsc_diagnostics::Type_0_is_missing_the_following_properties_from_type_1_Colon_2_and_3_more)
                    || std::ptr::eq(m, &tsc_diagnostics::Type_0_is_missing_the_following_properties_from_type_1_Colon_2) =>
            {
                if !is_conversion_or_interface_implementation_message(message)
                    && self.chain_args_match(&[
                        Some(generalized_source_type.clone()),
                        Some(target_type.clone()),
                    ])
                {
                    return;
                }
            }
            _ => {}
        }
        self.report_error(c, message, &[generalized_source_type, target_type]);
    }

    /// `(r *Relater) reportError`.
    pub(crate) fn report_error(
        &mut self,
        c: &mut Checker,
        message: &'static tsc_diagnostics::Message,
        args: &[String],
    ) {
        let mut message = message;
        let mut args_vec = args.to_vec();
        if std::ptr::eq(
            message,
            &tsc_diagnostics::Types_of_property_0_are_incompatible,
        ) {
            // Suppress if next message is an excess property error
            match self.get_chain_message(0) {
                Some(m)
                    if std::ptr::eq(m, &tsc_diagnostics::Object_literal_may_only_specify_known_properties_and_0_does_not_exist_in_type_1)
                        || std::ptr::eq(m, &tsc_diagnostics::Object_literal_may_only_specify_known_properties_but_0_does_not_exist_in_type_1_Did_you_mean_to_write_2) =>
                {
                    return;
                }
                _ => {}
            }
            // Transform a property incompatibility message for property 'x'
            // followed by some elaboration message followed by a signature
            // return type incompatibility message into a single return type
            // incompatibility message for 'x()' or 'x(...)'
            let mut arg: Option<String> = None;
            match self.get_chain_message(1) {
                Some(m)
                    if std::ptr::eq(m, &tsc_diagnostics::Call_signatures_with_no_arguments_have_incompatible_return_types_0_and_1) =>
                {
                    arg = Some(format!("{}()", get_property_name_arg(&args_vec[0])));
                }
                Some(m)
                    if std::ptr::eq(m, &tsc_diagnostics::Construct_signatures_with_no_arguments_have_incompatible_return_types_0_and_1) =>
                {
                    arg = Some(format!(
                        "new {}()",
                        get_property_name_arg(&args_vec[0])
                    ));
                }
                Some(m)
                    if std::ptr::eq(m, &tsc_diagnostics::Call_signature_return_types_0_and_1_are_incompatible) =>
                {
                    arg = Some(format!(
                        "{}(...)",
                        get_property_name_arg(&args_vec[0])
                    ));
                }
                Some(m)
                    if std::ptr::eq(m, &tsc_diagnostics::Construct_signature_return_types_0_and_1_are_incompatible) =>
                {
                    arg = Some(format!(
                        "new {}(...)",
                        get_property_name_arg(&args_vec[0])
                    ));
                }
                _ => {}
            }
            if let Some(arg) = arg {
                message =
                    &tsc_diagnostics::The_types_returned_by_0_are_incompatible_between_these_types;
                args_vec[0] = arg;
                self.error_chain = self
                    .error_chain
                    .take()
                    .and_then(|e| e.next)
                    .and_then(|e| e.next);
            }
            // Transform a property incompatibility message for property 'x'
            // followed by some elaboration message followed by a property
            // incompatibility message for property 'y' into a single property
            // incompatibility message for 'x.y'
            match self.get_chain_message(1) {
                Some(m)
                    if std::ptr::eq(m, &tsc_diagnostics::Types_of_property_0_are_incompatible)
                        || std::ptr::eq(m, &tsc_diagnostics::The_types_of_0_are_incompatible_between_these_types)
                        || std::ptr::eq(m, &tsc_diagnostics::The_types_returned_by_0_are_incompatible_between_these_types) =>
                {
                    let head = get_property_name_arg(&args_vec[0]);
                    let tail = self
                        .error_chain
                        .as_ref()
                        .and_then(|e| e.next.as_ref())
                        .and_then(|e| e.args.first().cloned())
                        .map(|a| get_property_name_arg(&a))
                        .unwrap_or_default();
                    let arg = add_to_dotted_name(&head, &tail);
                    self.error_chain = self
                        .error_chain
                        .take()
                        .and_then(|e| e.next)
                        .and_then(|e| e.next);
                    if std::ptr::eq(message, &tsc_diagnostics::Types_of_property_0_are_incompatible) {
                        message = &tsc_diagnostics::The_types_of_0_are_incompatible_between_these_types;
                    }
                    self.report_error(c, message, &[arg]);
                    return;
                }
                _ => {}
            }
        }
        self.error_chain = Some(Box::new(ErrorChain {
            next: self.error_chain.take(),
            message: Some(message),
            args: args_vec,
        }));
    }

    /// `(r *Relater) getChainMessage`.
    fn get_chain_message(&self, index: usize) -> Option<&'static tsc_diagnostics::Message> {
        let mut e = self.error_chain.as_deref();
        let mut index = index;
        loop {
            e?;
            if index == 0 {
                return e.and_then(|e| e.message);
            }
            e = e.and_then(|e| e.next.as_deref());
            index -= 1;
        }
    }

    /// `(r *Relater) chainArgsMatch` — return true if the arguments of the
    /// first entry on the error chain match the given arguments (where
    /// `None` acts as a wildcard).
    fn chain_args_match(&self, args: &[Option<String>]) -> bool {
        let chain = match &self.error_chain {
            Some(e) => e,
            None => return false,
        };
        for (i, a) in args.iter().enumerate() {
            if let Some(a) = a {
                if chain.args.get(i) != Some(a) {
                    return false;
                }
            }
        }
        true
    }

    /// `(r *Relater) traceUnionsOrIntersectionsTooLarge`.
    fn trace_unions_or_intersections_too_large(
        &mut self,
        c: &mut Checker,
        source: TypeId,
        target: TypeId,
    ) {
        let Some(tr) = &c.tracer else {
            return;
        };
        let (source_flags, target_flags) = {
            let __arena_s = c.types.clone();
            let s = __arena_s.get_ref(source);
            (s.flags, c.types_handle().get_ref(target).flags)
        };
        if source_flags.intersects(TypeFlags::UNION_OR_INTERSECTION)
            && target_flags.intersects(TypeFlags::UNION_OR_INTERSECTION)
        {
            if (c.types_handle().get_ref(source).object_flags
                & c.types_handle().get_ref(target).object_flags)
                .intersects(ObjectFlags::PRIMITIVE_UNION)
            {
                // There's a fast path for comparing primitive unions
                return;
            }
            let __arena_source_size = c.types.clone();
            let source_size = __arena_source_size.get_ref(source).types().len();
            let __arena_target_size = c.types.clone();
            let target_size = __arena_target_size.get_ref(target).types().len();
            if source_size * target_size > 1_000_000 {
                let mut args = TraceArgs::new();
                args.insert("sourceId".to_string(), source.0.into());
                args.insert("sourceSize".to_string(), (source_size as i64).into());
                args.insert("targetId".to_string(), target.0.into());
                args.insert("targetSize".to_string(), (target_size as i64).into());
                tr.instant(
                    tsc_tracing::PHASE_CHECK_TYPES,
                    "traceUnionsOrIntersectionsTooLarge_DepthLimit",
                    &args,
                );
            }
        }
    }
}

/// `addToDottedName` (relater.go).
fn add_to_dotted_name(head: &str, tail: &str) -> String {
    let head_owned;
    let head = if head.starts_with("new ") {
        head_owned = format!("({})", head);
        head_owned.as_str()
    } else {
        head
    };
    let mut pos = 0;
    loop {
        if tail[pos..].starts_with('(') {
            pos += 1;
        } else if tail[pos..].starts_with("new ") {
            pos += 4;
        } else {
            break;
        }
    }
    let prefix = &tail[..pos];
    let suffix = &tail[pos..];
    if suffix.starts_with('[') {
        return format!("{}{}{}", prefix, head, suffix);
    }
    format!("{}{}.{}", prefix, head, suffix)
}

/// `getPropertyNameArg` (relater.go).
fn get_property_name_arg(arg: &str) -> String {
    if !arg.is_empty() && (arg.starts_with('"') || arg.starts_with('\'') || arg.starts_with('`')) {
        return format!("[{}]", arg);
    }
    arg.to_string()
}

/// `isConversionOrInterfaceImplementationMessage` (relater.go).
fn is_conversion_or_interface_implementation_message(
    message: &'static tsc_diagnostics::Message,
) -> bool {
    std::ptr::eq(message, &tsc_diagnostics::Class_0_incorrectly_implements_interface_1)
        || std::ptr::eq(message, &tsc_diagnostics::Class_0_incorrectly_implements_class_1_Did_you_mean_to_extend_1_and_inherit_its_members_as_a_subclass)
        || std::ptr::eq(message, &tsc_diagnostics::Conversion_of_type_0_to_type_1_may_be_a_mistake_because_neither_type_sufficiently_overlaps_with_the_other_If_this_was_intentional_convert_the_expression_to_unknown_first)
        || std::ptr::eq(message, &tsc_diagnostics::Its_instance_type_0_is_not_a_valid_JSX_element)
        || std::ptr::eq(message, &tsc_diagnostics::Its_return_type_0_is_not_a_valid_JSX_element)
        || std::ptr::eq(message, &tsc_diagnostics::Its_element_type_0_is_not_a_valid_JSX_element)
}

/// `chainDepth` (relater.go).
fn chain_depth(chain: Option<&ErrorChain>) -> usize {
    let mut depth = 0;
    let mut chain = chain;
    while let Some(e) = chain {
        depth += 1;
        chain = e.next.as_deref();
    }
    depth
}

impl Checker {
    /// `(c *Checker) isObjectTypeWithInferableIndex` — return true if the
    /// type was inferred from
    ///   - an object literal, object type literal, enum type, or a value
    ///     module and has no call or construct signatures, or
    ///   - a JS expando object literal or a rest type, or
    ///   - a reverse mapped type with a source for which one of the above is
    ///     true.
    pub(crate) fn is_object_type_with_inferable_index(&mut self, t: TypeId) -> bool {
        let (flags, object_flags, symbol) = {
            let __arena_ty = self.types.clone();
            let ty = __arena_ty.get_ref(t);
            (ty.flags, ty.object_flags, ty.symbol)
        };
        if flags.intersects(TypeFlags::INTERSECTION) {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(t).types().to_vec();
            return types
                .iter()
                .all(|&t| self.is_object_type_with_inferable_index(t));
        }
        symbol.is_some_and(|s| {
            let flags = self.sym(s).flags;
            flags.intersects(
                ast::SymbolFlags::OBJECT_LITERAL
                    | ast::SymbolFlags::TYPE_LITERAL
                    | ast::SymbolFlags::ENUM
                    | ast::SymbolFlags::VALUE_MODULE,
            ) && !flags.intersects(ast::SymbolFlags::CLASS)
                && !self.type_has_call_or_construct_signatures(t)
        }) || object_flags.intersects(ObjectFlags::JS_LITERAL | ObjectFlags::OBJECT_REST_TYPE)
            || object_flags.intersects(ObjectFlags::REVERSE_MAPPED) && {
                let __arena___guard_source = self.types.clone();
                let __guard_source = __arena___guard_source.get(t).clone();
                let source = __guard_source.as_reverse_mapped_type().source;
                source.is_some_and(|s| self.is_object_type_with_inferable_index(s))
            }
    }
}

impl Checker {
    /// `(c *Checker) isTypeDerivedFrom` — an object type S is considered to
    /// be derived from an object type T if S is a union type and every
    /// constituent of S is derived from T, T is a union type and S is
    /// derived from at least one constituent of T, or S is an intersection
    /// type and some constituent of S is derived from T, or S is a type
    /// variable with a base constraint that is derived from T, or T is {}
    /// and S is an object-like type (ensuring {} is less derived than
    /// Object), or T is one of the global types Object and Function and S is
    /// a subtype of T, or T occurs directly or indirectly in an 'extends'
    /// clause of S.
    /// Note that this check ignores type parameters and only considers the
    /// inheritance hierarchy.
    pub(crate) fn is_type_derived_from(&mut self, source: TypeId, target: TypeId) -> bool {
        let __arena_source_flags = self.types.clone();
        let source_flags = __arena_source_flags.get_ref(source).flags;
        let __arena_target_flags = self.types.clone();
        let target_flags = __arena_target_flags.get_ref(target).flags;
        if source_flags.intersects(TypeFlags::UNION) {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(source).types().to_vec();
            return types.iter().all(|&t| self.is_type_derived_from(t, target));
        }
        if target_flags.intersects(TypeFlags::UNION) {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(target).types().to_vec();
            return types.iter().any(|&t| self.is_type_derived_from(source, t));
        }
        if source_flags.intersects(TypeFlags::INTERSECTION) {
            let __arena_types = self.types.clone();
            let types = __arena_types.get_ref(source).types().to_vec();
            return types.iter().any(|&t| self.is_type_derived_from(t, target));
        }
        if source_flags.intersects(TypeFlags::INSTANTIABLE_NON_PRIMITIVE) {
            let constraint = self
                .get_base_constraint_of_type(source)
                .unwrap_or(self.unknown_type);
            return self.is_type_derived_from(constraint, target);
        }
        if self.is_empty_anonymous_object_type(target) {
            return source_flags.intersects(TypeFlags::OBJECT | TypeFlags::NON_PRIMITIVE);
        }
        if target == self.global_object_type {
            return source_flags.intersects(TypeFlags::OBJECT | TypeFlags::NON_PRIMITIVE)
                && !self.is_empty_anonymous_object_type(source);
        }
        if target == self.global_function_type {
            return source_flags.intersects(TypeFlags::OBJECT)
                && self.is_function_object_type(source);
        }
        self.has_base_type(
            source,
            Some(crate::checker_c::get_target_type(&self.types, target)),
        ) || self.is_array_type(target)
            && !self.is_readonly_array_type(target)
            && self.is_type_derived_from(source, self.global_readonly_array_type)
    }

    /// `(c *Checker) isDistributionDependent`.
    pub(crate) fn is_distribution_dependent(
        &mut self,
        root: &crate::types::ConditionalRoot,
    ) -> bool {
        root.is_distributive
            && (root.check_type.is_some_and(|check_type| {
                let node = root.node;
                let true_type = node.and_then(|n| {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((n).file_index());
                    nodes[n].as_conditional_type_node().true_type
                });
                true_type
                    .is_some_and(|tt| self.is_type_parameter_possibly_referenced(check_type, tt))
            }) || root.check_type.is_some_and(|check_type| {
                let node = root.node;
                let false_type = node.and_then(|n| {
                    let __program = self.program.clone().expect("program");
                    let nodes = __program.nodes((n).file_index());
                    nodes[n].as_conditional_type_node().false_type
                });
                false_type
                    .is_some_and(|ft| self.is_type_parameter_possibly_referenced(check_type, ft))
            }))
    }
}

// __NEXT__
