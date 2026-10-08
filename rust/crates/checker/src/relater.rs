// Ported from tsc/internal/checker/relater.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the declarations needed by the
// `Checker` struct's relation state (`relation.go`-style flags, `Relation`,
// `Relater`, `ErrorChain`). Method bodies stay `PORT(deferred)`; this file
// carries the flag types, result enums, and data structures only.
//
// `RecursionId` already lives in checker_core.rs (mirrored earlier for
// tracer.rs); it stays there.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, NodeId, SymbolId};
use tsc_collections::OrderedSet;

use crate::checker_core::{CacheHashKey, Checker};
use crate::flagdef::flag_type;
use crate::types::{Ternary, TypeId};

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
    pub const STRONG_ARITY_FOR_UNTYPED_JS: MinArgumentCountFlags =
        MinArgumentCountFlags(1 << 0);
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
    pub const BOTH: RecursionFlags =
        RecursionFlags(Self::SOURCE.0 | Self::TARGET.0);
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
    pub const REPORTS_UNMEASURABLE: RelationComparisonResult =
        RelationComparisonResult(1 << 3);
    /// `RelationComparisonResultReportsUnreliable`.
    pub const REPORTS_UNRELIABLE: RelationComparisonResult =
        RelationComparisonResult(1 << 4);
    /// `RelationComparisonResultComplexityOverflow`.
    pub const COMPLEXITY_OVERFLOW: RelationComparisonResult =
        RelationComparisonResult(1 << 5);
    /// `RelationComparisonResultReportsMask`.
    pub const REPORTS_MASK: RelationComparisonResult = RelationComparisonResult(
        Self::REPORTS_UNMEASURABLE.0 | Self::REPORTS_UNRELIABLE.0,
    );
    /// `RelationComparisonResultOverflow`.
    pub const OVERFLOW: RelationComparisonResult = Self::COMPLEXITY_OVERFLOW;
}

// DiagnosticAndArguments

/// `type DiagnosticAndArguments struct` (relater.go). `arguments []any` →
/// `Vec<String>` per this port's diagnostic-args convention.
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
/// (relater.go). Go closures capture the relater (and through it the
/// checker); wave-2 decides the exact receiver — see PORT note on
/// `Relater::report_error`.
pub type ErrorReporter<'a> =
    dyn FnMut(&'static tsc_diagnostics::Message, Vec<String>) + 'a;

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
#[derive(Default)]
pub struct ErrorState {
    /// `errorChain`.
    pub error_chain: Option<Box<ErrorChain>>,
    /// `relatedInfo`.
    pub related_info: Vec<ast::diagnostic::DiagnosticRef>,
}

/// `type ErrorChain struct` (relater.go).
#[derive(Default)]
pub struct ErrorChain {
    /// `next`.
    pub next: Option<Box<ErrorChain>>,
    /// `message`.
    pub message: Option<&'static tsc_diagnostics::Message>,
    /// `args` — `[]any` → `Vec<String>`.
    pub args: Vec<String>,
}

// Relater

/// `type Relater struct` (relater.go) — PORT(partial): data only. The `c
/// *Checker` back-pointer is dropped (methods take `&mut Checker`), and
/// `relation` is the shared `Rc<RefCell<Relation>>` also stored on the
/// checker — Go aliases the same `*Relation`.
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

// TypeDiscriminator / Discriminator

/// `type TypeDiscriminator struct` (relater.go) — PORT(partial): `c
/// *Checker` dropped; `isRelatedTo` takes `&mut Checker`.
pub struct TypeDiscriminator {
    /// `props`.
    pub props: Vec<SymbolId>,
    /// `isRelatedTo`.
    pub is_related_to: Rc<dyn Fn(&mut Checker, TypeId, TypeId) -> Ternary + 'static>,
}

/// `type Discriminator interface` (relater.go). `matches` needs checker
/// state (it calls `getTypeOfSymbol`), so the trait takes `&mut Checker`.
pub trait Discriminator {
    /// `len() int` — number of discriminant properties.
    fn len(&self) -> usize;
    /// `name(index int) string` — property name of index-th discriminator.
    fn name(&self, index: usize) -> &str;
    /// `matches(index int, t *Type) bool`.
    fn matches(&self, c: &mut Checker, index: usize, t: TypeId) -> bool;

    /// `len() == 0` convenience.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
