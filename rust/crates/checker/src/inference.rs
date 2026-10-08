// Ported from tsc/internal/checker/inference.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the per-call inference state
// referenced by `Checker` (`InferenceKey`, `InferenceState` and its free
// list). `InferenceFlags`/`InferenceContext`/`InferenceInfo`/
// `InferencePriority` live in checker_core.rs (foundation-phase port);
// inferTypes and friends stay `PORT(deferred)`.

use rustc_hash::FxHashMap;

use crate::checker_core::{Checker, InferenceInfo, InferencePriority};
use crate::relater::ExpandingFlags;
use crate::types::TypeId;

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

/// `type InferenceState struct` (inference.go) — PORT(partial): Go's
/// `inferences []*InferenceInfo` aliases the `InferenceContext.inferences`
/// slice (writes propagate). Here it is an owned `Vec`; the `infer_types`
/// port will need to route through the owning `InferenceContextId` or
/// share entries — wave-2 decides (see PORTING-NOTES.md).
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
}
