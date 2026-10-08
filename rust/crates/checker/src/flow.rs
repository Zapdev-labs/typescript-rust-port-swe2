// Ported from tsc/internal/checker/flow.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — the control-flow-analysis state
// types referenced by `Checker` (`FlowType`, `SharedFlow`, `FlowState`) and
// the `typeofNEFacts` table. Method bodies stay `PORT(deferred)`.

use tsc_ast::{FlowNodeId, NodeId};

use crate::checker_core::{CacheHashKey, Checker};
use crate::checker_types::TypeFacts;
use crate::types::{TypeFlags, TypeId};

/// `type FlowType struct` (flow.go). Go's `t *Type` may be nil —
/// `isNil()` reports `t == nil`; the port is `Option<TypeId>`.
#[derive(Clone, Copy, Default)]
pub struct FlowType {
    /// `t`.
    pub t: Option<TypeId>,
    /// `incomplete`.
    pub incomplete: bool,
}

impl FlowType {
    /// `(ft *FlowType) isNil`.
    pub fn is_nil(&self) -> bool {
        self.t.is_none()
    }
}

/// `(c *Checker) newFlowType` (flow.go).
pub fn new_flow_type(c: &mut Checker, t: TypeId, incomplete: bool) -> FlowType {
    let t = if incomplete && c.types.get(t).flags.intersects(TypeFlags::NEVER) {
        c.silent_never_type
    } else {
        t
    };
    FlowType {
        t: Some(t),
        incomplete,
    }
}

/// `type SharedFlow struct` (flow.go). Go's zero `flow *ast.FlowNode` is
/// nil — `FlowNodeId::NONE`, not the derived `FlowNodeId(0)`.
#[derive(Clone, Copy)]
pub struct SharedFlow {
    /// `flow`.
    pub flow: FlowNodeId,
    /// `flowType`.
    pub flow_type: FlowType,
}

impl Default for SharedFlow {
    fn default() -> Self {
        SharedFlow {
            flow: FlowNodeId::NONE,
            flow_type: FlowType::default(),
        }
    }
}

/// `type FlowState struct` (flow.go). `reduceLabels []*ast.FlowReduceLabelData`
/// — a `FlowReduceLabelData` is embedded in a flow `Node`, so `FlowNodeId`
/// is the port's pointer.
#[derive(Default)]
pub struct FlowState {
    /// `reference`.
    pub reference: Option<NodeId>,
    /// `declaredType`.
    pub declared_type: Option<TypeId>,
    /// `initialType`.
    pub initial_type: Option<TypeId>,
    /// `flowContainer`.
    pub flow_container: Option<NodeId>,
    /// `refKey`.
    pub ref_key: CacheHashKey,
    /// `depth`.
    pub depth: i32,
    /// `sharedFlowStart`.
    pub shared_flow_start: usize,
    /// `reduceLabels`.
    pub reduce_labels: Vec<FlowNodeId>,
    /// `next` — free-list link (`Checker::free_flow_state`).
    pub next: Option<Box<FlowState>>,
}

impl Checker {
    /// `(c *Checker) getFlowState` (flow.go).
    pub fn get_flow_state(&mut self) -> Box<FlowState> {
        let mut f = self
            .free_flow_state
            .take()
            .unwrap_or_else(|| Box::new(FlowState::default()));
        self.free_flow_state = f.next.take();
        f
    }

    /// `(c *Checker) putFlowState` (flow.go). Go keeps the backing array
    /// (`f.reduceLabels[:0]`).
    pub fn put_flow_state(&mut self, mut f: Box<FlowState>) {
        let mut reused = FlowState::default();
        reused.reduce_labels = std::mem::take(&mut f.reduce_labels);
        reused.reduce_labels.clear();
        reused.next = self.free_flow_state.take();
        *f = reused;
        self.free_flow_state = Some(f);
    }
}

/// `getFlowNodeOfNode` (flow.go) — `node.FlowNodeData().FlowNode` → the
/// flow node attached to `node`, if any.
pub fn get_flow_node_of_node(nodes: &[tsc_ast::Node], node: NodeId) -> Option<FlowNodeId> {
    nodes[node]
        .flow_node_data()
        .and_then(|data| data.flow_node)
}

/// `var typeofNEFacts` (flow.go) — facts about `typeof x != "name"`.
pub fn typeof_ne_facts(type_name: &str) -> Option<TypeFacts> {
    match type_name {
        "string" => Some(TypeFacts::TYPEOF_NE_STRING),
        "number" => Some(TypeFacts::TYPEOF_NE_NUMBER),
        "bigint" => Some(TypeFacts::TYPEOF_NE_BIG_INT),
        "boolean" => Some(TypeFacts::TYPEOF_NE_BOOLEAN),
        "symbol" => Some(TypeFacts::TYPEOF_NE_SYMBOL),
        "undefined" => Some(TypeFacts::NE_UNDEFINED),
        "object" => Some(TypeFacts::TYPEOF_NE_OBJECT),
        "function" => Some(TypeFacts::TYPEOF_NE_FUNCTION),
        _ => None,
    }
}
