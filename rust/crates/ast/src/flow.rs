// Ported from tsc/internal/ast/flow.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// FlowFlags, FlowNode, FlowList, and the two synthetic AST payloads used by
// the flow graph (`FlowSwitchClauseData`, `FlowReduceLabelData`).
//
// Flow nodes are stored in a `Vec<FlowNode>` owned by the binder; `FlowNodeId`
// / `FlowListId` index it. The synthetic payloads are `NodeData` variants that
// carry `Kind::Unknown`, matching Go's `newNode(KindUnknown, ...)`.

use crate::ast_generated::FlowReduceLabelData;
use crate::ids::{FlowListId, FlowNodeId, NodeId};
use crate::{Node, NodeFactoryHooks};

// FlowFlags

flag_type! {
    pub struct FlowFlags(pub u32);
}

impl FlowFlags {
    /// Unreachable code
    pub const UNREACHABLE: FlowFlags = FlowFlags(1 << 0);
    /// Start of flow graph
    pub const START: FlowFlags = FlowFlags(1 << 1);
    /// Non-looping junction
    pub const BRANCH_LABEL: FlowFlags = FlowFlags(1 << 2);
    /// Looping junction
    pub const LOOP_LABEL: FlowFlags = FlowFlags(1 << 3);
    /// Assignment
    pub const ASSIGNMENT: FlowFlags = FlowFlags(1 << 4);
    /// Condition known to be true
    pub const TRUE_CONDITION: FlowFlags = FlowFlags(1 << 5);
    /// Condition known to be false
    pub const FALSE_CONDITION: FlowFlags = FlowFlags(1 << 6);
    /// Switch statement clause
    pub const SWITCH_CLAUSE: FlowFlags = FlowFlags(1 << 7);
    /// Potential array mutation
    pub const ARRAY_MUTATION: FlowFlags = FlowFlags(1 << 8);
    /// Potential assertion call
    pub const CALL: FlowFlags = FlowFlags(1 << 9);
    /// Temporarily reduce antecedents of label
    pub const REDUCE_LABEL: FlowFlags = FlowFlags(1 << 10);
    /// Referenced as antecedent once
    pub const REFERENCED: FlowFlags = FlowFlags(1 << 11);
    /// Referenced as antecedent more than once
    pub const SHARED: FlowFlags = FlowFlags(1 << 12);

    pub const LABEL: FlowFlags = FlowFlags(Self::BRANCH_LABEL.0 | Self::LOOP_LABEL.0);
    pub const CONDITION: FlowFlags = FlowFlags(Self::TRUE_CONDITION.0 | Self::FALSE_CONDITION.0);
}

// FlowNode

#[derive(Clone, Default)]
pub struct FlowNode {
    pub flags: FlowFlags,
    /// Associated AST node
    pub node: Option<NodeId>,
    /// Antecedent for all but FlowLabel
    pub antecedent: Option<FlowNodeId>,
    /// Linked list of antecedents for FlowLabel
    pub antecedents: Option<FlowListId>,
}

pub type FlowLabel = FlowNode;

// FlowList

#[derive(Clone, Copy, Default)]
pub struct FlowList {
    pub flow: Option<FlowNodeId>,
    pub next: Option<FlowListId>,
}

// FlowSwitchClauseData / FlowReduceLabelData payloads are declared in
// ast_generated.rs (as `NodeData` variants); their constructors are
// hand-written here since they bypass the NodeFactory.

/// Ported from `NewFlowSwitchClauseData` in flow.go.
pub fn new_flow_switch_clause_data(
    nodes: &mut Vec<Node>,
    switch_statement: Option<NodeId>,
    clause_start: i32,
    clause_end: i32,
) -> NodeId {
    let data = crate::ast_generated::FlowSwitchClauseData {
        switch_statement,
        clause_start,
        clause_end,
    };
    crate::ast::new_node(
        nodes,
        0,
        crate::Kind::Unknown,
        crate::NodeData::FlowSwitchClauseData(data),
        &mut NodeFactoryHooks::default(),
    )
}

/// `(node *FlowSwitchClauseData) IsEmpty`
pub fn flow_switch_clause_data_is_empty(node: &crate::ast_generated::FlowSwitchClauseData) -> bool {
    node.clause_start == node.clause_end
}

/// Ported from `NewFlowReduceLabelData` in flow.go.
pub fn new_flow_reduce_label_data(
    nodes: &mut Vec<Node>,
    target: Option<FlowNodeId>,
    antecedents: Option<FlowListId>,
) -> NodeId {
    let data = FlowReduceLabelData {
        target,
        antecedents,
    };
    crate::ast::new_node(
        nodes,
        0,
        crate::Kind::Unknown,
        crate::NodeData::FlowReduceLabelData(data),
        &mut NodeFactoryHooks::default(),
    )
}
