// Ported from tsc/internal/checker/flow.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — control-flow analysis: flow
// typing, narrowing, reachability, loop handling, exhaustive switch
// handling, evolving-array tracking, and assignment marking.
//
// Pointer mapping (see checker_core.rs):
//   `*Type`        -> `TypeId` (`Option<TypeId>` where Go returns nil)
//   `*ast.Node`    -> `NodeId` (`Option<NodeId>` where nil is possible)
//   `*ast.Symbol`  -> `SymbolId` / `Option<SymbolId>`
//   `*Signature`   -> `SignatureId` / `Option<SignatureId>`
//   `*ast.FlowNode`-> `FlowNodeId` / `Option<FlowNodeId>`
//   `*ast.FlowList`-> `Option<FlowListId>`
//   `*TypePredicate` -> `TypePredicate` (clone; the struct is a small POD)
//   `*ast.Diagnostic` -> `Option<DiagnosticRef>`
//   `*ast.FlowSwitchClauseData` -> `SwitchClauseData` snapshot (`FlowSwitchClauseData`
//      is a generated `NodeData` payload that does not implement `Clone`, so the
//      port snapshots its three `Copy` fields; flow graphs are per-file and the
//      snapshot lifetime is a single call — see PORT(note) below).
//
// Arenas: `FlowNodeId`/`FlowListId` index the per-file `BindResult` arenas
// produced by the binder; `NodeId` indexes the per-file `Vec<ast::Node>`
// arena. Go dereferences heap pointers so file context is implicit; the port
// carries it on `FlowState` (`nodes` + `file`, set at every public entry
// point from the referencing `NodeId`'s `file_index`), and helpers that
// dereference AST nodes take an explicit `nodes: &[ast::Node]` parameter —
// the same convention as `get_flow_node_of_node` and `crate::utilities`.
//
// Cross-file calls are written as direct snake_case references —
// `self.<method>(...)` for Checker methods owned by checker_a.rs/
// checker_c.rs/checker_d.rs/checker_core.rs, and `crate::<module>::<fn>(...)`
// for free functions owned by other Go files (`crate::utilities` for
// utilities.go, `crate::checker_b`/`crate::checker_d` for checker.go free
// functions per their line ranges). They resolve when the sibling files
// land.

use std::rc::Rc;
use std::sync::LazyLock;

use tsc_ast::checkflags::CheckFlags;
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::{FlowFlags, FlowListId, FlowNode, FlowNodeId, Kind, NodeId, SymbolId, self as ast};

use crate::checker_core::{CacheHashKey, CheckMode, Checker};
use crate::checker_types::{
    AssignmentReducedKey, CachedTypeKey, CachedTypeKind, FlowLoopInfo, FlowLoopKey, IterationUse,
    KeyBuilder, NarrowedTypeKey, TypeFacts, UnionReduction, hash_string_128,
};
use crate::types::{
    ExhaustiveState, NodeCheckFlags, ObjectFlags, SignatureId, SignatureKind, TypeArena, TypeData,
    TypeFlags, TypeId, TypePredicate, TypePredicateKind,
};

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

    /// `FlowType{}` — the Go zero value (nil `t`, `incomplete` false).
    pub fn none() -> FlowType {
        FlowType::default()
    }

    /// `flowType.t` at call sites where Go has established `t != nil`.
    pub fn ty(&self) -> TypeId {
        self.t.expect("flow type is nil")
    }
}

/// `(c *Checker) newFlowType` (flow.go).
pub fn new_flow_type(c: &mut Checker, t: TypeId, incomplete: bool) -> FlowType {
    let t = if incomplete && c.types_handle().get(t).flags.intersects(TypeFlags::NEVER) {
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
/// — a `FlowReduceLabelData` is embedded in a synthetic flow `Node`, so the
/// port stores the payload `NodeId`s and dereferences them through `nodes`.
///
/// PORT(addition): `nodes`/`file` carry the flow graph's owning file context
/// (Go's `*ast.FlowNode` heap pointers resolve globally; `FlowNodeId` /
/// `FlowListId` index the per-file `BindResult` arenas). Both are populated
/// by `set_flow_context` at each public entry point.
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
    /// `reduceLabels` — `NodeId`s of synthetic `FlowReduceLabelData` nodes.
    pub reduce_labels: Vec<NodeId>,
    /// `next` — free-list link (`Checker::free_flow_state`).
    pub next: Option<Box<FlowState>>,
    /// PORT(addition): shared handle of the owning file's arena — an
    /// `Rc<ArenaCell>` so nodes appended through `Program::nodes_mut`
    /// (synthetic `FlowSwitchClauseData` / `FlowReduceLabelData` payloads)
    /// stay visible through later snapshots.
    pub nodes: Option<Rc<ast::ArenaCell>>,
    /// PORT(addition): `NodeId` of the owning file's `SourceFile` — used to
    /// reach `tsc_binder::bind_result` (the `flow_nodes`/`flow_lists` arenas).
    pub file: Option<NodeId>,
}

impl FlowState {
    /// `f.reference` at call sites where Go has established it is non-nil.
    pub fn reference(&self) -> NodeId {
        self.reference.expect("FlowState.reference unset")
    }

    /// `f.declaredType` at call sites where Go has established it is non-nil.
    pub fn declared_type(&self) -> TypeId {
        self.declared_type.expect("FlowState.declaredType unset")
    }

    /// `f.initialType` at call sites where Go has established it is non-nil.
    pub fn initial_type(&self) -> TypeId {
        self.initial_type.expect("FlowState.initialType unset")
    }

    /// The owning file's node arena (every AST node touched by the flow
    /// graph, including the synthetic `FlowSwitchClauseData` /
    /// `FlowReduceLabelData` payloads, lives here).
    ///
    /// Returns an `Rc` snapshot of the shared arena — snapshots never pin a
    /// borrow, so `&mut FlowState` use while a snapshot is live is fine.
    /// Re-call for post-mutation reads.
    pub fn nodes(&self) -> Rc<ast::NodeArenaBuf> {
        self.nodes
            .as_ref()
            .expect("FlowState.nodes unset")
            .snapshot()
    }

    /// The owning file's `BindResult` (`flow_nodes`/`flow_lists` arenas).
    pub fn bind_result(
        &self,
    ) -> ast::ArenaRef<
        tsc_binder::binder::BindResult,
        impl for<'a> Fn(&'a Vec<ast::Node>) -> &'a tsc_binder::binder::BindResult,
    > {
        let file = self.file.expect("FlowState.file unset");
        ast::ArenaRef::new(self.nodes(), move |nodes| {
            tsc_binder::binder::bind_result(nodes, file).expect("flow graph without bind result")
        })
    }

    /// `flow.Flags`, `flow.Antecedent`, … — dereference a `FlowNodeId`.
    pub fn flow_node(
        &self,
        id: FlowNodeId,
    ) -> ast::ArenaRef<FlowNode, impl for<'a> Fn(&'a Vec<ast::Node>) -> &'a FlowNode> {
        let file = self.file.expect("FlowState.file unset");
        ast::ArenaRef::new(self.nodes(), move |nodes| {
            &tsc_binder::binder::bind_result(nodes, file)
                .expect("flow graph without bind result")
                .flow_nodes[id.index()]
        })
    }

    /// `list.Flow`, `list.Next` — dereference a `FlowListId`.
    pub fn flow_list(
        &self,
        id: FlowListId,
    ) -> ast::ArenaRef<ast::FlowList, impl for<'a> Fn(&'a Vec<ast::Node>) -> &'a ast::FlowList>
    {
        let file = self.file.expect("FlowState.file unset");
        ast::ArenaRef::new(self.nodes(), move |nodes| {
            &tsc_binder::binder::bind_result(nodes, file)
                .expect("flow graph without bind result")
                .flow_lists[id.index()]
        })
    }
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

    /// PORT(addition): attach the owning file context (`nodes`/`file`) to a
    /// `FlowState`. `context` is any `NodeId` in the file that owns the flow
    /// graph (the reference for type queries; the node the flow was taken
    /// from for reachability/post-super queries).
    fn set_flow_context(&self, f: &mut FlowState, context: NodeId) {
        if f.nodes.is_none() {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((context).file_index());
            f.file = ast::get_source_file_of_node(Some(context), &nodes);
            drop(nodes);
            f.nodes = Some(self.program_nodes_handle(context));
        }
    }
}

/// `getFlowNodeOfNode` (flow.go) — `node.FlowNodeData().FlowNode` → the
/// flow node attached to `node`, if any.
pub fn get_flow_node_of_node(nodes: &[tsc_ast::Node], node: NodeId) -> Option<FlowNodeId> {
    nodes[node].flow_node_data().and_then(|data| data.flow_node)
}

/// `getBranchLabelAntecedents` (flow.go).
fn get_branch_label_antecedents(f: &FlowState, flow: FlowNodeId) -> Option<FlowListId> {
    let mut i = f.reduce_labels.len();
    while i != 0 {
        i -= 1;
        // PORT(borrowck): snapshot the payload — `f.nodes()` is a temporary
        // `Ref` that cannot be borrowed into `let data`.
        let data = {
            let nodes = f.nodes();
            let d = nodes[f.reduce_labels[i]].as_flow_reduce_label_data();
            (d.target, d.antecedents)
        };
        if data.0 == Some(flow) {
            return data.1;
        }
    }
    f.flow_node(flow).antecedents
}

/// `*ast.FlowSwitchClauseData` — `Copy` snapshot of the generated payload
/// (`FlowSwitchClauseData` does not implement `Clone`; the three fields are
/// plain data). `clause_start`/`clause_end` stay `i32` like the payload.
#[derive(Clone, Copy, Default)]
pub struct SwitchClauseData {
    /// `switchStatement`.
    pub switch_statement: Option<NodeId>,
    /// `clauseStart`.
    pub clause_start: i32,
    /// `clauseEnd`.
    pub clause_end: i32,
}

impl SwitchClauseData {
    /// Snapshot `node.AsFlowSwitchClauseData()`.
    fn of(nodes: &[ast::Node], node: NodeId) -> SwitchClauseData {
        let data = nodes[node].as_flow_switch_clause_data();
        SwitchClauseData {
            switch_statement: data.switch_statement,
            clause_start: data.clause_start,
            clause_end: data.clause_end,
        }
    }

    /// `(data *FlowSwitchClauseData) IsEmpty`.
    fn is_empty(&self) -> bool {
        self.clause_start == self.clause_end
    }

    /// `data.ClauseStart`/`data.ClauseEnd` as slice indices.
    fn clause_start(&self) -> usize {
        self.clause_start as usize
    }
    fn clause_end(&self) -> usize {
        self.clause_end as usize
    }
}

impl Checker {
    /// `(c *Checker) getFlowTypeOfReference` (flow.go).
    pub(crate) fn get_flow_type_of_reference(
        &mut self,
        reference: NodeId,
        declared_type: TypeId,
    ) -> TypeId {
        self.get_flow_type_of_reference_ex(
            reference,
            declared_type,
            Some(declared_type),
            None,
            None,
        )
    }

    /// `(c *Checker) getFlowTypeOfReferenceEx` (flow.go).
    pub(crate) fn get_flow_type_of_reference_ex(
        &mut self,
        reference: NodeId,
        declared_type: TypeId,
        initial_type: Option<TypeId>,
        flow_container: Option<NodeId>,
        flow_node: Option<FlowNodeId>,
    ) -> TypeId {
        self.get_flow_type_of_reference_ex_ctx(
            reference,
            declared_type,
            initial_type,
            flow_container,
            flow_node,
            None,
        )
    }

    /// `getFlowTypeOfReferenceEx` with an explicit flow-graph file context.
    /// When the caller supplies a `flow_node` captured from a node in a
    /// different file than `reference` (e.g. `getNarrowedTypeOfSymbol`'s
    /// binding-pattern pseudo-reference), `flow_context` names a node in the
    /// file that owns the flow graph so `f.nodes` resolves the right arena.
    pub(crate) fn get_flow_type_of_reference_ex_ctx(
        &mut self,
        reference: NodeId,
        declared_type: TypeId,
        initial_type: Option<TypeId>,
        flow_container: Option<NodeId>,
        flow_node: Option<FlowNodeId>,
        flow_context: Option<NodeId>,
    ) -> TypeId {
        if self.flow_analysis_disabled {
            return self.error_type;
        }
        let mut flow_node = flow_node;
        if flow_node.is_none() {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((reference).file_index());
            flow_node = get_flow_node_of_node(&nodes, reference);
            if flow_node.is_none() {
                return declared_type;
            }
        }
        let flow_node = flow_node.unwrap();
        let mut f = self.get_flow_state();
        f.reference = Some(reference);
        f.declared_type = Some(declared_type);
        f.initial_type = Some(initial_type.unwrap_or(declared_type));
        f.flow_container = flow_container;
        f.shared_flow_start = self.shared_flows.len();
        self.set_flow_context(&mut f, flow_context.unwrap_or(reference));
        self.flow_invocation_count += 1;
        let evolved_type = self.get_type_at_flow_node(&mut f, flow_node).ty();
        self.shared_flows.truncate(f.shared_flow_start);
        let __arena_is_evolving = self.types.clone();
        let is_evolving = __arena_is_evolving
            .get(evolved_type)
            .object_flags
            .intersects(ObjectFlags::EVOLVING_ARRAY);
        // `reference` can be foreign to `f.nodes` (the flow-graph file) —
        // resolve it in its own arena.
        let nodes = self.program_nodes(reference);
        self.put_flow_state(f);
        // When the reference is 'x' in an 'x.length', 'x.push(value)', 'x.unshift(value)' or x[n] = value' operation,
        // we give type 'any[]' to 'x' instead of using the type determined by control flow analysis such that operations
        // on empty arrays are possible without implicit any errors and new element types can be inferred without
        // type mismatch errors.
        let result_type =
            if is_evolving && self.is_evolving_array_operation_target(&nodes, reference) {
                self.auto_array_type
            } else {
                self.finalize_evolving_array_type(evolved_type)
            };
        if result_type == self.unreachable_never_type
            || nodes[reference]
                .parent
                .is_some_and(|p| ast::is_non_null_expression(&nodes[p]))
                && !self
                    .types_handle()
                    .get(result_type)
                    .flags
                    .intersects(TypeFlags::NEVER)
                && {
                    let ft = self.get_type_with_facts(result_type, TypeFacts::NE_UNDEFINED_OR_NULL);
                    self.types_handle()
                        .get(ft)
                        .flags
                        .intersects(TypeFlags::NEVER)
                }
        {
            return declared_type;
        }
        result_type
    }

    /// `(c *Checker) getTypeAtFlowNode` (flow.go).
    pub(crate) fn get_type_at_flow_node(
        &mut self,
        f: &mut FlowState,
        flow: FlowNodeId,
    ) -> FlowType {
        let mut flow = flow;
        if f.depth == 2000 {
            // We have made 2000 recursive invocations. To avoid overflowing the call stack we report an error
            // and disable further control flow analysis in the containing function or module body.
            if let Some(tr) = &self.tracer {
                tr.instant(
                    tsc_tracing::PHASE_CHECK_TYPES,
                    "getTypeAtFlowNode_DepthLimit",
                    &tsc_tracing::trace_args(&[("depth", f.depth.into())]),
                );
            }
            self.flow_analysis_disabled = true;
            self.report_flow_control_error(f.reference());
            return FlowType {
                t: Some(self.error_type),
                incomplete: false,
            };
        }
        f.depth += 1;
        let mut shared_flow: Option<FlowNodeId> = None;
        loop {
            let flags = f.flow_node(flow).flags;
            if flags.intersects(FlowFlags::SHARED) {
                // We cache results of flow type resolution for shared nodes that were previously visited in
                // the same getFlowTypeOfReference invocation. A node is considered shared when it is the
                // antecedent of more than one node.
                let mut found: Option<FlowType> = None;
                for i in f.shared_flow_start..self.shared_flows.len() {
                    if self.shared_flows[i].flow == flow {
                        found = Some(self.shared_flows[i].flow_type);
                        break;
                    }
                }
                if let Some(found) = found {
                    f.depth -= 1;
                    return found;
                }
                shared_flow = Some(flow);
            }
            let t: FlowType;
            if flags.intersects(FlowFlags::ASSIGNMENT) {
                t = self.get_type_at_flow_assignment(f, flow);
                if t.is_nil() {
                    flow = f.flow_node(flow).antecedent.unwrap();
                    continue;
                }
            } else if flags.intersects(FlowFlags::CALL) {
                t = self.get_type_at_flow_call(f, flow);
                if t.is_nil() {
                    flow = f.flow_node(flow).antecedent.unwrap();
                    continue;
                }
            } else if flags.intersects(FlowFlags::CONDITION) {
                t = self.get_type_at_flow_condition(f, flow);
            } else if flags.intersects(FlowFlags::SWITCH_CLAUSE) {
                t = self.get_type_at_switch_clause(f, flow);
            } else if flags.intersects(FlowFlags::BRANCH_LABEL) {
                let antecedents = get_branch_label_antecedents(f, flow);
                if antecedents.and_then(|a| f.flow_list(a).next).is_none() {
                    flow = antecedents
                        .and_then(|a| f.flow_list(a).flow)
                        .expect("branch-label antecedent flow (Go: antecedents.Flow)");
                    continue;
                }
                t = self.get_type_at_flow_branch_label(f, flow, antecedents);
            } else if flags.intersects(FlowFlags::LOOP_LABEL) {
                let antecedents = f.flow_node(flow).antecedents;
                if antecedents.and_then(|a| f.flow_list(a).next).is_none() {
                    flow = antecedents.and_then(|a| f.flow_list(a).flow).unwrap();
                    continue;
                }
                t = self.get_type_at_flow_loop_label(f, flow);
            } else if flags.intersects(FlowFlags::ARRAY_MUTATION) {
                t = self.get_type_at_flow_array_mutation(f, flow);
                if t.is_nil() {
                    flow = f.flow_node(flow).antecedent.unwrap();
                    continue;
                }
            } else if flags.intersects(FlowFlags::REDUCE_LABEL) {
                let node = f.flow_node(flow).node.expect("reduce label node");
                f.reduce_labels.push(node);
                let antecedent = f.flow_node(flow).antecedent.unwrap();
                t = self.get_type_at_flow_node(f, antecedent);
                f.reduce_labels.pop();
            } else if flags.intersects(FlowFlags::START) {
                // Check if we should continue with the control flow of the containing function.
                let container = f.flow_node(flow).node;
                // `f.reference` can be foreign to the flow-graph arena —
                // resolve it in its own arena.
                let ref_nodes = self.program_nodes(f.reference());
                if container.is_some()
                    && container != f.flow_container
                    && !ast::is_property_access_expression(&ref_nodes[f.reference()])
                    && !ast::is_element_access_expression(&ref_nodes[f.reference()])
                    && !(ref_nodes[f.reference()].kind == Kind::ThisKeyword
                        && !ast::is_arrow_function(&f.nodes()[container.unwrap()]))
                {
                    flow = f.nodes()[container.unwrap()]
                        .flow_node_data()
                        .and_then(|d| d.flow_node)
                        .expect("container without flow node");
                    continue;
                }
                // At the top of the flow we have the initial type.
                t = FlowType {
                    t: f.initial_type,
                    incomplete: false,
                };
            } else {
                // Unreachable code errors are reported in the binding phase. Here we
                // simply return the non-auto declared type to reduce follow-on errors.
                t = FlowType {
                    t: Some(self.convert_auto_to_any(f.declared_type())),
                    incomplete: false,
                };
            }
            if let Some(shared_flow) = shared_flow {
                // Record visited node and the associated type in the cache.
                self.shared_flows.push(SharedFlow {
                    flow: shared_flow,
                    flow_type: t,
                });
            }
            f.depth -= 1;
            return t;
        }
    }

    /// `(c *Checker) getTypeAtFlowAssignment` (flow.go).
    pub(crate) fn get_type_at_flow_assignment(
        &mut self,
        f: &mut FlowState,
        flow: FlowNodeId,
    ) -> FlowType {
        let node = f.flow_node(flow).node.expect("assignment flow node");
        // Assignments only narrow the computed type if the declared type is a union type. Thus, we
        // only need to evaluate the assigned type if the declared type is a union type.
        if self.is_matching_reference(&f.nodes(), f.reference(), node) {
            // The flow graph lives in `f.file`'s arena — `f.reference` can
            // be a foreign pseudo-reference.
            if !self.is_reachable_flow_node(f.file.expect("FlowState.file unset"), flow) {
                return FlowType {
                    t: Some(self.unreachable_never_type),
                    incomplete: false,
                };
            }
            if crate::utilities::get_assignment_target_kind(node, &f.nodes())
                == crate::utilities::AssignmentKind::COMPOUND
            {
                let antecedent = f.flow_node(flow).antecedent.unwrap();
                let flow_type = self.get_type_at_flow_node(f, antecedent);
                let base = self.get_base_type_of_literal_type(flow_type.ty());
                return new_flow_type(self, base, flow_type.incomplete);
            }
            if f.declared_type() == self.auto_type || f.declared_type() == self.auto_array_type {
                if self.is_empty_array_assignment(&f.nodes(), node) {
                    let evolving = self.get_evolving_array_type(self.never_type);
                    return FlowType {
                        t: Some(evolving),
                        incomplete: false,
                    };
                }
                let __h520_51 = self.get_initial_or_assigned_type(f, flow);

                let assigned_type = self.get_widened_literal_type(__h520_51);
                if self.is_type_assignable_to(assigned_type, f.declared_type()) {
                    return FlowType {
                        t: Some(assigned_type),
                        incomplete: false,
                    };
                }
                return FlowType {
                    t: Some(self.any_array_type),
                    incomplete: false,
                };
            }
            let mut t = f.declared_type();
            if crate::utilities::is_in_compound_like_assignment(node, &f.nodes()) {
                t = self.get_base_type_of_literal_type(t);
            }
            if self
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::UNION)
            {
                let assigned_type = self.get_initial_or_assigned_type(f, flow);
                return FlowType {
                    t: Some(self.get_assignment_reduced_type(t, assigned_type)),
                    incomplete: false,
                };
            }
            return FlowType {
                t: Some(t),
                incomplete: false,
            };
        }
        // We didn't have a direct match. However, if the reference is a dotted name, this
        // may be an assignment to a left hand part of the reference. For example, for a
        // reference 'x.y.z', we may be at an assignment to 'x.y' or 'x'. In that case,
        // return the declared type.
        if self.contains_matching_reference(&f.nodes(), f.reference(), node) {
            if !self.is_reachable_flow_node(f.file.expect("FlowState.file unset"), flow) {
                return FlowType {
                    t: Some(self.unreachable_never_type),
                    incomplete: false,
                };
            }
            // A matching dotted name might also be an expando property on a function *expression*,
            // in which case we continue control flow analysis back to the function's declaration
            // PORT(borrowck): extract the condition so `f.nodes()` `Ref`
            // temporaries die before the `&mut f` uses inside the block.
            let is_decl_in_js = ast::is_variable_declaration(&f.nodes()[node])
                && (ast::is_in_js_file(Some(node), &f.nodes())
                    || ast::is_var_const_like(node, &f.nodes()));
            if is_decl_in_js {
                let init = { f.nodes()[node].initializer() };
                if let Some(init) = init {
                    if ast::is_function_expression_or_arrow_function(&f.nodes()[init]) {
                        let antecedent = f.flow_node(flow).antecedent.unwrap();
                        return self.get_type_at_flow_node(f, antecedent);
                    }
                }
            }
            return FlowType {
                t: Some(f.declared_type()),
                incomplete: false,
            };
        }
        // for (const _ in ref) acts as a nonnull on ref
        if ast::is_variable_declaration(&f.nodes()[node])
            && f.nodes()[node].parent.is_some_and(|p| {
                f.nodes()[p]
                    .parent
                    .is_some_and(|pp| ast::is_for_in_statement(&f.nodes()[pp]))
            })
        {
            let for_in = f.nodes()[f.nodes()[node].parent.unwrap()].parent.unwrap();
            if self.is_matching_reference(
                &f.nodes(),
                f.reference(),
                f.nodes()[for_in].expression().unwrap(),
            ) || self.optional_chain_contains_reference(
                &f.nodes(),
                f.nodes()[for_in].expression().unwrap(),
                f.reference(),
            ) {
                let antecedent = f.flow_node(flow).antecedent.unwrap();
                let at = self.get_type_at_flow_node(f, antecedent).ty();
                let t = self.finalize_evolving_array_type(at);
                return FlowType {
                    t: Some(self.get_non_nullable_type_if_needed(t)),
                    incomplete: false,
                };
            }
        }
        // Assignment doesn't affect reference
        FlowType::none()
    }

    /// `(c *Checker) getInitialOrAssignedType` (flow.go).
    pub(crate) fn get_initial_or_assigned_type(
        &mut self,
        f: &mut FlowState,
        flow: FlowNodeId,
    ) -> TypeId {
        let node = f.flow_node(flow).node.expect("flow node without node");
        if ast::is_variable_declaration(&f.nodes()[node])
            || ast::is_binding_element(&f.nodes()[node])
        {
            let initial = self.get_initial_type(node);
            self.get_narrowable_type_for_reference(initial, f.reference(), CheckMode::NORMAL)
        } else {
            let assigned = self.get_assigned_type(node);
            self.get_narrowable_type_for_reference(assigned, f.reference(), CheckMode::NORMAL)
        }
    }

    /// `(c *Checker) isEmptyArrayAssignment` (flow.go).
    pub(crate) fn is_empty_array_assignment(&self, nodes: &[ast::Node], node: NodeId) -> bool {
        (ast::is_variable_declaration(&nodes[node])
            && nodes[node]
                .initializer()
                .is_some_and(|i| crate::utilities::is_empty_array_literal(&nodes[i])))
            || (!ast::is_binding_element(&nodes[node])
                && nodes[node].parent.is_some_and(|p| {
                    ast::is_binary_expression(&nodes[p])
                        && crate::utilities::is_empty_array_literal(
                            &nodes[nodes[p].as_binary_expression().right.unwrap()],
                        )
                }))
    }

    /// `(c *Checker) getTypeAtFlowCall` (flow.go).
    pub(crate) fn get_type_at_flow_call(
        &mut self,
        f: &mut FlowState,
        flow: FlowNodeId,
    ) -> FlowType {
        let node = f.flow_node(flow).node.expect("call flow node");
        if let Some(signature) = self.get_effects_signature(node) {
            let predicate = self.get_type_predicate_of_signature(signature);
            if let Some(predicate) = &predicate {
                if predicate.kind == TypePredicateKind::AssertsThis
                    || predicate.kind == TypePredicateKind::AssertsIdentifier
                {
                    let antecedent = f.flow_node(flow).antecedent.unwrap();
                    let flow_type = self.get_type_at_flow_node(f, antecedent);
                    let t = self.finalize_evolving_array_type(flow_type.ty());
                    let narrowed_type;
                    if predicate.t.is_some() {
                        let predicate = predicate.clone();
                        narrowed_type =
                            self.narrow_type_by_type_predicate(f, t, &predicate, node, true);
                    } else if predicate.kind == TypePredicateKind::AssertsIdentifier
                        && predicate.parameter_index >= 0
                        && (predicate.parameter_index as usize)
                            < f.nodes()[node].arguments().map_or(0, |a| a.len())
                    {
                        let arg = f.nodes()[node].arguments().unwrap()
                            [predicate.parameter_index as usize];
                        narrowed_type = self.narrow_type_by_assertion(f, t, arg);
                    } else {
                        narrowed_type = t;
                    }
                    if narrowed_type == t {
                        return flow_type;
                    }
                    return new_flow_type(self, narrowed_type, flow_type.incomplete);
                }
            }
            let rt = self.get_return_type_of_signature(signature);
            if self
                .types_handle()
                .get(rt)
                .flags
                .intersects(TypeFlags::NEVER)
            {
                return FlowType {
                    t: Some(self.unreachable_never_type),
                    incomplete: false,
                };
            }
        }
        FlowType::none()
    }

    /// `(c *Checker) narrowTypeByTypePredicate` (flow.go).
    pub(crate) fn narrow_type_by_type_predicate(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        predicate: &TypePredicate,
        call_expression: NodeId,
        assume_true: bool,
    ) -> TypeId {
        let mut t = t;
        // Don't narrow from 'any' if the predicate type is exactly 'Object' or 'Function'
        if let Some(predicate_type) = predicate.t {
            if !(crate::utilities::is_type_any(&self.types, t)
                && (predicate_type == self.global_object_type
                    || predicate_type == self.global_function_type))
            {
                // PORT(borrowck): extract the scrutinee — the `f.nodes()`
                // `Ref` temporary would otherwise pin `*f` across the block's
                // `&mut f` calls.
                let predicate_argument =
                    self.get_type_predicate_argument(&f.nodes(), predicate, call_expression);
                if let Some(predicate_argument) = predicate_argument {
                    if self.is_matching_reference(&f.nodes(), f.reference(), predicate_argument) {
                        return self.get_narrowed_type(t, predicate_type, assume_true, false);
                    }
                    if self.strict_null_checks
                        && self.optional_chain_contains_reference(
                            &f.nodes(),
                            predicate_argument,
                            f.reference(),
                        )
                        && (assume_true
                            && !self.has_type_facts(predicate_type, TypeFacts::EQ_UNDEFINED)
                            || !assume_true
                                && crate::checker_d::every_type(
                                    self,
                                    predicate_type,
                                    |c: &mut Checker, t: TypeId| c.is_nullable_type(t),
                                ))
                    {
                        t = self.get_adjusted_type_with_facts(t, TypeFacts::NE_UNDEFINED_OR_NULL);
                    }
                    if let Some(access) =
                        self.get_discriminant_property_access(f, predicate_argument, t)
                    {
                        let __nodes_arena = f.nodes.clone().unwrap();
                        let nodes = __nodes_arena.snapshot();
                        return self.narrow_type_by_discriminant(
                            t,
                            access,
                            &nodes,
                            &mut |c: &mut Checker, t: TypeId| {
                                c.get_narrowed_type(t, predicate_type, assume_true, false)
                            },
                        );
                    }
                }
            }
        }
        t
    }

    /// `(c *Checker) narrowTypeByAssertion` (flow.go).
    pub(crate) fn narrow_type_by_assertion(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        expr: NodeId,
    ) -> TypeId {
        let node = ast::skip_parentheses(expr, &f.nodes());
        if { f.nodes()[node].kind } == Kind::FalseKeyword {
            return self.unreachable_never_type;
        }
        if { f.nodes()[node].kind } == Kind::BinaryExpression {
            // PORT(borrowck): hold one `Ref` — `f.nodes()` temporaries can't
            // be borrowed into locals.
            let (operator, left, right) = {
                let nodes = f.nodes();
                let e = nodes[node].as_binary_expression();
                (e.operator_token, e.left.unwrap(), e.right.unwrap())
            };
            let operator_kind = { f.nodes()[operator.unwrap()].kind };
            if operator_kind == Kind::AmpersandAmpersandToken {
                let t = self.narrow_type_by_assertion(f, t, left);
                return self.narrow_type_by_assertion(f, t, right);
            }
            if operator_kind == Kind::BarBarToken {
                let l = self.narrow_type_by_assertion(f, t, left);
                let r = self.narrow_type_by_assertion(f, t, right);
                return self.get_union_type(&[l, r]);
            }
        }
        self.narrow_type(f, t, node, true)
    }

    /// `(c *Checker) getTypeAtFlowCondition` (flow.go).
    pub(crate) fn get_type_at_flow_condition(
        &mut self,
        f: &mut FlowState,
        flow: FlowNodeId,
    ) -> FlowType {
        let antecedent = f.flow_node(flow).antecedent.unwrap();
        let flow_type = self.get_type_at_flow_node(f, antecedent);
        if self
            .types_handle()
            .get(flow_type.ty())
            .flags
            .intersects(TypeFlags::NEVER)
        {
            return flow_type;
        }
        // If we have an antecedent type (meaning we're reachable in some way), we first
        // attempt to narrow the antecedent type. If that produces the never type, and if
        // the antecedent type is incomplete (i.e. a transient type in a loop), then we
        // take the type guard as an indication that control *could* reach here once we
        // have the complete type. We proceed by switching to the silent never type which
        // doesn't report errors when operators are applied to it. Note that this is the
        // *only* place a silent never type is ever generated.
        let assume_true = f
            .flow_node(flow)
            .flags
            .intersects(FlowFlags::TRUE_CONDITION);
        let non_evolving_type = self.finalize_evolving_array_type(flow_type.ty());
        let node = f.flow_node(flow).node.expect("condition flow node");
        let narrowed_type = self.narrow_type(f, non_evolving_type, node, assume_true);
        if narrowed_type == non_evolving_type {
            return flow_type;
        }
        new_flow_type(self, narrowed_type, flow_type.incomplete)
    }

    /// `(c *Checker) narrowType` (flow.go) — narrow the given type based on
    /// the given expression having the assumed boolean value. The returned
    /// type will be a subtype or the same type as the argument.
    pub(crate) fn narrow_type(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        expr: NodeId,
        assume_true: bool,
    ) -> TypeId {
        // for `a?.b`, we emulate a synthetic `a !== null && a !== undefined` condition for `a`
        let is_question_question_left = {
            // PORT(borrowck): hold one `Ref` for the whole computation —
            // `f.nodes()` temporaries cannot be borrowed across statements.
            let nodes = f.nodes();
            nodes[expr].parent.is_some_and(|p| {
                ast::is_binary_expression(&nodes[p]) && {
                    let e = nodes[p].as_binary_expression();
                    let op = nodes[e.operator_token.unwrap()].kind;
                    (op == Kind::QuestionQuestionToken || op == Kind::QuestionQuestionEqualsToken)
                        && e.left == Some(expr)
                }
            })
        };
        if ast::is_expression_of_optional_chain_root(expr, &f.nodes()) || is_question_question_left
        {
            return self.narrow_type_by_optionality(f, t, expr, assume_true);
        }
        match { f.nodes()[expr].kind } {
            Kind::Identifier => {
                // When narrowing a reference to a const variable, non-assigned parameter, or readonly property, we inline
                // up to five levels of aliased conditional expressions that are themselves declared as const variables.
                if !self.is_matching_reference(&f.nodes(), f.reference(), expr)
                    && self.inline_level < 5
                {
                    let symbol = self.get_resolved_symbol(expr);
                    if self.is_constant_variable(symbol) {
                        let declaration =
                            self.symbol_arena.get_ref(symbol).value_declaration;
                        if let Some(declaration) = declaration {
                            // `declaration` can be foreign to the flow-graph
                            // arena — resolve it in its own arena.
                            let decl_nodes = self.program_nodes(declaration);
                            if ast::is_variable_declaration(&decl_nodes[declaration])
                                && decl_nodes[declaration].type_().is_none()
                                && decl_nodes[declaration].initializer().is_some()
                                && self.is_constant_reference(&f.nodes(), f.reference())
                            {
                                self.inline_level += 1;
                                let initializer = decl_nodes[declaration].initializer().unwrap();
                                let result = self.narrow_type(f, t, initializer, assume_true);
                                self.inline_level -= 1;
                                return result;
                            }
                        }
                    }
                }
                self.narrow_type_by_truthiness(f, t, expr, assume_true)
            }
            Kind::ThisKeyword
            | Kind::SuperKeyword
            | Kind::PropertyAccessExpression
            | Kind::ElementAccessExpression => {
                self.narrow_type_by_truthiness(f, t, expr, assume_true)
            }
            Kind::CallExpression => self.narrow_type_by_call_expression(f, t, expr, assume_true),
            Kind::ParenthesizedExpression | Kind::NonNullExpression | Kind::SatisfiesExpression => {
                let inner = f.nodes()[expr].expression().unwrap();
                self.narrow_type(f, t, inner, assume_true)
            }
            Kind::BinaryExpression => {
                self.narrow_type_by_binary_expression(f, t, expr, assume_true)
            }
            Kind::PrefixUnaryExpression => {
                let (operator, operand) = {
                    let nodes = f.nodes();
                    let e = nodes[expr].as_prefix_unary_expression();
                    (e.operator, e.operand)
                };
                if operator == Kind::ExclamationToken {
                    let operand = operand.unwrap();
                    self.narrow_type(f, t, operand, !assume_true)
                } else {
                    t
                }
            }
            _ => t,
        }
    }

    /// `(c *Checker) narrowTypeByOptionality` (flow.go).
    pub(crate) fn narrow_type_by_optionality(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        expr: NodeId,
        assume_present: bool,
    ) -> TypeId {
        if self.is_matching_reference(&f.nodes(), f.reference(), expr) {
            return self.get_adjusted_type_with_facts(
                t,
                tsc_core::core::if_else(
                    assume_present,
                    TypeFacts::NE_UNDEFINED_OR_NULL,
                    TypeFacts::EQ_UNDEFINED_OR_NULL,
                ),
            );
        }
        if let Some(access) = self.get_discriminant_property_access(f, expr, t) {
            let __nodes_arena = f.nodes.clone().unwrap();
            let nodes = __nodes_arena.snapshot();
            return self.narrow_type_by_discriminant(
                t,
                access,
                &nodes,
                &mut |c: &mut Checker, t: TypeId| {
                    c.get_type_with_facts(
                        t,
                        tsc_core::core::if_else(
                            assume_present,
                            TypeFacts::NE_UNDEFINED_OR_NULL,
                            TypeFacts::EQ_UNDEFINED_OR_NULL,
                        ),
                    )
                },
            );
        }
        t
    }

    /// `(c *Checker) narrowTypeByTruthiness` (flow.go).
    pub(crate) fn narrow_type_by_truthiness(
        &mut self,
        f: &mut FlowState,
        mut t: TypeId,
        expr: NodeId,
        assume_true: bool,
    ) -> TypeId {
        if self.is_matching_reference(&f.nodes(), f.reference(), expr) {
            return self.get_adjusted_type_with_facts(
                t,
                tsc_core::core::if_else(assume_true, TypeFacts::TRUTHY, TypeFacts::FALSY),
            );
        }
        if self.strict_null_checks
            && assume_true
            && self.optional_chain_contains_reference(&f.nodes(), expr, f.reference())
        {
            t = self.get_adjusted_type_with_facts(t, TypeFacts::NE_UNDEFINED_OR_NULL);
        }
        if let Some(access) = self.get_discriminant_property_access(f, expr, t) {
            let __nodes_arena = f.nodes.clone().unwrap();
            let nodes = __nodes_arena.snapshot();
            return self.narrow_type_by_discriminant(
                t,
                access,
                &nodes,
                &mut |c: &mut Checker, t: TypeId| {
                    c.get_type_with_facts(
                        t,
                        tsc_core::core::if_else(assume_true, TypeFacts::TRUTHY, TypeFacts::FALSY),
                    )
                },
            );
        }
        t
    }

    /// `(c *Checker) narrowTypeByCallExpression` (flow.go).
    pub(crate) fn narrow_type_by_call_expression(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        call_expression: NodeId,
        assume_true: bool,
    ) -> TypeId {
        if self.has_matching_argument(&f.nodes(), call_expression, f.reference()) {
            let mut predicate: Option<TypePredicate> = None;
            if assume_true || !crate::utilities::is_call_chain(&f.nodes()[call_expression]) {
                if let Some(signature) = self.get_effects_signature(call_expression) {
                    predicate = self.get_type_predicate_of_signature(signature);
                }
            }
            if let Some(predicate) = &predicate {
                if predicate.kind == TypePredicateKind::This
                    || predicate.kind == TypePredicateKind::Identifier
                {
                    let predicate = predicate.clone();
                    return self.narrow_type_by_type_predicate(
                        f,
                        t,
                        &predicate,
                        call_expression,
                        assume_true,
                    );
                }
            }
        }
        let contains_missing = self.contains_missing_type.clone();
        // `f.reference` can be foreign to the flow-graph arena — resolve it
        // in its own arena.
        let ref_nodes = self.program_nodes(f.reference());
        if contains_missing.is_some_and(|f2| f2(self, t))
            && ast::is_access_expression(&ref_nodes[f.reference()])
            && ast::is_property_access_expression(
                &f.nodes()[f.nodes()[call_expression].expression().unwrap()],
            )
        {
            let call_access = f.nodes()[call_expression].expression().unwrap();
            let candidate = self
                .get_reference_candidate(&f.nodes(), f.nodes()[call_access].expression().unwrap());
            if self.is_matching_reference(
                ref_nodes.as_slice(),
                ref_nodes[f.reference()].expression().unwrap(),
                candidate,
            ) && ast::is_identifier(&f.nodes()[f.nodes()[call_access].name().unwrap()])
                && f.nodes()[f.nodes()[call_access].name().unwrap()].text(&f.nodes())
                    == "hasOwnProperty"
                && f.nodes()[call_expression]
                    .arguments()
                    .map_or(0, |a| a.len())
                    == 1
            {
                let argument = f.nodes()[call_expression].arguments().unwrap()[0];
                let (accessed_name, ok) =
                    self.get_accessed_property_name(ref_nodes.as_slice(), f.reference());
                if ok
                    && ast::is_string_literal_like(&f.nodes()[argument])
                    && accessed_name == f.nodes()[argument].text(&f.nodes())
                {
                    return self.get_type_with_facts(
                        t,
                        tsc_core::core::if_else(
                            assume_true,
                            TypeFacts::NE_UNDEFINED,
                            TypeFacts::EQ_UNDEFINED,
                        ),
                    );
                }
            }
        }
        t
    }

    /// `(c *Checker) narrowTypeByBinaryExpression` (flow.go).
    pub(crate) fn narrow_type_by_binary_expression(
        &mut self,
        f: &mut FlowState,
        mut t: TypeId,
        expr: NodeId,
        assume_true: bool,
    ) -> TypeId {
        let (left_e, operator, right_e) = {
            let nodes = f.nodes();
            let e = nodes[expr].as_binary_expression();
            (e.left, e.operator_token, e.right)
        };
        match { f.nodes()[operator.unwrap()].kind } {
            Kind::EqualsToken
            | Kind::BarBarEqualsToken
            | Kind::AmpersandAmpersandEqualsToken
            | Kind::QuestionQuestionEqualsToken => {
                let t = self.narrow_type(f, t, right_e.unwrap(), assume_true);
                self.narrow_type_by_truthiness(f, t, left_e.unwrap(), assume_true)
            }
            Kind::EqualsEqualsToken
            | Kind::ExclamationEqualsToken
            | Kind::EqualsEqualsEqualsToken
            | Kind::ExclamationEqualsEqualsToken => {
                let operator = f.nodes()[operator.unwrap()].kind;
                let left = self.get_reference_candidate(&f.nodes(), left_e.unwrap());
                let right = self.get_reference_candidate(&f.nodes(), right_e.unwrap());
                if f.nodes()[left].kind == Kind::TypeOfExpression
                    && ast::is_string_literal_like(&f.nodes()[right])
                {
                    return self.narrow_type_by_typeof(f, t, left, operator, right, assume_true);
                }
                if f.nodes()[right].kind == Kind::TypeOfExpression
                    && ast::is_string_literal_like(&f.nodes()[left])
                {
                    return self.narrow_type_by_typeof(f, t, right, operator, left, assume_true);
                }
                if self.is_matching_reference(&f.nodes(), f.reference(), left) {
                    return self.narrow_type_by_equality(t, operator, right, assume_true);
                }
                if self.is_matching_reference(&f.nodes(), f.reference(), right) {
                    return self.narrow_type_by_equality(t, operator, left, assume_true);
                }
                if self.strict_null_checks {
                    if self.optional_chain_contains_reference(&f.nodes(), left, f.reference()) {
                        t = self.narrow_type_by_optional_chain_containment(
                            f,
                            t,
                            operator,
                            right,
                            assume_true,
                        );
                    } else if self.optional_chain_contains_reference(
                        &f.nodes(),
                        right,
                        f.reference(),
                    ) {
                        t = self.narrow_type_by_optional_chain_containment(
                            f,
                            t,
                            operator,
                            left,
                            assume_true,
                        );
                    }
                }
                if let Some(left_access) = self.get_discriminant_property_access(f, left, t) {
                    return self.narrow_type_by_discriminant_property(
                        t,
                        left_access,
                        operator,
                        right,
                        assume_true,
                        &f.nodes(),
                    );
                }
                if let Some(right_access) = self.get_discriminant_property_access(f, right, t) {
                    return self.narrow_type_by_discriminant_property(
                        t,
                        right_access,
                        operator,
                        left,
                        assume_true,
                        &f.nodes(),
                    );
                }
                if self.is_matching_constructor_reference(f, left) {
                    return self.narrow_type_by_constructor(t, operator, right, assume_true);
                }
                if self.is_matching_constructor_reference(f, right) {
                    return self.narrow_type_by_constructor(t, operator, left, assume_true);
                }
                if ast::is_boolean_literal(&f.nodes()[right])
                    && !ast::is_access_expression(&f.nodes()[left])
                {
                    return self.narrow_type_by_boolean_comparison(
                        f,
                        t,
                        left,
                        right,
                        operator,
                        assume_true,
                    );
                }
                if ast::is_boolean_literal(&f.nodes()[left])
                    && !ast::is_access_expression(&f.nodes()[right])
                {
                    return self.narrow_type_by_boolean_comparison(
                        f,
                        t,
                        right,
                        left,
                        operator,
                        assume_true,
                    );
                }
                t
            }
            Kind::InstanceOfKeyword => self.narrow_type_by_instanceof(f, t, expr, assume_true),
            Kind::InKeyword => {
                if ast::is_private_identifier(&f.nodes()[left_e.unwrap()]) {
                    return self.narrow_type_by_private_identifier_in_in_expression(
                        f,
                        t,
                        expr,
                        assume_true,
                    );
                }
                let target = self.get_reference_candidate(&f.nodes(), right_e.unwrap());
                let contains_missing = self.contains_missing_type.clone();
                // `f.reference` can be foreign to the flow-graph arena —
                // resolve it in its own arena.
                let ref_nodes = self.program_nodes(f.reference());
                if contains_missing.is_some_and(|f2| f2(self, t))
                    && ast::is_access_expression(&ref_nodes[f.reference()])
                    && self.is_matching_reference(
                        ref_nodes.as_slice(),
                        ref_nodes[f.reference()].expression().unwrap(),
                        target,
                    )
                {
                    let left_type = self.get_type_of_expression(left_e.unwrap());
                    if crate::utilities::is_type_usable_as_property_name(&self.types, left_type) {
                        let (accessed_name, ok) =
                            self.get_accessed_property_name(ref_nodes.as_slice(), f.reference());
                        if ok
                            && accessed_name
                                == crate::utilities::get_property_name_from_type(
                                    &self.types,
                                    left_type,
                                )
                        {
                            return self.get_type_with_facts(
                                t,
                                tsc_core::core::if_else(
                                    assume_true,
                                    TypeFacts::NE_UNDEFINED,
                                    TypeFacts::EQ_UNDEFINED,
                                ),
                            );
                        }
                    }
                }
                if self.is_matching_reference(&f.nodes(), f.reference(), target) {
                    let left_type = self.get_type_of_expression(left_e.unwrap());
                    if crate::utilities::is_type_usable_as_property_name(&self.types, left_type) {
                        return self.narrow_type_by_in_keyword(f, t, left_type, assume_true);
                    }
                }
                t
            }
            Kind::CommaToken => self.narrow_type(f, t, right_e.unwrap(), assume_true),
            Kind::AmpersandAmpersandToken => {
                // Ordinarily we won't see && and || expressions in control flow analysis because the Binder breaks those
                // expressions down to individual conditional control flows. However, we may encounter them when analyzing
                // aliased conditional expressions.
                if assume_true {
                    let t = self.narrow_type(f, t, left_e.unwrap(), true);
                    return self.narrow_type(f, t, right_e.unwrap(), true);
                }
                let l = self.narrow_type(f, t, left_e.unwrap(), false);
                let r = self.narrow_type(f, t, right_e.unwrap(), false);
                self.get_union_type(&[l, r])
            }
            Kind::BarBarToken => {
                if assume_true {
                    let l = self.narrow_type(f, t, left_e.unwrap(), true);
                    let r = self.narrow_type(f, t, right_e.unwrap(), true);
                    return self.get_union_type(&[l, r]);
                }
                let t = self.narrow_type(f, t, left_e.unwrap(), false);
                self.narrow_type(f, t, right_e.unwrap(), false)
            }
            _ => t,
        }
    }
}
impl Checker {
    /// `(c *Checker) narrowTypeByEquality` (flow.go).
    pub(crate) fn narrow_type_by_equality(
        &mut self,
        t: TypeId,
        operator: Kind,
        value: NodeId,
        assume_true: bool,
    ) -> TypeId {
        if self.types_handle().get(t).flags.intersects(TypeFlags::ANY) {
            return t;
        }
        let mut assume_true = assume_true;
        if operator == Kind::ExclamationEqualsToken
            || operator == Kind::ExclamationEqualsEqualsToken
        {
            assume_true = !assume_true;
        }
        let value_type = self.get_type_of_expression(value);
        let double_equals =
            operator == Kind::EqualsEqualsToken || operator == Kind::ExclamationEqualsToken;
        if self
            .types_handle()
            .get(value_type)
            .flags
            .intersects(TypeFlags::NULLABLE)
        {
            if !self.strict_null_checks {
                return t;
            }
            let facts = if double_equals {
                tsc_core::core::if_else(
                    assume_true,
                    TypeFacts::EQ_UNDEFINED_OR_NULL,
                    TypeFacts::NE_UNDEFINED_OR_NULL,
                )
            } else if self
                .types_handle()
                .get(value_type)
                .flags
                .intersects(TypeFlags::NULL)
            {
                tsc_core::core::if_else(assume_true, TypeFacts::EQ_NULL, TypeFacts::NE_NULL)
            } else {
                tsc_core::core::if_else(
                    assume_true,
                    TypeFacts::EQ_UNDEFINED,
                    TypeFacts::NE_UNDEFINED,
                )
            };
            return self.get_adjusted_type_with_facts(t, facts);
        }
        if assume_true {
            if !double_equals
                && (self
                    .types_handle()
                    .get(t)
                    .flags
                    .intersects(TypeFlags::UNKNOWN)
                    || crate::checker_d::some_type(self, t, |c: &mut Checker, t: TypeId| {
                        c.is_empty_anonymous_object_type(t)
                    }))
            {
                if self
                    .types_handle()
                    .get(value_type)
                    .flags
                    .intersects(TypeFlags::PRIMITIVE | TypeFlags::NON_PRIMITIVE)
                    || self.is_empty_anonymous_object_type(value_type)
                {
                    return value_type;
                }
                if self
                    .types_handle()
                    .get(value_type)
                    .flags
                    .intersects(TypeFlags::OBJECT)
                {
                    return self.non_primitive_type;
                }
            }
            if !double_equals
                && self
                    .types_handle()
                    .get(value_type)
                    .flags
                    .intersects(TypeFlags::PRIMITIVE)
                && self.is_uniform_union_type(t)
            {
                let regular_type = self.get_regular_type_of_literal_type(value_type);
                if self.union_contains_type(t, regular_type, false) {
                    return regular_type;
                }
            }
            let filtered_type = self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
                c.are_types_comparable(t, value_type)
                    || double_equals && is_coercible_under_double_equals(&c.types, t, value_type)
            });
            return self.replace_primitives_with_literals(filtered_type, value_type);
        }
        if crate::checker_d::is_unit_type(&self.types, value_type) {
            if self.is_uniform_union_type(t) {
                let regular = self.get_regular_type_of_literal_type(value_type);
                let filtered_type = self.remove_type(t, regular);
                if filtered_type != t {
                    return filtered_type;
                }
            }
            return self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
                !(c.is_unit_like_type(t) && c.are_types_comparable(t, value_type))
            });
        }
        t
    }

    /// `(c *Checker) narrowTypeByTypeof` (flow.go) — we have '==', '!=',
    /// '===', or '!==' operator with 'typeof xxx' and string literal
    /// operands.
    pub(crate) fn narrow_type_by_typeof(
        &mut self,
        f: &mut FlowState,
        mut t: TypeId,
        type_of_expr: NodeId,
        operator: Kind,
        literal: NodeId,
        mut assume_true: bool,
    ) -> TypeId {
        if operator == Kind::ExclamationEqualsToken
            || operator == Kind::ExclamationEqualsEqualsToken
        {
            assume_true = !assume_true;
        }
        let target =
            self.get_reference_candidate(&f.nodes(), f.nodes()[type_of_expr].expression().unwrap());
        if !self.is_matching_reference(&f.nodes(), f.reference(), target) {
            if self.strict_null_checks
                && self.optional_chain_contains_reference(&f.nodes(), target, f.reference())
                && assume_true == (f.nodes()[literal].text(&f.nodes()) != "undefined")
            {
                t = self.get_adjusted_type_with_facts(t, TypeFacts::NE_UNDEFINED_OR_NULL);
            }
            if let Some(property_access) = self.get_discriminant_property_access(f, target, t) {
                let __nodes_arena = f.nodes.clone().unwrap();
                let nodes = __nodes_arena.snapshot();
                return self.narrow_type_by_discriminant(
                    t,
                    property_access,
                    &nodes,
                    &mut |c: &mut Checker, t: TypeId| {
                        c.narrow_type_by_literal_expression(t, literal, assume_true, &nodes)
                    },
                );
            }
            return t;
        }
        self.narrow_type_by_literal_expression(t, literal, assume_true, &f.nodes())
    }

    /// `(c *Checker) narrowTypeByLiteralExpression` (flow.go).
    pub(crate) fn narrow_type_by_literal_expression(
        &mut self,
        t: TypeId,
        literal: NodeId,
        assume_true: bool,
        nodes: &[ast::Node],
    ) -> TypeId {
        let text = nodes[literal].text(nodes).into_owned();
        if assume_true {
            return self.narrow_type_by_type_name(t, &text);
        }
        let facts = typeof_ne_facts(&text).unwrap_or(TypeFacts::TYPEOF_NE_HOST_OBJECT);
        self.get_adjusted_type_with_facts(t, facts)
    }

    /// `(c *Checker) narrowTypeByTypeName` (flow.go).
    pub(crate) fn narrow_type_by_type_name(&mut self, t: TypeId, type_name: &str) -> TypeId {
        match type_name {
            "string" => {
                self.narrow_type_by_type_facts(t, self.string_type, TypeFacts::TYPEOF_EQ_STRING)
            }
            "number" => {
                self.narrow_type_by_type_facts(t, self.number_type, TypeFacts::TYPEOF_EQ_NUMBER)
            }
            "bigint" => {
                self.narrow_type_by_type_facts(t, self.bigint_type, TypeFacts::TYPEOF_EQ_BIG_INT)
            }
            "boolean" => {
                self.narrow_type_by_type_facts(t, self.boolean_type, TypeFacts::TYPEOF_EQ_BOOLEAN)
            }
            "symbol" => {
                self.narrow_type_by_type_facts(t, self.es_symbol_type, TypeFacts::TYPEOF_EQ_SYMBOL)
            }
            "object" => {
                if self.types_handle().get(t).flags.intersects(TypeFlags::ANY) {
                    return t;
                }
                let a = self.narrow_type_by_type_facts(
                    t,
                    self.non_primitive_type,
                    TypeFacts::TYPEOF_EQ_OBJECT,
                );
                let b = self.narrow_type_by_type_facts(t, self.null_type, TypeFacts::EQ_NULL);
                self.get_union_type(&[a, b])
            }
            "function" => {
                if self.types_handle().get(t).flags.intersects(TypeFlags::ANY) {
                    return t;
                }
                self.narrow_type_by_type_facts(
                    t,
                    self.global_function_type,
                    TypeFacts::TYPEOF_EQ_FUNCTION,
                )
            }
            "undefined" => {
                self.narrow_type_by_type_facts(t, self.undefined_type, TypeFacts::EQ_UNDEFINED)
            }
            _ => self.narrow_type_by_type_facts(
                t,
                self.non_primitive_type,
                TypeFacts::TYPEOF_EQ_HOST_OBJECT,
            ),
        }
    }

    /// `(c *Checker) narrowTypeByTypeFacts` (flow.go).
    pub(crate) fn narrow_type_by_type_facts(
        &mut self,
        t: TypeId,
        implied_type: TypeId,
        facts: TypeFacts,
    ) -> TypeId {
        self.map_type(
            t,
            Rc::new(move |c: &mut Checker, t: TypeId| {
                let relation = c.strict_subtype_relation.clone();
                if c.is_type_related_to(t, implied_type, &relation) {
                    if c.has_type_facts(t, facts) {
                        return t;
                    }
                    return c.never_type;
                }
                if c.is_type_subtype_of(implied_type, t) {
                    return implied_type;
                }
                if c.has_type_facts(t, facts) {
                    return c.get_intersection_type(&[t, implied_type]);
                }
                c.never_type
            }),
        )
    }

    /// `(c *Checker) narrowTypeByDiscriminantProperty` (flow.go).
    pub(crate) fn narrow_type_by_discriminant_property(
        &mut self,
        t: TypeId,
        access: NodeId,
        operator: Kind,
        value: NodeId,
        assume_true: bool,
        nodes: &[ast::Node],
    ) -> TypeId {
        // `access` can be foreign to `nodes` (a declaration in the
        // reference's file) — all `nodes` derefs below are on `access`.
        let __foreign;
        let nodes = if nodes.first().map(|n| n.id.file_index()) == Some(access.file_index()) {
            nodes
        } else {
            __foreign = self.program_nodes(access);
            __foreign.as_slice()
        };
        if (operator == Kind::EqualsEqualsEqualsToken
            || operator == Kind::ExclamationEqualsEqualsToken)
            && self
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::UNION)
        {
            let key_property_name = self.get_key_property_name(t);
            if !key_property_name.is_empty() {
                let (accessed_name, ok) = self.get_accessed_property_name(nodes, access);
                if ok && key_property_name == accessed_name {
                    let value_type = self.get_type_of_expression(value);
                    if let Some(candidate) = self.get_constituent_type_for_key_type(t, value_type) {
                        if (assume_true && operator == Kind::EqualsEqualsEqualsToken)
                            || (!assume_true && operator == Kind::ExclamationEqualsEqualsToken)
                        {
                            return candidate;
                        }
                        if let Some(prop_type) =
                            self.get_type_of_property_of_type(candidate, &key_property_name)
                        {
                            if crate::checker_d::is_unit_type(&self.types, prop_type) {
                                return self.remove_type(t, candidate);
                            }
                        }
                        return t;
                    }
                }
            }
        }
        self.narrow_type_by_discriminant(t, access, nodes, &mut |c: &mut Checker, t: TypeId| {
            c.narrow_type_by_equality(t, operator, value, assume_true)
        })
    }

    /// `(c *Checker) narrowTypeByDiscriminant` (flow.go).
    pub(crate) fn narrow_type_by_discriminant(
        &mut self,
        t: TypeId,
        access: NodeId,
        nodes: &[ast::Node],
        narrow_type: &mut dyn FnMut(&mut Checker, TypeId) -> TypeId,
    ) -> TypeId {
        // `access` can be foreign to `nodes` (a declaration in the
        // reference's file) — all `nodes` derefs below are on `access`.
        let __foreign;
        let nodes = if nodes.first().map(|n| n.id.file_index()) == Some(access.file_index()) {
            nodes
        } else {
            __foreign = self.program_nodes(access);
            __foreign.as_slice()
        };
        let (prop_name, ok) = self.get_accessed_property_name(nodes, access);
        if !ok {
            return t;
        }
        let optional_chain = ast::is_optional_chain(&nodes[access]);
        let remove_nullable = self.strict_null_checks
            && (optional_chain || crate::utilities::is_non_null_access(access, &nodes))
            && self.maybe_type_of_kind(t, TypeFlags::NULLABLE);
        let non_null_type = if remove_nullable {
            self.get_type_with_facts(t, TypeFacts::NE_UNDEFINED_OR_NULL)
        } else {
            t
        };
        let Some(prop_type) = self.get_type_of_property_of_type(non_null_type, &prop_name) else {
            return t;
        };
        let prop_type = if remove_nullable && optional_chain {
            self.get_optional_type(prop_type, false)
        } else {
            prop_type
        };
        let narrowed_prop_type = narrow_type(self, prop_type);
        self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
            let discriminant_type = tsc_core::core::or_else(
                c.get_type_of_property_or_index_signature_of_type(t, &prop_name)
                    .unwrap_or_default(),
                c.unknown_type,
            );
            !c.types_handle()
                .get(discriminant_type)
                .flags
                .intersects(TypeFlags::NEVER)
                && !c
                    .types_handle()
                    .get(narrowed_prop_type)
                    .flags
                    .intersects(TypeFlags::NEVER)
                && c.are_types_comparable(narrowed_prop_type, discriminant_type)
        })
    }

    /// `(c *Checker) isMatchingConstructorReference` (flow.go).
    pub(crate) fn is_matching_constructor_reference(
        &mut self,
        f: &FlowState,
        expr: NodeId,
    ) -> bool {
        let nodes = &f.nodes();
        let name = if ast::is_property_access_expression(&nodes[expr]) {
            nodes[expr].name()
        } else if ast::is_element_access_expression(&nodes[expr])
            && ast::is_string_literal_like(
                &nodes[nodes[expr]
                    .as_element_access_expression()
                    .argument_expression
                    .unwrap()],
            )
        {
            Some(
                nodes[expr]
                    .as_element_access_expression()
                    .argument_expression
                    .unwrap(),
            )
        } else {
            None
        };
        name.is_some_and(|n| nodes[n].text(nodes) == "constructor")
            && self.is_matching_reference(
                &f.nodes(),
                f.reference(),
                nodes[expr].expression().unwrap(),
            )
    }

    /// `(c *Checker) narrowTypeByConstructor` (flow.go).
    pub(crate) fn narrow_type_by_constructor(
        &mut self,
        t: TypeId,
        operator: Kind,
        identifier: NodeId,
        assume_true: bool,
    ) -> TypeId {
        // Do not narrow when checking inequality.
        if (assume_true
            && operator != Kind::EqualsEqualsToken
            && operator != Kind::EqualsEqualsEqualsToken)
            || (!assume_true
                && operator != Kind::ExclamationEqualsToken
                && operator != Kind::ExclamationEqualsEqualsToken)
        {
            return t;
        }
        // Get the type of the constructor identifier expression, if it is not a function then do not narrow.
        let identifier_type = self.get_type_of_expression(identifier);
        if !self.is_function_type(identifier_type) && !self.is_constructor_type(identifier_type) {
            return t;
        }
        // Get the prototype property of the type identifier so we can find out its type.
        let Some(prototype_property) = self.get_property_of_type(identifier_type, "prototype")
        else {
            return t;
        };
        // Get the type of the prototype, if it is undefined, or the global `Object` or `Function` types then do not narrow.
        let prototype_type = self.get_type_of_symbol(prototype_property);
        let candidate = if !crate::utilities::is_type_any(&self.types, prototype_type) {
            Some(prototype_type)
        } else {
            None
        };
        let Some(candidate) = candidate else {
            return t;
        };
        if candidate == self.global_object_type || candidate == self.global_function_type {
            return t;
        }
        // If the type that is being narrowed is `any` then just return the `candidate` type since every type is a subtype of `any`.
        if crate::utilities::is_type_any(&self.types, t) {
            return candidate;
        }
        // Filter out types that are not considered to be "constructed by" the `candidate` type.
        self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
            c.is_constructed_by(t, candidate)
        })
    }

    /// `(c *Checker) isConstructedBy` (flow.go). If either the source or
    /// target type are a class type then we need to check that they are the
    /// same exact type — you may have a class `A` that defines some set of
    /// properties, and another class `B` that defines the same set of
    /// properties as class `A`; they are structurally the same type, but
    /// `instanceOfA.constructor === B` will return false.
    pub(crate) fn is_constructed_by(&mut self, source: TypeId, target: TypeId) -> bool {
        let (s_flags, s_oflags, s_symbol) = {
            let __arena_t = self.types.clone();
            let t = __arena_t.get(source);
            (t.flags, t.object_flags, t.symbol)
        };
        let (t_flags, t_oflags, t_symbol) = {
            let __arena_t = self.types.clone();
            let t = __arena_t.get(target);
            (t.flags, t.object_flags, t.symbol)
        };
        if (s_flags.intersects(TypeFlags::OBJECT) && s_oflags.intersects(ObjectFlags::CLASS))
            || (t_flags.intersects(TypeFlags::OBJECT) && t_oflags.intersects(ObjectFlags::CLASS))
        {
            return s_symbol == t_symbol;
        }
        // For all other types just check that the `source` type is a subtype of the `target` type.
        self.is_type_subtype_of(source, target)
    }

    /// `(c *Checker) narrowTypeByBooleanComparison` (flow.go).
    pub(crate) fn narrow_type_by_boolean_comparison(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        expr: NodeId,
        bool_value: NodeId,
        operator: Kind,
        assume_true: bool,
    ) -> TypeId {
        let assume_true = (assume_true != (f.nodes()[bool_value].kind == Kind::TrueKeyword))
            != (operator != Kind::ExclamationEqualsEqualsToken
                && operator != Kind::ExclamationEqualsToken);
        self.narrow_type(f, t, expr, assume_true)
    }

    /// `(c *Checker) narrowTypeByInstanceof` (flow.go).
    pub(crate) fn narrow_type_by_instanceof(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        expr: NodeId,
        assume_true: bool,
    ) -> TypeId {
        let left = self.get_reference_candidate(
            &f.nodes(),
            f.nodes()[expr].as_binary_expression().left.unwrap(),
        );
        if !self.is_matching_reference(&f.nodes(), f.reference(), left) {
            if assume_true
                && self.strict_null_checks
                && self.optional_chain_contains_reference(&f.nodes(), left, f.reference())
            {
                return self.get_adjusted_type_with_facts(t, TypeFacts::NE_UNDEFINED_OR_NULL);
            }
            return t;
        }
        let right = f.nodes()[expr].as_binary_expression().right.unwrap();
        let right_type = self.get_type_of_expression(right);
        if !self.is_type_derived_from(right_type, self.global_object_type) {
            return t;
        }
        // if the right-hand side has an object type with a custom `[Symbol.hasInstance]` method, and that method
        // has a type predicate, use the type predicate to perform narrowing. This allows normal `object` types to
        // participate in `instanceof`, as per Step 2 of https://tc39.es/ecma262/#sec-instanceofoperator.
        let mut predicate: Option<TypePredicate> = None;
        if let Some(signature) = self.get_effects_signature(expr) {
            predicate = self.get_type_predicate_of_signature(signature);
        }
        if let Some(predicate) = &predicate {
            if predicate.kind == TypePredicateKind::Identifier && predicate.parameter_index == 0 {
                return self.get_narrowed_type(
                    t,
                    predicate.t.unwrap_or(self.any_type),
                    assume_true,
                    true,
                );
            }
        }
        if !self.is_type_derived_from(right_type, self.global_function_type) {
            return t;
        }
        let instance_type = self.map_type(
            right_type,
            Rc::new(|c: &mut Checker, t: TypeId| c.get_instance_type(t)),
        );
        // Don't narrow from `any` if the target type is exactly `Object` or `Function`, and narrow
        // in the false branch only if the target is a non-empty object type.
        if crate::utilities::is_type_any(&self.types, t)
            && (instance_type == self.global_object_type
                || instance_type == self.global_function_type)
            || !assume_true
                && !(self
                    .types_handle()
                    .get(instance_type)
                    .flags
                    .intersects(TypeFlags::OBJECT)
                    && !self.is_empty_anonymous_object_type(instance_type))
        {
            return t;
        }
        self.get_narrowed_type(t, instance_type, assume_true, true)
    }

    /// `(c *Checker) getNarrowedType` (flow.go).
    pub(crate) fn get_narrowed_type(
        &mut self,
        t: TypeId,
        candidate: TypeId,
        assume_true: bool,
        check_derived: bool,
    ) -> TypeId {
        if !self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::UNION)
        {
            return self.get_narrowed_type_worker(t, candidate, assume_true, check_derived);
        }
        let key = NarrowedTypeKey {
            t,
            candidate,
            assume_true,
            check_derived,
        };
        if let Some(&narrowed_type) = self.narrowed_types.get(&key) {
            return narrowed_type;
        }
        let narrowed_type = self.get_narrowed_type_worker(t, candidate, assume_true, check_derived);
        self.narrowed_types.insert(key, narrowed_type);
        narrowed_type
    }

    /// `(c *Checker) getNarrowedTypeWorker` (flow.go).
    pub(crate) fn get_narrowed_type_worker(
        &mut self,
        mut t: TypeId,
        candidate: TypeId,
        assume_true: bool,
        check_derived: bool,
    ) -> TypeId {
        if !assume_true {
            if t == candidate {
                return self.never_type;
            }
            if check_derived {
                return self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
                    !c.is_type_derived_from(t, candidate)
                });
            }
            if self
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::UNKNOWN)
            {
                t = self.unknown_union_type;
            }
            let true_type = self.get_narrowed_type(t, candidate, true, false);
            let filtered = self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
                !c.is_type_subset_of(t, true_type)
            });
            return self.recombine_unknown_type(filtered);
        }
        if self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::ANY_OR_UNKNOWN)
        {
            return candidate;
        }
        if t == candidate {
            return candidate;
        }
        // We first attempt to filter the current type, narrowing constituents as appropriate and removing
        // constituents that are unrelated to the candidate.
        let mut key_property_name = String::new();
        if self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::UNION)
        {
            key_property_name = self.get_key_property_name(t);
        }
        let narrowed_type = self.map_type(
            candidate,
            Rc::new(move |c: &mut Checker, n: TypeId| {
                // If a discriminant property is available, use that to reduce the type.
                let mut matching = t;
                if !key_property_name.is_empty() {
                    if let Some(discriminant) =
                        c.get_type_of_property_of_type(n, &key_property_name)
                    {
                        if let Some(constituent) =
                            c.get_constituent_type_for_key_type(t, discriminant)
                        {
                            matching = constituent;
                        }
                    }
                }
                // For each constituent t in the current type, if t and c are directly related, pick the most
                // specific of the two. When t and c are related in both directions, we prefer c for type predicates
                // because that is the asserted type, but t for `instanceof` because generics aren't reflected in
                // prototype object types.
                let map_fn = move |c: &mut Checker, t: TypeId| -> TypeId {
                    if check_derived {
                        if c.is_type_derived_from(t, n) {
                            return t;
                        }
                        if c.is_type_derived_from(n, t) {
                            return n;
                        }
                        return c.never_type;
                    }
                    if c.is_type_strict_subtype_of(t, n) {
                        return t;
                    }
                    if c.is_type_strict_subtype_of(n, t) {
                        return n;
                    }
                    if c.is_type_subtype_of(t, n) {
                        return t;
                    }
                    if c.is_type_subtype_of(n, t) {
                        return n;
                    }
                    c.never_type
                };
                let directly_related = c.map_type(matching, Rc::new(map_fn));
                if !c
                    .types_handle()
                    .get(directly_related)
                    .flags
                    .intersects(TypeFlags::NEVER)
                {
                    return directly_related;
                }
                // If no constituents are directly related, create intersections for any generic constituents that
                // are related by constraint.
                c.map_type(
                    t,
                    Rc::new(move |c: &mut Checker, t: TypeId| {
                        if c.maybe_type_of_kind(t, TypeFlags::INSTANTIABLE) {
                            let constraint = c.get_base_constraint_of_type(t);
                            let related = match constraint {
                                None => true,
                                Some(constraint) => {
                                    if check_derived {
                                        c.is_type_derived_from(n, constraint)
                                    } else {
                                        c.is_type_subtype_of(n, constraint)
                                    }
                                }
                            };
                            if related {
                                return c.get_intersection_type(&[t, n]);
                            }
                        }
                        c.never_type
                    }),
                )
            }),
        );
        // If filtering produced a non-empty type, return that. Otherwise, pick the most specific of the two
        // based on assignability, or as a last resort produce an intersection.
        if !self
            .types_handle()
            .get(narrowed_type)
            .flags
            .intersects(TypeFlags::NEVER)
        {
            return narrowed_type;
        }
        if self.is_type_subtype_of(candidate, t) {
            return candidate;
        }
        if self.is_type_assignable_to(t, candidate) {
            return t;
        }
        if self.is_type_assignable_to(candidate, t) {
            return candidate;
        }
        self.get_intersection_type(&[t, candidate])
    }

    /// `(c *Checker) getInstanceType` (flow.go).
    pub(crate) fn get_instance_type(&mut self, constructor_type: TypeId) -> TypeId {
        if let Some(prototype_property_type) =
            self.get_type_of_property_of_type(constructor_type, "prototype")
        {
            if !crate::utilities::is_type_any(&self.types, prototype_property_type) {
                return prototype_property_type;
            }
        }
        let construct_signatures =
            self.get_signatures_of_type(constructor_type, SignatureKind::Construct);
        if !construct_signatures.is_empty() {
            let types: Vec<TypeId> = construct_signatures
                .iter()
                .map(|&signature| {
                    let erased = self.get_erased_signature(signature);
                    self.get_return_type_of_signature(erased)
                })
                .collect();
            return self.get_union_type(&types);
        }
        // We use the empty object type to indicate we don't know the type of objects created by
        // this constructor function.
        self.empty_object_type
    }

    /// `(c *Checker) narrowTypeByPrivateIdentifierInInExpression` (flow.go).
    pub(crate) fn narrow_type_by_private_identifier_in_in_expression(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        expr: NodeId,
        assume_true: bool,
    ) -> TypeId {
        let target = self.get_reference_candidate(
            &f.nodes(),
            f.nodes()[expr].as_binary_expression().right.unwrap(),
        );
        if !self.is_matching_reference(&f.nodes(), f.reference(), target) {
            return t;
        }
        let left = f.nodes()[expr].as_binary_expression().left.unwrap();
        let Some(symbol) = self.get_symbol_for_private_identifier_expression(left) else {
            return t;
        };
        let (class_symbol, value_declaration) = {
            let arena = self.symbol_arena.clone();
            (
                arena[symbol.index()].parent,
                arena[symbol.index()].value_declaration,
            )
        };
        let Some(class_symbol) = class_symbol else {
            return t;
        };
        let target_type =
            if value_declaration.is_some_and(|d| ast::has_static_modifier(&f.nodes()[d])) {
                self.get_type_of_symbol(class_symbol)
            } else {
                self.get_declared_type_of_symbol(class_symbol)
            };
        self.get_narrowed_type(t, target_type, assume_true, true)
    }

    /// `(c *Checker) narrowTypeByInKeyword` (flow.go).
    pub(crate) fn narrow_type_by_in_keyword(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        name_type: TypeId,
        assume_true: bool,
    ) -> TypeId {
        let name = crate::utilities::get_property_name_from_type(&self.types, name_type);
        let is_known_property =
            crate::checker_d::some_type(self, t, |c: &mut Checker, t: TypeId| {
                c.is_type_presence_possible(t, &name, true)
            });
        if is_known_property {
            // If the check is for a known property (i.e. a property declared in some constituent of
            // the target type), we filter the target type by presence of absence of the property.
            return self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
                c.is_type_presence_possible(t, &name, assume_true)
            });
        }
        let _ = f;
        if assume_true {
            // If the check is for an unknown property, we intersect the target type with `Record<X, unknown>`,
            // where X is the name of the property.
            if let Some(record_symbol) = (self.get_global_record_symbol.clone().unwrap())(self) {
                let record = self.get_type_alias_instantiation(
                    record_symbol,
                    &[name_type, self.unknown_type],
                    None,
                );
                return self.get_intersection_type(&[t, record]);
            }
        }
        t
    }

    /// `(c *Checker) isTypePresencePossible` (flow.go).
    pub(crate) fn is_type_presence_possible(
        &mut self,
        t: TypeId,
        prop_name: &str,
        assume_true: bool,
    ) -> bool {
        if let Some(prop) = self.get_property_of_type(t, prop_name) {
            let (flags, check_flags) = {
                let arena = self.symbol_arena.clone();
                (arena[prop.index()].flags, arena[prop.index()].check_flags)
            };
            return flags.intersects(ast::SymbolFlags::OPTIONAL)
                || check_flags.intersects(CheckFlags::PARTIAL)
                || assume_true;
        }
        self.get_applicable_index_info_for_name(t, prop_name)
            .is_some()
            || !assume_true
    }

    /// `(c *Checker) narrowTypeByOptionalChainContainment` (flow.go). We are
    /// in a branch of `obj?.foo === value` (or any one of the other equality
    /// operators). We narrow `obj` as follows: when operator is `===` and
    /// type of value excludes undefined, null and undefined is removed from
    /// type of obj in true branch; when operator is `!==` and type of value
    /// excludes undefined, null and undefined is removed in false branch;
    /// when operator is `==` and type of value excludes null and undefined,
    /// null and undefined is removed in true branch; when operator is `!=`
    /// and type of value excludes null and undefined, null and undefined is
    /// removed in false branch; when operator is `===` and type of value is
    /// undefined, null and undefined is removed in false branch; when
    /// operator is `!==` and type of value is undefined, null and undefined
    /// is removed in true branch; when operator is `==` and type of value is
    /// null or undefined, null and undefined is removed in false branch;
    /// when operator is `!=` and type of value is null or undefined, null
    /// and undefined is removed in true branch.
    pub(crate) fn narrow_type_by_optional_chain_containment(
        &mut self,
        f: &mut FlowState,
        t: TypeId,
        operator: Kind,
        value: NodeId,
        assume_true: bool,
    ) -> TypeId {
        let _ = f;
        let equals_operator =
            operator == Kind::EqualsEqualsToken || operator == Kind::EqualsEqualsEqualsToken;
        let nullable_flags =
            if operator == Kind::EqualsEqualsToken || operator == Kind::ExclamationEqualsToken {
                TypeFlags::NULLABLE
            } else {
                TypeFlags::UNDEFINED
            };
        let value_type = self.get_type_of_expression(value);
        // Note that we include any and unknown in the exclusion test because their domain includes null and undefined.
        let remove_nullable = (equals_operator != assume_true
            && crate::checker_d::every_type(self, value_type, |c: &mut Checker, t: TypeId| {
                c.types_handle().get(t).flags.intersects(nullable_flags)
            }))
            || (equals_operator == assume_true
                && crate::checker_d::every_type(self, value_type, |c: &mut Checker, t: TypeId| {
                    !c.types_handle()
                        .get(t)
                        .flags
                        .intersects(TypeFlags::ANY_OR_UNKNOWN | nullable_flags)
                }));
        if remove_nullable {
            return self.get_adjusted_type_with_facts(t, TypeFacts::NE_UNDEFINED_OR_NULL);
        }
        t
    }
}
// __CONTINUE__

/// `var typeofNEFacts` (flow.go) — not-equal facts for `typeof` case names.
fn typeof_ne_facts(text: &str) -> Option<TypeFacts> {
    match text {
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

impl Checker {
    /// `(c *Checker) getTypeAtSwitchClause` (flow.go).
    pub(crate) fn get_type_at_switch_clause(
        &mut self,
        f: &mut FlowState,
        flow: FlowNodeId,
    ) -> FlowType {
        let node = f.flow_node(flow).node.expect("switch clause flow node");
        let data = SwitchClauseData::of(&f.nodes(), node);
        let expr = ast::skip_parentheses(
            f.nodes()[data.switch_statement.expect("switch statement")]
                .expression()
                .unwrap(),
            &f.nodes(),
        );
        let antecedent = f.flow_node(flow).antecedent.unwrap();
        let flow_type = self.get_type_at_flow_node(f, antecedent);
        let mut t = flow_type.ty();
        if self.is_matching_reference(&f.nodes(), f.reference(), expr) {
            t = self.narrow_type_by_switch_on_discriminant(t, data);
        } else if f.nodes()[expr].kind == Kind::TypeOfExpression
            && self.is_matching_reference(
                &f.nodes(),
                f.reference(),
                f.nodes()[expr].expression().unwrap(),
            )
        {
            t = self.narrow_type_by_switch_on_typeof(t, data);
        } else if f.nodes()[expr].kind == Kind::TrueKeyword {
            t = self.narrow_type_by_switch_on_true(f, t, data);
        } else {
            if self.strict_null_checks {
                if self.optional_chain_contains_reference(&f.nodes(), expr, f.reference()) {
                    t = self.narrow_type_by_switch_optional_chain_containment(
                        t,
                        data,
                        &mut |c: &mut Checker, t: TypeId| {
                            !c.types_handle()
                                .get(t)
                                .flags
                                .intersects(TypeFlags::UNDEFINED | TypeFlags::NEVER)
                        },
                    );
                } else if ast::is_type_of_expression(&f.nodes()[expr])
                    && self.optional_chain_contains_reference(
                        &f.nodes(),
                        f.nodes()[expr].expression().unwrap(),
                        f.reference(),
                    )
                {
                    t = self.narrow_type_by_switch_optional_chain_containment(
                        t,
                        data,
                        &mut |c: &mut Checker, t: TypeId| {
                            let __arena_flags = c.types.clone();
                            let flags = __arena_flags.get(t).flags;
                            !(flags.intersects(TypeFlags::NEVER)
                                || flags.intersects(TypeFlags::STRING_LITERAL)
                                    && crate::checker_d::get_string_literal_value(&c.types, t)
                                        == "undefined")
                        },
                    );
                }
            }
            if let Some(access) = self.get_discriminant_property_access(f, expr, t) {
                t = self.narrow_type_by_switch_on_discriminant_property(t, access, data);
            }
        }
        new_flow_type(self, t, flow_type.incomplete)
    }

    /// `(c *Checker) narrowTypeBySwitchOnDiscriminant` (flow.go). We only
    /// narrow if all case expressions specify values with unit types, except
    /// for the case where `type` is unknown. In this instance we map object
    /// types to the nonPrimitive type and narrow with that.
    pub(crate) fn narrow_type_by_switch_on_discriminant(
        &mut self,
        t: TypeId,
        data: SwitchClauseData,
    ) -> TypeId {
        let switch_statement = data.switch_statement.expect("switch statement");
        let switch_types = self.get_switch_clause_types(switch_statement);
        if switch_types.is_empty() {
            return t;
        }
        let clause_types = switch_types[data.clause_start()..data.clause_end()].to_vec();
        let has_default_clause =
            data.clause_start == data.clause_end || clause_types.contains(&self.never_type);
        if self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::UNKNOWN)
            && !has_default_clause
        {
            let mut ground_clause_types: Option<Vec<TypeId>> = None;
            for (i, &s) in clause_types.iter().enumerate() {
                let __arena_s_flags = self.types.clone();
                let s_flags = __arena_s_flags.get(s).flags;
                if s_flags.intersects(TypeFlags::PRIMITIVE | TypeFlags::NON_PRIMITIVE) {
                    if let Some(ground) = &mut ground_clause_types {
                        ground.push(s);
                    }
                } else if s_flags.intersects(TypeFlags::OBJECT) {
                    if ground_clause_types.is_none() {
                        ground_clause_types = Some(clause_types[..i].to_vec());
                    }
                    ground_clause_types
                        .as_mut()
                        .unwrap()
                        .push(self.non_primitive_type);
                } else {
                    return t;
                }
            }
            return self.get_union_type(ground_clause_types.as_deref().unwrap_or(&clause_types));
        }
        let discriminant_type = self.get_union_type(&clause_types);
        let case_type: TypeId;
        if self
            .types_handle()
            .get(discriminant_type)
            .flags
            .intersects(TypeFlags::NEVER)
        {
            case_type = self.never_type;
        } else {
            let mut case_type_opt: Option<TypeId> = None;
            if self
                .types_handle()
                .get(discriminant_type)
                .flags
                .intersects(TypeFlags::PRIMITIVE)
                && self.is_uniform_union_type(t)
            {
                let regular_type = self.get_regular_type_of_literal_type(discriminant_type);
                if self.union_contains_type(t, regular_type, false) {
                    case_type_opt = Some(regular_type);
                }
            }
            case_type = match case_type_opt {
                Some(t) => t,
                None => {
                    let filtered = self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
                        c.are_types_comparable(discriminant_type, t)
                    });
                    self.replace_primitives_with_literals(filtered, discriminant_type)
                }
            };
        }
        if !has_default_clause {
            return case_type;
        }
        let default_type = self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
            if !c.is_unit_like_type(t) {
                return true;
            }
            let mut u = c.undefined_type;
            if !c
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::UNDEFINED)
            {
                let __h2246_56 = c.extract_unit_type(t);

                u = c.get_regular_type_of_literal_type(__h2246_56);
            }
            // PORT(borrowck): sequential borrows in a loop instead of a
            // `any` closure that would capture `*c` both shared (`c.types`)
            // and mutable (`are_types_comparable`).
            let mut any_comparable = false;
            for &st in switch_types.iter() {
                if crate::checker_d::is_unit_type(&c.types, st) && c.are_types_comparable(st, u) {
                    any_comparable = true;
                    break;
                }
            }
            !any_comparable
        });
        if self
            .types_handle()
            .get(case_type)
            .flags
            .intersects(TypeFlags::NEVER)
        {
            return default_type;
        }
        self.get_union_type(&[case_type, default_type])
    }

    /// `(c *Checker) narrowTypeBySwitchOnTypeOf` (flow.go).
    pub(crate) fn narrow_type_by_switch_on_typeof(
        &mut self,
        t: TypeId,
        data: SwitchClauseData,
    ) -> TypeId {
        let switch_statement = data.switch_statement.expect("switch statement");
        let Some(witnesses) = self.get_switch_clause_type_of_witnesses(switch_statement) else {
            return t;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((switch_statement).file_index());
        let clauses: Vec<NodeId> = nodes[switch_statement]
            .as_switch_statement()
            .case_block
            .map(|cb| {
                nodes[cb]
                    .as_case_block()
                    .clauses
                    .as_ref()
                    .map(|c| c.nodes().to_vec())
                    .unwrap_or_default()
            })
            .unwrap_or_default();
        // Equal start and end denotes implicit fallthrough; undefined marks
        // explicit default clause.
        let default_index = clauses
            .iter()
            .position(|&clause| nodes[clause].kind == Kind::DefaultClause)
            .map(|i| i as i32)
            .unwrap_or(-1);
        let clause_start = data.clause_start;
        let clause_end = data.clause_end;
        let has_default_clause = clause_start == clause_end
            || (default_index >= clause_start && default_index < clause_end);
        if has_default_clause {
            // In the default clause we filter constituents down to those that
            // are not-equal to all handled cases.
            let not_equal_facts =
                self.get_not_equal_facts_from_typeof_switch(clause_start, clause_end, &witnesses);
            return self.filter_type(t, &mut |c: &mut Checker, t: TypeId| {
                c.get_type_facts(t, not_equal_facts) == not_equal_facts
            });
        }
        // In the non-default case we create a union of the type narrowed by
        // each of the listed cases.
        let clause_witnesses = witnesses[clause_start as usize..clause_end as usize].to_vec();
        let types: Vec<TypeId> = clause_witnesses
            .iter()
            .map(|text| {
                if !text.is_empty() {
                    self.narrow_type_by_type_name(t, text)
                } else {
                    self.never_type
                }
            })
            .collect();
        self.get_union_type(&types)
    }

    /// `(c *Checker) narrowTypeBySwitchOnTrue` (flow.go).
    pub(crate) fn narrow_type_by_switch_on_true(
        &mut self,
        f: &mut FlowState,
        mut t: TypeId,
        data: SwitchClauseData,
    ) -> TypeId {
        let switch_statement = data.switch_statement.expect("switch statement");
        let clauses: Vec<NodeId> = f.nodes()[switch_statement]
            .as_switch_statement()
            .case_block
            .map(|cb| {
                f.nodes()[cb]
                    .as_case_block()
                    .clauses
                    .as_ref()
                    .map(|c| c.nodes().to_vec())
                    .unwrap_or_default()
            })
            .unwrap_or_default();
        let default_index = clauses
            .iter()
            .position(|&clause| f.nodes()[clause].kind == Kind::DefaultClause)
            .map(|i| i as i32)
            .unwrap_or(-1);
        let clause_start = data.clause_start;
        let clause_end = data.clause_end;
        let has_default_clause = clause_start == clause_end
            || (default_index >= clause_start && default_index < clause_end);
        // First, narrow away all of the cases that preceded this set of cases.
        for &clause in &clauses[..clause_start as usize] {
            if f.nodes()[clause].kind == Kind::CaseClause {
                let expr = f.nodes()[clause].expression().unwrap();
                t = self.narrow_type(f, t, expr, false);
            }
        }
        // If our current set has a default, then none the other cases were hit
        // either. There's no point in narrowing by the other cases in the set,
        // since we can get here through other paths.
        if has_default_clause {
            for &clause in &clauses[clause_end as usize..] {
                if f.nodes()[clause].kind == Kind::CaseClause {
                    let expr = f.nodes()[clause].expression().unwrap();
                    t = self.narrow_type(f, t, expr, false);
                }
            }
            return t;
        }
        // Now, narrow based on the cases in this set.
        let mut t_by_clause = Vec::with_capacity(clause_end as usize - clause_start as usize);
        for &clause in &clauses[clause_start as usize..clause_end as usize] {
            t_by_clause.push(if f.nodes()[clause].kind == Kind::CaseClause {
                let expr = f.nodes()[clause].expression().unwrap();
                self.narrow_type(f, t, expr, true)
            } else {
                self.never_type
            });
        }
        self.get_union_type(&t_by_clause)
    }

    /// `(c *Checker) narrowTypeBySwitchOptionalChainContainment` (flow.go).
    pub(crate) fn narrow_type_by_switch_optional_chain_containment(
        &mut self,
        t: TypeId,
        data: SwitchClauseData,
        clause_check: &mut dyn FnMut(&mut Checker, TypeId) -> bool,
    ) -> TypeId {
        let switch_statement = data.switch_statement.expect("switch statement");
        let switch_types = self.get_switch_clause_types(switch_statement);
        let every_clause_checks = data.clause_start != data.clause_end && {
            let clause_types = switch_types[data.clause_start()..data.clause_end()].to_vec();
            clause_types.into_iter().all(|t| clause_check(self, t))
        };
        if every_clause_checks {
            return self.get_type_with_facts(t, TypeFacts::NE_UNDEFINED_OR_NULL);
        }
        t
    }

    /// `(c *Checker) narrowTypeBySwitchOnDiscriminantProperty` (flow.go).
    pub(crate) fn narrow_type_by_switch_on_discriminant_property(
        &mut self,
        t: TypeId,
        access: NodeId,
        data: SwitchClauseData,
    ) -> TypeId {
        if data.clause_start < data.clause_end
            && self
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::UNION)
        {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((access).file_index());
            let (accessed_name, ok) = self.get_accessed_property_name(&nodes, access);
            if ok && !accessed_name.is_empty() && self.get_key_property_name(t) == accessed_name {
                let switch_statement = data.switch_statement.expect("switch statement");
                let clause_types = self.get_switch_clause_types(switch_statement)
                    [data.clause_start()..data.clause_end()]
                    .to_vec();
                let types: Vec<TypeId> = clause_types
                    .iter()
                    .map(|&s| {
                        self.get_constituent_type_for_key_type(t, s)
                            .unwrap_or(self.unknown_type)
                    })
                    .collect();
                let candidate = self.get_union_type(&types);
                if candidate != self.unknown_type {
                    return candidate;
                }
            }
        }
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((access).file_index());
        self.narrow_type_by_discriminant(t, access, &nodes, &mut |c: &mut Checker, t: TypeId| {
            c.narrow_type_by_switch_on_discriminant(t, data)
        })
    }

    /// `(c *Checker) getTypeAtFlowBranchLabel` (flow.go).
    pub(crate) fn get_type_at_flow_branch_label(
        &mut self,
        f: &mut FlowState,
        _flow: FlowNodeId,
        antecedents: Option<FlowListId>,
    ) -> FlowType {
        let antecedent_start = self.antecedent_types.len();
        let mut subtype_reduction = false;
        let mut seen_incomplete = false;
        let mut bypass_flow: Option<FlowNodeId> = None;
        let mut list = antecedents;
        while let Some(l) = list {
            let antecedent = f.flow_list(l).flow.expect("antecedent flow");
            if bypass_flow.is_none()
                && f.flow_node(antecedent)
                    .flags
                    .intersects(FlowFlags::SWITCH_CLAUSE)
                && {
                    let node = f.flow_node(antecedent).node.expect("switch clause node");
                    SwitchClauseData::of(&f.nodes(), node).is_empty()
                }
            {
                // The antecedent is the bypass branch of a potentially
                // exhaustive switch statement.
                bypass_flow = Some(antecedent);
                list = f.flow_list(l).next;
                continue;
            }
            let flow_type = self.get_type_at_flow_node(f, antecedent);
            // If the type at a particular antecedent path is the declared type
            // and the reference is known to always be assigned (i.e. when
            // declared and initial types are the same), there is no reason to
            // process more antecedents since the only possible outcome is
            // subtypes that will be removed in the final union type anyway.
            if flow_type.t == f.declared_type && f.declared_type == f.initial_type {
                self.antecedent_types.truncate(antecedent_start);
                return FlowType {
                    t: flow_type.t,
                    incomplete: false,
                };
            }
            if !self.antecedent_types[antecedent_start..].contains(&flow_type.ty()) {
                self.antecedent_types.push(flow_type.ty());
            }
            // If an antecedent type is not a subset of the declared type, we
            // need to perform subtype reduction. This happens when a "foreign"
            // type is injected into the control flow using the instanceof
            // operator or a user defined type predicate.
            if !self.is_type_subset_of(flow_type.ty(), f.initial_type()) {
                subtype_reduction = true;
            }
            if flow_type.incomplete {
                seen_incomplete = true;
            }
            list = f.flow_list(l).next;
        }
        if let Some(bypass_flow) = bypass_flow {
            let flow_type = self.get_type_at_flow_node(f, bypass_flow);
            // If the bypass flow contributes a type we haven't seen yet and
            // the switch statement isn't exhaustive, process the bypass flow
            // type. Since exhaustiveness checks increase the risk of
            // circularities, we only want to perform them when they make a
            // difference.
            if !self
                .types_handle()
                .get(flow_type.ty())
                .flags
                .intersects(TypeFlags::NEVER)
                && !self.antecedent_types[antecedent_start..].contains(&flow_type.ty())
                && !self.is_exhaustive_switch_statement(
                    SwitchClauseData::of(
                        &f.nodes(),
                        f.flow_node(bypass_flow).node.expect("switch clause node"),
                    )
                    .switch_statement
                    .expect("switch statement"),
                )
            {
                if flow_type.t == f.declared_type && f.declared_type == f.initial_type {
                    self.antecedent_types.truncate(antecedent_start);
                    return FlowType {
                        t: flow_type.t,
                        incomplete: false,
                    };
                }
                self.antecedent_types.push(flow_type.ty());
                if !self.is_type_subset_of(flow_type.ty(), f.initial_type()) {
                    subtype_reduction = true;
                }
                if flow_type.incomplete {
                    seen_incomplete = true;
                }
            }
        }
        let antecedent_types = self.antecedent_types[antecedent_start..].to_vec();
        let union_or_evolving = self.get_union_or_evolving_array_type(
            f,
            &antecedent_types,
            tsc_core::core::if_else(
                subtype_reduction,
                UnionReduction::Subtype,
                UnionReduction::Literal,
            ),
        );
        let result = new_flow_type(self, union_or_evolving, seen_incomplete);
        self.antecedent_types.truncate(antecedent_start);
        result
    }

    /// `(c *Checker) getUnionOrEvolvingArrayType` (flow.go). At flow control
    /// branch or loop junctions, if the type along every antecedent code path
    /// is an evolving array type, we construct a combined evolving array
    /// type. Otherwise we finalize all evolving array types.
    pub(crate) fn get_union_or_evolving_array_type(
        &mut self,
        f: &mut FlowState,
        types: &[TypeId],
        subtype_reduction: UnionReduction,
    ) -> TypeId {
        if is_evolving_array_type_list(&self.types, types) {
            let element_types: Vec<TypeId> = types
                .iter()
                .map(|&t| self.get_element_type_of_evolving_array_type(t))
                .collect();
            let element_union = self.get_union_type(&element_types);
            return self.get_evolving_array_type(element_union);
        }
        let finalized: Vec<TypeId> = types
            .iter()
            .map(|&t| self.finalize_evolving_array_type(t))
            .collect();
        // `core.SameMap` — the finalized list aliases `types` when nothing
        // changed.
        let finalized = if finalized == types {
            types.to_vec()
        } else {
            finalized
        };
        let union = self.get_union_type_ex(&finalized, subtype_reduction, None, None);
        let result = self.recombine_unknown_type(union);
        if result != f.declared_type()
            && (self.types_handle().get(result).flags
                & self.types_handle().get(f.declared_type()).flags)
                .intersects(TypeFlags::UNION)
            && self.types_handle().get(result).types()
                == self.types_handle().get(f.declared_type()).types()
        {
            return f.declared_type();
        }
        result
    }

    /// `(c *Checker) getTypeAtFlowLoopLabel` (flow.go).
    pub(crate) fn get_type_at_flow_loop_label(
        &mut self,
        f: &mut FlowState,
        flow: FlowNodeId,
    ) -> FlowType {
        if f.ref_key == CacheHashKey::default() {
            f.ref_key = self.get_flow_reference_key(f);
        }
        if f.ref_key == *NON_DOTTED_NAME_CACHE_KEY {
            // No cache key is generated when binding patterns are in
            // unnarrowable situations
            return FlowType {
                t: f.declared_type,
                incomplete: false,
            };
        }
        let key = FlowLoopKey {
            flow_node: flow,
            ref_key: f.ref_key,
        };
        // If we have previously computed the control flow type for the
        // reference at this flow loop junction, return the cached type.
        if let Some(&cached) = self.flow_loop_cache.get(&key) {
            return FlowType {
                t: Some(cached),
                incomplete: false,
            };
        }
        // If this flow loop junction and reference are already being
        // processed, return the union of the types computed for each branch so
        // far, marked as incomplete. It is possible to see an empty array in
        // cases where loops are nested and the back edge of the outer loop
        // reaches an inner loop that is already being analyzed. In such cases
        // we restart the analysis of the inner loop, which will then see a
        // non-empty in-process array for the outer loop and eventually
        // terminate because the first antecedent of a loop junction is always
        // the non-looping control flow path that leads to the top.
        for loop_info in &self.flow_loop_stack {
            if loop_info.key == key && !loop_info.types.is_empty() {
                let types = loop_info.types.clone();
                let union_or_evolving =
                    self.get_union_or_evolving_array_type(f, &types, UnionReduction::Literal);
                return new_flow_type(self, union_or_evolving, true);
            }
        }
        // Add the flow loop junction and reference to the in-process stack and
        // analyze each antecedent code path.
        let mut antecedent_types: Vec<TypeId> = Vec::with_capacity(4);
        let mut subtype_reduction = false;
        let mut first_antecedent_type = FlowType::none();
        let mut list = f.flow_node(flow).antecedents;
        while let Some(l) = list {
            let flow_type: FlowType;
            if first_antecedent_type.is_nil() {
                // The first antecedent of a loop junction is always the
                // non-looping control flow path that leads to the top.
                let antecedent = f.flow_list(l).flow.expect("antecedent flow");
                first_antecedent_type = self.get_type_at_flow_node(f, antecedent);
                flow_type = first_antecedent_type;
            } else {
                // All but the first antecedent are the looping control flow
                // paths that lead back to the loop junction. We track these
                // on the flow loop stack.
                self.flow_loop_stack.push(FlowLoopInfo {
                    key,
                    types: antecedent_types.clone(),
                });
                let save_flow_type_cache = std::mem::take(&mut self.flow_type_cache);
                let antecedent = f.flow_list(l).flow.expect("antecedent flow");
                flow_type = self.get_type_at_flow_node(f, antecedent);
                self.flow_type_cache = save_flow_type_cache;
                self.flow_loop_stack.pop();
                // If we see a value appear in the cache it is a sign that
                // control flow analysis was restarted and completed by
                // checkExpressionCached. We can simply pick up the resulting
                // type and bail out.
                if let Some(&cached) = self.flow_loop_cache.get(&key) {
                    return FlowType {
                        t: Some(cached),
                        incomplete: false,
                    };
                }
            }
            if !antecedent_types.contains(&flow_type.ty()) {
                antecedent_types.push(flow_type.ty());
            }
            // If an antecedent type is not a subset of the declared type, we
            // need to perform subtype reduction. This happens when a "foreign"
            // type is injected into the control flow using the instanceof
            // operator or a user defined type predicate.
            if !self.is_type_subset_of(flow_type.ty(), f.initial_type()) {
                subtype_reduction = true;
            }
            // If the type at a particular antecedent path is the declared type
            // there is no reason to process more antecedents since the only
            // possible outcome is subtypes that will be removed in the final
            // union type anyway.
            if flow_type.t == f.declared_type {
                break;
            }
            list = f.flow_list(l).next;
        }
        // The result is incomplete if the first antecedent (the non-looping
        // control flow path) is incomplete.
        let result = self.get_union_or_evolving_array_type(
            f,
            &antecedent_types,
            tsc_core::core::if_else(
                subtype_reduction,
                UnionReduction::Subtype,
                UnionReduction::Literal,
            ),
        );
        if first_antecedent_type.incomplete {
            return new_flow_type(self, result, true);
        }
        self.flow_loop_cache.insert(key, result);
        FlowType {
            t: Some(result),
            incomplete: false,
        }
    }

    /// `(c *Checker) getTypeAtFlowArrayMutation` (flow.go).
    pub(crate) fn get_type_at_flow_array_mutation(
        &mut self,
        f: &mut FlowState,
        flow: FlowNodeId,
    ) -> FlowType {
        if f.declared_type() == self.auto_type || f.declared_type() == self.auto_array_type {
            let node = f.flow_node(flow).node.expect("array mutation node");
            let expr = if ast::is_call_expression(&f.nodes()[node]) {
                f.nodes()[f.nodes()[node].expression().unwrap()].expression()
            } else {
                f.nodes()[f.nodes()[node].as_binary_expression().left.unwrap()].expression()
            };
            if expr.is_some_and(|e| {
                let e = self.get_reference_candidate(&f.nodes(), e);
                self.is_matching_reference(&f.nodes(), f.reference(), e)
            }) {
                let antecedent = f.flow_node(flow).antecedent.unwrap();
                let flow_type = self.get_type_at_flow_node(f, antecedent);
                if self
                    .types_handle()
                    .get(flow_type.ty())
                    .object_flags
                    .intersects(ObjectFlags::EVOLVING_ARRAY)
                {
                    let mut evolved_type = flow_type.ty();
                    if ast::is_call_expression(&f.nodes()[node]) {
                        let args: Vec<NodeId> = f.nodes()[node]
                            .arguments()
                            .map(|a| a.to_vec())
                            .unwrap_or_default();
                        for arg in args {
                            evolved_type = self.add_evolving_array_element_type(evolved_type, arg);
                        }
                    } else {
                        // We must get the context free expression type so as
                        // to not recur in an uncached fashion on the LHS
                        // (which causes exponential blowup in compile time)
                        let index_expr = f.nodes()[node]
                            .as_binary_expression()
                            .left
                            .map(|l| {
                                f.nodes()[l]
                                    .as_element_access_expression()
                                    .argument_expression
                            })
                            .flatten();
                        let index_type =
                            index_expr.map(|e| self.get_context_free_type_of_expression(e));
                        if index_type.is_some_and(|t| {
                            self.is_type_assignable_to_kind(t, TypeFlags::NUMBER_LIKE)
                        }) {
                            let right = f.nodes()[node].as_binary_expression().right.unwrap();
                            evolved_type =
                                self.add_evolving_array_element_type(evolved_type, right);
                        }
                    }
                    return new_flow_type(self, evolved_type, flow_type.incomplete);
                }
                return flow_type;
            }
        }
        FlowType::none()
    }

    /// `(c *Checker) getDiscriminantPropertyAccess` (flow.go). As long as the
    /// computed type is a subset of the declared type, we use the full
    /// declared type to detect a discriminant property. In cases where the
    /// computed type isn't a subset, e.g because of a preceding type
    /// predicate narrowing, we use the actual computed type.
    pub(crate) fn get_discriminant_property_access(
        &mut self,
        f: &mut FlowState,
        expr: NodeId,
        computed_type: TypeId,
    ) -> Option<NodeId> {
        if self
            .types_handle()
            .get(f.declared_type())
            .flags
            .intersects(TypeFlags::UNION)
            || self
                .types_handle()
                .get(computed_type)
                .flags
                .intersects(TypeFlags::UNION)
        {
            if let Some(access) = self.get_candidate_discriminant_property_access(f, expr) {
                let (name, ok) = self.get_accessed_property_name(&f.nodes(), access);
                if ok {
                    let t = if self
                        .types_handle()
                        .get(f.declared_type())
                        .flags
                        .intersects(TypeFlags::UNION)
                        && self.is_type_subset_of(computed_type, f.declared_type())
                    {
                        f.declared_type()
                    } else {
                        computed_type
                    };
                    if self.is_discriminant_property(t, &name) {
                        return Some(access);
                    }
                }
            }
        }
        None
    }

    /// `(c *Checker) getCandidateDiscriminantPropertyAccess` (flow.go).
    pub(crate) fn get_candidate_discriminant_property_access(
        &mut self,
        f: &mut FlowState,
        expr: NodeId,
    ) -> Option<NodeId> {
        let reference = f.reference();
        let __nodes_arena = f.nodes.clone().expect("FlowState.nodes unset");
        let nodes = __nodes_arena.snapshot();
        // `reference` and resolved `declaration`s can be foreign to the
        // flow-graph arena (cross-file narrowing) — resolve them in their
        // own arenas.
        let ref_nodes = self.program_nodes(reference);
        if ast::is_binding_pattern(&ref_nodes[reference])
            || ast::is_function_expression_or_arrow_function(&ref_nodes[reference])
            || ast::is_object_literal_method(reference, ref_nodes.as_slice())
        {
            // When the reference is a binding pattern or function or arrow
            // expression, we are narrowing a pseudo-reference in
            // getNarrowedTypeOfSymbol. An identifier for a destructuring
            // variable declared in the same binding pattern or parameter
            // declared in the same parameter list is a candidate.
            if ast::is_identifier(&nodes[expr]) {
                let symbol = self.get_resolved_symbol(expr);
                let exported = self.get_export_symbol_of_value_symbol_if_exported(Some(symbol));
                let declaration =
                    exported.and_then(|e| self.symbol_arena.get_ref(e).value_declaration);
                if let Some(declaration) = declaration {
                    let decl_nodes = self.program_nodes(declaration);
                    if (ast::is_binding_element(&decl_nodes[declaration])
                        || ast::is_parameter_declaration(&decl_nodes[declaration]))
                        && decl_nodes[declaration].parent == Some(reference)
                        && decl_nodes[declaration].initializer().is_none()
                        && !crate::utilities::has_dot_dot_dot_token(&decl_nodes[declaration], &decl_nodes)
                    {
                        return Some(declaration);
                    }
                }
            }
        } else if ast::is_access_expression(&nodes[expr]) {
            // An access expression is a candidate if the reference matches the
            // left hand expression.
            let inner = nodes[expr].expression();
            if inner.is_some_and(|e| self.is_matching_reference(nodes.as_slice(), reference, e)) {
                return Some(expr);
            }
        } else if ast::is_identifier(&nodes[expr]) {
            let symbol = self.get_resolved_symbol(expr);
            if self.is_constant_variable(symbol) {
                let declaration = self.symbol_arena.get_ref(symbol).value_declaration;
                // `declaration` can be foreign to the flow-graph arena —
                // resolve it in its own arena.
                let decl_nodes = declaration.map(|d| self.program_nodes(d));
                let dnodes: &[ast::Node] = decl_nodes
                    .as_ref()
                    .map(|v| v.as_slice())
                    .unwrap_or(nodes.as_slice());
                let initializer = declaration.and_then(|d| {
                    get_candidate_variable_declaration_initializer(dnodes, d)
                });
                // Given 'const x = obj.kind', allow 'x' as an alias for
                // 'obj.kind'
                if let Some(initializer) = initializer {
                    if ast::is_access_expression(&dnodes[initializer])
                        && dnodes[initializer].expression().is_some_and(|e| {
                            self.is_matching_reference(dnodes, reference, e)
                        })
                    {
                        return Some(initializer);
                    }
                }
                // Given 'const { kind: x } = obj', allow 'x' as an alias for
                // 'obj.kind'
                if let Some(declaration) = declaration {
                    if ast::is_binding_element(&dnodes[declaration])
                        && dnodes[declaration].initializer().is_none()
                    {
                        let grand_parent = dnodes[declaration].parent.and_then(|p| dnodes[p].parent);
                        let initializer = grand_parent.and_then(|gp| {
                            get_candidate_variable_declaration_initializer(dnodes, gp)
                        });
                        if let Some(initializer) = initializer {
                            if (ast::is_identifier(&dnodes[initializer])
                                || ast::is_access_expression(&dnodes[initializer]))
                                && self.is_matching_reference(
                                    dnodes,
                                    reference,
                                    initializer,
                                )
                            {
                                return Some(declaration);
                            }
                        }
                    }
                }
            }
        }
        None
    }
}

/// `getCandidateVariableDeclarationInitializer` (flow.go).
fn get_candidate_variable_declaration_initializer(
    nodes: &[ast::Node],
    node: NodeId,
) -> Option<NodeId> {
    if ast::is_variable_declaration(&nodes[node]) && nodes[node].type_().is_none() {
        if let Some(initializer) = nodes[node].initializer() {
            return Some(ast::skip_parentheses(initializer, nodes));
        }
    }
    None
}

/// `var nonDottedNameCacheKey` (flow.go) — `CacheHashKey(xxh3.HashString128("?"))`.
pub static NON_DOTTED_NAME_CACHE_KEY: LazyLock<CacheHashKey> =
    LazyLock::new(|| hash_string_128("?"));

impl Checker {
    /// `(c *Checker) getEvolvingArrayType` (flow.go). An evolving array type
    /// tracks the element types that have so far been seen in an
    /// 'x.push(value)' or 'x[n] = value' operation along the control flow
    /// graph. Evolving array types are ultimately converted into manifest
    /// array types (using getFinalArrayType) and never escape the
    /// getFlowTypeOfReference function.
    pub(crate) fn get_evolving_array_type(&mut self, element_type: TypeId) -> TypeId {
        let key = CachedTypeKey {
            kind: CachedTypeKind::EvolvingArrayType,
            type_id: element_type,
        };
        if let Some(&result) = self.cached_types.get(&key) {
            return result;
        }
        let result = self.new_object_type(ObjectFlags::EVOLVING_ARRAY, None);
        if let TypeData::EvolvingArray(d) = &mut self.types_handle().get_mut(result).data {
            d.element_type = Some(element_type);
        }
        self.cached_types.insert(key, result);
        result
    }

    /// `(c *Checker) getElementTypeOfEvolvingArrayType` (flow.go).
    pub(crate) fn get_element_type_of_evolving_array_type(&mut self, t: TypeId) -> TypeId {
        if self
            .types_handle()
            .get(t)
            .object_flags
            .intersects(ObjectFlags::EVOLVING_ARRAY)
        {
            return self
                .types_handle()
                .get(t)
                .as_evolving_array_type()
                .element_type
                .unwrap_or(self.never_type);
        }
        self.never_type
    }

    /// `(c *Checker) isEvolvingArrayOperationTarget` (flow.go). Return true if
    /// the given node is 'x' in an 'x.length', 'x.push(value)',
    /// 'x.unshift(value)' or 'x[n] = value' operation, where 'n' is an
    /// expression of type any, undefined, or a number-like type.
    pub(crate) fn is_evolving_array_operation_target(
        &mut self,
        nodes: &[ast::Node],
        node: NodeId,
    ) -> bool {
        let root = self.get_reference_root(nodes, node);
        let parent = nodes[root].parent;
        let Some(parent) = parent else {
            return false;
        };
        let is_length_push_or_unshift = ast::is_property_access_expression(&nodes[parent])
            && (nodes[parent]
                .name()
                .is_some_and(|n| nodes[n].text(nodes) == "length")
                || nodes[parent].parent.is_some_and(|pp| {
                    ast::is_call_expression(&nodes[pp])
                        && nodes[parent].name().is_some_and(|n| {
                            ast::is_identifier(&nodes[n])
                                && ast::is_push_or_unshift_identifier(&nodes[n], nodes)
                        })
                }));
        let is_element_assignment = ast::is_element_access_expression(&nodes[parent])
            && nodes[parent].expression() == Some(root)
            && nodes[parent].parent.is_some_and(|pp| {
                ast::is_binary_expression(&nodes[pp]) && {
                    let e = nodes[pp].as_binary_expression();
                    e.operator_token
                        .is_some_and(|op| nodes[op].kind == Kind::EqualsToken)
                        && e.left == Some(parent)
                        && !ast::is_assignment_target(pp, nodes)
                }
            })
            && {
                let argument = nodes[parent]
                    .as_element_access_expression()
                    .argument_expression;
                argument.is_some_and(|a| {
                    let t = self.get_type_of_expression(a);
                    self.is_type_assignable_to_kind(t, TypeFlags::NUMBER_LIKE)
                })
            };
        is_length_push_or_unshift || is_element_assignment
    }

    /// `(c *Checker) addEvolvingArrayElementType` (flow.go). When adding
    /// evolving array element types we do not perform subtype reduction.
    /// Instead, we defer subtype reduction until the evolving array type is
    /// finalized into a manifest array type.
    pub(crate) fn add_evolving_array_element_type(
        &mut self,
        evolving_array_type: TypeId,
        node: NodeId,
    ) -> TypeId {
        let cf_type = self.get_context_free_type_of_expression(node);
        let base = self.get_base_type_of_literal_type(cf_type);
        let new_element_type = self.get_regular_type_of_object_literal(base);
        let element_type = self.types.get_ref(evolving_array_type)
            .as_evolving_array_type()
            .element_type
            .unwrap_or(self.never_type);
        if self.is_type_subset_of(new_element_type, element_type) {
            return evolving_array_type;
        }
        let union = self.get_union_type(&[element_type, new_element_type]);
        self.get_evolving_array_type(union)
    }

    /// `(c *Checker) finalizeEvolvingArrayType` (flow.go).
    pub(crate) fn finalize_evolving_array_type(&mut self, t: TypeId) -> TypeId {
        if self
            .types_handle()
            .get(t)
            .object_flags
            .intersects(ObjectFlags::EVOLVING_ARRAY)
        {
            return self.get_final_array_type(t);
        }
        t
    }

    /// `(c *Checker) getFinalArrayType` (flow.go).
    pub(crate) fn get_final_array_type(&mut self, t: TypeId) -> TypeId {
        if self
            .types_handle()
            .get(t)
            .as_evolving_array_type()
            .final_array_type
            .is_none()
        {
            let element_type = self.types.get_ref(t)
                .as_evolving_array_type()
                .element_type
                .unwrap_or(self.never_type);
            let final_array_type = self.create_final_array_type(element_type);
            if let TypeData::EvolvingArray(d) = &mut self.types_handle().get_mut(t).data {
                d.final_array_type = Some(final_array_type);
            }
        }
        self.types_handle()
            .get(t)
            .as_evolving_array_type()
            .final_array_type
            .unwrap()
    }

    /// `(c *Checker) createFinalArrayType` (flow.go).
    pub(crate) fn create_final_array_type(&mut self, element_type: TypeId) -> TypeId {
        let __arena_flags = self.types.clone();
        let flags = __arena_flags.get(element_type).flags;
        if flags.intersects(TypeFlags::NEVER) {
            return self.auto_array_type;
        }
        if flags.intersects(TypeFlags::UNION) {
            let __arena_types = self.types.clone();
            let types = __arena_types.get(element_type).types_rc();
            let union = self.get_union_type_ex(&types, UnionReduction::Subtype, None, None);
            return self.create_array_type(union);
        }
        self.create_array_type(element_type)
    }

    /// `(c *Checker) reportFlowControlError` (flow.go).
    pub(crate) fn report_flow_control_error(&mut self, node: NodeId) {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let block = ast::find_ancestor(
            Some(node),
            &nodes,
            &mut |n: &ast::Node, nodes: &[ast::Node]| ast::is_function_or_module_block(n, nodes),
        );
        let source_file = ast::get_source_file_of_node(Some(node), &nodes);
        if let (Some(block), Some(source_file)) = (block, source_file) {
            let Some(list) = nodes[block].statement_list() else {
                return;
            };
            let span = tsc_scanner::scanner::get_range_of_token_at_position(
                nodes[source_file].as_source_file(),
                list.pos() as usize,
            );
            let diagnostic = ast::diagnostic::new_diagnostic(
                Some(ast::diagnostic::DiagnosticFile::from_node(source_file, &nodes)),
                span,
                &tsc_diagnostics::The_containing_function_or_module_body_is_too_large_for_control_flow_analysis,
                &[] as &[String],
            );
            self.add_diagnostic(&diagnostic);
        }
    }

    /// `(c *Checker) isMatchingReference` (flow.go).
    ///
    /// `nodes` is the flow-graph arena — either operand can be foreign to it
    /// (a pseudo-reference or a node resolved into another file during
    /// cross-file narrowing). Resolve each operand in its own arena and
    /// delegate to [`Checker::is_matching_reference_ex`].
    pub(crate) fn is_matching_reference(
        &mut self,
        nodes: &[ast::Node],
        source: NodeId,
        target: NodeId,
    ) -> bool {
        let fi = nodes.first().map(|n| n.id.file_index());
        if Some(source.file_index()) == fi && Some(target.file_index()) == fi {
            return self.is_matching_reference_ex(nodes, source, nodes, target);
        }
        let snodes = (Some(source.file_index()) != fi).then(|| self.program_nodes(source));
        let tnodes = (Some(target.file_index()) != fi).then(|| self.program_nodes(target));
        self.is_matching_reference_ex(
            snodes.as_ref().map(|v| v.as_slice()).unwrap_or(nodes),
            source,
            tnodes.as_ref().map(|v| v.as_slice()).unwrap_or(nodes),
            target,
        )
    }

    /// Two-arena `isMatchingReference` worker — `source` is read in
    /// `snodes`, `target` in `tnodes` (AST children stay in their parent's
    /// arena). Go dereferences raw node pointers; arena ids need the split.
    fn is_matching_reference_ex(
        &mut self,
        snodes: &[ast::Node],
        source: NodeId,
        tnodes: &[ast::Node],
        target: NodeId,
    ) -> bool {
        match tnodes[target].kind {
            Kind::ParenthesizedExpression | Kind::NonNullExpression => {
                if let Some(e) = tnodes[target].expression() {
                    return self.is_matching_reference_ex(snodes, source, tnodes, e);
                }
            }
            Kind::BinaryExpression => {
                let e = tnodes[target].as_binary_expression();
                if ast::is_assignment_expression(&tnodes[target], tnodes, false)
                    && e.left
                        .is_some_and(|l| self.is_matching_reference_ex(snodes, source, tnodes, l))
                {
                    return true;
                }
                if e.operator_token
                    .is_some_and(|op| tnodes[op].kind == Kind::CommaToken)
                    && e.right
                        .is_some_and(|r| self.is_matching_reference_ex(snodes, source, tnodes, r))
                {
                    return true;
                }
                return false;
            }
            _ => {}
        }
        match snodes[source].kind {
            Kind::MetaProperty => {
                return ast::is_meta_property(&tnodes[target])
                    && snodes[source].as_meta_property().keyword_token
                        == tnodes[target].as_meta_property().keyword_token
                    && snodes[source]
                        .name()
                        .map(|n| snodes[n].text(snodes).into_owned())
                        == tnodes[target]
                            .name()
                            .map(|n| tnodes[n].text(tnodes).into_owned());
            }
            Kind::Identifier | Kind::PrivateIdentifier => {
                if ast::is_this_in_type_query(source, snodes) {
                    return tnodes[target].kind == Kind::ThisKeyword;
                }
                if ast::is_identifier(&tnodes[target]) {
                    return self.get_resolved_symbol(source) == self.get_resolved_symbol(target);
                }
                if ast::is_variable_declaration(&tnodes[target])
                    || ast::is_binding_element(&tnodes[target])
                {
                    let src_sym = self.get_resolved_symbol(source);
                    let export = self.get_export_symbol_of_value_symbol_if_exported(Some(src_sym));
                    return export == self.get_symbol_of_declaration(target);
                }
                return false;
            }
            Kind::ThisKeyword => return tnodes[target].kind == Kind::ThisKeyword,
            Kind::SuperKeyword => return tnodes[target].kind == Kind::SuperKeyword,
            Kind::NonNullExpression | Kind::ParenthesizedExpression | Kind::SatisfiesExpression => {
                if let Some(e) = snodes[source].expression() {
                    return self.is_matching_reference_ex(snodes, e, tnodes, target);
                }
            }
            Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
                let (source_property_name, ok) = self.get_accessed_property_name(snodes, source);
                if ok && ast::is_access_expression(&tnodes[target]) {
                    let (target_property_name, ok2) =
                        self.get_accessed_property_name(tnodes, target);
                    if ok2 && target_property_name == source_property_name {
                        let (se, te) = (snodes[source].expression(), tnodes[target].expression());
                        if let (Some(se), Some(te)) = (se, te) {
                            return self.is_matching_reference_ex(snodes, se, tnodes, te);
                        }
                        return false;
                    }
                    return false;
                }
                if ast::is_element_access_expression(&snodes[source])
                    && ast::is_element_access_expression(&tnodes[target])
                {
                    let source_arg = snodes[source]
                        .as_element_access_expression()
                        .argument_expression;
                    let target_arg = tnodes[target]
                        .as_element_access_expression()
                        .argument_expression;
                    if let (Some(source_arg), Some(target_arg)) = (source_arg, target_arg) {
                        if ast::is_identifier(&snodes[source_arg])
                            && ast::is_identifier(&tnodes[target_arg])
                        {
                            let symbol = self.get_resolved_symbol(source_arg);
                            if symbol == self.get_resolved_symbol(target_arg)
                                && (self.is_constant_variable(symbol)
                                    || (self.is_parameter_or_mutable_local_variable(symbol)
                                        && !self.is_symbol_assigned(symbol)))
                            {
                                let (se, te) =
                                    (snodes[source].expression(), tnodes[target].expression());
                                if let (Some(se), Some(te)) = (se, te) {
                                    return self.is_matching_reference_ex(snodes, se, tnodes, te);
                                }
                                return false;
                            }
                        }
                    }
                }
                return false;
            }
            Kind::QualifiedName => {
                if ast::is_access_expression(&tnodes[target]) {
                    let (target_property_name, ok) = self.get_accessed_property_name(tnodes, target);
                    if ok {
                        let q = snodes[source].as_qualified_name();
                        let right_text = q.right.map(|r| snodes[r].text(snodes).into_owned());
                        if right_text.as_deref() == Some(target_property_name.as_str()) {
                            if let (Some(l), Some(te)) = (q.left, tnodes[target].expression()) {
                                return self.is_matching_reference_ex(snodes, l, tnodes, te);
                            }
                        }
                    }
                    return false;
                }
                return false;
            }
            Kind::BinaryExpression => {
                let e = snodes[source].as_binary_expression();
                return e
                    .operator_token
                    .is_some_and(|op| snodes[op].kind == Kind::CommaToken)
                    && e.right
                        .is_some_and(|r| self.is_matching_reference_ex(snodes, r, tnodes, target));
            }
            _ => {}
        }
        false
    }

    /// `(c *Checker) getFlowReferenceKey` (flow.go). Return the flow cache key
    /// for a "dotted name" (i.e. a sequence of identifiers separated by dots).
    /// The key consists of the id of the symbol referenced by the leftmost
    /// identifier followed by zero or more property names separated by dots.
    /// The result is nonDottedNameCacheKey if the reference isn't a dotted
    /// name.
    pub(crate) fn get_flow_reference_key(&mut self, f: &mut FlowState) -> CacheHashKey {
        let mut b = KeyBuilder::default();
        if self.write_flow_cache_key(
            &mut b,
            f.reference(),
            f.declared_type(),
            f.initial_type(),
            f.flow_container,
        ) {
            return b.hash();
        }
        *NON_DOTTED_NAME_CACHE_KEY // Reference isn't a dotted name
    }

    /// `(c *Checker) writeFlowCacheKey` (flow.go).
    pub(crate) fn write_flow_cache_key(
        &mut self,
        b: &mut KeyBuilder,
        node: NodeId,
        declared_type: TypeId,
        initial_type: TypeId,
        flow_container: Option<NodeId>,
    ) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            Kind::Identifier | Kind::ThisKeyword => {
                if nodes[node].kind == Kind::Identifier && !ast::is_this_in_type_query(node, &nodes)
                {
                    let symbol = self.get_resolved_symbol(node);
                    if symbol == self.unknown_symbol {
                        return false;
                    }
                    b.write_symbol(symbol);
                }
                b.write_byte(b':');
                b.write_type(declared_type);
                if initial_type != declared_type {
                    b.write_byte(b'=');
                    b.write_type(initial_type);
                }
                if let Some(flow_container) = flow_container {
                    b.write_byte(b'@');
                    b.write_node(Some(flow_container));
                }
                true
            }
            Kind::NonNullExpression | Kind::ParenthesizedExpression => {
                let Some(e) = nodes[node].expression() else {
                    return false;
                };
                self.write_flow_cache_key(b, e, declared_type, initial_type, flow_container)
            }
            Kind::QualifiedName => {
                let q = nodes[node].as_qualified_name();
                let (left, right) = (q.left, q.right);
                let Some(left) = left else {
                    return false;
                };
                if !self.write_flow_cache_key(b, left, declared_type, initial_type, flow_container)
                {
                    return false;
                }
                b.write_byte(b'.');
                if let Some(right) = right {
                    b.write_string(&nodes[right].text(&nodes));
                }
                true
            }
            Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
                let (prop_name, ok) = self.get_accessed_property_name(&nodes, node);
                if ok {
                    let Some(e) = nodes[node].expression() else {
                        return false;
                    };
                    if !self.write_flow_cache_key(b, e, declared_type, initial_type, flow_container)
                    {
                        return false;
                    }
                    b.write_byte(b'.');
                    b.write_string(&prop_name);
                    return true;
                }
                if ast::is_element_access_expression(&nodes[node]) {
                    let arg = nodes[node]
                        .as_element_access_expression()
                        .argument_expression;
                    if arg.is_some_and(|a| ast::is_identifier(&nodes[a])) {
                        let symbol = self.get_resolved_symbol(arg.unwrap());
                        if self.is_constant_variable(symbol)
                            || (self.is_parameter_or_mutable_local_variable(symbol)
                                && !self.is_symbol_assigned(symbol))
                        {
                            let Some(e) = nodes[node].expression() else {
                                return false;
                            };
                            if !self.write_flow_cache_key(
                                b,
                                e,
                                declared_type,
                                initial_type,
                                flow_container,
                            ) {
                                return false;
                            }
                            b.write_string(".@");
                            b.write_symbol(symbol);
                            return true;
                        }
                    }
                }
                false
            }
            Kind::ObjectBindingPattern
            | Kind::ArrayBindingPattern
            | Kind::FunctionDeclaration
            | Kind::FunctionExpression
            | Kind::ArrowFunction
            | Kind::MethodDeclaration => {
                b.write_node(Some(node));
                b.write_byte(b'#');
                b.write_type(declared_type);
                true
            }
            _ => false,
        }
    }

    /// `(c *Checker) getAccessedPropertyName` (flow.go).
    pub(crate) fn get_accessed_property_name(
        &mut self,
        nodes: &[ast::Node],
        access: NodeId,
    ) -> (String, bool) {
        // `access` can be foreign to `nodes` (a binding-element or parameter
        // candidate in the reference's file) — resolve it in its own arena.
        let __foreign;
        let nodes = if nodes.first().map(|n| n.id.file_index()) == Some(access.file_index()) {
            nodes
        } else {
            __foreign = self.program_nodes(access);
            __foreign.as_slice()
        };
        if ast::is_property_access_expression(&nodes[access]) {
            if let Some(name) = nodes[access].name() {
                return (nodes[name].text(nodes).into_owned(), true);
            }
            return (String::new(), false);
        }
        if ast::is_element_access_expression(&nodes[access]) {
            return self.try_get_element_access_expression_name(nodes, access);
        }
        if ast::is_binding_element(&nodes[access]) {
            return self.get_destructuring_property_name(nodes, access);
        }
        if ast::is_parameter_declaration(&nodes[access]) {
            let index = nodes[access]
                .parent
                .and_then(|p| {
                    nodes[p]
                        .parameters()
                        .map(|ps| ps.iter().position(|&x| x == access))
                })
                .flatten();
            if let Some(index) = index {
                return (index.to_string(), true);
            }
            return (String::new(), false);
        }
        (String::new(), false)
    }

    /// `(c *Checker) tryGetElementAccessExpressionName` (flow.go).
    pub(crate) fn try_get_element_access_expression_name(
        &mut self,
        nodes: &[ast::Node],
        node: NodeId,
    ) -> (String, bool) {
        let arg = nodes[node]
            .as_element_access_expression()
            .argument_expression;
        let Some(arg) = arg else {
            return (String::new(), false);
        };
        if ast::is_string_or_numeric_literal_like(&nodes[arg]) {
            return (nodes[arg].text(nodes).into_owned(), true);
        }
        if ast::is_entity_name_expression(&nodes[arg], nodes) {
            return self.try_get_name_from_entity_name_expression(nodes, arg);
        }
        (String::new(), false)
    }

    /// `(c *Checker) tryGetNameFromEntityNameExpression` (flow.go).
    pub(crate) fn try_get_name_from_entity_name_expression(
        &mut self,
        nodes: &[ast::Node],
        node: NodeId,
    ) -> (String, bool) {
        let Some(symbol) =
            self.resolve_entity_name(Some(node), ast::SymbolFlags::VALUE, true, false, None)
        else {
            return (String::new(), false);
        };
        if !(self.is_constant_variable(symbol)
            || self.symbol_arena.get_ref(symbol)
                .flags
                .intersects(ast::SymbolFlags::ENUM_MEMBER))
        {
            return (String::new(), false);
        }
        let Some(declaration) = self.symbol_arena.get_ref(symbol).value_declaration else {
            return (String::new(), false);
        };
        if let Some(t) = self.try_get_type_from_type_node(declaration) {
            if let (name, true) = try_get_name_from_type(&self.types, t) {
                return (name, true);
            }
        }
        // The declaration can live in another file's arena (e.g. `a.key`
        // resolving to a const in a.ts while `nodes` is b.ts's buffer) —
        // read it in its own arena (Go's pointers carry their arena).
        let __program = self.program.clone().expect("program");
        let decl_nodes = __program.nodes((declaration).file_index());
        // We exclude binding elements because their initializers don't solely
        // determine their types and resolving full types can cause
        // circularities (see https://github.com/microsoft/TypeScript/issues/63192).
        if crate::utilities::has_only_expression_initializer(&decl_nodes[declaration])
            && !ast::is_binding_element(&decl_nodes[declaration])
            && self.is_block_scoped_name_declared_before_use(declaration, node)
        {
            if let Some(initializer) = decl_nodes[declaration].initializer() {
                let initializer_type = self.get_type_of_expression(initializer);
                return try_get_name_from_type(&self.types, initializer_type);
            }
            if ast::is_enum_member(&decl_nodes[declaration]) {
                if let Some(name) = decl_nodes[declaration].name() {
                    let (text, ok) = ast::try_get_text_of_property_name(name, &decl_nodes);
                    return (text.unwrap_or_default(), ok);
                }
            }
        }
        (String::new(), false)
    }

    /// `(c *Checker) getDestructuringPropertyName` (flow.go).
    pub(crate) fn get_destructuring_property_name(
        &mut self,
        nodes: &[ast::Node],
        node: NodeId,
    ) -> (String, bool) {
        let Some(parent) = nodes[node].parent else {
            return (String::new(), false);
        };
        if ast::is_binding_element(&nodes[node]) && ast::is_object_binding_pattern(&nodes[parent]) {
            if let Some(name) = crate::utilities::get_binding_element_property_name(&nodes[node]) {
                return self.get_literal_property_name_text(nodes, name);
            }
            return (String::new(), false);
        }
        if ast::is_property_assignment(&nodes[node])
            || ast::is_shorthand_property_assignment(&nodes[node])
        {
            if let Some(name) = nodes[node].name() {
                return self.get_literal_property_name_text(nodes, name);
            }
            return (String::new(), false);
        }
        if ast::is_array_literal_expression(&nodes[parent])
            || ast::is_array_binding_pattern(&nodes[parent])
        {
            if let Some(index) = nodes[parent]
                .elements()
                .and_then(|es| es.iter().position(|&x| x == node))
            {
                return (index.to_string(), true);
            }
        }
        (String::new(), false)
    }

    /// `(c *Checker) getLiteralPropertyNameText` (flow.go).
    pub(crate) fn get_literal_property_name_text(
        &mut self,
        nodes: &[ast::Node],
        name: NodeId,
    ) -> (String, bool) {
        let _ = nodes;
        let t = self.get_literal_type_from_property_name(name);
        if self
            .types_handle()
            .get(t)
            .flags
            .intersects(TypeFlags::STRING_LITERAL | TypeFlags::NUMBER_LITERAL)
        {
            if let Some(v) = self.types_handle().get(t).as_literal_type().value.as_ref() {
                return (tsc_evaluator::any_to_string(v), true);
            }
        }
        (String::new(), false)
    }

    /// `(c *Checker) isConstantReference` (flow.go).
    ///
    /// `node` can be foreign to `nodes` (a pseudo-reference during
    /// cross-file narrowing) — resolve it in its own arena.
    pub(crate) fn is_constant_reference(&mut self, nodes: &[ast::Node], node: NodeId) -> bool {
        let __foreign;
        let nodes = if nodes.first().map(|n| n.id.file_index()) == Some(node.file_index()) {
            nodes
        } else {
            __foreign = self.program_nodes(node);
            __foreign.as_slice()
        };
        match nodes[node].kind {
            Kind::ThisKeyword => true,
            Kind::Identifier => {
                if ast::is_this_in_type_query(node, nodes) {
                    return false;
                }
                let symbol = self.get_resolved_symbol(node);
                if self.is_constant_variable(symbol)
                    || (self.is_parameter_or_mutable_local_variable(symbol)
                        && !self.is_symbol_assigned(symbol))
                {
                    return true;
                }
                self.symbol_arena.get_ref(symbol)
                    .value_declaration
                    .is_some_and(|d| {
                        let __program = self.program.clone().expect("program");
                        let decl_nodes = __program.nodes((d).file_index());
                        ast::is_function_expression(&decl_nodes[d])
                    })
            }
            Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
                // The resolvedSymbol property is initialized by
                // checkPropertyAccess or checkElementAccess before we get
                // here.
                if let Some(e) = nodes[node].expression() {
                    if self.is_constant_reference(nodes, e) {
                        if let Some(symbol) = self.get_resolved_symbol_or_nil(node) {
                            return self.is_readonly_symbol(symbol);
                        }
                    }
                }
                false
            }
            Kind::ObjectBindingPattern | Kind::ArrayBindingPattern => {
                let Some(parent) = nodes[node].parent else {
                    return false;
                };
                let root_declaration = ast::get_root_declaration(parent, nodes);
                if ast::is_parameter_declaration(&nodes[root_declaration])
                    || (ast::is_variable_declaration(&nodes[root_declaration])
                        && nodes[root_declaration]
                            .parent
                            .is_some_and(|p| ast::is_catch_clause(&nodes[p])))
                {
                    return !self.is_some_symbol_assigned(root_declaration);
                }
                ast::is_variable_declaration(&nodes[root_declaration])
                    && ast::is_var_const_like(root_declaration, nodes)
            }
            _ => false,
        }
    }

    /// `(c *Checker) containsMatchingReference` (flow.go).
    ///
    /// `source` can be foreign to `nodes` (a pseudo-reference during
    /// cross-file narrowing) — resolve the walk in its own arena.
    /// `is_matching_reference` re-resolves `target` per-operand.
    pub(crate) fn contains_matching_reference(
        &mut self,
        nodes: &[ast::Node],
        source: NodeId,
        target: NodeId,
    ) -> bool {
        let __foreign;
        let snodes = if nodes.first().map(|n| n.id.file_index()) == Some(source.file_index()) {
            nodes
        } else {
            __foreign = self.program_nodes(source);
            __foreign.as_slice()
        };
        let mut source = source;
        while ast::is_access_expression(&snodes[source]) {
            let Some(e) = snodes[source].expression() else {
                return false;
            };
            source = e;
            if self.is_matching_reference(snodes, source, target) {
                return true;
            }
        }
        false
    }

    /// `(c *Checker) optionalChainContainsReference` (flow.go).
    pub(crate) fn optional_chain_contains_reference(
        &mut self,
        nodes: &[ast::Node],
        source: NodeId,
        target: NodeId,
    ) -> bool {
        let mut source = source;
        while ast::is_optional_chain(&nodes[source]) {
            let Some(e) = nodes[source].expression() else {
                return false;
            };
            source = e;
            if self.is_matching_reference(nodes, source, target) {
                return true;
            }
        }
        false
    }

    /// `(c *Checker) getReferenceCandidate` (flow.go).
    pub(crate) fn get_reference_candidate(&mut self, nodes: &[ast::Node], node: NodeId) -> NodeId {
        match nodes[node].kind {
            Kind::ParenthesizedExpression => {
                if let Some(e) = nodes[node].expression() {
                    return self.get_reference_candidate(nodes, e);
                }
            }
            Kind::BinaryExpression => {
                let e = nodes[node].as_binary_expression();
                match e.operator_token.map(|op| nodes[op].kind) {
                    Some(Kind::EqualsToken)
                    | Some(Kind::BarBarEqualsToken)
                    | Some(Kind::AmpersandAmpersandEqualsToken)
                    | Some(Kind::QuestionQuestionEqualsToken) => {
                        if let Some(l) = e.left {
                            return self.get_reference_candidate(nodes, l);
                        }
                    }
                    Some(Kind::CommaToken) => {
                        if let Some(r) = e.right {
                            return self.get_reference_candidate(nodes, r);
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
        node
    }

    /// `(c *Checker) getReferenceRoot` (flow.go).
    pub(crate) fn get_reference_root(&mut self, nodes: &[ast::Node], node: NodeId) -> NodeId {
        let Some(parent) = nodes[node].parent else {
            return node;
        };
        if ast::is_parenthesized_expression(&nodes[parent])
            || (ast::is_binary_expression(&nodes[parent]) && {
                let e = nodes[parent].as_binary_expression();
                e.operator_token
                    .is_some_and(|op| nodes[op].kind == Kind::EqualsToken)
                    && e.left == Some(node)
            })
            || (ast::is_binary_expression(&nodes[parent]) && {
                let e = nodes[parent].as_binary_expression();
                e.operator_token
                    .is_some_and(|op| nodes[op].kind == Kind::CommaToken)
                    && e.right == Some(node)
            })
        {
            return self.get_reference_root(nodes, parent);
        }
        node
    }

    /// `(c *Checker) hasMatchingArgument` (flow.go).
    pub(crate) fn has_matching_argument(
        &mut self,
        nodes: &[ast::Node],
        expression: NodeId,
        reference: NodeId,
    ) -> bool {
        if let Some(args) = nodes[expression].arguments() {
            for &argument in args {
                if self.is_or_contains_matching_reference(nodes, reference, argument)
                    || self.optional_chain_contains_reference(nodes, argument, reference)
                {
                    return true;
                }
            }
        }
        if let Some(e) = nodes[expression].expression() {
            if ast::is_property_access_expression(&nodes[e]) {
                if let Some(ee) = nodes[e].expression() {
                    if self.is_or_contains_matching_reference(nodes, reference, ee) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// `(c *Checker) isOrContainsMatchingReference` (flow.go).
    pub(crate) fn is_or_contains_matching_reference(
        &mut self,
        nodes: &[ast::Node],
        source: NodeId,
        target: NodeId,
    ) -> bool {
        self.is_matching_reference(nodes, source, target)
            || self.contains_matching_reference(nodes, source, target)
    }

    /// `(c *Checker) replacePrimitivesWithLiterals` (flow.go). Return a new
    /// type in which occurrences of the string, number and bigint primitives
    /// and placeholder template literal types in typeWithPrimitives have been
    /// replaced with occurrences of compatible and more specific types from
    /// typeWithLiterals. This is essentially a limited form of intersection
    /// between the two types. We avoid a true intersection because it is more
    /// costly and, when applied to union types, generates a large number of
    /// types we don't actually care about.
    pub(crate) fn replace_primitives_with_literals(
        &mut self,
        type_with_primitives: TypeId,
        type_with_literals: TypeId,
    ) -> TypeId {
        if self.maybe_type_of_kind(
            type_with_primitives,
            TypeFlags::STRING
                | TypeFlags::TEMPLATE_LITERAL
                | TypeFlags::NUMBER
                | TypeFlags::BIG_INT,
        ) && self.maybe_type_of_kind(
            type_with_literals,
            TypeFlags::STRING_LITERAL
                | TypeFlags::TEMPLATE_LITERAL
                | TypeFlags::STRING_MAPPING
                | TypeFlags::NUMBER_LITERAL
                | TypeFlags::BIG_INT_LITERAL,
        ) {
            return self.map_type(
                type_with_primitives,
                Rc::new(move |c: &mut Checker, t: TypeId| {
                    let __arena_flags = c.types.clone();
                    let flags = __arena_flags.get(t).flags;
                    if flags.intersects(TypeFlags::STRING) {
                        return c.extract_types_of_kind(
                            type_with_literals,
                            TypeFlags::STRING
                                | TypeFlags::STRING_LITERAL
                                | TypeFlags::TEMPLATE_LITERAL
                                | TypeFlags::STRING_MAPPING,
                        );
                    }
                    if c.is_pattern_literal_type(t)
                        && !c.maybe_type_of_kind(
                            type_with_literals,
                            TypeFlags::STRING
                                | TypeFlags::TEMPLATE_LITERAL
                                | TypeFlags::STRING_MAPPING,
                        )
                    {
                        return c
                            .extract_types_of_kind(type_with_literals, TypeFlags::STRING_LITERAL);
                    }
                    if flags.intersects(TypeFlags::NUMBER) {
                        return c.extract_types_of_kind(
                            type_with_literals,
                            TypeFlags::NUMBER | TypeFlags::NUMBER_LITERAL,
                        );
                    }
                    if flags.intersects(TypeFlags::BIG_INT) {
                        return c.extract_types_of_kind(
                            type_with_literals,
                            TypeFlags::BIG_INT | TypeFlags::BIG_INT_LITERAL,
                        );
                    }
                    t
                }),
            );
        }
        type_with_primitives
    }
}

/// `isEvolvingArrayTypeList` (flow.go).
fn is_evolving_array_type_list(types_arena: &TypeArena, types: &[TypeId]) -> bool {
    let mut has_evolving_array_type = false;
    for &t in types {
        if !types_arena.get(t).flags.intersects(TypeFlags::NEVER) {
            if !types_arena
                .get(t)
                .object_flags
                .intersects(ObjectFlags::EVOLVING_ARRAY)
            {
                return false;
            }
            has_evolving_array_type = true;
        }
    }
    has_evolving_array_type
}

/// `tryGetNameFromType` (flow.go).
fn try_get_name_from_type(types: &TypeArena, t: TypeId) -> (String, bool) {
    let ty = types.get(t);
    if ty.flags.intersects(TypeFlags::UNIQUE_ES_SYMBOL) {
        let name = ty.as_unique_es_symbol_type().name.clone();
        if !name.is_empty() {
            return (name, true);
        }
        return (String::new(), false);
    }
    if ty.flags.intersects(TypeFlags::STRING_OR_NUMBER_LITERAL) {
        if let Some(v) = ty.as_literal_type().value.as_ref() {
            return (tsc_evaluator::any_to_string(v), true);
        }
    }
    (String::new(), false)
}

/// `isCoercibleUnderDoubleEquals` (flow.go).
fn is_coercible_under_double_equals(types: &TypeArena, source: TypeId, target: TypeId) -> bool {
    types
        .get(source)
        .flags
        .intersects(TypeFlags::NUMBER | TypeFlags::STRING | TypeFlags::BOOLEAN_LITERAL)
        && types
            .get(target)
            .flags
            .intersects(TypeFlags::NUMBER | TypeFlags::STRING | TypeFlags::BOOLEAN)
}

impl Checker {
    /// `(c *Checker) isExhaustiveSwitchStatement` (flow.go).
    pub(crate) fn is_exhaustive_switch_statement(&mut self, node: NodeId) -> bool {
        let state = self.switch_statement_links.get(node).exhaustive_state;
        match state {
            ExhaustiveState::Unknown => {
                // Indicate resolution is in process
                self.switch_statement_links.get(node).exhaustive_state = ExhaustiveState::Computing;
                let is_exhaustive = self.compute_exhaustive_switch_statement(node);
                let links = self.switch_statement_links.get(node);
                if links.exhaustive_state == ExhaustiveState::Computing {
                    links.exhaustive_state = tsc_core::core::if_else(
                        is_exhaustive,
                        ExhaustiveState::True,
                        ExhaustiveState::False,
                    );
                }
            }
            ExhaustiveState::Computing => {
                // Resolve circularity to false
                self.switch_statement_links.get(node).exhaustive_state = ExhaustiveState::False;
            }
            _ => {}
        }
        self.switch_statement_links.get(node).exhaustive_state == ExhaustiveState::True
    }

    /// `(c *Checker) computeExhaustiveSwitchStatement` (flow.go).
    pub(crate) fn compute_exhaustive_switch_statement(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let expression = nodes[node].expression();
        if expression.is_some_and(|e| ast::is_type_of_expression(&nodes[e])) {
            let type_of_expr = expression.unwrap();
            let Some(witnesses) = self.get_switch_clause_type_of_witnesses(node) else {
                return false;
            };
            let operand = nodes[type_of_expr].expression().unwrap();
            let operand_type = self.check_expression_cached(operand);
            let operand_constraint = self.get_base_constraint_or_type(operand_type);
            // Get the not-equal flags for all handled cases.
            let not_equal_facts = self.get_not_equal_facts_from_typeof_switch(0, 0, &witnesses);
            if self
                .types_handle()
                .get(operand_constraint)
                .flags
                .intersects(TypeFlags::ANY_OR_UNKNOWN)
            {
                // We special case the top types to be exhaustive when all
                // cases are handled.
                return (TypeFacts::ALL_TYPEOF_NE & not_equal_facts) == TypeFacts::ALL_TYPEOF_NE;
            }
            // A missing not-equal flag indicates that the type wasn't handled
            // by some case.
            return !crate::checker_d::some_type(
                self,
                operand_constraint,
                |c: &mut Checker, t: TypeId| {
                    c.get_type_facts(t, not_equal_facts) == not_equal_facts
                },
            );
        }
        let Some(expression) = expression else {
            return false;
        };
        let expression_type = self.check_expression_cached(expression);
        let t = self.get_base_constraint_or_type(expression_type);
        if !crate::checker_d::is_literal_type(&self.types, t) {
            return false;
        }
        let switch_types = self.get_switch_clause_types(node);
        if switch_types.is_empty()
            || switch_types
                .iter()
                .any(|&t| crate::checker_d::is_neither_unit_type_nor_never(&self.types, t))
        {
            return false;
        }
        let mapped = self.map_type(
            t,
            Rc::new(|c: &mut Checker, t: TypeId| c.get_regular_type_of_literal_type(t)),
        );
        self.each_type_contained_in(mapped, &switch_types)
    }

    /// `(c *Checker) eachTypeContainedIn` (flow.go).
    pub(crate) fn each_type_contained_in(&mut self, source: TypeId, types: &[TypeId]) -> bool {
        if self
            .types_handle()
            .get(source)
            .flags
            .intersects(TypeFlags::UNION)
        {
            return !self
                .types_handle()
                .get(source)
                .types()
                .iter()
                .any(|t| !types.contains(t));
        }
        types.contains(&source)
    }

    /// `(c *Checker) getSwitchClauseTypeOfWitnesses` (flow.go). Get the type
    /// names from all cases in a switch on `typeof`. The default clause
    /// and/or duplicate type names are represented as empty strings. Return
    /// nil if one or more case clause expressions are not string literals.
    pub(crate) fn get_switch_clause_type_of_witnesses(
        &mut self,
        node: NodeId,
    ) -> Option<Vec<String>> {
        if !self.switch_statement_links.get(node).witnesses_computed {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let clauses: Vec<NodeId> = nodes[node]
                .as_switch_statement()
                .case_block
                .map(|cb| {
                    nodes[cb]
                        .as_case_block()
                        .clauses
                        .as_ref()
                        .map(|c| c.nodes().to_vec())
                        .unwrap_or_default()
                })
                .unwrap_or_default();
            let mut witnesses: Option<Vec<String>> = Some(vec![String::new(); clauses.len()]);
            for (i, &clause) in clauses.iter().enumerate() {
                if nodes[clause].kind == Kind::CaseClause {
                    let Some(expr) = nodes[clause].expression() else {
                        witnesses = None;
                        break;
                    };
                    if !ast::is_string_literal_like(&nodes[expr]) {
                        witnesses = None;
                        break;
                    }
                    let text = nodes[expr].text(&nodes).into_owned();
                    if !witnesses.as_ref().unwrap().contains(&text) {
                        witnesses.as_mut().unwrap()[i] = text;
                    }
                }
            }
            let links = self.switch_statement_links.get(node);
            links.witnesses = witnesses;
            links.witnesses_computed = true;
        }
        self.switch_statement_links.get(node).witnesses.clone()
    }

    /// `(c *Checker) getNotEqualFactsFromTypeofSwitch` (flow.go). Return the
    /// combined not-equal type facts for all cases except those between the
    /// start and end indices.
    pub(crate) fn get_not_equal_facts_from_typeof_switch(
        &mut self,
        start: i32,
        end: i32,
        witnesses: &[String],
    ) -> TypeFacts {
        let mut facts = TypeFacts::NONE;
        for (i, witness) in witnesses.iter().enumerate() {
            if (i < start as usize || i >= end as usize) && !witness.is_empty() {
                facts |= typeof_ne_facts(witness).unwrap_or(TypeFacts::TYPEOF_NE_HOST_OBJECT);
            }
        }
        facts
    }

    /// `(c *Checker) getSwitchClauseTypes` (flow.go).
    pub(crate) fn get_switch_clause_types(&mut self, node: NodeId) -> Vec<TypeId> {
        if !self.switch_statement_links.get(node).switch_types_computed {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            let clauses: Vec<NodeId> = nodes[node]
                .as_switch_statement()
                .case_block
                .map(|cb| {
                    nodes[cb]
                        .as_case_block()
                        .clauses
                        .as_ref()
                        .map(|c| c.nodes().to_vec())
                        .unwrap_or_default()
                })
                .unwrap_or_default();
            let types: Vec<TypeId> = clauses
                .iter()
                .map(|&clause| self.get_type_of_switch_clause(&nodes, clause))
                .collect();
            let links = self.switch_statement_links.get(node);
            links.switch_types = types.into();
            links.switch_types_computed = true;
        }
        self.switch_statement_links.get(node).switch_types.to_vec()
    }

    /// `(c *Checker) getTypeOfSwitchClause` (flow.go).
    pub(crate) fn get_type_of_switch_clause(
        &mut self,
        nodes: &[ast::Node],
        clause: NodeId,
    ) -> TypeId {
        if nodes[clause].kind == Kind::CaseClause {
            if let Some(expr) = nodes[clause].expression() {
                let t = self.get_type_of_expression(expr);
                return self.get_regular_type_of_literal_type(t);
            }
        }
        self.never_type
    }

    /// `(c *Checker) getEffectsSignature` (flow.go).
    pub(crate) fn get_effects_signature(&mut self, node: NodeId) -> Option<SignatureId> {
        let mut signature = self.signature_links.get(node).effects_signature;
        if signature.is_none() {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((node).file_index());
            // A call expression parented by an expression statement is a
            // potential assertion. Other call expressions are potential type
            // predicate function calls. In order to avoid triggering
            // circularities in control flow analysis, we use
            // getTypeOfDottedName when resolving the call target expression
            // of an assertion.
            let mut func_type: Option<TypeId> = None;
            if ast::is_binary_expression(&nodes[node]) {
                if let Some(right) = nodes[node].as_binary_expression().right {
                    let right_type = self.check_non_null_expression(right);
                    func_type = self.get_symbol_has_instance_method_of_object_type(right_type);
                }
            } else if nodes[node]
                .parent
                .is_some_and(|p| ast::is_expression_statement(&nodes[p]))
            {
                func_type = nodes[node]
                    .expression()
                    .and_then(|e| self.get_type_of_dotted_name(e, None));
            } else if nodes[node]
                .expression()
                .is_some_and(|e| nodes[e].kind != Kind::SuperKeyword)
            {
                let e = nodes[node].expression().unwrap();
                if ast::is_optional_chain(&nodes[node]) {
                    let t = self.check_expression(e);
                    let optional = self.get_optional_expression_type(t, e);
                    func_type = Some(self.check_non_null_type(optional, e));
                } else {
                    func_type = Some(self.check_non_null_expression(e));
                }
            }
            let apparent_type = func_type.map(|t| self.get_apparent_type(t));
            let signatures = self.get_signatures_of_type(
                apparent_type.unwrap_or(self.unknown_type),
                SignatureKind::Call,
            );
            if signatures.len() == 1
                && self
                    .signature_arena
                    .get(signatures[0])
                    .type_parameters
                    .is_empty()
            {
                signature = Some(signatures[0]);
            } else if signatures
                .iter()
                .any(|&sig| self.has_type_predicate_or_never_return_type(sig))
            {
                signature = self.get_resolved_signature(node, None, CheckMode::NORMAL);
            }
            if !signature.is_some_and(|sig| self.has_type_predicate_or_never_return_type(sig)) {
                signature = Some(self.unknown_signature);
            }
            self.signature_links.get(node).effects_signature = signature;
        }
        if signature == Some(self.unknown_signature) {
            return None;
        }
        signature
    }

    /// `(c *Checker) getSymbolHasInstanceMethodOfObjectType` (flow.go). Get
    /// the type of the `[Symbol.hasInstance]` method of an object type.
    pub(crate) fn get_symbol_has_instance_method_of_object_type(
        &mut self,
        t: TypeId,
    ) -> Option<TypeId> {
        let has_instance_property_name =
            self.get_property_name_for_known_symbol_name("hasInstance");
        if self.all_types_assignable_to_kind(t, TypeFlags::NON_PRIMITIVE) {
            if let Some(has_instance_property) =
                self.get_property_of_type(t, &has_instance_property_name)
            {
                let has_instance_property_type = self.get_type_of_symbol(has_instance_property);
                if !self
                    .get_signatures_of_type(has_instance_property_type, SignatureKind::Call)
                    .is_empty()
                {
                    return Some(has_instance_property_type);
                }
            }
        }
        None
    }

    /// `(c *Checker) getPropertyNameForKnownSymbolName` (flow.go).
    pub(crate) fn get_property_name_for_known_symbol_name(&mut self, symbol_name: &str) -> String {
        let ctor_symbol = {
            let thunk = self
                .get_global_es_symbol_constructor_symbol_or_nil
                .clone()
                .expect("getGlobalESSymbolConstructorSymbolOrNil");
            thunk(self)
        };
        if let Some(ctor_symbol) = ctor_symbol {
            let ctor_type = self.get_type_of_symbol(ctor_symbol);
            if let Some(unique_type) = self.get_type_of_property_of_type(ctor_type, symbol_name) {
                if crate::utilities::is_type_usable_as_property_name(&self.types, unique_type) {
                    return crate::utilities::get_property_name_from_type(&self.types, unique_type);
                }
            }
        }
        format!("{}@{symbol_name}", ast::symbol::INTERNAL_SYMBOL_NAME_PREFIX)
    }

    /// `(c *Checker) getTypeOfDottedName` (flow.go). We require the dotted
    /// function name in an assertion expression to be comprised of
    /// identifiers that reference function, method, class or value module
    /// symbols; or variable, property or parameter symbols with declarations
    /// that have explicit type annotations. Such references are resolvable
    /// with no possibility of triggering circularities in control flow
    /// analysis.
    pub(crate) fn get_type_of_dotted_name(
        &mut self,
        node: NodeId,
        diagnostic: Option<DiagnosticRef>,
    ) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if nodes[node]
            .flags
            .intersects(ast::NodeFlags::IN_WITH_STATEMENT)
        {
            return None;
        }
        match nodes[node].kind {
            Kind::Identifier => {
                let resolved = self.get_resolved_symbol(node);
                let symbol = self
                    .get_export_symbol_of_value_symbol_if_exported(Some(resolved))
                    .expect("exported symbol");
                self.get_explicit_type_of_symbol(symbol, diagnostic)
            }
            Kind::ThisKeyword => self.get_explicit_this_type(node),
            Kind::SuperKeyword => Some(self.check_super_expression(node)),
            Kind::PropertyAccessExpression => {
                let t = nodes[node]
                    .expression()
                    .and_then(|e| self.get_type_of_dotted_name(e, diagnostic.clone()));
                if let Some(t) = t {
                    let name = nodes[node].name();
                    let prop = if let Some(name) = name {
                        if ast::is_private_identifier(&nodes[name]) {
                            let __arena_t_symbol = self.types.clone();
                            let t_symbol = __arena_t_symbol.get(t).symbol;
                            t_symbol.and_then(|symbol| {
                                let key =
                                    tsc_binder::binder::get_symbol_name_for_private_identifier(
                                        symbol,
                                        &nodes[name].text(&nodes),
                                    );
                                self.get_property_of_type(t, &key)
                            })
                        } else {
                            let text = nodes[name].text(&nodes).into_owned();
                            self.get_property_of_type(t, &text)
                        }
                    } else {
                        None
                    };
                    if let Some(prop) = prop {
                        return self.get_explicit_type_of_symbol(prop, diagnostic);
                    }
                }
                None
            }
            Kind::ParenthesizedExpression => nodes[node]
                .expression()
                .and_then(|e| self.get_type_of_dotted_name(e, diagnostic)),
            _ => None,
        }
    }

    /// `(c *Checker) getExplicitTypeOfSymbol` (flow.go).
    pub(crate) fn get_explicit_type_of_symbol(
        &mut self,
        symbol: SymbolId,
        diagnostic: Option<DiagnosticRef>,
    ) -> Option<TypeId> {
        let symbol = self.resolve_symbol(symbol);
        if self.resolving_explicit_type_of_symbol.has(&symbol) {
            return None;
        }
        self.resolving_explicit_type_of_symbol.add(symbol);
        let result = self.get_explicit_type_of_symbol_worker(symbol, diagnostic);
        self.resolving_explicit_type_of_symbol.delete(&symbol);
        result
    }

    /// `getExplicitTypeOfSymbol` continuation (the Go function's `defer`-less
    /// body — kept separate so the `resolvingExplicitTypeOfSymbol` remove is
    /// unconditional, like Go's `defer`).
    fn get_explicit_type_of_symbol_worker(
        &mut self,
        symbol: SymbolId,
        diagnostic: Option<DiagnosticRef>,
    ) -> Option<TypeId> {
        let symbol_flags = self.symbol_arena.get_ref(symbol).flags;
        if symbol_flags.intersects(
            ast::SymbolFlags::FUNCTION
                | ast::SymbolFlags::METHOD
                | ast::SymbolFlags::CLASS
                | ast::SymbolFlags::VALUE_MODULE,
        ) {
            return Some(self.get_type_of_symbol(symbol));
        }
        if symbol_flags.intersects(ast::SymbolFlags::VARIABLE | ast::SymbolFlags::PROPERTY) {
            if self.symbol_arena.get_ref(symbol)
                .check_flags
                .intersects(CheckFlags::MAPPED)
            {
                let origin = self.mapped_symbol_links.get(symbol).synthetic_origin;
                if let Some(origin) = origin {
                    if self
                        .get_explicit_type_of_symbol(origin, diagnostic.clone())
                        .is_some()
                    {
                        return Some(self.get_type_of_symbol(symbol));
                    }
                }
            }
            let declaration = self.symbol_arena.get_ref(symbol).value_declaration;
            if let Some(declaration) = declaration {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((declaration).file_index());
                if self.is_declaration_with_explicit_type_annotation(&nodes, declaration) {
                    return Some(self.get_type_of_symbol(symbol));
                }
                if ast::is_variable_declaration(&nodes[declaration])
                    && nodes[declaration]
                        .parent
                        .and_then(|p| nodes[p].parent)
                        .is_some_and(|gp| ast::is_for_of_statement(&nodes[gp]))
                {
                    let statement = nodes[declaration]
                        .parent
                        .and_then(|p| nodes[p].parent)
                        .unwrap();
                    let expression_type = nodes[statement]
                        .expression()
                        .and_then(|e| self.get_type_of_dotted_name(e, None));
                    if let Some(expression_type) = expression_type {
                        let use_ = if nodes[statement]
                            .as_for_in_or_of_statement()
                            .await_modifier
                            .is_some()
                        {
                            IterationUse::FOR_AWAIT_OF
                        } else {
                            IterationUse::FOR_OF
                        };
                        return Some(self.check_iterated_type_or_element_type(
                            use_,
                            expression_type,
                            self.undefined_type,
                            None,
                        ));
                    }
                }
                if let Some(diagnostic) = diagnostic {
                    let sym_str = self.symbol_to_string(symbol);
                    let related = self.new_diagnostic_for_node(
                        Some(declaration),
                        &tsc_diagnostics::X_0_needs_an_explicit_type_annotation,
                        &[sym_str],
                    );
                    ast::diagnostic::lock_diagnostic(&diagnostic).add_related_info(Some(related));
                }
            }
        }
        None
    }

    /// `(c *Checker) isDeclarationWithExplicitTypeAnnotation` (flow.go).
    pub(crate) fn is_declaration_with_explicit_type_annotation(
        &mut self,
        nodes: &[ast::Node],
        node: NodeId,
    ) -> bool {
        (ast::is_variable_declaration(&nodes[node])
            || ast::is_property_declaration(&nodes[node])
            || ast::is_property_signature_declaration(&nodes[node])
            || ast::is_parameter_declaration(&nodes[node]))
            && nodes[node].type_().is_some()
            || self.is_expando_property_function_with_return_type_annotation(nodes, node)
    }

    /// `(c *Checker) isExpandoPropertyFunctionWithReturnTypeAnnotation` (flow.go).
    pub(crate) fn is_expando_property_function_with_return_type_annotation(
        &mut self,
        nodes: &[ast::Node],
        node: NodeId,
    ) -> bool {
        if ast::is_binary_expression(&nodes[node]) {
            if let Some(expr) = nodes[node].as_binary_expression().right {
                if ast::is_function_like(Some(expr), nodes) && nodes[expr].type_().is_some() {
                    return true;
                }
            }
        }
        false
    }

    /// `(c *Checker) hasTypePredicateOrNeverReturnType` (flow.go).
    pub(crate) fn has_type_predicate_or_never_return_type(&mut self, sig: SignatureId) -> bool {
        if self.get_type_predicate_of_signature(sig).is_some() {
            return true;
        }
        let declaration = self.signature_arena.get(sig).declaration;
        if let Some(declaration) = declaration {
            let return_type = self
                .get_return_type_from_annotation(declaration)
                .unwrap_or(self.unknown_type);
            return self
                .types_handle()
                .get(return_type)
                .flags
                .intersects(TypeFlags::NEVER);
        }
        false
    }

    /// `(c *Checker) getExplicitThisType` (flow.go).
    pub(crate) fn get_explicit_this_type(&mut self, node: NodeId) -> Option<TypeId> {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let container = ast::get_this_container(node, &nodes, false, false);
        if ast::is_function_like(Some(container), &nodes) {
            let signature = self.get_signature_from_declaration(container);
            if let Some(this_parameter) = self.signature_arena.get(signature).this_parameter {
                return self.get_explicit_type_of_symbol(this_parameter, None);
            }
        }
        if let Some(parent) = nodes[container].parent {
            if ast::is_class_like(Some(parent), &nodes) {
                let symbol = self.get_symbol_of_declaration(parent);
                if let Some(symbol) = symbol {
                    if ast::is_static(&nodes[container]) {
                        return Some(self.get_type_of_symbol(symbol));
                    }
                    let declared = self.get_declared_type_of_symbol(symbol);
                    return self
                        .types_handle()
                        .get(declared)
                        .as_interface_type()
                        .and_then(|i| i.this_type);
                }
            }
        }
        None
    }
}

impl Checker {
    /// `(c *Checker) getInitialType` (flow.go).
    pub(crate) fn get_initial_type(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            Kind::VariableDeclaration => self.get_initial_type_of_variable_declaration(node),
            Kind::BindingElement => self.get_initial_type_of_binding_element(node),
            _ => panic!("Unhandled case in getInitialType"),
        }
    }

    /// `(c *Checker) getInitialTypeOfVariableDeclaration` (flow.go).
    pub(crate) fn get_initial_type_of_variable_declaration(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        if let Some(initializer) = nodes[node].initializer() {
            return self.get_type_of_initializer(initializer);
        }
        if nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .is_some_and(|gp| ast::is_for_in_statement(&nodes[gp]))
        {
            return self.string_type;
        }
        if nodes[node]
            .parent
            .and_then(|p| nodes[p].parent)
            .is_some_and(|gp| ast::is_for_of_statement(&nodes[gp]))
        {
            let for_of = nodes[node].parent.and_then(|p| nodes[p].parent).unwrap();
            return self.check_right_hand_side_of_for_of(for_of);
        }
        self.error_type
    }

    /// `(c *Checker) getTypeOfInitializer` (flow.go). Return the cached type
    /// if one is available. If the type of the variable was inferred from its
    /// initializer, we'll already have cached the type. Otherwise we compute
    /// it now without caching such that transient types are reflected.
    pub(crate) fn get_type_of_initializer(&mut self, node: NodeId) -> TypeId {
        if self.type_node_links.has(&node) {
            if let Some(t) = self.type_node_links.get(node).resolved_type {
                return t;
            }
        }
        self.get_type_of_expression(node)
    }

    /// `(c *Checker) getInitialTypeOfBindingElement` (flow.go).
    pub(crate) fn get_initial_type_of_binding_element(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let pattern = nodes[node].parent.expect("binding pattern");
        let declaration = nodes[pattern].parent.expect("binding declaration");
        let parent_type = self.get_initial_type(declaration);
        let t = if ast::is_object_binding_pattern(&nodes[pattern]) {
            let name = crate::utilities::get_binding_element_property_name(&nodes[node]);
            self.get_type_of_destructured_property(parent_type, name)
        } else if !crate::utilities::has_dot_dot_dot_token(&nodes[node], &nodes) {
            let index = nodes[pattern]
                .elements()
                .and_then(|es| es.iter().position(|&e| e == node))
                .unwrap_or(usize::MAX);
            self.get_type_of_destructured_array_element(parent_type, index)
        } else {
            self.get_type_of_destructured_spread_expression(parent_type)
        };
        let initializer = nodes[node].initializer();
        self.get_type_with_default(t, initializer)
    }

    /// `(c *Checker) getAssignedType` (flow.go).
    pub(crate) fn get_assigned_type(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let Some(parent) = nodes[node].parent else {
            return self.error_type;
        };
        match nodes[parent].kind {
            Kind::ForInStatement => self.string_type,
            Kind::ForOfStatement => self.check_right_hand_side_of_for_of(parent),
            Kind::BinaryExpression => self.get_assigned_type_of_binary_expression(parent),
            Kind::DeleteExpression => self.undefined_type,
            Kind::ArrayLiteralExpression => {
                self.get_assigned_type_of_array_literal_element(parent, node)
            }
            Kind::SpreadElement => self.get_assigned_type_of_spread_expression(parent),
            Kind::PropertyAssignment => self.get_assigned_type_of_property_assignment(parent),
            Kind::ShorthandPropertyAssignment => {
                self.get_assigned_type_of_shorthand_property_assignment(parent)
            }
            _ => self.error_type,
        }
    }

    /// `(c *Checker) getAssignedTypeOfBinaryExpression` (flow.go).
    pub(crate) fn get_assigned_type_of_binary_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let is_destructuring_default_assignment = nodes[node].parent.is_some_and(|p| {
            (ast::is_array_literal_expression(&nodes[p])
                && self.is_destructuring_assignment_target(&nodes, p))
                || (ast::is_property_assignment(&nodes[p])
                    && nodes[p]
                        .parent
                        .is_some_and(|pp| self.is_destructuring_assignment_target(&nodes, pp)))
        });
        if is_destructuring_default_assignment {
            let assigned = self.get_assigned_type(node);
            let right = nodes[node].as_binary_expression().right;
            return self.get_type_with_default(assigned, right);
        }
        let right = nodes[node].as_binary_expression().right.unwrap();
        self.get_type_of_expression(right)
    }

    /// `(c *Checker) getAssignedTypeOfArrayLiteralElement` (flow.go).
    pub(crate) fn get_assigned_type_of_array_literal_element(
        &mut self,
        node: NodeId,
        element: NodeId,
    ) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let index = nodes[node]
            .elements()
            .and_then(|es| es.iter().position(|&e| e == element))
            .unwrap_or(usize::MAX);
        let assigned = self.get_assigned_type(node);
        self.get_type_of_destructured_array_element(assigned, index)
    }

    /// `(c *Checker) getTypeOfDestructuredArrayElement` (flow.go).
    pub(crate) fn get_type_of_destructured_array_element(
        &mut self,
        t: TypeId,
        index: usize,
    ) -> TypeId {
        if crate::checker_d::every_type(self, t, |c: &mut Checker, t: TypeId| {
            c.is_tuple_like_type(t)
        }) {
            if let Some(element_type) = self.get_tuple_element_type(t, index) {
                return element_type;
            }
        }
        let element_type = self.check_iterated_type_or_element_type(
            IterationUse::DESTRUCTURING,
            t,
            self.undefined_type,
            None,
        );
        return self
            .include_undefined_in_index_signature(Some(element_type))
            .unwrap_or(element_type);
    }

    /// `(c *Checker) includeUndefinedInIndexSignature` (flow.go).
    pub(crate) fn include_undefined_in_index_signature(
        &mut self,
        t: Option<TypeId>,
    ) -> Option<TypeId> {
        let t = t?;
        if self.compiler_options.no_unchecked_indexed_access == tsc_core::tristate::TS_TRUE {
            return Some(self.get_union_type(&[t, self.missing_type]));
        }
        Some(t)
    }

    /// `(c *Checker) getAssignedTypeOfSpreadExpression` (flow.go).
    pub(crate) fn get_assigned_type_of_spread_expression(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let parent = __program.nodes((node).file_index())[node]
            .parent
            .expect("spread parent");
        let assigned = self.get_assigned_type(parent);
        self.get_type_of_destructured_spread_expression(assigned)
    }

    /// `(c *Checker) getTypeOfDestructuredSpreadExpression` (flow.go).
    pub(crate) fn get_type_of_destructured_spread_expression(&mut self, t: TypeId) -> TypeId {
        let element_type = self.check_iterated_type_or_element_type(
            IterationUse::DESTRUCTURING,
            t,
            self.undefined_type,
            None,
        );
        self.create_array_type(element_type)
    }

    /// `(c *Checker) getAssignedTypeOfPropertyAssignment` (flow.go).
    pub(crate) fn get_assigned_type_of_property_assignment(&mut self, node: NodeId) -> TypeId {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let parent = nodes[node].parent.expect("property assignment parent");
        let name = nodes[node].name();
        let assigned = self.get_assigned_type(parent);
        self.get_type_of_destructured_property(assigned, name)
    }

    /// `(c *Checker) getTypeOfDestructuredProperty` (flow.go).
    pub(crate) fn get_type_of_destructured_property(
        &mut self,
        t: TypeId,
        name: Option<NodeId>,
    ) -> TypeId {
        let Some(name) = name else {
            return self.error_type;
        };
        let name_type = self.get_literal_type_from_property_name(name);
        if !crate::utilities::is_type_usable_as_property_name(&self.types, name_type) {
            return self.error_type;
        }
        let text = crate::utilities::get_property_name_from_type(&self.types, name_type);
        if let Some(prop_type) = self.get_type_of_property_of_type(t, &text) {
            return prop_type;
        }
        if let Some(index_info) = self.get_applicable_index_info_for_name(t, &text) {
            let value_type = self
                .index_info_arena
                .get(index_info)
                .value_type
                .unwrap_or(self.error_type);
            return self
                .include_undefined_in_index_signature(Some(value_type))
                .unwrap_or(value_type);
        }
        self.error_type
    }

    /// `(c *Checker) getAssignedTypeOfShorthandPropertyAssignment` (flow.go).
    pub(crate) fn get_assigned_type_of_shorthand_property_assignment(
        &mut self,
        node: NodeId,
    ) -> TypeId {
        let assigned = self.get_assigned_type_of_property_assignment(node);
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        let default_expr = nodes[node]
            .as_shorthand_property_assignment()
            .object_assignment_initializer;
        self.get_type_with_default(assigned, default_expr)
    }

    /// `(c *Checker) isDestructuringAssignmentTarget` (flow.go).
    pub(crate) fn is_destructuring_assignment_target(
        &mut self,
        nodes: &[ast::Node],
        parent: NodeId,
    ) -> bool {
        nodes[parent].parent.is_some_and(|gp| {
            (ast::is_binary_expression(&nodes[gp])
                && nodes[gp].as_binary_expression().left == Some(parent))
                || (ast::is_for_of_statement(&nodes[gp])
                    && nodes[gp].as_for_in_or_of_statement().initializer == Some(parent))
        })
    }

    /// `(c *Checker) getTypeWithDefault` (flow.go).
    pub(crate) fn get_type_with_default(
        &mut self,
        t: TypeId,
        default_expression: Option<NodeId>,
    ) -> TypeId {
        if let Some(default_expression) = default_expression {
            let a = self.get_non_undefined_type(t);
            let b = self.get_type_of_expression(default_expression);
            return self.get_union_type(&[a, b]);
        }
        t
    }

    /// `(c *Checker) getAssignmentReducedType` (flow.go). Remove those
    /// constituent types of declaredType to which no constituent type of
    /// assignedType is assignable. For example, when a variable of type
    /// number | string | boolean is assigned a value of type number |
    /// boolean, we remove type string.
    pub(crate) fn get_assignment_reduced_type(
        &mut self,
        declared_type: TypeId,
        assigned_type: TypeId,
    ) -> TypeId {
        if declared_type == assigned_type {
            return declared_type;
        }
        if self
            .types_handle()
            .get(assigned_type)
            .flags
            .intersects(TypeFlags::NEVER)
        {
            return assigned_type;
        }
        let key = AssignmentReducedKey {
            id1: declared_type,
            id2: assigned_type,
        };
        if let Some(&result) = self.assignment_reduced_types.get(&key) {
            return result;
        }
        let result = self.get_assignment_reduced_type_worker(declared_type, assigned_type);
        self.assignment_reduced_types.insert(key, result);
        result
    }

    /// `(c *Checker) getAssignmentReducedTypeWorker` (flow.go).
    pub(crate) fn get_assignment_reduced_type_worker(
        &mut self,
        declared_type: TypeId,
        assigned_type: TypeId,
    ) -> TypeId {
        let filtered_type = self.filter_type(declared_type, &mut |c: &mut Checker, t: TypeId| {
            c.type_maybe_assignable_to(assigned_type, t)
        });
        // Ensure that we narrow to fresh types if the assignment is a fresh
        // boolean literal type.
        let mut reduced_type = filtered_type;
        if self
            .types_handle()
            .get(assigned_type)
            .flags
            .intersects(TypeFlags::BOOLEAN_LITERAL)
            && crate::checker_d::is_fresh_literal_type(&self.types, assigned_type)
        {
            reduced_type = self.map_type(
                reduced_type,
                Rc::new(|c: &mut Checker, t: TypeId| c.get_fresh_type_of_literal_type(t)),
            );
        }
        // Our crude heuristic produces an invalid result in some cases: see
        // GH#26130. For now, when that happens, we give up and don't narrow at
        // all. (This also means we'll never narrow for erroneous assignments
        // where the assigned type is not assignable to the declared type.)
        if self.is_type_assignable_to(assigned_type, reduced_type) {
            return reduced_type;
        }
        declared_type
    }

    /// `(c *Checker) typeMaybeAssignableTo` (flow.go).
    pub(crate) fn type_maybe_assignable_to(&mut self, source: TypeId, target: TypeId) -> bool {
        if !self
            .types_handle()
            .get(source)
            .flags
            .intersects(TypeFlags::UNION)
        {
            return self.is_type_assignable_to(source, target);
        }
        // Quick exit when source union contains the target type
        if self.types_handle().get(source).types().contains(&target) {
            return true;
        }
        // Otherwise, check if any constituent type of the source union is
        // assignable to the target type
        let __arena_types = self.types.clone();
        let types = __arena_types.get(source).types_rc();
        for t in (types).iter().copied() {
            if self.is_type_assignable_to(t, target) {
                return true;
            }
        }
        false
    }

    /// `(c *Checker) getTypePredicateArgument` (flow.go).
    pub(crate) fn get_type_predicate_argument(
        &mut self,
        nodes: &[ast::Node],
        predicate: &TypePredicate,
        call_expression: NodeId,
    ) -> Option<NodeId> {
        if predicate.kind == TypePredicateKind::Identifier
            || predicate.kind == TypePredicateKind::AssertsIdentifier
        {
            if let Some(arguments) = nodes[call_expression].arguments() {
                if predicate.parameter_index >= 0
                    && (predicate.parameter_index as usize) < arguments.len()
                {
                    return Some(arguments[predicate.parameter_index as usize]);
                }
            }
        } else {
            let invoked_expression = ast::skip_parentheses(
                nodes[call_expression]
                    .expression()
                    .unwrap_or(call_expression),
                nodes,
            );
            if ast::is_access_expression(&nodes[invoked_expression]) {
                return nodes[invoked_expression]
                    .expression()
                    .map(|e| ast::skip_parentheses(e, nodes));
            }
        }
        None
    }

    /// `(c *Checker) getFlowTypeInConstructor` (flow.go).
    pub(crate) fn get_flow_type_in_constructor(
        &mut self,
        symbol: SymbolId,
        constructor: NodeId,
    ) -> Option<TypeId> {
        let symbol_name = self.symbol_arena.get_ref(symbol).name.clone();
        let private_name = symbol_name
            .starts_with(&format!("{}#", ast::symbol::INTERNAL_SYMBOL_NAME_PREFIX))
            .then(|| symbol_name[symbol_name.find('@').map(|i| i + 1).unwrap_or(0)..].to_string());
        let file_index = constructor.file_index();
        // PORT(borrowck): clone the `Rc` program handle so the arena
        // `RefMut` borrows the local, not `self` — `self.factory` needs
        // `&mut` while the arena is alive.
        let program = self.program.clone().expect("program");
        let old_file_index = self.factory.file_index();
        self.factory.set_file_index(file_index);
        let access_name = {
            let mut arena = program.nodes_mut(file_index);
            if let Some(private_name) = private_name {
                self.factory
                    .new_private_identifier(&mut arena, &private_name)
            } else {
                self.factory.new_identifier(&mut arena, &symbol_name)
            }
        };
        let reference = {
            let mut arena = program.nodes_mut(file_index);
            let this = self
                .factory
                .new_keyword_expression(&mut arena, Kind::ThisKeyword);
            let reference = self.factory.new_property_access_expression(
                &mut arena,
                Some(this),
                None,
                Some(access_name),
                ast::NodeFlags::NONE,
            );
            arena[this].parent = Some(reference);
            arena[reference].parent = Some(constructor);
            reference
        };
        self.factory.set_file_index(old_file_index);
        // `reference.FlowNodeData().FlowNode = constructor.AsConstructorDeclaration().ReturnFlowNode`
        {
            let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((constructor).file_index());
            let return_flow_node = nodes[constructor]
                .as_constructor_declaration()
                .return_flow_node;
            let __program = self.program.clone().expect("program");
            let mut arena = __program.nodes_mut(file_index);
            arena[reference]
                .as_property_access_expression_mut()
                .flow_node_base
                .flow_node = return_flow_node;
        }
        let flow_type = self.get_flow_type_of_property(reference, Some(symbol));
        if self.no_implicit_any
            && (flow_type == self.auto_type || flow_type == self.auto_array_type)
        {
            let declaration = self.symbol_arena.get_ref(symbol).value_declaration;
            let args = [
                self.symbol_to_string(symbol),
                self.type_to_string(flow_type),
            ];
            self.error(
                declaration,
                &tsc_diagnostics::Member_0_implicitly_has_an_1_type,
                &args,
            );
        }
        // We don't infer a type if assignments are only null or undefined.
        if crate::checker_d::every_type(self, flow_type, |c: &mut Checker, t: TypeId| {
            c.is_nullable_type(t)
        }) {
            return None;
        }
        Some(self.convert_auto_to_any(flow_type))
    }

    /// `(c *Checker) getFlowTypeInStaticBlocks` (flow.go).
    pub(crate) fn get_flow_type_in_static_blocks(
        &mut self,
        symbol: SymbolId,
        static_blocks: &[NodeId],
    ) -> Option<TypeId> {
        let symbol_name = self.symbol_arena.get_ref(symbol).name.clone();
        let private_name = symbol_name
            .starts_with(&format!("{}#", ast::symbol::INTERNAL_SYMBOL_NAME_PREFIX))
            .then(|| symbol_name[symbol_name.find('@').map(|i| i + 1).unwrap_or(0)..].to_string());
        for &static_block in static_blocks {
            let file_index = static_block.file_index();
            // PORT(borrowck): clone the `Rc` program handle so the arena
            // `RefMut` borrows the local, not `self`.
            let program = self.program.clone().expect("program");
            let old_file_index = self.factory.file_index();
            self.factory.set_file_index(file_index);
            let access_name = {
                let mut arena = program.nodes_mut(file_index);
                if let Some(private_name) = private_name.clone() {
                    self.factory
                        .new_private_identifier(&mut arena, &private_name)
                } else {
                    self.factory.new_identifier(&mut arena, &symbol_name)
                }
            };
            let reference = {
                let mut arena = program.nodes_mut(file_index);
                let this = self
                    .factory
                    .new_keyword_expression(&mut arena, Kind::ThisKeyword);
                let reference = self.factory.new_property_access_expression(
                    &mut arena,
                    Some(this),
                    None,
                    Some(access_name),
                    ast::NodeFlags::NONE,
                );
                arena[this].parent = Some(reference);
                arena[reference].parent = Some(static_block);
                reference
            };
            self.factory.set_file_index(old_file_index);
            {
                let __program = self.program.clone().expect("program");
                let nodes = __program.nodes((static_block).file_index());
                let return_flow_node = nodes[static_block]
                    .as_class_static_block_declaration()
                    .return_flow_node;
                let __program = self.program.clone().expect("program");
                let mut arena = __program.nodes_mut(file_index);
                arena[reference]
                    .as_property_access_expression_mut()
                    .flow_node_base
                    .flow_node = return_flow_node;
            }
            let flow_type = self.get_flow_type_of_property(reference, Some(symbol));
            if self.no_implicit_any
                && (flow_type == self.auto_type || flow_type == self.auto_array_type)
            {
                let declaration = self.symbol_arena.get_ref(symbol).value_declaration;
                let args = [
                    self.symbol_to_string(symbol),
                    self.type_to_string(flow_type),
                ];
                self.error(
                    declaration,
                    &tsc_diagnostics::Member_0_implicitly_has_an_1_type,
                    &args,
                );
            }
            // We don't infer a type if assignments are only null or undefined.
            if crate::checker_d::every_type(self, flow_type, |c: &mut Checker, t: TypeId| {
                c.is_nullable_type(t)
            }) {
                continue;
            }
            return Some(self.convert_auto_to_any(flow_type));
        }
        None
    }

    /// `(c *Checker) isReachableFlowNode` (flow.go). `context` is any node in
    /// the file that owns the flow graph — used only to locate the per-file
    /// arenas (`set_flow_context`).
    pub(crate) fn is_reachable_flow_node(&mut self, context: NodeId, flow: FlowNodeId) -> bool {
        let mut f = self.get_flow_state();
        self.set_flow_context(&mut f, context);
        let result = self.is_reachable_flow_node_worker(&mut f, flow, false);
        self.put_flow_state(f);
        self.last_flow_node = flow;
        self.last_flow_node_reachable = result;
        result
    }

    /// `(c *Checker) isReachableFlowNodeWorker` (flow.go).
    pub(crate) fn is_reachable_flow_node_worker(
        &mut self,
        f: &mut FlowState,
        mut flow: FlowNodeId,
        mut no_cache_check: bool,
    ) -> bool {
        loop {
            if flow == self.last_flow_node {
                return self.last_flow_node_reachable;
            }
            let flags = f.flow_node(flow).flags;
            if flags.intersects(FlowFlags::SHARED) {
                if !no_cache_check && f.reduce_labels.is_empty() {
                    if let Some(&reachable) = self.flow_node_reachable.get(&flow) {
                        return reachable;
                    }
                    let reachable = self.is_reachable_flow_node_worker(f, flow, true);
                    self.flow_node_reachable.insert(flow, reachable);
                    return reachable;
                }
                no_cache_check = false;
            }
            if flags.intersects(
                FlowFlags::ASSIGNMENT | FlowFlags::CONDITION | FlowFlags::ARRAY_MUTATION,
            ) {
                flow = f.flow_node(flow).antecedent.expect("flow antecedent");
            } else if flags.intersects(FlowFlags::CALL) {
                let node = f.flow_node(flow).node.expect("call node");
                if let Some(signature) = self.get_effects_signature(node) {
                    if let Some(predicate) = self.get_type_predicate_of_signature(signature) {
                        if predicate.kind == TypePredicateKind::AssertsIdentifier
                            && predicate.t.is_none()
                        {
                            if let Some(arguments) = f.nodes()[node].arguments() {
                                if predicate.parameter_index >= 0
                                    && (predicate.parameter_index as usize) < arguments.len()
                                    && self.is_false_expression(
                                        &f.nodes(),
                                        arguments[predicate.parameter_index as usize],
                                    )
                                {
                                    return false;
                                }
                            }
                        }
                    }
                    let return_type = self.get_return_type_of_signature(signature);
                    if self
                        .types_handle()
                        .get(return_type)
                        .flags
                        .intersects(TypeFlags::NEVER)
                    {
                        return false;
                    }
                }
                flow = f.flow_node(flow).antecedent.expect("flow antecedent");
            } else if flags.intersects(FlowFlags::BRANCH_LABEL) {
                // A branching point is reachable if any branch is reachable.
                let mut list = get_branch_label_antecedents(f, flow);
                let mut reachable = false;
                while let Some(l) = list {
                    let antecedent = f.flow_list(l).flow.expect("antecedent flow");
                    if self.is_reachable_flow_node_worker(f, antecedent, false) {
                        reachable = true;
                        break;
                    }
                    list = f.flow_list(l).next;
                }
                return reachable;
            } else if flags.intersects(FlowFlags::LOOP_LABEL) {
                let Some(antecedents) = f.flow_node(flow).antecedents else {
                    return false;
                };
                // A loop is reachable if the control flow path that leads to
                // the top is reachable.
                flow = f.flow_list(antecedents).flow.expect("loop antecedent");
            } else if flags.intersects(FlowFlags::SWITCH_CLAUSE) {
                // The control flow path representing an unmatched value in a
                // switch statement with no default clause is unreachable if
                // the switch statement is exhaustive.
                let node = f.flow_node(flow).node.expect("switch clause node");
                let data = SwitchClauseData::of(&f.nodes(), node);
                if data.clause_start == data.clause_end
                    && self.is_exhaustive_switch_statement(
                        data.switch_statement.expect("switch statement"),
                    )
                {
                    return false;
                }
                flow = f.flow_node(flow).antecedent.expect("flow antecedent");
            } else if flags.intersects(FlowFlags::REDUCE_LABEL) {
                // Cache is unreliable once we start adjusting labels
                self.last_flow_node = FlowNodeId::NONE;
                let node = f.flow_node(flow).node.expect("reduce label node");
                f.reduce_labels.push(node);
                let antecedent = f.flow_node(flow).antecedent.expect("flow antecedent");
                let result = self.is_reachable_flow_node_worker(f, antecedent, false);
                f.reduce_labels.pop();
                return result;
            } else {
                return !flags.intersects(FlowFlags::UNREACHABLE);
            }
        }
    }

    /// `(c *Checker) isFalseExpression` (flow.go).
    pub(crate) fn is_false_expression(&mut self, nodes: &[ast::Node], expr: NodeId) -> bool {
        let node = ast::skip_parentheses(expr, nodes);
        if nodes[node].kind == Kind::FalseKeyword {
            return true;
        }
        if ast::is_binary_expression(&nodes[node]) {
            let binary = nodes[node].as_binary_expression();
            let op = binary.operator_token.map(|t| nodes[t].kind);
            return op == Some(Kind::AmpersandAmpersandToken)
                && (binary
                    .left
                    .is_some_and(|l| self.is_false_expression(nodes, l))
                    || binary
                        .right
                        .is_some_and(|r| self.is_false_expression(nodes, r)))
                || op == Some(Kind::BarBarToken)
                    && binary
                        .left
                        .is_some_and(|l| self.is_false_expression(nodes, l))
                    && binary
                        .right
                        .is_some_and(|r| self.is_false_expression(nodes, r));
        }
        false
    }

    /// `(c *Checker) isPostSuperFlowNode` (flow.go). Return true if the given
    /// flow node is preceded by a 'super(...)' call in every possible code
    /// path leading to the node. `context` is any node in the file that owns
    /// the flow graph (see `is_reachable_flow_node`).
    pub(crate) fn is_post_super_flow_node(
        &mut self,
        context: NodeId,
        flow: FlowNodeId,
        no_cache_check: bool,
    ) -> bool {
        let mut f = self.get_flow_state();
        self.set_flow_context(&mut f, context);
        let result = self.is_post_super_flow_node_worker(&mut f, flow, no_cache_check);
        self.put_flow_state(f);
        result
    }

    /// `(c *Checker) isPostSuperFlowNodeWorker` (flow.go).
    pub(crate) fn is_post_super_flow_node_worker(
        &mut self,
        f: &mut FlowState,
        mut flow: FlowNodeId,
        mut no_cache_check: bool,
    ) -> bool {
        loop {
            let flags = f.flow_node(flow).flags;
            if flags.intersects(FlowFlags::SHARED) {
                if !no_cache_check {
                    if let Some(&post_super) = self.flow_node_post_super.get(&flow) {
                        return post_super;
                    }
                    let post_super = self.is_post_super_flow_node_worker(f, flow, true);
                    self.flow_node_post_super.insert(flow, post_super);
                    return post_super;
                }
                no_cache_check = false;
            }
            if flags.intersects(
                FlowFlags::ASSIGNMENT
                    | FlowFlags::CONDITION
                    | FlowFlags::ARRAY_MUTATION
                    | FlowFlags::SWITCH_CLAUSE,
            ) {
                flow = f.flow_node(flow).antecedent.expect("flow antecedent");
            } else if flags.intersects(FlowFlags::CALL) {
                let node = f.flow_node(flow).node.expect("call node");
                if f.nodes()[node]
                    .expression()
                    .is_some_and(|e| f.nodes()[e].kind == Kind::SuperKeyword)
                {
                    return true;
                }
                flow = f.flow_node(flow).antecedent.expect("flow antecedent");
            } else if flags.intersects(FlowFlags::BRANCH_LABEL) {
                let mut list = get_branch_label_antecedents(f, flow);
                let mut all_post_super = true;
                while let Some(l) = list {
                    let antecedent = f.flow_list(l).flow.expect("antecedent flow");
                    if !self.is_post_super_flow_node_worker(f, antecedent, false) {
                        all_post_super = false;
                        break;
                    }
                    list = f.flow_list(l).next;
                }
                return all_post_super;
            } else if flags.intersects(FlowFlags::LOOP_LABEL) {
                let Some(antecedents) = f.flow_node(flow).antecedents else {
                    return false;
                };
                // A loop is post-super if the control flow path that leads to
                // the top is post-super.
                flow = f.flow_list(antecedents).flow.expect("loop antecedent");
            } else if flags.intersects(FlowFlags::REDUCE_LABEL) {
                let node = f.flow_node(flow).node.expect("reduce label node");
                f.reduce_labels.push(node);
                let antecedent = f.flow_node(flow).antecedent.expect("flow antecedent");
                let result = self.is_post_super_flow_node_worker(f, antecedent, false);
                f.reduce_labels.pop();
                return result;
            } else {
                // Unreachable nodes are considered post-super to silence errors
                return flags.intersects(FlowFlags::UNREACHABLE);
            }
        }
    }

    /// `(c *Checker) isSymbolAssignedDefinitely` (flow.go). Check if a
    /// parameter, catch variable, or mutable local variable is definitely
    /// assigned anywhere.
    pub(crate) fn is_symbol_assigned_definitely(&mut self, symbol: SymbolId) -> bool {
        self.ensure_assignments_marked(symbol);
        self.marked_assignment_symbol_links
            .get(symbol)
            .has_definite_assignment
    }

    /// `(c *Checker) isSymbolAssigned` (flow.go). Check if a parameter, catch
    /// variable, or mutable local variable is assigned anywhere.
    pub(crate) fn is_symbol_assigned(&mut self, symbol: SymbolId) -> bool {
        self.ensure_assignments_marked(symbol);
        self.marked_assignment_symbol_links
            .get(symbol)
            .last_assignment_pos
            != 0
    }

    /// `(c *Checker) isPastLastAssignment` (flow.go). Return true if there
    /// are no assignments to the given symbol or if the given location is
    /// past the last assignment to the symbol.
    pub(crate) fn is_past_last_assignment(
        &mut self,
        symbol: SymbolId,
        location: Option<NodeId>,
    ) -> bool {
        self.ensure_assignments_marked(symbol);
        let last_assignment_pos = self
            .marked_assignment_symbol_links
            .get(symbol)
            .last_assignment_pos;
        if last_assignment_pos == 0 {
            return true;
        }
        let Some(location) = location else {
            return false;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((location).file_index());
        last_assignment_pos < nodes[location].pos()
    }

    /// `(c *Checker) ensureAssignmentsMarked` (flow.go).
    pub(crate) fn ensure_assignments_marked(&mut self, symbol: SymbolId) {
        let value_declaration = self.symbol_arena.get_ref(symbol).value_declaration;
        let Some(value_declaration) = value_declaration else {
            return;
        };
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((value_declaration).file_index());
        let parent = ast::find_ancestor(
            Some(value_declaration),
            &nodes,
            &mut |n: &ast::Node, nodes: &[ast::Node]| ast::is_function_or_source_file(n, nodes),
        );
        let Some(parent) = parent else {
            return;
        };
        if !self
            .node_links
            .get(parent)
            .flags
            .intersects(NodeCheckFlags::ASSIGNMENTS_MARKED)
        {
            self.node_links
                .get(parent)
                .flags
                .insert(NodeCheckFlags::ASSIGNMENTS_MARKED);
            if !self.has_parent_with_assignments_marked(&nodes, parent) {
                let mark = self
                    .mark_node_assignments
                    .clone()
                    .expect("mark_node_assignments");
                mark(self, parent);
            }
        }
    }

    /// `(c *Checker) hasParentWithAssignmentsMarked` (flow.go).
    pub(crate) fn has_parent_with_assignments_marked(
        &mut self,
        nodes: &[ast::Node],
        node: NodeId,
    ) -> bool {
        let node_links = &mut self.node_links;
        ast::find_ancestor(
            nodes[node].parent,
            nodes,
            &mut |n: &ast::Node, nodes: &[ast::Node]| {
                ast::is_function_or_source_file(n, nodes)
                    && node_links
                        .get(n.id)
                        .flags
                        .intersects(NodeCheckFlags::ASSIGNMENTS_MARKED)
            },
        )
        .is_some()
    }

    /// `(c *Checker) markNodeAssignmentsWorker` (flow.go). For all
    /// assignments within the given root node, record the last assignment
    /// source position for all referenced parameters and mutable local
    /// variables. When assignments occur in nested functions or references
    /// occur in export specifiers, record math.MaxInt32 as the assignment
    /// position. When assignments occur in compound statements, record the
    /// ending source position of the compound statement as the assignment
    /// position (this is more conservative than full control flow analysis,
    /// but requires only a single walk over the AST).
    pub(crate) fn mark_node_assignments_worker(&mut self, node: NodeId) -> bool {
        let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());
        match nodes[node].kind {
            Kind::Identifier => {
                let assignment_kind = crate::utilities::get_assignment_target_kind(node, &nodes);
                if assignment_kind != crate::utilities::AssignmentKind::NONE {
                    let symbol = self.get_resolved_symbol(node);
                    if self.is_parameter_or_mutable_local_variable(symbol) {
                        let last_assignment_pos = self
                            .marked_assignment_symbol_links
                            .get(symbol)
                            .last_assignment_pos;
                        if last_assignment_pos == 0 || last_assignment_pos != i32::MAX {
                            let value_declaration =
                                self.symbol_arena.get_ref(symbol).value_declaration;
                            let referencing_function = ast::find_ancestor(
                                Some(node),
                                &nodes,
                                &mut |n: &ast::Node, nodes: &[ast::Node]| {
                                    ast::is_function_or_source_file(n, nodes)
                                },
                            );
                            let declaring_function = value_declaration.and_then(|d| {
                                ast::find_ancestor(
                                    Some(d),
                                    &nodes,
                                    &mut |n: &ast::Node, nodes: &[ast::Node]| {
                                        ast::is_function_or_source_file(n, nodes)
                                    },
                                )
                            });
                            if referencing_function == declaring_function {
                                if let Some(declaration) = value_declaration {
                                    let pos =
                                        self.extend_assignment_position(&nodes, node, declaration);
                                    self.marked_assignment_symbol_links
                                        .get(symbol)
                                        .last_assignment_pos = pos;
                                }
                            } else {
                                self.marked_assignment_symbol_links
                                    .get(symbol)
                                    .last_assignment_pos = i32::MAX;
                            }
                        }
                        if assignment_kind == crate::utilities::AssignmentKind::DEFINITE {
                            self.marked_assignment_symbol_links
                                .get(symbol)
                                .has_definite_assignment = true;
                        }
                    }
                }
                false
            }
            Kind::ExportSpecifier => {
                let export_declaration = nodes[node].parent.and_then(|p| nodes[p].parent);
                let name = nodes[node].property_name_or_name();
                if let (Some(export_declaration), Some(name)) = (export_declaration, name) {
                    if !nodes[node].is_type_only()
                        && !nodes[export_declaration]
                            .as_export_declaration()
                            .is_type_only
                        && nodes[export_declaration].module_specifier().is_none()
                        && !ast::is_string_literal(&nodes[name])
                    {
                        if let Some(symbol) = self.resolve_entity_name(
                            Some(name),
                            ast::SymbolFlags::VALUE,
                            true,
                            true,
                            None,
                        ) {
                            if self.is_parameter_or_mutable_local_variable(symbol) {
                                self.marked_assignment_symbol_links
                                    .get(symbol)
                                    .last_assignment_pos = i32::MAX;
                            }
                        }
                    }
                }
                false
            }
            Kind::InterfaceDeclaration
            | Kind::TypeAliasDeclaration
            | Kind::JSTypeAliasDeclaration
            | Kind::EnumDeclaration => false,
            _ => {
                if ast::is_type_node(&nodes[node]) {
                    return false;
                }
                let mark = self
                    .mark_node_assignments
                    .clone()
                    .expect("mark_node_assignments");
                nodes[node].for_each_child(nodes.as_slice(), &mut |child| mark(self, child))
            }
        }
    }

    /// `(c *Checker) extendAssignmentPosition` (flow.go). Extend the position
    /// of the given assignment target node to the end of any intervening
    /// variable statement, expression statement, compound statement, or class
    /// declaration occurring between the node and the given declaration node.
    pub(crate) fn extend_assignment_position(
        &mut self,
        nodes: &[ast::Node],
        node: NodeId,
        declaration: NodeId,
    ) -> i32 {
        let mut pos = nodes[node].pos();
        let mut node = Some(node);
        while let Some(n) = node {
            if nodes[n].pos() <= nodes[declaration].pos() {
                break;
            }
            match nodes[n].kind {
                Kind::VariableStatement
                | Kind::ExpressionStatement
                | Kind::IfStatement
                | Kind::DoStatement
                | Kind::WhileStatement
                | Kind::ForStatement
                | Kind::ForInStatement
                | Kind::ForOfStatement
                | Kind::WithStatement
                | Kind::SwitchStatement
                | Kind::TryStatement
                | Kind::ClassDeclaration => {
                    pos = nodes[n].end();
                }
                _ => {}
            }
            node = nodes[n].parent;
        }
        pos
    }
}
