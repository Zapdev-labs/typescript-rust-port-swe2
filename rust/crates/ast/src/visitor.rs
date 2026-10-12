// Ported from tsc/internal/ast/visitor.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// NodeVisitor: a visitor that updates each child of a node via a callback and
// rebuilds nodes whose children changed. Since `*Node` is an id here, the
// visitor machinery threads `&mut VisitorCx` (arena + factory) through every
// call instead of relying on heap pointers.
//
// Return-convention deviation from Go: `visit_each_child` and the generated
// `update_*` factory methods return `Option<NodeId>` where `None` means
// "the node was unchanged" (i.e. the Go function returned the input pointer).
// `visit_node`/`visit_nodes` return the resulting child (`None` = removed,
// mirroring Go nil).

use crate::ast::{ModifierList, Node, NodeFactory};
use crate::ids::NodeId;
use crate::kind_generated::Kind;

/// Mutable context threaded through a visit: the node arena and the factory
/// that allocates replacement nodes. Go achieves this with heap pointers.
// `VisitorCx` carries a separate `'f` for the factory's own hook-capture
// lifetime: `&'a mut NodeFactory<'a>` would be unsatisfiable inside
// `impl NodeFactory<'f>` methods, where the borrow `&mut self` is shorter
// than `'f` and `&mut` is invariant over its pointee.
pub struct VisitorCx<'a, 'f> {
    pub nodes: &'a mut Vec<Node>,
    pub factory: &'a mut NodeFactory<'f>,
}

impl<'a, 'f> VisitorCx<'a, 'f> {
    pub fn new(nodes: &'a mut Vec<Node>, factory: &'a mut NodeFactory<'f>) -> VisitorCx<'a, 'f> {
        VisitorCx { nodes, factory }
    }
}

/// `v.Visit` — the required node-visit callback. Returns `Some` replacement
/// or `None` to remove the node (Go nil).
///
/// PORT: Go's `Visit` closure captures the enclosing `*NodeVisitor`
/// (`deepclone.go` does `visitor.VisitEachChild` inside its visit fn). Rust
/// closures cannot capture the not-yet-constructed visitor, so the visitor is
/// passed explicitly. The `'a` parameter is the closure-capture lifetime; the
/// `VisitorCx` lifetimes are higher-ranked so any borrow pair can be passed.
pub type VisitFn<'a> =
    dyn for<'cx, 'f> Fn(&NodeVisitor<'a>, &mut VisitorCx<'cx, 'f>, NodeId) -> Option<NodeId> + 'a;

// Hook signatures mirror NodeVisitorHooks. Each receives `v` so the hook may
// continue the default traversal.
pub type VisitNodeHook<'a> =
    dyn for<'cx, 'f> Fn(&mut VisitorCx<'cx, 'f>, NodeId, &NodeVisitor<'a>) -> Option<NodeId> + 'a;
pub type VisitTokenHook<'a> = VisitNodeHook<'a>;
pub type VisitNodesHook<'a> = dyn for<'cx, 'f> Fn(&mut VisitorCx<'cx, 'f>, Option<NodeList>, &NodeVisitor<'a>) -> Option<NodeList>
    + 'a;
pub type VisitModifiersHook<'a> = dyn for<'cx, 'f> Fn(
        &mut VisitorCx<'cx, 'f>,
        Option<ModifierList>,
        &NodeVisitor<'a>,
    ) -> Option<ModifierList>
    + 'a;
pub type VisitEmbeddedStatementHook<'a> = VisitNodeHook<'a>;
pub type VisitIterationBodyHook<'a> = VisitNodeHook<'a>;
pub type VisitParametersHook<'a> = VisitNodesHook<'a>;
pub type VisitFunctionBodyHook<'a> = VisitNodeHook<'a>;
pub type VisitTopLevelStatementsHook<'a> = VisitNodesHook<'a>;

use crate::ast::NodeList;

/// `NodeVisitorHooks` — hooks that intercept the default behavior of the
/// visitor. Only invoked by `visit_each_child` on a given node subtype,
/// matching the Go contract.
#[derive(Default)]
pub struct NodeVisitorHooks<'a> {
    /// Overrides visiting a Node.
    pub visit_node: Option<Box<VisitNodeHook<'a>>>,
    /// Overrides visiting a TokenNode.
    pub visit_token: Option<Box<VisitTokenHook<'a>>>,
    /// Overrides visiting a NodeList.
    pub visit_nodes: Option<Box<VisitNodesHook<'a>>>,
    /// Overrides visiting a ModifierList.
    pub visit_modifiers: Option<Box<VisitModifiersHook<'a>>>,
    /// Overrides visiting a Node when it is the embedded statement body of an
    /// iteration statement, `if` statement, or `with` statement.
    pub visit_embedded_statement: Option<Box<VisitEmbeddedStatementHook<'a>>>,
    /// Overrides visiting a Node when it is the embedded statement body of an
    /// iteration statement.
    pub visit_iteration_body: Option<Box<VisitIterationBodyHook<'a>>>,
    /// Overrides visiting a ParameterList.
    pub visit_parameters: Option<Box<VisitParametersHook<'a>>>,
    /// Overrides visiting a function body.
    pub visit_function_body: Option<Box<VisitFunctionBodyHook<'a>>>,
    /// Overrides visiting a variable environment.
    pub visit_top_level_statements: Option<Box<VisitTopLevelStatementsHook<'a>>>,
}

/// `type NodeVisitor struct`. The factory lives in `VisitorCx` rather than on
/// the visitor so hooks can receive `&NodeVisitor` while mutating the arena.
#[derive(Default)]
pub struct NodeVisitor<'a> {
    /// The callback used to visit a node. `None` mirrors a nil Go `Visit`
    /// (all visit methods become no-ops returning their input).
    pub visit: Option<Box<VisitFn<'a>>>,
    /// Hooks to be invoked when visiting a node.
    pub hooks: NodeVisitorHooks<'a>,
}

impl<'a> NodeVisitor<'a> {
    /// `NewNodeVisitor(visit, factory, hooks)` — the factory is supplied
    /// through `VisitorCx::new` instead.
    pub fn new(visit: Box<VisitFn<'a>>, hooks: NodeVisitorHooks<'a>) -> NodeVisitor<'a> {
        NodeVisitor {
            visit: Some(visit),
            hooks,
        }
    }

    /// `v.VisitSourceFile(node)`
    pub fn visit_source_file(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        self.visit_node(cx, Some(node))
    }

    /// `v.VisitNode` — visits a Node, possibly returning a new Node in its
    /// place. `Some(node)` result is the visited node; `None` means removed.
    ///
    ///   - If the input node is `None`, then the output is `None`.
    ///   - If `v.visit` is `None`, then the output is the input.
    ///   - If `v.visit` returns `None`, then the output is `None`.
    ///   - If `v.visit` returns a SyntaxList Node, then the output is the only
    ///     child of the SyntaxList Node.
    pub fn visit_node(&self, cx: &mut VisitorCx<'_, '_>, node: Option<NodeId>) -> Option<NodeId> {
        let node = node?;
        let visit = self.visit.as_ref()?;
        let mut visited = visit(self, cx, node);
        // The lift check only applies to ids that resolve in `cx.nodes`. A
        // visitor minting into a different arena space (e.g. the declaration
        // builder's scratch-relocate pass, which returns destination-space
        // ids for nodes not yet present in this buffer) would read an
        // arbitrary node here — or index out of bounds.
        if let Some(id) = visited
            && id.file_index() == node.file_index()
            && (id.local_index() as usize) < cx.nodes.len()
            && cx.nodes[id].kind == Kind::SyntaxList
        {
            let children = &cx.nodes[id].as_syntax_list().children;
            if children.len() != 1 {
                panic!("Expected only a single node to be written to output");
            }
            let lifted = children[0];
            visited = Some(lifted);
            if cx.nodes[lifted].kind == Kind::SyntaxList {
                panic!("The result of visiting and lifting a Node may not be SyntaxList");
            }
        }
        visited
    }

    /// `v.VisitEmbeddedStatement` — visits an embedded Statement (i.e., the
    /// single statement body of a loop, `if..else` branch, etc.), possibly
    /// returning a new Statement in its place.
    ///
    ///   - If `v.visit` returns a SyntaxList Node, then the output is either
    ///     the only child of the SyntaxList Node, or a Block containing the
    ///     nodes in the list.
    pub fn visit_embedded_statement(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        let node = node?;
        let visit = self.visit.as_ref()?;
        let visited = visit(self, cx, node)?;
        Some(self.lift_to_block(cx, visited))
    }

    /// `v.VisitNodes` — visits a NodeList, possibly returning a new NodeList
    /// in its place.
    ///
    ///   - If `v.visit` returns a SyntaxList Node, then the children of that
    ///     node will be merged into the output and a new NodeList will be
    ///     returned.
    ///   - If this method returns a new NodeList for any reason, it will have
    ///     the same Loc as the input NodeList.
    ///
    /// NOTE: Go takes `*NodeList` and returns `*NodeList`; the slice is
    /// cloned here because the arena is borrowed mutably by the context.
    pub fn visit_nodes(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        nodes: Option<NodeList>,
    ) -> Option<NodeList> {
        let nodes = nodes?;
        self.visit.as_ref()?;
        if let Some(result) = self.visit_slice(cx, &nodes.nodes) {
            let mut list = cx.factory.new_node_list(result);
            list.loc = nodes.loc;
            return Some(list);
        }
        Some(nodes)
    }

    /// `v.VisitModifiers` — visits a ModifierList, possibly returning a new
    /// ModifierList in its place.
    pub fn visit_modifiers(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        nodes: Option<ModifierList>,
    ) -> Option<ModifierList> {
        let nodes = nodes?;
        self.visit.as_ref()?;
        if let Some(result) = self.visit_slice(cx, &nodes.nodes) {
            let modifier_flags = crate::utilities::modifiers_to_flags(&result, cx.nodes);
            let list = ModifierList {
                loc: nodes.loc,
                nodes: result.into_boxed_slice(),
                modifier_flags,
            };
            return Some(list);
        }
        Some(nodes)
    }

    /// `v.VisitSlice` — visits a slice of Nodes, returning `Some(result)` if
    /// the slice changed (a fresh `Vec`) or `None` if it is unchanged.
    pub fn visit_slice(&self, cx: &mut VisitorCx<'_, '_>, nodes: &[NodeId]) -> Option<Vec<NodeId>> {
        self.visit.as_ref()?;

        let visit = self.visit.as_ref().unwrap();
        for i in 0..nodes.len() {
            let node = nodes[i];
            let visited = visit(self, cx, node);
            if visited != Some(node) {
                let mut updated: Vec<NodeId> = nodes[..i].to_vec();
                let mut i = i;
                let mut visited = visited;
                loop {
                    // finish prior loop
                    match visited {
                        None => {} // do nothing
                        Some(id) if cx.nodes[id].kind == Kind::SyntaxList => {
                            let children = cx.nodes[id].as_syntax_list().children.clone();
                            updated.extend_from_slice(&children);
                        }
                        Some(id) => updated.push(id),
                    }

                    i += 1;

                    // loop over remaining elements
                    if i >= nodes.len() {
                        break;
                    }

                    let node = nodes[i];
                    visited = visit(self, cx, node);
                }
                return Some(updated);
            }
        }

        None
    }

    /// `v.VisitEachChild` — visits each child of a Node, possibly returning a
    /// new Node of the same kind in its place. Returns `None` when the node
    /// was unchanged (Go returned the same pointer).
    pub fn visit_each_child(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> Option<NodeId> {
        self.visit.as_ref()?;
        crate::ast_generated::visit_each_child(cx, self, node)
    }

    // Hook dispatch (Go's lowercase `visitNode`, `visitToken`, ... helpers).

    /// `v.visitNode`
    pub(crate) fn visit_node_hooked(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        if let Some(hook) = &self.hooks.visit_node {
            return hook(cx, node?, self);
        }
        self.visit_node(cx, node)
    }

    /// `v.visitEmbeddedStatement`
    pub(crate) fn visit_embedded_statement_hooked(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        if let Some(hook) = &self.hooks.visit_embedded_statement {
            return hook(cx, node?, self);
        }
        if self.hooks.visit_node.is_some() {
            let hooked = self.visit_node_hooked(cx, node)?;
            return Some(self.lift_to_block(cx, hooked));
        }
        self.visit_embedded_statement(cx, node)
    }

    /// `v.visitIterationBody`
    pub(crate) fn visit_iteration_body_hooked(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        if let Some(hook) = &self.hooks.visit_iteration_body {
            return hook(cx, node?, self);
        }
        self.visit_embedded_statement_hooked(cx, node)
    }

    /// `v.visitFunctionBody`
    pub(crate) fn visit_function_body_hooked(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        if let Some(hook) = &self.hooks.visit_function_body {
            return hook(cx, node?, self);
        }
        self.visit_node_hooked(cx, node)
    }

    /// `v.visitToken`
    pub(crate) fn visit_token_hooked(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        if let Some(hook) = &self.hooks.visit_token {
            return hook(cx, node?, self);
        }
        self.visit_node(cx, node)
    }

    /// `v.visitNodes`
    pub(crate) fn visit_nodes_hooked(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        nodes: Option<NodeList>,
    ) -> Option<NodeList> {
        if let Some(hook) = &self.hooks.visit_nodes {
            return hook(cx, nodes, self);
        }
        self.visit_nodes(cx, nodes)
    }

    /// `v.visitModifiers`
    pub(crate) fn visit_modifiers_hooked(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        nodes: Option<ModifierList>,
    ) -> Option<ModifierList> {
        if let Some(hook) = &self.hooks.visit_modifiers {
            return hook(cx, nodes, self);
        }
        self.visit_modifiers(cx, nodes)
    }

    /// `v.visitParameters`
    pub(crate) fn visit_parameters_hooked(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        nodes: Option<NodeList>,
    ) -> Option<NodeList> {
        if let Some(hook) = &self.hooks.visit_parameters {
            return hook(cx, nodes, self);
        }
        self.visit_nodes_hooked(cx, nodes)
    }

    /// `v.visitTopLevelStatements`
    pub(crate) fn visit_top_level_statements_hooked(
        &self,
        cx: &mut VisitorCx<'_, '_>,
        nodes: Option<NodeList>,
    ) -> Option<NodeList> {
        if let Some(hook) = &self.hooks.visit_top_level_statements {
            return hook(cx, nodes, self);
        }
        self.visit_nodes_hooked(cx, nodes)
    }

    /// `v.liftToBlock`
    pub(crate) fn lift_to_block(&self, cx: &mut VisitorCx<'_, '_>, node: NodeId) -> NodeId {
        let mut nodes: Vec<NodeId> = Vec::new();
        if cx.nodes[node].kind == Kind::SyntaxList {
            nodes = cx.nodes[node].as_syntax_list().children.clone().into_vec();
        } else {
            nodes.push(node);
        }
        let node = if nodes.len() == 1 {
            nodes[0]
        } else {
            let list = cx.factory.new_node_list(nodes);
            cx.factory
                .new_block(cx.nodes, Some(list), true /* multi_line */)
        };
        if cx.nodes[node].kind == Kind::SyntaxList {
            panic!("The result of visiting and lifting a Node may not be SyntaxList");
        }
        node
    }
}
