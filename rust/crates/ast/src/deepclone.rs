// Ported from tsc/internal/ast/deepclone.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_core::text::TextRange;

use crate::ast::{ModifierList, Node, NodeFactory, NodeList};
use crate::ids::NodeId;
use crate::nodeflags::NodeFlags;
use crate::utilities::set_parent_in_children;
use crate::visitor::{NodeVisitor, NodeVisitorHooks, VisitFn, VisitorCx};

// Ideally, this would get cached on the node factory so there's only ever one set of closures made per factory
fn get_deep_clone_visitor<'a>(synthetic_location: bool) -> NodeVisitor<'a> {
    NodeVisitor::new(
        Box::new(
            move |v: &NodeVisitor, cx: &mut VisitorCx, node: NodeId| -> Option<NodeId> {
                let visited = v.visit_each_child(cx, node);
                if let Some(visited) = visited {
                    if synthetic_location {
                        cx.nodes[visited].loc = TextRange::new(-1, -1);
                    }
                    return Some(visited);
                }
                // forcibly clone leaf nodes, which will then cascade new nodes/arrays upwards via `update` calls
                let c = cx.factory.clone_node(cx.nodes, node);
                // In strada, `factory.cloneNode` was dynamic and did _not_ clone positions for any "special cases", meanwhile
                // Node.Clone in corsa reliably uses `Update` calls for all nodes and so copies locations by default.
                // Deep clones are done to copy a node across files, so here, we explicitly make the location range synthetic on all cloned nodes
                if synthetic_location {
                    cx.nodes[c].loc = TextRange::new(-1, -1);
                }
                Some(c)
            },
        ) as Box<VisitFn<'a>>,
        NodeVisitorHooks {
            visit_nodes: Some(Box::new(
                move |cx: &mut VisitorCx, nodes: Option<NodeList>, v: &NodeVisitor| {
                    let nodes = nodes?;
                    let visited = v.visit_nodes(cx, Some(nodes.clone()));
                    let mut new_list = match visited {
                        Some(visited) if visited != nodes => visited,
                        _ => nodes.clone_list(cx.factory),
                    };
                    if synthetic_location {
                        new_list.loc = TextRange::new(-1, -1);
                        if nodes.has_trailing_comma(cx.nodes) {
                            let last = *new_list.nodes.last().unwrap();
                            cx.nodes[last].loc = TextRange::new(-2, -2);
                        }
                    }
                    Some(new_list)
                },
            )),
            visit_modifiers: Some(Box::new(
                move |cx: &mut VisitorCx, nodes: Option<ModifierList>, v: &NodeVisitor| {
                    let nodes = nodes?;
                    let visited = v.visit_modifiers(cx, Some(nodes.clone()));
                    let mut new_list = match visited {
                        Some(visited) if visited != nodes => visited,
                        _ => nodes.clone_list(cx.factory),
                    };
                    if synthetic_location {
                        new_list.loc = TextRange::new(-1, -1);
                        if nodes.has_trailing_comma(cx.nodes) {
                            let last = *new_list.nodes.last().unwrap();
                            cx.nodes[last].loc = TextRange::new(-2, -2);
                        }
                    }
                    Some(new_list)
                },
            )),
            ..Default::default()
        },
    )
}

impl NodeFactory<'_> {
    /// `f.DeepCloneNode(node)`
    pub fn deep_clone_node(&mut self, nodes: &mut Vec<Node>, node: NodeId) -> Option<NodeId> {
        let visitor = get_deep_clone_visitor(true /* synthetic_location */);
        let mut cx = VisitorCx::new(nodes, self);
        visitor.visit_node(&mut cx, Some(node))
    }

    /// `f.DeepCloneReparse(node)`
    pub fn deep_clone_reparse(
        &mut self,
        nodes: &mut Vec<Node>,
        node: Option<NodeId>,
    ) -> Option<NodeId> {
        let node = node?;
        let node = {
            let visitor = get_deep_clone_visitor(false /* synthetic_location */);
            let mut cx = VisitorCx::new(nodes, self);
            visitor.visit_node(&mut cx, Some(node))
        }?;
        set_parent_in_children(nodes, node);
        nodes[node].flags |= NodeFlags::REPARSED;
        Some(node)
    }

    /// `f.DeepCloneReparseModifiers(modifiers)`
    pub fn deep_clone_reparse_modifiers(
        &mut self,
        nodes: &mut Vec<Node>,
        modifiers: Option<ModifierList>,
    ) -> Option<ModifierList> {
        let visitor = get_deep_clone_visitor(false /* synthetic_location */);
        let mut cx = VisitorCx::new(nodes, self);
        visitor.visit_modifiers(&mut cx, modifiers)
    }
}
