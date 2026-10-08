// Ported from tsc/internal/ast/ast.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// AST node core: `Node`, `NodeList`, `ModifierList`, `NodeFactory`, factory
// hooks, child traversal helpers, and the kind-switch `Node` accessors.
//
// Pointer model: Go `*Node` becomes `Option<NodeId>` on data fields and
// `NodeId` where a value is provably mandatory (e.g. `Node::id`). Node
// payloads live in `NodeData` (see ast_generated.rs) and are stored in the
// `Vec<Node>` owned by a `SourceFile`.

use std::borrow::Cow;

use tsc_collections::OrderedMap;
use tsc_core::options_generated::ModuleKind;
use tsc_core::text::{TextPos, TextRange};
use tsc_tspath::RootedDirectoryPath;

use crate::ast_generated::*;
use crate::ids::{NodeId, SymbolId};
use crate::kind_generated::Kind;
use crate::modifierflags::ModifierFlags;
use crate::nodeflags::NodeFlags;
use crate::symbol::SymbolTable;

// NodeList

/// A list of AST nodes with a shared source range, mirroring
/// `type NodeList struct` in ast.go.
#[derive(Clone, PartialEq, Default)]
pub struct NodeList {
    pub loc: TextRange,
    pub nodes: Box<[NodeId]>,
}

impl NodeList {
    pub fn new(nodes: impl Into<Box<[NodeId]>>) -> NodeList {
        NodeList {
            loc: TextRange::undefined(),
            nodes: nodes.into(),
        }
    }

    /// `list.Loc.Pos()`
    pub fn pos(&self) -> TextPos {
        self.loc.pos()
    }

    /// `list.Loc.End()`
    pub fn end(&self) -> TextPos {
        self.loc.end()
    }

    /// `list.Loc`
    pub fn loc(&self) -> TextRange {
        self.loc
    }

    /// `len(list.Nodes)`
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// `list.Nodes`
    pub fn nodes(&self) -> &[NodeId] {
        &self.nodes
    }

    /// `HasTrailingComma` — whether the last element's end precedes the list's
    /// end (i.e. a trailing comma token follows it). Needs the node arena to
    /// resolve the final child.
    pub fn has_trailing_comma(&self, nodes: &[Node]) -> bool {
        let Some(&last) = self.nodes.last() else {
            return false;
        };
        nodes[last].end() < self.end()
    }

    /// `(list *NodeList) Clone` — builds a new list sharing the same child ids.
    pub fn clone_list(&self, _f: &mut NodeFactory) -> NodeList {
        // Go allocates via the list arena and shares `list.Nodes`; a fresh
        // boxed slice keeps the shared-allocation cost model equivalent.
        let mut result = NodeList::new(self.nodes.clone());
        result.loc = self.loc;
        result
    }
}

// ModifierList

/// A `NodeList` of modifiers plus a cached `ModifierFlags` rollup, mirroring
/// `type ModifierList struct` in ast.go. The embedded `NodeList` is flattened
/// into `loc`/`nodes` fields.
#[derive(Clone, PartialEq, Default)]
pub struct ModifierList {
    pub loc: TextRange,
    pub nodes: Box<[NodeId]>,
    pub modifier_flags: ModifierFlags,
}

impl ModifierList {
    pub fn pos(&self) -> TextPos {
        self.loc.pos()
    }

    pub fn end(&self) -> TextPos {
        self.loc.end()
    }

    pub fn loc(&self) -> TextRange {
        self.loc
    }

    pub fn nodes(&self) -> &[NodeId] {
        &self.nodes
    }

    /// The embedded `NodeList` view (Go's promoted `NodeList` fields).
    pub fn as_node_list(&self) -> NodeList {
        NodeList {
            loc: self.loc,
            nodes: self.nodes.clone(),
        }
    }

    /// `(list *ModifierList) Clone`
    pub fn clone_list(&self, _f: &mut NodeFactory) -> ModifierList {
        ModifierList {
            loc: self.loc,
            nodes: self.nodes.clone(),
            modifier_flags: self.modifier_flags,
        }
    }
}

// Node

/// The AST node header. In the Go implementation this type is embedded in
/// every node payload via `NodeBase`; here it is the arena element and the
/// payload hangs off `data`.
pub struct Node {
    /// Packed `file:20|local:44` id, assigned on arena insertion. This stands
    /// in for Go's lazily-assigned `id atomic.Uint64` plus the pointer's
    /// inherent identity.
    pub id: NodeId,
    pub kind: Kind,
    pub flags: NodeFlags,
    pub loc: TextRange,
    /// Set during binding. `None` mirrors Go's nil `Parent`.
    pub parent: Option<NodeId>,
    pub data: NodeData,
}

impl core::ops::Index<NodeId> for [Node] {
    type Output = Node;
    #[inline]
    fn index(&self, id: NodeId) -> &Node {
        // `local_index` is the slot within the owning file's `Vec<Node>`.
        &self[id.local_index() as usize]
    }
}

impl core::ops::IndexMut<NodeId> for [Node] {
    #[inline]
    fn index_mut(&mut self, id: NodeId) -> &mut Node {
        &mut self[id.local_index() as usize]
    }
}

// `Vec<Node>` has its own `Index` impl (via SliceIndex) that would shadow the
// slice impl — add explicit impls so `nodes[id]` works on the arena directly.
impl core::ops::Index<NodeId> for Vec<Node> {
    type Output = Node;
    #[inline]
    fn index(&self, id: NodeId) -> &Node {
        &self.as_slice()[id]
    }
}

impl core::ops::IndexMut<NodeId> for Vec<Node> {
    #[inline]
    fn index_mut(&mut self, id: NodeId) -> &mut Node {
        &mut self.as_mut_slice()[id]
    }
}

// NodeFactoryHooks / NodeFactory

/// Hook invoked when a node is created. Receives the arena and the new node id.
pub type NodeCreateHook<'a> = dyn FnMut(&mut Vec<Node>, NodeId) + 'a;
/// Hook invoked when a node is updated or cloned. Receives the arena, the new
/// node id, and the original node id.
pub type NodeUpdateHook<'a> = dyn FnMut(&mut Vec<Node>, NodeId, NodeId) + 'a;

/// Ported from `type NodeFactoryHooks struct`.
#[derive(Default)]
pub struct NodeFactoryHooks<'a> {
    /// Hooks the creation of a node.
    pub on_create: Option<Box<NodeCreateHook<'a>>>,
    /// Hooks the updating of a node.
    pub on_update: Option<Box<NodeUpdateHook<'a>>>,
    /// Hooks the cloning of a node.
    pub on_clone: Option<Box<NodeUpdateHook<'a>>>,
}

/// Ported from `type NodeFactory struct`. Per-kind arenas are dropped in
/// favour of the file's single `Vec<Node>`; `file_index` selects the high
/// bits of every `NodeId` this factory mints.
#[derive(Default)]
pub struct NodeFactory<'a> {
    pub(crate) hooks: NodeFactoryHooks<'a>,
    node_count: u64,
    /// `f.identifierCount` — incremented by generated `new_*` methods.
    pub(crate) identifier_count: u64,
    /// `f.textCount` — incremented by generated `new_*` methods.
    pub(crate) text_count: u64,
    file_index: u32,
}

impl<'a> NodeFactory<'a> {
    /// `NewNodeFactory(hooks)`
    pub fn new(hooks: NodeFactoryHooks<'a>) -> NodeFactory<'a> {
        NodeFactory {
            hooks,
            ..Default::default()
        }
    }

    /// `f.nodeCount`
    pub fn node_count(&self) -> u64 {
        self.node_count
    }

    /// `f.textCount`
    pub fn text_count(&self) -> u64 {
        self.text_count
    }

    /// `f.identifierCount`
    pub fn identifier_count(&self) -> u64 {
        self.identifier_count
    }

    /// The file index packed into ids minted by this factory. Set when the
    /// factory is bound to a `SourceFile` arena; defaults to 0.
    pub fn file_index(&self) -> u32 {
        self.file_index
    }

    pub fn set_file_index(&mut self, file_index: u32) {
        self.file_index = file_index;
    }

    /// `f.newNode(kind, data)`
    pub(crate) fn new_node(&mut self, nodes: &mut Vec<Node>, kind: Kind, data: NodeData) -> NodeId {
        self.node_count += 1;
        new_node(nodes, self.file_index, kind, data, &mut self.hooks)
    }

    /// `f.NewNodeList(nodes)`
    pub fn new_node_list(&self, nodes: impl Into<Box<[NodeId]>>) -> NodeList {
        NodeList::new(nodes)
    }

    /// `f.NewModifierList(nodes)` — computes `ModifierFlags` like Go.
    pub fn new_modifier_list(&self, nodes: &[Node], modifiers: impl Into<Box<[NodeId]>>) -> ModifierList {
        let modifiers = modifiers.into();
        let modifier_flags = crate::utilities::modifiers_to_flags(&modifiers, nodes);
        ModifierList {
            loc: TextRange::undefined(),
            nodes: modifiers,
            modifier_flags,
        }
    }
}

/// `newNode` — pushes a node into the arena, assigning its packed id, then
/// runs the `OnCreate` hook.
pub(crate) fn new_node(
    nodes: &mut Vec<Node>,
    file_index: u32,
    kind: Kind,
    data: NodeData,
    hooks: &mut NodeFactoryHooks<'_>,
) -> NodeId {
    let id = NodeId::new(file_index, nodes.len() as u64);
    nodes.push(Node {
        id,
        kind,
        flags: NodeFlags::NONE,
        loc: TextRange::undefined(),
        parent: None,
        data,
    });
    if let Some(on_create) = hooks.on_create.as_mut() {
        on_create(nodes, id);
    }
    id
}

/// `updateNode` — preserves `flags`/`loc` and invokes `OnUpdate` when the
/// node changed.
pub(crate) fn update_node(
    nodes: &mut Vec<Node>,
    updated: NodeId,
    original: NodeId,
    hooks: &mut NodeFactoryHooks<'_>,
) -> NodeId {
    if updated != original {
        nodes[updated].flags = nodes[original].flags;
        nodes[updated].loc = nodes[original].loc;
        if let Some(on_update) = hooks.on_update.as_mut() {
            on_update(nodes, updated, original);
        }
    }
    updated
}

/// `cloneNode` — `updateNode` plus the `OnClone` hook.
pub(crate) fn clone_node(
    nodes: &mut Vec<Node>,
    updated: NodeId,
    original: NodeId,
    hooks: &mut NodeFactoryHooks<'_>,
) -> NodeId {
    update_node(nodes, updated, original, hooks);
    if updated != original && let Some(on_clone) = hooks.on_clone.as_mut() {
        on_clone(nodes, updated, original);
    }
    updated
}

// Child traversal helpers

/// The Go `Visitor` — a callback receiving a child `&Node`; returns `true` to
/// stop traversal early.
pub type Visitor<'a> = dyn FnMut(&Node) -> bool + 'a;

/// `visit(v, node)` — visits a single optional child.
pub fn visit(v: &mut Visitor<'_>, node: Option<NodeId>, nodes: &[Node]) -> bool {
    node.is_some_and(|id| v(&nodes[id]))
}

/// `visitNodeList(v, children)` — visits each element of an optional list.
pub fn visit_node_list(v: &mut Visitor<'_>, children: &Option<NodeList>, nodes: &[Node]) -> bool {
    if let Some(children) = children {
        visit_nodes(v, &children.nodes, nodes)
    } else {
        false
    }
}

/// `visitNodes(v, children)` — visits each element of a `[]*Node` slice.
pub fn visit_nodes(v: &mut Visitor<'_>, children: &[NodeId], nodes: &[Node]) -> bool {
    children.iter().any(|&id| v(&nodes[id]))
}

/// `visitModifiers(v, modifiers)` — visits each element of an optional
/// `ModifierList`.
pub fn visit_modifiers(v: &mut Visitor<'_>, modifiers: &Option<ModifierList>, nodes: &[Node]) -> bool {
    if let Some(modifiers) = modifiers {
        visit_nodes(v, &modifiers.nodes, nodes)
    } else {
        false
    }
}

// Node accessors

impl Node {
    /// `n.AsNode()`
    #[inline]
    pub fn as_node(&self) -> &Node {
        self
    }

    /// `n.Loc.Pos()`
    #[inline]
    pub fn pos(&self) -> TextPos {
        self.loc.pos()
    }

    /// `n.Loc.End()`
    #[inline]
    pub fn end(&self) -> TextPos {
        self.loc.end()
    }

    /// `n.Kind.String()`
    pub fn kind_string(&self) -> &'static str {
        self.kind.kind_string()
    }

    /// `int16(n.Kind)`
    pub fn kind_value(&self) -> i16 {
        self.kind as i16
    }

    /// `n.ForEachChild(visitor)` — `true` stops traversal early (Go convention).
    pub fn for_each_child(&self, nodes: &[Node], visitor: &mut Visitor<'_>) -> bool {
        self.data.for_each_child(visitor, nodes)
    }

    /// `n.IterChildren()` — yields each direct child `&Node`.
    pub fn iter_children<'a>(&'a self, nodes: &'a [Node]) -> impl Iterator<Item = &'a Node> + 'a {
        let mut children: Vec<&'a Node> = Vec::new();
        self.for_each_child(nodes, &mut |child| {
            children.push(child);
            false
        });
        children.into_iter()
    }

    /// `n.data.Modifiers()`
    pub fn modifiers(&self) -> Option<&ModifierList> {
        self.data.modifiers()
    }

    /// `n.data.setModifiers(modifiers)` — the `MutableNode` setter.
    pub fn set_modifiers(&mut self, modifiers: Option<ModifierList>) {
        self.data.set_modifiers(modifiers);
    }

    /// `n.data.Name()`
    pub fn name(&self) -> Option<NodeId> {
        self.data.name()
    }

    /// `n.data.FlowNodeData()`
    pub fn flow_node_data(&self) -> Option<&FlowNodeBase> {
        self.data.flow_node_data()
    }

    /// `n.data.DeclarationData()`
    pub fn declaration_data(&self) -> Option<&DeclarationBase> {
        self.data.declaration_data()
    }

    /// `n.data.ExportableData()`
    pub fn exportable_data(&self) -> Option<&ExportableBase> {
        self.data.exportable_data()
    }

    /// `n.data.LocalsContainerData()`
    pub fn locals_container_data(&self) -> Option<&LocalsContainerBase> {
        self.data.locals_container_data()
    }

    /// `n.data.FunctionLikeData()`
    pub fn function_like_data(&self) -> Option<&FunctionLikeBase> {
        self.data.function_like_data()
    }

    /// `n.ParameterList()`
    pub fn parameter_list(&self) -> Option<&NodeList> {
        self.function_like_data().and_then(|d| d.parameters.as_ref())
    }

    /// `n.Parameters()`
    pub fn parameters<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.parameter_list().map(|l| l.nodes())
    }

    /// `n.data.ClassLikeData()`
    pub fn class_like_data(&self) -> Option<&ClassLikeBase> {
        self.data.class_like_data()
    }

    /// `n.data.BodyData()`
    pub fn body_data(&self) -> Option<&BodyBase> {
        self.data.body_data()
    }

    /// `n.data.LiteralLikeData()`
    pub fn literal_like_data(&self) -> Option<&LiteralLikeNodeBase> {
        self.data.literal_like_data()
    }

    /// `n.data.TemplateLiteralLikeData()`
    pub fn template_literal_like_data(&self) -> Option<&TemplateLiteralLikeNodeBase> {
        self.data.template_literal_like_data()
    }

    /// `n.data.SubtreeFacts()`
    pub fn subtree_facts(&self, nodes: &[Node]) -> crate::SubtreeFacts {
        self.data.subtree_facts(self, nodes)
    }

    /// `n.Decorators()`
    pub fn decorators<'a>(&'a self, nodes: &'a [Node]) -> Vec<&'a Node> {
        let Some(modifiers) = self.modifiers() else {
            return Vec::new();
        };
        modifiers
            .nodes
            .iter()
            .map(|&id| &nodes[id])
            .filter(|n| crate::ast_generated::is_decorator(n))
            .collect()
    }

    /// `n.Symbol()` — the bound symbol for declarations, or `None`.
    pub fn symbol(&self) -> Option<SymbolId> {
        self.declaration_data().and_then(|d| d.symbol)
    }

    /// `n.LocalSymbol()`
    pub fn local_symbol(&self) -> Option<SymbolId> {
        self.exportable_data().and_then(|d| d.local_symbol)
    }

    /// `n.Locals()`
    pub fn locals(&self) -> Option<&SymbolTable> {
        self.locals_container_data().map(|d| &d.locals)
    }

    /// `n.Body()`
    pub fn body(&self) -> Option<NodeId> {
        self.body_data().and_then(|d| d.body)
    }

    /// `n.Text()`
    pub fn text<'a>(&'a self, nodes: &'a [Node]) -> Cow<'a, str> {
        match self.kind {
            Kind::Identifier => Cow::Borrowed(self.as_identifier().text.as_str()),
            Kind::PrivateIdentifier => Cow::Borrowed(self.as_private_identifier().text.as_str()),
            Kind::StringLiteral => {
                Cow::Borrowed(self.as_string_literal().literal_expression_base.literal_like_node_base.text.as_str())
            }
            Kind::NumericLiteral => {
                Cow::Borrowed(self.as_numeric_literal().literal_expression_base.literal_like_node_base.text.as_str())
            }
            Kind::BigIntLiteral => {
                Cow::Borrowed(self.as_big_int_literal().literal_expression_base.literal_like_node_base.text.as_str())
            }
            Kind::MetaProperty => {
                let name = self.as_meta_property().name.unwrap_or_else(|| {
                    panic!("MetaProperty without name in Node.Text")
                });
                nodes[name].text(nodes)
            }
            Kind::NoSubstitutionTemplateLiteral => Cow::Borrowed(
                self.as_no_substitution_template_literal()
                    .template_literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::TemplateHead => {
                Cow::Borrowed(self.as_template_head().template_literal_like_node_base.literal_like_node_base.text.as_str())
            }
            Kind::TemplateMiddle => {
                Cow::Borrowed(self.as_template_middle().template_literal_like_node_base.literal_like_node_base.text.as_str())
            }
            Kind::TemplateTail => {
                Cow::Borrowed(self.as_template_tail().template_literal_like_node_base.literal_like_node_base.text.as_str())
            }
            Kind::JsxNamespacedName => {
                let d = self.as_jsx_namespaced_name();
                let mut s = nodes[d.namespace.unwrap()].text(nodes).into_owned();
                s.push(':');
                s.push_str(&nodes[d.name.unwrap()].text(nodes));
                Cow::Owned(s)
            }
            Kind::RegularExpressionLiteral => Cow::Borrowed(
                self.as_regular_expression_literal()
                    .literal_expression_base.literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::JSDocText => Cow::Owned(self.as_js_doc_text().js_doc_comment_base.text.join("")),
            Kind::JSDocLink => Cow::Owned(self.as_js_doc_link().js_doc_comment_base.text.join("")),
            Kind::JSDocLinkCode => {
                Cow::Owned(self.as_js_doc_link_code().js_doc_comment_base.text.join(""))
            }
            Kind::JSDocLinkPlain => {
                Cow::Owned(self.as_js_doc_link_plain().js_doc_comment_base.text.join(""))
            }
            _ => panic!("Unhandled case in Node.Text: {}", self.kind_string()),
        }
    }

    /// `n.Expression()`
    pub fn expression(&self) -> Option<NodeId> {
        match self.kind {
            Kind::PropertyAccessExpression => self.as_property_access_expression().expression,
            Kind::ElementAccessExpression => self.as_element_access_expression().expression,
            Kind::ParenthesizedExpression => self.as_parenthesized_expression().expression,
            Kind::CallExpression => self.as_call_expression().expression,
            Kind::NewExpression => self.as_new_expression().expression,
            Kind::ExpressionWithTypeArguments => self.as_expression_with_type_arguments().expression,
            Kind::ComputedPropertyName => self.as_computed_property_name().expression,
            Kind::NonNullExpression => self.as_non_null_expression().expression,
            Kind::TypeAssertionExpression => self.as_type_assertion().expression,
            Kind::AsExpression => self.as_as_expression().expression,
            Kind::SatisfiesExpression => self.as_satisfies_expression().expression,
            Kind::TypeOfExpression => self.as_type_of_expression().expression,
            Kind::SpreadAssignment => self.as_spread_assignment().expression,
            Kind::SpreadElement => self.as_spread_element().expression,
            Kind::TemplateSpan => self.as_template_span().expression,
            Kind::DeleteExpression => self.as_delete_expression().expression,
            Kind::VoidExpression => self.as_void_expression().expression,
            Kind::AwaitExpression => self.as_await_expression().expression,
            Kind::YieldExpression => self.as_yield_expression().expression,
            Kind::PartiallyEmittedExpression => self.as_partially_emitted_expression().expression,
            Kind::IfStatement => self.as_if_statement().expression,
            Kind::DoStatement => self.as_do_statement().expression,
            Kind::WhileStatement => self.as_while_statement().expression,
            Kind::WithStatement => self.as_with_statement().expression,
            Kind::ForInStatement | Kind::ForOfStatement => {
                self.as_for_in_or_of_statement().expression
            }
            Kind::SwitchStatement => self.as_switch_statement().expression,
            Kind::CaseClause => self.as_case_or_default_clause().expression,
            Kind::ExpressionStatement => self.as_expression_statement().expression,
            Kind::ReturnStatement => self.as_return_statement().expression,
            Kind::ThrowStatement => self.as_throw_statement().expression,
            Kind::ExternalModuleReference => self.as_external_module_reference().expression,
            Kind::ExportAssignment => self.as_export_assignment().expression,
            Kind::Decorator => self.as_decorator().expression,
            Kind::JsxExpression => self.as_jsx_expression().expression,
            Kind::JsxSpreadAttribute => self.as_jsx_spread_attribute().expression,
            _ => panic!("Unhandled case in Node.Expression: {}", self.kind_string()),
        }
    }

    /// `mutableNode.SetExpression(expr)`
    pub fn set_expression(&mut self, expr: Option<NodeId>) {
        let kind = self.kind;
        let data = &mut self.data;
        match kind {
            Kind::PropertyAccessExpression => data.as_property_access_expression_mut().expression = expr,
            Kind::ElementAccessExpression => data.as_element_access_expression_mut().expression = expr,
            Kind::ParenthesizedExpression => data.as_parenthesized_expression_mut().expression = expr,
            Kind::CallExpression => data.as_call_expression_mut().expression = expr,
            Kind::NewExpression => data.as_new_expression_mut().expression = expr,
            Kind::ExpressionWithTypeArguments => {
                data.as_expression_with_type_arguments_mut().expression = expr;
            }
            Kind::ComputedPropertyName => data.as_computed_property_name_mut().expression = expr,
            Kind::NonNullExpression => data.as_non_null_expression_mut().expression = expr,
            Kind::TypeAssertionExpression => data.as_type_assertion_mut().expression = expr,
            Kind::AsExpression => data.as_as_expression_mut().expression = expr,
            Kind::SatisfiesExpression => data.as_satisfies_expression_mut().expression = expr,
            Kind::TypeOfExpression => data.as_type_of_expression_mut().expression = expr,
            Kind::SpreadAssignment => data.as_spread_assignment_mut().expression = expr,
            Kind::SpreadElement => data.as_spread_element_mut().expression = expr,
            Kind::TemplateSpan => data.as_template_span_mut().expression = expr,
            Kind::DeleteExpression => data.as_delete_expression_mut().expression = expr,
            Kind::VoidExpression => data.as_void_expression_mut().expression = expr,
            Kind::AwaitExpression => data.as_await_expression_mut().expression = expr,
            Kind::YieldExpression => data.as_yield_expression_mut().expression = expr,
            Kind::PartiallyEmittedExpression => {
                data.as_partially_emitted_expression_mut().expression = expr;
            }
            Kind::IfStatement => data.as_if_statement_mut().expression = expr,
            Kind::DoStatement => data.as_do_statement_mut().expression = expr,
            Kind::WhileStatement => data.as_while_statement_mut().expression = expr,
            Kind::WithStatement => data.as_with_statement_mut().expression = expr,
            Kind::ForInStatement | Kind::ForOfStatement => {
                data.as_for_in_or_of_statement_mut().expression = expr;
            }
            Kind::SwitchStatement => data.as_switch_statement_mut().expression = expr,
            Kind::CaseClause => data.as_case_or_default_clause_mut().expression = expr,
            Kind::ExpressionStatement => data.as_expression_statement_mut().expression = expr,
            Kind::ReturnStatement => data.as_return_statement_mut().expression = expr,
            Kind::ThrowStatement => data.as_throw_statement_mut().expression = expr,
            Kind::ExternalModuleReference => data.as_external_module_reference_mut().expression = expr,
            Kind::ExportAssignment => data.as_export_assignment_mut().expression = expr,
            Kind::Decorator => data.as_decorator_mut().expression = expr,
            Kind::JsxExpression => data.as_jsx_expression_mut().expression = expr,
            Kind::JsxSpreadAttribute => data.as_jsx_spread_attribute_mut().expression = expr,
            _ => panic!("Unhandled case in mutableNode.SetExpression: {}", kind.kind_string()),
        }
    }

    /// `n.RawText()`
    pub fn raw_text(&self) -> &str {
        match self.kind {
            Kind::TemplateHead => self.as_template_head().template_literal_like_node_base.raw_text.as_str(),
            Kind::TemplateMiddle => {
                self.as_template_middle().template_literal_like_node_base.raw_text.as_str()
            }
            Kind::TemplateTail => self.as_template_tail().template_literal_like_node_base.raw_text.as_str(),
            _ => panic!("Unhandled case in Node.RawText: {}", self.kind_string()),
        }
    }

    /// `n.ArgumentList()`
    pub fn argument_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::CallExpression => self.as_call_expression().arguments.as_ref(),
            Kind::NewExpression => self.as_new_expression().arguments.as_ref(),
            _ => panic!("Unhandled case in Node.Arguments: {}", self.kind_string()),
        }
    }

    /// `n.Arguments()`
    pub fn arguments<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.argument_list().map(|l| l.nodes())
    }

    /// `n.TypeArgumentList()`
    pub fn type_argument_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::CallExpression => self.as_call_expression().type_arguments.as_ref(),
            Kind::NewExpression => self.as_new_expression().type_arguments.as_ref(),
            Kind::TaggedTemplateExpression => {
                self.as_tagged_template_expression().type_arguments.as_ref()
            }
            Kind::TypeReference => self.as_type_reference_node().node_with_type_arguments_base.type_arguments.as_ref(),
            Kind::ExpressionWithTypeArguments => {
                self.as_expression_with_type_arguments().type_arguments.as_ref()
            }
            Kind::ImportType => self.as_import_type_node().node_with_type_arguments_base.type_arguments.as_ref(),
            Kind::TypeQuery => self.as_type_query_node().node_with_type_arguments_base.type_arguments.as_ref(),
            Kind::JsxOpeningElement => self.as_jsx_opening_element().type_arguments.as_ref(),
            Kind::JsxSelfClosingElement => self.as_jsx_self_closing_element().type_arguments.as_ref(),
            _ => panic!("Unhandled case in Node.TypeArguments"),
        }
    }

    /// `n.TypeArguments()`
    pub fn type_arguments<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.type_argument_list().map(|l| l.nodes())
    }

    /// `n.TypeParameterList()`
    pub fn type_parameter_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::ClassDeclaration => self.as_class_declaration().class_like_base.type_parameters.as_ref(),
            Kind::ClassExpression => self.as_class_expression().class_like_base.type_parameters.as_ref(),
            Kind::InterfaceDeclaration => {
                self.as_interface_declaration().type_parameters.as_ref()
            }
            Kind::TypeAliasDeclaration | Kind::JSTypeAliasDeclaration => {
                self.as_type_alias_declaration().type_parameters.as_ref()
            }
            Kind::JSDocTemplateTag => self.as_js_doc_template_tag().type_parameters.as_ref(),
            _ => {
                let func_like = self
                    .function_like_data()
                    .unwrap_or_else(|| panic!("Unhandled case in Node.TypeParameterList"));
                func_like.type_parameters.as_ref()
            }
        }
    }

    /// `n.TypeParameters()`
    pub fn type_parameters<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.type_parameter_list().map(|l| l.nodes())
    }

    /// `n.MemberList()`
    pub fn member_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::ClassDeclaration => self.as_class_declaration().class_like_base.members.as_ref(),
            Kind::ClassExpression => self.as_class_expression().class_like_base.members.as_ref(),
            Kind::InterfaceDeclaration => self.as_interface_declaration().members.as_ref(),
            Kind::EnumDeclaration => self.as_enum_declaration().members.as_ref(),
            Kind::TypeLiteral => self.as_type_literal_node().members.as_ref(),
            Kind::MappedType => self.as_mapped_type_node().members.as_ref(),
            _ => panic!("Unhandled case in Node.MemberList: {}", self.kind_string()),
        }
    }

    /// `n.Members()`
    pub fn members<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.member_list().map(|l| l.nodes())
    }

    /// `n.StatementList()`
    pub fn statement_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::SourceFile => self.as_source_file().statements.as_ref(),
            Kind::Block => self.as_block().statements.as_ref(),
            Kind::ModuleBlock => self.as_module_block().statements.as_ref(),
            Kind::CaseClause | Kind::DefaultClause => {
                self.as_case_or_default_clause().statements.as_ref()
            }
            _ => panic!("Unhandled case in Node.StatementList: {}", self.kind_string()),
        }
    }

    /// `n.Statements()`
    pub fn statements<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.statement_list().map(|l| l.nodes())
    }

    /// `n.CanHaveStatements()`
    pub fn can_have_statements(&self) -> bool {
        matches!(
            self.kind,
            Kind::SourceFile | Kind::Block | Kind::ModuleBlock | Kind::CaseClause | Kind::DefaultClause
        )
    }

    /// `n.ModifierFlags()`
    pub fn modifier_flags(&self) -> ModifierFlags {
        match self.modifiers() {
            Some(modifiers) => modifiers.modifier_flags,
            None => ModifierFlags::NONE,
        }
    }

    /// `n.ModifierNodes()`
    pub fn modifier_nodes<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.modifiers().map(|m| m.nodes())
    }

    /// `n.Type()`
    pub fn type_(&self) -> Option<NodeId> {
        match self.kind {
            Kind::VariableDeclaration => self.as_variable_declaration().type_,
            Kind::Parameter => self.as_parameter_declaration().type_,
            Kind::PropertySignature => self.as_property_signature_declaration().type_,
            Kind::PropertyDeclaration => self.as_property_declaration().type_,
            Kind::PropertyAssignment => self.as_property_assignment().type_,
            Kind::ShorthandPropertyAssignment => self.as_shorthand_property_assignment().type_,
            Kind::TypePredicate => self.as_type_predicate_node().type_,
            Kind::ParenthesizedType => self.as_parenthesized_type_node().type_,
            Kind::TypeOperator => self.as_type_operator_node().type_,
            Kind::MappedType => self.as_mapped_type_node().type_,
            Kind::TypeAssertionExpression => self.as_type_assertion().type_,
            Kind::AsExpression => self.as_as_expression().type_,
            Kind::SatisfiesExpression => self.as_satisfies_expression().type_,
            Kind::TypeAliasDeclaration | Kind::JSTypeAliasDeclaration => {
                self.as_type_alias_declaration().type_
            }
            Kind::NamedTupleMember => self.as_named_tuple_member().type_,
            Kind::OptionalType => self.as_optional_type_node().type_,
            Kind::RestType => self.as_rest_type_node().type_,
            Kind::TemplateLiteralTypeSpan => self.as_template_literal_type_span().type_,
            Kind::JSDocTypeExpression => self.as_js_doc_type_expression().type_,
            Kind::JSDocParameterTag | Kind::JSDocPropertyTag => {
                self.as_js_doc_parameter_or_property_tag().type_expression
            }
            Kind::JSDocNullableType => self.as_js_doc_nullable_type().type_,
            Kind::JSDocNonNullableType => self.as_js_doc_non_nullable_type().type_,
            Kind::JSDocOptionalType => self.as_js_doc_optional_type().type_,
            Kind::ExportAssignment => self.as_export_assignment().type_,
            Kind::BinaryExpression => self.as_binary_expression().type_,
            _ => {
                if let Some(func_like) = self.function_like_data() {
                    func_like.type_
                } else {
                    None
                }
            }
        }
    }

    /// `mutableNode.SetType(t)`
    pub fn set_type(&mut self, t: Option<NodeId>) {
        let kind = self.kind;
        let data = &mut self.data;
        match kind {
            Kind::VariableDeclaration => data.as_variable_declaration_mut().type_ = t,
            Kind::Parameter => data.as_parameter_declaration_mut().type_ = t,
            Kind::PropertySignature => data.as_property_signature_declaration_mut().type_ = t,
            Kind::PropertyDeclaration => data.as_property_declaration_mut().type_ = t,
            Kind::PropertyAssignment => data.as_property_assignment_mut().type_ = t,
            Kind::ShorthandPropertyAssignment => data.as_shorthand_property_assignment_mut().type_ = t,
            Kind::TypePredicate => data.as_type_predicate_node_mut().type_ = t,
            Kind::ParenthesizedType => data.as_parenthesized_type_node_mut().type_ = t,
            Kind::TypeOperator => data.as_type_operator_node_mut().type_ = t,
            Kind::MappedType => data.as_mapped_type_node_mut().type_ = t,
            Kind::TypeAssertionExpression => data.as_type_assertion_mut().type_ = t,
            Kind::AsExpression => data.as_as_expression_mut().type_ = t,
            Kind::SatisfiesExpression => data.as_satisfies_expression_mut().type_ = t,
            Kind::TypeAliasDeclaration | Kind::JSTypeAliasDeclaration => {
                data.as_type_alias_declaration_mut().type_ = t;
            }
            Kind::NamedTupleMember => data.as_named_tuple_member_mut().type_ = t,
            Kind::OptionalType => data.as_optional_type_node_mut().type_ = t,
            Kind::RestType => data.as_rest_type_node_mut().type_ = t,
            Kind::TemplateLiteralTypeSpan => data.as_template_literal_type_span_mut().type_ = t,
            Kind::JSDocTypeExpression => data.as_js_doc_type_expression_mut().type_ = t,
            Kind::JSDocParameterTag | Kind::JSDocPropertyTag => {
                data.as_js_doc_parameter_or_property_tag_mut().type_expression = t;
            }
            Kind::JSDocNullableType => data.as_js_doc_nullable_type_mut().type_ = t,
            Kind::JSDocNonNullableType => data.as_js_doc_non_nullable_type_mut().type_ = t,
            Kind::JSDocOptionalType => data.as_js_doc_optional_type_mut().type_ = t,
            Kind::ExportAssignment => data.as_export_assignment_mut().type_ = t,
            Kind::BinaryExpression => data.as_binary_expression_mut().type_ = t,
            _ => {
                if let Some(func_like) = self.data.function_like_data_mut() {
                    func_like.type_ = t;
                } else {
                    panic!("Unhandled case in mutableNode.SetType: {}", kind.kind_string());
                }
            }
        }
    }

    /// `n.Initializer()`
    pub fn initializer(&self) -> Option<NodeId> {
        match self.kind {
            Kind::VariableDeclaration => self.as_variable_declaration().initializer,
            Kind::Parameter => self.as_parameter_declaration().initializer,
            Kind::BindingElement => self.as_binding_element().initializer,
            Kind::PropertyDeclaration => self.as_property_declaration().initializer,
            Kind::PropertySignature => self.as_property_signature_declaration().initializer,
            Kind::PropertyAssignment => self.as_property_assignment().initializer,
            Kind::EnumMember => self.as_enum_member().initializer,
            Kind::ForStatement => self.as_for_statement().initializer,
            Kind::ForInStatement | Kind::ForOfStatement => self.as_for_in_or_of_statement().initializer,
            Kind::JsxAttribute => self.as_jsx_attribute().initializer,
            _ => panic!("Unhandled case in Node.Initializer"),
        }
    }

    /// `mutableNode.SetInitializer(initializer)`
    pub fn set_initializer(&mut self, initializer: Option<NodeId>) {
        let kind = self.kind;
        let data = &mut self.data;
        match kind {
            Kind::VariableDeclaration => data.as_variable_declaration_mut().initializer = initializer,
            Kind::Parameter => data.as_parameter_declaration_mut().initializer = initializer,
            Kind::BindingElement => data.as_binding_element_mut().initializer = initializer,
            Kind::PropertyDeclaration => data.as_property_declaration_mut().initializer = initializer,
            Kind::PropertySignature => data.as_property_signature_declaration_mut().initializer = initializer,
            Kind::PropertyAssignment => data.as_property_assignment_mut().initializer = initializer,
            Kind::EnumMember => data.as_enum_member_mut().initializer = initializer,
            Kind::ForStatement => data.as_for_statement_mut().initializer = initializer,
            Kind::ForInStatement | Kind::ForOfStatement => {
                data.as_for_in_or_of_statement_mut().initializer = initializer;
            }
            Kind::JsxAttribute => data.as_jsx_attribute_mut().initializer = initializer,
            _ => panic!("Unhandled case in mutableNode.SetInitializer"),
        }
    }

    /// `n.TagName()`
    pub fn tag_name(&self) -> Option<NodeId> {
        match self.kind {
            Kind::JsxOpeningElement => self.as_jsx_opening_element().tag_name,
            Kind::JsxClosingElement => self.as_jsx_closing_element().tag_name,
            Kind::JsxSelfClosingElement => self.as_jsx_self_closing_element().tag_name,
            Kind::JSDocUnknownTag => self.as_js_doc_unknown_tag().js_doc_tag_base.tag_name,
            Kind::JSDocAugmentsTag => self.as_js_doc_augments_tag().js_doc_tag_base.tag_name,
            Kind::JSDocImplementsTag => self.as_js_doc_implements_tag().js_doc_tag_base.tag_name,
            Kind::JSDocDeprecatedTag => self.as_js_doc_deprecated_tag().js_doc_tag_base.tag_name,
            Kind::JSDocPublicTag => self.as_js_doc_public_tag().js_doc_tag_base.tag_name,
            Kind::JSDocPrivateTag => self.as_js_doc_private_tag().js_doc_tag_base.tag_name,
            Kind::JSDocProtectedTag => self.as_js_doc_protected_tag().js_doc_tag_base.tag_name,
            Kind::JSDocReadonlyTag => self.as_js_doc_readonly_tag().js_doc_tag_base.tag_name,
            Kind::JSDocOverrideTag => self.as_js_doc_override_tag().js_doc_tag_base.tag_name,
            Kind::JSDocCallbackTag => self.as_js_doc_callback_tag().js_doc_tag_base.tag_name,
            Kind::JSDocOverloadTag => self.as_js_doc_overload_tag().js_doc_tag_base.tag_name,
            Kind::JSDocParameterTag | Kind::JSDocPropertyTag => {
                self.as_js_doc_parameter_or_property_tag().js_doc_tag_base.tag_name
            }
            Kind::JSDocReturnTag => self.as_js_doc_return_tag().js_doc_tag_base.tag_name,
            Kind::JSDocThisTag => self.as_js_doc_this_tag().js_doc_tag_base.tag_name,
            Kind::JSDocTypeTag => self.as_js_doc_type_tag().js_doc_tag_base.tag_name,
            Kind::JSDocTemplateTag => self.as_js_doc_template_tag().js_doc_tag_base.tag_name,
            Kind::JSDocTypedefTag => self.as_js_doc_typedef_tag().js_doc_tag_base.tag_name,
            Kind::JSDocSeeTag => self.as_js_doc_see_tag().js_doc_tag_base.tag_name,
            Kind::JSDocSatisfiesTag => self.as_js_doc_satisfies_tag().js_doc_tag_base.tag_name,
            Kind::JSDocThrowsTag => self.as_js_doc_throws_tag().js_doc_tag_base.tag_name,
            Kind::JSDocImportTag => self.as_js_doc_import_tag().js_doc_tag_base.tag_name,
            _ => panic!("Unhandled case in Node.TagName: {}", self.kind_string()),
        }
    }

    /// `n.PropertyName()`
    pub fn property_name(&self) -> Option<NodeId> {
        match self.kind {
            Kind::ImportSpecifier => self.as_import_specifier().property_name,
            Kind::ExportSpecifier => self.as_export_specifier().property_name,
            Kind::BindingElement => self.as_binding_element().property_name,
            _ => None,
        }
    }

    /// `n.PropertyNameOrName()`
    pub fn property_name_or_name(&self) -> Option<NodeId> {
        self.property_name().or_else(|| self.name())
    }

    /// `n.IsTypeOnly()`
    pub fn is_type_only(&self) -> bool {
        match self.kind {
            Kind::ImportEqualsDeclaration => self.as_import_equals_declaration().is_type_only,
            Kind::ImportSpecifier => self.as_import_specifier().is_type_only,
            Kind::ImportClause => self.as_import_clause().phase_modifier == Kind::TypeKeyword,
            Kind::ExportDeclaration => self.as_export_declaration().is_type_only,
            Kind::ExportSpecifier => self.as_export_specifier().is_type_only,
            _ => false,
        }
    }

    /// `n.CommentList()`
    ///
    /// If updating this function, also update `hasComment`.
    pub fn comment_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::JSDoc => self.as_js_doc().comment.as_ref(),
            Kind::JSDocUnknownTag => self.as_js_doc_unknown_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocAugmentsTag => self.as_js_doc_augments_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocImplementsTag => self.as_js_doc_implements_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocDeprecatedTag => self.as_js_doc_deprecated_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocPublicTag => self.as_js_doc_public_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocPrivateTag => self.as_js_doc_private_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocProtectedTag => self.as_js_doc_protected_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocReadonlyTag => self.as_js_doc_readonly_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocOverrideTag => self.as_js_doc_override_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocCallbackTag => self.as_js_doc_callback_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocOverloadTag => self.as_js_doc_overload_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocParameterTag | Kind::JSDocPropertyTag => {
                self.as_js_doc_parameter_or_property_tag().js_doc_tag_base.comment.as_ref()
            }
            Kind::JSDocReturnTag => self.as_js_doc_return_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocThisTag => self.as_js_doc_this_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocTypeTag => self.as_js_doc_type_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocTemplateTag => self.as_js_doc_template_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocTypedefTag => self.as_js_doc_typedef_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocSeeTag => self.as_js_doc_see_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocSatisfiesTag => self.as_js_doc_satisfies_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocThrowsTag => self.as_js_doc_throws_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocImportTag => self.as_js_doc_import_tag().js_doc_tag_base.comment.as_ref(),
            _ => panic!("Unhandled case in Node.CommentList: {}", self.kind_string()),
        }
    }

    /// `n.Comments()`
    pub fn comments<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.comment_list().map(|l| l.nodes())
    }

    /// `n.Label()`
    pub fn label(&self) -> Option<NodeId> {
        match self.kind {
            Kind::LabeledStatement => self.as_labeled_statement().label,
            Kind::BreakStatement => self.as_break_statement().label,
            Kind::ContinueStatement => self.as_continue_statement().label,
            _ => panic!("Unhandled case in Node.Label: {}", self.kind_string()),
        }
    }

    /// `n.Attributes()`
    pub fn attributes(&self) -> Option<NodeId> {
        match self.kind {
            Kind::JsxOpeningElement => self.as_jsx_opening_element().attributes,
            Kind::JsxSelfClosingElement => self.as_jsx_self_closing_element().attributes,
            Kind::ModuleDeclaration => self.as_module_declaration().attributes,
            _ => panic!("Unhandled case in Node.Attributes: {}", self.kind_string()),
        }
    }

    /// `n.Children()` — the JsxElement/JsxFragment children list.
    pub fn children(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::JsxElement => self.as_jsx_element().children.as_ref(),
            Kind::JsxFragment => self.as_jsx_fragment().children.as_ref(),
            _ => panic!("Unhandled case in Node.Children: {}", self.kind_string()),
        }
    }

    /// `n.ModuleSpecifier()`
    pub fn module_specifier(&self) -> Option<NodeId> {
        match self.kind {
            Kind::ImportDeclaration | Kind::JSImportDeclaration => {
                self.as_import_declaration().module_specifier
            }
            Kind::ExportDeclaration => self.as_export_declaration().module_specifier,
            Kind::JSDocImportTag => self.as_js_doc_import_tag().module_specifier,
            _ => panic!("Unhandled case in Node.ModuleSpecifier: {}", self.kind_string()),
        }
    }

    /// `n.ImportClause()`
    pub fn import_clause(&self) -> Option<NodeId> {
        match self.kind {
            Kind::ImportDeclaration | Kind::JSImportDeclaration => self.as_import_declaration().import_clause,
            Kind::JSDocImportTag => self.as_js_doc_import_tag().import_clause,
            _ => panic!("Unhandled case in Node.ImportClause: {}", self.kind_string()),
        }
    }

    /// `n.Statement()`
    pub fn statement(&self) -> Option<NodeId> {
        match self.kind {
            Kind::DoStatement => self.as_do_statement().iteration_statement_base.statement,
            Kind::WhileStatement => self.as_while_statement().iteration_statement_base.statement,
            Kind::ForStatement => self.as_for_statement().iteration_statement_base.statement,
            Kind::ForInStatement | Kind::ForOfStatement => self.as_for_in_or_of_statement().statement,
            Kind::WithStatement => self.as_with_statement().statement,
            Kind::LabeledStatement => self.as_labeled_statement().statement,
            _ => panic!("Unhandled case in Node.Statement: {}", self.kind_string()),
        }
    }

    /// `n.PropertyList()`
    pub fn property_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::ObjectLiteralExpression => self.as_object_literal_expression().properties.as_ref(),
            Kind::JsxAttributes => self.as_jsx_attributes().properties.as_ref(),
            _ => panic!("Unhandled case in Node.PropertyList: {}", self.kind_string()),
        }
    }

    /// `n.Properties()`
    pub fn properties<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.property_list().map(|l| l.nodes())
    }

    /// `n.ElementList()`
    pub fn element_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::NamedImports => self.as_named_imports().elements.as_ref(),
            Kind::NamedExports => self.as_named_exports().elements.as_ref(),
            Kind::ObjectBindingPattern | Kind::ArrayBindingPattern => {
                self.as_binding_pattern().elements.as_ref()
            }
            Kind::ArrayLiteralExpression => self.as_array_literal_expression().elements.as_ref(),
            Kind::TupleType => self.as_tuple_type_node().elements.as_ref(),
            _ => panic!("Unhandled case in Node.ElementList: {}", self.kind_string()),
        }
    }

    /// `n.Elements()`
    pub fn elements<'a>(&'a self) -> Option<&'a [NodeId]> {
        self.element_list().map(|l| l.nodes())
    }

    /// `n.PostfixToken()`
    pub fn postfix_token(&self) -> Option<NodeId> {
        match self.kind {
            Kind::MethodDeclaration => self.as_method_declaration().named_member_base.postfix_token,
            Kind::ShorthandPropertyAssignment => self.as_shorthand_property_assignment().named_member_base.postfix_token,
            Kind::MethodSignature => self.as_method_signature_declaration().named_member_base.postfix_token,
            Kind::PropertySignature => self.as_property_signature_declaration().named_member_base.postfix_token,
            Kind::PropertyAssignment => self.as_property_assignment().named_member_base.postfix_token,
            Kind::PropertyDeclaration => self.as_property_declaration().named_member_base.postfix_token,
            Kind::EnumMember => self.as_enum_member().named_member_base.postfix_token,
            Kind::GetAccessor => self.as_get_accessor_declaration().named_member_base.postfix_token,
            Kind::SetAccessor => self.as_set_accessor_declaration().named_member_base.postfix_token,
            _ => None,
        }
    }

    /// `n.QuestionToken()`
    pub fn question_token(&self, nodes: &[Node]) -> Option<NodeId> {
        match self.kind {
            Kind::Parameter => return self.as_parameter_declaration().question_token,
            Kind::ConditionalExpression => return self.as_conditional_expression().question_token,
            Kind::MappedType => return self.as_mapped_type_node().question_token,
            Kind::NamedTupleMember => return self.as_named_tuple_member().question_token,
            _ => {}
        }
        let postfix = self.postfix_token()?;
        (nodes[postfix].kind == Kind::QuestionToken).then_some(postfix)
    }

    /// `n.QuestionDotToken()`
    pub fn question_dot_token(&self) -> Option<NodeId> {
        match self.kind {
            Kind::ElementAccessExpression => self.as_element_access_expression().question_dot_token,
            Kind::PropertyAccessExpression => self.as_property_access_expression().question_dot_token,
            Kind::CallExpression => self.as_call_expression().question_dot_token,
            Kind::TaggedTemplateExpression => self.as_tagged_template_expression().question_dot_token,
            _ => panic!("Unhandled case in Node.QuestionDotToken: {}", self.kind_string()),
        }
    }

    /// `n.TypeExpression()`
    pub fn type_expression(&self) -> Option<NodeId> {
        match self.kind {
            Kind::JSDocParameterTag | Kind::JSDocPropertyTag => {
                self.as_js_doc_parameter_or_property_tag().type_expression
            }
            Kind::JSDocReturnTag => self.as_js_doc_return_tag().type_expression,
            Kind::JSDocTypeTag => self.as_js_doc_type_tag().type_expression,
            Kind::JSDocTypedefTag => self.as_js_doc_typedef_tag().type_expression,
            Kind::JSDocCallbackTag => self.as_js_doc_callback_tag().type_expression,
            Kind::JSDocSatisfiesTag => self.as_js_doc_satisfies_tag().type_expression,
            Kind::JSDocThrowsTag => self.as_js_doc_throws_tag().type_expression,
            _ => panic!("Unhandled case in Node.TypeExpression: {}", self.kind_string()),
        }
    }

    /// `n.ClassName()`
    pub fn class_name(&self) -> Option<NodeId> {
        match self.kind {
            Kind::JSDocAugmentsTag => self.as_js_doc_augments_tag().class_name,
            Kind::JSDocImplementsTag => self.as_js_doc_implements_tag().class_name,
            _ => panic!("Unhandled case in Node.ClassName: {}", self.kind_string()),
        }
    }

    /// Contains-check that resolves `parent` ids through the node arena —
    /// the usable form of Go's `n.Contains(descendant)` in this port. Panics
    /// if `descendant` is not parented except when it is a `SourceFile`.
    pub fn contains(&self, nodes: &[Node], mut descendant: Option<NodeId>) -> bool {
        while let Some(d) = descendant {
            if nodes[d].id == self.id {
                return true;
            }
            let parent = nodes[d].parent;
            if parent.is_none() && !crate::ast_generated::is_source_file(&nodes[d]) {
                panic!("descendant is not parented");
            }
            descendant = parent;
        }
        false
    }
}

// Small source-file support types ported from ast.go. The `SourceFile`
// container itself lives in `crate::source_file`.

/// `type PatternAmbientModule struct`
#[derive(Clone, Default)]
pub struct PatternAmbientModule {
    pub pattern: tsc_core::pattern::Pattern,
    pub symbol: Option<SymbolId>,
}

/// `type CommentDirectiveKind int32`
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub enum CommentDirectiveKind {
    #[default]
    Unknown = 0,
    ExpectError = 1,
    Ignore = 2,
}

/// `type CommentDirective struct`
#[derive(Clone, Copy, Default)]
pub struct CommentDirective {
    pub loc: TextRange,
    pub kind: CommentDirectiveKind,
}

/// `type SourceFileMetaData struct`
#[derive(Clone, Default)]
pub struct SourceFileMetaData {
    pub package_json_type: String,
    pub package_json_directory: RootedDirectoryPath,
    /// `core.ResolutionMode` is a Go alias for `ModuleKind`.
    pub implied_node_format: ModuleKind,
}

/// `type CheckJsDirective struct`
#[derive(Clone, Copy, Default)]
pub struct CheckJsDirective {
    pub enabled: bool,
    pub range: CommentRange,
}

/// `type CommentRange struct`
#[derive(Clone, Copy, Default)]
pub struct CommentRange {
    pub text_range: TextRange,
    pub kind: Kind,
    pub has_trailing_new_line: bool,
}

// SourceFile — hand-written traversal, construction, update, and clone
// (Go's `SourceFile` methods are hand-written in ast.go; the generator
// leaves them to this module via `custom` markers in kinds.toml).

/// `(node *SourceFile) ForEachChild` — `forEachChild` for Kind::SourceFile.
pub fn for_each_child_source_file(
    d: &SourceFile,
    visitor: &mut Visitor<'_>,
    nodes: &[Node],
) -> bool {
    visit_node_list(visitor, &d.statements, nodes) || visit(visitor, d.end_of_file_token, nodes)
}

/// `(node *SourceFile) VisitEachChild` — rebuilds via `UpdateSourceFile`.
pub fn visit_each_child_source_file(
    cx: &mut crate::visitor::VisitorCx<'_>,
    v: &crate::visitor::NodeVisitor<'_>,
    node: NodeId,
) -> Option<NodeId> {
    let (statements, end_of_file_token) = {
        let d = cx.nodes[node].as_source_file();
        (d.statements.clone(), d.end_of_file_token)
    };
    let statements = v.visit_top_level_statements_hooked(cx, statements);
    let end_of_file_token = v.visit_token_hooked(cx, end_of_file_token);
    cx.factory
        .update_source_file(cx.nodes, node, statements, end_of_file_token)
}

/// `forEachChild_JSDocParameterOrPropertyTag` — the `IsNameFirst` conditional
/// ordering is a hand-written special case in ast.go.
pub fn for_each_child_js_doc_parameter_or_property_tag(
    d: &JSDocParameterOrPropertyTag,
    visitor: &mut Visitor<'_>,
    nodes: &[Node],
) -> bool {
    visit(visitor, d.js_doc_tag_base.tag_name, nodes)
        || (d.is_name_first
            && (visit(visitor, d.name, nodes) || visit(visitor, d.type_expression, nodes)))
        || (!d.is_name_first
            && (visit(visitor, d.type_expression, nodes) || visit(visitor, d.name, nodes)))
        || visit_node_list(visitor, &d.js_doc_tag_base.comment, nodes)
}

/// `visitEachChild_JSDocParameterOrPropertyTag`.
pub fn visit_each_child_js_doc_parameter_or_property_tag(
    cx: &mut crate::visitor::VisitorCx<'_>,
    v: &crate::visitor::NodeVisitor<'_>,
    node: NodeId,
) -> Option<NodeId> {
    let (tag_name, name, is_bracketed, type_expression, is_name_first, comment) = {
        let d = cx.nodes[node].as_js_doc_parameter_or_property_tag();
        (
            d.js_doc_tag_base.tag_name,
            d.name,
            d.is_bracketed,
            d.type_expression,
            d.is_name_first,
            d.js_doc_tag_base.comment.clone(),
        )
    };
    let tag_name = v.visit_node_hooked(cx, tag_name);
    let name = v.visit_node_hooked(cx, name);
    let type_expression = v.visit_node_hooked(cx, type_expression);
    let comment = v.visit_nodes_hooked(cx, comment);
    cx.factory.update_js_doc_parameter_or_property_tag(
        cx.nodes,
        node,
        tag_name,
        name,
        is_bracketed,
        type_expression,
        is_name_first,
        comment,
    )
}

impl NodeFactory<'_> {
    /// `f.NewSourceFile(opts, text, statements, endOfFileToken)` — the parse
    /// options collapse to `file_name`/`language_variant`/`script_kind` here;
    /// the remaining `SourceFileParseOptions` members are set post-construction.
    pub fn new_source_file(
        &mut self,
        nodes: &mut Vec<Node>,
        file_name: &str,
        text: &str,
        statements: Option<NodeList>,
        end_of_file_token: Option<NodeId>,
    ) -> NodeId {
        let mut data = SourceFile::default();
        data.file_name = file_name.to_string();
        data.text = text.to_string();
        data.statements = statements;
        data.end_of_file_token = end_of_file_token;
        self.new_node(nodes, Kind::SourceFile, NodeData::SourceFile(data))
    }

    /// `f.UpdateSourceFile` — `None` when nothing changed. Mirrors
    /// `updated.copyFrom(node)` by copying the non-constructor fields.
    pub fn update_source_file(
        &mut self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        statements: Option<NodeList>,
        end_of_file_token: Option<NodeId>,
    ) -> Option<NodeId> {
        let (changed, file_name, text) = {
            let d = nodes[node].as_source_file();
            (
                statements != d.statements || end_of_file_token != d.end_of_file_token,
                d.file_name.clone(),
                d.text.clone(),
            )
        };
        if changed {
            let updated =
                self.new_source_file(nodes, &file_name, &text, statements, end_of_file_token);
            copy_source_file_from(nodes, updated, node);
            return Some(update_node(nodes, updated, node, &mut self.hooks));
        }
        None
    }
}

/// `(node *SourceFile) copyFrom(other)` — copies every field not set by
/// `NewSourceFile`, then ORs the flags. Implemented by taking the new
/// file's data, filling it from `other`, and writing it back (the arena
/// forbids holding two mutable borrows).
fn copy_source_file_from(nodes: &mut Vec<Node>, new_file: NodeId, other: NodeId) {
    let mut d = std::mem::take(nodes[new_file].as_source_file_mut());
    {
        let o = nodes[other].as_source_file();
        d.language_variant = o.language_variant;
        d.script_kind = o.script_kind;
        d.is_declaration_file = o.is_declaration_file;
        d.uses_uri_style_node_core_modules = o.uses_uri_style_node_core_modules;
        d.identifier_count = o.identifier_count;
        d.imports = o.imports.clone();
        d.module_augmentations = o.module_augmentations.clone();
        d.ambient_module_names = o.ambient_module_names.clone();
        d.comment_directives = o.comment_directives.clone();
        d.pragmas = o.pragmas.clone();
        d.referenced_files = o.referenced_files.clone();
        d.type_reference_directives = o.type_reference_directives.clone();
        d.lib_reference_directives = o.lib_reference_directives.clone();
        d.check_js_directive = o.check_js_directive;
        d.node_count = o.node_count;
        d.text_count = o.text_count;
        d.common_js_module_indicator = o.common_js_module_indicator;
        d.external_module_indicator = o.external_module_indicator;
        d.symbol_count = o.symbol_count;
        d.pattern_ambient_modules = o.pattern_ambient_modules.clone();
        d.global_exports = o.global_exports.clone();
        d.reparsed_clones = o.reparsed_clones.clone();
    }
    *nodes[new_file].as_source_file_mut() = d;
    nodes[new_file].flags |= nodes[other].flags;
}

/// `(node *SourceFile) Clone(f)` — NewSourceFile + copyFrom.
pub(crate) fn clone_source_file(
    f: &mut NodeFactory<'_>,
    nodes: &mut Vec<Node>,
    node: NodeId,
) -> NodeId {
    let (file_name, text, statements, end_of_file_token) = {
        let d = nodes[node].as_source_file();
        (
            d.file_name.clone(),
            d.text.clone(),
            d.statements.clone(),
            d.end_of_file_token,
        )
    };
    let updated = f.new_source_file(nodes, &file_name, &text, statements, end_of_file_token);
    copy_source_file_from(nodes, updated, node);
    clone_node(nodes, updated, node, &mut f.hooks)
}

/// `f.NewCommentRange(kind, pos, end, hasTrailingNewLine)`
impl NodeFactory<'_> {
    pub fn new_comment_range(
        &self,
        kind: Kind,
        pos: TextPos,
        end: TextPos,
        has_trailing_new_line: bool,
    ) -> CommentRange {
        CommentRange {
            text_range: TextRange::new(pos, end),
            kind,
            has_trailing_new_line,
        }
    }
}

/// `type FileReference struct`
#[derive(Clone, Default)]
pub struct FileReference {
    pub text_range: TextRange,
    pub file_name: String,
    /// `core.ResolutionMode` is a Go alias for `ModuleKind`.
    pub resolution_mode: ModuleKind,
    pub preserve: bool,
}

/// `type PragmaArgument struct`
#[derive(Clone, Default)]
pub struct PragmaArgument {
    pub text_range: TextRange,
    pub name: String,
    pub value: String,
}

/// `type Pragma struct`
#[derive(Clone, Default)]
pub struct Pragma {
    pub comment_range: CommentRange,
    pub name: String,
    /// Go stores `map[string]PragmaArgument`; `OrderedMap` preserves
    /// deterministic insertion order.
    pub args: OrderedMap<String, PragmaArgument>,
}

/// `PragmaKindFlags` bitmask.
pub type PragmaKindFlags = u8;

pub const PRAGMA_KIND_TRIPLE_SLASH_XML: PragmaKindFlags = 1 << 0;
pub const PRAGMA_KIND_SINGLE_LINE: PragmaKindFlags = 1 << 1;
pub const PRAGMA_KIND_MULTI_LINE: PragmaKindFlags = 1 << 2;
pub const PRAGMA_KIND_FLAGS_NONE: PragmaKindFlags = 0;
pub const PRAGMA_KIND_ALL: PragmaKindFlags =
    PRAGMA_KIND_TRIPLE_SLASH_XML | PRAGMA_KIND_SINGLE_LINE | PRAGMA_KIND_MULTI_LINE;
pub const PRAGMA_KIND_DEFAULT: PragmaKindFlags = PRAGMA_KIND_ALL;

/// `type PragmaArgumentSpecification struct`
pub struct PragmaArgumentSpecification {
    pub name: &'static str,
    pub optional: bool,
    pub capture_span: bool,
}
