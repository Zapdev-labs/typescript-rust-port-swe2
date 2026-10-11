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
use std::collections::hash_map::Entry;
use std::sync::atomic::Ordering;
use std::sync::{Arc, RwLock};

use rustc_hash::{FxBuildHasher, FxHashMap};
use tsc_collections::{OrderedMap, Set};
use tsc_core::core::compute_ecma_line_starts;
use tsc_core::options_generated::ModuleKind;
use tsc_core::text::{TextPos, TextRange};
use tsc_spanmap::SpanMap;
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};

use crate::ast_generated::*;
use crate::diagnostic::DiagnosticRef;
use crate::ids::{NodeId, SymbolId};
use crate::kind_generated::Kind;
use crate::modifierflags::ModifierFlags;
use crate::nodeflags::NodeFlags;
use crate::parseoptions::SourceFileParseOptions;
use crate::positionmap::{PositionMap, compute_position_map};
use crate::symbol::SymbolTable;
use crate::tokenflags::TokenFlags;
use crate::utilities::{
    JsDeclarationKind, get_assignment_declaration_kind, get_non_assigned_name_of_declaration,
    get_source_file_of_node, has_syntactic_modifier, is_binding_pattern, is_property_name,
    is_string_or_numeric_literal_like, is_tag_name, literal_is_name,
};

// NodeList

/// A list of AST nodes with a shared source range, mirroring
/// `type NodeList struct` in ast.go.
#[derive(Clone, PartialEq, Default)]
pub struct NodeList {
    pub loc: TextRange,
    pub nodes: Box<[NodeId]>,
    /// `missingListNodes` sentinel — `true` marks the parser's "missing"
    /// list (a bracketed list whose opening token was absent), produced by
    /// `Parser.createMissingList`. Go detects it by comparing the backing
    /// array address against a shared cap-1 sentinel slice; a
    /// `Box<[NodeId]>` carries no capacity and cannot alias a static, so the
    /// marker is a flag instead.
    #[doc(hidden)]
    pub is_missing: bool,
}

impl NodeList {
    pub fn new(nodes: impl Into<Box<[NodeId]>>) -> NodeList {
        NodeList {
            loc: TextRange::undefined(),
            nodes: nodes.into(),
            is_missing: false,
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
        // Go clones share the sentinel backing array — a clone of a missing
        // list is still missing.
        result.is_missing = self.is_missing;
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

    /// `(list *ModifierList) HasTrailingComma` — promoted from the embedded
    /// `NodeList` in Go.
    pub fn has_trailing_comma(&self, nodes: &[Node]) -> bool {
        self.as_node_list().has_trailing_comma(nodes)
    }

    /// The embedded `NodeList` view (Go's promoted `NodeList` fields).
    pub fn as_node_list(&self) -> NodeList {
        NodeList {
            loc: self.loc,
            nodes: self.nodes.clone(),
            is_missing: false,
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
///
/// PORT: `Clone` produces a shallow structural copy — `NodeId`s inside the
/// data still reference arena slots — used by `ArenaCheckout` to leave a
/// frozen arena in the program's cell while emit mutates the live `Vec`.
#[derive(Clone)]
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

// PORT: lets `debug::fail_bad_syntax_kind!(node)` accept `Node`/`&Node`,
// matching Go's `interface{ KindString() string }` argument contract.
impl tsc_debug::KindString for Node {
    fn kind_string(&self) -> String {
        Node::kind_string(self).to_string()
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
    pub fn new_modifier_list(
        &self,
        nodes: &[Node],
        modifiers: impl Into<Box<[NodeId]>>,
    ) -> ModifierList {
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
    if updated != original
        && let Some(on_clone) = hooks.on_clone.as_mut()
    {
        on_clone(nodes, updated, original);
    }
    updated
}

// Child traversal helpers

/// The Go `Visitor` — a callback receiving a child `NodeId` (Go passes
/// `*Node`); returns `true` to stop traversal early.
pub type Visitor<'a> = dyn FnMut(NodeId) -> bool + 'a;

/// `visit(v, node)` — visits a single optional child.
pub fn visit(v: &mut Visitor<'_>, node: Option<NodeId>, _nodes: &[Node]) -> bool {
    node.is_some_and(v)
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
pub fn visit_nodes(v: &mut Visitor<'_>, children: &[NodeId], _nodes: &[Node]) -> bool {
    children.iter().any(|&id| v(id))
}

/// `visitModifiers(v, modifiers)` — visits each element of an optional
/// `ModifierList`.
pub fn visit_modifiers(
    v: &mut Visitor<'_>,
    modifiers: &Option<ModifierList>,
    nodes: &[Node],
) -> bool {
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
        let mut children: Vec<NodeId> = Vec::new();
        self.for_each_child(nodes, &mut |child| {
            children.push(child);
            false
        });
        children.into_iter().map(|id| &nodes[id])
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
        self.function_like_data()
            .and_then(|d| d.parameters.as_ref())
    }

    /// `n.Parameters()`
    pub fn parameters(&self) -> Option<&[NodeId]> {
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
            Kind::StringLiteral => Cow::Borrowed(
                self.as_string_literal()
                    .literal_expression_base
                    .literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::NumericLiteral => Cow::Borrowed(
                self.as_numeric_literal()
                    .literal_expression_base
                    .literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::BigIntLiteral => Cow::Borrowed(
                self.as_big_int_literal()
                    .literal_expression_base
                    .literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::MetaProperty => {
                let name = self
                    .as_meta_property()
                    .name
                    .unwrap_or_else(|| panic!("MetaProperty without name in Node.Text"));
                nodes[name].text(nodes)
            }
            Kind::NoSubstitutionTemplateLiteral => Cow::Borrowed(
                self.as_no_substitution_template_literal()
                    .template_literal_like_node_base
                    .literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::TemplateHead => Cow::Borrowed(
                self.as_template_head()
                    .template_literal_like_node_base
                    .literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::TemplateMiddle => Cow::Borrowed(
                self.as_template_middle()
                    .template_literal_like_node_base
                    .literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::TemplateTail => Cow::Borrowed(
                self.as_template_tail()
                    .template_literal_like_node_base
                    .literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::JsxNamespacedName => {
                let d = self.as_jsx_namespaced_name();
                let mut s = nodes[d.namespace.unwrap()].text(nodes).into_owned();
                s.push(':');
                s.push_str(&nodes[d.name.unwrap()].text(nodes));
                Cow::Owned(s)
            }
            Kind::RegularExpressionLiteral => Cow::Borrowed(
                self.as_regular_expression_literal()
                    .literal_expression_base
                    .literal_like_node_base
                    .text
                    .as_str(),
            ),
            Kind::JSDocText => Cow::Owned(self.as_js_doc_text().js_doc_comment_base.text.join("")),
            Kind::JSDocLink => Cow::Owned(self.as_js_doc_link().js_doc_comment_base.text.join("")),
            Kind::JSDocLinkCode => {
                Cow::Owned(self.as_js_doc_link_code().js_doc_comment_base.text.join(""))
            }
            Kind::JSDocLinkPlain => Cow::Owned(
                self.as_js_doc_link_plain()
                    .js_doc_comment_base
                    .text
                    .join(""),
            ),
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
            Kind::ExpressionWithTypeArguments => {
                self.as_expression_with_type_arguments().expression
            }
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
            Kind::PropertyAccessExpression => {
                data.as_property_access_expression_mut().expression = expr
            }
            Kind::ElementAccessExpression => {
                data.as_element_access_expression_mut().expression = expr
            }
            Kind::ParenthesizedExpression => {
                data.as_parenthesized_expression_mut().expression = expr
            }
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
            Kind::ExternalModuleReference => {
                data.as_external_module_reference_mut().expression = expr
            }
            Kind::ExportAssignment => data.as_export_assignment_mut().expression = expr,
            Kind::Decorator => data.as_decorator_mut().expression = expr,
            Kind::JsxExpression => data.as_jsx_expression_mut().expression = expr,
            Kind::JsxSpreadAttribute => data.as_jsx_spread_attribute_mut().expression = expr,
            _ => panic!(
                "Unhandled case in mutableNode.SetExpression: {}",
                kind.kind_string()
            ),
        }
    }

    /// `n.RawText()`
    pub fn raw_text(&self) -> &str {
        match self.kind {
            Kind::TemplateHead => self
                .as_template_head()
                .template_literal_like_node_base
                .raw_text
                .as_str(),
            Kind::TemplateMiddle => self
                .as_template_middle()
                .template_literal_like_node_base
                .raw_text
                .as_str(),
            Kind::TemplateTail => self
                .as_template_tail()
                .template_literal_like_node_base
                .raw_text
                .as_str(),
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
    pub fn arguments(&self) -> Option<&[NodeId]> {
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
            Kind::TypeReference => self
                .as_type_reference_node()
                .node_with_type_arguments_base
                .type_arguments
                .as_ref(),
            Kind::ExpressionWithTypeArguments => self
                .as_expression_with_type_arguments()
                .type_arguments
                .as_ref(),
            Kind::ImportType => self
                .as_import_type_node()
                .node_with_type_arguments_base
                .type_arguments
                .as_ref(),
            Kind::TypeQuery => self
                .as_type_query_node()
                .node_with_type_arguments_base
                .type_arguments
                .as_ref(),
            Kind::JsxOpeningElement => self.as_jsx_opening_element().type_arguments.as_ref(),
            Kind::JsxSelfClosingElement => {
                self.as_jsx_self_closing_element().type_arguments.as_ref()
            }
            _ => panic!("Unhandled case in Node.TypeArguments"),
        }
    }

    /// `n.TypeArguments()`
    pub fn type_arguments(&self) -> Option<&[NodeId]> {
        self.type_argument_list().map(|l| l.nodes())
    }

    /// `n.TypeParameterList()`
    pub fn type_parameter_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::ClassDeclaration => self
                .as_class_declaration()
                .class_like_base
                .type_parameters
                .as_ref(),
            Kind::ClassExpression => self
                .as_class_expression()
                .class_like_base
                .type_parameters
                .as_ref(),
            Kind::InterfaceDeclaration => self.as_interface_declaration().type_parameters.as_ref(),
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
    pub fn type_parameters(&self) -> Option<&[NodeId]> {
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
    pub fn members(&self) -> Option<&[NodeId]> {
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
            _ => panic!(
                "Unhandled case in Node.StatementList: {}",
                self.kind_string()
            ),
        }
    }

    /// `n.Statements()`
    pub fn statements(&self) -> Option<&[NodeId]> {
        self.statement_list().map(|l| l.nodes())
    }

    /// `n.CanHaveStatements()`
    pub fn can_have_statements(&self) -> bool {
        matches!(
            self.kind,
            Kind::SourceFile
                | Kind::Block
                | Kind::ModuleBlock
                | Kind::CaseClause
                | Kind::DefaultClause
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
    pub fn modifier_nodes(&self) -> Option<&[NodeId]> {
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
            Kind::ShorthandPropertyAssignment => {
                data.as_shorthand_property_assignment_mut().type_ = t
            }
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
                data.as_js_doc_parameter_or_property_tag_mut()
                    .type_expression = t;
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
                    panic!(
                        "Unhandled case in mutableNode.SetType: {}",
                        kind.kind_string()
                    );
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
            Kind::ForInStatement | Kind::ForOfStatement => {
                self.as_for_in_or_of_statement().initializer
            }
            Kind::JsxAttribute => self.as_jsx_attribute().initializer,
            _ => panic!("Unhandled case in Node.Initializer"),
        }
    }

    /// `mutableNode.SetInitializer(initializer)`
    pub fn set_initializer(&mut self, initializer: Option<NodeId>) {
        let kind = self.kind;
        let data = &mut self.data;
        match kind {
            Kind::VariableDeclaration => {
                data.as_variable_declaration_mut().initializer = initializer
            }
            Kind::Parameter => data.as_parameter_declaration_mut().initializer = initializer,
            Kind::BindingElement => data.as_binding_element_mut().initializer = initializer,
            Kind::PropertyDeclaration => {
                data.as_property_declaration_mut().initializer = initializer
            }
            Kind::PropertySignature => {
                data.as_property_signature_declaration_mut().initializer = initializer
            }
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
                self.as_js_doc_parameter_or_property_tag()
                    .js_doc_tag_base
                    .tag_name
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
            Kind::JSDocUnknownTag => self
                .as_js_doc_unknown_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocAugmentsTag => self
                .as_js_doc_augments_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocImplementsTag => self
                .as_js_doc_implements_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocDeprecatedTag => self
                .as_js_doc_deprecated_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocPublicTag => self.as_js_doc_public_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocPrivateTag => self
                .as_js_doc_private_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocProtectedTag => self
                .as_js_doc_protected_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocReadonlyTag => self
                .as_js_doc_readonly_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocOverrideTag => self
                .as_js_doc_override_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocCallbackTag => self
                .as_js_doc_callback_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocOverloadTag => self
                .as_js_doc_overload_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocParameterTag | Kind::JSDocPropertyTag => self
                .as_js_doc_parameter_or_property_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocReturnTag => self.as_js_doc_return_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocThisTag => self.as_js_doc_this_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocTypeTag => self.as_js_doc_type_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocTemplateTag => self
                .as_js_doc_template_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocTypedefTag => self
                .as_js_doc_typedef_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocSeeTag => self.as_js_doc_see_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocSatisfiesTag => self
                .as_js_doc_satisfies_tag()
                .js_doc_tag_base
                .comment
                .as_ref(),
            Kind::JSDocThrowsTag => self.as_js_doc_throws_tag().js_doc_tag_base.comment.as_ref(),
            Kind::JSDocImportTag => self.as_js_doc_import_tag().js_doc_tag_base.comment.as_ref(),
            _ => panic!("Unhandled case in Node.CommentList: {}", self.kind_string()),
        }
    }

    /// `n.Comments()`
    pub fn comments(&self) -> Option<&[NodeId]> {
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
            _ => panic!(
                "Unhandled case in Node.ModuleSpecifier: {}",
                self.kind_string()
            ),
        }
    }

    /// `n.ImportClause()`
    pub fn import_clause(&self) -> Option<NodeId> {
        match self.kind {
            Kind::ImportDeclaration | Kind::JSImportDeclaration => {
                self.as_import_declaration().import_clause
            }
            Kind::JSDocImportTag => self.as_js_doc_import_tag().import_clause,
            _ => panic!(
                "Unhandled case in Node.ImportClause: {}",
                self.kind_string()
            ),
        }
    }

    /// `n.Statement()`
    pub fn statement(&self) -> Option<NodeId> {
        match self.kind {
            Kind::DoStatement => self.as_do_statement().iteration_statement_base.statement,
            Kind::WhileStatement => self.as_while_statement().iteration_statement_base.statement,
            Kind::ForStatement => self.as_for_statement().iteration_statement_base.statement,
            Kind::ForInStatement | Kind::ForOfStatement => {
                self.as_for_in_or_of_statement().statement
            }
            Kind::WithStatement => self.as_with_statement().statement,
            Kind::LabeledStatement => self.as_labeled_statement().statement,
            _ => panic!("Unhandled case in Node.Statement: {}", self.kind_string()),
        }
    }

    /// `n.PropertyList()`
    pub fn property_list(&self) -> Option<&NodeList> {
        match self.kind {
            Kind::ObjectLiteralExpression => {
                self.as_object_literal_expression().properties.as_ref()
            }
            Kind::JsxAttributes => self.as_jsx_attributes().properties.as_ref(),
            _ => panic!(
                "Unhandled case in Node.PropertyList: {}",
                self.kind_string()
            ),
        }
    }

    /// `n.Properties()`
    pub fn properties(&self) -> Option<&[NodeId]> {
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
    pub fn elements(&self) -> Option<&[NodeId]> {
        self.element_list().map(|l| l.nodes())
    }

    /// `n.PostfixToken()`
    pub fn postfix_token(&self) -> Option<NodeId> {
        match self.kind {
            Kind::MethodDeclaration => self.as_method_declaration().named_member_base.postfix_token,
            Kind::ShorthandPropertyAssignment => {
                self.as_shorthand_property_assignment()
                    .named_member_base
                    .postfix_token
            }
            Kind::MethodSignature => {
                self.as_method_signature_declaration()
                    .named_member_base
                    .postfix_token
            }
            Kind::PropertySignature => {
                self.as_property_signature_declaration()
                    .named_member_base
                    .postfix_token
            }
            Kind::PropertyAssignment => {
                self.as_property_assignment()
                    .named_member_base
                    .postfix_token
            }
            Kind::PropertyDeclaration => {
                self.as_property_declaration()
                    .named_member_base
                    .postfix_token
            }
            Kind::EnumMember => self.as_enum_member().named_member_base.postfix_token,
            Kind::GetAccessor => {
                self.as_get_accessor_declaration()
                    .accessor_declaration_base
                    .named_member_base
                    .postfix_token
            }
            Kind::SetAccessor => {
                self.as_set_accessor_declaration()
                    .accessor_declaration_base
                    .named_member_base
                    .postfix_token
            }
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
            Kind::PropertyAccessExpression => {
                self.as_property_access_expression().question_dot_token
            }
            Kind::CallExpression => self.as_call_expression().question_dot_token,
            Kind::TaggedTemplateExpression => {
                self.as_tagged_template_expression().question_dot_token
            }
            _ => panic!(
                "Unhandled case in Node.QuestionDotToken: {}",
                self.kind_string()
            ),
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
            _ => panic!(
                "Unhandled case in Node.TypeExpression: {}",
                self.kind_string()
            ),
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

/// `type SourceFileLike interface` — `Text()` + `ECMALineMap()`.
pub trait SourceFileLike {
    /// `Text()`.
    fn text(&self) -> &str;
    /// `ECMALineMap()`.
    fn ecma_line_map(&self) -> &[TextPos];
}

/// `type TokenCacheKey struct` — `{parent *Node, loc core.TextRange}`.
///
/// PORT: `parent` is a `NodeId`; Go's `GetOrCreateToken` dereferences the
/// pointer unconditionally, so a nil parent would panic there anyway.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TokenCacheKey {
    pub parent: NodeId,
    pub loc: TextRange,
}

/// `xxh3.Uint128` — the language-service content hash stored on `SourceFile`.
/// Only the value type is needed here; the xxh3 hash function lands with the
/// API/encoder layer that computes it.
#[derive(Clone, Copy, Default, PartialEq, Eq, Hash, Debug)]
pub struct Uint128 {
    pub hi: u64,
    pub lo: u64,
}

/// `type MappedDiagnosticDirectivePolicy uint8`.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub enum MappedDiagnosticDirectivePolicy {
    /// `MappedDiagnosticDirectivePolicyIgnore`
    #[default]
    Ignore = 0,
    /// `MappedDiagnosticDirectivePolicyExpect`
    Expect = 1,
}

/// `type MappedDiagnosticDirective struct`
#[derive(Clone, Default)]
pub struct MappedDiagnosticDirective {
    pub original_range: TextRange,
    pub virtual_range: TextRange,
    pub policy: MappedDiagnosticDirectivePolicy,
    pub unused_code: i32,
    pub unused_message_text: String,
    pub source: String,
}

/// `type ContentMapperSourceFileInfo struct`
///
/// PORT: `*SourceFile` members are `NodeId`s into the owning arena;
/// `*spanmap.SpanMap` is a shared pointer, so `Option<Arc<SpanMap>>`.
#[derive(Clone, Default)]
pub struct ContentMapperSourceFileInfo {
    pub content_mapper: String,
    pub transform_identity: String,
    pub parse_options: SourceFileParseOptions,
    pub virtual_file_name: RootedFilePath,
    pub original_text: String,
    pub span_map: Option<Arc<SpanMap>>,
    pub diagnostic_directives: Vec<MappedDiagnosticDirective>,
    pub supplemental_source_files: Vec<NodeId>,
    pub canonical_source_file: Option<NodeId>,
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
pub fn visit_each_child_source_file<'v>(
    cx: &mut crate::visitor::VisitorCx<'_, '_>,
    v: &crate::visitor::NodeVisitor<'v>,
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
pub fn visit_each_child_js_doc_parameter_or_property_tag<'v>(
    cx: &mut crate::visitor::VisitorCx<'_, '_>,
    v: &crate::visitor::NodeVisitor<'v>,
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
    /// `f.NewSourceFile(opts, text, statements, endOfFileToken)` — sets
    /// `fileName`/`parseOptions`/`text`/`Statements`/`EndOfFileToken`; every
    /// other field keeps its zero value.
    pub fn new_source_file(
        &mut self,
        nodes: &mut Vec<Node>,
        opts: &SourceFileParseOptions,
        text: &str,
        statements: Option<NodeList>,
        end_of_file_token: Option<NodeId>,
    ) -> NodeId {
        let data = SourceFile {
            file_name: opts.file_name.clone(),
            parse_options: opts.clone(),
            text: text.to_string(),
            statements,
            end_of_file_token,
            ..Default::default()
        };
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
        let (changed, opts, text) = {
            let d = nodes[node].as_source_file();
            (
                statements != d.statements || end_of_file_token != d.end_of_file_token,
                d.parse_options.clone(),
                d.text.clone(),
            )
        };
        if changed {
            let updated = self.new_source_file(nodes, &opts, &text, statements, end_of_file_token);
            copy_source_file_from(nodes, updated, node);
            return Some(update_node(nodes, updated, node, &mut self.hooks));
        }
        None
    }
}

/// `(node *SourceFile) copyFrom(other)` — copies exactly the field list Go's
/// `copyFrom` copies (contentMapperInfo through ExternalModuleIndicator),
/// then ORs the flags. Fields set by `NewSourceFile` (text, parseOptions,
/// fileName, Statements, EndOfFileToken), the diagnostics, counters,
/// `checkJsDirective`, binder state, `ReparsedClones`, and every
/// lazily-computed cache are deliberately NOT copied — Go leaves them at
/// their zero values on the updated file. Implemented by taking the new
/// file's data, filling it from `other`, and writing it back (the arena
/// forbids holding two mutable borrows).
fn copy_source_file_from(nodes: &mut [Node], new_file: NodeId, other: NodeId) {
    let mut d = std::mem::take(nodes[new_file].as_source_file_mut());
    {
        let o = nodes[other].as_source_file();
        // `if other.contentMapperInfo != nil { node.SetContentMapperInfo(...) }`
        // — `d` is fresh, so the slot is always empty.
        if o.content_mapper_info.is_some() {
            d.content_mapper_info = o.content_mapper_info.clone();
        }
        d.language_variant = o.language_variant;
        d.script_kind = o.script_kind;
        d.is_declaration_file = o.is_declaration_file;
        d.uses_uri_style_node_core_modules = o.uses_uri_style_node_core_modules;
        d.imports = o.imports.clone();
        d.module_augmentations = o.module_augmentations.clone();
        d.ambient_module_names = o.ambient_module_names.clone();
        d.comment_directives = o.comment_directives.clone();
        d.pragmas = o.pragmas.clone();
        d.referenced_files = o.referenced_files.clone();
        d.type_reference_directives = o.type_reference_directives.clone();
        d.lib_reference_directives = o.lib_reference_directives.clone();
        d.common_js_module_indicator = o.common_js_module_indicator;
        d.external_module_indicator = o.external_module_indicator;
    }
    *nodes[new_file].as_source_file_mut() = d;
    let other_flags = nodes[other].flags;
    nodes[new_file].flags |= other_flags;
}

/// `(node *SourceFile) Clone(f)` — NewSourceFile + copyFrom.
pub(crate) fn clone_source_file(
    f: &mut NodeFactory<'_>,
    nodes: &mut Vec<Node>,
    node: NodeId,
) -> NodeId {
    let (opts, text, statements, end_of_file_token) = {
        let d = nodes[node].as_source_file();
        (
            d.parse_options.clone(),
            d.text.clone(),
            d.statements.clone(),
            d.end_of_file_token,
        )
    };
    let updated = f.new_source_file(nodes, &opts, &text, statements, end_of_file_token);
    copy_source_file_from(nodes, updated, node);
    clone_node(nodes, updated, node, &mut f.hooks)
}

/// PORT: manual `Clone` — `SourceFile` is generated in `ast_generated.rs`
/// but several fields (`OnceLock` lazies, atomics, `NodeFactory` hooks) are
/// not `Clone`. The clone is shallow in the arena sense: `NodeId`s inside
/// still index the owning `Vec<Node>`, and `SourceFileData` cells are
/// `Rc`-shared. Lazies are carried over only if already computed; the
/// `token_factory` (JSDoc token reparse) is dropped — it is lazily
/// recreated on demand.
impl Clone for SourceFile {
    fn clone(&self) -> SourceFile {
        fn clone_lock<T: Clone + Send>(lock: &std::sync::OnceLock<T>) -> std::sync::OnceLock<T> {
            match lock.get() {
                Some(v) => std::sync::OnceLock::from(v.clone()),
                None => std::sync::OnceLock::new(),
            }
        }
        SourceFile {
            declaration_base: self.declaration_base.clone(),
            locals_container_base: self.locals_container_base.clone(),
            composite_base: self.composite_base.clone(),
            file_name: self.file_name.clone(),
            parse_options: self.parse_options.clone(),
            text: self.text.clone(),
            content_mapper_info: self.content_mapper_info.clone(),
            statements: self.statements.clone(),
            end_of_file_token: self.end_of_file_token,
            data: self.data.clone(),
            diagnostics: self.diagnostics.clone(),
            js_diagnostics: self.js_diagnostics.clone(),
            jsdoc_diagnostics: self.jsdoc_diagnostics.clone(),
            language_variant: self.language_variant,
            script_kind: self.script_kind,
            is_declaration_file: self.is_declaration_file,
            uses_uri_style_node_core_modules: self.uses_uri_style_node_core_modules,
            identifier_count: self.identifier_count,
            imports: self.imports.clone(),
            module_augmentations: self.module_augmentations.clone(),
            ambient_module_names: self.ambient_module_names.clone(),
            comment_directives: self.comment_directives.clone(),
            jsdoc_cache: self.jsdoc_cache.clone(),
            has_lazy_js_doc: self.has_lazy_js_doc,
            identifiers: clone_lock(&self.identifiers),
            reparsed_clones: self.reparsed_clones.clone(),
            pragmas: self.pragmas.clone(),
            referenced_files: self.referenced_files.clone(),
            type_reference_directives: self.type_reference_directives.clone(),
            lib_reference_directives: self.lib_reference_directives.clone(),
            check_js_directive: self.check_js_directive.clone(),
            node_count: self.node_count,
            text_count: self.text_count,
            common_js_module_indicator: self.common_js_module_indicator,
            external_module_indicator: self.external_module_indicator,
            is_bound: std::sync::atomic::AtomicBool::new(
                self.is_bound.load(std::sync::atomic::Ordering::Acquire),
            ),
            bind_once: std::sync::atomic::AtomicBool::new(
                self.bind_once.load(std::sync::atomic::Ordering::Acquire),
            ),
            bind_diagnostics: self.bind_diagnostics.clone(),
            symbol_count: self.symbol_count,
            pattern_ambient_modules: self.pattern_ambient_modules.clone(),
            global_exports: self.global_exports.clone(),
            ecma_line_map: clone_lock(&self.ecma_line_map),
            hash: self.hash,
            token_cache: self.token_cache.clone(),
            // `NodeFactory` hooks hold closures — not `Clone`; the factory is
            // lazily created by token reparse paths.
            token_factory: None,
            declaration_map: self.declaration_map.clone(),
            name_table: self.name_table.clone(),
            position_map: clone_lock(&self.position_map),
        }
    }
}

// SourceFile accessors and lazily-computed state — the `*SourceFile` methods
// of ast.go. Methods that only read take `&self`; Go's `sync.Once` fields map
// to `std::sync::OnceLock` where the computation is read-only, while
// computations that can grow the arena (lazy JSDoc, token creation,
// JSDoc-aware walks) are free functions taking `&mut Vec<Node>` — exclusive
// arena access replaces Go's `sync.Mutex`/`sync.RWMutex` guards.

impl SourceFile {
    /// `(node *SourceFile) ParseOptions()`.
    pub fn parse_options(&self) -> &SourceFileParseOptions {
        &self.parse_options
    }

    /// `(node *SourceFile) Text()`.
    pub fn text(&self) -> &str {
        &self.text
    }

    /// `(node *SourceFile) OriginalText()` — the untransformed source text
    /// for content-mapped files, or `Text()` otherwise.
    pub fn original_text(&self) -> &str {
        if !self.content_mapper().is_empty() {
            return &self.content_mapper_info.as_ref().unwrap().original_text;
        }
        &self.text
    }

    /// `(node *SourceFile) OriginalFileName()` — the canonical filename
    /// associated with a supplemental source file, or `FileName()`.
    pub fn original_file_name<'a>(&'a self, nodes: &'a [Node]) -> &'a RootedFilePath {
        if let Some(canonical) = self.canonical_source_file() {
            return nodes[canonical].as_source_file().file_name();
        }
        self.file_name()
    }

    /// `(node *SourceFile) SpanMap()` — positions in this file's transformed
    /// `Text()` mapped back to its original content. `None` is Go's nil map,
    /// which maps positions identically.
    pub fn span_map(&self) -> Option<Arc<SpanMap>> {
        self.content_mapper_info
            .as_ref()
            .and_then(|info| info.span_map.clone())
    }

    /// `(node *SourceFile) IsContentMapped()`.
    pub fn is_content_mapped(&self) -> bool {
        self.content_mapper_info.is_some()
    }

    /// `(node *SourceFile) ContentMapper()` — the mapper's identity, or "".
    pub fn content_mapper(&self) -> &str {
        self.content_mapper_info
            .as_ref()
            .map_or("", |info| info.content_mapper.as_str())
    }

    /// `(node *SourceFile) IsContentMapperFailureStub()`.
    pub fn is_content_mapper_failure_stub(&self) -> bool {
        !self.content_mapper().is_empty() && self.span_map().is_none()
    }

    /// `(node *SourceFile) ContentMapperTransformIdentity()`.
    pub fn content_mapper_transform_identity(&self) -> &str {
        self.content_mapper_info
            .as_ref()
            .map_or("", |info| info.transform_identity.as_str())
    }

    /// `(node *SourceFile) VirtualFileName()`.
    pub fn virtual_file_name(&self) -> RootedFilePath {
        self.content_mapper_info
            .as_ref()
            .map(|info| info.virtual_file_name.clone())
            .unwrap_or_default()
    }

    /// `(node *SourceFile) ContentMapperParseOptions()` — the parse options
    /// used to acquire this file from the mapped parse cache.
    pub fn content_mapper_parse_options(&self) -> SourceFileParseOptions {
        self.content_mapper_info
            .as_ref()
            .map(|info| info.parse_options.clone())
            .unwrap_or_default()
    }

    /// `(node *SourceFile) SetContentMapperInfo(info)` — initializes all
    /// content-mapper metadata before the source file is published; panics
    /// if already set.
    pub fn set_content_mapper_info(&mut self, info: ContentMapperSourceFileInfo) {
        if self.content_mapper_info.is_some() {
            panic!("content mapper source file info already set");
        }
        self.content_mapper_info = Some(Box::new(info));
    }

    /// `(node *SourceFile) DiagnosticDirectives()`.
    pub fn diagnostic_directives(&self) -> &[MappedDiagnosticDirective] {
        self.content_mapper_info
            .as_ref()
            .map_or(&[], |info| info.diagnostic_directives.as_slice())
    }

    /// `(node *SourceFile) SupplementalSourceFiles()` — additional outputs
    /// produced from this canonical source file.
    pub fn supplemental_source_files(&self) -> &[NodeId] {
        self.content_mapper_info
            .as_ref()
            .map_or(&[], |info| info.supplemental_source_files.as_slice())
    }

    /// `(node *SourceFile) CanonicalSourceFile()` — the canonical output
    /// associated with this supplemental source file.
    pub fn canonical_source_file(&self) -> Option<NodeId> {
        self.content_mapper_info
            .as_ref()
            .and_then(|info| info.canonical_source_file)
    }

    /// `(node *SourceFile) IsContentMapperSupplemental()`.
    pub fn is_content_mapper_supplemental(&self) -> bool {
        self.canonical_source_file().is_some()
    }

    /// `(node *SourceFile) FileName()` — `parseOptions.FileName` (the
    /// `file_name` field is debug-only, as in Go).
    pub fn file_name(&self) -> &RootedFilePath {
        &self.parse_options.file_name
    }

    /// `(node *SourceFile) PathKey()` — `parseOptions.PathKey`.
    pub fn path_key(&self) -> &PathKey {
        &self.parse_options.path_key
    }

    /// `(node *SourceFile) Imports()`.
    pub fn imports(&self) -> &[NodeId] {
        &self.imports
    }

    /// `(node *SourceFile) Diagnostics()`.
    pub fn diagnostics(&self) -> &[DiagnosticRef] {
        &self.diagnostics
    }

    /// `(node *SourceFile) SetDiagnostics(diags)`.
    pub fn set_diagnostics(&mut self, diags: Vec<DiagnosticRef>) {
        self.diagnostics = diags;
    }

    /// `(node *SourceFile) JSDiagnostics()`.
    pub fn js_diagnostics(&self) -> &[DiagnosticRef] {
        &self.js_diagnostics
    }

    /// `(node *SourceFile) SetJSDiagnostics(diags)`.
    pub fn set_js_diagnostics(&mut self, diags: Vec<DiagnosticRef>) {
        self.js_diagnostics = diags;
    }

    /// `(node *SourceFile) JSDocDiagnostics()`.
    pub fn jsdoc_diagnostics(&self) -> &[DiagnosticRef] {
        &self.jsdoc_diagnostics
    }

    /// `(node *SourceFile) SetJSDocDiagnostics(diags)`.
    pub fn set_jsdoc_diagnostics(&mut self, diags: Vec<DiagnosticRef>) {
        self.jsdoc_diagnostics = diags;
    }

    /// `(node *SourceFile) SetJSDocCache(cache)` — the parser seeds the
    /// eagerly-parsed cache before `SetHasLazyJSDoc`.
    pub fn set_jsdoc_cache(&mut self, cache: FxHashMap<NodeId, Vec<NodeId>>) {
        self.jsdoc_cache = cache;
    }

    /// `(node *SourceFile) SetHasLazyJSDoc(lazy)`.
    pub fn set_has_lazy_jsdoc(&mut self, lazy: bool) {
        self.has_lazy_js_doc = lazy;
    }

    /// `(node *SourceFile) BindDiagnostics()`.
    pub fn bind_diagnostics(&self) -> &[DiagnosticRef] {
        &self.bind_diagnostics
    }

    /// `(node *SourceFile) SetBindDiagnostics(diags)`.
    pub fn set_bind_diagnostics(&mut self, diags: Vec<DiagnosticRef>) {
        self.bind_diagnostics = diags;
    }

    /// `(node *SourceFile) IsJS()` — `IsSourceFileJS(node)`.
    pub fn is_js(&self) -> bool {
        crate::utilities::is_source_file_js(self)
    }

    /// `(node *SourceFile) ECMALineMap()` — `OnceLock` is the
    /// `ecmaLineMapMu` double-checked lock; the computation only reads
    /// `self.text`.
    pub fn ecma_line_map(&self) -> &[TextPos] {
        self.ecma_line_map
            .get_or_init(|| compute_ecma_line_starts(&self.text))
    }

    /// `(node *SourceFile) IsBound()`.
    pub fn is_bound(&self) -> bool {
        self.is_bound.load(Ordering::Acquire)
    }

    /// `(file *SourceFile) GetPositionMap()` — the `PositionMap` for this
    /// source file, computed lazily (`positionMapOnce`/`positionMap`).
    pub fn position_map(&self) -> &PositionMap {
        self.position_map
            .get_or_init(|| compute_position_map(self.text.as_bytes()))
    }
}

impl SourceFileLike for SourceFile {
    fn text(&self) -> &str {
        SourceFile::text(self)
    }

    fn ecma_line_map(&self) -> &[TextPos] {
        SourceFile::ecma_line_map(self)
    }
}

/// `SourceFile` satisfies Go's `HasFileName` interface (`FileName()` +
/// `PathKey()`).
impl crate::utilities::HasFileName for SourceFile {
    fn file_name(&self) -> &RootedFilePath {
        SourceFile::file_name(self)
    }

    fn path_key(&self) -> &PathKey {
        SourceFile::path_key(self)
    }
}

/// `(file *SourceFile) HasIdentifier(name)` — `identifiersOnce` +
/// `identifiers` become a `OnceLock<Set<String>>`; the collection walk is
/// read-only, so `&[Node]` suffices.
pub fn has_identifier(nodes: &[Node], file: NodeId, name: &str) -> bool {
    nodes[file]
        .as_source_file()
        .identifiers
        .get_or_init(|| collect_identifiers_for_source_file(file, nodes))
        .has(name)
}

/// `collectIdentifiersForSourceFile` — every identifier/literal text in the
/// file. `collect` never returns true, so the child loop is a plain
/// recursion.
fn collect_identifiers_for_source_file(source_file: NodeId, nodes: &[Node]) -> Set<String> {
    fn collect(node: NodeId, nodes: &[Node], identifiers: &mut Set<String>) {
        match nodes[node].kind {
            Kind::Identifier
            | Kind::PrivateIdentifier
            | Kind::StringLiteral
            | Kind::NumericLiteral
            | Kind::BigIntLiteral
            | Kind::NoSubstitutionTemplateLiteral => {
                identifiers.add(nodes[node].text(nodes).into_owned());
            }
            _ => {}
        }
        let children: Vec<NodeId> = nodes[node].iter_children(nodes).map(|c| c.id).collect();
        for child in children {
            collect(child, nodes, identifiers);
        }
    }
    let mut identifiers = Set::new();
    collect(source_file, nodes, &mut identifiers);
    identifiers
}

/// `(node *SourceFile) BindOnce(bind)` — `bindOnce sync.Once` +
/// `isBound atomic.Bool`. The once-flag flips before `bind` runs, matching
/// Go 1.21+ semantics where a panicking `Do` still marks the `Once` done
/// (and `isBound` stays false, matching Go's store-after-`bind` order).
/// PORT: `bind` takes the arena — the binder's `func()` closes over it.
pub fn bind_once(nodes: &mut Vec<Node>, file: NodeId, bind: impl FnOnce(&mut Vec<Node>)) {
    if nodes[file]
        .as_source_file()
        .bind_once
        .swap(true, Ordering::AcqRel)
    {
        return;
    }
    bind(nodes);
    nodes[file]
        .as_source_file()
        .is_bound
        .store(true, Ordering::Release);
}

// Lazy JSDoc — `parseJSDocForNode`, `SetParseJSDocForNode`, `resolveJSDoc`,
// `Node.JSDoc`, `Node.EagerJSDoc`.

/// `parseJSDocForNode` — the package-level lazy JSDoc parse function,
/// registered by the parser (Go: `SetParseJSDocForNode` from parser's
/// `init()`). Receives `(nodes, sourceFile, node)` — the Go
/// `(*SourceFile, *Node)` pair as arena handles.
pub type ParseJsDocForNodeFn = fn(&mut Vec<Node>, NodeId, NodeId) -> Vec<NodeId>;

/// The `parseJSDocForNode` package var — an `RwLock` keeps the Go "plain
/// var" semantics (re-settable, readable without mutation).
static PARSE_JSDOC_FOR_NODE: RwLock<Option<ParseJsDocForNodeFn>> = RwLock::new(None);

/// `SetParseJSDocForNode(fn)` — registers the lazy JSDoc parse function.
pub fn set_parse_jsdoc_for_node(f: ParseJsDocForNodeFn) {
    // Go's plain-var assignment never fails; `into_inner` recovers from a
    // poisoned lock the way Go's mutexes stay usable after a panic.
    *PARSE_JSDOC_FOR_NODE
        .write()
        .unwrap_or_else(|e| e.into_inner()) = Some(f);
}

fn parse_jsdoc_for_node_fn() -> ParseJsDocForNodeFn {
    PARSE_JSDOC_FOR_NODE
        .read()
        .unwrap_or_else(|e| e.into_inner())
        .unwrap_or_else(|| {
            panic!("resolveJSDoc called but parseJSDocForNode is not registered; ensure the parser package is imported")
        })
}

/// `(node *SourceFile) resolveJSDoc(n)` — `jsdocMu` collapses into the
/// exclusive `&mut Vec<Node>` borrow; the read/write-lock double-check is
/// unnecessary under `&mut`.
pub(crate) fn resolve_jsdoc(nodes: &mut Vec<Node>, file: NodeId, n: NodeId) -> Vec<NodeId> {
    // Go panics on an unregistered hook before touching the cache.
    let parse = parse_jsdoc_for_node_fn();
    if let Some(jsdocs) = nodes[file].as_source_file().jsdoc_cache.get(&n) {
        return jsdocs.clone();
    }
    let jsdocs = parse(nodes, file, n);
    nodes[file]
        .as_source_file_mut()
        .jsdoc_cache
        .insert(n, jsdocs.clone());
    jsdocs
}

/// `(node *Node) JSDoc(file)` — `None` for `file` walks to the root of the
/// tree to find the file, like Go's nil. Returns the cached or lazily-parsed
/// JSDoc nodes for `node` (empty when absent, like Go's nil slice).
pub fn js_doc(nodes: &mut Vec<Node>, node: NodeId, file: Option<NodeId>) -> Vec<NodeId> {
    if !nodes[node].flags.intersects(NodeFlags::HAS_JSDOC) {
        return Vec::new();
    }
    let file = match file.or_else(|| get_source_file_of_node(Some(node), nodes)) {
        Some(file) => file,
        None => return Vec::new(),
    };
    if nodes[file].as_source_file().has_lazy_js_doc {
        return resolve_jsdoc(nodes, file, node);
    }
    nodes[file]
        .as_source_file()
        .jsdoc_cache
        .get(&node)
        .cloned()
        .unwrap_or_default()
}

/// `(node *Node) EagerJSDoc(file)` — JSDoc nodes already parsed and cached,
/// without triggering lazy JSDoc parsing.
pub fn eager_js_doc(nodes: &[Node], node: NodeId, file: Option<NodeId>) -> Vec<NodeId> {
    if !nodes[node].flags.intersects(NodeFlags::HAS_JSDOC) {
        return Vec::new();
    }
    let Some(file) = file.or_else(|| get_source_file_of_node(Some(node), nodes)) else {
        return Vec::new();
    };
    // Go reads through `jsdocMu` when `hasLazyJSDoc` — moot under a shared
    // borrow; the lookup is identical either way.
    nodes[file]
        .as_source_file()
        .jsdoc_cache
        .get(&node)
        .cloned()
        .unwrap_or_default()
}

// Token cache — `GetOrCreateToken`/`createToken`.

/// `(node *SourceFile) GetOrCreateToken(kind, pos, end, parent, flags)` —
/// gets a token from the file's token cache, creating it if it does not
/// already exist. NOT for synthetic tokens that aren't in the file.
/// `tokenCacheMu` collapses into the exclusive `&mut Vec<Node>` borrow.
pub fn get_or_create_token(
    nodes: &mut Vec<Node>,
    file: NodeId,
    kind: Kind,
    pos: TextPos,
    end: TextPos,
    parent: NodeId,
    flags: TokenFlags,
) -> NodeId {
    let loc = TextRange::new(pos, end);
    let key = TokenCacheKey { parent, loc };
    if let Some(&token) = nodes[file].as_source_file().token_cache.get(&key) {
        let cached_kind = nodes[token].kind;
        if cached_kind != kind {
            panic!(
                "Token cache mismatch: {} != {}",
                cached_kind.kind_string(),
                kind.kind_string()
            );
        }
        return token;
    }
    if nodes[parent].flags.intersects(NodeFlags::REPARSED) {
        panic!(
            "Cannot create token from reparsed node of kind {}",
            nodes[parent].kind_string()
        );
    }
    let token = create_token(nodes, file, kind, pos, end, flags);
    nodes[token].loc = loc;
    nodes[token].parent = Some(parent);
    nodes[file]
        .as_source_file_mut()
        .token_cache
        .insert(key, token);
    token
}

/// `createToken(kind, file, pos, end, flags)` — `kind` is a token kind.
fn create_token(
    nodes: &mut Vec<Node>,
    file: NodeId,
    kind: Kind,
    pos: TextPos,
    end: TextPos,
    flags: TokenFlags,
) -> NodeId {
    // `file.tokenFactory`, created lazily (Go: `*NodeFactory`). PORT: the
    // factory's `new_*` methods need `&mut Vec<Node>` to mint arena nodes, so
    // the stored factory is taken out of the file for the call and put back
    // afterwards. `NodeFactory<'static>` because `SourceFile` cannot carry a
    // borrow-bound lifetime.
    let mut factory = match nodes[file].as_source_file_mut().token_factory.take() {
        Some(factory) => factory,
        None => {
            let mut factory = NodeFactory::new(NodeFactoryHooks::default());
            factory.set_file_index(nodes[file].id.file_index());
            factory
        }
    };
    let text = nodes[file].as_source_file().text[pos as usize..end as usize].to_string();
    let token = match kind {
        Kind::NumericLiteral => factory.new_numeric_literal(nodes, &text, flags),
        Kind::BigIntLiteral => factory.new_big_int_literal(nodes, &text, flags),
        Kind::StringLiteral => factory.new_string_literal(nodes, &text, flags),
        Kind::JsxText | Kind::JsxTextAllWhiteSpaces => {
            // `NewJsxText` always mints `KindJsxText`, even for
            // `KindJsxTextAllWhiteSpaces` input — same as Go.
            factory.new_jsx_text(nodes, &text, kind == Kind::JsxTextAllWhiteSpaces)
        }
        Kind::RegularExpressionLiteral => {
            factory.new_regular_expression_literal(nodes, &text, flags)
        }
        Kind::NoSubstitutionTemplateLiteral => {
            factory.new_no_substitution_template_literal(nodes, &text, flags)
        }
        Kind::TemplateHead => factory.new_template_head(nodes, &text, "", flags),
        Kind::TemplateMiddle => factory.new_template_middle(nodes, &text, "", flags),
        Kind::TemplateTail => factory.new_template_tail(nodes, &text, "", flags),
        Kind::Identifier => factory.new_identifier(nodes, &text),
        Kind::PrivateIdentifier => factory.new_private_identifier(nodes, &text),
        // Punctuation and keywords.
        _ => factory.new_token(nodes, kind),
    };
    nodes[file].as_source_file_mut().token_factory = Some(factory);
    token
}

// Declaration map — `GetDeclarationMap`/`computeDeclarationMap`/
// `GetDeclarationName`.

/// `(node *SourceFile) GetDeclarationMap()` — `declarationMapMu` collapses
/// to `Option` under exclusive arena access (the compute is read-only).
pub fn get_declaration_map<'a>(
    nodes: &'a mut Vec<Node>,
    file: NodeId,
) -> &'a FxHashMap<String, Vec<NodeId>> {
    if nodes[file].as_source_file().declaration_map.is_none() {
        let map = compute_declaration_map(nodes, file);
        nodes[file].as_source_file_mut().declaration_map = Some(map);
    }
    nodes[file]
        .as_source_file()
        .declaration_map
        .as_ref()
        .unwrap()
}

/// `(node *SourceFile) computeDeclarationMap` — a read-only tree walk.
fn compute_declaration_map(nodes: &[Node], file: NodeId) -> FxHashMap<String, Vec<NodeId>> {
    fn add_declaration(
        nodes: &[Node],
        result: &mut FxHashMap<String, Vec<NodeId>>,
        declaration: NodeId,
    ) {
        let name = get_declaration_name(nodes, declaration);
        if !name.is_empty() {
            result.entry(name).or_default().push(declaration);
        }
    }

    fn for_each_child(node: NodeId, nodes: &[Node]) -> Vec<NodeId> {
        // `node.ForEachChild(visit)` — `visit` never returns true.
        nodes[node].iter_children(nodes).map(|c| c.id).collect()
    }

    /// `case KindParameter (fallthrough), KindVariableDeclaration,
    /// KindBindingElement` — the shared `name`/`IsBindingPattern` walk.
    fn visit_declared_name(
        node: NodeId,
        nodes: &[Node],
        result: &mut FxHashMap<String, Vec<NodeId>>,
    ) {
        let Some(name) = nodes[node].name() else {
            return;
        };
        if is_binding_pattern(&nodes[name]) {
            for child in for_each_child(name, nodes) {
                visit(child, nodes, result);
            }
        } else {
            if let Some(initializer) = nodes[node].initializer() {
                visit(initializer, nodes, result);
            }
            add_declaration(nodes, result, node);
        }
    }

    fn visit(node: NodeId, nodes: &[Node], result: &mut FxHashMap<String, Vec<NodeId>>) {
        match nodes[node].kind {
            Kind::FunctionDeclaration
            | Kind::FunctionExpression
            | Kind::MethodDeclaration
            | Kind::MethodSignature => {
                let declaration_name = get_declaration_name(nodes, node);
                if !declaration_name.is_empty() {
                    let declarations = result.entry(declaration_name).or_default();
                    // Check whether this declaration belongs to an
                    // "overload group".
                    let last_declaration = declarations.last().copied();
                    if last_declaration.is_some_and(|last| {
                        nodes[node].parent == nodes[last].parent
                            && nodes[node].symbol() == nodes[last].symbol()
                    }) {
                        // Overwrite the last declaration if it was an
                        // overload and this one is an implementation.
                        let last = last_declaration.unwrap();
                        if nodes[node].body().is_some() && nodes[last].body().is_none() {
                            let len = declarations.len();
                            declarations[len - 1] = node;
                        }
                    } else {
                        declarations.push(node);
                    }
                }
                for child in for_each_child(node, nodes) {
                    visit(child, nodes, result);
                }
            }
            Kind::ClassDeclaration
            | Kind::ClassExpression
            | Kind::InterfaceDeclaration
            | Kind::TypeAliasDeclaration
            | Kind::EnumDeclaration
            | Kind::ModuleDeclaration
            | Kind::ImportEqualsDeclaration
            | Kind::ImportClause
            | Kind::NamespaceImport
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::TypeLiteral => {
                add_declaration(nodes, result, node);
                for child in for_each_child(node, nodes) {
                    visit(child, nodes, result);
                }
            }
            Kind::ImportSpecifier | Kind::ExportSpecifier => {
                if nodes[node].property_name().is_some() {
                    add_declaration(nodes, result, node);
                }
            }
            Kind::Parameter => {
                // Only consider parameter properties. Go `break` exits the
                // switch — non-parameter properties are not traversed.
                if has_syntactic_modifier(&nodes[node], ModifierFlags::PARAMETER_PROPERTY_MODIFIER)
                {
                    visit_declared_name(node, nodes, result);
                }
            }
            Kind::VariableDeclaration | Kind::BindingElement => {
                visit_declared_name(node, nodes, result);
            }
            Kind::EnumMember | Kind::PropertyDeclaration | Kind::PropertySignature => {
                add_declaration(nodes, result, node);
            }
            Kind::ExportDeclaration => {
                // Handle named exports case e.g.:
                //    export {a, b as B} from "mod";
                if let Some(export_clause) = nodes[node].as_export_declaration().export_clause {
                    if is_named_exports(&nodes[export_clause]) {
                        if let Some(elements) = nodes[export_clause].elements() {
                            for &element in elements {
                                visit(element, nodes, result);
                            }
                        }
                    } else if let Some(name) = nodes[export_clause].as_namespace_export().name {
                        visit(name, nodes, result);
                    }
                }
            }
            Kind::ImportDeclaration => {
                if let Some(import_clause) = nodes[node].as_import_declaration().import_clause {
                    // Handle default import case e.g.:
                    //    import d from "mod";
                    if let Some(name) = nodes[import_clause].name() {
                        add_declaration(nodes, result, name);
                    }
                    // Handle named bindings in imports e.g.:
                    //    import * as NS from "mod";
                    //    import {a, b as B} from "mod";
                    if let Some(named_bindings) =
                        nodes[import_clause].as_import_clause().named_bindings
                    {
                        if nodes[named_bindings].kind == Kind::NamespaceImport {
                            add_declaration(nodes, result, named_bindings);
                        } else if let Some(elements) = nodes[named_bindings].elements() {
                            for &element in elements {
                                visit(element, nodes, result);
                            }
                        }
                    }
                }
            }
            Kind::BinaryExpression => {
                match get_assignment_declaration_kind(node, nodes) {
                    JsDeclarationKind::ExportsProperty
                    | JsDeclarationKind::ThisProperty
                    | JsDeclarationKind::Property => add_declaration(nodes, result, node),
                    _ => {}
                }
                for child in for_each_child(node, nodes) {
                    visit(child, nodes, result);
                }
            }
            _ => {
                for child in for_each_child(node, nodes) {
                    visit(child, nodes, result);
                }
            }
        }
    }

    let mut result = FxHashMap::default();
    // `node.ForEachChild(visit)` on the file itself — statements, then the
    // EOF token.
    let mut children = Vec::new();
    for_each_child_source_file(
        nodes[file].as_source_file(),
        &mut |child| {
            children.push(child);
            false
        },
        nodes,
    );
    for child in children {
        visit(child, nodes, &mut result);
    }
    result
}

/// `GetDeclarationName(declaration)` — the name text for a declaration node,
/// or "".
pub fn get_declaration_name(nodes: &[Node], declaration: NodeId) -> String {
    let Some(name) = get_non_assigned_name_of_declaration(declaration, nodes) else {
        return String::new();
    };
    let name_node = &nodes[name];
    if is_computed_property_name(name_node) {
        // `name.Expression()` — the nil dereference of a missing expression
        // mirrors Go's unchecked field read.
        let expression = name_node
            .expression()
            .expect("ComputedPropertyName without Expression in GetDeclarationName");
        let e = &nodes[expression];
        if is_string_or_numeric_literal_like(e) {
            return e.text(nodes).into_owned();
        }
        if is_property_access_expression(e)
            && let Some(inner) = e.name()
        {
            return nodes[inner].text(nodes).into_owned();
        }
    } else if is_property_name(name_node) {
        return name_node.text(nodes).into_owned();
    }
    String::new()
}

// Name table — `GetNameTable`.

/// `(file *SourceFile) GetNameTable()` — a map of all names in the file to
/// their positions (`-1` when a name appears more than once).
/// `nameTableOnce` collapses to `Option`; computing it may lazily parse
/// JSDoc, so it needs `&mut Vec<Node>`.
pub fn get_name_table<'a>(nodes: &'a mut Vec<Node>, file: NodeId) -> &'a FxHashMap<String, i32> {
    if nodes[file].as_source_file().name_table.is_none() {
        let table = compute_name_table(nodes, file);
        nodes[file].as_source_file_mut().name_table = Some(table);
    }
    nodes[file].as_source_file().name_table.as_ref().unwrap()
}

/// The `nameTableOnce.Do` body — `walk` never returns true, so the
/// `ForEachChild` calls are plain child loops.
fn compute_name_table(nodes: &mut Vec<Node>, file: NodeId) -> FxHashMap<String, i32> {
    fn walk(
        node: NodeId,
        file: NodeId,
        nodes: &mut Vec<Node>,
        name_table: &mut FxHashMap<String, i32>,
    ) {
        let children = {
            let n = &nodes[node];
            if (is_identifier(n) && !is_tag_name(node, nodes) && !n.text(nodes).is_empty())
                || (is_string_or_numeric_literal_like(n) && literal_is_name(node, nodes))
                || is_private_identifier(n)
            {
                let text = n.text(nodes).into_owned();
                match name_table.entry(text) {
                    Entry::Occupied(mut e) => {
                        *e.get_mut() = -1;
                    }
                    Entry::Vacant(e) => {
                        e.insert(n.pos());
                    }
                }
            }
            // `node.ForEachChild(walk)`.
            n.iter_children(nodes).map(|c| c.id).collect::<Vec<_>>()
        };
        for child in children {
            walk(child, file, nodes, name_table);
        }
        // `jsdocNodes := node.JSDoc(file)` then `jsdoc.ForEachChild(walk)`.
        for jsdoc in js_doc(nodes, node, Some(file)) {
            let children = nodes[jsdoc]
                .iter_children(nodes)
                .map(|c| c.id)
                .collect::<Vec<_>>();
            for child in children {
                walk(child, file, nodes, name_table);
            }
        }
    }

    // `make(map[string]int, file.IdentifierCount)`.
    let identifier_count = nodes[file].as_source_file().identifier_count.max(0) as usize;
    let mut name_table = FxHashMap::with_capacity_and_hasher(identifier_count, FxBuildHasher);
    // `file.ForEachChild(walk)` — statements, then the EOF token.
    let mut children = Vec::new();
    for_each_child_source_file(
        nodes[file].as_source_file(),
        &mut |child| {
            children.push(child);
            false
        },
        nodes,
    );
    for child in children {
        walk(child, file, nodes, &mut name_table);
    }
    name_table
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

// ---------------------------------------------------------------------------
// ArenaCell / ArenaMut / ArenaCheckout — shared per-file node arenas
// ---------------------------------------------------------------------------

/// `ArenaCell` — a per-file node arena: `RefCell<Rc<Vec<Node>>>`.
///
/// Readers take cheap `Rc` snapshots ([`ArenaCell::snapshot`], `Program::nodes`)
/// that never pin a `RefCell` borrow, so a held snapshot can never block a
/// writer. Writers go through copy-on-write ([`ArenaCell::cow`] /
/// `Program::nodes_mut` → [`ArenaMut`]): `Rc::make_mut` mutates in place when
/// the arena is unshared, otherwise clones once per guard.
///
/// PORT(divergence): Go's shared mutable `[]*ast.Node` graph has no borrow
/// discipline — element writes are visible to anyone holding the slice. A
/// Rust snapshot does not observe in-place mutations made after it was taken
/// (appended nodes were invisible to Go slice holders too). In practice
/// checker mutations append synthetic nodes or patch transient fields and
/// all consumers re-snapshot, so this is observationally equivalent.
pub struct ArenaCell(
    pub std::cell::RefCell<std::rc::Rc<Vec<Node>>>,
    std::cell::Cell<bool>,
    /// Write generation — bumped on every `set`/`flush`. `ArenaMut`/
    /// `ArenaCheckout` record it at checkout; a mismatch at write-back means
    /// a concurrent writer committed in between (lost update — Go's shared
    /// mutable arena can't express this). Detected when `TSC_ARENA_DBG` is
    /// set; the write still goes through (last-writer-wins).
    std::cell::Cell<u64>,
    /// Nonzero while an [`ArenaCheckout`] holds the arena — concurrent
    /// `set`/`flush` commits during that window will be clobbered by the
    /// checkout's write-back. Diagnostic only (`TSC_ARENA_DBG`).
    std::cell::Cell<u64>,
);

impl ArenaCell {
    pub fn new(nodes: Vec<Node>) -> ArenaCell {
        ArenaCell(
            std::cell::RefCell::new(std::rc::Rc::new(nodes)),
            std::cell::Cell::new(false),
            std::cell::Cell::new(0),
            std::cell::Cell::new(0),
        )
    }

    /// Cheap read snapshot — an `Rc` clone, never a held borrow.
    /// While a `cow()` guard has the buffer checked out this returns the
    /// empty placeholder.
    pub fn snapshot(&self) -> std::rc::Rc<Vec<Node>> {
        self.0.borrow().clone()
    }

    /// Copy-on-write mutable access — see [`ArenaMut`]. The guard owns an
    /// `Rc` of this cell so it can outlive the lookup that produced it.
    pub fn cow(self: &std::rc::Rc<Self>) -> ArenaMut {
        assert!(
            !self.1.get(),
            "ArenaCell: nested cow() while a checkout is active"
        );
        let mut slot = self.0.borrow_mut();
        if std::rc::Rc::strong_count(&slot) == 1 {
            // Sole owner: move the buffer out so `make_mut` mutates in
            // place with no clone; the cell is refilled on flush/drop.
            // Snapshots taken while the guard lives see the empty
            // placeholder — mirrors the exclusive-writer semantics the
            // `RefMut` design enforced.
            let work = std::mem::replace(&mut *slot, std::rc::Rc::new(Vec::new()));
            drop(slot);
            self.1.set(true);
            ArenaMut {
                cell: self.clone(),
                work,
                dirty: false,
                checked_out: true,
                wgen: self.2.get(),
            }
        } else {
            ArenaMut {
                cell: self.clone(),
                work: slot.clone(),
                dirty: false,
                checked_out: false,
                wgen: self.2.get(),
            }
        }
    }

    /// Replaces the arena contents (construction/restore paths).
    pub fn set(&self, nodes: Vec<Node>) {
        if std::env::var("TSC_ARENA_DBG").is_ok() && self.3.get() != 0 {
            eprintln!(
                "[arena] set() while ArenaCheckout active len={}\n{}",
                nodes.len(),
                std::backtrace::Backtrace::force_capture()
            );
        }
        *self.0.borrow_mut() = std::rc::Rc::new(nodes);
        self.2.set(self.2.get() + 1);
    }

    /// Whether read snapshots (or the cell copy) share the buffer — a
    /// `cow()` on an unshared cell mutates in place; on a shared cell it
    /// clones first.
    pub fn is_shared(&self) -> bool {
        std::rc::Rc::strong_count(&self.0.borrow()) > 1
    }

    /// Compat alias for [`ArenaCell::snapshot`] — the `Rc` snapshot plays the
    /// role `Ref<Vec<Node>>` had before the COW conversion.
    pub fn borrow(&self) -> std::rc::Rc<Vec<Node>> {
        self.snapshot()
    }

    /// Compat alias for [`ArenaCell::cow`].
    pub fn borrow_mut(self: &std::rc::Rc<Self>) -> ArenaMut {
        self.cow()
    }
}

/// `ArenaMut` — RAII copy-on-write guard over an [`ArenaCell`]. Reads deref
/// to `&Vec<Node>`; the first mutable access calls `Rc::make_mut` (cloning
/// only when snapshots share the buffer) and marks the guard dirty. `Drop`
/// writes a dirty buffer back into the cell — a clean guard leaves the cell
/// untouched so a nested guard's earlier write-back is never clobbered.
pub struct ArenaMut {
    cell: std::rc::Rc<ArenaCell>,
    work: std::rc::Rc<Vec<Node>>,
    dirty: bool,
    /// The working buffer was moved out of the cell (no snapshot was
    /// alive at checkout). The cell holds an empty placeholder until
    /// `flush`/`drop` restores it — write-back is then mandatory even
    /// when `dirty` is false.
    checked_out: bool,
    /// `ArenaCell::wgen` at checkout — see `ArenaCell::wgen`.
    wgen: u64,
}

impl ArenaMut {
    /// Writes back the working buffer if dirty, even mid-scope (a second
    /// call is a no-op). Normally not needed — `Drop` handles it.
    pub fn flush(&mut self) {
        if std::env::var("TSC_ARENA_DBG").is_ok()
            && self.cell.3.get() != 0
            && (self.checked_out || self.dirty)
        {
            eprintln!(
                "[arena] flush() while ArenaCheckout active len={}\n{}",
                self.work.len(),
                std::backtrace::Backtrace::force_capture()
            );
        }
        if self.checked_out {
            *self.cell.0.borrow_mut() = self.work.clone();
            self.checked_out = false;
            self.cell.1.set(false);
            self.dirty = false;
            self.cell.2.set(self.cell.2.get() + 1);
        } else if self.dirty {
            if std::env::var("TSC_ARENA_DBG").is_ok() && self.cell.2.get() != self.wgen {
                eprintln!(
                    "[arena] ArenaMut stale write-back (gen {} -> {}) len={}\n{}",
                    self.wgen,
                    self.cell.2.get(),
                    self.work.len(),
                    std::backtrace::Backtrace::force_capture()
                );
            }
            *self.cell.0.borrow_mut() = self.work.clone();
            self.dirty = false;
            self.cell.2.set(self.cell.2.get() + 1);
        }
    }
}

impl std::ops::Deref for ArenaMut {
    type Target = Vec<Node>;

    fn deref(&self) -> &Vec<Node> {
        &self.work
    }
}

/// Diagnostic counters for the COW path — set `TSC_COW_STATS` in the
/// `tsc` binary to print (clones, cloned elements) at exit.
pub static COW_CLONES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub static COW_ELEMS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

impl std::ops::DerefMut for ArenaMut {
    fn deref_mut(&mut self) -> &mut Vec<Node> {
        self.dirty = true;
        if std::rc::Rc::strong_count(&self.work) > 1 {
            use std::sync::atomic::Ordering::Relaxed;
            COW_CLONES.fetch_add(1, Relaxed);
            COW_ELEMS.fetch_add(self.work.len() as u64, Relaxed);
            if std::env::var("TSC_COW_STATS").is_ok() && self.work.len() > 50_000 {
                eprintln!("[cow-big] cloning {} nodes", self.work.len());
            }
            if std::env::var("TSC_COW_TRACE").is_ok() {
                static N: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
                let n = N.fetch_add(1, Relaxed);
                if n < 12 {
                    eprintln!(
                        "[cow-trace] clone #{n} len={}\n{}",
                        self.work.len(),
                        std::backtrace::Backtrace::force_capture()
                    );
                }
            }
        }
        std::rc::Rc::make_mut(&mut self.work)
    }
}

impl Drop for ArenaMut {
    fn drop(&mut self) {
        self.flush();
    }
}

/// `ArenaRef<T>` — the `Rc`-snapshot analog of `Ref::map`: owns an arena
/// snapshot and projects it to `&T` on deref via a stored accessor.
/// `Deref` re-resolves the projection each call, so the returned `&T`
/// borrows `self` (the snapshot) — no self-reference problem.
pub struct ArenaRef<T: ?Sized, F> {
    arena: std::rc::Rc<Vec<Node>>,
    f: F,
    _t: std::marker::PhantomData<fn() -> T>,
}

impl<T: ?Sized, F> ArenaRef<T, F>
where
    F: for<'a> Fn(&'a Vec<Node>) -> &'a T,
{
    pub fn new(
        arena: std::rc::Rc<Vec<Node>>,
        f: F,
    ) -> ArenaRef<T, F> {
        ArenaRef {
            arena,
            f,
            _t: std::marker::PhantomData,
        }
    }
}

impl<T: ?Sized, F> std::ops::Deref for ArenaRef<T, F>
where
    F: for<'a> Fn(&'a Vec<Node>) -> &'a T,
{
    type Target = T;

    fn deref(&self) -> &T {
        (self.f)(&self.arena)
    }
}

/// `ArenaCheckout` — RAII guard that owns a private working `Vec<Node>` for
/// a `&mut Vec<Node>` consumer (transformers, node builders); the arena
/// cell keeps its original contents so re-entrant reads through
/// `ArenaCell::snapshot` keep working. `Drop` writes the mutated `Vec` back.
/// `NodeId`s minted during the visit don't resolve through the cell
/// (known limitation).
pub struct ArenaCheckout {
    arena: std::rc::Rc<ArenaCell>,
    work: Vec<Node>,
    /// `ArenaCell::wgen` at checkout — see `ArenaCell::wgen`.
    wgen: u64,
}

impl ArenaCheckout {
    /// Checks the arena out: clones its contents into a private working
    /// `Vec`.
    pub fn new(arena: std::rc::Rc<ArenaCell>) -> ArenaCheckout {
        assert!(
            !arena.1.get(),
            "ArenaCell: ArenaCheckout while a cow() checkout is active"
        );
        let wgen = arena.2.get();
        let work = arena.0.borrow().as_ref().clone();
        arena.3.set(arena.3.get() + 1);
        ArenaCheckout { arena, work, wgen }
    }
}

impl std::ops::Deref for ArenaCheckout {
    type Target = Vec<Node>;

    fn deref(&self) -> &Vec<Node> {
        &self.work
    }
}

impl std::ops::DerefMut for ArenaCheckout {
    fn deref_mut(&mut self) -> &mut Vec<Node> {
        &mut self.work
    }
}

impl Drop for ArenaCheckout {
    fn drop(&mut self) {
        if std::env::var("TSC_ARENA_DBG").is_ok() && self.arena.2.get() != self.wgen {
            eprintln!(
                "[arena] ArenaCheckout stale write-back (gen {} -> {}) len={}\n{}",
                self.wgen,
                self.arena.2.get(),
                self.work.len(),
                std::backtrace::Backtrace::force_capture()
            );
        }
        self.arena.3.set(self.arena.3.get().saturating_sub(1));
        self.arena.set(std::mem::take(&mut self.work));
    }
}
