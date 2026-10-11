// Ported from tsc/internal/printer/emitcontext.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Stores side-table information used during transformation that can be read
// by the printer to customize emit.
//
// NOTE: EmitContext is not guaranteed to be thread-safe.
//
// PORT: Go's EmitContext owns a `*NodeFactory` whose hooks call back into the
// context (`SetOriginal`, `autoGenerate`). Rust cannot express that cycle
// safely, so every table the hooks touch lives in
// `Rc<RefCell<EmitContextShared>>`, shared between this context, its
// `factory`, and the `ast::NodeFactory` hooks. Behavior is identical.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicU32, Ordering};

use rustc_hash::FxHashMap;
use tsc_ast::visitor::{NodeVisitor, NodeVisitorHooks, VisitorCx};
use tsc_ast::{self as ast, Kind, Node, NodeFactoryHooks, NodeId, NodeList};
use tsc_collections::{OrderedSet, Set};
use tsc_core::linkstore::LinkStore;
use tsc_core::text::TextRange;

use crate::emit_flags::EmitFlags;
use crate::emit_helpers::{EmitHelper, EmitHelperRef};
use crate::utilities::find_span_end;

/// Shared handle to the emit-context tables.
pub(crate) type Shared = Rc<RefCell<EmitContextShared>>;

/// `type environmentFlags int`
pub(crate) type EnvironmentFlags = i32;

pub(crate) const ENVIRONMENT_FLAGS_NONE: EnvironmentFlags = 0;
/// currently visiting a parameter list
pub(crate) const ENVIRONMENT_FLAGS_IN_PARAMETERS: EnvironmentFlags = 1 << 0;
/// a temp variable was hoisted while visiting a parameter list
pub(crate) const ENVIRONMENT_FLAGS_VARIABLES_HOISTED_IN_PARAMETERS: EnvironmentFlags = 1 << 1;

/// `type varScope struct`
#[derive(Default)]
pub(crate) struct VarScope {
    pub(crate) variables: Vec<NodeId>,
    pub(crate) functions: Vec<NodeId>,
    pub(crate) flags: EnvironmentFlags,
    pub(crate) initialization_statements: Vec<NodeId>,
}

/// `type emitNodeFlags uint32`
pub(crate) type EmitNodeFlags = u32;

pub(crate) const HAS_COMMENT_RANGE: EmitNodeFlags = 1 << 0;
pub(crate) const HAS_SOURCE_MAP_RANGE: EmitNodeFlags = 1 << 1;

/// `type SnippetKind int`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SnippetKind {
    /// `SnippetKindTabStop`
    TabStop,
}

/// `type SnippetElement struct`
#[derive(Clone, Debug)]
pub struct SnippetElement {
    pub kind: SnippetKind,
    pub order: i32,
}

/// `type SynthesizedComment struct`
#[derive(Clone, Default)]
pub struct SynthesizedComment {
    pub kind: Kind,
    pub loc: TextRange,
    pub has_leading_new_line: bool,
    pub has_trailing_new_line: bool,
    pub text: String,
}

/// `type emitNode struct`
#[derive(Default)]
pub struct EmitNode {
    pub(crate) flags: EmitNodeFlags,
    pub(crate) emit_flags: EmitFlags,
    pub(crate) comment_range: TextRange,
    pub(crate) source_map_range: TextRange,
    pub(crate) token_source_map_ranges: Option<FxHashMap<Kind, TextRange>>,
    pub(crate) helpers: Vec<Arc<EmitHelper>>,
    pub(crate) external_helpers_module_name: Option<NodeId>,
    pub(crate) leading_comments: Vec<SynthesizedComment>,
    pub(crate) trailing_comments: Vec<SynthesizedComment>,
    pub(crate) type_node: Option<NodeId>,
    pub(crate) snippet_element: Option<Box<SnippetElement>>,
}

impl EmitNode {
    /// `(e *emitNode) copyFrom(source)` — NOTE: This method is not guaranteed
    /// to be thread-safe.
    pub(crate) fn copy_from(&mut self, source: &EmitNode) {
        self.flags = source.flags;
        self.emit_flags = source.emit_flags;
        self.comment_range = source.comment_range;
        self.source_map_range = source.source_map_range;
        self.token_source_map_ranges = source.token_source_map_ranges.clone();
        self.helpers = source.helpers.clone();
        self.external_helpers_module_name = source.external_helpers_module_name;
        self.leading_comments = source.leading_comments.clone();
        self.trailing_comments = source.trailing_comments.clone();
        self.type_node = source.type_node;
        self.snippet_element = source.snippet_element.clone();
    }
}

/// The side tables shared between `EmitContext`, its `NodeFactory`, and the
/// `ast::NodeFactory` hooks (`onUpdate`/`onClone` write `original` and copy
/// `emitNodes`/`autoGenerate` entries).
#[derive(Default)]
pub(crate) struct EmitContextShared {
    pub(crate) auto_generate: FxHashMap<NodeId, AutoGenerateInfo>,
    pub(crate) text_source: FxHashMap<NodeId, NodeId>,
    pub(crate) original: FxHashMap<NodeId, NodeId>,
    pub(crate) emit_nodes: LinkStore<NodeId, EmitNode>,
    pub(crate) assigned_name: FxHashMap<NodeId, NodeId>,
    pub(crate) class_this: FxHashMap<NodeId, NodeId>,
    pub(crate) var_scope_stack: Vec<VarScope>,
    pub(crate) let_scope_stack: Vec<VarScope>,
    pub(crate) emit_helpers: OrderedSet<EmitHelperRef>,
}

/// `type AutoGenerateId uint32`
pub type AutoGenerateId = u32;

/// `nextAutoGenerateId atomic.Uint32`
static NEXT_AUTO_GENERATE_ID: AtomicU32 = AtomicU32::new(0);

/// `nextAutoGenerateId.Add(1)`
pub(crate) fn next_auto_generate_id() -> AutoGenerateId {
    NEXT_AUTO_GENERATE_ID.fetch_add(1, Ordering::Relaxed) + 1
}

/// `type AutoGenerateInfo struct`
#[derive(Clone)]
pub struct AutoGenerateInfo {
    /// Specifies whether to auto-generate the text for an identifier.
    pub flags: crate::emit_flags::GeneratedIdentifierFlags,
    /// Ensures unique generated identifiers get unique names, but clones get the same name.
    pub id: AutoGenerateId,
    /// Optional prefix to apply to the start of the generated name
    pub prefix: String,
    /// Optional suffix to apply to the end of the generated name
    pub suffix: String,
    /// For a GeneratedIdentifierFlagsNode, the node from which to generate an identifier
    pub node: Option<NodeId>,
}

/// `type AutoGenerateOptions struct`
#[derive(Clone, Default)]
pub struct AutoGenerateOptions {
    pub flags: crate::emit_flags::GeneratedIdentifierFlags,
    pub prefix: String,
    pub suffix: String,
}

/// `type EmitContext struct`
pub struct EmitContext {
    /// Required. The NodeFactory to use to create new nodes
    pub factory: crate::factory::NodeFactory,
    pub(crate) shared: Shared,
}

impl Default for EmitContext {
    fn default() -> Self {
        Self::new()
    }
}

/// `(c *EmitContext) SetOriginalEx` — shared implementation for the
/// `onUpdate`/`onClone` factory hooks and `EmitContext::set_original_ex`.
pub(crate) fn set_original_shared(
    shared: &RefCell<EmitContextShared>,
    node: NodeId,
    original: NodeId,
    allow_overwrite: bool,
) {
    let mut shared = shared.borrow_mut();
    let emit_source = shared.emit_nodes.try_get(&original).map(|e| {
        let mut copy = EmitNode::default();
        copy.copy_from(e);
        copy
    });
    match shared.original.get(&node) {
        None => {
            shared.original.insert(node, original);
            if let Some(emit_source) = emit_source {
                shared.emit_nodes.get(node).copy_from(&emit_source);
            }
        }
        Some(&existing) if !allow_overwrite && existing != original => {
            if std::env::var("TSC_DBG_ORIG").is_ok() {
                eprintln!("[orig] node={node:?} existing={existing:?} new={original:?}");
            }
            panic!("Original node already set.")
        }
        Some(_) if allow_overwrite => {
            shared.original.insert(node, original);
        }
        _ => {}
    }
}

/// `(c *EmitContext) onCreate`
fn on_create(nodes: &mut Vec<Node>, node: NodeId) {
    nodes[node].flags |= ast::NodeFlags::SYNTHESIZED;
}

/// `(c *EmitContext) onUpdate`
fn on_update(shared: Shared) -> impl FnMut(&mut Vec<Node>, NodeId, NodeId) {
    move |_nodes, updated, original| set_original_shared(&shared, updated, original, false)
}

/// `(c *EmitContext) onClone`
fn on_clone(shared: Shared) -> impl FnMut(&mut Vec<Node>, NodeId, NodeId) {
    move |nodes, updated, original| {
        set_original_shared(&shared, updated, original, false);
        if ast::is_identifier(&nodes[updated]) || ast::is_private_identifier(&nodes[updated]) {
            let auto_generate = shared.borrow().auto_generate.get(&original).cloned();
            if let Some(auto_generate) = auto_generate {
                shared
                    .borrow_mut()
                    .auto_generate
                    .insert(updated, auto_generate);
            }
        }
    }
}

/// `emitFlags` on the shared tables (used by helpers that only hold `Shared`).
pub(crate) fn emit_flags(shared: &RefCell<EmitContextShared>, node: NodeId) -> EmitFlags {
    match shared.borrow_mut().emit_nodes.try_get(&node) {
        Some(emit_node) => emit_node.emit_flags,
        None => EmitFlags::NONE,
    }
}

/// `SetEmitFlags` on the shared tables.
pub(crate) fn set_emit_flags(shared: &RefCell<EmitContextShared>, node: NodeId, flags: EmitFlags) {
    shared.borrow_mut().emit_nodes.get(node).emit_flags = flags;
}

/// `AddEmitFlags` on the shared tables.
pub(crate) fn set_emit_flags_add(
    shared: &RefCell<EmitContextShared>,
    node: NodeId,
    flags: EmitFlags,
) {
    shared.borrow_mut().emit_nodes.get(node).emit_flags |= flags;
}

/// `getNodeForGeneratedNameWorker` on the shared tables.
pub(crate) fn get_node_for_generated_name_worker(
    shared: &Shared,
    nodes: &[Node],
    node: NodeId,
    auto_generate_id: AutoGenerateId,
) -> NodeId {
    let mut node = node;
    let mut original = shared.borrow().original.get(&node).copied();
    while let Some(o) = original {
        node = o;
        if ast::is_member_name(&nodes[node]) {
            // if "node" is a different generated name (having a different "autoGenerateId"), use it and stop traversing.
            let auto_generate = shared.borrow().auto_generate.get(&node).cloned();
            match auto_generate {
                None => break,
                Some(ag) if ag.flags.is_node() && ag.id != auto_generate_id => break,
                Some(ag) => {
                    if ag.flags.is_node() {
                        original = ag.node;
                        continue;
                    }
                }
            }
        }
        original = shared.borrow().original.get(&node).copied();
    }
    node
}

/// `(c *EmitContext) isHoistedFunction`
fn is_hoisted_function(shared: &RefCell<EmitContextShared>, nodes: &[Node], node: NodeId) -> bool {
    emit_flags(shared, node).0 & EmitFlags::CUSTOM_PROLOGUE.0 != 0
        && ast::is_function_declaration(&nodes[node])
}

/// `isHoistedVariable`
fn is_hoisted_variable(nodes: &[Node], node: NodeId) -> bool {
    ast::is_identifier(&nodes[node]) && nodes[node].initializer().is_none()
}

/// `(c *EmitContext) isHoistedVariableStatement`
fn is_hoisted_variable_statement(
    shared: &RefCell<EmitContextShared>,
    nodes: &[Node],
    node: NodeId,
) -> bool {
    emit_flags(shared, node).0 & EmitFlags::CUSTOM_PROLOGUE.0 != 0
        && ast::is_variable_statement(&nodes[node])
        && nodes[node]
            .as_variable_statement()
            .declaration_list
            .and_then(|d| nodes[d].as_variable_declaration_list().declarations.clone())
            .is_some_and(|d| tsc_core::core::every(&d.nodes, |n| is_hoisted_variable(nodes, *n)))
}

/// `core.Splice` wrapper returning an owned `Vec`.
fn splice_vec<T: Clone>(slice: &[T], start: i32, delete_count: i32, items: &[T]) -> Vec<T> {
    tsc_core::core::splice(slice, start, delete_count, items).into_owned()
}

impl EmitContext {
    /// `NewEmitContext()`
    pub fn new() -> EmitContext {
        let shared: Shared = Rc::new(RefCell::new(EmitContextShared::default()));
        let factory = crate::factory::NodeFactory::new(
            ast::NodeFactory::new(NodeFactoryHooks {
                on_create: Some(Box::new(on_create)),
                on_update: Some(Box::new(on_update(shared.clone()))),
                on_clone: Some(Box::new(on_clone(shared.clone()))),
            }),
            shared.clone(),
        );
        EmitContext { factory, shared }
    }

    /// A handle to the shared tables (for `PrinterNodeFactory`, the
    /// `NameGenerator`, and the `Printer` which read them directly just as Go
    /// package-internal callers do).
    pub(crate) fn shared(&self) -> Shared {
        self.shared.clone()
    }

    /// Creates a new NodeVisitor attached to this EmitContext.
    ///
    /// PORT: the hooks capture `shared` so they can keep updating the emit
    /// context while the visitor drives `cx.factory` (`factory.inner`).
    pub fn new_node_visitor<'v>(&self, visit: Box<ast::visitor::VisitFn<'v>>) -> NodeVisitor<'v> {
        let visit_parameters_shared = self.shared.clone();
        let visit_function_body_shared = self.shared.clone();
        let visit_iteration_body_shared = self.shared.clone();
        let visit_variable_environment_shared = self.shared.clone();
        let visit_embedded_statement_shared = self.shared.clone();
        NodeVisitor::new(
            visit,
            NodeVisitorHooks {
                visit_parameters: Some(Box::new(move |cx, nodes, v| {
                    visit_parameters(&visit_parameters_shared, cx, nodes, v)
                })),
                visit_function_body: Some(Box::new(move |cx, node, v| {
                    visit_function_body(&visit_function_body_shared, cx, node, v)
                })),
                visit_iteration_body: Some(Box::new(move |cx, node, v| {
                    visit_iteration_body(&visit_iteration_body_shared, cx, node, v)
                })),
                visit_top_level_statements: Some(Box::new(move |cx, nodes, v| {
                    visit_variable_environment(&visit_variable_environment_shared, cx, nodes, v)
                })),
                visit_embedded_statement: Some(Box::new(move |cx, node, v| {
                    visit_embedded_statement(&visit_embedded_statement_shared, cx, node, v)
                })),
                ..Default::default()
            },
        )
    }

    //
    // Environment tracking
    //

    /// `StartVariableEnvironment` — starts a new VariableEnvironment used to
    /// track hoisted `var` statements and function declarations.
    ///
    /// see: https://tc39.es/ecma262/#table-additional-state-components-for-ecmascript-code-execution-contexts
    ///
    /// NOTE: This is the equivalent of `transformContext.startLexicalEnvironment` in Strada.
    pub fn start_variable_environment(&mut self) {
        self.shared
            .borrow_mut()
            .var_scope_stack
            .push(VarScope::default());
        self.start_lexical_environment();
    }

    /// `EndVariableEnvironment` — ends the current VariableEnvironment,
    /// returning a list of statements that should be emitted at the start of
    /// the current scope.
    ///
    /// NOTE: This is the equivalent of `transformContext.endLexicalEnvironment` in Strada.
    pub fn end_variable_environment(&mut self, nodes: &mut Vec<Node>) -> Vec<NodeId> {
        let scope = self.shared.borrow_mut().var_scope_stack.pop().unwrap();
        let mut statements = scope.functions.clone();
        if !scope.variables.is_empty() {
            let list = self.factory.new_node_list(scope.variables);
            let var_decl_list =
                self.factory
                    .new_variable_declaration_list(nodes, Some(list), ast::NodeFlags::NONE);
            let var_statement =
                self.factory
                    .new_variable_statement(nodes, None, Some(var_decl_list));
            self.set_emit_flags(var_statement, EmitFlags::CUSTOM_PROLOGUE);
            statements.push(var_statement);
        }
        statements.extend(scope.initialization_statements.iter().copied());
        statements.extend(self.end_lexical_environment(nodes));
        statements
    }

    /// `EndAndMergeVariableEnvironmentList` — invokes
    /// `EndVariableEnvironment()` and merges the results into `statements`.
    pub fn end_and_merge_variable_environment_list(
        &mut self,
        nodes: &mut Vec<Node>,
        statements: Option<NodeList>,
    ) -> Option<NodeList> {
        let declarations = self.end_variable_environment(nodes);
        let statements_nodes: &[NodeId] = statements.as_ref().map_or(&[], |l| &l.nodes);
        let (result, changed) = self.merge_environment(nodes, statements_nodes, &declarations);
        if changed {
            let mut list = self.factory.new_node_list(result);
            list.loc = statements.as_ref().map_or(TextRange::default(), |l| l.loc);
            return Some(list);
        }
        statements
    }

    /// `EndAndMergeVariableEnvironment` — invokes `EndVariableEnvironment()`
    /// and merges the results into `statements`.
    pub fn end_and_merge_variable_environment(
        &mut self,
        nodes: &mut Vec<Node>,
        statements: &[NodeId],
    ) -> Vec<NodeId> {
        let declarations = self.end_variable_environment(nodes);
        self.merge_environment(nodes, statements, &declarations).0
    }

    /// `AddVariableDeclaration` — adds a `var` declaration to the current
    /// VariableEnvironment.
    ///
    /// NOTE: This is the equivalent of `transformContext.hoistVariableDeclaration` in Strada.
    pub fn add_variable_declaration(&mut self, nodes: &mut Vec<Node>, name: NodeId) {
        let var_decl = self
            .factory
            .new_variable_declaration(nodes, Some(name), None, None, None);
        self.set_emit_flags(var_decl, EmitFlags::NO_NESTED_SOURCE_MAPS);
        let mut shared = self.shared.borrow_mut();
        let scope = shared
            .var_scope_stack
            .last_mut()
            .expect("variable scope stack is empty");
        scope.variables.push(var_decl);
        if scope.flags & ENVIRONMENT_FLAGS_IN_PARAMETERS != 0 {
            scope.flags |= ENVIRONMENT_FLAGS_VARIABLES_HOISTED_IN_PARAMETERS;
        }
    }

    /// `AddHoistedFunctionDeclaration` — adds a hoisted function declaration
    /// to the current VariableEnvironment.
    ///
    /// NOTE: This is the equivalent of `transformContext.hoistFunctionDeclaration` in Strada.
    pub fn add_hoisted_function_declaration(&mut self, node: NodeId) {
        self.set_emit_flags(node, EmitFlags::CUSTOM_PROLOGUE);
        self.shared
            .borrow_mut()
            .var_scope_stack
            .last_mut()
            .expect("variable scope stack is empty")
            .functions
            .push(node);
    }

    /// `StartLexicalEnvironment` — starts a new LexicalEnvironment used to
    /// track block-scoped `let`, `const`, and `using` declarations.
    ///
    /// see: https://tc39.es/ecma262/#table-additional-state-components-for-ecmascript-code-execution-contexts
    ///
    /// NOTE: This is the equivalent of `transformContext.startBlockScope` in Strada.
    /// NOTE: This is *not* the same as `startLexicalEnvironment` in Strada as that method is incorrectly named.
    pub fn start_lexical_environment(&mut self) {
        self.shared
            .borrow_mut()
            .let_scope_stack
            .push(VarScope::default());
    }

    /// `EndLexicalEnvironment` — ends the current LexicalEnvironment,
    /// returning a list of statements that should be emitted at the start of
    /// the current scope.
    ///
    /// NOTE: This is the equivalent of `transformContext.endLexicalEnvironment` in Strada.
    /// NOTE: This is *not* the same as `endLexicalEnvironment` in Strada as that method is incorrectly named.
    pub fn end_lexical_environment(&mut self, nodes: &mut Vec<Node>) -> Vec<NodeId> {
        let scope = self.shared.borrow_mut().let_scope_stack.pop().unwrap();
        let mut statements = Vec::new();
        if !scope.variables.is_empty() {
            let list = self.factory.new_node_list(scope.variables);
            let var_decl_list =
                self.factory
                    .new_variable_declaration_list(nodes, Some(list), ast::NodeFlags::LET);
            let var_statement =
                self.factory
                    .new_variable_statement(nodes, None, Some(var_decl_list));
            self.set_emit_flags(var_statement, EmitFlags::CUSTOM_PROLOGUE);
            statements.push(var_statement);
        }
        statements
    }

    /// `EndAndMergeLexicalEnvironmentList` — invokes `EndLexicalEnvironment()`
    /// and merges the results into `statements`.
    pub fn end_and_merge_lexical_environment_list(
        &mut self,
        nodes: &mut Vec<Node>,
        statements: Option<NodeList>,
    ) -> Option<NodeList> {
        let declarations = self.end_lexical_environment(nodes);
        let statements_nodes: &[NodeId] = statements.as_ref().map_or(&[], |l| &l.nodes);
        let (result, changed) = self.merge_environment(nodes, statements_nodes, &declarations);
        if changed {
            let mut list = self.factory.new_node_list(result);
            list.loc = statements.as_ref().map_or(TextRange::default(), |l| l.loc);
            return Some(list);
        }
        statements
    }

    /// `EndAndMergeLexicalEnvironment` — invokes `EndLexicalEnvironment()`
    /// and merges the results into `statements`.
    pub fn end_and_merge_lexical_environment(
        &mut self,
        nodes: &mut Vec<Node>,
        statements: &[NodeId],
    ) -> Vec<NodeId> {
        let declarations = self.end_lexical_environment(nodes);
        self.merge_environment(nodes, statements, &declarations).0
    }

    /// `AddLexicalDeclaration` — adds a `let` declaration to the current
    /// LexicalEnvironment.
    pub fn add_lexical_declaration(&mut self, nodes: &mut Vec<Node>, name: NodeId) {
        let var_decl = self
            .factory
            .new_variable_declaration(nodes, Some(name), None, None, None);
        self.set_emit_flags(var_decl, EmitFlags::NO_NESTED_SOURCE_MAPS);
        self.shared
            .borrow_mut()
            .let_scope_stack
            .last_mut()
            .expect("lexical scope stack is empty")
            .variables
            .push(var_decl);
    }

    /// `MergeEnvironmentList` — merges declarations produced by
    /// `EndVariableEnvironment()` or `EndLexicalEnvironment()` into a
    /// statement list.
    pub fn merge_environment_list(
        &mut self,
        nodes: &mut Vec<Node>,
        statements: &NodeList,
        declarations: &[NodeId],
    ) -> NodeList {
        let (result, changed) = self.merge_environment(nodes, &statements.nodes, declarations);
        if changed {
            let mut list = self.factory.new_node_list(result);
            list.loc = statements.loc;
            return list;
        }
        statements.clone()
    }

    /// `MergeEnvironment` — merges declarations produced by
    /// `EndVariableEnvironment()` or `EndLexicalEnvironment()` into a slice
    /// of statements.
    pub fn merge_environment(
        &mut self,
        nodes: &mut Vec<Node>,
        statements: &[NodeId],
        declarations: &[NodeId],
    ) -> (Vec<NodeId>, bool) {
        if declarations.is_empty() {
            return (statements.to_vec(), false);
        }

        // When we merge new lexical statements into an existing statement list, we merge them in the following manner:
        //
        // Given:
        //
        // | Left                               | Right                               |
        // |------------------------------------|-------------------------------------|
        // | [standard prologues (left)]        | [standard prologues (right)]        |
        // | [hoisted functions (left)]         | [hoisted functions (right)]         |
        // | [hoisted variables (left)]         | [hoisted variables (right)]         |
        // | [lexical init statements (left)]   | [lexical init statements (right)]   |
        // | [other statements (left)]          |                                     |
        //
        // The resulting statement list will be:
        //
        // | Result                              |
        // |-------------------------------------|
        // | [standard prologues (right)]        |
        // | [standard prologues (left)]         |
        // | [hoisted functions (right)]         |
        // | [hoisted functions (left)]          |
        // | [hoisted variables (right)]         |
        // | [hoisted variables (left)]          |
        // | [lexical init statements (right)]   |
        // | [lexical init statements (left)]    |
        // | [other statements (left)]           |
        //
        // NOTE: It is expected that new lexical init statements must be evaluated before existing lexical init statements,
        // as the prior transformation may depend on the evaluation of the lexical init statements to be in the correct state.

        let mut changed = false;
        let shared = self.shared.clone();

        // find standard prologues on left in the following order: standard directives, hoisted functions, hoisted variables, other custom
        let left_standard_prologue_end = find_span_end(
            statements,
            |s| ast::is_prologue_directive(&nodes[*s], nodes),
            0,
        );
        let left_hoisted_functions_end = find_span_end(
            statements,
            |s| is_hoisted_function(&shared, nodes, *s),
            left_standard_prologue_end,
        );
        let left_hoisted_variables_end = find_span_end(
            statements,
            |s| is_hoisted_variable_statement(&shared, nodes, *s),
            left_hoisted_functions_end,
        );

        // find standard prologues on right in the following order: standard directives, hoisted functions, hoisted variables, other custom
        let right_standard_prologue_end = find_span_end(
            declarations,
            |s| ast::is_prologue_directive(&nodes[*s], nodes),
            0,
        );
        let right_hoisted_functions_end = find_span_end(
            declarations,
            |s| is_hoisted_function(&shared, nodes, *s),
            right_standard_prologue_end,
        );
        let right_hoisted_variables_end = find_span_end(
            declarations,
            |s| is_hoisted_variable_statement(&shared, nodes, *s),
            right_hoisted_functions_end,
        );
        let right_custom_prologue_end = find_span_end(
            declarations,
            |s| emit_flags(&shared, *s).0 & EmitFlags::CUSTOM_PROLOGUE.0 != 0,
            right_hoisted_variables_end,
        );
        if right_custom_prologue_end != declarations.len() {
            panic!("Expected declarations to be valid standard or custom prologues");
        }

        let mut left: Vec<NodeId> = statements.to_vec();

        // splice other custom prologues from right into left
        if right_custom_prologue_end > right_hoisted_variables_end {
            left = splice_vec(
                &left,
                left_hoisted_variables_end as i32,
                0,
                &declarations[right_hoisted_variables_end..right_custom_prologue_end],
            );
            changed = true;
        }

        // splice hoisted variables from right into left
        if right_hoisted_variables_end > right_hoisted_functions_end {
            left = splice_vec(
                &left,
                left_hoisted_functions_end as i32,
                0,
                &declarations[right_hoisted_functions_end..right_hoisted_variables_end],
            );
            changed = true;
        }

        // splice hoisted functions from right into left
        if right_hoisted_functions_end > right_standard_prologue_end {
            left = splice_vec(
                &left,
                left_standard_prologue_end as i32,
                0,
                &declarations[right_standard_prologue_end..right_hoisted_functions_end],
            );
            changed = true;
        }

        // splice standard prologues from right into left (that are not already in left)
        if right_standard_prologue_end > 0 {
            if left_standard_prologue_end == 0 {
                left = splice_vec(&left, 0, 0, &declarations[..right_standard_prologue_end]);
                changed = true;
            } else {
                let mut left_prologues: Set<String> = Set::new();
                for &statement in statements.iter().take(left_standard_prologue_end) {
                    if let Some(expr) = nodes[statement].expression() {
                        left_prologues.add(nodes[expr].text(nodes).into_owned());
                    }
                }
                for &right_prologue in declarations[..right_standard_prologue_end].iter().rev() {
                    let text = nodes[right_prologue]
                        .expression()
                        .map(|e| nodes[e].text(nodes).into_owned())
                        .unwrap_or_default();
                    if !left_prologues.has(&text) {
                        left.insert(0, right_prologue);
                        changed = true;
                    }
                }
            }
        }

        (left, changed)
    }

    /// `(c *EmitContext) isCustomPrologue`
    pub(crate) fn is_custom_prologue(&self, node: NodeId) -> bool {
        self.emit_flags(node).0 & EmitFlags::CUSTOM_PROLOGUE.0 != 0
    }

    //
    // Name Generation
    //

    /// `HasAutoGenerateInfo` — gets whether a given name has an associated
    /// AutoGenerateInfo entry.
    pub fn has_auto_generate_info(&self, node: Option<NodeId>) -> bool {
        match node {
            Some(node) => self.shared.borrow().auto_generate.contains_key(&node),
            None => false,
        }
    }

    /// `GetAutoGenerateInfo` — gets the associated AutoGenerateInfo entry for
    /// a given name.
    pub fn get_auto_generate_info(&self, name: Option<NodeId>) -> Option<AutoGenerateInfo> {
        self.shared.borrow().auto_generate.get(&name?).cloned()
    }

    /// `GetNodeForGeneratedName` — walks the associated AutoGenerateInfo
    /// entries of a name to find the root Node from which the name should be
    /// generated.
    pub fn get_node_for_generated_name(&self, nodes: &[Node], name: NodeId) -> NodeId {
        let auto_generate = self.shared.borrow().auto_generate.get(&name).cloned();
        if let Some(auto_generate) = auto_generate
            && auto_generate.flags.is_node()
        {
            return get_node_for_generated_name_worker(
                &self.shared,
                nodes,
                auto_generate.node.unwrap(),
                auto_generate.id,
            );
        }
        name
    }

    //
    // Original Node Tracking
    //

    /// `SetOriginal` — sets the original node for a given node.
    ///
    /// NOTE: This is the equivalent to `setOriginalNode` in Strada.
    pub fn set_original(&self, node: NodeId, original: NodeId) {
        self.set_original_ex(node, original, false)
    }

    /// `UnsetOriginal`
    pub fn unset_original(&self, node: NodeId) {
        self.shared.borrow_mut().original.remove(&node);
    }

    /// Drops every per-node emit-table entry keyed by `node`.
    ///
    /// PORT: nodebuilder scratch-arena clones mint temporary ids in the
    /// destination file's index space; after the clone tail is relocated,
    /// the tmp ids would alias future real ids and poison their emit data
    /// (Go never reuses node pointers, so it needs no counterpart).
    pub fn dispose_emit_node(&self, node: NodeId) {
        let mut shared = self.shared.borrow_mut();
        shared.auto_generate.remove(&node);
        shared.text_source.remove(&node);
        shared.original.remove(&node);
        shared.emit_nodes.remove(&node);
        shared.assigned_name.remove(&node);
        shared.class_this.remove(&node);
    }

    /// `SetOriginalEx`
    pub fn set_original_ex(&self, node: NodeId, original: NodeId, allow_overwrite: bool) {
        set_original_shared(&self.shared, node, original, allow_overwrite)
    }

    /// `Original` — gets the original node for a given node.
    ///
    /// NOTE: This is the equivalent to reading `node.original` in Strada.
    pub fn original(&self, node: NodeId) -> Option<NodeId> {
        self.shared.borrow().original.get(&node).copied()
    }

    /// `MostOriginal` — gets the most original node associated with this node
    /// by walking Original pointers.
    ///
    /// NOTE: This method is analogous to `getOriginalNode` in the old compiler, but the name has changed to avoid accidental
    /// conflation with `SetOriginal`/`Original`
    pub fn most_original(&self, node: Option<NodeId>) -> Option<NodeId> {
        let mut node = node;
        while let Some(n) = node {
            match self.original(n) {
                Some(original) => node = Some(original),
                None => break,
            }
        }
        node
    }

    /// `ParseNode` — gets the original parse tree node for a given node.
    ///
    /// NOTE: This is the equivalent to `getParseTreeNode` in Strada.
    pub fn parse_node(&self, nodes: &[Node], node: NodeId) -> Option<NodeId> {
        let node = self.most_original(Some(node))?;
        if ast::is_parse_tree_node(&nodes[node]) {
            return Some(node);
        }
        None
    }

    /// `IsFileLevelUniqueName`
    pub fn is_file_level_unique_name(
        &self,
        nodes: &[Node],
        source_file: NodeId,
        name: &str,
        has_global_name: &mut dyn FnMut(&str) -> bool,
    ) -> bool {
        if has_global_name(name) {
            return false;
        }
        match self.most_original(Some(source_file)) {
            Some(source_file) => !ast::has_identifier(nodes, source_file, name),
            None => true,
        }
    }

    //
    // Emit-related Data
    //

    /// `EmitFlags`
    pub fn emit_flags(&self, node: NodeId) -> EmitFlags {
        emit_flags(&self.shared, node)
    }

    /// `SetEmitFlags`
    pub fn set_emit_flags(&self, node: NodeId, flags: EmitFlags) {
        self.shared.borrow_mut().emit_nodes.get(node).emit_flags = flags;
    }

    /// `AddEmitFlags`
    pub fn add_emit_flags(&self, node: NodeId, flags: EmitFlags) {
        self.shared.borrow_mut().emit_nodes.get(node).emit_flags |= flags;
    }

    /// `SnippetElement`
    pub fn snippet_element(&self, node: NodeId) -> Option<SnippetElement> {
        match self.shared.borrow_mut().emit_nodes.try_get(&node) {
            Some(emit_node) => emit_node.snippet_element.as_deref().cloned(),
            None => None,
        }
    }

    /// `SetSnippetElement`
    pub fn set_snippet_element(&self, node: NodeId, snippet_element: SnippetElement) {
        self.shared
            .borrow_mut()
            .emit_nodes
            .get(node)
            .snippet_element = Some(Box::new(snippet_element));
    }

    /// `CommentRange` — gets the range to use for a node when emitting comments.
    pub fn comment_range(&self, nodes: &[Node], node: NodeId) -> TextRange {
        if let Some(emit_node) = self.shared.borrow_mut().emit_nodes.try_get(&node)
            && emit_node.flags & HAS_COMMENT_RANGE != 0
        {
            return emit_node.comment_range;
        }
        nodes[node].loc
    }

    /// `SetCommentRange` — sets the range to use for a node when emitting comments.
    pub fn set_comment_range(&self, node: NodeId, loc: TextRange) {
        let mut shared = self.shared.borrow_mut();
        let emit_node = shared.emit_nodes.get(node);
        emit_node.comment_range = loc;
        emit_node.flags |= HAS_COMMENT_RANGE;
    }

    /// `AssignCommentRange` — sets the range to use for a node when emitting comments.
    pub fn assign_comment_range(&self, nodes: &[Node], to: NodeId, from: NodeId) {
        let range = self.comment_range(nodes, from);
        self.set_comment_range(to, range);
    }

    /// `SourceMapRange` — gets the range to use for a node when emitting source maps.
    pub fn source_map_range(&self, nodes: &[Node], node: NodeId) -> TextRange {
        if let Some(emit_node) = self.shared.borrow_mut().emit_nodes.try_get(&node)
            && emit_node.flags & HAS_SOURCE_MAP_RANGE != 0
        {
            return emit_node.source_map_range;
        }
        nodes[node].loc
    }

    /// `SetSourceMapRange` — sets the range to use for a node when emitting source maps.
    pub fn set_source_map_range(&self, node: NodeId, loc: TextRange) {
        let mut shared = self.shared.borrow_mut();
        let emit_node = shared.emit_nodes.get(node);
        emit_node.source_map_range = loc;
        emit_node.flags |= HAS_SOURCE_MAP_RANGE;
    }

    /// `AssignSourceMapRange` — sets the range to use for a node when emitting source maps.
    pub fn assign_source_map_range(&self, nodes: &[Node], to: NodeId, from: NodeId) {
        let range = self.source_map_range(nodes, from);
        self.set_source_map_range(to, range);
    }

    /// `AssignCommentAndSourceMapRanges` — sets the range to use for a node
    /// when emitting comments and source maps.
    pub fn assign_comment_and_source_map_ranges(&self, nodes: &[Node], to: NodeId, from: NodeId) {
        let comment_range = self.comment_range(nodes, from);
        let source_map_range = self.source_map_range(nodes, from);
        let mut shared = self.shared.borrow_mut();
        let emit_node = shared.emit_nodes.get(to);
        emit_node.comment_range = comment_range;
        emit_node.source_map_range = source_map_range;
        emit_node.flags |= HAS_COMMENT_RANGE | HAS_SOURCE_MAP_RANGE;
    }

    /// `TokenSourceMapRange` — gets the range for a token of a node when
    /// emitting source maps.
    pub fn token_source_map_range(&self, node: NodeId, kind: Kind) -> Option<TextRange> {
        if let Some(emit_node) = self.shared.borrow_mut().emit_nodes.try_get(&node)
            && let Some(ranges) = &emit_node.token_source_map_ranges
        {
            return ranges.get(&kind).copied();
        }
        None
    }

    /// `SetTokenSourceMapRange` — sets the range for a token of a node when
    /// emitting source maps.
    pub fn set_token_source_map_range(&self, node: NodeId, kind: Kind, loc: TextRange) {
        let mut shared = self.shared.borrow_mut();
        let emit_node = shared.emit_nodes.get(node);
        emit_node
            .token_source_map_ranges
            .get_or_insert_with(FxHashMap::default)
            .insert(kind, loc);
    }

    /// `AssignedName`
    pub fn assigned_name(&self, node: NodeId) -> Option<NodeId> {
        self.shared.borrow().assigned_name.get(&node).copied()
    }

    /// `TextSource`
    pub fn text_source(&self, node: NodeId) -> Option<NodeId> {
        self.shared.borrow().text_source.get(&node).copied()
    }

    /// `SetAssignedName`
    pub fn set_assigned_name(&self, node: NodeId, name: NodeId) {
        self.shared.borrow_mut().assigned_name.insert(node, name);
    }

    /// `ClassThis`
    pub fn class_this(&self, node: NodeId) -> Option<NodeId> {
        self.shared.borrow().class_this.get(&node).copied()
    }

    /// `SetClassThis`
    pub fn set_class_this(&self, node: NodeId, class_this: NodeId) {
        self.shared.borrow_mut().class_this.insert(node, class_this);
    }

    /// `RequestEmitHelper`
    pub fn request_emit_helper(&mut self, helper: &Arc<EmitHelper>) {
        if helper.scoped {
            panic!("Cannot request a scoped emit helper");
        }
        for h in &helper.dependencies {
            self.request_emit_helper(h);
        }
        self.shared
            .borrow_mut()
            .emit_helpers
            .add(EmitHelperRef(helper.clone()));
    }

    /// `ReadEmitHelpers`
    pub fn read_emit_helpers(&mut self) -> Vec<Arc<EmitHelper>> {
        let mut shared = self.shared.borrow_mut();
        let helpers: Vec<Arc<EmitHelper>> =
            shared.emit_helpers.values().map(|h| h.0.clone()).collect();
        shared.emit_helpers.clear();
        helpers
    }

    /// `AddEmitHelper`
    pub fn add_emit_helper(&self, node: NodeId, helpers: &[Arc<EmitHelper>]) {
        let mut shared = self.shared.borrow_mut();
        let emit_node = shared.emit_nodes.get(node);
        for h in helpers {
            if !emit_node.helpers.iter().any(|x| Arc::ptr_eq(x, h)) {
                emit_node.helpers.push(h.clone());
            }
        }
    }

    /// `MoveEmitHelpers`
    pub fn move_emit_helpers(
        &self,
        source: NodeId,
        target: NodeId,
        mut predicate: impl FnMut(&Arc<EmitHelper>) -> bool,
    ) {
        let mut shared = self.shared.borrow_mut();
        if shared.emit_nodes.try_get(&source).is_none() {
            return;
        }
        let mut source_emit_helpers = std::mem::take(&mut shared.emit_nodes.get(source).helpers);
        if source_emit_helpers.is_empty() {
            shared.emit_nodes.get(source).helpers = source_emit_helpers;
            return;
        }

        let mut helpers_removed = 0usize;
        for i in 0..source_emit_helpers.len() {
            let helper = source_emit_helpers[i].clone();
            if predicate(&helper) {
                helpers_removed += 1;
                let target_emit_node = shared.emit_nodes.get(target);
                if !target_emit_node
                    .helpers
                    .iter()
                    .any(|x| Arc::ptr_eq(x, &helper))
                {
                    target_emit_node.helpers.push(helper);
                }
            } else if helpers_removed > 0 {
                source_emit_helpers[i - helpers_removed] = helper;
            }
        }

        if helpers_removed > 0 {
            source_emit_helpers.truncate(source_emit_helpers.len() - helpers_removed);
        }
        shared.emit_nodes.get(source).helpers = source_emit_helpers;
    }

    /// `GetEmitHelpers`
    pub fn get_emit_helpers(&self, node: NodeId) -> Vec<Arc<EmitHelper>> {
        match self.shared.borrow_mut().emit_nodes.try_get(&node) {
            Some(emit_node) => emit_node.helpers.clone(),
            None => Vec::new(),
        }
    }

    /// `GetExternalHelpersModuleName`
    pub fn get_external_helpers_module_name(&self, nodes: &[Node], node: NodeId) -> Option<NodeId> {
        if let Some(parse_node) = self.parse_node(nodes, node)
            && let Some(emit_node) = self.shared.borrow_mut().emit_nodes.try_get(&parse_node)
        {
            return emit_node.external_helpers_module_name;
        }
        None
    }

    /// `SetExternalHelpersModuleName`
    pub fn set_external_helpers_module_name(&self, nodes: &[Node], node: NodeId, name: NodeId) {
        let Some(parse_node) = self.parse_node(nodes, node) else {
            panic!(
                "Node must be a parse tree node or have an Original pointer to a parse tree node."
            )
        };
        self.shared
            .borrow_mut()
            .emit_nodes
            .get(parse_node)
            .external_helpers_module_name = Some(name);
    }

    /// `HasRecordedExternalHelpers`
    pub fn has_recorded_external_helpers(&self, nodes: &[Node], node: NodeId) -> bool {
        if let Some(parse_node) = self.parse_node(nodes, node) {
            return match self.shared.borrow_mut().emit_nodes.try_get(&parse_node) {
                Some(emit_node) => {
                    emit_node.external_helpers_module_name.is_some()
                        || emit_node.emit_flags.0 & EmitFlags::EXTERNAL_HELPERS.0 != 0
                }
                None => false,
            };
        }
        false
    }

    /// `IsCallToHelper`
    pub fn is_call_to_helper(
        &self,
        nodes: &[Node],
        first_segment: NodeId,
        helper_name: &str,
    ) -> bool {
        ast::is_call_expression(&nodes[first_segment])
            && nodes[first_segment].expression().is_some_and(|expr| {
                ast::is_identifier(&nodes[expr])
                    && self.emit_flags(expr).0 & EmitFlags::HELPER_NAME.0 != 0
                    && &*nodes[expr].text(nodes) == helper_name
            })
    }

    //
    // Visitor Hooks — implemented as free functions on `Shared` below; the
    // methods here adapt `&mut self`.
    //

    /// `VisitVariableEnvironment`
    pub fn visit_variable_environment(
        &mut self,
        cx: &mut VisitorCx<'_, '_>,
        nodes: Option<NodeList>,
        visitor: &NodeVisitor<'_>,
    ) -> Option<NodeList> {
        visit_variable_environment(&self.shared, cx, nodes, visitor)
    }

    /// `VisitParameters`
    pub fn visit_parameters(
        &mut self,
        cx: &mut VisitorCx<'_, '_>,
        nodes: Option<NodeList>,
        visitor: &NodeVisitor<'_>,
    ) -> Option<NodeList> {
        visit_parameters(&self.shared, cx, nodes, visitor)
    }

    /// `AddInitializationStatement`
    pub fn add_initialization_statement(&self, node: NodeId) {
        self.add_emit_flags(node, EmitFlags::CUSTOM_PROLOGUE);
        let mut shared = self.shared.borrow_mut();
        match shared.var_scope_stack.last_mut() {
            Some(scope) => scope.initialization_statements.push(node),
            None => {
                panic!(
                    "Tried to add an initialization statement without a surrounding variable scope"
                )
            }
        }
    }

    /// `ConvertToFunctionBlock`
    pub fn convert_to_function_block(
        &mut self,
        nodes: &mut Vec<Node>,
        node: NodeId,
        multi_line: bool,
    ) -> NodeId {
        if ast::is_block(&nodes[node]) {
            return node;
        }
        let mut return_statement = self.factory.new_return_statement(nodes, Some(node));
        nodes[return_statement].loc = nodes[node].loc;
        let mut statements = self.factory.new_node_list([return_statement]);
        statements.loc = nodes[node].loc;
        let block = self.factory.new_block(nodes, Some(statements), multi_line);
        nodes[block].loc = nodes[node].loc;
        block
    }

    /// `VisitFunctionBody`
    pub fn visit_function_body(
        &mut self,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
        visitor: &NodeVisitor<'_>,
    ) -> Option<NodeId> {
        visit_function_body(&self.shared, cx, node?, visitor)
    }

    /// `VisitIterationBody`
    pub fn visit_iteration_body(
        &mut self,
        cx: &mut VisitorCx<'_, '_>,
        body: Option<NodeId>,
        visitor: &NodeVisitor<'_>,
    ) -> Option<NodeId> {
        visit_iteration_body(&self.shared, cx, body?, visitor)
    }

    /// `VisitEmbeddedStatement`
    pub fn visit_embedded_statement(
        &mut self,
        cx: &mut VisitorCx<'_, '_>,
        node: Option<NodeId>,
        visitor: &NodeVisitor<'_>,
    ) -> Option<NodeId> {
        visit_embedded_statement(&self.shared, cx, node?, visitor)
    }

    /// `SetSyntheticLeadingComments`
    pub fn set_synthetic_leading_comments(
        &self,
        node: NodeId,
        comments: Vec<SynthesizedComment>,
    ) -> NodeId {
        self.shared
            .borrow_mut()
            .emit_nodes
            .get(node)
            .leading_comments = comments;
        node
    }

    /// `AddSyntheticLeadingComment`
    pub fn add_synthetic_leading_comment(
        &self,
        node: NodeId,
        kind: Kind,
        text: &str,
        has_trailing_new_line: bool,
    ) -> NodeId {
        let comment = SynthesizedComment {
            kind,
            loc: TextRange::new(-1, -1),
            has_trailing_new_line,
            text: text.to_string(),
            ..Default::default()
        };
        self.shared
            .borrow_mut()
            .emit_nodes
            .get(node)
            .leading_comments
            .push(comment);
        node
    }

    /// `GetSyntheticLeadingComments`
    pub fn get_synthetic_leading_comments(&self, node: NodeId) -> Vec<SynthesizedComment> {
        let mut shared = self.shared.borrow_mut();
        if shared.emit_nodes.has(&node) {
            return shared.emit_nodes.get(node).leading_comments.clone();
        }
        Vec::new()
    }

    /// `SetSyntheticTrailingComments`
    pub fn set_synthetic_trailing_comments(
        &self,
        node: NodeId,
        comments: Vec<SynthesizedComment>,
    ) -> NodeId {
        self.shared
            .borrow_mut()
            .emit_nodes
            .get(node)
            .trailing_comments = comments;
        node
    }

    /// `AddSyntheticTrailingComment`
    pub fn add_synthetic_trailing_comment(
        &self,
        node: NodeId,
        kind: Kind,
        text: &str,
        has_trailing_new_line: bool,
    ) -> NodeId {
        let comment = SynthesizedComment {
            kind,
            loc: TextRange::new(-1, -1),
            has_trailing_new_line,
            text: text.to_string(),
            ..Default::default()
        };
        self.shared
            .borrow_mut()
            .emit_nodes
            .get(node)
            .trailing_comments
            .push(comment);
        node
    }

    /// `GetSyntheticTrailingComments`
    pub fn get_synthetic_trailing_comments(&self, node: NodeId) -> Vec<SynthesizedComment> {
        let mut shared = self.shared.borrow_mut();
        if shared.emit_nodes.has(&node) {
            return shared.emit_nodes.get(node).trailing_comments.clone();
        }
        Vec::new()
    }

    /// `SetTypeNode` — stores the original type node on a name node when the
    /// type is erased, so the emitter can use the type's position for comment
    /// preservation.
    pub fn set_type_node(&self, node: NodeId, type_node: NodeId) {
        self.shared.borrow_mut().emit_nodes.get(node).type_node = Some(type_node);
    }

    /// `GetTypeNode` — gets the type node stored on a name node by the type
    /// eraser.
    pub fn get_type_node(&self, node: NodeId) -> Option<NodeId> {
        match self.shared.borrow_mut().emit_nodes.try_get(&node) {
            Some(emit_node) => emit_node.type_node,
            None => None,
        }
    }

    /// `NewNotEmittedStatement`
    pub fn new_not_emitted_statement(&mut self, nodes: &mut Vec<Node>, node: NodeId) -> NodeId {
        let statement = self.factory.new_not_emitted_statement(nodes);
        nodes[statement].loc = nodes[node].loc;
        self.set_original(statement, node);
        self.assign_comment_range(nodes, statement, node);
        statement
    }
}

//
// Visitor Hooks
//

/// `(c *EmitContext) VisitVariableEnvironment`
fn visit_variable_environment(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    nodes: Option<NodeList>,
    visitor: &NodeVisitor<'_>,
) -> Option<NodeList> {
    shared
        .borrow_mut()
        .var_scope_stack
        .push(VarScope::default());
    shared
        .borrow_mut()
        .let_scope_stack
        .push(VarScope::default());
    let visited = visitor.visit_nodes(cx, nodes);
    end_and_merge_variable_environment_list_shared(shared, cx, visited)
}

/// `endAndMergeVariableEnvironmentList` on `Shared` (no `EmitContext`
/// receiver — the factory comes from `cx`).
fn end_and_merge_variable_environment_list_shared(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    statements: Option<NodeList>,
) -> Option<NodeList> {
    let declarations = end_variable_environment_shared(shared, cx);
    let statements_nodes: &[NodeId] = statements.as_ref().map_or(&[], |l| &l.nodes);
    let (result, changed) =
        merge_environment_shared(shared, cx.nodes, statements_nodes, &declarations);
    if changed {
        let mut list = cx.factory.new_node_list(result);
        list.loc = statements.as_ref().map_or(TextRange::default(), |l| l.loc);
        return Some(list);
    }
    statements
}

/// `endVariableEnvironment` on `Shared`.
fn end_variable_environment_shared(shared: &Shared, cx: &mut VisitorCx<'_, '_>) -> Vec<NodeId> {
    let scope = shared.borrow_mut().var_scope_stack.pop().unwrap();
    let mut statements = scope.functions.clone();
    if !scope.variables.is_empty() {
        let list = cx.factory.new_node_list(scope.variables);
        let var_decl_list =
            cx.factory
                .new_variable_declaration_list(cx.nodes, Some(list), ast::NodeFlags::NONE);
        let var_statement = cx
            .factory
            .new_variable_statement(cx.nodes, None, Some(var_decl_list));
        {
            let mut s = shared.borrow_mut();
            s.emit_nodes.get(var_statement).emit_flags = EmitFlags::CUSTOM_PROLOGUE;
        }
        statements.push(var_statement);
    }
    statements.extend(scope.initialization_statements.iter().copied());
    statements.extend(end_lexical_environment_shared(shared, cx));
    statements
}

/// `endLexicalEnvironment` on `Shared`.
fn end_lexical_environment_shared(shared: &Shared, cx: &mut VisitorCx<'_, '_>) -> Vec<NodeId> {
    let scope = shared.borrow_mut().let_scope_stack.pop().unwrap();
    let mut statements = Vec::new();
    if !scope.variables.is_empty() {
        let list = cx.factory.new_node_list(scope.variables);
        let var_decl_list =
            cx.factory
                .new_variable_declaration_list(cx.nodes, Some(list), ast::NodeFlags::LET);
        let var_statement = cx
            .factory
            .new_variable_statement(cx.nodes, None, Some(var_decl_list));
        {
            let mut s = shared.borrow_mut();
            s.emit_nodes.get(var_statement).emit_flags = EmitFlags::CUSTOM_PROLOGUE;
        }
        statements.push(var_statement);
    }
    statements
}

/// `mergeEnvironment` on `Shared`.
fn merge_environment_shared(
    shared: &Shared,
    nodes: &mut Vec<Node>,
    statements: &[NodeId],
    declarations: &[NodeId],
) -> (Vec<NodeId>, bool) {
    if declarations.is_empty() {
        return (statements.to_vec(), false);
    }
    let mut changed = false;

    let left_standard_prologue_end = find_span_end(
        statements,
        |s| ast::is_prologue_directive(&nodes[*s], nodes),
        0,
    );
    let left_hoisted_functions_end = find_span_end(
        statements,
        |s| is_hoisted_function(shared, nodes, *s),
        left_standard_prologue_end,
    );
    let left_hoisted_variables_end = find_span_end(
        statements,
        |s| is_hoisted_variable_statement(shared, nodes, *s),
        left_hoisted_functions_end,
    );

    let right_standard_prologue_end = find_span_end(
        declarations,
        |s| ast::is_prologue_directive(&nodes[*s], nodes),
        0,
    );
    let right_hoisted_functions_end = find_span_end(
        declarations,
        |s| is_hoisted_function(shared, nodes, *s),
        right_standard_prologue_end,
    );
    let right_hoisted_variables_end = find_span_end(
        declarations,
        |s| is_hoisted_variable_statement(shared, nodes, *s),
        right_hoisted_functions_end,
    );
    let right_custom_prologue_end = find_span_end(
        declarations,
        |s| emit_flags(shared, *s).0 & EmitFlags::CUSTOM_PROLOGUE.0 != 0,
        right_hoisted_variables_end,
    );
    if right_custom_prologue_end != declarations.len() {
        panic!("Expected declarations to be valid standard or custom prologues");
    }

    let mut left: Vec<NodeId> = statements.to_vec();

    if right_custom_prologue_end > right_hoisted_variables_end {
        left = splice_vec(
            &left,
            left_hoisted_variables_end as i32,
            0,
            &declarations[right_hoisted_variables_end..right_custom_prologue_end],
        );
        changed = true;
    }

    if right_hoisted_variables_end > right_hoisted_functions_end {
        left = splice_vec(
            &left,
            left_hoisted_functions_end as i32,
            0,
            &declarations[right_hoisted_functions_end..right_hoisted_variables_end],
        );
        changed = true;
    }

    if right_hoisted_functions_end > right_standard_prologue_end {
        left = splice_vec(
            &left,
            left_standard_prologue_end as i32,
            0,
            &declarations[right_standard_prologue_end..right_hoisted_functions_end],
        );
        changed = true;
    }

    if right_standard_prologue_end > 0 {
        if left_standard_prologue_end == 0 {
            left = splice_vec(&left, 0, 0, &declarations[..right_standard_prologue_end]);
            changed = true;
        } else {
            let mut left_prologues: Set<String> = Set::new();
            for &statement in statements.iter().take(left_standard_prologue_end) {
                if let Some(expr) = nodes[statement].expression() {
                    left_prologues.add(nodes[expr].text(nodes).into_owned());
                }
            }
            for &right_prologue in declarations[..right_standard_prologue_end].iter().rev() {
                let text = nodes[right_prologue]
                    .expression()
                    .map(|e| nodes[e].text(nodes).into_owned())
                    .unwrap_or_default();
                if !left_prologues.has(&text) {
                    left.insert(0, right_prologue);
                    changed = true;
                }
            }
        }
    }

    (left, changed)
}

/// `(c *EmitContext) VisitParameters`
fn visit_parameters(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    nodes: Option<NodeList>,
    visitor: &NodeVisitor<'_>,
) -> Option<NodeList> {
    shared
        .borrow_mut()
        .var_scope_stack
        .push(VarScope::default());
    shared
        .borrow_mut()
        .let_scope_stack
        .push(VarScope::default());
    let old_flags = {
        let mut s = shared.borrow_mut();
        let scope = s.var_scope_stack.last_mut().unwrap();
        let old_flags = scope.flags;
        scope.flags |= ENVIRONMENT_FLAGS_IN_PARAMETERS;
        old_flags
    };
    let nodes = visitor.visit_nodes(cx, nodes);

    // As of ES2015, any runtime execution of that occurs in for a parameter (such as evaluating an
    // initializer or a binding pattern), occurs in its own lexical scope. As a result, any expression
    // that we might transform that introduces a temporary variable would fail as the temporary variable
    // exists in a different lexical scope. To address this, we move any binding patterns and initializers
    // in a parameter list to the body if we detect a variable being hoisted while visiting a parameter list
    // when the emit target is greater than ES2015. (Which is now all targets.)
    let hoisted = {
        let s = shared.borrow();
        s.var_scope_stack.last().unwrap().flags & ENVIRONMENT_FLAGS_VARIABLES_HOISTED_IN_PARAMETERS
            != 0
    };
    let nodes = if hoisted {
        add_default_value_assignments_if_needed(shared, cx, nodes)
    } else {
        nodes
    };
    shared
        .borrow_mut()
        .var_scope_stack
        .last_mut()
        .unwrap()
        .flags = old_flags;
    // !!! c.suspendVariableEnvironment()
    nodes
}

/// `(c *EmitContext) addDefaultValueAssignmentsIfNeeded`
fn add_default_value_assignments_if_needed(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    node_list: Option<NodeList>,
) -> Option<NodeList> {
    let node_list = node_list?;
    let mut result: Option<Vec<NodeId>> = None;
    for (i, &parameter) in node_list.nodes.iter().enumerate() {
        let updated = add_default_value_assignment_if_needed(shared, cx, parameter);
        if updated != parameter {
            if result.is_none() {
                result = Some(node_list.nodes.to_vec());
            }
            result.as_mut().unwrap()[i] = updated;
        }
    }
    if let Some(result) = result {
        let mut res = cx.factory.new_node_list(result);
        res.loc = node_list.loc;
        return Some(res);
    }
    Some(node_list)
}

/// `(c *EmitContext) addDefaultValueAssignmentIfNeeded`
fn add_default_value_assignment_if_needed(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    parameter: NodeId,
) -> NodeId {
    // A rest parameter cannot have a binding pattern or an initializer,
    // so let's just ignore it.
    let (dot_dot_dot_token, name, initializer, ty) = {
        let d = cx.nodes[parameter].as_parameter_declaration();
        (d.dot_dot_dot_token, d.name, d.initializer, d.type_)
    };
    if dot_dot_dot_token.is_some() {
        return parameter;
    } else if name.is_some_and(|n| ast::is_binding_pattern(&cx.nodes[n])) {
        return add_default_value_assignment_for_binding_pattern(shared, cx, parameter);
    } else if initializer.is_some() {
        return add_default_value_assignment_for_initializer(
            shared,
            cx,
            parameter,
            name.unwrap(),
            initializer.unwrap(),
        );
    }
    parameter
}

/// `(c *EmitContext) addDefaultValueAssignmentForBindingPattern`
fn add_default_value_assignment_for_binding_pattern(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    parameter: NodeId,
) -> NodeId {
    let (name, initializer, ty, modifiers, dot_dot_dot_token, question_token) = {
        let d = cx.nodes[parameter].as_parameter_declaration();
        (
            d.name,
            d.initializer,
            d.type_,
            d.modifiers_base.modifiers.clone(),
            d.dot_dot_dot_token,
            d.question_token,
        )
    };
    let init_node = if let Some(initializer) = initializer {
        let left = new_generated_name_for_node(shared, cx, parameter);
        let right = crate::factory::new_void_zero_expression(&mut cx.factory, cx.nodes);
        let condition = crate::factory::new_binary_operator_expression(
            &mut cx.factory,
            cx.nodes,
            Kind::EqualsEqualsEqualsToken,
            left,
            right,
        );
        let question_token = cx.factory.new_token(cx.nodes, Kind::QuestionToken);
        let colon_token = cx.factory.new_token(cx.nodes, Kind::ColonToken);
        let generated_name = new_generated_name_for_node(shared, cx, parameter);
        cx.factory.new_conditional_expression(
            cx.nodes,
            Some(condition),
            Some(question_token),
            Some(initializer),
            Some(colon_token),
            Some(generated_name),
        )
    } else {
        new_generated_name_for_node(shared, cx, parameter)
    };
    let var_decl = cx
        .factory
        .new_variable_declaration(cx.nodes, name, None, ty, Some(init_node));
    let decl_list = cx.factory.new_node_list([var_decl]);
    let var_decl_list =
        cx.factory
            .new_variable_declaration_list(cx.nodes, Some(decl_list), ast::NodeFlags::NONE);
    let var_statement = cx
        .factory
        .new_variable_statement(cx.nodes, None, Some(var_decl_list));
    add_initialization_statement_shared(shared, var_statement);
    let generated_name = new_generated_name_for_node(shared, cx, parameter);
    cx.factory
        .update_parameter_declaration(
            cx.nodes,
            parameter,
            modifiers,
            dot_dot_dot_token,
            Some(generated_name),
            question_token,
            ty,
            None,
        )
        .unwrap_or(parameter)
}

/// `(c *EmitContext) addDefaultValueAssignmentForInitializer`
fn add_default_value_assignment_for_initializer(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    parameter: NodeId,
    name: NodeId,
    initializer: NodeId,
) -> NodeId {
    let (param_name, ty, modifiers, dot_dot_dot_token, question_token) = {
        let d = cx.nodes[parameter].as_parameter_declaration();
        (
            d.name,
            d.type_,
            d.modifiers_base.modifiers.clone(),
            d.dot_dot_dot_token,
            d.question_token,
        )
    };
    {
        let mut s = shared.borrow_mut();
        s.emit_nodes.get(initializer).emit_flags |=
            EmitFlags::NO_SOURCE_MAP | EmitFlags::NO_COMMENTS;
    }
    let name_clone = cx.factory.clone_node(cx.nodes, name);
    {
        let mut s = shared.borrow_mut();
        s.emit_nodes.get(name_clone).emit_flags |= EmitFlags::NO_SOURCE_MAP;
    }
    let equals_token = cx.factory.new_token(cx.nodes, Kind::EqualsToken);
    let init_assignment = cx.factory.new_binary_expression(
        cx.nodes,
        None,
        Some(name_clone),
        None,
        Some(equals_token),
        Some(initializer),
    );
    cx.nodes[init_assignment].loc = cx.nodes[parameter].loc;
    {
        let mut s = shared.borrow_mut();
        s.emit_nodes.get(init_assignment).emit_flags |= EmitFlags::NO_COMMENTS;
    }
    let expr_statement = cx
        .factory
        .new_expression_statement(cx.nodes, Some(init_assignment));
    let init_block = cx.factory.new_block(
        cx.nodes,
        Some(cx.factory.new_node_list([expr_statement])),
        false,
    );
    cx.nodes[init_block].loc = cx.nodes[parameter].loc;
    {
        let mut s = shared.borrow_mut();
        s.emit_nodes.get(init_block).emit_flags |= EmitFlags::SINGLE_LINE
            | EmitFlags::NO_TRAILING_SOURCE_MAP
            | EmitFlags::NO_TOKEN_SOURCE_MAPS
            | EmitFlags::NO_COMMENTS;
    }
    let name_clone2 = cx.factory.clone_node(cx.nodes, name);
    let type_check =
        crate::factory::new_type_check(&mut cx.factory, cx.nodes, name_clone2, "undefined");
    let if_statement =
        cx.factory
            .new_if_statement(cx.nodes, Some(type_check), Some(init_block), None);
    add_initialization_statement_shared(shared, if_statement);
    cx.factory
        .update_parameter_declaration(
            cx.nodes,
            parameter,
            modifiers,
            dot_dot_dot_token,
            param_name,
            question_token,
            ty,
            None,
        )
        .unwrap_or(parameter)
}

/// `newGeneratedNameForNode` via the shared tables (mirrors
/// `f.NewGeneratedNameForNode` on the printer factory).
fn new_generated_name_for_node(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
) -> NodeId {
    // PORT: equivalent to `f.NewGeneratedNameForNodeEx(node, {})` — when
    // prefix/suffix are empty, `Optimistic` is not added.
    crate::factory::new_generated_identifier(
        shared,
        cx.factory,
        cx.nodes,
        crate::emit_flags::GeneratedIdentifierFlags::NODE,
        "",
        Some(node),
        &AutoGenerateOptions::default(),
    )
}

/// `(c *EmitContext) AddInitializationStatement`
fn add_initialization_statement_shared(shared: &Shared, node: NodeId) {
    {
        let mut s = shared.borrow_mut();
        s.emit_nodes.get(node).emit_flags |= EmitFlags::CUSTOM_PROLOGUE;
    }
    let mut s = shared.borrow_mut();
    match s.var_scope_stack.last_mut() {
        Some(scope) => scope.initialization_statements.push(node),
        None => {
            panic!("Tried to add an initialization statement without a surrounding variable scope")
        }
    }
}

/// `(c *EmitContext) VisitFunctionBody`
fn visit_function_body(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    visitor: &NodeVisitor<'_>,
) -> Option<NodeId> {
    // !!! c.resumeVariableEnvironment()
    // PORT: the `visit_function_body` hook only runs for non-nil bodies
    // (`hooked()` short-circuits `None`), so `node` is a `NodeId` here.
    let updated = visitor.visit_node(cx, Some(node));
    let declarations = end_variable_environment_shared(shared, cx);
    if declarations.is_empty() {
        return updated;
    }

    let Some(updated) = updated else {
        return Some(cx.factory.new_block(
            cx.nodes,
            Some(cx.factory.new_node_list(declarations)),
            true, /* multiLine */
        ));
    };

    if !ast::is_block(&cx.nodes[updated]) {
        {
            let mut s = shared.borrow_mut();
            s.emit_nodes.get(updated).emit_flags |= EmitFlags::NO_COMMENTS;
        }
        let block = convert_to_function_block_shared(shared, cx, updated, false);
        let block_statements = cx.nodes[block].statement_list().cloned();
        let merged = merge_environment_list_shared(shared, cx, block_statements, &declarations);
        let multi_line = cx.nodes[block].as_block().multi_line;
        return cx
            .factory
            .update_block(cx.nodes, block, Some(merged), multi_line)
            .or(Some(block));
    }

    let updated_statements = cx.nodes[updated].statement_list().cloned();
    let merged = merge_environment_list_shared(shared, cx, updated_statements, &declarations);
    let multi_line = cx.nodes[updated].as_block().multi_line;
    cx.factory
        .update_block(cx.nodes, updated, Some(merged), multi_line)
        .or(Some(updated))
}

/// `mergeEnvironmentList` on `Shared`.
fn merge_environment_list_shared(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    statements: Option<NodeList>,
    declarations: &[NodeId],
) -> NodeList {
    let statements_nodes: &[NodeId] = statements.as_ref().map_or(&[], |l| &l.nodes);
    let (result, changed) =
        merge_environment_shared(shared, cx.nodes, statements_nodes, declarations);
    if changed {
        let mut list = cx.factory.new_node_list(result);
        list.loc = statements.as_ref().map_or(TextRange::default(), |l| l.loc);
        return list;
    }
    statements.unwrap_or_default()
}

/// `(c *EmitContext) ConvertToFunctionBlock` on `Shared`.
fn convert_to_function_block_shared(
    _shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    multi_line: bool,
) -> NodeId {
    if ast::is_block(&cx.nodes[node]) {
        return node;
    }
    let return_statement = cx.factory.new_return_statement(cx.nodes, Some(node));
    cx.nodes[return_statement].loc = cx.nodes[node].loc;
    let mut statements = cx.factory.new_node_list([return_statement]);
    statements.loc = cx.nodes[node].loc;
    let block = cx.factory.new_block(cx.nodes, Some(statements), multi_line);
    cx.nodes[block].loc = cx.nodes[node].loc;
    block
}

/// `(c *EmitContext) VisitIterationBody`
fn visit_iteration_body(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    body: NodeId,
    visitor: &NodeVisitor<'_>,
) -> Option<NodeId> {
    // PORT: the `visit_iteration_body` hook only runs for non-nil bodies.
    let body = body;

    shared
        .borrow_mut()
        .let_scope_stack
        .push(VarScope::default());
    let updated = visit_embedded_statement(shared, cx, body, visitor);
    let Some(updated) = updated else {
        panic!("Expected visitor to return a statement.")
    };

    let mut statements = end_lexical_environment_shared(shared, cx);
    if !statements.is_empty() {
        if ast::is_block(&cx.nodes[updated]) {
            let multi_line = cx.nodes[updated].as_block().multi_line;
            let block_loc = cx.nodes[updated]
                .statement_list()
                .map(|s| s.loc)
                .unwrap_or_default();
            if let Some(existing) = cx.nodes[updated].statements() {
                statements.extend(existing.iter().copied());
            }
            let mut statements_list = cx.factory.new_node_list(statements);
            statements_list.loc = block_loc;
            return cx
                .factory
                .update_block(cx.nodes, updated, Some(statements_list), multi_line)
                .or(Some(updated));
        }
        statements.push(updated);
        return Some(cx.factory.new_block(
            cx.nodes,
            Some(cx.factory.new_node_list(statements)),
            true, /* multiLine */
        ));
    }

    Some(updated)
}

/// `(c *EmitContext) VisitEmbeddedStatement`
fn visit_embedded_statement(
    shared: &Shared,
    cx: &mut VisitorCx<'_, '_>,
    node: NodeId,
    visitor: &NodeVisitor<'_>,
) -> Option<NodeId> {
    // PORT: the `visit_embedded_statement` hook only runs for non-nil nodes.
    let node = node;
    let embedded_statement = visitor.visit_embedded_statement(cx, Some(node));
    if embedded_statement.is_none()
        || embedded_statement.is_some_and(|s| ast::is_not_emitted_statement(&cx.nodes[s]))
    {
        let empty_statement = cx.factory.new_empty_statement(cx.nodes);
        cx.nodes[empty_statement].loc = cx.nodes[node].loc;
        set_original_shared(shared, empty_statement, node, false);
        // AssignCommentRange
        let range = {
            let mut s = shared.borrow_mut();
            if let Some(emit_node) = s.emit_nodes.try_get(&node)
                && emit_node.flags & HAS_COMMENT_RANGE != 0
            {
                emit_node.comment_range
            } else {
                cx.nodes[node].loc
            }
        };
        {
            let mut s = shared.borrow_mut();
            let emit_node = s.emit_nodes.get(empty_statement);
            emit_node.comment_range = range;
            emit_node.flags |= HAS_COMMENT_RANGE;
        }
        return Some(empty_statement);
    }
    embedded_statement
}
