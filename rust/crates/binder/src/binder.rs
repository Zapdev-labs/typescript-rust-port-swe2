// Ported from tsc/internal/binder/binder.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The binder: declares symbols into locals/members/exports tables, builds the
// control-flow graph (`FlowNode`/`FlowList` arenas) and marks module
// indicators on the `SourceFile`.
//
// Pointer model (see SPEC §5.1):
//   `*ast.Node`        -> `NodeId` (`Option<NodeId>` where Go may pass nil)
//   `*ast.Symbol`      -> `SymbolId` (`Option<SymbolId>` where Go may pass nil)
//   `*ast.FlowNode` / `*ast.FlowLabel` -> `FlowNodeId` (`Option<FlowNodeId>` for nil)
//   `*ast.FlowList`    -> `FlowListId` (`Option<FlowListId>` for nil)
//   `ast.SymbolTable`  -> `SymbolTable` (`OrderedMap<String, SymbolId>`)
//
// Go mutates nodes/symbols/flow nodes through shared heap pointers. Here the
// binder holds exclusive borrows of the three arenas (`nodes` comes from the
// caller; `symbols`/`flow_nodes`/`flow_lists` are built per bind and stored in
// the file's `SourceFileData` under `BIND_RESULT_KEY`). Because a Go
// `SymbolTable` map argument aliases its owner, table destinations are passed
// as `SymbolTableDest` handles that are re-resolved against the arenas at each
// use — holding a `&mut SymbolTable` into one arena across calls would alias
// the other arenas.
//
// PORT: Go's `binderPool`/`getBinder`/`putBinder` `sync.Pool` recycling is an
// allocation optimization; `Binder::new` keeps identical semantics.

use std::sync::Arc;
use std::sync::LazyLock;
use std::sync::atomic::Ordering;

use tsc_ast::ast::{ModifierList, Node, NodeList, PatternAmbientModule};
use tsc_ast::ast_generated::*;
use tsc_ast::diagnostic::{DiagnosticRef, lock_diagnostic, new_diagnostic};
use tsc_ast::flow::{FlowList, FlowNode, new_flow_reduce_label_data, new_flow_switch_clause_data};
use tsc_ast::ids::{FlowListId, FlowNodeId, NodeId, SymbolId};
use tsc_ast::kind_generated::Kind;
use tsc_ast::modifierflags::ModifierFlags;
use tsc_ast::nodeflags::NodeFlags;
use tsc_ast::sourcefiledata::{SourceFileDataKey, new_source_file_data_key};
use tsc_ast::symbol::{
    INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION, INTERNAL_SYMBOL_NAME_CALL,
    INTERNAL_SYMBOL_NAME_CLASS, INTERNAL_SYMBOL_NAME_COMPUTED, INTERNAL_SYMBOL_NAME_CONSTRUCTOR,
    INTERNAL_SYMBOL_NAME_DEFAULT, INTERNAL_SYMBOL_NAME_EXPORT_EQUALS,
    INTERNAL_SYMBOL_NAME_EXPORT_STAR, INTERNAL_SYMBOL_NAME_FUNCTION, INTERNAL_SYMBOL_NAME_GLOBAL,
    INTERNAL_SYMBOL_NAME_INDEX, INTERNAL_SYMBOL_NAME_JSX_ATTRIBUTES, INTERNAL_SYMBOL_NAME_MISSING,
    INTERNAL_SYMBOL_NAME_NEW, INTERNAL_SYMBOL_NAME_OBJECT, INTERNAL_SYMBOL_NAME_PREFIX,
    INTERNAL_SYMBOL_NAME_TYPE, Symbol, symbol_name,
};
use tsc_ast::symbolflags::SymbolFlags;
use tsc_ast::utilities::*;
use tsc_collections::Set;
use tsc_core::pattern::try_parse_pattern;
use tsc_diagnostics as diagnostics;
use tsc_scanner::scanner::{get_identifier_token, get_range_of_token_at_position, token_to_string};
use tsc_scanner::utilities::{
    declaration_name_to_string, get_source_text_of_node_from_source_file,
};

// `type ContainerFlags int32` — a plain `u32` bitset; the flag values only
// appear in binder-internal control flow, never in output.
pub type ContainerFlags = u32;

/// The current node is not a container, and no container manipulation should happen before
/// recursing into it.
pub const CONTAINER_FLAGS_NONE: ContainerFlags = 0;
// The current node is a container.  It should be set as the current container (and block-
// container) before recursing into it.  The current node does not have locals.  Examples:
// Classes, ObjectLiterals, TypeLiterals, Interfaces...
pub const CONTAINER_FLAGS_IS_CONTAINER: ContainerFlags = 1 << 0;
// The current node is a block-scoped-container.  It should be set as the current block-
// container before recursing into it.  Examples:
// Blocks (when not parented by functions), Catch clauses, For/For-in/For-of statements...
pub const CONTAINER_FLAGS_IS_BLOCK_SCOPED_CONTAINER: ContainerFlags = 1 << 1;
/// The current node is the container of a control flow path. The current control flow should
/// be saved and restored, and a new control flow initialized within the container.
pub const CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER: ContainerFlags = 1 << 2;
pub const CONTAINER_FLAGS_IS_FUNCTION_LIKE: ContainerFlags = 1 << 3;
pub const CONTAINER_FLAGS_IS_FUNCTION_EXPRESSION: ContainerFlags = 1 << 4;
pub const CONTAINER_FLAGS_HAS_LOCALS: ContainerFlags = 1 << 5;
pub const CONTAINER_FLAGS_IS_INTERFACE: ContainerFlags = 1 << 6;
pub const CONTAINER_FLAGS_IS_OBJECT_LITERAL_OR_CLASS_EXPRESSION_METHOD_OR_ACCESSOR: ContainerFlags =
    1 << 7;
pub const CONTAINER_FLAGS_IS_THIS_CONTAINER: ContainerFlags = 1 << 8;
pub const CONTAINER_FLAGS_PROPAGATES_THIS_KEYWORD: ContainerFlags = 1 << 9;

/// `type ExpandoAssignmentInfo struct`
struct ExpandoAssignmentInfo {
    node: NodeId,
    container: NodeId,
    block_scope_container: NodeId,
}

/// `type ActiveLabel struct` — Go keeps the active labels on a linked list;
/// here it is a `Vec` used as a stack (top of stack = head of Go's list).
struct ActiveLabel {
    break_target: Option<FlowNodeId>,
    continue_target: Option<FlowNodeId>,
    name: String,
    referenced: bool,
}

/// `type SymbolTableDest` — stands in for Go's `symbolTable SymbolTable`
/// map argument. A Go map is reference-like: `declareSymbol` receives the
/// table itself. Since the tables live inside the `nodes`/`symbols` arenas
/// (or on the `SourceFile`), destinations are resolved per access.
#[derive(Clone, Copy)]
enum SymbolTableDest {
    /// `ast.GetLocals(container)` — `container.locals_container_base.locals`.
    Locals(NodeId),
    /// `ast.GetExports(symbol)`.
    Exports(SymbolId),
    /// `ast.GetMembers(symbol)`.
    Members(SymbolId),
    /// `ast.GetSymbolTable(&file.GlobalExports)`.
    GlobalExports,
}

/// Arenas produced by a bind. Stored on the `SourceFile`'s `SourceFileData`
/// under `BIND_RESULT_KEY` (SPEC §5.10 — `bind_results`; the `SourceFileData`
/// key registry is the extension point for data owned outside `tsc-ast`).
///
/// PORT: symbols are NOT stored here — Go's `b.symbolArena` is the program's
/// shared `Vec<Symbol>` (SPEC §5.2), borrowed by the binder for the duration
/// of the bind so `SymbolId`s are globally unique.
#[derive(Clone)]
pub struct BindResult {
    /// `b.flowNodeArena` — the control-flow graph, indexed by `FlowNodeId`.
    pub flow_nodes: Vec<FlowNode>,
    /// `b.flowListArena` — antecedent list cells, indexed by `FlowListId`.
    pub flow_lists: Vec<FlowList>,
}

static BIND_RESULT_KEY: LazyLock<SourceFileDataKey<BindResult>> =
    LazyLock::new(new_source_file_data_key);

/// The bound arenas for a file, if `bind_source_file` has run.
pub fn bind_result(nodes: &[Node], file: NodeId) -> Option<&BindResult> {
    nodes[file].as_source_file().data.get(&BIND_RESULT_KEY)
}

/// Mutable `bind_result` — the checker appends synthetic `FlowNode`s
/// (`&ast.FlowNode{}` literals in Go become `FlowNodeId`s here) e.g. in
/// `checkIfExpressionRefinesParameter`.
///
/// PORT(COW): when an arena snapshot shares the `Rc` cell, `get_mut` cannot
/// hand out `&mut`. Clone the `BindResult` into a fresh cell instead —
/// pre-existing snapshots keep their point-in-time view (they'd see the old
/// `flow_nodes` length under in-place mutation anyway), and post-clone
/// reads observe the appended node.
pub fn bind_result_mut(nodes: &mut [Node], file: NodeId) -> Option<&mut BindResult> {
    let data = &mut nodes[file].as_source_file_mut().data;
    if data.get_mut(&BIND_RESULT_KEY).is_none() {
        let cloned = data.get(&BIND_RESULT_KEY)?.clone();
        data.insert(&BIND_RESULT_KEY, cloned);
    }
    data.get_mut(&BIND_RESULT_KEY)
}

/// `type Binder struct`
pub struct Binder<'a> {
    nodes: &'a mut Vec<Node>,
    file: NodeId,
    unreachable_flow: FlowNodeId,

    container: Option<NodeId>,
    this_container: Option<NodeId>,
    block_scope_container: Option<NodeId>,
    last_container: Option<NodeId>,
    current_flow: Option<FlowNodeId>,
    current_break_target: Option<FlowNodeId>,
    current_continue_target: Option<FlowNodeId>,
    current_return_target: Option<FlowNodeId>,
    current_true_target: Option<FlowNodeId>,
    current_false_target: Option<FlowNodeId>,
    current_exception_target: Option<FlowNodeId>,
    pre_switch_case_flow: Option<FlowNodeId>,
    /// Go's `activeLabelList *ActiveLabel` — a linked list; here a stack whose
    /// last element is the list head.
    active_labels: Vec<ActiveLabel>,
    emit_flags: NodeFlags,
    seen_this_keyword: bool,
    has_explicit_return: bool,
    has_flow_effects: bool,
    in_assignment_pattern: bool,
    seen_parse_error: bool,
    symbol_count: i32,
    not_const_enum_only_modules: Set<SymbolId>,
    /// `b.symbolArena` — in the port this is a mutable borrow of the
    /// program's global symbol arena (SPEC §5.2): `SymbolId` is an index into
    /// a single `Vec<Symbol>` shared by every bound file and every `Checker`,
    /// standing in for Go's pointer-identity `*ast.Symbol` heap.
    symbols: &'a mut Vec<Symbol>,
    /// `b.flowNodeArena`
    flow_nodes: Vec<FlowNode>,
    /// `b.flowListArena`
    flow_lists: Vec<FlowList>,
    /// `b.expandoAssignments`
    expando_assignments: Vec<ExpandoAssignmentInfo>,
    /// Scratch buffer for `bind_each_child` — reused across calls to avoid a
    /// `Vec` allocation per node (Go's visitor callback needs no allocation).
    child_scratch: Vec<NodeId>,
}

/// `func BindSourceFile(file *ast.SourceFile)`
///
/// `symbols` is the program-global symbol arena (SPEC §5.2); the binder
/// appends to it so `SymbolId`s are valid program-wide, mirroring Go where
/// binder-allocated `*ast.Symbol`s live on the shared heap.
pub fn bind_source_file(nodes: &mut Vec<Node>, file: NodeId, symbols: &mut Vec<Symbol>) {
    // This is constructed this way to make the compiler "out-line" the function,
    // avoiding most work in the common case where the file has already been bound.
    if !nodes[file]
        .as_source_file()
        .is_bound
        .load(Ordering::Acquire)
    {
        bind_source_file_worker(nodes, file, symbols);
    }
}

fn bind_source_file_worker(nodes: &mut Vec<Node>, file: NodeId, symbols: &mut Vec<Symbol>) {
    tsc_ast::ast::bind_once(nodes, file, |nodes| {
        let mut b = Binder::new(nodes, file, symbols);
        b.unreachable_flow = b.new_flow_node(tsc_ast::FlowFlags::UNREACHABLE);
        b.bind(Some(file));
        b.bind_deferred_expando_assignments();
        let symbol_count = b.symbol_count;
        let result = BindResult {
            flow_nodes: b.flow_nodes,
            flow_lists: b.flow_lists,
        };
        let file_data = nodes[file].as_source_file_mut();
        file_data.symbol_count = symbol_count;
        file_data.data.insert(&BIND_RESULT_KEY, result);
    });
}

impl<'a> Binder<'a> {
    fn new(nodes: &'a mut Vec<Node>, file: NodeId, symbols: &'a mut Vec<Symbol>) -> Binder<'a> {
        Binder {
            nodes,
            file,
            unreachable_flow: FlowNodeId::NONE,
            container: None,
            this_container: None,
            block_scope_container: None,
            last_container: None,
            current_flow: None,
            current_break_target: None,
            current_continue_target: None,
            current_return_target: None,
            current_true_target: None,
            current_false_target: None,
            current_exception_target: None,
            pre_switch_case_flow: None,
            active_labels: Vec::new(),
            emit_flags: NodeFlags::NONE,
            seen_this_keyword: false,
            has_explicit_return: false,
            has_flow_effects: false,
            in_assignment_pattern: false,
            seen_parse_error: false,
            symbol_count: 0,
            not_const_enum_only_modules: Set::new(),
            symbols,
            flow_nodes: Vec::new(),
            flow_lists: Vec::new(),
            expando_assignments: Vec::new(),
            child_scratch: Vec::new(),
        }
    }

    /// `file` as a `&SourceFile` — shorthand for the pervasive `b.file` reads.
    fn file_data(&self) -> &SourceFile {
        self.nodes[self.file].as_source_file()
    }

    fn new_symbol(&mut self, flags: SymbolFlags, name: String) -> SymbolId {
        self.symbol_count += 1;
        self.symbols.push(Symbol {
            flags,
            name: name.into(),
            ..Default::default()
        });
        SymbolId((self.symbols.len() - 1) as u32)
    }

    /// `SymbolTableDest` resolution — `symbolTable[name]` read.
    fn table_get(&self, dest: SymbolTableDest, name: &str) -> Option<SymbolId> {
        let table = match dest {
            SymbolTableDest::Locals(n) => {
                &self.nodes[n]
                    .locals_container_data()
                    .expect("GetLocals on node without LocalsContainerData")
                    .locals
            }
            SymbolTableDest::Exports(s) => &self.symbols[s.index()].exports,
            SymbolTableDest::Members(s) => &self.symbols[s.index()].members,
            SymbolTableDest::GlobalExports => &self.file_data().global_exports,
        };
        table.get(name).copied()
    }

    /// `SymbolTableDest` resolution — `symbolTable[name] = symbol` write.
    fn table_set(&mut self, dest: SymbolTableDest, name: impl Into<Arc<str>>, symbol: SymbolId) {
        let table = match dest {
            SymbolTableDest::Locals(n) => {
                &mut self.nodes[n]
                    .data
                    .locals_container_data_mut()
                    .expect("GetLocals on node without LocalsContainerData")
                    .locals
            }
            SymbolTableDest::Exports(s) => &mut self.symbols[s.index()].exports,
            SymbolTableDest::Members(s) => &mut self.symbols[s.index()].members,
            SymbolTableDest::GlobalExports => &mut self.file_data_mut().global_exports,
        };
        table.set(name.into(), symbol);
    }

    fn file_data_mut(&mut self) -> &mut SourceFile {
        self.nodes[self.file].as_source_file_mut()
    }

    /**
     * Declares a Symbol for the node and adds it to symbols. Reports errors for conflicting identifier names.
     * @param symbolTable - The symbol table which node will be added to.
     * @param parent - node's parent declaration.
     * @param node - The declaration to be added to the symbol table
     * @param includes - The SymbolFlags that node has in addition to its declaration type (eg: export, ambient, etc.)
     * @param excludes - The flags which node cannot be declared alongside in a symbol table. Used to report forbidden declarations.
     */
    fn declare_symbol(
        &mut self,
        symbol_table: SymbolTableDest,
        parent: Option<SymbolId>,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
    ) -> SymbolId {
        self.declare_symbol_ex(
            symbol_table,
            parent,
            node,
            includes,
            excludes,
            false, /*isReplaceableByMethod*/
            false, /*isComputedName*/
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn declare_symbol_ex(
        &mut self,
        symbol_table: SymbolTableDest,
        parent: Option<SymbolId>,
        node: NodeId,
        includes: SymbolFlags,
        excludes: SymbolFlags,
        is_replaceable_by_method: bool,
        is_computed_name: bool,
    ) -> SymbolId {
        tsc_debug::assert_!(
            is_computed_name || !has_dynamic_name(node, self.nodes),
            "hasDynamicName without isComputedName"
        );
        let is_default_export = has_syntactic_modifier(&self.nodes[node], ModifierFlags::DEFAULT)
            || is_export_specifier(&self.nodes[node])
                && module_export_name_is_default(
                    &self.nodes[self.nodes[node].as_export_specifier().name.unwrap()],
                    self.nodes,
                );
        // The exported symbol for an export default function/class node is always named "default"
        let name = if is_computed_name {
            INTERNAL_SYMBOL_NAME_COMPUTED.to_string()
        } else if is_default_export && parent.is_some() {
            INTERNAL_SYMBOL_NAME_DEFAULT.to_string()
        } else {
            self.get_declaration_name(node)
        };
        let symbol: SymbolId;
        if name == INTERNAL_SYMBOL_NAME_MISSING {
            symbol = self.new_symbol(SymbolFlags::NONE, INTERNAL_SYMBOL_NAME_MISSING.to_string());
        } else {
            // Check and see if the symbol table already has a symbol with this name.  If not,
            // create a new symbol with this name and add it to the table.  Note that we don't
            // give the new symbol any flags *yet*.  This ensures that it will not conflict
            // with the 'excludes' flags we pass in.
            //
            // If we do get an existing symbol, see if it conflicts with the new symbol we're
            // creating.  For example, a 'var' symbol and a 'class' symbol will conflict within
            // the same symbol table.  If we have a conflict, report the issue on each
            // declaration we have for this symbol, and then create a new symbol for this
            // declaration.
            //
            // Note that when properties declared in Javascript constructors
            // (marked by isReplaceableByMethod) conflict with another symbol, the property loses.
            // Always. This allows the common Javascript pattern of overwriting a prototype method
            // with an bound instance method of the same type: `this.method = this.method.bind(this)`
            //
            // If we created a new symbol, either because we didn't have a symbol with this name
            // in the symbol table, or we conflicted with an existing symbol, then just add this
            // node as the sole declaration of the new symbol.
            //
            // Otherwise, we'll be merging into a compatible existing symbol (for example when
            // you have multiple 'vars' with the same name in the same container).  In this case
            // just add this node into the declarations list of the symbol.
            match self.table_get(symbol_table, &name) {
                None => {
                    symbol = self.new_symbol(SymbolFlags::NONE, name.clone());
                    self.table_set(symbol_table, name, symbol);
                    if is_replaceable_by_method {
                        self.symbols[symbol.index()].flags |= SymbolFlags::REPLACEABLE_BY_METHOD;
                    }
                }
                Some(s) => {
                    if is_replaceable_by_method
                        && !self.symbols[s.index()]
                            .flags
                            .intersects(SymbolFlags::REPLACEABLE_BY_METHOD)
                    {
                        // A symbol already exists, so don't add this as a declaration.
                        return s;
                    }
                    if self.symbols[s.index()].flags.intersects(excludes) {
                        if self.symbols[s.index()]
                            .flags
                            .intersects(SymbolFlags::REPLACEABLE_BY_METHOD)
                        {
                            // Javascript constructor-declared symbols can be discarded in favor of
                            // prototype symbols like methods.
                            symbol = self.new_symbol(SymbolFlags::NONE, name.clone());
                            self.table_set(symbol_table, name, symbol);
                        } else if !(includes.intersects(SymbolFlags::VARIABLE)
                            && self.symbols[s.index()]
                                .flags
                                .intersects(SymbolFlags::ASSIGNMENT)
                            || includes.intersects(SymbolFlags::ASSIGNMENT)
                                && self.symbols[s.index()]
                                    .flags
                                    .intersects(SymbolFlags::VARIABLE))
                        {
                            // Assignment declarations are allowed to merge with variables, no matter what other flags they have.
                            // Report errors every position with duplicate declaration
                            // Report errors on previous encountered declarations
                            let mut message: &'static diagnostics::Message = if self.symbols
                                [s.index()]
                            .flags
                            .intersects(SymbolFlags::BLOCK_SCOPED_VARIABLE)
                            {
                                &diagnostics::Cannot_redeclare_block_scoped_variable_0
                            } else {
                                &diagnostics::Duplicate_identifier_0
                            };
                            let mut message_needs_name = true;
                            if self.symbols[s.index()].flags.intersects(SymbolFlags::ENUM)
                                || includes.intersects(SymbolFlags::ENUM)
                            {
                                message = &diagnostics::Enum_declarations_can_only_merge_with_namespace_or_other_enum_declarations;
                                message_needs_name = false;
                            }
                            let mut multiple_default_exports = false;
                            if !self.symbols[s.index()].declarations.is_empty() {
                                // If the current node is a default export of some sort, then check if
                                // there are any other default exports that we need to error on.
                                // We'll know whether we have other default exports depending on if `symbol` already has a declaration list set.
                                if is_default_export {
                                    message =
                                        &diagnostics::A_module_cannot_have_multiple_default_exports;
                                    message_needs_name = false;
                                    multiple_default_exports = true;
                                } else {
                                    // This is to properly report an error in the case "export default { }" is after export default of class declaration or function declaration.
                                    // Error on multiple export default in the following case:
                                    // 1. multiple export default of class declaration or function declaration by checking NodeFlags.Default
                                    // 2. multiple export default of export assignment. This one doesn't have NodeFlags.Default on (as export default doesn't considered as modifiers)
                                    if !self.symbols[s.index()].declarations.is_empty()
                                        && is_export_assignment(&self.nodes[node])
                                        && !self.nodes[node].as_export_assignment().is_export_equals
                                    {
                                        message = &diagnostics::A_module_cannot_have_multiple_default_exports;
                                        message_needs_name = false;
                                        multiple_default_exports = true;
                                    }
                                }
                            }
                            let mut declaration_name =
                                get_name_of_declaration(Some(node), self.nodes);
                            if declaration_name.is_none() {
                                declaration_name = Some(node);
                            }
                            let declaration_name = declaration_name.unwrap();
                            let diag: DiagnosticRef = if message_needs_name {
                                let display = self.get_display_name(node);
                                self.create_diagnostic_for_node(
                                    declaration_name,
                                    message,
                                    &[display],
                                )
                            } else {
                                self.create_diagnostic_for_node(declaration_name, message, &[])
                            };
                            if is_type_alias_declaration(&self.nodes[node])
                                && node_is_missing(self.nodes[node].type_(), self.nodes)
                                && has_syntactic_modifier(&self.nodes[node], ModifierFlags::EXPORT)
                                && self.symbols[s.index()].flags.intersects(
                                    SymbolFlags::ALIAS | SymbolFlags::TYPE | SymbolFlags::NAMESPACE,
                                )
                            {
                                // export type T; - may have meant export type { T }?
                                let suggestion = format!(
                                    "export type {{ {} }}",
                                    self.nodes[node]
                                        .as_type_alias_declaration()
                                        .name
                                        .map_or_else(String::new, |n| self.nodes[n]
                                            .text(self.nodes)
                                            .into_owned())
                                );
                                let related = self.create_diagnostic_for_node(
                                    node,
                                    &diagnostics::Did_you_mean_0,
                                    &[suggestion],
                                );
                                lock_diagnostic(&diag).add_related_info(Some(related));
                            }
                            let declarations = self.symbols[s.index()].declarations.clone();
                            for (index, declaration) in declarations.iter().enumerate() {
                                let decl = get_name_of_declaration(Some(*declaration), self.nodes)
                                    .unwrap_or(*declaration);
                                let d: DiagnosticRef = if message_needs_name {
                                    let display = self.get_display_name(*declaration);
                                    self.create_diagnostic_for_node(decl, message, &[display])
                                } else {
                                    self.create_diagnostic_for_node(decl, message, &[])
                                };
                                if multiple_default_exports {
                                    let related = self.create_diagnostic_for_node(
                                        declaration_name,
                                        if index == 0 {
                                            &diagnostics::Another_export_default_is_here
                                        } else {
                                            &diagnostics::X_and_here
                                        },
                                        &[],
                                    );
                                    lock_diagnostic(&d).add_related_info(Some(related));
                                }
                                self.add_diagnostic(d);
                                if multiple_default_exports {
                                    let related = self.create_diagnostic_for_node(
                                        decl,
                                        &diagnostics::The_first_export_default_is_here,
                                        &[],
                                    );
                                    lock_diagnostic(&diag).add_related_info(Some(related));
                                }
                            }
                            self.add_diagnostic(diag);
                            // When get or set accessor conflicts with a non-accessor or an accessor of a different kind, we mark
                            // the symbol as a full accessor such that all subsequent declarations are considered conflicting. This
                            // for example ensures that a get accessor followed by a non-accessor followed by a set accessor with the
                            // same name are all marked as duplicates.
                            if self.symbols[s.index()]
                                .flags
                                .intersects(SymbolFlags::ACCESSOR)
                                && self.symbols[s.index()].flags & SymbolFlags::ACCESSOR
                                    != includes & SymbolFlags::ACCESSOR
                            {
                                self.symbols[s.index()].flags |= SymbolFlags::ACCESSOR;
                            }
                            symbol = self.new_symbol(SymbolFlags::NONE, name);
                        } else {
                            symbol = s;
                        }
                    } else {
                        symbol = s;
                    }
                }
            }
        }
        self.add_declaration_to_symbol(symbol, node, includes);
        if self.symbols[symbol.index()].parent.is_none() {
            self.symbols[symbol.index()].parent = parent;
        } else if self.symbols[symbol.index()].parent != parent {
            panic!("Existing symbol parent should match new one");
        }
        symbol
    }

    /// Should not be called on a declaration with a computed property name,
    /// unless it is a well known Symbol.
    fn get_declaration_name(&mut self, node: NodeId) -> String {
        if is_export_assignment(&self.nodes[node]) {
            return if self.nodes[node].as_export_assignment().is_export_equals {
                INTERNAL_SYMBOL_NAME_EXPORT_EQUALS.to_string()
            } else {
                INTERNAL_SYMBOL_NAME_DEFAULT.to_string()
            };
        }
        if let Some(name) = get_name_of_declaration(Some(node), self.nodes) {
            if is_ambient_module(&self.nodes[node], self.nodes) {
                let module_name = self.nodes[name].text(self.nodes).into_owned();
                if is_global_scope_augmentation(&self.nodes[node]) {
                    return INTERNAL_SYMBOL_NAME_GLOBAL.to_string();
                }
                let pattern = try_parse_pattern(&module_name);
                if pattern.is_valid() && pattern.star_index >= 0 {
                    if let Some(attributes) = self.nodes[node].as_module_declaration().attributes {
                        return format!(
                            "{}\"{}\"pattern@{}",
                            INTERNAL_SYMBOL_NAME_PREFIX, module_name, self.nodes[attributes].id.0
                        );
                    }
                }
                return format!("\"{module_name}\"");
            }
            if is_private_identifier(&self.nodes[name]) {
                // containingClass exists because private names only allowed inside classes
                let Some(containing_class) = get_containing_class(node, self.nodes) else {
                    // we can get here in cases where there is already a parse error.
                    return INTERNAL_SYMBOL_NAME_MISSING.to_string();
                };
                let class_symbol = self.nodes[containing_class]
                    .symbol()
                    .expect("private identifier outside class");
                return get_symbol_name_for_private_identifier(
                    class_symbol,
                    &self.nodes[name].text(self.nodes),
                );
            }
            if is_property_name_literal(&self.nodes[name])
                || is_jsx_namespaced_name(&self.nodes[name])
            {
                return self.nodes[name].text(self.nodes).into_owned();
            }
            if is_computed_property_name(&self.nodes[name]) {
                let name_expression = self.nodes[name]
                    .as_computed_property_name()
                    .expression
                    .unwrap();
                // treat computed property names where expression is string/numeric literal as just string/numeric literal
                if is_string_or_numeric_literal_like(&self.nodes[name_expression]) {
                    return self.nodes[name_expression].text(self.nodes).into_owned();
                }
                if is_signed_numeric_literal(&self.nodes[name_expression], self.nodes) {
                    let unary_expression = self.nodes[name_expression].as_prefix_unary_expression();
                    return format!(
                        "{}{}",
                        token_to_string(unary_expression.operator),
                        self.nodes[unary_expression.operand.unwrap()].text(self.nodes)
                    );
                }
                panic!("Only computed properties with literal names have declaration names")
            }
            return INTERNAL_SYMBOL_NAME_MISSING.to_string();
        }
        match self.nodes[node].kind {
            Kind::Constructor => INTERNAL_SYMBOL_NAME_CONSTRUCTOR.to_string(),
            Kind::FunctionType | Kind::CallSignature => INTERNAL_SYMBOL_NAME_CALL.to_string(),
            Kind::ConstructorType | Kind::ConstructSignature => {
                INTERNAL_SYMBOL_NAME_NEW.to_string()
            }
            Kind::IndexSignature => INTERNAL_SYMBOL_NAME_INDEX.to_string(),
            Kind::ExportDeclaration => INTERNAL_SYMBOL_NAME_EXPORT_STAR.to_string(),
            Kind::SourceFile | Kind::BinaryExpression => {
                INTERNAL_SYMBOL_NAME_EXPORT_EQUALS.to_string()
            }
            _ => INTERNAL_SYMBOL_NAME_MISSING.to_string(),
        }
    }

    fn get_display_name(&mut self, node: NodeId) -> String {
        if let Some(name_node) = self.nodes[node].name() {
            return declaration_name_to_string(Some(name_node), self.nodes);
        }
        let name = self.get_declaration_name(node);
        if name != INTERNAL_SYMBOL_NAME_MISSING {
            return name;
        }
        "(Missing)".to_string()
    }

    fn declare_module_member(
        &mut self,
        node: NodeId,
        symbol_flags: SymbolFlags,
        symbol_excludes: SymbolFlags,
    ) -> SymbolId {
        let container = self
            .container
            .expect("declareModuleMember without container");
        let container_symbol = self.nodes[container].symbol();
        let has_export_modifier = get_combined_modifier_flags(node, self.nodes)
            .intersects(ModifierFlags::EXPORT)
            || is_implicitly_exported_js_doc_declaration(&self.nodes[node], self.nodes);
        if symbol_flags.intersects(SymbolFlags::ALIAS) {
            if self.nodes[node].kind == Kind::ExportSpecifier
                || (self.nodes[node].kind == Kind::ImportEqualsDeclaration && has_export_modifier)
            {
                return self.declare_symbol(
                    SymbolTableDest::Exports(container_symbol.expect("container symbol")),
                    container_symbol,
                    node,
                    symbol_flags,
                    symbol_excludes,
                );
            }
            return self.declare_symbol(
                SymbolTableDest::Locals(container),
                None, /*parent*/
                node,
                symbol_flags,
                symbol_excludes,
            );
        }
        // Exported module members are given 2 symbols: A local symbol that is classified with an ExportValue flag,
        // and an associated export symbol with all the correct flags set on it. There are 2 main reasons:
        //
        //   1. We treat locals and exports of the same name as mutually exclusive within a container.
        //      That means the binder will issue a Duplicate Identifier error if you mix locals and exports
        //      with the same name in the same container.
        //      TODO: Make this a more specific error and decouple it from the exclusion logic.
        //   2. When we checkIdentifier in the checker, we set its resolved symbol to the local symbol,
        //      but return the export symbol (by calling getExportSymbolOfValueSymbolIfExported). That way
        //      when the emitter comes back to it, it knows not to qualify the name if it was found in a containing scope.
        //
        // NOTE: Nested ambient modules always should go to to 'locals' table to prevent their automatic merge
        //       during global merging in the checker. Why? The only case when ambient module is permitted inside another module is module augmentation
        //       and this case is specially handled. Module augmentations should only be merged with original module definition
        //       and should never be merged directly with other augmentation, and the latter case would be possible if automatic merge is allowed.
        if !is_ambient_module(&self.nodes[node], self.nodes)
            && (has_export_modifier
                || self.nodes[container]
                    .flags
                    .intersects(NodeFlags::EXPORT_CONTEXT))
        {
            if !self.is_locals_container(container)
                || (has_syntactic_modifier(&self.nodes[node], ModifierFlags::DEFAULT)
                    && self.get_declaration_name(node) == INTERNAL_SYMBOL_NAME_MISSING)
            {
                return self.declare_symbol(
                    SymbolTableDest::Exports(container_symbol.expect("container symbol")),
                    container_symbol,
                    node,
                    symbol_flags,
                    symbol_excludes,
                );
                // No local symbol for an unnamed default!
            }
            let mut export_kind = SymbolFlags::NONE;
            if symbol_flags.intersects(SymbolFlags::VALUE) {
                export_kind = SymbolFlags::EXPORT_VALUE;
            }
            let local = self.declare_symbol(
                SymbolTableDest::Locals(container),
                None, /*parent*/
                node,
                export_kind,
                symbol_excludes,
            );
            let export_symbol = self.declare_symbol(
                SymbolTableDest::Exports(container_symbol.expect("container symbol")),
                container_symbol,
                node,
                symbol_flags,
                symbol_excludes,
            );
            self.symbols[local.index()].export_symbol = Some(export_symbol);
            self.nodes[node]
                .data
                .exportable_data_mut()
                .expect("ExportableData")
                .local_symbol = Some(local);
            return local;
        }
        self.declare_symbol(
            SymbolTableDest::Locals(container),
            None, /*parent*/
            node,
            symbol_flags,
            symbol_excludes,
        )
    }

    /// `ast.IsLocalsContainer(node)` — has a `LocalsContainerBase`.
    fn is_locals_container(&self, node: NodeId) -> bool {
        self.nodes[node].locals_container_data().is_some()
    }

    fn declare_class_member(
        &mut self,
        node: NodeId,
        symbol_flags: SymbolFlags,
        symbol_excludes: SymbolFlags,
    ) -> SymbolId {
        let container_symbol = self.nodes[self.container.expect("container")]
            .symbol()
            .expect("container symbol");
        if is_static(&self.nodes[node]) {
            return self.declare_symbol(
                SymbolTableDest::Exports(container_symbol),
                Some(container_symbol),
                node,
                symbol_flags,
                symbol_excludes,
            );
        }
        self.declare_symbol(
            SymbolTableDest::Members(container_symbol),
            Some(container_symbol),
            node,
            symbol_flags,
            symbol_excludes,
        )
    }

    fn declare_source_file_member(
        &mut self,
        node: NodeId,
        symbol_flags: SymbolFlags,
        symbol_excludes: SymbolFlags,
    ) -> SymbolId {
        if is_external_module(self.file_data()) {
            return self.declare_module_member(node, symbol_flags, symbol_excludes);
        }
        self.declare_symbol(
            SymbolTableDest::Locals(self.file),
            None, /*parent*/
            node,
            symbol_flags,
            symbol_excludes,
        )
    }

    fn declare_symbol_and_add_to_symbol_table(
        &mut self,
        node: NodeId,
        symbol_flags: SymbolFlags,
        symbol_excludes: SymbolFlags,
    ) -> SymbolId {
        match self.nodes[self.container.expect("container")].kind {
            Kind::ModuleDeclaration => {
                self.declare_module_member(node, symbol_flags, symbol_excludes)
            }
            Kind::SourceFile => {
                self.declare_source_file_member(node, symbol_flags, symbol_excludes)
            }
            Kind::ClassExpression | Kind::ClassDeclaration => {
                self.declare_class_member(node, symbol_flags, symbol_excludes)
            }
            Kind::EnumDeclaration => {
                let container_symbol = self.nodes[self.container.unwrap()].symbol().unwrap();
                self.declare_symbol(
                    SymbolTableDest::Exports(container_symbol),
                    Some(container_symbol),
                    node,
                    symbol_flags,
                    symbol_excludes,
                )
            }
            Kind::TypeLiteral
            | Kind::ObjectLiteralExpression
            | Kind::InterfaceDeclaration
            | Kind::JsxAttributes => {
                let container_symbol = self.nodes[self.container.unwrap()].symbol().unwrap();
                self.declare_symbol(
                    SymbolTableDest::Members(container_symbol),
                    Some(container_symbol),
                    node,
                    symbol_flags,
                    symbol_excludes,
                )
            }
            Kind::FunctionType
            | Kind::ConstructorType
            | Kind::CallSignature
            | Kind::ConstructSignature
            | Kind::IndexSignature
            | Kind::MethodDeclaration
            | Kind::MethodSignature
            | Kind::Constructor
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::FunctionDeclaration
            | Kind::FunctionExpression
            | Kind::ArrowFunction
            | Kind::ClassStaticBlockDeclaration
            | Kind::TypeAliasDeclaration
            | Kind::JSTypeAliasDeclaration
            | Kind::MappedType => self.declare_symbol(
                SymbolTableDest::Locals(self.container.unwrap()),
                None, /*parent*/
                node,
                symbol_flags,
                symbol_excludes,
            ),
            _ => panic!("Unhandled case in declareSymbolAndAddToSymbolTable"),
        }
    }

    fn new_flow_node(&mut self, flags: tsc_ast::FlowFlags) -> FlowNodeId {
        self.flow_nodes.push(FlowNode {
            flags,
            ..Default::default()
        });
        FlowNodeId((self.flow_nodes.len() - 1) as u32)
    }

    fn new_flow_node_ex(
        &mut self,
        flags: tsc_ast::FlowFlags,
        node: Option<NodeId>,
        antecedent: Option<FlowNodeId>,
    ) -> FlowNodeId {
        let result = self.new_flow_node(flags);
        self.flow_nodes[result.index()].node = node;
        self.flow_nodes[result.index()].antecedent = antecedent;
        result
    }

    fn create_loop_label(&mut self) -> FlowNodeId {
        self.new_flow_node(tsc_ast::FlowFlags::LOOP_LABEL)
    }

    fn create_branch_label(&mut self) -> FlowNodeId {
        self.new_flow_node(tsc_ast::FlowFlags::BRANCH_LABEL)
    }

    fn create_reduce_label(
        &mut self,
        target: FlowNodeId,
        antecedents: Option<FlowListId>,
        antecedent: FlowNodeId,
    ) -> FlowNodeId {
        let data = new_flow_reduce_label_data(self.nodes, Some(target), antecedents);
        self.new_flow_node_ex(
            tsc_ast::FlowFlags::REDUCE_LABEL,
            Some(data),
            Some(antecedent),
        )
    }

    fn create_flow_condition(
        &mut self,
        flags: tsc_ast::FlowFlags,
        antecedent: FlowNodeId,
        expression: Option<NodeId>,
    ) -> FlowNodeId {
        if self.flow_nodes[antecedent.index()]
            .flags
            .intersects(tsc_ast::FlowFlags::UNREACHABLE)
        {
            return antecedent;
        }
        let Some(expression) = expression else {
            if flags.intersects(tsc_ast::FlowFlags::TRUE_CONDITION) {
                return antecedent;
            }
            return self.unreachable_flow;
        };
        if (self.nodes[expression].kind == Kind::TrueKeyword
            && flags.intersects(tsc_ast::FlowFlags::FALSE_CONDITION)
            || self.nodes[expression].kind == Kind::FalseKeyword
                && flags.intersects(tsc_ast::FlowFlags::TRUE_CONDITION))
            && !is_expression_of_optional_chain_root(expression, self.nodes)
            && !self.nodes[expression]
                .parent
                .is_some_and(|p| is_nullish_coalesce(&self.nodes[p], self.nodes))
        {
            return self.unreachable_flow;
        }
        if !self.is_narrowing_expression(expression) {
            return antecedent;
        }
        self.set_flow_node_referenced(antecedent);
        self.new_flow_node_ex(flags, Some(expression), Some(antecedent))
    }

    fn create_flow_mutation(
        &mut self,
        flags: tsc_ast::FlowFlags,
        antecedent: FlowNodeId,
        node: NodeId,
    ) -> FlowNodeId {
        self.set_flow_node_referenced(antecedent);
        self.has_flow_effects = true;
        let result = self.new_flow_node_ex(flags, Some(node), Some(antecedent));
        if let Some(exception_target) = self.current_exception_target {
            self.add_antecedent(exception_target, Some(result));
        }
        result
    }

    fn create_flow_switch_clause(
        &mut self,
        antecedent: FlowNodeId,
        switch_statement: NodeId,
        clause_start: i32,
        clause_end: i32,
    ) -> FlowNodeId {
        self.set_flow_node_referenced(antecedent);
        let data = new_flow_switch_clause_data(
            self.nodes,
            Some(switch_statement),
            clause_start,
            clause_end,
        );
        self.new_flow_node_ex(
            tsc_ast::FlowFlags::SWITCH_CLAUSE,
            Some(data),
            Some(antecedent),
        )
    }

    fn create_flow_call(&mut self, antecedent: FlowNodeId, node: NodeId) -> FlowNodeId {
        self.set_flow_node_referenced(antecedent);
        self.has_flow_effects = true;
        self.new_flow_node_ex(tsc_ast::FlowFlags::CALL, Some(node), Some(antecedent))
    }

    fn new_flow_list(&mut self, head: FlowNodeId, tail: Option<FlowListId>) -> FlowListId {
        self.flow_lists.push(FlowList {
            flow: Some(head),
            next: tail,
        });
        FlowListId((self.flow_lists.len() - 1) as u32)
    }

    fn combine_flow_lists(
        &mut self,
        head: Option<FlowListId>,
        tail: Option<FlowListId>,
    ) -> Option<FlowListId> {
        let Some(head) = head else {
            return tail;
        };
        let head_flow = self.flow_lists[head.index()].flow.expect("flow list cell");
        let head_next = self.flow_lists[head.index()].next;
        let new_tail = self.combine_flow_lists(head_next, tail);
        Some(self.new_flow_list(head_flow, new_tail))
    }

    /// `setFlowNodeReferenced` — a free function in Go taking `flow *FlowNode`.
    fn set_flow_node_referenced(&mut self, flow: FlowNodeId) {
        // On first reference we set the Referenced flag, thereafter we set the Shared flag
        let f = &mut self.flow_nodes[flow.index()].flags;
        if !f.intersects(tsc_ast::FlowFlags::REFERENCED) {
            f.insert(tsc_ast::FlowFlags::REFERENCED);
        } else {
            f.insert(tsc_ast::FlowFlags::SHARED);
        }
    }

    /// `func (b *Binder) addAntecedent(label *ast.FlowLabel, antecedent *ast.FlowNode)`.
    ///
    /// PORT: `antecedent` is `Option` because callers pass `b.currentFlow`
    /// (which Go models as a nil-able `*FlowNode`); Go would panic on a nil
    /// dereference, so `None` panics here too.
    fn add_antecedent(&mut self, label: FlowNodeId, antecedent: Option<FlowNodeId>) {
        let antecedent = antecedent.expect("addAntecedent with nil antecedent");
        if self.flow_nodes[antecedent.index()]
            .flags
            .intersects(tsc_ast::FlowFlags::UNREACHABLE)
        {
            return;
        }
        // If antecedent isn't already on the Antecedents list, add it to the end of the list
        let mut last: Option<FlowListId> = None;
        let mut list = self.flow_nodes[label.index()].antecedents;
        while let Some(l) = list {
            if self.flow_lists[l.index()].flow == Some(antecedent) {
                return;
            }
            last = list;
            list = self.flow_lists[l.index()].next;
        }
        let cell = self.new_flow_list(antecedent, None);
        match last {
            None => self.flow_nodes[label.index()].antecedents = Some(cell),
            Some(last) => self.flow_lists[last.index()].next = Some(cell),
        }
        self.set_flow_node_referenced(antecedent);
    }

    fn finish_flow_label(&mut self, label: FlowNodeId) -> FlowNodeId {
        let Some(antecedents) = self.flow_nodes[label.index()].antecedents else {
            return self.unreachable_flow;
        };
        if self.flow_lists[antecedents.index()].next.is_none() {
            return self.flow_lists[antecedents.index()]
                .flow
                .expect("flow list cell");
        }
        label
    }

    /// `func (b *Binder) bind(node *ast.Node) bool` — the per-node dispatch;
    /// the `bool` return mirrors Go's `Visitor` signature (always `false`).
    fn bind(&mut self, node: Option<NodeId>) -> bool {
        let Some(node) = node else {
            return false;
        };
        // Even though in the AST the jsdoc @typedef node belongs to the current node,
        // its symbol might be in the same scope with the current node's symbol. Consider:
        //
        //     /** @typedef {string | number} MyType */
        //     function foo();
        //
        // Here the current node is "foo", which is a container, but the scope of "MyType" should
        // not be inside "foo". Therefore we always bind @typedef before bind the parent node,
        // and skip binding this tag later when binding all the other jsdoc tags.
        // PORT: the JSDoc @typedef early-bind is a no-op here; JSDoc lazy
        // resolution is not yet wired up in tsc-ast.

        // First we bind declaration nodes to a symbol if possible. We'll both create a symbol
        // and then potentially add the symbol to an appropriate symbol table. Possible
        // destination symbol tables are:
        //
        //  1) The 'exports' table of the current container's symbol.
        //  2) The 'members' table of the current container's symbol.
        //  3) The 'locals' table of the current container.
        //
        // However, not all symbols will end up in any of these tables. 'Anonymous' symbols
        // (like TypeLiterals for example) will not be put in any table.
        match self.nodes[node].kind {
            Kind::Identifier => {
                self.nodes[node]
                    .data
                    .flow_node_data_mut()
                    .expect("identifier flow node data")
                    .flow_node = self.current_flow;
                self.check_contextual_identifier(node);
            }
            Kind::ThisKeyword | Kind::SuperKeyword => {
                if self.nodes[node].kind == Kind::ThisKeyword {
                    self.seen_this_keyword = true;
                }
                self.nodes[node]
                    .data
                    .flow_node_data_mut()
                    .expect("keyword flow node data")
                    .flow_node = self.current_flow;
            }
            Kind::QualifiedName => {
                if self.current_flow.is_some() && is_part_of_type_query(node, self.nodes) {
                    self.nodes[node]
                        .data
                        .flow_node_data_mut()
                        .expect("qualified name flow node data")
                        .flow_node = self.current_flow;
                }
            }
            Kind::MetaProperty => {
                self.nodes[node]
                    .data
                    .flow_node_data_mut()
                    .expect("meta property flow node data")
                    .flow_node = self.current_flow;
            }
            Kind::PrivateIdentifier => self.check_private_identifier(node),
            Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
                if self.current_flow.is_some() && self.is_narrowable_reference(node) {
                    self.set_flow_node(node, self.current_flow);
                }
            }
            Kind::BinaryExpression => {
                match get_assignment_declaration_kind(node, self.nodes) {
                    JsDeclarationKind::ModuleExports => self.bind_module_exports_assignment(node),
                    JsDeclarationKind::ExportsProperty => {
                        self.bind_exports_or_object_define_property(node)
                    }
                    JsDeclarationKind::Property => self.bind_expando_property_assignment(node),
                    JsDeclarationKind::ThisProperty => self.bind_this_property_assignment(node),
                    _ => {}
                }
                self.check_strict_mode_binary_expression(node);
            }
            Kind::CatchClause => self.check_strict_mode_catch_clause(node),
            Kind::DeleteExpression => self.check_strict_mode_delete_expression(node),
            Kind::PostfixUnaryExpression => self.check_strict_mode_postfix_unary_expression(node),
            Kind::PrefixUnaryExpression => self.check_strict_mode_prefix_unary_expression(node),
            Kind::WithStatement => self.check_strict_mode_with_statement(node),
            Kind::LabeledStatement => self.check_strict_mode_labeled_statement(node),
            Kind::ThisType => self.seen_this_keyword = true,
            Kind::TypeParameter => self.bind_type_parameter(node),
            Kind::Parameter => self.bind_parameter(node),
            Kind::VariableDeclaration => self.bind_variable_declaration_or_binding_element(node),
            Kind::BindingElement => {
                self.nodes[node]
                    .as_binding_element_mut()
                    .flow_node_base
                    .flow_node = self.current_flow;
                self.bind_variable_declaration_or_binding_element(node);
            }
            Kind::PropertyDeclaration | Kind::PropertySignature => self.bind_property_worker(node),
            Kind::PropertyAssignment | Kind::ShorthandPropertyAssignment => self
                .bind_property_or_method_or_accessor(
                    node,
                    SymbolFlags::PROPERTY,
                    SymbolFlags::PROPERTY_EXCLUDES,
                ),
            Kind::EnumMember => self.bind_property_or_method_or_accessor(
                node,
                SymbolFlags::ENUM_MEMBER,
                SymbolFlags::ENUM_MEMBER_EXCLUDES,
            ),
            Kind::CallSignature | Kind::ConstructSignature | Kind::IndexSignature => {
                self.declare_symbol_and_add_to_symbol_table(
                    node,
                    SymbolFlags::SIGNATURE,
                    SymbolFlags::NONE,
                );
            }
            Kind::MethodDeclaration | Kind::MethodSignature => self
                .bind_property_or_method_or_accessor(
                    node,
                    SymbolFlags::METHOD | self.get_optional_symbol_flag_for_node(node),
                    if is_object_literal_method(node, self.nodes) {
                        SymbolFlags::VALUE
                    } else {
                        SymbolFlags::METHOD_EXCLUDES
                    },
                ),
            Kind::FunctionDeclaration => self.bind_function_declaration(node),
            Kind::Constructor => {
                self.declare_symbol_and_add_to_symbol_table(
                    node,
                    SymbolFlags::CONSTRUCTOR,
                    SymbolFlags::NONE,
                );
            }
            Kind::GetAccessor => self.bind_property_or_method_or_accessor(
                node,
                SymbolFlags::GET_ACCESSOR,
                SymbolFlags::GET_ACCESSOR_EXCLUDES,
            ),
            Kind::SetAccessor => self.bind_property_or_method_or_accessor(
                node,
                SymbolFlags::SET_ACCESSOR,
                SymbolFlags::SET_ACCESSOR_EXCLUDES,
            ),
            Kind::FunctionType | Kind::ConstructorType => {
                self.bind_function_or_constructor_type(node)
            }
            Kind::TypeLiteral | Kind::MappedType => self.bind_anonymous_declaration(
                node,
                SymbolFlags::TYPE_LITERAL,
                INTERNAL_SYMBOL_NAME_TYPE,
            ),
            Kind::ObjectLiteralExpression => self.bind_anonymous_declaration(
                node,
                SymbolFlags::OBJECT_LITERAL,
                INTERNAL_SYMBOL_NAME_OBJECT,
            ),
            Kind::FunctionExpression | Kind::ArrowFunction => self.bind_function_expression(node),
            Kind::ClassExpression | Kind::ClassDeclaration => {
                self.bind_class_like_declaration(node)
            }
            Kind::InterfaceDeclaration => self.bind_block_scoped_declaration(
                node,
                SymbolFlags::INTERFACE,
                SymbolFlags::INTERFACE_EXCLUDES,
            ),
            Kind::CallExpression => {
                match get_assignment_declaration_kind(node, self.nodes) {
                    JsDeclarationKind::ObjectDefinePropertyValue => {
                        self.bind_expando_property_assignment(node)
                    }
                    JsDeclarationKind::ObjectDefinePropertyExports => {
                        self.bind_exports_or_object_define_property(node)
                    }
                    _ => {}
                }
                if is_in_js_file(Some(node), self.nodes) {
                    self.bind_call_expression(node);
                }
            }
            Kind::TypeAliasDeclaration => self.bind_block_scoped_declaration(
                node,
                SymbolFlags::TYPE_ALIAS,
                SymbolFlags::TYPE_ALIAS_EXCLUDES,
            ),
            Kind::JSTypeAliasDeclaration => {
                // Top-level JSTypeAliasDeclaration nodes are processed in bindContainer
                if self.nodes[self.block_scope_container.expect("block scope container")].kind
                    != Kind::SourceFile
                {
                    self.bind_block_scoped_declaration(
                        node,
                        SymbolFlags::TYPE_ALIAS,
                        SymbolFlags::TYPE_ALIAS_EXCLUDES,
                    );
                }
            }
            Kind::EnumDeclaration => self.bind_enum_declaration(node),
            Kind::ModuleDeclaration => self.bind_module_declaration(node),
            Kind::ImportEqualsDeclaration
            | Kind::NamespaceImport
            | Kind::ImportSpecifier
            | Kind::ExportSpecifier => {
                self.declare_symbol_and_add_to_symbol_table(
                    node,
                    SymbolFlags::ALIAS,
                    SymbolFlags::ALIAS_EXCLUDES,
                );
            }
            Kind::NamespaceExportDeclaration => self.bind_namespace_export_declaration(node),
            Kind::ImportClause => self.bind_import_clause(node),
            Kind::ExportDeclaration => self.bind_export_declaration(node),
            Kind::ExportAssignment => self.bind_export_assignment(node),
            Kind::SourceFile => self.bind_source_file_if_external_module(),
            Kind::JsxAttributes => self.bind_jsx_attributes(node),
            Kind::JsxAttribute => {
                self.bind_jsx_attribute(node, SymbolFlags::PROPERTY, SymbolFlags::PROPERTY_EXCLUDES)
            }
            _ => {}
        }
        // Then we recurse into the children of the node to bind them as well. For certain
        // symbols we do specialized work when we recurse. For example, we'll keep track of
        // the current 'container' node when it changes. This helps us know which symbol table
        // a local should go into for example. Since terminal nodes are known not to have
        // children, as an optimization we don't process those.
        let mut this_node_or_any_subnodes_has_error = self.nodes[node]
            .flags
            .intersects(NodeFlags::THIS_NODE_HAS_ERROR);
        if self.nodes[node].kind > Kind::LAST_TOKEN {
            let save_seen_parse_error = self.seen_parse_error;
            self.seen_parse_error = false;
            let container_flags = get_container_flags(node, self.nodes);
            if container_flags == CONTAINER_FLAGS_NONE {
                self.bind_children(node);
            } else {
                self.bind_container(node, container_flags);
            }
            if self.seen_parse_error {
                this_node_or_any_subnodes_has_error = true;
            }
            self.seen_parse_error = save_seen_parse_error;
        }
        if this_node_or_any_subnodes_has_error {
            self.nodes[node]
                .flags
                .insert(NodeFlags::THIS_NODE_OR_ANY_SUB_NODES_HAS_ERROR);
            self.seen_parse_error = true;
        }
        false
    }

    fn bind_property_worker(&mut self, node: NodeId) {
        let is_auto_accessor = is_auto_accessor_property_declaration(&self.nodes[node]);
        let includes = if is_auto_accessor {
            SymbolFlags::ACCESSOR
        } else {
            SymbolFlags::PROPERTY
        };
        let excludes = if is_auto_accessor {
            SymbolFlags::ACCESSOR_EXCLUDES
        } else {
            SymbolFlags::PROPERTY_EXCLUDES
        };
        self.bind_property_or_method_or_accessor(
            node,
            includes | self.get_optional_symbol_flag_for_node(node),
            excludes,
        );
    }

    fn bind_source_file_if_external_module(&mut self) {
        self.set_export_context_flag(self.file);
        if is_external_or_commonjs_module(self.file_data()) {
            self.bind_source_file_as_external_module();
        } else if is_json_source_file(self.file_data()) {
            self.bind_source_file_as_external_module();
            // Create symbol equivalent for the module.exports = {}
            let original_symbol = self.file_data().declaration_base.symbol;
            let file_symbol = original_symbol.expect("file symbol");
            self.declare_symbol(
                SymbolTableDest::Exports(file_symbol),
                Some(file_symbol),
                self.file,
                SymbolFlags::PROPERTY,
                SymbolFlags::ALL,
            );
            self.file_data_mut().declaration_base.symbol = original_symbol;
        }
    }

    fn bind_source_file_as_external_module(&mut self) {
        let name = format!(
            "\"{}\"",
            self.file_data()
                .file_name()
                .remove_file_extension()
                .as_string()
        );
        self.bind_anonymous_declaration(self.file, SymbolFlags::VALUE_MODULE, &name);
    }

    fn bind_module_declaration(&mut self, node: NodeId) {
        self.set_export_context_flag(node);
        if is_ambient_module(&self.nodes[node], self.nodes) {
            if has_syntactic_modifier(&self.nodes[node], ModifierFlags::EXPORT) {
                self.error_on_first_token(node, &diagnostics::X_export_modifier_cannot_be_applied_to_ambient_modules_and_module_augmentations_since_they_are_always_visible, &[]);
            }
            if is_module_augmentation_external(&self.nodes[node], self.nodes) {
                self.declare_module_symbol(node);
            } else {
                let name = self.nodes[node].as_module_declaration().name.unwrap();
                let symbol = self.declare_symbol_and_add_to_symbol_table(
                    node,
                    SymbolFlags::VALUE_MODULE,
                    SymbolFlags::VALUE_MODULE_EXCLUDES,
                );

                if is_string_literal(&self.nodes[name]) {
                    let attributes = self.nodes[node].as_module_declaration().attributes;
                    let pattern = try_parse_pattern(&self.nodes[name].text(self.nodes));
                    if !pattern.is_valid() {
                        // An invalid pattern - must have multiple wildcards.
                        let text = self.nodes[name].text(self.nodes).into_owned();
                        self.error_on_first_token(
                            name,
                            &diagnostics::Pattern_0_can_have_at_most_one_Asterisk_character,
                            &[text],
                        );
                    } else if pattern.star_index >= 0 {
                        let mut modules =
                            std::mem::take(&mut self.file_data_mut().pattern_ambient_modules)
                                .into_vec();
                        modules.push(PatternAmbientModule {
                            pattern,
                            symbol: Some(symbol),
                        });
                        self.file_data_mut().pattern_ambient_modules = modules.into_boxed_slice();
                    } else if attributes.is_some() {
                        self.error_on_node(name, &diagnostics::An_ambient_module_declaration_with_import_attributes_must_use_a_pattern_name_with_an_Asterisk_character, &[]);
                    }
                }
            }
        } else {
            let state = self.declare_module_symbol(node);
            if state != ModuleInstanceState::NonInstantiated {
                let symbol = self.nodes[node].symbol().expect("module symbol");
                // if module was already merged with some function, class or non-const enum, treat it as non-const-enum-only
                let const_enum_only_module = !self.symbols[symbol.index()].flags.intersects(
                    SymbolFlags::FUNCTION | SymbolFlags::CLASS | SymbolFlags::REGULAR_ENUM,
                ) &&
                    // Current must be `const enum` only
                    state == ModuleInstanceState::ConstEnumOnly &&
                    // Can't have been set to 'false' in a previous merged symbol. ('undefined' OK)
                    !self.not_const_enum_only_modules.has(&symbol);
                if const_enum_only_module {
                    self.symbols[symbol.index()].flags |= SymbolFlags::CONST_ENUM_ONLY_MODULE;
                } else {
                    self.symbols[symbol.index()]
                        .flags
                        .remove(SymbolFlags::CONST_ENUM_ONLY_MODULE);
                    self.not_const_enum_only_modules.add(symbol);
                }
            }
        }
    }

    fn declare_module_symbol(&mut self, node: NodeId) -> ModuleInstanceState {
        let state = get_module_instance_state(node, self.nodes);
        let instantiated = state != ModuleInstanceState::NonInstantiated;
        self.declare_symbol_and_add_to_symbol_table(
            node,
            if instantiated {
                SymbolFlags::VALUE_MODULE
            } else {
                SymbolFlags::NAMESPACE_MODULE
            },
            if instantiated {
                SymbolFlags::VALUE_MODULE_EXCLUDES
            } else {
                SymbolFlags::NAMESPACE_MODULE_EXCLUDES
            },
        );
        state
    }

    fn bind_namespace_export_declaration(&mut self, node: NodeId) {
        if self.nodes[node].modifiers().is_some() {
            self.error_on_node(node, &diagnostics::Modifiers_cannot_appear_here, &[]);
        }
        let parent = self.nodes[node].parent;
        if !parent.is_some_and(|p| is_source_file(&self.nodes[p])) {
            self.error_on_node(
                node,
                &diagnostics::Global_module_exports_may_only_appear_at_top_level,
                &[],
            );
        } else if !is_external_module(self.nodes[parent.unwrap()].as_source_file()) {
            self.error_on_node(
                node,
                &diagnostics::Global_module_exports_may_only_appear_in_module_files,
                &[],
            );
        } else if !self.nodes[parent.unwrap()]
            .as_source_file()
            .is_declaration_file
        {
            self.error_on_node(
                node,
                &diagnostics::Global_module_exports_may_only_appear_in_declaration_files,
                &[],
            );
        } else {
            let file_symbol = self.file_data().declaration_base.symbol;
            self.declare_symbol(
                SymbolTableDest::GlobalExports,
                file_symbol,
                node,
                SymbolFlags::ALIAS,
                SymbolFlags::ALIAS_EXCLUDES,
            );
        }
    }

    fn bind_import_clause(&mut self, node: NodeId) {
        if self.nodes[node].as_import_clause().name.is_some() {
            self.declare_symbol_and_add_to_symbol_table(
                node,
                SymbolFlags::ALIAS,
                SymbolFlags::ALIAS_EXCLUDES,
            );
        }
    }

    fn bind_export_declaration(&mut self, node: NodeId) {
        let container_symbol = self.nodes[self.container.expect("container")].symbol();
        if container_symbol.is_none() {
            // Export * in some sort of block construct
            let name = self.get_declaration_name(node);
            self.bind_anonymous_declaration(node, SymbolFlags::EXPORT_STAR, &name);
        } else if let Some(container_symbol) = container_symbol {
            match self.nodes[node].as_export_declaration().export_clause {
                None => {
                    // All export * declarations are collected in an __export symbol
                    self.declare_symbol(
                        SymbolTableDest::Exports(container_symbol),
                        Some(container_symbol),
                        node,
                        SymbolFlags::EXPORT_STAR,
                        SymbolFlags::NONE,
                    );
                }
                Some(export_clause) if is_namespace_export(&self.nodes[export_clause]) => {
                    self.declare_symbol(
                        SymbolTableDest::Exports(container_symbol),
                        Some(container_symbol),
                        export_clause,
                        SymbolFlags::ALIAS,
                        SymbolFlags::ALIAS_EXCLUDES,
                    );
                }
                _ => {}
            }
        }
    }

    fn bind_export_assignment(&mut self, node: NodeId) {
        let container = self.container.expect("container");
        if self.nodes[container].symbol().is_none() && is_export_assignment(&self.nodes[node]) {
            // Incorrect export assignment in some sort of block construct
            let name = self.get_declaration_name(node);
            self.bind_anonymous_declaration(node, SymbolFlags::VALUE, &name);
        } else {
            let container_symbol = self.nodes[container].symbol().unwrap();
            // If there is an `export default x;` alias declaration, can't `export default` anything else.
            // (In contrast, you can still have `export default function f() {}` and `export default interface I {}`.)
            let expression = self.nodes[node].expression();
            let flags =
                if expression.is_some_and(|e| expression_is_alias(&self.nodes[e], self.nodes)) {
                    SymbolFlags::ALIAS
                } else {
                    SymbolFlags::PROPERTY
                };
            let symbol = self.declare_symbol(
                SymbolTableDest::Exports(container_symbol),
                Some(container_symbol),
                node,
                flags,
                SymbolFlags::ALL,
            );
            if self.nodes[node].as_export_assignment().is_export_equals {
                // Ensure export assignments have a ValueDeclaration set.
                set_value_declaration(self.symbols, symbol, node, &|id| self.nodes[id].clone());
            }
        }
    }

    fn bind_jsx_attributes(&mut self, node: NodeId) {
        self.bind_anonymous_declaration(
            node,
            SymbolFlags::OBJECT_LITERAL,
            INTERNAL_SYMBOL_NAME_JSX_ATTRIBUTES,
        );
    }

    fn bind_jsx_attribute(
        &mut self,
        node: NodeId,
        symbol_flags: SymbolFlags,
        symbol_excludes: SymbolFlags,
    ) {
        self.declare_symbol_and_add_to_symbol_table(node, symbol_flags, symbol_excludes);
    }

    fn set_export_context_flag(&mut self, node: NodeId) {
        // A declaration source file or ambient module declaration that contains no export declarations (but possibly regular
        // declarations with export modifiers) is an export context in which declarations are implicitly exported.
        if self.nodes[node].flags.intersects(NodeFlags::AMBIENT)
            && !self.has_export_declarations(node)
        {
            self.nodes[node].flags.insert(NodeFlags::EXPORT_CONTEXT);
        } else {
            self.nodes[node].flags.remove(NodeFlags::EXPORT_CONTEXT);
        }
    }

    fn has_export_declarations(&self, node: NodeId) -> bool {
        let statements: &[NodeId] = match self.nodes[node].kind {
            Kind::SourceFile => self.nodes[node].statements().unwrap_or(&[]),
            Kind::ModuleDeclaration => match self.nodes[node].body() {
                Some(body) if is_module_block(&self.nodes[body]) => {
                    self.nodes[body].statements().unwrap_or(&[])
                }
                _ => &[],
            },
            _ => &[],
        };
        statements
            .iter()
            .any(|&s| is_export_declaration(&self.nodes[s]) || is_export_assignment(&self.nodes[s]))
    }

    fn bind_function_expression(&mut self, node: NodeId) {
        if !self.file_data().is_declaration_file
            && !self.nodes[node].flags.intersects(NodeFlags::AMBIENT)
            && is_async_function(&self.nodes[node])
        {
            self.emit_flags |= NodeFlags::HAS_ASYNC_FUNCTIONS;
        }
        self.set_flow_node(node, self.current_flow);
        let mut binding_name = INTERNAL_SYMBOL_NAME_FUNCTION.to_string();
        if is_function_expression(&self.nodes[node])
            && self.nodes[node].as_function_expression().name.is_some()
        {
            self.check_strict_mode_function_name(node);
            binding_name = self.nodes[self.nodes[node].as_function_expression().name.unwrap()]
                .text(self.nodes)
                .into_owned();
        }
        self.bind_anonymous_declaration(node, SymbolFlags::FUNCTION, &binding_name);
    }

    fn bind_call_expression(&mut self, node: NodeId) {
        // We're only inspecting call expressions to detect CommonJS modules, so we can skip
        // this check if we've already seen the module indicator
        if self.file_data().common_js_module_indicator.is_none()
            && is_require_call(
                &self.nodes[node],
                false, /*requireStringLiteralLikeArgument*/
                self.nodes,
            )
        {
            self.set_commonjs_module_indicator(node);
        }
    }

    fn set_commonjs_module_indicator(&mut self, node: NodeId) -> bool {
        let external_indicator = self.file_data().external_module_indicator;
        if external_indicator.is_some() && external_indicator != Some(self.file) {
            return false;
        }
        if self.file_data().common_js_module_indicator.is_none() {
            self.file_data_mut().common_js_module_indicator = Some(node);
            if self.file_data().external_module_indicator.is_none() {
                self.bind_source_file_as_external_module();
            }
        }
        true
    }

    fn bind_class_like_declaration(&mut self, node: NodeId) {
        let name = self.nodes[node].name();
        match self.nodes[node].kind {
            Kind::ClassDeclaration => self.bind_block_scoped_declaration(
                node,
                SymbolFlags::CLASS,
                SymbolFlags::CLASS_EXCLUDES,
            ),
            Kind::ClassExpression => {
                let name_text = name.map_or_else(
                    || INTERNAL_SYMBOL_NAME_CLASS.to_string(),
                    |n| self.nodes[n].text(self.nodes).into_owned(),
                );
                self.bind_anonymous_declaration(node, SymbolFlags::CLASS, &name_text);
            }
            _ => {}
        }
        let symbol = self.nodes[node].symbol().expect("class symbol");
        // TypeScript 1.0 spec (April 2014): 8.4
        // Every class automatically contains a static property member named 'prototype', the
        // type of which is an instantiation of the class type with type Any supplied as a type
        // argument for each type parameter. It is an error to explicitly declare a static
        // property member with the name 'prototype'.
        //
        // Note: we check for this here because this class may be merging into a module.  The
        // module might have an exported variable called 'prototype'.  We can't allow that as
        // that would clash with the built-in 'prototype' for the class.
        let prototype_symbol = self.new_symbol(
            SymbolFlags::PROPERTY | SymbolFlags::PROTOTYPE,
            "prototype".to_string(),
        );
        if let Some(symbol_export) = self.table_get(SymbolTableDest::Exports(symbol), "prototype") {
            let decl = self.symbols[symbol_export.index()].declarations[0];
            let arg = symbol_name(&self.symbols[prototype_symbol.index()], self.nodes).into_owned();
            self.error_on_node(decl, &diagnostics::Duplicate_identifier_0, &[arg]);
        }
        self.table_set(
            SymbolTableDest::Exports(symbol),
            "prototype".to_string(),
            prototype_symbol,
        );
        self.symbols[prototype_symbol.index()].parent = Some(symbol);
    }

    fn bind_property_or_method_or_accessor(
        &mut self,
        node: NodeId,
        symbol_flags: SymbolFlags,
        symbol_excludes: SymbolFlags,
    ) {
        if !self.file_data().is_declaration_file
            && !self.nodes[node].flags.intersects(NodeFlags::AMBIENT)
            && is_async_function(&self.nodes[node])
        {
            self.emit_flags |= NodeFlags::HAS_ASYNC_FUNCTIONS;
        }
        if self.current_flow.is_some()
            && is_object_literal_or_class_expression_method_or_accessor(node, self.nodes)
        {
            self.set_flow_node(node, self.current_flow);
        }
        if has_dynamic_name(node, self.nodes) {
            self.bind_anonymous_declaration(node, symbol_flags, INTERNAL_SYMBOL_NAME_COMPUTED);
        } else {
            self.declare_symbol_and_add_to_symbol_table(node, symbol_flags, symbol_excludes);
        }
    }

    fn bind_function_or_constructor_type(&mut self, node: NodeId) {
        // For a given function symbol "<...>(...) => T" we want to generate a symbol identical
        // to the one we would get for: { <...>(...): T }
        //
        // We do that by making an anonymous type literal symbol, and then setting the function
        // symbol as its sole member. To the rest of the system, this symbol will be indistinguishable
        // from an actual type literal symbol you would have gotten had you used the long form.
        let name = self.get_declaration_name(node);
        let symbol = self.new_symbol(SymbolFlags::SIGNATURE, name);
        self.add_declaration_to_symbol(symbol, node, SymbolFlags::SIGNATURE);
        let type_literal_symbol = self.new_symbol(
            SymbolFlags::TYPE_LITERAL,
            INTERNAL_SYMBOL_NAME_TYPE.to_string(),
        );
        self.add_declaration_to_symbol(type_literal_symbol, node, SymbolFlags::TYPE_LITERAL);
        let symbol_name = self.symbols[symbol.index()].name.clone();
        self.symbols[type_literal_symbol.index()]
            .members
            .set(symbol_name.into(), symbol);
    }

    fn add_late_bound_assignment_declaration_to_symbol(&mut self, node: NodeId, symbol: SymbolId) {
        let exports = SymbolTableDest::Exports(symbol);
        let assignment_symbol =
            match self.table_get(exports, INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION) {
                Some(s) => s,
                None => {
                    let s = self.new_symbol(
                        SymbolFlags::NONE,
                        INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION.to_string(),
                    );
                    self.table_set(
                        exports,
                        INTERNAL_SYMBOL_NAME_ASSIGNMENT_DECLARATION.to_string(),
                        s,
                    );
                    s
                }
            };
        self.symbols[assignment_symbol.index()]
            .declarations
            .push(node);
    }

    fn bind_module_exports_assignment(&mut self, node: NodeId) {
        if self.set_commonjs_module_indicator(node) {
            let container = self.file;
            let container_symbol = self.nodes[container].symbol().expect("file symbol");
            let right = self.nodes[node].as_binary_expression().right;
            let flags = if right.is_some_and(|r| expression_is_alias(&self.nodes[r], self.nodes)) {
                SymbolFlags::ALIAS
            } else {
                SymbolFlags::PROPERTY
            };
            let symbol = self.declare_symbol(
                SymbolTableDest::Exports(container_symbol),
                Some(container_symbol),
                node,
                flags,
                SymbolFlags::NONE,
            );
            set_value_declaration(self.symbols, symbol, node, &|id| self.nodes[id].clone());
        }
    }

    fn bind_expando_property_assignment(&mut self, node: NodeId) {
        self.expando_assignments.push(ExpandoAssignmentInfo {
            node,
            container: self.container.expect("expando container"),
            block_scope_container: self.block_scope_container.expect("expando block container"),
        });
    }

    fn bind_deferred_expando_assignments(&mut self) {
        let infos = std::mem::take(&mut self.expando_assignments);
        for info in infos {
            self.container = Some(info.container);
            self.block_scope_container = Some(info.block_scope_container);
            self.bind_deferred_expando_assignment(info.node);
        }
    }

    /// If the given module symbol has an export= symbol, promote exports with a type or namespace meaning
    /// from the module symbol onto the export= symbol and, if any such exports exist, mark the export=
    /// symbol as a namespace module.
    fn bind_commonjs_type_exports(&mut self, module_symbol: SymbolId) {
        if let Some(export_equals) = self.symbols[module_symbol.index()]
            .exports
            .get(INTERNAL_SYMBOL_NAME_EXPORT_EQUALS)
            .copied()
        {
            let promoted: Vec<(Arc<str>, SymbolId)> = self.symbols[module_symbol.index()]
                .exports
                .entries()
                .filter(|(name, sym)| {
                    &***name != INTERNAL_SYMBOL_NAME_EXPORT_EQUALS
                        && self.symbols[sym.index()]
                            .flags
                            .intersects(SymbolFlags::TYPE | SymbolFlags::NAMESPACE)
                })
                .map(|(name, sym)| (name.clone(), *sym))
                .collect();
            for (name, symbol) in promoted {
                self.symbols[export_equals.index()]
                    .exports
                    .set(name, symbol);
                self.symbols[export_equals.index()].flags |= SymbolFlags::NAMESPACE_MODULE;
            }
        }
    }

    fn bind_deferred_expando_assignment(&mut self, node: NodeId) {
        let parent = get_parent_of_property_assignment(node, self.nodes);
        let mut symbol = self.lookup_entity(parent, self.block_scope_container.unwrap());
        if symbol.is_none() {
            symbol = self.lookup_entity(parent, self.container.unwrap());
        }
        if let Some(symbol) = symbol.and_then(|s| self.get_initializer_symbol(s)) {
            if has_dynamic_name(node, self.nodes) {
                self.bind_anonymous_declaration(
                    node,
                    SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT,
                    INTERNAL_SYMBOL_NAME_COMPUTED,
                );
                self.add_late_bound_assignment_declaration_to_symbol(node, symbol);
            } else {
                // We declare expandos only when there are no non-expando declarations for that name.
                let exports = SymbolTableDest::Exports(symbol);
                let name = self.get_declaration_name(node);
                let declare = match self.table_get(exports, &name) {
                    None => true,
                    Some(existing) => self.symbols[existing.index()]
                        .flags
                        .intersects(SymbolFlags::ASSIGNMENT),
                };
                if declare {
                    self.declare_symbol(
                        exports,
                        Some(symbol),
                        node,
                        SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT,
                        SymbolFlags::PROPERTY_EXCLUDES,
                    );
                }
            }
        }
    }

    fn bind_exports_or_object_define_property(&mut self, node: NodeId) {
        if self.set_commonjs_module_indicator(node) {
            let container = self.file;
            let container_symbol = self.nodes[container].symbol().expect("file symbol");
            let flags = if is_binary_expression(&self.nodes[node])
                && self.nodes[node]
                    .as_binary_expression()
                    .right
                    .is_some_and(|r| expression_is_alias(&self.nodes[r], self.nodes))
            {
                SymbolFlags::ALIAS
            } else {
                SymbolFlags::FUNCTION_SCOPED_VARIABLE
            };
            self.declare_symbol(
                SymbolTableDest::Exports(container_symbol),
                Some(container_symbol),
                node,
                flags,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
            );
        }
    }

    /// `getInitializerSymbol` — reads `symbol` via the arena (`&[Symbol]` view).
    fn get_initializer_symbol(&self, symbol: SymbolId) -> Option<SymbolId> {
        get_initializer_symbol(self.symbols, symbol, self.nodes)
    }

    fn bind_this_property_assignment(&mut self, node: NodeId) {
        if !is_in_js_file(Some(node), self.nodes) {
            return;
        }
        let bin = self.nodes[node].as_binary_expression();
        let left = bin.left;
        if left.is_some_and(|l| {
            is_property_access_expression(&self.nodes[l])
                && is_private_identifier(
                    &self.nodes[self.nodes[l].as_property_access_expression().name.unwrap()],
                )
        }) || self.this_container.is_none()
        {
            return;
        }
        if let (Some(class_symbol), Some(symbol_table)) = self.get_this_class_and_symbol_table() {
            if has_dynamic_name(node, self.nodes) {
                self.declare_symbol_ex(
                    symbol_table,
                    Some(class_symbol),
                    node,
                    SymbolFlags::PROPERTY,
                    SymbolFlags::NONE,
                    true, /*isReplaceableByMethod*/
                    true, /*isComputedName*/
                );
                self.add_late_bound_assignment_declaration_to_symbol(node, class_symbol);
            } else {
                self.declare_symbol_ex(
                    symbol_table,
                    Some(class_symbol),
                    node,
                    SymbolFlags::PROPERTY | SymbolFlags::ASSIGNMENT,
                    SymbolFlags::NONE,
                    true,  /*isReplaceableByMethod*/
                    false, /*isComputedName*/
                );
            }
        } else {
            let this_container = self.this_container.unwrap();
            if self.nodes[this_container].kind != Kind::FunctionDeclaration
                && self.nodes[this_container].kind != Kind::FunctionExpression
            {
                // !!! constructor functions
                panic!(
                    "Unhandled case in bindThisPropertyAssignment: {}",
                    self.nodes[this_container].kind_string()
                );
            }
        }
    }

    fn get_this_class_and_symbol_table(&mut self) -> (Option<SymbolId>, Option<SymbolTableDest>) {
        let Some(this_container) = self.this_container else {
            return (None, None);
        };
        let mut class_symbol = None;
        let mut symbol_table = None;
        match self.nodes[this_container].kind {
            Kind::FunctionDeclaration | Kind::FunctionExpression => {
                // !!! constructor functions
            }
            Kind::Constructor
            | Kind::PropertyDeclaration
            | Kind::MethodDeclaration
            | Kind::GetAccessor
            | Kind::SetAccessor
            | Kind::ClassStaticBlockDeclaration => {
                // this.property assignment in class member -- bind to the containing class
                class_symbol = self.nodes[this_container]
                    .parent
                    .and_then(|p| self.nodes[p].symbol());
                if is_static(&self.nodes[this_container]) {
                    symbol_table = Some(SymbolTableDest::Exports(class_symbol.unwrap()));
                } else {
                    symbol_table = Some(SymbolTableDest::Members(class_symbol.unwrap()));
                }
            }
            _ => {}
        }
        (class_symbol, symbol_table)
    }

    fn bind_enum_declaration(&mut self, node: NodeId) {
        if is_enum_const(node, self.nodes) {
            self.bind_block_scoped_declaration(
                node,
                SymbolFlags::CONST_ENUM,
                SymbolFlags::CONST_ENUM_EXCLUDES,
            );
        } else {
            self.bind_block_scoped_declaration(
                node,
                SymbolFlags::REGULAR_ENUM,
                SymbolFlags::REGULAR_ENUM_EXCLUDES,
            );
        }
    }

    fn bind_variable_declaration_or_binding_element(&mut self, node: NodeId) {
        let name = self.nodes[node].name();
        self.check_strict_mode_eval_or_arguments(node, name);
        if let Some(name) = name {
            if !is_binding_pattern(&self.nodes[name]) {
                if is_variable_declaration_initialized_to_require(node, self.nodes) {
                    self.declare_symbol_and_add_to_symbol_table(
                        node,
                        SymbolFlags::ALIAS,
                        SymbolFlags::ALIAS_EXCLUDES,
                    );
                } else if is_block_or_catch_scoped(node, self.nodes) {
                    self.bind_block_scoped_declaration(
                        node,
                        SymbolFlags::BLOCK_SCOPED_VARIABLE,
                        SymbolFlags::BLOCK_SCOPED_VARIABLE_EXCLUDES,
                    );
                } else if is_part_of_parameter_declaration(node, self.nodes) {
                    // It is safe to walk up parent chain to find whether the node is a destructuring parameter declaration
                    // because its parent chain has already been set up, since parents are set before descending into children.
                    //
                    // If node is a binding element in parameter declaration, we need to use ParameterExcludes.
                    // Using ParameterExcludes flag allows the compiler to report an error on duplicate identifiers in Parameter Declaration
                    // For example:
                    //      function foo([a,a]) {} // Duplicate Identifier error
                    //      function bar(a,a) {}   // Duplicate Identifier error, parameter declaration in this case is handled in bindParameter
                    //                             // which correctly set excluded symbols
                    self.declare_symbol_and_add_to_symbol_table(
                        node,
                        SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                        SymbolFlags::PARAMETER_EXCLUDES,
                    );
                } else {
                    self.declare_symbol_and_add_to_symbol_table(
                        node,
                        SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                        SymbolFlags::FUNCTION_SCOPED_VARIABLE_EXCLUDES,
                    );
                }
            }
        }
    }

    fn bind_parameter(&mut self, node: NodeId) {
        let decl_name = self.nodes[node].as_parameter_declaration().name;
        if !self.nodes[node].flags.intersects(NodeFlags::AMBIENT) {
            // It is a SyntaxError if the identifier eval or arguments appears within a FormalParameterList of a
            // strict mode FunctionLikeDeclaration or FunctionExpression(13.1)
            self.check_strict_mode_eval_or_arguments(node, decl_name);
        }
        if decl_name.is_some_and(|n| is_binding_pattern(&self.nodes[n])) {
            let parent = self.nodes[node].parent.unwrap();
            let index = self.nodes[parent]
                .parameters()
                .unwrap_or(&[])
                .iter()
                .position(|&p| p == node)
                .expect("parameter not in parent parameter list");
            let name = format!("__{index}");
            self.bind_anonymous_declaration(node, SymbolFlags::FUNCTION_SCOPED_VARIABLE, &name);
        } else {
            self.declare_symbol_and_add_to_symbol_table(
                node,
                SymbolFlags::FUNCTION_SCOPED_VARIABLE,
                SymbolFlags::PARAMETER_EXCLUDES,
            );
        }
        // If this is a property-parameter, then also declare the property symbol into the
        // containing class.
        let parent = self.nodes[node].parent.unwrap();
        if is_parameter_property_declaration(&self.nodes[node], &self.nodes[parent]) {
            let class_declaration = self.nodes[parent].parent.unwrap();
            let class_symbol = self.nodes[class_declaration].symbol().unwrap();
            let flags = SymbolFlags::PROPERTY
                | if self.nodes[node]
                    .as_parameter_declaration()
                    .question_token
                    .is_some()
                {
                    SymbolFlags::OPTIONAL
                } else {
                    SymbolFlags::NONE
                };
            self.declare_symbol(
                SymbolTableDest::Members(class_symbol),
                Some(class_symbol),
                node,
                flags,
                SymbolFlags::PROPERTY_EXCLUDES,
            );
        }
    }

    fn bind_function_declaration(&mut self, node: NodeId) {
        if !self.file_data().is_declaration_file
            && !self.nodes[node].flags.intersects(NodeFlags::AMBIENT)
            && is_async_function(&self.nodes[node])
        {
            self.emit_flags |= NodeFlags::HAS_ASYNC_FUNCTIONS;
        }
        self.check_strict_mode_function_name(node);
        self.bind_block_scoped_declaration(
            node,
            SymbolFlags::FUNCTION,
            SymbolFlags::FUNCTION_EXCLUDES,
        );
    }

    fn get_infer_type_container(&self, node: NodeId) -> Option<NodeId> {
        let extends_type =
            find_ancestor(Some(node), self.nodes, &mut |n: &Node, nodes: &[Node]| {
                let Some(parent) = n.parent else {
                    return false;
                };
                is_conditional_type_node(&nodes[parent])
                    && nodes[parent].as_conditional_type_node().extends_type == Some(n.id)
            })?;
        self.nodes[extends_type].parent
    }

    fn bind_anonymous_declaration(&mut self, node: NodeId, symbol_flags: SymbolFlags, name: &str) {
        let symbol = self.new_symbol(symbol_flags, name.to_string());
        if symbol_flags.intersects(SymbolFlags::ENUM_MEMBER | SymbolFlags::CLASS_MEMBER) {
            self.symbols[symbol.index()].parent =
                self.nodes[self.container.expect("container")].symbol();
        }
        self.add_declaration_to_symbol(symbol, node, symbol_flags);
    }

    fn bind_block_scoped_declaration(
        &mut self,
        node: NodeId,
        symbol_flags: SymbolFlags,
        symbol_excludes: SymbolFlags,
    ) {
        let block_scope_container = self.block_scope_container.expect("block scope container");
        match self.nodes[block_scope_container].kind {
            Kind::ModuleDeclaration => {
                self.declare_module_member(node, symbol_flags, symbol_excludes);
            }
            Kind::SourceFile
                if is_external_or_commonjs_module(
                    self.nodes[self.container.expect("container")].as_source_file(),
                ) =>
            {
                self.declare_module_member(node, symbol_flags, symbol_excludes);
            }
            _ => {
                self.declare_symbol(
                    SymbolTableDest::Locals(block_scope_container),
                    None, /*parent*/
                    node,
                    symbol_flags,
                    symbol_excludes,
                );
            }
        }
    }

    fn bind_type_parameter(&mut self, node: NodeId) {
        if self.nodes[self.nodes[node].parent.unwrap()].kind == Kind::InferType {
            let container = self.get_infer_type_container(self.nodes[node].parent.unwrap());
            if let Some(container) = container {
                self.declare_symbol(
                    SymbolTableDest::Locals(container),
                    None, /*parent*/
                    node,
                    SymbolFlags::TYPE_PARAMETER,
                    SymbolFlags::TYPE_PARAMETER_EXCLUDES,
                );
            } else {
                let name = self.get_declaration_name(node);
                self.bind_anonymous_declaration(node, SymbolFlags::TYPE_PARAMETER, &name);
            }
        } else {
            self.declare_symbol_and_add_to_symbol_table(
                node,
                SymbolFlags::TYPE_PARAMETER,
                SymbolFlags::TYPE_PARAMETER_EXCLUDES,
            );
        }
    }

    fn lookup_entity(&mut self, node: NodeId, container: NodeId) -> Option<SymbolId> {
        if is_identifier(&self.nodes[node]) {
            let name = self.nodes[node].text(self.nodes).into_owned();
            return self.lookup_name(&name, container);
        }
        let expression = self.nodes[node].expression();
        if expression.is_some_and(|e| self.nodes[e].kind == Kind::ThisKeyword) {
            if let (_, Some(symbol_table)) = self.get_this_class_and_symbol_table() {
                if let Some(name) =
                    get_element_or_property_access_name(&self.nodes[node], self.nodes)
                {
                    return self.table_get(symbol_table, &self.nodes[name].text(self.nodes));
                }
            }
            return None;
        }
        if let Some(expr) = expression {
            if let Some(symbol) = self
                .lookup_entity(expr, container)
                .and_then(|s| self.get_initializer_symbol(s))
            {
                if !self.symbols[symbol.index()].exports.is_empty() {
                    if let Some(name) =
                        get_element_or_property_access_name(&self.nodes[node], self.nodes)
                    {
                        return self.symbols[symbol.index()]
                            .exports
                            .get(&self.nodes[name].text(self.nodes) as &str)
                            .copied();
                    }
                }
            }
        }
        None
    }

    fn lookup_name(&mut self, name: &str, container: NodeId) -> Option<SymbolId> {
        if let Some(locals_container) = self.nodes[container].locals_container_data() {
            if let Some(local) = locals_container.locals.get(name) {
                let local = *local;
                return Some(self.symbols[local.index()].export_symbol.unwrap_or(local));
            }
        }
        if let Some(declaration) = self.nodes[container].declaration_data() {
            if let Some(symbol) = declaration.symbol {
                return self.symbols[symbol.index()].exports.get(name).copied();
            }
        }
        None
    }

    // The binder visits every node in the syntax tree so it is a convenient place to perform a single localized
    // check for reserved words used as identifiers in strict mode code, as well as `yield` or `await` in
    // [Yield] or [Await] contexts, respectively.
    fn check_contextual_identifier(&mut self, node: NodeId) {
        // Report error only if there are no parse errors in file
        if self.file_data().diagnostics.is_empty()
            && !self.nodes[node].flags.intersects(NodeFlags::AMBIENT)
            && !self.nodes[node].flags.intersects(NodeFlags::JSDOC)
            && !is_identifier_name(node, self.nodes)
        {
            // strict mode identifiers
            let original_keyword_kind =
                get_identifier_token(self.nodes[node].text(self.nodes).as_bytes());
            if original_keyword_kind == Kind::Identifier {
                return;
            }
            if original_keyword_kind >= Kind::FIRST_FUTURE_RESERVED_WORD
                && original_keyword_kind <= Kind::LAST_FUTURE_RESERVED_WORD
            {
                let message = self.get_strict_mode_identifier_message(node);
                let arg = declaration_name_to_string(Some(node), self.nodes);
                self.error_on_node(node, message, &[arg]);
            } else if original_keyword_kind == Kind::AwaitKeyword {
                if is_external_module(self.file_data()) && is_in_top_level_context(node, self.nodes)
                {
                    let arg = declaration_name_to_string(Some(node), self.nodes);
                    self.error_on_node(node, &diagnostics::Identifier_expected_0_is_a_reserved_word_at_the_top_level_of_a_module, &[arg]);
                } else if self.nodes[node].flags.intersects(NodeFlags::AWAIT_CONTEXT) {
                    let arg = declaration_name_to_string(Some(node), self.nodes);
                    self.error_on_node(node, &diagnostics::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here, &[arg]);
                }
            } else if original_keyword_kind == Kind::YieldKeyword
                && self.nodes[node].flags.intersects(NodeFlags::YIELD_CONTEXT)
            {
                let arg = declaration_name_to_string(Some(node), self.nodes);
                self.error_on_node(
                    node,
                    &diagnostics::Identifier_expected_0_is_a_reserved_word_that_cannot_be_used_here,
                    &[arg],
                );
            }
        }
    }

    fn check_private_identifier(&mut self, node: NodeId) {
        if self.nodes[node].text(self.nodes) == "#constructor" {
            // Report error only if there are no parse errors in file
            if self.file_data().diagnostics.is_empty() {
                let arg = declaration_name_to_string(Some(node), self.nodes);
                self.error_on_node(node, &diagnostics::X_constructor_is_a_reserved_word, &[arg]);
            }
        }
    }

    fn get_strict_mode_identifier_message(
        &mut self,
        node: NodeId,
    ) -> &'static diagnostics::Message {
        // Provide specialized messages to help the user understand why we think they're in
        // strict mode.
        if get_containing_class(node, self.nodes).is_some() {
            return &diagnostics::Identifier_expected_0_is_a_reserved_word_in_strict_mode_Class_definitions_are_automatically_in_strict_mode;
        }
        if self.file_data().external_module_indicator.is_some() {
            return &diagnostics::Identifier_expected_0_is_a_reserved_word_in_strict_mode_Modules_are_automatically_in_strict_mode;
        }
        &diagnostics::Identifier_expected_0_is_a_reserved_word_in_strict_mode
    }

    fn check_strict_mode_function_name(&mut self, node: NodeId) {
        if !self.nodes[node].flags.intersects(NodeFlags::AMBIENT) {
            // It is a SyntaxError if the identifier eval or arguments appears within a FormalParameterList of a strict mode FunctionDeclaration or FunctionExpression (13.1))
            self.check_strict_mode_eval_or_arguments(node, self.nodes[node].name());
        }
    }

    #[allow(dead_code)]
    fn get_strict_mode_block_scope_function_declaration_message(
        &mut self,
        node: NodeId,
    ) -> &'static diagnostics::Message {
        // Provide specialized messages to help the user understand why we think they're in strict mode.
        if get_containing_class(node, self.nodes).is_some() {
            return &diagnostics::Function_declarations_are_not_allowed_inside_blocks_in_strict_mode_when_targeting_ES5_Class_definitions_are_automatically_in_strict_mode;
        }
        if self.file_data().external_module_indicator.is_some() {
            return &diagnostics::Function_declarations_are_not_allowed_inside_blocks_in_strict_mode_when_targeting_ES5_Modules_are_automatically_in_strict_mode;
        }
        &diagnostics::Function_declarations_are_not_allowed_inside_blocks_in_strict_mode_when_targeting_ES5
    }

    fn check_strict_mode_binary_expression(&mut self, node: NodeId) {
        let expr = self.nodes[node].as_binary_expression();
        if expr
            .left
            .is_some_and(|l| is_left_hand_side_expression(&self.nodes[l], self.nodes))
            && self.nodes[expr.operator_token.unwrap()]
                .kind
                .is_assignment_operator()
        {
            // ECMA 262 (Annex C) The identifier eval or arguments may not appear as the LeftHandSideExpression of an
            // Assignment operator(11.13) or of a PostfixExpression(11.3)
            self.check_strict_mode_eval_or_arguments(node, expr.left);
        }
    }

    fn check_strict_mode_catch_clause(&mut self, node: NodeId) {
        // It is a SyntaxError if a TryStatement with a Catch occurs within strict code and the Identifier of the
        // Catch production is eval or arguments
        let clause = self.nodes[node].as_catch_clause();
        if let Some(variable_declaration) = clause.variable_declaration {
            self.check_strict_mode_eval_or_arguments(
                node,
                self.nodes[variable_declaration]
                    .as_variable_declaration()
                    .name,
            );
        }
    }

    fn check_strict_mode_delete_expression(&mut self, node: NodeId) {
        // Grammar checking
        let expr = self.nodes[node].as_delete_expression();
        if expr
            .expression
            .is_some_and(|e| self.nodes[e].kind == Kind::Identifier)
        {
            // When a delete operator occurs within strict mode code, a SyntaxError is thrown if its
            // UnaryExpression is a direct reference to a variable, function argument, or function name
            self.error_on_node(
                expr.expression.unwrap(),
                &diagnostics::X_delete_cannot_be_called_on_an_identifier_in_strict_mode,
                &[],
            );
        }
    }

    fn check_strict_mode_postfix_unary_expression(&mut self, node: NodeId) {
        // Grammar checking
        // The identifier eval or arguments may not appear as the LeftHandSideExpression of an
        // Assignment operator(11.13) or of a PostfixExpression(11.3) or as the UnaryExpression
        // operated upon by a Prefix Increment(11.4.4) or a Prefix Decrement(11.4.5) operator.
        let operand = self.nodes[node].as_postfix_unary_expression().operand;
        self.check_strict_mode_eval_or_arguments(node, operand);
    }

    fn check_strict_mode_prefix_unary_expression(&mut self, node: NodeId) {
        let expr = self.nodes[node].as_prefix_unary_expression();
        if expr.operator == Kind::PlusPlusToken || expr.operator == Kind::MinusMinusToken {
            self.check_strict_mode_eval_or_arguments(node, expr.operand);
        }
    }

    fn check_strict_mode_with_statement(&mut self, node: NodeId) {
        // Grammar checking for withStatement
        self.error_on_first_token(
            node,
            &diagnostics::X_with_statements_are_not_allowed_in_strict_mode,
            &[],
        );
    }

    fn check_strict_mode_labeled_statement(&mut self, node: NodeId) {
        // Grammar checking for labeledStatement
        let data = self.nodes[node].as_labeled_statement();
        if data.statement.is_some_and(|s| {
            is_declaration_statement(&self.nodes[s]) || is_variable_statement(&self.nodes[s])
        }) {
            self.error_on_first_token(
                data.label.unwrap(),
                &diagnostics::A_label_is_not_allowed_here,
                &[],
            );
        }
    }

    fn check_strict_mode_eval_or_arguments(&mut self, context_node: NodeId, name: Option<NodeId>) {
        if let Some(name) = name {
            if is_eval_or_arguments_identifier(&self.nodes[name], self.nodes) {
                // We check first if the name is inside class declaration or class expression; if so give explicit message
                // otherwise report generic error message.
                let message = self.get_strict_mode_eval_or_arguments_message(context_node);
                let arg = self.nodes[name].text(self.nodes).into_owned();
                self.error_on_node(name, message, &[arg]);
            }
        }
    }

    fn get_strict_mode_eval_or_arguments_message(
        &mut self,
        node: NodeId,
    ) -> &'static diagnostics::Message {
        // Provide specialized messages to help the user understand why we think they're in strict mode
        if get_containing_class(node, self.nodes).is_some() {
            return &diagnostics::Code_contained_in_a_class_is_evaluated_in_JavaScript_s_strict_mode_which_does_not_allow_this_use_of_0_For_more_information_see_https_Colon_Slash_Slashdeveloper_mozilla_org_Slashen_US_Slashdocs_SlashWeb_SlashJavaScript_SlashReference_SlashStrict_mode;
        }
        if self.file_data().external_module_indicator.is_some() {
            return &diagnostics::Invalid_use_of_0_Modules_are_automatically_in_strict_mode;
        }
        &diagnostics::Invalid_use_of_0_in_strict_mode
    }

    // All container nodes are kept on a linked list in declaration order. This list is used by
    // the getLocalNameOfContainer function in the type checker to validate that the local name
    // used for a container is unique.
    fn bind_container(&mut self, node: NodeId, container_flags: ContainerFlags) {
        // Before we recurse into a node's children, we first save the existing parent, container
        // and block-container.  Then after we pop out of processing the children, we restore
        // these saved values.
        let save_container = self.container;
        let save_this_container = self.this_container;
        let saved_block_scope_container = self.block_scope_container;
        // Depending on what kind of node this is, we may have to adjust the current container
        // and block-container.   If the current node is a container, then it is automatically
        // considered the current block-container as well.  Also, for containers that we know
        // may contain locals, we eagerly initialize the .locals field. We do this because
        // it's highly likely that the .locals will be needed to place some child in (for example,
        // a parameter, or variable declaration).
        //
        // However, we do not proactively create the .locals for block-containers because it's
        // totally normal and common for block-containers to never actually have a block-scoped
        // variable in them.  We don't want to end up allocating an object for every 'block' we
        // run into when most of them won't be necessary.
        //
        // Finally, if this is a block-container, then we clear out any existing .locals object
        // it may contain within it.  This happens in incremental scenarios.  Because we can be
        // reusing a node from a previous compilation, that node may have had 'locals' created
        // for it.  We must clear this so we don't accidentally move any stale data forward from
        // a previous compilation.
        // PORT: locals tables are inline in the arena (`LocalsContainerBase`),
        // so there is no map allocation to skip; incremental re-binding of a
        // node is not yet a scenario in this port.
        if container_flags & CONTAINER_FLAGS_IS_CONTAINER != 0 {
            self.container = Some(node);
            self.block_scope_container = Some(node);
            if container_flags & CONTAINER_FLAGS_HAS_LOCALS != 0 {
                self.add_to_container_chain(node);
            }
        } else if container_flags & CONTAINER_FLAGS_IS_BLOCK_SCOPED_CONTAINER != 0 {
            self.block_scope_container = Some(node);
            self.add_to_container_chain(node);
        }
        if container_flags & CONTAINER_FLAGS_IS_THIS_CONTAINER != 0 {
            self.this_container = Some(node);
        }
        if container_flags & CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER != 0 {
            let save_current_flow = self.current_flow;
            let save_break_target = self.current_break_target;
            let save_continue_target = self.current_continue_target;
            let save_return_target = self.current_return_target;
            let save_exception_target = self.current_exception_target;
            // Go: `saveActiveLabelList := b.activeLabelList` …
            // `b.activeLabelList = nil` … `b.activeLabelList = saveActiveLabelList`
            // — swap the whole list out so labels bound inside the container
            // don't leak and outer labels stay invisible to inner lookups.
            let save_active_label_list = std::mem::take(&mut self.active_labels);
            let save_has_explicit_return = self.has_explicit_return;
            let save_seen_this_keyword = self.seen_this_keyword;
            let is_immediately_invoked = (container_flags & CONTAINER_FLAGS_IS_FUNCTION_EXPRESSION
                != 0
                && !has_syntactic_modifier(&self.nodes[node], ModifierFlags::ASYNC)
                && !is_generator_function_expression(&self.nodes[node])
                && get_immediately_invoked_function_expression(node, self.nodes).is_some())
                || self.nodes[node].kind == Kind::ClassStaticBlockDeclaration;
            // A non-async, non-generator IIFE is considered part of the containing control flow. Return statements behave
            // similarly to break statements that exit to a label just past the statement body.
            if !is_immediately_invoked {
                let flow_start = self.new_flow_node(tsc_ast::FlowFlags::START);
                self.current_flow = Some(flow_start);
                if container_flags
                    & (CONTAINER_FLAGS_IS_FUNCTION_EXPRESSION
                        | CONTAINER_FLAGS_IS_OBJECT_LITERAL_OR_CLASS_EXPRESSION_METHOD_OR_ACCESSOR)
                    != 0
                {
                    self.flow_nodes[flow_start.index()].node = Some(node);
                }
            }
            // We create a return control flow graph for IIFEs and constructors. For constructors
            // we use the return control flow graph in strict property initialization checks.
            if is_immediately_invoked || self.nodes[node].kind == Kind::Constructor {
                self.current_return_target =
                    Some(self.new_flow_node(tsc_ast::FlowFlags::BRANCH_LABEL));
            } else {
                self.current_return_target = None;
            }
            self.current_exception_target = None;
            self.current_break_target = None;
            self.current_continue_target = None;
            self.has_explicit_return = false;
            self.seen_this_keyword = false;
            self.bind_children(node);
            // Reset flags (for incremental scenarios)
            self.nodes[node]
                .flags
                .remove(NodeFlags::REACHABILITY_AND_EMIT_FLAGS | NodeFlags::CONTAINS_THIS);
            if !self.current_flow_is_unreachable()
                && container_flags & CONTAINER_FLAGS_IS_FUNCTION_LIKE != 0
            {
                let body = self.nodes[node].body_data().and_then(|d| d.body);
                if node_is_present(body, self.nodes) {
                    self.nodes[node]
                        .flags
                        .insert(NodeFlags::HAS_IMPLICIT_RETURN);
                    if self.has_explicit_return {
                        self.nodes[node]
                            .flags
                            .insert(NodeFlags::HAS_EXPLICIT_RETURN);
                    }
                    self.nodes[node]
                        .data
                        .body_data_mut()
                        .expect("BodyData")
                        .end_flow_node = self.current_flow;
                }
            }
            if self.seen_this_keyword {
                self.nodes[node].flags.insert(NodeFlags::CONTAINS_THIS);
            }
            if self.nodes[node].kind == Kind::SourceFile {
                self.nodes[node].flags.insert(self.emit_flags);
            }
            if let Some(return_target) = self.current_return_target {
                self.add_antecedent(return_target, self.current_flow);
                self.current_flow = Some(self.finish_flow_label(return_target));
                if self.nodes[node].kind == Kind::Constructor
                    || self.nodes[node].kind == Kind::ClassStaticBlockDeclaration
                {
                    self.set_return_flow_node(node, self.current_flow);
                }
            }
            if !is_immediately_invoked {
                self.current_flow = save_current_flow;
            }
            self.current_break_target = save_break_target;
            self.current_continue_target = save_continue_target;
            self.current_return_target = save_return_target;
            self.current_exception_target = save_exception_target;
            self.active_labels = save_active_label_list;
            self.has_explicit_return = save_has_explicit_return;
            if container_flags & CONTAINER_FLAGS_PROPAGATES_THIS_KEYWORD != 0 {
                self.seen_this_keyword = save_seen_this_keyword || self.seen_this_keyword;
            } else {
                self.seen_this_keyword = save_seen_this_keyword;
            }
        } else if container_flags & CONTAINER_FLAGS_IS_INTERFACE != 0 {
            let save_seen_this_keyword = self.seen_this_keyword;
            self.seen_this_keyword = false;
            self.bind_children(node);
            // ContainsThis cannot overlap with HasExtendedUnicodeEscape on Identifier
            if self.seen_this_keyword {
                self.nodes[node].flags.insert(NodeFlags::CONTAINS_THIS);
            } else {
                self.nodes[node].flags.remove(NodeFlags::CONTAINS_THIS);
            }
            self.seen_this_keyword = save_seen_this_keyword;
        } else {
            self.bind_children(node);
        }
        if is_source_file(&self.nodes[node]) && is_in_js_file(Some(node), self.nodes) {
            // Binding of top-level JSTypeAliasDeclaration nodes is deferred to ensure CommonJS module
            // indicators, if any, are processed first.
            let statements: Vec<NodeId> = self.nodes[node].statements().unwrap_or(&[]).to_vec();
            for statement in statements {
                if is_js_type_alias_declaration(&self.nodes[statement]) {
                    self.bind_block_scoped_declaration(
                        statement,
                        SymbolFlags::TYPE_ALIAS,
                        SymbolFlags::TYPE_ALIAS_EXCLUDES,
                    );
                }
            }
            if self.file_data().common_js_module_indicator.is_some() {
                self.declare_commonjs_variable("module");
                self.declare_commonjs_variable("exports");
            }
        }
        if is_source_file(&self.nodes[node])
            && is_external_or_commonjs_module(self.nodes[node].as_source_file())
            || is_ambient_module(&self.nodes[node], self.nodes)
        {
            let symbol = self.nodes[node].symbol().expect("module symbol");
            self.bind_commonjs_type_exports(symbol);
        }
        self.container = save_container;
        self.this_container = save_this_container;
        self.block_scope_container = saved_block_scope_container;
    }

    /// `b.currentFlow.Flags&FlowFlagsUnreachable != 0` — a `None` current flow
    /// is treated as reachable (Go would nil-deref, but `currentFlow` is
    /// always set inside `IsControlFlowContainer` before `bindChildren` runs).
    fn current_flow_is_unreachable(&self) -> bool {
        self.current_flow.is_some_and(|f| {
            self.flow_nodes[f.index()]
                .flags
                .intersects(tsc_ast::FlowFlags::UNREACHABLE)
        })
    }

    fn declare_commonjs_variable(&mut self, name: &str) {
        let locals = SymbolTableDest::Locals(self.file);
        if self.table_get(locals, name).is_none() {
            let symbol = self.new_symbol(
                SymbolFlags::FUNCTION_SCOPED_VARIABLE | SymbolFlags::MODULE_EXPORTS,
                name.to_string(),
            );
            self.symbols[symbol.index()].declarations = vec![self.file];
            self.symbols[symbol.index()].value_declaration = Some(self.file);
            if name == "module" {
                let exports_property = self.new_symbol(
                    SymbolFlags::MODULE_EXPORTS | SymbolFlags::PROPERTY,
                    "exports".to_string(),
                );
                self.symbols[exports_property.index()].declarations =
                    self.symbols[symbol.index()].declarations.clone();
                self.symbols[exports_property.index()].value_declaration =
                    self.symbols[symbol.index()].value_declaration;
                self.symbols[exports_property.index()].parent = Some(symbol);
                self.symbols[symbol.index()]
                    .members
                    .set(Arc::from("exports"), exports_property);
            }
            self.table_set(locals, name.to_string(), symbol);
        }
    }

    fn bind_children(&mut self, node: NodeId) {
        let save_in_assignment_pattern = self.in_assignment_pattern;
        // Most nodes aren't valid in an assignment pattern, so we clear the value here
        // and set it before we descend into nodes that could actually be part of an assignment pattern.
        self.in_assignment_pattern = false;

        if self.current_flow == Some(self.unreachable_flow) {
            if let Some(flow_node_data) = self.nodes[node].data.flow_node_data_mut() {
                flow_node_data.flow_node = None;
            }
            if is_potentially_executable_node(&self.nodes[node], self.nodes) {
                self.nodes[node].flags.insert(NodeFlags::UNREACHABLE);
            }
            self.bind_each_child(node);
            self.in_assignment_pattern = save_in_assignment_pattern;
            return;
        }

        if Kind::FIRST_STATEMENT <= self.nodes[node].kind
            && self.nodes[node].kind <= Kind::LAST_STATEMENT
        {
            if let Some(flow_node_data) = self.nodes[node].data.flow_node_data_mut() {
                flow_node_data.flow_node = self.current_flow;
            }
        }

        match self.nodes[node].kind {
            Kind::WhileStatement => self.bind_while_statement(node),
            Kind::DoStatement => self.bind_do_statement(node),
            Kind::ForStatement => self.bind_for_statement(node),
            Kind::ForInStatement | Kind::ForOfStatement => {
                self.bind_for_in_or_for_of_statement(node)
            }
            Kind::IfStatement => self.bind_if_statement(node),
            Kind::ReturnStatement => self.bind_return_statement(node),
            Kind::ThrowStatement => self.bind_throw_statement(node),
            Kind::BreakStatement => self.bind_break_statement(node),
            Kind::ContinueStatement => self.bind_continue_statement(node),
            Kind::TryStatement => self.bind_try_statement(node),
            Kind::SwitchStatement => self.bind_switch_statement(node),
            Kind::CaseBlock => self.bind_case_block(node),
            Kind::CaseClause | Kind::DefaultClause => self.bind_case_or_default_clause(node),
            Kind::ExpressionStatement => self.bind_expression_statement(node),
            Kind::LabeledStatement => self.bind_labeled_statement(node),
            Kind::PrefixUnaryExpression => self.bind_prefix_unary_expression_flow(node),
            Kind::PostfixUnaryExpression => self.bind_postfix_unary_expression_flow(node),
            Kind::BinaryExpression => {
                if is_destructuring_assignment(&self.nodes[node], self.nodes) {
                    // Carry over whether we are in an assignment pattern to
                    // binary expressions that could actually be an initializer
                    self.in_assignment_pattern = save_in_assignment_pattern;
                    self.bind_destructuring_assignment_flow(node);
                    self.in_assignment_pattern = save_in_assignment_pattern;
                    return;
                }
                self.bind_binary_expression_flow(node);
            }
            Kind::DeleteExpression => self.bind_delete_expression_flow(node),
            Kind::ConditionalExpression => self.bind_conditional_expression_flow(node),
            Kind::VariableDeclaration => self.bind_variable_declaration_flow(node),
            Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
                self.bind_access_expression_flow(node)
            }
            Kind::CallExpression => self.bind_call_expression_flow(node),
            Kind::NonNullExpression => self.bind_non_null_expression_flow(node),
            Kind::SourceFile => {
                let statements = self.nodes[node].as_source_file().statements.clone();
                self.bind_each_statement_functions_first(statements.as_ref());
                let end_of_file_token = self.nodes[node].as_source_file().end_of_file_token;
                self.bind(end_of_file_token);
            }
            Kind::Block | Kind::ModuleBlock => {
                let statements = self.nodes[node].statement_list().cloned();
                self.bind_each_statement_functions_first(statements.as_ref());
            }
            Kind::BindingElement => self.bind_binding_element_flow(node),
            Kind::Parameter => self.bind_parameter_flow(node),
            Kind::ObjectLiteralExpression
            | Kind::ArrayLiteralExpression
            | Kind::PropertyAssignment
            | Kind::SpreadElement => {
                self.in_assignment_pattern = save_in_assignment_pattern;
                self.bind_each_child(node);
            }
            _ => self.bind_each_child(node),
        }
        self.in_assignment_pattern = save_in_assignment_pattern;
    }

    fn bind_each_child(&mut self, node: NodeId) {
        // Go: `node.ForEachChild(b.bindFunc)`. `for_each_child` needs `&[Node]`
        // while `bind` needs `&mut`, so children are collected into a scratch
        // buffer first.
        let mut children = std::mem::take(&mut self.child_scratch);
        children.clear();
        self.nodes[node].for_each_child(self.nodes, &mut |child| {
            children.push(child);
            false
        });
        for child in children.iter().copied() {
            self.bind(Some(child));
        }
        children.clear();
        self.child_scratch = children;
    }

    fn bind_each(&mut self, nodes: &[NodeId]) {
        for &node in nodes {
            self.bind(Some(node));
        }
    }

    fn bind_node_list(&mut self, node_list: Option<&NodeList>) {
        if let Some(node_list) = node_list {
            let nodes = node_list.nodes.clone();
            self.bind_each(&nodes);
        }
    }

    fn bind_modifiers(&mut self, modifiers: Option<ModifierList>) {
        if let Some(modifiers) = modifiers {
            let nodes = modifiers.nodes.to_vec();
            self.bind_each(&nodes);
        }
    }

    fn bind_each_statement_functions_first(&mut self, statements: Option<&NodeList>) {
        let Some(statements) = statements else {
            return;
        };
        let nodes = statements.nodes.clone();
        for &node in nodes.iter() {
            if self.nodes[node].kind == Kind::FunctionDeclaration {
                self.bind(Some(node));
            }
        }
        for &node in nodes.iter() {
            if self.nodes[node].kind != Kind::FunctionDeclaration {
                self.bind(Some(node));
            }
        }
    }

    fn set_continue_target(&mut self, node: NodeId, target: FlowNodeId) -> FlowNodeId {
        let mut node = node;
        for label in self.active_labels.iter_mut().rev() {
            if self.nodes[node]
                .parent
                .is_some_and(|p| self.nodes[p].kind == Kind::LabeledStatement)
            {
                label.continue_target = Some(target);
                node = self.nodes[node].parent.unwrap();
            } else {
                break;
            }
        }
        target
    }

    fn do_with_conditional_branches(
        &mut self,
        action: fn(&mut Self, Option<NodeId>) -> bool,
        value: Option<NodeId>,
        true_target: FlowNodeId,
        false_target: FlowNodeId,
    ) {
        let saved_true_target = self.current_true_target;
        let saved_false_target = self.current_false_target;
        self.current_true_target = Some(true_target);
        self.current_false_target = Some(false_target);
        action(self, value);
        self.current_true_target = saved_true_target;
        self.current_false_target = saved_false_target;
    }

    /// `bindCondition` — the `doWithConditionalBranches(b.bindFunc, ...)`
    /// caller is inlined here since it is the only one.
    fn bind_condition(
        &mut self,
        node: Option<NodeId>,
        true_target: FlowNodeId,
        false_target: FlowNodeId,
    ) {
        self.do_with_conditional_branches(Binder::bind, node, true_target, false_target);
        if node.is_none()
            || !node.is_some_and(|n| is_logical_assignment_expression(n, self.nodes))
                && !is_logical_expression(node.unwrap(), self.nodes)
                && !(is_optional_chain(&self.nodes[node.unwrap()])
                    && is_outermost_optional_chain(&self.nodes[node.unwrap()], self.nodes))
        {
            let current_flow = self.current_flow.expect("current flow");
            let true_condition =
                self.create_flow_condition(tsc_ast::FlowFlags::TRUE_CONDITION, current_flow, node);
            self.add_antecedent(true_target, Some(true_condition));
            let current_flow = self.current_flow.expect("current flow");
            let false_condition =
                self.create_flow_condition(tsc_ast::FlowFlags::FALSE_CONDITION, current_flow, node);
            self.add_antecedent(false_target, Some(false_condition));
        }
    }

    fn bind_iterative_statement(
        &mut self,
        node: Option<NodeId>,
        break_target: FlowNodeId,
        continue_target: FlowNodeId,
    ) {
        let save_break_target = self.current_break_target;
        let save_continue_target = self.current_continue_target;
        self.current_break_target = Some(break_target);
        self.current_continue_target = Some(continue_target);
        self.bind(node);
        self.current_break_target = save_break_target;
        self.current_continue_target = save_continue_target;
    }

    fn bind_assignment_target_flow(&mut self, node: NodeId) {
        match self.nodes[node].kind {
            Kind::ArrayLiteralExpression => {
                let elements: Vec<NodeId> = self.nodes[node].elements().unwrap_or(&[]).to_vec();
                for e in elements {
                    if self.nodes[e].kind == Kind::SpreadElement {
                        let expr = self.nodes[e].expression();
                        if let Some(expr) = expr {
                            self.bind_assignment_target_flow(expr);
                        }
                    } else {
                        self.bind_destructuring_target_flow(e);
                    }
                }
            }
            Kind::ObjectLiteralExpression => {
                let properties: Vec<NodeId> = self.nodes[node].properties().unwrap_or(&[]).to_vec();
                for p in properties {
                    match self.nodes[p].kind {
                        Kind::PropertyAssignment => {
                            if let Some(init) = self.nodes[p].initializer() {
                                self.bind_destructuring_target_flow(init);
                            }
                        }
                        Kind::ShorthandPropertyAssignment => {
                            let name = self.nodes[p].name();
                            if let Some(name) = name {
                                self.bind_assignment_target_flow(name);
                            }
                        }
                        Kind::SpreadAssignment => {
                            let expr = self.nodes[p].expression();
                            if let Some(expr) = expr {
                                self.bind_assignment_target_flow(expr);
                            }
                        }
                        _ => {}
                    }
                }
            }
            _ => {
                if self.is_narrowable_reference(node) {
                    let current_flow = self.current_flow.expect("current flow");
                    self.current_flow = Some(self.create_flow_mutation(
                        tsc_ast::FlowFlags::ASSIGNMENT,
                        current_flow,
                        node,
                    ));
                }
            }
        }
    }

    fn bind_destructuring_target_flow(&mut self, node: NodeId) {
        if is_binary_expression(&self.nodes[node])
            && self.nodes[self.nodes[node]
                .as_binary_expression()
                .operator_token
                .unwrap()]
            .kind
                == Kind::EqualsToken
        {
            let left = self.nodes[node].as_binary_expression().left.unwrap();
            self.bind_assignment_target_flow(left);
        } else {
            self.bind_assignment_target_flow(node);
        }
    }

    fn bind_while_statement(&mut self, node: NodeId) {
        let (expression, statement) = {
            let stmt = self.nodes[node].as_while_statement();
            (stmt.expression, stmt.iteration_statement_base.statement)
        };
        let pre_while_label = self.create_loop_label();
        let pre_while_label = self.set_continue_target(node, pre_while_label);
        let pre_body_label = self.create_branch_label();
        let post_while_label = self.create_branch_label();
        let current_flow = self.current_flow;
        self.add_antecedent(pre_while_label, current_flow);
        self.current_flow = Some(pre_while_label);
        self.bind_condition(expression, pre_body_label, post_while_label);
        self.current_flow = Some(self.finish_flow_label(pre_body_label));
        self.bind_iterative_statement(statement, post_while_label, pre_while_label);
        let current_flow = self.current_flow;
        self.add_antecedent(pre_while_label, current_flow);
        self.current_flow = Some(self.finish_flow_label(post_while_label));
    }

    fn bind_do_statement(&mut self, node: NodeId) {
        let (expression, statement) = {
            let stmt = self.nodes[node].as_do_statement();
            (stmt.expression, stmt.iteration_statement_base.statement)
        };
        let pre_do_label = self.create_loop_label();
        let pre_condition_label = self.create_branch_label();
        let pre_condition_label = self.set_continue_target(node, pre_condition_label);
        let post_do_label = self.create_branch_label();
        let current_flow = self.current_flow;
        self.add_antecedent(pre_do_label, current_flow);
        self.current_flow = Some(pre_do_label);
        self.bind_iterative_statement(statement, post_do_label, pre_condition_label);
        let current_flow = self.current_flow;
        self.add_antecedent(pre_condition_label, current_flow);
        self.current_flow = Some(self.finish_flow_label(pre_condition_label));
        self.bind_condition(expression, pre_do_label, post_do_label);
        self.current_flow = Some(self.finish_flow_label(post_do_label));
    }

    fn bind_for_statement(&mut self, node: NodeId) {
        let (initializer, condition, statement, incrementor) = {
            let stmt = self.nodes[node].as_for_statement();
            (
                stmt.initializer,
                stmt.condition,
                stmt.iteration_statement_base.statement,
                stmt.incrementor,
            )
        };
        self.bind(initializer);
        if self.current_flow == Some(self.unreachable_flow) {
            // Unlike while/do, the for-loop initializer is bound inside this function before the loop's
            // flow graph is constructed. If it makes flow unreachable (e.g. a throwing IIFE), addAntecedent
            // will filter out the unreachable entry to preLoopLabel, leaving only the back-edge from the
            // incrementor. This creates a cycle with no exit that crashes isReachableFlowNodeWorker.
            // Bail out early and just bind the remaining children with unreachable flow.
            self.bind(condition);
            self.bind(statement);
            self.bind(incrementor);
            return;
        }
        let pre_loop_label = self.create_loop_label();
        let pre_loop_label = self.set_continue_target(node, pre_loop_label);
        let pre_body_label = self.create_branch_label();
        let pre_incrementor_label = self.create_branch_label();
        let post_loop_label = self.create_branch_label();
        let current_flow = self.current_flow;
        self.add_antecedent(pre_loop_label, current_flow);
        self.current_flow = Some(pre_loop_label);
        self.bind_condition(condition, pre_body_label, post_loop_label);
        self.current_flow = Some(self.finish_flow_label(pre_body_label));
        self.bind_iterative_statement(statement, post_loop_label, pre_incrementor_label);
        let current_flow = self.current_flow;
        self.add_antecedent(pre_incrementor_label, current_flow);
        self.current_flow = Some(self.finish_flow_label(pre_incrementor_label));
        self.bind(incrementor);
        let current_flow = self.current_flow;
        self.add_antecedent(pre_loop_label, current_flow);
        self.current_flow = Some(self.finish_flow_label(post_loop_label));
    }

    fn bind_for_in_or_for_of_statement(&mut self, node: NodeId) {
        let (expression, await_modifier, initializer, statement) = {
            let stmt = self.nodes[node].as_for_in_or_of_statement();
            (
                stmt.expression,
                stmt.await_modifier,
                stmt.initializer,
                stmt.statement,
            )
        };
        self.bind(expression);
        if self.current_flow == Some(self.unreachable_flow) {
            // Like the for-loop initializer, the for-in/for-of expression is bound before the loop's
            // flow graph is constructed. If it makes flow unreachable (e.g. a throwing IIFE), addAntecedent
            // will filter out the unreachable entry to preLoopLabel, leaving only the back-edge from the
            // loop body. This creates a cycle with no exit that crashes isReachableFlowNodeWorker.
            // Bail out early and just bind the remaining children with unreachable flow.
            self.bind(initializer);
            self.bind(statement);
            return;
        }
        let pre_loop_label = self.create_loop_label();
        let pre_loop_label = self.set_continue_target(node, pre_loop_label);
        let post_loop_label = self.create_branch_label();
        let current_flow = self.current_flow;
        self.add_antecedent(pre_loop_label, current_flow);
        self.current_flow = Some(pre_loop_label);
        if self.nodes[node].kind == Kind::ForOfStatement {
            self.bind(await_modifier);
        }
        let current_flow = self.current_flow;
        self.add_antecedent(post_loop_label, current_flow);
        self.bind(initializer);
        if initializer.is_some_and(|i| self.nodes[i].kind != Kind::VariableDeclarationList) {
            self.bind_assignment_target_flow(initializer.unwrap());
        }
        self.bind_iterative_statement(statement, post_loop_label, pre_loop_label);
        let current_flow = self.current_flow;
        self.add_antecedent(pre_loop_label, current_flow);
        self.current_flow = Some(self.finish_flow_label(post_loop_label));
    }

    fn bind_if_statement(&mut self, node: NodeId) {
        let (expression, then_statement, else_statement) = {
            let stmt = self.nodes[node].as_if_statement();
            (stmt.expression, stmt.then_statement, stmt.else_statement)
        };
        let then_label = self.create_branch_label();
        let else_label = self.create_branch_label();
        let post_if_label = self.create_branch_label();
        self.bind_condition(expression, then_label, else_label);
        self.current_flow = Some(self.finish_flow_label(then_label));
        self.bind(then_statement);
        let current_flow = self.current_flow;
        self.add_antecedent(post_if_label, current_flow);
        self.current_flow = Some(self.finish_flow_label(else_label));
        self.bind(else_statement);
        let current_flow = self.current_flow;
        self.add_antecedent(post_if_label, current_flow);
        self.current_flow = Some(self.finish_flow_label(post_if_label));
    }

    fn bind_return_statement(&mut self, node: NodeId) {
        let expression = self.nodes[node].expression();
        self.bind(expression);
        if let Some(return_target) = self.current_return_target {
            self.add_antecedent(return_target, self.current_flow);
        }
        self.current_flow = Some(self.unreachable_flow);
        self.has_explicit_return = true;
        self.has_flow_effects = true;
    }

    fn bind_throw_statement(&mut self, node: NodeId) {
        let expression = self.nodes[node].expression();
        self.bind(expression);
        self.current_flow = Some(self.unreachable_flow);
        self.has_flow_effects = true;
    }

    fn bind_break_statement(&mut self, node: NodeId) {
        let label = self.nodes[node].label();
        let target = self.current_break_target;
        self.bind_break_or_continue_statement(label, target, |l| l.break_target);
    }

    fn bind_continue_statement(&mut self, node: NodeId) {
        let label = self.nodes[node].label();
        let target = self.current_continue_target;
        self.bind_break_or_continue_statement(label, target, |l| l.continue_target);
    }

    fn bind_break_or_continue_statement(
        &mut self,
        label: Option<NodeId>,
        current_target: Option<FlowNodeId>,
        get_target: fn(&ActiveLabel) -> Option<FlowNodeId>,
    ) {
        self.bind(label);
        if let Some(label) = label {
            let name = self.nodes[label].text(self.nodes).into_owned();
            if let Some(index) = self.find_active_label(&name) {
                self.active_labels[index].referenced = true;
                let target = get_target(&self.active_labels[index]);
                self.bind_break_or_continue_flow(target);
            }
        } else {
            self.bind_break_or_continue_flow(current_target);
        }
    }

    /// `findActiveLabel` — returns the stack index of the label (top-down).
    fn find_active_label(&self, name: &str) -> Option<usize> {
        self.active_labels
            .iter()
            .rposition(|label| label.name == name)
    }

    fn bind_break_or_continue_flow(&mut self, flow_label: Option<FlowNodeId>) {
        if let Some(flow_label) = flow_label {
            self.add_antecedent(flow_label, self.current_flow);
            self.current_flow = Some(self.unreachable_flow);
            self.has_flow_effects = true;
        }
    }

    fn bind_try_statement(&mut self, node: NodeId) {
        // We conservatively assume that *any* code in the try block can cause an exception, but we only need
        // to track code that causes mutations (because only mutations widen the possible control flow type of
        // a variable). The exceptionLabel is the target label for control flows that result from exceptions.
        // We add all mutation flow nodes as antecedents of this label such that we can analyze them as possible
        // antecedents of the start of catch or finally blocks. Furthermore, we add the current control flow to
        // represent exceptions that occur before any mutations.
        let (try_block, catch_clause, finally_block) = {
            let stmt = self.nodes[node].as_try_statement();
            (stmt.try_block, stmt.catch_clause, stmt.finally_block)
        };
        let save_return_target = self.current_return_target;
        let save_exception_target = self.current_exception_target;
        let normal_exit_label = self.create_branch_label();
        let return_label = self.create_branch_label();
        let mut exception_label = self.create_branch_label();
        if finally_block.is_some() {
            self.current_return_target = Some(return_label);
        }
        let current_flow = self.current_flow;
        self.add_antecedent(exception_label, current_flow);
        self.current_exception_target = Some(exception_label);
        self.bind(try_block);
        let current_flow = self.current_flow;
        self.add_antecedent(normal_exit_label, current_flow);
        if catch_clause.is_some() {
            // Start of catch clause is the target of exceptions from try block.
            self.current_flow = Some(self.finish_flow_label(exception_label));
            // The currentExceptionTarget now represents control flows from exceptions in the catch clause.
            // Effectively, in a try-catch-finally, if an exception occurs in the try block, the catch block
            // acts like a second try block.
            exception_label = self.create_branch_label();
            let current_flow = self.current_flow;
            self.add_antecedent(exception_label, current_flow);
            self.current_exception_target = Some(exception_label);
            self.bind(catch_clause);
            let current_flow = self.current_flow;
            self.add_antecedent(normal_exit_label, current_flow);
        }
        self.current_return_target = save_return_target;
        self.current_exception_target = save_exception_target;
        if finally_block.is_some() {
            // Possible ways control can reach the finally block:
            // 1) Normal completion of try block of a try-finally or try-catch-finally
            // 2) Normal completion of catch block (following exception in try block) of a try-catch-finally
            // 3) Return in try or catch block of a try-finally or try-catch-finally
            // 4) Exception in try block of a try-finally
            // 5) Exception in catch block of a try-catch-finally
            // When analyzing a control flow graph that starts inside a finally block we want to consider all
            // five possibilities above. However, when analyzing a control flow graph that starts outside (past)
            // the finally block, we only want to consider the first two (if we're past a finally block then it
            // must have completed normally). Likewise, when analyzing a control flow graph from return statements
            // in try or catch blocks in an IIFE, we only want to consider the third. To make this possible, we
            // inject a ReduceLabel node into the control flow graph. This node contains an alternate reduced
            // set of antecedents for the pre-finally label. As control flow analysis passes by a ReduceLabel
            // node, the pre-finally label is temporarily switched to the reduced antecedent set.
            let finally_label = self.create_branch_label();
            let normal_antecedents = self.flow_nodes[normal_exit_label.index()].antecedents;
            let exception_antecedents = self.flow_nodes[exception_label.index()].antecedents;
            let return_antecedents = self.flow_nodes[return_label.index()].antecedents;
            let inner = self.combine_flow_lists(exception_antecedents, return_antecedents);
            let combined = self.combine_flow_lists(normal_antecedents, inner);
            self.flow_nodes[finally_label.index()].antecedents = combined;
            self.current_flow = Some(finally_label);
            self.bind(finally_block);
            if self.current_flow_is_unreachable() {
                // If the end of the finally block is unreachable, the end of the entire try statement is unreachable.
                self.current_flow = Some(self.unreachable_flow);
            } else {
                // If we have an IIFE return target and return statements in the try or catch blocks, add a control
                // flow that goes back through the finally block and back through only the return statements.
                if self.current_return_target.is_some() && return_antecedents.is_some() {
                    let return_target = self.current_return_target.unwrap();
                    let reduced = self.create_reduce_label(
                        finally_label,
                        return_antecedents,
                        self.current_flow.unwrap(),
                    );
                    self.add_antecedent(return_target, Some(reduced));
                }
                // If we have an outer exception target (i.e. a containing try-finally or try-catch-finally), add a
                // control flow that goes back through the finally block and back through each possible exception source.
                if self.current_exception_target.is_some() && exception_antecedents.is_some() {
                    let exception_target = self.current_exception_target.unwrap();
                    let reduced = self.create_reduce_label(
                        finally_label,
                        exception_antecedents,
                        self.current_flow.unwrap(),
                    );
                    self.add_antecedent(exception_target, Some(reduced));
                }
                // If the end of the finally block is reachable, but the end of the try and catch blocks are not,
                // convert the current flow to unreachable. For example, 'try { return 1; } finally { ... }' should
                // result in an unreachable current control flow.
                if normal_antecedents.is_some() {
                    self.current_flow = Some(self.create_reduce_label(
                        finally_label,
                        normal_antecedents,
                        self.current_flow.unwrap(),
                    ));
                } else {
                    self.current_flow = Some(self.unreachable_flow);
                }
            }
        } else {
            self.current_flow = Some(self.finish_flow_label(normal_exit_label));
        }
    }

    fn bind_switch_statement(&mut self, node: NodeId) {
        let (expression, case_block) = {
            let stmt = self.nodes[node].as_switch_statement();
            (stmt.expression, stmt.case_block)
        };
        let post_switch_label = self.create_branch_label();
        self.bind(expression);
        let save_break_target = self.current_break_target;
        let save_pre_switch_case_flow = self.pre_switch_case_flow;
        self.current_break_target = Some(post_switch_label);
        self.pre_switch_case_flow = self.current_flow;
        self.bind(case_block);
        let current_flow = self.current_flow;
        self.add_antecedent(post_switch_label, current_flow);
        let has_default = case_block.is_some_and(|cb| {
            self.nodes[cb]
                .as_case_block()
                .clauses
                .as_ref()
                .is_some_and(|clauses| {
                    clauses
                        .nodes
                        .iter()
                        .any(|c| self.nodes[*c].kind == Kind::DefaultClause)
                })
        });
        if !has_default {
            let pre_switch_case_flow = self.pre_switch_case_flow.unwrap();
            let switch_clause = self.create_flow_switch_clause(pre_switch_case_flow, node, 0, 0);
            self.add_antecedent(post_switch_label, Some(switch_clause));
        }
        self.current_break_target = save_break_target;
        self.pre_switch_case_flow = save_pre_switch_case_flow;
        self.current_flow = Some(self.finish_flow_label(post_switch_label));
    }

    fn bind_case_block(&mut self, node: NodeId) {
        let switch_statement = self.nodes[node].parent.unwrap();
        let clauses: Vec<NodeId> = self.nodes[node]
            .as_case_block()
            .clauses
            .as_ref()
            .map_or_else(Vec::new, |c| c.nodes.to_vec());
        let switch_expression = self.nodes[switch_statement].expression().unwrap();
        let is_narrowing_switch = self.nodes[switch_expression].kind == Kind::TrueKeyword
            || self.is_narrowing_expression(switch_expression);
        let mut fallthrough_flow = self.unreachable_flow;
        let mut i = 0;
        while i < clauses.len() {
            let clause_start = i;
            while self.nodes[clauses[i]]
                .statements()
                .unwrap_or(&[])
                .is_empty()
                && i + 1 < clauses.len()
            {
                if fallthrough_flow == self.unreachable_flow {
                    self.current_flow = self.pre_switch_case_flow;
                }
                self.bind(Some(clauses[i]));
                i += 1;
            }
            let pre_case_label = self.create_branch_label();
            let mut pre_case_flow = self.pre_switch_case_flow.unwrap();
            if is_narrowing_switch {
                pre_case_flow = self.create_flow_switch_clause(
                    pre_case_flow,
                    switch_statement,
                    clause_start as i32,
                    (i + 1) as i32,
                );
            }
            self.add_antecedent(pre_case_label, Some(pre_case_flow));
            self.add_antecedent(pre_case_label, Some(fallthrough_flow));
            self.current_flow = Some(self.finish_flow_label(pre_case_label));
            let clause = clauses[i];
            self.bind(Some(clause));
            fallthrough_flow = self.current_flow.unwrap_or(self.unreachable_flow);
            if !self.current_flow_is_unreachable() && i != clauses.len() - 1 {
                self.nodes[clause]
                    .as_case_or_default_clause_mut()
                    .fallthrough_flow_node = self.current_flow;
            }
            i += 1;
        }
    }

    fn bind_case_or_default_clause(&mut self, node: NodeId) {
        let (expression, statements) = {
            let clause = self.nodes[node].as_case_or_default_clause();
            (clause.expression, clause.statements.clone())
        };
        if let Some(expression) = expression {
            let save_current_flow = self.current_flow;
            self.current_flow = self.pre_switch_case_flow;
            self.bind(Some(expression));
            self.current_flow = save_current_flow;
        }
        if let Some(statements) = statements {
            self.bind_each(&statements.nodes);
        }
    }

    fn bind_expression_statement(&mut self, node: NodeId) {
        let expression = self.nodes[node].as_expression_statement().expression;
        self.bind(expression);
        if let Some(expression) = expression {
            self.maybe_bind_expression_flow_if_call(expression);
        }
    }

    fn maybe_bind_expression_flow_if_call(&mut self, node: NodeId) {
        // A top level or comma expression call expression with a dotted function name and at least one argument
        // is potentially an assertion and is therefore included in the control flow.
        if is_call_expression(&self.nodes[node]) {
            let expression = self.nodes[node].expression();
            if expression.is_some_and(|e| {
                self.nodes[e].kind != Kind::SuperKeyword
                    && is_dotted_name(&self.nodes[e], self.nodes)
            }) {
                let current_flow = self.current_flow.expect("current flow");
                self.current_flow = Some(self.create_flow_call(current_flow, node));
            }
        }
    }

    fn bind_labeled_statement(&mut self, node: NodeId) {
        let (label_node, statement) = {
            let stmt = self.nodes[node].as_labeled_statement();
            (stmt.label, stmt.statement)
        };
        let post_statement_label = self.create_branch_label();
        self.active_labels.push(ActiveLabel {
            name: label_node
                .map(|l| self.nodes[l].text(self.nodes).into_owned())
                .unwrap_or_default(),
            break_target: Some(post_statement_label),
            continue_target: None,
            referenced: false,
        });
        self.bind(label_node);
        self.bind(statement);
        let label = self.active_labels.pop().expect("active label");
        if !label.referenced {
            // Mark the label as unused; the checker will decide whether to report it
            if let Some(label_node) = label_node {
                self.nodes[label_node].flags.insert(NodeFlags::UNREACHABLE);
            }
        }
        let current_flow = self.current_flow;
        self.add_antecedent(post_statement_label, current_flow);
        self.current_flow = Some(self.finish_flow_label(post_statement_label));
    }

    fn bind_prefix_unary_expression_flow(&mut self, node: NodeId) {
        let (operator, operand) = {
            let expr = self.nodes[node].as_prefix_unary_expression();
            (expr.operator, expr.operand)
        };
        if operator == Kind::ExclamationToken {
            std::mem::swap(
                &mut self.current_true_target,
                &mut self.current_false_target,
            );
            self.bind_each_child(node);
            std::mem::swap(
                &mut self.current_true_target,
                &mut self.current_false_target,
            );
        } else {
            self.bind_each_child(node);
            if operator == Kind::PlusPlusToken || operator == Kind::MinusMinusToken {
                self.bind_assignment_target_flow(operand.unwrap());
            }
        }
    }

    fn bind_postfix_unary_expression_flow(&mut self, node: NodeId) {
        let (operator, operand) = {
            let expr = self.nodes[node].as_postfix_unary_expression();
            (expr.operator, expr.operand)
        };
        self.bind_each_child(node);
        if operator == Kind::PlusPlusToken || operator == Kind::MinusMinusToken {
            self.bind_assignment_target_flow(operand.unwrap());
        }
    }

    fn bind_destructuring_assignment_flow(&mut self, node: NodeId) {
        let (left, type_, operator_token, right) = {
            let expr = self.nodes[node].as_binary_expression();
            (expr.left, expr.type_, expr.operator_token, expr.right)
        };
        if self.in_assignment_pattern {
            self.in_assignment_pattern = false;
            self.bind(operator_token);
            self.bind(right);
            self.in_assignment_pattern = true;
            self.bind(left);
            self.bind(type_);
        } else {
            self.in_assignment_pattern = true;
            self.bind(left);
            self.bind(type_);
            self.in_assignment_pattern = false;
            self.bind(operator_token);
            self.bind(right);
        }
        if let Some(left) = left {
            self.bind_assignment_target_flow(left);
        }
    }

    fn bind_binary_expression_flow(&mut self, node: NodeId) {
        let (left, type_, operator_token, right) = {
            let expr = self.nodes[node].as_binary_expression();
            (expr.left, expr.type_, expr.operator_token, expr.right)
        };
        let operator = self.nodes[operator_token.unwrap()].kind;
        if is_logical_or_coalescing_binary_operator(operator)
            || operator.is_logical_or_coalescing_assignment_operator()
        {
            if is_top_level_logical_expression(node, self.nodes) {
                let post_expression_label = self.create_branch_label();
                let save_current_flow = self.current_flow;
                let save_has_flow_effects = self.has_flow_effects;
                self.has_flow_effects = false;
                self.bind_logical_like_expression(
                    node,
                    post_expression_label,
                    post_expression_label,
                );
                if self.has_flow_effects {
                    self.current_flow = Some(self.finish_flow_label(post_expression_label));
                } else {
                    self.current_flow = save_current_flow;
                }
                self.has_flow_effects = self.has_flow_effects || save_has_flow_effects;
            } else {
                let true_target = self.current_true_target.expect("true target");
                let false_target = self.current_false_target.expect("false target");
                self.bind_logical_like_expression(node, true_target, false_target);
            }
        } else {
            self.bind(left);
            self.bind(type_);
            if operator == Kind::CommaToken {
                if let Some(left) = left {
                    self.maybe_bind_expression_flow_if_call(left);
                }
            }
            self.bind(operator_token);
            self.bind(right);
            if operator == Kind::CommaToken {
                if let Some(right) = right {
                    self.maybe_bind_expression_flow_if_call(right);
                }
            }
            if operator.is_assignment_operator() && !is_assignment_target(node, self.nodes) {
                if let Some(left) = left {
                    self.bind_assignment_target_flow(left);
                }
                if operator == Kind::EqualsToken
                    && left.is_some_and(|l| self.nodes[l].kind == Kind::ElementAccessExpression)
                {
                    let left = left.unwrap();
                    let element_access = self.nodes[left].as_element_access_expression();
                    if element_access
                        .expression
                        .is_some_and(|e| self.is_narrowable_operand(e))
                    {
                        let current_flow = self.current_flow.expect("current flow");
                        self.current_flow = Some(self.create_flow_mutation(
                            tsc_ast::FlowFlags::ARRAY_MUTATION,
                            current_flow,
                            node,
                        ));
                    }
                }
            }
        }
    }

    fn bind_logical_like_expression(
        &mut self,
        node: NodeId,
        true_target: FlowNodeId,
        false_target: FlowNodeId,
    ) {
        let (left, operator_token, right) = {
            let expr = self.nodes[node].as_binary_expression();
            (expr.left, expr.operator_token, expr.right)
        };
        let operator = self.nodes[operator_token.unwrap()].kind;
        let pre_right_label = self.create_branch_label();
        if operator == Kind::AmpersandAmpersandToken
            || operator == Kind::AmpersandAmpersandEqualsToken
        {
            self.bind_condition(left, pre_right_label, false_target);
        } else {
            self.bind_condition(left, true_target, pre_right_label);
        }
        self.current_flow = Some(self.finish_flow_label(pre_right_label));
        self.bind(operator_token);
        if operator.is_logical_or_coalescing_assignment_operator() {
            self.do_with_conditional_branches(Binder::bind, right, true_target, false_target);
            if let Some(left) = left {
                self.bind_assignment_target_flow(left);
            }
            let current_flow = self.current_flow.expect("current flow");
            let true_condition = self.create_flow_condition(
                tsc_ast::FlowFlags::TRUE_CONDITION,
                current_flow,
                Some(node),
            );
            self.add_antecedent(true_target, Some(true_condition));
            let current_flow = self.current_flow.expect("current flow");
            let false_condition = self.create_flow_condition(
                tsc_ast::FlowFlags::FALSE_CONDITION,
                current_flow,
                Some(node),
            );
            self.add_antecedent(false_target, Some(false_condition));
        } else {
            self.bind_condition(right, true_target, false_target);
        }
    }

    fn bind_delete_expression_flow(&mut self, node: NodeId) {
        let expression = self.nodes[node].as_delete_expression().expression;
        self.bind_each_child(node);
        if expression.is_some_and(|e| self.nodes[e].kind == Kind::PropertyAccessExpression) {
            self.bind_assignment_target_flow(expression.unwrap());
        }
    }

    fn bind_conditional_expression_flow(&mut self, node: NodeId) {
        let (condition, question_token, when_true, colon_token, when_false) = {
            let expr = self.nodes[node].as_conditional_expression();
            (
                expr.condition,
                expr.question_token,
                expr.when_true,
                expr.colon_token,
                expr.when_false,
            )
        };
        let true_label = self.create_branch_label();
        let false_label = self.create_branch_label();
        let post_expression_label = self.create_branch_label();
        let save_current_flow = self.current_flow;
        let save_has_flow_effects = self.has_flow_effects;
        self.has_flow_effects = false;
        self.bind_condition(condition, true_label, false_label);
        self.current_flow = Some(self.finish_flow_label(true_label));
        self.bind(question_token);
        self.bind(when_true);
        let current_flow = self.current_flow;
        self.add_antecedent(post_expression_label, current_flow);
        self.current_flow = Some(self.finish_flow_label(false_label));
        self.bind(colon_token);
        self.bind(when_false);
        let current_flow = self.current_flow;
        self.add_antecedent(post_expression_label, current_flow);
        if self.has_flow_effects {
            self.current_flow = Some(self.finish_flow_label(post_expression_label));
        } else {
            self.current_flow = save_current_flow;
        }
        self.has_flow_effects = self.has_flow_effects || save_has_flow_effects;
    }

    fn bind_variable_declaration_flow(&mut self, node: NodeId) {
        self.bind_each_child(node);
        if self.nodes[node].initializer().is_some()
            || is_for_in_or_of_statement(
                self.nodes[node].parent.and_then(|p| self.nodes[p].parent),
                self.nodes,
            )
        {
            self.bind_initialized_variable_flow(node);
        }
    }

    fn bind_initialized_variable_flow(&mut self, node: NodeId) {
        let name = match self.nodes[node].kind {
            Kind::VariableDeclaration => self.nodes[node].as_variable_declaration().name,
            Kind::BindingElement => self.nodes[node].as_binding_element().name,
            _ => None,
        };
        if name.is_some_and(|n| is_binding_pattern(&self.nodes[n])) {
            let elements: Vec<NodeId> =
                self.nodes[name.unwrap()].elements().unwrap_or(&[]).to_vec();
            for child in elements {
                self.bind_initialized_variable_flow(child);
            }
        } else {
            let current_flow = self.current_flow.expect("current flow");
            self.current_flow =
                Some(self.create_flow_mutation(tsc_ast::FlowFlags::ASSIGNMENT, current_flow, node));
        }
    }

    fn bind_access_expression_flow(&mut self, node: NodeId) {
        if is_optional_chain(&self.nodes[node]) {
            self.bind_optional_chain_flow(node);
        } else {
            self.bind_each_child(node);
        }
    }

    fn bind_optional_chain_flow(&mut self, node: NodeId) {
        if is_top_level_logical_expression(node, self.nodes) {
            let post_expression_label = self.create_branch_label();
            let save_current_flow = self.current_flow;
            let save_has_flow_effects = self.has_flow_effects;
            self.bind_optional_chain(node, post_expression_label, post_expression_label);
            if self.has_flow_effects {
                self.current_flow = Some(self.finish_flow_label(post_expression_label));
            } else {
                self.current_flow = save_current_flow;
            }
            self.has_flow_effects = self.has_flow_effects || save_has_flow_effects;
        } else {
            let true_target = self.current_true_target.expect("true target");
            let false_target = self.current_false_target.expect("false target");
            self.bind_optional_chain(node, true_target, false_target);
        }
    }

    fn bind_optional_chain(
        &mut self,
        node: NodeId,
        true_target: FlowNodeId,
        false_target: FlowNodeId,
    ) {
        // For an optional chain, we emulate the behavior of a logical expression:
        //
        // a?.b         -> a && a.b
        // a?.b.c       -> a && a.b.c
        // a?.b?.c      -> a && a.b && a.b.c
        // a?.[x = 1]   -> a && a[x = 1]
        //
        // To do this we descend through the chain until we reach the root of a chain (the expression with a `?.`)
        // and build it's CFA graph as if it were the first condition (`a && ...`). Then we bind the rest
        // of the node as part of the "true" branch, and continue to do so as we ascend back up to the outermost
        // chain node. We then treat the entire node as the right side of the expression.
        let pre_chain_label = if is_optional_chain_root(&self.nodes[node]) {
            Some(self.create_branch_label())
        } else {
            None
        };
        let expression = self.nodes[node].expression();
        let expr_true_target = pre_chain_label.unwrap_or(true_target);
        self.bind_optional_expression(expression, expr_true_target, false_target);
        if let Some(pre_chain_label) = pre_chain_label {
            self.current_flow = Some(self.finish_flow_label(pre_chain_label));
        }
        self.do_with_conditional_branches(
            Binder::bind_optional_chain_rest,
            Some(node),
            true_target,
            false_target,
        );
        if is_outermost_optional_chain(&self.nodes[node], self.nodes) {
            let current_flow = self.current_flow.expect("current flow");
            let true_condition = self.create_flow_condition(
                tsc_ast::FlowFlags::TRUE_CONDITION,
                current_flow,
                Some(node),
            );
            self.add_antecedent(true_target, Some(true_condition));
            let current_flow = self.current_flow.expect("current flow");
            let false_condition = self.create_flow_condition(
                tsc_ast::FlowFlags::FALSE_CONDITION,
                current_flow,
                Some(node),
            );
            self.add_antecedent(false_target, Some(false_condition));
        }
    }

    fn bind_optional_expression(
        &mut self,
        node: Option<NodeId>,
        true_target: FlowNodeId,
        false_target: FlowNodeId,
    ) {
        self.do_with_conditional_branches(Binder::bind, node, true_target, false_target);
        if let Some(node) = node {
            if !is_optional_chain(&self.nodes[node])
                || is_outermost_optional_chain(&self.nodes[node], self.nodes)
            {
                let current_flow = self.current_flow.expect("current flow");
                let true_condition = self.create_flow_condition(
                    tsc_ast::FlowFlags::TRUE_CONDITION,
                    current_flow,
                    Some(node),
                );
                self.add_antecedent(true_target, Some(true_condition));
                let current_flow = self.current_flow.expect("current flow");
                let false_condition = self.create_flow_condition(
                    tsc_ast::FlowFlags::FALSE_CONDITION,
                    current_flow,
                    Some(node),
                );
                self.add_antecedent(false_target, Some(false_condition));
            }
        }
    }

    fn bind_optional_chain_rest(&mut self, node: Option<NodeId>) -> bool {
        let Some(node) = node else {
            return false;
        };
        match self.nodes[node].kind {
            Kind::PropertyAccessExpression => {
                let question_dot_token = self.nodes[node].question_dot_token();
                self.bind(question_dot_token);
                let name = self.nodes[node].name();
                self.bind(name);
            }
            Kind::ElementAccessExpression => {
                let question_dot_token = self.nodes[node].question_dot_token();
                self.bind(question_dot_token);
                let argument = self.nodes[node]
                    .as_element_access_expression()
                    .argument_expression;
                self.bind(argument);
            }
            Kind::CallExpression => {
                let question_dot_token = self.nodes[node].question_dot_token();
                self.bind(question_dot_token);
                let type_arguments = self.nodes[node].type_argument_list().cloned();
                self.bind_node_list(type_arguments.as_ref());
                let arguments = self.nodes[node]
                    .argument_list()
                    .map_or_else(Vec::new, |l| l.nodes.to_vec());
                self.bind_each(&arguments);
            }
            _ => {}
        }
        false
    }

    fn bind_call_expression_flow(&mut self, node: NodeId) {
        if is_optional_chain(&self.nodes[node]) {
            self.bind_optional_chain_flow(node);
        } else {
            // If the target of the call expression is a function expression or arrow function we have
            // an immediately invoked function expression (IIFE). Initialize the flowNode property to
            // the current control flow (which includes evaluation of the IIFE arguments).
            let (expression, type_arguments, arguments) = {
                let call = self.nodes[node].as_call_expression();
                (
                    call.expression,
                    call.type_arguments.clone(),
                    call.arguments.clone(),
                )
            };
            let expr = expression.map(|e| skip_parentheses(e, self.nodes));
            if expr.is_some_and(|e| {
                self.nodes[e].kind == Kind::FunctionExpression
                    || self.nodes[e].kind == Kind::ArrowFunction
            }) {
                self.bind_node_list(type_arguments.as_ref());
                if let Some(arguments) = arguments {
                    let args = arguments.nodes.clone();
                    self.bind_each(&args);
                }
                self.bind(expression);
            } else {
                self.bind_each_child(node);
                if expression.is_some_and(|e| self.nodes[e].kind == Kind::SuperKeyword) {
                    let current_flow = self.current_flow.expect("current flow");
                    self.current_flow = Some(self.create_flow_call(current_flow, node));
                }
            }
        }
        let expression = self.nodes[node].as_call_expression().expression;
        if expression.is_some_and(|e| is_property_access_expression(&self.nodes[e])) {
            let access = self.nodes[expression.unwrap()].as_property_access_expression();
            if access.name.is_some_and(|n| is_identifier(&self.nodes[n]))
                && access
                    .expression
                    .is_some_and(|e| self.is_narrowable_operand(e))
                && is_push_or_unshift_identifier(&self.nodes[access.name.unwrap()], self.nodes)
            {
                let current_flow = self.current_flow.expect("current flow");
                self.current_flow = Some(self.create_flow_mutation(
                    tsc_ast::FlowFlags::ARRAY_MUTATION,
                    current_flow,
                    node,
                ));
            }
        }
    }

    fn bind_non_null_expression_flow(&mut self, node: NodeId) {
        if is_optional_chain(&self.nodes[node]) {
            self.bind_optional_chain_flow(node);
        } else {
            self.bind_each_child(node);
        }
    }

    fn bind_binding_element_flow(&mut self, node: NodeId) {
        // When evaluating a binding pattern, the initializer is evaluated before the binding pattern, per:
        // - https://tc39.es/ecma262/#sec-destructuring-binding-patterns-runtime-semantics-iteratorbindinginitialization
        //   - `BindingElement: BindingPattern Initializer?`
        // - https://tc39.es/ecma262/#sec-runtime-semantics-keyedbindinginitialization
        //   - `BindingElement: BindingPattern Initializer?`
        let (dot_dot_dot_token, property_name, initializer, name) = {
            let elem = self.nodes[node].as_binding_element();
            (
                elem.dot_dot_dot_token,
                elem.property_name,
                elem.initializer,
                elem.name,
            )
        };
        self.bind(dot_dot_dot_token);
        self.bind(property_name);
        self.bind_initializer(initializer);
        self.bind(name);
    }

    fn bind_parameter_flow(&mut self, node: NodeId) {
        let (modifiers, dot_dot_dot_token, question_token, type_, initializer, name) = {
            let param = self.nodes[node].as_parameter_declaration();
            (
                param.modifiers_base.modifiers.clone(),
                param.dot_dot_dot_token,
                param.question_token,
                param.type_,
                param.initializer,
                param.name,
            )
        };
        self.bind_modifiers(modifiers);
        self.bind(dot_dot_dot_token);
        self.bind(question_token);
        self.bind(type_);
        self.bind_initializer(initializer);
        self.bind(name);
    }

    // a BindingElement/Parameter does not have side effects if initializers are not evaluated and used. (see GH#49759)
    fn bind_initializer(&mut self, node: Option<NodeId>) {
        let Some(node) = node else {
            return;
        };
        let entry_flow = self.current_flow;
        self.bind(Some(node));
        if entry_flow == Some(self.unreachable_flow) || entry_flow == self.current_flow {
            return;
        }
        let exit_flow = self.create_branch_label();
        self.add_antecedent(exit_flow, entry_flow);
        let current_flow = self.current_flow;
        self.add_antecedent(exit_flow, current_flow);
        self.current_flow = Some(self.finish_flow_label(exit_flow));
    }

    /// `setFlowNode` — a free function in Go taking `(node, flowNode)`.
    fn set_flow_node(&mut self, node: NodeId, flow_node: Option<FlowNodeId>) {
        if let Some(data) = self.nodes[node].data.flow_node_data_mut() {
            data.flow_node = flow_node;
        }
    }

    /// `setReturnFlowNode` — a free function in Go taking `(node, returnFlowNode)`.
    fn set_return_flow_node(&mut self, node: NodeId, return_flow_node: Option<FlowNodeId>) {
        match self.nodes[node].kind {
            Kind::Constructor => {
                self.nodes[node]
                    .as_constructor_declaration_mut()
                    .return_flow_node = return_flow_node;
            }
            Kind::FunctionDeclaration => {
                self.nodes[node]
                    .as_function_declaration_mut()
                    .return_flow_node = return_flow_node;
            }
            Kind::FunctionExpression => {
                self.nodes[node]
                    .as_function_expression_mut()
                    .return_flow_node = return_flow_node;
            }
            Kind::ClassStaticBlockDeclaration => {
                self.nodes[node]
                    .as_class_static_block_declaration_mut()
                    .return_flow_node = return_flow_node;
            }
            _ => {}
        }
    }

    fn add_to_container_chain(&mut self, next: NodeId) {
        if let Some(last_container) = self.last_container {
            self.nodes[last_container]
                .data
                .locals_container_data_mut()
                .expect("locals container data")
                .next_container = Some(next);
        }
        self.last_container = Some(next);
    }

    fn add_declaration_to_symbol(
        &mut self,
        symbol: SymbolId,
        node: NodeId,
        symbol_flags: SymbolFlags,
    ) {
        self.symbols[symbol.index()].flags |= symbol_flags;
        self.nodes[node]
            .data
            .declaration_data_mut()
            .expect("declaration data")
            .symbol = Some(symbol);
        if self.symbols[symbol.index()].declarations.is_empty() {
            self.symbols[symbol.index()].declarations = vec![node];
        } else if !self.symbols[symbol.index()].declarations.contains(&node) {
            self.symbols[symbol.index()].declarations.push(node);
        }
        // On merge of const enum module with class or function, reset const enum only flag (namespaces will already recalculate)
        if self.symbols[symbol.index()]
            .flags
            .intersects(SymbolFlags::CONST_ENUM_ONLY_MODULE)
            && self.symbols[symbol.index()]
                .flags
                .intersects(SymbolFlags::FUNCTION | SymbolFlags::CLASS | SymbolFlags::REGULAR_ENUM)
        {
            self.symbols[symbol.index()]
                .flags
                .remove(SymbolFlags::CONST_ENUM_ONLY_MODULE);
            self.not_const_enum_only_modules.add(symbol);
        }
        if symbol_flags.intersects(SymbolFlags::VALUE) {
            set_value_declaration(self.symbols, symbol, node, &|id| self.nodes[id].clone());
        }
    }

    /// `SetValueDeclaration` — exported in Go for the checker.
    pub fn set_value_declaration_exported(&mut self, symbol: SymbolId, node: NodeId) {
        set_value_declaration(self.symbols, symbol, node, &|id| self.nodes[id].clone())
    }

    fn error_on_node(
        &mut self,
        node: NodeId,
        message: &'static diagnostics::Message,
        args: &[String],
    ) {
        let diagnostic = self.create_diagnostic_for_node(node, message, args);
        self.add_diagnostic(diagnostic);
    }

    fn error_on_first_token(
        &mut self,
        node: NodeId,
        message: &'static diagnostics::Message,
        args: &[String],
    ) {
        let span =
            get_range_of_token_at_position(self.file_data(), self.nodes[node].pos() as usize);
        let diagnostic = new_diagnostic(
            Some(tsc_ast::diagnostic::DiagnosticFile::from_node(
                self.file, self.nodes,
            )),
            span,
            message,
            args,
        );
        self.add_diagnostic(diagnostic);
    }

    /// Inside the binder, we may create a diagnostic for an as-yet unbound node (with potentially no parent pointers, implying no accessible source file)
    /// If so, the node _must_ be in the current file (as that's the only way anything could have traversed to it to yield it as the error node)
    /// This version of `createDiagnosticForNode` uses the binder's context to account for this, and always yields correct diagnostics even in these situations.
    fn create_diagnostic_for_node(
        &mut self,
        node: NodeId,
        message: &'static diagnostics::Message,
        args: &[String],
    ) -> DiagnosticRef {
        let span =
            tsc_scanner::scanner::get_error_range_for_node(self.file_data(), node, self.nodes);
        new_diagnostic(
            Some(tsc_ast::diagnostic::DiagnosticFile::from_node(
                self.file, self.nodes,
            )),
            span,
            message,
            args,
        )
    }

    fn add_diagnostic(&mut self, diagnostic: DiagnosticRef) {
        self.file_data_mut().bind_diagnostics.push(diagnostic);
    }

    fn get_optional_symbol_flag_for_node(&self, node: NodeId) -> SymbolFlags {
        match self.nodes[node].postfix_token() {
            Some(t) if self.nodes[t].kind == Kind::QuestionToken => SymbolFlags::OPTIONAL,
            _ => SymbolFlags::NONE,
        }
    }

    fn is_narrowing_expression(&self, expr: NodeId) -> bool {
        is_narrowing_expression(self.nodes, expr)
    }

    fn is_narrowable_reference(&self, node: NodeId) -> bool {
        is_narrowable_reference(self.nodes, node)
    }

    fn is_narrowable_operand(&self, expr: NodeId) -> bool {
        is_narrowable_operand(self.nodes, expr)
    }
}

/// `func isUseStrictPrologueDirective`.
fn is_use_strict_prologue_directive(
    source_file: &SourceFile,
    node: NodeId,
    nodes: &[Node],
) -> bool {
    let node_text = get_source_text_of_node_from_source_file(
        source_file,
        nodes[node]
            .expression()
            .expect("prologue directive expression"),
        false, /*includeTrivia*/
        nodes,
    );
    // Note: the node text must be exactly "use strict" or 'use strict'.  It is not ok for the
    // string to contain unicode escapes (as per ES5).
    node_text == "\"use strict\"" || node_text == "'use strict'"
}

/// `func FindUseStrictPrologue`.
pub fn find_use_strict_prologue(
    source_file: &SourceFile,
    statements: &[NodeId],
    nodes: &[Node],
) -> Option<NodeId> {
    for &statement in statements {
        if is_prologue_directive(&nodes[statement], nodes) {
            if is_use_strict_prologue_directive(source_file, statement, nodes) {
                return Some(statement);
            }
        } else {
            return None;
        }
    }
    None
}

/// `func GetContainerFlags` — exported in Go (also used outside the binder).
pub fn get_container_flags(node: NodeId, nodes: &[Node]) -> ContainerFlags {
    match nodes[node].kind {
        Kind::ClassExpression
        | Kind::ClassDeclaration
        | Kind::EnumDeclaration
        | Kind::ObjectLiteralExpression
        | Kind::TypeLiteral
        | Kind::JsxAttributes => CONTAINER_FLAGS_IS_CONTAINER,
        Kind::InterfaceDeclaration => CONTAINER_FLAGS_IS_CONTAINER | CONTAINER_FLAGS_IS_INTERFACE,
        Kind::ModuleDeclaration
        | Kind::TypeAliasDeclaration
        | Kind::JSTypeAliasDeclaration
        | Kind::MappedType
        | Kind::IndexSignature => CONTAINER_FLAGS_IS_CONTAINER | CONTAINER_FLAGS_HAS_LOCALS,
        Kind::SourceFile => {
            CONTAINER_FLAGS_IS_CONTAINER
                | CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER
                | CONTAINER_FLAGS_HAS_LOCALS
        }
        Kind::GetAccessor | Kind::SetAccessor | Kind::MethodDeclaration
            if is_object_literal_or_class_expression_method_or_accessor(node, nodes) =>
        {
            CONTAINER_FLAGS_IS_CONTAINER
                | CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER
                | CONTAINER_FLAGS_HAS_LOCALS
                | CONTAINER_FLAGS_IS_FUNCTION_LIKE
                | CONTAINER_FLAGS_IS_OBJECT_LITERAL_OR_CLASS_EXPRESSION_METHOD_OR_ACCESSOR
                | CONTAINER_FLAGS_IS_THIS_CONTAINER
        }
        Kind::GetAccessor
        | Kind::SetAccessor
        | Kind::MethodDeclaration
        | Kind::Constructor
        | Kind::FunctionDeclaration
        | Kind::ClassStaticBlockDeclaration => {
            CONTAINER_FLAGS_IS_CONTAINER
                | CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER
                | CONTAINER_FLAGS_HAS_LOCALS
                | CONTAINER_FLAGS_IS_FUNCTION_LIKE
                | CONTAINER_FLAGS_IS_THIS_CONTAINER
        }
        Kind::MethodSignature
        | Kind::CallSignature
        | Kind::FunctionType
        | Kind::ConstructSignature
        | Kind::ConstructorType => {
            CONTAINER_FLAGS_IS_CONTAINER
                | CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER
                | CONTAINER_FLAGS_HAS_LOCALS
                | CONTAINER_FLAGS_IS_FUNCTION_LIKE
                | CONTAINER_FLAGS_PROPAGATES_THIS_KEYWORD
        }
        Kind::FunctionExpression => {
            CONTAINER_FLAGS_IS_CONTAINER
                | CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER
                | CONTAINER_FLAGS_HAS_LOCALS
                | CONTAINER_FLAGS_IS_FUNCTION_LIKE
                | CONTAINER_FLAGS_IS_FUNCTION_EXPRESSION
                | CONTAINER_FLAGS_IS_THIS_CONTAINER
        }
        Kind::ArrowFunction => {
            CONTAINER_FLAGS_IS_CONTAINER
                | CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER
                | CONTAINER_FLAGS_HAS_LOCALS
                | CONTAINER_FLAGS_IS_FUNCTION_LIKE
                | CONTAINER_FLAGS_IS_FUNCTION_EXPRESSION
                | CONTAINER_FLAGS_PROPAGATES_THIS_KEYWORD
        }
        Kind::ModuleBlock => CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER,
        Kind::PropertyDeclaration => {
            if nodes[node].initializer().is_some() {
                CONTAINER_FLAGS_IS_CONTROL_FLOW_CONTAINER | CONTAINER_FLAGS_IS_THIS_CONTAINER
            } else {
                CONTAINER_FLAGS_NONE
            }
        }
        Kind::CatchClause
        | Kind::ForStatement
        | Kind::ForInStatement
        | Kind::ForOfStatement
        | Kind::CaseBlock => CONTAINER_FLAGS_IS_BLOCK_SCOPED_CONTAINER | CONTAINER_FLAGS_HAS_LOCALS,
        Kind::Block => {
            if nodes[node].parent.is_some_and(|p| {
                is_function_like(Some(p), nodes) || is_class_static_block_declaration(&nodes[p])
            }) {
                CONTAINER_FLAGS_NONE
            } else {
                CONTAINER_FLAGS_IS_BLOCK_SCOPED_CONTAINER | CONTAINER_FLAGS_HAS_LOCALS
            }
        }
        _ => CONTAINER_FLAGS_NONE,
    }
}

/// `func getParentOfPropertyAssignment`.
fn get_parent_of_property_assignment(node: NodeId, nodes: &[Node]) -> NodeId {
    match nodes[node].kind {
        Kind::BinaryExpression => nodes[nodes[node]
            .as_binary_expression()
            .left
            .expect("binary left")]
        .expression()
        .expect("assignment parent expression"),
        Kind::CallExpression => nodes[node].arguments().expect("call arguments")[0],
        _ => panic!("Unhandled case in getParentOfPropertyAssignment"),
    }
}

/// `func getInitializerSymbol` — a free function in Go.
fn get_initializer_symbol(
    symbols: &[Symbol],
    symbol: SymbolId,
    nodes: &[Node],
) -> Option<SymbolId> {
    let declaration = symbols[symbol.index()].value_declaration?;
    // For an assignment 'fn.xxx = ...', where 'fn' is a previously declared function or a previously
    // declared const variable initialized with a function expression or arrow function, we add expando
    // property declarations to the function's symbol. This also applies to class expressions in JS files,
    // and empty object literals in JS files when the declaration doesn't have a type annotation.
    if is_function_declaration(&nodes[declaration])
        || is_in_js_file(Some(declaration), nodes) && is_class_declaration(&nodes[declaration])
    {
        return Some(symbol);
    }
    if is_variable_declaration(&nodes[declaration]) {
        let parent_is_const = nodes[declaration]
            .parent
            .is_some_and(|p| nodes[p].flags.intersects(NodeFlags::CONST));
        if parent_is_const || is_in_js_file(Some(declaration), nodes) {
            let initializer = nodes[declaration].initializer();
            if is_expando_initializer(&nodes[declaration], initializer, nodes) {
                return initializer.and_then(|i| nodes[i].symbol());
            }
        }
    }
    if is_binary_expression(&nodes[declaration]) && is_in_js_file(Some(declaration), nodes) {
        let initializer = nodes[declaration].as_binary_expression().right;
        if is_expando_initializer(&nodes[declaration], initializer, nodes) {
            return initializer.and_then(|i| nodes[i].symbol());
        }
    }
    None
}

/// `func isEvalOrArgumentsIdentifier`.
fn is_eval_or_arguments_identifier(node: &Node, nodes: &[Node]) -> bool {
    is_identifier(node) && matches!(&*node.text(nodes), "eval" | "arguments")
}

/// `func isLogicalAssignmentExpression`.
fn is_logical_assignment_expression(node: NodeId, nodes: &[Node]) -> bool {
    is_logical_or_coalescing_assignment_expression(&nodes[skip_parentheses(node, nodes)], nodes)
}

/// `func isGeneratorFunctionExpression`.
fn is_generator_function_expression(node: &Node) -> bool {
    is_function_expression(node) && node.body_data().is_some_and(|d| d.asterisk_token.is_some())
}

/// `func isStatementCondition`.
fn is_statement_condition(node: NodeId, nodes: &[Node]) -> bool {
    let Some(parent) = nodes[node].parent else {
        return false;
    };
    match nodes[parent].kind {
        Kind::IfStatement | Kind::WhileStatement | Kind::DoStatement => {
            nodes[parent].expression() == Some(node)
        }
        Kind::ForStatement => nodes[parent].as_for_statement().condition == Some(node),
        Kind::ConditionalExpression => {
            nodes[parent].as_conditional_expression().condition == Some(node)
        }
        _ => false,
    }
}

/// `func isTopLevelLogicalExpression`.
fn is_top_level_logical_expression(mut node: NodeId, nodes: &[Node]) -> bool {
    while nodes[node].parent.is_some_and(|p| {
        is_parenthesized_expression(&nodes[p])
            || is_prefix_unary_expression(&nodes[p])
                && nodes[p].as_prefix_unary_expression().operator == Kind::ExclamationToken
    }) {
        node = nodes[node].parent.unwrap();
    }
    !is_statement_condition(node, nodes)
        && !nodes[node]
            .parent
            .is_some_and(|p| is_logical_expression(p, nodes))
        && !(nodes[node]
            .parent
            .is_some_and(|p| is_optional_chain(&nodes[p]) && nodes[p].expression() == Some(node)))
}

/// `func isAssignmentDeclaration`.
fn is_assignment_declaration(node: &Node) -> bool {
    is_binary_expression(node)
        || is_access_expression(node)
        || is_identifier(node)
        || is_call_expression(node)
}

/// `func isEffectiveModuleDeclaration`.
fn is_effective_module_declaration(node: &Node) -> bool {
    is_module_declaration(node) || is_identifier(node)
}

/// `func isFunctionSymbol` — dead code in Go too; ported for parity.
#[allow(dead_code)]
fn is_function_symbol(symbol: &Symbol, nodes: &[Node]) -> bool {
    if let Some(d) = symbol.value_declaration {
        if is_function_declaration(&nodes[d]) {
            return true;
        }
        if is_variable_declaration(&nodes[d]) {
            if let Some(initializer) = nodes[d].as_variable_declaration().initializer {
                return is_function_like(Some(initializer), nodes);
            }
        }
    }
    false
}

/// `func SetValueDeclaration` — a free function in Go so the checker can call
/// it on any symbol; takes the symbols arena since `SymbolId` is an index.
///
/// PORT: `node_at` resolves `NodeId`s because the stored `value_declaration`
/// and the incoming `node` may live in DIFFERENT file arenas (global symbol
/// merging crosses files). Go reads `*ast.Node` pointers directly; here a
/// single `&[Node]` slice cannot cover both files. Callers pass a per-file
/// arena lookup (`nodes[id].clone()` or `program.nodes(id.file_index())`).
pub fn set_value_declaration(
    symbols: &mut Vec<Symbol>,
    symbol: SymbolId,
    node: NodeId,
    node_at: &dyn Fn(NodeId) -> Node,
) {
    let value_declaration = symbols[symbol.index()].value_declaration;
    if value_declaration.is_none()
        || value_declaration.is_some_and(|v| {
            is_assignment_declaration(&node_at(v)) && !is_assignment_declaration(&node_at(node))
        })
        || value_declaration.is_some_and(|v| {
            node_at(v).kind != node_at(node).kind && is_effective_module_declaration(&node_at(v))
        })
    {
        // Non-assignment declarations take precedence over assignment declarations and
        // non-namespace declarations take precedence over namespace declarations.
        symbols[symbol.index()].value_declaration = Some(node);
    }
}

/// `func GetSymbolNameForPrivateIdentifier` — exported in Go.
pub fn get_symbol_name_for_private_identifier(
    containing_class_symbol: SymbolId,
    description: &str,
) -> String {
    format!(
        "{INTERNAL_SYMBOL_NAME_PREFIX}#{}@{description}",
        containing_class_symbol.0
    )
}

/// `func isNarrowingExpression`.
fn is_narrowing_expression(nodes: &[Node], expr: NodeId) -> bool {
    match nodes[expr].kind {
        Kind::Identifier | Kind::ThisKeyword => true,
        Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
            contains_narrowable_reference(nodes, expr)
        }
        Kind::CallExpression => has_narrowable_argument(nodes, expr),
        Kind::ParenthesizedExpression | Kind::NonNullExpression | Kind::TypeOfExpression => nodes
            [expr]
            .expression()
            .is_some_and(|e| is_narrowing_expression(nodes, e)),
        Kind::BinaryExpression => is_narrowing_binary_expression(nodes, expr),
        Kind::PrefixUnaryExpression => {
            let e = nodes[expr].as_prefix_unary_expression();
            e.operator == Kind::ExclamationToken
                && e.operand.is_some_and(|o| is_narrowing_expression(nodes, o))
        }
        _ => false,
    }
}

/// `func containsNarrowableReference`.
fn contains_narrowable_reference(nodes: &[Node], expr: NodeId) -> bool {
    if is_narrowable_reference(nodes, expr) {
        return true;
    }
    if nodes[expr].flags.intersects(NodeFlags::OPTIONAL_CHAIN) {
        match nodes[expr].kind {
            Kind::PropertyAccessExpression
            | Kind::ElementAccessExpression
            | Kind::CallExpression
            | Kind::NonNullExpression => {
                return nodes[expr]
                    .expression()
                    .is_some_and(|e| contains_narrowable_reference(nodes, e));
            }
            _ => {}
        }
    }
    false
}

/// `func isNarrowableReference`.
fn is_narrowable_reference(nodes: &[Node], node: NodeId) -> bool {
    match nodes[node].kind {
        Kind::Identifier | Kind::ThisKeyword | Kind::SuperKeyword | Kind::MetaProperty => true,
        Kind::PropertyAccessExpression
        | Kind::ParenthesizedExpression
        | Kind::NonNullExpression => nodes[node]
            .expression()
            .is_some_and(|e| is_narrowable_reference(nodes, e)),
        Kind::ElementAccessExpression => {
            let e = nodes[node].as_element_access_expression();
            e.argument_expression
                .is_some_and(|a| is_string_or_numeric_literal_like(&nodes[a]))
                || e.argument_expression
                    .is_some_and(|a| is_entity_name_expression(&nodes[a], nodes))
                    && e.expression
                        .is_some_and(|x| is_narrowable_reference(nodes, x))
        }
        Kind::BinaryExpression => {
            let e = nodes[node].as_binary_expression();
            let op = e.operator_token.map(|t| nodes[t].kind);
            op == Some(Kind::CommaToken)
                && e.right.is_some_and(|r| is_narrowable_reference(nodes, r))
                || op.is_some_and(|o| o.is_assignment_operator())
                    && e.left
                        .is_some_and(|l| is_left_hand_side_expression(&nodes[l], nodes))
        }
        _ => false,
    }
}

/// `func hasNarrowableArgument`.
fn has_narrowable_argument(nodes: &[Node], expr: NodeId) -> bool {
    let call = nodes[expr].as_call_expression();
    if let Some(args) = &call.arguments {
        for &argument in args.nodes.iter() {
            if contains_narrowable_reference(nodes, argument) {
                return true;
            }
        }
    }
    if call
        .expression
        .is_some_and(|e| is_property_access_expression(&nodes[e]))
    {
        if let Some(inner) = call.expression.and_then(|e| nodes[e].expression()) {
            if contains_narrowable_reference(nodes, inner) {
                return true;
            }
        }
    }
    false
}

/// `func isNarrowingBinaryExpression`.
fn is_narrowing_binary_expression(nodes: &[Node], expr: NodeId) -> bool {
    let e = nodes[expr].as_binary_expression();
    let Some(op) = e.operator_token.map(|t| nodes[t].kind) else {
        return false;
    };
    match op {
        Kind::EqualsToken
        | Kind::BarBarEqualsToken
        | Kind::AmpersandAmpersandEqualsToken
        | Kind::QuestionQuestionEqualsToken => e
            .left
            .is_some_and(|l| contains_narrowable_reference(nodes, l)),
        Kind::EqualsEqualsToken
        | Kind::ExclamationEqualsToken
        | Kind::EqualsEqualsEqualsToken
        | Kind::ExclamationEqualsEqualsToken => {
            let left = e.left.map(|l| skip_parentheses(l, nodes));
            let right = e.right.map(|r| skip_parentheses(r, nodes));
            left.is_some_and(|l| is_narrowable_operand(nodes, l))
                || right.is_some_and(|r| is_narrowable_operand(nodes, r))
                || (right.is_some()
                    && left.is_some()
                    && (is_narrowing_type_of_operands(nodes, right.unwrap(), left.unwrap())
                        || is_narrowing_type_of_operands(nodes, left.unwrap(), right.unwrap())))
                || (right.is_some_and(|r| is_boolean_literal(&nodes[r]))
                    && left.is_some_and(|l| is_narrowing_expression(nodes, l))
                    || left.is_some_and(|l| is_boolean_literal(&nodes[l]))
                        && right.is_some_and(|r| is_narrowing_expression(nodes, r)))
        }
        Kind::InstanceOfKeyword => e.left.is_some_and(|l| is_narrowable_operand(nodes, l)),
        Kind::InKeyword => e.right.is_some_and(|r| is_narrowing_expression(nodes, r)),
        Kind::CommaToken => e.right.is_some_and(|r| is_narrowing_expression(nodes, r)),
        _ => false,
    }
}

/// `func isNarrowableOperand`.
fn is_narrowable_operand(nodes: &[Node], expr: NodeId) -> bool {
    match nodes[expr].kind {
        Kind::ParenthesizedExpression => nodes[expr]
            .expression()
            .is_some_and(|e| is_narrowable_operand(nodes, e)),
        Kind::BinaryExpression => {
            let e = nodes[expr].as_binary_expression();
            match e.operator_token.map(|t| nodes[t].kind) {
                Some(Kind::EqualsToken) => e.left.is_some_and(|l| is_narrowable_operand(nodes, l)),
                Some(Kind::CommaToken) => e.right.is_some_and(|r| is_narrowable_operand(nodes, r)),
                _ => contains_narrowable_reference(nodes, expr),
            }
        }
        _ => contains_narrowable_reference(nodes, expr),
    }
}

/// `func isNarrowingTypeOfOperands`.
fn is_narrowing_type_of_operands(nodes: &[Node], expr1: NodeId, expr2: NodeId) -> bool {
    is_type_of_expression(&nodes[expr1])
        && nodes[expr1]
            .expression()
            .is_some_and(|e| is_narrowable_operand(nodes, e))
        && is_string_literal_like(&nodes[expr2])
}
