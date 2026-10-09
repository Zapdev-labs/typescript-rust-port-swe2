// Ported from tsc/internal/checker/nodebuilder.go @
// ec47d33c23e464a17cdf2475632cba629bee8763 — `NodeBuilder` (the
// `NodeBuilderInterface` implementation), `VerbosityContext`, the
// hover-simplification helpers, and the `Checker::getNodeBuilder*`
// entry points.
//
// PORT notes:
//
// - `*ast.Node` → `Option<NodeId>` where nil-able (`NodeId` where Go
//   asserts non-nil through usage), `*ast.Symbol` → `SymbolId`,
//   `*Type` → `TypeId`, `*Signature` → `SignatureId`,
//   `*IndexInfo` → `IndexInfoId`, `*TypePredicate` → `&TypePredicate`.
// - `ch *Checker` / `pc` / `e *printer.EmitContext` handling: methods take
//   `c: &mut Checker` explicitly (SPEC §5.4); `EmitContext` and
//   `PseudoChecker` are stored on `NodeBuilderImpl`.
// - Go stores `b.impl.ctx *NodeBuilderContext` and swaps pointers in
//   `enterContext`/`popContext`; the port moves the whole
//   `NodeBuilderContext` value onto `ctx_stack` (Go's nil ctx on an empty
//   stack is `NodeBuilderContext::default()`).
// - Every public entry point takes `nodes: &mut Vec<ast::Node>` — the
//   arena of `enclosingDeclaration`'s file (which is also where
//   synthesized nodes are minted; `enter_context` sets the factory's
//   `file_index` to match). Reads of foreign-file nodes route through
//   `Checker::program_nodes`.
// - `releaseNodes`' `EmitContext().Factory.ReleaseArenas()` has no
//   counterpart in the ported arena model (`Vec<Node>` arenas are owned by
//   the program/source files) — `get_node_builder` documents the omission.

use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, NodeId, SymbolId};
use tsc_nodebuilder as nodebuilder;
use tsc_printer::EmitContext;

use crate::checker_core::Checker;
use crate::checker_types::Host;
use crate::nodebuilderimpl::{NodeBuilderContext, NodeBuilderImpl};
use crate::symboltracker::new_symbol_tracker_impl;
use crate::types::{IndexInfoId, SignatureId, TypeId, TypePredicate};

/// `type NodeBuilder struct` (nodebuilder.go). `impl_` is the
/// `NodeBuilderImpl<'static>` (its `ch *Checker` back-pointer is an
/// explicit `&mut Checker` parameter on the methods; its `f`/`e`/`pc`
/// members live on the struct).
pub struct NodeBuilder {
    /// `ctxStack` — Go stores `*NodeBuilderContext` pointers pushed in
    /// `enterContext`; here the whole context value is pushed/popped.
    pub ctx_stack: Vec<NodeBuilderContext>,
    /// `host`.
    pub host: Option<Rc<dyn Host>>,
    /// `impl`.
    pub impl_: Option<Box<NodeBuilderImpl<'static>>>,
    /// `verbosity` — nil for non-hover callers.
    pub verbosity: Option<Box<VerbosityContext>>,
}

/// `type VerbosityContext struct` (nodebuilder.go) — controls
/// hover-expansion behavior in the node builder. `None` on
/// `NodeBuilder::verbosity` means no expansion (non-hover callers).
/// Level 0 = default hover (`max_expansion_depth` = 0; detects
/// expandability without expanding). Level 1+ = expansion enabled
/// (`max_expansion_depth` = Level).
#[derive(Default)]
pub struct VerbosityContext {
    /// `Level` — 0 = default (no expansion), 1+ = expansion depth.
    pub level: i32,
    /// `MaxTruncationLength` — 0 = use default.
    pub max_truncation_length: i32,
    /// `CanIncreaseVerbosity` — output: whether increasing Level would
    /// reveal more.
    pub can_increase_verbosity: bool,
    /// `Truncated` — output: whether output was truncated.
    pub truncated: bool,
}

impl NodeBuilder {
    fn impl_mut(&mut self) -> &mut NodeBuilderImpl<'static> {
        self.impl_.as_deref_mut().expect("NodeBuilder without impl")
    }

    /// `EmitContext() *printer.EmitContext` — implements
    /// `NodeBuilderInterface`.
    pub fn emit_context(&self) -> std::rc::Rc<std::cell::RefCell<EmitContext>> {
        self.impl_.as_ref().expect("NodeBuilder without impl").e.clone()
    }

    /// `(b *NodeBuilder) enterContext`.
    pub(crate) fn enter_context(
        &mut self,
        c: &mut Checker,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) {
        let mut verbosity_level = -1;
        let mut max_truncation_length = 0;
        if let Some(verbosity) = &self.verbosity {
            verbosity_level = verbosity.level;
            max_truncation_length = verbosity.max_truncation_length;
        }
        let enclosing_file = match enclosing_declaration {
            Some(decl) => {
                let nodes = c.program_nodes(decl);
                ast::get_source_file_of_node(Some(decl), &nodes)
            }
            None => None,
        };
        let impl_ = self.impl_mut();
        // PORT: synthesized nodes are minted into the enclosing file's
        // arena, so the factory's `file_index` tracks it. With no enclosing
        // declaration the factory's current index is kept.
        if let Some(file) = enclosing_file {
            impl_.f.set_file_index(file.file_index());
        }
        let old_ctx = std::mem::replace(
            &mut impl_.ctx,
            NodeBuilderContext {
                host: self.host.clone(),
                tracker: None,
                flags,
                internal_flags,
                max_expansion_depth: verbosity_level,
                max_truncation_length,
                enclosing_declaration,
                enclosing_file,
                infer_type_parameters: Vec::new(),
                symbol_depth: FxHashMap::default(),
                tracked_symbols: std::rc::Rc::new(std::cell::RefCell::new(Vec::new())),
                reverse_mapped_stack: Vec::new(),
                enclosing_symbol_types: FxHashMap::default(),
                remapped_symbol_references: FxHashMap::default(),
                reported_diagnostic: std::rc::Rc::new(std::cell::Cell::new(false)),
                ..Default::default()
            },
        );
        self.ctx_stack.push(old_ctx);
        // `tracker = NewSymbolTrackerImpl(b.impl.ctx, tracker)` —
        // the wrapper shares the new context's `tracked_symbols` /
        // `reported_diagnostic` cells (see symboltracker.rs).
        let tracker = new_symbol_tracker_impl(&impl_.ctx, tracker, c.symbol_arena.clone());
        impl_.ctx.tracker = Some(std::rc::Rc::new(std::cell::RefCell::new(tracker)));
    }

    /// `(b *NodeBuilder) propagateVerbosityOut` — copies expansion signals
    /// from the context to the VerbosityContext output.
    fn propagate_verbosity_out(&mut self) {
        // Only set to true, never clear — multiple calls share the
        // same VerbosityContext.
        let (can_increase, truncated) = {
            let ctx = &self.impl_mut().ctx;
            (ctx.can_increase_expansion_depth, ctx.expansion_truncated)
        };
        if let Some(verbosity) = self.verbosity.as_mut() {
            if can_increase {
                verbosity.can_increase_verbosity = true;
            }
            if truncated {
                verbosity.truncated = true;
            }
        }
    }

    /// `(b *NodeBuilder) popContext`.
    fn pop_context(&mut self) {
        match self.ctx_stack.pop() {
            Some(ctx) => self.impl_mut().ctx = ctx,
            // Go sets `b.impl.ctx = nil`; the port restores the zero value.
            None => self.impl_mut().ctx = NodeBuilderContext::default(),
        }
    }

    /// `(b *NodeBuilder) exitContext`.
    pub(crate) fn exit_context(
        &mut self,
        nodes: &[ast::Node],
        result: Option<NodeId>,
    ) -> Option<NodeId> {
        self.propagate_verbosity_out();
        self.exit_context_check(nodes);
        let encountered_error = self.impl_mut().ctx.encountered_error;
        self.pop_context();
        if encountered_error {
            return None;
        }
        result
    }

    /// `(b *NodeBuilder) exitContextSlice`.
    pub(crate) fn exit_context_slice(
        &mut self,
        nodes: &[ast::Node],
        result: Vec<NodeId>,
    ) -> Vec<NodeId> {
        self.propagate_verbosity_out();
        self.exit_context_check(nodes);
        let encountered_error = self.impl_mut().ctx.encountered_error;
        self.pop_context();
        if encountered_error {
            return Vec::new();
        }
        result
    }

    /// `(b *NodeBuilder) exitContextCheck`.
    fn exit_context_check(&mut self, nodes: &[ast::Node]) {
        let impl_ = self.impl_mut();
        if impl_.ctx.truncating
            && impl_
                .ctx
                .flags
                .intersects(nodebuilder::Flags::NO_TRUNCATION)
            && let Some(tracker) = impl_.ctx.tracker.as_mut()
        {
            tracker.borrow_mut().report_truncation_error(nodes);
        }
    }

    /// `IndexInfoToIndexSignatureDeclaration` — implements
    /// `NodeBuilderInterface`.
    pub fn index_info_to_index_signature_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        info: IndexInfoId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let info = c.index_info_arena.get(info).clone();
        let result = self
            .impl_mut()
            .index_info_to_index_signature_declaration_helper(c, nodes, &info, None);
        self.exit_context(nodes, Some(result))
    }

    /// `SerializeReturnTypeForSignature` — implements
    /// `NodeBuilderInterface`.
    pub fn serialize_return_type_for_signature(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        signature_declaration: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let signature = c.get_signature_from_declaration(signature_declaration);
        let impl_ = self.impl_mut();
        let (_expanded, cleanup) = impl_.enter_signature_scope(c, nodes, signature);
        let result = impl_.serialize_return_type_for_signature(c, nodes, signature, true);
        cleanup.restore(impl_, nodes);
        self.exit_context(nodes, result)
    }

    /// `(b *NodeBuilder) SerializeTypeParametersForSignature`.
    pub fn serialize_type_parameters_for_signature(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        signature_declaration: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Vec<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let symbol = c.get_symbol_of_declaration(signature_declaration);
        let type_params = self.symbol_to_type_parameter_declarations(
            c,
            nodes,
            symbol.unwrap_or(SymbolId::NONE),
            enclosing_declaration,
            flags,
            internal_flags,
            tracker,
        );
        self.exit_context_slice(nodes, type_params)
    }

    /// `SerializeTypeForDeclaration` — implements `NodeBuilderInterface`.
    pub fn serialize_type_for_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        declaration: NodeId,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self.impl_mut().serialize_type_for_declaration(
            c,
            nodes,
            Some(declaration),
            None,
            Some(symbol),
            true,
        );
        self.exit_context(nodes, Some(result))
    }

    /// `SerializeTypeForExpression` — implements `NodeBuilderInterface`.
    pub fn serialize_type_for_expression(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        expr: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self
            .impl_mut()
            .serialize_type_for_expression(c, nodes, expr);
        self.exit_context(nodes, Some(result))
    }

    /// `SignatureToSignatureDeclaration` — implements
    /// `NodeBuilderInterface`.
    pub fn signature_to_signature_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        signature: SignatureId,
        kind: ast::Kind,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self
            .impl_mut()
            .signature_to_signature_declaration_helper(
                c,
                nodes,
                signature,
                kind,
                Default::default(),
            );
        self.exit_context(nodes, Some(result))
    }

    /// `ExpandSymbolForHover` — produces declaration nodes for a symbol
    /// with verbosity level support.
    pub fn expand_symbol_for_hover(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: ast::SymbolFlags,
    ) -> Vec<NodeId> {
        self.enter_context(
            c,
            None,
            nodebuilder::Flags::IGNORE_ERRORS
                | nodebuilder::Flags::MULTILINE_OBJECT_LITERALS
                | nodebuilder::Flags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE,
            nodebuilder::InternalFlags::NONE,
            None,
        );

        // Push the declared type onto the type stack to prevent
        // re-expansion. We push a nil sentinel after the real type so that
        // isTypeOnStack (which skips the last element) still checks
        // declaredType.
        let declared_type = c.get_declared_type_of_symbol(symbol);
        {
            let ctx = &mut self.impl_mut().ctx;
            ctx.type_stack.push(declared_type);
            // Go's nil sentinel — `TypeId::NONE` never equals a real type.
            ctx.type_stack.push(TypeId::NONE);
        }

        let hover_nodes = self.impl_mut().expand_symbol_for_hover(c, nodes, symbol);

        {
            let ctx = &mut self.impl_mut().ctx;
            ctx.type_stack.truncate(ctx.type_stack.len() - 2);
        }

        self.propagate_verbosity_out();

        // Simplify declarations by applying original modifiers.
        let declarations = c.symbol_arena.borrow()[symbol.index()].declarations.clone();
        let mut result = Vec::with_capacity(hover_nodes.len());
        for node in hover_nodes {
            match nodes[node].kind {
                ast::Kind::ClassDeclaration => {
                    result.push(simplify_class_declaration(
                        c,
                        &mut self.impl_mut().f,
                        nodes,
                        node,
                        &declarations,
                    ));
                }
                ast::Kind::EnumDeclaration => {
                    result.push(simplify_modifiers(
                        c,
                        &mut self.impl_mut().f,
                        nodes,
                        node,
                        &declarations,
                        |n| ast::is_enum_declaration(n),
                    ));
                }
                ast::Kind::InterfaceDeclaration => {
                    if meaning.intersects(ast::SymbolFlags::INTERFACE) {
                        result.push(simplify_modifiers(
                            c,
                            &mut self.impl_mut().f,
                            nodes,
                            node,
                            &declarations,
                            |n| ast::is_interface_declaration(n),
                        ));
                    }
                }
                ast::Kind::ModuleDeclaration => {
                    result.push(simplify_modifiers(
                        c,
                        &mut self.impl_mut().f,
                        nodes,
                        node,
                        &declarations,
                        |n| ast::is_module_declaration(n),
                    ));
                }
                _ => {}
            }
        }

        self.exit_context_slice(nodes, result)
    }

    /// `SymbolToEntityName` — implements `NodeBuilderInterface`.
    pub fn symbol_to_entity_name(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: ast::SymbolFlags,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self
            .impl_mut()
            .symbol_to_name(c, nodes, symbol, meaning, false);
        self.exit_context(nodes, result)
    }

    /// `SymbolToExpression` — implements `NodeBuilderInterface`.
    pub fn symbol_to_expression(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: ast::SymbolFlags,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self
            .impl_mut()
            .symbol_to_expression(c, nodes, symbol, meaning);
        self.exit_context(nodes, result)
    }

    /// `SymbolToNode` — implements `NodeBuilderInterface`.
    pub fn symbol_to_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        meaning: ast::SymbolFlags,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self.impl_mut().symbol_to_node(c, nodes, symbol, meaning);
        self.exit_context(nodes, result)
    }

    /// `SymbolToParameterDeclaration` — implements `NodeBuilderInterface`.
    /// (Go declares this on a `NodeBuilder` value receiver; the port keeps
    /// `&mut self` since `enter_context` mutates.)
    pub fn symbol_to_parameter_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self
            .impl_mut()
            .symbol_to_parameter_declaration(c, nodes, symbol, false);
        self.exit_context(nodes, result)
    }

    /// `SymbolToTypeParameterDeclarations` — implements
    /// `NodeBuilderInterface`.
    pub fn symbol_to_type_parameter_declarations(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Vec<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self
            .impl_mut()
            .symbol_to_type_parameter_declarations(c, nodes, symbol);
        self.exit_context_slice(nodes, result)
    }

    /// `TypeParameterToDeclaration` — implements `NodeBuilderInterface`.
    pub fn type_parameter_to_declaration(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        parameter: TypeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self
            .impl_mut()
            .type_parameter_to_declaration(c, nodes, parameter);
        self.exit_context(nodes, Some(result))
    }

    /// `TypePredicateToTypePredicateNode` — implements
    /// `NodeBuilderInterface`.
    pub fn type_predicate_to_type_predicate_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        predicate: Option<&TypePredicate>,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = predicate
            .map(|p| self.impl_mut().type_predicate_to_type_predicate_node(c, nodes, p));
        self.exit_context(nodes, result)
    }

    /// `TypeToTypeNode` — implements `NodeBuilderInterface`.
    pub fn type_to_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        typ: TypeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self.impl_mut().type_to_type_node(c, nodes, typ);
        self.exit_context(nodes, result)
    }

    /// `(b *NodeBuilder) TryJSTypeNodeToTypeNode`.
    pub fn try_js_type_node_to_type_node(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        node: NodeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        tracker: Option<Box<dyn nodebuilder::SymbolTracker>>,
    ) -> Option<NodeId> {
        self.enter_context(c, enclosing_declaration, flags, internal_flags, tracker);
        let result = self
            .impl_mut()
            .try_js_type_node_to_type_node(c, nodes, node);
        self.exit_context(nodes, result)
    }
}

/// `simplifyClassDeclaration` (nodebuilder.go) — returns the declaration
/// with the original declaration's modifiers minus export/ambient.
///
/// PORT: `symbol.Declarations` is staged by the caller (the symbol arena
/// can't be borrowed across the factory calls); each declaration is read
/// in its own file arena via `program_nodes` since sibling declarations
/// may be foreign to `nodes`.
fn simplify_class_declaration(
    c: &Checker,
    f: &mut ast::NodeFactory<'_>,
    nodes: &mut Vec<ast::Node>,
    class_decl: NodeId,
    declarations: &[NodeId],
) -> NodeId {
    let class_declarations: Vec<NodeId> = declarations
        .iter()
        .copied()
        .filter(|&d| {
            let dn = c.program_nodes(d);
            ast::is_class_like(Some(d), &dn)
        })
        .collect();
    let original_class_decl = if !class_declarations.is_empty() {
        class_declarations[0]
    } else {
        class_decl
    };
    let (modifiers, is_anonymous) = {
        let dn = c.program_nodes(original_class_decl);
        (
            dn[original_class_decl].modifier_flags()
                & !(ast::ModifierFlags::EXPORT | ast::ModifierFlags::AMBIENT),
            ast::is_class_expression(&dn[original_class_decl]),
        )
    };
    let mut class_decl = class_decl;
    if is_anonymous {
        let (type_parameters, heritage_clauses, members, modifier_list) = {
            let cd = nodes[class_decl].as_class_declaration();
            (
                cd.class_like_base.type_parameters.clone(),
                cd.class_like_base.heritage_clauses.clone(),
                cd.class_like_base.members.clone(),
                nodes[class_decl].modifiers().cloned(),
            )
        };
        class_decl = f
            .update_class_declaration(
                nodes,
                class_decl,
                modifier_list,
                None,
                type_parameters,
                heritage_clauses,
                members,
            )
            .unwrap_or(class_decl);
    }
    let modifier_nodes = {
        let mut create_modifier = |kind: ast::Kind| -> NodeId { f.new_token(nodes, kind) };
        ast::create_modifiers_from_modifier_flags(modifiers, &mut create_modifier)
    };
    let modifier_list = f.new_modifier_list(nodes, modifier_nodes);
    ast::replace_modifiers(f, nodes, class_decl, Some(modifier_list)).unwrap_or(class_decl)
}

/// `simplifyModifiers` (nodebuilder.go). PORT: `isDeclKind` is evaluated
/// per-declaration in that declaration's own arena (sibling declarations
/// may live in other files).
fn simplify_modifiers(
    c: &Checker,
    f: &mut ast::NodeFactory<'_>,
    nodes: &mut Vec<ast::Node>,
    new_decl: NodeId,
    declarations: &[NodeId],
    is_decl_kind: impl Fn(&ast::Node) -> bool,
) -> NodeId {
    let decls: Vec<NodeId> = declarations
        .iter()
        .copied()
        .filter(|&d| {
            let dn = c.program_nodes(d);
            is_decl_kind(&dn[d])
        })
        .collect();
    let decl_with_modifiers = decls.first().copied().unwrap_or(new_decl);
    let modifiers = {
        let dn = c.program_nodes(decl_with_modifiers);
        dn[decl_with_modifiers].modifier_flags()
            & !(ast::ModifierFlags::EXPORT | ast::ModifierFlags::AMBIENT)
    };
    let modifier_nodes = {
        let mut create_modifier = |kind: ast::Kind| -> NodeId { f.new_token(nodes, kind) };
        ast::create_modifiers_from_modifier_flags(modifiers, &mut create_modifier)
    };
    let modifier_list = f.new_modifier_list(nodes, modifier_nodes);
    ast::replace_modifiers(f, nodes, new_decl, Some(modifier_list)).unwrap_or(new_decl)
}

/// `NewNodeBuilder(ch, e)`.
pub fn new_node_builder(c: &Checker, e: EmitContext) -> NodeBuilder {
    new_node_builder_ex(c, e, FxHashMap::default())
}

/// `NewNodeBuilderEx(ch, e, idToSymbol)`.
pub fn new_node_builder_ex(
    c: &Checker,
    e: EmitContext,
    id_to_symbol: FxHashMap<NodeId, SymbolId>,
) -> NodeBuilder {
    let impl_ = crate::nodebuilderimpl::new_node_builder_impl(c, e, id_to_symbol);
    NodeBuilder {
        impl_: Some(Box::new(impl_)),
        ctx_stack: Vec::with_capacity(1),
        host: c.program.clone().map(|p| p as Rc<dyn Host>),
        verbosity: None,
    }
}

impl Checker {
    /// `(c *Checker) getNodeBuilder` — lazily creates (or reuses) the
    /// type-to-string node builder.
    ///
    /// PORT: Go returns `(*NodeBuilder, func())` where the cleanup releases
    /// factory arenas; `ReleaseArenas` has no counterpart here (`Vec<Node>`
    /// arenas are file-owned), so this returns the builder by value — the
    /// caller stores it back when done (`take`/`put` instead of Go's
    /// shared pointer).
    pub fn get_node_builder(&mut self) -> NodeBuilder {
        if let Some(b) = self.type_to_string_nodebuilder.take() {
            return *b;
        }
        self.get_node_builder_ex(FxHashMap::default())
    }

    /// `(c *Checker) getNodeBuilderEx`.
    pub fn get_node_builder_ex(
        &mut self,
        id_to_symbol: FxHashMap<NodeId, SymbolId>,
    ) -> NodeBuilder {
        new_node_builder_ex(self, EmitContext::new(), id_to_symbol)
    }
}
