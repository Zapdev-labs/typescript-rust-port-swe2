// Ported from tsc/internal/checker/printer.go @
// ec47d33c23e464a17cdf2475632cba629bee8763
//
// Checker-side printing helpers — `createPrinterWith*`, `TypeToString`,
// `SymbolToString`, `SignatureToString`, `typePredicateToString`,
// `valueToString`, `formatUnionTypes`, `TypeToTypeNode`,
// `SignatureToSignatureDeclaration`, `ExpandSymbolForHover`,
// `TypeParameterToStringEx`, `TypeToTypeNodeEx`,
// `TypePredicateToTypePredicateNode`.
//
// PORT notes:
//
// - Go's `createPrinterWithX(emitContext)` gains `nodes`/`symbols` borrow
//   parameters because `Printer::new` takes `&mut Vec<Node>` +
//   `&[Symbol]` (the arenas Go reaches through pointers). Callers hold the
//   `RefMut`/`Ref` guards (`emit_context`, `arena`, `symbols` locals) for
//   the printer's whole scope — they cannot be created inside the helpers.
// - `getNodeBuilder()`/`getNodeBuilderEx()` return the `NodeBuilder` by
//   value; Go's `release()` callback is spelled as putting the pooled
//   builder back into `c.type_to_string_nodebuilder` — see
//   `release_node_builder`. `getNodeBuilderEx` callers in Go do not release
//   (fresh builders), so the `*_ex`/`TypeToTypeNode` helpers drop theirs.
// - `nodeBuilder.EmitContext()` in Go is a `*printer.EmitContext`; here the
//   impl stores `Rc<RefCell<EmitContext>>` (`NodeBuilderImpl::e`), so the
//   printer borrows it through `borrow_mut` — same shared context object.
// - The synthesized nodes are minted into the enclosing file's node arena
//   (`enter_context` sets `f.file_index` from the enclosing declaration's
//   source file), so `nodes` for the builder and the `Printer` are the
//   `program.nodes_mut(file_index)` arena of that file — or the factory's
//   current file index when there is no enclosing declaration. `program`
//   is `Rc`-cloned out of `self` first so the returned `RefMut` does not
//   keep `&self` borrowed across the `&mut self` builder calls.
// - `vc *VerbosityContext` is `Option<&mut VerbosityContext>`: the caller's
//   value is swapped into `NodeBuilder::verbosity` (`Option<Box<..>>`) and
//   written back afterwards, preserving `propagate_verbosity_out`'s
//   writes to `Truncated`/`CanIncreaseVerbosity`.

use rustc_hash::FxHashMap;

use tsc_ast::{self as ast, Node, NodeId, Symbol, SymbolId};
use tsc_core::tristate::Tristate;
use tsc_evaluator as evaluator;
use tsc_nodebuilder as nodebuilder;
use tsc_printer::{
    self as printer, EmitContext, EmitTextWriter, Printer, PrinterOptions, TextWriter,
};

use crate::checker_core::Checker;
use crate::nodebuilder::{NodeBuilder, VerbosityContext};
use crate::types::{
    SignatureFlags, SignatureId, SymbolFormatFlags, TypeFlags, TypeFormatFlags, TypeId,
    TypePredicate,
};

/// `ArenaView` — a read view over a file's node arena that is either an
/// `Rc` snapshot ([`Program::nodes`]) or a borrow of the caller's
/// checked-out working buffer. Deref/Index resolve through the slice
/// either way, so `view[id]`/`view.len()` work unchanged.
pub enum ArenaView<'x> {
    Snapshot(std::rc::Rc<Vec<Node>>),
    Working(&'x [Node]),
}

impl<'x> std::ops::Deref for ArenaView<'x> {
    type Target = [Node];

    fn deref(&self) -> &[Node] {
        match self {
            ArenaView::Snapshot(rc) => rc,
            ArenaView::Working(nodes) => nodes,
        }
    }
}

thread_local! {
    /// Extra live working buffers that cannot be threaded through a single
    /// `work` slice — e.g. while `nodecopy` visits a scratch clone of a
    /// foreign source arena, the destination arena buffer is immutably
    /// borrowed (`nodes.as_slice()` → `extra_live`) for the visit, and
    /// nested walks (enclosing-declaration chains, symbol accessibility)
    /// may hit node ids belonging to *either* buffer (Go follows raw
    /// pointers). Because the registered buffer is immutably borrowed for
    /// the whole scope it cannot change, so a snapshot `Rc` is faithful.
    static LIVE_ARENAS: std::cell::RefCell<Vec<std::rc::Rc<Vec<Node>>>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// RAII registration of an extra live arena buffer. While the guard is
/// alive, `arena_view` resolves reads for the buffer's file index against
/// a clone of the buffer rather than a program snapshot.
pub struct LiveArenaGuard;

impl LiveArenaGuard {
    /// `nodes` should stay immutably borrowed for the guard's lifetime
    /// (e.g. `vec.as_slice()` while `vec` is borrowed `&`) — the registry
    /// keeps a clone, so reads reflect the buffer at registration time.
    pub fn register(nodes: &[Node]) -> Self {
        LIVE_ARENAS.with(|r| {
            r.borrow_mut()
                .push(std::rc::Rc::new(nodes.to_vec()))
        });
        LiveArenaGuard
    }
}

impl Drop for LiveArenaGuard {
    fn drop(&mut self) {
        LIVE_ARENAS.with(|r| {
            r.borrow_mut().pop();
        });
    }
}

fn live_arena_lookup(fi: u32) -> Option<std::rc::Rc<Vec<Node>>> {
    LIVE_ARENAS.with(|r| {
        r.borrow()
            .iter()
            .rev()
            .find(|buf| buf.first().is_some_and(|n| n.id.file_index() == fi))
            .cloned()
    })
}

/// `buf` physically holds `id` — a node's packed `id` matches its slot only
/// in the buffer it was minted into (per-file arenas alias `local_index`).
pub(crate) fn buffer_resolves_id(buf: &[Node], id: NodeId) -> bool {
    (id.local_index() as usize) < buf.len() && buf[id].id == id
}

pub(crate) fn live_arena_lookup_for(id: NodeId) -> Option<std::rc::Rc<Vec<Node>>> {
    LIVE_ARENAS.with(|r| {
        r.borrow()
            .iter()
            .rev()
            .find(|buf| buffer_resolves_id(buf, id))
            .cloned()
    })
}

/// True when every id reachable from `root` physically lives in `buf` —
/// i.e. `deep_clone_node(buf, root)` can visit the whole subtree without
/// crossing arena buffers. Go's clone follows heap pointers into any
/// arena; the port's visitor can only read `cx.nodes`, so a tree minted
/// in a since-dropped scratch buffer (or one embedding foreign-arena ids)
/// is not clonable and the caller must regenerate it.
pub(crate) fn subtree_clonable_in(buf: &[Node], root: NodeId) -> bool {
    let mut stack = vec![root];
    let mut seen: rustc_hash::FxHashSet<NodeId> = rustc_hash::FxHashSet::default();
    while let Some(id) = stack.pop() {
        if id.is_none() || !seen.insert(id) {
            continue;
        }
        if !buffer_resolves_id(buf, id) {
            return false;
        }
        buf[id].for_each_child(buf, &mut |child| {
            stack.push(child);
            false
        });
    }
    true
}

/// `arena_view` for callers that must deref a specific `id`: picks the
/// buffer where `id` actually resolves (a scratch/live clone can share the
/// destination arena's `file_index` while `work` is a different buffer with
/// the same index). Falls back to `arena_view`'s fi-based selection.
pub fn resolve_arena_for<'x>(
    program: &std::rc::Rc<dyn crate::checker_types::Program>,
    work: &'x [Node],
    id: NodeId,
) -> ArenaView<'x> {
    if buffer_resolves_id(work, id) {
        return ArenaView::Working(work);
    }
    if let Some(extra) = live_arena_lookup_for(id) {
        return ArenaView::Snapshot(extra);
    }
    let snap = program.nodes(id.file_index());
    if buffer_resolves_id(&snap, id) {
        return ArenaView::Snapshot(snap);
    }
    arena_view(program, work, id.file_index())
}

/// `program.nodes(fi)` that stays correct while the caller holds an
/// `ArenaMut`/`ArenaCheckout` on arena `fi`: when `work` IS that arena's
/// working buffer (its first node's `file_index` is `fi`), borrowing it
/// reproduces Go's live-slice semantics — synthetic nodes minted
/// mid-operation are visible to nested reads. Next, buffers registered via
/// [`LiveArenaGuard`] are checked. Any other `fi` takes a normal snapshot.
pub fn arena_view<'x>(
    program: &std::rc::Rc<dyn crate::checker_types::Program>,
    work: &'x [Node],
    fi: u32,
) -> ArenaView<'x> {
    if work.first().is_some_and(|n| n.id.file_index() == fi) {
        ArenaView::Working(work)
    } else if let Some(extra) = live_arena_lookup(fi) {
        ArenaView::Snapshot(extra)
    } else {
        ArenaView::Snapshot(program.nodes(fi))
    }
}

/// `arena_view` through the checker's program handle.
pub fn checker_arena_view<'x>(
    c: &Checker,
    work: &'x [Node],
    fi: u32,
) -> ArenaView<'x> {
    arena_view(c.program.as_ref().expect("program"), work, fi)
}

/// `createPrinterWithDefaults`.
fn create_printer_with_defaults<'a>(
    emit_context: &'a mut EmitContext,
    nodes: &'a mut Vec<Node>,
    symbols: &'a [Symbol],
) -> Printer<'a> {
    Printer::new(
        PrinterOptions::default(),
        printer::PrintHandlers::default(),
        emit_context,
        nodes,
        symbols,
    )
}

/// `create_printerWithRemoveComments`.
fn create_printer_with_remove_comments<'a>(
    emit_context: &'a mut EmitContext,
    nodes: &'a mut Vec<Node>,
    symbols: &'a [Symbol],
) -> Printer<'a> {
    Printer::new(
        PrinterOptions {
            remove_comments: true,
            ..Default::default()
        },
        printer::PrintHandlers::default(),
        emit_context,
        nodes,
        symbols,
    )
}

/// `createPrinterWithRemoveCommentsOmitTrailingSemicolon`.
fn create_printer_with_remove_comments_omit_trailing_semicolon<'a>(
    emit_context: &'a mut EmitContext,
    nodes: &'a mut Vec<Node>,
    symbols: &'a [Symbol],
) -> Printer<'a> {
    Printer::new(
        PrinterOptions {
            remove_comments: true,
            omit_trailing_semicolon: true,
            ..Default::default()
        },
        printer::PrintHandlers::default(),
        emit_context,
        nodes,
        symbols,
    )
}

/// `createPrinterWithRemoveCommentsOmitTrailingSemicolonNeverAsciiEscape`.
fn create_printer_with_remove_comments_omit_trailing_semicolon_never_ascii_escape<'a>(
    emit_context: &'a mut EmitContext,
    nodes: &'a mut Vec<Node>,
    symbols: &'a [Symbol],
) -> Printer<'a> {
    Printer::new(
        PrinterOptions {
            remove_comments: true,
            omit_trailing_semicolon: true,
            never_ascii_escape: true,
            ..Default::default()
        },
        printer::PrintHandlers::default(),
        emit_context,
        nodes,
        symbols,
    )
}

/// `createPrinterWithRemoveCommentsNeverAsciiEscape`.
fn create_printer_with_remove_comments_never_ascii_escape<'a>(
    emit_context: &'a mut EmitContext,
    nodes: &'a mut Vec<Node>,
    symbols: &'a [Symbol],
) -> Printer<'a> {
    Printer::new(
        PrinterOptions {
            remove_comments: true,
            never_ascii_escape: true,
            ..Default::default()
        },
        printer::PrintHandlers::default(),
        emit_context,
        nodes,
        symbols,
    )
}

/// `toNodeBuilderFlags`.
fn to_node_builder_flags(flags: TypeFormatFlags) -> nodebuilder::Flags {
    nodebuilder::Flags(flags.0 & TypeFormatFlags::NODE_BUILDER_FLAGS_MASK.0)
}

/// Swaps `vc` into `node_builder.verbosity` (`oldVerbosity`/`= vc` in Go).
/// Returns the previous verbosity; `put_verbosity` is the matching `defer`.
fn take_verbosity(
    node_builder: &mut NodeBuilder,
    vc: Option<&mut VerbosityContext>,
) -> Option<Box<VerbosityContext>> {
    let old = node_builder.verbosity.take();
    node_builder.verbosity = vc.map(|v| Box::new(std::mem::take(v)));
    old
}

/// `nodeBuilder.verbosity = oldVerbosity` (the Go `defer`) — writes the
/// builder-mutated verbosity back into the caller's `vc` first.
fn put_verbosity(
    node_builder: &mut NodeBuilder,
    vc: Option<&mut VerbosityContext>,
    old: Option<Box<VerbosityContext>>,
) {
    if let Some(vc) = vc
        && let Some(b) = node_builder.verbosity.take()
    {
        *vc = *b;
    }
    node_builder.verbosity = old;
}

/// The Go `release()` callback of `getNodeBuilder` — returns the pooled
/// builder to `c.typeToStringNodeBuilder`.
fn release_node_builder(c: &mut Checker, node_builder: NodeBuilder<'static>) {
    c.type_to_string_nodebuilder = Some(Box::new(node_builder));
}

/// The arena synthesized nodes are minted into — `enter_context` sets the
/// factory's `file_index` to the enclosing declaration's file, so the same
/// arena serves the builder calls and the `Printer`'s `nodes` borrow. With
/// no enclosing declaration the factory's current index is used (the
/// builder is pooled across calls).
fn builder_arena_index(node_builder: &NodeBuilder, enclosing_declaration: Option<NodeId>) -> u32 {
    enclosing_declaration
        .map(|d| d.file_index())
        .unwrap_or_else(|| {
            node_builder
                .impl_
                .as_ref()
                .expect("NodeBuilder without impl")
                .f
                .file_index()
        })
}

impl Checker {
    /// `(c *Checker) TypeToString`.
    ///
    /// PORT: `impl Into<Option<TypeId>>` accepts both `TypeId` and
    /// `Option<TypeId>` callers (Go's `*Type` is nilable); `None` panics
    /// like Go's nil deref.
    pub fn type_to_string(&mut self, t: impl Into<Option<TypeId>>) -> String {
        self.type_to_string_private(t.into().expect("TypeToString: nil type"), None)
    }

    /// `(c *Checker) typeToString`.
    pub(crate) fn type_to_string_private(
        &mut self,
        t: TypeId,
        enclosing_declaration: Option<NodeId>,
    ) -> String {
        self.type_to_string_ex(
            t,
            enclosing_declaration,
            TypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
                | TypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE,
            None,
        )
    }

    /// `(c *Checker) TypeToStringEx` + `typeToStringEx` (the Go public
    /// wrapper forwards straight through).
    pub fn type_to_string_ex(
        &mut self,
        t: TypeId,
        enclosing_declaration: Option<NodeId>,
        flags: TypeFormatFlags,
        vc: Option<&mut VerbosityContext>,
    ) -> String {
        // Serialization of types can lead to (lazy) resolution of members,
        // which can cause diagnostics that again require serialization of
        // types. This can potentially result in infinite recursion and
        // stack overflows. To prevent that, after a certain number of
        // recursive invocations the function simply returns "?".
        if self.serialization_level >= crate::checker_types::MAX_SERIALIZATION_LEVEL {
            return "?".into();
        }
        let mut vc = vc;
        let new_line = if flags.intersects(TypeFormatFlags::MULTILINE_OBJECT_LITERALS) {
            "\n"
        } else {
            ""
        };
        let mut writer = TextWriter::new(new_line, 0);
        let no_truncation = (vc.as_deref().map(|v| v.max_truncation_length).unwrap_or(0) == 0
            && self.compiler_options.no_error_truncation == Tristate::True)
            || flags.intersects(TypeFormatFlags::NO_TRUNCATION);
        let mut combined_flags = to_node_builder_flags(flags) | nodebuilder::Flags::IGNORE_ERRORS;
        if no_truncation {
            combined_flags = combined_flags | nodebuilder::Flags::NO_TRUNCATION;
        }
        let mut node_builder = self.get_node_builder();
        let old_verbosity = take_verbosity(&mut node_builder, vc.as_deref_mut());
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        // `nodes` — the arena guard is cloned out of `program` so it does
        // not hold a `&self` borrow (see the header note).
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        self.serialization_level += 1;
        let type_node = node_builder.type_to_type_node(
            self,
            &mut nodes,
            t,
            enclosing_declaration,
            combined_flags,
            nodebuilder::InternalFlags::NONE,
            None,
        );
        self.serialization_level -= 1;
        let Some(type_node) = type_node else {
            panic!("should always get typenode")
        };
        let emit_context_cell = node_builder
            .impl_
            .as_ref()
            .expect("NodeBuilder without impl")
            .e
            .clone();
        let mut emit_context = emit_context_cell.borrow_mut();
        let symbol_arena = self.symbol_arena.clone();
        let symbols = symbol_arena.borrow();
        let source_file =
            enclosing_declaration.and_then(|d| ast::get_source_file_of_node(Some(d), &nodes));
        // The unresolved type gets a synthesized comment on `any` to hint to
        // users that it's not a plain `any`. Otherwise, we always strip
        // comments out.
        let mut p = if t == self.unresolved_type {
            create_printer_with_defaults(&mut emit_context, &mut nodes, &symbols)
        } else {
            create_printer_with_remove_comments(&mut emit_context, &mut nodes, &symbols)
        };
        p.write(Some(type_node), source_file, &mut writer, None);
        drop(p);
        drop(symbols);
        drop(emit_context);
        drop(nodes);
        drop(program);
        put_verbosity(&mut node_builder, vc.as_deref_mut(), old_verbosity);
        release_node_builder(self, node_builder);
        let result = writer.get_text();

        let mut max_length =
            crate::nodebuilderimpl::NodeBuilderImpl::DEFAULT_MAXIMUM_TRUNCATION_LENGTH * 2;
        if let Some(vc) = vc.as_deref()
            && vc.max_truncation_length > 0
        {
            max_length = vc.max_truncation_length * 10; // hard cutoff matching Strada's absoluteMaximumLength
        }
        if no_truncation {
            max_length =
                crate::nodebuilderimpl::NodeBuilderImpl::NO_TRUNCATION_MAXIMUM_TRUNCATION_LENGTH
                    * 2;
        }
        if max_length > 0 && !result.is_empty() && result.len() as i32 >= max_length {
            if let Some(vc) = vc {
                vc.truncated = true;
            }
            let mut truncated = result;
            // Go byte-slices `result[0:maxLength-len("...")]`; stay on a
            // UTF-8 char boundary.
            let mut end = (max_length - 3) as usize;
            while !truncated.is_char_boundary(end) {
                end -= 1;
            }
            truncated.truncate(end);
            truncated.push_str("...");
            return truncated;
        }
        result
    }

    /// `(c *Checker) SymbolToString`.
    ///
    /// PORT: `impl Into<Option<SymbolId>>` accepts both `SymbolId` and
    /// `Option<SymbolId>` callers (Go's `*ast.Symbol` is nilable); `None`
    /// panics like Go's nil deref.
    pub fn symbol_to_string(&mut self, s: impl Into<Option<SymbolId>>) -> String {
        self.symbol_to_string_private(s.into().expect("SymbolToString: nil symbol"))
    }

    /// `(c *Checker) symbolToString`.
    fn symbol_to_string_private(&mut self, symbol: SymbolId) -> String {
        self.symbol_to_string_ex(
            symbol,
            None,
            ast::SymbolFlags::ALL,
            SymbolFormatFlags::ALLOW_ANY_NODE_KIND,
            None,
        )
    }

    /// `(c *Checker) SymbolToStringEx` + `symbolToStringEx`.
    ///
    /// `live_nodes` is the caller's live node buffer for resolving
    /// `enclosing_declaration` when it is a synthetic node minted outside
    /// this function's fresh arena checkout (Go follows raw pointers).
    pub fn symbol_to_string_ex(
        &mut self,
        symbol: SymbolId,
        enclosing_declaration: Option<NodeId>,
        meaning: ast::SymbolFlags,
        flags: SymbolFormatFlags,
        live_nodes: Option<&[Node]>,
    ) -> String {
        let mut writer = printer::get_single_line_string_writer();
        // `enclosing_declaration` may be a synthetic id that only resolves in
        // the caller's working buffer — register it so `arena_view`/
        // `resolve_arena_for` find it from nested calls.
        let _live_guard = live_nodes.map(LiveArenaGuard::register);

        let mut node_flags = nodebuilder::Flags::IGNORE_ERRORS;
        let mut internal_node_flags = nodebuilder::InternalFlags::NONE;
        if flags.intersects(SymbolFormatFlags::USE_ONLY_EXTERNAL_ALIASING) {
            node_flags |= nodebuilder::Flags::USE_ONLY_EXTERNAL_ALIASING;
        }
        if flags.intersects(SymbolFormatFlags::WRITE_TYPE_PARAMETERS_OR_ARGUMENTS) {
            node_flags |= nodebuilder::Flags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME;
        }
        if flags.intersects(SymbolFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE) {
            node_flags |= nodebuilder::Flags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE;
        }
        if flags.intersects(SymbolFormatFlags::DO_NOT_INCLUDE_SYMBOL_CHAIN) {
            internal_node_flags |= nodebuilder::InternalFlags::DO_NOT_INCLUDE_SYMBOL_CHAIN;
        }
        if flags.intersects(SymbolFormatFlags::WRITE_COMPUTED_PROPS) {
            internal_node_flags |= nodebuilder::InternalFlags::WRITE_COMPUTED_PROPS;
        }

        let mut node_builder = self.get_node_builder();
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        let source_file = enclosing_declaration.and_then(|d| {
            let arena = resolve_arena_for(&program, &nodes, d);
            ast::get_source_file_of_node(Some(d), &arena)
        });
        // `builder = nodeBuilder.SymbolToNode` / `SymbolToEntityName` —
        // runs before the printer is created because the printer holds
        // `&mut nodes` while `symbol_to_*` needs it mutably too.
        let entity = if flags.intersects(SymbolFormatFlags::ALLOW_ANY_NODE_KIND) {
            node_builder.symbol_to_node(
                self,
                &mut nodes,
                symbol,
                meaning,
                enclosing_declaration,
                node_flags,
                internal_node_flags,
                None,
            )
        } else {
            node_builder.symbol_to_entity_name(
                self,
                &mut nodes,
                symbol,
                meaning,
                enclosing_declaration,
                node_flags,
                internal_node_flags,
                None,
            )
        };
        let emit_context_cell = node_builder
            .impl_
            .as_ref()
            .expect("NodeBuilder without impl")
            .e
            .clone();
        let mut emit_context = emit_context_cell.borrow_mut();
        let symbol_arena = self.symbol_arena.clone();
        let symbols = symbol_arena.borrow();
        // add neverAsciiEscape for GH#39027
        let enclosing_is_source_file = enclosing_declaration.is_some_and(|d| {
            resolve_arena_for(&program, &nodes, d)[d].kind == ast::Kind::SourceFile
        });
        let mut p = if enclosing_is_source_file {
            create_printer_with_remove_comments_omit_trailing_semicolon_never_ascii_escape(
                &mut emit_context,
                &mut nodes,
                &symbols,
            )
        } else {
            create_printer_with_remove_comments_omit_trailing_semicolon(
                &mut emit_context,
                &mut nodes,
                &symbols,
            )
        };
        p.write(entity, source_file, &mut writer, None); // TODO: GH#18217
        drop(p);
        drop(symbols);
        drop(emit_context);
        drop(nodes);
        drop(program);
        release_node_builder(self, node_builder);
        writer.get_text()
    }

    /// `(c *Checker) signatureToString`.
    pub(crate) fn signature_to_string(&mut self, signature: SignatureId) -> String {
        self.signature_to_string_ex(signature, None, TypeFormatFlags::NONE, None)
    }

    /// `(c *Checker) SignatureToStringEx` + `signatureToStringEx`.
    pub fn signature_to_string_ex(
        &mut self,
        signature: SignatureId,
        enclosing_declaration: Option<NodeId>,
        flags: TypeFormatFlags,
        vc: Option<&mut VerbosityContext>,
    ) -> String {
        let mut vc = vc;
        let is_constructor = self
            .signature_arena
            .get(signature)
            .flags
            .intersects(SignatureFlags::CONSTRUCT)
            && !flags.intersects(TypeFormatFlags::WRITE_CALL_STYLE_SIGNATURE);
        let sig_output = if flags.intersects(TypeFormatFlags::WRITE_ARROW_STYLE_SIGNATURE) {
            if is_constructor {
                ast::Kind::ConstructorType
            } else {
                ast::Kind::FunctionType
            }
        } else if is_constructor {
            ast::Kind::ConstructSignature
        } else {
            ast::Kind::CallSignature
        };

        let mut node_builder = self.get_node_builder();
        let old_verbosity = take_verbosity(&mut node_builder, vc.as_deref_mut());
        let combined_flags = to_node_builder_flags(flags)
            | nodebuilder::Flags::IGNORE_ERRORS
            | nodebuilder::Flags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME;
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        let sig = node_builder.signature_to_signature_declaration(
            self,
            &mut nodes,
            signature,
            sig_output,
            enclosing_declaration,
            combined_flags,
            nodebuilder::InternalFlags::NONE,
            None,
        );
        let emit_context_cell = node_builder
            .impl_
            .as_ref()
            .expect("NodeBuilder without impl")
            .e
            .clone();
        let mut emit_context = emit_context_cell.borrow_mut();
        let symbol_arena = self.symbol_arena.clone();
        let symbols = symbol_arena.borrow();
        let source_file =
            enclosing_declaration.and_then(|d| ast::get_source_file_of_node(Some(d), &nodes));
        let mut p = create_printer_with_remove_comments_omit_trailing_semicolon_never_ascii_escape(
            &mut emit_context,
            &mut nodes,
            &symbols,
        );
        let result = if flags.intersects(TypeFormatFlags::MULTILINE_OBJECT_LITERALS) {
            let mut writer = TextWriter::new("\n", 0);
            p.write(sig, source_file, &mut writer, None);
            writer.get_text()
        } else {
            let mut writer = printer::get_single_line_string_writer();
            p.write(sig, source_file, &mut writer, None);
            writer.get_text()
        };
        drop(p);
        drop(symbols);
        drop(emit_context);
        drop(nodes);
        drop(program);
        put_verbosity(&mut node_builder, vc.as_deref_mut(), old_verbosity);
        release_node_builder(self, node_builder);
        result
    }

    /// `(c *Checker) typePredicateToString`.
    pub fn type_predicate_to_string(&mut self, type_predicate: Option<&TypePredicate>) -> String {
        self.type_predicate_to_string_ex(
            type_predicate,
            None,
            TypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE,
        )
    }

    /// `(c *Checker) typePredicateToStringEx`.
    fn type_predicate_to_string_ex(
        &mut self,
        type_predicate: Option<&TypePredicate>,
        enclosing_declaration: Option<NodeId>,
        flags: TypeFormatFlags,
    ) -> String {
        let mut writer = printer::get_single_line_string_writer();
        let mut node_builder = self.get_node_builder();
        let combined_flags = to_node_builder_flags(flags)
            | nodebuilder::Flags::IGNORE_ERRORS
            | nodebuilder::Flags::WRITE_TYPE_PARAMETERS_IN_QUALIFIED_NAME;
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        let predicate = node_builder.type_predicate_to_type_predicate_node(
            self,
            &mut nodes,
            type_predicate,
            enclosing_declaration,
            combined_flags,
            nodebuilder::InternalFlags::NONE,
            None, /*tracker*/ // TODO: GH#18217
        );
        let emit_context_cell = node_builder
            .impl_
            .as_ref()
            .expect("NodeBuilder without impl")
            .e
            .clone();
        let mut emit_context = emit_context_cell.borrow_mut();
        let symbol_arena = self.symbol_arena.clone();
        let symbols = symbol_arena.borrow();
        let source_file =
            enclosing_declaration.and_then(|d| ast::get_source_file_of_node(Some(d), &nodes));
        let mut p = create_printer_with_remove_comments(&mut emit_context, &mut nodes, &symbols);
        p.write(predicate, source_file, &mut writer, None);
        drop(p);
        drop(symbols);
        drop(emit_context);
        drop(nodes);
        drop(program);
        release_node_builder(self, node_builder);
        writer.get_text()
    }

    /// `(c *Checker) valueToString`.
    pub fn value_to_string(&mut self, value: Option<&evaluator::Value>) -> String {
        crate::checker_core::value_to_string(value)
    }

    /// `(c *Checker) formatUnionTypes`.
    pub(crate) fn format_union_types(
        &mut self,
        types: &[TypeId],
        expanding_enum: bool,
    ) -> Vec<TypeId> {
        let mut result: Vec<TypeId> = Vec::new();
        let mut flags = TypeFlags::NONE;
        let mut i = 0;
        while i < types.len() {
            let t = types[i];
            flags |= self.types_handle().get(t).flags;
            if !self
                .types_handle()
                .get(t)
                .flags
                .intersects(TypeFlags::NULLABLE)
            {
                if self
                    .types_handle()
                    .get(t)
                    .flags
                    .intersects(TypeFlags::BOOLEAN_LITERAL)
                    || (!expanding_enum
                        && self
                            .types_handle()
                            .get(t)
                            .flags
                            .intersects(TypeFlags::ENUM_LIKE))
                {
                    let base_type = if self
                        .types_handle()
                        .get(t)
                        .flags
                        .intersects(TypeFlags::BOOLEAN_LITERAL)
                    {
                        self.boolean_type
                    } else {
                        self.get_base_type_of_enum_like_type(t)
                    };
                    if self
                        .types_handle()
                        .get(base_type)
                        .flags
                        .intersects(TypeFlags::UNION)
                    {
                        let __arena_union_types = self.types.clone();
                        let union_types = __arena_union_types
                            .get(base_type)
                            .as_union_type()
                            .union_or_intersection
                            .types
                            .clone();
                        let count = union_types.len();
                        if i + count <= types.len()
                            && self.get_regular_type_of_literal_type(types[i + count - 1])
                                == self.get_regular_type_of_literal_type(union_types[count - 1])
                        {
                            result.push(base_type);
                            i += count - 1;
                            i += 1;
                            continue;
                        }
                    }
                }
                result.push(t);
            }
            i += 1;
        }
        if flags.intersects(TypeFlags::NULL) {
            result.push(self.null_type);
        }
        if flags.intersects(TypeFlags::UNDEFINED) {
            result.push(self.undefined_type);
        }
        result
    }

    /// `(c *Checker) TypeToTypeNode`.
    pub fn type_to_type_node(
        &mut self,
        t: TypeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        id_to_symbol: FxHashMap<NodeId, SymbolId>,
    ) -> Option<NodeId> {
        let mut node_builder = self.get_node_builder_ex(id_to_symbol);
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        node_builder.type_to_type_node(
            self,
            &mut nodes,
            t,
            enclosing_declaration,
            flags,
            nodebuilder::InternalFlags::NONE,
            None,
        )
    }

    /// `(c *Checker) SignatureToSignatureDeclaration`.
    pub fn signature_to_signature_declaration(
        &mut self,
        signature: SignatureId,
        kind: ast::Kind,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
    ) -> Option<NodeId> {
        let mut node_builder = self.get_node_builder();
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        let result = node_builder.signature_to_signature_declaration(
            self,
            &mut nodes,
            signature,
            kind,
            enclosing_declaration,
            flags,
            nodebuilder::InternalFlags::NONE,
            None,
        );
        drop(nodes);
        drop(program);
        release_node_builder(self, node_builder);
        result
    }

    /// `(c *Checker) ExpandSymbolForHover` — produces declaration strings
    /// for a symbol with verbosity support for expandable hover.
    pub fn expand_symbol_for_hover(
        &mut self,
        symbol: SymbolId,
        meaning: ast::SymbolFlags,
        vc: Option<&mut VerbosityContext>,
    ) -> String {
        let mut vc = vc;
        let mut node_builder = self.get_node_builder();
        let old_verbosity = take_verbosity(&mut node_builder, vc.as_deref_mut());
        // The hover nodes are minted into the file containing the symbol's
        // value declaration (there is no enclosing declaration).
        let file_index = self
            .sym(symbol)
            .value_declaration
            .map(|d| d.file_index())
            .unwrap_or_else(|| {
                node_builder
                    .impl_
                    .as_ref()
                    .expect("NodeBuilder without impl")
                    .f
                    .file_index()
            });
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        let nodes_out = node_builder.expand_symbol_for_hover(self, &mut nodes, symbol, meaning);
        if nodes_out.is_empty() {
            drop(nodes);
            drop(program);
            put_verbosity(&mut node_builder, vc.as_deref_mut(), old_verbosity);
            release_node_builder(self, node_builder);
            return String::new();
        }
        let emit_context_cell = node_builder
            .impl_
            .as_ref()
            .expect("NodeBuilder without impl")
            .e
            .clone();
        let mut emit_context = emit_context_cell.borrow_mut();
        let symbol_arena = self.symbol_arena.clone();
        let symbols = symbol_arena.borrow();
        let source_file = self
            .sym(symbol)
            .value_declaration
            .and_then(|d| ast::get_source_file_of_node(Some(d), &nodes));
        let mut p = create_printer_with_remove_comments(&mut emit_context, &mut nodes, &symbols);
        let mut b = String::new();
        for (i, node) in nodes_out.iter().enumerate() {
            if i > 0 {
                b.push('\n');
            }
            b.push_str(&p.emit(Some(*node), source_file));
        }
        drop(p);
        drop(symbols);
        drop(emit_context);
        drop(nodes);
        drop(program);
        put_verbosity(&mut node_builder, vc.as_deref_mut(), old_verbosity);
        release_node_builder(self, node_builder);
        b
    }

    /// `(c *Checker) TypeParameterToStringEx` — renders a type parameter
    /// declaration (e.g. "T extends Foo") with optional verbosity support.
    pub fn type_parameter_to_string_ex(
        &mut self,
        t: TypeId,
        enclosing_declaration: Option<NodeId>,
        vc: Option<&mut VerbosityContext>,
    ) -> String {
        let mut vc = vc;
        let mut node_builder = self.get_node_builder();
        let old_verbosity = take_verbosity(&mut node_builder, vc.as_deref_mut());
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        let type_param_node = node_builder.type_parameter_to_declaration(
            self,
            &mut nodes,
            t,
            enclosing_declaration,
            nodebuilder::Flags::IGNORE_ERRORS,
            nodebuilder::InternalFlags::NONE,
            None,
        );
        let Some(type_param_node) = type_param_node else {
            drop(nodes);
            drop(program);
            put_verbosity(&mut node_builder, vc.as_deref_mut(), old_verbosity);
            release_node_builder(self, node_builder);
            return self.type_to_string(t);
        };
        let emit_context_cell = node_builder
            .impl_
            .as_ref()
            .expect("NodeBuilder without impl")
            .e
            .clone();
        let mut emit_context = emit_context_cell.borrow_mut();
        let symbol_arena = self.symbol_arena.clone();
        let symbols = symbol_arena.borrow();
        let source_file =
            enclosing_declaration.and_then(|d| ast::get_source_file_of_node(Some(d), &nodes));
        let mut p = create_printer_with_remove_comments(&mut emit_context, &mut nodes, &symbols);
        let result = p.emit(Some(type_param_node), source_file);
        drop(p);
        drop(symbols);
        drop(emit_context);
        drop(nodes);
        drop(program);
        put_verbosity(&mut node_builder, vc.as_deref_mut(), old_verbosity);
        release_node_builder(self, node_builder);
        result
    }

    /// `(c *Checker) TypeToTypeNode` variant that also returns the
    /// `idToSymbol` map the Go caller retains by reference after the call
    /// (Go fills the caller's `map[*ast.IdentifierNode]*ast.Symbol`; the
    /// builder consumes it here, so it is handed back to the caller).
    /// Used by `autoimport::TypeToAutoImportableTypeNode`.
    pub fn type_to_type_node_with_id_map(
        &mut self,
        t: TypeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
    ) -> (Option<NodeId>, FxHashMap<NodeId, SymbolId>) {
        let mut node_builder = self.get_node_builder_ex(FxHashMap::default());
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        let type_node = node_builder.type_to_type_node(
            self,
            &mut nodes,
            t,
            enclosing_declaration,
            flags,
            nodebuilder::InternalFlags::NONE,
            None,
        );
        let id_to_symbol = node_builder
            .impl_
            .as_mut()
            .map(|i| std::mem::take(&mut i.id_to_symbol))
            .unwrap_or_default();
        (type_node, id_to_symbol)
    }

    /// `(c *Checker) TypeToTypeNodeEx`.
    pub fn type_to_type_node_ex(
        &mut self,
        t: TypeId,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        internal_flags: nodebuilder::InternalFlags,
        id_to_symbol: FxHashMap<NodeId, SymbolId>,
    ) -> Option<NodeId> {
        let mut node_builder = self.get_node_builder_ex(id_to_symbol);
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        node_builder.type_to_type_node(
            self,
            &mut nodes,
            t,
            enclosing_declaration,
            flags,
            internal_flags,
            None,
        )
    }

    /// `(c *Checker) TypePredicateToTypePredicateNode`.
    pub fn type_predicate_to_type_predicate_node(
        &mut self,
        t: Option<&TypePredicate>,
        enclosing_declaration: Option<NodeId>,
        flags: nodebuilder::Flags,
        id_to_symbol: FxHashMap<NodeId, SymbolId>,
    ) -> Option<NodeId> {
        let mut node_builder = self.get_node_builder_ex(id_to_symbol);
        let file_index = builder_arena_index(&node_builder, enclosing_declaration);
        let program = self.program.clone().expect("program");
        let (file_index, __arena_cell) = program.nodes_handle_or_fallback(file_index);
        node_builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaCheckout::new(__arena_cell);
        node_builder.type_predicate_to_type_predicate_node(
            self,
            &mut nodes,
            t,
            enclosing_declaration,
            flags,
            nodebuilder::InternalFlags::NONE,
            None,
        )
    }
}
