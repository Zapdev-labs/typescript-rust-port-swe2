// Ported from tsc/internal/checker/nodebuilderscopes.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Scope bookkeeping for the node builder: context cloning (for sibling type
// parameter scopes) and fake-scope injection for signature parameters.
//
// PORT notes:
//
// - Go's `func()` cleanup callbacks become `ScopeCleanup`/`ScopeUndo`
//   records with a `restore` method — closures can't disjointly capture
//   `b.ctx`, `b.links`, and `nodes` in Rust, so the captured state is
//   explicit and `restore` re-borrows the arenas.
// - `locals ast.SymbolTable` mutations in `pushFakeScope` write through the
//   fake-scope node's `locals_container_data_mut` — Go mutates the map
//   header held by the node; same effect. Go's `add` callback is
//   restructured: call sites collect `Vec<(name, symbol)>` additions first
//   (the callback can't capture the locals borrow across `&mut` arena
//   reads), then `apply_additions` performs Go's `newLocals`/`oldLocals`
//   bookkeeping in the same order.
// - `[]*ast.Symbol` with nil-able elements → `Vec<Option<SymbolId>>`
//   (`expanded_params`); `[]*Type` `type_parameters` keeps `Vec<TypeId>`
//   since Go callers only ever pass non-nil element slices (the per-element
//   nil checks in Go are defensive — see `Some(p != nil)`).
// - `*string` fake-scope kind → `Option<String>` on `NodeBuilderLinks`; a
//   `SymbolId::NONE` addition mirrors Go's `locals[name] = nil-symbol`
//   (possible via a nil `typeParam.symbol`).

use tsc_ast::{self as ast, Kind, NodeId, SymbolId};
use tsc_nodebuilder as nodebuilder;

use crate::checker_core::Checker;
use crate::mapper::TypeMapperId;
use crate::nodebuilderimpl::{NodeBuilderContext, NodeBuilderImpl};
use crate::types::{SignatureId, TypeId};

/// `cloneNodeBuilderContext` — make type parameters created within this
/// context not consume the name outside this context. The symbol serializer
/// ends up creating many sibling scopes that all need "separate" contexts
/// when it comes to naming things — within a normal `typeToTypeNode` call,
/// the node builder only ever descends through the type tree, so the only
/// cases where we could have used distinct sibling scopes was when there
/// were multiple generic overloads with similar generated type parameter
/// names.
///
/// The effect: when we write out
/// ```text
/// export const x: <T>(x: T) => T
/// export const y: <T>(x: T) => T
/// ```
/// we write it out like that, rather than as
/// ```text
/// export const x: <T>(x: T) => T
/// export const y: <T_1>(x: T_1) => T_1
/// ```
///
/// PORT: Go returns `func()`; `CopyOnWriteMap::enter_scope`'s restore
/// closures take the map by `&mut`, so the returned closure takes the whole
/// context to route each restore at its field. It is boxed so the `'static`
/// capture (each `enter_scope` restore owns an `Rc`, not a borrow) does not
/// extend the `&mut context` borrow across `enter_new_scope`'s body.
pub fn clone_node_builder_context(
    context: &mut NodeBuilderContext,
) -> Box<dyn FnOnce(&mut NodeBuilderContext)> {
    let restore_names = context.type_parameter_names.enter_scope();
    let restore_name_texts = context.type_parameter_name_texts.enter_scope();
    let restore_names_by_text = context.type_parameter_names_by_text.enter_scope();
    let restore_names_by_text_next_name_count = context
        .type_parameter_names_by_text_next_name_count
        .enter_scope();
    let restore_symbol_list = context.type_parameter_symbol_list.enter_scope();
    Box::new(move |context: &mut NodeBuilderContext| {
        restore_names(&mut context.type_parameter_names);
        restore_name_texts(&mut context.type_parameter_name_texts);
        restore_names_by_text(&mut context.type_parameter_names_by_text);
        restore_names_by_text_next_name_count(
            &mut context.type_parameter_names_by_text_next_name_count,
        );
        restore_symbol_list(&mut context.type_parameter_symbol_list);
    })
}

/// `type localsRecord struct` (declared in nodebuilderscopes.go; the struct
/// itself lives here rather than nodebuilderimpl.rs).
///
/// `oldSymbol` is `Option<SymbolId>` — Go stores `*ast.Symbol` which may be
/// nil.
#[derive(Clone)]
pub struct LocalsRecord {
    /// `name`.
    pub name: String,
    /// `oldSymbol`.
    pub old_symbol: Option<SymbolId>,
}

/// Undo record for one injected fake scope — the `undo` closure Go returns
/// from `pushFakeScope` when reusing an existing scope. `detached` holds the
/// fresh `SymbolTable` for the case where the existing scope node has no
/// locals container — matching Go, where writes to that detached map are
/// dead writes.
pub struct ScopeUndo {
    /// `existingFakeScope` node whose `locals` get un-added entries.
    fake_scope: NodeId,
    /// `newLocals`.
    new_locals: Vec<String>,
    /// `oldLocals`.
    old_locals: Vec<LocalsRecord>,
    /// Detached locals for the no-container edge case (see header).
    detached: Option<ast::SymbolTable>,
}

impl ScopeUndo {
    /// `undo()`.
    fn restore(mut self, nodes: &mut Vec<ast::Node>) {
        let detached_fallback;
        // PORT: `Rc::make_mut` on a shared `locals` table (node cloned after
        // binding) detaches before undo writes instead of mutating through
        // Go's shared map header — the clone keeps the pre-`pushFakeScope`
        // contents, which is what undo restores anyway.
        let locals: &mut ast::SymbolTable =
            match nodes[self.fake_scope].data.locals_container_data_mut() {
                Some(d) => std::rc::Rc::make_mut(&mut d.locals),
                None => {
                    detached_fallback = self.detached.get_or_insert_with(Default::default);
                    detached_fallback
                }
            };
        for s in &self.new_locals {
            locals.delete(s.as_str());
        }
        for s in &self.old_locals {
            match s.old_symbol {
                Some(old) => {
                    locals.set(s.name.clone().into(), old);
                }
                None => {
                    locals.delete(s.name.as_str());
                }
            }
        }
    }
}

/// The composite cleanup returned by `enter_new_scope` — Go's outer
/// `func()` closure. `restore(b, nodes)` runs `cleanupParams`,
/// `cleanupTypeParams`, `cleanupContext`, then restores
/// `enclosingDeclaration`/`mapper`, in Go's order.
pub struct ScopeCleanup {
    /// `cleanupParams`.
    params: Option<ScopeUndo>,
    /// `cleanupTypeParams`.
    type_params: Option<ScopeUndo>,
    /// `cleanupContext` — the `cloneNodeBuilderContext` restore closure.
    context: Box<dyn FnOnce(&mut NodeBuilderContext)>,
    /// `oldEnclosingDecl`.
    old_enclosing_decl: Option<NodeId>,
    /// `oldMapper`.
    old_mapper: Option<TypeMapperId>,
}

impl ScopeCleanup {
    /// The Go `func()` cleanup.
    pub fn restore(self, b: &mut NodeBuilderImpl<'_>, nodes: &mut Vec<ast::Node>) {
        if let Some(cleanup_params) = self.params {
            cleanup_params.restore(nodes);
        }
        if let Some(cleanup_type_params) = self.type_params {
            cleanup_type_params.restore(nodes);
        }
        (self.context)(&mut b.ctx);
        b.ctx.enclosing_declaration = self.old_enclosing_decl;
        b.ctx.mapper = self.old_mapper;
    }
}

impl<'a> NodeBuilderImpl<'a> {
    /// `(b *NodeBuilderImpl) addSymbolTypeToContext`.
    ///
    /// PORT: returns a scoped restore closure taking `&mut NodeBuilderContext`
    /// (the map can't be captured disjointly from `b`).
    pub fn add_symbol_type_to_context(
        &mut self,
        symbol: SymbolId,
        t: TypeId,
    ) -> impl FnOnce(&mut NodeBuilderContext) + use<> {
        let (old_type, old_type_exists) = match self.ctx.enclosing_symbol_types.get(&symbol) {
            Some(&old) => (Some(old), true),
            None => (None, false),
        };
        self.ctx.enclosing_symbol_types.insert(symbol, t);
        move |ctx: &mut NodeBuilderContext| {
            if old_type_exists {
                ctx.enclosing_symbol_types.insert(symbol, old_type.unwrap());
            } else {
                ctx.enclosing_symbol_types.remove(&symbol);
            }
        }
    }

    /// `(b *NodeBuilderImpl) enterSignatureScope` — returns the expanded
    /// params plus the `enterNewScope` cleanup.
    pub fn enter_signature_scope(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        signature: SignatureId,
    ) -> (Vec<Option<SymbolId>>, ScopeCleanup) {
        // `[0]` on the expanded-parameters result — Go indexes directly;
        // `remove(0)`/`next()` panics on empty just like Go.
        let expanded_params: Vec<Option<SymbolId>> = c
            .get_expanded_parameters(signature, true /*skipUnionExpanding*/)
            .into_iter()
            .next()
            .map(|v| v.into_iter().map(Some).collect())
            .unwrap_or_default();
        let (declaration, type_parameters, parameters, mapper) = {
            let sig = c.signature_arena.get(signature);
            (
                sig.declaration,
                sig.type_parameters.to_vec(),
                sig.parameters.clone(),
                sig.mapper,
            )
        };
        let cleanup = self.enter_new_scope(
            c,
            nodes,
            declaration,
            Some(expanded_params.clone()),
            Some(type_parameters),
            Some(parameters),
            mapper,
        );
        (expanded_params, cleanup)
    }

    /// `(b *NodeBuilderImpl) enterNewScope`.
    ///
    /// For regular function/method declarations, the enclosing declaration
    /// will already be `signature.declaration`, so this is a no-op, but for
    /// arrow functions and function expressions, the enclosing declaration
    /// will be the declaration that the arrow function / function expression
    /// is assigned to.
    ///
    /// If the parameters or return type include "typeof globalThis.paramName",
    /// using the wrong scope will lead us to believe that we can emit
    /// "typeof paramName" instead, even though that would refer to the
    /// parameter, not the global. Make sure we are in the right scope by
    /// changing the enclosingDeclaration to the function.
    ///
    /// We can't use the declaration directly; it may be in another file and
    /// so we may lose access to symbols accessible to the current enclosing
    /// declaration, or gain access to symbols not accessible to the current
    /// enclosing declaration. To keep this chain accurate, insert a fake
    /// scope into the chain which makes the function's parameters visible.
    pub fn enter_new_scope(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        declaration: Option<NodeId>,
        expanded_params: Option<Vec<Option<SymbolId>>>,
        type_parameters: Option<Vec<TypeId>>,
        original_parameters: Option<Vec<SymbolId>>,
        mapper: Option<TypeMapperId>,
    ) -> ScopeCleanup {
        let cleanup_context = clone_node_builder_context(&mut self.ctx);

        let mut cleanup_params = None;
        let mut cleanup_type_params = None;
        let old_enclosing_decl = self.ctx.enclosing_declaration;
        let old_mapper = self.ctx.mapper;
        if let Some(mapper) = mapper {
            self.ctx.mapper = Some(mapper);
        }
        if self.ctx.enclosing_declaration.is_some() && declaration.is_some() {
            // `pushFakeScope` is extracted as a method — see below. Reusing
            // the same fake scope within a chain is a performance
            // optimization (see the Go comment): all names introduced into
            // the chain go into one large table we push/pop as needed, and
            // `isSymbolAccessible` walks upward and finds the closest fake
            // scope.
            if expanded_params
                .as_ref()
                .is_none_or(|params| params.iter().all(Option::is_none))
            {
                // `expandedParams == nil || !Some(p != nil)` → no cleanup.
            } else {
                // `pushFakeScope("params", addAll)` — collect the (name,
                // symbol) additions eagerly; see file header for why the
                // callback is a Vec.
                let mut additions: Vec<(String, SymbolId)> = Vec::new();
                if let Some(params) = &expanded_params {
                    for (p_index, param) in params.iter().enumerate() {
                        let Some(param) = *param else {
                            continue;
                        };
                        let original_param = original_parameters
                            .as_ref()
                            .and_then(|p| p.get(p_index))
                            .copied();
                        if original_parameters.is_some() && original_param != Some(param) {
                            // Can't reference the expanded parameter name,
                            // just the original, unless we've expanded the
                            // param list for some reason.
                            if let Some(original_param) = original_param {
                                additions.push((
                                    c.symbol_arena.get_ref(original_param).name.to_string(),
                                    original_param,
                                ));
                            }
                        } else if !collect_binding_pattern_symbols(c, nodes, param, &mut additions)
                        {
                            additions
                                .push((c.symbol_arena.get_ref(param).name.to_string(), param));
                        }
                    }
                }
                cleanup_params = self.push_fake_scope(c, nodes, "params", additions);
            }

            if self
                .ctx
                .flags
                .intersects(nodebuilder::Flags::GENERATE_NAMES_FOR_SHADOWED_TYPE_PARAMS)
                && type_parameters.as_ref().is_some_and(|p| !p.is_empty())
            {
                let mut additions: Vec<(String, SymbolId)> = Vec::new();
                if let Some(type_parameters) = &type_parameters {
                    for &type_param in type_parameters {
                        // `b.typeParameterToName(typeParam).Text`
                        let name_node = self.type_parameter_to_name(c, nodes, type_param);
                        let name = nodes[name_node].text(nodes).into_owned();
                        // `typeParam.symbol` may be nil → `SymbolId::NONE`.
                        let __arena_symbol = c.types.clone();
                        let symbol = __arena_symbol
                            .get(type_param)
                            .symbol
                            .unwrap_or(SymbolId::NONE);
                        additions.push((name, symbol));
                    }
                }
                cleanup_type_params = self.push_fake_scope(c, nodes, "typeParams", additions);
            }
        }

        ScopeCleanup {
            params: cleanup_params,
            type_params: cleanup_type_params,
            context: cleanup_context,
            old_enclosing_decl,
            old_mapper,
        }
    }

    /// The `pushFakeScope` closure from `enterNewScope`, extracted as a
    /// method. `additions` is the eagerly-collected (name, symbol) list —
    /// see the file header.
    fn push_fake_scope(
        &mut self,
        c: &mut Checker,
        nodes: &mut Vec<ast::Node>,
        kind: &str,
        additions: Vec<(String, SymbolId)>,
    ) -> Option<ScopeUndo> {
        // We only ever need to look two declarations upward.
        debug_assert!(self.ctx.enclosing_declaration.is_some());
        let enclosing = self.ctx.enclosing_declaration.unwrap();
        // `enclosing` must physically resolve in `nodes` for the
        // existing-scope reuse checks below — `file_index` agreement alone
        // is not enough, since scratch clones can share an index with the
        // live buffer while being different storage.
        let enclosing_in_nodes =
            crate::printer_util::buffer_resolves_id(nodes, enclosing);
        // PORT: Go's `links.Has(node)`/`links.Get(node)` key by node pointer,
        // so a `fakeScopeForSignatureDeclaration` match can only ever come
        // from the fake-scope Block itself. Here NodeIds alias across arena
        // buffers (a fake-scope id minted in a scratch buffer can coincide
        // with a real node in the live buffer), so the link is trusted only
        // when the candidate node is actually a Block — the only kind that
        // ever receives the link (Go's `debug.Assert` enforces the same
        // invariant).
        fn node_at<'n>(nodes: &'n [ast::Node], id: NodeId) -> Option<&'n ast::Node> {
            nodes.get(id.local_index() as usize)
        }
        let mut existing_fake_scope: Option<NodeId> = None;
        if enclosing_in_nodes
            && node_at(nodes, enclosing).is_some_and(|n| n.kind == Kind::Block)
            && self
                .links
                .try_get(&enclosing)
                .is_some_and(|l| l.fake_scope_for_signature_declaration.as_deref() == Some(kind))
        {
            existing_fake_scope = Some(enclosing);
        }
        if enclosing_in_nodes
            && existing_fake_scope.is_none()
            && let Some(parent) = node_at(nodes, enclosing).and_then(|n| n.parent)
            && parent.file_index() == self.f.file_index()
            && node_at(nodes, parent).is_some_and(|n| n.kind == Kind::Block)
            && self
                .links
                .try_get(&parent)
                .is_some_and(|l| l.fake_scope_for_signature_declaration.as_deref() == Some(kind))
        {
            existing_fake_scope = Some(parent);
        }
        debug_assert!(existing_fake_scope.is_none_or(|s| nodes[s].kind == Kind::Block));

        let mut new_locals: Vec<String> = Vec::new();
        let mut old_locals: Vec<LocalsRecord> = Vec::new();

        if let Some(scope) = existing_fake_scope {
            match nodes[scope].data.locals_container_data_mut() {
                Some(d) => {
                    // PORT: writes into a (possibly node-clone-shared)
                    // `locals` table detach via `Rc::make_mut` rather than
                    // mutating through Go's shared map header. The undo
                    // record restores by name, so detaching is equivalent.
                    apply_additions(
                        std::rc::Rc::make_mut(&mut d.locals),
                        &additions,
                        &mut new_locals,
                        &mut old_locals,
                        true,
                    );
                    Some(ScopeUndo {
                        fake_scope: scope,
                        new_locals,
                        old_locals,
                        detached: None,
                    })
                }
                None => {
                    // PORT: Go creates a detached `make(ast.SymbolTable)`
                    // here; writes to it are dead — mirror that with a
                    // detached table owned by the undo record.
                    let mut detached = ast::SymbolTable::default();
                    apply_additions(
                        &mut detached,
                        &additions,
                        &mut new_locals,
                        &mut old_locals,
                        true,
                    );
                    Some(ScopeUndo {
                        fake_scope: scope,
                        new_locals,
                        old_locals,
                        detached: Some(detached),
                    })
                }
            }
        } else {
            // No existing scope — apply additions to a fresh locals table,
            // then attach it to a new Block node.
            let mut locals = ast::SymbolTable::default();
            apply_additions(
                &mut locals,
                &additions,
                &mut new_locals,
                &mut old_locals,
                false,
            );
            // Use a Block for this; the type of the node doesn't matter so
            // long as it has locals, and this is cheaper/easier than using a
            // function-ish Node.
            // Always mint into the working buffer — even when `enclosing`
            // is foreign (scratch-arena node reuse). Minting into
            // `program.nodes_mut(enclosing.file_index())` is wrong: when
            // `enclosing` lives in a checked-out emit buffer the write
            // lands in the stale clone left in the cell, and the minted id
            // then aliases an unrelated node in the live buffer (the
            // `inferingFromAny` `a is T` → `boolean` bug). `parent` may
            // point at a foreign NodeId — Go's raw pointer — and the name
            // resolver resolves parent chains cross-arena, so the walk
            // still sees Go's real chain.
            let empty_list = self.f.new_node_list([]);
            let fake_scope = self.f.new_block(nodes, Some(empty_list), false);
            self.links
                .get(fake_scope)
                .fake_scope_for_signature_declaration = Some(kind.to_string());
            if let Some(data) = nodes[fake_scope].data.locals_container_data_mut() {
                data.locals = locals.into();
            }
            // `fakeScope.Parent = enclosingDeclaration`.
            nodes[fake_scope].parent = Some(enclosing);
            self.ctx.enclosing_declaration = Some(fake_scope);
            None
        }
    }
}

/// `apply_additions` — the `add` callback inside `pushFakeScope`,
/// restructured to run after the `(name, symbol)` list is collected.
/// `track_undo` corresponds to `existingFakeScope != nil`. `SymbolId::NONE`
/// symbols still write an entry (`locals[name] = nil` in Go).
fn apply_additions(
    locals: &mut ast::SymbolTable,
    additions: &[(String, SymbolId)],
    new_locals: &mut Vec<String>,
    old_locals: &mut Vec<LocalsRecord>,
    track_undo: bool,
) {
    for (name, symbol) in additions {
        // Add cleanup information only if we don't own the fake scope.
        if track_undo {
            match locals.get(name.as_str()) {
                // `!ok || oldSymbol == nil` → newLocals. The port's
                // "nil symbol" sentinel is `SymbolId::NONE` (see header).
                None => new_locals.push(name.clone()),
                Some(&old) if old == SymbolId::NONE => new_locals.push(name.clone()),
                Some(&old) => old_locals.push(LocalsRecord {
                    name: name.clone(),
                    old_symbol: Some(old),
                }),
            }
        }
        locals.set(name.clone().into(), *symbol);
    }
}

/// The `core.Some(param.Declarations, ...)` predicate from `enterNewScope`.
/// Walks `param`'s declarations; if one is a parameter whose name is a
/// binding pattern, adds each bound element's symbol to `additions` and
/// returns true. (Go performs the adds inside the `Some` predicate via the
/// `add` closure; the port passes `additions` explicitly.)
pub(crate) fn collect_binding_pattern_symbols(
    c: &mut Checker,
    nodes: &mut Vec<ast::Node>,
    param: SymbolId,
    additions: &mut Vec<(String, SymbolId)>,
) -> bool {
    // `bindPattern`/`bindElement` recursion over the binding pattern.
    // `nodes` is the arena containing the declaration being walked — it may
    // be a snapshot of another file's arena when `param` is declared there.
    fn bind_pattern(
        c: &mut Checker,
        nodes: &[ast::Node],
        pattern: NodeId,
        additions: &mut Vec<(String, SymbolId)>,
    ) {
        let elements = nodes[pattern]
            .as_binding_pattern()
            .elements
            .as_ref()
            .map(|l| l.nodes_rc())
            .unwrap_or_default();
        for e in elements.iter().copied() {
            match nodes[e].kind {
                Kind::OmittedExpression => return,
                Kind::BindingElement => bind_element(c, nodes, e, additions),
                _ => panic!("Unhandled binding element kind"),
            }
        }
    }

    fn bind_element(
        c: &mut Checker,
        nodes: &[ast::Node],
        e: NodeId,
        additions: &mut Vec<(String, SymbolId)>,
    ) {
        if let Some(name) = nodes[e].name()
            && ast::is_binding_pattern(&nodes[name])
        {
            bind_pattern(c, nodes, name, additions);
            return;
        }
        let symbol = c.get_symbol_of_declaration(e);
        // omitted expressions are now parsed as nameless binding patterns
        // and also have no symbol
        if let Some(symbol) = symbol {
            additions.push((c.symbol_arena.get_ref(symbol).name.to_string(), symbol));
        }
    }

    let declarations = c.symbol_arena.get_ref(param).declarations.clone();
    for d in declarations {
        // `d` may be declared in another file's arena (e.g. a lib parameter
        // symbol) — view it through the right arena rather than the caller's
        // working buffer.
        let arena =
            crate::printer_util::checker_arena_view(c, nodes.as_slice(), d.file_index());
        if ast::is_parameter_declaration(&arena[d])
            && let Some(name) = arena[d].name()
            && ast::is_binding_pattern(&arena[name])
        {
            bind_pattern(c, &arena, name, additions);
            return true;
        }
    }
    false
}
