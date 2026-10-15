// Ported from tsc/internal/api/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Checker-backed API handlers — Go session.go lines ~4190-4991
// (`handleGetIntrinsicType` … `handleGetFalseTypeOfConditionalType`).
//
// PORT notes:
// - Go's `defer setup.done()` becomes `CheckerSetup`'s `Drop` (the
//   `checker_pool::DoneFn` runs when `setup` leaves scope), so early
//   returns need no explicit release — including the error paths in
//   `resolveIndexInfoRequest` where Go calls `setup.done()` by hand.
// - `setup.checker` is `Rc<RefCell<Checker>>`; `borrow()`/`borrow_mut()`
//   map to Go's direct `*checker.Checker` use. `&mut self` checker
//   methods take `borrow_mut()`.
// - `nodes` arguments to `newSymbolResponse`/`newTypeResponse`/
//   `newSignatureResponse`/`newIndexInfoResponse` must be the arena of
//   the file that owns the nodes being classified — `nodes[id]` indexes
//   by `NodeId::local_index`, so a foreign file's arena mis-indexes.
//   `symbol_nodes`/`type_nodes`/`signature_nodes` pick the owning file's
//   arena from the entity's first declaration, falling back to any
//   program arena for declaration-free entities (transient symbols and
//   signatures never reach the arena lookups in those paths). Symbols
//   whose declaration list spans files (merged multi-file declarations)
//   still resolve each declaration in the first declaration's arena —
//   the scaffold's single-arena signature cannot express per-declaration
//   arenas; single-file declaration lists (the norm) are unaffected.
// - `(*nodes).get_mut()` derefs the `Rc<NodeArenaBuf>` explicitly so
//   `NodeArenaBuf::get_mut` (not `Rc::get_mut`) resolves — Go's shared
//   mutable `[]*ast.Node` write shape.
// - Handle registries resolve to entries carrying `(arena, id)`; checker
//   calls take `entry.symbol`/`entry.ty`/`entry.signature` (the arena
//   ids), not `entry.ptr()` — Go's `*ast.Symbol`/`*checker.Type`/
//   `*checker.Signature`.
// - `ls::jsdoc::get_symbol_js_doc_tags`/`get_symbol_documentation_comment`
//   are the API's `ls.GetSymbolJSDocTags`/`ls.GetSymbolDocumentationComment`
//   (the `jsdoc` module in tsc_ls is private — it must be exported for
//   this crate to link).

use std::rc::Rc;

use tsc_ast as ast;
use tsc_checker::checker_core::Checker;
use tsc_checker::exports as checker_exports;
use tsc_checker::types as checker;
use tsc_core as core_;
use tsc_evaluator::Value as EvaluatorValue;
use tsc_ls as ls;

use crate::proto::*;
use crate::session::*;

/// `program.nodes(node.file_index())` — the arena snapshot that owns
/// `node`. Synthetic ids may name an index with no registered arena;
/// `nodes_handle_or_fallback` substitutes any live arena like the
/// checker's synthetic-node paths do.
fn nodes_of(setup: &CheckerSetup, node: ast::NodeId) -> Rc<ast::NodeArenaBuf> {
    setup
        .program
        .nodes_handle_or_fallback(node.file_index())
        .1
        .snapshot()
}

/// Any registered program arena. Used when no declaration pins a file —
/// transient entities never reach the arena lookups in the response
/// builders, so the buffer identity is inert.
fn fallback_nodes(setup: &CheckerSetup) -> Rc<ast::NodeArenaBuf> {
    setup.program.nodes_handle_or_fallback(0).1.snapshot()
}

/// The node arena `symbolOwnerFile`/`buildSymbolResponse` inspect for
/// `symbol`: the file owning its first declaration, with
/// `getSourceFileOfSymbol`'s implicit-prototype parent fallback when the
/// declaration list is empty. Declaration-free symbols get the fallback
/// arena — both response paths skip arena access for them.
fn symbol_nodes(
    setup: &CheckerSetup,
    arena: &ast::SymbolArena,
    symbol: ast::SymbolId,
) -> Rc<ast::NodeArenaBuf> {
    let s = arena.get_ref(symbol);
    if let Some(&decl) = s.declarations.first() {
        return nodes_of(setup, decl);
    }
    if let Some(parent) = s.parent {
        if let Some(&decl) = arena.get_ref(parent).declarations.first() {
            return nodes_of(setup, decl);
        }
    }
    fallback_nodes(setup)
}

/// The node arena for a type response: the file of the type's symbol (or
/// alias symbol), else the first labeled tuple-element declaration's
/// file — the entities `newTypeResponse` emits references/handles for.
fn type_nodes(setup: &CheckerSetup, c: &Checker, ty: checker::TypeId) -> Rc<ast::NodeArenaBuf> {
    let t = c.types.get(ty);
    if let Some(sym) = t.symbol {
        return symbol_nodes(setup, &c.symbol_arena, sym);
    }
    if let Some(alias) = &t.alias {
        if let Some(sym) = alias.symbol {
            return symbol_nodes(setup, &c.symbol_arena, sym);
        }
    }
    if checker_exports::is_tuple_type_target(&c.types, ty) {
        for info in t.as_tuple_type().element_infos() {
            if let Some(decl) = info.labeled_declaration() {
                return nodes_of(setup, decl);
            }
        }
    }
    fallback_nodes(setup)
}

/// The node arena for a signature response: the signature declaration's
/// file (parameter symbol references resolve through the same file).
fn signature_nodes(
    setup: &CheckerSetup,
    c: &Checker,
    signature: checker::SignatureId,
) -> Rc<ast::NodeArenaBuf> {
    if let Some(decl) = c.signature_arena.get(signature).declaration() {
        return nodes_of(setup, decl);
    }
    fallback_nodes(setup)
}

/// `(setup checkerSetup) resolveSymbolHandle` — the scaffold's `nodes`
/// argument is unused by the decode; the returned `SymbolEntry` carries
/// the symbol's binding arena for the response.
fn resolve_symbol(setup: &CheckerSetup, ref_: &SymbolReference) -> Result<SymbolEntry, String> {
    let nodes = fallback_nodes(setup);
    setup.resolve_symbol_handle(ref_, (*nodes).get_mut())
}

/// `setup.sd.newTypeResponse(setup.projectID, t, setup.checker)` — nil
/// `*checker.Type` becomes `None`/absent like the scaffold's
/// `new_type_response` NONE-id guard.
fn type_response(setup: &CheckerSetup, ty: checker::TypeId) -> Option<TypeResponse> {
    if ty.is_none() {
        return None;
    }
    let nodes = type_nodes(setup, &setup.checker.borrow(), ty);
    setup.sd.new_type_response(
        (*nodes).get_mut(),
        &mut setup.checker.borrow_mut(),
        &setup.project_id,
        ty,
    )
}

/// `setup.newSymbolResponse(sym)` with the owning file's arena resolved
/// first. `Option<SymbolId>` mirrors Go's nil `*ast.Symbol` → nil response.
fn symbol_response(
    setup: &CheckerSetup,
    arena: &ast::SymbolArena,
    symbol: Option<ast::SymbolId>,
) -> Option<SymbolResponse> {
    let symbol = symbol?;
    let nodes = symbol_nodes(setup, arena, symbol);
    setup.new_symbol_response((*nodes).get_mut(), arena, symbol)
}

/// `setup.newSignatureResponse(sig)`.
fn signature_response(
    setup: &CheckerSetup,
    signature: checker::SignatureId,
) -> Option<SignatureResponse> {
    if signature.is_none() {
        return None;
    }
    let nodes = signature_nodes(setup, &setup.checker.borrow(), signature);
    setup.new_signature_response((*nodes).get_mut(), &setup.checker.borrow(), signature)
}

/// `setup.newIndexInfoResponse(info)` — `info` is cloned out of the
/// checker's `IndexInfoArena` (Go shared `*IndexInfo` pointers) so the
/// immutable arena read ends before `new_type_response` takes `&mut`
/// checker access.
fn index_info_response(setup: &CheckerSetup, info_id: checker::IndexInfoId) -> Option<IndexInfoResponse> {
    let info = setup.checker.borrow().index_info_arena.get(info_id).clone();
    let nodes = match info.declaration {
        Some(decl) => nodes_of(setup, decl),
        None => fallback_nodes(setup),
    };
    setup.new_index_info_response(
        (*nodes).get_mut(),
        &mut setup.checker.borrow_mut(),
        &info,
    )
}

impl Session {
    /// `handleGetIntrinsicType` returns an intrinsic type (any, string,
    /// number, etc.).
    pub(crate) fn handle_get_intrinsic_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetIntrinsicTypeParams,
        getter: fn(&Checker) -> checker::TypeId,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = getter(&setup.checker.borrow());
        if t.is_none() {
            return Ok(None);
        }

        Ok(type_response(&setup, t))
    }

    /// `handleGetWellKnownSymbols` returns the handle ids of the
    /// per-checker singleton symbols (unknown, undefined, arguments) so
    /// the client can identify them by id.
    pub(crate) fn handle_get_well_known_symbols(
        &self,
        ctx: &core_::context::Context,
        params: &GetIntrinsicTypeParams,
    ) -> Result<WellKnownSymbolsResponse, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let c = setup.checker.borrow();
        let unknown_symbol = c.get_unknown_symbol();
        let undefined_symbol = c.get_undefined_symbol();
        let arguments_symbol = c.get_arguments_symbol();
        debug_assert!(
            c.symbol_arena
                .get_ref(unknown_symbol)
                .flags
                .intersects(ast::SymbolFlags::TRANSIENT)
        );
        debug_assert!(
            c.symbol_arena
                .get_ref(undefined_symbol)
                .flags
                .intersects(ast::SymbolFlags::TRANSIENT)
        );
        debug_assert!(
            c.symbol_arena
                .get_ref(arguments_symbol)
                .flags
                .intersects(ast::SymbolFlags::TRANSIENT)
        );
        let (unknown, _) =
            setup
                .sd
                .register_symbol(&c.symbol_arena, unknown_symbol, &setup.project_id);
        let (undefined, _) =
            setup
                .sd
                .register_symbol(&c.symbol_arena, undefined_symbol, &setup.project_id);
        let (arguments, _) =
            setup
                .sd
                .register_symbol(&c.symbol_arena, arguments_symbol, &setup.project_id);
        Ok(WellKnownSymbolsResponse {
            unknown,
            undefined,
            arguments,
        })
    }

    /// `handleGetWellKnownSignatures` returns the handle id of the
    /// per-checker unknown signature so the client can identify it by id.
    pub(crate) fn handle_get_well_known_signatures(
        &self,
        ctx: &core_::context::Context,
        params: &GetIntrinsicTypeParams,
    ) -> Result<WellKnownSignaturesResponse, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let c = setup.checker.borrow();
        Ok(WellKnownSignaturesResponse {
            unknown: setup.sd.register_signature(
                &c.signature_arena,
                &setup.project_id,
                c.get_unknown_signature(),
            ),
        })
    }

    /// `handleIsContextSensitive` returns whether a node is
    /// context-sensitive.
    pub(crate) fn handle_is_context_sensitive(
        &self,
        ctx: &core_::context::Context,
        params: &GetContextualTypeParams,
    ) -> Result<bool, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;

        Ok(setup.checker.borrow_mut().is_context_sensitive(node))
    }

    /// `handleGetReturnTypeOfSignature` returns the return type of a
    /// signature.
    pub(crate) fn handle_get_return_type_of_signature(
        &self,
        ctx: &core_::context::Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let sig = setup.resolve_signature_handle(params.signature)?;

        let t = setup
            .checker
            .borrow_mut()
            .get_return_type_of_signature(sig.signature);
        Ok(type_response(&setup, t))
    }

    /// `handleGetRestTypeOfSignature` returns the rest type of a
    /// signature.
    pub(crate) fn handle_get_rest_type_of_signature(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSignatureParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let sig = setup.resolve_signature_handle(params.signature)?;

        let t = setup
            .checker
            .borrow_mut()
            .get_rest_type_of_signature(sig.signature);
        Ok(type_response(&setup, t))
    }

    /// `handleGetTypePredicateOfSignature` returns the type predicate of
    /// a signature.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_type_predicate_of_signature(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSignatureParams,
    ) -> Result<Option<TypePredicateResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let sig = setup.resolve_signature_handle(params.signature)?;

        let pred = setup
            .checker
            .borrow_mut()
            .get_type_predicate_of_signature(sig.signature);
        let Some(pred) = pred else {
            return Ok(None);
        };

        let mut resp = TypePredicateResponse {
            kind: pred.kind() as i32,
            parameter_index: pred.parameter_index(),
            parameter_name: pred.parameter_name().to_string(),
            ..Default::default()
        };
        if let Some(t) = pred.t() {
            resp.r#type = type_response(&setup, t);
        }

        Ok(Some(resp))
    }

    /// `handleIsArrayType` returns whether a type is `Array<T>` or
    /// `ReadonlyArray<T>`.
    pub(crate) fn handle_is_array_type(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerTypeParams,
    ) -> Result<bool, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        Ok(setup.checker.borrow().is_array_type(t.ty))
    }

    /// `handleIsReadonlySymbol` returns whether a symbol is a readonly
    /// symbol.
    pub(crate) fn handle_is_readonly_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<bool, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;

        Ok(setup.checker.borrow_mut().is_readonly_symbol(symbol.symbol))
    }

    /// `handleGetBaseTypes` returns the base types of an interface/class
    /// type.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_base_types(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerTypeParams,
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let base_types = setup.checker.borrow_mut().get_base_types(t.ty);
        if base_types.is_empty() {
            return Ok(None);
        }

        Ok(Some(
            base_types
                .iter()
                .map(|&bt| type_response(&setup, bt))
                .collect(),
        ))
    }

    /// `handleGetPropertiesOfType` returns the properties of a type.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_properties_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerTypeParams,
    ) -> Result<Option<Vec<Option<SymbolResponse>>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let sym_arena = setup.checker.borrow().symbol_arena.clone();
        let props = setup.checker.borrow_mut().get_properties_of_type(t.ty);
        if props.is_empty() {
            return Ok(None);
        }

        Ok(Some(
            props
                .iter()
                .map(|&p| symbol_response(&setup, &sym_arena, Some(p)))
                .collect(),
        ))
    }

    /// `handleGetApparentPropertiesOfType` returns the apparent
    /// properties of a type, including CallableFunction or
    /// NewableFunction members where applicable. Not nullable — Go's
    /// `make([]*SymbolResponse, 0)` marshals `[]`.
    pub(crate) fn handle_get_apparent_properties_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Vec<Option<SymbolResponse>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let sym_arena = setup.checker.borrow().symbol_arena.clone();
        let props = setup.checker.borrow_mut().get_apparent_properties(t.ty);
        Ok(props
            .iter()
            .map(|&p| symbol_response(&setup, &sym_arena, Some(p)))
            .collect())
    }

    /// `handleGetApparentType` returns the apparent type of a type.
    pub(crate) fn handle_get_apparent_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let apparent = setup.checker.borrow_mut().get_apparent_type(t.ty);
        Ok(type_response(&setup, apparent))
    }

    /// `handleGetReducedType` returns the reduced type of a type.
    pub(crate) fn handle_get_reduced_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let reduced = setup.checker.borrow_mut().get_reduced_type(t.ty);
        Ok(type_response(&setup, reduced))
    }

    /// `handleGetIndexInfosOfType` returns the index infos of a type.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_index_infos_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerTypeParams,
    ) -> Result<Option<Vec<Option<IndexInfoResponse>>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let infos = setup.checker.borrow_mut().get_index_infos_of_type(t.ty);
        if infos.is_empty() {
            return Ok(None);
        }

        Ok(Some(
            infos
                .iter()
                .map(|&info| index_info_response(&setup, info))
                .collect(),
        ))
    }

    /// `resolveIndexInfoRequest` — the resolved setup, type, and index
    /// key type. Go's manual `setup.done()` error-path calls are covered
    /// by `CheckerSetup::drop`.
    fn resolve_index_info_request(
        &self,
        ctx: &core_::context::Context,
        params: &GetIndexInfoOfTypeParams,
    ) -> Result<(CheckerSetup, checker::TypeId, checker::TypeId), String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let key_type = match params.kind {
            k if k == checker::IndexKind::String as i32 => {
                setup.checker.borrow().get_string_type()
            }
            k if k == checker::IndexKind::Number as i32 => {
                setup.checker.borrow().get_number_type()
            }
            _ => {
                return Err(format!(
                    "{}: invalid index kind {}",
                    ERR_CLIENT_ERROR, params.kind
                ));
            }
        };
        Ok((setup, t.ty, key_type))
    }

    /// `handleGetIndexInfoOfType`.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_index_info_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetIndexInfoOfTypeParams,
    ) -> Result<Option<IndexInfoResponse>, String> {
        let (setup, t, key_type) = self.resolve_index_info_request(ctx, params)?;

        let info = setup
            .checker
            .borrow_mut()
            .get_index_info_of_type(t, key_type);
        match info {
            Some(info_id) => Ok(index_info_response(&setup, info_id)),
            None => Ok(None),
        }
    }

    /// `handleGetConstraintOfTypeParameter` returns the constraint of a
    /// type parameter.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_constraint_of_type_parameter(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let constraint = setup
            .checker
            .borrow_mut()
            .get_constraint_of_type_parameter(t.ty);
        Ok(constraint.and_then(|c| type_response(&setup, c)))
    }

    /// `handleGetDefaultFromTypeParameter` returns the default type of a
    /// type parameter.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_default_from_type_parameter(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let default = setup
            .checker
            .borrow_mut()
            .get_default_from_type_parameter(t.ty);
        Ok(default.and_then(|d| type_response(&setup, d)))
    }

    /// `handleGetBaseConstraintOfType` returns the base constraint of an
    /// instantiable type.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_base_constraint_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerTypeParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let constraint = setup
            .checker
            .borrow_mut()
            .get_base_constraint_of_type(t.ty);
        Ok(constraint.and_then(|c| type_response(&setup, c)))
    }

    /// `handleGetPropertyOfType` returns a named property symbol of a
    /// type.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_property_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetPropertyOfTypeParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let sym_arena = setup.checker.borrow().symbol_arena.clone();
        let prop = setup
            .checker
            .borrow_mut()
            .get_property_of_type(t.ty, &params.name);
        Ok(symbol_response(&setup, &sym_arena, prop))
    }

    /// `handleGetTypeOfPropertyOfType`.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_type_of_property_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetPropertyOfTypeParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let ty = setup
            .checker
            .borrow_mut()
            .get_type_of_property_of_type(t.ty, &params.name);
        Ok(ty.and_then(|ty| type_response(&setup, ty)))
    }

    /// `handleGetConstantValue` returns the constant value of an enum
    /// member or const enum access.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_constant_value(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerNodeParams,
    ) -> Result<Option<ConstantValueResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;

        let value = setup.checker.borrow_mut().get_constant_value(node);
        Ok(Some(ConstantValueResponse {
            // Go `value.(jsnum.Number)` type assertion.
            is_number: matches!(value, Some(EvaluatorValue::Number(_))),
            value: literal_value_to_json(value.as_ref()),
        }))
    }

    /// `handleGetSignatureFromDeclaration` returns the signature of a
    /// function-like declaration.
    pub(crate) fn handle_get_signature_from_declaration(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerNodeParams,
    ) -> Result<Option<SignatureResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;

        let sig = setup
            .checker
            .borrow_mut()
            .get_signature_from_declaration(node);
        Ok(signature_response(&setup, sig))
    }

    /// `handleGetExportSpecifierLocalTargetSymbol` returns the local
    /// target symbol of an export specifier.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_export_specifier_local_target_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerNodeParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;

        let sym_arena = setup.checker.borrow().symbol_arena.clone();
        let symbol = setup
            .checker
            .borrow_mut()
            .get_export_specifier_local_target_symbol(node);
        Ok(symbol_response(&setup, &sym_arena, symbol))
    }

    /// `handleGetMergedSymbol`.
    pub(crate) fn handle_get_merged_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;

        let merged = setup
            .checker
            .borrow_mut()
            .get_merged_symbol(symbol.symbol);
        Ok(symbol_response(&setup, &symbol.arena, Some(merged)))
    }

    /// `handleGetSymbolOfNode`.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_symbol_of_node(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerNodeParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;

        let sym_arena = setup.checker.borrow().symbol_arena.clone();
        let symbol = setup.checker.borrow_mut().get_symbol_of_node(node);
        Ok(symbol_response(&setup, &sym_arena, symbol))
    }

    /// `handleGetSymbolOfDeclarationForChecker` — Go's
    /// `checker.GetSymbolOfDeclaration`.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_symbol_of_declaration_for_checker(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerNodeParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;

        let sym_arena = setup.checker.borrow().symbol_arena.clone();
        let symbol = setup
            .checker
            .borrow_mut()
            .get_symbol_of_declaration(node);
        Ok(symbol_response(&setup, &sym_arena, symbol))
    }

    /// `handleGetParentOfSymbolForChecker` — Go's
    /// `checker.GetParentOfSymbol`.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_parent_of_symbol_for_checker(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;

        let parent = setup
            .checker
            .borrow_mut()
            .get_parent_of_symbol(symbol.symbol);
        Ok(symbol_response(&setup, &symbol.arena, parent))
    }

    /// `handleGetAliasedSymbol` resolves an alias symbol to its target.
    pub(crate) fn handle_get_aliased_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;

        let aliased = setup
            .checker
            .borrow_mut()
            .get_aliased_symbol(symbol.symbol);
        Ok(symbol_response(&setup, &symbol.arena, aliased))
    }

    /// `handleGetFullyQualifiedName` returns the fully qualified name of
    /// a symbol (e.g. `"/path/to/module".Namespace.Name`).
    ///
    /// PORT: `GetFullyQualifiedName` is the `_api` wrapper —
    /// `get_fully_qualified_name(symbol, None)` per the exports.rs
    /// delegation note.
    pub(crate) fn handle_get_fully_qualified_name(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<String, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;
        if symbol.symbol.is_none() {
            return Ok(String::new());
        }

        Ok(setup
            .checker
            .borrow_mut()
            .get_fully_qualified_name_api(symbol.symbol))
    }

    /// `handleGetImmediateAliasedSymbol` resolves one level of alias
    /// indirection.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_immediate_aliased_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;
        if symbol.symbol.is_none() {
            return Ok(None);
        }

        let aliased = setup
            .checker
            .borrow_mut()
            .get_immediate_aliased_symbol(symbol.symbol);
        Ok(symbol_response(&setup, &symbol.arena, aliased))
    }

    /// `handleGetTargetSymbol` returns the target symbol if the symbol is
    /// instantiated, otherwise returns the provided symbol.
    ///
    /// PORT: `Checker::get_target_symbol` is `pub(crate)` in tsc-checker
    /// (the exports.rs table delegates Go's `GetTargetSymbol` to it), so
    /// the body — checker_c.rs:10827, Go checker.go:22087 — is inlined
    /// here.
    pub(crate) fn handle_method_get_target_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;

        // If the symbol is instantiated its flags are not copied from the
        // target — get back the original target symbol to work with the
        // correct set of flags.
        let target = {
            let mut c = setup.checker.borrow_mut();
            let s = symbol.symbol;
            if c.symbol_arena
                .get_ref(s)
                .check_flags
                .intersects(ast::checkflags::CheckFlags::INSTANTIATED)
            {
                c.value_symbol_links.get(s).target.unwrap_or(s)
            } else {
                s
            }
        };
        Ok(symbol_response(&setup, &symbol.arena, Some(target)))
    }

    /// `handleGetExportSymbolOfSymbolForChecker` — Go's
    /// `checker.GetExportSymbolOfSymbol`.
    pub(crate) fn handle_get_export_symbol_of_symbol_for_checker(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;

        let export = setup
            .checker
            .borrow_mut()
            .get_export_symbol_of_symbol(symbol.symbol);
        Ok(symbol_response(&setup, &symbol.arena, Some(export)))
    }

    /// `handleGetExportsOfModule` returns the resolved exports of a
    /// module symbol, including those introduced by `export *` and
    /// re-exports.
    /// @gen-proto-nullable
    ///
    /// PORT: `GetExportsOfModule` and `getExportsOfModuleAsArray` are
    /// identical in Go — the port collapses them into
    /// `get_exports_of_module_as_array` (services.rs).
    pub(crate) fn handle_get_exports_of_module(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<Vec<Option<SymbolResponse>>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;
        if symbol.symbol.is_none() {
            return Ok(None);
        }

        let sym_arena = setup.checker.borrow().symbol_arena.clone();
        let mut exports = {
            let mut c = setup.checker.borrow_mut();
            let mut exports = c.get_exports_of_module_as_array(symbol.symbol);
            // `slices.SortFunc(exports, setup.checker.CompareSymbols)`.
            exports.sort_by(|&a, &b| c.compare_symbols(a, b).cmp(&0));
            exports
        };
        if exports.is_empty() {
            return Ok(None);
        }

        Ok(Some(
            exports
                .drain(..)
                .map(|e| symbol_response(&setup, &sym_arena, Some(e)))
                .collect(),
        ))
    }

    /// `handleGetMemberInModuleExports` returns an export by name from a
    /// module symbol.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_member_in_module_exports(
        &self,
        ctx: &core_::context::Context,
        params: &GetMemberInModuleExportsParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;
        if symbol.symbol.is_none() {
            return Ok(None);
        }

        let sym_arena = setup.checker.borrow().symbol_arena.clone();
        let member = setup
            .checker
            .borrow_mut()
            .try_get_member_in_module_exports(&params.name, symbol.symbol);
        Ok(symbol_response(&setup, &sym_arena, member))
    }

    /// `handleGetJSDocTags` returns the JSDoc tags of a symbol as
    /// structured name/text pairs.
    /// @gen-proto-nullable
    ///
    /// PORT: `ls.GetSymbolJSDocTags` is `ls::jsdoc::get_symbol_js_doc_tags`
    /// — it needs the program and the `Rc<RefCell<Checker>>` handle, not
    /// a `&Checker`.
    pub(crate) fn handle_get_js_doc_tags(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<Option<Vec<JsDocTagInfo>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;
        if symbol.symbol.is_none() {
            return Ok(None);
        }

        let Some(tags) = ls::jsdoc::get_symbol_js_doc_tags(
            &setup.program,
            &setup.checker,
            Some(symbol.symbol),
        ) else {
            return Ok(None);
        };
        // Go builds `results[i] = &JSDocTagInfo{...}` — elements are never
        // nil, so `Vec<JsDocTagInfo>` (not `Vec<Option<..>>`).
        Ok(Some(
            tags.into_iter()
                .map(|tag| JsDocTagInfo {
                    name: tag.name,
                    text: tag.text,
                })
                .collect(),
        ))
    }

    /// `handleGetDocumentationComment` returns the rendered documentation
    /// comment of a symbol as plain text.
    pub(crate) fn handle_get_documentation_comment(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerSymbolParams,
    ) -> Result<String, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let symbol = resolve_symbol(&setup, &params.symbol)?;
        if symbol.symbol.is_none() {
            return Ok(String::new());
        }

        Ok(ls::jsdoc::get_symbol_documentation_comment(
            &setup.program,
            &setup.checker,
            Some(symbol.symbol),
        ))
    }

    /// `handleGetTypeArguments` returns the type arguments of a type
    /// reference.
    /// @gen-proto-nullable
    pub(crate) fn handle_get_type_arguments(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerTypeParams,
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let type_args = setup.checker.borrow_mut().get_type_arguments(t.ty);
        if type_args.is_empty() {
            return Ok(None);
        }

        Ok(Some(
            type_args
                .iter()
                .map(|&ta| type_response(&setup, ta))
                .collect(),
        ))
    }

    /// `handleGetTrueTypeOfConditionalType`.
    ///
    /// PORT: Go's `GetTrueTypeOfConditionalType` delegates to
    /// `get_true_type_from_conditional_type` (checker_d.rs) per the
    /// exports.rs delegation table.
    pub(crate) fn handle_get_true_type_of_conditional_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let true_type = setup
            .checker
            .borrow_mut()
            .get_true_type_from_conditional_type(t.ty);
        Ok(type_response(&setup, true_type))
    }

    /// `handleGetFalseTypeOfConditionalType`.
    ///
    /// PORT: Go's `GetFalseTypeOfConditionalType` delegates to
    /// `get_false_type_from_conditional_type` (checker_d.rs).
    pub(crate) fn handle_get_false_type_of_conditional_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let false_type = setup
            .checker
            .borrow_mut()
            .get_false_type_from_conditional_type(t.ty);
        Ok(type_response(&setup, false_type))
    }
}
