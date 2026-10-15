// Ported from tsc/internal/api/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Diagnostics + language-service session handlers — Go's `getDiagnostics`
// helper (session.go:5273) and the handlers at session.go:5300-5619
// (`handleGetSyntacticDiagnostics` … `handleGetReferencedSymbolsForNode`).
// `resolveOptionalSourceFile` (session.go:5397) already lives in
// session.rs and is reused here.
//
// PORT notes:
// - `[]*ast.Diagnostic` → `Vec<DiagnosticRef>`; `[]*DiagnosticResponse` →
//   `Vec<Option<DiagnosticResponse>>` (elements are never nil). Go's nil
//   slices marshal as `null`; a `Vec` marshals `[]`, so the `nil, nil`
//   early returns below serialize `[]` instead of `null` — the
//   `[]T` → `Vec<T>` convention.
// - Diagnostic arena: Go diagnostics carry live `*ast.SourceFile`
//   pointers; a `DiagnosticRef` snapshots a `DiagnosticFile` whose `node`
//   `NodeId` only indexes the arena that minted it. Every conversion goes
//   through `diagnostic_response`, which picks the owning arena (see its
//   comment).
// - `params.Files` is a `Vec` — Go's `Files != nil` check becomes
//   `!files.is_empty()`, so an explicit `"files": []` request takes the
//   whole-program path rather than Go's empty-list path.
// - `errors.Is(err, ls.ErrNeedsAutoImports)`: `ls::api::Error` and its
//   `NeedsAutoImports` variant are `pub` inside `pub(crate) mod api`, and
//   `ls::completions::CompletionList` is `pub` inside a private module —
//   neither can be named here, so the sentinel is matched on its `Display`
//   message text.
// - PORT(visibility): `get_referenced_symbols_for_node_public` returns
//   `Vec<Rc<RefCell<SymbolAndEntries>>>` whose type, fields, and methods
//   are all `pub(crate)` — `handle_get_referenced_symbols_for_node` is
//   written against those members as Go uses `entry.DefinitionNode()`/
//   `References()`/`DefinitionSymbol()`, but tsc_ls must promote them to
//   `pub` for this file to compile.

use std::rc::Rc;

use tsc_ast as ast;
use tsc_ast::diagnostic::{DiagnosticRef, lock_diagnostic};
use tsc_compiler as compiler;
use tsc_core as core_;
use tsc_lsconv as lsconv;
use tsc_project as project;

use crate::proto::*;
use crate::session::*;

/// `NewDiagnosticResponses` — `[]*DiagnosticResponse` →
/// `Vec<Option<DiagnosticResponse>>` (elements are never nil; see the
//  header note on nil slices).
fn diagnostic_responses(
    program: &compiler::program::Program,
    diags: &[DiagnosticRef],
) -> Vec<Option<DiagnosticResponse>> {
    diags.iter()
        .map(|d| Some(diagnostic_response(program, d)))
        .collect()
}

/// `NewDiagnosticResponse` — resolves the arena that owns the
/// diagnostic's `DiagnosticFile.node`. A `NodeId` indexes only the arena
/// that minted it, so each diagnostic renders through its own file's
/// arena: a program file arena, or the tsconfig parse arena for
/// config-file diagnostics. A node minted by an arena the program no
/// longer holds (extended config files, reparsed files, externally
/// produced diagnostics) is stripped to the `DiagnosticFile` snapshot —
/// identical text/`span_map` rendering minus the live-node refresh (see
/// `diagnosticwriter::ASTDiagnostic::file`).
fn diagnostic_response(
    program: &compiler::program::Program,
    d: &DiagnosticRef,
) -> DiagnosticResponse {
    let file = lock_diagnostic(d).file().cloned();
    let Some(node) = file.as_ref().and_then(|f| f.node) else {
        return new_diagnostic_response(d.clone(), &[]);
    };
    let file = file.expect("file");
    // Program-owned arena — the file index must match, not just the path
    // key (a reparsed file keeps its key but gets a fresh arena).
    if let Some(source_file) = program.get_source_file_by_path(&file.path_key) {
        if source_file.file_index() == node.file_index() {
            let nodes = program.nodes(node.file_index());
            return new_diagnostic_response(d.clone(), &nodes);
        }
    }
    // The tsconfig parse arena (`TsConfigSourceFile::nodes`).
    if let Some(config_file) = program.opts.config.config_file.as_ref() {
        if config_file.source_file.file_index() == node.file_index() {
            return new_diagnostic_response(d.clone(), &config_file.nodes);
        }
    }
    // Foreign arena — render the `DiagnosticFile` snapshot rather than
    // dereferencing a node this program cannot resolve.
    let stripped = lock_diagnostic(d).clone_diagnostic();
    {
        let mut locked = lock_diagnostic(&stripped);
        let mut file = locked.file().cloned().expect("file");
        file.node = None;
        locked.set_file(Some(file));
    }
    new_diagnostic_response(stripped, &[])
}

/// `sd.nodeHandleFrom(node)` — supplies the node's `SourceFile` for the
/// index table, resolved through `node`'s own arena (Go's
/// `ast.GetSourceFileOfNode` walked the shared node heap).
fn program_node_handle(
    sd: &SnapshotData,
    program: &compiler::program::Program,
    node: ast::NodeId,
) -> NodeHandle {
    let nodes = program.arena_of(node);
    let file = ast::get_source_file_of_node(Some(node), &nodes)
        .expect("node has no source file");
    sd.node_handle_from((*nodes).get_mut(), file, node)
}

/// The node arena `sd.new_symbol_response` resolves a program symbol's
/// declaration handles through — the arena of the symbol's first
/// declaration (or `value_declaration`). Go's shared node heap needed no
/// arena choice; `SymbolId` declaration `NodeId`s only index the arena
/// that minted them.
fn program_symbol_nodes(
    program: &compiler::program::Program,
    symbol: ast::SymbolId,
) -> Rc<ast::NodeArenaBuf> {
    let anchor = {
        let s = program.symbols.get_ref(symbol);
        s.declarations.first().copied().or(s.value_declaration)
    };
    match anchor {
        Some(node) => program.nodes(node.file_index()),
        // A declaration-less symbol yields no node handles; any
        // registered arena satisfies `symbol_owner_file`'s early exits.
        None => program.nodes_handle_or_fallback(0).1.snapshot(),
    }
}

impl Session {
    /// `s.getDiagnostics` — `getter` is one of `Program`'s diagnostic
    /// getters; `source_file` `None` means all files.
    fn get_diagnostics(
        &self,
        ctx: &core_::context::Context,
        params: &GetDiagnosticsParams,
        getter: impl Fn(
            &compiler::program::Program,
            &core_::context::Context,
            Option<ast::NodeId>,
        ) -> Vec<DiagnosticRef>,
    ) -> Result<Vec<Option<DiagnosticResponse>>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;

        if !params.files.is_empty() {
            let mut all_diags = Vec::new();
            for file in &params.files {
                let source_file = self.resolve_optional_source_file(&program, Some(file))?;
                all_diags.extend(getter(&program, ctx, source_file));
            }
            return Ok(diagnostic_responses(&program, &all_diags));
        }

        Ok(diagnostic_responses(&program, &getter(&program, ctx, None)))
    }

    /// `handleGetSyntacticDiagnostics` — `@gen-proto-nullable`.
    pub(crate) fn handle_get_syntactic_diagnostics(
        &self,
        ctx: &core_::context::Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<Option<DiagnosticResponse>>, String> {
        let ctx = core_::context::with_checker_lifetime(
            ctx,
            core_::context::CheckerLifetime::Diagnostics,
        );
        self.get_diagnostics(&ctx, params, |program, ctx, source_file| {
            program.get_syntactic_diagnostics(ctx.clone(), source_file)
        })
    }

    /// `handleGetBindDiagnostics` — `@gen-proto-nullable`.
    pub(crate) fn handle_get_bind_diagnostics(
        &self,
        ctx: &core_::context::Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<Option<DiagnosticResponse>>, String> {
        let ctx = core_::context::with_checker_lifetime(
            ctx,
            core_::context::CheckerLifetime::Diagnostics,
        );
        self.get_diagnostics(&ctx, params, |program, ctx, source_file| {
            program.get_bind_diagnostics(ctx.clone(), source_file)
        })
    }

    /// `handleGetSemanticDiagnostics` — `@gen-proto-nullable`.
    pub(crate) fn handle_get_semantic_diagnostics(
        &self,
        ctx: &core_::context::Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<Option<DiagnosticResponse>>, String> {
        let ctx = core_::context::with_checker_lifetime(
            ctx,
            core_::context::CheckerLifetime::Diagnostics,
        );
        self.get_diagnostics(&ctx, params, |program, ctx, source_file| {
            program.get_semantic_diagnostics(ctx.clone(), source_file)
        })
    }

    /// `handleGetSuggestionDiagnostics` — `@gen-proto-nullable`.
    pub(crate) fn handle_get_suggestion_diagnostics(
        &self,
        ctx: &core_::context::Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<Option<DiagnosticResponse>>, String> {
        let ctx = core_::context::with_checker_lifetime(
            ctx,
            core_::context::CheckerLifetime::Diagnostics,
        );
        self.get_diagnostics(&ctx, params, |program, ctx, source_file| {
            program.get_suggestion_diagnostics(ctx.clone(), source_file)
        })
    }

    /// `handleGetDeclarationDiagnostics` — `@gen-proto-nullable`.
    pub(crate) fn handle_get_declaration_diagnostics(
        &self,
        ctx: &core_::context::Context,
        params: &GetDiagnosticsParams,
    ) -> Result<Vec<Option<DiagnosticResponse>>, String> {
        let ctx = core_::context::with_checker_lifetime(
            ctx,
            core_::context::CheckerLifetime::Diagnostics,
        );
        self.get_diagnostics(&ctx, params, |program, ctx, source_file| {
            program.get_declaration_diagnostics(ctx.clone(), source_file)
        })
    }

    /// `handleGetConfigFileParsingDiagnostics` returns config file
    /// parsing diagnostics. `@gen-proto-nullable`.
    pub(crate) fn handle_get_config_file_parsing_diagnostics(
        &self,
        _ctx: &core_::context::Context,
        params: &GetProjectDiagnosticsParams,
    ) -> Result<Vec<Option<DiagnosticResponse>>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;

        let diags = program.get_config_file_parsing_diagnostics();
        Ok(diagnostic_responses(&program, &diags))
    }

    /// `handleGetProgramDiagnostics` returns program-wide diagnostics,
    /// including options diagnostics. `@gen-proto-nullable`.
    pub(crate) fn handle_get_program_diagnostics(
        &self,
        _ctx: &core_::context::Context,
        params: &GetProjectDiagnosticsParams,
    ) -> Result<Vec<Option<DiagnosticResponse>>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;

        let diags = program.get_program_diagnostics();
        Ok(diagnostic_responses(&program, &diags))
    }

    /// `handleGetGlobalDiagnostics` returns global (non-file-specific)
    /// semantic diagnostics. `@gen-proto-nullable`.
    pub(crate) fn handle_get_global_diagnostics(
        &self,
        ctx: &core_::context::Context,
        params: &GetProjectDiagnosticsParams,
    ) -> Result<Vec<Option<DiagnosticResponse>>, String> {
        let ctx = core_::context::with_checker_lifetime(
            ctx,
            core_::context::CheckerLifetime::Diagnostics,
        );
        let sd = self.get_snapshot_data(params.snapshot)?;

        let proj = sd.get_project(&params.project)?;

        let Some(program) = proj.get_program().cloned() else {
            return Err(format!("{}: project has no program", ERR_CLIENT_ERROR));
        };

        // Global diagnostics are accumulated lazily by the project's
        // checker pool as files are checked. Force a full semantic pass so
        // any global (non-file-specific) diagnostics are produced;
        // otherwise this would return an empty result for projects using
        // an external checker pool (the typical API case), since
        // Program::get_global_diagnostics only reports for the internal
        // pool.
        let _ = program.get_semantic_diagnostics(ctx.clone(), None);

        // PORT: `Project::get_project_diagnostics` takes no ctx in the
        // port. `core.Filter(d.File() == nil)` keeps global diagnostics.
        let diags: Vec<DiagnosticRef> = proj
            .get_project_diagnostics()
            .into_iter()
            .filter(|d| lock_diagnostic(d).file().is_none())
            .collect();
        Ok(diagnostic_responses(&program, &diags))
    }

    /// `handleGetReferencesToSymbolInFile` returns node handles for all
    /// identifiers in a file that reference the given symbol.
    pub(crate) fn handle_get_references_to_symbol_in_file(
        &self,
        ctx: &core_::context::Context,
        params: &GetReferencesToSymbolInFileParams,
    ) -> Result<Vec<NodeHandle>, String> {
        // `defer setup.done()` — `CheckerSetup::drop` releases the checker.
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        // PORT: `resolve_symbol_handle`'s `nodes` parameter is unused —
        // Go's `symbol == nil` check is dead code (resolution errors or
        // returns a symbol), mirrored by `?`.
        let symbol = setup.resolve_symbol_handle(&params.symbol, &mut Vec::new())?;

        let Some(source_file) = setup
            .program
            .get_source_file(&params.file.to_file_name(&setup.program.base_directory()))
        else {
            return Err(format!(
                "{}: source file not found: {}",
                ERR_CLIENT_ERROR,
                params.file
            ));
        };

        let nodes = setup
            .checker
            .borrow_mut()
            .get_references_to_symbol_in_file(source_file, symbol.symbol);
        let arena = setup.program.arena_of(source_file);
        Ok(nodes
            .into_iter()
            .map(|node| setup.sd.node_handle_from((*arena).get_mut(), source_file, node))
            .collect())
    }

    /// `handleGetSignatureUsages` — `@gen-proto-nullable`.
    pub(crate) fn handle_get_signature_usages(
        &self,
        ctx: &core_::context::Context,
        params: &GetSignatureUsagesParams,
    ) -> Result<Vec<SignatureUsageResponse>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;

        // Go's `signatureDecl == nil` check is dead code —
        // `resolve_node_handle` errors where Go could return nil.
        let signature_decl = sd.resolve_node_handle(&program, &params.signature_decl)?;

        let lang_svc =
            self.setup_language_service(&sd.snapshot, &program, &params.project, "")?;

        let usages = lang_svc.get_signature_usages(ctx, signature_decl);

        let mut result = Vec::with_capacity(usages.len());
        for u in &usages {
            let mut entry = SignatureUsageResponse {
                name: program_node_handle(&sd, &program, u.name),
                ..Default::default()
            };
            if let Some(call) = u.call {
                entry.call = program_node_handle(&sd, &program, call);
            }
            result.push(entry);
        }
        Ok(result)
    }

    /// `handleGetCompletionsAtPosition` returns completions at a position
    /// in a document. `@gen-proto-nullable`.
    pub(crate) fn handle_get_completions_at_position(
        &self,
        ctx: &core_::context::Context,
        params: &GetCompletionsAtPositionParams,
    ) -> Result<Option<CompletionInfoResponse>, String> {
        let ctx = if params.include_symbol {
            core_::context::with_checker_lifetime(
                ctx,
                core_::context::CheckerLifetime::Api,
            )
        } else {
            ctx.clone()
        };
        let sd = self.get_snapshot_data(params.snapshot)?;

        // `run` — Go's `func(snapshot, program) (*ls.CompletionList, error)`.
        // The ls `Error` is mapped to its `Display` text so setup (`String`)
        // and ls errors share a channel; `NeedsAutoImports` is matched on
        // message text below (see header note).
        // Return type is inferred — `ls::completions::CompletionList` is
        // `pub` inside a private module and cannot be named here.
        let run = |snapshot: &project::snapshot::Snapshot,
                   program: &Rc<compiler::program::Program>| {
            let Some(source_file) = program
                .get_source_file(&params.file.to_file_name(&program.base_directory()))
            else {
                return Ok(None);
            };
            let (active_file, internal_pos) = {
                let nodes = program.arena_of(source_file);
                let sf = nodes[source_file].as_source_file();
                (
                    sf.file_name().as_string().to_string(),
                    sf.position_map().utf16_to_utf8(params.position as usize),
                )
            };
            let lang_svc =
                self.setup_language_service(snapshot, program, &params.project, &active_file)?;
            lang_svc
                .get_completions_at_position(
                    &ctx,
                    source_file,
                    internal_pos as core_::text::TextPos,
                    params.trigger_character.as_deref(),
                    params.include_symbol,
                )
                .map_err(|e| e.to_string())
        };

        let mut program = sd.get_program(&params.project)?;
        let mut result = run(&sd.snapshot, &program);
        // `errors.Is(err, ls.ErrNeedsAutoImports)` — on message text (see
        // header note); `Error::Wrapped` renders its chain into `msg`.
        let needs_auto_imports = result
            .as_ref()
            .err()
            .is_some_and(|e| e.contains("completion list needs auto imports"));
        // The derived snapshot stays alive until the response is built —
        // Go's `defer preparedSnapshot.Deref()`.
        let mut prepared_snapshot = None;
        if needs_auto_imports {
            if params.include_symbol {
                return Err(format!(
                    "{}: snapshot is not prepared for auto-imports for {}",
                    ERR_CLIENT_ERROR,
                    params.file
                ));
            }
            let Some(source_file) = program
                .get_source_file(&params.file.to_file_name(&program.base_directory()))
            else {
                return Ok(None);
            };
            let uri = {
                let nodes = program.arena_of(source_file);
                lsconv::file_name_to_document_uri(
                    nodes[source_file].as_source_file().file_name(),
                )
            };
            let prepared = self.snapshot_host.clone_snapshot_with_auto_imports(
                &ctx,
                &sd.snapshot,
                &uri,
                None,
            );
            if let Some(session) = &self.project_session {
                session.try_adopt_snapshot_in_background(&sd.snapshot, &prepared);
            }
            if ctx.is_cancelled() {
                project::snapshot::Snapshot::deref(&prepared);
                return Err("context canceled".to_string());
            }
            let project_id = &params.project;
            let Some(proj) = prepared
                .project_collection
                .get_project(project_id)
                .cloned()
            else {
                project::snapshot::Snapshot::deref(&prepared);
                return Err(format!(
                    "{}: project {} not found",
                    ERR_CLIENT_ERROR,
                    project_id
                ));
            };
            let Some(prepared_program) = proj.get_program().cloned() else {
                project::snapshot::Snapshot::deref(&prepared);
                return Err(format!("{}: project has no program", ERR_CLIENT_ERROR));
            };
            result = run(&prepared, &prepared_program);
            program = prepared_program;
            prepared_snapshot = Some(prepared);
        }

        let response = (|| -> Result<Option<CompletionInfoResponse>, String> {
            let result = match result {
                Err(e) => return Err(e),
                Ok(None) => return Ok(None),
                Ok(Some(result)) => result,
            };
            let mut entries = Vec::with_capacity(result.items.len());
            for item in &result.items {
                // PORT: `Items` elements are `Option` (Go's nil
                // `*CompletionItem`); Go would panic dereferencing one —
                // skip instead.
                let Some(item) = item else {
                    continue;
                };
                let lsp = &item.item;
                let mut entry = CompletionEntryResponse {
                    name: lsp.label.clone(),
                    sort_text: lsp.sort_text.clone(),
                    insert_text: lsp.insert_text.clone(),
                    filter_text: lsp.filter_text.clone(),
                    detail: lsp.detail.clone(),
                    ..Default::default()
                };
                if let Some(kind) = &lsp.kind {
                    entry.kind = kind.0;
                }
                if let Some(details) = &lsp.label_details {
                    entry.label_details = Some(CompletionEntryLabelDetailsResponse {
                        detail: details.detail.clone(),
                        description: details.description.clone(),
                    });
                }
                if let Some(symbol) = item.symbol {
                    // PORT: symbols are registered against the original
                    // `sd` (as in Go) but resolve through the (possibly
                    // prepared) program's arenas.
                    let nodes = program_symbol_nodes(&program, symbol);
                    entry.symbol = sd.new_symbol_response(
                        (*nodes).get_mut(),
                        &program.symbols,
                        symbol,
                        &params.project,
                    );
                }
                entries.push(entry);
            }
            Ok(Some(CompletionInfoResponse {
                is_incomplete: result.is_incomplete,
                entries,
            }))
        })();
        if let Some(prepared) = prepared_snapshot {
            project::snapshot::Snapshot::deref(&prepared);
        }
        response
    }

    /// `handleGetReferencedSymbolsForNode` returns node handles for all
    /// references found at a node. `@gen-proto-nullable`.
    pub(crate) fn handle_get_referenced_symbols_for_node(
        &self,
        ctx: &core_::context::Context,
        params: &GetReferencedSymbolsForNodeParams,
    ) -> Result<Vec<ReferencedSymbolEntry>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;

        // Go's `node == nil` check is dead code — `resolve_node_handle`
        // errors where Go could return nil.
        let node = sd.resolve_node_handle(&program, &params.node)?;

        let lang_svc =
            self.setup_language_service(&sd.snapshot, &program, &params.project, "")?;

        let source_files = program.source_files();
        let entries = lang_svc.get_referenced_symbols_for_node_public(
            ctx,
            params.position as i32,
            node,
            &source_files,
        );

        // `SymbolAndEntries::definition_node` resolves a symbol-only
        // definition through the checker's symbol arena — acquire one
        // like `get_referenced_symbols_for_node` does internally.
        let (checker, done) = program.get_type_checker(ctx.clone());

        let mut result = Vec::new();
        for entry in &entries {
            // PORT(visibility): `definition_node`/`references`/
            // `definition_symbol`/`is_node_entry`/`node` are `pub(crate)`
            // in tsc_ls — see the header note.
            let e = entry.borrow();
            let Some(def_node) = e.definition_node(&checker) else {
                continue;
            };
            let mut refs = Vec::new();
            for ref_ in &e.references {
                if let Some(node) = ref_.borrow().node() {
                    refs.push(program_node_handle(&sd, &program, node));
                }
            }
            let mut re = ReferencedSymbolEntry {
                definition: program_node_handle(&sd, &program, def_node),
                references: refs,
                ..Default::default()
            };
            if let Some(sym) = e.definition_symbol() {
                let nodes = program_symbol_nodes(&program, sym);
                re.symbol = sd.new_symbol_response(
                    (*nodes).get_mut(),
                    &program.symbols,
                    sym,
                    &params.project,
                );
            }
            result.push(re);
        }
        drop(checker);
        done();
        Ok(result)
    }
}
