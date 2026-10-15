// Ported from tsc/internal/api/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//   (handlers at session.go:2459-3600)
//
// Symbol/type/signature resolution handlers: source-file enumeration,
// module/type-reference-directive resolution lookups, symbol and type
// queries on the API checker, symbol/type/signature property accessors,
// and the import-adder edits endpoint.
//
// PORT notes:
// - `new_symbol_response`/`new_type_response`/`new_signature_response`
//   need the node arena containing the object's owning file (`nodes` —
//   see `SnapshotData::new_symbol_response`). `symbol_nodes`/
//   `type_nodes`/`signature_nodes` pick that arena through the packed
//   `NodeId` file index of the first declaration, mirroring
//   `symbolOwnerFile`'s own `declarations[0]` choice. For merged symbols
//   whose declarations span files, handles for foreign-file declarations
//   are computed in that arena — the scaffold's single-arena shape; Go
//   resolves each node's own `*ast.SourceFile` instead.
// - Go's `resolveSignaturePropertyOfSignature` runs without a checker;
//   `SnapshotData::new_signature_response` needs `&Checker` (its
//   `signature_arena`/`types`/`symbol_arena`), so the port goes through
//   `setup_checker`. Same for the symbol-property-of-signature helpers,
//   which need `program.symbols` (`SignatureEntry` does not carry a
//   symbol arena).
// - `handle_get_import_adder_edits`: `defer preparedSnapshot.Deref()`
//   becomes the `SnapshotDeref` drop guard; `autoimport.NewView` in the
//   port takes the full `lsutil.UserPreferences` (matching
//   `LanguageService::get_prepared_auto_import_view`), not
//   `ModuleSpecifierPreferences()`.

use std::cmp::Ordering;
use std::rc::Rc;
use std::sync::Arc;

use tsc_ast as ast;
use tsc_astnav as astnav;
use tsc_checker::checker_core::Checker;
use tsc_checker::types as checker;
use tsc_compiler as compiler;
use tsc_core as core_;
use tsc_ls as ls;
use tsc_ls::autoimport::import_adder::ImportAdder;
use tsc_lsconv as lsconv;
use tsc_lsproto as lsproto;
use tsc_module as module;
use tsc_project as project;

use crate::proto::*;
use crate::session::*;

/// `nodes` fallback for objects with no declaration chain — only
/// reachable when `symbol_owner_file`/`get_source_file_of_symbol` would
/// return `None` before indexing `nodes`.
fn fallback_nodes(program: &compiler::program::Program) -> Rc<ast::NodeArenaBuf> {
    program
        .source_files()
        .first()
        .map(|&file| program.arena_of(file))
        .unwrap_or_else(|| Rc::new(ast::NodeArenaBuf::default()))
}

/// The node arena `new_symbol_response` expects for `symbol`: the arena
/// of the file containing the first declaration found by
/// `get_source_file_of_symbol`'s walk (`declarations[0]`, with the
/// implicit-prototype `parent` fallback). The packed `NodeId` file index
/// addresses the arena directly, without a parent walk.
fn symbol_nodes(
    program: &compiler::program::Program,
    arena: &ast::SymbolArena,
    symbol: ast::SymbolId,
) -> Rc<ast::NodeArenaBuf> {
    let mut sym = symbol;
    let declaration = loop {
        let s = arena.get_ref(sym);
        if s.flags.intersects(ast::SymbolFlags::TRANSIENT) {
            break None;
        }
        if let Some(&declaration) = s.declarations.first() {
            break Some(declaration);
        }
        match s.parent {
            Some(parent) => sym = parent,
            None => break None,
        }
    };
    match declaration {
        Some(declaration) => program.arena_of(declaration),
        None => fallback_nodes(program),
    }
}

/// The node arena `new_type_response` expects for `t`: its `symbol` (or
/// `alias.symbol`, mirroring `new_type_response`'s reference order).
fn type_nodes(
    program: &compiler::program::Program,
    c: &Checker,
    ty: checker::TypeId,
) -> Rc<ast::NodeArenaBuf> {
    let t = c.types.get_ref(ty);
    match t.symbol.or_else(|| t.alias.as_ref().and_then(|a| a.symbol)) {
        Some(symbol) => symbol_nodes(program, &c.symbol_arena, symbol),
        None => fallback_nodes(program),
    }
}

/// The node arena `new_signature_response` expects for `sig`: its
/// declaration's file, or the first parameter's owning file.
fn signature_nodes(
    program: &compiler::program::Program,
    c: &Checker,
    signature: checker::SignatureId,
) -> Rc<ast::NodeArenaBuf> {
    let sig = c.signature_arena.get(signature);
    if let Some(declaration) = sig.declaration() {
        return program.arena_of(declaration);
    }
    if let Some(&parameter) = sig.parameters().first() {
        return symbol_nodes(program, &c.symbol_arena, parameter);
    }
    fallback_nodes(program)
}

/// `defer preparedSnapshot.Deref()` — releases the derived snapshot's
/// reference when the handler scope exits.
struct SnapshotDeref(Arc<project::snapshot::Snapshot>);

impl Drop for SnapshotDeref {
    fn drop(&mut self) {
        self.0.deref();
    }
}

/// `newResolvedModuleResponse`.
fn new_resolved_module_response(
    resolution: Option<module::ResolvedModule>,
) -> Option<ResolvedModule> {
    let resolution = resolution?;
    if !resolution.is_resolved() {
        return None;
    }
    Some(ResolvedModule {
        resolved_file_name: resolution.resolved_file_name.as_string().to_string(),
        original_path: resolution.original_path.as_string().to_string(),
        extension: resolution.extension,
        resolved_using_ts_extension: resolution.resolved_using_ts_extension,
        resolved_using_extra_extensions: resolution.resolved_using_extra_extensions,
        package_id: new_package_id(&resolution.package_id),
        is_external_library_import: resolution.is_external_library_import,
        alternate_result: resolution.alternate_result.as_string().to_string(),
    })
}

/// `newResolvedTypeReferenceDirectiveResponse`.
fn new_resolved_type_reference_directive_response(
    resolution: Option<module::ResolvedTypeReferenceDirective>,
) -> Option<ResolvedTypeReferenceDirective> {
    let resolution = resolution?;
    if !resolution.is_resolved() {
        return None;
    }
    Some(ResolvedTypeReferenceDirective {
        primary: resolution.primary,
        resolved_file_name: resolution.resolved_file_name.as_string().to_string(),
        original_path: resolution.original_path.as_string().to_string(),
        package_id: new_package_id(&resolution.package_id),
        is_external_library_import: resolution.is_external_library_import,
    })
}

/// `originalTextOffset` — maps an LSP position to an original-text byte
/// offset. PORT: `position.line`/`character` are `u32`, so Go's `line < 0`
/// check is folded into the bounds test.
fn original_text_offset(
    line_map: &lsconv::LspLineMap,
    position: lsproto::Position,
    text_length: usize,
) -> Option<usize> {
    let line = position.line as usize;
    if line >= line_map.line_starts.len() {
        return None;
    }
    let line_start = line_map.line_starts[line] as usize;
    let offset = line_start + position.character as usize;
    if offset < line_start || offset > text_length {
        return None;
    }
    Some(offset)
}

/// `toAPITextEdits` — converts LSP text edits to API text edits
/// (UTF-16 positions into the original text). `None` mirrors Go's `nil`
/// result when a position falls outside the line map.
fn to_api_text_edits(
    nodes: &Rc<ast::NodeArenaBuf>,
    source_file: ast::NodeId,
    edits: &[lsproto::TextEdit],
) -> Option<Vec<TextEdit>> {
    let original_text = nodes[source_file].as_source_file().original_text();
    let line_map = lsconv::compute_lsp_line_starts(original_text.as_bytes());
    let position_map = ast::positionmap::compute_position_map(original_text.as_bytes());
    let mut result = Vec::with_capacity(edits.len());
    for edit in edits {
        let start = original_text_offset(&line_map, edit.range.start, original_text.len())?;
        let end = original_text_offset(&line_map, edit.range.end, original_text.len())?;
        result.push(TextEdit {
            pos: position_map.utf8_to_utf16(start) as i64,
            end: position_map.utf8_to_utf16(end) as i64,
            new_text: edit.new_text.clone(),
        });
    }
    Some(result)
}

impl crate::session::Session {
    /// `s.resolveOptionalSourceFile` resolves an optional
    /// `DocumentIdentifier` to a source file. Returns `None` if the
    /// identifier is `None` (meaning all files).
    pub(crate) fn resolve_optional_source_file(
        &self,
        program: &compiler::program::Program,
        file: Option<&DocumentIdentifier>,
    ) -> Result<Option<ast::NodeId>, String> {
        let Some(file) = file else {
            return Ok(None);
        };
        let source_file = program.get_source_file(&file.to_file_name(&program.base_directory()));
        match source_file {
            Some(source_file) => Ok(Some(source_file)),
            None => Err(format!(
                "{}: source file not found: {}",
                ERR_CLIENT_ERROR, file
            )),
        }
    }

    /// `s.resolveSourceFile` — `resolve_optional_source_file` for params
    /// where the document identifier is required (a bare
    /// `DocumentIdentifier` field in Go always reaches the not-found
    /// error or a file).
    pub(crate) fn resolve_source_file(
        &self,
        program: &compiler::program::Program,
        file: &DocumentIdentifier,
    ) -> Result<ast::NodeId, String> {
        self.resolve_optional_source_file(program, Some(file))?
            .ok_or_else(|| {
                format!("{}: source file not found: {}", ERR_CLIENT_ERROR, file)
            })
    }

    /// `handleGetSourceFileNames` returns file names of all source files
    /// in a project.
    ///
    /// PORT: `[]tspath.RootedFilePath` → `Vec<String>` —
    /// `RootedFilePath` carries no `Serialize` impl (proto bridges it
    /// per-field through `ser_str`); a `Vec<String>` is the same wire
    /// shape.
    pub(crate) fn handle_get_source_file_names(
        &self,
        _ctx: &core_::context::Context,
        params: &GetSourceFileNamesParams,
    ) -> Result<Vec<String>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        Ok(program
            .source_files()
            .iter()
            .map(|&file| {
                let nodes = program.arena_of(file);
                nodes[file].as_source_file().file_name().as_string().to_string()
            })
            .collect())
    }

    /// `handleGetSourceFileMetadata` returns program-stored metadata for a
    /// single source file.
    pub(crate) fn handle_get_source_file_metadata(
        &self,
        _ctx: &core_::context::Context,
        params: &GetSourceFileParams,
    ) -> Result<Option<SourceFileMetadata>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        let Some(source_file) =
            program.get_source_file(&params.file.to_file_name(&program.base_directory()))
        else {
            return Ok(None);
        };
        let path_key = {
            let nodes = program.arena_of(source_file);
            nodes[source_file].as_source_file().path_key().clone()
        };
        let meta_data = program.get_source_file_meta_data(&path_key);
        Ok(Some(SourceFileMetadata {
            is_default_library: program.is_source_file_default_library(&path_key),
            is_from_external_library: program.is_source_file_from_external_library(source_file),
            package_json_type: meta_data.package_json_type,
            package_json_directory: meta_data.package_json_directory,
            implied_node_format: meta_data.implied_node_format,
        }))
    }

    /// `handleGetModeForUsageLocation`.
    pub(crate) fn handle_get_mode_for_usage_location(
        &self,
        _ctx: &core_::context::Context,
        params: &GetModeForUsageLocationParams,
    ) -> Result<core_::compileroptions::ResolutionMode, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        let source_file = self.resolve_source_file(&program, &params.file)?;
        let usage = sd.resolve_node_handle(&program, &params.usage)?;
        {
            let nodes = program.arena_of(usage);
            if !ast::is_string_literal_like(&nodes[usage]) {
                return Err(format!(
                    "{}: usage must be a StringLiteralLike node",
                    ERR_CLIENT_ERROR
                ));
            }
        }
        let has_name = program.file_has_file_name(source_file);
        Ok(program.get_mode_for_usage_location(&has_name, usage))
    }

    /// `handleGetModeForResolutionAtIndex`.
    pub(crate) fn handle_get_mode_for_resolution_at_index(
        &self,
        _ctx: &core_::context::Context,
        params: &GetModeForResolutionAtIndexParams,
    ) -> Result<core_::compileroptions::ResolutionMode, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        let source_file = self.resolve_source_file(&program, &params.file)?;
        let resolution_count = {
            let nodes = program.arena_of(source_file);
            let source_file_data = nodes[source_file].as_source_file();
            source_file_data.imports().len()
                + source_file_data
                    .module_augmentations
                    .iter()
                    .filter(|&&augmentation| nodes[augmentation].kind == ast::Kind::StringLiteral)
                    .count()
        };
        if params.index < 0 || params.index >= resolution_count as i64 {
            return Err(format!("{}: invalid resolution index", ERR_CLIENT_ERROR));
        }
        Ok(program.get_mode_for_resolution_at_index(source_file, params.index as usize))
    }

    /// `handleGetResolvedModule`.
    pub(crate) fn handle_get_resolved_module(
        &self,
        _ctx: &core_::context::Context,
        params: &GetResolvedModuleParams,
    ) -> Result<Option<ResolvedModule>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        let source_file = self.resolve_source_file(&program, &params.file)?;
        let has_name = program.file_has_file_name(source_file);
        Ok(new_resolved_module_response(program.get_resolved_module(
            &has_name,
            &params.module_name,
            params.mode,
        )))
    }

    /// `handleGetResolvedModuleFromModuleSpecifier`.
    pub(crate) fn handle_get_resolved_module_from_module_specifier(
        &self,
        _ctx: &core_::context::Context,
        params: &GetResolvedModuleFromModuleSpecifierParams,
    ) -> Result<Option<ResolvedModule>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        let node = sd.resolve_node_handle(&program, &params.module_specifier)?;
        let mut source_file;
        {
            let nodes = program.arena_of(node);
            if !ast::is_string_literal_like(&nodes[node]) {
                return Err(format!(
                    "{}: moduleSpecifier must be a StringLiteralLike node",
                    ERR_CLIENT_ERROR
                ));
            }
            source_file = ast::get_source_file_of_node(Some(node), nodes.as_slice());
        }
        if let Some(file) = params.source_file.as_ref() {
            source_file = self.resolve_optional_source_file(&program, Some(file))?;
        }
        let Some(source_file) = source_file else {
            return Err(format!(
                "{}: moduleSpecifier must have a SourceFile ancestor or sourceFile must be provided",
                ERR_CLIENT_ERROR
            ));
        };
        Ok(new_resolved_module_response(
            program.get_resolved_module_from_module_specifier(source_file, node),
        ))
    }

    /// `handleGetResolvedTypeReferenceDirective`.
    pub(crate) fn handle_get_resolved_type_reference_directive(
        &self,
        _ctx: &core_::context::Context,
        params: &GetResolvedTypeReferenceDirectiveParams,
    ) -> Result<Option<ResolvedTypeReferenceDirective>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        let source_file = self.resolve_source_file(&program, &params.file)?;
        let has_name = program.file_has_file_name(source_file);
        Ok(new_resolved_type_reference_directive_response(
            program.get_resolved_type_reference_directive(
                &has_name,
                &params.type_directive_name,
                params.mode,
            ),
        ))
    }

    /// `handleGetResolvedTypeReferenceDirectiveFromReference`.
    pub(crate) fn handle_get_resolved_type_reference_directive_from_reference(
        &self,
        _ctx: &core_::context::Context,
        params: &GetResolvedTypeReferenceDirectiveFromReferenceParams,
    ) -> Result<Option<ResolvedTypeReferenceDirective>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        let source_file = self.resolve_source_file(&program, &params.source_file)?;
        let has_name = program.file_has_file_name(source_file);
        let mut mode = params.resolution_mode;
        if mode == core_::compileroptions::ResolutionMode::None {
            mode = program.get_default_resolution_mode_for_file(&has_name);
        }
        Ok(new_resolved_type_reference_directive_response(
            program.get_resolved_type_reference_directive(
                &has_name,
                &params.type_directive_name,
                mode,
            ),
        ))
    }

    /// `handleGetSymbolAtPosition` returns the symbol at a position in a
    /// file.
    pub(crate) fn handle_get_symbol_at_position(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolAtPositionParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let Some(source_file) = setup
            .program
            .get_source_file(&params.file.to_file_name(&setup.program.base_directory()))
        else {
            return Err(format!(
                "{}: source file not found: {}",
                ERR_CLIENT_ERROR, params.file
            ));
        };

        let node = {
            let nodes = setup.program.arena_of(source_file);
            let position = nodes[source_file]
                .as_source_file()
                .position_map()
                .utf16_to_utf8(params.position as usize);
            astnav::tokens::get_touching_property_name(
                (*nodes).get_mut(),
                source_file,
                position as core_::text::TextPos,
            )
        };
        let Some(node) = node else {
            return Ok(None);
        };

        let mut c = setup.checker.borrow_mut();
        let Some(symbol) = c.get_symbol_at_location_api(node) else {
            return Ok(None);
        };
        let nodes = symbol_nodes(&setup.program, &c.symbol_arena, symbol);
        Ok(setup.new_symbol_response((*nodes).get_mut(), &c.symbol_arena, symbol))
    }

    /// `handleGetSymbolOfSourceFile` returns the module symbol for a
    /// source file, if any. For non-module (script) files, returns `None`.
    pub(crate) fn handle_get_symbol_of_source_file(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolOfSourceFileParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let Some(source_file) = setup
            .program
            .get_source_file(&params.file.to_file_name(&setup.program.base_directory()))
        else {
            return Err(format!(
                "{}: source file not found: {}",
                ERR_CLIENT_ERROR, params.file
            ));
        };

        let mut c = setup.checker.borrow_mut();
        let Some(symbol) = c.get_symbol_at_location_api(source_file) else {
            return Ok(None);
        };
        let nodes = symbol_nodes(&setup.program, &c.symbol_arena, symbol);
        Ok(setup.new_symbol_response((*nodes).get_mut(), &c.symbol_arena, symbol))
    }

    /// `handleGetSymbolsOfSourceFiles` returns the module symbols for
    /// multiple source files.
    pub(crate) fn handle_get_symbols_of_source_files(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolsOfSourceFilesParams,
    ) -> Result<Vec<Option<SymbolResponse>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let mut c = setup.checker.borrow_mut();
        let mut results = Vec::with_capacity(params.files.len());
        for file in &params.files {
            let Some(source_file) = setup
                .program
                .get_source_file(&file.to_file_name(&setup.program.base_directory()))
            else {
                return Err(format!(
                    "{}: source file not found: {}",
                    ERR_CLIENT_ERROR, file
                ));
            };
            let symbol = c.get_symbol_at_location_api(source_file);
            results.push(symbol.and_then(|symbol| {
                let nodes = symbol_nodes(&setup.program, &c.symbol_arena, symbol);
                setup.new_symbol_response((*nodes).get_mut(), &c.symbol_arena, symbol)
            }));
        }
        Ok(results)
    }

    /// `handleGetSymbolsAtPositions` returns symbols at multiple
    /// positions in a file.
    pub(crate) fn handle_get_symbols_at_positions(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolsAtPositionsParams,
    ) -> Result<Vec<Option<SymbolResponse>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let Some(source_file) = setup
            .program
            .get_source_file(&params.file.to_file_name(&setup.program.base_directory()))
        else {
            return Err(format!(
                "{}: source file not found: {}",
                ERR_CLIENT_ERROR, params.file
            ));
        };

        let nodes = setup.program.arena_of(source_file);
        let positions: Vec<usize> = params
            .positions
            .iter()
            .map(|&pos| {
                nodes[source_file]
                    .as_source_file()
                    .position_map()
                    .utf16_to_utf8(pos as usize)
            })
            .collect();
        let mut c = setup.checker.borrow_mut();
        let mut results = Vec::with_capacity(positions.len());
        for position in positions {
            let node = astnav::tokens::get_touching_property_name(
                (*nodes).get_mut(),
                source_file,
                position as core_::text::TextPos,
            );
            results.push(node.and_then(|node| {
                c.get_symbol_at_location_api(node).and_then(|symbol| {
                    let symbol_nodes =
                        symbol_nodes(&setup.program, &c.symbol_arena, symbol);
                    setup.new_symbol_response(
                        (*symbol_nodes).get_mut(),
                        &c.symbol_arena,
                        symbol,
                    )
                })
            }));
        }
        Ok(results)
    }

    /// `handleGetSymbolAtLocation` returns the symbol at a node location.
    ///
    /// PORT: Go's `node == nil` check is unreachable —
    /// `resolve_node_handle` errors on every unresolvable handle.
    pub(crate) fn handle_get_symbol_at_location(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolAtLocationParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;

        let mut c = setup.checker.borrow_mut();
        let Some(symbol) = c.get_symbol_at_location_api(node) else {
            return Ok(None);
        };
        let nodes = symbol_nodes(&setup.program, &c.symbol_arena, symbol);
        Ok(setup.new_symbol_response((*nodes).get_mut(), &c.symbol_arena, symbol))
    }

    /// `handleGetSymbolsAtLocations` returns symbols at multiple node
    /// locations.
    pub(crate) fn handle_get_symbols_at_locations(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolsAtLocationsParams,
    ) -> Result<Vec<Option<SymbolResponse>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let mut c = setup.checker.borrow_mut();
        let mut results = Vec::with_capacity(params.locations.len());
        for loc in &params.locations {
            let node = setup.sd.resolve_node_handle(&setup.program, loc)?;
            results.push(c.get_symbol_at_location_api(node).and_then(|symbol| {
                let nodes = symbol_nodes(&setup.program, &c.symbol_arena, symbol);
                setup.new_symbol_response((*nodes).get_mut(), &c.symbol_arena, symbol)
            }));
        }
        Ok(results)
    }

    /// `handleGetTypeOfSymbol` returns the type of a symbol.
    pub(crate) fn handle_get_type_of_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypeOfSymbolParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let symbol = setup.resolve_symbol_handle(&params.symbol, &mut Vec::new())?;
        let mut c = setup.checker.borrow_mut();
        let ty = c.get_type_of_symbol(symbol.symbol);
        let nodes = type_nodes(&setup.program, &c, ty);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, ty))
    }

    /// `handleGetTypesOfSymbols` returns the types of multiple symbols.
    pub(crate) fn handle_get_types_of_symbols(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypesOfSymbolsParams,
    ) -> Result<Vec<Option<TypeResponse>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let mut c = setup.checker.borrow_mut();
        let mut results = Vec::with_capacity(params.symbols.len());
        for symbol_reference in &params.symbols {
            let symbol = setup.resolve_symbol_handle(symbol_reference, &mut Vec::new())?;
            // `resolve_symbol_handle` errors on an unresolvable handle and
            // `get_type_of_symbol` never returns none, so every element
            // resolves to a type (error type at worst).
            let ty = c.get_type_of_symbol(symbol.symbol);
            let nodes = type_nodes(&setup.program, &c, ty);
            results.push(
                setup
                    .sd
                    .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, ty),
            );
        }
        Ok(results)
    }

    /// `handleGetDeclaredTypeOfSymbol` returns the declared type of a
    /// symbol (e.g. the type alias body for type alias symbols).
    pub(crate) fn handle_get_declared_type_of_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypeOfSymbolParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let symbol = setup.resolve_symbol_handle(&params.symbol, &mut Vec::new())?;
        let mut c = setup.checker.borrow_mut();
        let ty = c.get_declared_type_of_symbol(symbol.symbol);
        let nodes = type_nodes(&setup.program, &c, ty);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, ty))
    }

    /// `handleGetNonMissingTypeOfSymbol` returns the type of a symbol,
    /// excluding the missing type.
    pub(crate) fn handle_get_non_missing_type_of_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypeOfSymbolParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let symbol = setup.resolve_symbol_handle(&params.symbol, &mut Vec::new())?;
        let mut c = setup.checker.borrow_mut();
        let ty = c.get_non_missing_type_of_symbol(symbol.symbol);
        let nodes = type_nodes(&setup.program, &c, ty);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, ty))
    }

    /// `handleResolveName` resolves a name to a symbol at a given
    /// location.
    pub(crate) fn handle_resolve_name(
        &self,
        ctx: &core_::context::Context,
        params: &ResolveNameParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        // Resolve location node — either from node handle or from
        // fileName+position.
        let location = setup.resolve_location(
            &params.location,
            params.file.as_ref(),
            params.position,
        )?;

        let mut c = setup.checker.borrow_mut();
        let Some(symbol) = c.resolve_name_api(
            &params.name,
            location,
            ast::SymbolFlags(params.meaning),
            params.exclude_globals,
        ) else {
            return Ok(None);
        };
        let nodes = symbol_nodes(&setup.program, &c.symbol_arena, symbol);
        Ok(setup.new_symbol_response((*nodes).get_mut(), &c.symbol_arena, symbol))
    }

    /// `handleGetSymbolsInScope` returns all symbols with the given
    /// meaning that are visible at a location.
    pub(crate) fn handle_get_symbols_in_scope(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolsInScopeParams,
    ) -> Result<Vec<Option<SymbolResponse>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let Some(location) = setup.resolve_location(
            &params.location,
            params.file.as_ref(),
            params.position,
        )? else {
            return Err(format!(
                "{}: getSymbolsInScope requires a location",
                ERR_CLIENT_ERROR
            ));
        };

        let mut c = setup.checker.borrow_mut();
        let symbols = c.get_symbols_in_scope(location, ast::SymbolFlags(params.meaning));
        let results = symbols
            .iter()
            .map(|&symbol| {
                let nodes = symbol_nodes(&setup.program, &c.symbol_arena, symbol);
                setup.new_symbol_response((*nodes).get_mut(), &c.symbol_arena, symbol)
            })
            .collect();
        Ok(results)
    }

    /// `handleGetSignaturesOfType` returns the call or construct
    /// signatures of a type.
    pub(crate) fn handle_get_signatures_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetSignaturesOfTypeParams,
    ) -> Result<Vec<Option<SignatureResponse>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let t = setup.resolve_type_handle(params.r#type)?;
        // `checker.SignatureKind(params.Kind)` — Go's unchecked cast;
        // `get_signatures_of_structured_type` treats `!= Call` as
        // construct-signature lookup.
        let kind = if params.kind == checker::SignatureKind::Call as i32 {
            checker::SignatureKind::Call
        } else {
            checker::SignatureKind::Construct
        };
        let mut c = setup.checker.borrow_mut();
        let sigs = c.get_signatures_of_type(t.ty, kind);
        let results = sigs
            .iter()
            .map(|&sig| {
                let nodes = signature_nodes(&setup.program, &c, sig);
                setup.new_signature_response((*nodes).get_mut(), &c, sig)
            })
            .collect();
        Ok(results)
    }

    /// `handleGetResolvedSignature` returns the resolved signature of a
    /// call-like expression.
    pub(crate) fn handle_get_resolved_signature(
        &self,
        ctx: &core_::context::Context,
        params: &GetResolvedSignatureParams,
    ) -> Result<Option<SignatureResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;
        let mut c = setup.checker.borrow_mut();
        let Some(signature) = c.get_resolved_signature_api(node) else {
            return Ok(None);
        };
        let nodes = signature_nodes(&setup.program, &c, signature);
        Ok(setup.new_signature_response((*nodes).get_mut(), &c, signature))
    }

    /// `handleGetTypeAtLocation` returns the type at a node location.
    pub(crate) fn handle_get_type_at_location(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypeAtLocationParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let node = setup
            .sd
            .resolve_node_handle(&setup.program, &params.location)?;
        let mut c = setup.checker.borrow_mut();
        let ty = c.get_type_at_location(node);
        let nodes = type_nodes(&setup.program, &c, ty);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, ty))
    }

    /// `handleGetTypeAtLocations` returns types at multiple node
    /// locations.
    pub(crate) fn handle_get_type_at_locations(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypeAtLocationsParams,
    ) -> Result<Vec<Option<TypeResponse>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let mut c = setup.checker.borrow_mut();
        let mut results = Vec::with_capacity(params.locations.len());
        for loc in &params.locations {
            let node = setup.sd.resolve_node_handle(&setup.program, loc)?;
            // `resolve_node_handle` errors on an unresolvable handle and
            // `get_type_at_location` never returns none, so every element
            // resolves to a type (error type at worst).
            let ty = c.get_type_at_location(node);
            let nodes = type_nodes(&setup.program, &c, ty);
            results.push(
                setup
                    .sd
                    .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, ty),
            );
        }
        Ok(results)
    }

    /// `handleGetTypeAtPosition` returns the type at a position in a
    /// file.
    pub(crate) fn handle_get_type_at_position(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypeAtPositionParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let Some(source_file) = setup
            .program
            .get_source_file(&params.file.to_file_name(&setup.program.base_directory()))
        else {
            return Err(format!(
                "{}: source file not found: {}",
                ERR_CLIENT_ERROR, params.file
            ));
        };

        let node = {
            let nodes = setup.program.arena_of(source_file);
            let position = nodes[source_file]
                .as_source_file()
                .position_map()
                .utf16_to_utf8(params.position as usize);
            astnav::tokens::get_touching_property_name(
                (*nodes).get_mut(),
                source_file,
                position as core_::text::TextPos,
            )
        };
        let Some(node) = node else {
            return Ok(None);
        };

        let mut c = setup.checker.borrow_mut();
        let ty = c.get_type_at_location(node);
        if ty.is_none() {
            return Ok(None);
        }
        let nodes = type_nodes(&setup.program, &c, ty);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, ty))
    }

    /// `handleGetTypesAtPositions` returns types at multiple positions in
    /// a file.
    pub(crate) fn handle_get_types_at_positions(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypesAtPositionsParams,
    ) -> Result<Vec<Option<TypeResponse>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let Some(source_file) = setup
            .program
            .get_source_file(&params.file.to_file_name(&setup.program.base_directory()))
        else {
            return Err(format!(
                "{}: source file not found: {}",
                ERR_CLIENT_ERROR, params.file
            ));
        };

        let nodes = setup.program.arena_of(source_file);
        let positions: Vec<usize> = params
            .positions
            .iter()
            .map(|&pos| {
                nodes[source_file]
                    .as_source_file()
                    .position_map()
                    .utf16_to_utf8(pos as usize)
            })
            .collect();
        let mut c = setup.checker.borrow_mut();
        let mut results = Vec::with_capacity(positions.len());
        for position in positions {
            let node = astnav::tokens::get_touching_property_name(
                (*nodes).get_mut(),
                source_file,
                position as core_::text::TextPos,
            );
            results.push(node.and_then(|node| {
                let ty = c.get_type_at_location(node);
                if ty.is_none() {
                    return None;
                }
                let type_nodes = type_nodes(&setup.program, &c, ty);
                setup.sd.new_type_response(
                    (*type_nodes).get_mut(),
                    &mut c,
                    &setup.project_id,
                    ty,
                )
            }));
        }
        Ok(results)
    }

    /// `handleGetParentOfSymbol`.
    pub(crate) fn handle_get_parent_of_symbol(
        &self,
        _ctx: &core_::context::Context,
        params: &GetSymbolPropertyParams,
    ) -> Result<Option<SymbolResponse>, String> {
        self.resolve_symbol_property_of_symbol(params, |sym| sym.parent)
    }

    /// `handleGetMembersOfSymbol`.
    pub(crate) fn handle_get_members_of_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolPropertyParams,
    ) -> Result<Option<Vec<Option<SymbolResponse>>>, String> {
        self.resolve_symbol_table_property_of_symbol(ctx, params, |sym| {
            sym.members.clone()
        })
    }

    /// `handleGetExportsOfSymbol`.
    pub(crate) fn handle_get_exports_of_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolPropertyParams,
    ) -> Result<Option<Vec<Option<SymbolResponse>>>, String> {
        self.resolve_symbol_table_property_of_symbol(ctx, params, |sym| {
            sym.exports.clone()
        })
    }

    /// `handleGetExportSymbolOfSymbol`.
    pub(crate) fn handle_get_export_symbol_of_symbol(
        &self,
        _ctx: &core_::context::Context,
        params: &GetSymbolPropertyParams,
    ) -> Result<Option<SymbolResponse>, String> {
        self.resolve_symbol_property_of_symbol(params, |sym| sym.export_symbol)
    }

    /// `handleGetSymbolOfType`.
    pub(crate) fn handle_get_symbol_of_type(
        &self,
        _ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<SymbolResponse>, String> {
        self.resolve_symbol_property_of_type(params, |t| t.symbol)
    }

    /// `handleGetTargetOfType`.
    pub(crate) fn handle_get_target_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| t.target())
    }

    /// `handleGetFreshTypeOfType`.
    pub(crate) fn handle_get_fresh_type_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_literal_type().fresh_type()
        })
    }

    /// `handleGetRegularTypeOfType`.
    pub(crate) fn handle_get_regular_type_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_literal_type().regular_type()
        })
    }

    /// `handleGetTypesOfType`.
    pub(crate) fn handle_get_types_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        self.resolve_type_array_property_of_type(ctx, params, |t| t.types())
    }

    /// `handleGetTypeParametersOfType`.
    pub(crate) fn handle_get_type_parameters_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        self.resolve_type_array_property_of_type(ctx, params, |t| {
            t.as_interface_type()
                .expect("type is not an interface type")
                .type_parameters()
        })
    }

    /// `handleGetOuterTypeParametersOfType`.
    pub(crate) fn handle_get_outer_type_parameters_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        self.resolve_type_array_property_of_type(ctx, params, |t| {
            t.as_interface_type()
                .expect("type is not an interface type")
                .outer_type_parameters()
        })
    }

    /// `handleGetLocalTypeParametersOfType`.
    pub(crate) fn handle_get_local_type_parameters_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        self.resolve_type_array_property_of_type(ctx, params, |t| {
            t.as_interface_type()
                .expect("type is not an interface type")
                .local_type_parameters()
        })
    }

    /// `handleGetThisTypeOfType`.
    pub(crate) fn handle_get_this_type_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_interface_type()
                .expect("type is not an interface type")
                .this_type()
        })
    }

    /// `handleGetAliasTypeArgumentsOfType`.
    pub(crate) fn handle_get_alias_type_arguments_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        self.resolve_type_array_property_of_type(ctx, params, |t| {
            t.alias
                .as_ref()
                .map(|alias| alias.type_arguments())
                .unwrap_or(&[])
        })
    }

    /// `handleGetAliasSymbolOfType`.
    pub(crate) fn handle_get_alias_symbol_of_type(
        &self,
        _ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<SymbolResponse>, String> {
        self.resolve_symbol_property_of_type(params, |t| {
            t.alias.as_ref().and_then(|alias| alias.symbol)
        })
    }

    /// `handleGetObjectTypeOfType`.
    pub(crate) fn handle_get_object_type_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_indexed_access_type().object_type()
        })
    }

    /// `handleGetIndexTypeOfType`.
    pub(crate) fn handle_get_index_type_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_indexed_access_type().index_type()
        })
    }

    /// `handleGetCheckTypeOfType`.
    pub(crate) fn handle_get_check_type_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_conditional_type().check_type()
        })
    }

    /// `handleGetExtendsTypeOfType`.
    pub(crate) fn handle_get_extends_type_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_conditional_type().extends_type()
        })
    }

    /// `handleGetBaseTypeOfType`.
    pub(crate) fn handle_get_base_type_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_substitution_type().base_type()
        })
    }

    /// `handleGetConstraintOfType` returns the constraint of a
    /// substitution type. Type parameter constraints are handled by
    /// `handleGetConstraintOfTypeParameter`.
    pub(crate) fn handle_get_constraint_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_substitution_type().subst_constraint()
        })
    }

    /// `handleGetTypeParameterOfMappedType`.
    pub(crate) fn handle_get_type_parameter_of_mapped_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_mapped_type().type_parameter()
        })
    }

    /// `handleGetConstraintTypeOfMappedType`.
    pub(crate) fn handle_get_constraint_type_of_mapped_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_mapped_type().constraint_type()
        })
    }

    /// `handleGetNameTypeOfMappedType`.
    pub(crate) fn handle_get_name_type_of_mapped_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_mapped_type().name_type()
        })
    }

    /// `handleGetTemplateTypeOfMappedType`.
    pub(crate) fn handle_get_template_type_of_mapped_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        self.resolve_type_property_of_type(ctx, params, |t| {
            t.as_mapped_type().template_type()
        })
    }

    /// `handleGetTypeParametersOfSignature`.
    pub(crate) fn handle_get_type_parameters_of_signature(
        &self,
        ctx: &core_::context::Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        self.resolve_type_array_property_of_signature(ctx, params, |s| {
            s.type_parameters()
        })
    }

    /// `handleGetParametersOfSignature`.
    pub(crate) fn handle_get_parameters_of_signature(
        &self,
        _ctx: &core_::context::Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Option<Vec<Option<SymbolResponse>>>, String> {
        self.resolve_symbol_array_property_of_signature(params, |s| s.parameters())
    }

    /// `handleGetThisParameterOfSignature`.
    pub(crate) fn handle_get_this_parameter_of_signature(
        &self,
        _ctx: &core_::context::Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Option<SymbolResponse>, String> {
        self.resolve_symbol_property_of_signature(params, |s| s.this_parameter())
    }

    /// `handleGetTargetOfSignature`.
    pub(crate) fn handle_get_target_of_signature(
        &self,
        ctx: &core_::context::Context,
        params: &GetSignaturePropertyParams,
    ) -> Result<Option<SignatureResponse>, String> {
        self.resolve_signature_property_of_signature(ctx, params, |s| s.target())
    }

    /// `handleGetImportAdderEdits`.
    pub(crate) fn handle_get_import_adder_edits(
        &self,
        ctx: &core_::context::Context,
        params: &GetImportAdderEditsParams,
    ) -> Result<Option<Vec<TextEdit>>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let project_id = params.project.clone();
        let mut working_snapshot = Arc::clone(&sd.snapshot);
        let mut program = sd.get_program(&params.project)?;
        let mut source_file = program
            .get_source_file(&params.file.to_file_name(&program.base_directory()))
            .ok_or_else(|| {
                format!("{}: source file not found: {}", ERR_CLIENT_ERROR, params.file)
            })?;
        let mut file_name = {
            let nodes = program.arena_of(source_file);
            nodes[source_file].as_source_file().file_name().clone()
        };
        let autoimport_project_id = ls::autoimport::ProjectId(Rc::from(params.project.0.as_str()));

        let needs_preparation = match working_snapshot.auto_import_registry() {
            None => true,
            Some(registry) => !registry.is_prepared_for_importing_file(
                &file_name,
                &autoimport_project_id,
                working_snapshot.user_preferences(),
            ),
        };
        if needs_preparation {
            let prepared_snapshot = self.snapshot_host.clone_snapshot_with_auto_imports(
                ctx,
                &working_snapshot,
                &lsconv::file_name_to_document_uri(&file_name),
                None,
            );
            if let Some(project_session) = &self.project_session {
                project_session
                    .try_adopt_snapshot_in_background(&working_snapshot, &prepared_snapshot);
            }
            // `defer preparedSnapshot.Deref()`.
            let _prepared_snapshot_guard = SnapshotDeref(Arc::clone(&prepared_snapshot));
            working_snapshot = prepared_snapshot;

            let Some(proj) = working_snapshot.project_collection.get_project(&project_id)
            else {
                return Err(format!(
                    "{}: project {} not found",
                    ERR_CLIENT_ERROR, project_id
                ));
            };
            program = proj.get_program().cloned().ok_or_else(|| {
                format!("{}: project has no program", ERR_CLIENT_ERROR)
            })?;
            source_file = program
                .get_source_file(&params.file.to_file_name(&program.base_directory()))
                .ok_or_else(|| {
                    format!("{}: source file not found: {}", ERR_CLIENT_ERROR, params.file)
                })?;
            file_name = {
                let nodes = program.arena_of(source_file);
                nodes[source_file].as_source_file().file_name().clone()
            };
        }

        let Some(registry) = working_snapshot.auto_import_registry() else {
            return Ok(Some(Vec::new()));
        };

        // PORT: `program.GetTypeChecker(ctx)` → the `Api`-lifetime pool
        // checkout, matching `setup_checker` — the API checker owns the
        // arena that snapshot symbol handles resolve against.
        let (ch, done) = program.get_type_checker(core_::context::with_checker_lifetime(
            ctx,
            core_::context::CheckerLifetime::Api,
        ));
        // `defer done()` — releasing the API checker is `CheckerSetup`'s
        // `Drop`, so declare it first among the imports locals to keep
        // Go's ordering (the checker outlives the adder).
        let setup = CheckerSetup {
            sd: sd.clone(),
            snapshot: params.snapshot,
            program: program.clone(),
            checker: ch.clone(),
            done: Some(done),
            project_id: project_id.clone(),
        };

        let view = ls::autoimport::View::new(
            registry,
            source_file,
            autoimport_project_id,
            program.clone(),
            &ch,
            // PORT: the port's `View::new` takes `lsutil.UserPreferences`
            // (see `get_prepared_auto_import_view`), where Go's
            // `autoimport.NewView` takes
            // `ModuleSpecifierPreferences()`.
            working_snapshot.user_preferences().clone(),
        );
        // PORT: `new_import_adder` takes `&'a Converters<'a>` — the inner
        // `'a` equals the borrow lifetime, and `Converters` has a `Drop`
        // impl, so a plain local can never satisfy dropck. `ManuallyDrop`
        // suppresses it — same pattern as `codeactions_importfixes.rs`.
        let converters = std::mem::ManuallyDrop::new(working_snapshot.converters());
        let mut import_adder = ls::autoimport::import_adder::new_import_adder(
            ctx.clone(),
            &program,
            &ch,
            source_file,
            &view,
            working_snapshot
                .get_preferences(file_name.as_string())
                .format_code_settings
                .clone(),
            &converters,
            working_snapshot.user_preferences(),
        );

        for (i, action) in params.actions.iter().enumerate() {
            if action.kind == IMPORT_ADDER_ACTION_KIND_IMPORT_SYMBOL {
                let Some(symbol_reference) = action.symbol.as_ref() else {
                    return Err(format!(
                        "{}: import adder action {} missing symbol",
                        ERR_CLIENT_ERROR, i
                    ));
                };
                let symbol = setup.resolve_symbol_handle(symbol_reference, &mut Vec::new())?;
                let is_valid_type_only_use_site =
                    action.is_valid_type_only_use_site.unwrap_or(true);
                import_adder
                    .add_import_from_exported_symbol(symbol.symbol, is_valid_type_only_use_site);
            } else {
                return Err(format!(
                    "{}: unknown import adder action kind {:?}",
                    ERR_CLIENT_ERROR,
                    action.kind.as_str()
                ));
            }
        }

        if !import_adder.has_fixes() {
            return Ok(Some(Vec::new()));
        }
        let nodes = program.arena_of(source_file);
        Ok(to_api_text_edits(&nodes, source_file, &import_adder.edits()))
    }

    // -- Property-resolution helpers (session.go:3355-3597) -------------

    /// `resolveTypePropertyOfType` resolves a type property of type
    /// `Type` and returns a type response.
    fn resolve_type_property_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
        getter: impl Fn(&checker::Type) -> Option<checker::TypeId>,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let t = setup.resolve_type_handle(params.r#type)?;
        let Some(result) = getter(&t.ptr()) else {
            return Ok(None);
        };
        let mut c = setup.checker.borrow_mut();
        let nodes = type_nodes(&setup.program, &c, result);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, result))
    }

    /// `resolveTypeArrayPropertyOfType` resolves a type property of an
    /// array of types and returns an array of type responses.
    fn resolve_type_array_property_of_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
        getter: impl Fn(&checker::Type) -> &[checker::TypeId],
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let t = setup.resolve_type_handle(params.r#type)?;
        let types: Vec<checker::TypeId> = getter(&t.ptr()).to_vec();
        if types.is_empty() {
            return Ok(None);
        }
        let mut c = setup.checker.borrow_mut();
        let results = types
            .iter()
            .map(|&sub| {
                let nodes = type_nodes(&setup.program, &c, sub);
                setup
                    .sd
                    .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, sub)
            })
            .collect();
        Ok(Some(results))
    }

    /// `resolveSymbolPropertyOfType` resolves a type property of type
    /// `Symbol` and returns a symbol response.
    ///
    /// PORT: `SignatureEntry`/`TypeEntry` do not carry a symbol arena, so
    /// the project program supplies `program.symbols` (the checker's
    /// `symbol_arena`) — Go needs no program here.
    fn resolve_symbol_property_of_type(
        &self,
        params: &GetTypePropertyParams,
        getter: impl Fn(&checker::Type) -> Option<ast::SymbolId>,
    ) -> Result<Option<SymbolResponse>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let t = sd.resolve_type_handle(&params.project, params.r#type)?;
        let Some(result) = getter(&t.ptr()) else {
            return Ok(None);
        };
        let program = sd.get_program(&params.project)?;
        let nodes = symbol_nodes(&program, &program.symbols, result);
        Ok(sd.new_symbol_response(
            (*nodes).get_mut(),
            &program.symbols,
            result,
            &params.project,
        ))
    }

    /// `resolveSymbolPropertyOfSymbol` resolves a symbol property of type
    /// `Symbol` and returns a symbol response.
    fn resolve_symbol_property_of_symbol(
        &self,
        params: &GetSymbolPropertyParams,
        getter: impl Fn(&ast::Symbol) -> Option<ast::SymbolId>,
    ) -> Result<Option<SymbolResponse>, String> {
        let resolved = self.resolve_symbol_reference(&params.symbol)?;
        let Some(result) = getter(resolved.entry.arena.get_ref(resolved.entry.symbol)) else {
            return Ok(None);
        };
        match &resolved.sd {
            None => {
                let bound = resolved
                    .bound
                    .as_ref()
                    .expect("file symbol reference without bound source file");
                Ok(Some(new_file_symbol_response(
                    (*bound.nodes).get_mut(),
                    &resolved.entry.arena,
                    result,
                )))
            }
            Some(sd) => {
                let program = sd.get_program(&resolved.canonical_project)?;
                let nodes = symbol_nodes(&program, &resolved.entry.arena, result);
                Ok(sd.new_symbol_response(
                    (*nodes).get_mut(),
                    &resolved.entry.arena,
                    result,
                    &resolved.canonical_project,
                ))
            }
        }
    }

    /// `resolveSymbolTablePropertyOfSymbol` resolves a symbol property of
    /// type `SymbolTable` and returns an array of symbol responses.
    /// Results are sorted using the checker's canonical symbol ordering
    /// so that API consumers receive a stable, deterministic order
    /// instead of randomized map iteration order.
    fn resolve_symbol_table_property_of_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &GetSymbolPropertyParams,
        getter: impl Fn(&ast::Symbol) -> Rc<ast::SymbolTable>,
    ) -> Result<Option<Vec<Option<SymbolResponse>>>, String> {
        let resolved = self.resolve_symbol_reference(&params.symbol)?;
        let symbol_table = getter(resolved.entry.arena.get_ref(resolved.entry.symbol));
        if symbol_table.is_empty() {
            return Ok(None);
        }
        if symbol_table.size() == 1 {
            let sub = *symbol_table.values().next().unwrap();
            let response = match &resolved.sd {
                None => {
                    let bound = resolved
                        .bound
                        .as_ref()
                        .expect("file symbol reference without bound source file");
                    Some(new_file_symbol_response(
                        (*bound.nodes).get_mut(),
                        &resolved.entry.arena,
                        sub,
                    ))
                }
                Some(sd) => {
                    let program = sd.get_program(&resolved.canonical_project)?;
                    let nodes = symbol_nodes(&program, &resolved.entry.arena, sub);
                    sd.new_symbol_response(
                        (*nodes).get_mut(),
                        &resolved.entry.arena,
                        sub,
                        &resolved.canonical_project,
                    )
                }
            };
            return Ok(Some(vec![response]));
        }

        let mut symbols: Vec<ast::SymbolId> = symbol_table.values().copied().collect();
        match &resolved.sd {
            None => {
                // Binder tables of a file-owned symbol only contain
                // symbols from the same file, so they can be ordered by
                // declaration position without a checker.
                let bound = resolved
                    .bound
                    .as_ref()
                    .expect("file symbol reference without bound source file")
                    .clone();
                let nodes = bound.nodes.as_slice();
                let arena = &resolved.entry.arena;
                symbols.sort_by(|&left, &right| {
                    debug_assert_eq!(
                        get_source_file_of_symbol(nodes, arena, left),
                        Some(bound.file)
                    );
                    debug_assert_eq!(
                        get_source_file_of_symbol(nodes, arena, right),
                        Some(bound.file)
                    );
                    let l = arena.get_ref(left);
                    let r = arena.get_ref(right);
                    let left_has_declaration = !l.declarations.is_empty();
                    let right_has_declaration = !r.declarations.is_empty();
                    if left_has_declaration != right_has_declaration {
                        return if left_has_declaration {
                            Ordering::Less
                        } else {
                            Ordering::Greater
                        };
                    }
                    if left_has_declaration {
                        let order = nodes[l.declarations[0]]
                            .pos()
                            .cmp(&nodes[r.declarations[0]].pos());
                        if order != Ordering::Equal {
                            return order;
                        }
                    }
                    let order = l.name.as_ref().cmp(r.name.as_ref());
                    if order != Ordering::Equal {
                        return order;
                    }
                    symbol_handle(arena.get(left))
                        .0
                        .cmp(&symbol_handle(arena.get(right)).0)
                });
                let results = symbols
                    .iter()
                    .map(|&sub| {
                        Some(new_file_symbol_response(
                            (*bound.nodes).get_mut(),
                            arena,
                            sub,
                        ))
                    })
                    .collect();
                Ok(Some(results))
            }
            Some(_) => {
                // Tables of snapshot-owned symbols may contain symbols
                // from several files, so they use the checker's ordering.
                let setup = self.setup_checker(
                    ctx,
                    params.symbol.owner.snapshot,
                    &params.symbol.owner.project,
                )?;
                {
                    let c = setup.checker.borrow();
                    symbols.sort_by(|&left, &right| {
                        c.compare_symbols(left, right).cmp(&0)
                    });
                }
                let results = symbols
                    .iter()
                    .map(|&sub| {
                        let nodes =
                            symbol_nodes(&setup.program, &resolved.entry.arena, sub);
                        setup.new_symbol_response(
                            (*nodes).get_mut(),
                            &resolved.entry.arena,
                            sub,
                        )
                    })
                    .collect();
                Ok(Some(results))
            }
        }
    }

    /// `resolveSymbolArrayPropertyOfSignature` resolves a signature
    /// property of an array of symbols and returns an array of symbol
    /// responses.
    fn resolve_symbol_array_property_of_signature(
        &self,
        params: &GetSignaturePropertyParams,
        getter: impl Fn(&checker::Signature) -> &[ast::SymbolId],
    ) -> Result<Option<Vec<Option<SymbolResponse>>>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let sig = sd.resolve_signature_handle(&params.project, params.signature)?;
        let symbols: Vec<ast::SymbolId> = getter(sig.get()).to_vec();
        if symbols.is_empty() {
            return Ok(None);
        }
        let program = sd.get_program(&params.project)?;
        let results = symbols
            .iter()
            .map(|&sym| {
                let nodes = symbol_nodes(&program, &program.symbols, sym);
                sd.new_symbol_response((*nodes).get_mut(), &program.symbols, sym, &params.project)
            })
            .collect();
        Ok(Some(results))
    }

    /// `resolveSymbolPropertyOfSignature` resolves a signature property
    /// of type `Symbol` and returns a symbol response.
    fn resolve_symbol_property_of_signature(
        &self,
        params: &GetSignaturePropertyParams,
        getter: impl Fn(&checker::Signature) -> Option<ast::SymbolId>,
    ) -> Result<Option<SymbolResponse>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let sig = sd.resolve_signature_handle(&params.project, params.signature)?;
        let Some(result) = getter(sig.get()) else {
            return Ok(None);
        };
        let program = sd.get_program(&params.project)?;
        let nodes = symbol_nodes(&program, &program.symbols, result);
        Ok(sd.new_symbol_response(
            (*nodes).get_mut(),
            &program.symbols,
            result,
            &params.project,
        ))
    }

    /// `resolveTypeArrayPropertyOfSignature`.
    fn resolve_type_array_property_of_signature(
        &self,
        ctx: &core_::context::Context,
        params: &GetSignaturePropertyParams,
        getter: impl Fn(&checker::Signature) -> &[checker::TypeId],
    ) -> Result<Option<Vec<Option<TypeResponse>>>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let sig = setup.resolve_signature_handle(params.signature)?;
        let types: Vec<checker::TypeId> = getter(sig.get()).to_vec();
        if types.is_empty() {
            return Ok(None);
        }
        let mut c = setup.checker.borrow_mut();
        let results = types
            .iter()
            .map(|&sub| {
                let nodes = type_nodes(&setup.program, &c, sub);
                setup
                    .sd
                    .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, sub)
            })
            .collect();
        Ok(Some(results))
    }

    /// `resolveSignaturePropertyOfSignature`.
    ///
    /// PORT: Go runs this without a checker (`sd` +
    /// `resolveSignatureHandle` only); the port's
    /// `SnapshotData::new_signature_response` needs `&Checker` for
    /// `signature_arena`/`types`/`symbol_arena`, so it goes through
    /// `setup_checker`. The API checker owns the signature's arena, so
    /// registration produces the same registry entry.
    fn resolve_signature_property_of_signature(
        &self,
        ctx: &core_::context::Context,
        params: &GetSignaturePropertyParams,
        getter: impl Fn(&checker::Signature) -> Option<checker::SignatureId>,
    ) -> Result<Option<SignatureResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;
        let sig = setup.resolve_signature_handle(params.signature)?;
        let Some(result) = getter(sig.get()) else {
            return Ok(None);
        };
        let c = setup.checker.borrow();
        let nodes = signature_nodes(&setup.program, &c, result);
        Ok(setup.new_signature_response((*nodes).get_mut(), &c, result))
    }
}
