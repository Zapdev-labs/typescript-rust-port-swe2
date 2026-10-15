// Ported from tsc/internal/api/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Checker type/symbol queries through `handleGetTypeOfSymbolAtLocation`,
// node serialization (`typeToTypeNode`, `signatureToSignatureDeclaration`,
// `typeToString`), `printNode`, the `emit` family, and
// `formatNodeForInsertion`.
//
// PORT notes:
// - Go's nil `*ast.Type`/`*ast.Symbol`/`*ast.Node` returns become
//   `Option`s; `TypeId::NONE`/`SymbolId::is_none()` are the nil stand-ins
//   the registries already use.
// - `symbolOwnerFile`/`nodeHandleFrom` dereference `nodes` by
//   `NodeId::local_index`, which only resolves inside the owning file's
//   per-file arena (Go reads the live `*ast.SourceFile` heap pointer). The
//   `*_response_nodes` helpers pick the arena of the symbol's (or type's
//   symbol's) first declaration; types whose auxiliary symbols
//   (`alias_symbol`, tuple labeled-element declarations) live in other
//   files still resolve through the primary declaration's arena — Go's
//   shared heap had no such constraint.
// - `EmitOptions::write_file` captures `Rc<RefCell<..>>` state instead of
//   Go's `sync.Mutex` — emit runs on one thread here (the compiler's own
//   emit path makes the same assumption).
// - `base64.StdEncoding` has no crate dependency in this workspace (the
//   tsc-sourcemap port keeps its own private copy); a minimal decoder is
//   ported locally and `ipc::base64_std_encode` covers the encode side.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_apiencoder as encoder;
use tsc_ast as ast;
use tsc_checker::checker_core::Checker;
use tsc_checker::types as checker;
use tsc_compiler as compiler;
use tsc_core as core_;
use tsc_format as format;
use tsc_ipc as ipc;
use tsc_nodebuilder as nodebuilder;
use tsc_printer as printer;
use tsc_project as project;
use tsc_tspath as tspath;

use crate::proto::*;
use crate::session::*;

/// The node arena `symbolOwnerFile`/`nodeHandleFrom` dereference for a
/// `newTypeResponse` call: they index `nodes` by `NodeId::local_index`,
/// which only resolves inside the arena containing the type's symbol's
/// declarations. Uses the type's `symbol` (then `alias.symbol`) first
/// declaration; falls back to any registered program arena when there is
/// no declaration to locate — in that case the `nodes` reads inside
/// `new_type_response` are unreachable (`symbolOwnerFile` returns `None`
/// and no node handles are built).
///
/// PORT: Go walks `symbol.Declarations[0]` to its `*ast.SourceFile` on the
/// shared heap, so cross-file auxiliary symbols work transparently; here a
/// single arena can only describe one file.
fn type_response_nodes(
    program: &compiler::program::Program,
    c: &Checker,
    ty: checker::TypeId,
) -> Rc<ast::NodeArenaBuf> {
    let declaration = if !ty.is_none() {
        let t = c.types.get(ty);
        t.symbol
            .or_else(|| t.alias.as_ref().and_then(|a| a.symbol))
            .and_then(|symbol| {
                let s = c.symbol_arena.get_ref(symbol);
                s.declarations.first().copied().or(s.value_declaration)
            })
    } else {
        None
    };
    match declaration {
        Some(d) => program.arena_of(d),
        None => program.nodes_handle_or_fallback(0).1.snapshot(),
    }
}

/// `type_response_nodes` for a `newSymbolResponse` call — the arena of the
/// symbol's first declaration.
fn symbol_response_nodes(
    program: &compiler::program::Program,
    arena: &ast::SymbolArena,
    symbol: ast::SymbolId,
) -> Rc<ast::NodeArenaBuf> {
    let declaration = if !symbol.is_none() {
        let s = arena.get_ref(symbol);
        s.declarations.first().copied().or(s.value_declaration)
    } else {
        None
    };
    match declaration {
        Some(d) => program.arena_of(d),
        None => program.nodes_handle_or_fallback(0).1.snapshot(),
    }
}

/// Go's `ast.Kind(params.Kind)` — an unchecked `int32`→`Kind` cast.
/// `Kind` is `#[repr(i16)]` over contiguous ordinals `0..Kind::COUNT`
/// (mirroring Go's iota block); out-of-range input maps to
/// `Kind::Unknown`, the decoder's stance for unknown kinds, rather than
/// producing an invalid discriminant.
#[allow(unsafe_code)]
fn kind_from_i32(kind: i32) -> ast::Kind {
    if (0..ast::Kind::COUNT as i32).contains(&kind) {
        // SAFETY: every ordinal in `0..Kind::COUNT` is a declared `Kind`
        // discriminant.
        unsafe { std::mem::transmute::<i16, ast::Kind>(kind as i16) }
    } else {
        ast::Kind::Unknown
    }
}

/// `base64.StdEncoding.DecodeString` — local port of Go's std decoder.
/// Like Go, '\r' and '\n' are skipped anywhere in the input and padding
/// is only legal in the final quartet.
fn base64_std_decode(s: &str) -> Result<Vec<u8>, String> {
    const ALPHABET: &[u8; 64] =
        b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    fn decode_char(c: u8) -> Result<u8, String> {
        match c {
            b'A'..=b'Z' => Ok(c - b'A'),
            b'a'..=b'z' => Ok(c - b'a' + 26),
            b'0'..=b'9' => Ok(c - b'0' + 52),
            b'+' => Ok(62),
            b'/' => Ok(63),
            _ => Err("illegal base64 data".to_string()),
        }
    }
    let filtered: Vec<u8> = s.bytes().filter(|&b| !matches!(b, b'\r' | b'\n')).collect();
    if filtered.len() % 4 != 0 {
        return Err("illegal base64 data".to_string());
    }
    let n_chunks = filtered.len() / 4;
    let mut out = Vec::with_capacity(n_chunks * 3);
    for (i, chunk) in filtered.chunks(4).enumerate() {
        let is_last = i + 1 == n_chunks;
        let mut vals = [0u8; 4];
        let mut pad = 0;
        for (j, &c) in chunk.iter().enumerate() {
            if c == b'=' {
                if !is_last || j < 2 || pad > 1 {
                    return Err("illegal base64 data".to_string());
                }
                pad += 1;
            } else {
                if pad > 0 {
                    return Err("illegal base64 data".to_string());
                }
                vals[j] = decode_char(c)?;
            }
        }
        out.push((vals[0] << 2) | (vals[1] >> 4));
        if pad < 2 {
            out.push((vals[1] << 4) | (vals[2] >> 2));
        }
        if pad < 1 {
            out.push((vals[2] << 6) | vals[3]);
        }
    }
    Ok(out)
}

/// `decodePrintNode` — decodes base64 + binary-encoded AST data into a
/// `(node, arena)` pair. PORT: Go returns a `*ast.Node` on the shared
/// heap; the decoder mints a fresh `Vec<Node>` arena the caller owns.
fn decode_print_node(encoded: &str) -> Result<(ast::NodeId, Vec<ast::Node>), String> {
    let data = base64_std_decode(encoded)
        .map_err(|e| format!("{}: invalid base64 data: {}", ERR_CLIENT_ERROR, e))?;
    encoder::decode_nodes(&data)
        .map_err(|e| format!("{}: failed to decode AST: {}", ERR_CLIENT_ERROR, e))
}

/// `emitProgram` — `Program::emit` always returns a value in the port;
/// Go's nil-result/`ctx.Err()` branches have no counterpart (emit already
/// early-returns a default `EmitResult` when the context is cancelled).
fn emit_program(
    ctx: &core_::context::Context,
    program: &compiler::program::Program,
    options: &mut compiler::emit_host::EmitOptions<'_>,
) -> Result<compiler::emit_host::EmitResult, String> {
    Ok(program.emit(ctx.clone(), options))
}

/// `nonNilDiagnostics` — always a non-empty `Vec` (serializes `[]`).
///
/// PORT: `newDiagnosticResponse` resolves each diagnostic's
/// `DiagnosticFile.node` through `nodes`, which is a single per-file
/// arena; emit diagnostics may reference different files, so the arena is
/// resolved per diagnostic. Related-information / message-chain
/// diagnostics in other files still resolve through the primary file's
/// arena — a divergence inherent in the single-`nodes` signature.
fn non_nil_diagnostics(
    program: &compiler::program::Program,
    diags: &[ast::diagnostic::DiagnosticRef],
) -> Vec<DiagnosticResponse> {
    diags.iter()
        .map(|d| {
            let file = ast::diagnostic::lock_diagnostic(d)
                .file()
                .and_then(|f| f.node);
            match file {
                Some(file) => {
                    let nodes = program.arena_of(file);
                    new_diagnostic_response(d.clone(), &nodes)
                }
                // The diagnostic has no file; `nodes` is never
                // dereferenced for file-less diagnostics.
                None => new_diagnostic_response(d.clone(), &[]),
            }
        })
        .collect()
}

/// `emitToOutput` — emits with a `WriteFile` collector and returns the
/// outputs sorted by file name.
fn emit_to_output(
    ctx: &core_::context::Context,
    program: &Rc<compiler::program::Program>,
    mut options: compiler::emit_host::EmitOptions<'_>,
) -> Result<EmitOutputResponse, String> {
    let output_files: Rc<RefCell<Vec<EmitOutputFile>>> = Rc::new(RefCell::new(Vec::new()));
    {
        let output_files = output_files.clone();
        let program = program.clone();
        options.write_file = Some(Box::new(move |file_name, text, data| {
            let source_file_name = data.source_file.map(|sf| {
                program.arena_of(sf)[sf].as_source_file().file_name().clone()
            });
            output_files.borrow_mut().push(EmitOutputFile {
                file_name: file_name.clone(),
                text: text.to_string(),
                source_file_name,
            });
            Ok(())
        }));
    }

    let result = emit_program(ctx, program, &mut options)?;
    let mut output_files = output_files.borrow_mut();
    output_files.sort_by(|a, b| a.file_name.compare(&b.file_name).cmp(&0));
    Ok(EmitOutputResponse {
        emit_skipped: result.emit_skipped,
        diagnostics: non_nil_diagnostics(program, &result.diagnostics),
        output_files: std::mem::take(&mut output_files),
    })
}

/// `getEmitOnly` — `nil`/`0` → `EmitAll`, `1` → `EmitOnlyJs`,
/// `2` → `EmitOnlyDts`; anything larger is a client error (mirrors
/// `*value > uint32(compiler.EmitOnlyDts)`).
fn get_emit_only(value: Option<u32>) -> Result<compiler::emit_host::EmitOnly, String> {
    match value {
        None | Some(0) => Ok(compiler::emit_host::EmitOnly::All),
        Some(1) => Ok(compiler::emit_host::EmitOnly::Js),
        Some(2) => Ok(compiler::emit_host::EmitOnly::Dts),
        Some(v) => Err(format!(
            "{}: invalid emitOnly value: {}",
            ERR_CLIENT_ERROR, v
        )),
    }
}

impl Session {
    /// `handleGetContextualType` returns the contextual type for a node.
    pub(crate) fn handle_get_contextual_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetContextualTypeParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup.sd.resolve_node_handle(&setup.program, &params.location)?;
        // Go's `if node == nil` guard is unreachable — `resolveNodeHandle`
        // either returns a node or an error.

        let mut c = setup.checker.borrow_mut();
        let Some(t) = c.get_contextual_type_api(node, checker::ContextFlags::NONE) else {
            return Ok(None);
        };
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleGetContextualTypeForArgument` returns the contextual type
    /// for the argument at `params.index`.
    pub(crate) fn handle_get_contextual_type_for_argument(
        &self,
        ctx: &core_::context::Context,
        params: &GetContextualTypeForArgumentParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup.sd.resolve_node_handle(&setup.program, &params.location)?;

        let mut c = setup.checker.borrow_mut();
        let Some(t) = c.get_contextual_type_for_argument_at_index(node, params.index) else {
            return Ok(None);
        };
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleGetAwaitedType` returns the awaited type of a type.
    pub(crate) fn handle_get_awaited_type(
        &self,
        ctx: &core_::context::Context,
        params: &CheckerTypeParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let mut c = setup.checker.borrow_mut();
        let Some(t) = c.get_awaited_type(t.ty) else {
            return Ok(None);
        };
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleGetBaseTypeOfLiteralType` returns the base type of a literal
    /// type (e.g. number for 42).
    pub(crate) fn handle_get_base_type_of_literal_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetBaseTypeOfLiteralTypeParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let mut c = setup.checker.borrow_mut();
        let t = c.get_base_type_of_literal_type(t.ty);
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleGetNonNullableType` returns the type with null and
    /// undefined removed.
    pub(crate) fn handle_get_non_nullable_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypePropertyParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let mut c = setup.checker.borrow_mut();
        let t = c.get_non_nullable_type(t.ty);
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleGetTypeFromTypeNode` returns the type for a type node.
    pub(crate) fn handle_get_type_from_type_node(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypeFromTypeNodeParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup.sd.resolve_node_handle(&setup.program, &params.location)?;

        let mut c = setup.checker.borrow_mut();
        let t = c.get_type_from_type_node(node);
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleGetWidenedType` returns the widened type.
    pub(crate) fn handle_get_widened_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetWidenedTypeParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let mut c = setup.checker.borrow_mut();
        let t = c.get_widened_type(t.ty);
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleGetParameterType` returns the type of a parameter at a
    /// given index in a signature.
    pub(crate) fn handle_get_parameter_type(
        &self,
        ctx: &core_::context::Context,
        params: &GetParameterTypeParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let sig = setup.resolve_signature_handle(params.signature)?;

        if params.index < 0 {
            return Err(format!("{}: invalid parameter index", ERR_CLIENT_ERROR));
        }

        let mut c = setup.checker.borrow_mut();
        let t = c.get_type_at_position(sig.signature, params.index as usize);
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleGetTypeParameterAtPosition` returns the type parameter at a
    /// given index in a signature.
    pub(crate) fn handle_get_type_parameter_at_position(
        &self,
        ctx: &core_::context::Context,
        params: &GetParameterTypeParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let sig = setup.resolve_signature_handle(params.signature)?;

        if params.index < 0 {
            return Err(format!("{}: invalid parameter index", ERR_CLIENT_ERROR));
        }

        let mut c = setup.checker.borrow_mut();
        let t = c.get_type_parameter_at_position(sig.signature, params.index as usize);
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleIsArrayLikeType` returns whether a type is array-like.
    pub(crate) fn handle_is_array_like_type(
        &self,
        ctx: &core_::context::Context,
        params: &IsArrayLikeTypeParams,
    ) -> Result<bool, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        Ok(setup.checker.borrow_mut().is_array_like_type(t.ty))
    }

    /// `handleIsTypeAssignableTo` returns whether source is assignable to
    /// target.
    pub(crate) fn handle_is_type_assignable_to(
        &self,
        ctx: &core_::context::Context,
        params: &IsTypeAssignableToParams,
    ) -> Result<bool, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let source = setup.resolve_type_handle(params.source)?;
        let target = setup.resolve_type_handle(params.target)?;

        Ok(setup
            .checker
            .borrow_mut()
            .is_type_assignable_to(source.ty, target.ty))
    }

    /// `handleGetShorthandAssignmentValueSymbol` returns the value symbol
    /// of a shorthand property assignment.
    pub(crate) fn handle_get_shorthand_assignment_value_symbol(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypeAtLocationParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let node = setup.sd.resolve_node_handle(&setup.program, &params.location)?;

        let mut c = setup.checker.borrow_mut();
        let Some(symbol) = c.get_shorthand_assignment_value_symbol(Some(node)) else {
            return Ok(None);
        };
        let nodes = symbol_response_nodes(&setup.program, &c.symbol_arena, symbol);
        Ok(setup.new_symbol_response((*nodes).get_mut(), &c.symbol_arena, symbol))
    }

    /// `handleGetTypeOfSymbolAtLocation` returns the narrowed type of a
    /// symbol at a specific location.
    pub(crate) fn handle_get_type_of_symbol_at_location(
        &self,
        ctx: &core_::context::Context,
        params: &GetTypeOfSymbolAtLocationParams,
    ) -> Result<Option<TypeResponse>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        // The port's `resolve_symbol_handle` takes an unused `nodes`
        // scratch arena (Go's signature has no such parameter).
        let symbol = setup.resolve_symbol_handle(&params.symbol, &mut Vec::new())?;

        let node = setup.sd.resolve_node_handle(&setup.program, &params.location)?;

        let mut c = setup.checker.borrow_mut();
        let t = c.get_type_of_symbol_at_location(symbol.symbol, Some(node));
        let nodes = type_response_nodes(&setup.program, &c, t);
        Ok(setup
            .sd
            .new_type_response((*nodes).get_mut(), &mut c, &setup.project_id, t))
    }

    /// `handleTypeToTypeNode` converts a Type to a TypeNode AST and
    /// returns it as binary-encoded data.
    pub(crate) fn handle_type_to_type_node(
        &self,
        ctx: &core_::context::Context,
        params: &TypeToTypeNodeParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        // Go: `if params.Location != ""` — `resolve_location` resolves a
        // non-empty handle and returns `None` for an empty one.
        let enclosing_declaration =
            setup.resolve_location(&params.location, None, None)?;

        let Some(type_node) = setup.checker.borrow_mut().type_to_type_node(
            t.ty,
            enclosing_declaration,
            nodebuilder::Flags(params.flags as u32),
            Default::default(), // Go's nil `idToSymbol` map
        ) else {
            return Ok(None);
        };

        // PORT: `encoder.EncodeNode` cannot fail in the port (it returns
        // `(data, table)`, not an error), so Go's error branch is dropped.
        let nodes = setup.program.arena_of(type_node);
        let (data, _) = encoder::encode_node((*nodes).get_mut(), type_node, None);

        if self.use_binary_responses() {
            return Ok(Some(ipc::ResponsePayload::Binary(data)));
        }
        let value = ipc::marshal_params(&SourceFileResponse {
            data: ipc::base64_std_encode(&data),
        })
        .map_err(|e| e.to_string())?;
        Ok(Some(ipc::ResponsePayload::Json(value)))
    }

    /// `handleSignatureToSignatureDeclaration` converts a Signature to a
    /// signature declaration AST and returns it as binary-encoded data.
    pub(crate) fn handle_signature_to_signature_declaration(
        &self,
        ctx: &core_::context::Context,
        params: &SignatureToSignatureDeclarationParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let sig = setup.resolve_signature_handle(params.signature)?;

        let enclosing_declaration =
            setup.resolve_location(&params.location, None, None)?;

        let Some(node) = setup
            .checker
            .borrow_mut()
            .signature_to_signature_declaration(
                sig.signature,
                kind_from_i32(params.kind),
                enclosing_declaration,
                nodebuilder::Flags(params.flags as u32),
            )
        else {
            return Ok(None);
        };

        // PORT: `encoder.EncodeNode` cannot fail in the port (it returns
        // `(data, table)`, not an error), so Go's error branch is dropped.
        let nodes = setup.program.arena_of(node);
        let (data, _) = encoder::encode_node((*nodes).get_mut(), node, None);

        if self.use_binary_responses() {
            return Ok(Some(ipc::ResponsePayload::Binary(data)));
        }
        let value = ipc::marshal_params(&SourceFileResponse {
            data: ipc::base64_std_encode(&data),
        })
        .map_err(|e| e.to_string())?;
        Ok(Some(ipc::ResponsePayload::Json(value)))
    }

    /// `handleTypeToString` converts a Type to its string representation.
    /// Go returns the bare string as `any` — marshaled as a JSON string.
    pub(crate) fn handle_type_to_string(
        &self,
        ctx: &core_::context::Context,
        params: &TypeToTypeNodeParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let setup = self.setup_checker(ctx, params.snapshot, &params.project)?;

        let t = setup.resolve_type_handle(params.r#type)?;

        let enclosing_declaration =
            setup.resolve_location(&params.location, None, None)?;

        let text = if params.flags != 0 {
            setup.checker.borrow_mut().type_to_string_ex(
                t.ty,
                enclosing_declaration,
                checker::TypeFormatFlags(params.flags as u32),
                None,
            )
        } else {
            setup.checker.borrow_mut().type_to_string_ex(
                t.ty,
                enclosing_declaration,
                checker::TypeFormatFlags::ALLOW_UNIQUE_ES_SYMBOL_TYPE
                    | checker::TypeFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE,
                None,
            )
        };

        let value = ipc::marshal_params(&text).map_err(|e| e.to_string())?;
        Ok(Some(ipc::ResponsePayload::Json(value)))
    }

    /// `handlePrintNode` decodes a binary-encoded AST node and prints it
    /// to text.
    pub(crate) fn handle_print_node(
        &self,
        _ctx: &core_::context::Context,
        params: &PrintNodeParams,
    ) -> Result<String, String> {
        let (node, mut nodes) = decode_print_node(&params.data)?;

        // `ast.IsSourceFile(node)` — the decoded root doubles as the
        // `sourceFile` argument when it is one.
        let source_file = (nodes[node].kind == ast::Kind::SourceFile).then_some(node);

        // `newPrinter(params)` — `PrinterOptions` + empty `PrintHandlers`;
        // Go's nil `emitContext` becomes a fresh `EmitContext`.
        let mut emit_context = printer::EmitContext::new();
        let symbols = ast::SymbolArena::default();
        let mut p = printer::Printer::new(
            printer::PrinterOptions {
                preserve_source_newlines: params.preserve_source_newlines,
                never_ascii_escape: params.never_ascii_escape,
                terminate_unterminated_literals: params.terminate_unterminated_literals,
                ..Default::default()
            },
            printer::PrintHandlers::default(),
            &mut emit_context,
            &mut nodes,
            &symbols,
        );
        Ok(p.emit(Some(node), source_file))
    }

    /// `handleEmit` runs a full emit, collecting outputs when the
    /// snapshot's file system is a full file system and writing through
    /// to the snapshot host's FS otherwise.
    pub(crate) fn handle_emit(
        &self,
        ctx: &core_::context::Context,
        params: &EmitParams,
    ) -> Result<EmitResponse, String> {
        let (program, mut options) = self.get_emit_options(params)?;

        let sd = self.get_snapshot_data(params.snapshot)?;
        let output_files: Option<Rc<RefCell<FxHashMap<tspath::RootedFilePath, String>>>>;
        if crate::requestfilesystem::has_full_file_system(&sd.file_system) {
            let files = Rc::new(RefCell::new(FxHashMap::default()));
            output_files = Some(files.clone());
            options.write_file = Some(Box::new(move |file_name, text, _data| {
                files.borrow_mut().insert(file_name.clone(), text.to_string());
                Ok(())
            }));
        } else {
            output_files = None;
            // `s.snapshotHost.FS().WriteFile` — write through to the
            // host's real file system.
            let fs = self.snapshot_host.fs().clone();
            options.write_file = Some(Box::new(move |file_name, text, _data| {
                fs.write_file(file_name, text).map_err(|e| e.to_string())
            }));
        }

        let compiler::emit_host::EmitResult {
            emit_skipped,
            diagnostics,
            emitted_files,
            ..
        } = emit_program(ctx, &program, &mut options)?;

        // `emittedFilesContents` is parallel to `emitted_files` only when
        // outputs were collected (full file system); write-through emits
        // leave it empty.
        let mut emitted_files_contents = Vec::new();
        if let Some(output_files) = &output_files {
            let output_files = output_files.borrow();
            emitted_files_contents = emitted_files
                .iter()
                .map(|file_name| output_files.get(file_name).cloned().unwrap_or_default())
                .collect();
        }

        Ok(EmitResponse {
            emit_skipped,
            diagnostics: non_nil_diagnostics(&program, &diagnostics),
            emitted_files,
            emitted_files_contents,
        })
    }

    /// `handleEmitToString` emits and returns the outputs instead of
    /// writing them.
    pub(crate) fn handle_emit_to_string(
        &self,
        ctx: &core_::context::Context,
        params: &EmitParams,
    ) -> Result<EmitOutputResponse, String> {
        let (program, options) = self.get_emit_options(params)?;
        emit_to_output(ctx, &program, options)
    }

    /// `handleSelectedFilesEmit` emits only the requested files
    /// (`emitOnly` selects JS-only or declaration-only output).
    pub(crate) fn handle_selected_files_emit(
        &self,
        ctx: &core_::context::Context,
        params: &SelectedFilesEmitParams,
        emit_only: compiler::emit_host::EmitOnly,
    ) -> Result<EmitOutputResponse, String> {
        let program = self.get_emit_program(params.snapshot, &params.project)?;

        // PORT: Go checks `params.Files == nil`; serde cannot distinguish
        // an omitted field from `[]`, so an empty list errors here too.
        if params.files.is_empty() {
            return Err(format!("{}: files is required", ERR_CLIENT_ERROR));
        }
        let mut target_source_files = Vec::with_capacity(params.files.len());
        for file in &params.files {
            let source_file = self.resolve_source_file(&program, file)?;
            target_source_files.push(source_file);
        }
        emit_to_output(
            ctx,
            &program,
            compiler::emit_host::EmitOptions {
                target_source_files: Some(target_source_files),
                emit_only,
                force_emit: true,
                ..Default::default()
            },
        )
    }

    /// `getEmitOptions` resolves the program and builds `EmitOptions`
    /// from `params.emit_only`.
    fn get_emit_options(
        &self,
        params: &EmitParams,
    ) -> Result<
        (
            Rc<compiler::program::Program>,
            compiler::emit_host::EmitOptions<'static>,
        ),
        String,
    > {
        let program = self.get_emit_program(params.snapshot, &params.project)?;
        let emit_only = get_emit_only(params.emit_only)?;
        Ok((
            program,
            compiler::emit_host::EmitOptions {
                emit_only,
                ..Default::default()
            },
        ))
    }

    /// `getEmitProgram` resolves a program for emit (no checker).
    pub(crate) fn get_emit_program(
        &self,
        snapshot: SnapshotId,
        project_handle: &project::project::Id,
    ) -> Result<Rc<compiler::program::Program>, String> {
        let sd = self.get_snapshot_data(snapshot)?;
        sd.get_program(project_handle)
    }

    /// `resolveOptionalSourceFile` resolves a `DocumentIdentifier` to a
    /// source file in the program. Go returns `nil, nil` for a nil file;
    /// the callers here always pass a real identifier, so the port
    /// returns the file or a client error.


    /// `handleFormatNodeForInsertion` formats a synthesized node with the
    /// correct indentation for insertion at a specific position in an
    /// existing file.
    pub(crate) fn handle_format_node_for_insertion(
        &self,
        ctx: &core_::context::Context,
        params: &FormatNodeForInsertionParams,
    ) -> Result<String, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;

        let program = sd.get_program(&params.project)?;

        let target_source_file = self.resolve_source_file(&program, &params.file)?;

        let data = base64_std_decode(&params.data)
            .map_err(|e| format!("{}: invalid base64 data: {}", ERR_CLIENT_ERROR, e))?;

        let (node, mut nodes) = encoder::decode_nodes(&data)
            .map_err(|e| format!("{}: failed to decode AST: {}", ERR_CLIENT_ERROR, e))?;

        let target_nodes = program.arena_of(target_source_file);
        let pos = target_nodes[target_source_file]
            .as_source_file()
            .position_map()
            .utf16_to_utf8(params.position as usize) as i32;
        let parse_options = target_nodes[target_source_file]
            .as_source_file()
            .parse_options()
            .clone();
        // `targetSourceFile.LanguageVariant` — the synthetic file's
        // formatting runs under the target file's variant.
        let language_variant = target_nodes[target_source_file]
            .as_source_file()
            .language_variant;

        let format_options = sd.snapshot.user_preferences().format_code_settings.clone();
        let new_line = format_options.editor_settings.new_line_character.clone();

        let mut factory = ast::NodeFactory::new(ast::NodeFactoryHooks::default());
        let mut emit_context = printer::EmitContext::new();
        let (text, node_with_pos) = printer::print_and_position_node(
            &mut nodes,
            &mut factory,
            node,
            None,
            new_line.as_str(),
            format_options.editor_settings.indent_size,
            &mut emit_context,
        );
        let synthetic_file = printer::create_synthetic_source_file(
            &mut nodes,
            &mut factory,
            node_with_pos,
            &text,
            &parse_options,
        );

        let is_at_line_start = format::get_line_start_position_for_position(
            pos,
            target_source_file,
            &target_nodes,
        ) == pos;
        let initial_indentation = format::get_indentation(
            pos,
            target_source_file,
            &format_options,
            is_at_line_start,
            (*target_nodes).get_mut(),
        );

        let mut delta = 0;
        if format_options.editor_settings.indent_size != 0
            && format::should_indent_child_node(
                &format_options,
                node,
                None,
                None,
                false,
                &mut nodes,
            )
        {
            delta = format_options.editor_settings.indent_size;
        }

        let ctx = format::with_format_code_settings(ctx, format_options, &new_line);
        let changes = format::format_node_given_indentation(
            &ctx,
            node_with_pos,
            synthetic_file,
            language_variant,
            initial_indentation,
            delta,
            &mut nodes,
        );

        Ok(core_::textchange::apply_bulk_edits(&text, &changes))
    }
}
