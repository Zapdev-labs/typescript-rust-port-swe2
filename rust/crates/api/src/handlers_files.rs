// Ported from tsc/internal/api/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Handlers for command-line/config parsing, transpilation, and the
// source-file lease surface (create/retain/get/release/cached) —
// Go lines ~1990-2456 (`handleParseCommandLine` … `encodeSourceFileResponse`).
//
// PORT notes:
// - `*ast.SourceFile` leases are `ParsedSourceFile` pairs
//   (`{nodes: Rc<NodeArenaBuf>, file: NodeId}`) under the snapshot host's
//   parse cache; the encoder takes `&mut Vec<Node>` via
//   `(*parsed.nodes).get_mut()` — `Rc::get_mut` would shadow the arena
//   method, so the deref is explicit everywhere.
// - `encoder::encode_source_file` is infallible in Rust (it returns
//   `(Vec<u8>, NodeIndexTable)`); Go's `failed to encode source file`
//   error paths have no Rust equivalent.
// - Go's `any` returns are `Result<Option<ipc::ResponsePayload>, String>`:
//   `RawBinary(data)` → `Binary`, nil → `None`, and non-binary results are
//   marshaled to `Json` here (`SourceFileResponse` base64 wrappers).
// - A `DiagnosticFile.node` is a `NodeId` into the arena that minted it;
//   config/transpile diagnostics can reference arenas that are unreachable
//   here (dropped transient parses, per-file arenas the caller does not
//   hold). `strip_foreign_diagnostic_nodes` clears every `node` handle
//   that does not index the `keep` arena — the response then renders from
//   the `DiagnosticFile` snapshot, identical output for the
//   non-content-mapped files these handlers produce (same convention as
//   `strip_diagnostic_nodes` in handlers_lifecycle.rs, generalized with
//   the `keep` escape).

use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::Ordering;

use tsc_apiencoder as encoder;
use tsc_ast as ast;
use tsc_ast::diagnostic::DiagnosticRef;
use tsc_core as core_;
use tsc_ipc as ipc;
use tsc_project as project;
use tsc_transpile as transpile;
use tsc_tsoptions as tsoptions;
use tsc_tspath as tspath;

use crate::proto::*;
use crate::session::*;

impl crate::session::Session {
    /// `s.handleParseCommandLine`.
    pub(crate) fn handle_parse_command_line(
        &self,
        _ctx: &core_::context::Context,
        params: &ParseCommandLineParams,
    ) -> Result<Option<ConfigFileResponse>, String> {
        let parsed_command_line = tsoptions::commandlineparser::parse_command_line(
            &params.command_line,
            &self.snapshot_host.fs,
            self.current_directory(),
        );
        // Command-line diagnostics are file-less, so the empty arena is
        // the Go `nil`-free equivalent — see `new_config_file_response`.
        Ok(new_config_file_response(Some(&parsed_command_line), &[]))
    }

    /// `s.handleReadConfigFile` reads and parses a JSON configuration file.
    pub(crate) fn handle_read_config_file(
        &self,
        _ctx: &core_::context::Context,
        params: &ReadConfigFileParams,
    ) -> Result<Option<ReadConfigFileResponse>, String> {
        let config_file_name = self.to_file_name(&params.file);
        let Some(config_file_content) = self.fs().read_file(&config_file_name) else {
            return Ok(Some(ReadConfigFileResponse {
                // `map[string]any{}` — the empty object, not `null`.
                config: serde_json::Value::Object(serde_json::Map::new()),
                error: Some(new_diagnostic_response(
                    ast::diagnostic::new_compiler_diagnostic(
                        &tsc_diagnostics::Cannot_read_file_0,
                        &[config_file_name.as_string().to_string()],
                    ),
                    &[],
                )),
            }));
        };

        let (config, parse_errors) = tsoptions::tsconfigparsing::parse_config_file_text_to_json(
            config_file_name.clone(),
            self.path_key(&config_file_name),
            &config_file_content,
        );
        let mut response = ReadConfigFileResponse {
            // PORT: `config` is `tsoptions::value::Value` — the port's
            // closed `any` carrier; serialized it is the same JSON Go
            // marshals from `map[string]any`.
            config: serde_json::to_value(&config).unwrap_or(serde_json::Value::Null),
            error: None,
        };
        if let Some(first) = parse_errors.first() {
            // The diagnostics' parse arena is dropped inside
            // `parse_config_file_text_to_json`; strip the `file.node`
            // handles so rendering uses the `DiagnosticFile` snapshot.
            response.error = Some(new_diagnostic_response(
                strip_foreign_diagnostic_nodes(first, None),
                &[],
            ));
        }
        Ok(Some(response))
    }

    /// `s.handleParseJsonConfigFileContent` parses an in-memory JSON
    /// configuration.
    pub(crate) fn handle_parse_json_config_file_content(
        &self,
        _ctx: &core_::context::Context,
        params: &ParseJsonConfigFileContentParams,
    ) -> Result<Option<ConfigFileResponse>, String> {
        if params.config_directory.is_none() == params.config_file_name.is_none() {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: exactly one of configDirectory or configFileName is required"
            ));
        }

        let (base_path, config_file_name) = if let Some(dir) = &params.config_directory {
            (
                tspath::to_rooted_directory_path(dir, &self.current_directory()),
                tspath::RootedFilePath::default(),
            )
        } else {
            let config_file_name = self.to_file_name(params.config_file_name.as_ref().unwrap());
            (config_file_name.directory(), config_file_name)
        };

        // PORT: `jsonValueToAny` produces the closed `tsoptions::value::Value`
        // enum — Go's `any` carrier.
        let json = json_value_to_any(&params.json);
        let parsed_command_line = tsoptions::tsconfigparsing::parse_json_config_file_content(
            &json,
            &self.snapshot_host.fs,
            base_path,
            None, // existing_options
            config_file_name,
            &[],  // resolution_stack
            None, // extended_config_cache
        );
        // Diagnostics (e.g. from an `extends` chain) can reference
        // transient config arenas that do not survive the parse — strip
        // every `file.node` handle.
        {
            let mut errors = parsed_command_line.errors.lock().unwrap();
            for d in errors.iter_mut() {
                *d = strip_foreign_diagnostic_nodes(d, None);
            }
        }
        Ok(new_config_file_response(Some(&parsed_command_line), &[]))
    }

    /// `s.handleParseConfigFile` parses a tsconfig.json file and returns
    /// its contents.
    pub(crate) fn handle_parse_config_file(
        &self,
        _ctx: &core_::context::Context,
        params: &ParseConfigFileParams,
    ) -> Result<Option<ConfigFileResponse>, String> {
        let config_file_name = self.to_file_name(&params.file);
        let Some(config_file_content) = self.fs().read_file(&config_file_name) else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: could not read file {:?}",
                config_file_name.as_string()
            ));
        };

        let config_dir = config_file_name.directory();
        // PORT: Go mutates the `*TsConfigSourceFile` by pointer; the port
        // shares it as `Arc` (interior `Mutex` fields carry the mutation).
        let ts_config_source_file = Arc::new(
            tsoptions::tsconfigparsing::new_tsconfig_source_file_from_file_path(
                config_file_name.clone(),
                self.path_key(&config_file_name),
                &config_file_content,
            ),
        );
        let parsed_command_line = tsoptions::tsconfigparsing::parse_json_source_file_config_file_content(
            &ts_config_source_file,
            &self.snapshot_host.fs,
            config_dir,
            None, // existing_options
            None, // existing_options_raw
            &[],  // resolution_stack
            None, // extended_config_cache
        );
        // Root-config diagnostics keep their `file.node` handles (the
        // arena is `ts_config_source_file.nodes`); diagnostics minted by
        // transient extended-config parses index foreign arenas and are
        // stripped.
        let keep = Some(ts_config_source_file.source_file.file_index());
        {
            let mut errors = parsed_command_line.errors.lock().unwrap();
            for d in errors.iter_mut() {
                *d = strip_foreign_diagnostic_nodes(d, keep);
            }
        }
        Ok(new_config_file_response(
            Some(&parsed_command_line),
            &ts_config_source_file.nodes,
        ))
    }

    /// `s.handleTranspile`.
    pub(crate) fn handle_transpile(
        &self,
        ctx: &core_::context::Context,
        params: &TranspileParams,
        declaration: bool,
    ) -> Result<Option<TranspileOutputResponse>, String> {
        transpile_output(
            ctx,
            &params.input,
            &params.options,
            declaration,
            &self.current_directory(),
        )
    }

    /// `s.handleTranspileFromFile`.
    pub(crate) fn handle_transpile_from_file(
        &self,
        ctx: &core_::context::Context,
        params: &TranspileFromFileParams,
        declaration: bool,
    ) -> Result<Option<TranspileOutputResponse>, String> {
        let file_name =
            tspath::to_rooted_file_path(&params.file_name, &self.current_directory());
        let Some(input) = self.fs().read_file(&file_name) else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: could not read file {:?}",
                file_name.as_string()
            ));
        };
        let mut options = params.options.clone();
        options.file_name = file_name.as_string().to_string();
        transpile_output(ctx, &input, &options, declaration, &self.current_directory())
    }

    /// `s.handleCreateSourceFile`.
    /// `@gen-proto-result: SourceFileResponse`
    pub(crate) fn handle_create_source_file(
        &self,
        _ctx: &core_::context::Context,
        params: &CreateSourceFileParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let file_name = self.resolve_create_source_file_name(&params.file_name)?;
        let lease =
            self.create_source_file(file_name, params.source_text.clone(), &params.options)?;
        self.encode_leased_source_file(lease)
    }

    /// `s.handleCreateSourceFileFromFile`.
    /// `@gen-proto-result: SourceFileResponse`
    pub(crate) fn handle_create_source_file_from_file(
        &self,
        _ctx: &core_::context::Context,
        params: &CreateSourceFileFromFileParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let file_name = self.resolve_create_source_file_name(&params.file_name)?;
        let Some(source_text) = self.fs().read_file(&file_name) else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: could not read file {:?}",
                file_name.as_string()
            ));
        };
        let lease = self.create_source_file(file_name, source_text, &params.options)?;
        self.encode_leased_source_file(lease)
    }

    /// `s.handleRetainSourceFile`.
    pub(crate) fn handle_retain_source_file(
        &self,
        params: &RetainSourceFileParams,
    ) -> Result<Option<RetainSourceFileResponse>, String> {
        let lease = self.acquire_cached_source_file(&params.file)?;
        Ok(Some(RetainSourceFileResponse {
            lease: self.register_source_file_lease(lease),
        }))
    }

    /// `s.handleGetCachedSourceFile`.
    /// `@gen-proto-result: SourceFileResponse`
    pub(crate) fn handle_get_cached_source_file(
        &self,
        params: &GetCachedSourceFileParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let lease = self.acquire_cached_source_file(&params.file)?;
        // `defer lease.Release()`.
        let result = {
            let parsed = lease.source_file().lock().unwrap();
            self.encode_source_file_response(Some((
                (*parsed.nodes).get_mut(),
                parsed.file,
            )))
        };
        lease.release();
        result
    }

    /// `s.handleGetSymbolOfDeclaration`.
    pub(crate) fn handle_get_symbol_of_declaration(
        &self,
        params: &GetSymbolOfDeclarationParams,
    ) -> Result<Option<SymbolResponse>, String> {
        let lease = self.acquire_cached_source_file(&params.file)?;
        // PORT: the leased parse-cache file is unbound (Go binds cached
        // files eagerly, so `node.Symbol()` works on `lease.SourceFile()`);
        // `bound_source_file` is the session's privately bound clone. Its
        // arena layout is identical, so the encoder's index table still
        // applies.
        let bound = self.bound_source_file(&lease);

        let result = (|| {
            let nodes = (*bound.nodes).get_mut();
            let table = encoder::get_node_index_table(nodes, bound.file);
            if params.index == 0 || params.index as usize >= table.nodes.len() {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: declaration node index {} is out of range",
                    params.index
                ));
            }
            let Some(node) = table.nodes[params.index as usize] else {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: node index {} is not a declaration",
                    params.index
                ));
            };
            if !ast::is_declaration(&nodes[node]) {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: node index {} is not a declaration",
                    params.index
                ));
            }
            let Some(symbol) = nodes[node].symbol() else {
                return Err(format!(
                    "{ERR_CLIENT_ERROR}: declaration node index {} has no binder symbol",
                    params.index
                ));
            };
            Ok(new_file_symbol_response(nodes, &bound.symbols, symbol))
        })();
        lease.release();
        result.map(Some)
    }

    /// `s.handleReleaseSourceFile`.
    ///
    /// PORT: Go's `params == nil` arm is unreachable — dispatch always
    /// unmarshals a params box.
    pub(crate) fn handle_release_source_file(
        &self,
        params: &ReleaseSourceFileParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        if params.lease == 0 {
            return Err(format!("{ERR_CLIENT_ERROR}: empty source file lease"));
        }
        let lease = self
            .source_file_leases
            .lock()
            .unwrap()
            .remove(&params.lease);
        let Some(lease) = lease else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: source file lease {} not found",
                params.lease
            ));
        };
        lease.release();
        // Go returns `true` — a JSON `true` payload.
        Ok(Some(ipc::ResponsePayload::Json(
            ipc::marshal_params(&true).map_err(|e| e.to_string())?,
        )))
    }

    /// `s.handleGetSourceFile` returns a source file from a project within
    /// a snapshot.
    /// `@gen-proto-result: SourceFileResponse` `@gen-proto-nullable`
    pub(crate) fn handle_get_source_file(
        &self,
        _ctx: &core_::context::Context,
        params: &GetSourceFileParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;
        match program.get_source_file(&params.file.to_file_name(&program.base_directory())) {
            Some(file) => {
                let nodes = program.arena_of(file);
                self.encode_source_file_response(Some(((*nodes).get_mut(), file)))
            }
            None => self.encode_source_file_response(None),
        }
    }

    /// `s.handleGetConfigFileNames` returns tsconfig file names associated
    /// with the project's command line.
    /// `@gen-proto-nullable`
    ///
    /// PORT: `[]tspath.RootedFilePath` → `Vec<String>` — `RootedFilePath`
    /// carries no `Serialize` impl (proto bridges it per-field through
    /// `ser_str`); a `Vec<String>` is the same wire shape. Go's
    /// `commandLine == nil` check is unreachable — `command_line()` is a
    /// non-null `&Arc<ParsedCommandLine>` — so `config_file` absence covers
    /// it.
    pub(crate) fn handle_get_config_file_names(
        &self,
        _ctx: &core_::context::Context,
        params: &GetProjectDiagnosticsParams,
    ) -> Result<Option<Vec<String>>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;

        let command_line = program.command_line();
        let Some(config_file) = command_line.config_file.as_ref() else {
            return Ok(None);
        };
        // `commandLine.ConfigFile.SourceFile == nil`.
        if config_file.source_file.is_none() {
            return Ok(None);
        }

        let extended_files = command_line.extended_source_files();
        let mut config_files = Vec::with_capacity(extended_files.len() + 1);
        config_files.push(config_file.file_name().as_string().to_string());
        config_files.extend(
            extended_files
                .iter()
                .map(|f| f.as_string().to_string()),
        );
        Ok(Some(config_files))
    }

    /// `s.handleGetConfigSourceFile` returns a tsconfig source file
    /// associated with the project's command line.
    /// `@gen-proto-result: SourceFileResponse` `@gen-proto-nullable`
    pub(crate) fn handle_get_config_source_file(
        &self,
        _ctx: &core_::context::Context,
        params: &GetSourceFileParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;

        // See `handle_get_config_file_names` for the `commandLine == nil`
        // PORT note.
        let command_line = program.command_line();
        let Some(config_file) = command_line.config_file.as_ref() else {
            return self.encode_source_file_response(None);
        };
        if config_file.source_file.is_none() {
            return self.encode_source_file_response(None);
        }

        let requested_path = program
            .path_key_for_file_name(&params.file.to_file_name(&program.base_directory()));
        let root_config_source_file = config_file.source_file;
        if config_file.nodes[root_config_source_file]
            .as_source_file()
            .path_key()
            == &requested_path
        {
            // PORT: `config_file` is `Arc`-shared and `nodes` is a plain
            // `Vec` — the encoder needs `&mut Vec<Node>` to cache the node
            // index table on the file, so the arena is cloned. Go mutates
            // the shared `*ast.SourceFile` directly.
            let mut nodes = config_file.nodes.clone();
            return self.encode_source_file_response(Some((&mut nodes, root_config_source_file)));
        }

        for config_file_name in command_line.extended_source_files() {
            if program
                .case_sensitivity()
                .path_key(&config_file_name.as_path())
                != requested_path
            {
                continue;
            }
            let Some(config_file_content) = sd.snapshot.read_file(&config_file_name) else {
                return self.encode_source_file_response(None);
            };
            let mut config_source_file = tsoptions::tsconfigparsing::new_tsconfig_source_file_from_file_path(
                config_file_name,
                requested_path.clone(),
                &config_file_content,
            );
            return self.encode_source_file_response(Some((
                &mut config_source_file.nodes,
                config_source_file.source_file,
            )));
        }

        self.encode_source_file_response(None)
    }

    // ---------------------------------------------------------------------
    // lease plumbing
    // ---------------------------------------------------------------------

    /// `s.resolveCreateSourceFileName`.
    fn resolve_create_source_file_name(
        &self,
        file_name: &str,
    ) -> Result<tspath::RootedFilePath, String> {
        if file_name.is_empty() {
            return Err(format!("{ERR_CLIENT_ERROR}: fileName must not be empty"));
        }
        Ok(self.current_directory().resolve_file(file_name))
    }

    /// `s.createSourceFile`.
    fn create_source_file(
        &self,
        file_name: tspath::RootedFilePath,
        source_text: String,
        options: &CreateSourceFileOptions,
    ) -> Result<project::snapshothost::SourceFileLease, String> {
        let mut script_kind = options.script_kind;
        if script_kind == core_::scriptkind::ScriptKind::Unknown {
            script_kind = core_::core::ensure_script_kind_from_file_name(&file_name);
        }
        if !is_valid_create_source_file_script_kind(script_kind) {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: invalid scriptKind {}",
                script_kind as i32
            ));
        }
        let path_key = self.path_key(&file_name);
        Ok(self.acquire_source_file(
            ast::parseoptions::SourceFileParseOptions {
                file_name,
                path_key,
                ..Default::default()
            },
            source_text,
            script_kind,
        ))
    }

    /// `s.encodeLeasedSourceFile` — registers the lease so the client can
    /// release it later, then encodes like `encodeSourceFileResponse`.
    fn encode_leased_source_file(
        &self,
        lease: project::snapshothost::SourceFileLease,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        // PORT: `encode_source_file` is infallible — Go's `EncodeSourceFile`
        // error path (release the lease, `failed to encode source file`)
        // has no Rust equivalent.
        let (mut data, file) = {
            let parsed = lease.source_file().lock().unwrap();
            let (data, _) =
                encoder::encode_source_file((*parsed.nodes).get_mut(), parsed.file);
            (data, parsed.file)
        };
        encoder::set_source_file_id(&mut data, source_file_node_id(file));
        let id = self.register_source_file_lease(lease);
        encoder::set_source_file_lease(&mut data, id.0);
        self.source_file_data_response(data)
    }

    /// `s.registerSourceFileLease`.
    fn register_source_file_lease(
        &self,
        lease: project::snapshothost::SourceFileLease,
    ) -> SourceFileLeaseId {
        let id = SourceFileLeaseId(
            self.next_source_file_lease_id
                .fetch_add(1, Ordering::SeqCst)
                + 1,
        );
        self.source_file_leases
            .lock()
            .unwrap()
            .insert(id, Rc::new(lease));
        id
    }

    /// `s.releaseSourceFileLeases` — drains the lease table and releases
    /// each lease (called from `Close` in Go; session.go:5173).
    pub(crate) fn release_source_file_leases(&self) {
        let leases: Vec<Rc<project::snapshothost::SourceFileLease>> = self
            .source_file_leases
            .lock()
            .unwrap()
            .drain()
            .map(|(_, lease)| lease)
            .collect();
        for lease in leases {
            lease.release();
        }
    }

    /// `s.encodeSourceFileResponse` — `None` → `RawBinary(nil)`/`null`.
    fn encode_source_file_response(
        &self,
        source_file: Option<(&mut Vec<ast::Node>, ast::NodeId)>,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let Some((nodes, file)) = source_file else {
            if self.use_binary_responses {
                return Ok(Some(ipc::ResponsePayload::Binary(Vec::new())));
            }
            return Ok(None);
        };
        // Encode the full source file.
        let (mut data, _) = encoder::encode_source_file(nodes, file);
        encoder::set_source_file_id(&mut data, source_file_node_id(file));
        self.source_file_data_response(data)
    }

    /// The shared `useBinaryResponses` tail of `encodeSourceFileResponse` /
    /// `encodeLeasedSourceFile`: `RawBinary` for binary sessions, else a
    /// JSON `SourceFileResponse` payload.
    fn source_file_data_response(
        &self,
        data: Vec<u8>,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        if self.use_binary_responses {
            return Ok(Some(ipc::ResponsePayload::Binary(data)));
        }
        Ok(Some(ipc::ResponsePayload::Json(
            ipc::marshal_params(&SourceFileResponse {
                data: ipc::base64_std_encode(&data),
            })
            .map_err(|e| e.to_string())?,
        )))
    }
}

/// `transpileOutput`.
fn transpile_output(
    ctx: &core_::context::Context,
    input: &str,
    options: &TranspileOptions,
    declaration: bool,
    current_directory: &tspath::RootedDirectoryPath,
) -> Result<Option<TranspileOutputResponse>, String> {
    let mut compiler_options = options.compiler_options.clone();
    let mut diagnostics: Vec<DiagnosticRef> = Vec::new();
    if let Some(input_options) = &options.compiler_options_input {
        let (opts, diags) = input_options.finalize(current_directory);
        compiler_options = Some(opts);
        diagnostics = diags;
    }
    let transpile_options = transpile::Options {
        compiler_options,
        file_name: options.file_name.clone(),
        report_diagnostics: options.report_diagnostics,
    };
    let output = if declaration {
        transpile::transpile_declaration(ctx, input, transpile_options)
    } else {
        transpile::transpile_module(ctx, input, transpile_options)
    };
    let Some(output) = output else {
        if ctx.is_cancelled() {
            // `ctx.Err()` — `context.Canceled`.
            return Err(ipc::Error::ContextCanceled.to_string());
        }
        return Err("transpilation produced no output".to_string());
    };

    // `output.Diagnostics = append(diagnostics, output.Diagnostics...)`.
    let transpile::Output {
        output_text,
        diagnostics: output_diagnostics,
        source_map_text,
        nodes: arenas,
    } = output;
    let mut all_diagnostics = diagnostics;
    all_diagnostics.extend(output_diagnostics);

    // Diagnostics carry `file.node` handles into their own arenas — the
    // output retains a snapshot per `file_index`. Each diagnostic keeps
    // its handle only when its arena is present.
    let diagnostics = all_diagnostics
        .iter()
        .map(|d| {
            let keep = ast::diagnostic::lock_diagnostic(d)
                .file()
                .and_then(|file| file.node)
                .map(|node| node.file_index())
                .filter(|index| arenas.contains_key(index));
            let nodes: &[ast::Node] = keep
                .and_then(|index| arenas.get(&index))
                .map(|arena| arena.as_slice())
                .unwrap_or(&[]);
            new_diagnostic_response(strip_foreign_diagnostic_nodes(d, keep), nodes)
        })
        .collect();

    Ok(Some(TranspileOutputResponse {
        output_text,
        diagnostics,
        source_map_text,
    }))
}

/// `strip_diagnostic_nodes` (handlers_lifecycle.rs) with a `keep` escape:
/// clears `file.node` recursively unless the node's `file_index` names the
/// `keep` arena — the one arena the caller passes to
/// `new_diagnostic_response`. Handles outside it would index the wrong
/// nodes (`Index<NodeId>` resolves `local_index` only) or a dead arena.
fn strip_foreign_diagnostic_nodes(
    d: &DiagnosticRef,
    keep: Option<u32>,
) -> DiagnosticRef {
    let stripped = ast::diagnostic::lock_diagnostic(d).clone_diagnostic();
    {
        let mut locked = ast::diagnostic::lock_diagnostic(&stripped);
        if let Some(mut file) = locked.file().cloned() {
            if file
                .node
                .is_some_and(|node| Some(node.file_index()) != keep)
            {
                file.node = None;
                locked.set_file(Some(file));
            }
        }
        let chain: Vec<DiagnosticRef> = locked
            .message_chain()
            .iter()
            .map(|c| strip_foreign_diagnostic_nodes(c, keep))
            .collect();
        locked.set_message_chain(chain);
        let related: Vec<DiagnosticRef> = locked
            .related_information()
            .iter()
            .map(|r| strip_foreign_diagnostic_nodes(r, keep))
            .collect();
        locked.set_related_info(related);
    }
    stripped
}
