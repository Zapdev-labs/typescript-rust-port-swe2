// Ported from tsc/internal/api/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Handlers for command-line/config parsing, transpilation, and the
// source-file lease surface (create/retain/get/release/cached) —
// Go lines ~1990–2458.
//
// PORT notes:
// - `*ast.SourceFile` leases are `ParsedSourceFile` pairs
//   (`{nodes: Rc<NodeArenaBuf>, file: NodeId}`) under the snapshot host's
//   parse cache; the encoder takes `&mut Vec<Node>` via
//   `(*parsed.nodes).get_mut()`.
// - Go's `any` returns are `Result<Option<ipc::ResponsePayload>, String>`:
//   `RawBinary(data)` → `Binary`, nil → `None`, other values → JSON.

use std::sync::Arc;

use tsc_apiencoder as encoder;
use tsc_ast as ast;
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
        Ok(new_config_file_response(
            Some(&tsoptions::commandlineparser::parse_command_line(
                &params.command_line,
                &self.snapshot_host.fs(),
                self.current_directory(),
            )),
            &[],
        ))
    }

    /// `s.handleReadConfigFile` reads and parses a JSON configuration file.
    pub(crate) fn handle_read_config_file(
        &self,
        _ctx: &core_::context::Context,
        params: &ReadConfigFileParams,
    ) -> Result<Option<ReadConfigFileResponse>, String> {
        let config_file_name = self.to_file_name(&params.file);
        let Some(config_file_content) = self.snapshot_host.fs().read_file(&config_file_name) else {
            return Ok(Some(ReadConfigFileResponse {
                config: serde_json::Value::Object(Default::default()),
                error: Some(new_diagnostic_response(
                    ast::diagnostic::new_compiler_diagnostic(
                        &tsc_diagnostics::Cannot_read_file_0,
                        &[config_file_name.as_string()],
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
            config: serde_json::to_value(&config).unwrap_or(serde_json::Value::Null),
            error: None,
        };
        if let Some(first) = parse_errors.first() {
            // `new_diagnostic_response` needs the parse arena that produced
            // the diagnostic — `parse_config_file_text_to_json` owns it, so
            // resolve with an empty table like Go's plain-diagnostic path.
            response.error = Some(new_diagnostic_response(first.clone(), &[]));
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
            let name = self.to_file_name(params.config_file_name.as_ref().unwrap());
            (name.directory(), name)
        };

        let parsed_command_line = tsoptions::tsconfigparsing::parse_json_config_file_content(
            &json_value_to_tsoptions(&params.json),
            &self.snapshot_host.fs(),
            base_path,
            None, // existing_options
            config_file_name,
            &[],  // resolution_stack
            None, // extended_config_cache
        );
        let nodes: &[ast::Node] = parsed_command_line
            .config_file
            .as_ref()
            .map(|cf| cf.nodes.as_slice())
            .unwrap_or(&[]);
        Ok(new_config_file_response(Some(&parsed_command_line), nodes))
    }

    /// `s.handleParseConfigFile` parses a tsconfig.json file and returns
    /// its contents.
    pub(crate) fn handle_parse_config_file(
        &self,
        _ctx: &core_::context::Context,
        params: &ParseConfigFileParams,
    ) -> Result<Option<ConfigFileResponse>, String> {
        let config_file_name = self.to_file_name(&params.file);
        let Some(config_file_content) = self.snapshot_host.fs().read_file(&config_file_name)
        else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: could not read file {:?}",
                config_file_name
            ));
        };

        let config_dir = config_file_name.directory();
        let tsconfig_source_file = Arc::new(tsoptions::tsconfigparsing::new_tsconfig_source_file_from_file_path(
            config_file_name.clone(),
            self.path_key(&config_file_name),
            &config_file_content,
        ));
        let nodes = tsconfig_source_file.nodes.clone();
        let parsed_command_line = tsoptions::tsconfigparsing::parse_json_source_file_config_file_content(
            &tsconfig_source_file,
            &self.snapshot_host.fs(),
            config_dir,
            None, // existing_options
            None, // existing_options_raw
            &[],  // resolution_stack
            None, // extended_config_cache
        );
        Ok(new_config_file_response(Some(&parsed_command_line), &nodes))
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
        let Some(input) = self.snapshot_host.fs().read_file(&file_name) else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: could not read file {:?}",
                file_name
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
        let Some(source_text) = self.snapshot_host.fs().read_file(&file_name) else {
            return Err(format!(
                "{ERR_CLIENT_ERROR}: could not read file {:?}",
                file_name
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
        let result = {
            let parsed = lease.source_file();
            let parsed = parsed.lock().unwrap();
            self.encode_source_file_response(
                &mut (*parsed.nodes).get_mut(),
                Some(parsed.file),
            )
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

        // Go's `node.Symbol()` reads the binder-owned symbol; the port
        // binds the leased AST into a private clone arena
        // (`bound_source_file`) — the clone shares node indices with the
        // cached file, so the encoder's index table addresses it.
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
    pub(crate) fn handle_release_source_file(
        &self,
        params: &ReleaseSourceFileParams,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        if params.lease.is_zero() {
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
                params.lease.0
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
        let file_name = params.file.to_file_name(&program.base_directory());
        match program.get_source_file(&file_name) {
            Some(source_file) => {
                let nodes = program.arena_of(source_file);
                self.encode_source_file_response(
                    (*nodes).get_mut(),
                    Some(source_file),
                )
            }
            None => self.encode_source_file_response(&mut Vec::new(), None),
        }
    }

    /// `s.handleGetConfigFileNames` returns tsconfig file names associated
    /// with the project's command line.
    /// `@gen-proto-nullable`
    pub(crate) fn handle_get_config_file_names(
        &self,
        _ctx: &core_::context::Context,
        params: &GetProjectDiagnosticsParams,
    ) -> Result<Option<Vec<String>>, String> {
        let sd = self.get_snapshot_data(params.snapshot)?;
        let program = sd.get_program(&params.project)?;

        // PORT: `program.command_line()` is always `Some` in the port
        // (Go's nil check is subsumed); `config_file` stays Optional.
        let command_line = program.command_line();
        let Some(config_file) = command_line.config_file.as_ref() else {
            return Ok(None);
        };

        let extended = command_line.extended_source_files();
        let mut config_files = Vec::with_capacity(extended.len() + 1);
        config_files.push(
            config_file.file_name().as_string().to_string(),
        );
        config_files.extend(extended.iter().map(|f| f.as_string().to_string()));
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

        let command_line = program.command_line();
        let Some(config_file) = command_line.config_file.as_ref() else {
            return self.encode_source_file_response(&mut Vec::new(), None);
        };

        let requested_path =
            program.path_key_for_file_name(&params.file.to_file_name(&program.base_directory()));
        let root_config_source_file = config_file.source_file;
        if *config_file.nodes[root_config_source_file].as_source_file().path_key() == requested_path {
            let mut nodes = config_file.nodes.clone();
            return self.encode_source_file_response(&mut nodes, Some(root_config_source_file));
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
                return self.encode_source_file_response(&mut Vec::new(), None);
            };
            let config_source_file = tsoptions::tsconfigparsing::new_tsconfig_source_file_from_file_path(
                config_file_name,
                requested_path.clone(),
                &config_file_content,
            );
            let mut nodes = config_source_file.nodes.clone();
            return self.encode_source_file_response(&mut nodes, Some(config_source_file.source_file));
        }

        self.encode_source_file_response(&mut Vec::new(), None)
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
        Ok(self.acquire_source_file(
            ast::parseoptions::SourceFileParseOptions {
                file_name: file_name.clone(),
                path_key: self.path_key(&file_name),
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
        let (mut data, file) = {
            let parsed = lease.source_file();
            let parsed = parsed.lock().unwrap();
            let (data, _) =
                encoder::encode_source_file((*parsed.nodes).get_mut(), parsed.file);
            (data, parsed.file)
        };
        encoder::set_source_file_id(&mut data, source_file_node_id(file));
        let id = self.register_source_file_lease(lease);
        encoder::set_source_file_lease(&mut data, id.0);
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

    /// `s.registerSourceFileLease`.
    fn register_source_file_lease(
        &self,
        lease: project::snapshothost::SourceFileLease,
    ) -> SourceFileLeaseId {
        let id = SourceFileLeaseId(
            self.next_source_file_lease_id
                .fetch_add(1, std::sync::atomic::Ordering::SeqCst)
                + 1,
        );
        self.source_file_leases
            .lock()
            .unwrap()
            .insert(id, std::rc::Rc::new(lease));
        id
    }

    /// `s.encodeSourceFileResponse` — `None` → `RawBinary(nil)`/`null`.
    fn encode_source_file_response(
        &self,
        nodes: &mut Vec<ast::Node>,
        source_file: Option<ast::NodeId>,
    ) -> Result<Option<ipc::ResponsePayload>, String> {
        let Some(source_file) = source_file else {
            if self.use_binary_responses {
                return Ok(Some(ipc::ResponsePayload::Binary(Vec::new())));
            }
            return Ok(None);
        };
        let (mut data, _) = encoder::encode_source_file(nodes, source_file);
        encoder::set_source_file_id(&mut data, source_file_node_id(source_file));
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

/// `packagejson.JSONValue` → `tsoptions.Value` (Go's `any` round-trips the
/// same shapes: `*OrderedMap[string,any]` → `Map`, `[]any` → `List`,
/// `float64` → `Float`, etc.).
fn json_value_to_tsoptions(v: &tsc_packagejson::JSONValue) -> tsoptions::value::Value {
    use tsc_packagejson::JSONValueData;
    match &v.value {
        JSONValueData::Null => tsoptions::value::Value::Null,
        JSONValueData::String(s) => tsoptions::value::Value::Str(s.clone()),
        JSONValueData::Number(n) => tsoptions::value::Value::Float(*n),
        JSONValueData::Boolean(b) => tsoptions::value::Value::Bool(*b),
        JSONValueData::Array(items) => tsoptions::value::Value::List(
            items.iter().map(json_value_to_tsoptions).collect(),
        ),
        JSONValueData::Object(map) => {
            let mut out = tsc_collections::OrderedMap::new();
            for (k, child) in map.entries() {
                out.set(k.clone(), json_value_to_tsoptions(child));
            }
            tsoptions::value::Value::Map(out)
        }
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
    let mut diagnostics: Vec<ast::diagnostic::DiagnosticRef> = Vec::new();
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
    let Some(mut output) = output else {
        if ctx.is_cancelled() {
            return Err("context cancelled".to_string());
        }
        return Err("transpilation produced no output".to_string());
    };
    diagnostics.extend(output.diagnostics);
    output.diagnostics = diagnostics;
    // Diagnostics carry `Node` refs from the transpile arena — resolve
    // them with the arena snapshots the output retains.
    let nodes: &[ast::Node] = output
        .nodes
        .values()
        .next()
        .map(|a| a.as_slice())
        .unwrap_or(&[]);
    Ok(Some(TranspileOutputResponse {
        output_text: output.output_text,
        diagnostics: new_diagnostic_responses(&output.diagnostics, nodes),
        source_map_text: output.source_map_text,
    }))
}
