// Ported from tsc/internal/lsp/server.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// The `handle*` request/notification methods of `Server`, split out of
// `server.rs` (allowed per the port instructions — Go keeps them in the same
// file).

use std::collections::{BTreeMap, HashMap};
use std::io::Write as _;
use std::rc::Rc;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex, mpsc};

use tsc_collections::Set;
use tsc_core::context::{Context, with_checker_lifetime, CheckerLifetime};
use tsc_core::options_generated::CompilerOptions;
use tsc_ipc as ipc;
use tsc_json as json;
use tsc_ls as ls;
use tsc_lsconv as lsconv;
use tsc_lsproto as lsproto;
use tsc_lsutil as lsutil;
use tsc_project as project;
use tsc_project::session::{ContentMapperContributions, SessionInit, SessionOptions};
use tsc_tsoptions as tsoptions;
use tsc_tspath as tspath;
use tsc_project_logging::Logger as _;

use crate::logger::is_valid_log_verbosity;
use crate::progress::new_project_loading_progress;
use crate::server::{
    ApiSessionState, Error, Server, ServerOrchestrator, file_rename_filters,
    supported_code_action_kinds,
};

impl Server {
    /// `s.clientCapabilities` — the resolved caps (zero value pre-initialize).
    pub(crate) fn caps(&self) -> &lsproto::ResolvedClientCapabilities {
        static DEFAULT: std::sync::LazyLock<lsproto::ResolvedClientCapabilities> =
            std::sync::LazyLock::new(lsproto::ResolvedClientCapabilities::default);
        self.client_capabilities.get().unwrap_or(&DEFAULT)
    }
}

impl Server {
    /// `s.handleInitialize`.
    pub(crate) fn handle_initialize(
        self: &Arc<Self>,
        _ctx: &Context,
        params: Option<lsproto::InitializeParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::InitializeResponse, Error> {
        if self.has_initialize_params() {
            return Err(Error::Code(lsproto::ErrorCode::InvalidRequest));
        }
        self.init_started.store(true, Ordering::SeqCst);

        let params = params.unwrap_or_default();
        // The spec types initializationOptions as nullable; treat null and
        // absent as empty options.
        let initialization_options = params
            .initialization_options
            .as_ref()
            .and_then(|o| o.initialization_options.clone())
            .unwrap_or_default();
        if let Some(v) = initialization_options.log_verbosity
            && is_valid_log_verbosity(v)
        {
            self.logger.set_verbosity(v);
        }
        if let Some(flake) = initialization_options.track_flaky_diagnostics {
            *self.flake_logging.lock().unwrap() = flake;
        }
        let caps = lsproto::ResolvedClientCapabilities::resolve(params.capabilities.as_ref());
        if caps.window.work_done_progress {
            *self.project_progress.lock().unwrap() =
                Some(new_project_loading_progress(self, self.progress_delay));
        }

        let capabilities_json =
            json::marshal_indent(&caps, "", "\t").map_err(|e| Error::Marshal(e.to_string()))?;
        self.logger.info(format_args!(
            "Resolved client capabilities: {}",
            String::from_utf8_lossy(&capabilities_json)
        ));

        let position_encoding = if caps
            .general
            .position_encodings
            .iter()
            .any(|e| *e == lsproto::PositionEncodingKind::UTF8)
        {
            lsproto::PositionEncodingKind::UTF8
        } else {
            lsproto::PositionEncodingKind::UTF16
        };

        if let Some(locale) = &params.locale {
            let (parsed, _) = tsc_locale::parse(locale);
            self.set_locale(parsed);
        }
        let _ = self.init_locale.set(self.get_locale());

        if let Some(start_watchdog) = &self.start_watchdog
            && let Some(pid) = params.process_id.integer
        {
            start_watchdog(pid);
        }

        let _ = self.initialize_params.set(params);
        let _ = self.initialization_options.set(initialization_options);
        let _ = self.position_encoding.set(position_encoding.clone());
        self.client_capabilities.set(caps).ok();

        Ok(Some(lsproto::InitializeResult {
            server_info: Some(lsproto::ServerInfo {
                name: "typescript".to_string(),
                version: Some(tsc_core::version::version().to_string()),
            }),
            capabilities: Some(lsproto::ServerCapabilities {
                position_encoding: Some(position_encoding),
                text_document_sync: Some(lsproto::TextDocumentSyncOptionsOrKind {
                    options: Some(lsproto::TextDocumentSyncOptions {
                        open_close: Some(true),
                        change: Some(lsproto::TextDocumentSyncKind::Incremental),
                        save: Some(lsproto::BooleanOrSaveOptions {
                            boolean: Some(true),
                            ..Default::default()
                        }),
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
                hover_provider: Some(lsproto::BooleanOrHoverOptions {
                    boolean: Some(true),
                    ..Default::default()
                }),
                definition_provider: Some(lsproto::BooleanOrDefinitionOptions {
                    boolean: Some(true),
                    ..Default::default()
                }),
                type_definition_provider: Some(
                    lsproto::BooleanOrTypeDefinitionOptionsOrTypeDefinitionRegistrationOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                references_provider: Some(lsproto::BooleanOrReferenceOptions {
                    boolean: Some(true),
                    ..Default::default()
                }),
                implementation_provider: Some(
                    lsproto::BooleanOrImplementationOptionsOrImplementationRegistrationOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                diagnostic_provider: Some(lsproto::DiagnosticOptionsOrRegistrationOptions {
                    options: Some(lsproto::DiagnosticOptions {
                        identifier: Some("typescript".to_string()),
                        inter_file_dependencies: true,
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
                completion_provider: Some(lsproto::CompletionOptions {
                    trigger_characters: Some(ls::completion_trigger_characters()),
                    resolve_provider: Some(true),
                    completion_item: Some(lsproto::ServerCompletionItemOptions {
                        label_details_support: Some(true),
                    }),
                    ..Default::default()
                }),
                signature_help_provider: Some(lsproto::SignatureHelpOptions {
                    trigger_characters: Some(ls::SIGNATURE_HELP_TRIGGER_CHARACTERS.to_vec()),
                    retrigger_characters: Some(
                        ls::SIGNATURE_HELP_RETRIGGER_CHARACTERS.to_vec(),
                    ),
                    ..Default::default()
                }),
                document_formatting_provider: Some(
                    lsproto::BooleanOrDocumentFormattingOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                document_range_formatting_provider: Some(
                    lsproto::BooleanOrDocumentRangeFormattingOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                document_on_type_formatting_provider: Some(
                    lsproto::DocumentOnTypeFormattingOptions {
                        first_trigger_character: "{".to_string(),
                        more_trigger_character: Some(vec![
                            "}".to_string(),
                            ";".to_string(),
                            "\n".to_string(),
                        ]),
                    },
                ),
                workspace_symbol_provider: Some(lsproto::BooleanOrWorkspaceSymbolOptions {
                    boolean: Some(true),
                    ..Default::default()
                }),
                document_symbol_provider: Some(lsproto::BooleanOrDocumentSymbolOptions {
                    boolean: Some(true),
                    ..Default::default()
                }),
                folding_range_provider: Some(
                    lsproto::BooleanOrFoldingRangeOptionsOrFoldingRangeRegistrationOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                rename_provider: Some(lsproto::BooleanOrRenameOptions {
                    rename_options: Some(lsproto::RenameOptions {
                        prepare_provider: Some(true),
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
                document_highlight_provider: Some(
                    lsproto::BooleanOrDocumentHighlightOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                selection_range_provider: Some(
                    lsproto::BooleanOrSelectionRangeOptionsOrSelectionRangeRegistrationOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                linked_editing_range_provider: Some(
                    lsproto::BooleanOrLinkedEditingRangeOptionsOrLinkedEditingRangeRegistrationOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                inlay_hint_provider: Some(
                    lsproto::BooleanOrInlayHintOptionsOrInlayHintRegistrationOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                code_lens_provider: Some(lsproto::CodeLensOptions {
                    resolve_provider: Some(true),
                    ..Default::default()
                }),
                code_action_provider: Some(lsproto::BooleanOrCodeActionOptions {
                    code_action_options: Some(lsproto::CodeActionOptions {
                        code_action_kinds: Some(supported_code_action_kinds()),
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
                call_hierarchy_provider: Some(
                    lsproto::BooleanOrCallHierarchyOptionsOrCallHierarchyRegistrationOptions {
                        boolean: Some(true),
                        ..Default::default()
                    },
                ),
                experimental: Some(lsproto::ExperimentalServerCapabilities {
                    custom_source_definition_provider: Some(true),
                    custom_multi_document_highlight_provider: Some(true),
                }),
                vs_references_provider: Some(true),
                vs_on_auto_insert_provider: Some(lsproto::VSOnAutoInsertOptions {
                    vs_trigger_characters: Some(vec![">".to_string()]),
                }),
                workspace: Some(lsproto::WorkspaceOptions {
                    file_operations: Some(lsproto::FileOperationOptions {
                        will_rename: Some(lsproto::FileOperationRegistrationOptions {
                            filters: Some(file_rename_filters()),
                        }),
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
                semantic_tokens_provider: Some(
                    lsproto::SemanticTokensOptionsOrRegistrationOptions {
                        options: Some(lsproto::SemanticTokensOptions {
                            legend: Some(ls::semantic_tokens_legend(
                                &self.caps().text_document.semantic_tokens,
                            )),
                            full: Some(lsproto::BooleanOrSemanticTokensFullDelta {
                                boolean: Some(true),
                                ..Default::default()
                            }),
                            range: Some(lsproto::BooleanOrEmptyObject {
                                boolean: Some(true),
                                ..Default::default()
                            }),
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            }),
        }))
    }

    /// `s.handleInitialized`.
    pub(crate) fn handle_initialized(
        self: &Arc<Self>,
        ctx: &Context,
        _params: Option<lsproto::InitializedParams>,
    ) -> Result<(), Error> {
        let options = self.initialization_options.get().cloned().unwrap_or_default();
        let disable_push_diagnostics = options.disable_push_diagnostics.unwrap_or(false);
        let enable_telemetry = options.enable_telemetry.unwrap_or(false);
        let run_external_code = options.run_external_code.unwrap_or(false);

        let caps = self.caps().clone();
        if caps.workspace.did_change_watched_files.dynamic_registration {
            self.logger.logf(format_args!(
                "file watching: using LSP client-side watching (client supports dynamic registration)"
            ));
            self.watch_enabled.store(true, Ordering::SeqCst);
        } else if tsc_fswatch::default().has_fast_recursive_backend() {
            self.logger.logf(format_args!(
                "file watching: using builtin in-process watcher (client lacks dynamic watch registration)"
            ));
            self.watch_enabled.store(true, Ordering::SeqCst);
            let weak = Arc::downgrade(self);
            *self.builtin_watcher.lock().unwrap() = Some(crate::lspwatcher::Watcher::new(
                self.fs.clone(),
                Arc::new(move |changes: &[lsproto::FileEvent]| {
                    if let Some(s) = weak.upgrade()
                        && let Some(session) = s.session_opt()
                    {
                        session.did_change_watched_files(&s.background_ctx, changes);
                    }
                }),
                self.logger.clone(),
            ));
        } else {
            self.logger.logf(format_args!(
                "file watching: disabled (client lacks dynamic watch registration and builtin watcher backend is not fast-recursive)"
            ));
        }

        let mut cwd = self.cwd.clone();
        let params = self.initialize_params.get().cloned().unwrap_or_default();
        if caps.workspace.workspace_folders
            && let Some(folders) = params
                .workspace_folders
                .as_ref()
                .and_then(|f| f.workspace_folders.as_ref())
            && folders.len() == 1
        {
            let file_name =
                lsproto::DocumentUri(folders[0].uri.0.clone()).file_name();
            if !file_name.as_string().is_empty() {
                cwd = tspath::rooted_directory_path_from_path(tspath::rooted_path_from_normalized(
                    file_name.as_string(),
                ));
            }
        } else if let Some(uri) = params.root_uri.document_uri.as_ref() {
            let file_name = uri.file_name();
            if !file_name.as_string().is_empty() {
                cwd = tspath::rooted_directory_path_from_path(tspath::rooted_path_from_normalized(
                    file_name.as_string(),
                ));
            }
        } else if let Some(root_path) = params
            .root_path
            .as_ref()
            .and_then(|r| r.string.as_ref())
            && tspath::path_is_absolute(root_path)
        {
            cwd = tspath::rooted_directory_path_from_absolute(root_path);
        }

        self.telemetry_enabled.store(enable_telemetry, Ordering::SeqCst);

        let session = project::session::new_session(&SessionInit {
            background_ctx: lsproto::with_client_capabilities(&self.background_ctx, caps),
            options: Arc::new(SessionOptions {
                current_directory: cwd,
                default_library_path: self.default_library_path.clone(),
                typings_location: self.typings_location.clone(),
                position_encoding: self
                    .position_encoding
                    .get()
                    .cloned()
                    .unwrap_or_default(),
                watch_enabled: self.watch_enabled.load(Ordering::SeqCst),
                logging_enabled: true,
                telemetry_enabled: enable_telemetry,
                debounce_delay: std::time::Duration::from_millis(500),
                push_diagnostics_enabled: !disable_push_diagnostics,
                run_external_code,
                ..Default::default()
            }),
            fs: self.fs.clone(),
            client: Some(self.client.clone().unwrap_or_else(|| self.clone())),
            logger: Some(self.logger.clone()),
            npm_executor: Some(self.clone()),
            spawner: self.content_mapper_spawner(),
            content_mapper_logger: self.content_mapper_logger(),
            parse_cache: self.parse_cache.clone(),
            content_mapped_parse_cache: None,
        });
        let _ = self.session.set(session);

        let user_preferences = self.request_configuration(ctx)?;
        self.session().initialize_with_user_config(user_preferences);

        self.send_client_request(
            ctx,
            &lsproto::CLIENT_REGISTER_CAPABILITY_INFO,
            Some(lsproto::RegistrationParams {
                registrations: Some(vec![lsproto::Registration {
                    id: "typescript-config-watch-id".to_string(),
                    register_options: Some(lsproto::RegisterOptions {
                        workspace_did_change_configuration: Some(
                            lsproto::DidChangeConfigurationRegistrationOptions {
                                section: Some(lsproto::StringOrStrings {
                                    strings: Some(vec![
                                        "js/ts".to_string(),
                                        "typescript".to_string(),
                                        "javascript".to_string(),
                                        "editor".to_string(),
                                    ]),
                                    ..Default::default()
                                }),
                            },
                        ),
                        ..Default::default()
                    }),
                }]),
            }),
        )
        .map_err(|e| {
            Error::Message(format!("failed to register configuration change watcher: {e}"))
        })?;

        if let Some(options) = self
            .compiler_options_for_inferred_projects
            .lock()
            .unwrap()
            .clone()
        {
            self.session()
                .did_change_compiler_options_for_inferred_projects(ctx, options.clone());
        }

        self.session().start_performance_telemetry();

        if let Some(tx) = self.init_complete_tx.lock().unwrap().take() {
            let _ = tx.send(());
        }
        Ok(())
    }

    /// `s.handleShutdown`.
    pub(crate) fn handle_shutdown(
        self: &Arc<Self>,
        _ctx: &Context,
        _params: lsproto::NoParams,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::ShutdownResponse, Error> {
        if let Some(watcher) = self.builtin_watcher.lock().unwrap().take() {
            watcher.close();
        }
        self.close_api_sessions();
        if let Some(session) = self.session_opt() {
            session.close();
        }
        Ok(lsproto::Null::default())
    }

    /// `s.handleExit` — returns `io.EOF`.
    pub(crate) fn handle_exit(
        self: &Arc<Self>,
        _ctx: &Context,
        _params: lsproto::NoParams,
    ) -> Result<(), Error> {
        Err(Error::Eof)
    }

    /// `s.handleDidChangeWorkspaceConfiguration`.
    pub(crate) fn handle_did_change_workspace_configuration(
        self: &Arc<Self>,
        _ctx: &Context,
        params: Option<lsproto::DidChangeConfigurationParams>,
    ) -> Result<(), Error> {
        let params = params.unwrap_or_default();
        if params.settings.is_null() {
            return Ok(());
        }
        if let serde_json::Value::Object(settings) = params.settings {
            self.session().configure(lsutil::parse_user_preferences(&settings));
        }
        Ok(())
    }

    /// `s.handleDidOpen`.
    pub(crate) fn handle_did_open(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::DidOpenTextDocumentParams>,
    ) -> Result<(), Error> {
        let params = params.unwrap_or_default();
        let doc = params.text_document;
        self.session().did_open_file(
            ctx,
            doc.uri,
            doc.version,
            doc.text,
            doc.language_id,
        );
        Ok(())
    }

    /// `s.handleDidChange`.
    pub(crate) fn handle_did_change(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::DidChangeTextDocumentParams>,
    ) -> Result<(), Error> {
        let params = params.unwrap_or_default();
        self.session().did_change_file(
            ctx,
            params.text_document.uri,
            params.text_document.version,
            params.content_changes.unwrap_or_default(),
        );
        Ok(())
    }

    /// `s.handleDidSave`.
    pub(crate) fn handle_did_save(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::DidSaveTextDocumentParams>,
    ) -> Result<(), Error> {
        let params = params.unwrap_or_default();
        self.session().did_save_file(ctx, params.text_document.uri);
        Ok(())
    }

    /// `s.handleDidClose`.
    pub(crate) fn handle_did_close(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::DidCloseTextDocumentParams>,
    ) -> Result<(), Error> {
        let params = params.unwrap_or_default();
        self.session().did_close_file(ctx, params.text_document.uri);
        Ok(())
    }

    /// `s.handleDidChangeWatchedFiles`.
    pub(crate) fn handle_did_change_watched_files(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::DidChangeWatchedFilesParams>,
    ) -> Result<(), Error> {
        let params = params.unwrap_or_default();
        self.session()
            .did_change_watched_files(ctx, &params.changes.unwrap_or_default());
        Ok(())
    }

    /// `s.handleSetTrace` — intentional no-op (see Go comment).
    pub(crate) fn handle_set_trace(
        self: &Arc<Self>,
        _ctx: &Context,
        _params: Option<lsproto::SetTraceParams>,
    ) -> Result<(), Error> {
        Ok(())
    }

    /// `s.handleSetLogVerbosity`.
    pub(crate) fn handle_set_log_verbosity(
        self: &Arc<Self>,
        _ctx: &Context,
        params: Option<lsproto::SetLogVerbosityParams>,
    ) -> Result<(), Error> {
        let params = params.unwrap_or_default();
        if !is_valid_log_verbosity(params.verbosity) {
            return Err(Error::Coded(
                lsproto::ErrorCode::InvalidParams,
                format!("invalid log verbosity {}", params.verbosity),
            ));
        }
        self.logger.set_verbosity(params.verbosity);
        Ok(())
    }

    /// `s.handleDocumentDiagnostic`.
    pub(crate) fn handle_document_diagnostic(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::DocumentDiagnosticParams>,
    ) -> Result<lsproto::DocumentDiagnosticResponse, Error> {
        let params = params.unwrap_or_default();
        let ctx = with_checker_lifetime(ctx, CheckerLifetime::Diagnostics);
        if *self.flake_logging.lock().unwrap() == lsproto::DiagnosticFlakeLogLevel::Off {
            return Ok(language_service
                .provide_diagnostics(&ctx, params.text_document.uri)
                .map_err(Error::Ls)?);
        }
        let direct = language_service
            .provide_diagnostics(&ctx, params.text_document.uri.clone())
            .map_err(Error::Ls)?;
        // Emit, then re-check: a second pass must produce identical
        // diagnostics; a diff indicates nondeterminism (`flakeLogging`).
        let program = language_service.get_program();
        program.emit(
            ctx.clone(),
            &mut tsc_compiler::emit_host::EmitOptions {
                write_file: Some(Box::new(|_file, _text, _data| Ok(()))),
                ..Default::default()
            },
        );
        let secondary = language_service
            .provide_diagnostics(&ctx, params.text_document.uri.clone())
            .map_err(Error::Ls)?;
        let items_of = |r: &lsproto::DocumentDiagnosticResponse| -> Vec<&lsproto::Diagnostic> {
            r.full_document_diagnostic_report
                .as_ref()
                .and_then(|f| f.items.as_ref())
                .map(|v| v.iter().collect())
                .unwrap_or_default()
        };
        let (missing_from_pre, missing_from_post) =
            lsproto::compare_diagnostics(&items_of(&direct), &items_of(&secondary));
        if missing_from_pre.is_empty() && missing_from_post.is_empty() {
            return Ok(direct);
        }
        let diff = generate_diagnostic_diff_string(
            &missing_from_pre,
            &missing_from_post,
            lsproto::Diagnostic::as_string,
        );
        self.logger.error(format_args!("{diff}"));
        if self.telemetry_enabled.load(Ordering::SeqCst) {
            let sanitized = generate_diagnostic_diff_string(
                &missing_from_pre,
                &missing_from_post,
                |d| d.code_as_string(),
            );
            let _ = self.send_notification(
                &lsproto::TELEMETRY_EVENT_INFO,
                lsproto::TelemetryEvent {
                    request_failure_telemetry_event: Some(
                        lsproto::RequestFailureTelemetryEvent {
                            properties: Some(
                                lsproto::RequestFailureTelemetryProperties {
                                    error_code: lsproto::ErrorCode::InternalError.to_string(),
                                    request_method: "textDocument.diagnostic.flakeLog".to_string(),
                                    stack: sanitized,
                                },
                            ),
                            ..Default::default()
                        },
                    ),
                    ..Default::default()
                },
            );
        }
        if *self.flake_logging.lock().unwrap() == lsproto::DiagnosticFlakeLogLevel::Panic {
            panic!("flaky diagnostic(s) logged:\n{diff}");
        }
        Ok(direct)
    }

    /// `s.handleHover`.
    pub(crate) fn handle_hover(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::HoverParams>,
    ) -> Result<lsproto::HoverResponse, Error> {
        Ok(language_service
            .provide_hover(ctx, &params.unwrap_or_default())
            .map_err(Error::Ls)?)
    }

    /// `s.handlePrepareRename`.
    pub(crate) fn handle_prepare_rename(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::PrepareRenameParams>,
    ) -> Result<lsproto::PrepareRenameResponse, Error> {
        let params = params.unwrap_or_default();
        let info = language_service.get_rename_info(
            ctx,
            "",
            &params.text_document.uri,
            params.position,
        );
        if !info.can_rename {
            return Err(Error::UserFacing(info.localized_error_message));
        }
        Ok(lsproto::RangeOrPrepareRenamePlaceholderOrPrepareRenameDefaultBehaviorOrNull {
            prepare_rename_placeholder: Some(lsproto::PrepareRenamePlaceholder {
                range: info.trigger_span,
                placeholder: info.display_name,
            }),
            ..Default::default()
        })
    }

    /// `s.handleRename`.
    pub(crate) fn handle_rename(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::RenameParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::RenameResponse, Error> {
        let params = params.unwrap_or_default();
        let Some((sls, all_projects)) = self
            .get_language_service_and_orchestrator_parts(ctx, &params.text_document.uri)?
        else {
            return Ok(Default::default());
        };
        let language_service = sls.language_service();
        let info = language_service.get_rename_info(
            ctx,
            &params.new_name,
            &params.text_document.uri,
            params.position,
        );
        if info.can_rename && let Some(file_to_rename) = &info.file_to_rename {
            // Send a `willRenameFiles` request if the client supports it;
            // otherwise compute the edits for the file rename directly.
            let caps = lsproto::get_client_capabilities(ctx);
            let new_file_name = info.new_file_name.clone().unwrap_or_default();
            if caps.workspace.file_operations.will_rename {
                return Ok(lsproto::WorkspaceEditOrNull {
                    workspace_edit: Some(lsproto::WorkspaceEdit {
                        document_changes: Some(vec![
                            lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile {
                                rename_file: Some(lsproto::RenameFile {
                                    old_uri: lsconv::path_to_document_uri(file_to_rename),
                                    new_uri: lsconv::path_to_document_uri(&new_file_name),
                                    ..Default::default()
                                }),
                                ..Default::default()
                            },
                        ]),
                        ..Default::default()
                    }),
                });
            }
            let rename_files_params = lsproto::RenameFilesParams {
                files: Some(vec![lsproto::FileRename {
                    old_uri: lsconv::path_to_document_uri(file_to_rename),
                    new_uri: lsconv::path_to_document_uri(&new_file_name),
                }]),
            };
            return self.handle_will_rename_files_worker(ctx, &rename_files_params, true);
        }
        let orchestrator = ServerOrchestrator {
            server: self,
            snapshot: &sls.snapshot,
            default_project: sls.project.clone(),
            all_projects,
            known: std::cell::RefCell::new(HashMap::new()),
        };
        orchestrator.register_known();
        language_service
            .provide_rename(ctx, &params, Some(&orchestrator))
            .map_err(Error::Ls)
    }

    /// `s.handleWillRenameFiles`.
    pub(crate) fn handle_will_rename_files(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::RenameFilesParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::WillRenameFilesResponse, Error> {
        self.handle_will_rename_files_worker(ctx, &params.unwrap_or_default(), false)
    }

    /// `s.handleWillRenameFilesWorker` — `sendRenameFile` is true when a
    /// `rename` operation is being handled for a client without
    /// `willRenameFiles` support, so the file rename is included in the edits.
    pub(crate) fn handle_will_rename_files_worker(
        self: &Arc<Self>,
        ctx: &Context,
        params: &lsproto::RenameFilesParams,
        send_rename_file: bool,
    ) -> Result<lsproto::WillRenameFilesResponse, Error> {
        let files = params.files.clone().unwrap_or_default();
        if files.is_empty() {
            return Ok(Default::default());
        }
        let uris: Vec<lsproto::DocumentUri> =
            files.iter().map(|f| f.old_uri.clone()).collect();
        let (snapshot, projects) = self
            .session()
            .get_language_services_for_documents_loading_project_tree(ctx, &uris);

        #[derive(PartialEq)]
        struct EditKey {
            uri: lsproto::DocumentUri,
            range: lsproto::Range,
        }
        let mut seen_edits: Vec<(EditKey, String)> = Vec::new();
        let mut seen_renames: Set<lsproto::DocumentUri> = Set::new();
        let mut document_changes: Vec<
            lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile,
        > = Vec::new();
        for project in &projects {
            let Some(program) = project.get_program().cloned() else {
                continue;
            };
            let language_service = tsc_ls::languageservice::new_language_service(
                ls::autoimport::ProjectId(Rc::from(project.id.0.as_str())),
                program,
                &*snapshot,
                Default::default(),
            );
            for file in &files {
                for change in language_service.get_edits_for_file_rename(
                    ctx,
                    &file.old_uri,
                    &file.new_uri,
                ) {
                    if let Some(rename) = &change.rename_file {
                        if !seen_renames.has(&rename.old_uri) {
                            seen_renames.add(rename.old_uri.clone());
                            document_changes.push(change);
                        }
                    } else if let Some(edit) = &change.text_document_edit {
                        let uri = edit.text_document.uri.clone();
                        let mut deduped = Vec::new();
                        for text_edit in edit.edits.clone().unwrap_or_default() {
                            if let Some(te) = &text_edit.text_edit {
                                let key = EditKey {
                                    uri: uri.clone(),
                                    range: te.range.clone(),
                                };
                                if seen_edits
                                    .iter()
                                    .any(|(k, t)| *k == key && *t == te.new_text)
                                {
                                    continue;
                                }
                                seen_edits.push((key, te.new_text.clone()));
                            }
                            deduped.push(text_edit);
                        }
                        if !deduped.is_empty() {
                            document_changes.push(
                                lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile {
                                    text_document_edit: Some(lsproto::TextDocumentEdit {
                                        text_document: edit.text_document.clone(),
                                        edits: Some(deduped),
                                    }),
                                    ..Default::default()
                                },
                            );
                        }
                    }
                }
            }
        }
        if send_rename_file {
            for file in &files {
                document_changes.push(
                    lsproto::TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile {
                        rename_file: Some(lsproto::RenameFile {
                            old_uri: file.old_uri.clone(),
                            new_uri: file.new_uri.clone(),
                            ..Default::default()
                        }),
                        ..Default::default()
                    },
                );
            }
        }
        if document_changes.is_empty() {
            return Ok(Default::default());
        }
        let caps = lsproto::get_client_capabilities(ctx);
        if caps.workspace.workspace_edit.document_changes {
            return Ok(lsproto::WorkspaceEditOrNull {
                workspace_edit: Some(lsproto::WorkspaceEdit {
                    document_changes: Some(document_changes),
                    ..Default::default()
                }),
            });
        }
        let mut changes: BTreeMap<lsproto::DocumentUri, Vec<lsproto::TextEdit>> = BTreeMap::new();
        for change in &document_changes {
            if let Some(edit) = &change.text_document_edit {
                let uri = edit.text_document.uri.clone();
                for text_edit in edit.edits.clone().unwrap_or_default() {
                    if let Some(te) = text_edit.text_edit {
                        changes.entry(uri.clone()).or_default().push(te);
                    }
                }
            }
        }
        Ok(lsproto::WorkspaceEditOrNull {
            workspace_edit: Some(lsproto::WorkspaceEdit {
                changes: Some(changes),
                ..Default::default()
            }),
        })
    }

    /// `s.handleSignatureHelp`.
    pub(crate) fn handle_signature_help(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::SignatureHelpParams>,
    ) -> Result<lsproto::SignatureHelpResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_signature_help(
                ctx,
                params.text_document.uri,
                params.position,
                params.context.as_ref(),
            )
            .map_err(Error::Ls)?)
    }

    /// `s.handleFoldingRange`.
    pub(crate) fn handle_folding_range(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::FoldingRangeParams>,
    ) -> Result<lsproto::FoldingRangeResponse, Error> {
        Ok(language_service
            .provide_folding_range(ctx, params.unwrap_or_default().text_document.uri)
            .map_err(Error::Ls)?)
    }

    /// `s.handleVSOnAutoInsert`.
    pub(crate) fn handle_on_auto_insert(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::VSOnAutoInsertParams>,
    ) -> Result<lsproto::VSOnAutoInsertResponse, Error> {
        Ok(language_service
            .provide_on_auto_insert(ctx, &params.unwrap_or_default())
            .map_err(Error::Ls)?)
    }

    /// `s.handleLinkedEditingRange`.
    pub(crate) fn handle_linked_editing_range(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::LinkedEditingRangeParams>,
    ) -> Result<lsproto::LinkedEditingRangeResponse, Error> {
        Ok(language_service
            .provide_linked_editing_range(ctx, &params.unwrap_or_default())
            .map_err(Error::Ls)?)
    }

    /// `s.handleDefinition`.
    pub(crate) fn handle_definition(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::DefinitionParams>,
    ) -> Result<lsproto::DefinitionResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_definition(ctx, &params.text_document.uri, params.position)
            .map_err(Error::Ls)?)
    }

    /// `s.handleSourceDefinition`.
    pub(crate) fn handle_source_definition(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::TextDocumentPositionParams>,
    ) -> Result<lsproto::CustomTextDocumentSourceDefinitionResponse, Error> {
        let params = params.unwrap_or_default();
        let resp = language_service
            .provide_source_definition(ctx, &params.text_document.uri, params.position)
            .map_err(Error::Ls)?;
        Ok(Some(resp))
    }

    /// `s.handleTypeDefinition`.
    pub(crate) fn handle_type_definition(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::TypeDefinitionParams>,
    ) -> Result<lsproto::TypeDefinitionResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_type_definition(ctx, &params.text_document.uri, params.position)
            .map_err(Error::Ls)?)
    }

    /// `s.handleCompletion`.
    pub(crate) fn handle_completion(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::CompletionParams>,
    ) -> Result<lsproto::CompletionResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_completion(
                ctx,
                params.text_document.uri,
                params.position,
                params.context.as_ref(),
            )
            .map_err(Error::Ls)?)
    }

    /// `s.handleCompletionItemResolve`.
    pub(crate) fn handle_completion_item_resolve(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::CompletionItem>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::CompletionResolveResponse, Error> {
        let mut params = params.unwrap_or_default();
        let Some(data) = params.data.clone() else {
            return Err(Error::Message("completion item data is nil".to_string()));
        };
        let Some(file_name) = tspath::try_rooted_file_path_from_absolute(&data.file_name) else {
            return Err(Error::Message(
                "completion item data fileName must be absolute".to_string(),
            ));
        };
        let uri = if file_name.is_dynamic() {
            lsproto::try_dynamic_file_name_to_document_uri(&file_name.as_path()).ok_or_else(|| {
                Error::Message(
                    "completion item data fileName must be a valid dynamic path".to_string(),
                )
            })?
        } else {
            lsconv::file_name_to_document_uri(&file_name)
        };
        let sls = self
            .session()
            .get_language_service(ctx, &uri)
            .map_err(Error::from_session)?;
        let language_service = sls.language_service();
        language_service
            .resolve_completion_item(ctx, &mut params, &data, &file_name)
            .map_err(Error::Ls)?;
        Ok(Some(params))
    }

    /// `s.handleDocumentFormat`.
    pub(crate) fn handle_document_format(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::DocumentFormattingParams>,
    ) -> Result<lsproto::DocumentFormattingResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_format_document(ctx, params.text_document.uri, &params.options)
            .map_err(Error::Ls)?)
    }

    /// `s.handleDocumentRangeFormat`.
    pub(crate) fn handle_document_range_format(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::DocumentRangeFormattingParams>,
    ) -> Result<lsproto::DocumentRangeFormattingResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_format_document_range(
                ctx,
                params.text_document.uri,
                &params.options,
                params.range,
            )
            .map_err(Error::Ls)?)
    }

    /// `s.handleDocumentOnTypeFormat`.
    pub(crate) fn handle_document_on_type_format(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::DocumentOnTypeFormattingParams>,
    ) -> Result<lsproto::DocumentOnTypeFormattingResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_format_document_on_type(
                ctx,
                params.text_document.uri,
                &params.options,
                params.position,
                &params.ch,
            )
            .map_err(Error::Ls)?)
    }

    /// `s.handleWorkspaceSymbol`.
    pub(crate) fn handle_workspace_symbol(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::WorkspaceSymbolParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::WorkspaceSymbolResponse, Error> {
        let params = params.unwrap_or_default();
        let mut result: Result<lsproto::WorkspaceSymbolResponse, ls::Error> =
            Ok(Default::default());
        let current_project = params.text_document.is_some()
            && self.session().config().workspace_symbols_scope
                == lsutil::WorkspaceSymbolsScope::CURRENT_PROJECT;
        if let Some(uri) = current_project.then(|| params.text_document.as_ref().unwrap().uri.clone()) {
            self.session().with_snapshot_for_document(ctx, &uri, |snapshot| {
                let programs: Vec<Rc<tsc_compiler::program::Program>> = snapshot
                    .get_language_service_projects_containing_file(&uri)
                    .iter()
                    .filter_map(|p| p.get_program().cloned())
                    .collect();
                result = ls::provide_workspace_symbols(
                    ctx,
                    &programs,
                    &snapshot.converters(),
                    snapshot.user_preferences(),
                    &params.query,
                );
            });
        } else {
            self.session().with_snapshot_loading_project_tree(
                ctx,
                &Set::new(),
                |snapshot| {
                    let programs: Vec<Rc<tsc_compiler::program::Program>> = snapshot
                        .project_collection
                        .language_service_projects()
                        .iter()
                        .filter_map(|p| p.get_program().cloned())
                        .collect();
                    result = ls::provide_workspace_symbols(
                        ctx,
                        &programs,
                        &snapshot.converters(),
                        snapshot.user_preferences(),
                        &params.query,
                    );
                },
            );
        }
        result.map_err(Error::Ls)
    }

    /// `s.handleDocumentSymbol`.
    pub(crate) fn handle_document_symbol(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::DocumentSymbolParams>,
    ) -> Result<lsproto::DocumentSymbolResponse, Error> {
        Ok(language_service
            .provide_document_symbols(ctx, params.unwrap_or_default().text_document.uri)
            .map_err(Error::Ls)?)
    }

    /// `s.handleDocumentHighlight`.
    pub(crate) fn handle_document_highlight(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::DocumentHighlightParams>,
    ) -> Result<lsproto::DocumentHighlightResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_document_highlights(ctx, &params.text_document.uri, params.position)
            .map_err(Error::Ls)?)
    }

    /// `s.handleMultiDocumentHighlight`.
    pub(crate) fn handle_multi_document_highlight(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::MultiDocumentHighlightParams>,
    ) -> Result<lsproto::CustomMultiDocumentHighlightResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_multi_document_highlights(
                ctx,
                &params.text_document.uri,
                params.position,
                &params.files_to_search.unwrap_or_default(),
            )
            .map_err(Error::Ls)?)
    }

    /// `s.handleSelectionRange`.
    pub(crate) fn handle_selection_range(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::SelectionRangeParams>,
    ) -> Result<lsproto::SelectionRangeResponse, Error> {
        Ok(language_service
            .provide_selection_ranges(ctx, &params.unwrap_or_default())
            .map_err(Error::Ls)?)
    }

    /// `s.handleCodeAction`.
    pub(crate) fn handle_code_action(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::CodeActionParams>,
    ) -> Result<lsproto::CodeActionResponse, Error> {
        Ok(language_service
            .provide_code_actions(ctx, &params.unwrap_or_default())
            .map_err(Error::Ls)?)
    }

    /// `s.handleInlayHint`.
    pub(crate) fn handle_inlay_hint(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::InlayHintParams>,
    ) -> Result<lsproto::InlayHintResponse, Error> {
        Ok(language_service
            .provide_inlay_hint(ctx, &params.unwrap_or_default())
            .map_err(Error::Ls)?)
    }

    /// `s.handleCodeLens`.
    pub(crate) fn handle_code_lens(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::CodeLensParams>,
    ) -> Result<lsproto::CodeLensResponse, Error> {
        Ok(language_service
            .provide_code_lenses(ctx, &params.unwrap_or_default().text_document.uri)
            .map_err(Error::Ls)?)
    }

    /// `s.handleCodeLensResolve`.
    pub(crate) fn handle_code_lens_resolve(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::CodeLens>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::CodeLensResolveResponse, Error> {
        let mut code_lens = params.unwrap_or_default();
        let data = code_lens.data.clone().unwrap_or_default();
        let resolved = self.get_language_service_and_orchestrator_parts(ctx, &data.uri);
        if ctx.is_cancelled() {
            return Err(Error::Canceled);
        }
        let Some((sls, all_projects)) = resolved.ok().flatten() else {
            // `ErrorCodeContentModified` — the file could have been modified
            // or removed since `Data.Uri` was captured (see Go comment).
            return match resolved {
                Err(e) => Err(e),
                Ok(None) => Err(Error::Code(lsproto::ErrorCode::ContentModified)),
            };
        };
        let language_service = sls.language_service();
        let orchestrator = ServerOrchestrator {
            server: self,
            snapshot: &sls.snapshot,
            default_project: sls.project.clone(),
            all_projects,
            known: std::cell::RefCell::new(HashMap::new()),
        };
        orchestrator.register_known();
        language_service
            .resolve_code_lens(
                ctx,
                &mut code_lens,
                self.initialization_options
                    .get()
                    .and_then(|o| o.code_lens_show_locations_command_name.as_deref()),
                Some(&orchestrator),
            )
            .map_err(Error::Ls)?;
        Ok(Some(code_lens))
    }

    /// `s.handlePrepareCallHierarchy`.
    pub(crate) fn handle_prepare_call_hierarchy(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::CallHierarchyPrepareParams>,
    ) -> Result<lsproto::CallHierarchyPrepareResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_prepare_call_hierarchy(ctx, &params.text_document.uri, params.position)
            .map_err(Error::Ls)?)
    }

    /// `s.handleCallHierarchyIncomingCalls`.
    pub(crate) fn handle_call_hierarchy_incoming_calls(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::CallHierarchyIncomingCallsParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::CallHierarchyIncomingCallsResponse, Error> {
        let params = params.unwrap_or_default();
        let item = params.item.clone().unwrap_or_default();
        let Some((sls, all_projects)) = self
            .get_language_service_and_orchestrator_parts(ctx, &item.uri)?
        else {
            return Ok(Default::default());
        };
        let language_service = sls.language_service();
        let orchestrator = ServerOrchestrator {
            server: self,
            snapshot: &sls.snapshot,
            default_project: sls.project.clone(),
            all_projects,
            known: std::cell::RefCell::new(HashMap::new()),
        };
        orchestrator.register_known();
        Ok(language_service
            .provide_call_hierarchy_incoming_calls(ctx, &item, Some(&orchestrator))
            .map_err(Error::Ls)?)
    }

    /// `s.handleCallHierarchyOutgoingCalls`.
    pub(crate) fn handle_call_hierarchy_outgoing_calls(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::CallHierarchyOutgoingCallsParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::CallHierarchyOutgoingCallsResponse, Error> {
        let params = params.unwrap_or_default();
        let item = params.item.clone().unwrap_or_default();
        let sls = self
            .session()
            .get_language_service(ctx, &item.uri)
            .map_err(Error::from_session)?;
        let language_service = sls.language_service();
        Ok(language_service
            .provide_call_hierarchy_outgoing_calls(ctx, &item)
            .map_err(Error::Ls)?)
    }

    /// `s.handleSemanticTokensFull`.
    pub(crate) fn handle_semantic_tokens_full(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::SemanticTokensParams>,
    ) -> Result<lsproto::SemanticTokensResponse, Error> {
        Ok(language_service
            .provide_semantic_tokens(ctx, params.unwrap_or_default().text_document.uri)
            .map_err(Error::Ls)?)
    }

    /// `s.handleSemanticTokensRange`.
    pub(crate) fn handle_semantic_tokens_range(
        self: &Arc<Self>,
        ctx: &Context,
        language_service: &tsc_ls::languageservice::LanguageService<'_>,
        params: Option<lsproto::SemanticTokensRangeParams>,
    ) -> Result<lsproto::SemanticTokensRangeResponse, Error> {
        let params = params.unwrap_or_default();
        Ok(language_service
            .provide_semantic_tokens_range(ctx, params.text_document.uri, params.range)
            .map_err(Error::Ls)?)
    }

    /// `s.handleRunGC`.
    pub(crate) fn handle_run_gc(
        self: &Arc<Self>,
        _ctx: &Context,
        _params: lsproto::NoParams,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::RunGCResponse, Error> {
        tsc_pprof::run_gc();
        self.logger.info(format_args!("GC triggered"));
        Ok(lsproto::Null::default())
    }

    /// `s.handleSaveHeapProfile`.
    pub(crate) fn handle_save_heap_profile(
        self: &Arc<Self>,
        _ctx: &Context,
        params: Option<lsproto::ProfileParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::SaveHeapProfileResponse, Error> {
        let file_path = tsc_pprof::save_heap_profile(&params.unwrap_or_default().dir)
            .map_err(Error::Message)?;
        self.logger
            .info(format_args!("Heap profile saved to: {file_path}"));
        Ok(Some(lsproto::ProfileResult { file: file_path }))
    }

    /// `s.handleSaveAllocProfile`.
    pub(crate) fn handle_save_alloc_profile(
        self: &Arc<Self>,
        _ctx: &Context,
        params: Option<lsproto::ProfileParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::SaveAllocProfileResponse, Error> {
        let file_path = tsc_pprof::save_alloc_profile(&params.unwrap_or_default().dir)
            .map_err(Error::Message)?;
        self.logger
            .info(format_args!("Allocation profile saved to: {file_path}"));
        Ok(Some(lsproto::ProfileResult { file: file_path }))
    }

    /// `s.handleStartCPUProfile`.
    pub(crate) fn handle_start_cpu_profile(
        self: &Arc<Self>,
        _ctx: &Context,
        params: Option<lsproto::ProfileParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::StartCPUProfileResponse, Error> {
        self.cpu_profiler
            .start_cpu_profile(&params.unwrap_or_default().dir)
            .map_err(Error::Message)?;
        self.logger.info(format_args!(
            "CPU profiling started, will save to: {}",
            params.unwrap_or_default().dir
        ));
        Ok(lsproto::Null::default())
    }

    /// `s.handleStopCPUProfile`.
    pub(crate) fn handle_stop_cpu_profile(
        self: &Arc<Self>,
        _ctx: &Context,
        _params: lsproto::NoParams,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::StopCPUProfileResponse, Error> {
        let file_path = self.cpu_profiler.stop_cpu_profile().map_err(Error::Message)?;
        self.logger
            .info(format_args!("CPU profile saved to: {file_path}"));
        Ok(Some(lsproto::ProfileResult { file: file_path }))
    }

    /// `s.handleInitializeAPISession`.
    pub(crate) fn handle_initialize_api_session(
        self: &Arc<Self>,
        _ctx: &Context,
        params: Option<lsproto::InitializeAPISessionParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::CustomInitializeAPISessionResponse, Error> {
        let api_session = tsc_api::session::new_lsp_session(&self.session(), None);
        // Use the provided pipe path or generate a unique one.
        let pipe_path = match params.and_then(|p| p.pipe) {
            Some(p) if !p.is_empty() => p,
            _ => Server::generate_api_pipe_path(),
        };
        let transport = ipc::new_pipe_transport(&pipe_path).map_err(|e| {
            Error::Message(format!("failed to create API transport: {e}"))
        })?;
        let (api_ctx, api_cancel) = self.background_ctx.with_cancel();
        let (done_tx, done_rx) = mpsc::channel(1);
        let state = Arc::new(ApiSessionState {
            session: api_session,
            transport: Arc::new(transport),
            cancel: api_cancel.clone(),
            done: Mutex::new(Some(done_rx)),
            inner: Mutex::new(Default::default()),
        });
        let id = state.session.id().to_string();
        self.api_sessions
            .lock()
            .unwrap()
            .insert(id.clone(), state.clone());
        let s = self.clone();
        let state2 = state.clone();
        std::thread::spawn(move || {
            let _guard = scopeguard(&api_cancel, &s, &state2, id.clone(), done_tx);
            #[cfg(unix)]
            {
                let rwc = match state2.transport.accept() {
                    Ok(r) => r,
                    Err(e) => {
                        s.logger.error(format_args!(
                            "API session {id}: failed to accept connection: {e}"
                        ));
                        return;
                    }
                };
                let _ = state2.transport.close();
                if !state2.attach_connection(rwc.clone()) {
                    return;
                }
                let rwc2 = rwc.clone();
                let result = catch_unwind(AssertUnwindSafe(|| {
                    let conn = Arc::new(ipc::new_async_conn(
                        rwc,
                        state2.session.clone() as Arc<dyn ipc::Handler>,
                    ));
                    state2.session.set_connection(conn.clone());
                    if let Err(e) = conn.run(&api_ctx) {
                        s.logger
                            .error(format_args!("API session {id}: {e}"));
                    }
                }));
                if let Err(payload) = result {
                    let stack = std::backtrace::Backtrace::force_capture();
                    s.logger.error(format_args!(
                        "API session {id}: panic: {}\n{stack}",
                        crate::server::panic_payload_string(payload.as_ref())
                    ));
                    api_cancel.cancel();
                    let _ = ipc::IoClose::close(&*rwc2);
                }
            }
            #[cfg(not(unix))]
            {
                let _ = state2.transport.accept();
            }
        });
        Ok(Some(lsproto::InitializeAPISessionResult {
            session_id: id,
            pipe: pipe_path,
        }))
    }

    /// `s.handleProjectInfo`.
    pub(crate) fn handle_project_info(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::ProjectInfoParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::CustomProjectInfoResponse, Error> {
        let params = params.unwrap_or_default();
        let (sls, _all_projects) = self
            .session()
            .get_language_service_and_projects_for_file(ctx, &params.text_document.uri)
            .map_err(Error::from_session)?;
        let config_file_path = if sls.project.kind == project::project::Kind::Configured {
            sls.project.config_file_name().as_string().to_string()
        } else {
            String::new()
        };
        Ok(Some(lsproto::ProjectInfoResult {
            config_file_path,
        }))
    }

    /// `s.handleSetContentMapperContributions`.
    pub(crate) fn handle_set_content_mapper_contributions(
        self: &Arc<Self>,
        ctx: &Context,
        params: Option<lsproto::SetContentMapperContributionsParams>,
        _req: &lsproto::RequestMessage,
    ) -> Result<lsproto::CustomSetContentMapperContributionsResponse, Error> {
        let params = params.unwrap_or_default();
        let contributions =
            parse_content_mapper_contributions(&params.contributions.unwrap_or_default())?;
        let documents: Vec<lsproto::DocumentUri> = params
            .open_documents
            .unwrap_or_default()
            .iter()
            .map(|d| d.uri.clone())
            .collect();
        self.session()
            .set_content_mapper_contributions(ctx, contributions, documents);
        Ok(lsproto::Null::default())
    }

    /// `s.getLanguageServiceAndCrossProjectOrchestrator` — sync part only;
    /// the caller builds the `LanguageService` + [`ServerOrchestrator`]
    /// inside its own scope (Rust borrows the snapshot for `'h`).
    ///
    /// Returns `Ok(None)` as a stand-in for Go's `nil` orchestrator when the
    /// session lookup fails — callers that Go returns the error for get the
    /// error via the `Err` case; `handleCodeLensResolve` maps `Ok(None)` to
    /// `ErrorCodeContentModified` per its Go comment.
    pub(crate) fn get_language_service_and_orchestrator_parts(
        self: &Arc<Self>,
        ctx: &Context,
        uri: &lsproto::DocumentUri,
    ) -> Result<
        Option<(project::session::SessionLanguageService, Vec<Rc<project::project::Project>>)>,
        Error,
    > {
        match self
            .session()
            .get_language_service_and_projects_for_file(ctx, uri)
        {
            Ok(v) => Ok(Some(v)),
            Err(e) => Err(Error::from_session(e)),
        }
    }

    /// `s.RequestConfiguration`.
    fn request_configuration(self: &Arc<Self>, ctx: &Context) -> Result<lsutil::UserPreferences, Error> {
        let caps = lsproto::get_client_capabilities(ctx);
        if !caps.workspace.configuration {
            if let Some(opts) = self.initialization_options.get()
                && let Some(user_prefs) = &opts.user_preferences
            {
                self.logger.logf(format_args!(
                    "received formatting options from initialization: {user_prefs:?}\n{user_prefs:?}",
                ));
                if let serde_json::Value::Object(config) = user_prefs {
                    let mut map = serde_json::Map::new();
                    map.insert(
                        "js/ts".to_string(),
                        serde_json::Value::Object(config.clone()),
                    );
                    return Ok(lsutil::parse_user_preferences(&map));
                }
            }
            return Ok(lsutil::new_default_user_preferences());
        }
        let configs: lsproto::ConfigurationResponse = self
            .send_client_request(
                ctx,
                &lsproto::WORKSPACE_CONFIGURATION_INFO,
                Some(lsproto::ConfigurationParams {
                    items: Some(vec![
                        lsproto::ConfigurationItem {
                            section: Some("js/ts".to_string()),
                            ..Default::default()
                        },
                        lsproto::ConfigurationItem {
                            section: Some("typescript".to_string()),
                            ..Default::default()
                        },
                        lsproto::ConfigurationItem {
                            section: Some("javascript".to_string()),
                            ..Default::default()
                        },
                        lsproto::ConfigurationItem {
                            section: Some("editor".to_string()),
                            ..Default::default()
                        },
                    ]),
                }),
            )
            .map_err(|e| Error::Message(format!("configure request failed: {e}")))?;
        let mut config_map = serde_json::Map::new();
        for (i, config) in configs.iter().enumerate() {
            match i {
                0 => config_map.insert("js/ts".to_string(), config.clone()),
                1 => config_map.insert("typescript".to_string(), config.clone()),
                2 => config_map.insert("javascript".to_string(), config.clone()),
                3 => config_map.insert("editor".to_string(), config.clone()),
                _ => None,
            };
        }
        self.logger.logf(format_args!(
            "received options from workspace/configuration request:\njs/ts: {:?}\n\ntypescript: {:?}\n\njavascript: {:?}\n\neditor: {:?}\n",
            config_map.get("js/ts"),
            config_map.get("typescript"),
            config_map.get("javascript"),
            config_map.get("editor"),
        ));
        Ok(lsutil::parse_user_preferences(&config_map))
    }

    /// `s.contentMapperSpawner`.
    fn content_mapper_spawner(self: &Arc<Self>) -> Option<Arc<dyn tsc_contentmapper::Spawner>> {
        self.spawn.clone()
    }

    /// `s.contentMapperLogger`.
    fn content_mapper_logger(self: &Arc<Self>) -> Option<tsc_contentmapper::Logger> {
        let weak = Arc::downgrade(self);
        Some(Arc::new(move |message: &str| {
            if let Some(s) = weak.upgrade()
                && s.logger.is_tracing()
            {
                s.logger.info(format_args!("{message}"));
            }
        }))
    }
}

/// `s.handleInitialized` goroutine teardown — `defer close(done)`,
/// `defer apiCancel()`, `defer { apiSession.Close(); removeAPISession }`.
fn scopeguard(
    api_cancel: &tsc_core::context::CancelFunc,
    s: &Arc<Server>,
    state: &Arc<ApiSessionState>,
    session_id: String,
    done_tx: mpsc::Sender<()>,
) -> impl Drop {
    struct Guard {
        api_cancel: tsc_core::context::CancelFunc,
        s: Arc<Server>,
        state: Arc<ApiSessionState>,
        session_id: String,
        done_tx: Option<mpsc::Sender<()>>,
    }
    impl Drop for Guard {
        fn drop(&mut self) {
            drop(self.done_tx.take());
            self.api_cancel.cancel();
            self.state.session.close();
            self.s.remove_api_session(&self.session_id);
        }
    }
    Guard {
        api_cancel: api_cancel.clone(),
        s: s.clone(),
        state: state.clone(),
        session_id,
        done_tx: Some(done_tx),
    }
}

/// `generateDiagnosticDiffString`.
fn generate_diagnostic_diff_string(
    missing_from_pre: &[&lsproto::Diagnostic],
    missing_from_post: &[&lsproto::Diagnostic],
    stringifier: impl Fn(&lsproto::Diagnostic) -> String,
) -> String {
    let mut b = String::new();
    for elem in missing_from_pre {
        b.push_str(&format!(
            "Diagnostic {} was present after emit but not before emit\n",
            stringifier(elem)
        ));
    }
    for elem in missing_from_post {
        b.push_str(&format!(
            "Diagnostic {} was present before emit but not after emit\n",
            stringifier(elem)
        ));
    }
    b
}

/// `parseContentMapperContributions`.
fn parse_content_mapper_contributions(
    values: &[lsproto::ContentMapperContribution],
) -> Result<ContentMapperContributions, Error> {
    let mut result = ContentMapperContributions::default();
    let mut claimed_extensions = Set::<String>::new();
    for (index, value) in values.iter().enumerate() {
        if value.contributor_id.is_empty() {
            return Err(Error::Message(
                "content mapper contribution requires a contributorId".to_string(),
            ));
        }
        let identity = format!("{}[{index}]", value.contributor_id);
        let mut valid_extensions = Vec::new();
        for extension in value.extensions.clone().unwrap_or_default() {
            if !is_valid_contributed_content_mapper_extension(&extension) {
                return Err(Error::Message(format!(
                    "content mapper contribution {identity:?} has invalid extension {extension:?}"
                )));
            }
            valid_extensions.push(extension);
        }
        let Some(inferred_project) = &value.inferred_project_contribution else {
            continue;
        };
        let manifest = inferred_project.manifest.clone().unwrap_or_default();
        if manifest.name.is_empty() || manifest.exec.as_ref().is_none_or(|e| e.is_empty()) {
            return Err(Error::Message(format!(
                "content mapper contribution {identity:?} requires a manifest name and exec"
            )));
        }
        for option in manifest.compiler_options.clone().unwrap_or_default() {
            if tsoptions::tsconfigparsing::command_line_compiler_options_map()
                .get_option_declaration_from_name(&option, false)
                .is_none()
            {
                return Err(Error::Message(format!(
                    "content mapper contribution {identity:?} requests unknown compiler option {option:?}"
                )));
            }
        }
        for extension in &valid_extensions {
            if !claimed_extensions.add_if_absent(extension.to_lowercase()) {
                return Err(Error::Message(format!(
                    "content mapper contributions both claim extension {extension:?}"
                )));
            }
            result.extensions.push(extension.clone());
        }
        let options = match &inferred_project.options {
            None => json::marshal(&serde_json::json!({}), &[])
                .map_err(|e| Error::Marshal(e.to_string()))?,
            Some(o) => json::marshal(o, &[]).map_err(|e| {
                Error::Message(format!(
                    "content mapper contribution {identity:?} has invalid options: {e}"
                ))
            })?,
        };
        let mut mapper = tsc_contentmapper::Mapper {
            package: identity.clone(),
            extensions: Some(valid_extensions),
            options: Some(
                serde_json::value::RawValue::from_string(
                    String::from_utf8(options).map_err(|e| Error::Marshal(e.to_string()))?,
                )
                .map_err(|e| Error::Marshal(e.to_string()))?,
            ),
            name: manifest.name,
            version: manifest.version.unwrap_or_default(),
            exec: manifest.exec,
            compiler_options: manifest.compiler_options,
            dynamic_config: manifest.dynamic_config.unwrap_or_default(),
            package_directory: Default::default(),
            contribution_id: identity.clone(),
        };
        if let Some(cwd) = &manifest.cwd {
            if !tspath::path_is_absolute(cwd) {
                return Err(Error::Message(format!(
                    "content mapper contribution {identity:?} has non-absolute cwd"
                )));
            }
            mapper.package_directory = tspath::rooted_directory_path_from_absolute(cwd);
        }
        result.mappers.push(Arc::new(mapper));
    }
    result.extensions.sort();
    Ok(result)
}

/// `isValidContributedContentMapperExtension`.
fn is_valid_contributed_content_mapper_extension(extension: &str) -> bool {
    if extension.len() <= 1
        || !extension.starts_with('.')
        || tspath::get_any_extension_from_path(
            &format!("file{extension}"),
            &[],
            tspath::CaseSensitivity::CaseSensitive,
        ) != extension
    {
        return false;
    }
    !tspath::ALL_SUPPORTED_EXTENSIONS_WITH_JSON
        .iter()
        .flat_map(|g| g.iter())
        .any(|native| native.eq_ignore_ascii_case(extension))
}
