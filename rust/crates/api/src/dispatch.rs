// Ported from tsc/internal/api/session.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// Request dispatch, batch handling, and notification entry points —
// Go's `HandleRequest` / `HandleNotification` / `handleBatchRequests` and
// friends. The method-name switch is a mechanical transcription of Go's
// `HandleRequest` dispatch table; handler bodies live in `handlers_*.rs`
// (one file per Go section), module resolution in `module_resolution.rs`,
// and the session lifecycle in `session.rs`.

use std::any::Any;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::Ordering;

use serde::Serialize;
use tsc_checker::checker_core::Checker;
use tsc_core as core_;
use tsc_compiler as compiler;
use tsc_ipc as ipc;
use tsc_json as json;

use crate::proto::*;
use crate::session::{BatchResponsePage, Session, DEFAULT_MAX_RESPONSE_BYTES_PER_PAGE};

type HandlerResult = Result<Option<ipc::ResponsePayload>, String>;

/// Marshals a serializable handler result into a JSON `ResponsePayload`.
/// `Option<T>` handlers return `None` for Go's nil pointer — serde writes
/// `null`, matching Go's `json.Marshal` of a nil `*T`.
fn marshal_result<T: Serialize>(result: Result<T, String>) -> HandlerResult {
    result
        .and_then(|v| ipc::marshal_params(&v).map_err(|e| e.to_string()))
        .map(|v| Some(ipc::ResponsePayload::Json(v)))
}

/// `isSourceFileResponseMethod` — methods whose binary `RawBinary` result
/// must be wrapped in a `SourceFileResponse` for non-msgpack transport.
fn is_source_file_response_method(method: &str) -> bool {
    matches!(
        method,
        "getSourceFile"
            | "getSourceFileByPath"
            | "createSourceFile"
            | "createSourceFileFromFile"
            | "getCachedSourceFile"
            | "getConfigSourceFile"
    )
}

impl ipc::Handler for Session {
    /// `(*Session).HandleRequest` — locale context, `echo`/`ping`
    /// shortcuts, param unmarshalling, then the method switch.
    fn handle_request(
        &self,
        ctx: &core_::context::Context,
        method: &str,
        params: Option<json::Value>,
    ) -> Result<Option<ipc::ResponsePayload>, Box<dyn std::error::Error + Send + Sync>> {
        let localized;
        let ctx = if let Some(with_locale) = self.with_locale.as_ref() {
            localized = with_locale(ctx.clone());
            &localized
        } else {
            ctx
        };

        // Simple methods that don't need param parsing.
        match method {
            "echo" => {
                // Return raw binary for msgpack protocol compatibility.
                let payload = params
                    .map(|v| v.get().as_bytes().to_vec())
                    .unwrap_or_default();
                return Ok(Some(if self.use_binary_responses {
                    ipc::ResponsePayload::Binary(payload)
                } else {
                    ipc::ResponsePayload::Json(
                        serde_json::value::to_raw_value(&serde_json::Value::from(
                            ipc::base64_std_encode(&payload),
                        ))
                        .map_err(|e| e.to_string())?,
                    )
                }));
            }
            "ping" => {
                return marshal_result::<String>(Ok("pong".to_string()))
                    .map_err(|e| e.into());
            }
            _ => {}
        }
        let payload_bytes = params.as_ref().map(|v| v.get().as_bytes()).unwrap_or(b"");
        let parsed = unmarshal_payload(method, payload_bytes)
            .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> {
                format!("{ERR_INVALID_REQUEST}: {e}").into()
            })?;

        self.dispatch_request(ctx, method, parsed)
            .map_err(|e| -> Box<dyn std::error::Error + Send + Sync> { e.into() })
    }

    /// `(*Session).HandleNotification` — Go's body is a TODO no-op.
    fn handle_notification(
        &self,
        _ctx: &core_::context::Context,
        _method: &str,
        _params: Option<json::Value>,
    ) -> Result<(), Box<dyn std::error::Error + Send + Sync>> {
        Ok(())
    }
}

impl Session {
    /// The `switch method` of `HandleRequest`.
    ///
    /// `parsed` is the `unmarshalers[method]` output — each arm downcasts
    /// it to that method's registered params type. A mismatch means the
    /// unmarshal table and this switch disagree, which is a bug, not a
    /// client error.
    fn dispatch_request(
        &self,
        ctx: &core_::context::Context,
        method: &str,
        parsed: Box<dyn Any>,
    ) -> HandlerResult {
        macro_rules! params {
            ($t:ty) => {
                parsed.downcast::<$t>().map_err(|_| {
                    format!("{ERR_INVALID_REQUEST}: internal params type mismatch for {method}")
                })?
            };
        }
        match method {
            "batchRequests" => {
                let p = params!(BatchRequestsParams);
                marshal_result(self.handle_batch_requests(&ctx, &*p))
            }
            "release" => {
                let p = params!(ReleaseParams);
                self.handle_release(&ctx, &*p)
            }
            "releaseSourceFile" => {
                let p = params!(ReleaseSourceFileParams);
                self.handle_release_source_file(&*p)
            }
            "retainSourceFile" => {
                let p = params!(RetainSourceFileParams);
                marshal_result(self.handle_retain_source_file(&*p))
            }
            "getCachedSourceFile" => {
                let p = params!(GetCachedSourceFileParams);
                self.handle_get_cached_source_file(&*p)
            }
            "getSymbolOfDeclaration" => {
                let p = params!(GetSymbolOfDeclarationParams);
                marshal_result(self.handle_get_symbol_of_declaration(&*p))
            }
            "initialize" => marshal_result(self.handle_initialize(&ctx)),
            "createSnapshot" => {
                let p = params!(CreateSnapshotParams);
                marshal_result(self.handle_create_snapshot(&ctx, &*p))
            }
            "updateSnapshot" => {
                let p = params!(UpdateSnapshotParams);
                marshal_result(self.handle_update_snapshot(&ctx, &*p))
            }
            "getCurrentLanguageServerSnapshot" => {
                let p = params!(GetCurrentLanguageServerSnapshotParams);
                marshal_result(self.handle_get_current_language_server_snapshot(&ctx, &*p))
            }
            "createModuleResolver" => {
                let p = params!(CreateModuleResolverParams);
                marshal_result(self.handle_create_module_resolver(&*p))
            }
            "releaseModuleResolver" => {
                let p = params!(ReleaseModuleResolverParams);
                self.handle_release_module_resolver(&*p)
            }
            "resolveModuleName" => {
                let p = params!(ResolveModuleNameParams);
                marshal_result(self.handle_resolve_module_name(&ctx, &*p))
            }
            "parseCommandLine" => {
                let p = params!(ParseCommandLineParams);
                marshal_result(self.handle_parse_command_line(&ctx, &*p))
            }
            "readConfigFile" => {
                let p = params!(ReadConfigFileParams);
                marshal_result(self.handle_read_config_file(&ctx, &*p))
            }
            "parseJsonConfigFileContent" => {
                let p = params!(ParseJsonConfigFileContentParams);
                marshal_result(self.handle_parse_json_config_file_content(&ctx, &*p))
            }
            "parseConfigFile" => {
                let p = params!(ParseConfigFileParams);
                marshal_result(self.handle_parse_config_file(&ctx, &*p))
            }
            "createBuildOrchestrator" => {
                let p = params!(CreateBuildOrchestratorParams);
                marshal_result(self.handle_create_build_orchestrator(&ctx, &*p))
            }
            "disposeBuildOrchestrator" => {
                let p = params!(DisposeBuildOrchestratorParams);
                self.handle_dispose_build_orchestrator(&ctx, &*p)
            }
            "build" => {
                let p = params!(BuildParams);
                marshal_result(self.handle_build(&ctx, &*p))
            }
            "buildReferences" => {
                let p = params!(BuildParams);
                marshal_result(self.handle_build_references(&ctx, &*p))
            }
            "cleanBuild" => {
                let p = params!(CleanBuildParams);
                marshal_result(self.handle_clean_build(&ctx, &*p))
            }
            "cleanReferences" => {
                let p = params!(CleanBuildParams);
                marshal_result(self.handle_clean_references(&ctx, &*p))
            }
            "createSourceFile" => {
                let p = params!(CreateSourceFileParams);
                self.handle_create_source_file(&ctx, &*p)
            }
            "createSourceFileFromFile" => {
                let p = params!(CreateSourceFileFromFileParams);
                self.handle_create_source_file_from_file(&ctx, &*p)
            }
            "transpileModule" => {
                let p = params!(TranspileParams);
                marshal_result(self.handle_transpile(&ctx, &*p, false))
            }
            "transpileModuleFromFile" => {
                let p = params!(TranspileFromFileParams);
                marshal_result(self.handle_transpile_from_file(&ctx, &*p, false))
            }
            "transpileDeclaration" => {
                let p = params!(TranspileParams);
                marshal_result(self.handle_transpile(&ctx, &*p, true))
            }
            "transpileDeclarationFromFile" => {
                let p = params!(TranspileFromFileParams);
                marshal_result(self.handle_transpile_from_file(&ctx, &*p, true))
            }
            "getDefaultProjectForFile" => {
                let p = params!(GetDefaultProjectForFileParams);
                marshal_result(self.handle_get_default_project_for_file(&ctx, &*p))
            }
            "getSourceFile" => {
                let p = params!(GetSourceFileParams);
                self.handle_get_source_file(&ctx, &*p)
            }
            "getSourceFileNames" => {
                let p = params!(GetSourceFileNamesParams);
                marshal_result(self.handle_get_source_file_names(&ctx, &*p))
            }
            "getSourceFileMetadata" => {
                let p = params!(GetSourceFileParams);
                marshal_result(self.handle_get_source_file_metadata(&ctx, &*p))
            }
            "getModeForUsageLocation" => {
                let p = params!(GetModeForUsageLocationParams);
                marshal_result(self.handle_get_mode_for_usage_location(&ctx, &*p))
            }
            "getModeForResolutionAtIndex" => {
                let p = params!(GetModeForResolutionAtIndexParams);
                marshal_result(self.handle_get_mode_for_resolution_at_index(&ctx, &*p))
            }
            "getResolvedModule" => {
                let p = params!(GetResolvedModuleParams);
                marshal_result(self.handle_get_resolved_module(&ctx, &*p))
            }
            "getResolvedModuleFromModuleSpecifier" => {
                let p = params!(GetResolvedModuleFromModuleSpecifierParams);
                marshal_result(self.handle_get_resolved_module_from_module_specifier(&ctx, &*p))
            }
            "getResolvedTypeReferenceDirective" => {
                let p = params!(GetResolvedTypeReferenceDirectiveParams);
                marshal_result(self.handle_get_resolved_type_reference_directive(&ctx, &*p))
            }
            "getResolvedTypeReferenceDirectiveFromTypeReferenceDirective" => {
                let p = params!(GetResolvedTypeReferenceDirectiveFromReferenceParams);
                marshal_result(self.handle_get_resolved_type_reference_directive_from_reference(&ctx, &*p))
            }
            "getConfigFileNames" => {
                let p = params!(GetProjectDiagnosticsParams);
                marshal_result(self.handle_get_config_file_names(&ctx, &*p))
            }
            "getConfigSourceFile" => {
                let p = params!(GetSourceFileParams);
                self.handle_get_config_source_file(&ctx, &*p)
            }
            "getSymbolAtPosition" => {
                let p = params!(GetSymbolAtPositionParams);
                marshal_result(self.handle_get_symbol_at_position(&ctx, &*p))
            }
            "getSymbolsAtPositions" => {
                let p = params!(GetSymbolsAtPositionsParams);
                marshal_result(self.handle_get_symbols_at_positions(&ctx, &*p))
            }
            "getSymbolAtLocation" => {
                let p = params!(GetSymbolAtLocationParams);
                marshal_result(self.handle_get_symbol_at_location(&ctx, &*p))
            }
            "getSymbolsAtLocations" => {
                let p = params!(GetSymbolsAtLocationsParams);
                marshal_result(self.handle_get_symbols_at_locations(&ctx, &*p))
            }
            "getSymbolOfSourceFile" => {
                let p = params!(GetSymbolOfSourceFileParams);
                marshal_result(self.handle_get_symbol_of_source_file(&ctx, &*p))
            }
            "getSymbolsOfSourceFiles" => {
                let p = params!(GetSymbolsOfSourceFilesParams);
                marshal_result(self.handle_get_symbols_of_source_files(&ctx, &*p))
            }
            "getTypeOfSymbol" => {
                let p = params!(GetTypeOfSymbolParams);
                marshal_result(self.handle_get_type_of_symbol(&ctx, &*p))
            }
            "getTypesOfSymbols" => {
                let p = params!(GetTypesOfSymbolsParams);
                marshal_result(self.handle_get_types_of_symbols(&ctx, &*p))
            }
            "getDeclaredTypeOfSymbol" => {
                let p = params!(GetTypeOfSymbolParams);
                marshal_result(self.handle_get_declared_type_of_symbol(&ctx, &*p))
            }
            "getNonMissingTypeOfSymbol" => {
                let p = params!(GetTypeOfSymbolParams);
                marshal_result(self.handle_get_non_missing_type_of_symbol(&ctx, &*p))
            }
            "resolveName" => {
                let p = params!(ResolveNameParams);
                marshal_result(self.handle_resolve_name(&ctx, &*p))
            }
            "getSymbolsInScope" => {
                let p = params!(GetSymbolsInScopeParams);
                marshal_result(self.handle_get_symbols_in_scope(&ctx, &*p))
            }
            "getSignaturesOfType" => {
                let p = params!(GetSignaturesOfTypeParams);
                marshal_result(self.handle_get_signatures_of_type(&ctx, &*p))
            }
            "getResolvedSignature" => {
                let p = params!(GetResolvedSignatureParams);
                marshal_result(self.handle_get_resolved_signature(&ctx, &*p))
            }
            "getTypeAtLocation" => {
                let p = params!(GetTypeAtLocationParams);
                marshal_result(self.handle_get_type_at_location(&ctx, &*p))
            }
            "getTypeAtLocations" => {
                let p = params!(GetTypeAtLocationsParams);
                marshal_result(self.handle_get_type_at_locations(&ctx, &*p))
            }
            "getTypeAtPosition" => {
                let p = params!(GetTypeAtPositionParams);
                marshal_result(self.handle_get_type_at_position(&ctx, &*p))
            }
            "getTypesAtPositions" => {
                let p = params!(GetTypesAtPositionsParams);
                marshal_result(self.handle_get_types_at_positions(&ctx, &*p))
            }
            "getParentOfSymbol" => {
                let p = params!(GetSymbolPropertyParams);
                marshal_result(self.handle_get_parent_of_symbol(&ctx, &*p))
            }
            "getMembersOfSymbol" => {
                let p = params!(GetSymbolPropertyParams);
                marshal_result(self.handle_get_members_of_symbol(&ctx, &*p))
            }
            "getExportsOfSymbol" => {
                let p = params!(GetSymbolPropertyParams);
                marshal_result(self.handle_get_exports_of_symbol(&ctx, &*p))
            }
            "getExportSymbolOfSymbol" => {
                let p = params!(GetSymbolPropertyParams);
                marshal_result(self.handle_get_export_symbol_of_symbol(&ctx, &*p))
            }
            "getSymbolOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_symbol_of_type(&ctx, &*p))
            }
            "getTargetOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_target_of_type(&ctx, &*p))
            }
            "getFreshTypeOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_fresh_type_of_type(&ctx, &*p))
            }
            "getRegularTypeOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_regular_type_of_type(&ctx, &*p))
            }
            "getTypesOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_types_of_type(&ctx, &*p))
            }
            "getTypeParametersOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_type_parameters_of_type(&ctx, &*p))
            }
            "getOuterTypeParametersOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_outer_type_parameters_of_type(&ctx, &*p))
            }
            "getLocalTypeParametersOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_local_type_parameters_of_type(&ctx, &*p))
            }
            "getThisTypeOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_this_type_of_type(&ctx, &*p))
            }
            "getAliasTypeArgumentsOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_alias_type_arguments_of_type(&ctx, &*p))
            }
            "getAliasSymbolOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_alias_symbol_of_type(&ctx, &*p))
            }
            "getObjectTypeOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_object_type_of_type(&ctx, &*p))
            }
            "getIndexTypeOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_index_type_of_type(&ctx, &*p))
            }
            "getCheckTypeOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_check_type_of_type(&ctx, &*p))
            }
            "getExtendsTypeOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_extends_type_of_type(&ctx, &*p))
            }
            "getBaseTypeOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_base_type_of_type(&ctx, &*p))
            }
            "getConstraintOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_constraint_of_type(&ctx, &*p))
            }
            "getTypeParameterOfMappedType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_type_parameter_of_mapped_type(&ctx, &*p))
            }
            "getConstraintTypeOfMappedType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_constraint_type_of_mapped_type(&ctx, &*p))
            }
            "getNameTypeOfMappedType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_name_type_of_mapped_type(&ctx, &*p))
            }
            "getTemplateTypeOfMappedType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_template_type_of_mapped_type(&ctx, &*p))
            }
            "getTrueTypeOfConditionalType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_true_type_of_conditional_type(&ctx, &*p))
            }
            "getFalseTypeOfConditionalType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_false_type_of_conditional_type(&ctx, &*p))
            }
            "getTypeParametersOfSignature" => {
                let p = params!(GetSignaturePropertyParams);
                marshal_result(self.handle_get_type_parameters_of_signature(&ctx, &*p))
            }
            "getParametersOfSignature" => {
                let p = params!(GetSignaturePropertyParams);
                marshal_result(self.handle_get_parameters_of_signature(&ctx, &*p))
            }
            "getThisParameterOfSignature" => {
                let p = params!(GetSignaturePropertyParams);
                marshal_result(self.handle_get_this_parameter_of_signature(&ctx, &*p))
            }
            "getTargetOfSignature" => {
                let p = params!(GetSignaturePropertyParams);
                marshal_result(self.handle_get_target_of_signature(&ctx, &*p))
            }
            "getContextualType" => {
                let p = params!(GetContextualTypeParams);
                marshal_result(self.handle_get_contextual_type(&ctx, &*p))
            }
            "getContextualTypeForArgument" => {
                let p = params!(GetContextualTypeForArgumentParams);
                marshal_result(self.handle_get_contextual_type_for_argument(&ctx, &*p))
            }
            "getAwaitedType" => {
                let p = params!(CheckerTypeParams);
                marshal_result(self.handle_get_awaited_type(&ctx, &*p))
            }
            "getBaseTypeOfLiteralType" => {
                let p = params!(GetBaseTypeOfLiteralTypeParams);
                marshal_result(self.handle_get_base_type_of_literal_type(&ctx, &*p))
            }
            "getNonNullableType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_non_nullable_type(&ctx, &*p))
            }
            "getTypeFromTypeNode" => {
                let p = params!(GetTypeFromTypeNodeParams);
                marshal_result(self.handle_get_type_from_type_node(&ctx, &*p))
            }
            "getWidenedType" => {
                let p = params!(GetWidenedTypeParams);
                marshal_result(self.handle_get_widened_type(&ctx, &*p))
            }
            "getParameterType" => {
                let p = params!(GetParameterTypeParams);
                marshal_result(self.handle_get_parameter_type(&ctx, &*p))
            }
            "getTypeParameterAtPosition" => {
                let p = params!(GetParameterTypeParams);
                marshal_result(self.handle_get_type_parameter_at_position(&ctx, &*p))
            }
            "isArrayLikeType" => {
                let p = params!(IsArrayLikeTypeParams);
                marshal_result(self.handle_is_array_like_type(&ctx, &*p))
            }
            "isTypeAssignableTo" => {
                let p = params!(IsTypeAssignableToParams);
                marshal_result(self.handle_is_type_assignable_to(&ctx, &*p))
            }
            "getShorthandAssignmentValueSymbol" => {
                let p = params!(GetTypeAtLocationParams);
                marshal_result(self.handle_get_shorthand_assignment_value_symbol(&ctx, &*p))
            }
            "getTypeOfSymbolAtLocation" => {
                let p = params!(GetTypeOfSymbolAtLocationParams);
                marshal_result(self.handle_get_type_of_symbol_at_location(&ctx, &*p))
            }
            "typeToTypeNode" => {
                let p = params!(TypeToTypeNodeParams);
                self.handle_type_to_type_node(&ctx, &*p)
            }
            "signatureToSignatureDeclaration" => {
                let p = params!(SignatureToSignatureDeclarationParams);
                self.handle_signature_to_signature_declaration(&ctx, &*p)
            }
            "typeToString" => {
                let p = params!(TypeToTypeNodeParams);
                self.handle_type_to_string(&ctx, &*p)
            }
            "printNode" => {
                let p = params!(PrintNodeParams);
                marshal_result(self.handle_print_node(&ctx, &*p))
            }
            "formatNodeForInsertion" => {
                let p = params!(FormatNodeForInsertionParams);
                marshal_result(self.handle_format_node_for_insertion(&ctx, &*p))
            }
            "emit" => {
                let p = params!(EmitParams);
                marshal_result(self.handle_emit(&ctx, &*p))
            }
            "emitToString" => {
                let p = params!(EmitParams);
                marshal_result(self.handle_emit_to_string(&ctx, &*p))
            }
            "getJavaScriptEmit" => {
                let p = params!(SelectedFilesEmitParams);
                marshal_result(self.handle_selected_files_emit(&ctx, &*p, compiler::emit_host::EmitOnly::Js))
            }
            "getDeclarationEmit" => {
                let p = params!(SelectedFilesEmitParams);
                marshal_result(self.handle_selected_files_emit(&ctx, &*p, compiler::emit_host::EmitOnly::Dts))
            }
            "isContextSensitive" => {
                let p = params!(GetContextualTypeParams);
                marshal_result(self.handle_is_context_sensitive(&ctx, &*p))
            }
            "getReturnTypeOfSignature" => {
                let p = params!(GetSignaturePropertyParams);
                marshal_result(self.handle_get_return_type_of_signature(&ctx, &*p))
            }
            "getRestTypeOfSignature" => {
                let p = params!(CheckerSignatureParams);
                marshal_result(self.handle_get_rest_type_of_signature(&ctx, &*p))
            }
            "getTypePredicateOfSignature" => {
                let p = params!(CheckerSignatureParams);
                marshal_result(self.handle_get_type_predicate_of_signature(&ctx, &*p))
            }
            "getBaseTypes" => {
                let p = params!(CheckerTypeParams);
                marshal_result(self.handle_get_base_types(&ctx, &*p))
            }
            "getPropertiesOfType" => {
                let p = params!(CheckerTypeParams);
                marshal_result(self.handle_get_properties_of_type(&ctx, &*p))
            }
            "getApparentPropertiesOfType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_apparent_properties_of_type(&ctx, &*p))
            }
            "getApparentType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_apparent_type(&ctx, &*p))
            }
            "getReducedType" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_reduced_type(&ctx, &*p))
            }
            "getPropertyOfType" => {
                let p = params!(GetPropertyOfTypeParams);
                marshal_result(self.handle_get_property_of_type(&ctx, &*p))
            }
            "getTypeOfPropertyOfType" => {
                let p = params!(GetPropertyOfTypeParams);
                marshal_result(self.handle_get_type_of_property_of_type(&ctx, &*p))
            }
            "getIndexInfoOfType" => {
                let p = params!(GetIndexInfoOfTypeParams);
                marshal_result(self.handle_get_index_info_of_type(&ctx, &*p))
            }
            "getIndexInfosOfType" => {
                let p = params!(CheckerTypeParams);
                marshal_result(self.handle_get_index_infos_of_type(&ctx, &*p))
            }
            "getConstraintOfTypeParameter" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_constraint_of_type_parameter(&ctx, &*p))
            }
            "getBaseConstraintOfType" => {
                let p = params!(CheckerTypeParams);
                marshal_result(self.handle_get_base_constraint_of_type(&ctx, &*p))
            }
            "getDefaultFromTypeParameter" => {
                let p = params!(GetTypePropertyParams);
                marshal_result(self.handle_get_default_from_type_parameter(&ctx, &*p))
            }
            "getTypeArguments" => {
                let p = params!(CheckerTypeParams);
                marshal_result(self.handle_get_type_arguments(&ctx, &*p))
            }
            "getImportAdderEdits" => {
                let p = params!(GetImportAdderEditsParams);
                marshal_result(self.handle_get_import_adder_edits(&ctx, &*p))
            }
            "getConstantValue" => {
                let p = params!(CheckerNodeParams);
                marshal_result(self.handle_get_constant_value(&ctx, &*p))
            }
            "getSignatureFromDeclaration" => {
                let p = params!(CheckerNodeParams);
                marshal_result(self.handle_get_signature_from_declaration(&ctx, &*p))
            }
            "getExportSpecifierLocalTargetSymbol" => {
                let p = params!(CheckerNodeParams);
                marshal_result(self.handle_get_export_specifier_local_target_symbol(&ctx, &*p))
            }
            "getAliasedSymbol" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_get_aliased_symbol(&ctx, &*p))
            }
            "getImmediateAliasedSymbol" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_get_immediate_aliased_symbol(&ctx, &*p))
            }
            "getTargetSymbol" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_method_get_target_symbol(&ctx, &*p))
            }
            "getMergedSymbol" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_get_merged_symbol(&ctx, &*p))
            }
            "getSymbolOfNode" => {
                let p = params!(CheckerNodeParams);
                marshal_result(self.handle_get_symbol_of_node(&ctx, &*p))
            }
            "getSymbolOfDeclarationForChecker" => {
                let p = params!(CheckerNodeParams);
                marshal_result(self.handle_get_symbol_of_declaration_for_checker(&ctx, &*p))
            }
            "getParentOfSymbolForChecker" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_get_parent_of_symbol_for_checker(&ctx, &*p))
            }
            "getExportSymbolOfSymbolForChecker" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_get_export_symbol_of_symbol_for_checker(&ctx, &*p))
            }
            "getFullyQualifiedName" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_get_fully_qualified_name(&ctx, &*p))
            }
            "getExportsOfModule" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_get_exports_of_module(&ctx, &*p))
            }
            "getMemberInModuleExports" => {
                let p = params!(GetMemberInModuleExportsParams);
                marshal_result(self.handle_get_member_in_module_exports(&ctx, &*p))
            }
            "getJsDocTags" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_get_js_doc_tags(&ctx, &*p))
            }
            "getDocumentationComment" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_get_documentation_comment(&ctx, &*p))
            }
            "isArrayType" => {
                let p = params!(CheckerTypeParams);
                marshal_result(self.handle_is_array_type(&ctx, &*p))
            }
            "isReadonlySymbol" => {
                let p = params!(CheckerSymbolParams);
                marshal_result(self.handle_is_readonly_symbol(&ctx, &*p))
            }
            "getAnyType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_any_type))
            }
            "getStringType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_string_type))
            }
            "getNumberType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_number_type))
            }
            "getBooleanType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_boolean_type))
            }
            "getVoidType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_void_type))
            }
            "getUndefinedType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_undefined_type))
            }
            "getNullType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_null_type))
            }
            "getNeverType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_never_type))
            }
            "getUnknownType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_unknown_type))
            }
            "getBigIntType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_big_int_type))
            }
            "getESSymbolType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_es_symbol_type))
            }
            "getNonPrimitiveType" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_intrinsic_type(&ctx, &*p, Checker::get_non_primitive_type))
            }
            "getWellKnownSymbols" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_well_known_symbols(&ctx, &*p))
            }
            "getWellKnownSignatures" => {
                let p = params!(GetIntrinsicTypeParams);
                marshal_result(self.handle_get_well_known_signatures(&ctx, &*p))
            }
            "getSyntacticDiagnostics" => {
                let p = params!(GetDiagnosticsParams);
                marshal_result(self.handle_get_syntactic_diagnostics(&ctx, &*p))
            }
            "getBindDiagnostics" => {
                let p = params!(GetDiagnosticsParams);
                marshal_result(self.handle_get_bind_diagnostics(&ctx, &*p))
            }
            "getSemanticDiagnostics" => {
                let p = params!(GetDiagnosticsParams);
                marshal_result(self.handle_get_semantic_diagnostics(&ctx, &*p))
            }
            "getSuggestionDiagnostics" => {
                let p = params!(GetDiagnosticsParams);
                marshal_result(self.handle_get_suggestion_diagnostics(&ctx, &*p))
            }
            "getDeclarationDiagnostics" => {
                let p = params!(GetDiagnosticsParams);
                marshal_result(self.handle_get_declaration_diagnostics(&ctx, &*p))
            }
            "getProgramDiagnostics" => {
                let p = params!(GetProjectDiagnosticsParams);
                marshal_result(self.handle_get_program_diagnostics(&ctx, &*p))
            }
            "getGlobalDiagnostics" => {
                let p = params!(GetProjectDiagnosticsParams);
                marshal_result(self.handle_get_global_diagnostics(&ctx, &*p))
            }
            "getConfigFileParsingDiagnostics" => {
                let p = params!(GetProjectDiagnosticsParams);
                marshal_result(self.handle_get_config_file_parsing_diagnostics(&ctx, &*p))
            }
            "startCPUProfile" => {
                let p = params!(ProfileParams);
                self.handle_start_cpu_profile(&ctx, &*p)
            }
            "stopCPUProfile" => marshal_result(self.handle_stop_cpu_profile(&ctx)),
            "saveHeapProfile" => {
                let p = params!(ProfileParams);
                marshal_result(self.handle_save_heap_profile(&ctx, &*p))
            }
            "getReferencesToSymbolInFile" => {
                let p = params!(GetReferencesToSymbolInFileParams);
                marshal_result(self.handle_get_references_to_symbol_in_file(&ctx, &*p))
            }
            "getReferencedSymbolsForNode" => {
                let p = params!(GetReferencedSymbolsForNodeParams);
                marshal_result(self.handle_get_referenced_symbols_for_node(&ctx, &*p))
            }
            "getSignatureUsages" => {
                let p = params!(GetSignatureUsagesParams);
                marshal_result(self.handle_get_signature_usages(&ctx, &*p))
            }
            "getCompletionsAtPosition" => {
                let p = params!(GetCompletionsAtPositionParams);
                marshal_result(self.handle_get_completions_at_position(&ctx, &*p))
            }
            _ => Err(format!("unknown method: {method}")),
        }
    }

    /// `handleBatchRequests`. Nested `batchRequests` are rejected
    /// per-item inside `handleBatchRequest`, same as Go — the outer call
    /// only forks on `continuationToken`.
    fn handle_batch_requests(
        &self,
        ctx: &core_::context::Context,
        params: &BatchRequestsParams,
    ) -> Result<BatchRequestsResponse, String> {
        if !params.continuation_token.is_empty() {
            let page = self
                .batch_response_pages
                .lock()
                .unwrap()
                .remove(&params.continuation_token);
            let Some(page) = page else {
                return Err(format!("{ERR_CLIENT_ERROR}: invalid batch continuation token"));
            };
            return self.paginate_batch_responses(page, None, params.max_response_bytes_per_page);
        }

        let responses: Vec<BatchResponse> = params
            .requests
            .iter()
            .map(|request| self.handle_batch_request(ctx, request))
            .collect();
        let page = new_batch_response_page(&responses)?;
        self.paginate_batch_responses(page, Some(responses), params.max_response_bytes_per_page)
    }

    /// `handleBatchRequest` — one batch item. Nested batches and panics
    /// land in the item's `error` field, not the outer error.
    fn handle_batch_request(
        &self,
        ctx: &core_::context::Context,
        request: &BatchRequest,
    ) -> BatchResponse {
        let method = request.method.as_str().to_string();
        if request.method.as_str() == "batchRequests" {
            return BatchResponse {
                method: request.method.clone(),
                result: serde_json::Value::Null,
                error: format!("{ERR_INVALID_REQUEST}: batchRequests cannot be nested"),
            };
        }

        let params = request.params.clone();
        let unwind = catch_unwind(AssertUnwindSafe(|| {
            <Self as ipc::Handler>::handle_request(self, ctx, &method, params)
        }));
        let (result, error) = match unwind {
            Err(payload) => {
                let msg = if let Some(s) = payload.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = payload.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "unknown panic".to_string()
                };
                (
                    None,
                    format!("panic: {msg}\n{}", std::backtrace::Backtrace::capture()),
                )
            }
            Ok(Err(e)) => (None, e.to_string()),
            Ok(Ok(r)) => (r, String::new()),
        };

        // Go marshals the `any` result; `RawBinary` inside a batch becomes
        // a base64 string, or a `SourceFileResponse` for source-file
        // methods (`isSourceFileResponseMethod`).
        let json_result = match result {
            None => serde_json::Value::Null,
            Some(ipc::ResponsePayload::Json(v)) => {
                serde_json::from_str(v.get()).unwrap_or(serde_json::Value::Null)
            }
            Some(ipc::ResponsePayload::Binary(data)) => {
                if is_source_file_response_method(&method) {
                    if data.is_empty() {
                        serde_json::Value::Null
                    } else {
                        serde_json::to_value(SourceFileResponse {
                            data: ipc::base64_std_encode(&data),
                        })
                        .unwrap_or(serde_json::Value::Null)
                    }
                } else {
                    // `json.Marshal([]byte)` — a base64 string.
                    serde_json::Value::from(ipc::base64_std_encode(&data))
                }
            }
        };

        BatchResponse {
            method: request.method.clone(),
            result: json_result,
            error,
        }
    }

    /// `paginateBatchResponses` — walks the page's pre-encoded responses,
    /// accounting for the `{"responses":[...]}` wrapper, comma separators,
    /// and the continuation-token field itself. `responses` is `Some` on
    /// the first page (so `responses[:pageLength]` can be returned) and
    /// `None` on continuations.
    fn paginate_batch_responses(
        &self,
        page: BatchResponsePage,
        responses: Option<Vec<BatchResponse>>,
        max_response_bytes_per_page: i64,
    ) -> Result<BatchRequestsResponse, String> {
        let mut max_response_bytes_per_page = max_response_bytes_per_page;
        if max_response_bytes_per_page <= 0 {
            max_response_bytes_per_page = DEFAULT_MAX_RESPONSE_BYTES_PER_PAGE as i64;
        }
        let max = max_response_bytes_per_page as usize;

        let mut encoded_length = r#"{"responses":[]}"#.len();
        let mut page_length = 0;
        for encoded in &page.encoded_responses {
            let mut additional_length = encoded.get().len();
            if page_length > 0 {
                additional_length += 1;
            }
            if page_length > 0 && encoded_length + additional_length > max {
                break;
            }
            encoded_length += additional_length;
            page_length += 1;
        }

        if page_length == page.encoded_responses.len() {
            return Ok(BatchRequestsResponse {
                responses: responses.unwrap_or_default(),
                continuation_token: String::new(),
                encoded_responses: Some(page.encoded_responses),
            });
        }

        let continuation_token = format!(
            "{}-{}",
            self.id,
            self.next_batch_response_page_id.fetch_add(1, Ordering::SeqCst) + 1
        );
        let continuation_length = ",\"continuationToken\":\"\"".len() + continuation_token.len();
        while page_length > 1 && encoded_length + continuation_length > max {
            encoded_length -= page.encoded_responses[page_length - 1].get().len() + 1;
            page_length -= 1;
        }

        let mut encoded = page.encoded_responses;
        let remaining_responses = encoded.split_off(page_length);
        self.batch_response_pages.lock().unwrap().insert(
            continuation_token.clone(),
            BatchResponsePage {
                encoded_responses: remaining_responses,
            },
        );
        Ok(BatchRequestsResponse {
            responses: responses
                .map(|r| r.into_iter().take(page_length).collect())
                .unwrap_or_default(),
            continuation_token,
            encoded_responses: Some(encoded),
        })
    }
}

/// `newBatchResponsePage` — pre-encodes every `BatchResponse` so page
/// boundaries are computed on wire bytes, not struct sizes.
fn new_batch_response_page(responses: &[BatchResponse]) -> Result<BatchResponsePage, String> {
    let mut encoded_responses = Vec::with_capacity(responses.len());
    for response in responses {
        let encoded = serde_json::value::to_raw_value(response).map_err(|e| e.to_string())?;
        encoded_responses.push(encoded);
    }
    Ok(BatchResponsePage { encoded_responses })
}
