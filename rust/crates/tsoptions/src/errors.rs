// Ported from tsc/internal/tsoptions/errors.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_ast::diagnostic::{DiagnosticFile, DiagnosticRef, new_compiler_diagnostic, new_diagnostic};
use tsc_ast::{Node, NodeId};
use tsc_core::text::TextRange;
use tsc_diagnostics::{self as diagnostics, Message};
use tsc_scanner::scanner::skip_trivia;

use crate::commandlineoption::{CommandLineOptionKind, CommandLineOptionRef};
use crate::diagnostics::AlternateModeDiagnostics;
use crate::tsconfigparsing::{CommandLineOptionNameMap, SourceFileCtx};
use crate::value::Value;

/// `createDiagnosticForInvalidEnumType`.
pub fn create_diagnostic_for_invalid_enum_type(
    opt: CommandLineOptionRef,
    source_file: Option<SourceFileCtx<'_>>,
    node: Option<NodeId>,
) -> DiagnosticRef {
    let names_of_type: Vec<String> = opt
        .enum_map()
        .map(|m| m.keys().cloned().collect())
        .unwrap_or_default();
    let string_names = format_enum_type_keys(opt, &names_of_type);
    let opt_name = format!("--{}", opt.name);
    create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
        source_file,
        node,
        &diagnostics::Argument_for_0_option_must_be_Colon_1,
        &[Value::Str(opt_name), Value::Str(string_names)],
    )
}

/// `formatEnumTypeKeys`.
pub fn format_enum_type_keys(opt: CommandLineOptionRef, keys: &[String]) -> String {
    let mut keys = keys.to_vec();
    if let Some(deprecated) = opt.deprecated_keys() {
        keys.retain(|key| !deprecated.has(key));
    }
    format!("'{}'", keys.join("', '"))
}

/// `getCompilerOptionValueTypeString`.
pub fn get_compiler_option_value_type_string(option: CommandLineOptionRef) -> String {
    match option.kind {
        CommandLineOptionKind::ListOrElement => {
            format!(
                "{} or Array",
                get_compiler_option_value_type_string(option.elements().unwrap())
            )
        }
        CommandLineOptionKind::List => "Array".to_string(),
        _ => option.kind.as_str().to_string(),
    }
}

/// `createUnknownOptionError` — creates a diagnostic for an unknown option.
/// If `unknown_did_you_mean_diagnostic` and `options_name_map` are provided,
/// it also checks for a spelling suggestion and emits a "did you mean"
/// diagnostic instead.
pub fn create_unknown_option_error(
    unknown_option: &str,
    unknown_option_diagnostic: &'static Message,
    unknown_option_error_text: &str,                   // optional
    node: Option<NodeId>,                              // optional
    source_file: Option<SourceFileCtx<'_>>,            // optional
    alternate_mode: Option<&AlternateModeDiagnostics>, // optional
    unknown_did_you_mean_diagnostic: Option<&'static Message>, // optional; None skips suggestion
    options_name_map: Option<&CommandLineOptionNameMap>, // optional; None skips suggestion
) -> DiagnosticRef {
    if let Some(alternate_mode) = alternate_mode {
        let options_name_map = (alternate_mode.options_name_map)();
        if let Some(other_option) = options_name_map.get(&unknown_option.to_lowercase()) {
            // tscbuildoption
            let diagnostic = if other_option.name == "build" {
                &diagnostics::Option_build_must_be_the_first_command_line_argument
            } else {
                alternate_mode.diagnostic
            };
            return create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                source_file,
                node,
                diagnostic,
                &[Value::Str(unknown_option.to_string())],
            );
        }
    }
    let unknown_option_error_text = if unknown_option_error_text.is_empty() {
        unknown_option
    } else {
        unknown_option_error_text
    };
    if let (Some(did_you_mean), Some(name_map)) =
        (unknown_did_you_mean_diagnostic, options_name_map)
    {
        if let Some(possible_option) =
            crate::tsconfigparsing::name_map_get_spelling_suggestion(name_map, unknown_option)
        {
            return create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
                source_file,
                node,
                did_you_mean,
                &[
                    Value::Str(unknown_option_error_text.to_string()),
                    Value::Str(possible_option.name.to_string()),
                ],
            );
        }
    }
    create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
        source_file,
        node,
        unknown_option_diagnostic,
        &[Value::Str(unknown_option_error_text.to_string())],
    )
}

/// `CreateDiagnosticForNodeInSourceFile`.
///
/// PORT: `sourceFile`/`node` are `NodeId`s resolved through the arena
/// (`SourceFileCtx` bundles both).
pub fn create_diagnostic_for_node_in_source_file(
    source_file: SourceFileCtx<'_>,
    node: NodeId,
    message: &'static Message,
    args: &[Value],
) -> DiagnosticRef {
    let file_node = source_file.nodes[source_file.file].as_source_file();
    let text = file_node.text();
    let n: &Node = &source_file.nodes[node];
    new_diagnostic(
        Some(DiagnosticFile::from_node(
            source_file.file,
            source_file.nodes,
        )),
        TextRange::new(skip_trivia(text, n.pos()), n.end()),
        message,
        args,
    )
}

/// `CreateDiagnosticForNodeInSourceFileOrCompilerDiagnostic`.
pub fn create_diagnostic_for_node_in_source_file_or_compiler_diagnostic(
    source_file: Option<SourceFileCtx<'_>>,
    node: Option<NodeId>,
    message: &'static Message,
    args: &[Value],
) -> DiagnosticRef {
    if let (Some(sf), Some(node)) = (source_file, node) {
        return create_diagnostic_for_node_in_source_file(sf, node, message, args);
    }
    new_compiler_diagnostic(message, args)
}

/// `extraKeyDiagnostics`.
pub fn extra_key_diagnostics(s: &str) -> Option<&'static Message> {
    match s {
        "compilerOptions" => Some(&diagnostics::Unknown_compiler_option_0),
        "typeAcquisition" => Some(&diagnostics::Unknown_type_acquisition_option_0),
        "buildOptions" => Some(&diagnostics::Unknown_build_option_0),
        _ => None,
    }
}

/// `extraKeyDidYouMeanDiagnostics`.
pub fn extra_key_did_you_mean_diagnostics(s: &str) -> Option<&'static Message> {
    match s {
        "compilerOptions" => Some(&diagnostics::Unknown_compiler_option_0_Did_you_mean_1),
        "typeAcquisition" => Some(&diagnostics::Unknown_type_acquisition_option_0_Did_you_mean_1),
        "buildOptions" => Some(&diagnostics::Unknown_build_option_0_Did_you_mean_1),
        _ => None,
    }
}
