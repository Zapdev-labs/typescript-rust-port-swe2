// Ported from tsc/internal/ls/signaturehelp.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*ast.Node` → `NodeId`; `*ast.Symbol` → `SymbolId`; `*checker.Type` →
//   `TypeId`; `*checker.Signature` → `SignatureId`; `*checker.Checker` →
//   `Rc<RefCell<Checker>>`; `*ast.NodeList` → `Option<NodeList>`.
// - `argumentListInfo.invocation` is `*invocation` in Go; exactly one of the
//   three fields is set, kept as three `Option`s (see `Invocation` below) for
//   compatibility with `completions.rs`.
// - `nodes_mut` guards are taken in short scopes only and are never held
//   across node-builder/printer calls, which mint nodes through an arena
//   checkout.

use std::cell::RefCell;
use std::rc::Rc;

use rustc_hash::FxHashMap;
use tsc_ast::{self as ast, Kind, Node, NodeId, NodeList, SymbolId};
use tsc_checker::checker_types as checker_types;
use tsc_checker::checker_core::Checker;
use tsc_checker::nodebuilder::NodeBuilder;
use tsc_checker::types::{
    ContextFlags, SignatureId, SignatureKind, SymbolFormatFlags, TypeId,
};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::options_generated::NewLineKind;
use tsc_core::text::{TextPos, TextRange};
use tsc_debug as debug;
use tsc_lsproto::{self as lsproto};
use tsc_nodebuilder as nodebuilder;
use tsc_printer::{EmitContext, EmitTextWriter, PrintHandlers, Printer, PrinterOptions};
use tsc_scanner::scanner::{Scanner, skip_trivia, token_to_string};
use tsc_spanmap::Feature;

use crate::api::Error;
use crate::displaypartswriter::{DisplayPartsWriter, new_display_parts_writer};
use crate::hover::get_documentation_from_declaration;
use crate::languageservice::LanguageService;
use crate::utilities::{
    find_containing_list, get_children_from_non_jsdoc_node, get_possible_generic_signatures,
    get_possible_type_arguments_info, is_in_comment, is_in_string, is_inside_template_literal,
    is_no_substitution_template_literal, is_tagged_template_expression, is_template_head,
    is_template_tail, range_contains_range,
};

/// `signatureHelpNodeBuilderFlags`.
fn signature_help_node_builder_flags() -> nodebuilder::Flags {
    nodebuilder::Flags::OMIT_PARAMETER_MODIFIERS
        | nodebuilder::Flags::IGNORE_ERRORS
        | nodebuilder::Flags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE
}

/// `SignatureHelpTriggerCharacters`.
pub static SIGNATURE_HELP_TRIGGER_CHARACTERS: &[&str] = &["(", ",", "<"];
/// `SignatureHelpRetriggerCharacters`.
pub static SIGNATURE_HELP_RETRIGGER_CHARACTERS: &[&str] = &[")"];

/// `signatureHelpTriggerReasonKind`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SignatureHelpTriggerReasonKind {
    /// `signatureHelpNoneInvokeReason` (`0`).
    None,
    /// `signatureHelpInvoked`.
    Invoked,
    /// `signatureHelpCharacterTyped`.
    CharacterTyped,
    /// `signatureHelpRetriggered`.
    Retriggered,
}

/// `type callInvocation`.
pub(crate) struct CallInvocation {
    /// `node` — CallExpression | NewExpression | TaggedTemplateExpression |
    /// JsxOpeningLikeElement.
    pub(crate) node: NodeId,
}

/// `type typeArgsInvocation`.
pub(crate) struct TypeArgsInvocation {
    /// `called` — `*ast.IdentifierNode`.
    pub(crate) called: NodeId,
}

/// `type contextualInvocation`.
pub(crate) struct ContextualInvocation {
    /// `signature`.
    pub(crate) signature: SignatureId,
    /// `node`.
    pub(crate) node: NodeId,
    /// `symbol`.
    pub(crate) symbol: SymbolId,
}

/// `type invocation` — exactly one field is set (see Go `invocation`/`callInvocation`).
pub(crate) struct Invocation {
    /// `callInvocation`.
    pub(crate) call_invocation: Option<CallInvocation>,
    /// `typeArgsInvocation`.
    pub(crate) type_args_invocation: Option<TypeArgsInvocation>,
    /// `contextualInvocation`.
    pub(crate) contextual_invocation: Option<ContextualInvocation>,
}

/// `type argumentListInfo`.
pub(crate) struct ArgumentListInfo {
    /// `isTypeParameterList`.
    pub(crate) is_type_parameter_list: bool,
    /// `invocation`.
    pub(crate) invocation: Invocation,
    /// `argumentsSpan`.
    pub(crate) arguments_span: TextRange,
    /// `argumentIndex`.
    pub(crate) argument_index: usize,
    /// `argumentCount`.
    pub(crate) argument_count: usize,
}

/// `candidateInfo`.
struct CandidateInfo {
    /// `candidates`.
    candidates: Vec<SignatureId>,
    /// `resolvedSignature`.
    resolved_signature: SignatureId,
    /// `callTarget`.
    call_target: NodeId,
}

/// `candidateOrTypeInfo`.
struct CandidateOrTypeInfo {
    /// `candidateInfo`.
    candidate_info: Option<CandidateInfo>,
    /// `typeInfo`.
    type_info: Option<SymbolId>,
}

/// `argumentOrParameterListInfo`.
struct ArgumentOrParameterListInfo {
    /// `list`.
    list: Option<NodeList>,
    /// `argumentIndex`.
    argument_index: usize,
    /// `argumentCount`.
    argument_count: usize,
    /// `argumentsSpan`.
    arguments_span: TextRange,
}

/// `contextualSignatureLocationInfo`.
struct ContextualSignatureLocationInfo {
    /// `contextualType`.
    contextual_type: TypeId,
    /// `argumentIndex`.
    argument_index: usize,
    /// `argumentCount`.
    argument_count: usize,
    /// `argumentSpan`.
    argument_span: TextRange,
}

/// `signatureHelpParameter`.
struct SignatureHelpParameter {
    /// `isVariadic`.
    is_variadic: bool,
    /// `isOptional`.
    is_optional: bool,
    /// `isRest`.
    is_rest: bool,
    /// `parameterInfo`.
    parameter_info: lsproto::ParameterInformation,
}

/// `signatureInformation` — pre-LSP form (label/documentation may be filled
/// in later by `createSignatureHelpItems`/`getTypeHelpItem`).
struct SignatureInformation {
    /// `Label`.
    label: String,
    /// `Documentation`.
    documentation: Option<String>,
    /// `Parameters`.
    parameters: Vec<SignatureHelpParameter>,
    /// `isVariadic`.
    is_variadic: bool,
    /// `ColorizedRuns`.
    colorized_runs: Vec<lsproto::VSClassifiedTextRun>,
}

impl<'h> LanguageService<'h> {
    /// `ProvideSignatureHelp`.
    pub fn provide_signature_help(
        &self,
        ctx: &Context,
        document_uri: lsproto::DocumentUri,
        position: lsproto::Position,
        context: Option<&lsproto::SignatureHelpContext>,
    ) -> Result<lsproto::SignatureHelpOrNull, Error> {
        let (program, source_file) = self.get_program_and_file(&document_uri);
        let nodes = program.nodes(source_file.file_index());
        let positions = self.converters.from_lsp_position_for_source_file(
            source_file,
            &nodes,
            position,
            Feature::SignatureHelp,
        );
        for projection in &positions {
            if !projection.fidelity.is_single_segment() {
                continue;
            }
            let items = self.get_signature_help_items(
                ctx,
                projection.position,
                &program,
                projection.script.file,
                context,
            );
            if let Some(items) = items {
                return Ok(lsproto::SignatureHelpOrNull {
                    signature_help: Some(items),
                });
            }
        }
        Ok(lsproto::SignatureHelpOrNull {
            signature_help: None,
        })
    }

    /// `GetSignatureHelpItems`.
    pub fn get_signature_help_items(
        &self,
        ctx: &Context,
        position: TextPos,
        program: &Rc<Program>,
        source_file: NodeId,
        context: Option<&lsproto::SignatureHelpContext>,
    ) -> Option<lsproto::SignatureHelp> {
        // Find a valid signature help context.
        let (type_checker, done) = program.get_type_checker_for_file(ctx.clone(), source_file);
        let starting_token = {
            let mut nodes = program.nodes_mut(source_file.file_index());
            tsc_astnav::tokens::find_preceding_token(&mut nodes, source_file, position)
        };
        let Some(starting_token) = starting_token else {
            done();
            return None;
        };

        // Decide whether to show signature help
        let mut trigger_reason_kind = SignatureHelpTriggerReasonKind::None;
        if let Some(context) = context {
            match context.trigger_kind {
                lsproto::SignatureHelpTriggerKind::Invoked => {
                    trigger_reason_kind = SignatureHelpTriggerReasonKind::Invoked;
                }
                lsproto::SignatureHelpTriggerKind::TriggerCharacter
                    if context
                        .trigger_character
                        .as_deref()
                        .is_some_and(|c| SIGNATURE_HELP_TRIGGER_CHARACTERS.contains(&c)) =>
                {
                    trigger_reason_kind = SignatureHelpTriggerReasonKind::CharacterTyped;
                }
                lsproto::SignatureHelpTriggerKind::ContentChange
                    if context
                        .trigger_character
                        .as_deref()
                        .is_some_and(|c| SIGNATURE_HELP_RETRIGGER_CHARACTERS.contains(&c)) =>
                {
                    trigger_reason_kind = SignatureHelpTriggerReasonKind::Retriggered;
                }
                _ => {}
            }
        }
        let only_use_syntactic_owners =
            trigger_reason_kind == SignatureHelpTriggerReasonKind::CharacterTyped;
        if only_use_syntactic_owners {
            // Bail out quickly in the obvious cases.
            // - in a string literal or template literal
            // - in comments
            let in_string_or_comment = {
                let mut nodes = program.nodes_mut(source_file.file_index());
                is_in_string(&mut nodes, source_file, position, Some(starting_token))
                    || is_in_comment(&mut nodes, source_file, position, Some(starting_token))
                        .is_some()
            };
            if in_string_or_comment {
                done();
                return None;
            }
        }

        let is_manually_invoked =
            context.map(|c| c.is_retrigger) == Some(false)
                || trigger_reason_kind == SignatureHelpTriggerReasonKind::Invoked;
        let program_dyn: Rc<dyn checker_types::Program> = program.clone();
        let argument_info = get_containing_argument_info(
            &checker_types::ProgramPtr::from_rc(&program_dyn),
            starting_token,
            source_file,
            &type_checker,
            is_manually_invoked,
            position,
        );
        let Some(argument_info) = argument_info else {
            done();
            return None;
        };
        let candidate_info = get_candidate_or_type_info(
            &checker_types::ProgramPtr::from_rc(&program_dyn),
            &argument_info,
            &type_checker,
            source_file,
            starting_token,
            only_use_syntactic_owners,
        );
        let Some(candidate_info) = candidate_info else {
            done();
            return None;
        };
        match (candidate_info.candidate_info, candidate_info.type_info) {
            (Some(candidate_info), _) => {
                let result = self.create_signature_help_items(
                    ctx,
                    &candidate_info.candidates,
                    candidate_info.resolved_signature,
                    &argument_info,
                    source_file,
                    &type_checker,
                    true, /*useFullPrefix*/
                    program,
                );
                done();
                result
            }
            (_, Some(type_info)) => {
                let result = self.create_type_help_items(
                    ctx,
                    type_info,
                    &argument_info,
                    source_file,
                    &type_checker,
                    program,
                );
                done();
                result
            }
            _ => {
                done();
                let nodes = program.nodes(source_file.file_index());
                if ast::is_source_file_js(&nodes[source_file].as_source_file()) {
                    return self.create_js_signature_help_items(
                        ctx,
                        &argument_info,
                        program,
                        &type_checker,
                        source_file,
                    );
                }
                None
            }
        }
    }

    /// `createSignatureHelpItems`.
    fn create_signature_help_items(
        &self,
        ctx: &Context,
        candidates: &[SignatureId],
        resolved_signature: SignatureId,
        argument_info: &ArgumentListInfo,
        source_file: NodeId,
        c: &Rc<RefCell<Checker>>,
        use_full_prefix: bool,
        program: &Rc<Program>,
    ) -> Option<lsproto::SignatureHelp> {
        if candidates.is_empty() {
            return None;
        }
        let enclosing_declaration =
            get_enclosing_declaration_from_invocation(&argument_info.invocation);
        let nodes = program.nodes(source_file.file_index());
        let call_target_symbol = c
            .borrow_mut()
            .get_symbol_at_location_api(get_expression_from_invocation(&argument_info.invocation));
        let Some(call_target_symbol) = call_target_symbol else {
            return None;
        };
        let call_target_display_parts: String = {
            let mut cb = c.borrow_mut();
            if use_full_prefix
                && enclosing_declaration
                    == cb.signature_arena.get(resolved_signature).declaration
            {
                if let Some(declaration) = cb
                    .signature_arena
                    .get(resolved_signature)
                    .declaration
                    .as_ref()
                    .map(|d| *d)
                {
                    let decl_nodes = program.arena_of(declaration);
                    let res = decl_nodes[declaration]
                        .symbol()
                        .map(|sym| cb.symbol_to_string(sym))
                        .unwrap_or_else(|| cb.symbol_to_string(call_target_symbol));
                    res
                } else {
                    cb.symbol_to_string(call_target_symbol)
                }
            } else if cb
                .symbol_arena
                .get_ref(call_target_symbol)
                .name
                .starts_with(ast::INTERNAL_SYMBOL_NAME_PREFIX)
            {
                String::new()
            } else {
                cb.symbol_to_string_ex(
                    call_target_symbol,
                    Some(source_file),
                    ast::SymbolFlags::NONE,
                    SymbolFormatFlags::USE_ALIAS_DEFINED_OUTSIDE_CURRENT_SCOPE,
                    Some(&nodes[..]),
                )
            }
        };

        let mut items: Vec<SignatureInformation> = Vec::with_capacity(candidates.len());
        if argument_info.is_type_parameter_list {
            items.extend(self.item_info_for_type_parameters(
                ctx,
                candidates,
                enclosing_declaration,
                source_file,
                c,
                program,
            ));
        } else {
            items.extend(self.item_info_for_parameters(
                ctx,
                candidates,
                enclosing_declaration,
                source_file,
                c,
                program,
            ));
        }

        let argument_list = get_expression_from_invocation(&argument_info.invocation);
        let mut active_signature = candidates.len();
        for i in 0..candidates.len() {
            if candidates[i] == resolved_signature {
                active_signature = i;
                break;
            }
        }
        if active_signature == candidates.len() {
            active_signature = 0;
        }

        let supports_null = lsproto::get_client_capabilities(ctx)
            .text_document
            .signature_help
            .signature_information
            .no_active_parameter_support;

        let mut seen = rustc_hash::FxHashSet::default();
        let mut items_vec: Vec<lsproto::SignatureInformation> = Vec::with_capacity(items.len());
        for mut item in items {
            item.label = format!("{call_target_display_parts}{}", item.label);
            if !seen.insert(item.label.clone()) {
                continue;
            }
            if let Some(ref docs) = item.documentation {
                item.documentation = Some(docs.to_string());
            }
            let vs_colorized_label = if item.colorized_runs.is_empty() {
                None
            } else {
                Some(lsproto::VSClassifiedTextElement {
                    runs: Some(std::mem::take(&mut item.colorized_runs)),
                    ..Default::default()
                })
            };
            let active_parameter =
                compute_active_parameter(&item, argument_info.argument_index, supports_null);
            items_vec.push(lsproto::SignatureInformation {
                label: item.label,
                documentation: Some(lsproto::StringOrMarkupContent {
                    markup_content: Some(lsproto::MarkupContent {
                        kind: lsproto::MarkupKind::Markdown,
                        value: item.documentation.unwrap_or_default(),
                    }),
                    ..Default::default()
                }),
                parameters: Some(
                    item.parameters
                        .into_iter()
                        .map(|p| p.parameter_info)
                        .collect(),
                ),
                active_parameter,
                vs_colorized_label,
                ..Default::default()
            });
        }
        if items_vec.is_empty() {
            return None;
        }

        let _ = argument_list;
        Some(lsproto::SignatureHelp {
            signatures: Some(items_vec),
            active_signature: Some(active_signature as u32),
            active_parameter: Some(lsproto::UintegerOrNull {
                uinteger: Some(argument_info.argument_index as u32),
            }),
        })
    }

    /// `createTypeHelpItems`.
    fn create_type_help_items(
        &self,
        ctx: &Context,
        symbol: SymbolId,
        argument_info: &ArgumentListInfo,
        source_file: NodeId,
        c: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
    ) -> Option<lsproto::SignatureHelp> {
        let _ = ctx;
        let type_parameters = {
            let mut cb = c.borrow_mut();
            cb.get_local_type_parameters_of_class_or_interface_or_type_alias(symbol, &[])
        };
        if type_parameters.is_empty() {
            return None;
        }
        let invocation_enclosing_declaration =
            get_enclosing_declaration_from_invocation(&argument_info.invocation);
        let mut item = self.get_type_help_item(
            ctx,
            symbol,
            &type_parameters,
            invocation_enclosing_declaration,
            source_file,
            c,
            program,
        );
        item.label = {
            let nodes = program.nodes(source_file.file_index());
            let invoked_expression = get_expression_from_invocation(&argument_info.invocation);
            let display = nodes[invoked_expression].text(&nodes).into_owned();
            format!("{display}{}", item.label)
        };

        let supports_null = lsproto::get_client_capabilities(ctx)
            .text_document
            .signature_help
            .signature_information
            .no_active_parameter_support;
        let active_param = compute_active_parameter(&item, argument_info.argument_index, supports_null);
        let mut help = lsproto::SignatureHelp::default();
        item.documentation = None;
        help.signatures = Some(vec![lsproto::SignatureInformation {
            label: item.label,
            documentation: item
                .documentation
                .map(|d| lsproto::StringOrMarkupContent {
                    string: Some(d),
                    ..Default::default()
                }),
            parameters: Some(
                item.parameters
                    .into_iter()
                    .map(|p| p.parameter_info)
                    .collect(),
            ),
            active_parameter: active_param,
            vs_colorized_label: if item.colorized_runs.is_empty() {
                None
            } else {
                Some(lsproto::VSClassifiedTextElement {
                    runs: Some(item.colorized_runs),
                    ..Default::default()
                })
            },
            ..Default::default()
        }]);
        help.active_signature = Some(0);
        Some(help)
    }

    /// `getTypeHelpItem`.
    fn get_type_help_item(
        &self,
        ctx: &Context,
        symbol: SymbolId,
        type_parameters: &[TypeId],
        enclosing_declaration: Option<NodeId>,
        source_file: NodeId,
        c: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
    ) -> SignatureInformation {
        let _ = ctx;
        let mut cb = c.borrow_mut();
        let mut builder = tsc_checker::nodebuilder::new_node_builder(&cb, EmitContext::new());
        let emit_context = builder.emit_context();
        let file_index = enclosing_declaration
            .map(|d| d.file_index())
            .unwrap_or_else(|| builder.impl_.as_ref().expect("impl").f.file_index());
        let (file_index, arena_cell) = program.nodes_handle_or_fallback(file_index);
        builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaAccess::new(&arena_cell);
        let symbols = cb.symbol_arena.clone();

        let mut parameters = Vec::with_capacity(type_parameters.len());
        for &type_param in type_parameters {
            parameters.push(create_signature_help_parameter_for_type_parameter(
                &mut cb,
                type_param,
                source_file,
                enclosing_declaration,
                &mut builder,
                &emit_context,
                &mut nodes,
                &symbols,
            ));
        }
        drop(nodes);
        let mut display_parts = cb.symbol_to_string(symbol);
        if !parameters.is_empty() {
            display_parts.push_str(token_to_string(Kind::LessThanToken));
            for (i, tp) in parameters.iter().enumerate() {
                if i > 0 {
                    display_parts.push_str(", ");
                }
                display_parts.push_str(
                    tp.parameter_info
                        .label
                        .string
                        .as_ref()
                        .expect("label string"),
                );
            }
            display_parts.push_str(token_to_string(Kind::GreaterThanToken));
        }
        drop(cb);
        SignatureInformation {
            label: display_parts,
            documentation: None,
            parameters,
            is_variadic: false,
            colorized_runs: Vec::new(),
        }
    }

    /// `itemInfoForTypeParameters`.
    fn item_info_for_type_parameters(
        &self,
        ctx: &Context,
        candidate_signatures: &[SignatureId],
        enclosing_declaration: Option<NodeId>,
        source_file: NodeId,
        c: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
    ) -> Vec<SignatureInformation> {
        let doc_format = if self.user_preferences().display_parts_for_jsdoc.is_true() {
            lsproto::MarkupKind::Markdown
        } else {
            lsproto::MarkupKind::PlainText
        };
        let supports_vs_colorized =
            lsproto::get_client_capabilities(ctx).vs_supports_visual_studio_extensions;
        let mut result = Vec::with_capacity(candidate_signatures.len());
        let mut cb = c.borrow_mut();
        let mut builder = tsc_checker::nodebuilder::new_node_builder(&cb, EmitContext::new());
        let emit_context = builder.emit_context();
        let file_index = enclosing_declaration
            .map(|d| d.file_index())
            .unwrap_or_else(|| builder.impl_.as_ref().expect("impl").f.file_index());
        let (file_index, arena_cell) = program.nodes_handle_or_fallback(file_index);
        builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaAccess::new(&arena_cell);
        let symbols = cb.symbol_arena.clone();

        for i in 0..candidate_signatures.len() {
            let candidate_signature = candidate_signatures[i];
            let signature = cb.signature_arena.get(candidate_signature);
            let this_parameter = signature.this_parameter;
            let type_parameters: Vec<TypeId> = signature.type_parameters.to_vec();
            let target = signature.target;
            let _ = signature;

            let mut signature_help_type_parameters: Vec<SignatureHelpParameter> =
                Vec::with_capacity(type_parameters.len());
            for &t in &type_parameters {
                signature_help_type_parameters.push(
                    create_signature_help_parameter_for_type_parameter(
                        &mut cb,
                        t,
                        source_file,
                        enclosing_declaration,
                        &mut builder,
                        &emit_context,
                        &mut nodes,
                        &symbols,
                    ),
                );
            }

            let mut this_parameter_params: Vec<SignatureHelpParameter> = Vec::new();
            if let Some(tp) = this_parameter {
                this_parameter_params.push(create_signature_help_parameter_for_parameter(
                    &mut cb,
                    tp,
                    enclosing_declaration,
                    source_file,
                    &mut builder,
                    &emit_context,
                    &mut nodes,
                    &symbols,
                    c,
                    program,
                    self,
                    doc_format.clone(),
                ));
            }

            let lists = cb.get_expanded_parameters(candidate_signature, false);
            let _ = target;
            let mut signature_help_parameters = this_parameter_params;
            for param_list in lists.iter().flatten() {
                let param_label = create_signature_help_parameter_for_parameter(
                    &mut cb,
                    *param_list,
                    enclosing_declaration,
                    source_file,
                    &mut builder,
                    &emit_context,
                    &mut nodes,
                    &symbols,
                    c,
                    program,
                    self,
                    doc_format.clone(),
                );
                signature_help_parameters.push(create_signature_help_parameter_from_label(
                    *param_list,
                    param_label,
                    c,
                    self,
                    doc_format.clone(),
                ));
            }

            let (label, runs) = self.signature_help_label_and_runs(
                &mut cb,
                candidate_signature,
                &signature_help_type_parameters,
                enclosing_declaration,
                source_file,
                c,
                program,
                supports_vs_colorized,
                true,
            );

            let documentation = {
                let declaration = cb.signature_arena.get(candidate_signature).declaration;
                let doc_format = doc_format.clone();
                declaration.map(|d| {
                    let mapper = self.documentation_location_mapper(Feature::SignatureHelp);
                    get_documentation_from_declaration(
                        &mapper,
                        program,
                        c,
                        None,
                        Some(d),
                        source_file,
                        doc_format,
                        true, /*commentOnly*/
                    )
                })
            };

            result.push(SignatureInformation {
                label,
                documentation,
                parameters: signature_help_type_parameters,
                is_variadic: false,
                colorized_runs: runs,
            });
            let _ = signature_help_parameters;
        }
        result
    }

    /// `itemInfoForParameters`.
    fn item_info_for_parameters(
        &self,
        ctx: &Context,
        candidate_signatures: &[SignatureId],
        enclosing_declaration: Option<NodeId>,
        source_file: NodeId,
        c: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
    ) -> Vec<SignatureInformation> {
        let doc_format = if self.user_preferences().display_parts_for_jsdoc.is_true() {
            lsproto::MarkupKind::Markdown
        } else {
            lsproto::MarkupKind::PlainText
        };
        let supports_vs_colorized =
            lsproto::get_client_capabilities(ctx).vs_supports_visual_studio_extensions;
        let mut result = Vec::with_capacity(candidate_signatures.len());
        let mut cb = c.borrow_mut();
        let mut builder = tsc_checker::nodebuilder::new_node_builder(&cb, EmitContext::new());
        let emit_context = builder.emit_context();
        let file_index = enclosing_declaration
            .map(|d| d.file_index())
            .unwrap_or_else(|| builder.impl_.as_ref().expect("impl").f.file_index());
        let (file_index, arena_cell) = program.nodes_handle_or_fallback(file_index);
        builder
            .impl_
            .as_mut()
            .expect("NodeBuilder without impl")
            .f
            .set_file_index(file_index);
        let mut nodes = tsc_ast::ast::ArenaAccess::new(&arena_cell);
        let symbols = cb.symbol_arena.clone();

        for i in 0..candidate_signatures.len() {
            let candidate_signature = candidate_signatures[i];
            let (this_parameter, has_rest, declaration) = {
                let signature = cb.signature_arena.get(candidate_signature);
                (
                    signature.this_parameter,
                    signature.has_rest_parameter(),
                    signature.declaration,
                )
            };
            let mut param_dpw = self.display_parts_writer(c, program, supports_vs_colorized);
            let mut signature_help_parameters = Vec::new();
            if let Some(tp) = this_parameter {
                signature_help_parameters.push(create_signature_help_parameter_for_parameter(
                    &mut cb,
                    tp,
                    enclosing_declaration,
                    source_file,
                    &mut builder,
                    &emit_context,
                    &mut nodes,
                    &symbols,
                    c,
                    program,
                    self,
                    doc_format.clone(),
                ));
            }

            let lists = cb.get_expanded_parameters(candidate_signature, false);
            let _ = has_rest;
            let mut is_variadic = false;
            for parameter_list in &lists {
                if parameter_list.is_empty() {
                    continue;
                }
                for &param in parameter_list {
                    signature_help_parameters.push(create_signature_help_parameter_from_label(
                        param,
                        create_signature_help_parameter_for_parameter(
                            &mut cb,
                            param,
                            enclosing_declaration,
                            source_file,
                            &mut builder,
                            &emit_context,
                            &mut nodes,
                            &symbols,
                            c,
                            program,
                            self,
                            doc_format.clone(),
                        ),
                        c,
                        self,
                        doc_format.clone(),
                    ));
                }
                if is_variadic_list(&mut cb, candidate_signature, parameter_list, lists.len()) {
                    is_variadic = true;
                }
            }

            let (label, runs) = self.signature_help_label_and_runs(
                &mut cb,
                candidate_signature,
                &signature_help_parameters,
                enclosing_declaration,
                source_file,
                c,
                program,
                supports_vs_colorized,
                false,
            );
            let _ = &mut param_dpw;

            let documentation = {
                let doc_format = doc_format.clone();
                declaration.map(|d| {
                    let mapper = self.documentation_location_mapper(Feature::SignatureHelp);
                    get_documentation_from_declaration(
                        &mapper,
                        program,
                        c,
                        None,
                        Some(d),
                        source_file,
                        doc_format,
                        true, /*commentOnly*/
                    )
                })
            };

            result.push(SignatureInformation {
                label,
                documentation,
                parameters: signature_help_parameters,
                is_variadic,
                colorized_runs: runs,
            });
        }
        drop(cb);
        let _ = ctx;
        result
    }

    /// Builds the `(param, ...) -> ret` label suffix for a candidate
    /// signature (the call-target symbol prefix is added by the caller).
    /// Mirrors the `displayPartsWriter` label accumulation in Go's
    /// `itemInfoForParameters`/`itemInfoForTypeParameters` plus
    /// `returnTypeToDisplayParts`.
    fn signature_help_label_and_runs(
        &self,
        cb: &mut Checker,
        candidate_signature: SignatureId,
        parameters: &[SignatureHelpParameter],
        enclosing_declaration: Option<NodeId>,
        source_file: NodeId,
        c: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
        vs_capability: bool,
        type_parameter_list: bool,
    ) -> (String, Vec<lsproto::VSClassifiedTextRun>) {
        let _ = c;
        let mut dpw = new_display_parts_writer(vs_capability, cb, program);
        if type_parameter_list {
            dpw.write_punctuation(token_to_string(Kind::LessThanToken));
        } else {
            dpw.write_punctuation(token_to_string(Kind::OpenParenToken));
        }
        for (i, p) in parameters.iter().enumerate() {
            let label = p
                .parameter_info
                .label
                .string
                .clone()
                .unwrap_or_default();
            if i != 0 {
                dpw.write_punctuation(",");
                dpw.write_space(" ");
            }
            dpw.write_punctuation(&label);
        }
        if type_parameter_list {
            dpw.write_punctuation(token_to_string(Kind::GreaterThanToken));
        } else {
            dpw.write_punctuation(token_to_string(Kind::CloseParenToken));
        }
        self.return_type_to_display_parts_dpw(
            &mut dpw,
            cb,
            candidate_signature,
            enclosing_declaration,
            source_file,
            program,
            vs_capability,
        );
        let label = dpw.string().to_string();
        let runs = if vs_capability {
            dpw.get_runs().to_vec()
        } else {
            Vec::new()
        };
        (label, runs)
    }

    /// `returnTypeToDisplayParts` — writes `": <type>"` (or the type
    /// predicate) into `dpw`.
    fn return_type_to_display_parts_dpw(
        &self,
        dpw: &mut DisplayPartsWriter,
        cb: &mut Checker,
        candidate_signature: SignatureId,
        enclosing_declaration: Option<NodeId>,
        source_file: NodeId,
        program: &Rc<Program>,
        vs_capability: bool,
    ) {
        dpw.write_punctuation(": ");
        let predicate = cb.get_type_predicate_of_signature(candidate_signature);
        if let Some(predicate) = &predicate {
            let s = cb.type_predicate_to_string(Some(predicate));
            dpw.write(&s);
        } else {
            let return_type = cb.get_return_type_of_signature(candidate_signature);
            let type_node = cb.type_to_type_node_ex(
                return_type,
                enclosing_declaration,
                signature_help_node_builder_flags(),
                nodebuilder::InternalFlags::NONE,
                FxHashMap::default(),
            );
            if let Some(type_node) = type_node {
                let mut temp_dpw = new_display_parts_writer(vs_capability, cb, program);
                {
                    let (_, arena_cell) =
                        program.nodes_handle_or_fallback(type_node.file_index());
                    let mut nodes = tsc_ast::ast::ArenaAccess::new(&arena_cell);
                    let emit_context = cb.get_node_builder().emit_context();
                    let mut ec = emit_context.borrow_mut();
                    let symbols = cb.symbol_arena.clone();
                    let mut p = Printer::new(
                        PrinterOptions {
                            new_line: NewLineKind::LF,
                            ..Default::default()
                        },
                        PrintHandlers::default(),
                        &mut ec,
                        &mut nodes,
                        &symbols,
                    );
                    p.write(Some(type_node), Some(source_file), &mut temp_dpw, None);
                }
                dpw.write_from(&mut temp_dpw);
            } else {
                let s = cb.type_to_string(return_type);
                dpw.write(&s);
            }
        }
    }

    /// `createSignatureHelpParameterForTypeParameter` — free helper needs
    /// access to `self` for the display-parts writer; thin wrapper kept on
    /// `self` for Go parity.
    fn display_parts_writer(
        &self,
        c: &Rc<RefCell<Checker>>,
        program: &Rc<Program>,
        vs_capability: bool,
    ) -> DisplayPartsWriter {
        new_display_parts_writer(vs_capability, &c.borrow(), program)
    }

}

/// `computeActiveParameter`.
fn compute_active_parameter(
    sig: &SignatureInformation,
    argument_index: usize,
    supports_null: bool,
) -> Option<lsproto::UintegerOrNull> {
    let param_count = sig.parameters.len();
    if param_count == 0 {
        return None;
    }
    let mut active_param = argument_index as u32;
    if sig.is_variadic {
        let first_rest = sig.parameters.iter().position(|p| p.is_rest);
        if let Some(first_rest) = first_rest
            && first_rest < param_count - 1
        {
            if supports_null {
                return Some(lsproto::UintegerOrNull::default());
            }
            return Some(lsproto::UintegerOrNull {
                uinteger: Some(param_count as u32),
            });
        }
        if active_param > param_count as u32 - 1 {
            active_param = param_count as u32 - 1;
        }
    }
    Some(lsproto::UintegerOrNull {
        uinteger: Some(active_param),
    })
}

/// `createSignatureHelpParameterFromLabel`.
fn create_signature_help_parameter_from_label(
    parameter: tsc_ast::SymbolId,
    param: SignatureHelpParameter,
    c: &Rc<RefCell<Checker>>,
    ls: &LanguageService,
    doc_format: lsproto::MarkupKind,
) -> SignatureHelpParameter {
    let _ = doc_format;
    let cb = c.borrow();
    let check_flags = cb.symbol_arena.get_ref(parameter).check_flags;
    drop(cb);
    let is_optional = check_flags.intersects(ast::checkflags::CheckFlags::OPTIONAL_PARAMETER);
    let is_rest = check_flags.intersects(ast::checkflags::CheckFlags::REST_PARAMETER);
    let is_variadic = is_rest;
    let _ = ls;
    SignatureHelpParameter {
        is_variadic,
        is_optional,
        is_rest,
        parameter_info: param.parameter_info,
    }
}

/// `createSignatureHelpParameterForParameter`.
fn create_signature_help_parameter_for_parameter(
    cb: &mut Checker,
    parameter: SymbolId,
    enclosing_declaration: Option<NodeId>,
    source_file: NodeId,
    builder: &mut NodeBuilder,
    emit_context: &Rc<RefCell<EmitContext>>,
    nodes: &mut Vec<Node>,
    symbols: &tsc_ast::SymbolArena,
    c: &Rc<RefCell<Checker>>,
    program: &Rc<Program>,
    ls: &LanguageService,
    doc_format: lsproto::MarkupKind,
) -> SignatureHelpParameter {
    let display = {
        let node = builder.symbol_to_parameter_declaration(
            cb,
            nodes,
            parameter,
            enclosing_declaration,
            signature_help_node_builder_flags(),
            nodebuilder::InternalFlags::NONE,
            None,
        );
        let mut ec = emit_context.borrow_mut();
        let mut p = Printer::new(
            PrinterOptions {
                new_line: NewLineKind::LF,
                ..Default::default()
            },
            PrintHandlers::default(),
            &mut ec,
            nodes,
            symbols,
        );
        p.emit(node, Some(source_file))
    };

    let cb2 = c.borrow();
    let check_flags = cb2.symbol_arena.get_ref(parameter).check_flags;
    let value_declaration = cb2.symbol_arena.get_ref(parameter).value_declaration;
    drop(cb2);
    let documentation = value_declaration.map(|vd| {
        let mapper = ls.documentation_location_mapper(Feature::SignatureHelp);
        get_documentation_from_declaration(
            &mapper,
            program,
            c,
            None,
            Some(vd),
            source_file,
            doc_format.clone(),
            true,
        )
    });

    SignatureHelpParameter {
        is_variadic: check_flags.intersects(ast::checkflags::CheckFlags::REST_PARAMETER),
        is_optional: check_flags.intersects(ast::checkflags::CheckFlags::OPTIONAL_PARAMETER),
        is_rest: check_flags.intersects(ast::checkflags::CheckFlags::REST_PARAMETER),
        parameter_info: lsproto::ParameterInformation {
            label: lsproto::StringOrTuple {
                string: Some(display),
                ..Default::default()
            },
            documentation: documentation.map(|d| lsproto::StringOrMarkupContent {
                markup_content: Some(lsproto::MarkupContent {
                    kind: lsproto::MarkupKind::Markdown,
                    value: d,
                }),
                ..Default::default()
            }),
        },
    }
}

/// `createSignatureHelpParameterForTypeParameter`.
fn create_signature_help_parameter_for_type_parameter(
    cb: &mut Checker,
    t: TypeId,
    source_file: NodeId,
    enclosing_declaration: Option<NodeId>,
    builder: &mut NodeBuilder,
    emit_context: &Rc<RefCell<EmitContext>>,
    nodes: &mut Vec<Node>,
    symbols: &tsc_ast::SymbolArena,
) -> SignatureHelpParameter {
    // Go: `defer builder.EmitContext().Factory.ReleaseArenas()` — no
    // counterpart in the Rust port (arenas are shared buffers).
    let display = {
        let node = builder.type_parameter_to_declaration(
            cb,
            nodes,
            t,
            enclosing_declaration,
            signature_help_node_builder_flags(),
            nodebuilder::InternalFlags::NONE,
            None,
        );
        let mut ec = emit_context.borrow_mut();
        let mut p = Printer::new(
            PrinterOptions {
                new_line: NewLineKind::LF,
                ..Default::default()
            },
            PrintHandlers::default(),
            &mut ec,
            nodes,
            symbols,
        );
        p.emit(node, Some(source_file))
    };
    SignatureHelpParameter {
        is_variadic: false,
        is_optional: false,
        is_rest: false,
        parameter_info: lsproto::ParameterInformation {
            label: lsproto::StringOrTuple {
                string: Some(display),
                ..Default::default()
            },
            ..Default::default()
        },
    }
}

/// `isVariadic` for `itemInfoForParameters`.
fn is_variadic_list(
    cb: &mut Checker,
    candidate_signature: SignatureId,
    parameter_list: &[SymbolId],
    list_count: usize,
) -> bool {
    if !cb.has_effective_rest_parameter(candidate_signature) {
        return false;
    }
    if list_count == 1 {
        return true;
    }
    parameter_list.last().is_some_and(|&p| {
        cb.symbol_arena
            .get_ref(p)
            .check_flags
            .intersects(ast::checkflags::CheckFlags::REST_PARAMETER)
    })
}

/// `getEnclosingDeclarationFromInvocation`.
fn get_enclosing_declaration_from_invocation(invocation: &Invocation) -> Option<NodeId> {
    if let Some(call_invocation) = &invocation.call_invocation {
        return Some(call_invocation.node);
    }
    if let Some(contextual_invocation) = &invocation.contextual_invocation {
        return Some(contextual_invocation.node);
    }
    None
}

/// `getExpressionFromInvocation`.
fn get_expression_from_invocation(invocation: &Invocation) -> NodeId {
    if let Some(call_invocation) = &invocation.call_invocation {
        return call_invocation.node;
    }
    if let Some(contextual_invocation) = &invocation.contextual_invocation {
        return contextual_invocation.node;
    }
    invocation
        .type_args_invocation
        .as_ref()
        .expect("invocation")
        .called
}

/// `getContainingArgumentInfo`.
fn get_containing_argument_info(
    program: &dyn tsc_checker::checker_types::Program,
    node: NodeId,
    source_file: NodeId,
    checker: &Rc<RefCell<Checker>>,
    is_manually_invoked: bool,
    position: TextPos,
) -> Option<ArgumentListInfo> {
    let mut first_argument_info: Option<ArgumentListInfo> = None;
    let mut n = Some(node);
    while let Some(cur) = n {
        {
            let nodes = program.nodes(source_file.file_index());
            if ast::is_source_file(&nodes[cur])
                || (!is_manually_invoked && ast::is_block(&nodes[cur]))
            {
                break;
            }
            let parent = nodes[cur].parent.expect("parent");
            debug::assert_!(
                range_contains_range(&nodes[parent].loc, &nodes[cur].loc),
                "Not a subspan. Child: , parent: "
            );
        }

        let argument_info = {
            let mut cb = checker.borrow_mut();
            get_immediately_containing_argument_or_contextual_parameter_info(
                program,
                cur,
                position,
                source_file,
                &mut cb,
            )
        };
        if let Some(info) = argument_info {
            if info.invocation.contextual_invocation.is_some() {
                return Some(info);
            }
            if first_argument_info.is_none() {
                // Clone-free path: stash a lightweight copy by index — the
                // struct is small and `invocation` is three `Option`s, but
                // `Clone` isn't implemented; reconstruct by re-invoking.
                first_argument_info = Some(ArgumentListInfo {
                    is_type_parameter_list: info.is_type_parameter_list,
                    invocation: Invocation {
                        call_invocation: info.invocation.call_invocation.as_ref().map(|ci| {
                            CallInvocation { node: ci.node }
                        }),
                        type_args_invocation: None,
                        contextual_invocation: info.invocation.contextual_invocation.as_ref().map(
                            |ci| ContextualInvocation {
                                signature: ci.signature,
                                node: ci.node,
                                symbol: ci.symbol,
                            },
                        ),
                    },
                    arguments_span: info.arguments_span,
                    argument_index: info.argument_index,
                    argument_count: info.argument_count,
                });
            }
            if info.arguments_span.end() == position {
                return Some(info);
            }
            if info.arguments_span.contains(position) {
                return Some(info);
            }
        }
        n = {
            let nodes = program.nodes(source_file.file_index());
            nodes[cur].parent
        };
    }
    first_argument_info
}

/// `getImmediatelyContainingArgumentOrContextualParameterInfo`.
fn get_immediately_containing_argument_or_contextual_parameter_info(
    program: &dyn tsc_checker::checker_types::Program,
    node: NodeId,
    position: TextPos,
    source_file: NodeId,
    checker: &mut Checker,
) -> Option<ArgumentListInfo> {
    if let Some(result) = try_get_parameter_info(program, node, source_file, checker) {
        return Some(result);
    }
    get_immediately_containing_argument_info_impl(
        program,
        node,
        position,
        source_file,
        checker,
    )
}

/// `tryGetParameterInfo`.
fn try_get_parameter_info(
    program: &dyn tsc_checker::checker_types::Program,
    starting_token: NodeId,
    source_file: NodeId,
    c: &mut Checker,
) -> Option<ArgumentListInfo> {
    let node = get_adjusted_node(program, starting_token, source_file);
    let info = get_contextual_signature_location_info(program, node, source_file, c)?;
    let non_nullable_contextual_type = c.get_non_nullable_type(info.contextual_type);
    let symbol = c.types.get_ref(non_nullable_contextual_type).symbol();
    let signatures =
        c.get_signatures_of_type(non_nullable_contextual_type, SignatureKind::Call);
    if signatures.is_empty() {
        return None;
    }
    let signature = *signatures.last().expect("last signature");
    let contextual_invocation = ContextualInvocation {
        signature,
        node: starting_token,
        symbol: choose_better_symbol(program, c, symbol).unwrap_or(SymbolId::NONE),
    };
    Some(ArgumentListInfo {
        is_type_parameter_list: false,
        invocation: Invocation {
            call_invocation: None,
            type_args_invocation: None,
            contextual_invocation: Some(contextual_invocation),
        },
        arguments_span: info.argument_span,
        argument_index: info.argument_index,
        argument_count: info.argument_count,
    })
}

/// `getAdjustedNode`.
fn get_adjusted_node(program: &dyn tsc_checker::checker_types::Program, node: NodeId, source_file: NodeId) -> NodeId {
    let nodes = program.nodes(source_file.file_index());
    match nodes[node].kind {
        Kind::OpenParenToken | Kind::CommaToken => node,
        _ => ast::find_ancestor(nodes[node].parent, &nodes, &mut |n, _| {
            ast::is_parameter_declaration(n)
        })
        .expect("adjusted node"),
    }
}

/// `getContextualSignatureLocationInfo`.
fn get_contextual_signature_location_info(
    program: &dyn tsc_checker::checker_types::Program,
    node: NodeId,
    source_file: NodeId,
    c: &mut Checker,
) -> Option<ContextualSignatureLocationInfo> {
    let nodes = program.nodes(source_file.file_index());
    let parent = nodes[node].parent.expect("parent");
    match nodes[parent].kind {
        Kind::ParenthesizedExpression
        | Kind::MethodDeclaration
        | Kind::FunctionExpression
        | Kind::ArrowFunction => {
            drop(nodes);
            let info = get_argument_or_parameter_list_info(program, node, source_file, c)?;
            let nodes = program.nodes(source_file.file_index());
            let contextual_type = if ast::is_method_declaration(&nodes[parent]) {
                c.get_contextual_type_for_object_literal_element(parent, ContextFlags::NONE)
            } else {
                c.get_contextual_type_api(parent, ContextFlags::NONE)
            };
            if let Some(contextual_type) = contextual_type {
                return Some(ContextualSignatureLocationInfo {
                    contextual_type,
                    argument_index: info.argument_index,
                    argument_count: info.argument_count,
                    argument_span: info.arguments_span,
                });
            }
            None
        }
        Kind::BinaryExpression => {
            let highest_binary = get_highest_binary(&nodes, nodes[parent].as_binary_expression().left.expect("left"), parent);
            drop(nodes);
            let contextual_type = c.get_contextual_type_api(highest_binary, ContextFlags::NONE);
            {
                let nodes = program.nodes(source_file.file_index());
                if nodes[node].kind != Kind::OpenParenToken {
                    let argument_index = count_binary_expression_parameters(&nodes, parent) - 1;
                    let argument_count = count_binary_expression_parameters(&nodes, highest_binary);
                    if let Some(contextual_type) = contextual_type {
                        return Some(ContextualSignatureLocationInfo {
                            contextual_type,
                            argument_index,
                            argument_count,
                            argument_span: TextRange::new(nodes[parent].pos(), nodes[parent].end()),
                        });
                    }
                    return None;
                }
            }
            None
        }
        _ => None,
    }
}

/// `getHighestBinary`.
fn get_highest_binary(nodes: &[Node], mut current: NodeId, root: NodeId) -> NodeId {
    let mut highest = root;
    while ast::is_binary_expression(&nodes[current]) {
        highest = current;
        current = match nodes[current].as_binary_expression().left {
            Some(l) => l,
            None => break,
        };
    }
    highest
}

/// `countBinaryExpressionParameters`.
fn count_binary_expression_parameters(nodes: &[Node], root: NodeId) -> usize {
    let mut last_operand = root;
    let mut current = match nodes[last_operand].as_binary_expression().left {
        Some(l) => l,
        None => return 0,
    };
    let mut result = 1usize;
    while ast::is_binary_expression(&nodes[current]) {
        result += 1;
        last_operand = current;
        current = match nodes[current].as_binary_expression().left {
            Some(l) => l,
            None => break,
        };
    }
    let _ = last_operand;
    result
}

/// `chooseBetterSymbol`.
fn choose_better_symbol(
    program: &dyn tsc_checker::checker_types::Program,
    cb: &mut Checker,
    s: Option<SymbolId>,
) -> Option<SymbolId> {
    let s = s?;
    if cb.symbol_arena.get_ref(s).name.as_ref() == ast::INTERNAL_SYMBOL_NAME_TYPE {
        let declarations = cb.symbol_arena.get_ref(s).declarations.clone();
        for d in declarations {
            let dnodes = program.nodes(d.file_index());
            if ast::is_function_type_node(&dnodes[d])
                && dnodes[d]
                    .parent
                    .is_some_and(|p| ast::can_have_symbol(&dnodes[p]))
            {
                return dnodes[d].parent.and_then(|p| dnodes[p].symbol());
            }
        }
    }
    Some(s)
}

/// `getImmediatelyContainingArgumentInfo` — internal entry
/// (`_impl` suffix avoids a clash with the `pub(crate)` wrapper used by
/// `completions.rs`).
fn get_immediately_containing_argument_info_impl(
    program: &dyn tsc_checker::checker_types::Program,
    node: NodeId,
    position: TextPos,
    source_file: NodeId,
    c: &mut Checker,
) -> Option<ArgumentListInfo> {
    let nodes = program.nodes(source_file.file_index());
    let parent = nodes[node].parent.expect("parent");
    if ast::is_call_or_new_expression(&nodes[parent]) {
        drop(nodes);
        let info = get_argument_or_parameter_list_info(program, node, source_file, c)?;
        let nodes = program.nodes(source_file.file_index());
        let list = info.list;
        let argument_index = info.argument_index;
        let argument_count = info.argument_count;
        let arguments_span = info.arguments_span;
        let mut is_type_parameter_list = false;
        if let Some(parent_type_argument_list) = nodes[parent].type_argument_list() {
            if parent_type_argument_list.pos()
                == list.as_ref().map(|l| l.pos()).unwrap_or(-1)
            {
                is_type_parameter_list = true;
            }
        }
        return Some(ArgumentListInfo {
            is_type_parameter_list,
            invocation: Invocation {
                call_invocation: Some(CallInvocation { node: parent }),
                type_args_invocation: None,
                contextual_invocation: None,
            },
            arguments_span,
            argument_index,
            argument_count,
        });
    } else if is_no_substitution_template_literal(node, &nodes)
        && is_tagged_template_expression(parent, &nodes)
    {
        if is_inside_template_literal(&nodes, node, position, source_file) {
            return get_argument_list_info_for_template(&nodes, parent, 0, source_file, program);
        }
        return None;
    } else if is_template_head(node, &nodes)
        && nodes[parent].parent.is_some_and(|pp| {
            nodes[pp].kind == Kind::TaggedTemplateExpression
        })
    {
        let template_expression = parent;
        let tag_expression = nodes[template_expression]
            .parent
            .expect("tag expression");
        let mut argument_index = 1usize;
        if is_inside_template_literal(&nodes, node, position, source_file) {
            argument_index = 0;
        }
        return get_argument_list_info_for_template(
            &nodes,
            tag_expression,
            argument_index,
            source_file,
            program,
        );
    } else if ast::is_template_span(&nodes[parent])
        && nodes[parent].parent.is_some_and(|pp| {
            nodes[pp].parent.is_some_and(|ppp| is_tagged_template_expression(ppp, &nodes))
        })
    {
        let template_span = parent;
        let tag_expression = nodes[nodes[parent].parent.expect("template parent")]
            .parent
            .expect("tag expression");
        if is_template_tail(node, &nodes)
            && !is_inside_template_literal(&nodes, node, position, source_file)
        {
            return None;
        }
        let template_spans = nodes[nodes[template_span].parent.expect("template expression")]
            .as_template_expression()
            .template_spans
            .as_ref()
            .map(|s| s.nodes().to_vec())
            .unwrap_or_default();
        let span_index = ast::index_of_node(&template_spans, template_span, &nodes);
        let argument_index = get_argument_index_for_template_piece(
            &nodes,
            span_index.max(0) as usize,
            node,
            position,
            source_file,
            program,
        );
        return get_argument_list_info_for_template(
            &nodes,
            tag_expression,
            argument_index,
            source_file,
            program,
        );
    } else if ast::is_jsx_opening_like_element(&nodes[parent]) {
        let attribute_span_start = nodes[parent]
            .attributes()
            .map(|a| nodes[a].loc.pos())
            .unwrap_or(0);
        let text = nodes[source_file].as_source_file().text().to_string();
        let attribute_span_end = skip_trivia(
            &text,
            nodes[parent]
                .attributes()
                .map(|a| nodes[a].loc.end())
                .unwrap_or(0),
        );
        return Some(ArgumentListInfo {
            is_type_parameter_list: false,
            invocation: Invocation {
                call_invocation: Some(CallInvocation { node: parent }),
                type_args_invocation: None,
                contextual_invocation: None,
            },
            arguments_span: TextRange::new(
                attribute_span_start,
                attribute_span_end - attribute_span_start,
            ),
            argument_index: 0,
            argument_count: 1,
        });
    } else {
        drop(nodes);
        let type_arg_info = {
            let mut nodes_mut = program.nodes_mut(source_file.file_index());
            get_possible_type_arguments_info(&mut nodes_mut, node, source_file)
        };
        let nodes = program.nodes(source_file.file_index());
        if let Some(type_arg_info) = type_arg_info {
            let called = type_arg_info.called;
            let n_type_arguments = type_arg_info.n_type_arguments;
            let invoc = Invocation {
                call_invocation: None,
                type_args_invocation: Some(TypeArgsInvocation { called }),
                contextual_invocation: None,
            };
            let argument_range = TextRange::new(nodes[called].loc.pos(), nodes[node].end());
            return Some(ArgumentListInfo {
                is_type_parameter_list: true,
                invocation: invoc,
                arguments_span: argument_range,
                argument_index: n_type_arguments.max(0) as usize,
                argument_count: (n_type_arguments + 1).max(0) as usize,
            });
        }
    }
    None
}

/// `getArgumentListInfoForTemplate`.
fn get_argument_list_info_for_template(
    nodes: &[Node],
    tag_expression: NodeId,
    argument_index: usize,
    source_file: NodeId,
    program: &dyn tsc_checker::checker_types::Program,
) -> Option<ArgumentListInfo> {
    let mut argument_count = 1usize;
    let template = nodes[tag_expression].as_tagged_template_expression().template;
    if let Some(template) = template
        && !is_no_substitution_template_literal(template, &nodes)
    {
        argument_count = nodes[template]
            .as_template_expression()
            .template_spans
            .as_ref()
            .map(|s| s.nodes().len() + 1)
            .unwrap_or(1);
    }
    if argument_index != 0 {
        debug::assert_!(argument_index < argument_count);
    }
    Some(ArgumentListInfo {
        is_type_parameter_list: false,
        invocation: Invocation {
            call_invocation: Some(CallInvocation {
                node: tag_expression,
            }),
            type_args_invocation: None,
            contextual_invocation: None,
        },
        argument_index,
        argument_count,
        arguments_span: get_applicable_range_for_tagged_template(
            nodes,
            tag_expression,
            source_file,
            program,
        ),
    })
}

/// `getApplicableRangeForTaggedTemplate`.
fn get_applicable_range_for_tagged_template(
    nodes: &[Node],
    tagged_template: NodeId,
    source_file: NodeId,
    program: &dyn tsc_checker::checker_types::Program,
) -> TextRange {
    let template = nodes[tagged_template]
        .as_tagged_template_expression()
        .template
        .expect("template");
    let applicable_span_start = {
        let nodes_mut = program.nodes_mut(source_file.file_index());
        tsc_scanner::scanner::get_token_pos_of_node(
            template,
            nodes_mut[source_file].as_source_file(),
            false,
            &nodes_mut,
        )
    };
    let mut applicable_span_end = nodes[template].end();
    if nodes[template].kind == Kind::TemplateExpression {
        let template_spans = nodes[template]
            .as_template_expression()
            .template_spans
            .as_ref()
            .map(|s| s.nodes().to_vec())
            .unwrap_or_default();
        let last_span = *template_spans.last().expect("last span");
        let literal = nodes[last_span]
            .as_template_span()
            .literal
            .expect("template span literal");
        if nodes[literal].end() - nodes[literal].pos() == 0 {
            let text = nodes[source_file].as_source_file().text().to_string();
            applicable_span_end = skip_trivia(&text, applicable_span_end);
        }
    }
    // PORT: Go passes `applicableSpanEnd-applicableSpanStart` as the second
    // (end) argument of `NewTextRange`; kept literally for fidelity.
    TextRange::new(
        applicable_span_start,
        applicable_span_end - applicable_span_start,
    )
}

/// `getArgumentIndexForTemplatePiece`.
fn get_argument_index_for_template_piece(
    nodes: &[Node],
    span_index: usize,
    node: NodeId,
    position: TextPos,
    source_file: NodeId,
    _program: &dyn tsc_checker::checker_types::Program,
) -> usize {
    debug::assert_!(position >= nodes[node].loc.pos());
    if ast::is_template_literal_token(&nodes[node]) {
        if is_inside_template_literal(nodes, node, position, source_file) {
            return 0;
        }
        // If the template has a tail, the tail is an argument at index
        // spanIndex + 1. Otherwise, the argument is at spanIndex + 2
        // (positions: head, expr, middle, expr, ..., tail).
        return span_index + 2;
    }
    span_index + 1
}

/// `getArgumentOrParameterListInfo` — `(list, index, count, span)`; the
/// caller unwraps `info` for `list`.
fn get_argument_or_parameter_list_info(
    program: &dyn tsc_checker::checker_types::Program,
    node: NodeId,
    source_file: NodeId,
    c: &mut Checker,
) -> Option<ArgumentOrParameterListInfo> {
    let (list, argument_index) =
        get_argument_or_parameter_list_and_index(program, node, source_file, c)?;
    let argument_count = get_argument_count(
        program,
        node,
        list.as_ref(),
        source_file,
        c,
    );
    let arguments_span = get_applicable_span_for_arguments(
        program,
        list.as_ref(),
        Some(node),
        source_file,
    );
    Some(ArgumentOrParameterListInfo {
        list,
        argument_index,
        argument_count,
        arguments_span,
    })
}

/// `getArgumentOrParameterListAndIndex`.
fn get_argument_or_parameter_list_and_index(
    program: &dyn tsc_checker::checker_types::Program,
    node: NodeId,
    source_file: NodeId,
    c: &mut Checker,
) -> Option<(Option<NodeList>, usize)> {
    let nodes = program.nodes(source_file.file_index());
    if nodes[node].kind == Kind::LessThanToken || nodes[node].kind == Kind::OpenParenToken {
        // Find the list that starts right *after* the < or ( token.
        // If the user has just opened a list, consider the item to the right.
        let list = get_child_list_that_starts_with_opener_token(
            &nodes,
            nodes[node].parent.expect("parent"),
            nodes[node].kind,
        );
        debug::assert_!(list.is_some(), "expected list");
        return Some((list, 0));
    }
    // Must be in a CommaToken or a close paren token.
    drop(nodes);
    let list = {
        let mut nodes_mut = program.nodes_mut(source_file.file_index());
        find_containing_list(&mut nodes_mut, node, source_file)
    }?;
    let argument_index = get_argument_index(program, node, Some(&list), source_file, c);
    Some((Some(list), argument_index))
}

/// `getChildListThatStartsWithOpenerToken`.
fn get_child_list_that_starts_with_opener_token(
    nodes: &[Node],
    parent: NodeId,
    opener_token: Kind,
) -> Option<NodeList> {
    if ast::is_call_or_new_expression(&nodes[parent]) {
        if opener_token == Kind::OpenParenToken {
            return nodes[parent].argument_list().cloned();
        }
        return nodes[parent].type_argument_list().cloned();
    }
    if opener_token == Kind::LessThanToken {
        return nodes[parent].type_parameter_list().cloned();
    }
    nodes[parent].parameter_list().cloned()
}

/// `getApplicableSpanForArguments`.
fn get_applicable_span_for_arguments(
    program: &dyn tsc_checker::checker_types::Program,
    argument_list: Option<&NodeList>,
    node: Option<NodeId>,
    source_file: NodeId,
) -> TextRange {
    let nodes = program.nodes(source_file.file_index());
    if argument_list.is_none() && node.is_some() {
        let node = node.unwrap();
        // The list or argument is empty. Parenthesize on the span of the first argument.
        let span_start = nodes[node].end();
        let text = nodes[source_file].as_source_file().text().to_string();
        let mut span_end = skip_trivia(&text, nodes[node].end());
        span_end = ensure_minimum_span_size(span_start, span_end);
        return TextRange::new(span_start, span_end);
    }
    let argument_list = argument_list.expect("argument list");
    let applicable_span_start = argument_list.pos();
    let text = nodes[source_file].as_source_file().text().to_string();
    let mut applicable_span_end = skip_trivia(&text, argument_list.end());
    applicable_span_end = ensure_minimum_span_size(applicable_span_start, applicable_span_end);
    TextRange::new(applicable_span_start, applicable_span_end)
}

/// `ensureMinimumSpanSize`.
fn ensure_minimum_span_size(pos: TextPos, end: TextPos) -> TextPos {
    if end - pos > 1 {
        return end;
    }
    end + 1
}

/// `getSpreadElementCount`.
fn get_spread_element_count(
    cb: &mut Checker,
    element: NodeId,
    nodes: &[Node],
) -> usize {
    debug::assert_!(ast::is_spread_element(&nodes[element]));
    let spread_type = cb.get_type_at_location(
        nodes[element].expression().expect("spread expression"),
    );
    if tsc_checker::checker_core::is_tuple_type(&cb.types, spread_type) {
        let target = cb.types.target_tuple_type(spread_type).expect("tuple target");
        let tuple = cb.types.get_ref(target).as_tuple_type();
        let element_flags = tuple.element_flags();
        let fixed_length = tuple.fixed_length();
        if fixed_length == 0 {
            return 0;
        }
        let first_optional_index = element_flags
            .iter()
            .position(|f| !f.intersects(tsc_checker::types::ElementFlags::REQUIRED));
        let required_args = first_optional_index.unwrap_or(fixed_length);
        if required_args > 0 {
            return required_args;
        }
    }
    1
}

/// `getArgumentIndexOrCount`.
fn get_argument_index_or_count(
    program: &dyn tsc_checker::checker_types::Program,
    arguments: &[NodeId],
    node: Option<NodeId>,
    source_file: NodeId,
    c: &mut Checker,
) -> usize {
    let nodes = program.nodes(source_file.file_index());
    let cb = &mut *c;
    let mut argument_index = 0usize;
    let mut skip_comma = false;
    for &arg in arguments {
        if let Some(n) = node
            && arg == n
        {
            if !skip_comma && nodes[arg].kind == Kind::CommaToken {
                argument_index += 1;
            }
            return argument_index;
        }
        if ast::is_spread_element(&nodes[arg]) {
            argument_index += get_spread_element_count(cb, arg, &nodes);
            skip_comma = true;
            continue;
        }
        if nodes[arg].kind != Kind::CommaToken {
            argument_index += 1;
            skip_comma = true;
            continue;
        }
        if skip_comma {
            skip_comma = false;
            continue;
        }
        argument_index += 1;
    }
    if node.is_some() {
        return argument_index;
    }
    let mut argument_count = argument_index;
    if let Some(&last) = arguments.last()
        && nodes[last].kind == Kind::CommaToken
    {
        argument_count = argument_index + 1;
    }
    argument_count
}

/// `getTokenFromNodeList`.
fn get_token_from_node_list(
    program: &dyn tsc_checker::checker_types::Program,
    node_list: Option<&NodeList>,
    node_list_parent: Option<NodeId>,
    source_file: NodeId,
) -> Vec<NodeId> {
    let (Some(node_list), Some(node_list_parent)) = (node_list, node_list_parent) else {
        return Vec::new();
    };
    let mut left = node_list.loc.pos();
    let mut node_list_index = 0usize;
    let mut tokens = Vec::new();
    let nl_nodes = node_list.nodes().to_vec();
    while left < node_list.loc.end() {
        let next = {
            let nodes = program.nodes(source_file.file_index());
            if nl_nodes.len() > node_list_index && left == nodes[nl_nodes[node_list_index]].pos() {
                Some(nl_nodes[node_list_index])
            } else {
                None
            }
        };
        if let Some(next) = next {
            tokens.push(next);
            left = program.nodes(source_file.file_index())[next].end();
            node_list_index += 1;
        } else {
            let mut nodes_mut = program.nodes_mut(source_file.file_index());
            let (text, language_variant) = {
                let sf = nodes_mut[source_file].as_source_file();
                (sf.text.clone(), sf.language_variant)
            };
            let mut scanner = Scanner::new();
            scanner.set_text(&text);
            scanner.set_language_variant(language_variant);
            scanner.reset_pos(left as usize);
            scanner.scan();
            let token = scanner.token();
            let token_full_start = scanner.token_full_start() as TextPos;
            let token_end = scanner.token_end() as TextPos;
            let token_flags = scanner.token_flags();
            tokens.push(ast::get_or_create_token(
                &mut nodes_mut,
                source_file,
                token,
                token_full_start,
                token_end,
                node_list_parent,
                token_flags,
            ));
            left = token_end;
        }
    }
    tokens
}

/// `getArgumentIndex`.
fn get_argument_index(
    program: &dyn tsc_checker::checker_types::Program,
    node: NodeId,
    arguments: Option<&NodeList>,
    source_file: NodeId,
    c: &mut Checker,
) -> usize {
    let nodes = program.nodes(source_file.file_index());
    let parent = nodes[node].parent;
    let token_list = get_token_from_node_list(program, arguments, parent, source_file);
    get_argument_index_or_count(program, &token_list, Some(node), source_file, c)
}

/// `getArgumentCount`.
fn get_argument_count(
    program: &dyn tsc_checker::checker_types::Program,
    node: NodeId,
    arguments: Option<&NodeList>,
    source_file: NodeId,
    c: &mut Checker,
) -> usize {
    let nodes = program.nodes(source_file.file_index());
    let parent = nodes[node].parent;
    let token_list = get_token_from_node_list(program, arguments, parent, source_file);
    get_argument_index_or_count(program, &token_list, None, source_file, c)
}

/// `getImmediatelyContainingArgumentInfo` — the shim-compatible public entry
/// used by `completions.rs` (`getArgumentInfoForCompletions`). Mirrors
/// `getImmediatelyContainingArgumentInfo` in Go; the `nodes`/`type_checker`
/// are the caller's arena view and checker — the implementation resolves its
/// own arena handles through `type_checker.program`.
pub(crate) fn get_immediately_containing_argument_info(
    nodes: &mut Vec<Node>,
    node: NodeId,
    position: TextPos,
    file: NodeId,
    type_checker: &mut Checker,
) -> Option<ArgumentListInfo> {
    let _ = nodes;
    let program = type_checker.program.clone().expect("program");
    get_immediately_containing_argument_info_impl(
        &checker_types::ProgramPtr::from_rc(&program),
        node,
        position,
        file,
        type_checker,
    )
}

/// `getCandidateOrTypeInfo`.
fn get_candidate_or_type_info(
    program: &dyn tsc_checker::checker_types::Program,
    argument_info: &ArgumentListInfo,
    c: &Rc<RefCell<Checker>>,
    source_file: NodeId,
    starting_token: NodeId,
    only_use_syntactic_owners: bool,
) -> Option<CandidateOrTypeInfo> {
    if only_use_syntactic_owners
        && !is_syntactic_owner(
            program,
            starting_token,
            &argument_info.invocation,
            source_file,
        )
    {
        return None;
    }
    if let Some(call_invocation) = &argument_info.invocation.call_invocation {
        let nodes = program.nodes(source_file.file_index());
        let _ = &nodes;
        let (resolved_signature, candidates) = {
            let mut cb = c.borrow_mut();
            tsc_checker::services::get_resolved_signature_for_signature_help(
                &mut cb,
                &nodes[..],
                call_invocation.node,
                argument_info.argument_count as i32,
            )
        };
        if !candidates.is_empty() {
            return Some(CandidateOrTypeInfo {
                candidate_info: Some(CandidateInfo {
                    candidates,
                    resolved_signature: resolved_signature.unwrap_or(SignatureId::NONE),
                    call_target: get_expression_from_invocation(&argument_info.invocation),
                }),
                type_info: None,
            });
        }
        let candidates2 = {
            let mut cb = c.borrow_mut();
            let called = get_expression_from_invocation(&argument_info.invocation);
            get_possible_generic_signatures(called, argument_info.argument_count as i32, &mut cb)
        };
        if !candidates2.is_empty() {
            return Some(CandidateOrTypeInfo {
                candidate_info: Some(CandidateInfo {
                    candidates: candidates2.clone(),
                    resolved_signature: *candidates2.first().expect("first"),
                    call_target: get_expression_from_invocation(&argument_info.invocation),
                }),
                type_info: None,
            });
        }
        return None;
    }
    if argument_info.invocation.contextual_invocation.is_some() {
        return Some(CandidateOrTypeInfo {
            candidate_info: Some(CandidateInfo {
                candidates: vec![
                    argument_info
                        .invocation
                        .contextual_invocation
                        .as_ref()
                        .unwrap()
                        .signature,
                ],
                resolved_signature: argument_info
                    .invocation
                    .contextual_invocation
                    .as_ref()
                    .unwrap()
                    .signature,
                call_target: get_expression_from_invocation(&argument_info.invocation),
            }),
            type_info: None,
        });
    }
    debug::assert_!(argument_info.invocation.type_args_invocation.is_some());
    let type_args = argument_info.invocation.type_args_invocation.as_ref().unwrap();
    let called = type_args.called;
    let call_target = {
        let nodes = program.nodes(source_file.file_index());
        let _ = &nodes;
        let mut cb = c.borrow_mut();
        cb.get_symbol_at_location_api(called)
    };
    if let Some(call_target) = call_target {
        return Some(CandidateOrTypeInfo {
            candidate_info: None,
            type_info: Some(call_target),
        });
    }
    let symbol = {
        let mut cb = c.borrow_mut();
        cb.get_symbol_at_location_api(called)
    };
    if let Some(symbol) = symbol {
        return Some(CandidateOrTypeInfo {
            candidate_info: None,
            type_info: Some(symbol),
        });
    }
    None
}

/// `isSyntacticOwner`.
fn is_syntactic_owner(
    program: &dyn tsc_checker::checker_types::Program,
    starting_token: NodeId,
    node_invocation: &Invocation,
    source_file: NodeId,
) -> bool {
    let node = match &node_invocation.call_invocation {
        Some(ci) => ci.node,
        None => return true,
    };
    let nodes = program.nodes(source_file.file_index());
    if !ast::is_call_or_new_expression(&nodes[node]) {
        return false;
    }
    drop(nodes);
    let invocation_children = {
        let mut nodes_mut = program.nodes_mut(source_file.file_index());
        get_children_from_non_jsdoc_node(&mut nodes_mut, node, source_file)
    };
    let nodes = program.nodes(source_file.file_index());
    match nodes[starting_token].kind {
        Kind::OpenParenToken | Kind::CommaToken => invocation_children.contains(&starting_token),
        Kind::LessThanToken => {
            // A type argument list.
            let expression = nodes[node].expression().expect("expression");
            contains_preceding_token(program, starting_token, source_file, expression)
        }
        _ => false,
    }
}

/// `containsPrecedingToken`.
fn contains_preceding_token(
    program: &dyn tsc_checker::checker_types::Program,
    starting_token: NodeId,
    source_file: NodeId,
    container: NodeId,
) -> bool {
    let nodes = program.nodes(source_file.file_index());
    let pos = nodes[starting_token].pos();
    let mut current_parent = nodes[starting_token].parent;
    drop(nodes);
    while let Some(parent) = current_parent {
        let preceding_token = {
            let mut nodes_mut = program.nodes_mut(source_file.file_index());
            tsc_astnav::tokens::find_preceding_token_ex(
                &mut nodes_mut,
                source_file,
                pos,
                Some(parent),
                true, /*excludeJsdoc*/
            )
        };
        if let Some(preceding_token) = preceding_token {
            let nodes = program.nodes(source_file.file_index());
            return range_contains_range(&nodes[container].loc, &nodes[preceding_token].loc);
        }
        let nodes = program.nodes(source_file.file_index());
        current_parent = nodes[parent].parent;
    }
    false
}

/// `createJSSignatureHelpItems`.
impl<'h> LanguageService<'h> {
    fn create_js_signature_help_items(
        &self,
        ctx: &Context,
        argument_info: &ArgumentListInfo,
        program: &Rc<Program>,
        c: &Rc<RefCell<Checker>>,
        source_file: NodeId,
    ) -> Option<lsproto::SignatureHelp> {
        let _ = ctx;
        if argument_info.invocation.contextual_invocation.is_some() {
            return None;
        }
        // We only need the parameter name to offer signature help
        // and we can offer signature help on all js expressions.
        // So we can use a simpler approach.
        let expression = get_expression_from_invocation(&argument_info.invocation);
        let nodes = program.nodes(source_file.file_index());
        if !ast::is_property_access_expression(&nodes[expression]) {
            return None;
        }
        let name = nodes[expression]
            .name()
            .map(|n| nodes[n].text(&nodes).into_owned());
        let name = name?;
        for file in program.source_files() {
            let declaration = find_signature_help_from_named_declarations(
                program,
                file,
                &name,
                argument_info,
                c,
            );
            if let Some(declaration) = declaration {
                let symbol = {
                    let file_nodes = program.nodes(file.file_index());
                    file_nodes[declaration].symbol()
                };
                let Some(symbol) = symbol else {
                    return None;
                };
                let t = {
                    let mut cb = c.borrow_mut();
                    cb.get_type_of_symbol_at_location(symbol, Some(declaration))
                };
                let call_signatures = {
                    let mut cb = c.borrow_mut();
                    cb.get_call_signatures(t)
                };
                if !call_signatures.is_empty() {
                    return self.create_signature_help_items(
                        ctx,
                        &call_signatures,
                        call_signatures[0],
                        argument_info,
                        source_file,
                        c,
                        true, /*useFullPrefix*/
                        program,
                    );
                }
            }
        }
        None
    }
}

/// `findSignatureHelpFromNamedDeclarations`.
fn find_signature_help_from_named_declarations(
    program: &Rc<Program>,
    source_file: NodeId,
    name: &str,
    argument_info: &ArgumentListInfo,
    c: &Rc<RefCell<Checker>>,
) -> Option<NodeId> {
    let _ = argument_info;
    let _ = c;
    fn visit(
        program: &Rc<Program>,
        nodes: &[Node],
        node: NodeId,
        name: &str,
        result: &mut Option<NodeId>,
    ) {
        if result.is_some() {
            return;
        }
        let decl_name = ast::get_declaration_name(nodes, node);
        if decl_name == name && nodes[node].symbol().is_some() {
            *result = Some(node);
            return;
        }
        let mut children = Vec::new();
        nodes[node].for_each_child(nodes, &mut |child| {
            children.push(child);
            false
        });
        for child in children {
            visit(program, nodes, child, name, result);
            if result.is_some() {
                return;
            }
        }
    }
    let nodes = program.nodes(source_file.file_index());
    let mut result = None;
    visit(program, &nodes, source_file, name, &mut result);
    result
}
