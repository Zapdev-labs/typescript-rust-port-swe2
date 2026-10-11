// Ported from tsc/internal/ls/codelens.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `*ast.Node` → `NodeId`; `*ast.SourceFile` → `NodeId`; `*ast.Symbol` →
//   `SymbolId`.
// - `provideSymbolsAndEntriesAtPosition` is reused from
//   `findallreferences.rs` (exported `pub(crate)` there).
// - `serde_json` is not a direct dependency of this crate, so the
//   `[]any{uri, position, locations}` command-argument list is built by
//   marshaling a `Serialize` tuple to raw JSON via
//   `NotificationInfo::new_notification_message` and unmarshaling it back
//   through `RequestMessage::unmarshal_params` — `Vec<serde_json::Value>`
//   is inferred from `cmd.arguments`, so the crate never needs naming.
// - `supplementalFileIndex`/`sourceFileForSupplementalFileIndex` are private
//   in `completions.rs`; local copies are kept here for the same reason.
// - The AST walk keeps Go's `lastSymbol` save/restore across
//   `ForEachChild` so lenses are not duplicated across overloads.

use std::collections::HashSet;

use tsc_ast::{self as ast, ModifierFlags, Node, NodeId, SymbolId};
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_diagnostics as diagnostics;
use tsc_lsconv::converters::source_file_script;
use tsc_lsproto as lsproto;
use tsc_lsutil::userpreferences_generated::CodeLensUserPreferences;
use tsc_scanner::scanner::skip_trivia;
use tsc_spanmap::Feature;

use crate::api::Error;
use crate::findallreferences::{CrossProjectOrchestrator, SymbolEntryTransformOptions};
use crate::languageservice::LanguageService;

impl<'h> LanguageService<'h> {
    /// `ProvideCodeLenses`.
    pub fn provide_code_lenses(
        &self,
        ctx: &Context,
        document_uri: &lsproto::DocumentUri,
    ) -> Result<lsproto::CodeLensResponse, Error> {
        let (_program, file) = self.get_program_and_file(document_uri);

        let user_prefs = &self.user_preferences().code_lens_user_preferences;
        if !user_prefs.references_code_lens_enabled.is_true()
            && !user_prefs.implementations_code_lens_enabled.is_true()
        {
            return Ok(lsproto::CodeLensResponse::default());
        }

        let program = self.get_program();
        let mut result: Vec<lsproto::CodeLens> = Vec::new();
        let mut seen: HashSet<CodeLensKey> = HashSet::new();
        let projections: Vec<NodeId> = {
            let nodes = program.nodes(file.file_index());
            let mut projections = vec![file];
            projections
                .extend_from_slice(nodes[file].as_source_file().supplemental_source_files());
            projections
        };

        for &projection in &projections {
            let nodes = program.nodes(projection.file_index());
            // Keeps track of the last symbol to avoid duplicating code lenses
            // across overloads.
            let mut last_symbol: Option<SymbolId> = None;
            visit_code_lens_node(
                self,
                ctx,
                document_uri,
                projection,
                projection,
                &nodes,
                &user_prefs,
                &mut last_symbol,
                &mut result,
                &mut seen,
            );
        }

        Ok(lsproto::CodeLensResponse {
            code_lenses: Some(result),
        })
    }

    /// `ResolveCodeLens`.
    pub fn resolve_code_lens(
        &self,
        ctx: &Context,
        code_lens: &mut lsproto::CodeLens,
        show_locations_command_name: Option<&str>,
        orchestrator: Option<&dyn CrossProjectOrchestrator<'h>>,
    ) -> Result<(), Error> {
        let data = match &code_lens.data {
            Some(data) => data.clone(),
            // Go would nil-dereference `codeLens.Data`; a lens without data
            // is invalid input, so report it as an error instead.
            None => {
                return Err(Error::Message(
                    "codeLens is missing data".to_string(),
                ));
            }
        };
        let uri = data.uri.clone();
        let text_doc = lsproto::TextDocumentIdentifier { uri: uri.clone() };
        let (program, file) = self.get_program_and_file(&uri);
        let Some(file) = ({
            let nodes = program.nodes(file.file_index());
            source_file_for_supplemental_file_index(&nodes, file, data.supplemental_file_index)
        }) else {
            return Err(Error::Message(format!(
                "supplemental source file index not found: {}",
                data.supplemental_file_index.unwrap_or(-1)
            )));
        };
        let locale = tsc_locale::from_context(ctx);
        let mut locs: Vec<lsproto::Location> = Vec::new();
        let mut lens_title = String::new();
        match data.kind {
            k if k == lsproto::CodeLensKind::References => {
                let (data, _) = self.provide_symbols_and_entries_at_position(
                    ctx,
                    &program,
                    file,
                    data.position,
                    false, /*isRename*/
                    false, /*implementations*/
                );
                let references_resp = self.provide_references_from_data(
                    ctx,
                    &lsproto::ReferenceParams {
                        text_document: text_doc,
                        position: code_lens.range.start.clone(),
                        context: Some(lsproto::ReferenceContext {
                            // Don't include the declaration in the
                            // references count.
                            include_declaration: false,
                        }),
                        ..Default::default()
                    },
                    orchestrator,
                    &data,
                )?;
                if let Some(locations) = references_resp.locations {
                    locs = locations;
                }

                if locs.len() == 1 {
                    lens_title = diagnostics::X_1_reference.localize(&locale, &[""; 0]);
                } else {
                    lens_title = diagnostics::X_0_references
                        .localize(&locale, &[locs.len().to_string()]);
                }
            }
            k if k == lsproto::CodeLensKind::Implementations => {
                let (data, _) = self.provide_symbols_and_entries_at_position(
                    ctx,
                    &program,
                    file,
                    data.position,
                    false, /*isRename*/
                    true,  /*implementations*/
                );
                let implementations = self.provide_implementations_from_data(
                    ctx,
                    &lsproto::ImplementationParams {
                        text_document: text_doc,
                        position: code_lens.range.start.clone(),
                        ..Default::default()
                    },
                    // "Force" link support to be false so that we only get
                    // `Locations` back, and don't include the "current" node
                    // in the results.
                    SymbolEntryTransformOptions {
                        require_locations_result: true,
                        drop_origin_nodes: true,
                    },
                    orchestrator,
                    &data,
                )?;
                if let Some(locations) = implementations.locations {
                    locs = locations;
                }

                if locs.len() == 1 {
                    lens_title = diagnostics::X_1_implementation.localize(&locale, &[""; 0]);
                } else {
                    lens_title = diagnostics::X_0_implementations
                        .localize(&locale, &[locs.len().to_string()]);
                }
            }
            _ => {}
        }

        let mut cmd = lsproto::Command {
            title: lens_title,
            ..Default::default()
        };
        if !locs.is_empty() {
            if let Some(command_name) = show_locations_command_name {
                cmd.command = command_name.to_string();
                // `Arguments: []any{codeLens.Data.URI, codeLens.Range.Start,
                // locs}` — see the `serde_json` PORT note above: the tuple
                // marshals to `[uri, position, locations]` and unmarshals
                // back into `Vec<serde_json::Value>` by inference.
                let msg = lsproto::NotificationInfo::<_>::new(
                    lsproto::Method::TextDocumentReferences,
                )
                .new_notification_message((&uri, &code_lens.range.start, &locs));
                cmd.arguments = msg.unmarshal_params().ok();
            }
        }

        code_lens.command = Some(cmd);
        Ok(())
    }

    /// `newCodeLensForNode`.
    fn new_code_lens_for_node(
        &self,
        file_uri: &lsproto::DocumentUri,
        file: NodeId,
        node: NodeId,
        kind: lsproto::CodeLensKind,
        nodes: &[Node],
    ) -> Option<lsproto::CodeLens> {
        let node_for_range = nodes[node].name().unwrap_or(node);
        let pos = skip_trivia(
            nodes[file].as_source_file().text(),
            nodes[node_for_range].pos(),
        );
        let script = source_file_script(file, nodes);
        let (lsp_range, fidelity) = self.converters.to_lsp_range_for_feature(
            &script,
            TextRange::new(pos, nodes[node].end()),
            Feature::CodeLens,
        );
        if fidelity.is_none() {
            return None;
        }

        Some(lsproto::CodeLens {
            range: lsp_range,
            command: None,
            data: Some(lsproto::CodeLensData {
                kind,
                uri: file_uri.clone(),
                position: pos,
                supplemental_file_index: supplemental_file_index(nodes, file),
            }),
        })
    }

}

/// `codeLensKey`.
#[derive(Clone, PartialEq, Eq, Hash)]
struct CodeLensKey {
    kind: lsproto::CodeLensKind,
    start_line: u32,
    start_character: u32,
    end_line: u32,
    end_character: u32,
}

/// `keyForCodeLens`.
fn key_for_code_lens(code_lens: &lsproto::CodeLens) -> CodeLensKey {
    CodeLensKey {
        kind: code_lens
            .data
            .as_ref()
            .map(|d| d.kind.clone())
            .unwrap_or_default(),
        start_line: code_lens.range.start.line,
        start_character: code_lens.range.start.character,
        end_line: code_lens.range.end.line,
        end_character: code_lens.range.end.character,
    }
}

/// Recursive workhorse for `ProvideCodeLenses`'s `visit` closure.
#[allow(clippy::too_many_arguments)]
fn visit_code_lens_node(
    l: &LanguageService<'_>,
    ctx: &Context,
    document_uri: &lsproto::DocumentUri,
    projection: NodeId,
    node: NodeId,
    nodes: &[Node],
    user_prefs: &CodeLensUserPreferences,
    last_symbol: &mut Option<SymbolId>,
    result: &mut Vec<lsproto::CodeLens>,
    seen: &mut HashSet<CodeLensKey>,
) {
    if ctx.is_cancelled() {
        return;
    }

    let current_symbol = nodes[node].symbol();
    if *last_symbol != current_symbol {
        *last_symbol = current_symbol;

        if user_prefs.references_code_lens_enabled.is_true()
            && is_valid_reference_lens_node(&nodes[node], nodes, user_prefs)
        {
            if let Some(code_lens) = l.new_code_lens_for_node(
                document_uri,
                projection,
                node,
                lsproto::CodeLensKind::References,
                nodes,
            ) {
                if seen.insert(key_for_code_lens(&code_lens)) {
                    result.push(code_lens);
                }
            }
        }

        if user_prefs.implementations_code_lens_enabled.is_true()
            && is_valid_implementations_code_lens_node(&nodes[node], nodes, user_prefs)
        {
            if let Some(code_lens) = l.new_code_lens_for_node(
                document_uri,
                projection,
                node,
                lsproto::CodeLensKind::Implementations,
                nodes,
            ) {
                if seen.insert(key_for_code_lens(&code_lens)) {
                    result.push(code_lens);
                }
            }
        }
    }

    let saved_last_symbol = *last_symbol;
    nodes[node].for_each_child(nodes, &mut |child| {
        visit_code_lens_node(
            l,
            ctx,
            document_uri,
            projection,
            child,
            nodes,
            user_prefs,
            last_symbol,
            result,
            seen,
        );
        ctx.is_cancelled()
    });
    *last_symbol = saved_last_symbol;
}

/// `isValidImplementationsCodeLensNode`.
fn is_valid_implementations_code_lens_node(
    node: &Node,
    nodes: &[Node],
    user_prefs: &CodeLensUserPreferences,
) -> bool {
    match node.kind {
        // Always show on interfaces
        // TODO: ast.KindTypeAliasDeclaration?
        ast::Kind::InterfaceDeclaration => true,

        // If configured, show on interface methods
        ast::Kind::MethodSignature => {
            user_prefs
                .implementations_code_lens_show_on_interface_methods
                .is_true()
                && node.parent.is_some_and(|p| nodes[p].kind == ast::Kind::InterfaceDeclaration)
        }

        // If configured, show on all class methods - but not private ones.
        ast::Kind::MethodDeclaration
            if user_prefs
                .implementations_code_lens_show_on_all_class_methods
                .is_true()
                && node.parent.is_some_and(|p| nodes[p].kind == ast::Kind::ClassDeclaration) =>
        {
            !ast::has_modifier(node, ModifierFlags::PRIVATE)
                && node.name().is_some_and(|n| nodes[n].kind != ast::Kind::PrivateIdentifier)
        }

        // Always show on abstract classes/properties/methods
        ast::Kind::MethodDeclaration
        | ast::Kind::ClassDeclaration
        | ast::Kind::Constructor
        | ast::Kind::GetAccessor
        | ast::Kind::SetAccessor
        | ast::Kind::PropertyDeclaration => ast::has_modifier(node, ModifierFlags::ABSTRACT),

        _ => false,
    }
}

/// `isValidReferenceLensNode`.
fn is_valid_reference_lens_node(
    node: &Node,
    nodes: &[Node],
    user_prefs: &CodeLensUserPreferences,
) -> bool {
    match node.kind {
        ast::Kind::FunctionDeclaration
            if user_prefs
                .references_code_lens_show_on_all_functions
                .is_true() =>
        {
            true
        }

        ast::Kind::FunctionDeclaration | ast::Kind::VariableDeclaration => {
            ast::get_combined_modifier_flags(node.id, nodes)
                .intersects(ModifierFlags::EXPORT)
        }

        ast::Kind::ClassDeclaration
        | ast::Kind::InterfaceDeclaration
        | ast::Kind::TypeAliasDeclaration
        | ast::Kind::EnumDeclaration
        | ast::Kind::EnumMember => true,

        // Don't show if child and parent have same start
        // For https://github.com/microsoft/vscode/issues/90396
        // !!!
        ast::Kind::MethodDeclaration
        | ast::Kind::MethodSignature
        | ast::Kind::Constructor
        | ast::Kind::GetAccessor
        | ast::Kind::SetAccessor
        | ast::Kind::PropertyDeclaration
        | ast::Kind::PropertySignature => node.parent.is_some_and(|p| {
            matches!(
                nodes[p].kind,
                ast::Kind::ClassDeclaration
                    | ast::Kind::InterfaceDeclaration
                    | ast::Kind::TypeLiteral
            )
        }),

        _ => false,
    }
}

/// `supplementalFileIndex` — local copy (the canonical copy is private in
/// `completions.rs`).
fn supplemental_file_index(nodes: &[Node], file: NodeId) -> Option<i32> {
    let sf = nodes[file].as_source_file();
    let canonical = sf.canonical_source_file()?;
    for (i, supplemental) in nodes[canonical]
        .as_source_file()
        .supplemental_source_files()
        .iter()
        .enumerate()
    {
        if *supplemental == file {
            return Some(i as i32);
        }
    }
    panic!("supplemental source file is not linked from its canonical source file")
}

/// `sourceFileForSupplementalFileIndex` — local copy (the canonical copy is
/// private in `completions.rs`).
fn source_file_for_supplemental_file_index(
    nodes: &[Node],
    file: NodeId,
    index: Option<i32>,
) -> Option<NodeId> {
    let index = index?;
    if index < 0 {
        return None;
    }
    nodes[file]
        .as_source_file()
        .supplemental_source_files()
        .get(index as usize)
        .copied()
}
