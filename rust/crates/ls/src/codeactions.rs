// Ported from tsc/internal/ls/codeactions.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's `CodeFixProvider` holds func fields; here they are plain `fn`
// pointers over `CodeFixContext<'_, '_>` (elided lifetimes give the same
// HRTB Go's closures have). `CodeFixContext` carries borrows (`program`,
// `ls`, `diagnostic`, `params`) rather than the shared pointers Go stores.
// `getAllDiagnostics` is a local copy — `diagnostics.go` is a sibling-owned
// skeleton.

use std::cmp::Ordering;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::rc::Rc;

use tsc_ast::NodeId;
use tsc_ast::diagnostic::{DiagnosticRef, lock_diagnostic};
use tsc_compiler::program::Program;
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_lsconv::converters::file_name_to_document_uri;
use tsc_lsproto as lsproto;
use tsc_spanmap::Feature;

use crate::api::Error;
use crate::codeactions_fixclassincorrectlyimplementsinterface::FIX_CLASS_INCORRECTLY_IMPLEMENTS_INTERFACE_PROVIDER;
use crate::codeactions_fixmissingtypeannotation::ISOLATED_DECLARATIONS_FIX_PROVIDER;
use crate::codeactions_importfixes::IMPORT_FIX_PROVIDER;
use crate::languageservice::LanguageService;

/// `CodeFixProvider` represents a provider for a specific type of code fix.
pub struct CodeFixProvider {
    /// `ErrorCodes`.
    pub error_codes: &'static [i32],
    /// `GetCodeActions`.
    pub get_code_actions:
        fn(&Context, &CodeFixContext<'_, '_>) -> Result<Vec<CodeAction>, Error>,
    /// `FixIds`.
    #[allow(dead_code)] // kept for parity; Go only reads ErrorCodes/Get* here
    pub fix_ids: &'static [&'static str],
    /// `GetAllCodeActions` — `None` is Go's nil func field.
    pub get_all_code_actions: Option<
        fn(&Context, &CodeFixContext<'_, '_>) -> Result<Option<CombinedCodeActions>, Error>,
    >,
}

/// `CodeFixContext` contains the context needed to generate code fixes.
pub struct CodeFixContext<'a, 'h> {
    /// `SourceFile`.
    pub source_file: NodeId,
    /// `Span`.
    pub span: TextRange,
    /// `ErrorCode`.
    pub error_code: i32,
    /// `Program`.
    pub program: &'a Rc<Program>,
    /// `LS`.
    pub ls: &'a LanguageService<'h>,
    /// `Diagnostic`.
    pub diagnostic: Option<&'a lsproto::Diagnostic>,
    /// `Params`.
    pub params: Option<&'a lsproto::CodeActionParams>,
}

/// `CodeAction` represents a single code action fix.
pub struct CodeAction {
    /// `Description`.
    pub description: String,
    /// `Changes`.
    pub changes: Vec<lsproto::TextEdit>,
    /// `FixID`.
    pub fix_id: &'static str,
    /// `FixAllDescription`.
    #[allow(dead_code)]
    pub fix_all_description: String,
}

impl CodeAction {
    /// `Compare` defines a total ordering for `CodeAction` values, comparing
    /// description then text edits lexicographically. Used with binary-search
    /// dedup (`slices.BinarySearchFunc` in Go).
    pub fn compare(&self, other: &CodeAction) -> Ordering {
        if let c @ (Ordering::Less | Ordering::Greater) =
            self.description.cmp(&other.description)
        {
            return c;
        }
        if let c @ (Ordering::Less | Ordering::Greater) =
            self.changes.len().cmp(&other.changes.len())
        {
            return c;
        }
        for (a_edit, b_edit) in self.changes.iter().zip(other.changes.iter()) {
            if let c @ (Ordering::Less | Ordering::Greater) =
                ordering(a_edit.compare(b_edit))
            {
                return c;
            }
        }
        Ordering::Equal
    }
}

/// `CombinedCodeActions` represents combined code actions for fix-all
/// scenarios.
pub struct CombinedCodeActions {
    /// `Description`.
    pub description: String,
    /// `Changes`.
    pub changes: Vec<lsproto::TextEdit>,
}

/// `stringutil.Comparison` (i32) → `Ordering`.
fn ordering(c: i32) -> std::cmp::Ordering {
    c.cmp(&0)
}

/// `codeFixProviders` is the list of all registered code fix providers.
///
/// PORT: Go's `var xProvider = &CodeFixProvider{...}` values are
/// `LazyLock`s (diagnostic `.code()` is not const-evaluable); `&*PROVIDER`
/// yields the `&'static CodeFixProvider` Go would store.
pub(crate) fn code_fix_providers() -> [&'static CodeFixProvider; 3] {
    [
        &*IMPORT_FIX_PROVIDER,
        &*ISOLATED_DECLARATIONS_FIX_PROVIDER,
        &*FIX_CLASS_INCORRECTLY_IMPLEMENTS_INTERFACE_PROVIDER,
        // Add more code fix providers here as they are implemented
    ]
}

impl<'h> LanguageService<'h> {
    /// `ProvideCodeActions` returns code actions for the given range and
    /// context.
    pub fn provide_code_actions(
        &self,
        ctx: &Context,
        params: &lsproto::CodeActionParams,
    ) -> Result<lsproto::CodeActionResponse, Error> {
        let (program, file) = self.get_program_and_file(&params.text_document.uri);

        let mut actions: Vec<lsproto::CommandOrCodeAction> = Vec::new();

        if let Some(only) = params.context.as_ref().and_then(|c| c.only.as_ref()) {
            for kind in only {
                let matching_kinds = get_organize_imports_actions_for_kind(kind);
                for matching_kind in &matching_kinds {
                    let organize_action =
                        self.create_organize_imports_action(ctx, &program, file, matching_kind);
                    actions.push(organize_action);
                }

                if is_fix_all_kind(kind) {
                    let fix_all_action = self.create_fix_all_action(
                        ctx,
                        &program,
                        file,
                        &params.text_document.uri,
                    )?;
                    if let Some(fix_all_action) = fix_all_action {
                        actions.push(fix_all_action);
                    }
                }
            }
        }

        let diagnostics_present = params
            .context
            .as_ref()
            .is_some_and(|c| c.diagnostics.is_some());
        if diagnostics_present
            && wants_quick_fixes(params.context.as_ref().and_then(|c| c.only.as_ref()))
        {
            let mut fix_id_seen: HashMap<&'static str, &'static CodeFixProvider> = HashMap::new();

            // sorted for binary search dedup, dedup across all diagnostics and providers so
            // if multiple diags produce the same codefix, only one is returned
            let mut seen: Vec<CodeAction> = Vec::new();

            let nodes = program.nodes(file.file_index());
            for diag in params
                .context
                .as_ref()
                .and_then(|c| c.diagnostics.as_ref())
                .expect("diagnostics checked above")
            {
                let Some(code) = &diag.code else {
                    continue;
                };
                let Some(error_code) = code.integer else {
                    continue;
                };

                for provider in code_fix_providers() {
                    if !code_fix_provider_matches_lsp_diagnostic(provider, diag) {
                        continue;
                    }

                    let mapped_spans = self.converters.from_lsp_range_for_source_file(
                        file,
                        &nodes,
                        diag.range.clone(),
                        Feature::CodeActions,
                    );
                    for mapped in &mapped_spans {
                        let fix_context = CodeFixContext {
                            source_file: mapped.script.file,
                            span: mapped.span,
                            error_code,
                            program: &program,
                            ls: self,
                            diagnostic: Some(diag),
                            params: Some(params),
                        };

                        let provider_actions =
                            (provider.get_code_actions)(ctx, &fix_context)?;
                        for action in provider_actions {
                            let i = seen
                                .binary_search_by(|probe| probe.compare(&action))
                                .unwrap_or_else(|i| i);
                            if seen
                                .get(i)
                                .is_some_and(|s| s.compare(&action) == Ordering::Equal)
                            {
                                continue;
                            }
                            seen.insert(i, action);
                            let action = &seen[i];
                            actions.push(convert_to_lsp_code_action(
                                action,
                                diag,
                                &params.text_document.uri,
                            ));
                            if !action.fix_id.is_empty() {
                                fix_id_seen.insert(action.fix_id, provider);
                            }
                        }
                    }
                }
            }
            drop(nodes);

            let fix_all_actions = self.get_fix_all_quick_fixes(
                ctx,
                &program,
                file,
                &params.text_document.uri,
                &fix_id_seen,
            )?;
            actions.extend(fix_all_actions);
        }

        Ok(lsproto::CommandOrCodeActionArrayOrNull {
            command_or_code_action_array: Some(actions),
        })
    }

    /// `getFixAllQuickFixes` returns per-provider "Fix all in file" quickfix
    /// entries for providers that matched at least 2 diagnostics in the full
    /// file.
    fn get_fix_all_quick_fixes(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        file: NodeId,
        uri: &lsproto::DocumentUri,
        fix_id_seen: &HashMap<&'static str, &'static CodeFixProvider>,
    ) -> Result<Vec<lsproto::CommandOrCodeAction>, Error> {
        let mut actions: Vec<lsproto::CommandOrCodeAction> = Vec::new();

        // Deduplicate providers; multiple fixIds may map to the same provider.
        let mut seen: HashSet<*const CodeFixProvider> = HashSet::new();
        for provider in fix_id_seen.values() {
            if !seen.insert(*provider as *const CodeFixProvider) {
                continue;
            }
            let provider = *provider;

            let Some(get_all) = provider.get_all_code_actions else {
                continue;
            };

            if !has_multiple_fixable_diagnostics(ctx, program, file, provider.error_codes) {
                continue;
            }

            let fix_context = CodeFixContext {
                source_file: file,
                span: TextRange::default(),
                error_code: 0,
                program,
                ls: self,
                diagnostic: None,
                params: None,
            };
            let combined = get_all(ctx, &fix_context)?;
            if let Some(combined) = combined {
                if !combined.changes.is_empty() {
                    let kind = lsproto::CodeActionKind::QuickFix;
                    let changes = BTreeMap::from([(uri.clone(), combined.changes)]);
                    actions.push(lsproto::CommandOrCodeAction {
                        command: None,
                        code_action: Some(lsproto::CodeAction {
                            title: combined.description,
                            kind: Some(kind),
                            edit: Some(lsproto::WorkspaceEdit {
                                changes: Some(changes),
                                ..Default::default()
                            }),
                            ..Default::default()
                        }),
                    });
                }
            }
        }

        Ok(actions)
    }

    /// `createFixAllAction` creates a source.fixAll code action that applies
    /// all auto-fixable code fixes across the file.
    fn create_fix_all_action(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        file: NodeId,
        uri: &lsproto::DocumentUri,
    ) -> Result<Option<lsproto::CommandOrCodeAction>, Error> {
        let kind = lsproto::CodeActionKind::SOURCE_FIX_ALL_TS;
        let mut lsp_changes: BTreeMap<lsproto::DocumentUri, Vec<lsproto::TextEdit>> =
            BTreeMap::new();

        for provider in code_fix_providers() {
            let Some(get_all) = provider.get_all_code_actions else {
                continue;
            };

            let fix_context = CodeFixContext {
                source_file: file,
                span: TextRange::default(),
                error_code: 0,
                program,
                ls: self,
                diagnostic: None,
                params: None,
            };

            let combined = get_all(ctx, &fix_context)?;
            if let Some(combined) = combined {
                if !combined.changes.is_empty() {
                    lsp_changes
                        .entry(uri.clone())
                        .or_default()
                        .extend(combined.changes);
                }
            }
        }

        if lsp_changes.is_empty() {
            return Ok(None);
        }

        Ok(Some(lsproto::CommandOrCodeAction {
            command: None,
            code_action: Some(lsproto::CodeAction {
                title: tsc_diagnostics::Fix_All
                    .localize(&tsc_locale::from_context(ctx), &[""; 0]),
                kind: Some(kind),
                edit: Some(lsproto::WorkspaceEdit {
                    changes: Some(lsp_changes),
                    ..Default::default()
                }),
                ..Default::default()
            }),
        }))
    }

    /// `createOrganizeImportsAction` creates the organize imports code action.
    fn create_organize_imports_action(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        file: NodeId,
        kind: &lsproto::CodeActionKind,
    ) -> lsproto::CommandOrCodeAction {
        let title = get_organize_imports_action_title(ctx, kind);
        let changes = self.organize_imports(ctx, file, program, kind);
        if changes.is_empty() {
            return lsproto::CommandOrCodeAction {
                command: None,
                code_action: Some(lsproto::CodeAction {
                    title,
                    kind: Some(kind.clone()),
                    edit: Some(lsproto::WorkspaceEdit {
                        changes: Some(BTreeMap::new()),
                        ..Default::default()
                    }),
                    ..Default::default()
                }),
            };
        }

        let mut lsp_changes: BTreeMap<lsproto::DocumentUri, Vec<lsproto::TextEdit>> =
            BTreeMap::new();
        for (file_name, edits) in changes {
            let file_uri = file_name_to_document_uri(&file_name);
            lsp_changes.insert(file_uri, edits);
        }

        lsproto::CommandOrCodeAction {
            command: None,
            code_action: Some(lsproto::CodeAction {
                title,
                kind: Some(kind.clone()),
                edit: Some(lsproto::WorkspaceEdit {
                    changes: Some(lsp_changes),
                    ..Default::default()
                }),
                ..Default::default()
            }),
        }
    }
}

/// `hasMultipleFixableDiagnostics` returns true if the file has at least 2
/// diagnostics matching the given error codes. Checks all diagnostic sources
/// (semantic, syntactic, suggestion, declaration) to match
/// `ProvideDiagnostics`.
fn has_multiple_fixable_diagnostics(
    ctx: &Context,
    program: &Rc<Program>,
    file: NodeId,
    error_codes: &[i32],
) -> bool {
    let all_diags = get_all_diagnostics(ctx, program, file);
    let mut count = 0;
    for d in &all_diags {
        if is_fixable_diagnostic(d, error_codes) {
            count += 1;
            if count >= 2 {
                return true;
            }
        }
    }
    false
}

/// `getAllDiagnostics` collects all diagnostics for a file: syntactic,
/// semantic, suggestion, and (when declarations are emitted) declaration
/// diagnostics.
///
/// PORT(local): copied from `diagnostics.go` (sibling-owned skeleton).
pub(crate) fn get_all_diagnostics(
    ctx: &Context,
    program: &Rc<Program>,
    file: NodeId,
) -> Vec<DiagnosticRef> {
    let mut diags: Vec<DiagnosticRef> = Vec::new();
    let mut files = vec![file];
    {
        let nodes = program.nodes(file.file_index());
        files.extend_from_slice(nodes[file].as_source_file().supplemental_source_files());
    }
    for source_file in files {
        diags.extend(program.get_syntactic_diagnostics(ctx.clone(), Some(source_file)));
        diags.extend(program.get_semantic_diagnostics(ctx.clone(), Some(source_file)));
        diags.extend(program.get_suggestion_diagnostics(ctx.clone(), Some(source_file)));
        if program.options().get_emit_declarations() {
            diags.extend(
                program.get_declaration_diagnostics(ctx.clone(), Some(source_file)),
            );
        }
    }
    diags
}

/// `codeFixProviderMatchesLSPDiagnostic`.
fn code_fix_provider_matches_lsp_diagnostic(
    provider: &CodeFixProvider,
    diagnostic: &lsproto::Diagnostic,
) -> bool {
    if diagnostic.source.as_deref().is_some_and(|s| s != "ts") {
        return false;
    }
    diagnostic
        .code
        .as_ref()
        .and_then(|c| c.integer)
        .is_some_and(|code| contains_error_code(provider.error_codes, code))
}

/// PORT helper — `Converters<'a>` is invariant in `'a` and
/// `new_import_adder` requires `&'a Converters<'a>` where `'a` also binds
/// the (locally-scoped) auto-import `view` borrow, so `&ls.converters`
/// (`Converters<'h>`) cannot be passed directly. Reborrowing `ls.host` at
/// the short `'a` through this generic helper yields a `Converters<'a>`
/// whose inner lifetime the caller is free to pick as the import-adder's
/// short lifetime. Behavior is identical to `ls.converters` —
/// `host.converters()` builds the same converter set the `LanguageService`
/// cached at construction.
pub(crate) fn short_converters<'a, 'h: 'a>(
    ls: &'a LanguageService<'h>,
) -> tsc_lsconv::converters::Converters<'a> {
    ls.host.converters()
}

/// `isFixableDiagnostic`.
pub(crate) fn is_fixable_diagnostic(diagnostic: &DiagnosticRef, error_codes: &[i32]) -> bool {
    let d = lock_diagnostic(diagnostic);
    d.source().is_empty() && contains_error_code(error_codes, d.code())
}

/// `isFixAllKind` returns true if the requested kind matches source.fixAll.
fn is_fix_all_kind(kind: &lsproto::CodeActionKind) -> bool {
    kind.contains(&lsproto::CodeActionKind::SOURCE_FIX_ALL_TS)
}

/// `wantsQuickFixes` returns true if the Only filter is nil/empty (meaning all
/// kinds are wanted) or explicitly includes the quickfix kind.
fn wants_quick_fixes(only: Option<&Vec<lsproto::CodeActionKind>>) -> bool {
    match only {
        None => true,
        Some(only) if only.is_empty() => true,
        Some(only) => only
            .iter()
            .any(|kind| kind.contains(&lsproto::CodeActionKind::QuickFix)),
    }
}

/// `getOrganizeImportsActionTitle` returns the appropriate title for the
/// given organize imports kind.
fn get_organize_imports_action_title(
    ctx: &Context,
    kind: &lsproto::CodeActionKind,
) -> String {
    let loc = tsc_locale::from_context(ctx);
    if *kind == lsproto::CodeActionKind::SOURCE_REMOVE_UNUSED_IMPORTS_TS {
        tsc_diagnostics::Remove_Unused_Imports.localize(&loc, &[""; 0])
    } else if *kind == lsproto::CodeActionKind::SOURCE_SORT_IMPORTS_TS {
        tsc_diagnostics::Sort_Imports.localize(&loc, &[""; 0])
    } else {
        tsc_diagnostics::Organize_Imports.localize(&loc, &[""; 0])
    }
}

/// `getOrganizeImportsActionsForKind` returns the organize imports code
/// action kinds that should be returned for the given requested kind.
fn get_organize_imports_actions_for_kind(
    requested_kind: &lsproto::CodeActionKind,
) -> Vec<lsproto::CodeActionKind> {
    let organize_imports_kinds = [
        lsproto::CodeActionKind::SOURCE_ORGANIZE_IMPORTS_TS,
        lsproto::CodeActionKind::SOURCE_REMOVE_UNUSED_IMPORTS_TS,
        lsproto::CodeActionKind::SOURCE_SORT_IMPORTS_TS,
    ];

    let mut result: Vec<lsproto::CodeActionKind> = Vec::new();
    for organize_kind in &organize_imports_kinds {
        if requested_kind.contains(organize_kind) {
            result.push(organize_kind.clone());
        }
    }

    if result.contains(requested_kind) {
        return vec![requested_kind.clone()];
    }

    result
}

/// `containsErrorCode` checks if the error code is in the list.
pub(crate) fn contains_error_code(codes: &[i32], code: i32) -> bool {
    codes.contains(&code)
}

/// `convertToLSPCodeAction` converts an internal `CodeAction` to an LSP
/// `CodeAction`.
fn convert_to_lsp_code_action(
    action: &CodeAction,
    diag: &lsproto::Diagnostic,
    uri: &lsproto::DocumentUri,
) -> lsproto::CommandOrCodeAction {
    let kind = lsproto::CodeActionKind::QuickFix;
    let changes = BTreeMap::from([(uri.clone(), action.changes.clone())]);
    let diagnostics = vec![diag.clone()];

    lsproto::CommandOrCodeAction {
        command: None,
        code_action: Some(lsproto::CodeAction {
            title: action.description.clone(),
            kind: Some(kind),
            edit: Some(lsproto::WorkspaceEdit {
                changes: Some(changes),
                ..Default::default()
            }),
            diagnostics: Some(diagnostics),
            ..Default::default()
        }),
    }
}
