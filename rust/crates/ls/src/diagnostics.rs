// Ported from tsc/internal/ls/diagnostics.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::rc::Rc;

use tsc_ast::diagnostic::{
    DiagnosticFile, DiagnosticRef, lock_diagnostic, new_diagnostic,
};
use tsc_ast::{self as ast, NodeId};
use tsc_collections::OrderedMap;
use tsc_core::context::Context;
use tsc_core::text::TextRange;
use tsc_diagnostics::{self as diagnostics, Category};
use tsc_lsconv::converters::diagnostic_to_lsp_pull;
use tsc_lsproto::{self as lsproto};
use tsc_spanmap::{Fidelity, SpanMap};
use tsc_compiler::program::Program;

use crate::api::Error;
use crate::languageservice::LanguageService;

/// `getAllDiagnostics` collects all diagnostics for a file: syntactic, semantic,
/// suggestion, and (when declarations are emitted) declaration diagnostics.
fn get_all_diagnostics(
    ctx: &Context,
    program: &Rc<Program>,
    file: NodeId,
    nodes: &[ast::Node],
) -> Vec<DiagnosticRef> {
    let mut diags: Vec<DiagnosticRef> = Vec::new();
    let mut files: Vec<NodeId> = vec![file];
    files.extend_from_slice(nodes[file].as_source_file().supplemental_source_files());
    for source_file in files {
        diags.extend(program.get_syntactic_diagnostics(ctx.clone(), Some(source_file)));
        diags.extend(program.get_semantic_diagnostics(ctx.clone(), Some(source_file)));
        diags.extend(program.get_suggestion_diagnostics(ctx.clone(), Some(source_file)));
        if program.options().get_emit_declarations() {
            diags.extend(program.get_declaration_diagnostics(ctx.clone(), Some(source_file)));
        }
    }
    diags
}

impl<'h> LanguageService<'h> {
    /// `ProvideDiagnostics`.
    pub fn provide_diagnostics(
        &self,
        ctx: &Context,
        uri: lsproto::DocumentUri,
    ) -> Result<lsproto::DocumentDiagnosticResponse, Error> {
        let (program, file) = self.get_program_and_file(&uri);

        if self.user_preferences().validate_enabled.is_false() {
            let diagnostics: Vec<lsproto::Diagnostic> = Vec::new();
            return Ok(
                lsproto::RelatedFullDocumentDiagnosticReportOrUnchangedDocumentDiagnosticReport {
                    full_document_diagnostic_report: Some(
                        lsproto::RelatedFullDocumentDiagnosticReport {
                            kind: lsproto::StringLiteralFull,
                            items: Some(diagnostics),
                            ..Default::default()
                        },
                    ),
                    ..Default::default()
                },
            );
        }

        let diagnostics = {
            let nodes = program.nodes(file.file_index());
            get_all_diagnostics(ctx, &program, file, &nodes)
        };

        Ok(
            lsproto::RelatedFullDocumentDiagnosticReportOrUnchangedDocumentDiagnosticReport {
                full_document_diagnostic_report: Some(
                    lsproto::RelatedFullDocumentDiagnosticReport {
                        kind: lsproto::StringLiteralFull,
                        items: Some(self.to_lsp_diagnostics(ctx, &program, &[diagnostics])),
                        ..Default::default()
                    },
                ),
                ..Default::default()
            },
        )
    }

    /// `toLSPDiagnostics`.
    pub(crate) fn to_lsp_diagnostics(
        &self,
        ctx: &Context,
        program: &Rc<Program>,
        diagnostics: &[Vec<DiagnosticRef>],
    ) -> Vec<lsproto::Diagnostic> {
        let report_style_checks_as_warnings = self
            .user_preferences()
            .report_style_checks_as_warnings
            .is_true();
        let mut size = 0;
        for diag_slice in diagnostics {
            size += diag_slice.len();
        }
        let mut lsp_diagnostics: Vec<lsproto::Diagnostic> = Vec::with_capacity(size);
        // Compiler diagnostics located entirely in a content-mapped file's synthesized code have no location
        // in the original file. Collect them per file and surface them through a single aggregate at the top
        // of the file (with the real messages as related information) rather than dropping them or scattering
        // them at position 0.
        let mut synthesized_by_file: OrderedMap<NodeId, Vec<DiagnosticRef>> = OrderedMap::new();
        for diag_slice in diagnostics {
            for diag in diag_slice {
                if is_synthesized_content_mapped_diagnostic(diag) {
                    let file_node = {
                        let d = lock_diagnostic(diag);
                        d.file().and_then(|f| f.node).expect("synthesized content-mapped diagnostic should have a file node")
                    };
                    let mut entry = synthesized_by_file.get(&file_node).cloned().unwrap_or_default();
                    entry.push(diag.clone());
                    synthesized_by_file.set(file_node, entry);
                    continue;
                }
                lsp_diagnostics.push(self.diagnostic_to_lsp_pull_for(
                    ctx,
                    diag,
                    report_style_checks_as_warnings,
                ));
            }
        }
        for (file, diags) in synthesized_by_file.entries() {
            let aggregate = {
                let nodes = program.nodes(file.file_index());
                aggregate_synthesized_diagnostics(*file, &nodes, diags)
            };
            lsp_diagnostics.push(self.diagnostic_to_lsp_pull_for(
                ctx,
                &aggregate,
                report_style_checks_as_warnings,
            ));
        }
        lsp_diagnostics
    }

    /// `converters.DiagnosticToLSPPull(ctx, l.converters, diag, reportStyleChecksAsWarnings)`
    /// resolved against the diagnostic's own file arena.
    fn diagnostic_to_lsp_pull_for(
        &self,
        ctx: &Context,
        diag: &DiagnosticRef,
        report_style_checks_as_warnings: bool,
    ) -> lsproto::Diagnostic {
        let file_node = {
            let d = lock_diagnostic(diag);
            d.file().and_then(|f| f.node)
        };
        if let Some(file_node) = file_node {
            let nodes = self.program.nodes(file_node.file_index());
            diagnostic_to_lsp_pull(ctx, &self.converters, diag, &nodes, report_style_checks_as_warnings)
        } else {
            diagnostic_to_lsp_pull(ctx, &self.converters, diag, &[], report_style_checks_as_warnings)
        }
    }
}

/// `isSynthesizedContentMappedDiagnostic` reports whether diag is a compiler diagnostic on a content-mapped
/// file whose location lies entirely in synthesized virtual code with no counterpart in the original
/// file, and so has no meaningful position to report against the original file.
fn is_synthesized_content_mapped_diagnostic(diag: &DiagnosticRef) -> bool {
    let (file, loc, source) = {
        let d = lock_diagnostic(diag);
        (d.file().cloned(), d.loc(), d.source().to_string())
    };
    let Some(file) = file else {
        return false;
    };
    let Some(span_map) = &file.span_map else {
        return false;
    };
    if !source.is_empty() {
        return false;
    }
    let (_, fidelity) = SpanMap::virtual_to_original_span(Some(span_map), loc);
    fidelity == Fidelity::None
}

/// `aggregateSynthesizedDiagnostics` builds a single diagnostic at the top of a content-mapped file standing
/// in for compiler diagnostics located in synthesized code with no original location. The originals are
/// attached as related information so their messages are surfaced rather than silently dropped. (A later
/// change will point the related locations at a read-only view of the file's virtual TypeScript.)
fn aggregate_synthesized_diagnostics(
    file: NodeId,
    nodes: &[ast::Node],
    diags: &[DiagnosticRef],
) -> DiagnosticRef {
    let content_mapper = nodes[file].as_source_file().content_mapper().to_string();
    let aggregate = new_diagnostic(
        Some(DiagnosticFile::from_node(file, nodes)),
        TextRange::new(0, 0),
        &diagnostics::Virtual_code_produced_by_the_content_mapper_0_has_problems_with_no_corresponding_location_in_this_file,
        &[content_mapper],
    );
    {
        let mut a = lock_diagnostic(&aggregate);
        a.set_related_info(diags.to_vec());
        a.set_category(worst_category(diags));
    }
    aggregate
}

/// `worstCategory`.
fn worst_category(diags: &[DiagnosticRef]) -> Category {
    let mut worst = lock_diagnostic(&diags[0]).category();
    for diag in diags {
        match lock_diagnostic(diag).category() {
            Category::Error => return Category::Error,
            Category::Warning => worst = Category::Warning,
            _ => {}
        }
    }
    worst
}
