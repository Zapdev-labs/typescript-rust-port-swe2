// Ported from tsc/internal/testutil/tsbaseline/contentmapper_baseline.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `ansiEscape` is [strip_ansi_escapes]. Diagnostics are rendered per
// diagnostic with its own file's arena — `WrapASTDiagnostics` wraps each
// `DiagnosticRef` with the `&[Node]` arena its `DiagnosticFile.node`
// resolves through, and a Rust `NodeId`'s arena is per-file (`NodeId::
// file_index`), so a single shared slice would mis-resolve diagnostics
// spanning multiple mapped files.

use std::fmt::Write as _;
use std::rc::Rc;

use rustc_hash::FxHashSet;
use tsc_ast::diagnostic::{DiagnosticRef, lock_diagnostic};
use tsc_ast::{Node, NodeId};
use tsc_compiler::program::ProgramLike;
use tsc_diagnosticwriter as diagnosticwriter;
use tsc_tspath::RootedFilePath;

use super::util::{remove_test_path_prefixes, strip_ansi_escapes};
use crate::baseline;

/// `contentMapperFormatOpts`.
fn content_mapper_format_opts() -> diagnosticwriter::FormattingOptions {
    diagnosticwriter::FormattingOptions {
        new_line: "\n".to_string(),
        ..Default::default()
    }
}

/// `DoContentMapperBaseline`.
pub fn do_content_mapper_baseline(
    baseline_path: &str,
    program: &Rc<dyn ProgramLike>,
    diagnostics: &[DiagnosticRef],
    opts: baseline::Options,
) {
    let content = get_content_mapper_baseline(program, diagnostics);
    if content.is_empty() {
        return;
    }
    baseline::run(
        &super::error_baseline::ts_extension_replace(baseline_path, ".contentmapper"),
        &content,
        &opts,
    )
    .unwrap_or_else(|e| panic!("{e}"));
}

/// `getContentMapperBaseline`.
fn get_content_mapper_baseline(
    program: &Rc<dyn ProgramLike>,
    diagnostics: &[DiagnosticRef],
) -> String {
    let prog = program.program();
    // `map[tspath.RootedFilePath]*contentmapper.Mapper` — only membership is
    // consulted for diagnostics, so this is a set of file names; the mapper
    // itself is fetched per file when needed.
    let mut mapped: FxHashSet<RootedFilePath> = FxHashSet::default();
    let mut files: Vec<NodeId> = Vec::new();
    for file in program.get_source_files() {
        if prog.get_content_mapper(file).is_some() {
            let nodes = prog.arena_of(file);
            mapped.insert(nodes[file].as_source_file().file_name().clone());
            files.push(file);
        }
    }
    if files.is_empty() {
        return String::new();
    }

    let mut b = String::new();
    for &file in &files {
        let (file_name, script_kind, original_text, text, extensions) = {
            let nodes = prog.arena_of(file);
            let sf = nodes[file].as_source_file();
            let mapper = prog.get_content_mapper(file);
            let extensions = mapper
                .and_then(|m| m.extensions.clone())
                .unwrap_or_default();
            (
                sf.file_name().clone(),
                sf.script_kind,
                sf.original_text().to_string(),
                sf.text().to_string(),
                extensions,
            )
        };
        // Go: `%v` on `[]string` — `[a b c]`, `[]` when empty.
        let extensions = format!("[{}]", extensions.join(" "));
        let _ = writeln!(
            b,
            "//// [{}] (ScriptKind: {}, ContentMapper: {})",
            remove_test_path_prefixes(file_name.as_string(), false),
            script_kind,
            extensions,
        );
        b.push_str("--- Original ---\n");
        b.push_str(&ensure_trailing_newline(&original_text));
        b.push_str("--- Transformed ---\n");
        b.push_str(&ensure_trailing_newline(&text));
        b.push('\n');
    }

    let file_diagnostics: Vec<DiagnosticRef> = diagnostics
        .iter()
        .filter(|d| {
            lock_diagnostic(d).file().is_some_and(|f| {
                // `mapped[d.File().FileName()]` — the diagnostic's *file
                // name* membership (the ASTDiagnostic canonicalization Go
                // applies at render time is skipped; the baseline only
                // selects on the raw file name).
                mapped.contains(&f.file_name)
            })
        })
        .cloned()
        .collect();

    b.push_str("=== Diagnostics ===\n\n");
    if file_diagnostics.is_empty() {
        b.push_str(baseline::NO_CONTENT);
        b.push('\n');
        return b;
    }

    // `diagnosticwriter.FormatDiagnosticsWithColorAndContext` — per-
    // diagnostic arena resolution, joined by `formatOpts.NewLine`.
    let format_opts = content_mapper_format_opts();
    let mut rendered = String::new();
    let mut first = true;
    for d in &file_diagnostics {
        let node = lock_diagnostic(d).file().and_then(|f| f.node);
        // Scoped arena borrow.
        let arena = node.map(|n| prog.nodes(n.file_index()));
        let nodes: &[Node] = arena.as_deref().map(|v| v.as_slice()).unwrap_or(&[]);
        let wrapped = diagnosticwriter::wrap_ast_diagnostic(d.clone(), nodes);
        if !first {
            rendered.push_str(&format_opts.new_line);
        }
        first = false;
        let mut buf: Vec<u8> = Vec::new();
        diagnosticwriter::format_diagnostic_with_color_and_context(
            &mut buf,
            &wrapped,
            &format_opts,
        );
        rendered.push_str(&String::from_utf8_lossy(&buf));
    }
    b.push_str(&remove_test_path_prefixes(
        &strip_ansi_escapes(&rendered),
        false,
    ));
    b
}

/// `ensureTrailingNewline`.
fn ensure_trailing_newline(s: &str) -> String {
    if s.is_empty() || s.ends_with('\n') {
        return s.to_string();
    }
    format!("{s}\n")
}
