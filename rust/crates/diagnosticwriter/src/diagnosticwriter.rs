// Ported from tsc/internal/diagnosticwriter/diagnosticwriter.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT notes:
// - `io.Writer` parameters become `&mut dyn io::Write`; every `fmt.Fprint*`
//   call in the Go code drops the returned error, so writes here drop the
//   `io::Result` as well (`emit!`).
// - `*ast.Diagnostic` is `DiagnosticRef` (`Arc<Mutex<Diagnostic>>`). The Go
//   `Diagnostic` interface becomes the `Diagnostic` trait; `ASTDiagnostic`
//   wraps `DiagnosticRef` plus the `nodes` arena it needs to resolve
//   `CanonicalSourceFile()`/`ContentMapper()` off the `DiagnosticFile.node`
//   handle (a `NodeId`).
// - `map[FileLike][]Diagnostic` keys on Go interface pointer identity. For
//   `*ast.SourceFile` that is the file itself; `*originalTextFile`/
//   `*renamedFile` are fresh allocations per `File()` call, so every
//   diagnostic on a content-mapped file lands in its own bucket. `FileKey`
//   reproduces exactly that identity (`Node`, `Fresh`, or `Path` for the
//   node-less `DiagnosticFile` snapshots Go cannot express).

use std::collections::HashMap;
use std::io;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use tsc_ast::ast::SourceFileLike;
use tsc_ast::ast_generated::SourceFile;
use tsc_ast::diagnostic::{
    DiagnosticFile, DiagnosticRef, compare_diagnostics, lock_diagnostic, new_compiler_diagnostic,
};
use tsc_ast::{Node, NodeId};
use tsc_core::core::{compute_ecma_line_starts, utf16_len};
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::{TextPos, TextRange};
use tsc_diagnostics::Category;
use tsc_locale::Locale;
use tsc_spanmap::SpanMap;
use tsc_tspath::{CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath};

/// `fmt.Fprint*` — the Go code ignores every `io.Writer` error, so writes
/// drop the `io::Result` here as well.
macro_rules! emit {
    ($out:expr, $($arg:tt)*) => {
        let _ = ::std::io::Write::write_fmt($out, ::std::format_args!($($arg)*));
    };
}

/// `formatFileNameRelativeTo`
fn format_file_name_relative_to(
    file_name: &RootedFilePath,
    directory: &RootedDirectoryPath,
    case_sensitivity: CaseSensitivity,
) -> String {
    if let Some(relative_path) = case_sensitivity.relative_path_from_directory(directory, file_name)
    {
        return relative_path.as_string().to_string();
    }
    file_name.as_string().to_string()
}

// FileLike

/// The text backing a `FileLike` — `file.Text()`/`file.OriginalText()`
/// borrowed from the live `SourceFile`, or the `DiagnosticFile` snapshot's
/// shared text for diagnostics whose file has no arena node.
#[derive(Clone)]
enum FileText<'a> {
    Borrowed(&'a str),
    Shared(Arc<str>),
}

/// The ECMA line map backing a `FileLike` — the `SourceFile`'s cached map,
/// or a `core.ComputeECMALineStarts` result for snapshot/original text.
#[derive(Clone)]
enum FileLineMap<'a> {
    Borrowed(&'a [TextPos]),
    Owned(Vec<TextPos>),
}

/// `map[FileLike]` identity — see the module header for the Go pointer-
/// identity semantics this encodes.
#[derive(Clone, PartialEq, Eq, Hash)]
enum FileKey {
    /// `*ast.SourceFile` pointer identity — the arena address of the node.
    Node(NodeId),
    /// A node-less `DiagnosticFile` snapshot — the canonical path key is the
    /// closest stable file identity (Go's `*SourceFile` is stable per file).
    Path(PathKey),
    /// `&originalTextFile{}`/`&renamedFile{}` — a fresh allocation per
    /// `File()` call, so each one is a distinct bucket.
    Fresh(u64),
}

static NEXT_FRESH_FILE_KEY: AtomicU64 = AtomicU64::new(0);

/// `&originalTextFile{}`/`&renamedFile{}` — a new map key per `File()` call.
fn fresh_file_key() -> FileKey {
    FileKey::Fresh(NEXT_FRESH_FILE_KEY.fetch_add(1, Ordering::Relaxed))
}

/// `FileLike` — Go's `diagnosticwriter.FileLike` interface value
/// (`FileName()`, `Text()`, `ECMALineMap()`). Implements
/// `ast.SourceFileLike` so the scanner's ECMA position helpers accept it.
#[derive(Clone)]
pub struct FileLike<'a> {
    file_name: RootedFilePath,
    text: FileText<'a>,
    line_map: FileLineMap<'a>,
    key: FileKey,
}

impl<'a> FileLike<'a> {
    fn new(
        file_name: RootedFilePath,
        text: FileText<'a>,
        line_map: FileLineMap<'a>,
        key: FileKey,
    ) -> FileLike<'a> {
        FileLike {
            file_name,
            text,
            line_map,
            key,
        }
    }

    /// `FileName()`.
    pub fn file_name(&self) -> &RootedFilePath {
        &self.file_name
    }
}

impl FileLike<'static> {
    /// Builds a `FileLike` for `Diagnostic` implementors outside the AST —
    /// in Go, `FileLike` is an interface other packages implement directly.
    /// The line map is `core.ComputeECMALineStarts(text)` and the `FileKey`
    /// is fresh per call, matching Go's pointer identity for a `FileLike`
    /// value shared across `File()` calls (clone the result to share).
    pub fn from_text(file_name: RootedFilePath, text: impl Into<Arc<str>>) -> FileLike<'static> {
        let text: Arc<str> = text.into();
        let line_map = compute_ecma_line_starts(&text);
        FileLike::new(
            file_name,
            FileText::Shared(text),
            FileLineMap::Owned(line_map),
            fresh_file_key(),
        )
    }
}

impl SourceFileLike for FileLike<'_> {
    /// `Text()`.
    fn text(&self) -> &str {
        match &self.text {
            FileText::Borrowed(text) => text,
            FileText::Shared(text) => text,
        }
    }

    /// `ECMALineMap()`.
    fn ecma_line_map(&self) -> &[TextPos] {
        match &self.line_map {
            FileLineMap::Borrowed(map) => map,
            FileLineMap::Owned(map) => map,
        }
    }
}

// PORT: `tsc_scanner::scanner::SourceFileLike` is a parallel trait with an
// owned `Vec<TextPos>` return; the scanner's position helpers take `&impl
// SourceFileLike`, so `FileLike` implements it too.
impl tsc_scanner::scanner::SourceFileLike for FileLike<'_> {
    fn text(&self) -> &str {
        SourceFileLike::text(self)
    }

    fn ecma_line_map(&self) -> Vec<TextPos> {
        self.line_map_slice().to_vec()
    }
}

impl FileLike<'_> {
    fn line_map_slice(&self) -> &[TextPos] {
        match &self.line_map {
            FileLineMap::Borrowed(map) => map,
            FileLineMap::Owned(map) => map,
        }
    }
}

// Diagnostic

/// `Diagnostic` — Go's `diagnosticwriter.Diagnostic` interface, which
/// abstracts over `ast.Diagnostic` and LSP diagnostics.
// PORT: `Len` is part of Go's interface; there is no `IsEmpty` counterpart.
#[allow(clippy::len_without_is_empty)]
pub trait Diagnostic {
    /// `File()` — `None` is Go's nil `FileLike`.
    fn file<'s>(&'s self) -> Option<FileLike<'s>>;
    /// `Pos()`.
    fn pos(&self) -> i32;
    /// `End()`.
    fn end(&self) -> i32;
    /// `Len()`.
    fn len(&self) -> i32;
    /// `Code()`.
    fn code(&self) -> i32;
    /// `Category()`.
    fn category(&self) -> Category;
    /// `Source()` — a custom prefix shown before the code instead of "TS"
    /// (empty means "TS"). A non-empty value marks the diagnostic as coming
    /// from an external source (e.g. a content mapper).
    fn source(&self) -> String;
    /// `Localize(locale)`.
    fn localize(&self, locale: &Locale) -> String;
    /// `MessageChain()`.
    fn message_chain<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>>;
    /// `RelatedInformation()`.
    fn related_information<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>>;
}

impl<T: Diagnostic + ?Sized> Diagnostic for Box<T> {
    fn file<'s>(&'s self) -> Option<FileLike<'s>> {
        (**self).file()
    }
    fn pos(&self) -> i32 {
        (**self).pos()
    }
    fn end(&self) -> i32 {
        (**self).end()
    }
    fn len(&self) -> i32 {
        (**self).len()
    }
    fn code(&self) -> i32 {
        (**self).code()
    }
    fn category(&self) -> Category {
        (**self).category()
    }
    fn source(&self) -> String {
        (**self).source()
    }
    fn localize(&self, locale: &Locale) -> String {
        (**self).localize(locale)
    }
    fn message_chain<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        (**self).message_chain()
    }
    fn related_information<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        (**self).related_information()
    }
}

/// `resolvedLocation` — how a diagnostic on a content-mapped file should be
/// reported.
#[derive(Clone, Copy, Default)]
struct ResolvedLocation {
    loc: TextRange,
    /// render against the file's original, untransformed text
    use_original: bool,
    /// the range is in virtual code with no corresponding original location
    synthesized: bool,
}

/// `ASTDiagnostic` wraps `ast.Diagnostic` (`DiagnosticRef`) to implement the
/// `Diagnostic` trait. `nodes` is the AST arena the diagnostic's
/// `DiagnosticFile.node` handle resolves through — Go's `File()` reads
/// `CanonicalSourceFile()`/`ContentMapper()`/`OriginalText()`/`ECMALineMap()`
/// off the live `*ast.SourceFile`.
pub struct ASTDiagnostic<'a> {
    /// `*ast.Diagnostic`.
    pub diagnostic: DiagnosticRef,
    /// The node arena (`[]ast.Node`).
    pub nodes: &'a [Node],
}

impl<'a> ASTDiagnostic<'a> {
    /// `d.Diagnostic.File()` — the snapshot handle, cloned out of the lock.
    fn diagnostic_file(&self) -> Option<DiagnosticFile> {
        lock_diagnostic(&self.diagnostic).file().cloned()
    }

    /// `file.ContentMapper()` — the content mapper's identity, or "".
    fn content_mapper(&self, file: &DiagnosticFile) -> String {
        file.node
            .map(|node| {
                self.nodes[node]
                    .as_source_file()
                    .content_mapper()
                    .to_string()
            })
            .unwrap_or_default()
    }

    /// `d.resolve()` — determines where and against which text a diagnostic
    /// should be reported. A content mapper's own diagnostics already carry
    /// original ranges. A compiler diagnostic on a content-mapped file has
    /// its virtual range mapped back to the original; if it falls entirely
    /// within synthesized code, there is no original location, so it is
    /// shown against the virtual text and flagged as synthesized.
    fn resolve(&self) -> ResolvedLocation {
        let d = lock_diagnostic(&self.diagnostic);
        let loc = d.loc();
        let Some(file) = d.file() else {
            return ResolvedLocation {
                loc,
                ..Default::default()
            };
        };
        if !d.source().is_empty() {
            return ResolvedLocation {
                loc,
                use_original: true,
                synthesized: false,
            };
        }
        if let Some(span_map) = file.span_map.as_deref() {
            let (mapped, fidelity) = SpanMap::virtual_to_original_span(Some(span_map), loc);
            if fidelity.is_none() {
                return ResolvedLocation {
                    loc,
                    use_original: false,
                    synthesized: true,
                };
            }
            return ResolvedLocation {
                loc: mapped,
                use_original: true,
                synthesized: false,
            };
        }
        ResolvedLocation {
            loc,
            use_original: false,
            synthesized: false,
        }
    }
}

impl<'a> Diagnostic for ASTDiagnostic<'a> {
    /// `d.File()` — mirrors the Go `ASTDiagnostic.File()`: the canonical file
    /// name for supplemental files, the original text for mapped ranges, a
    /// `renamedFile` when only the name differs, else the file itself.
    fn file<'s>(&'s self) -> Option<FileLike<'s>> {
        let file = self.diagnostic_file()?;
        let mut file_name = file.file_name.clone();
        if let Some(node) = file.node {
            if let Some(canonical) = self.nodes[node].as_source_file().canonical_source_file() {
                file_name = self.nodes[canonical].as_source_file().file_name().clone();
            }
        }
        if self.resolve().use_original {
            // `newOriginalTextFile(file, fileName)` — the mapper's own
            // diagnostics (Source != "") already carry original ranges;
            // compiler diagnostics have their transformed ranges mapped
            // back. Both render against the original, untransformed text.
            let text = match file.node {
                Some(node) => FileText::Borrowed(self.nodes[node].as_source_file().original_text()),
                None => FileText::Shared(file.original_text.clone()),
            };
            let line_map = FileLineMap::Owned(compute_ecma_line_starts(match &text {
                FileText::Borrowed(t) => t,
                FileText::Shared(t) => t.as_ref(),
            }));
            return Some(FileLike::new(file_name, text, line_map, fresh_file_key()));
        }
        if file_name != file.file_name {
            // `&renamedFile{file: file, fileName: fileName}` — the
            // supplemental file's own text under the canonical name.
            let (text, line_map) = match file.node {
                Some(node) => {
                    let source_file = self.nodes[node].as_source_file();
                    (
                        FileText::Borrowed(source_file.text()),
                        FileLineMap::Borrowed(source_file.ecma_line_map()),
                    )
                }
                None => (
                    FileText::Shared(file.text.clone()),
                    FileLineMap::Owned(compute_ecma_line_starts(&file.text)),
                ),
            };
            return Some(FileLike::new(file_name, text, line_map, fresh_file_key()));
        }
        // `return file` — the source file itself.
        match file.node {
            Some(node) => {
                let source_file: &'a SourceFile = self.nodes[node].as_source_file();
                Some(FileLike::new(
                    file_name,
                    FileText::Borrowed(source_file.text()),
                    FileLineMap::Borrowed(source_file.ecma_line_map()),
                    FileKey::Node(node),
                ))
            }
            None => {
                // A `DiagnosticFile` snapshot with no arena node — render
                // against its snapshotted text.
                Some(FileLike::new(
                    file_name,
                    FileText::Shared(file.text.clone()),
                    FileLineMap::Owned(compute_ecma_line_starts(&file.text)),
                    FileKey::Path(file.path_key.clone()),
                ))
            }
        }
    }

    /// `d.Source()`.
    fn source(&self) -> String {
        lock_diagnostic(&self.diagnostic).source().to_string()
    }

    /// `d.Pos()` — `d.resolve().loc.Pos()`.
    fn pos(&self) -> i32 {
        self.resolve().loc.pos()
    }

    /// `d.End()` — `d.resolve().loc.End()`.
    fn end(&self) -> i32 {
        self.resolve().loc.end()
    }

    /// `d.Len()` — `d.resolve().loc.Len()`.
    fn len(&self) -> i32 {
        self.resolve().loc.len()
    }

    /// `d.Code()`.
    fn code(&self) -> i32 {
        lock_diagnostic(&self.diagnostic).code()
    }

    /// `d.Category()`.
    fn category(&self) -> Category {
        lock_diagnostic(&self.diagnostic).category()
    }

    /// `d.Localize(locale)`.
    fn localize(&self, locale: &Locale) -> String {
        lock_diagnostic(&self.diagnostic).localize(locale)
    }

    /// `d.MessageChain()` — the diagnostic's chain plus, for synthesized
    /// ranges, a note identifying the producing content mapper.
    fn message_chain<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        let chain = lock_diagnostic(&self.diagnostic).message_chain().to_vec();
        let mut result: Vec<Box<dyn Diagnostic + 's>> = Vec::with_capacity(chain.len() + 1);
        for c in chain {
            result.push(Box::new(ASTDiagnostic {
                diagnostic: c,
                nodes: self.nodes,
            }));
        }
        if self.resolve().synthesized {
            let Some(file) = self.diagnostic_file() else {
                return result;
            };
            // The diagnostic points into synthesized virtual code; make
            // clear the shown location is not in the original file, and
            // which content mapper produced it.
            let note = new_compiler_diagnostic(
                &tsc_diagnostics::This_location_is_in_virtual_code_produced_by_the_content_mapper_0_and_has_no_corresponding_location_in_the_original_file,
                &[self.content_mapper(&file)],
            );
            result.push(Box::new(wrap_ast_diagnostic(note, self.nodes)));
        }
        result
    }

    /// `d.RelatedInformation()`.
    fn related_information<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        let related = lock_diagnostic(&self.diagnostic)
            .related_information()
            .to_vec();
        related
            .into_iter()
            .map(|r| {
                Box::new(ASTDiagnostic {
                    diagnostic: r,
                    nodes: self.nodes,
                }) as Box<dyn Diagnostic + 's>
            })
            .collect()
    }
}

/// `WrapASTDiagnostic`
pub fn wrap_ast_diagnostic<'a>(d: DiagnosticRef, nodes: &'a [Node]) -> ASTDiagnostic<'a> {
    ASTDiagnostic {
        diagnostic: d,
        nodes,
    }
}

/// `WrapASTDiagnostics`
pub fn wrap_ast_diagnostics<'a>(
    diags: &[DiagnosticRef],
    nodes: &'a [Node],
) -> Vec<ASTDiagnostic<'a>> {
    diags
        .iter()
        .map(|d| wrap_ast_diagnostic(d.clone(), nodes))
        .collect()
}

/// `FromASTDiagnostics` — `[]*ast.Diagnostic` → `[]Diagnostic`.
pub fn from_ast_diagnostics<'a>(
    diags: &[DiagnosticRef],
    nodes: &'a [Node],
) -> Vec<Box<dyn Diagnostic + 'a>> {
    diags
        .iter()
        .map(|d| Box::new(wrap_ast_diagnostic(d.clone(), nodes)) as Box<dyn Diagnostic + 'a>)
        .collect()
}

/// `ToDiagnostics[T Diagnostic]` — `[]T` → `[]Diagnostic`.
pub fn to_diagnostics<'a, T: Diagnostic + 'a>(diags: Vec<T>) -> Vec<Box<dyn Diagnostic + 'a>> {
    diags
        .into_iter()
        .map(|d| Box::new(d) as Box<dyn Diagnostic + 'a>)
        .collect()
}

/// `CompareASTDiagnostics`
pub fn compare_ast_diagnostics(a: &ASTDiagnostic, b: &ASTDiagnostic) -> i32 {
    compare_diagnostics(&a.diagnostic, &b.diagnostic)
}

/// `FormattingOptions`
#[derive(Clone, Default)]
pub struct FormattingOptions {
    pub locale: Locale,
    pub case_sensitivity: CaseSensitivity,
    pub current_directory: RootedDirectoryPath,
    pub new_line: String,
}

pub const FOREGROUND_COLOR_ESCAPE_GREY: &str = "\u{1b}[90m";
pub const FOREGROUND_COLOR_ESCAPE_RED: &str = "\u{1b}[91m";
pub const FOREGROUND_COLOR_ESCAPE_YELLOW: &str = "\u{1b}[93m";
pub const FOREGROUND_COLOR_ESCAPE_BLUE: &str = "\u{1b}[94m";
pub const FOREGROUND_COLOR_ESCAPE_CYAN: &str = "\u{1b}[96m";

pub const GUTTER_STYLE_SEQUENCE: &str = "\u{1b}[7m";
pub const GUTTER_SEPARATOR: &str = " ";
pub const RESET_ESCAPE_SEQUENCE: &str = "\u{1b}[0m";
pub const ELLIPSIS: &str = "...";

/// `FormatDiagnosticsWithColorAndContext`
pub fn format_diagnostics_with_color_and_context<D: Diagnostic>(
    output: &mut dyn io::Write,
    diags: &[D],
    format_opts: &FormattingOptions,
) {
    if diags.is_empty() {
        return;
    }
    for (i, diagnostic) in diags.iter().enumerate() {
        if i > 0 {
            emit!(output, "{}", format_opts.new_line);
        }
        format_diagnostic_with_color_and_context(output, diagnostic, format_opts);
    }
}

/// `FormatDiagnosticWithColorAndContext`
pub fn format_diagnostic_with_color_and_context<D: Diagnostic + ?Sized>(
    output: &mut dyn io::Write,
    diagnostic: &D,
    format_opts: &FormattingOptions,
) {
    if let Some(file) = diagnostic.file() {
        let pos = diagnostic.pos();
        write_location(
            output,
            &file,
            pos,
            Some(format_opts),
            &write_with_style_and_reset,
        );
        emit!(output, " - ");
    }

    write_with_style_and_reset(
        output,
        diagnostic.category().name(),
        get_category_format(diagnostic.category()),
    );
    emit!(
        output,
        "{} {}{}: {}",
        FOREGROUND_COLOR_ESCAPE_GREY,
        diagnostic_prefix(diagnostic),
        diagnostic.code(),
        RESET_ESCAPE_SEQUENCE
    );
    write_flattened_diagnostic_message(
        output,
        diagnostic,
        &format_opts.new_line,
        &format_opts.locale,
    );

    if diagnostic.file().is_some()
        && diagnostic.code() != tsc_diagnostics::File_appears_to_be_binary.code()
    {
        emit!(output, "{}", format_opts.new_line);
        if let Some(file) = diagnostic.file() {
            write_code_snippet(
                output,
                &file,
                diagnostic.pos(),
                diagnostic.len(),
                get_category_format(diagnostic.category()),
                "",
                format_opts,
            );
        }
        emit!(output, "{}", format_opts.new_line);
    }

    let related_information = diagnostic.related_information();
    if !related_information.is_empty() {
        for related_information in &related_information {
            if let Some(file) = related_information.file() {
                emit!(output, "{}", format_opts.new_line);
                emit!(output, "  ");
                let pos = related_information.pos();
                write_location(
                    output,
                    &file,
                    pos,
                    Some(format_opts),
                    &write_with_style_and_reset,
                );
                emit!(output, " - ");
                write_flattened_diagnostic_message(
                    output,
                    related_information.as_ref(),
                    &format_opts.new_line,
                    &format_opts.locale,
                );
                write_code_snippet(
                    output,
                    &file,
                    pos,
                    related_information.len(),
                    FOREGROUND_COLOR_ESCAPE_CYAN,
                    "    ",
                    format_opts,
                );
            }
            emit!(output, "{}", format_opts.new_line);
        }
    }
}

/// `writeCodeSnippet`
#[allow(clippy::too_many_arguments)]
fn write_code_snippet(
    writer: &mut dyn io::Write,
    source_file: &FileLike,
    start: i32,
    length: i32,
    squiggle_color: &str,
    indent: &str,
    format_opts: &FormattingOptions,
) {
    let (first_line, first_line_char) =
        tsc_scanner::scanner::get_ecma_line_and_utf16_character_of_position(source_file, start);
    let (last_line, mut last_line_char) =
        tsc_scanner::scanner::get_ecma_line_and_utf16_character_of_position(
            source_file,
            start + length,
        );
    if length == 0 {
        // When length is zero, squiggle the character right after the start position.
        last_line_char += 1;
    }

    let last_line_of_file = tsc_scanner::scanner::get_ecma_line_of_position(
        source_file,
        source_file.text().len() as i32,
    );

    let has_more_than_five_lines = last_line - first_line >= 4;
    let mut gutter_width = (last_line + 1).to_string().len();
    if has_more_than_five_lines {
        gutter_width = gutter_width.max(ELLIPSIS.len());
    }

    let mut i = first_line;
    while i <= last_line {
        emit!(writer, "{}", format_opts.new_line);

        // If the error spans over 5 lines, we'll only show the first 2 and last 2 lines,
        // so we'll skip ahead to the second-to-last line.
        if has_more_than_five_lines && first_line + 1 < i && i < last_line - 1 {
            emit!(writer, "{indent}");
            emit!(writer, "{GUTTER_STYLE_SEQUENCE}");
            emit!(writer, "{ELLIPSIS:>gutter_width$}");
            emit!(writer, "{RESET_ESCAPE_SEQUENCE}");
            emit!(writer, "{GUTTER_SEPARATOR}");
            emit!(writer, "{}", format_opts.new_line);
            i = last_line - 1;
        }

        let line_start =
            tsc_scanner::scanner::get_ecma_position_of_line_and_byte_offset(source_file, i, 0);
        let line_end = if i < last_line_of_file {
            tsc_scanner::scanner::get_ecma_position_of_line_and_byte_offset(source_file, i + 1, 0)
        } else {
            source_file.text().len() as i32
        };

        // `strings.TrimRightFunc(..., unicode.IsSpace)` — Go's IsSpace is the
        // Unicode White_Space property, matching `char::is_whitespace`.
        let line_content = source_file.text()[line_start as usize..line_end as usize]
            .trim_end_matches(char::is_whitespace)
            .replace('\t', " "); // convert tabs to single spaces

        // Output the gutter and the actual contents of the line.
        emit!(writer, "{indent}");
        emit!(writer, "{GUTTER_STYLE_SEQUENCE}");
        emit!(writer, "{:>gutter_width$}", i + 1);
        emit!(writer, "{RESET_ESCAPE_SEQUENCE}");
        emit!(writer, "{GUTTER_SEPARATOR}");
        emit!(writer, "{line_content}");
        emit!(writer, "{}", format_opts.new_line);

        // Output the gutter and the error span for the line using tildes.
        emit!(writer, "{indent}");
        emit!(writer, "{GUTTER_STYLE_SEQUENCE}");
        emit!(writer, "{:>gutter_width$}", "");
        emit!(writer, "{RESET_ESCAPE_SEQUENCE}");
        emit!(writer, "{GUTTER_SEPARATOR}");
        emit!(writer, "{squiggle_color}");
        if i == first_line {
            // If we're on the last line, then limit it to the last character of the last line.
            // Otherwise, we'll just squiggle the rest of the line, giving 'slice' no end position.
            let last_char_for_line = if i == last_line {
                last_line_char
            } else {
                utf16_len(&line_content)
            };

            // Fill with spaces until the first character,
            // then squiggle the remainder of the line.
            // (`strings.Repeat` panics on a negative count; `as usize` wraps a
            // negative to a capacity-overflow panic — a panic either way.)
            emit!(writer, "{}", " ".repeat(first_line_char as usize));
            emit!(
                writer,
                "{}",
                "~".repeat((last_char_for_line - first_line_char) as usize)
            );
        } else if i == last_line {
            // Squiggle until the final character.
            emit!(writer, "{}", "~".repeat(last_line_char as usize));
        } else {
            // Squiggle the entire line.
            emit!(writer, "{}", "~".repeat(utf16_len(&line_content) as usize));
        }

        emit!(writer, "{RESET_ESCAPE_SEQUENCE}");
        i += 1;
    }
}

/// `FlattenDiagnosticMessage`
pub fn flatten_diagnostic_message<D: Diagnostic + ?Sized>(
    d: &D,
    new_line: &str,
    locale: &Locale,
) -> String {
    let mut output = Vec::new();
    write_flattened_diagnostic_message(&mut output, d, new_line, locale);
    String::from_utf8_lossy(&output).into_owned()
}

/// `WriteFlattenedASTDiagnosticMessage`
pub fn write_flattened_ast_diagnostic_message(
    writer: &mut dyn io::Write,
    diagnostic: &DiagnosticRef,
    nodes: &[Node],
    newline: &str,
    locale: &Locale,
) {
    write_flattened_diagnostic_message(
        writer,
        &wrap_ast_diagnostic(diagnostic.clone(), nodes),
        newline,
        locale,
    );
}

/// `WriteFlattenedDiagnosticMessage`
pub fn write_flattened_diagnostic_message<D: Diagnostic + ?Sized>(
    writer: &mut dyn io::Write,
    diagnostic: &D,
    newline: &str,
    locale: &Locale,
) {
    emit!(writer, "{}", diagnostic.localize(locale));

    for chain in diagnostic.message_chain() {
        flatten_diagnostic_message_chain(writer, chain.as_ref(), newline, locale, 1 /*level*/);
    }
}

/// `flattenDiagnosticMessageChain`
fn flatten_diagnostic_message_chain(
    writer: &mut dyn io::Write,
    chain: &dyn Diagnostic,
    new_line: &str,
    locale: &Locale,
    level: usize,
) {
    emit!(writer, "{new_line}");
    for _ in 0..level {
        emit!(writer, "  ");
    }

    emit!(writer, "{}", chain.localize(locale));
    for child in chain.message_chain() {
        flatten_diagnostic_message_chain(writer, child.as_ref(), new_line, locale, level + 1);
    }
}

/// `diagnosticPrefix` — the prefix shown before a diagnostic's code, e.g.
/// "TS" for compiler diagnostics or a content mapper's custom source for its
/// diagnostics.
fn diagnostic_prefix<D: Diagnostic + ?Sized>(diagnostic: &D) -> String {
    let source = diagnostic.source();
    if !source.is_empty() {
        return source;
    }
    "TS".to_string()
}

/// `getCategoryFormat`
fn get_category_format(category: Category) -> &'static str {
    match category {
        Category::Error => FOREGROUND_COLOR_ESCAPE_RED,
        Category::Warning => FOREGROUND_COLOR_ESCAPE_YELLOW,
        Category::Suggestion => FOREGROUND_COLOR_ESCAPE_GREY,
        Category::Message => FOREGROUND_COLOR_ESCAPE_BLUE,
    }
}

/// `FormattedWriter`
pub type FormattedWriter<'a> = dyn Fn(&mut dyn io::Write, &str, &str) + 'a;

/// `writeWithStyleAndReset`
pub fn write_with_style_and_reset(output: &mut dyn io::Write, text: &str, format_style: &str) {
    emit!(output, "{format_style}");
    emit!(output, "{text}");
    emit!(output, "{RESET_ESCAPE_SEQUENCE}");
}

/// `WriteLocation`
pub fn write_location(
    output: &mut dyn io::Write,
    file: &FileLike,
    pos: i32,
    format_opts: Option<&FormattingOptions>,
    write_with_style_and_reset: &FormattedWriter,
) {
    let (first_line, first_char) =
        tsc_scanner::scanner::get_ecma_line_and_utf16_character_of_position(file, pos);
    let relative_file_name = match format_opts {
        Some(format_opts) => format_file_name_relative_to(
            file.file_name(),
            &format_opts.current_directory,
            format_opts.case_sensitivity,
        ),
        None => file.file_name().as_string().to_string(),
    };

    write_with_style_and_reset(output, &relative_file_name, FOREGROUND_COLOR_ESCAPE_CYAN);
    emit!(output, ":");
    write_with_style_and_reset(
        output,
        &(first_line + 1).to_string(),
        FOREGROUND_COLOR_ESCAPE_YELLOW,
    );
    emit!(output, ":");
    write_with_style_and_reset(
        output,
        &(first_char + 1).to_string(),
        FOREGROUND_COLOR_ESCAPE_YELLOW,
    );
}

// Error summary (some of these lived in watch.ts, but they're not specific
// to the watch API).

/// `ErrorSummary` — `ErrorsByFile` is stored as a sorted `Vec` paired with
/// the `FileKey` index used to build it (Go's `map[FileLike][]Diagnostic`
/// keyed by pointer identity; see the module header).
pub struct ErrorSummary<'a> {
    pub total_error_count: usize,
    pub global_errors: Vec<&'a dyn Diagnostic>,
    /// `ErrorsByFile` — entries in `SortedFiles` order; each `file`'s
    /// `FileKey` is the bucket identity.
    pub files: Vec<FileErrors<'a>>,
}

/// One `ErrorsByFile` bucket — a `FileLike` key and its error diagnostics.
pub struct FileErrors<'a> {
    pub file: FileLike<'a>,
    pub errors: Vec<&'a dyn Diagnostic>,
}

/// `WriteErrorSummaryText` — roughly corresponds to 'getErrorSummaryText'
/// from watch.ts.
pub fn write_error_summary_text<D: Diagnostic>(
    output: &mut dyn io::Write,
    all_diagnostics: &[D],
    format_opts: &FormattingOptions,
) {
    let error_summary = get_error_summary(all_diagnostics);
    let total_error_count = error_summary.total_error_count;
    if total_error_count == 0 {
        return;
    }

    let first_file = error_summary.files.first();
    let first_file_name = pretty_path_for_file_error(
        first_file.map(|f| &f.file),
        first_file.map(|f| f.errors.as_slice()).unwrap_or(&[]),
        format_opts,
    );
    let num_erroring_files = error_summary.files.len();

    let message = if total_error_count == 1 {
        // Special-case a single error.
        if !error_summary.global_errors.is_empty() || first_file_name.is_empty() {
            tsc_diagnostics::Found_1_error.localize(&format_opts.locale, &[] as &[String])
        } else {
            tsc_diagnostics::Found_1_error_in_0
                .localize(&format_opts.locale, std::slice::from_ref(&first_file_name))
        }
    } else {
        match num_erroring_files {
            0 => {
                // No file-specific errors.
                tsc_diagnostics::Found_0_errors
                    .localize(&format_opts.locale, &[total_error_count.to_string()])
            }
            1 => {
                // One file with errors.
                tsc_diagnostics::Found_0_errors_in_the_same_file_starting_at_Colon_1.localize(
                    &format_opts.locale,
                    &[total_error_count.to_string(), first_file_name.clone()],
                )
            }
            _ => {
                // Multiple files with errors.
                tsc_diagnostics::Found_0_errors_in_1_files.localize(
                    &format_opts.locale,
                    &[
                        total_error_count.to_string(),
                        num_erroring_files.to_string(),
                    ],
                )
            }
        }
    };
    emit!(output, "{}", format_opts.new_line);
    emit!(output, "{message}");
    emit!(output, "{}", format_opts.new_line);
    emit!(output, "{}", format_opts.new_line);
    if num_erroring_files > 1 {
        write_tabular_errors_display(output, &error_summary, format_opts);
        emit!(output, "{}", format_opts.new_line);
    }
}

/// `getErrorSummary`
fn get_error_summary<'a, D: Diagnostic>(diags: &'a [D]) -> ErrorSummary<'a> {
    let mut total_error_count = 0;
    let mut global_errors: Vec<&'a dyn Diagnostic> = Vec::new();
    let mut files: Vec<FileErrors<'a>> = Vec::new();
    // `map[FileLike]index` — the bucket index in `files`.
    let mut file_index: HashMap<FileKey, usize> = HashMap::new();

    for diagnostic in diags {
        if diagnostic.category() != Category::Error {
            continue;
        }

        total_error_count += 1;
        let diagnostic: &'a dyn Diagnostic = diagnostic;
        match diagnostic.file() {
            None => global_errors.push(diagnostic),
            Some(file) => match file_index.entry(file.key.clone()) {
                std::collections::hash_map::Entry::Occupied(entry) => {
                    files[*entry.get()].errors.push(diagnostic);
                }
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert(files.len());
                    files.push(FileErrors {
                        file,
                        errors: vec![diagnostic],
                    });
                }
            },
        }
    }

    // Go sorts `maps.Keys(errorsByFile)` — the buckets, by file name.
    files.sort_by(|a, b| a.file.file_name().compare(b.file.file_name()).cmp(&0));

    ErrorSummary {
        total_error_count,
        global_errors,
        files,
    }
}

/// `writeTabularErrorsDisplay`
fn write_tabular_errors_display(
    output: &mut dyn io::Write,
    error_summary: &ErrorSummary,
    format_opts: &FormattingOptions,
) {
    let mut max_errors = 0usize;
    for file_errors in &error_summary.files {
        max_errors = max_errors.max(file_errors.errors.len());
    }

    // !!!
    // TODO (drosen): This was never localized.
    // Should make this better.
    let header_row = tsc_diagnostics::Errors_Files.localize(&format_opts.locale, &[] as &[String]);
    let left_column_heading_length = header_row.split(' ').next().unwrap_or("").len();
    let length_of_biggest_error_count = max_errors.to_string().len();
    let left_padding_goal = left_column_heading_length.max(length_of_biggest_error_count);
    let header_padding =
        (length_of_biggest_error_count as i32 - left_column_heading_length as i32).max(0) as usize;

    emit!(output, "{}", " ".repeat(header_padding));
    emit!(output, "{header_row}");
    emit!(output, "{}", format_opts.new_line);

    for file_errors in &error_summary.files {
        let error_count = file_errors.errors.len();
        emit!(output, "{error_count:>left_padding_goal$}  ");
        emit!(
            output,
            "{}",
            pretty_path_for_file_error(Some(&file_errors.file), &file_errors.errors, format_opts)
        );
        emit!(output, "{}", format_opts.new_line);
    }
}

/// `prettyPathForFileError`
fn pretty_path_for_file_error(
    file: Option<&FileLike>,
    file_errors: &[&dyn Diagnostic],
    format_opts: &FormattingOptions,
) -> String {
    let Some(file) = file else {
        return String::new();
    };
    if file_errors.is_empty() {
        return String::new();
    }
    let line = tsc_scanner::scanner::get_ecma_line_of_position(file, file_errors[0].pos());
    let file_name = format_file_name_relative_to(
        file.file_name(),
        &format_opts.current_directory,
        format_opts.case_sensitivity,
    );
    format!(
        "{file_name}{FOREGROUND_COLOR_ESCAPE_GREY}:{}{RESET_ESCAPE_SEQUENCE}",
        line + 1
    )
}

/// `WriteFormatDiagnostics`
pub fn write_format_diagnostics<D: Diagnostic>(
    output: &mut dyn io::Write,
    diagnostics: &[D],
    format_opts: &FormattingOptions,
) {
    for diagnostic in diagnostics {
        write_format_diagnostic(output, diagnostic, format_opts);
    }
}

/// `WriteFormatDiagnostic`
pub fn write_format_diagnostic<D: Diagnostic>(
    output: &mut dyn io::Write,
    diagnostic: &D,
    format_opts: &FormattingOptions,
) {
    if let Some(file) = diagnostic.file() {
        let (line, character) = tsc_scanner::scanner::get_ecma_line_and_utf16_character_of_position(
            &file,
            diagnostic.pos(),
        );
        let file_name = file.file_name();
        let relative_file_name = format_file_name_relative_to(
            file_name,
            &format_opts.current_directory,
            format_opts.case_sensitivity,
        );
        emit!(
            output,
            "{relative_file_name}({},{}): ",
            line + 1,
            character + 1
        );
    }

    emit!(
        output,
        "{} {}{}: ",
        diagnostic.category().name(),
        diagnostic_prefix(diagnostic),
        diagnostic.code()
    );
    write_flattened_diagnostic_message(
        output,
        diagnostic,
        &format_opts.new_line,
        &format_opts.locale,
    );
    emit!(output, "{}", format_opts.new_line);
}

/// `FormatDiagnosticsStatusWithColorAndTime`
pub fn format_diagnostics_status_with_color_and_time<D: Diagnostic>(
    output: &mut dyn io::Write,
    time: &str,
    diag: &D,
    format_opts: &FormattingOptions,
) {
    emit!(output, "[");
    write_with_style_and_reset(output, time, FOREGROUND_COLOR_ESCAPE_GREY);
    emit!(output, "] ");
    write_flattened_diagnostic_message(output, diag, &format_opts.new_line, &format_opts.locale);
}

/// `FormatDiagnosticsStatusAndTime`
pub fn format_diagnostics_status_and_time<D: Diagnostic>(
    output: &mut dyn io::Write,
    time: &str,
    diag: &D,
    format_opts: &FormattingOptions,
) {
    emit!(output, "{time} - ");
    write_flattened_diagnostic_message(output, diag, &format_opts.new_line, &format_opts.locale);
}

/// `var ScreenStartingCodes` — `LazyLock` because `Message::code()` is not
/// const.
pub static SCREEN_STARTING_CODES: std::sync::LazyLock<[i32; 2]> = std::sync::LazyLock::new(|| {
    [
        tsc_diagnostics::Starting_compilation_in_watch_mode.code(),
        tsc_diagnostics::File_change_detected_Starting_incremental_compilation.code(),
    ]
});

/// `TryClearScreen`
pub fn try_clear_screen<D: Diagnostic>(
    output: &mut dyn io::Write,
    diag: &D,
    options: &CompilerOptions,
) -> bool {
    if !options.preserve_watch_output.is_true()
        && !options.extended_diagnostics.is_true()
        && !options.diagnostics.is_true()
        && SCREEN_STARTING_CODES.contains(&diag.code())
    {
        emit!(output, "\x1B[2J\x1B[3J\x1B[H"); // Clear screen and move cursor to home position
        return true;
    }
    false
}
