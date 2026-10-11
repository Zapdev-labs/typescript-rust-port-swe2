// Ported from tsc/internal/testutil/tsbaseline/error_baseline.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: Go's `DoErrorBaseline` wraps `[]*ast.Diagnostic` with
// `diagnosticwriter.WrapASTDiagnostics`, whose `File()` resolves the live
// `*ast.SourceFile` pointer. Rust diagnostics carry a `DiagnosticFile`
// snapshot (text/originalText/spanMap/pathKey) plus an optional arena
// `NodeId`; callers here do not hand us the program's per-file arenas, so
// `SnapshotDiagnostic` renders through the snapshot only — the
// `canonical_source_file` rename and the content-mapper "synthesized code"
// note (both needing arena access) are deferred; `verifyDiagnostics` in
// testrunner filters content-mapped diagnostics into the content-mapper
// baseline instead, where the arena is available.

use std::fmt::Write as _;

use rustc_hash::FxHashMap;
use tsc_ast::diagnostic::{DiagnosticFile, DiagnosticRef, lock_diagnostic};
use tsc_core::text::TextRange;
use tsc_diagnostics::Category;
use tsc_diagnosticwriter::{self as diagnosticwriter, Diagnostic, FileLike, FormattingOptions};
use tsc_spanmap::SpanMap;
use tsc_tspath as tspath;

use super::util::{
    is_built_file, is_default_library_file, is_tsconfig_file, remove_test_path_prefixes,
    sanitize_test_file_path,
};
use crate::baseline;
use crate::harnessutil::TestFile;

/// `const harnessNewLine`.
pub(crate) const HARNESS_NEW_LINE: &str = "\r\n";

/// `formatOpts`.
fn format_opts() -> FormattingOptions {
    FormattingOptions {
        new_line: HARNESS_NEW_LINE.to_string(),
        ..Default::default()
    }
}

/// `resolvedLocation` — mirrors `diagnosticwriter.ASTDiagnostic`'s
/// snapshot-resolvable parts.
#[derive(Clone, Copy, Default)]
struct ResolvedLocation {
    loc: TextRange,
    use_original: bool,
    /// The range is in virtual code with no corresponding original location —
    /// `message_chain` appends the "virtual code" note for it.
    synthesized: bool,
}

/// `SnapshotDiagnostic` — a `diagnosticwriter::Diagnostic` over a
/// `DiagnosticRef` resolved through its `DiagnosticFile` snapshot alone.
pub(crate) struct SnapshotDiagnostic {
    pub diagnostic: DiagnosticRef,
}

impl SnapshotDiagnostic {
    fn diagnostic_file(&self) -> Option<DiagnosticFile> {
        lock_diagnostic(&self.diagnostic).file().cloned()
    }

    /// `d.resolve()` — see `ASTDiagnostic::resolve`. The snapshot carries
    /// `span_map`, so virtual→original mapping still works.
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

impl Diagnostic for SnapshotDiagnostic {
    /// `d.File()` — the snapshot branches of `ASTDiagnostic::file()` (no
    /// arena `node` resolution).
    fn file<'s>(&'s self) -> Option<FileLike<'s>> {
        let file = self.diagnostic_file()?;
        let supplemental = file.is_content_mapper_supplemental;
        let mut file_name = file.file_name.clone();
        // `canonical.FileName()` — supplemental outputs render under the
        // canonical file's name (`renamedFile` in Go).
        if let Some(canonical) = &file.canonical_file_name {
            file_name = canonical.clone();
        }
        if self.resolve().use_original {
            return Some(
                FileLike::from_text(file_name, file.original_text)
                    .with_is_content_mapper_supplemental(supplemental),
            );
        }
        if file_name != file.file_name {
            // `&renamedFile{file, fileName}` — fresh pointer identity per
            // `File()` call, file's own (virtual) text, canonical name.
            return Some(
                FileLike::from_text(file_name, file.text)
                    .with_is_content_mapper_supplemental(supplemental),
            );
        }
        Some(
            FileLike::from_text_path_keyed(file_name, file.text, file.path_key)
                .with_is_content_mapper_supplemental(supplemental),
        )
    }

    fn pos(&self) -> i32 {
        self.resolve().loc.pos()
    }

    fn end(&self) -> i32 {
        self.resolve().loc.end()
    }

    fn len(&self) -> i32 {
        self.resolve().loc.len()
    }

    fn code(&self) -> i32 {
        lock_diagnostic(&self.diagnostic).code()
    }

    fn category(&self) -> Category {
        lock_diagnostic(&self.diagnostic).category()
    }

    fn source(&self) -> String {
        lock_diagnostic(&self.diagnostic).source().to_string()
    }

    fn localize(&self, locale: &tsc_locale::Locale) -> String {
        lock_diagnostic(&self.diagnostic).localize(locale)
    }

    fn message_chain<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        let mut result: Vec<Box<dyn Diagnostic + 's>> = lock_diagnostic(&self.diagnostic)
            .message_chain()
            .iter()
            .map(|c| {
                Box::new(SnapshotDiagnostic {
                    diagnostic: c.clone(),
                }) as Box<dyn Diagnostic>
            })
            .collect();
        if self.resolve().synthesized {
            // The diagnostic points into synthesized virtual code; make clear
            // the shown location is not in the original file, and which
            // content mapper produced it.
            let mapper = lock_diagnostic(&self.diagnostic)
                .file()
                .map(|f| f.content_mapper.to_string())
                .unwrap_or_default();
            let note = tsc_ast::diagnostic::new_compiler_diagnostic(
                &tsc_diagnostics::This_location_is_in_virtual_code_produced_by_the_content_mapper_0_and_has_no_corresponding_location_in_the_original_file,
                &[mapper],
            );
            result.push(Box::new(SnapshotDiagnostic { diagnostic: note }));
        }
        result
    }

    fn related_information<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        lock_diagnostic(&self.diagnostic)
            .related_information()
            .iter()
            .map(|r| {
                Box::new(SnapshotDiagnostic {
                    diagnostic: r.clone(),
                }) as Box<dyn Diagnostic>
            })
            .collect()
    }
}

/// The `compareDiagnostics` argument for [SnapshotDiagnostic] slices.
pub(crate) fn compare_snapshot_diagnostics(a: &SnapshotDiagnostic, b: &SnapshotDiagnostic) -> i32 {
    tsc_ast::diagnostic::compare_diagnostics(&a.diagnostic, &b.diagnostic)
}

/// `DoErrorBaseline`.
pub fn do_error_baseline(
    baseline_path: &str,
    input_files: &[TestFile],
    errors: &[DiagnosticRef],
    pretty: bool,
    opts: baseline::Options,
) {
    let baseline_path = ts_extension_replace(baseline_path, ".errors.txt");
    let error_baseline = if !errors.is_empty() {
        let diagnostics: Vec<SnapshotDiagnostic> = errors
            .iter()
            .map(|d| SnapshotDiagnostic {
                diagnostic: d.clone(),
            })
            .collect();
        get_error_baseline(
            input_files,
            &diagnostics,
            compare_snapshot_diagnostics,
            pretty,
        )
    } else {
        baseline::NO_CONTENT.to_string()
    };
    baseline::run(&baseline_path, &error_baseline, &opts).unwrap_or_else(|e| panic!("{e}"));
    if errors.iter().any(|d| lock_diagnostic(d).code() == -1) {
        panic!(
            "Found diagnostic with code -1, which is used to log critical assertion violations in the baseline. Inspect and fix those failures."
        );
    }
}

/// `minimalDiagnosticsToString`.
fn minimal_diagnostics_to_string<D: Diagnostic>(diagnostics: &[D], pretty: bool) -> String {
    let mut output: Vec<u8> = Vec::new();
    let format_opts = format_opts();
    if pretty {
        diagnosticwriter::format_diagnostics_with_color_and_context(
            &mut output,
            diagnostics,
            &format_opts,
        );
    } else {
        diagnosticwriter::write_format_diagnostics(&mut output, diagnostics, &format_opts);
    }
    String::from_utf8_lossy(&output).into_owned()
}

/// `&D` as an owned `Diagnostic` — `write_error_summary_text`/`ToDiagnostics`
/// need a slice of sized values and `iterate_error_baseline` holds `&[D]`.
struct ByRef<'a, D: Diagnostic + ?Sized>(&'a D);

impl<D: Diagnostic + ?Sized> Diagnostic for ByRef<'_, D> {
    fn file<'s>(&'s self) -> Option<FileLike<'s>> {
        self.0.file()
    }
    fn pos(&self) -> i32 {
        self.0.pos()
    }
    fn end(&self) -> i32 {
        self.0.end()
    }
    fn len(&self) -> i32 {
        self.0.len()
    }
    fn code(&self) -> i32 {
        self.0.code()
    }
    fn category(&self) -> Category {
        self.0.category()
    }
    fn source(&self) -> String {
        self.0.source()
    }
    fn localize(&self, locale: &tsc_locale::Locale) -> String {
        self.0.localize(locale)
    }
    fn message_chain<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        self.0.message_chain()
    }
    fn related_information<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        self.0.related_information()
    }
}

/// `GetErrorBaseline`.
///
// PORT: Go is generic over `diagnosticwriter.Diagnostic`; callers pass
// either [SnapshotDiagnostic] or `diagnosticwriter::ASTDiagnostic`.
pub fn get_error_baseline<D: Diagnostic>(
    input_files: &[TestFile],
    diagnostics: &[D],
    compare_diagnostics: fn(&D, &D) -> i32,
    pretty: bool,
) -> String {
    let mut output_lines =
        iterate_error_baseline(input_files, diagnostics, compare_diagnostics, pretty);

    if pretty {
        let mut summary_builder: Vec<u8> = Vec::new();
        let boxed: Vec<ByRef<'_, D>> = diagnostics.iter().map(ByRef).collect();
        diagnosticwriter::write_error_summary_text(&mut summary_builder, &boxed, &format_opts());
        let summary = remove_test_path_prefixes(&String::from_utf8_lossy(&summary_builder), false);
        output_lines.push(summary);
    }
    output_lines.join("")
}

/// `iterateErrorBaseline`.
fn iterate_error_baseline<D: Diagnostic>(
    input_files: &[TestFile],
    input_diagnostics: &[D],
    compare_diagnostics: fn(&D, &D) -> i32,
    pretty: bool,
) -> Vec<String> {
    let mut diagnostics: Vec<&D> = input_diagnostics.iter().collect();
    diagnostics.sort_by(|a, b| compare_diagnostics(*a, *b).cmp(&0));

    let mut output_lines = String::new();
    // Count up all errors that were found in files other than lib.d.ts so we don't miss any
    let mut total_errors_reported_in_non_library_non_tsconfig_files = 0i64;
    let mut errors_reported = 0i64;

    let mut first_line = true;
    macro_rules! new_line {
        () => {{
            if first_line {
                first_line = false;
                ""
            } else {
                "\r\n"
            }
        }};
    }

    let mut result: Vec<String> = Vec::new();

    fn output_error_text<D: Diagnostic>(
        diag: &D,
        output_lines: &mut String,
        first_line: &mut bool,
        errors_reported: &mut i64,
        total: &mut i64,
    ) {
        let message = diagnosticwriter::flatten_diagnostic_message(
            diag,
            HARNESS_NEW_LINE,
            &tsc_locale::DEFAULT,
        );

        let mut err_lines: Vec<String> = Vec::new();
        for line in remove_test_path_prefixes(&message, false).split('\n') {
            let line = line.strip_suffix('\r').unwrap_or(line);
            if line.is_empty() {
                continue;
            }
            err_lines.push(format!(
                "!!! {} TS{}: {}",
                diag.category().name(),
                diag.code(),
                line
            ));
        }

        for info in &diag.related_information() {
            let mut location = String::new();
            let info_file = info.file();
            if let Some(file) = &info_file {
                location = format!(" {}", format_location(file, info.pos(), &format_opts()));
            }
            location = remove_test_path_prefixes(&location, false);
            if !location.is_empty()
                && let Some(file) = &info_file
                && is_default_library_file(file.file_name().as_string())
            {
                location = replace_diagnostics_location_pattern(&location);
            }
            err_lines.push(format!(
                "!!! related TS{}{}: {}",
                info.code(),
                location,
                diagnosticwriter::flatten_diagnostic_message(
                    info.as_ref(),
                    HARNESS_NEW_LINE,
                    &tsc_locale::DEFAULT
                )
            ));
        }

        for e in err_lines {
            if *first_line {
                *first_line = false;
            } else {
                output_lines.push_str("\r\n");
            }
            output_lines.push_str(&e);
        }

        *errors_reported += 1;

        // do not count errors from lib.d.ts here, they are computed separately as numLibraryDiagnostics
        // if lib.d.ts is explicitly included in input files and there are some errors in it (i.e. because of duplicate identifiers)
        // then they will be added twice thus triggering 'total errors' assertion with condition
        // Similarly for tsconfig, which may be in the input files and contain errors.
        // 'totalErrorsReportedInNonLibraryNonTsconfigFiles + numLibraryDiagnostics + numTsconfigDiagnostics, diagnostics.length
        let file_name = diag.file().map(|f| f.file_name().as_string().to_string());
        if file_name.is_none_or(|f| !is_default_library_file(&f) && !is_tsconfig_file(&f)) {
            *total += 1;
        }
    }

    let top_diagnostics = {
        let boxed: Vec<ByRef<'_, D>> = diagnostics.iter().map(|d| ByRef(*d)).collect();
        let mut top = minimal_diagnostics_to_string(&boxed, pretty);
        top = remove_test_path_prefixes(&top, false);
        replace_diagnostics_location_prefix(&top)
    };

    result.push(format!(
        "{top_diagnostics}{HARNESS_NEW_LINE}{HARNESS_NEW_LINE}"
    ));

    // Report global errors
    for error in &diagnostics {
        if error.file().is_none() {
            output_error_text(
                *error,
                &mut output_lines,
                &mut first_line,
                &mut errors_reported,
                &mut total_errors_reported_in_non_library_non_tsconfig_files,
            );
        }
    }

    result.push(output_lines.clone());
    output_lines.clear();
    errors_reported = 0;

    // 'merge' the lines of each input file with any errors associated with it
    let mut dupe_case: FxHashMap<String, i64> = FxHashMap::default();
    for input_file in input_files {
        // Filter down to the errors in the file
        let file_errors: Vec<&D> = diagnostics
            .iter()
            .copied()
            .filter(|e| {
                e.file().is_some_and(|f| {
                    tspath::compare_paths(
                        &remove_test_path_prefixes(f.file_name().as_string(), false),
                        &remove_test_path_prefixes(&input_file.unit_name, false),
                        tspath::CaseSensitivity::CaseInsensitive,
                    ) == 0
                })
            })
            .collect();

        // Header
        let nl = new_line!();
        let _ = write!(
            output_lines,
            "{nl}==== {} ({} errors) ====",
            remove_test_path_prefixes(&input_file.unit_name, false),
            file_errors.len(),
        );

        // Make sure we emit something for every error
        let mut marked_error_count = 0usize;
        // For each line, emit the line followed by any error squiggles matching this line

        let line_starts = tsc_core::core::compute_ecma_line_starts(&input_file.content);
        let lines: Vec<&str> = split_line_delimiter(&input_file.content);

        for (line_index, line) in lines.iter().enumerate() {
            let mut line = *line;
            if line.ends_with('\r') {
                line = &line[..line.len() - 1];
            }

            let this_line_start = i64::from(line_starts[line_index]);
            // On the last line of the file, fake the next line start number so that we handle errors on the last character of the file correctly
            let next_line_start = if line_index == lines.len() - 1 {
                input_file.content.len() as i64
            } else {
                i64::from(line_starts[line_index + 1])
            };
            // Emit this line from the original file
            output_lines.push_str(new_line!());
            output_lines.push_str("    ");
            output_lines.push_str(line);
            for err_diagnostic in &file_errors {
                // Does any error start or continue on to this line? Emit squiggles
                let err_start = i64::from(err_diagnostic.pos());
                let end = err_start + i64::from(err_diagnostic.len());
                if end >= this_line_start
                    && (err_start < next_line_start || line_index == lines.len() - 1)
                {
                    // How many characters from the start of this line the error starts at (could be positive or negative)
                    let relative_offset = err_start - this_line_start;
                    // How many characters of the error are on this line (might be longer than this line in reality)
                    let length = (end - err_start) - 0.max(this_line_start - err_start);
                    // Calculate the start of the squiggle (byte offset into `line`)
                    let squiggle_start = 0.max(relative_offset) as usize;
                    // TODO/REVIEW: this doesn't work quite right in the browser if a multi file test has files whose names are just the right length relative to one another
                    output_lines.push_str(new_line!());
                    output_lines.push_str("    ");
                    // `nonWhitespace.ReplaceAllString(line[:squiggleStart], " ")`
                    for (byte_index, c) in line.char_indices() {
                        if byte_index >= squiggle_start {
                            break;
                        }
                        output_lines.push(if c.is_whitespace() { c } else { ' ' });
                    }
                    // This was `new Array(count).join("~")`; which maps 0 to "", 1 to "", 2 to "~", 3 to "~~", etc.
                    // Go: `utf8.RuneCountInString(line[squiggleStart:squiggleEnd])` —
                    // count chars starting inside the byte range (a char
                    // straddling the boundary counts once, like Go's
                    // RuneError).
                    let squiggle_end = squiggle_start
                        .max(squiggle_start.saturating_add(length as usize))
                        .min(line.len());
                    let squiggle_len = line
                        .char_indices()
                        .take_while(|(i, _)| *i < squiggle_end)
                        .filter(|(i, _)| *i >= squiggle_start)
                        .count();
                    output_lines.push_str(&"~".repeat(squiggle_len));
                    // If the error ended here, or we're at the end of the file, emit its message
                    if line_index == lines.len() - 1 || next_line_start > end {
                        output_error_text(
                            *err_diagnostic,
                            &mut output_lines,
                            &mut first_line,
                            &mut errors_reported,
                            &mut total_errors_reported_in_non_library_non_tsconfig_files,
                        );
                        marked_error_count += 1;
                    }
                }
            }
        }

        // Verify we didn't miss any errors in this file
        assert_eq!(
            marked_error_count,
            file_errors.len(),
            "count of errors in {}",
            input_file.unit_name
        );
        let sanitized = sanitize_test_file_path(&input_file.unit_name);
        let is_dupe = dupe_case.contains_key(&sanitized);
        *dupe_case.entry(sanitized).or_insert(0) += 1;
        result.push(output_lines.clone());
        if is_dupe {
            // Case-duplicated files on a case-insensitive build will have errors reported in both the dupe and the original
            // thanks to the case-insensitive path comparison on the error file path - We only want to count those errors once
            // for the assert below, so we subtract them here.
            total_errors_reported_in_non_library_non_tsconfig_files -= errors_reported;
        }
        output_lines.clear();
        errors_reported = 0;
    }

    let num_library_diagnostics = diagnostics
        .iter()
        .filter(|d| {
            d.file().is_some_and(|f| {
                is_default_library_file(f.file_name().as_string())
                    || is_built_file(f.file_name().as_string())
            })
        })
        .count() as i64;
    let num_tsconfig_diagnostics = diagnostics
        .iter()
        .filter(|d| {
            d.file()
                .is_some_and(|f| is_tsconfig_file(f.file_name().as_string()))
        })
        .count() as i64;
    // `numContentMapperSupplementalDiagnostics` — `file.IsContentMapperSupplemental()`,
    // surfaced on `FileLike` from the live node in `ASTDiagnostic::file`.
    let num_content_mapper_supplemental_diagnostics = diagnostics
        .iter()
        .filter(|d| d.file().is_some_and(|f| f.is_content_mapper_supplemental()))
        .count() as i64;
    // Verify we didn't miss any errors in total
    assert_eq!(
        total_errors_reported_in_non_library_non_tsconfig_files
            + num_library_diagnostics
            + num_tsconfig_diagnostics
            + num_content_mapper_supplemental_diagnostics,
        diagnostics.len() as i64,
        "total number of errors"
    );

    result
}

/// `formatLocation`.
fn format_location(file: &FileLike, pos: i32, format_opts: &FormattingOptions) -> String {
    let mut output: Vec<u8> = Vec::new();
    diagnosticwriter::write_location(
        &mut output,
        file,
        pos,
        Some(format_opts),
        &|out, text, _style| {
            use std::io::Write as _;
            let _ = out.write_all(text.as_bytes());
        },
    );
    String::from_utf8_lossy(&output).into_owned()
}

/// `lineDelimiter.Split(content, -1)` — splits on `\r?\n`.
fn split_line_delimiter(content: &str) -> Vec<&str> {
    let mut lines = Vec::new();
    let bytes = content.as_bytes();
    let mut start = 0;
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'\n' {
            lines.push(&content[start..i]);
            i += 1;
            start = i;
        } else if bytes[i] == b'\r' && i + 1 < bytes.len() && bytes[i + 1] == b'\n' {
            lines.push(&content[start..i]);
            i += 2;
            start = i;
        } else {
            i += 1;
        }
    }
    lines.push(&content[start..]);
    lines
}

/// `tsExtension.ReplaceAllString(baselinePath, ext)` — `\.tsx?$` → `ext`.
/// `util.rs`-shared so each `Do*Baseline` can apply it.
pub(crate) fn ts_extension_replace(path: &str, ext: &str) -> String {
    if path.ends_with(".tsx") {
        format!("{}{}", &path[..path.len() - 4], ext)
    } else if path.ends_with(".ts") {
        format!("{}{}", &path[..path.len() - 3], ext)
    } else {
        path.to_string()
    }
}

/// `diagnosticsLocationPrefix` — `(?im)^(lib.*\.d\.ts)\(\d+,\d+\)` →
/// `$1(--,--)`. Applied per line (Go `.` never crosses `\n`).
fn replace_diagnostics_location_prefix(text: &str) -> String {
    replace_locations(text, true)
}

/// `diagnosticsLocationPattern` — `(?i)(lib.*\.d\.ts):\d+:\d+` →
/// `$1:--:--`.
fn replace_diagnostics_location_pattern(text: &str) -> String {
    replace_locations(text, false)
}

fn replace_locations(text: &str, is_prefix: bool) -> String {
    let mut out = String::with_capacity(text.len());
    for (i, line) in text.split('\n').enumerate() {
        if i > 0 {
            out.push('\n');
        }
        replace_location_in_line(line, is_prefix, &mut out);
    }
    out
}

/// One line of either lib-location regex. `is_prefix` selects the
/// `(\d+,\d+)` form (anchored at line start) vs the `:\d+:\d+` form
/// (unanchored, repeated).
fn replace_location_in_line(line: &str, is_prefix: bool, out: &mut String) {
    let lower = line.to_ascii_lowercase();
    let mut search_from = 0usize;
    loop {
        let Some(lib_at) = lower[search_from..].find("lib").map(|o| o + search_from) else {
            out.push_str(&line[search_from.min(line.len())..]);
            return;
        };
        if is_prefix && lib_at != 0 {
            // `^lib` anchored — only position 0 qualifies.
            out.push_str(&line[search_from.min(line.len())..]);
            return;
        }
        // Greedy `.*\.d\.ts`: the last ".d.ts" on the line followed by the
        // location suffix.
        let mut candidate: Option<usize> = None;
        let mut pos = lib_at;
        while let Some(o) = lower[pos..].find(".d.ts") {
            let dts_end = pos + o + 5; // just past ".d.ts"
            pos = dts_end;
            if suffix_len(&lower, dts_end, is_prefix) > 0 {
                candidate = Some(dts_end);
            }
        }
        let Some(dts_end) = candidate else {
            // No match starting at this "lib" — emit through it and keep
            // scanning after it.
            out.push_str(&line[search_from..lib_at + 3]);
            search_from = lib_at + 3;
            continue;
        };
        out.push_str(&line[search_from..dts_end]);
        let end = dts_end + suffix_len(&lower, dts_end, is_prefix);
        out.push_str(if is_prefix { "(--,--)" } else { ":--:--" });
        search_from = end;
        if is_prefix {
            // Anchored at ^ — a second match on the same line is
            // impossible.
            out.push_str(&line[search_from.min(line.len())..]);
            return;
        }
    }
}

/// Length of `(\d+,\d+)` (prefix form) or `:\d+:\d+` at `start` — 0 if
/// absent.
fn suffix_len(lower: &str, start: usize, is_prefix: bool) -> usize {
    let bytes = lower.as_bytes();
    let mut i = start;
    let sep = if is_prefix { b'(' } else { b':' };
    if i >= bytes.len() || bytes[i] != sep {
        return 0;
    }
    i += 1;
    let d1 = i;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    if i == d1 {
        return 0;
    }
    let mid = if is_prefix { b',' } else { b':' };
    if i >= bytes.len() || bytes[i] != mid {
        return 0;
    }
    i += 1;
    let d2 = i;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
        i += 1;
    }
    if i == d2 {
        return 0;
    }
    if is_prefix {
        if i >= bytes.len() || bytes[i] != b')' {
            return 0;
        }
        i += 1;
    }
    i - start
}
