// Ported from tsc/internal/execute/tsc/diagnostics.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

use rustc_hash::FxHashMap;
use tsc_ast::NodeId;
use tsc_ast::diagnostic::{DiagnosticRef, lock_diagnostic, new_compiler_diagnostic};
use tsc_core::options_generated::CompilerOptions;
use tsc_core::text::TextRange;
use tsc_diagnostics::Category;
use tsc_diagnosticwriter::diagnosticwriter::{
    Diagnostic, FileLike, FormattingOptions, format_diagnostic_with_color_and_context,
    format_diagnostics_status_and_time, format_diagnostics_status_with_color_and_time,
    try_clear_screen, write_error_summary_text, write_format_diagnostic,
};
use tsc_locale::Locale;
use tsc_spanmap::SpanMap;
use tsc_tspath::PathKey;

use crate::tsc::compile::{SharedWriter, System};

/// `getFormatOptsOfSys`.
pub fn get_format_opts_of_sys(sys: &dyn System, locale: Locale) -> FormattingOptions {
    FormattingOptions {
        new_line: "\n".to_string(),
        current_directory: sys.current_directory(),
        case_sensitivity: sys.fs().case_sensitivity(),
        locale,
    }
}

// ---------------------------------------------------------------------------
// CliDiagnostic — `diagnosticwriter.WrapASTDiagnostic` equivalent.
//
// PORT: Go's `*ast.Diagnostic` carries a live `*SourceFile` pointer, so
// `WrapASTDiagnostic` needs no arena. In Rust the `DiagnosticFile` handle
// snapshots `FileName`/`PathKey`/`Text`/`OriginalText`/`SpanMap` at creation
// time, which covers everything `ASTDiagnostic` renders except the two
// lookups that still need the node arena — `canonical_source_file` and
// `content_mapper` — plus the live `text`/`ecma_line_map` (identical to the
// snapshots: source text is immutable once parsed). `DiagnosticRegistry`
// stores those per-`file_index` values, registered when a program or
// tsconfig source file is created; for files that were never registered
// (non-content-mapped files — the common case) the snapshot rendering is
// exactly equivalent.
// ---------------------------------------------------------------------------

/// Arena-independent fields read off a `SourceFile` node at registration —
/// `sf.CanonicalSourceFile()`'s file name and `sf.ContentMapper()`.
#[derive(Default)]
struct FileMapperInfo {
    /// `nodes[canonical].FileName()` when `canonical_source_file` is set.
    canonical_file_name: Option<tsc_tspath::RootedFilePath>,
    /// `sf.ContentMapper()`.
    content_mapper: String,
}

/// `DiagnosticRegistry` — maps `file_index` → mapper/canonical info for
/// `CliDiagnostic` rendering, and caches the stable-`FileKey` `FileLike`s
/// (Go's `*ast.SourceFile` pointer identity) so error-summary bucketing
/// groups diagnostics from the same file together.
#[derive(Default)]
pub struct DiagnosticRegistry {
    mapper_info: Mutex<FxHashMap<u32, FileMapperInfo>>,
    file_likes: Mutex<HashMap<StableFileKey, FileLike<'static>>>,
}

/// The stable-bucket identity of a rendered file — mirrors `FileKey::Node`
/// / `FileKey::Path` in diagnosticwriter.
#[derive(Clone, PartialEq, Eq, Hash)]
enum StableFileKey {
    Node(NodeId),
    Path(PathKey),
}

impl DiagnosticRegistry {
    /// Registers every source file of a `compiler::Program` — snapshots
    /// `canonical_source_file`'s file name and `content_mapper` per
    /// `file_index`. Call after program creation so later diagnostics render
    /// like Go's pointer-backed files.
    pub fn register_program(&self, program: &tsc_compiler::program::Program) {
        let mut mapper_info = self.mapper_info.lock().unwrap_or_else(|e| e.into_inner());
        for file in program.source_files() {
            let nodes = program.arena_of(file);
            let sf = nodes[file].as_source_file();
            mapper_info
                .entry(file.file_index())
                .or_insert_with(|| FileMapperInfo {
                    canonical_file_name: sf
                        .canonical_source_file()
                        .map(|c| nodes[c].as_source_file().file_name().clone()),
                    content_mapper: sf.content_mapper().to_string(),
                });
        }
    }

    /// Registers a parsed tsconfig file's arena (`TsConfigSourceFile`).
    pub fn register_config_file(
        &self,
        config: &tsc_tsoptions::tsconfigparsing::TsConfigSourceFile,
    ) {
        let sf = config.nodes[config.source_file].as_source_file();
        let mut mapper_info = self.mapper_info.lock().unwrap_or_else(|e| e.into_inner());
        mapper_info
            .entry(config.source_file.file_index())
            .or_insert_with(|| FileMapperInfo {
                canonical_file_name: sf
                    .canonical_source_file()
                    .map(|c| config.nodes[c].as_source_file().file_name().clone()),
                content_mapper: sf.content_mapper().to_string(),
            });
    }

    fn mapper_info(&self, file_index: u32) -> Option<FileMapperInfo> {
        self.mapper_info
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .get(&file_index)
            .map(|i| FileMapperInfo {
                canonical_file_name: i.canonical_file_name.clone(),
                content_mapper: i.content_mapper.clone(),
            })
    }

    /// Stable-`FileKey` `FileLike` for a non-renamed, non-original-text
    /// file — built from the `DiagnosticFile` snapshot (text and line map
    /// are identical to the live file's) and cached so all diagnostics on
    /// the same file share one bucket, matching `FileKey::Node`/`Path`.
    fn stable_file_like(
        &self,
        key: StableFileKey,
        file_name: &tsc_tspath::RootedFilePath,
        text: Arc<str>,
    ) -> FileLike<'static> {
        let mut cache = self.file_likes.lock().unwrap_or_else(|e| e.into_inner());
        cache
            .entry(key)
            .or_insert_with(|| FileLike::from_text(file_name.clone(), text))
            .clone()
    }
}

/// `CliDiagnostic` — the owned, `'static + Send` equivalent of
/// `diagnosticwriter.ASTDiagnostic`: a `DiagnosticRef` plus the registry
/// needed for arena lookups. See the PORT note above.
#[derive(Clone)]
pub struct CliDiagnostic {
    pub diagnostic: DiagnosticRef,
    registry: Arc<DiagnosticRegistry>,
}

/// `resolve()` result — mirrors `diagnosticwriter`'s `resolvedLocation`.
#[derive(Default)]
struct ResolvedLocation {
    loc: TextRange,
    use_original: bool,
    synthesized: bool,
}

impl CliDiagnostic {
    /// `WrapASTDiagnostic(diagnostic)` — wraps for immediate or deferred
    /// rendering; identical output for non-content-mapped diagnostics.
    pub fn wrap(diagnostic: DiagnosticRef, registry: &Arc<DiagnosticRegistry>) -> CliDiagnostic {
        CliDiagnostic {
            diagnostic,
            registry: registry.clone(),
        }
    }

    /// `d.resolve()`.
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

impl Diagnostic for CliDiagnostic {
    /// `d.File()` — mirrors `ASTDiagnostic.file()`: canonical name for
    /// supplemental files, original text for mapped ranges, `renamedFile`
    /// when only the name differs, else the file itself — all rendered from
    /// the `DiagnosticFile` snapshot.
    fn file<'s>(&'s self) -> Option<FileLike<'s>> {
        let file = lock_diagnostic(&self.diagnostic).file().cloned()?;
        let mut file_name = file.file_name.clone();
        if let Some(node) = file.node {
            if let Some(canonical) = self
                .registry
                .mapper_info(node.file_index())
                .and_then(|i| i.canonical_file_name)
            {
                file_name = canonical;
            }
        }
        if self.resolve().use_original {
            // `&originalTextFile{file: file, fileName: fileName}` — fresh
            // bucket per `File()` call.
            return Some(FileLike::from_text(file_name, file.original_text));
        }
        if file_name != file.file_name {
            // `&renamedFile{file: file, fileName: fileName}` — fresh bucket.
            return Some(FileLike::from_text(file_name, file.text));
        }
        // `return file` — stable identity per node/path.
        let key = match file.node {
            Some(node) => StableFileKey::Node(node),
            None => StableFileKey::Path(file.path_key.clone()),
        };
        Some(
            self.registry
                .stable_file_like(key, &file_name, file.text.clone()),
        )
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

    /// `d.Source()`.
    fn source(&self) -> String {
        lock_diagnostic(&self.diagnostic).source().to_string()
    }

    /// `d.Localize(locale)`.
    fn localize(&self, locale: &Locale) -> String {
        lock_diagnostic(&self.diagnostic).localize(locale)
    }

    /// `d.MessageChain()` — chain plus, for synthesized ranges, a note
    /// identifying the producing content mapper.
    fn message_chain<'s>(&'s self) -> Vec<Box<dyn Diagnostic + 's>> {
        let chain = lock_diagnostic(&self.diagnostic).message_chain().to_vec();
        let mut result: Vec<Box<dyn Diagnostic + 's>> = Vec::with_capacity(chain.len() + 1);
        for c in chain {
            result.push(Box::new(CliDiagnostic {
                diagnostic: c,
                registry: self.registry.clone(),
            }));
        }
        if self.resolve().synthesized {
            let d = lock_diagnostic(&self.diagnostic);
            if let Some(file) = d.file() {
                let mapper = file
                    .node
                    .and_then(|n| self.registry.mapper_info(n.file_index()))
                    .map(|i| i.content_mapper)
                    .unwrap_or_default();
                let note = new_compiler_diagnostic(
                    &tsc_diagnostics::This_location_is_in_virtual_code_produced_by_the_content_mapper_0_and_has_no_corresponding_location_in_the_original_file,
                    &[mapper],
                );
                result.push(Box::new(CliDiagnostic {
                    diagnostic: note,
                    registry: self.registry.clone(),
                }));
            }
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
                Box::new(CliDiagnostic {
                    diagnostic: r,
                    registry: self.registry.clone(),
                }) as Box<dyn Diagnostic + 's>
            })
            .collect()
    }
}

/// `WrapASTDiagnostics` equivalent — wraps a list for `write_error_summary_text`.
pub fn wrap_cli_diagnostics(
    diags: &[DiagnosticRef],
    registry: &Arc<DiagnosticRegistry>,
) -> Vec<CliDiagnostic> {
    diags
        .iter()
        .map(|d| CliDiagnostic::wrap(d.clone(), registry))
        .collect()
}

/// `type DiagnosticReporter = func(*ast.Diagnostic)`.
pub type DiagnosticReporter = Arc<dyn Fn(&DiagnosticRef) + Send + Sync>;

/// `QuietDiagnosticReporter`.
pub fn quiet_diagnostic_reporter(_diagnostic: &DiagnosticRef) {}

/// `QuietDiagnosticReporter` as a shared closure.
pub fn quiet_diagnostic_reporter_fn() -> DiagnosticReporter {
    Arc::new(quiet_diagnostic_reporter)
}

/// `CreateDiagnosticReporter`.
///
/// PORT: Go's `options` is `*CompilerOptions` (nullable); `None` is treated
/// as non-quiet/non-pretty-default rather than panicking.
pub fn create_diagnostic_reporter(
    sys: &Arc<dyn System>,
    w: SharedWriter,
    locale: Locale,
    options: Option<&CompilerOptions>,
) -> DiagnosticReporter {
    if options.map(|o| o.quiet.is_true()).unwrap_or(false) {
        return quiet_diagnostic_reporter_fn();
    }
    let format_opts = get_format_opts_of_sys(sys.as_ref(), locale);
    let registry = sys.diagnostic_registry().clone();
    if should_be_pretty(sys.as_ref(), options) {
        return Arc::new(move |diagnostic: &DiagnosticRef| {
            let mut g = w.guard();
            let wrapped = CliDiagnostic::wrap(diagnostic.clone(), &registry);
            format_diagnostic_with_color_and_context(&mut *g, &wrapped, &format_opts);
            use std::io::Write;
            let _ = write!(g, "{}", format_opts.new_line);
        });
    }
    Arc::new(move |diagnostic: &DiagnosticRef| {
        let mut g = w.guard();
        let wrapped = CliDiagnostic::wrap(diagnostic.clone(), &registry);
        write_format_diagnostic(&mut *g, &wrapped, &format_opts);
    })
}

/// `defaultIsPretty`.
pub fn default_is_pretty(sys: &dyn System) -> bool {
    if let Some(force_color) = sys.environment_variable("FORCE_COLOR") {
        match force_color.as_str() {
            "" | "1" | "2" | "3" | "true" => return true,
            _ => return false,
        }
    }
    if sys.environment_variable("NO_COLOR").unwrap_or_default() != "" {
        return false;
    }
    if sys.environment_variable("TERM").unwrap_or_default() == "dumb" {
        return false;
    }
    sys.write_output_is_tty()
}

/// `shouldBePretty`.
pub fn should_be_pretty(sys: &dyn System, options: Option<&CompilerOptions>) -> bool {
    if options.map(|o| o.pretty.is_unknown()).unwrap_or(true) {
        return default_is_pretty(sys);
    }
    options.is_some_and(|o| o.pretty.is_true())
}

/// `type colors struct`.
pub struct Colors {
    pub show_colors: bool,
    is_windows: bool,
    is_windows_terminal: bool,
    is_vscode: bool,
    supports_richer_colors: bool,
}

/// `createColors`.
pub fn create_colors(sys: &dyn System) -> Colors {
    if !default_is_pretty(sys) {
        return Colors {
            show_colors: false,
            is_windows: false,
            is_windows_terminal: false,
            is_vscode: false,
            supports_richer_colors: false,
        };
    }

    let os = sys.environment_variable("OS").unwrap_or_default();
    let is_windows = os.to_lowercase().contains("windows");
    let wt_session = sys.environment_variable("WT_SESSION").unwrap_or_default();
    let term_program = sys.environment_variable("TERM_PROGRAM").unwrap_or_default();
    let color_term = sys.environment_variable("COLORTERM").unwrap_or_default();
    let term = sys.environment_variable("TERM").unwrap_or_default();

    Colors {
        show_colors: true,
        is_windows,
        is_windows_terminal: !wt_session.is_empty(),
        is_vscode: term_program == "vscode",
        supports_richer_colors: color_term == "truecolor" || term == "xterm-256color",
    }
}

impl Colors {
    /// `(c *colors) bold`.
    pub fn bold(&self, str_: &str) -> String {
        if !self.show_colors {
            return str_.to_string();
        }
        format!("\x1b[1m{str_}\x1b[22m")
    }

    /// `(c *colors) blue`.
    pub fn blue(&self, str_: &str) -> String {
        if !self.show_colors {
            return str_.to_string();
        }
        // Effectively Powershell and Command prompt users use cyan instead
        // of blue because the default theme doesn't show blue with enough
        // contrast.
        if self.is_windows && !self.is_windows_terminal && !self.is_vscode {
            return self.bright_white(str_);
        }
        format!("\x1b[94m{str_}\x1b[39m")
    }

    /// `(c *colors) blueBackground`.
    pub fn blue_background(&self, str_: &str) -> String {
        if !self.show_colors {
            return str_.to_string();
        }
        if self.supports_richer_colors {
            format!("\x1B[48;5;68m{str_}\x1B[39;49m")
        } else {
            format!("\x1b[44m{str_}\x1B[39;49m")
        }
    }

    /// `(c *colors) brightWhite`.
    pub fn bright_white(&self, str_: &str) -> String {
        if !self.show_colors {
            return str_.to_string();
        }
        format!("\x1b[97m{str_}\x1b[39m")
    }
}

/// `type DiagnosticsReporter = func(diagnostics []*ast.Diagnostic)`.
pub type DiagnosticsReporter = Arc<dyn Fn(&[DiagnosticRef]) + Send + Sync>;

/// `QuietDiagnosticsReporter`.
pub fn quiet_diagnostics_reporter(_diagnostics: &[DiagnosticRef]) {}

/// `QuietDiagnosticsReporter` as a shared closure.
pub fn quiet_diagnostics_reporter_fn() -> DiagnosticsReporter {
    Arc::new(quiet_diagnostics_reporter)
}

/// `CreateReportErrorSummary`.
pub fn create_report_error_summary(
    sys: &Arc<dyn System>,
    locale: Locale,
    options: Option<&CompilerOptions>,
) -> DiagnosticsReporter {
    if should_be_pretty(sys.as_ref(), options) {
        let format_opts = get_format_opts_of_sys(sys.as_ref(), locale);
        let writer = sys.writer();
        let registry = sys.diagnostic_registry().clone();
        return Arc::new(move |diagnostics: &[DiagnosticRef]| {
            let mut g = writer.guard();
            let wrapped = wrap_cli_diagnostics(diagnostics, &registry);
            write_error_summary_text(&mut *g, &wrapped, &format_opts);
        });
    }
    quiet_diagnostics_reporter_fn()
}

/// `formatTime` for `sys.Now().Format("03:04:05 PM")` — the 12-hour kitchen
/// clock used by the build/watch status line. PORT: Go formats local time;
/// std has no timezone database, so this renders UTC (see
/// `projectlogging::timefmt` for the same pattern).
pub fn format_status_time(t: SystemTime) -> String {
    let secs = match t.duration_since(UNIX_EPOCH) {
        Ok(d) => d.as_secs() as i64,
        Err(e) => -(e.duration().as_secs() as i64),
    };
    let day = secs.rem_euclid(86_400);
    let (h24, m, s) = (day / 3600, (day % 3600) / 60, day % 60);
    let ampm = if h24 < 12 { "AM" } else { "PM" };
    let h12 = match h24 % 12 {
        0 => 12,
        h => h,
    };
    format!("{h12:02}:{m:02}:{s:02} {ampm}")
}

/// `CreateBuilderStatusReporter`.
pub fn create_builder_status_reporter(
    sys: &Arc<dyn System>,
    w: SharedWriter,
    locale: Locale,
    options: Option<&CompilerOptions>,
    testing: Option<&Arc<dyn crate::tsc::CommandLineTesting>>,
) -> DiagnosticReporter {
    if options.map(|o| o.quiet.is_true()).unwrap_or(false) {
        return quiet_diagnostic_reporter_fn();
    }

    let format_opts = get_format_opts_of_sys(sys.as_ref(), locale);
    let pretty = should_be_pretty(sys.as_ref(), options);
    let registry = sys.diagnostic_registry().clone();
    let sys = sys.clone();
    let testing = testing.cloned();
    Arc::new(move |diagnostic: &DiagnosticRef| {
        let wrapped = CliDiagnostic::wrap(diagnostic.clone(), &registry);
        let mut g = w.guard();
        if let Some(t) = &testing {
            t.on_build_status_report_start(&mut *g);
        }
        let time = format_status_time(sys.now());
        if pretty {
            format_diagnostics_status_with_color_and_time(&mut *g, &time, &wrapped, &format_opts);
        } else {
            format_diagnostics_status_and_time(&mut *g, &time, &wrapped, &format_opts);
        }
        use std::io::Write;
        let _ = write!(g, "{}{}", format_opts.new_line, format_opts.new_line);
        if let Some(t) = &testing {
            t.on_build_status_report_end(&mut *g);
        }
    })
}

/// `CreateWatchStatusReporter`.
///
/// PORT: Go captures `*CompilerOptions` in the closure; the Rust port
/// clones it (an empty `CompilerOptions` when Go's pointer is nil).
pub fn create_watch_status_reporter(
    sys: &Arc<dyn System>,
    locale: Locale,
    options: Option<&CompilerOptions>,
    testing: Option<&Arc<dyn crate::tsc::CommandLineTesting>>,
) -> DiagnosticReporter {
    let format_opts = get_format_opts_of_sys(sys.as_ref(), locale);
    let pretty = should_be_pretty(sys.as_ref(), options);
    let registry = sys.diagnostic_registry().clone();
    let sys = sys.clone();
    let testing = testing.cloned();
    let options = options.cloned().unwrap_or_default();
    Arc::new(move |diagnostic: &DiagnosticRef| {
        let wrapped = CliDiagnostic::wrap(diagnostic.clone(), &registry);
        let writer = sys.writer();
        let mut g = writer.guard();
        if let Some(t) = &testing {
            t.on_watch_status_report_start();
        }
        try_clear_screen(&mut *g, &wrapped, &options);
        let time = format_status_time(sys.now());
        if pretty {
            format_diagnostics_status_with_color_and_time(&mut *g, &time, &wrapped, &format_opts);
        } else {
            format_diagnostics_status_and_time(&mut *g, &time, &wrapped, &format_opts);
        }
        use std::io::Write;
        let _ = write!(g, "{}{}", format_opts.new_line, format_opts.new_line);
        if let Some(t) = &testing {
            t.on_watch_status_report_end();
        }
    })
}
