// Ported from tsc/internal/compiler/processingDiagnostic.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `processingDiagnostic.kind`/`reason`/`explanation` becomes a plain
// enum — the Go accessor methods (`asFileIncludeReason`,
// `asIncludeExplainingDiagnostic`) are match arms. `*FileIncludeReason` is
// `Rc<FileIncludeReason>`; the `seenReasons` pointer set is a `HashSet` of
// `Rc::as_ptr` casts.

use std::collections::HashSet;
use std::rc::Rc;

use tsc_ast::diagnostic::{DiagnosticRef, lock_diagnostic};
use tsc_diagnostics::{self as diagnostics};
use tsc_tsoptions::value::Value;
use tsc_tspath::{PathKey, RootedDirectoryPath};

use crate::file_include::FileIncludeReason;
use crate::program::Program;

/// `processingDiagnosticKind` + `processingDiagnostic` — the Go struct's
/// `kind` discriminator with `reason`/`explanation` payloads becomes an enum.
#[derive(Clone)]
pub enum ProcessingDiagnostic {
    /// `processingDiagnosticKindUnknownReference` — `reason`.
    UnknownReference(Rc<FileIncludeReason>),
    /// `processingDiagnosticKindExplainingFileInclude` — `explanation`.
    ExplainingFileInclude(Box<IncludeExplainingDiagnostic>),
}

/// `type includeExplainingDiagnostic struct`.
#[derive(Clone)]
pub struct IncludeExplainingDiagnostic {
    pub file: PathKey,
    pub diagnostic_reason: Option<Rc<FileIncludeReason>>,
    pub message: &'static diagnostics::Message,
    pub args: Vec<String>,
}

/// Locals of `createDiagnosticExplainingFile`, extracted to a struct so the
/// two Go closures (`processRelatedInfo`, `processInclude`) become methods
/// without borrow conflicts.
struct ExplainState {
    include_details: Vec<DiagnosticRef>,
    related_info: Vec<DiagnosticRef>,
    preferred_location: Option<Rc<FileIncludeReason>>,
    seen_reasons: HashSet<usize>,
}

impl ExplainState {
    /// `processRelatedInfo`.
    fn process_related_info(&mut self, include_reason: &Rc<FileIncludeReason>, program: &Program) {
        if self.preferred_location.is_none()
            && include_reason.is_referenced_file()
            && !program
                .include_processor
                .get_reference_location(include_reason, program)
                .is_synthetic
        {
            self.preferred_location = Some(include_reason.clone());
        } else if !matches!(&self.preferred_location, Some(p) if Rc::ptr_eq(p, include_reason)) {
            if let Some(info) = program
                .include_processor
                .get_related_info(include_reason, program)
            {
                self.related_info.push(info);
            }
        }
    }

    /// `processInclude`.
    fn process_include(&mut self, include_reason: &Rc<FileIncludeReason>, program: &Program) {
        if !self
            .seen_reasons
            .insert(Rc::as_ptr(include_reason) as usize)
        {
            return;
        }
        self.include_details.push(include_reason.to_diagnostic(
            program,
            false,
            RootedDirectoryPath::default(),
        ));
        self.process_related_info(include_reason, program);
    }
}

impl ProcessingDiagnostic {
    /// `(d *processingDiagnostic) toDiagnostic`.
    pub fn to_diagnostic(&self, program: &Program) -> DiagnosticRef {
        match self {
            ProcessingDiagnostic::UnknownReference(ref_) => {
                let loc = ref_.get_referenced_location(program);
                match ref_.kind {
                    crate::file_include::FILE_INCLUDE_KIND_TYPE_REFERENCE_DIRECTIVE => {
                        let nodes = program.arena_of(loc.file);
                        let file_name = loc
                            .ref_
                            .as_ref()
                            .map(|r| r.file_name.clone())
                            .unwrap_or_default();
                        loc.diagnostic_at(
                            &nodes,
                            &diagnostics::Cannot_find_type_definition_file_for_0,
                            &[Value::Str(file_name)],
                        )
                    }
                    crate::file_include::FILE_INCLUDE_KIND_LIB_REFERENCE_DIRECTIVE => {
                        let nodes = program.arena_of(loc.file);
                        let lib_name = tsc_tspath::to_file_name_lower_case(
                            &loc.ref_
                                .as_ref()
                                .map(|r| r.file_name.clone())
                                .unwrap_or_default(),
                        )
                        .into_owned();
                        let unqualified_lib_name = lib_name
                            .trim_start_matches("lib.")
                            .trim_end_matches(".d.ts")
                            .to_string();
                        let suggestion = tsc_core::core::get_spelling_suggestion_for_strings(
                            &unqualified_lib_name,
                            tsc_tsoptions::enummaps::libs().iter().map(|s| s.as_str()),
                        );
                        let message = if suggestion.is_some() {
                            &diagnostics::Cannot_find_lib_definition_for_0_Did_you_mean_1
                        } else {
                            &diagnostics::Cannot_find_lib_definition_for_0
                        };
                        loc.diagnostic_at(
                            &nodes,
                            message,
                            &[
                                Value::Str(lib_name),
                                Value::Str(suggestion.unwrap_or_default().to_string()),
                            ],
                        )
                    }
                    _ => panic!("unknown include kind"),
                }
            }
            ProcessingDiagnostic::ExplainingFileInclude(_) => {
                self.create_diagnostic_explaining_file(program)
            }
        }
    }

    /// `(d *processingDiagnostic) createDiagnosticExplainingFile`.
    pub fn create_diagnostic_explaining_file(&self, program: &Program) -> DiagnosticRef {
        let ProcessingDiagnostic::ExplainingFileInclude(diag) = self else {
            panic!("not an include-explaining diagnostic")
        };

        let mut state = ExplainState {
            include_details: Vec::new(),
            related_info: Vec::new(),
            preferred_location: None,
            seen_reasons: HashSet::new(),
        };
        let mut redirect_info: Vec<DiagnosticRef> = Vec::new();

        if let Some(reason) = &diag.diagnostic_reason {
            if reason.is_referenced_file()
                && !program
                    .include_processor
                    .get_reference_location(reason, program)
                    .is_synthetic
            {
                state.preferred_location = Some(reason.clone());
            }
        }

        // !!! todo sheetal caching

        if !diag.file.is_empty() {
            let reasons = program
                .file_include_reasons
                .get(&diag.file)
                .cloned()
                .unwrap_or_default();
            for reason in &reasons {
                state.process_include(reason, program);
            }
            redirect_info = program
                .include_processor
                .explain_redirect_and_implied_format(program, &diag.file, &mut |file_name| {
                    file_name.as_string().to_string()
                });
        }
        if let Some(diagnostic_reason) = &diag.diagnostic_reason {
            state.process_include(&diagnostic_reason.clone(), program);
        }
        let mut chain: Vec<DiagnosticRef> = Vec::new();
        if !state.include_details.is_empty()
            && (state.preferred_location.is_none() || state.seen_reasons.len() != 1)
        {
            let file_reason = tsc_ast::diagnostic::new_compiler_diagnostic(
                &diagnostics::The_file_is_in_the_program_because_Colon,
                &[] as &[String],
            );
            lock_diagnostic(&file_reason).set_message_chain(state.include_details);
            chain = vec![file_reason];
        }
        if !redirect_info.is_empty() {
            chain.extend(redirect_info);
        }

        let args: Vec<Value> = diag.args.iter().map(|a| Value::Str(a.clone())).collect();
        let mut result: Option<DiagnosticRef> = None;
        if let Some(preferred) = &state.preferred_location {
            let loc = program
                .include_processor
                .get_reference_location(preferred, program);
            let nodes = program.arena_of(loc.file);
            result = Some(loc.diagnostic_at(&nodes, diag.message, &args));
        }
        let result = result
            .unwrap_or_else(|| tsc_ast::diagnostic::new_compiler_diagnostic(diag.message, &args));
        if !chain.is_empty() {
            lock_diagnostic(&result).set_message_chain(chain);
        }
        if !state.related_info.is_empty() {
            lock_diagnostic(&result).set_related_info(state.related_info);
        }
        result
    }
}
