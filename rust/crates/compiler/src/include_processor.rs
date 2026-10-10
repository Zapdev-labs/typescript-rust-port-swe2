// Ported from tsc/internal/compiler/includeprocessor.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `collections.SyncMap` caches are `RefCell<HashMap>`s and `sync.Once`
// fields are `Cell`-gated `Option`s — the Rust port is single-threaded.
// `*FileIncludeReason` map keys are `Rc::as_ptr` casts to `usize`.
// `*referenceFileLocation`/`​*ast.Diagnostic`/`​*ast.ObjectLiteralExpression`
// are `Rc`/`Option<NodeId>`.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

use rustc_hash::FxHashMap;

use tsc_ast::diagnostic::{DiagnosticRef, DiagnosticsCollection};
use tsc_ast::{NodeId, is_external_or_commonjs_module};
use tsc_core::options_generated::ModuleKind;
use tsc_diagnostics::{self as diagnostics};
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};

use crate::file_include::{FileIncludeReason, ReferenceFileLocation};
use crate::processing_diagnostic::{IncludeExplainingDiagnostic, ProcessingDiagnostic};
use crate::program::Program;

/// `type fileIncludeData struct` — the include-reasons/processing-diagnostics
/// half of `processedFiles`, shared between the files parser and `Program`.
#[derive(Default)]
pub struct FileIncludeData {
    pub file_include_reasons: FxHashMap<PathKey, Vec<Rc<FileIncludeReason>>>,
    pub processing_diagnostics: Vec<ProcessingDiagnostic>,
}

/// `type includeProcessor struct` — owns the lazily-computed include-explain
/// diagnostics and their caches.
#[derive(Default)]
pub struct IncludeProcessor {
    /// `reasonDiagnostics`.
    pub reason_diagnostics: RefCell<FxHashMap<IncludeReasonDiagnosticKey, DiagnosticRef>>,
    /// `reasonToReferenceLocation` — keyed by `Rc::as_ptr(reason) as usize`.
    reason_to_reference_location: RefCell<FxHashMap<usize, Rc<ReferenceFileLocation>>>,
    /// `includeReasonToRelatedInfo` — keyed by `Rc::as_ptr(reason) as usize`.
    include_reason_to_related_info: RefCell<FxHashMap<usize, Option<DiagnosticRef>>>,
    /// `redirectAndFileFormat`.
    redirect_and_file_format: RefCell<FxHashMap<PathKey, Vec<DiagnosticRef>>>,
    /// `computedDiagnostics` + `computedDiagnosticsOnce`.
    computed_diagnostics: DiagnosticsCollection,
    computed_diagnostics_done: Cell<bool>,
    /// `compilerOptionsSyntax` + `compilerOptionsSyntaxOnce` — `None` inner
    /// mirrors Go's nil `*ast.ObjectLiteralExpression`.
    compiler_options_syntax: RefCell<Option<Option<NodeId>>>,
}

/// `type includeReasonDiagnosticKey struct` — `reason` is the
/// `Rc::as_ptr` pointer identity of the `FileIncludeReason`.
#[derive(PartialEq, Eq, Hash)]
pub struct IncludeReasonDiagnosticKey {
    pub reason: usize,
    pub relative_file_name: bool,
    pub relative_to: RootedDirectoryPath,
}

impl IncludeProcessor {
    /// `(i *includeProcessor) getDiagnostics`.
    pub fn get_diagnostics(&self, p: &Program) -> &DiagnosticsCollection {
        if !self.computed_diagnostics_done.get() {
            self.computed_diagnostics_done.set(true);
            for d in &p.processing_diagnostics {
                self.computed_diagnostics.add(&d.to_diagnostic(p));
            }
            for resolutions in p.resolved_modules.values() {
                for resolved_module in resolutions.values() {
                    let Some(resolved_module) = resolved_module else {
                        continue;
                    };
                    for diag in &resolved_module.resolution_diagnostics {
                        self.computed_diagnostics.add(diag);
                    }
                }
            }
            for type_resolutions in p.type_resolutions_in_file.values() {
                for resolved_type_ref in type_resolutions.values() {
                    for diag in &resolved_type_ref.resolution_diagnostics {
                        self.computed_diagnostics.add(diag);
                    }
                }
            }
        }
        &self.computed_diagnostics
    }

    /// `(i *includeProcessor) getReferenceLocation` — caches by
    /// `Rc` pointer identity.
    pub fn get_reference_location(
        &self,
        r: &Rc<FileIncludeReason>,
        program: &Program,
    ) -> Rc<ReferenceFileLocation> {
        let key = Rc::as_ptr(r) as usize;
        if let Some(existing) = self.reason_to_reference_location.borrow().get(&key) {
            return existing.clone();
        }
        let loc = Rc::new(r.get_referenced_location(program));
        self.reason_to_reference_location
            .borrow_mut()
            .entry(key)
            .or_insert_with(|| loc.clone())
            .clone()
    }

    /// `(i *includeProcessor) getCompilerOptionsObjectLiteralSyntax` — the
    /// `NodeId` of the `"compilerOptions"` object literal inside the config
    /// file's own arena, or `None`.
    pub fn get_compiler_options_object_literal_syntax(&self, program: &Program) -> Option<NodeId> {
        if let Some(cached) = *self.compiler_options_syntax.borrow() {
            return cached;
        }
        let result = (|| {
            let config_file = program.opts.config.config_file.as_ref()?;
            let ctx = config_file.as_ctx();
            let initializer = tsc_tsoptions::tsconfigparsing::for_each_ts_config_prop_array(
                Some(ctx),
                "compilerOptions",
                &mut |property| property.initializer,
            )?;
            let node = ctx.node(initializer);
            if node.kind == tsc_ast::Kind::ObjectLiteralExpression {
                Some(initializer)
            } else {
                None
            }
        })();
        *self.compiler_options_syntax.borrow_mut() = Some(result);
        result
    }

    /// `(i *includeProcessor) getRelatedInfo`.
    pub fn get_related_info(
        &self,
        r: &Rc<FileIncludeReason>,
        program: &Program,
    ) -> Option<DiagnosticRef> {
        let key = Rc::as_ptr(r) as usize;
        if let Some(existing) = self.include_reason_to_related_info.borrow().get(&key) {
            return existing.clone();
        }
        let related_info = r.to_related_info(program);
        self.include_reason_to_related_info
            .borrow_mut()
            .entry(key)
            .or_insert_with(|| related_info.clone())
            .clone()
    }

    /// `(i *includeProcessor) explainRedirectAndImpliedFormat`.
    pub fn explain_redirect_and_implied_format(
        &self,
        program: &Program,
        file_path: &PathKey,
        to_file_name: &mut dyn FnMut(&RootedFilePath) -> String,
    ) -> Vec<DiagnosticRef> {
        if let Some(existing) = self.redirect_and_file_format.borrow().get(file_path) {
            return existing.clone();
        }
        let mut result: Vec<DiagnosticRef> = Vec::new();
        let mut compute = || {
            // `var file ast.HasFileName` — either a `redirectsFile` stand-in or
            // the source file's `NodeId`; both resolve through the program's
            // `*HasFileName` parameter helpers via a lookup enum.
            enum FileRef {
                Redirect(Rc<crate::file_loader::RedirectsFile>),
                Source(NodeId),
            }
            let redirects_file = program.redirect_files_by_path.get(file_path).cloned();
            let source_file = if redirects_file.is_none() {
                match program.get_source_file_by_path(file_path) {
                    Some(sf) => Some(sf),
                    None => return,
                }
            } else {
                None
            };
            let file = match (redirects_file, source_file) {
                (Some(r), _) => FileRef::Redirect(r),
                (_, Some(s)) => FileRef::Source(s),
                (None, None) => return,
            };

            // `program.GetSourceOfProjectReferenceIfOutputIncluded(file)`
            let file_file_name = match &file {
                FileRef::Redirect(r) => r.file_name.clone(),
                FileRef::Source(s) => program
                    .arena_of(*s)[*s]
                    .as_source_file()
                    .file_name()
                    .clone(),
            };
            let source = match &file {
                FileRef::Redirect(r) => program
                    .get_source_of_project_reference_if_output_included(&**r),
                FileRef::Source(s) => program
                    .get_source_of_project_reference_if_output_included(
                        &program.file_has_file_name(*s),
                    ),
            };
            if source != file_file_name {
                result.push(tsc_ast::diagnostic::new_compiler_diagnostic(
                    &diagnostics::File_is_output_of_project_reference_source_0,
                    &[to_file_name(&source)],
                ));
            }

            if let FileRef::Redirect(r) = &file {
                if let Some(target_file) = program.get_source_file_by_path(&r.target) {
                    let nodes = program.arena_of(target_file);
                    let name = nodes[target_file].as_source_file().file_name().clone();
                    result.push(tsc_ast::diagnostic::new_compiler_diagnostic(
                        &diagnostics::File_redirects_to_file_0,
                        &[to_file_name(&name)],
                    ));
                }
            }

            if let FileRef::Source(sf_id) = &file {
                let nodes = program.arena_of(*sf_id);
                if is_external_or_commonjs_module(nodes[*sf_id].as_source_file()) {
                    let meta_data = program.get_source_file_meta_data(
                        nodes[*sf_id].as_source_file().path_key(),
                    );
                    match program.get_implied_node_format_for_emit(
                        &program.file_has_file_name(*sf_id),
                    ) {
                        ModuleKind::ESNext => {
                            if meta_data.package_json_type == "module" {
                                result.push(tsc_ast::diagnostic::new_compiler_diagnostic(
                                    &diagnostics::File_is_ECMAScript_module_because_0_has_field_type_with_value_module,
                                    &[to_file_name(
                                        &meta_data.package_json_directory.resolve_file("package.json"),
                                    )],
                                ));
                            }
                        }
                        ModuleKind::CommonJS => {
                            if !meta_data.package_json_type.is_empty() {
                                result.push(tsc_ast::diagnostic::new_compiler_diagnostic(
                                    &diagnostics::File_is_CommonJS_module_because_0_has_field_type_whose_value_is_not_module,
                                    &[to_file_name(
                                        &meta_data.package_json_directory.resolve_file("package.json"),
                                    )],
                                ));
                            } else if !meta_data.package_json_directory.is_empty() {
                                // `metaData.PackageJsonType == ""` is implied.
                                result.push(tsc_ast::diagnostic::new_compiler_diagnostic(
                                    &diagnostics::File_is_CommonJS_module_because_0_does_not_have_field_type,
                                    &[to_file_name(
                                        &meta_data.package_json_directory.resolve_file("package.json"),
                                    )],
                                ));
                            } else {
                                result.push(tsc_ast::diagnostic::new_compiler_diagnostic(
                                    &diagnostics::File_is_CommonJS_module_because_package_json_was_not_found,
                                    &[] as &[String],
                                ));
                            }
                        }
                        _ => {}
                    }
                }
            }
        };
        compute();
        self.redirect_and_file_format
            .borrow_mut()
            .entry(file_path.clone())
            .or_insert_with(|| result.clone())
            .clone()
    }
}

impl FileIncludeData {
    /// `(i *fileIncludeData) addProcessingDiagnostic`.
    pub fn add_processing_diagnostic(&mut self, d: ProcessingDiagnostic) {
        self.processing_diagnostics.push(d);
    }

    /// `(i *fileIncludeData) addProcessingDiagnosticsForFileCasing`.
    pub fn add_processing_diagnostics_for_file_casing(
        &mut self,
        file: PathKey,
        existing_casing: String,
        current_casing: String,
        reason: Rc<FileIncludeReason>,
    ) {
        if !reason.is_referenced_file()
            && self
                .file_include_reasons
                .get(&file)
                .is_some_and(|reasons| reasons.iter().any(|r| r.is_referenced_file()))
        {
            self.add_processing_diagnostic(ProcessingDiagnostic::ExplainingFileInclude(Box::new(
                IncludeExplainingDiagnostic {
                    file,
                    diagnostic_reason: Some(reason),
                    message: &diagnostics::Already_included_file_name_0_differs_from_file_name_1_only_in_casing,
                    args: vec![existing_casing, current_casing],
                },
            )));
        } else {
            self.add_processing_diagnostic(ProcessingDiagnostic::ExplainingFileInclude(Box::new(
                IncludeExplainingDiagnostic {
                    file,
                    diagnostic_reason: Some(reason),
                    message: &diagnostics::File_name_0_differs_from_already_included_file_name_1_only_in_casing,
                    args: vec![current_casing, existing_casing],
                },
            )));
        }
    }
}
