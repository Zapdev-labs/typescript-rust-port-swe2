// Ported from tsc/internal/compiler/fileInclude.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// PORT: `*ast.SourceFile`/`​*ast.Node` are `NodeId` + arena (`&[Node]` or
// `SourceFileCtx`). `*FileIncludeReason` identity is `Rc<FileIncludeReason>`
// (pointer-keyed caches index `Rc::as_ptr` casts). `*ast.Diagnostic` is
// `DiagnosticRef`. Go's `syncmap.SyncMap` diagnostic caches are plain
// `RefCell<HashMap>`s since the Rust port is single-threaded.

use std::rc::Rc;

use tsc_ast::diagnostic::DiagnosticRef;
use tsc_ast::{FileReference, Node, NodeId, node_is_synthesized};
use tsc_diagnostics::{self as diagnostics};
use tsc_module::PackageId;
use tsc_scanner::scanner::skip_trivia;
use tsc_tspath::{PathKey, RootedDirectoryPath, RootedFilePath};
use tsc_tsoptions::value::Value;

use crate::program::Program;

/// `fileIncludeKind` — open i32 newtype, mirroring the Go `int` kind.
#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct FileIncludeKind(pub i32);

// References from file
pub const FILE_INCLUDE_KIND_IMPORT: FileIncludeKind = FileIncludeKind(0);
pub const FILE_INCLUDE_KIND_REFERENCE_FILE: FileIncludeKind = FileIncludeKind(1);
pub const FILE_INCLUDE_KIND_TYPE_REFERENCE_DIRECTIVE: FileIncludeKind = FileIncludeKind(2);
pub const FILE_INCLUDE_KIND_LIB_REFERENCE_DIRECTIVE: FileIncludeKind = FileIncludeKind(3);

pub const FILE_INCLUDE_KIND_ROOT_FILE: FileIncludeKind = FileIncludeKind(4);
pub const FILE_INCLUDE_KIND_LIB_FILE: FileIncludeKind = FileIncludeKind(5);
pub const FILE_INCLUDE_KIND_AUTOMATIC_TYPE_DIRECTIVE_FILE: FileIncludeKind = FileIncludeKind(6);
pub const FILE_INCLUDE_KIND_CONTENT_MAPPER_SUPPLEMENTAL: FileIncludeKind = FileIncludeKind(7);

/// `type FileIncludeReason struct` — immutable after creation; shared through
/// `Rc` (Go pointers are the diagnostic-cache keys here as `usize` casts of
/// `Rc::as_ptr`).
#[derive(Default, Clone)]
pub struct FileIncludeReason {
    pub kind: FileIncludeKind,
    pub index: usize,
    pub is_default_lib: bool,
    pub referenced_file: Option<Box<ReferencedFileData>>,
    pub automatic_type_directive: Option<Box<AutomaticTypeDirectiveFileData>>,
    /// The canonical-source `PathKey` of the content mapper, for
    /// `FileIncludeKindContentMapperSupplemental` reasons.
    pub canonical_source_file: PathKey,
}

/// `type referencedFileData struct`.
#[derive(Clone)]
pub struct ReferencedFileData {
    /// The *referrer* file's path (`ref.file` in Go is the task's path).
    pub file: PathKey,
    /// `index` — Go `int`; negative for the synthetic importHelpers/JSX
    /// specifiers (`synthetic` is `Some` in that case and `index` is unused).
    pub index: isize,
    /// `synthetic *ast.Node` → `Option<NodeId>` — synthetic module specifier
    /// created by the loader for importHelpers/JSX-runtime imports.
    pub synthetic: Option<NodeId>,
}

/// `type referenceFileLocation struct`.
///
/// `file`/`node` are `NodeId`s in the same arena (the source file's);
/// `ref_`/`package_id` are values since Go's pointers here are read-only.
pub struct ReferenceFileLocation {
    /// The `SourceFile` node containing the reference.
    pub file: NodeId,
    /// The referencing import/module-augmentation node, if any.
    pub node: Option<NodeId>,
    /// The `/// <reference ... />` directive, for non-import kinds.
    pub ref_: Option<FileReference>,
    pub package_id: PackageId,
    pub is_synthetic: bool,
}

impl ReferenceFileLocation {
    /// `(r *referenceFileLocation) text()` — `nodes` is `file`'s arena.
    pub fn text(&self, nodes: &[Node]) -> String {
        if let Some(node_id) = self.node {
            let n = &nodes[node_id];
            let source_text = self.file_text(nodes);
            if !node_is_synthesized(n) {
                let pos = skip_trivia(source_text, n.pos()) as usize;
                let end = n.end() as usize;
                return source_text[pos..end].to_string();
            } else {
                return format!("\"{}\"", n.text(nodes));
            }
        }
        let ref_ = self.ref_.as_ref().expect("referenceFileLocation.ref");
        let source_text = self.file_text(nodes);
        source_text[ref_.text_range.pos() as usize..ref_.text_range.end() as usize].to_string()
    }

    fn file_text<'a>(&self, nodes: &'a [Node]) -> &'a str {
        nodes[self.file].as_source_file().text()
    }

    /// `(r *referenceFileLocation) diagnosticAt` — `nodes` is `file`'s arena.
    pub fn diagnostic_at(
        &self,
        nodes: &[Node],
        message: &'static diagnostics::Message,
        args: &[Value],
    ) -> DiagnosticRef {
        if let Some(node_id) = self.node {
            tsc_tsoptions::errors::create_diagnostic_for_node_in_source_file(
                tsc_tsoptions::tsconfigparsing::SourceFileCtx {
                    file: self.file,
                    nodes,
                },
                node_id,
                message,
                args,
            )
        } else {
            tsc_ast::diagnostic::new_diagnostic(
                Some(tsc_ast::diagnostic::DiagnosticFile::from_node(
                    self.file, nodes,
                )),
                self.ref_.as_ref().unwrap().text_range,
                message,
                args,
            )
        }
    }
}

/// `type automaticTypeDirectiveFileData struct`.
#[derive(Default, Clone)]
pub struct AutomaticTypeDirectiveFileData {
    pub type_reference: String,
    pub package_id: PackageId,
}

impl FileIncludeReason {
    /// `(r *FileIncludeReason) asIndex`.
    pub fn as_index(&self) -> usize {
        self.index
    }

    /// `(r *FileIncludeReason) asLibFileIndex` — `(index, ok)` where Go's
    /// second return is `!r.isDefaultLib`.
    pub fn as_lib_file_index(&self) -> (usize, bool) {
        (self.index, !self.is_default_lib)
    }

    /// `(r *FileIncludeReason) isReferencedFile`.
    pub fn is_referenced_file(&self) -> bool {
        self.kind.0 <= FILE_INCLUDE_KIND_LIB_REFERENCE_DIRECTIVE.0
    }

    /// `(r *FileIncludeReason) asReferencedFileData`.
    pub fn as_referenced_file_data(&self) -> &ReferencedFileData {
        self.referenced_file.as_deref().expect("referencedFile")
    }

    /// `(r *FileIncludeReason) asAutomaticTypeDirectiveFileData`.
    pub fn as_automatic_type_directive_file_data(&self) -> &AutomaticTypeDirectiveFileData {
        self.automatic_type_directive
            .as_deref()
            .expect("automaticTypeDirective")
    }

    /// `(r *FileIncludeReason) getReferencedLocation`.
    pub fn get_referenced_location(&self, program: &Program) -> ReferenceFileLocation {
        let ref_ = self.as_referenced_file_data();
        let file = program
            .get_source_file_by_path(&ref_.file)
            .expect("source file for referenced file path");
        let nodes = program.arena_of(file);
        let sf = nodes[file].as_source_file();
        match self.kind {
            FILE_INCLUDE_KIND_IMPORT => {
                let mut specifier: Option<NodeId> = None;
                let mut is_synthetic = false;
                if let Some(synthetic) = ref_.synthetic {
                    specifier = Some(synthetic);
                    is_synthetic = true;
                } else if ref_.index >= 0 && (ref_.index as usize) < sf.imports().len() {
                    specifier = Some(sf.imports()[ref_.index as usize]);
                } else {
                    let mut aug_index = sf.imports().len();
                    for &imp in &sf.module_augmentations {
                        if nodes[imp].kind == tsc_ast::Kind::StringLiteral {
                            if aug_index == ref_.index as usize {
                                specifier = Some(imp);
                                break;
                            }
                            aug_index += 1;
                        }
                    }
                }
                let resolution = specifier
                    .and_then(|specifier| program.get_resolved_module_from_module_specifier(file, specifier));
                ReferenceFileLocation {
                    file,
                    node: specifier,
                    ref_: None,
                    package_id: resolution.map_or_else(PackageId::default, |r| r.package_id),
                    is_synthetic,
                }
            }
            FILE_INCLUDE_KIND_REFERENCE_FILE => ReferenceFileLocation {
                file,
                node: None,
                ref_: Some(sf.referenced_files[ref_.index as usize].clone()),
                package_id: PackageId::default(),
                is_synthetic: false,
            },
            FILE_INCLUDE_KIND_TYPE_REFERENCE_DIRECTIVE => ReferenceFileLocation {
                file,
                node: None,
                ref_: Some(sf.type_reference_directives[ref_.index as usize].clone()),
                package_id: PackageId::default(),
                is_synthetic: false,
            },
            FILE_INCLUDE_KIND_LIB_REFERENCE_DIRECTIVE => ReferenceFileLocation {
                file,
                node: None,
                ref_: Some(sf.lib_reference_directives[ref_.index as usize].clone()),
                package_id: PackageId::default(),
                is_synthetic: false,
            },
            _ => panic!("unknown reason: {}", self.kind.0),
        }
    }

    /// `(r *FileIncludeReason) toDiagnostic`.
    pub fn to_diagnostic(
        self: &Rc<Self>,
        program: &Program,
        relative_file_name: bool,
        relative_to: RootedDirectoryPath,
    ) -> DiagnosticRef {
        let key = crate::include_processor::IncludeReasonDiagnosticKey {
            reason: Rc::as_ptr(self) as usize,
            relative_file_name,
            relative_to: relative_to.clone(),
        };
        if let Some(diagnostic) = program
            .include_processor
            .reason_diagnostics
            .borrow()
            .get(&key)
        {
            return diagnostic.clone();
        }
        let diagnostic = self.compute_diagnostic(program, &mut |file_name| {
            if relative_file_name {
                if let Some(relative_path) = program
                    .case_sensitivity()
                    .relative_path_from_directory(&relative_to, file_name)
                {
                    return relative_path.as_string().to_string();
                }
            }
            file_name.as_string().to_string()
        });
        program
            .include_processor
            .reason_diagnostics
            .borrow_mut()
            .entry(key)
            .or_insert_with(|| diagnostic.clone())
            .clone()
    }

    /// `(r *FileIncludeReason) computeDiagnostic`.
    pub fn compute_diagnostic(
        self: &Rc<Self>,
        program: &Program,
        to_file_name: &mut dyn FnMut(&RootedFilePath) -> String,
    ) -> DiagnosticRef {
        if self.is_referenced_file() {
            return self.compute_reference_file_diagnostic(program, to_file_name);
        }
        let config = program.config();
        match self.kind {
            FILE_INCLUDE_KIND_ROOT_FILE => {
                if config.config_file.is_some() {
                    let file_name = &config.file_names()[self.as_index()];
                    let matched_file_spec = config.get_matched_file_spec(file_name);
                    if !matched_file_spec.is_empty() {
                        return tsc_ast::diagnostic::new_compiler_diagnostic(
                            &diagnostics::Part_of_files_list_in_tsconfig_json,
                            &[matched_file_spec, to_file_name(file_name)],
                        );
                    } else {
                        let (matched_include_spec, is_default_include_spec) =
                            config.get_matched_include_spec(file_name);
                        if !matched_include_spec.is_empty() {
                            if is_default_include_spec {
                                return tsc_ast::diagnostic::new_compiler_diagnostic(
                                    &diagnostics::Matched_by_default_include_pattern_Asterisk_Asterisk_Slash_Asterisk,
                                    &[] as &[String],
                                );
                            } else {
                                return tsc_ast::diagnostic::new_compiler_diagnostic(
                                    &diagnostics::Matched_by_include_pattern_0_in_1,
                                    &[matched_include_spec, to_file_name(config.config_name())],
                                );
                            }
                        } else {
                            return tsc_ast::diagnostic::new_compiler_diagnostic(
                                &diagnostics::Root_file_specified_for_compilation,
                                &[] as &[String],
                            );
                        }
                    }
                } else {
                    tsc_ast::diagnostic::new_compiler_diagnostic(
                        &diagnostics::Root_file_specified_for_compilation,
                        &[] as &[String],
                    )
                }
            }
            FILE_INCLUDE_KIND_AUTOMATIC_TYPE_DIRECTIVE_FILE => {
                let data = self.as_automatic_type_directive_file_data();
                if !program.options().uses_wildcard_types() {
                    if !data.package_id.name.is_empty() {
                        tsc_ast::diagnostic::new_compiler_diagnostic(
                            &diagnostics::Entry_point_of_type_library_0_specified_in_compilerOptions_with_packageId_1,
                            &[data.type_reference.clone(), data.package_id.to_string()],
                        )
                    } else {
                        tsc_ast::diagnostic::new_compiler_diagnostic(
                            &diagnostics::Entry_point_of_type_library_0_specified_in_compilerOptions,
                            &[data.type_reference.clone()],
                        )
                    }
                } else if !data.package_id.name.is_empty() {
                    tsc_ast::diagnostic::new_compiler_diagnostic(
                        &diagnostics::Entry_point_for_implicit_type_library_0_with_packageId_1,
                        &[data.type_reference.clone(), data.package_id.to_string()],
                    )
                } else {
                    tsc_ast::diagnostic::new_compiler_diagnostic(
                        &diagnostics::Entry_point_for_implicit_type_library_0,
                        &[data.type_reference.clone()],
                    )
                }
            }
            FILE_INCLUDE_KIND_LIB_FILE => {
                let (index, ok) = self.as_lib_file_index();
                if ok {
                    let lib = program
                        .options()
                        .lib
                        .as_ref()
                        .map(|l| l[index].clone())
                        .unwrap_or_default();
                    tsc_ast::diagnostic::new_compiler_diagnostic(
                        &diagnostics::Library_0_specified_in_compilerOptions,
                        &[lib],
                    )
                } else {
                    let target = program.options().get_emit_script_target().to_string();
                    if !target.is_empty() {
                        tsc_ast::diagnostic::new_compiler_diagnostic(
                            &diagnostics::Default_library_for_target_0,
                            &[target],
                        )
                    } else {
                        tsc_ast::diagnostic::new_compiler_diagnostic(
                            &diagnostics::Default_library,
                            &[] as &[String],
                        )
                    }
                }
            }
            FILE_INCLUDE_KIND_CONTENT_MAPPER_SUPPLEMENTAL => {
                let canonical = program
                    .get_source_file_by_path(&self.canonical_source_file)
                    .expect("canonical source file");
                let nodes = program.arena_of(canonical);
                let file_name = nodes[canonical].as_source_file().file_name().clone();
                tsc_ast::diagnostic::new_compiler_diagnostic(
                    &diagnostics::Supplemental_virtual_file_produced_by_the_content_mapper_for_file_0,
                    &[to_file_name(&file_name)],
                )
            }
            _ => panic!("unknown reason: {}", self.kind.0),
        }
    }

    /// `(r *FileIncludeReason) computeReferenceFileDiagnostic`.
    pub fn compute_reference_file_diagnostic(
        self: &Rc<Self>,
        program: &Program,
        to_file_name: &mut dyn FnMut(&RootedFilePath) -> String,
    ) -> DiagnosticRef {
        let reference_location = program.include_processor.get_reference_location(self, program);
        let nodes = program.arena_of(reference_location.file);
        let reference_text = reference_location.text(&nodes);
        let file_name = to_file_name(
            nodes[reference_location.file].as_source_file().file_name(),
        );
        match self.kind {
            FILE_INCLUDE_KIND_IMPORT => {
                if !reference_location.is_synthetic {
                    if !reference_location.package_id.name.is_empty() {
                        tsc_ast::diagnostic::new_compiler_diagnostic(
                            &diagnostics::Imported_via_0_from_file_1_with_packageId_2,
                            &[
                                reference_text,
                                file_name,
                                reference_location.package_id.to_string(),
                            ],
                        )
                    } else {
                        tsc_ast::diagnostic::new_compiler_diagnostic(
                            &diagnostics::Imported_via_0_from_file_1,
                            &[reference_text, file_name],
                        )
                    }
                } else if program
                    .import_helpers_import_specifiers
                    .get(
                        nodes[reference_location.file]
                            .as_source_file()
                            .path_key(),
                    )
                    .copied()
                    == reference_location.node
                {
                    if !reference_location.package_id.name.is_empty() {
                        tsc_ast::diagnostic::new_compiler_diagnostic(
                            &diagnostics::Imported_via_0_from_file_1_with_packageId_2_to_import_importHelpers_as_specified_in_compilerOptions,
                            &[
                                reference_text,
                                file_name,
                                reference_location.package_id.to_string(),
                            ],
                        )
                    } else {
                        tsc_ast::diagnostic::new_compiler_diagnostic(
                            &diagnostics::Imported_via_0_from_file_1_to_import_importHelpers_as_specified_in_compilerOptions,
                            &[reference_text, file_name],
                        )
                    }
                } else if !reference_location.package_id.name.is_empty() {
                    tsc_ast::diagnostic::new_compiler_diagnostic(
                        &diagnostics::Imported_via_0_from_file_1_with_packageId_2_to_import_jsx_and_jsxs_factory_functions,
                        &[
                            reference_text,
                            file_name,
                            reference_location.package_id.to_string(),
                        ],
                    )
                } else {
                    tsc_ast::diagnostic::new_compiler_diagnostic(
                        &diagnostics::Imported_via_0_from_file_1_to_import_jsx_and_jsxs_factory_functions,
                        &[reference_text, file_name],
                    )
                }
            }
            FILE_INCLUDE_KIND_REFERENCE_FILE => tsc_ast::diagnostic::new_compiler_diagnostic(
                &diagnostics::Referenced_via_0_from_file_1,
                &[reference_text, file_name],
            ),
            FILE_INCLUDE_KIND_TYPE_REFERENCE_DIRECTIVE => {
                if !reference_location.package_id.name.is_empty() {
                    tsc_ast::diagnostic::new_compiler_diagnostic(
                        &diagnostics::Type_library_referenced_via_0_from_file_1_with_packageId_2,
                        &[
                            reference_text,
                            file_name,
                            reference_location.package_id.to_string(),
                        ],
                    )
                } else {
                    tsc_ast::diagnostic::new_compiler_diagnostic(
                        &diagnostics::Type_library_referenced_via_0_from_file_1,
                        &[reference_text, file_name],
                    )
                }
            }
            FILE_INCLUDE_KIND_LIB_REFERENCE_DIRECTIVE => {
                tsc_ast::diagnostic::new_compiler_diagnostic(
                    &diagnostics::Library_referenced_via_0_from_file_1,
                    &[reference_text, file_name],
                )
            }
            _ => panic!("unknown reason: {}", self.kind.0),
        }
    }

    /// `(r *FileIncludeReason) toRelatedInfo`.
    pub fn to_related_info(self: &Rc<Self>, program: &Program) -> Option<DiagnosticRef> {
        if self.is_referenced_file() {
            return self.compute_reference_file_related_info(program);
        }
        let config = program.config();
        let config_file = config.config_file.as_ref()?;
        let config_ctx = config_file.as_ctx();
        match self.kind {
            FILE_INCLUDE_KIND_ROOT_FILE => {
                let file_name = &config.file_names()[self.as_index()];
                let matched_file_spec = config.get_matched_file_spec(file_name);
                if !matched_file_spec.is_empty() {
                    if let Some(files_node) =
                        tsc_tsoptions::tsconfigparsing::get_ts_config_prop_array_element_value(
                            Some(config_ctx),
                            "files",
                            &matched_file_spec,
                        )
                    {
                        return Some(tsc_tsoptions::errors::create_diagnostic_for_node_in_source_file(
                            config_ctx,
                            files_node,
                            &diagnostics::File_is_matched_by_files_list_specified_here,
                            &[],
                        ));
                    }
                } else {
                    let (matched_include_spec, is_default_include_spec) =
                        config.get_matched_include_spec(file_name);
                    if !matched_include_spec.is_empty() && !is_default_include_spec {
                        if let Some(include_node) =
                            tsc_tsoptions::tsconfigparsing::get_ts_config_prop_array_element_value(
                                Some(config_ctx),
                                "include",
                                &matched_include_spec,
                            )
                        {
                            return Some(
                                tsc_tsoptions::errors::create_diagnostic_for_node_in_source_file(
                                    config_ctx,
                                    include_node,
                                    &diagnostics::File_is_matched_by_include_pattern_specified_here,
                                    &[],
                                ),
                            );
                        }
                    }
                }
            }
            FILE_INCLUDE_KIND_AUTOMATIC_TYPE_DIRECTIVE_FILE => {
                if !program.options().uses_wildcard_types() {
                    let data = self.as_automatic_type_directive_file_data();
                    if let Some(types_syntax) =
                        tsc_tsoptions::tsconfigparsing::get_options_syntax_by_array_element_value(
                            program
                                .include_processor
                                .get_compiler_options_object_literal_syntax(program),
                            config_ctx,
                            "types",
                            &data.type_reference,
                        )
                    {
                        return Some(tsc_tsoptions::errors::create_diagnostic_for_node_in_source_file(
                            config_ctx,
                            types_syntax,
                            &diagnostics::File_is_entry_point_of_type_library_specified_here,
                            &[],
                        ));
                    }
                }
            }
            FILE_INCLUDE_KIND_LIB_FILE => {
                let (index, ok) = self.as_lib_file_index();
                if ok {
                    let lib_value = program
                        .options()
                        .lib
                        .as_ref()
                        .map(|l| l[index].clone())
                        .unwrap_or_default();
                    if let Some(lib_syntax) =
                        tsc_tsoptions::tsconfigparsing::get_options_syntax_by_array_element_value(
                            program
                                .include_processor
                                .get_compiler_options_object_literal_syntax(program),
                            config_ctx,
                            "lib",
                            &lib_value,
                        )
                    {
                        return Some(tsc_tsoptions::errors::create_diagnostic_for_node_in_source_file(
                            config_ctx,
                            lib_syntax,
                            &diagnostics::File_is_library_specified_here,
                            &[],
                        ));
                    }
                } else {
                    let target = program.options().get_emit_script_target().to_string();
                    if !target.is_empty() {
                        if let Some(target_value_syntax) =
                            tsc_tsoptions::tsconfigparsing::for_each_property_assignment(
                                program
                                    .include_processor
                                    .get_compiler_options_object_literal_syntax(program),
                                config_ctx,
                                "target",
                                &mut |property| {
                                    let initializer = property.initializer?;
                                    let node = config_ctx.node(initializer);
                                    if node.kind == tsc_ast::Kind::StringLiteral
                                        && node.text(config_ctx.nodes) == target
                                    {
                                        return Some(initializer);
                                    }
                                    None
                                },
                                None,
                            )
                        {
                            return Some(tsc_tsoptions::errors::create_diagnostic_for_node_in_source_file(
                                config_ctx,
                                target_value_syntax,
                                &diagnostics::File_is_default_library_for_target_specified_here,
                                &[],
                            ));
                        }
                    }
                }
            }
            FILE_INCLUDE_KIND_CONTENT_MAPPER_SUPPLEMENTAL => return None,
            _ => panic!("unknown reason: {}", self.kind.0),
        }
        None
    }

    /// `(r *FileIncludeReason) computeReferenceFileRelatedInfo`.
    pub fn compute_reference_file_related_info(
        self: &Rc<Self>,
        program: &Program,
    ) -> Option<DiagnosticRef> {
        let reference_location = program.include_processor.get_reference_location(self, program);
        if reference_location.is_synthetic {
            return None;
        }
        let nodes = program.arena_of(reference_location.file);
        match self.kind {
            FILE_INCLUDE_KIND_IMPORT => Some(reference_location.diagnostic_at(
                &nodes,
                &diagnostics::File_is_included_via_import_here,
                &[],
            )),
            FILE_INCLUDE_KIND_REFERENCE_FILE => Some(reference_location.diagnostic_at(
                &nodes,
                &diagnostics::File_is_included_via_reference_here,
                &[],
            )),
            FILE_INCLUDE_KIND_TYPE_REFERENCE_DIRECTIVE => Some(reference_location.diagnostic_at(
                &nodes,
                &diagnostics::File_is_included_via_type_library_reference_here,
                &[],
            )),
            FILE_INCLUDE_KIND_LIB_REFERENCE_DIRECTIVE => Some(reference_location.diagnostic_at(
                &nodes,
                &diagnostics::File_is_included_via_library_reference_here,
                &[],
            )),
            _ => panic!("unknown reason: {}", self.kind.0),
        }
    }
}
